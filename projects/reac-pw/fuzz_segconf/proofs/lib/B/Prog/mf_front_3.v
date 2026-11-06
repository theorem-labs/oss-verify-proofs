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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 183 of its 232 lines of code are new or changed and 404 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_FRONT of lib/B/Prog/m_file_m.v,
   piece 3 (sl, lib/B/Prog/mf_front_m.v): `fr_sl : FR_E_stmt B n -> FR_SL_stmt B n`, the code back from
   strlen(p) when the text left has no '\n' (the neutral listing of m_file in image B lines 157-162):
     0x863ac not a1,s10        a1 = ~p (the executor keeps s10 xor -1)
     0x863b0 li a6,32
     0x863b4 bltu a1,a0,86e84  the UBSan trap (pointer overflow of p + len): a0 = |rest|, and mf_loop's
                               sa_addr p (|rest| + 1) gives p + |rest| + 1 <= 2^63, so ~p = 2^64 - 1 - p >= |rest|
                               and the branch to the unimp 0x86e84 is not taken
     0x863b8 add a0,s10,a0     a0 = p + |rest|
     0x863bc sd a0,168(s1)     168(s1) = p + |rest|
     0x863c0 mv a2,a0          a2 = p + |rest|
   and so to 0x863c4 = FR_E. With no '\n' in rest, mf_line rest = rest and mf_next p rest = p + |rest|
   (mf_front_mdl.v fr_next_cases), which is FR_E's a0, a2 and 168(s1); a6 = 0x20; 176(s1) = p is kept.
   The walk: m_file_sd.v's mf_seed at FR_SL (no cells, no 152(s1)) with the frame cells' write window narrowed to
   [168, 176) (PaLibF.v region_ok_rewindow), two token runs (to the branch; past it to FR_E), the trap edge
   refuted at its branch from the executor's branch condition (YI08.v U_not), and the cut facts carried across
   the store by fr_run_keep (m_file_k.v mf_keep_run_s; mf_val_keep for the frame cells outside the window). The
   new 168(s1) is the final state's chunk (PaDenot.v field_of_region).
   SHARED with piece 2 (lib/B/Prog/mf_front_2.v): fr_run_keep, fr_denot_U and the tactics fr_awr (the run's write
   goal over the seed's regions), fr_U, fr_win (kept_of_frame's window goal).
   A walk lane of the image-B m_file-family owner's G2B, pieces 2 and 3 (a working branch). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_front_mdl mf_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* a word expression's value from its unsigned value *)
Lemma fr_denot_U : forall E e x, U E e = x -> sv_denot E e = Z_to_bv 64 x.
Proof. intros E e x H. unfold U in H. rewrite <- H. symmetry. apply Z_to_bv_bv_unsigned. Qed.
(* the write goal of a run from the seed with the frame cells' window narrowed to strip's cells: the frame cells'
   region (index 1, base atom 2 = s1 = sp0 + (s1 - sp0)) is in the stack band below sp0; every other region is
   read-only *)
Ltac fr_awr U2 HSTK :=
  lazymatch goal with |- awr_ok ?a1 ?a2 ?a3 ?rs ?a5 ?a6 ?a7 ?a8 ?a9 ?a10 ?a11 ?a12 =>
    let rs' := eval vm_compute in rs in change (awr_ok a1 a2 a3 rs' a5 a6 a7 a8 a9 a10 a11 a12) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  lazymatch goal with |- awr_ok _ _ _ _ _ ?sp0 _ _ _ _ _ _ =>
    eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ _ _ _ 2%nat (mf_s1 sp0 - sp0));
    [reflexivity | rewrite U2; lia | cbn [YP09.r_wlo]; rewrite ?HSTK; lia | cbn [YP09.r_whi]; lia |] end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
(* the unsigned value of an ALU expression over atoms whose values the context gives *)
Ltac fr_U := repeat rewrite U_SAlu; rewrite ?U_SLit; cbn [zalu_raw].
(* kept_of_frame's window goal for the seed's regions: the read-only regions have empty windows; the frame cells'
   window is at s1 (U2 : the value of atom 2) *)
Ltac fr_win U2 :=
  let bb := fresh "bb" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "x" in
  let Hinw := fresh "Hinw" in let Hr := fresh "Hr" in let Hq := fresh "Hq" in
  intros bb wlo whi x Hinw Hr; vm_compute in Hinw;
  repeat (destruct Hinw as [Hq | Hinw];
    [injection Hq as <- <- <-; cbn [base_val] in Hr; first [lia | rewrite U2 in Hr; lia] |]);
  destruct Hinw.

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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the head's cut facts across a run that writes only the frame cells [s1 + lo, s1 + hi), 152 <= lo (strip's cells
   168 / 176 here): mf_core, mf_cells, mf_loop at the new memory (m_file_k.v mf_keep_run_s), and every 8-byte frame
   cell outside the window keeps its value *)
Lemma fr_run_keep : forall v lyc Sc (Wc : world SEGS) memc mdc pos mcc cur mem2 md2 lo hi,
mf_cx B v -> mf_core B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc -> mf_cells v lyc pos memc Wc cur ->
ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
  (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
152 <= lo -> hi <= 216 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + lo <= a < mf_s1 (mv_sp v) + hi) -> rdW Wc mem2 a = rdW Wc memc a) ->
mf_core B v lyc Sc Wc mem2 md2 pos MF_LOW_OFF mcc /\ mf_cells v lyc pos mem2 Wc cur /\
(forall mc0 cur0 line p rest, mf_loop v Wc memc mc0 cur0 line p rest -> mf_loop v Wc mem2 mc0 cur0 line p rest) /\
(forall o x, 16 <= o -> o + 8 <= 216 -> (o + 8 <= lo \/ hi <= o) -> mf_slot v memc Wc o x -> mf_slot v mem2 Wc o x).
Proof.
intros v lyc Sc Wc memc mdc pos mcc cur mem2 md2 lo hi CX CORE CELLS HJ2 Hlo Hhi K.
set (RW := fun a => mf_s1 (mv_sp v) + lo <= a < mf_s1 (mv_sp v) + hi).
change (forall a, 0 <= a < 2 ^ 64 -> ~ RW a -> rdW Wc mem2 a = rdW Wc memc a) in K.
pose proof CORE as (HJ & _ & _ & VSH & _ & _ & Hmc & _).
pose proof CELLS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & V136 & _).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (1, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (mf_frame_facts B lyc Sc Wc memc mdc pos HAR Hin) as (F1 & F2 & _).
destruct (mf_s1_facts B v CX) as (Hs1 & _ & Hsp).
destruct (mf_sp0 B v CX) as (_ & Sp2 & _).
destruct (mf_c_entry B v CX) as (bc & mbc & _ & Hb1 & Hb2 & Hb3 & Hb4 & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hsp.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (Z.div_mod (frame_addr lyc 1 pos) 8 ltac:(lia)) as D8.
pose proof (Z.mod_pos_bound (frame_addr lyc 1 pos) 8 ltac:(lia)) as M8.
destruct (mf_keep_run_s B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur mem2 md2 RW MF_LOW_OFF cur mcc CX CORE CELLS
  HJ2 K) as (C1 & C2 & C3).
- intros a Ha. unfold mf_rw. right; right; right; right; right. unfold RW in Ha. lia.
- intros a Ha _. right. unfold RW in Ha. lia.
- intros i Hi. apply (mf_val_keep Wc Wc memc mem2 RW _ 1 _ K);
    [unfold SHADOW_OFF; lia | change (Z.of_nat 1) with 1; unfold SHADOW_OFF; lia
    | intros k Hk HR; unfold RW in HR; change (Z.of_nat 1) with 1 in Hk; unfold SHADOW_OFF in HR; lia | exact (VSH i Hi)].
- apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [lia | change (Z.of_nat 8) with 8; lia
    | intros k Hk HR; unfold RW in HR; change (Z.of_nat 8) with 8 in Hk; lia | exact V136].
- apply (mf_mconf_keep Wc Wc memc mem2 RW _ _ K); [lia | unfold seg_spec.SEG_M_SIZE in *; lia
    | intros a Ha HR; unfold RW in HR; unfold seg_spec.SEG_M_SIZE in *; lia | exact Hmc].
- split; [exact C1|]. split; [exact C2|]. split; [exact C3|].
  intros o x Ho1 Ho2 Ho3 V. unfold mf_slot in V |- *.
  apply (mf_val_keep Wc Wc memc mem2 RW _ 8 _ K);
    [lia | change (Z.of_nat 8) with 8; lia
    | intros k Hk HR; unfold RW in HR; change (Z.of_nat 8) with 8 in Hk; lia | exact V].
Qed.

Lemma fr_sl : forall n, FR_E_stmt B n -> FR_SL_stmt B n.
Proof.
intros n FE. unfold FR_SL_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX R26 R21 R20 S176 HNL R10.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & EQ).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (L1 & L2 & L3 & LSTR & LADDR & HCOK & _).
pose proof LADDR as (Hp0 & Hp63 & _).
destruct (fr_next_cases p rest) as [(Hx & _) | (_ & HNX & HLN)]; [rewrite HNL in Hx; discriminate|].
destruct (mf_s1_facts B v CX) as (Hs1 & Hs1m & Hsp).
destruct (mf_sp0 B v CX) as (_ & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hsp.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE HCOK) as Hcur.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur 0 [] FR_SL false false [] false false [] false
  CX CORE RB ltac:(intros Hf; discriminate Hf) Hcur ltac:(intros Hf; discriminate Hf) ltac:(lia)
  ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS0.
remember (mfE regs1 v lyc pos cur 0 []) as E eqn:HE0.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr regs1 r)
  by (subst E; intros; apply mfE_reg; assumption).
assert (EX : forall j, (32 + j < A_TEXT)%nat -> ew E (32 + j) = nth j (mf_extra v lyc pos cur 0 []) (Z_to_bv 64 0))
  by (subst E; intros; apply mfE_extra; assumption).
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
clear HE0.
pose proof (EX 0%nat ltac:(unfold A_TEXT; lia)) as E32. cbn [Nat.add nth mf_extra map app] in E32.
assert (U2 : bv_unsigned (ew E 2) = mf_s1 (mv_sp v))
  by (rewrite (EE 2%nat 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof HR1 as (_ & _ & HW1 & _);
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 168 176) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 168 176 HR1 ltac:(intros o Ho; apply HW1; cbv [mf_r_slots YP09.r_wlo YP09.r_whi]; lia)))
    as HS1 end.
clear HS0 HR1 HW1.
lazymatch type of HS1 with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS1 end.
pose proof CORE as (HJ & _).
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
assert (E26 : ew E 26 = Z_to_bv 64 p) by (rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity).
assert (U26 : U E (SOff 26 0) = p) by (apply (U_atom E 26 p E26); lia).
assert (E10 : ew E 10 = Z_to_bv 64 (Z.of_nat (length rest))) by (rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity).
assert (U10 : U E (SOff 10 0) = Z.of_nat (length rest)) by (apply (U_atom E 10 _ E10); lia).
(* 0x863ac not a1,s10; 0x863b0 li a6,32: the run stops at the trap branch 0x863b4 *)
paj_run_tok RUN HS1 HJ SHOK Bspan.
{ fr_awr U2 HSTK. }
psrr_branch_tok RUN BR HS1 SHOK Bspan.
- (* 0x863b4 bltu a1,a0 taken: the UBSan trap (p + |rest| wraps), refuted: ~p = 2^64 - 1 - p >= |rest| *)
  (* the executor leaves a1 = s10 xor -1 *)
  exfalso. rewrite branch_ltu_U, (U_not E 26 p E26 ltac:(lia)), U10 in Hc.
  apply Z.ltb_lt in Hc. lia.
- (* 0x863b8 add a0,s10,a0; 0x863bc sd a0,168(s1); 0x863c0 mv a2,a0: to FR_E *)
  clear Hc.
  paj_run_to_tok RUNTO HS1 HJ SHOK Bspan FR_E.
  { fr_awr U2 HSTK. }
  (* the two runs wrote only 168(s1): every cut fact at the new memory *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 176) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha HnW.
    refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms) (fun a => mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 176)
      HFr _ a Ha HnW).
    fr_win U2. }
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 176) ->
    rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha HnW.
    refine (kept_of_frame E _ (w_H Wc) (ms_mem ms) (ms_mem ms0)
      (fun a => mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 176) HFr0 _ a Ha HnW).
    fr_win U2. }
  assert (Kc : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 176) ->
    rdW Wc (ms_mem ms0) a = rdW Wc memc a) by (intros a Ha HnW; rewrite (K2 a Ha HnW); exact (K1 a Ha HnW)).
  destruct (fr_run_keep v lyc Sc Wc memc mdc pos mcc cur (ms_mem ms0) _ 168 176 CX CORE CELLS HJ ltac:(lia) ltac:(lia) Kc)
    as (CORE2 & CELLS2 & LPf & SLf).
  (* 168(s1) = a0 = p + |rest| from the final state's frame cells *)
  pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1. cbn [restrict ms_mem] in HR1.
  assert (V168 : mf_slot v (ms_mem ms0) Wc 168 (p + Z.of_nat (length rest))).
  { unfold mf_slot.
    lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
      refine (field_of_region E _ nb _ cs lo hi wlo whi 168 8%N (SAlu ALU_ADD (SOff 10 0) (SOff 26 0))
        (p + Z.of_nat (length rest)) HR1 U2 ltac:(cbn [In]; left; reflexivity) _ ltac:(cbn; lia) ltac:(cbn; lia)) end.
    apply fr_denot_U. fr_U. rewrite U10, U26, zcanon_id by (unfold M64; lia). lia. }
  (* the registers at FR_E *)
  prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
  prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23.
  prreg HS1 (24%bv : bv 5) Q24. prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22.
  prreg HS1 (25%bv : bv 5) Q25. prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (21%bv : bv 5) Q21.
  prreg HS1 (20%bv : bv 5) Q20.
  pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ _ (10%bv : bv 5) HS1) as P10.
  lazymatch type of P10 with _ = sv_denot _ (sr_get ?aa ?rr) =>
    let w := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with w in P10 end.
  cbn [ms_regs restrict mkst] in P10.
  pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ _ (12%bv : bv 5) HS1) as P12.
  lazymatch type of P12 with _ = sv_denot _ (sr_get ?aa ?rr) =>
    let w := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with w in P12 end.
  cbn [ms_regs restrict mkst] in P12.
  pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ _ (16%bv : bv 5) HS1) as P16.
  lazymatch type of P16 with _ = sv_denot _ (sr_get ?aa ?rr) =>
    let w := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with w in P16 end.
  cbn [ms_regs restrict mkst] in P16.
  assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms0)).
  { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms0) RA).
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
  rewrite HLN in HNX.
  pmkst HS1.
  apply (FE v lyc Sc Wc (ms_regs ms0) (ms_mem ms0) _ pos mcc cur line p rest).
  + exact (conj CX (conj LS (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj Hn (conj Hne
      (conj (LPf _ _ _ _ _ LOOP) EQ))))))))).
  + rewrite Q26, (EE 26%nat 26%bv eq_refl). exact R26.
  + rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
  + rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
  + exact (SLf 176 p ltac:(lia) ltac:(lia) ltac:(lia) S176).
  + rewrite HLN. exact V168.
  + rewrite P10, HLN. unfold w64. apply fr_denot_U. fr_U. rewrite U10, U26, zcanon_id by (unfold M64; lia). lia.
  + rewrite P12, HNX. unfold w64. apply fr_denot_U. fr_U. rewrite U10, U26, zcanon_id by (unfold M64; lia). lia.
  + rewrite P16. reflexivity.
Qed.
(* inside the Sections: the Section hypotheses as its assumptions *)
About fr_sl. Print Assumptions fr_sl.
End e.
End f.
End d.
About fr_sl. Print Assumptions fr_sl.
