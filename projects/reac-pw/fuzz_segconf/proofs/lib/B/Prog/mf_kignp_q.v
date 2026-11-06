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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v; 127 of its 183 lines of code are new or changed and 397 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3, twin 80e82127e8ca; 0x86140), segment S_MF_KIGNP:
   the two state moves and the two ieq call steps its pieces share. A walk lane of the image-B m_file-family owner's G2B.
   proves no function (kind: segment lemma of m_file's walk: S_MF_KIGNP's shared steps).

   - ki_kbase_move / ki_vbase_move: the K state (mf_kignp_m.v ki_kbase / ki_vbase) after a run that changed no
     byte (the seed's write windows empty, mf_kignp_c.v ki_ro_frame) and left the registers the state names, at the
     run's memory and registers (m_file_k.v mf_keep_run0, m_file_iq.v iq_val_keep for the scratch cells).
   - ki_ieq_k / ki_ieq_v: ieq(k, kl, x) (0x86978) and ieq(v, vl, x) (0x86994, 0x869b0, 0x869f4, 0x86a0c) from
     ieq's entry (the `jal` executed) at the K state: m_file_iq.v mf_ieq_call (the owner's shared step, its KCHAIN /
     KROD / KLIT given by m_file_k.v mf_chain / mf_rod_now RELRO / mf_lit_now), then the K state again at the
     return, with a0 = b2z (ieq k x) or b2z (ieq vv x); the scratch cells 208(s1) / 192(s1) lie above s1, outside
     ieq's window [s1 - STK_ieq, s1) (ki_slot_keep).
   Section hypotheses: RELRO (m_file_k.v's), IEQ (the image-B m_file segment table's ieq row). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_iq ieq_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_kignp_t mf_kignp_m mf_kignp_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the registers a K state names: mf_regs_at's eleven, s5 = kl, s10 = vl, s11 = line + 1 *)
Definition ki_kregs : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 22; 23; 24; 25; 21; 26; 27]%bv.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
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
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis RELRO : forall a, SegInstB.RLO_A <= a < SegInstB.RHI_A -> in_img SEGS a.
Hypothesis IEQ : forall fx0 : YK11.FPState,
  ieq_contract (fx := fx0) SEGS B (BASE + AF_ieq) SegInstB.STK_ieq SegInstB.RLO_A SegInstB.RHI_A.

(* s1's bounds: 0 <= s1, s1 + 216 <= 2 ^ 64 *)
Lemma ki_s1_range : forall v, mf_cx B v -> 0 <= mf_s1 (mv_sp v) /\ mf_s1 (mv_sp v) + 216 <= 2 ^ 47.
Proof.
intros v CX. destruct (mf_s1_facts B v CX) as (Hs1 & _ & Hc). destruct (mf_sp0 B v CX) as (_ & Hsp & _).
pose proof asan_consts as ((C1 & C2) & _).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hc.
destruct Hs1 as [E | E]; rewrite E; lia.
Qed.

(* mf_regs_at from the K state's register equalities *)
Lemma ki_regs_at_move : forall v lyc pos (regs1 rr : bvmap 5 word),
  mf_regs_at B v lyc pos regs1 -> (forall r : bv 5, In r ki_kregs -> getr rr r = getr regs1 r) ->
  mf_regs_at B v lyc pos rr.
Proof.
intros v lyc pos regs1 rr RA K.
apply (mf_regs_at_of B v lyc pos regs1 rr RA); apply K; unfold ki_kregs; cbn [In]; tauto.
Qed.

(* the value's state after a run that changed no byte *)
Lemma ki_vbase_move : forall n v lyc Sc Wc regs1 rr memc m' mdc md' pos mcc gi line p rest ov vl vv,
  ki_vbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ov vl vv ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc m' md' 0 ->
  (forall x, m' x = memc x) ->
  (forall r : bv 5, In r ki_kregs -> getr rr r = getr regs1 r) ->
  ki_vbase B n v lyc Sc Wc rr m' md' pos mcc gi line p rest ov vl vv.
Proof.
intros n v lyc Sc Wc regs1 rr memc m' mdc md' pos mcc gi line p rest ov vl vv VB HJ HM K.
destruct VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc m' a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HM; reflexivity).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) m' md' CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
destruct (ki_s1_range v CX) as (Hs0 & Hs1).
unfold ki_vbase.
refine (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj (ki_regs_at_move v lyc pos regs1 rr RA K)
  (conj Hn (conj Hr (conj (LPk _ _ _ _ _ LOOP) (conj V1 (conj V2 _))))))))))).
split; [unfold mf_slot in *; apply (iq_val_keep Wc Wc memc m'); [intros y Hy; apply EQV; lia | exact S192]|].
split; [rewrite (K 26%bv ltac:(unfold ki_kregs; cbn [In]; tauto)); exact R26|].
split; [rewrite (K 27%bv ltac:(unfold ki_kregs; cbn [In]; tauto)); exact R27|].
exact (NPk _ NP).
Qed.

(* the K state with the key after a run that changed no byte *)
Lemma ki_kbase_move : forall n v lyc Sc Wc regs1 rr memc m' mdc md' pos mcc gi line p rest ok kl ov vl k vv,
  ki_kbase B n v lyc Sc Wc regs1 memc mdc pos mcc gi line p rest ok kl ov vl k vv ->
  ajournal SEGS B SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc m' md' 0 ->
  (forall x, m' x = memc x) ->
  (forall r : bv 5, In r ki_kregs -> getr rr r = getr regs1 r) ->
  ki_kbase B n v lyc Sc Wc rr m' md' pos mcc gi line p rest ok kl ov vl k vv.
Proof.
intros n v lyc Sc Wc regs1 rr memc m' mdc md' pos mcc gi line p rest ok kl ov vl k vv KB HJ HM K.
destruct KB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & KV & S208 & R21 & S192 & R26 & R27 & NP).
assert (EQV : forall a, 0 <= a < 2 ^ 64 -> rdW Wc m' a = rdW Wc memc a)
  by (intros a _; apply aview_eq_of; unfold mrestrict; rewrite HM; reflexivity).
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) m' md' CX CORE CELLS HJ EQV)
  as (CORE' & CELLS' & NPk & LPk).
destruct (ki_s1_range v CX) as (Hs0 & Hs1).
unfold ki_kbase.
refine (conj CX (conj LS (conj FRM (conj CORE' (conj CELLS' (conj (ki_regs_at_move v lyc pos regs1 rr RA K)
  (conj Hn (conj Hr (conj (LPk _ _ _ _ _ LOOP) (conj KV _)))))))))).
split; [unfold mf_slot in *; apply (iq_val_keep Wc Wc memc m'); [intros y Hy; apply EQV; lia | exact S208]|].
split; [rewrite (K 21%bv ltac:(unfold ki_kregs; cbn [In]; tauto)); exact R21|].
split; [unfold mf_slot in *; apply (iq_val_keep Wc Wc memc m'); [intros y Hy; apply EQV; lia | exact S192]|].
split; [rewrite (K 26%bv ltac:(unfold ki_kregs; cbn [In]; tauto)); exact R26|].
split; [rewrite (K 27%bv ltac:(unfold ki_kregs; cbn [In]; tauto)); exact R27|].
exact (NPk _ NP).
Qed.

(* ieq(v, vl, x) from ieq's entry at the value's state: the value's state again at BASE + ret, a0 = b2z (ieq vv x) *)
Lemma ki_ieq_v : forall n v lyc Sc Wc (rr : bvmap 5 word) memc mdc pos mcc gi line p rest ov vl vv (ret : Z) x,
  ki_vbase B n v lyc Sc Wc rr memc mdc pos mcc gi line p rest ov vl vv ->
  getr rr 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 -> In x M_FILE_LITS ->
  getr rr 10 = w64 (p + Z.of_nat ov) -> getr rr 11 = w64 (Z.of_nat vl) ->
  getr rr 12 = w64 (SegInstB.seg_litA_fz x) ->
  (forall S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
    ki_vbase B n v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ov vl vv ->
    aregs_preserved rr regs2 -> getr regs2 10 = w64 (seg_spec.b2z (ieq vv x)) ->
    SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) (MF_POST B v)) ->
  SRr SEGS Wc (mkCfg (mkst rr (Z_to_bv 64 (BASE + AF_ieq)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros n v lyc Sc Wc rr memc mdc pos mcc gi line p rest ov vl vv ret x VB R1 Hret Hret2 HX R10 R11 R12 KC.
destruct VB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & V1 & V2 & S192 & R26 & R27 & NP).
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
pose proof (ki_line_le rest) as Hml.
destruct (ki_slice_facts B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) line p rest ov vl CX CORE LOOP
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite V2 in SB, SZ, SL.
destruct (ki_s1_range v CX) as (Hs0 & Hs1).
apply (mf_ieq_call B IEQ (mf_chain B) (mf_rod_now B RELRO) (mf_lit_now B) v lyc Sc Wc rr memc mdc pos MF_LOW_ON
  mcc (Some gi) line p rest (mf_next p rest) ret (p + Z.of_nat ov) (Z.of_nat vl) (seg_spec.zb vv) x
  CX LS CORE CELLS LOOP NP R2 R3 R4 R8 R1 Hret Hret2 HX R10 R11 R12 S0 SB SL SA SH).
intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
rewrite SZ in A02.
apply (KC S2 W2 regs2 mem2 md2); [|exact HP2 | exact A02].
unfold ki_vbase.
refine (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj (mf_regs_keep B v lyc pos rr regs2 RA HP2)
  (conj Hn (conj Hr (conj LOOP2 (conj V1 (conj V2 _))))))))))).
split; [exact (ki_slot_keep v Wc W2 memc mem2 _ 192 _ K2 Hs0 ltac:(lia) ltac:(lia) S192)|].
split; [transitivity (getr rr 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]|].
split; [transitivity (getr rr 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact R27]|].
exact NP2.
Qed.

(* ieq(k, kl, x) from ieq's entry at the K state with the key: that state again at BASE + ret, a0 = b2z (ieq k x) *)
Lemma ki_ieq_k : forall n v lyc Sc Wc (rr : bvmap 5 word) memc mdc pos mcc gi line p rest ok kl ov vl k vv (ret : Z) x,
  ki_kbase B n v lyc Sc Wc rr memc mdc pos mcc gi line p rest ok kl ov vl k vv ->
  getr rr 1 = Z_to_bv 64 (BASE + ret) -> 0 <= ret < 2 ^ 40 -> ret mod 2 = 0 -> In x M_FILE_LITS ->
  getr rr 10 = w64 (p + Z.of_nat ok) -> getr rr 11 = w64 (Z.of_nat kl) ->
  getr rr 12 = w64 (SegInstB.seg_litA_fz x) ->
  (forall S2 (W2 : world SEGS) (regs2 : bvmap 5 word) mem2 md2,
    ki_kbase B n v lyc S2 W2 regs2 mem2 md2 pos mcc gi line p rest ok kl ov vl k vv ->
    aregs_preserved rr regs2 -> getr regs2 10 = w64 (seg_spec.b2z (ieq k x)) ->
    SRr SEGS W2 (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + ret)) mem2 (seg_rom SEGS)) md2) (MF_POST B v)) ->
  SRr SEGS Wc (mkCfg (mkst rr (Z_to_bv 64 (BASE + AF_ieq)) memc (seg_rom SEGS)) mdc) (MF_POST B v).
Proof.
intros n v lyc Sc Wc rr memc mdc pos mcc gi line p rest ok kl ov vl k vv ret x KB R1 Hret Hret2 HX R10 R11 R12 KC.
destruct KB as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hr & LOOP & KV & S208 & R21 & S192 & R26 & R27 & NP).
pose proof KV as (KV1 & KV2 & KV3 & KV4).
pose proof RA as ((R2 & R3 & R4 & R8 & _) & _).
pose proof (ki_line_le rest) as Hml.
destruct (ki_slice_facts B v lyc Sc Wc memc mdc pos MF_LOW_ON mcc (Some gi) line p rest ok kl CX CORE LOOP
  ltac:(lia)) as (SB & SZ & SL & SA & SH & S0).
rewrite KV3 in SB, SZ, SL.
destruct (ki_s1_range v CX) as (Hs0 & Hs1).
apply (mf_ieq_call B IEQ (mf_chain B) (mf_rod_now B RELRO) (mf_lit_now B) v lyc Sc Wc rr memc mdc pos MF_LOW_ON
  mcc (Some gi) line p rest (mf_next p rest) ret (p + Z.of_nat ok) (Z.of_nat kl) (seg_spec.zb k) x
  CX LS CORE CELLS LOOP NP R2 R3 R4 R8 R1 Hret Hret2 HX R10 R11 R12 S0 SB SL SA SH).
intros S2 W2 regs2 mem2 md2 Hwle LS2 CORE2 CELLS2 LOOP2 NP2 HP2 A02 K2.
rewrite SZ in A02.
apply (KC S2 W2 regs2 mem2 md2); [|exact HP2 | exact A02].
unfold ki_kbase.
refine (conj CX (conj LS2 (conj FRM (conj CORE2 (conj CELLS2 (conj (mf_regs_keep B v lyc pos rr regs2 RA HP2)
  (conj Hn (conj Hr (conj LOOP2 (conj KV _)))))))))).
split; [exact (ki_slot_keep v Wc W2 memc mem2 _ 208 _ K2 Hs0 ltac:(lia) ltac:(lia) S208)|].
split; [transitivity (getr rr 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact R21]|].
split; [exact (ki_slot_keep v Wc W2 memc mem2 _ 192 _ K2 Hs0 ltac:(lia) ltac:(lia) S192)|].
split; [transitivity (getr rr 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact R26]|].
split; [transitivity (getr rr 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact R27]|].
exact NP2.
Qed.
End e.
End f.
End d.
