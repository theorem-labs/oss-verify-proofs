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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 430 of its 485 lines of code are new or changed and 398 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_FRONT, the call pieces of the line head (MF-CUTS-A.md section 4;
   lib/A/Prog/m_file_s_front_m.v's points):
     fr_head  HEAD 0x860d0 `li a1,10; mv a0,s11; jal` the strchr wrapper (trampoline 0x43a28, the interceptor-layer owner's row 6
              RtSeg.astrchr_realizes): back at SC 0x860dc with a0 = the line's '\n' or 0 (fr_nl);
     fr_sc    SC 0x860dc `mv s4,a0; mv s7,a0; bnez a0`: a '\n' goes to E 0x860f4 (s7 = s4 = p + L); none
              `mv a0,s11; jal` the strlen wrapper (trampoline 0x43a0c, row 16 RtString.astrlen_realizes): back at
              SL 0x860f0 with a0 = |rest|, s4 = 0;
     fr_sl    SL 0x860f0 `add s7,s11,a0`: at E with s7 = p + |rest| = p + L (no '\n': the line is the whole text left).
   Each run is over a state of the registers alone (no region: the three pieces read and store no byte themselves),
   so the head's facts cross it by fr_ctx_run. A wrapper call is the step of PaArt.v's aj_art_at (as fuzz_command's
   check_reply_s2.v:589-612 at 501c0d516c69 steps memchr), at sp = s1 with the wrapper's window below s1 (2 * ESTACK
   for strchr, ESTACK for strlen); its premises come from the text facts the head keeps (m_file_pre's text, the text's
   heap block, the band room amem_range t (|s| + 8)), and the head's facts cross it by m_file_k.v's mf_keep_art0.
   The FRONT call sub-lane of the G2 walk owner's G2. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP00 YP0i YP0j YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0n YI0s YI16 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList SegAddr SegPa.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaLibG PaLibH PaSB PaDenot PaLibF PaCall PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_s_front_mdl m_file_s_front_m.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_k m_file_sd m_file_s_front_g.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* the strchr wrapper's answer as the line split: a0 = fr_nl p rest *)
Lemma fr_nl_post : forall p rest (r : bvmap 5 word),
  (getr r 10 = w64 0 /\ ~ In 10 rest) \/ (exists j, RtSeg.first_at rest 10 j /\ getr r 10 = w64 (p + Z.of_nat j)) ->
  getr r 10 = w64 (fr_nl p rest).
Proof.
intros p rest r [[H0 Hn] | (j & (Hj & Hnj & Hf) & Hr)].
- destruct (fr_noNL rest Hn) as (_ & _ & E). unfold fr_nl. rewrite E. exact H0.
- destruct (fr_firstNL rest j Hj Hnj Hf) as (_ & _ & L & E). unfold fr_nl. rewrite E, L. exact Hr.
Qed.
(* a callee-saved register across a wrapper (fuzz_catalogue_rowA_k.v fcr_pres_reg) *)
Lemma fr_pres : forall (regs regs' : bvmap 5 word) (r : bv 5), aregs_preserved regs regs' ->
  acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. rewrite <- (Z_to_bv_bv_unsigned 5 r). exact (HP _ Hr). Qed.
(* a register whose symbolic value has unsigned value z *)
Lemma fr_reg_U : forall E e (rg : bvmap 5 word) (r : bv 5) z, getr rg r = sv_denot E e -> U E e = z ->
  0 <= z < 2 ^ 64 -> getr rg r = w64 z.
Proof. intros E e rg r z H HU Hz. rewrite H. apply bv_eq. unfold w64. rewrite unsigned_lit_small by exact Hz. exact HU. Qed.
Definition fr_facts0 : facts := mkFacts [] [] [].

Ltac fr_rawreg HS r H :=
  lazymatch type of HS with
  | st_ok_pi ?segs ?vl ?Ex ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_pi_restrict_reg Hh Ex ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst extK] in H
  | st_ok ?segs ?Ex ?ss (restrict ?Hh ?ms) =>
    pose proof (st_ok_restrict_reg segs Hh Ex ss ms r HS) as H;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in H;
    cbn [ms_regs restrict mkst extK] in H
  end.
Ltac fr_csav := unfold acallee_saved;
  lazymatch goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in
    change (bv_unsigned x) with z end; lia.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(* a state of the registers alone at listing offset pc *)
Lemma fr_seed0 : forall regs1 memc pc (Wc : world SEGS),
  st_ok_pi SEGS VAL (Eimg (Ereg regs1 [])) (mkSS pc sr_atoms [] None fr_facts0)
    (restrict (w_H Wc) (mkst regs1 (Z_to_bv 64 (BASE + pc)) memc (seg_rom SEGS))).
Proof.
intros regs1 memc pc Wc. rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- exact I.
- unfold facts_ok, fr_facts0. cbn. repeat constructor.
Qed.
Lemma fr_HAE : forall regs1, env_agree 32 (Ereg regs1 []) (Eimg (Ereg regs1 [])).
Proof. intros regs1. split; [intros k Hk; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* the return address a jal leaves: the code pointer atom at offset k *)
Lemma fr_ra : forall E (rg : bvmap 5 word) k, img_env VAL A_LIM E -> getr rg 1 = sv_denot E (SOff A_TEXT k) ->
  getr rg 1 = Z_to_bv 64 (BASE + k).
Proof. intros E rg k HE H. rewrite H. apply codeptr_val. exact HE. Qed.
(* an atom of a register at a later environment of the run (its fresh atoms are 1024 and up) *)
Lemma fr_ew_reg : forall Ex regs1 (k : nat) (r : bv 5) z,
  (forall j, (j < 1024)%nat -> ew Ex j = ew (Eimg (Ereg regs1 [])) j) -> Z.of_nat k = bv_unsigned r -> (k < 32)%nat ->
  getr regs1 r = w64 z -> 0 <= z < 2 ^ 64 -> bv_unsigned (ew Ex k) = z.
Proof.
intros Ex regs1 k r z HEx Hk Hk32 Hr Hz. rewrite HEx by lia. rewrite Eimg_low by (unfold A_TEXT; lia).
rewrite (ew_Ereg_nat regs1 [] k r Hk), Hr. unfold w64. apply unsigned_lit_small. exact Hz.
Qed.
Lemma fr_U_reg : forall Ex regs1 (k : nat) (r : bv 5) z,
  (forall j, (j < 1024)%nat -> ew Ex j = ew (Eimg (Ereg regs1 [])) j) -> Z.of_nat k = bv_unsigned r -> (k < 32)%nat ->
  getr regs1 r = w64 z -> 0 <= z < 2 ^ 64 -> U Ex (SOff k 0) = z.
Proof.
intros Ex regs1 k r z HEx Hk Hk32 Hr Hz. apply U_atom; [|exact Hz].
rewrite HEx by lia. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs1 [] k r Hk). exact Hr.
Qed.

Section e.
Variable B : asyms.
Hypothesis TL : PALib B.
Hypothesis ASTRCHR : forall fx0 : YK11.FPState, @RtSeg.astrchr_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strchr).
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(* the text left at the head as the wrappers take it: the C string zb rest at p, its NUL's word visible, the band
   room past it, inside the text's heap block *)
Lemma fr_str : forall v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n,
  fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n ->
  astr_at SEGS Wc memc p (seg_spec.zb rest) /\ map (fun b : byte => bv_unsigned b) (seg_spec.zb rest) = rest /\
  astr_len (seg_spec.zb rest) = Z.of_nat (length rest) /\
  atail_vis SEGS Wc memc (p + Z.of_nat (length rest)) /\ amem_range p (Z.of_nat (length rest) + 8) /\
  (exists bb bm, In (bb, bm) (ablocks B lyc Sc) /\ bb <= p /\ p + (Z.of_nat (length rest) + 1) <= bb + bm).
Proof.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX.
destruct CTX as (CX & LS & FRM & CORE & CELLS & RA & R24 & Hn & Hne & LOOP & EQ & R21).
pose proof LOOP as (Hlr & _ & Hp & (STRZ & TAIL) & _).
destruct (sa_strz_bytes SEGS (w_H Wc) memc p rest STRZ) as (BY & NZ & ZZ).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MP & _).
pose proof MP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TAMR & _).
split; [split; [exact BY | exact NZ]|].
split; [exact ZZ|].
split; [unfold astr_len, seg_spec.zb; rewrite length_map; reflexivity|].
split; [exact TAIL|].
split; [unfold amem_range in *; lia|].
destruct (mf_txt_heap_now B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as (bb & bm & Hin & Hb1 & Hb2).
exists bb, bm. split; [exact Hin|]. lia.
Qed.

(* the head's facts across a wrapper called at sp = s1 that writes only its window [s1 - stk, s1) *)
Lemma fr_art_ctx : forall v lyc Sc Wc rg mm mdq pos mcc cur line p rest n regs2 mem2 md2 stk,
  fr_ctx B v lyc Sc Wc rg mm mdq pos mcc cur line p rest n ->
  ajournal SEGS B SegInstA.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
    (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc mem2 md2 0 ->
  aregs_preserved rg regs2 -> 0 <= stk <= 2 * ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - stk <= a < mf_s1 (mv_sp v)) -> rdW Wc mem2 a = rdW Wc mm a) ->
  fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n.
Proof.
intros v lyc Sc Wc rg mm mdq pos mcc cur line p rest n regs2 mem2 md2 stk CTX HJ2 HP Hstk KW.
destruct CTX as (CX & LS & FRM & CORE & CELLS & RA & R24 & Hn & Hne & LOOP & EQ & R21).
pose proof (mf_s1_facts B v CX) as (Hs1 & _ & Hc).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
destruct (mf_keep_art0 B v lyc Sc Wc rg mm mdq pos MF_LOW_OFF mcc cur regs2 mem2 md2 (mf_s1 (mv_sp v) - stk)
  (mf_s1 (mv_sp v)) CX CORE CELLS RA HJ2 HP ltac:(lia) ltac:(lia) KW) as (C1 & C2 & C3 & _ & C5).
refine (conj CX (conj LS (conj FRM (conj C1 (conj C2 (conj C3 (conj _ (conj Hn (conj Hne
  (conj (C5 _ _ _ _ _ LOOP) (conj EQ _))))))))))).
- rewrite (fr_pres rg regs2 24%bv HP ltac:(fr_csav)). exact R24.
- rewrite (fr_pres rg regs2 21%bv HP ltac:(fr_csav)). exact R21.
Qed.

(* the numbers of a wrapper call at a point of the segment: sp = s1 = sp0 + o, o = -288 or -304 *)
Lemma fr_call_nums : forall v lyc pos rg, mf_cx B v -> mf_regs_at B v lyc pos rg ->
  spZ rg = mv_sp v + (mf_s1 (mv_sp v) - mv_sp v) /\ (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0 /\
  -304 <= mf_s1 (mv_sp v) - mv_sp v <= -288 /\ alloc_ceiling + SegInstA.STK_m_file <= mv_sp v.
Proof.
intros v lyc pos rg CX RA.
pose proof (mf_sp_at B v lyc pos rg CX RA) as Hsp1.
pose proof (mf_s1_facts B v CX) as (Hs1 & _ & Hc).
split; [lia|]. split; [|split; [lia | exact Hc]].
destruct Hs1 as [E | E]; rewrite E.
- replace (mv_sp v - 288 - mv_sp v) with (-288) by lia. reflexivity.
- replace (mv_sp v - 304 - mv_sp v) with (-304) by lia. reflexivity.
Qed.

(* 0x860d8 / the strchr wrapper: strchr(p, '\n') returns to raw with a0 = fr_nl p rest, the head's facts kept *)
Lemma fr_call_strchr : forall v lyc Sc Wc rg mm mdq pos mcc cur line p rest n raw,
  fr_ctx B v lyc Sc Wc rg mm mdq pos mcc cur line p rest n ->
  getr rg 10 = w64 p -> getr rg 11 = w64 10 -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
     aregs_preserved rg regs2 -> getr regs2 10 = w64 (fr_nl p rest) ->
     SRr SEGS Wc (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) (MF_POST B v)) ->
  SRr SEGS Wc (mkCfg (mkst rg (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_strchr)) mm (seg_rom SEGS)) mdq)
    (MF_POST B v).
Proof.
intros v lyc Sc Wc rg mm mdq pos mcc cur line p rest n raw CTX R10 R11 R1 HRA K.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & RA & R24 & Hn & Hne & LOOP & EQ & R21).
pose proof CORE as (HJ & _).
pose proof (proj1 HJ) as HAR.
pose proof RA as (R2 & R3 & R4 & _).
destruct (fr_call_nums v lyc pos rg CX RA) as (Hsp & Ho16 & Ho & Hc).
pose proof (mf_sp_at B v lyc pos rg CX RA) as Hsp1.
destruct (fr_text_facts B v lyc Sc Wc rg mm mdq pos mcc cur line p rest n CTX) as (Hp1 & Hp2 & _ & _ & _).
destruct (fr_str v lyc Sc Wc rg mm mdq pos mcc cur line p rest n CTX) as (STR & ZR & SL & TV & AMR & (bb & bm & Hin & Hb1 & Hb2)).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) (2 * ESTACK) (fun _ => False)
    (SIGMA SS___interceptor_trampoline_strchr) Wc rg mm _ _ _ _ _ _ _ _ _ lyc Sc mdq 0 (mf_s1 (mv_sp v) - mv_sp v) raw
    (fun regs' _ => (getr regs' 10 = w64 0 /\ ~ In 10 (map (fun b : byte => bv_unsigned b) (seg_spec.zb rest))) \/
       (exists j, RtSeg.first_at (map (fun b : byte => bv_unsigned b) (seg_spec.zb rest)) 10 j /\
          getr regs' 10 = w64 (p + Z.of_nat j)))
    HJ Hsp Ho16).
  - lia.
  - lia.
  - lia.
  - exact R1.
  - intros a [].
  - apply (ASTRCHR fx lyc Sc Wc rg mm mdq p 10 (seg_spec.zb rest)).
    + apply (ecall_pre_stk_at SEGS B (2 * ESTACK) SegInstA.STK_m_file (mv_sp v) _ _ _ _ _ _ _ lyc Sc Wc mm mdq 0 rg
        (mf_s1 (mv_sp v) - mv_sp v) HJ Hsp Ho16); [lia | lia | lia | rewrite R1; exact HRA | exact R3 | exact R4].
    + exact R10.
    + exact R11.
    + lia.
    + lia.
    + exact STR.
    + rewrite SL. apply (aread_ok_of_block SEGS B LAWS (2 * ESTACK) lyc Sc Wc rg mm mdq bb bm p
        (Z.of_nat (length rest) + 1) HAR Hin); [lia | lia | lia | rewrite Hsp1; lia].
    + rewrite SL. exact AMR.
    + rewrite SL. exact TV.
    + exact (mf_rom_now B v lyc Sc Wc mm mdq pos MF_LOW_OFF mcc CX CORE). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & A0 & HK).
rewrite ZR in A0.
apply (K regs2 mem2 md2).
- apply (fr_art_ctx v lyc Sc Wc rg mm mdq pos mcc cur line p rest n regs2 mem2 md2 (2 * ESTACK) CTX HJ2 HP2
    ltac:(lia)).
  intros a Ha Hna. apply HK; [exact Ha | lia | intros []].
- exact HP2.
- exact (fr_nl_post p rest regs2 A0).
Qed.

(* 0x860ec / the strlen wrapper: strlen(p) returns to raw with a0 = |rest|, the head's facts kept *)
Lemma fr_call_strlen : forall v lyc Sc Wc rg mm mdq pos mcc cur line p rest n raw,
  fr_ctx B v lyc Sc Wc rg mm mdq pos mcc cur line p rest n ->
  getr rg 10 = w64 p -> getr rg 1 = raw -> YK0s.ret_ok raw ->
  (forall regs2 mem2 md2, fr_ctx B v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest n ->
     aregs_preserved rg regs2 -> getr regs2 10 = w64 (Z.of_nat (length rest)) ->
     SRr SEGS Wc (mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2) (MF_POST B v)) ->
  SRr SEGS Wc (mkCfg (mkst rg (Z_to_bv 64 (SIGMA SS___interceptor_trampoline_strlen)) mm (seg_rom SEGS)) mdq)
    (MF_POST B v).
Proof.
intros v lyc Sc Wc rg mm mdq pos mcc cur line p rest n raw CTX R10 R1 HRA K.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & RA & R24 & Hn & Hne & LOOP & EQ & R21).
pose proof CORE as (HJ & _).
pose proof (proj1 HJ) as HAR.
pose proof RA as (R2 & R3 & R4 & _).
destruct (fr_call_nums v lyc pos rg CX RA) as (Hsp & Ho16 & Ho & Hc).
pose proof (mf_sp_at B v lyc pos rg CX RA) as Hsp1.
destruct (fr_text_facts B v lyc Sc Wc rg mm mdq pos mcc cur line p rest n CTX) as (Hp1 & Hp2 & _ & _ & _).
destruct (fr_str v lyc Sc Wc rg mm mdq pos mcc cur line p rest n CTX) as (STR & ZR & SL & TV & AMR & (bb & bm & Hin & Hb1 & Hb2)).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
eapply SRr_bind.
{ apply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) ESTACK (fun _ => False)
    (SIGMA SS___interceptor_trampoline_strlen) Wc rg mm _ _ _ _ _ _ _ _ _ lyc Sc mdq 0 (mf_s1 (mv_sp v) - mv_sp v) raw
    (fun regs' _ => getr regs' 10 = w64 (astr_len (seg_spec.zb rest)))
    HJ Hsp Ho16).
  - lia.
  - lia.
  - lia.
  - exact R1.
  - intros a [].
  - apply (ASTRLEN fx lyc Sc Wc rg mm mdq p (seg_spec.zb rest)).
    + apply (ecall_pre_stk_at SEGS B ESTACK SegInstA.STK_m_file (mv_sp v) _ _ _ _ _ _ _ lyc Sc Wc mm mdq 0 rg
        (mf_s1 (mv_sp v) - mv_sp v) HJ Hsp Ho16); [lia | lia | lia | rewrite R1; exact HRA | exact R3 | exact R4].
    + exact R10.
    + lia.
    + exact STR.
    + rewrite SL. apply (aread_ok_of_block SEGS B LAWS ESTACK lyc Sc Wc rg mm mdq bb bm p
        (Z.of_nat (length rest) + 1) HAR Hin); [lia | lia | lia | rewrite Hsp1; lia].
    + rewrite SL. exact TV.
    + exact (mf_rom_now B v lyc Sc Wc mm mdq pos MF_LOW_OFF mcc CX CORE). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & A0 & HK).
rewrite SL in A0.
apply (K regs2 mem2 md2).
- apply (fr_art_ctx v lyc Sc Wc rg mm mdq pos mcc cur line p rest n regs2 mem2 md2 ESTACK CTX HJ2 HP2 ltac:(lia)).
  intros a Ha Hna. apply HK; [exact Ha | lia | intros []].
- exact HP2.
- exact A0.
Qed.

(* the run tactics over a state of the registers alone (m_file_s_front_cl.v's, with no region) *)
Ltac fr_awr :=
  lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?fr0x ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok sg bb Ex rs' stkx spx fpx b0x bcx fr0x lyx ownx) end;
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.
Ltac fr_meq :=
  lazymatch goal with
  | HFr : frame_of _ ?rs (mrestrict ?H ?m0) (mrestrict ?H ?m1),
    MEQ : forall a, aview _ _ ?m0 a = aview _ _ ?mc a |- _ =>
    let M := fresh "M" in
    pose proof (fr_aview_ro _ rs H m0 m1 HFr ltac:(vm_compute; reflexivity)) as M;
    let MEQ' := fresh "MEQ" in
    assert (MEQ' : forall a, aview SEGS H m1 a = aview SEGS H mc a) by (intros a; rewrite M; apply MEQ);
    clear M MEQ HFr; rename MEQ' into MEQ end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac fr_run :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_tok RUN HS HJ SHOK Bspan; try (fr_awr; fail); fr_meq end.
Ltac fr_runto stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    SHOK : sh_ok _ _ _ _ _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK Bspan stop; try (fr_awr; fail); fr_meq end.
Ltac fr_branch := lazymatch goal with HS : st_ok_pi _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
  psrr_branch_tok RUN BR HS SHOK Bspan end.
(* the registers of l the run left as they were (a stop inside the listing, or at a wrapper's entry) *)
Ltac fr_kept regs0 l HK :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ecur _ (restrict _ _) |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs0 []) Ecur) by (env_agree_chain (fr_HAE regs0));
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs0 _ l HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2
  | HS : st_ok _ ?Ecur _ (restrict _ _) |- _ =>
    let HAE2 := fresh "HAE2" in
    assert (HAE2 : env_agree 32 (Ereg regs0 []) Ecur) by (env_agree_chain (fr_HAE regs0));
    pose proof (regs_kept_of_st_ok SEGS _ _ _ regs0 _ l HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK; clear HAE2
  end.
(* the environment of the run's state agrees with the start's below the fresh atoms *)
Ltac fr_ux regs0 HEx :=
  lazymatch goal with
  | HS : st_ok_pi _ _ ?Ex _ _ |- _ =>
    assert (HEx : forall k, (k < 1024)%nat -> ew Ex k = ew (Eimg (Ereg regs0 [])) k)
      by (intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)
  | HS : st_ok _ ?Ex _ _ |- _ =>
    assert (HEx : forall k, (k < 1024)%nat -> ew Ex k = ew (Eimg (Ereg regs0 [])) k)
      by (intros ?k ?Hk; repeat rewrite ew_ewset_other by lia; reflexivity)
  end.
(* fr_ctx at a stop of a run that stored nothing *)
Ltac fr_ctx_stop CTX HJ MEQ HK R19 :=
  eapply fr_ctx_run; [exact CTX | exact HJ | exact MEQ | intros ?r ?Hr; apply HK; apply in_or_app; left; assumption
    | rewrite (HK 19%bv ltac:(cbv; tauto)); exact R19].

(* ============================== HEAD 0x860d0: strchr(p, '\n') ============================== *)
Lemma fr_head : forall n, FR_SC_stmt B n -> MF_HEAD_stmt B (S n).
Proof.
intros n HSC v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CX LS FRM CORE CELLS RA R24 Hn Hne LOOP EQ R27 R21 R22.
assert (CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n).
{ refine (conj CX (conj LS (conj FRM (conj CORE (conj CELLS (conj RA (conj R24 (conj _ (conj Hne (conj LOOP
    (conj EQ R21))))))))))). lia. }
pose proof CORE as (HJ & _).
pose proof RA as (_ & _ & _ & _ & _ & _ & R19 & _).
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (Hp1 & Hp2 & _ & _ & _).
pose proof alloc_ceiling_lt as HAC.
pose proof (fr_seed0 regs1 memc MF_HEAD Wc) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
assert (SHOK : sh_ok SEGS (SOff 18 0) [] (Eimg (Ereg regs1 [])) (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
clear CX LS FRM CORE CELLS RA R24 Hn Hne LOOP EQ R21.
unfold mf_at.
fr_run.
fr_kept regs1 (FR_KEPT ++ [19; 22; 27]%bv) HK.
fr_ux regs1 HEx.
fr_rawreg HS (10%bv : bv 5) Q10. fr_rawreg HS (11%bv : bv 5) Q11. fr_rawreg HS (1%bv : bv 5) Q1.
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  apply (fr_call_strchr v lyc Sc Wc rg mm mdq pos mcc cur line p rest n (Z_to_bv 64 (BASE + FR_SC))) end.
- fr_ctx_stop CTX HJ MEQ HK R19.
- apply (fr_reg_U _ _ _ _ _ Q10); [|lia].
  apply (fr_U_reg _ regs1 27 27%bv p HEx eq_refl); [lia | exact R27 | lia].
- apply (fr_reg_U _ _ _ _ _ Q11); [apply U_lit; lia | lia].
- exact (fr_ra _ _ _ HEI Q1).
- apply ret_ok_codeptr_v; [unfold FR_SC, AF_m_file; lia | reflexivity].
- intros regs2 mem2 md2 CTX2 HP2 A0. apply (HSC v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest CTX2).
  + rewrite (fr_pres _ _ 27%bv HP2 ltac:(fr_csav)), (HK 27%bv ltac:(cbv; tauto)). exact R27.
  + rewrite (fr_pres _ _ 22%bv HP2 ltac:(fr_csav)), (HK 22%bv ltac:(cbv; tauto)). exact R22.
  + exact A0.
Qed.

(* ============================== SC 0x860dc: the branch on a0; strlen(p) ============================== *)
Section sc.
Variables (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HE : FR_E_stmt B n.
Hypothesis HSL : FR_SL_stmt B n.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis R27 : getr regs1 27 = w64 p.
Hypothesis R22 : getr regs1 22 = w64 line.
Hypothesis R10 : getr regs1 10 = w64 (fr_nl p rest).

Lemma sc_nl : 0 <= fr_nl p rest < 2 ^ 64 /\ 4096 <= p /\ p + Z.of_nat (length (mf_line rest)) < 2 ^ 64 /\
  (fr_nl p rest <> 0 -> fr_nl p rest = p + Z.of_nat (length (mf_line rest))) /\
  (fr_nl p rest = 0 -> existsb (fun b => b =? NL) rest = false).
Proof.
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (H1 & H2 & _ & _ & _).
pose proof (fr_line_len rest) as HLL. pose proof alloc_ceiling_lt as HAC.
unfold fr_nl. destruct (existsb (fun b => b =? NL) rest) eqn:E.
- split; [lia|]. split; [lia|]. split; [lia|]. split; [intros _; reflexivity | intros H0; lia].
- split; [lia|]. split; [lia|]. split; [lia|]. split; [intros H0; exfalso; apply H0; reflexivity | intros _; reflexivity].
Qed.

Lemma sc_step : mf_at B v Wc regs1 memc mdc FR_SC.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _ & RA & _).
pose proof RA as (_ & _ & _ & _ & _ & _ & R19 & _).
pose proof sc_nl as (N1 & N2 & N3 & N4 & N5).
pose proof (fr_seed0 regs1 memc FR_SC Wc) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
assert (SHOK : sh_ok SEGS (SOff 18 0) [] (Eimg (Ereg regs1 [])) (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
clear RA.
unfold mf_at.
fr_run; fr_branch.
- (* bnez taken: a '\n' at p + L; s7 = s4 = a0 *)
  fr_ux regs1 HEx0.
  lazymatch goal with Hc : branch_taken _ _ _ = true |- _ =>
    rewrite branch_ne_U, (fr_U_reg _ regs1 10 10%bv (fr_nl p rest) HEx0 eq_refl ltac:(lia) R10 N1) in Hc;
    rewrite U_lit in Hc by lia; apply Bool.negb_true_iff, Z.eqb_neq in Hc; rename Hc into HNZ end.
  clear HEx0.
  fr_runto FR_E.
  fr_kept regs1 (FR_KEPT ++ [19; 22; 27]%bv) HK.
  fr_ux regs1 HEx.
  fr_rawreg HS (23%bv : bv 5) Q23. fr_rawreg HS (20%bv : bv 5) Q20.
  pmkst HS.
  eapply HE.
  + fr_ctx_stop CTX HJ MEQ HK R19.
  + rewrite (HK 27%bv ltac:(cbv; tauto)). exact R27.
  + rewrite (HK 22%bv ltac:(cbv; tauto)). exact R22.
  + apply (fr_reg_U _ _ _ _ _ Q23); [|lia].
    rewrite (fr_U_reg _ regs1 10 10%bv (fr_nl p rest) HEx eq_refl ltac:(lia) R10 N1). exact (N4 HNZ).
  + apply (fr_reg_U _ _ _ _ _ Q20); [|exact N1].
    exact (fr_U_reg _ regs1 10 10%bv (fr_nl p rest) HEx eq_refl ltac:(lia) R10 N1).
- (* not taken: no '\n'; strlen(p) *)
  fr_ux regs1 HEx0.
  lazymatch goal with Hc : branch_taken _ _ _ = false |- _ =>
    rewrite branch_ne_U, (fr_U_reg _ regs1 10 10%bv (fr_nl p rest) HEx0 eq_refl ltac:(lia) R10 N1) in Hc;
    rewrite U_lit in Hc by lia; apply Bool.negb_false_iff, Z.eqb_eq in Hc; rename Hc into HZ end.
  clear HEx0.
  fr_run.
  fr_kept regs1 (FR_KEPT ++ [19; 22; 27]%bv) HK.
  fr_ux regs1 HEx.
  fr_rawreg HS (10%bv : bv 5) Q10. fr_rawreg HS (20%bv : bv 5) Q20. fr_rawreg HS (1%bv : bv 5) Q1.
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    apply (fr_call_strlen v lyc Sc Wc rg mm mdq pos mcc cur line p rest n (Z_to_bv 64 (BASE + FR_SL))) end.
  + fr_ctx_stop CTX HJ MEQ HK R19.
  + apply (fr_reg_U _ _ _ _ _ Q10); [|lia].
    apply (fr_U_reg _ regs1 27 27%bv p HEx eq_refl); [lia | exact R27 | lia].
  + exact (fr_ra _ _ _ HEI Q1).
  + apply ret_ok_codeptr_v; [unfold FR_SL, AF_m_file; lia | reflexivity].
  + intros regs2 mem2 md2 CTX2 HP2 A0. apply (HSL v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest CTX2).
    * rewrite (fr_pres _ _ 27%bv HP2 ltac:(fr_csav)), (HK 27%bv ltac:(cbv; tauto)). exact R27.
    * rewrite (fr_pres _ _ 22%bv HP2 ltac:(fr_csav)), (HK 22%bv ltac:(cbv; tauto)). exact R22.
    * exact (N5 HZ).
    * rewrite (fr_pres _ _ 20%bv HP2 ltac:(fr_csav)). apply (fr_reg_U _ _ _ _ _ Q20); [|lia].
      rewrite (fr_U_reg _ regs1 10 10%bv (fr_nl p rest) HEx eq_refl ltac:(lia) R10 N1). exact HZ.
    * exact A0.
Qed.
End sc.

Lemma fr_sc : forall n, FR_E_stmt B n -> FR_SL_stmt B n -> FR_SC_stmt B n.
Proof.
intros n HE HSL v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX R27 R22 R10.
eapply sc_step; eassumption.
Qed.

(* ============================== SL 0x860f0: s7 = p + |rest| ============================== *)
Section sl.
Variables (n : nat) (v : mfv) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (regs1 : bvmap 5 word)
  (memc : word -> option byte) (mdc : Model) (pos : Z) (mcc : mconf) (cur : option nat) (line p : Z)
  (rest : list Z).
Hypothesis HE : FR_E_stmt B n.
Hypothesis CTX : fr_ctx B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n.
Hypothesis R27 : getr regs1 27 = w64 p.
Hypothesis R22 : getr regs1 22 = w64 line.
Hypothesis HNN : existsb (fun b => b =? NL) rest = false.
Hypothesis R20 : getr regs1 20 = w64 0.
Hypothesis R10 : getr regs1 10 = w64 (Z.of_nat (length rest)).

Lemma sl_step : mf_at B v Wc regs1 memc mdc FR_SL.
Proof.
pose proof CTX as (_ & _ & _ & (HJ & _) & _ & RA & _).
pose proof RA as (_ & _ & _ & _ & _ & _ & R19 & _).
destruct (fr_text_facts B v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest n CTX) as (Hp1 & Hp2 & _ & _ & _).
pose proof alloc_ceiling_lt as HAC.
assert (ML : mf_line rest = rest).
{ destruct (fr_next_cases p rest) as [[E1 _] | (_ & _ & ML)]; [rewrite HNN in E1; discriminate | exact ML]. }
pose proof (fr_seed0 regs1 memc FR_SL Wc) as HS.
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs1 []))) by apply Eimg_env.
assert (SHOK : sh_ok SEGS (SOff 18 0) [] (Eimg (Ereg regs1 [])) (mrestrict (w_H Wc) memc)) by constructor.
assert (MEQ : forall a, aview SEGS (w_H Wc) memc a = aview SEGS (w_H Wc) memc a) by reflexivity.
clear RA.
unfold mf_at.
fr_runto FR_E.
fr_kept regs1 (FR_KEPT ++ [19; 20; 22; 27]%bv) HK.
fr_ux regs1 HEx.
fr_rawreg HS (23%bv : bv 5) Q23.
pmkst HS.
eapply HE.
- fr_ctx_stop CTX HJ MEQ HK R19.
- rewrite (HK 27%bv ltac:(cbv; tauto)). exact R27.
- rewrite (HK 22%bv ltac:(cbv; tauto)). exact R22.
- apply (fr_reg_U _ _ _ _ _ Q23); [|rewrite ML; lia].
  pose proof (fr_ew_reg _ regs1 27 27%bv p HEx eq_refl ltac:(lia) R27 ltac:(lia)) as E27.
  pose proof (fr_ew_reg _ regs1 10 10%bv _ HEx eq_refl ltac:(lia) R10 ltac:(lia)) as E10.
  rewrite U_add_off_atom by (rewrite ?E27, ?E10; unfold M64; lia).
  rewrite E27, E10, ML. lia.
- rewrite (HK 20%bv ltac:(cbv; tauto)), R20. unfold fr_nl. rewrite HNN. reflexivity.
Qed.
End sl.

Lemma fr_sl : forall n, FR_E_stmt B n -> FR_SL_stmt B n.
Proof.
intros n HE v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX R27 R22 HNN R20 R10.
eapply sl_step; eassumption.
Qed.
End e.
End f.
End d.

About fr_head.
Print Assumptions fr_head.
About fr_sc.
Print Assumptions fr_sc.
About fr_sl.
Print Assumptions fr_sl.
