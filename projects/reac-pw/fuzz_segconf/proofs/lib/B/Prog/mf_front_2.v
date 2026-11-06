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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 266 of its 315 lines of code are new or changed and 404 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan-ubsan (image B, pin c3796c0b38f3), segment S_MF_FRONT of lib/B/Prog/m_file_m.v,
   piece 2 (sc, lib/B/Prog/mf_front_m.v): `fr_sc : FR_E_stmt B n -> FR_SL_stmt B n -> FR_SC_stmt B n`, the code back
   from strchr(p, '\n') (the neutral listing of m_file in image B lines 147-156), a0 = fr_nl p rest:
     0x86384 sd s10,176(s1)      176(s1) = p
     0x86388 beqz a0,863a4
   '\n' found (a0 <> 0, so the text left has a '\n' and a0 = p + L, L = |mf_line rest|):
     0x8638c sd a0,168(s1)       168(s1) = p + L
     0x86390 li a6,32
     0x86394 li a1,-1
     0x86398 beq a0,a1,86e84     the UBSan trap (pointer overflow of a0 + 1): mf_loop's sa_addr p (|rest| + 1)
                                 gives p + L + 1 <= p + |rest| + 1 <= 2^63, so a0 <> 2^64 - 1 and the branch to
                                 the unimp 0x86e84 is not taken
     0x8639c addi a2,a0,1        a2 = p + L + 1 = mf_next p rest (mf_front_mdl.v fr_next_cases)
     0x863a0 j 863c4             to FR_E
   no '\n' (a0 = 0: fr_nl p rest = 0 with p >= 4096, so existsb (=? NL) rest = false):
     0x863a4 mv a0,s10
     0x863a8 jal 43a98           strlen(p), the wrapper's contract RtString.astrlen_realizes (Section hypothesis
                                 STRLEN) stepped by mf_front_art.v fr_art_at; its premises: ecall_pre_stk_at at
                                 sp = s1, a0 = p > 0, the C string zb rest at p and its slack (mf_loop's sa_str by
                                 SegABase.v sa_strz_bytes), aread_ok of [p, p + |rest| + 1) inside the text's block
                                 (m_file_sd.v mf_txt_blk, PaArt.v aread_ok_of_block), the ROM view (m_file_k.v
                                 mf_rom_now); post a0 = |rest|; strlen writes only [s1 - ESTACK, s1)
   and back at 0x863ac = FR_SL. The cut facts cross the runs by mf_front_3.v fr_run_keep (the write window [168,
   184) of the frame cells) and the call by m_file_k.v mf_keep_art0; 176(s1) = p across the call by mf_val_keep.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtString.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import m_file_c m_file_m m_file_sd m_file_k.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import mf_front_mdl mf_front_m mf_front_art mf_front_3.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

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
Hypothesis VOBJS : seg_val_objs.
Hypothesis STRLEN : forall fx0 : YK11.FPState, @RtString.astrlen_realizes fx0 rc SEGS B (SIGMA SS___interceptor_trampoline_strlen).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma fr_sc : forall n, FR_E_stmt B n -> FR_SL_stmt B n -> FR_SC_stmt B n.
Proof.
intros n FE FSL. unfold FR_SC_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest CTX R26 R21 R20 R10.
pose proof CTX as (CX & LS & FRM & CORE & CELLS & RA & Hn & Hne & LOOP & EQ).
pose proof (mf_regs_base_of B v lyc pos regs1 RA) as RB.
pose proof RA as ((R2 & R3 & R4 & R8 & R9 & R18 & R23 & R24) & R19 & R22 & R25).
pose proof LOOP as (L1 & L2 & L3 & LSTR & LADDR & HCOK & _).
pose proof LADDR as (Hp0 & Hp63 & _).
pose proof (fr_line_len rest) as HLL.
destruct (mf_s1_facts B v CX) as (Hs1 & Hs1m & Hsp).
destruct (mf_sp0 B v CX) as (_ & Sp2 & Sp3).
assert (HSTK : SegInstB.STK_m_file = 8592) by (vm_compute; reflexivity). rewrite HSTK in Hsp.
pose proof (@YG0f.ASAN_CEIL_range rc) as ((CR1 & CR2) & _). unfold YG0f.ASAN_CEIL in CR1, CR2.
pose proof CORE as (HJ & HPerm & _).
pose proof HJ as (HAR & _).
destruct (mf_txt_blk B v Wc memc mcc cur line p rest CX LOOP) as (bt & mt & Hbt0 & Hbt1 & Hbt2).
assert (Hbt : In (bt, mt) (ablocks B lyc Sc)) by (apply (Permutation_in _ (Permutation_sym HPerm)); exact Hbt0).
destruct (al_blocks SEGS B LAWS _ _ _ _ _ bt mt HAR Hbt) as (_ & Bt4096 & Btceil & _).
assert (Hnl : 0 <= fr_nl p rest < 2 ^ 63) by (unfold fr_nl; destruct (existsb _ rest); lia).
pose proof (mf_cur_range B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur CX CORE HCOK) as Hcur.
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur 0 [] FR_SC false false [] false false [] false
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
(* the frame cells' window narrowed to 168(s1) and 176(s1), the cells this piece stores *)
pose proof (st_ok_pi_region_nth E _ _ 1 _ HS0 eq_refl) as HR1.
lazymatch type of HR1 with region_ok _ _ _ ?r =>
  pose proof HR1 as (_ & _ & HW1 & _);
  pose proof (ast_ok_pi_set_region E _ _ 1 r (set_window r 168 184) HS0 eq_refl eq_refl ltac:(vm_compute; reflexivity)
    (region_ok_rewindow SEGS E _ r 168 184 HR1 ltac:(intros o Ho; apply HW1; cbv [mf_r_slots YP09.r_wlo YP09.r_whi]; lia)))
    as HS1 end.
clear HS0 HR1 HW1.
lazymatch type of HS1 with st_ok_pi _ _ _ ?s _ => let s' := eval vm_compute in s in change s with s' in HS1 end.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold mf_at.
assert (E26 : ew E 26 = Z_to_bv 64 p) by (rewrite (EE 26%nat 26%bv eq_refl), R26; reflexivity).
assert (U26 : U E (SOff 26 0) = p) by (apply (U_atom E 26 p E26); lia).
assert (E10 : ew E 10 = Z_to_bv 64 (fr_nl p rest)) by (rewrite (EE 10%nat 10%bv eq_refl), R10; reflexivity).
assert (U10 : U E (SOff 10 0) = fr_nl p rest) by (apply (U_atom E 10 _ E10); lia).
(* 0x86384 sd s10,176(s1): the run stops at 0x86388 beqz a0 *)
paj_run_tok RUN HS1 HJ SHOK Bspan.
{ fr_awr U2 HSTK. }
psrr_branch_tok RUN BR HS1 SHOK Bspan.
- (* a0 = 0: no '\n' in the text left (fr_nl p rest = 0 and p >= 4096); 0x863a4 mv a0,s10; 0x863a8 jal strlen *)
  assert (HNL : existsb (fun b => b =? NL) rest = false).
  { rewrite branch_eq_U, U10, U_SLit in Hc. apply Z.eqb_eq in Hc. change (zcanon 0) with 0 in Hc.
    unfold fr_nl in Hc. destruct (existsb (fun b => b =? NL) rest); [lia | reflexivity]. }
  clear Hc.
  paj_run_tok RUN HS1 HJ SHOK Bspan.
  { fr_awr U2 HSTK. }
  (* the two runs wrote only 176(s1) *)
  assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
  { intros a Ha HnW.
    refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms) (fun a => mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184)
      HFr _ a Ha HnW).
    fr_win U2. }
  assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) ->
    rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
  { intros a Ha HnW.
    refine (kept_of_frame E _ (w_H Wc) (ms_mem ms) (ms_mem ms0)
      (fun a => mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) HFr0 _ a Ha HnW).
    fr_win U2. }
  assert (Kc : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) ->
    rdW Wc (ms_mem ms0) a = rdW Wc memc a) by (intros a Ha HnW; rewrite (K2 a Ha HnW); exact (K1 a Ha HnW)).
  destruct (fr_run_keep B v lyc Sc Wc memc mdc pos mcc cur (ms_mem ms0) _ 168 184 CX CORE CELLS HJ ltac:(lia) ltac:(lia)
    Kc) as (CORE1 & CELLS1 & LPf1 & _).
  pose proof (LPf1 _ _ _ _ _ LOOP) as LOOP1. clear LPf1.
  (* 176(s1) = s10 = p, from the call state's frame cells *)
  pose proof (st_ok_region_nth E _ _ 1 _ HS1 eq_refl) as HR1. cbn [restrict ms_mem] in HR1.
  assert (V176 : mf_slot v (ms_mem ms0) Wc 176 p).
  { unfold mf_slot.
    lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
      refine (field_of_region E _ nb _ cs lo hi wlo whi 176 8%N (SOff 26 0) p HR1 U2
        ltac:(cbn [In]; repeat first [left; reflexivity | right]) (fr_denot_U E _ p U26) ltac:(cbn; lia)
        ltac:(cbn; lia)) end. }
  clear HR1.
  (* the registers at the call: a0 = s10 = p, ra = 0x863ac, the cut's registers kept *)
  prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
  prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23.
  prreg HS1 (24%bv : bv 5) Q24. prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22.
  prreg HS1 (25%bv : bv 5) Q25. prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (21%bv : bv 5) Q21.
  prreg HS1 (20%bv : bv 5) Q20. prreg HS1 (10%bv : bv 5) Q10. prreg HS1 (1%bv : bv 5) Q1.
  assert (RAg : mf_regs_at B v lyc pos (ms_regs ms0)).
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
  assert (G26 : getr (ms_regs ms0) 26 = w64 p) by (rewrite Q26, (EE 26%nat 26%bv eq_refl); exact R26).
  assert (G21 : getr (ms_regs ms0) 21 = w64 line) by (rewrite Q21, (EE 21%nat 21%bv eq_refl); exact R21).
  assert (G20 : getr (ms_regs ms0) 20 = w64 511) by (rewrite Q20, (EE 20%nat 20%bv eq_refl); exact R20).
  assert (G10 : getr (ms_regs ms0) 10 = w64 p) by (rewrite Q10, E26; reflexivity).
  pose proof RAg as ((G2 & G3 & G4 & _) & _).
  clear Q2 Q3 Q4 Q8 Q9 Q18 Q23 Q24 Q19 Q22 Q25 Q26 Q21 Q20 Q10.
  pmkst HS1.
  (* strlen(p): fr_art_at (mf_front_art.v) with RtString.astrlen_realizes; strlen writes only its scratch window
     [s1 - ESTACK, s1) below the call's sp = s1 *)
  assert (HES : ESTACK = 4096) by reflexivity.
  pose proof (mf_sp_at B v lyc pos (ms_regs ms0) CX RAg) as Usp.
  assert (Hs1m16 : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0)
    by (destruct Hs1 as [E1 | E1]; rewrite E1; [replace (mv_sp v - 320 - mv_sp v) with (-320) by lia
        | replace (mv_sp v - 336 - mv_sp v) with (-336) by lia]; reflexivity).
  pose proof HJ as (HAR1 & _).
  assert (Hzb : length (seg_spec.zb rest) = length rest) by (unfold seg_spec.zb; apply length_map).
  pose proof LOOP1 as (_ & _ & _ & (LZ & LT) & _).
  destruct (sa_strz_bytes SEGS (w_H Wc) (ms_mem ms0) p rest LZ) as (HBy & HN0 & _).
  eapply SRr_bind.
  { eapply (fr_art_at SEGS B LAWS pa_segs_low ESTACK (SIGMA SS___interceptor_trampoline_strlen) Wc (ms_regs ms0)
      (ms_mem ms0) SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v)
      (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc _ 0 (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + FR_SL)) _ HJ).
    - rewrite Usp. lia.
    - exact Hs1m16.
    - lia.
    - rewrite HES. lia.
    - rewrite HES, HSTK. lia.
    - exact Q1.
    - apply (STRLEN fx lyc Sc Wc (ms_regs ms0) (ms_mem ms0) _ p (seg_spec.zb rest)).
      + apply (ecall_pre_stk_at SEGS B ESTACK SegInstB.STK_m_file (mv_sp v) (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v))
          (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc Wc (ms_mem ms0) _ 0 (ms_regs ms0)
          (mf_s1 (mv_sp v) - mv_sp v) HJ).
        * rewrite Usp. lia.
        * exact Hs1m16.
        * lia.
        * lia.
        * rewrite HES, HSTK. lia.
        * rewrite Q1. apply ret_ok_codeptr_v; [lia | reflexivity].
        * exact G3.
        * exact G4.
      + exact G10.
      + lia.
      + exact (conj HBy HN0).
      + unfold astr_len. rewrite Hzb.
        apply (aread_ok_of_block SEGS B LAWS ESTACK lyc Sc Wc (ms_regs ms0) (ms_mem ms0) _ bt mt p _ HAR1 Hbt);
          [lia | lia | lia | rewrite Usp, HES; lia].
      + unfold astr_len. rewrite Hzb. exact LT.
      + exact (mf_rom_now B v lyc Sc Wc (ms_mem ms0) _ pos MF_LOW_OFF mcc CX CORE1). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & HQ2 & HK2).
  assert (HK2' : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) - ESTACK <= a < mf_s1 (mv_sp v)) ->
    rdW Wc mem2 a = rdW Wc (ms_mem ms0) a) by (intros a Ha Hna; apply HK2; [exact Ha | lia]).
  (* every cut fact at strlen's return 0x863ac = FR_SL *)
  destruct (mf_keep_art0 B v lyc Sc Wc (ms_regs ms0) (ms_mem ms0) _ pos MF_LOW_OFF mcc cur regs2 mem2 md2
    (mf_s1 (mv_sp v) - ESTACK) (mf_s1 (mv_sp v)) CX CORE1 CELLS1 RAg HJ2 HP2 ltac:(rewrite HES, HSTK; lia) ltac:(lia)
    HK2') as (CORE2 & CELLS2 & RA2 & _ & LPf2).
  assert (V176' : mf_slot v mem2 Wc 176 p).
  { unfold mf_slot in V176 |- *.
    apply (mf_val_keep Wc Wc (ms_mem ms0) mem2 (fun a => mf_s1 (mv_sp v) - ESTACK <= a < mf_s1 (mv_sp v)) _ 8 _ HK2');
      [lia | change (Z.of_nat 8) with 8; lia | intros k Hk HR; change (Z.of_nat 8) with 8 in Hk; lia | exact V176]. }
  apply (FSL v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest).
  + exact (conj CX (conj LS (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj Hn (conj Hne
      (conj (LPf2 _ _ _ _ _ LOOP1) EQ))))))))).
  + transitivity (getr (ms_regs ms0) 26); [exact (HP2 26 ltac:(unfold acallee_saved; lia)) | exact G26].
  + transitivity (getr (ms_regs ms0) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact G21].
  + transitivity (getr (ms_regs ms0) 20); [exact (HP2 20 ltac:(unfold acallee_saved; lia)) | exact G20].
  + exact V176'.
  + exact HNL.
  + rewrite HQ2. unfold astr_len. rewrite Hzb. reflexivity.
- (* a0 <> 0: the first '\n' is at p + L (fr_nl p rest = p + L), mf_next p rest = p + L + 1 *)
  rewrite branch_eq_U, U10, U_SLit in Hc. apply Z.eqb_neq in Hc. change (zcanon 0) with 0 in Hc.
  destruct (fr_next_cases p rest) as [(HNL & HNX) | (HNL & _ & _)];
    [| exfalso; unfold fr_nl in Hc; rewrite HNL in Hc; lia].
  assert (Hfn : fr_nl p rest = p + Z.of_nat (length (mf_line rest))) by (unfold fr_nl; rewrite HNL; reflexivity).
  clear Hc.
  (* 0x8638c sd a0,168(s1); 0x86390 li a6,32; 0x86394 li a1,-1: the run stops at the trap branch 0x86398 *)
  paj_run_tok RUN HS1 HJ SHOK Bspan.
  { fr_awr U2 HSTK. }
  psrr_branch_tok RUN BR HS1 SHOK Bspan.
  + (* 0x86398 beq a0,a1 taken: the UBSan trap (p + L + 1 wraps), refuted: a0 = p + L < 2^63 - 1 *)
    exfalso. rewrite branch_eq_U, U10, U_SLit in Hc. apply Z.eqb_eq in Hc.
    rewrite Hfn, zcanon_id in Hc by (unfold M64; lia). lia.
  + (* 0x8639c addi a2,a0,1; 0x863a0 j 863c4: to FR_E *)
    clear Hc.
    paj_run_to_tok RUNTO HS1 HJ SHOK Bspan FR_E.
    { fr_awr U2 HSTK. }
    (* the three runs wrote only 176(s1) and 168(s1) *)
    assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) ->
      rdW Wc (ms_mem ms) a = rdW Wc memc a).
    { intros a Ha HnW.
      refine (kept_of_frame E _ (w_H Wc) memc (ms_mem ms)
        (fun a => mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) HFr _ a Ha HnW).
      fr_win U2. }
    assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) ->
      rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
    { intros a Ha HnW.
      refine (kept_of_frame E _ (w_H Wc) (ms_mem ms) (ms_mem ms0)
        (fun a => mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) HFr0 _ a Ha HnW).
      fr_win U2. }
    assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) ->
      rdW Wc (ms_mem ms1) a = rdW Wc (ms_mem ms0) a).
    { intros a Ha HnW.
      refine (kept_of_frame E _ (w_H Wc) (ms_mem ms0) (ms_mem ms1)
        (fun a => mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) HFr1 _ a Ha HnW).
      fr_win U2. }
    assert (Kc : forall a, 0 <= a < 2 ^ 64 -> ~ (mf_s1 (mv_sp v) + 168 <= a < mf_s1 (mv_sp v) + 184) ->
      rdW Wc (ms_mem ms1) a = rdW Wc memc a)
      by (intros a Ha HnW; rewrite (K3 a Ha HnW), (K2 a Ha HnW); exact (K1 a Ha HnW)).
    destruct (fr_run_keep B v lyc Sc Wc memc mdc pos mcc cur (ms_mem ms1) _ 168 184 CX CORE CELLS HJ ltac:(lia)
      ltac:(lia) Kc) as (CORE2 & CELLS2 & LPf & _).
    (* 176(s1) = s10 = p and 168(s1) = a0 = p + L, from the final state's frame cells *)
    pose proof (st_ok_pi_region_nth E _ _ 1 _ HS1 eq_refl) as HR1. cbn [restrict ms_mem] in HR1.
    assert (V176 : mf_slot v (ms_mem ms1) Wc 176 p).
    { unfold mf_slot.
      lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
        refine (field_of_region E _ nb _ cs lo hi wlo whi 176 8%N (SOff 26 0) p HR1 U2
          ltac:(cbn [In]; repeat first [left; reflexivity | right]) (fr_denot_U E _ p U26) ltac:(cbn; lia)
          ltac:(cbn; lia)) end. }
    assert (V168 : mf_slot v (ms_mem ms1) Wc 168 (p + Z.of_nat (length (mf_line rest)))).
    { unfold mf_slot.
      lazymatch type of HR1 with region_ok _ _ _ (YP09.mkRegion (Some ?nb) ?lo ?hi ?wlo ?whi ?cs) =>
        refine (field_of_region E _ nb _ cs lo hi wlo whi 168 8%N (SOff 10 0) (p + Z.of_nat (length (mf_line rest)))
          HR1 U2 ltac:(cbn [In]; repeat first [left; reflexivity | right]) _ ltac:(cbn; lia) ltac:(cbn; lia)) end.
      apply fr_denot_U. rewrite U10. exact Hfn. }
    clear HR1.
    (* the registers at FR_E: a0 = p + L, a2 = a0 + 1 = mf_next p rest, a6 = 0x20 *)
    prreg HS1 (2%bv : bv 5) Q2. prreg HS1 (3%bv : bv 5) Q3. prreg HS1 (4%bv : bv 5) Q4. prreg HS1 (8%bv : bv 5) Q8.
    prreg HS1 (9%bv : bv 5) Q9. prreg HS1 (18%bv : bv 5) Q18. prreg HS1 (23%bv : bv 5) Q23.
    prreg HS1 (24%bv : bv 5) Q24. prreg HS1 (19%bv : bv 5) Q19. prreg HS1 (22%bv : bv 5) Q22.
    prreg HS1 (25%bv : bv 5) Q25. prreg HS1 (26%bv : bv 5) Q26. prreg HS1 (21%bv : bv 5) Q21.
    prreg HS1 (20%bv : bv 5) Q20. prreg HS1 (10%bv : bv 5) Q10.
    pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ _ (12%bv : bv 5) HS1) as P12.
    lazymatch type of P12 with _ = sv_denot _ (sr_get ?aa ?rr) =>
      let w := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with w in P12 end.
    cbn [ms_regs restrict mkst] in P12.
    pose proof (st_ok_pi_restrict_reg (w_H Wc) E _ _ (16%bv : bv 5) HS1) as P16.
    lazymatch type of P16 with _ = sv_denot _ (sr_get ?aa ?rr) =>
      let w := eval vm_compute in (sr_get aa rr) in change (sr_get aa rr) with w in P16 end.
    cbn [ms_regs restrict mkst] in P16.
    assert (RA2 : mf_regs_at B v lyc pos (ms_regs ms1)).
    { apply (mf_regs_at_of B v lyc pos regs1 (ms_regs ms1) RA).
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
    pmkst HS1.
    apply (FE v lyc Sc Wc (ms_regs ms1) (ms_mem ms1) _ pos mcc cur line p rest).
    * exact (conj CX (conj LS (conj FRM (conj CORE2 (conj CELLS2 (conj RA2 (conj Hn (conj Hne
        (conj (LPf _ _ _ _ _ LOOP) EQ))))))))).
    * rewrite Q26, (EE 26%nat 26%bv eq_refl). exact R26.
    * rewrite Q21, (EE 21%nat 21%bv eq_refl). exact R21.
    * rewrite Q20, (EE 20%nat 20%bv eq_refl). exact R20.
    * exact V176.
    * exact V168.
    * rewrite Q10, E10, Hfn. reflexivity.
    * rewrite P12, HNX. unfold w64. apply fr_denot_U.
      rewrite (U_atom_off E 10 (fr_nl p rest) 1 E10) by lia. rewrite Hfn. reflexivity.
    * rewrite P16. reflexivity.
Qed.
(* inside the Sections: the Section hypotheses as its assumptions *)
About fr_sc. Print Assumptions fr_sc.
End e.
End f.
End d.
About fr_sc. Print Assumptions fr_sc.
