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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 119 of its 161 lines of code are new or changed and 411 lines of the source are left out. *)
(* m_file on fuzz_segconf.asan (image A), segment S_MF_HDRA: the walk of HDR (0x862cc, a header line): `li a1,93;
   mv a0,s11; jal` to memchr's trampoline with a2 = j - i, so memchr(s, ']', j - i) over the stripped line
   sl = slice i j (mf_line rest) at s = p + i; the call is m_file_memchr.v's aj_memchr_atM (memchr writes only its
   window [s1 - ESTACK, s1)), its first_byte is the model's memchr of sl (m_file_s_hdra_e.v hda_memchr_of_fb), and
   the walk goes on at memchr's return 0x862d8 (HDA_RMC_stmt, at the same FP state). The run to the call writes no
   byte (the seed's slots read-only); every cut fact crosses it by m_file_k.v's mf_keep_run0 and crosses the call by
   mf_keep_art0. The HDRA segment lane of the G2 walk owner's G2. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegObj SegGlob SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Rt Require MemchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import m_file_c m_file_m m_file_sd m_file_k m_file_memchr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
m_file_s_hdra_t m_file_s_hdra_m m_file_s_hdra_e m_file_s_hdra_w.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require SegInstA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
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
Hypothesis RELRO : forall a, SegInstA.RLO_A <= a < SegInstA.RHI_A -> in_img SEGS a.
Hypothesis AMEMCHR : forall fx0 : YK11.FPState,
  @MemchrDef.amemchr_realizesM fx0 rc SEGS B SegInstA.memchr_loA SegInstA.memchr_hiA (SIGMA SS___interceptor_trampoline_memchr).
Hypothesis MCROM : m_file_memchr.memchr_rom_fact SEGS B.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma hda_hdr : forall n, HDA_RMC_stmt B n -> MF_HDR_stmt B n.
Proof.
intros n RMC. unfold MF_HDR_stmt.
intros v lyc Sc Wc regs1 memc mdc pos mcc cur line p rest i j CX LS FRM CORE CELLS HR R24 Hn Hr LOOP
  HL512 Hij HjL HSL HLB HFIN R27 R23 R12 R17 NP R22 R21.
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R25 & R26).
assert (RB : mf_regs_base v regs1) by (repeat split; assumption).
pose proof LOOP as (_ & _ & _ & _ & _ & HCOK & _).
pose proof (mf_seed B VOBJS v lyc Sc Wc regs1 memc mdc pos MF_LOW_OFF mcc cur (mf_next p rest) [] MF_HDR
  true true [] false false [] false CX CORE RB (fun _ => CELLS) (mf_cur_range B _ _ _ _ _ _ _ _ _ _ CX CORE HCOK)
  (fun _ => NP) (hda_np64 _ _ _ _ _ _ _ _ LOOP) ltac:(unfold MF_LOW_OFF; lia) (Forall_nil _) (Forall_nil _)
  ltac:(vm_compute; reflexivity)) as HS0.
pose proof (hda_ro_slots _ _ _ _ _ _ _ _ _ _ _ HS0 ltac:(vm_compute; reflexivity)) as HS. clear HS0.
pose proof CORE as (HJ & _).
set (E := mfE regs1 v lyc pos cur (mf_next p rest) []) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold mfE; apply Eimg_env).
assert (EE : forall k0 (r : bv 5), Z.of_nat k0 = bv_unsigned r -> ew E k0 = getr regs1 r)
  by (intros k0 r Hk0; subst E; apply mfE_reg; exact Hk0).
pose proof (hda_E32 regs1 v lyc pos cur (mf_next p rest) []) as E32. fold E in E32.
assert (SHOK : sh_ok SEGS (SOff 32 0) [] E (mrestrict (w_H Wc) memc)) by (unfold sh_ok; constructor).
unfold mf_at.
(* li a1,93; mv a0,s11; jal: the run stops at memchr's trampoline *)
paj_run_tok RUN HS HJ SHOK Bspan; [hda_awr_ro|].
(* the run wrote no byte: every cut fact at the call's memory *)
pose proof (hda_frame_ro E _ (w_H Wc) memc (ms_mem ms) HFr ltac:(vm_compute; reflexivity)) as KA.
destruct (mf_keep_run0 B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc cur (ms_mem ms) _ CX CORE CELLS HJ (fun a _ => KA a))
  as (CORE1 & CELLS1 & NPf1 & LPf1).
pose proof (LPf1 _ _ _ _ _ LOOP) as LOOP1. pose proof (NPf1 _ NP) as NP1. clear NPf1 LPf1.
(* the registers at the call: a0 = s, a1 = ']', a2 = j - i, ra = memchr's return, the cut's registers kept *)
assert (RAg : mf_regs_at B v lyc pos (ms_regs ms)) by (mf_regs_carry HS EE E32 HR).
assert (G24 : getr (ms_regs ms) 24 = w64 (frame_addr lyc 1 pos)) by (hda_rg HS EE 24%nat (24%bv : bv 5); exact R24).
assert (G27 : getr (ms_regs ms) 27 = w64 (p + Z.of_nat i)) by (hda_rg HS EE 27%nat (27%bv : bv 5); exact R27).
assert (G21 : getr (ms_regs ms) 21 = w64 (mv_c v)) by (hda_rg HS EE 21%nat (21%bv : bv 5); exact R21).
assert (G22 : getr (ms_regs ms) 22 = w64 (line + 1)) by (hda_rg HS EE 22%nat (22%bv : bv 5); exact R22).
assert (G23 : getr (ms_regs ms) 23 = w64 (p + Z.of_nat j)) by (hda_rg HS EE 23%nat (23%bv : bv 5); exact R23).
prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11. prreg HS (12%bv : bv 5) Q12. prreg HS (1%bv : bv 5) Q1.
rewrite (EE 27%nat 27%bv eq_refl), R27 in Q10. rewrite (EE 12%nat 12%bv eq_refl), R12 in Q12.
pmkst HS.
(* the numbers memchr's contract asks *)
pose proof RAg as (G2 & G3 & G4 & _).
pose proof CX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HMP & _).
pose proof HMP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Ht0 & _ & _ & _ & (Ht00 & _) & _).
pose proof LOOP1 as (LP1 & LP2 & LP3 & LSTR & LADDR & _).
pose proof LADDR as (Hp0 & Hp63 & _).
pose proof (hda_line_le rest) as HLr.
destruct (mf_s1_facts B v CX) as (Hs1 & _ & _).
assert (Hs1m : (mf_s1 (mv_sp v) - mv_sp v) mod 16 = 0)
  by (destruct Hs1 as [E1 | E1]; rewrite E1; [replace (mv_sp v - 288 - mv_sp v) with (-288) by lia
      | replace (mv_sp v - 304 - mv_sp v) with (-304) by lia]; reflexivity).
assert (Hs1b : mf_s1 (mv_sp v) + 288 <= mv_sp v <= mf_s1 (mv_sp v) + 304) by (destruct Hs1 as [E1 | E1]; lia).
assert (HSTK : SegInstA.STK_m_file = 8560) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
pose proof (mf_sp_at B v lyc pos (ms_regs ms) CX RAg) as Usp.
assert (HBS : forall a, p <= a < p + Z.of_nat (length rest) + 1 -> a < mf_s1 (mv_sp v) - 2 * ESTACK).
{ intros a Ha. pose proof (mf_txt_heap_now B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc CX CORE) as HTH.
  apply (mf_heap_below_stack B v lyc Sc Wc memc mdc pos MF_LOW_OFF mcc _ _ CX CORE HTH). rewrite LP3 in Ha. lia. }
assert (Hx0 : 0 < p + Z.of_nat i) by lia.
pose proof (hda_addr_sub _ p (Z.of_nat (length rest) + 1) (p + Z.of_nat i) (Z.of_nat (j - i)) LADDR
  ltac:(lia) ltac:(lia) ltac:(lia)) as (_ & _ & XAM & XRA & XHULL).
(* memchr(s, ']', j - i) *)
eapply SRr_bind.
{ apply (aj_memchr_atM SEGS B LAWS pa_segs_low (SIGMA SS___interceptor_trampoline_memchr) SegInstA.RLO_A SegInstA.RHI_A
    (AMEMCHR fx) MCROM Wc (ms_regs ms) (ms_mem ms) SegInstA.STK_m_file (mv_sp v)
    (M_FILE_FP (mv_c v) (mv_k0 v) (mf_final v)) (mv_ly v) (mv_S v) (mv_W v) (mv_mem v) (mv_md v) [(1, pos)] lyc Sc _ 0
    (p + Z.of_nat i) 93 (Z.of_nat (j - i)) (mf_s1 (mv_sp v) - mv_sp v) (Z_to_bv 64 (BASE + HDA_RMC)) HJ).
  - exact Q10.
  - exact Q11.
  - exact Q12.
  - lia.
  - lia.
  - exact Hx0.
  - lia.
  - rewrite Usp. lia.
  - exact Hs1m.
  - lia.
  - rewrite HES, HSTK. lia.
  - exact G3.
  - exact G4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold HDA_RMC, AF_m_file; lia | vm_compute; reflexivity].
  - intros a Ha. rewrite Usp. split.
    + replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
      rewrite (hda_txt_byte _ p rest (Z.to_nat (a - p)) LSTR) by lia. discriminate.
    + pose proof (HBS a ltac:(lia)). rewrite HES in *. lia.
  - exact XAM.
  - exact XRA.
  - exact XHULL.
  - exact (mf_rod_now B RELRO v lyc Sc Wc (ms_mem ms) _ pos MF_LOW_OFF mcc CX CORE1). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & kk & -> & HJ2 & HP2 & HFB & HRES & HK2 & HPR2).
replace (mv_sp v + (mf_s1 (mv_sp v) - mv_sp v)) with (mf_s1 (mv_sp v)) in HK2 by lia.
(* every cut fact at memchr's return: memchr wrote only [s1 - ESTACK, s1) *)
destruct (mf_keep_art0 B v lyc Sc Wc (ms_regs ms) (ms_mem ms) _ pos MF_LOW_OFF mcc cur regs2 mem2 md2
  (mf_s1 (mv_sp v) - ESTACK) (mf_s1 (mv_sp v)) CX CORE1 CELLS1 RAg HJ2 HP2 ltac:(lia) ltac:(lia) HK2)
  as (CORE2 & CELLS2 & RA2 & NPf2 & LPf2).
(* memchr's answer kk is the model's memchr of sl *)
destruct (hda_memchr_of_fb SEGS Wc (ms_mem ms) p rest i j 93 kk LSTR ltac:(lia) HFB) as (k & Ekk & Hk & HMC).
apply (RMC v lyc Sc Wc regs2 mem2 md2 pos mcc cur line p rest i j k).
- exact (conj CX (conj LS (conj FRM (conj CORE2 (conj CELLS2 (conj Hn (conj Hr
    (conj (LPf2 _ _ _ _ _ LOOP1) (NPf2 _ NP1))))))))).
- exact RA2.
- transitivity (getr (ms_regs ms) 24); [exact (HP2 24 ltac:(unfold acallee_saved; lia)) | exact G24].
- unfold hda_hdr, hda_sl. split; [exact HL512|]. split; [exact Hij|]. split; [exact HjL|]. split; [exact HSL|].
  split; [exact HLB|]. rewrite HSL. exact HFIN.
- exact Hk.
- exact HMC.
- rewrite HRES, Ekk. unfold hda_sl. rewrite (hda_slice_length (mf_line rest) i j) by lia.
  destruct (Nat.ltb_spec k (j - i)) as [Hlt | Hge];
    destruct (Z.ltb_spec (Z.of_nat k) (Z.of_nat (j - i))) as [Hlt' | Hge']; try lia.
  + f_equal. lia.
  + reflexivity.
- transitivity (getr (ms_regs ms) 27); [exact (HP2 27 ltac:(unfold acallee_saved; lia)) | exact G27].
- transitivity (getr (ms_regs ms) 21); [exact (HP2 21 ltac:(unfold acallee_saved; lia)) | exact G21].
- transitivity (getr (ms_regs ms) 22); [exact (HP2 22 ltac:(unfold acallee_saved; lia)) | exact G22].
- transitivity (getr (ms_regs ms) 23); [exact (HP2 23 ltac:(unfold acallee_saved; lia)) | exact G23].
Qed.
End e.
End f.
End d.
