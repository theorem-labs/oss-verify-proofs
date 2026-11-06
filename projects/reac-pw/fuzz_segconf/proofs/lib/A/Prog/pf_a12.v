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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 90 of its 127 lines of code are new or changed and 416 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a6_l.v, with its module paths and module names changed; 673 of its 714 lines of code are new or changed and 86 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A12 of reac_segconf_parse_file's walk, the ignore
   key (reac_segconf.c:271-280 with parse_bool R:88-99 inlined): [pf_a12_holds : S_A12 B] of
   lib/A/Prog/pf_pieces.v. From the cut IGN (0x88364) the walk reaches RS3 (0x88100, the F_badignore refusal)
   or PROV2 (0x889f0, after cur->ignore = b and cur->ignore_set = 1 are stored).

   The pieces: lib/A/Prog/pf_a12_pure.v (image-free), pf_a12_k.v (the state, the mid-walk invariant a12_I and
   its seed), pf_a12_keep.v (the shadow entries and the transport), pf_a12_c.v (the strcasecmp contract's
   premises), pf_a12_cl.v (one strcasecmp call, a12_call), pf_a12_store.v / pf_a12_st.v (the two ignore stores
   and the exit to PROV2), pf_a12_s.v / pf_a12_rf.v (the refuse call and the exit to RS3).
   This file is only the control flow between them: four calls, six branches.
   Rule 24 (reuse lookup of reac_segconf_parse_file): none found, written new; the record is
   the unit's internal record, commit dfb49d6ad789, path records/segp/g3-lookup.md.
   Segment A12's proof, by the G3 walk owner, 2026-10-30. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import
PaTable PaSym PaStep PaRun PaShadow PaJournal SegSyms SegList SegPa SegPaLib PaCall PaDenot.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaLibG PaLibF PaLibH PaSB PaCallRun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaArt PaFx SegAddr SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase SegInstA.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import pf_pieces pf_a5_k pf_a6_k
pf_a12_pure pf_a12_k pf_a12_keep pf_a12_c pf_a12_cl pf_a12_s pf_a12_st pf_a12_rf.
Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(** The four texts A12 compares the value against are literals of this function. *)
Lemma a12_in_yes : In S_yes PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma a12_in_true : In S_true PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma a12_in_no : In S_no PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.
Lemma a12_in_false : In S_false PARSE_FILE_LITS.
Proof. unfold PARSE_FILE_LITS. apply in_or_app. left. cbn [In]. tauto. Qed.

(* every region of a12_ss_ro is read-only, so a run in it writes nothing *)
Local Ltac a12_awr :=
  cbv [a12_ss_ro a12_ss_w a12_regions_w ss_mem];
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil.

(* the side condition of frame_of for a state all of whose regions are read-only *)
Local Ltac a12_nowrite :=
  intros (r & Hr & Ha); cbv [a12_ss_ro a12_ss_w a12_regions_w] in Hr; cbn [ss_mem In] in Hr;
  destruct Hr as [<- | [<- | [<- | []]]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation SIG s := (@pa_sigma _ seg_listing PI s).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Hypothesis TL : PALib B.
Hypothesis ASC : forall fx0 : YK11.FPState,
  @RtSeg.astrcasecmp_realizes fx0 rc SEGS B (SIG SS___interceptor_trampoline_strcasecmp).
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

Section s.
Context {fx : YK11.FPState}.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

(** *** From 0x883c8 on: the "no" and "false" calls, the `val[0] = '0'` test and the refusal.
    Both paths of the `val[0] = '1'` test arrive here, with parse_bool's first three tests already failed. *)
Lemma a12_rest : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val,
  HA_RS3 B n -> HA_PROV2 B n ->
  a12_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (nth 0 val 0) ->
  SegModel.strcasecmp val S_yes <> 0 -> SegModel.strcasecmp val S_true <> 0 ->
  SegModel.strcmp val [49] <> 0 ->
  SRr SEGS Wc (mkCfg (mkst rX (Z_to_bv 64 (BASE + A12_NO)) memc (seg_rom SEGS)) mdc)
    (pf_postm B v (match SegModel.parse_bool val with
                   | None => (SegModel.refuse cf (ln + 1) F_badignore [AS nm; AS val], Some gi, nm)
                   | Some b => (pf_prov_fin (PIgn b) cf gi, Some gi, nm)
                   end) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val HRS3 HPROV2 HI Hy Ht H1.
pose proof (a12_seed_I_ro B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (nth 0 val 0)
  A12_NO HI) as HS.
pose proof (a12_ei rX v pos val) as HEI.
pose proof (a12_shok_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (nth 0 val 0) false HI I)
  as SHOK.
change (if false then a12_SH2 else a12_SH1) with a12_SH1 in SHOK.
pose proof HI as (HB & _). pose proof HB as (_ & (HJ & _) & _).
(* 0x883c8 .. 0x883d4: a1 = "no", the third call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ a12_awr. }
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  a12_nowrite. }
pmkst HS. rewrite Hmem in HJ |- *.
assert (HAG : env_agree 32 (Ereg rX (a12_extra v pos val)) (a12_E rX v pos val))
  by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS _ _ _ rX (a12_extra v pos val) a12_KEPT HS HAG
  ltac:(vm_compute; reflexivity)) as HPRc.
cbn [ms_regs restrict] in HPRc.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (E52 : ew (a12_E rX v pos val) (A_OBJ 52) = w64 (seg_litA_rc S_no)).
{ rewrite (img_env_atomP _ (A_OBJ 52) HEI) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (OBJ 52%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  unfold w64; f_equal; vm_compute; reflexivity. }
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
  apply (a12_call B TL ASC S_no A12_RET3 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val
    (nth 0 val 0) rg _ _ HI HJ a12_in_no HPRc) end.
- rewrite Q1. unfold A12_RET3, AF_reac_segconf_parse_file. reflexivity.
- rewrite Q1. apply ret_ok_codeptr_v; [unfold A12_RET3, AF_reac_segconf_parse_file; lia | reflexivity].
- unfold a12_E in Q10. rewrite Q10, (ew_Eimg_Ereg_nat rX (a12_extra v pos val) 25 25%bv eq_refl).
  exact (a5_rg_get rX _ 25 _ (proj2 (proj2 (proj2 (proj2 (proj2 HI)))))
           ltac:(cbn [PF_RM app In]; tauto)).
- rewrite Q11. change 293%nat with (A_OBJ 52). exact E52.
- intros rX3 mem3 md3 HI3 HPR3 Hans3.
  clear HPR3 HPRc HJ HS SHOK HEI HAG Hmem Q1 Q10 Q11 E52.
  (* 0x883d8 beqz a0 *)
  pose proof (a12_seed_I_ro B n v pos lyc Sc Wc rX3 mem3 md3 cf nm o ln d gi vp val (nth 0 val 0)
    A12_RET3 HI3) as HS.
  pose proof (a12_ei rX3 v pos val) as HEI.
  pose proof (a12_shok_I B n v pos lyc Sc Wc rX3 mem3 md3 cf nm o ln d gi vp val (nth 0 val 0) false
    HI3 I) as SHOK.
  change (if false then a12_SH2 else a12_SH1) with a12_SH1 in SHOK.
  pose proof HI3 as (HB3 & _). pose proof HB3 as (_ & (HJ & _) & _).
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* strcasecmp val "no" = 0: parse_bool val = Some false, the stores with s7 = 0 *)
    assert (Hsc : SegModel.strcasecmp val S_no = 0)
      by (apply Hans3; exact (a12_a0_zero rX3 (a12_a0_br rX3 v pos val true Hc))).
    rewrite (a12_pb_false val Hy Ht H1 (or_introl Hsc)). cbv beta iota.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_ST.
    { a12_awr. }
    lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
      assert (Hmem : ms_mem msB = mA) by
        (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
         [reflexivity | a12_nowrite]) end.
    pmkst HS. rewrite Hmem in HJ |- *.
    assert (HAG : env_agree 32 (Ereg rX3 (a12_extra v pos val)) (a12_E rX3 v pos val))
      by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                 | reflexivity]).
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX3 _ a12_KEPT HS HAG ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (23%bv : bv 5) Q23.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
      apply (a12_store_blk B OBJ (fx := fx) false n v pos lyc Sc Wc rg mem3 _ cf nm o ln d gi vp val
        (nth 0 val 0)
        (a12_step B n v pos lyc Sc Wc rX3 mem3 md3 cf nm o ln d gi vp val (nth 0 val 0) rg _ HI3 HJ HK)
        ltac:(rewrite Q23; unfold w64, seg_spec.b2z; reflexivity) HPROV2) end.
  + (* strcasecmp val "no" <> 0: 0x883dc .. 0x883e8, a1 = "false", the fourth call *)
    assert (Hno : SegModel.strcasecmp val S_no <> 0)
      by (intros E; apply (a12_a0_nz rX3 (a12_a0_br rX3 v pos val false Hc)); apply Hans3; exact E).
    clear Hc Hans3.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { a12_awr. }
    lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
      assert (Hmem : ms_mem msB = mA) by
        (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
         [reflexivity | a12_nowrite]) end.
    pmkst HS. rewrite Hmem in HJ |- *.
    assert (HAG : env_agree 32 (Ereg rX3 (a12_extra v pos val)) (a12_E rX3 v pos val))
      by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                 | reflexivity]).
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX3 (a12_extra v pos val) a12_KEPT HS HAG
      ltac:(vm_compute; reflexivity)) as HPRc.
    cbn [ms_regs restrict] in HPRc.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    assert (E53 : ew (a12_E rX3 v pos val) (A_OBJ 53) = w64 (seg_litA_rc S_false)).
    { rewrite (img_env_atomP _ (A_OBJ 53) HEI) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
      rewrite (OBJ 53%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
      unfold w64; f_equal; vm_compute; reflexivity. }
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
      apply (a12_call B TL ASC S_false A12_RET4 n v pos lyc Sc Wc rX3 mem3 md3 cf nm o ln d gi vp val
        (nth 0 val 0) rg _ _ HI3 HJ a12_in_false HPRc) end.
    * rewrite Q1. unfold A12_RET4, AF_reac_segconf_parse_file. reflexivity.
    * rewrite Q1. apply ret_ok_codeptr_v; [unfold A12_RET4, AF_reac_segconf_parse_file; lia | reflexivity].
    * unfold a12_E in Q10. rewrite Q10, (ew_Eimg_Ereg_nat rX3 (a12_extra v pos val) 25 25%bv eq_refl).
      exact (a5_rg_get rX3 _ 25 _ (proj2 (proj2 (proj2 (proj2 (proj2 HI3)))))
               ltac:(cbn [PF_RM app In]; tauto)).
    * rewrite Q11. change 294%nat with (A_OBJ 53). exact E53.
    * intros rX4 mem4 md4 HI4 HPR4 Hans4.
      clear HPR4 HPRc HJ HS SHOK HEI HAG Hmem Q1 Q10 Q11 E53.
      pose proof HI4 as (_ & _ & _ & HVstr4 & _). pose proof HVstr4 as ((_ & HVn) & _).
      (* 0x883ec beqz a0 *)
      pose proof (a12_seed_I_ro B n v pos lyc Sc Wc rX4 mem4 md4 cf nm o ln d gi vp val (nth 0 val 0)
        A12_RET4 HI4) as HS.
      pose proof (a12_ei rX4 v pos val) as HEI.
      pose proof (a12_shok_I B n v pos lyc Sc Wc rX4 mem4 md4 cf nm o ln d gi vp val (nth 0 val 0) false
        HI4 I) as SHOK.
      change (if false then a12_SH2 else a12_SH1) with a12_SH1 in SHOK.
      pose proof HI4 as (HB4 & _). pose proof HB4 as (_ & (HJ & _) & _).
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- (* strcasecmp val "false" = 0: parse_bool val = Some false *)
         assert (Hsc : SegModel.strcasecmp val S_false = 0)
           by (apply Hans4; exact (a12_a0_zero rX4 (a12_a0_br rX4 v pos val true Hc))).
         rewrite (a12_pb_false val Hy Ht H1 (or_intror (or_introl Hsc))). cbv beta iota.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_ST.
         { a12_awr. }
         lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
           assert (Hmem : ms_mem msB = mA) by
             (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
              [reflexivity | a12_nowrite]) end.
         pmkst HS. rewrite Hmem in HJ |- *.
         assert (HAG : env_agree 32 (Ereg rX4 (a12_extra v pos val)) (a12_E rX4 v pos val))
           by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                      | reflexivity]).
         pose proof (regs_kept_of_st_ok_pi _ _ _ rX4 _ a12_KEPT HS HAG ltac:(vm_compute; reflexivity)) as HK.
         cbn [ms_regs restrict] in HK.
         prreg HS (23%bv : bv 5) Q23.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
           apply (a12_store_blk B OBJ (fx := fx) false n v pos lyc Sc Wc rg mem4 _ cf nm o ln d gi vp val
             (nth 0 val 0)
             (a12_step B n v pos lyc Sc Wc rX4 mem4 md4 cf nm o ln d gi vp val (nth 0 val 0) rg _ HI4 HJ HK)
             ltac:(rewrite Q23; unfold w64, seg_spec.b2z; reflexivity) HPROV2) end.
      -- (* strcasecmp val "false" <> 0: 0x883f0 a0 = '0'; 0x883f4 bne s3, a0 *)
         assert (Hfa : SegModel.strcasecmp val S_false <> 0)
           by (intros E; apply (a12_a0_nz rX4 (a12_a0_br rX4 v pos val false Hc)); apply Hans4; exact E).
         clear Hc Hans4.
         paj_run_tok RUN HS HJ SHOK Bspan.
         { a12_awr. }
         lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
           assert (Hmem : ms_mem msB = mA) by
             (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
              [reflexivity | a12_nowrite]) end.
         assert (HAG : env_agree 32 (Ereg rX4 (a12_extra v pos val)) (a12_E rX4 v pos val))
           by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                      | reflexivity]).
         pose proof (regs_kept_of_st_ok_pi _ _ _ rX4 _ a12_KEPT HS HAG ltac:(vm_compute; reflexivity)) as HK.
         cbn [ms_regs restrict] in HK.
         assert (E19 : ew (a12_E rX4 v pos val) 19 = Z_to_bv 64 (nth 0 val 0)).
         { unfold a12_E. rewrite (ew_Eimg_Ereg_nat rX4 (a12_extra v pos val) 19 19%bv eq_refl).
           exact (a5_rg_get rX4 _ 19 _ (proj2 (proj2 (proj2 (proj2 (proj2 HI4)))))
                    ltac:(cbn [PF_RM app In]; tauto)). }
         pose proof (a12_val0_rng Wc mem4 vp val HVstr4) as Hv0r.
         psrr_branch_tok RUN BR HS SHOK Bspan.
         ++ (* val[0] <> '0': parse_bool val = None, the refusal *)
            assert (H0 : nth 0 val 0 <> 48).
            { pose proof (a12_br_ne (a12_E rX4 v pos val) 19 (nth 0 val 0) 48 true E19 ltac:(lia) ltac:(lia) Hc)
                as Hb. apply negb_true_iff in Hb. apply Z.eqb_neq in Hb. exact Hb. }
            assert (H0s : SegModel.strcmp val [48] <> 0).
            { intros E. apply H0. apply (a12_strcmp1 val 48 HVn ltac:(lia)) in E.
              rewrite E. reflexivity. }
            rewrite (a12_pb_none val Hy Ht H1 Hno Hfa H0s). cbv beta iota.
            paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_REFS.
            { a12_awr. }
            lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
              assert (Hmem2 : ms_mem msB = mem4) by
                (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                 [exact (f_equal (fun m => m x) Hmem) | a12_nowrite]) end.
            pmkst HS. rewrite Hmem2 in HJ |- *.
            pose proof (regs_kept_of_st_ok_pi _ _ _ rX4 _ a12_KEPT HS HAG ltac:(vm_compute; reflexivity))
              as HK2.
            cbn [ms_regs restrict] in HK2.
            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
              apply (a12_ref_blk B REFUSE SIGP OBJ VRO SSPX (fx := fx) n v pos lyc Sc Wc rg mem4 _ cf nm o
                ln d gi vp val (nth 0 val 0)
                (a12_step B n v pos lyc Sc Wc rX4 mem4 md4 cf nm o ln d gi vp val (nth 0 val 0) rg _
                   HI4 HJ HK2) HRS3) end.
         ++ (* val[0] = '0': 0x883f8 check #24, a0 = val[1], 0x88410 beqz *)
            assert (H0 : nth 0 val 0 = 48).
            { pose proof (a12_br_ne (a12_E rX4 v pos val) 19 (nth 0 val 0) 48 false E19 ltac:(lia)
                ltac:(lia) Hc) as Hb. apply negb_false_iff in Hb. apply Z.eqb_eq in Hb. exact Hb. }
            assert (Hlen : (1 <= length val)%nat) by (exact (a12_len1 val 48 ltac:(lia) H0)).
            clear Hc.
            (* run the branch itself, then re-seed with the state that also holds the second byte *)
            paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_B0.
            { a12_awr. }
            lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
              assert (HmemA : ms_mem msB = mem4) by
                (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                 [exact (f_equal (fun m => m x) Hmem) | a12_nowrite]) end.
            pmkst HS. rewrite HmemA in HJ |- *.
            pose proof (regs_kept_of_st_ok_pi _ _ _ rX4 _ a12_KEPT HS HAG ltac:(vm_compute; reflexivity))
              as HKb.
            cbn [ms_regs restrict] in HKb.
            clear HS SHOK HEI.
            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
              pose proof (a12_step B n v pos lyc Sc Wc rX4 mem4 md4 cf nm o ln d gi vp val (nth 0 val 0)
                rg _ HI4 HJ HKb) as HIb;
              pose proof (a12_seed_I2_ro B n v pos lyc Sc Wc rg mem4 _ cf nm o ln d gi vp val
                (nth 0 val 0) A12_B0 HIb Hlen) as HS;
              pose proof (a12_ei rg v pos val) as HEI;
              pose proof (a12_shok_I B n v pos lyc Sc Wc rg mem4 _ cf nm o ln d gi vp val
                (nth 0 val 0) true HIb Hlen) as SHOK end.
            change (if true then a12_SH2 else a12_SH1) with a12_SH2 in SHOK.
            paj_run_tok RUN HS HJ SHOK Bspan.
            { cbv [a12_ss2_ro a12_ss_w a12_regions_w ss_mem];
              repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil. }
            lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
              assert (HmemB : ms_mem msB = mA) by
                (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                 [reflexivity |
                  intros (r & Hr & Ha); cbv [a12_ss2_ro a12_ss_w a12_regions_w] in Hr;
                  cbn [ss_mem In] in Hr;
                  destruct Hr as [<- | [<- | [<- | []]]];
                  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia]) end.
            lazymatch type of HIb with a12_I _ _ _ _ _ _ _ ?rg _ _ _ _ _ _ _ _ _ _ _ =>
              assert (HAGb : env_agree 32 (Ereg rg (a12_extra v pos val)) (a12_E rg v pos val))
                by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                           | reflexivity]);
              assert (E34b : ew (a12_E rg v pos val) 34 = Z_to_bv 64 (nth 1 val 0)) by apply a12_ew34 end.
            pose proof (a12_val1_rng Wc mem4 vp val HVstr4) as Hv1r.
            psrr_branch_tok RUN BR HS SHOK Bspan.
            ** (* val[1] = 0, so val = "0": parse_bool val = Some false *)
               assert (H1b : nth 1 val 0 = 0).
               { pose proof (a12_br_eq0 _ 34 (nth 1 val 0) true E34b ltac:(lia) Hc) as Hb.
                 apply Z.eqb_eq in Hb. exact Hb. }
               assert (H0s : SegModel.strcmp val [48] = 0).
               { apply (a12_strcmp1 val 48 HVn ltac:(lia)).
                 apply (a12_one_byte val 48 HVn ltac:(lia) H0). exact H1b. }
               rewrite (a12_pb_false val Hy Ht H1 (or_intror (or_intror H0s))). cbv beta iota.
               paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_ST.
               { cbv [a12_ss2_ro a12_ss_w a12_regions_w ss_mem];
                 repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil. }
               lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
                 assert (HmemC : ms_mem msB = mem4) by
                   (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                    [exact (f_equal (fun m => m x) HmemB) |
                     intros (r & Hr & Ha); cbv [a12_ss2_ro a12_ss_w a12_regions_w] in Hr;
                     cbn [ss_mem In] in Hr;
                     destruct Hr as [<- | [<- | [<- | []]]];
                     cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia]) end.
               pmkst HS. rewrite HmemC in HJ |- *.
               lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
                 lazymatch type of HAGb with env_agree _ (Ereg ?rg0 _) _ =>
                   assert (HAGc : env_agree 32 (Ereg rg0 (a12_extra v pos val)) E1)
                     by (env_agree_chain HAGb) end end.
               pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ a12_KEPT HS HAGc
                 ltac:(vm_compute; reflexivity)) as HKc.
               cbn [ms_regs restrict] in HKc.
               prreg HS (23%bv : bv 5) Q23.
               lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                 apply (a12_store_blk B OBJ (fx := fx) false n v pos lyc Sc Wc rg2 mem4 _ cf nm o ln d gi
                   vp val (nth 0 val 0)
                   (a12_step B n v pos lyc Sc Wc _ mem4 _ cf nm o ln d gi vp val (nth 0 val 0) rg2 _
                      HIb HJ HKc)
                   ltac:(rewrite Q23; unfold w64, seg_spec.b2z; reflexivity) HPROV2) end.
            ** (* val[1] <> 0, so val <> "0": parse_bool val = None, the refusal *)
               assert (H1b : nth 1 val 0 <> 0).
               { pose proof (a12_br_eq0 _ 34 (nth 1 val 0) false E34b ltac:(lia) Hc) as Hb.
                 apply Z.eqb_neq in Hb. exact Hb. }
               assert (H0s : SegModel.strcmp val [48] <> 0).
               { intros E. apply H1b.
                 apply (a12_one_byte val 48 HVn ltac:(lia) H0).
                 apply (a12_strcmp1 val 48 HVn ltac:(lia)). exact E. }
               rewrite (a12_pb_none val Hy Ht H1 Hno Hfa H0s). cbv beta iota.
               paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_REFS.
               { cbv [a12_ss2_ro a12_ss_w a12_regions_w ss_mem];
                 repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil. }
               lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
                 assert (HmemC : ms_mem msB = mem4) by
                   (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                    [exact (f_equal (fun m => m x) HmemB) |
                     intros (r & Hr & Ha); cbv [a12_ss2_ro a12_ss_w a12_regions_w] in Hr;
                     cbn [ss_mem In] in Hr;
                     destruct Hr as [<- | [<- | [<- | []]]];
                     cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia]) end.
               pmkst HS. rewrite HmemC in HJ |- *.
               lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
                 lazymatch type of HAGb with env_agree _ (Ereg ?rg0 _) _ =>
                   assert (HAGc : env_agree 32 (Ereg rg0 (a12_extra v pos val)) E1)
                     by (env_agree_chain HAGb) end end.
               pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ a12_KEPT HS HAGc
                 ltac:(vm_compute; reflexivity)) as HKc.
               cbn [ms_regs restrict] in HKc.
               lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
                 apply (a12_ref_blk B REFUSE SIGP OBJ VRO SSPX (fx := fx) n v pos lyc Sc Wc rg2 mem4 _ cf
                   nm o ln d gi vp val (nth 0 val 0)
                   (a12_step B n v pos lyc Sc Wc _ mem4 _ cf nm o ln d gi vp val (nth 0 val 0) rg2 _
                      HIb HJ HKc) HRS3) end.
Qed.

(** *** The walk *)
Lemma a12_walk : forall n, HA_RS3 B n -> HA_PROV2 B n -> H_IGN B n.
Proof.
intros n HRS3 HPROV2.
intros v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HINV Hrole Hmodel Hign.
pose proof (a12_I_of_kv B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi kp vp key val HINV) as HI.
pose proof HINV as (_ & _ & _ & ((ei & Hei & Hkey & Hval) & _) & _ & _).
rewrite (a12_spine cf gi nm (ln + 1) (pf_tline (p_s v) o) ei key val Hei Hkey Hval Hrole Hmodel Hign).
unfold cfg_at. change (w64 (BASE + PF_IGN)) with (Z_to_bv 64 (BASE + PF_IGN)).
(* 0x88364 .. 0x88370: a0 = val, a1 = "yes", jal the strcasecmp trampoline *)
pose proof (a12_seed_I_ro B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_SH v pos + 8) PF_IGN HI)
  as HS.
pose proof (a12_ei rX v pos val) as HEI.
pose proof (a12_shok_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val (pf_SH v pos + 8) false HI I)
  as SHOK.
change (if false then a12_SH2 else a12_SH1) with a12_SH1 in SHOK.
pose proof HI as (HB & _). pose proof HB as (_ & (HJ & _) & _).
paj_run_tok RUN HS HJ SHOK Bspan.
{ a12_awr. }
(* the run wrote nothing: every region of a12_ss_ro is read-only *)
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  a12_nowrite. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ |- *.
assert (HAG : env_agree 32 (Ereg rX (a12_extra v pos val)) (a12_E rX v pos val))
  by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
pose proof (regs_kept_of_st_ok SEGS _ _ _ rX (a12_extra v pos val) a12_KEPT HS HAG
  ltac:(vm_compute; reflexivity)) as HPRc.
cbn [ms_regs restrict] in HPRc.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
assert (E50 : ew (a12_E rX v pos val) (A_OBJ 50) = w64 (seg_litA_rc S_yes)).
{ rewrite (img_env_atomP _ (A_OBJ 50) HEI) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
  rewrite (OBJ 50%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
  unfold w64; f_equal; vm_compute; reflexivity. }
apply (a12_call B TL ASC S_yes A12_RET1 n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val
  (pf_SH v pos + 8) (ms_regs ms) mdq _ HI HJ a12_in_yes HPRc).
- rewrite Q1. unfold A12_RET1, AF_reac_segconf_parse_file. reflexivity.
- rewrite Q1. apply ret_ok_codeptr_v; [unfold A12_RET1, AF_reac_segconf_parse_file; lia | reflexivity].
- unfold a12_E in Q10. rewrite Q10, (ew_Eimg_Ereg_nat rX (a12_extra v pos val) 25 25%bv eq_refl).
  exact (a5_rg_get rX _ 25 _ (proj2 (proj2 (proj2 (proj2 (proj2 HI)))))
           ltac:(cbn [PF_RM app In]; tauto)).
- rewrite Q11. change 291%nat with (A_OBJ 50). exact E50.
- intros rX1 mem1 md1 HI1 HPR1 Hans.
  clear HPR1 ms mdq HF HFr HG HJ HS SHOK HEI Hmem HAG HPRc Q1 Q10 Q11 E50.
  (* 0x88374 s7 = 1; 0x88378 beqz a0 *)
  pose proof (a12_seed_I_ro B n v pos lyc Sc Wc rX1 mem1 md1 cf nm o ln d gi vp val (pf_SH v pos + 8)
    A12_RET1 HI1) as HS.
  pose proof (a12_ei rX1 v pos val) as HEI.
  pose proof (a12_shok_I B n v pos lyc Sc Wc rX1 mem1 md1 cf nm o ln d gi vp val (pf_SH v pos + 8) false
    HI1 I) as SHOK.
  change (if false then a12_SH2 else a12_SH1) with a12_SH1 in SHOK.
  pose proof HI1 as (HB1 & _). pose proof HB1 as (_ & (HJ & _) & _).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { a12_awr. }
  assert (Hmem : ms_mem ms = mem1).
  { apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
    a12_nowrite. }
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* a0 = 0: strcasecmp val "yes" = 0, so parse_bool val = Some true; the stores with s7 = 1 *)
    assert (Hsc : SegModel.strcasecmp val S_yes = 0)
      by (apply Hans; exact (a12_a0_zero rX1 (a12_a0_br rX1 v pos val true Hc))).
    rewrite (a12_pb_yes val Hsc). cbv beta iota.
    paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_ST.
    { a12_awr. }
    lazymatch goal with Hf : frame_of _ _ (ms_mem ms) (ms_mem ?ms2) |- _ =>
      assert (Hmem2 : ms_mem ms2 = mem1) by
        (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
         [exact (f_equal (fun m => m x) Hmem) | a12_nowrite]) end.
    pmkst HS. rewrite Hmem2 in HJ |- *.
    assert (HAG : env_agree 32 (Ereg rX1 (a12_extra v pos val)) (a12_E rX1 v pos val))
      by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                 | reflexivity]).
    pose proof (regs_kept_of_st_ok_pi _ _ _ rX1 _ a12_KEPT HS HAG ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    prreg HS (23%bv : bv 5) Q23.
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
      apply (a12_store_blk B OBJ (fx := fx) true n v pos lyc Sc Wc rg mem1 _ cf nm o ln d gi vp val (pf_SH v pos + 8)
        (a12_step B n v pos lyc Sc Wc rX1 mem1 md1 cf nm o ln d gi vp val (pf_SH v pos + 8) rg _
           HI1 HJ HK)
        ltac:(rewrite Q23; unfold w64, seg_spec.b2z; reflexivity) HPROV2) end.
  + (* a0 <> 0: 0x8837c .. 0x88388, a1 = "true", the second call *)
    assert (Hne1 : SegModel.strcasecmp val S_yes <> 0)
      by (intros E; apply (a12_a0_nz rX1 (a12_a0_br rX1 v pos val false Hc)); apply Hans; exact E).
    clear Hans Hc.
    paj_run_tok RUN HS HJ SHOK Bspan.
    { a12_awr. }
    lazymatch goal with Hf : frame_of _ _ (ms_mem ms) (ms_mem ?ms2) |- _ =>
      assert (Hmem2 : ms_mem ms2 = mem1) by
        (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
         [exact (f_equal (fun m => m x) Hmem) | a12_nowrite]) end.
    pmkst HS. rewrite Hmem2 in HJ |- *.
    assert (HAG : env_agree 32 (Ereg rX1 (a12_extra v pos val)) (a12_E rX1 v pos val))
      by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                 | reflexivity]).
    pose proof (regs_kept_of_st_ok SEGS _ _ _ rX1 (a12_extra v pos val) a12_KEPT HS HAG
      ltac:(vm_compute; reflexivity)) as HPRc.
    cbn [ms_regs restrict] in HPRc.
    prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
    prreg HS (23%bv : bv 5) Q23.
    assert (E51 : ew (a12_E rX1 v pos val) (A_OBJ 51) = w64 (seg_litA_rc S_true)).
    { rewrite (img_env_atomP _ (A_OBJ 51) HEI) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
      rewrite (OBJ 51%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
      unfold w64; f_equal; vm_compute; reflexivity. }
    lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
      apply (a12_call B TL ASC S_true A12_RET2 n v pos lyc Sc Wc rX1 mem1 md1 cf nm o ln d gi vp val
        (pf_SH v pos + 8) rg _ _ HI1 HJ a12_in_true HPRc) end.
    * rewrite Q1. unfold A12_RET2, AF_reac_segconf_parse_file. reflexivity.
    * rewrite Q1. apply ret_ok_codeptr_v; [unfold A12_RET2, AF_reac_segconf_parse_file; lia | reflexivity].
    * unfold a12_E in Q10. rewrite Q10, (ew_Eimg_Ereg_nat rX1 (a12_extra v pos val) 25 25%bv eq_refl).
      exact (a5_rg_get rX1 _ 25 _ (proj2 (proj2 (proj2 (proj2 (proj2 HI1)))))
               ltac:(cbn [PF_RM app In]; tauto)).
    * rewrite Q11. change 292%nat with (A_OBJ 51). exact E51.
    * intros rX2 mem2' md2 HI2 HPR2 Hans2.
      lazymatch type of HPR2 with aregs_preserved ?rg _ =>
        assert (Hs7 : getr rX2 23 = w64 1) by
          (transitivity (getr rg 23); [exact (HPR2 23 ltac:(unfold acallee_saved; lia)) | exact Q23]) end.
      clear HPR2 HPRc HJ HS SHOK HEI HAG Hmem Hmem2 Q1 Q10 Q11 Q23 E51 HI1.
      (* 0x8838c beqz a0 *)
      pose proof (a12_seed_I_ro B n v pos lyc Sc Wc rX2 mem2' md2 cf nm o ln d gi vp val (pf_SH v pos + 8)
        A12_RET2 HI2) as HS.
      pose proof (a12_ei rX2 v pos val) as HEI.
      pose proof (a12_shok_I B n v pos lyc Sc Wc rX2 mem2' md2 cf nm o ln d gi vp val (pf_SH v pos + 8)
        false HI2 I) as SHOK.
      change (if false then a12_SH2 else a12_SH1) with a12_SH1 in SHOK.
      pose proof HI2 as (HB2 & _). pose proof HB2 as (_ & (HJ & _) & _).
      psrr_branch_tok RUN BR HS SHOK Bspan.
      -- (* a0 = 0: strcasecmp val "true" = 0, so parse_bool val = Some true *)
         assert (Hsc : SegModel.strcasecmp val S_true = 0)
           by (apply Hans2; exact (a12_a0_zero rX2 (a12_a0_br rX2 v pos val true Hc))).
         rewrite (a12_pb_true val Hsc). cbv beta iota.
         paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_ST.
         { a12_awr. }
         lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
           assert (Hmem : ms_mem msB = mA) by
             (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
              [reflexivity | a12_nowrite]) end.
         pmkst HS. rewrite Hmem in HJ |- *.
         assert (HAG : env_agree 32 (Ereg rX2 (a12_extra v pos val)) (a12_E rX2 v pos val))
           by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                      | reflexivity]).
         pose proof (regs_kept_of_st_ok_pi _ _ _ rX2 _ a12_KEPT7 HS HAG ltac:(vm_compute; reflexivity))
           as HK7.
         cbn [ms_regs restrict] in HK7.
         lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ _ _) _) _ =>
           apply (a12_store_blk B OBJ (fx := fx) true n v pos lyc Sc Wc rg mem2' _ cf nm o ln d gi vp val
             (pf_SH v pos + 8)
             (a12_step B n v pos lyc Sc Wc rX2 mem2' md2 cf nm o ln d gi vp val (pf_SH v pos + 8) rg _
                HI2 HJ (fun r Hr => HK7 r (a12_kept7_sub r Hr)))
             ltac:(rewrite (HK7 23%bv ltac:(left; reflexivity)); rewrite Hs7;
                   unfold w64, seg_spec.b2z; reflexivity) HPROV2) end.
      -- (* strcasecmp val "true" <> 0: 0x88390 check #22, s3 = val[0], 0x883a8 bne s3, '1' *)
         assert (Ht : SegModel.strcasecmp val S_true <> 0)
           by (intros E; apply (a12_a0_nz rX2 (a12_a0_br rX2 v pos val false Hc)); apply Hans2; exact E).
         clear Hc Hans2.
         pose proof HI2 as (_ & _ & _ & HVstr2 & _). pose proof HVstr2 as ((_ & HVn) & _).
         paj_run_tok RUN HS HJ SHOK Bspan.
         { a12_awr. }
         lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
           assert (Hmem : ms_mem msB = mA) by
             (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
              [reflexivity | a12_nowrite]) end.
         assert (HAG0 : env_agree 32 (Ereg rX2 (a12_extra v pos val)) (a12_E rX2 v pos val))
           by (split; [intros k Hk; unfold a12_E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity
                      | reflexivity]).
         lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
           assert (HAG : env_agree 32 (Ereg rX2 (a12_extra v pos val)) E1) by (env_agree_chain HAG0) end.
         pose proof (regs_kept_of_st_ok_pi _ _ _ rX2 _ a12_KEPT37 HS HAG ltac:(vm_compute; reflexivity))
           as HK37.
         cbn [ms_regs restrict] in HK37.
         prreg HS (19%bv : bv 5) Q19.
         pose proof (a12_val0_rng Wc mem2' vp val HVstr2) as Hv0r.
         assert (E33 : ew (a12_E rX2 v pos val) 33 = Z_to_bv 64 (nth 0 val 0)) by apply a12_ew33.
         lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
           assert (HAGx : env_agree 1024 (a12_E rX2 v pos val) E1)
             by (env_agree_chain (env_agree_refl 1024 (a12_E rX2 v pos val)));
           assert (E33b : ew E1 33 = Z_to_bv 64 (nth 0 val 0))
             by (rewrite <- (proj1 HAGx 33%nat ltac:(lia)) in E33; exact E33) end.
         pose proof HJ as HJm. rewrite Hmem in HJm.
         lazymatch type of Q19 with getr (ms_regs ?msB) _ = _ =>
           assert (H19 : getr (ms_regs msB) 19 = w64 (nth 0 val 0))
             by (rewrite Q19; exact E33b);
           pose proof (a12_step3 B n v pos lyc Sc Wc rX2 mem2' md2 cf nm o ln d gi vp val
             (pf_SH v pos + 8) (nth 0 val 0) (ms_regs msB) _ HI2 HJm
             (fun r Hr => HK37 r (a12_kept37_sub3 r Hr)) H19) as HI5;
           assert (Hs7b : getr (ms_regs msB) 23 = w64 1)
             by (rewrite (HK37 23%bv ltac:(left; reflexivity)); exact Hs7) end.
         psrr_branch_tok RUN BR HS SHOK Bspan.
         ++ (* val[0] <> '1': on to the "no" call at 0x883c8 *)
            assert (H1n : nth 0 val 0 <> 49).
            { pose proof (a12_br_ne _ 33 (nth 0 val 0) 49 true E33b ltac:(lia) ltac:(lia) Hc) as Hb.
              apply negb_true_iff in Hb. apply Z.eqb_neq in Hb. exact Hb. }
            assert (H1s : SegModel.strcmp val [49] <> 0).
            { intros E. apply H1n. apply (a12_strcmp1 val 49 HVn ltac:(lia)) in E.
              rewrite E. reflexivity. }
            clear Hc.
            paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_NO.
            { a12_awr. }
            lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
              assert (HmemC : ms_mem msB = mem2') by
                (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                 [exact (f_equal (fun m => m x) Hmem) | a12_nowrite]) end.
            pmkst HS. rewrite HmemC in HJ |- *.
            lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
              assert (HAGd : env_agree 32 (Ereg rX2 (a12_extra v pos val)) E1) by (env_agree_chain HAG);
              assert (HAGy : env_agree 1024 (a12_E rX2 v pos val) E1)
                by (env_agree_chain (env_agree_refl 1024 (a12_E rX2 v pos val)));
              assert (E33d : ew E1 33 = Z_to_bv 64 (nth 0 val 0))
                by (pose proof E33 as E33'; rewrite <- (proj1 HAGy 33%nat ltac:(lia)) in E33'; exact E33') end.
            pose proof (regs_kept_of_st_ok_pi _ _ _ rX2 _ a12_KEPT37 HS HAGd
              ltac:(vm_compute; reflexivity)) as HKd.
            cbn [ms_regs restrict] in HKd.
            prreg HS (19%bv : bv 5) Q19d.
            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
              assert (H19d : getr rg2 19 = w64 (nth 0 val 0)) by (rewrite Q19d; exact E33d);
              exact (a12_rest n v pos lyc Sc Wc rg2 mem2' _ cf nm o ln d gi vp val HRS3 HPROV2
                (a12_step3 B n v pos lyc Sc Wc rX2 mem2' md2 cf nm o ln d gi vp val (pf_SH v pos + 8)
                   (nth 0 val 0) rg2 _ HI2 HJ (fun r Hr => HKd r (a12_kept37_sub3 r Hr)) H19d)
                Hne1 Ht H1s) end.
         ++ (* val[0] = '1': 0x883ac check #23, a0 = val[1], 0x883c4 beqz *)
            assert (H1e : nth 0 val 0 = 49).
            { pose proof (a12_br_ne _ 33 (nth 0 val 0) 49 false E33b ltac:(lia) ltac:(lia) Hc) as Hb.
              apply negb_false_iff in Hb. apply Z.eqb_eq in Hb. exact Hb. }
            assert (Hlen : (1 <= length val)%nat) by (exact (a12_len1 val 49 ltac:(lia) H1e)).
            clear Hc.
            paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_B1.
            { a12_awr. }
            lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
              assert (HmemC : ms_mem msB = mem2') by
                (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                 [exact (f_equal (fun m => m x) Hmem) | a12_nowrite]) end.
            pmkst HS. rewrite HmemC in HJ |- *.
            lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
              assert (HAGd : env_agree 32 (Ereg rX2 (a12_extra v pos val)) E1) by (env_agree_chain HAG);
              assert (HAGy : env_agree 1024 (a12_E rX2 v pos val) E1)
                by (env_agree_chain (env_agree_refl 1024 (a12_E rX2 v pos val)));
              assert (E33d : ew E1 33 = Z_to_bv 64 (nth 0 val 0))
                by (pose proof E33 as E33'; rewrite <- (proj1 HAGy 33%nat ltac:(lia)) in E33'; exact E33') end.
            pose proof (regs_kept_of_st_ok_pi _ _ _ rX2 _ a12_KEPT37 HS HAGd
              ltac:(vm_compute; reflexivity)) as HKd.
            cbn [ms_regs restrict] in HKd.
            prreg HS (19%bv : bv 5) Q19d.
            clear HS SHOK HEI.
            lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg2 _ _ _) _) _ =>
              assert (H19d : getr rg2 19 = w64 (nth 0 val 0)) by (rewrite Q19d; exact E33d);
              pose proof (a12_step3 B n v pos lyc Sc Wc rX2 mem2' md2 cf nm o ln d gi vp val
                (pf_SH v pos + 8) (nth 0 val 0) rg2 _ HI2 HJ (fun r Hr => HKd r (a12_kept37_sub3 r Hr))
                H19d) as HIb;
              assert (Hs7c : getr rg2 23 = w64 1)
                by (rewrite (HKd 23%bv ltac:(left; reflexivity)); exact Hs7);
              pose proof (a12_seed_I2_ro B n v pos lyc Sc Wc rg2 mem2' _ cf nm o ln d gi vp val
                (nth 0 val 0) A12_B1 HIb Hlen) as HS;
              pose proof (a12_ei rg2 v pos val) as HEI;
              pose proof (a12_shok_I B n v pos lyc Sc Wc rg2 mem2' _ cf nm o ln d gi vp val
                (nth 0 val 0) true HIb Hlen) as SHOK end.
            change (if true then a12_SH2 else a12_SH1) with a12_SH2 in SHOK.
            paj_run_tok RUN HS HJ SHOK Bspan.
            { cbv [a12_ss2_ro a12_ss_w a12_regions_w ss_mem];
              repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil. }
            lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
              assert (HmemD : ms_mem msB = mA) by
                (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                 [reflexivity |
                  intros (r & Hr & Ha); cbv [a12_ss2_ro a12_ss_w a12_regions_w] in Hr;
                  cbn [ss_mem In] in Hr;
                  destruct Hr as [<- | [<- | [<- | []]]];
                  cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia]) end.
            lazymatch type of HIb with a12_I _ _ _ _ _ _ _ ?rg2 _ _ _ _ _ _ _ _ _ _ _ =>
              assert (HAGe0 : env_agree 1024 (a12_E rg2 v pos val) (a12_E rg2 v pos val))
                by apply env_agree_refl;
              assert (E34b : ew (a12_E rg2 v pos val) 34 = Z_to_bv 64 (nth 1 val 0)) by apply a12_ew34
            end.
            lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
              assert (HAGe : env_agree 1024 (a12_E _ v pos val) E1) by (env_agree_chain HAGe0);
              assert (E34c : ew E1 34 = Z_to_bv 64 (nth 1 val 0))
                by (rewrite <- (proj1 HAGe 34%nat ltac:(lia)) in E34b; exact E34b) end.
            pose proof (a12_val1_rng Wc mem2' vp val HVstr2) as Hv1r.
            psrr_branch_tok RUN BR HS SHOK Bspan.
            ** (* val[1] = 0, so val = "1": parse_bool val = Some true *)
               assert (H1b : nth 1 val 0 = 0).
               { pose proof (a12_br_eq0 _ 34 (nth 1 val 0) true E34c ltac:(lia) Hc) as Hb.
                 apply Z.eqb_eq in Hb. exact Hb. }
               assert (H1s : SegModel.strcmp val [49] = 0).
               { apply (a12_strcmp1 val 49 HVn ltac:(lia)).
                 apply (a12_one_byte val 49 HVn ltac:(lia) H1e). exact H1b. }
               rewrite (a12_pb_one val H1s). cbv beta iota.
               paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_ST.
               { cbv [a12_ss2_ro a12_ss_w a12_regions_w ss_mem];
                 repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil. }
               lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
                 assert (HmemE : ms_mem msB = mem2') by
                   (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                    [exact (f_equal (fun m => m x) HmemD) |
                     intros (r & Hr & Ha); cbv [a12_ss2_ro a12_ss_w a12_regions_w] in Hr;
                     cbn [ss_mem In] in Hr;
                     destruct Hr as [<- | [<- | [<- | []]]];
                     cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia]) end.
               pmkst HS. rewrite HmemE in HJ |- *.
               lazymatch type of HIb with a12_I _ _ _ _ _ _ _ ?rg2 _ _ _ _ _ _ _ _ _ _ _ =>
                 lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
                   assert (HAGf : env_agree 32 (Ereg rg2 (a12_extra v pos val)) E1)
                     by (env_agree_chain (a12_ag0 rg2 v pos val)) end end.
               pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ a12_KEPT7 HS HAGf
                 ltac:(vm_compute; reflexivity)) as HKe.
               cbn [ms_regs restrict] in HKe.
               lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg3 _ _ _) _) _ =>
                 apply (a12_store_blk B OBJ (fx := fx) true n v pos lyc Sc Wc rg3 mem2' _ cf nm o ln d gi
                   vp val (nth 0 val 0)
                   (a12_step B n v pos lyc Sc Wc _ mem2' _ cf nm o ln d gi vp val (nth 0 val 0) rg3 _
                      HIb HJ (fun r Hr => HKe r (a12_kept7_sub r Hr)))
                   ltac:(rewrite (HKe 23%bv ltac:(left; reflexivity)); rewrite Hs7c;
                         unfold w64, seg_spec.b2z; reflexivity) HPROV2) end.
            ** (* val[1] <> 0, so val <> "1": on to the "no" call *)
               assert (H1b : nth 1 val 0 <> 0).
               { pose proof (a12_br_eq0 _ 34 (nth 1 val 0) false E34c ltac:(lia) Hc) as Hb.
                 apply Z.eqb_neq in Hb. exact Hb. }
               assert (H1s : SegModel.strcmp val [49] <> 0).
               { intros E. apply H1b. apply (a12_one_byte val 49 HVn ltac:(lia) H1e).
                 apply (a12_strcmp1 val 49 HVn ltac:(lia)). exact E. }
               paj_run_to_tok RUNTO HS HJ SHOK Bspan A12_NO.
               { cbv [a12_ss2_ro a12_ss_w a12_regions_w ss_mem];
                 repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi]; lia|]); apply awr_ok_nil. }
               lazymatch goal with Hf : frame_of _ _ ?mA (ms_mem ?msB) |- _ =>
                 assert (HmemE : ms_mem msB = mem2') by
                   (apply functional_extensionality; intros x; unfold frame_of in Hf; rewrite Hf;
                    [exact (f_equal (fun m => m x) HmemD) |
                     intros (r & Hr & Ha); cbv [a12_ss2_ro a12_ss_w a12_regions_w] in Hr;
                     cbn [ss_mem In] in Hr;
                     destruct Hr as [<- | [<- | [<- | []]]];
                     cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia]) end.
               pmkst HS. rewrite HmemE in HJ |- *.
               lazymatch type of HIb with a12_I _ _ _ _ _ _ _ ?rg2 _ _ _ _ _ _ _ _ _ _ _ =>
                 lazymatch type of HS with st_ok_pi _ _ ?E1 _ _ =>
                   assert (HAGf : env_agree 32 (Ereg rg2 (a12_extra v pos val)) E1)
                     by (env_agree_chain (a12_ag0 rg2 v pos val)) end end.
               pose proof (regs_kept_of_st_ok_pi _ _ _ _ _ a12_KEPT HS HAGf
                 ltac:(vm_compute; reflexivity)) as HKe.
               cbn [ms_regs restrict] in HKe.
               lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg3 _ _ _) _) _ =>
                 exact (a12_rest n v pos lyc Sc Wc rg3 mem2' _ cf nm o ln d gi vp val HRS3 HPROV2
                   (a12_step B n v pos lyc Sc Wc _ mem2' _ cf nm o ln d gi vp val (nth 0 val 0) rg3 _
                      HIb HJ HKe) Hne1 Ht H1s) end.
Qed.

End s.

Theorem pf_a12_holds : S_A12 B.
Proof. intros f0. exact (a12_walk (fx := f0)). Qed.

End e.
End f.
End d.
