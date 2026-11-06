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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/reac_box_catalogue.v, with its module paths and module names changed; 193 of its 226 lines of code are new or changed and 420 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): segment A6's REF3 half of reac_segconf_parse_file's walk
   (lib/A/Prog/pf_pieces.v H_REF3, :430-445): from the cut REF3 (0x87e74, INV_REF3) the call of refuse
   (`jal 0x88da4`, refuse(c, lineno, f, a3)) and `j 0x88068` to the cut TAIL, where the hypothesis HA_TAIL n takes
   over. Segment A6's proof, 2026-10-30.
   The call: PaFx.cl_callSF (refuse's post is apost_baseF: it returns at an FP state of its own), its premises
   from pf_a6_k.refuse_site_ok_87e74 (VERIFY rule 1j-bis) and pf_a5_k.a5_chain; the state after it rebuilt by
   jafter_call_keep_hi and carried to the returned FP state by st_ok_pi_restrict_xfx (reac_segconf_parse.v's
   route); the cut facts at TAIL from refuse's journal (pf_a6_k.a6_keeps_refuse, a6_base_move, a6_nm_move) and the
   spine (pfA_facts.pf_cnt_refuse, pf_next_skipn_lt; SegModel.refuse_proj).
   Section hypotheses: REF (refuse_contract at image A's numbers, every FP state), SIGP (the listing's program call
   targets), and VRO / SSPX, FORCED by a6_base_move after the refuse call: refuse's post gives only its journal,
   which keeps an image byte only off as_owned_static B (YCbq.v:479); whether the GOT word 0xa36d8 and the guard
   0x5ff078 are owned statics is a record fact of listing stage 2 (SegRecCells.seg_rec_cells), and arodata_okP
   after refuse needs pa_relro_img (VRO). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YC5d YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstA pf_pieces pf_a5_k pf_a6_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
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
(* refuse's contract at image A's numbers (pf_pieces.v:683), at every FP state *)
Hypothesis REF : forall fx0 : YK11.FPState, refuse_contract (fx := fx0) SEGS B (BASE + AF_refuse) STK_refuse
  RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's program call targets (SegObj.v; the pinned instance gives it by computation) *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
(* FORCED by a6_base_move after the refuse call (head comment) *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Theorem pf_a6_ref3 : forall n, HA_TAIL B n -> H_REF3 B n.
Proof.
intros n HT. unfold H_REF3.
intros v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 HINV.
pose proof HINV as (HB & MID & ST & REFA & RG).
pose proof HB as (CX & FI & OBJ & SL & FSH).
pose proof FI as (HJ & Hly' & HFS & HPERM & HSV & HFL & HFRM & HFIRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
destruct (a5_chain B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as [ch1 HCH].
pose proof OBJ as (_ & _ & _ & _ & HCH0 & _).
pose proof MID as (Ho & Hon & HLC).
pose proof HLC as (HLC1 & _ & HLC3 & HLC4).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
destruct (a6_cx B v CX) as (Hc0 & Hc16 & HLS & HDJ & Hceil & Hslo & H47 & Hsp16).
pose proof CX as (_ & _ & _ & Hc64 & _).
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HCH0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
assert (Hnext : (pf_next (p_s v) o <= length (p_s v))%nat) by exact (pf_next_le (p_s v) o Ho).
assert (Hln : 0 <= ln + 1 <= 65535) by lia.
assert (Hfa : 0 <= fa < 2 ^ 64).
{ destruct REFA as [(_ & -> & _ & _) | (x & [(_ & ->) | (_ & ->)] & _)];
    (split; [apply Z.leb_le | apply Z.ltb_lt]; vm_compute; reflexivity). }
(* the seed at REF3: the cut's registers, no region *)
set (E := Eimg (Ereg rX [])).
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n0 r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HA0 : env_agree 32 (Ereg rX []) E)
  by (split; [intros n0 Hn; subst E; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (HS : st_ok_pi SEGS VAL E (mkSS PF_REF3 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_REF3)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
unfold cfg_at. change (w64 (BASE + PF_REF3)) with (Z_to_bv 64 (BASE + PF_REF3)).
(* 0x87e74 jal refuse *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ apply awr_ok_nil. }
assert (HM : ms_mem ms = memc).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hr & _). destruct Hr. }
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite HM in HJ |- *.
(* the callee-saved registers are the cut's *)
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX [] HS HA0 ltac:(vm_compute; reflexivity)) as HPR.
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
assert (KR : forall r, In r [2; 10; 11; 12; 13] -> getr (ms_regs ms) (Z_to_bv 5 r) = getr rX (Z_to_bv 5 r)).
{ intros r Hr. cbn [In] in Hr.
  destruct Hr as [<- | [<- | [<- | [<- | [<- | []]]]]].
  - exact (HPR 2 ltac:(unfold acallee_saved; lia)).
  - exact (eq_trans Q10 (EE 10%nat (10%bv : bv 5) eq_refl)).
  - exact (eq_trans Q11 (EE 11%nat (11%bv : bv 5) eq_refl)).
  - exact (eq_trans Q12 (EE 12%nat (12%bv : bv 5) eq_refl)).
  - exact (eq_trans Q13 (EE 13%nat (13%bv : bv 5) eq_refl)). }
(* VERIFY rule 1j-bis at 0x87e74: refuse_contract's premises from INV_REF3, pf_a6_k.v's closed site lemma *)
destruct (refuse_site_ok_87e74 B n v pos lyc Sc Wc rX memc mdc cf cur' nm o ln d f fa args a3 (ms_regs ms) HINV KR)
  as (ROD & RPRE & ROOM & EV).
assert (R10 : getr rX 10 = w64 (p_c v))
  by (exact (a5_rg_get rX _ 10 _ RG ltac:(apply in_or_app; right; apply in_or_app; right; cbn [In]; tauto))).
assert (R11 : getr rX 11 = w64 (ln + 1))
  by (exact (a5_rg_get rX _ 11 _ RG ltac:(apply in_or_app; right; apply in_or_app; right; cbn [In]; tauto))).
assert (R12 : getr rX 12 = w64 fa)
  by (exact (a5_rg_get rX _ 12 _ RG ltac:(apply in_or_app; right; apply in_or_app; right; cbn [In]; tauto))).
assert (C1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + 12612)) by exact Q1.
assert (C10 : getr (ms_regs ms) 10 = w64 (p_c v)) by (rewrite <- R10; exact (KR 10 ltac:(cbn; tauto))).
assert (C11 : getr (ms_regs ms) 11 = w64 (ln + 1)) by (rewrite <- R11; exact (KR 11 ltac:(cbn; tauto))).
assert (C12 : getr (ms_regs ms) 12 = w64 fa) by (rewrite <- R12; exact (KR 12 ltac:(cbn; tauto))).
assert (C2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)).
{ transitivity (getr rX 2); [exact (HPR 2 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 2 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C3 : getr (ms_regs ms) 3 = w64 (as_gp B)).
{ transitivity (getr rX 3); [exact (HPR 3 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 3 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C4 : getr (ms_regs ms) 4 = w64 (as_tp B)).
{ transitivity (getr rX 4); [exact (HPR 4 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 4 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (C8 : getr (ms_regs ms) 8 = w64 (pf_sp0 v)).
{ transitivity (getr rX 8); [exact (HPR 8 ltac:(unfold acallee_saved; lia))|].
  exact (a5_rg_get rX _ 8 _ HFI ltac:(cbn [a5_FI In]; tauto)). }
assert (Csp : spZ (ms_regs ms) = pf_s1 v).
{ unfold spZ. rewrite C2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. lia. }
(* the cut's facts at the call state: memory the cut's, journal the run's (model mdq) *)
assert (HBc : pf_base B v pos lyc Sc Wc rX memc mdq PF_SC_LINE).
{ split; [exact CX|]. split; [|exact (conj OBJ (conj SL FSH))].
  exact (conj HJ (conj Hly' (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM HFIRG))))))). }
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 12612)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) f args) /\ sa_noalloc B lyc Sc ly2 S2) HJ).
  - rewrite Csp. lia.
  - exact S1d.
  - lia.
  - rewrite SRF. lia.
  - rewrite SRF, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REF fx lyc Sc Wc (ms_regs ms) memc mdq ch1 (p_c v) (ln + 1) fa (ln + 1) cf f args HPRE1 ROD
        C10 ltac:(lia) C11 ltac:(lia) C12 Hfa RPRE ROOM EV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
    apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
(* back at 0x87e78, at the FP state fx1 refuse returned *)
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
destruct HNA2 as (HP2b & Hly2 & HS2e).
pose proof (a6_keeps_refuse B v pos lyc Sc Wc rX memc mdq PF_SC_LINE cf ly2 S2 W2 mem2 md2 EV_refuse
  HBc HJc2 HP2b) as HK.
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP2).
(* 0x87e78 j 0x88068: a seed at fx1 with the returned registers, the plain run to TAIL *)
set (E2 := Eimg (Ereg regs2 [])).
assert (HEI2 : img_env VAL A_LIM E2) by (subst E2; apply Eimg_env).
assert (HA2 : env_agree 32 (Ereg regs2 []) E2)
  by (split; [intros n0 Hn; subst E2; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
assert (HS2 : st_ok_pi (fx := fx1) SEGS VAL E2 (mkSS 12612 sr_atoms [] None (mkFacts [] [] []))
  (restrict (w_H W2) (@mkst fx1 regs2 (Z_to_bv 64 (BASE + 12612)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  - subst E2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - cbn. tauto.
  - unfold facts_ok; cbn; repeat split; first [exact I | apply Forall_nil | constructor]. }
paj_run_to_sh (SRr_run_to_pi_AJ (fx := fx1) B LAWS) HS2 HJ2 PF_TAIL.
{ apply awr_ok_nil. }
(* at TAIL (0x88068): the `j` wrote nothing and changed no register *)
assert (HM3 : ms_mem ms0 = mem2).
{ apply functional_extensionality. intros x. apply HF. intros (r & Hr & _). destruct Hr. }
clear HF HFr HG.
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (md3 := dM) in *; clearbody md3 end.
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ regs2 [] HS2 HA2 ltac:(vm_compute; reflexivity)) as HP3.
pmkst HS2. rewrite HM3 in HJ2 |- *.
assert (HPR3 : aregs_preserved rX (ms_regs ms0)) by exact (aregs_preserved_trans _ _ _ HPR2 HP3).
(* pf_base at TAIL: the heap facts re-derived from AR there (a6_base_move; it takes VRO and SSPX) *)
assert (HB3 : pf_base (fx := fx1) B v pos ly2 S2 W2 (ms_regs ms0) mem2 md3 PF_SC_LINE).
{ apply (a6_base_move (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc rX memc mdq PF_SC_LINE ly2 S2 W2 (ms_regs ms0)
    mem2 md3 HBc Hfx1 HJ2 Hly2 HS2e HP2b HK).
  intros r Hr. apply HPR3. unfold acallee_saved. cbn [In] in Hr. lia. }
destruct ST as (HRCc & COK & NM & CNT).
assert (RG' : pf_rg rX (PF_RL v pos ++
  [(21, p_t v + Z.of_nat (pf_next (p_s v) o)); (26, ln + 1); (20, pf_cur_ptr (p_c v) cur')])).
{ apply (a5_rg_incl rX (PF_RL v pos ++ PF_RM v o ln ++
    [(20, pf_cur_ptr (p_c v) cur'); (10, p_c v); (11, ln + 1); (12, fa); (13, a3)])); [|exact RG].
  intros x Hx. rewrite in_app_iff in Hx |- *. destruct Hx as [Hx | Hx]; [left; exact Hx | right].
  rewrite in_app_iff. unfold PF_RM. cbn [In] in Hx |- *. tauto. }
assert (HINV2 : INV_TAIL (fx := fx1) B n v pos ly2 S2 W2 (ms_regs ms0) mem2 md3 (refuse cf (ln + 1) f args) cur' nm
  (pf_next (p_s v) o) (ln + 1) d).
{ split; [exact HB3|]. split; [exact HLC|].
  split; [pose proof (pf_next_skipn_lt (p_s v) o Ho); lia|].
  split.
  - split; [exact HRC2|]. split.
    + destruct cur' as [i|]; cbn [pf_cur_ok] in COK |- *; [|exact I].
      rewrite (proj1 (refuse_proj cf (ln + 1) f args)). exact COK.
    + split.
      * destruct HK as (_ & _ & _ & K4). apply (a6_nm_move v pos (rdW Wc memc) _ nm NM).
        intros a Ha. apply K4. left. exact Ha.
      * exact (pf_cnt_refuse cf (ln + 1) f args _ _ (pf_next_skipn_lt (p_s v) o Ho) CNT).
  - apply (a5_rg_pres rX (ms_regs ms0) _ HPR3); [|exact RG'].
    apply Forall_app. split; [apply a5_RL_cs|].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. }
exact (HT fx1 v pos ly2 S2 W2 (ms_regs ms0) mem2 md3 (refuse cf (ln + 1) f args) cur' nm (pf_next (p_s v) o)
  (ln + 1) d HINV2).
Qed.
End e.
End f.
End d.
