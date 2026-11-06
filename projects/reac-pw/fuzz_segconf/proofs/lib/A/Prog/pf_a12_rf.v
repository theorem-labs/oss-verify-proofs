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
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/A/Prog/pf_a6_r.v; 158 of its 252 lines of code are new or changed and 132 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image A (fuzz_segconf.asan): the REFUSE exit of segment A12 of reac_segconf_parse_file's
   walk (the ignore key; pf_pieces.v S_A12), `a12_ref_blk`: from 0x88414 (BASE + A12_REFS, pf_a12_k.v) under the
   mid-walk invariant a12_I to the cut RS3 (0x88100). Part of segment A12's proof (the refuse exit), by the G3 walk owner, 2026-10-30.

   The code (excerpt in the unit's internal record, commit dfb49d6ad789, path records/segp/dis/reac_segconf_parse_file.fuzz_segconf.asan.s):
     0x88414 auipc a0, 0xfff99 ; 0x88418 addi a2, a0, 0x4ec   a2 = 0x21900 = seg_litA_rc F_badignore (listing
                                                              object 54, A12_O_BADIGN)
     0x8841c mv a0, s8 (c)     ; 0x88420 mv a1, s10 (lineno = ln + 1)
     0x88424 ld a3, 0x50(s1)   (slot 0x50 = &cur_name = F + PF_O_CN)  ; 0x88428 mv a4, s9 (the value in buf)
     0x8842c jal refuse        -- returns at 0x88430 (BASE + A12_RETR)
     0x88430 j 0x88100         -- RS3 (BASE + PF_RS3); H_RS3 at the FP state refuse returned ends the block.
   Eight instructions, one program call, no inline check.

   The walk follows segment A7's proof, lib/A/Prog/pf_a7_u.v at commit 89bf60b43b36 (the UNK
   refusal of A7) step for step; the parts copied from it are its seed -> run -> call -> rebuild skeleton, the
   call-register derivations and the cl_callSF obligations (pf_a7_u.v:116-249), adapted:
   - the seed is pf_a12_k.v's a12_seed_I at A12_REFS with its third region (cur's ignore / ignore_set words,
     WRITABLE) dropped by PaLibH.st_ok_pi_submem: the six instructions before the jal store nothing, so the run's
     regions are all read-only and its frame_of gives the call state's memory = the cut's;
   - the premises of refuse_contract are pf_a12_s.v's closed site lemma a12_ref_site (pf_cnt cf 0 by pf_cnt_mono);
   - after the call, pf_base / cur_name at the FP state fx1 refuse returned come from pf_a12_s.v's a12_ref_after
     (pf_a6_k's a6_keeps_refuse + a6_base_move + a6_nm_move);
   - unlike pf_a7_u.v the return address is not the cut: the one `j 0x88100` at 0x88430 is run at fx1 by the
     closed lemma a12r_j below, from a trivial symbolic state (every register its own atom, no region, no fact;
     trim_s.v's ta_ss shape) with PaLibF.SRr_run_to_pi_AJ to PF_RS3; the memory is unchanged (no region) and the
     callee-saved registers kept (aregs_preserved_of_st_ok), so INV_RS3 at the return state is INV_RS3 at RS3.

   Section hypotheses:
     REFUSE refuse_contract at BASE + AF_refuse, STK_refuse, RLO_A, RHI_A, seg_litA_rc, gotwA, guardA, at every FP
            state (pf_pieces.v's segment list, A12's program callee): the call at 0x8842c
     SIGP   SegObj.seg_sig_prog: the call target pa_sigma SS_refuse is BASE + AF_refuse
     OBJ    SegObj.seg_val_objs: the auipc / addi pair's object atom A_OBJ 54 is seg_litA_rc F_badignore (a12r_lit)
     VRO, SSPX  FORCED by pf_a12_s.v's a12_ref_after (pf_a6_k.v's a6_base_move) after the refuse call, used nowhere
            else (see pf_a12_s.v's head comment). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09 YG0s.
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
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstA
  pf_pieces pf_a5_k pf_a6_k pf_a12_k pf_a12_s.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* the state of the `j 0x88100` at 0x88430: every register its own atom, no region, no fact (trim_s.v's ta_ss) *)
Definition a12r_jss : sstate := mkSS A12_RETR sr_atoms [] None (mkFacts [] [] []).

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).

(** ** The environment of pf_a12_k.v's state (the shape of pf_a7_q.v's a7_E_agree / a7_ew_reg / a7_ew_F) *)
Lemma a12r_E_agree : forall rX v pos val, env_agree 32 (Ereg rX (a12_extra v pos val)) (a12_E rX v pos val).
Proof.
intros rX v pos val. unfold a12_E.
split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity].
Qed.
Lemma a12r_ew_reg : forall rX v pos val k (r : bv 5), Z.of_nat k = bv_unsigned r ->
  ew (a12_E rX v pos val) k = getr rX r.
Proof. intros rX v pos val k r Hk. unfold a12_E. apply ew_Eimg_Ereg_nat. exact Hk. Qed.
Lemma a12r_ew_F : forall rX v pos val, ew (a12_E rX v pos val) 32 = Z_to_bv 64 (pf_F v pos).
Proof.
intros rX v pos val. unfold a12_E. rewrite Eimg_low by (unfold A_TEXT; lia).
exact (ew_Ereg_extra rX (a12_extra v pos val) 0).
Qed.

Section e.
Variable B : asyms.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
(* the program callee (pf_pieces.v's segment list for A12), at image A's numbers, at every FP state *)
Hypothesis REFUSE : forall fx0 : YK11.FPState,
  @refuse_contract fx0 rc SK SEGS B (BASE + AF_refuse) STK_refuse RLO_A RHI_A seg_litA_rc gotwA guardA.
(* the listing's facts over the walk's abstract instance (SegObj.v; the pinned instance gives each by
   computation): the call target, the object atoms *)
Hypothesis SIGP : seg_sig_prog (PI := PI).
Hypothesis OBJ : seg_val_objs (PI := PI).
(* FORCED by pf_a12_s.v's a12_ref_after (pf_a6_k.v's a6_base_move) after the refuse call, used nowhere else *)
Hypothesis VRO : seg_val_relro (PI := PI).
Hypothesis SSPX : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> sa_ssp (rdW W mem) gotwA guardA.

(* the literal a2 holds at the call: listing object 54 is F_badignore's text (pf_a12_k.v's A12_O_BADIGN) *)
Lemma a12r_lit : forall E, img_env VAL A_LIM E -> ew E (A_OBJ 54) = w64 (seg_litA_rc F_badignore).
Proof.
intros E HE. rewrite (img_env_atomP E (A_OBJ 54) HE) by (unfold A_OBJ, A_TEXT, A_LIM; lia).
rewrite (OBJ 54%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity)).
unfold w64; f_equal; vm_compute; reflexivity.
Qed.

(* the run before the call writes nothing: the two regions it keeps of a12_ss have no write window *)
Local Ltac a12r_awr := lazymatch goal with |- awr_ok _ _ ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok SEGS B Ex rs' stk spx fp b0 bc fr0 lyx own) end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(** ** 0x88430 `j 0x88100`: INV_RS3 at the return address is INV_RS3 at RS3 (closed, so the walk applies it at the
    FP state refuse returned) *)
Section j.
Context {fx : YK11.FPState}.

Lemma a12r_j : forall n v pos ly S (W : world SEGS) regs mem md cf cur nm o ln d,
  INV_RS3 B n v pos ly S W regs mem md cf cur nm o ln d ->
  H_RS3 B n ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A12_RETR)) mem (seg_rom SEGS)) md)
    (pf_postm B v (cf, cur, nm) o ln).
Proof.
intros n v pos ly S W regs mem md cf cur nm o ln d HINV HRS3.
pose proof HINV as ((HCX & (HJ & Hly & HFS & HPERM & HSV & HFL & HFRM & HRG0) & HOBJ & HSL & HFSH) &
  HMID & HST & HRG).
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg regs [])) a12r_jss
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A12_RETR)) mem (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold a12r_jss. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs []))) by apply Eimg_env.
assert (HA0 : env_agree 32 (Ereg regs []) (Eimg (Ereg regs [])))
  by (split; [intros k Hk; rewrite Eimg_low by (unfold A_TEXT; lia); reflexivity | reflexivity]).
paj_run_to_shc (SRr_run_to_pi_AJ (fx := fx) B LAWS) HS HJ PF_RS3.
{ unfold a12r_jss. cbn [ss_mem]. apply awr_ok_nil. }
assert (Hmem : ms_mem ms = mem).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & _). unfold a12r_jss in Hr. cbn [ss_mem In] in Hr. destruct Hr. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ |- *.
assert (HPR : aregs_preserved regs (ms_regs ms)).
{ unfold st_ok_pi in HS.
  exact (aregs_preserved_of_st_ok SEGS _ _ _ _ regs [] HS HA0 ltac:(vm_compute; reflexivity)). }
assert (HINV' : INV_RS3 B n v pos ly S W (ms_regs ms) mem mdq cf cur nm o ln d).
{ split; [|split; [exact HMID|split; [exact HST|]]].
  - split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
    refine (conj HJ (conj Hly (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM _))))))).
    exact (a5_rg_pres regs (ms_regs ms) (a5_FI B v) HPR (a5_FI_cs B v) HRG0).
  - apply (a5_rg_pres regs (ms_regs ms) _ HPR); [|exact HRG].
    unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. }
exact (HRS3 v pos ly S W (ms_regs ms) mem mdq cf cur nm o ln d HINV').
Qed.

End j.

(** ** The block: 0x88414 .. 0x8842c, refuse, then a12r_j at the FP state refuse returned *)
Section s.
Context {fx : YK11.FPState}.

Lemma a12_ref_blk : forall n v pos lyc Sc (Wc : world SEGS) rX memc mdc cf nm o ln d gi vp val z3,
  a12_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 ->
  HA_RS3 B n ->
  SRr SEGS Wc (mkCfg (mkst rX (Z_to_bv 64 (BASE + A12_REFS)) memc (seg_rom SEGS)) mdc)
    (pf_postm B v (refuse cf (ln + 1) F_badignore [AS nm; AS val], Some gi, nm) o ln).
Proof.
intros n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 HI HRS3.
pose proof HI as (HB & HMID & HST & HVstr & HVinb & HRG).
pose proof (a5_geo B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as (HAR & Hly & Hfin & G & _).
pose proof G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _).
pose proof (a5_fi_regs B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as HFI.
destruct (a5_chain B v pos lyc Sc Wc rX memc mdc PF_SC_LINE HB) as [ch1 HCH].
pose proof HB as (HCX & (HJ & Hly' & HFS & HPERM & HSV & HFL & HFRM & _) & HOBJ & HSL & HFSH).
pose proof HOBJ as (_ & _ & _ & _ & HCH0 & _).
pose proof HST as (HRC & HOK & HNM & HCNT).
pose proof HMID as (Ho & _ & _).
pose proof STK_values as (_ & SRF & _ & SPF & _).
pose proof asan_consts as (K1 & K2 & K3 & K4 & K5).
pose proof (a6_s1 (pf_sp0 v) G3) as (S1a & S1b & S1c & S1d). rewrite <- a6_s1_eq in S1a, S1b, S1c, S1d.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (a6_heap_bounds B lyc Sc Wc memc mdc (p_c v) seg_spec.SEG_C_SIZE HAR HCH0
  ltac:(unfold seg_spec.SEG_C_SIZE; lia)) as (bc & mc & Hinc & Hc1 & Hc2 & _).
(* the registers the cut names *)
assert (R24 : getr rX 24 = w64 (p_c v))
  by (exact (a5_rg_get rX _ 24 _ HRG ltac:(cbn [PF_RM app In]; tauto))).
assert (R25 : getr rX 25 = w64 vp)
  by (exact (a5_rg_get rX _ 25 _ HRG ltac:(cbn [PF_RM app In]; tauto))).
assert (R26 : getr rX 26 = w64 (ln + 1))
  by (exact (a5_rg_get rX _ 26 _ HRG ltac:(cbn [PF_RM app In]; tauto))).
(* the seed at REFS, without the writable region of cur's two words (nothing is stored before the call) *)
pose proof (a12_seed_I B n v pos lyc Sc Wc rX memc mdc cf nm o ln d gi vp val z3 A12_REFS HI) as HS0.
pose proof (st_ok_pi_submem _ _ _ (firstn 2 a12_regions) HS0
  ltac:(unfold a12_ss, a12_regions; cbn [ss_mem firstn];
        apply submem_keep; [apply subregion_refl|]; apply submem_keep; [apply subregion_refl|]; apply submem_nil)
  ltac:(vm_compute; reflexivity)) as HS.
clear HS0.
assert (HEI : img_env VAL A_LIM (a12_E rX v pos val)) by (unfold a12_E; apply Eimg_env).
(* 0x88414 .. 0x8842c: a2 = F_badignore's literal, a0 = c, a1 = lineno, a3 = cur_name, a4 = val, the call *)
paj_run_shc (SRr_run_pi_AJ (fx := fx) B LAWS) (SRr_run_pi_AJ_call (fx := fx) B LAWS) HS HJ.
{ a12r_awr. }
assert (Hmem : ms_mem ms = memc).
{ apply functional_extensionality. intros x. unfold frame_of in HF. rewrite HF; [reflexivity|].
  intros (r & Hr & Ha). vm_compute in Hr.
  destruct Hr as [<- | [<- | []]]; cbn [YP09.r_base YP09.r_wlo YP09.r_whi] in Ha; lia. }
lazymatch goal with |- SRr _ _ (mkCfg _ ?dM) _ => set (mdq := dM) in *; clearbody mdq end.
pmkst HS. rewrite Hmem in HJ |- *.
clear HF HFr HG.
(* the callee-saved registers are the cut's *)
pose proof (aregs_preserved_of_st_ok SEGS _ _ _ _ rX (a12_extra v pos val) HS (a12r_E_agree rX v pos val)
  ltac:(vm_compute; reflexivity)) as HPR.
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
{ unfold spZ. rewrite C2. unfold w64. apply unsigned_lit_small. lia. }
(* the call's registers *)
prreg HS (1%bv : bv 5) Q1. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13. prreg HS (14%bv : bv 5) Q14.
assert (C1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + A12_RETR)).
{ rewrite Q1. unfold A12_RETR, AF_reac_segconf_parse_file. reflexivity. }
assert (C10 : getr (ms_regs ms) 10 = w64 (p_c v)).
{ rewrite Q10, (a12r_ew_reg rX v pos val 24 24%bv eq_refl). exact R24. }
assert (C11 : getr (ms_regs ms) 11 = w64 (ln + 1)).
{ rewrite Q11, (a12r_ew_reg rX v pos val 26 26%bv eq_refl). exact R26. }
assert (C12 : getr (ms_regs ms) 12 = w64 (seg_litA_rc F_badignore)).
{ rewrite Q12. change 295%nat with (A_OBJ 54). exact (a12r_lit _ HEI). }
assert (C13 : getr (ms_regs ms) 13 = w64 (pf_F v pos + PF_O_CN)).
{ rewrite Q13, a12r_ew_F. unfold w64, PF_O_CN. rewrite unsigned_lit_small by lia. reflexivity. }
assert (C14 : getr (ms_regs ms) 14 = w64 vp).
{ rewrite Q14, (a12r_ew_reg rX v pos val 25 25%bv eq_refl). exact R25. }
assert (Hret : YK0s.ret_ok (getr (ms_regs ms) 1)).
{ rewrite C1. apply ret_ok_codeptr_v; [unfold A12_RETR, AF_reac_segconf_parse_file; lia | reflexivity]. }
(* the cut's facts at the call state: its memory is the cut's, its journal the run's *)
assert (HBc : pf_base B v pos lyc Sc Wc (ms_regs ms) memc mdq PF_SC_LINE).
{ split; [exact HCX|]. split; [|exact (conj HOBJ (conj HSL HFSH))].
  refine (conj HJ (conj Hly' (conj HFS (conj HPERM (conj HSV (conj HFL (conj HFRM _))))))).
  exact (a5_rg_pres rX (ms_regs ms) (a5_FI B v) HPR (a5_FI_cs B v) HFI). }
(* VERIFY rule 1j-bis at 0x8842c: refuse_contract's premises besides afn_pre, pf_a12_s.v's closed site lemma *)
pose proof (a12_ref_site B v pos lyc Sc Wc rX memc mdc (ms_regs ms) cf nm o ln d n gi vp val HB HRC
  (pf_cnt_mono cf _ 0 (Nat.le_0_l _) HCNT) HMID HNM HVstr HVinb Csp Hret C3 C4 C10 C11 C12 C13 C14)
  as (ROD & Hc64 & Hl64 & Hf64 & RPRE & ROOM & EV).
rewrite (SIGP SS_refuse ltac:(unfold seg_prog_syms; cbn [In]; repeat (first [left; reflexivity | right]))).
replace (seg_af SS_refuse) with AF_refuse by (vm_compute; reflexivity).
eapply SRr_bind.
{ eapply (cl_callSF (fx := fx) B LAWS Wc (ms_regs ms) memc _ STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdq 0
    STK_refuse (refuse_W (p_c v) cf) EV_refuse (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + A12_RETR)) ch1
    (fun ly2 S2 W2 regs2 mem2 md2 =>
       sa_rconf (rdW W2 mem2) (p_c v) (refuse cf (ln + 1) F_badignore [AS nm; AS val]) /\
       sa_noalloc B lyc Sc ly2 S2) HJ).
  - rewrite Csp. lia.
  - exact S1d.
  - lia.
  - rewrite SRF. lia.
  - rewrite SRF, SPF. lia.
  - exact C3.
  - exact C4.
  - exact C1.
  - apply ret_ok_codeptr_v; [unfold A12_RETR, AF_reac_segconf_parse_file; lia | reflexivity].
  - rewrite unsigned_lit_small by (unfold A12_RETR, AF_reac_segconf_parse_file; lia).
    unfold A12_RETR, AF_reac_segconf_parse_file. lia.
  - replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) by lia.
    unfold s0Z. rewrite C8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH.
  - intros HPRE1. eapply SRr_mono.
    { exact (REFUSE fx lyc Sc Wc (ms_regs ms) memc mdq ch1 (p_c v) (ln + 1) (seg_litA_rc F_badignore) (ln + 1) cf
        F_badignore [AS nm; AS val] HPRE1 ROD C10 Hc64 C11 Hl64 C12 Hf64 RPRE ROOM EV). }
    cbv beta. intros W' c' _ (fx' & ly' & S' & regs' & mem' & md' & -> & Hf1 & Hf2 & HJ' & HP' & HK').
    exists fx', ly', S', regs', mem', md'. split; [rewrite C1; reflexivity|].
    split; [exact Hf1|]. split; [exact Hf2|]. split; [exact HJ'|]. split; [exact HP' | exact HK'].
  - intros a Ha. left. split; [exact (a6_refuse_W_sub _ _ a Ha)|].
    apply a6_refuse_W_in_block in Ha. exists bc, mc. split; [exact Hinc|].
    unfold seg_spec.RC_REFUSAL, seg_spec.RC_OVERFLOW, seg_spec.SEG_C_SIZE in *. lia. }
(* back at 0x88430 = BASE + A12_RETR, at the FP state fx1 refuse returned *)
cbv beta. intros W2 c2 _ (fx1 & ly2 & S2 & regs2 & mem2 & md2 & Hfx1 & -> & HJ2 & HJc2 & HP2 & (HRC2 & HNA2)).
unfold pf_postm, PF_POSTr.
eapply (srr_apost_baseF_lift SEGS fx1); [exact Hfx1|].
replace (pf_sp0 v + (pf_s1 v - pf_sp0 v)) with (pf_s1 v) in HJc2 by lia.
replace (0 + EV_refuse) with 0 in HJ2 by (unfold EV_refuse; lia).
assert (HPR2 : aregs_preserved rX regs2) by exact (aregs_preserved_trans _ _ _ HPR HP2).
(* pf_base and cur_name at the returned state (pf_a12_s.v, through pf_a6_k.v) *)
destruct (a12_ref_after (fx := fx) B VRO SSPX fx1 v pos lyc Sc Wc (ms_regs ms) memc mdq ly2 S2 W2 mem2 md2 regs2
  cf HBc Hfx1 HJc2 HJ2 HNA2 (a5_rg_pres rX regs2 (a5_FI B v) HPR2 (a5_FI_cs B v) HFI)) as (HB2 & HNM2 & _ & _).
assert (HINV2 : INV_RS3 (fx := fx1) B n v pos ly2 S2 W2 regs2 mem2 md2
  (refuse cf (ln + 1) F_badignore [AS nm; AS val]) (Some gi) nm o ln d).
{ split; [exact HB2|]. split; [exact HMID|]. split.
  - split; [exact HRC2|]. split.
    + cbn [pf_cur_ok] in HOK |- *. rewrite (proj1 (refuse_proj cf (ln + 1) F_badignore [AS nm; AS val])). exact HOK.
    + split; [exact (HNM2 nm HNM)|].
      exact (pf_cnt_refuse cf (ln + 1) F_badignore [AS nm; AS val] _ _ (pf_next_skipn_lt (p_s v) o Ho) HCNT).
  - apply (a5_rg_incl regs2 ([(18, 0x23); (19, z3); (24, p_c v); (27, pf_SH v pos)] ++ PF_RM v o ln ++
            [(20, seg_spec.rseg_addr (p_c v) gi); (25, vp)])).
    + intros x Hx. unfold PF_RM in Hx |- *. cbn [app In pf_cur_ptr] in Hx |- *. tauto.
    + apply (a5_rg_pres rX regs2 _ HPR2); [|exact HRG].
      unfold PF_RM. cbn [app]. repeat apply Forall_cons; try apply Forall_nil; cbn [fst]; unfold acallee_saved; lia. }
(* 0x88430 j 0x88100 at fx1, then RS3 *)
exact (a12r_j (fx := fx1) n v pos ly2 S2 W2 regs2 mem2 md2 (refuse cf (ln + 1) F_badignore [AS nm; AS val])
  (Some gi) nm o ln d HINV2 (HRS3 fx1)).
Qed.

End s.

End e.
End f.
End d.
