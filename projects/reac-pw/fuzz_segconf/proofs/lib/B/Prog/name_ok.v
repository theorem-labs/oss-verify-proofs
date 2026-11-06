(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk of mix_call (plugin-hostd/fuzz_command,
   fuzz_command.asan-ubsan, entry BASE + AF_mix_call = 0x8ad54, 480 bytes, 120 instructions): tmix_call_spec of
   a Theorem Labs lane's lib/B/Prog/mix_call_c.v (blob ebd1fd295d8, the same on a working branch f490061c104 and 707acd856cb), proved in the A walk's
   style (lib/A/Prog/mix_call.v, a working branch fa7944d852b): the verified symbolic executor over
   cmd_listing (paj_run_tok / paj_run_to_tok / psrr_branch_tok, lib/B/Prog/CmdPaLib.v), the inline shadow checks
   removed by the token executor with their addressability obligations, the strlen wrapper through its Theorem Labs lane
   contract taken at the current FP state, and one lemma per loop (the 4 bytes of c->fn run straight; the argument
   loop and the byte loop are inductions over a re-seeded loop head).

   The B code, measured with capstone on the pinned fuzz_command.asan-ubsan (.symtab: mix_call LOCAL FUNC 0x8ad54,
   480 bytes), is A's code with a 96-byte frame (ra, s0-s10), other registers and the UBSan checks:
     0x8ad54 .. 0x8ad84  the frame; 0x8ad88 beqz a1 -> trap; 0x8ad94 bnez (c & 7) -> trap
     0x8ad98 / 0x8ada8   the two auipc pairs: the shadow-base GOT word 0xa5f50 (A_OBJ 0) and the FNV-1a offset
                         basis 0x10330 (A_OBJ 58), both object atoms bridged by VOBJS (no A_HI value: no VHIS)
     0x8adc8 .. 0x8adf8  the 4 bytes of c->fn (a4 counts 4 -> 0), each with 0x8adcc bgeu 1, b + 1 -> trap and the
                         load1 check 0x8add8 (slow path 0x8ae00, report 0x8ae08)
     0x8ae0c .. 0x8ae24  the load4 check on c->nargs 0x8ae18 (slow path 0x8af20, report 0x8af2c), blez nargs
     0x8ae28 .. 0x8ae4c  a := 0 (s4), s5 := c + 8, s6 := basis, s7 := ~s5, s8 := nargs, s9 := INT_MAX, s10 := 1
     0x8ae50 .. 0x8ae74  argument loop: 0x8ae54 bltu s7, 8a -> trap; load8 check 0x8ae64 (report 0x8af30);
                         s1 := c->args[a]; jal __interceptor_trampoline_strlen 0x4517c (at 0x8ae74)
     0x8ae78 .. 0x8ae84  basis if the digest is 0, a1 := len + 1, into the byte loop
     0x8ae88 .. 0x8ae94  0x8ae88 beq a, INT_MAX -> trap; a := a + 1; 0x8ae90 beq a, nargs -> epilogue
     0x8ae9c .. 0x8aed0  byte loop: 0x8aea0 bgeu 1, b + 1 -> trap; load1 check 0x8aeac (slow path 0x8aed4, report
                         0x8aedc); digest step; back to 0x8ae88 after the terminator
     0x8aee0 .. 0x8af18  epilogue; 0x8af1c unimp (the one UBSan trap)

   Report / trap edges, each refuted at its branch:
     0x8ad88 (c = NULL -> 0x8af1c): decided by the executor's decide_cond2 (lib/Reusable/YP0e.v:932, sound by
       decide_cond2_sound :981) in mc_core's first run, from the slot premise (atom 11's fact A_G_REC <= c in
       mc_facts0, established in mc_entry).
     0x8ad94 (c mod 8 <> 0 -> 0x8af1c): the same, from the slot premise (atom 11's alignment 2 ^ 3 in mc_facts0).
     0x8adcc (b + 1 <= 1 over c->fn -> 0x8af1c), 4 times: the same, in mc_core's second run (atom 11's range).
     0x8add8 -> 0x8ae00 -> 0x8ae08 (__asan_report_load1 on c->fn): removed by the token executor, whose obligation
       is range_addressable at c + k (OBL in mc_core), from the slot premise by mc_rec_addr (CmdZsh's
       cmd_addressable_in over the record's zero-shadow ranges of g_rec and record.spill, lib/B/YF0m.v:4650-4651).
     0x8ae18 -> 0x8af20 -> 0x8af2c (__asan_report_load4 on c->nargs): the same (OBL in mc_core).
     0x8ae54 (c + 8 + 8a overflows -> 0x8af1c): at a = 0 (mc_core) refuted by mc_ltu0 (s7 < 0 unsigned never
       holds); at a + 1 (mc_inc) decided by the executor from ss_inc's facts (atom 23 = ~(c + 8) >= MC_NOTC
       A_REC_SPILL, atom 20 = a <= 5), from the slot premise and acall_at's nargs <= 6.
     0x8ae64 -> 0x8af30 (__asan_report_load8 on c->args[a]): removed by the token executor in mc_args, its
       obligation discharged by mc_rec_addr from the slot premise.
     0x8ae88 (a = INT_MAX -> 0x8af1c): decided by the executor in mc_inc from ss_inc's facts (atom 20 = a <= 5,
       atom 25 = s9 = 0x7fffffff), from acall_at's nargs <= 6.
     0x8aea0 (b + 1 <= 1 over an argument -> 0x8af1c): decided by the executor in mc_bytes from mc_bl_facts (atom
       10 = b >= 4096, atom 26 = s10 = 1), from acall_at's argument block (AR's block law al_blocks).
     0x8aeac -> 0x8aed4 -> 0x8aedc (__asan_report_load1 on an argument's bytes): removed by the token executor in
       mc_bytes, its obligation discharged by range_addressable_of_block (AR's block law) from acall_at.

   Section hypotheses beyond the statement's (ASTRLEN, VOBJS): the per-binary allocator record CmdBSyms (HB), and
   the per-binary image facts in the form of a Theorem Labs lane's lib/B/Prog/CmdRecImg.v cmd_img_facts_tfib at this walk's
   abstract segments (used for CmdRecCells' cmd_cf_env, the errno / trace facts of the runtime-entry call). The
   shadow-cell and GOT facts are CmdRecCells' cmd_cf_cell / cmd_cf_got (HB + VOBJS), the AR laws AR_laws_ok.

   TAKEN FROM: the A walk lib/A/Prog/mix_call.v (a working branch fa7944d852b), re-walked at the B
   addresses above; the Generation-N B walk lib/B/Prog/mix_call.v (a working branch a3f99d62c52) read as a
   template of the B code only, not ported and not required. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/B/Prog/mix_call.v, with its module paths, module names and numbers changed; 698 of its 886 lines of code are new or changed and 1051 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/name_ok_s1.v, with its module paths and module names changed; 116 of its 205 lines of code are new or changed and 797 lines of the source are left out. *)
(* The image-B port of lib/A/Prog/name_ok.v (commit ce5629fa227b), part 2: the ASan+UBSan walk
   of name_ok on fuzz_segconf image B (fuzz_segconf.asan-ubsan, entry BASE + AF_name_ok = 0x8a408): `name_ok_walk`
   proves name_ok_contract (lib/B/Prog/name_ok_c.v, image B's copy of the FINAL contract text) at image B's numbers, over
   the Pa engine of image B's listing seg_listing, from the contract of its one callee, musl's isalnum (row 9,
   RtSeg.aisalnum_realizes, image B's copy lib/B/Rt/RtSeg.v). This file holds the loop (NK_L, the call of isalnum,
   induction on the bytes left) and the theorem; the call-free stretches (the entry, NK_B, NK_R, NK_N with its UBSan
   trap branch, NK_X) and the invariant are in lib/B/Prog/name_ok_s1.v, whose header lists the labels, the A-to-B
   differences and the 5 instructions not walked. Plan: the unit record's Bwalks-G45-plans/plan-name_ok.md.

   Image-B numbers, image B's instance file's (lib/B/Prog/SegInstB.v): SegInstB.RLO_A / RHI_A, the read-only window
   of arodata_okP (image B's SegGlob.SEG_RLO / SEG_RHI, 0xa1c60 / 0xa3f08, .data.rel.ro start and .got end), and
   SegInstB.STK_name_ok = 64 + ESTACK (named STK_name_ok_B in name_ok_s1.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegSyms SegList SegPa SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaSB PaArt SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel SegBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec isalnum_c.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import name_ok_lem name_ok_c name_ok_s1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require SegInstB.

Import ListNotations.
#[local] Unset Lia Cache. #[local] Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Lemma nk_b2z_eq : forall b : bool, seg_spec.b2z b = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.
Lemma nk_set_fs_id : forall S : astate, S = set_fs (st_fs S) S.
Proof. intros [a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12]. reflexivity. Qed.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).

Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let STK : Z := STK_name_ok_B.
Let HSTK : 64 <= STK := ltac:(unfold STK, STK_name_ok_B, ESTACK; lia).
Let HSTKE : 64 + ESTACK <= STK := ltac:(unfold STK, STK_name_ok_B; lia).

Let RUN := paj_run B LAWS.

(* The contract of the callee: row 9, musl's isalnum at image B 0x9094c (a direct call, not intercepted; a 28-byte
   leaf that touches no stack and no memory), at the listing's call target `pa_sigma SS_isalnum`. Its text is
   lib/B/Rt/RtSeg.v's (commit 5b814360ea8f), word for word image A's. *)
Hypothesis ISALNUM : forall fx0 : YK11.FPState, @RtSeg.aisalnum_realizes fx0 rc SEGS B (SIGMA SS_isalnum).

(* NK_L, 0x8a474: zext.b a0,s6; jal isalnum; the answer comes back at NK_R *)
Definition ss_nk_l : sstate := mkSS NK_L sr_atoms [] None
(mkFacts [(2%nat, mkAF (2^46) (2^47) 4); (8%nat, mkAF 4096 (2^47 - 1) 0); (9%nat, mkAF 4096 (2^47 - 1) 0);
          (18%nat, mkAF SB SB 0); (19%nat, mkAF 50 50 0); (20%nat, mkAF NK_MASK NK_MASK 0);
          (21%nat, mkAF NK_M1 NK_M1 0); (22%nat, mkAF 1 255 0)] [] []).

Lemma nk_loop : forall (j : nat) (nm : list Z) W ly S mem0 md0 regs0 regs memc mdc s k,
(k + j = length nm)%nat -> (0 < j)%nat ->
nk_inv B ly S W mem0 md0 regs0 memc mdc -> YK0s.ret_ok (getr regs0 1) ->
getr regs0 3 = w64 (as_gp B) -> getr regs0 4 = w64 (as_tp B) ->
nk_str W mem0 (spZ regs0) s nm ->
nk_regsL regs0 regs (s + Z.of_nat k) (nth k nm 0) ->
SegModel.name_ok nm = forallb nk_ch (skipn k nm) ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + NK_L)) memc (seg_rom SEGS)) mdc)
(nk_post B regs0 ly S W mem0 md0 (Z.b2z (SegModel.name_ok nm))).
Proof using LAWS TL HSTK HSTKE ISALNUM.
induction j as [|j IH]; intros nm W ly S mem0 md0 regs0 regs memc mdc s k Hkj Hj HI Hra Hgp0 Htp0 HSTR HRL HM;
[lia|].
pose proof HRL as (H2 & H18 & H19 & H20 & H21 & H8 & H9 & H22 & HK0).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof HI as (HJ & HLOW & HSV).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof HSTR as (HB0 & HNZ & HRA & Hs4 & Hs47 & HWIN).
assert (HSTKn : STK = 4160) by (unfold STK, STK_name_ok_B, ESTACK; reflexivity).
assert (Hk : (k < length nm)%nat) by lia.
set (c := nth k nm 0) in *. set (p := s + Z.of_nat k) in *.
pose proof (nk_str_byte W mem0 (spZ regs0) s nm k HSTR Hk) as Hc.
remember (Eimg (Ereg regs [])) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs []) E) by (rewrite HE; split; [intros k0 Hk0; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EN : forall k0 (r0 : bv 5), Z.of_nat k0 = bv_unsigned r0 -> (k0 < 32)%nat -> ew E k0 = getr regs r0).
{ intros k0 r0 Hk0 Hk32. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hk0. }
assert (E2 : ew E 2 = w64 (spZ regs0 - 64)) by (rewrite (EN 2%nat 2%bv eq_refl) by lia; exact H2).
assert (E8 : ew E 8 = w64 p) by (rewrite (EN 8%nat 8%bv eq_refl) by lia; exact H8).
assert (E9 : ew E 9 = w64 (p + 1)) by (rewrite (EN 9%nat 9%bv eq_refl) by lia; exact H9).
assert (E18 : ew E 18 = w64 SB) by (rewrite (EN 18%nat 18%bv eq_refl) by lia; exact H18).
assert (E19 : ew E 19 = w64 50) by (rewrite (EN 19%nat 19%bv eq_refl) by lia; exact H19).
assert (E20 : ew E 20 = w64 NK_MASK) by (rewrite (EN 20%nat 20%bv eq_refl) by lia; exact H20).
assert (E21 : ew E 21 = w64 NK_M1) by (rewrite (EN 21%nat 21%bv eq_refl) by lia; exact H21).
assert (E22 : ew E 22 = w64 c) by (rewrite (EN 22%nat 22%bv eq_refl) by lia; exact H22).
assert (Usp : bv_unsigned (ew E 2) = spZ regs0 - 64) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E ss_nk_l (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + NK_L)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_nk_l. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- constructor.
- cbn [pairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E2, E8, E9, E18, E19, E20, E21, E22. unfold w64, NK_MASK, NK_M1.
  rewrite !unsigned_lit_small by (unfold SB; subst p; lia).
  change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
  assert (Hm16 : (spZ regs0 - 64) mod 16 = 0) by (rewrite Zminus_mod, Hal16; reflexivity).
  subst p. revert Hslo Hshi H47 Hceil C1 Hstk0 Hm16 Hs4 Hs47 Hc HSTK HSTKE. clear - Hk. unfold SB, ESTACK. intros.
  repeat match goal with |- _ /\ _ => split end; lia. }
clear HE.
assert (SHOK : sh_ok SEGS (SOff 18 0) [] E (mrestrict (w_H W) memc)) by constructor.
paj_run_tok RUN HS HJ SHOK Bspan.
{ awr_ok_tac. }
pose proof (nk_inv_run B ly S W mem0 md0 regs0 memc mdc (ms_mem ms) _ E [] HI HJ HFr ltac:(vm_compute; reflexivity)) as HI1.
clear HF HFr HG.
pose proof HI1 as (_ & HLOW1 & HSV1).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (10%bv : bv 5) R10.
rewrite E2 in R2.
rewrite (EN 3%nat 3%bv eq_refl), (HK0 3%bv ltac:(cbv; tauto)), Hgp0 in R3 by lia.
rewrite (EN 4%nat 4%bv eq_refl), (HK0 4%bv ltac:(cbv; tauto)), Htp0 in R4 by lia.
assert (Hsp1 : spZ (ms_regs ms) = spZ regs0 + -64)
  by (unfold spZ at 1; rewrite R2; unfold w64; rewrite unsigned_lit_small by lia; lia).
assert (Hraw : YK0s.ret_ok (getr (ms_regs ms) 1))
  by (rewrite R1; apply ret_ok_codeptr_v; [unfold NK_R; lia | reflexivity]).
assert (R10c : getr (ms_regs ms) 10 = w64 c).
{ rewrite R10, ?E22. unfold w64. apply (nk_zext_byte E c). lia. }
lazymatch type of HS with st_ok _ ?Ecur _ _ => assert (HAEc : env_agree 32 (Ereg regs []) Ecur) by (env_agree_chain HAE) end.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ NK_KR HS HAEc ltac:(vm_compute; reflexivity)) as KA.
cbn [ms_regs restrict] in KA.
pmkst HS.
eapply SRr_bind.
{ eapply (aj_art_at SEGS B LAWS pa_segs_low (pal_env B TL) ESTACK (fun _ => False) (SIGMA SS_isalnum)
    W (ms_regs ms) (ms_mem ms) STK (spZ regs0) [] ly S W mem0 md0 [] ly S _ 0 (-64) (getr (ms_regs ms) 1)
    (fun regs' (_ : word -> option byte) => getr regs' 10 <> w64 0 <-> RtSeg.alnum_b c = true) HJ).
  1: exact Hsp1. 1: reflexivity. 1: lia. 1: unfold ESTACK; lia. 1: unfold ESTACK; lia. 1: reflexivity.
  1: intros a' [].
  eapply (ISALNUM _ ly S W (ms_regs ms) (ms_mem ms) _ c).
  - eapply (ecall_pre_stk_at SEGS B ESTACK STK (spZ regs0) [] ly S W mem0 md0 [] ly S W (ms_mem ms) _ 0
      (ms_regs ms) (-64) HJ);
    [exact Hsp1 | reflexivity | lia | lia | unfold ESTACK; lia | exact Hraw | exact R3 | exact R4].
  - exact R10c.
  - lia. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha2 & Hfr2).
rewrite R1.
assert (HI2 : nk_inv B ly S W mem0 md0 regs0 mem2 md2).
{ split; [exact HJ2|]. unfold ESTACK in Hfr2. split.
  - apply (nk_low_kept W mem0 (ms_mem ms) mem2); [|exact HLOW1].
    intros a' Ha'. apply Hfr2; [lia | lia | intros []].
  - apply (nk_saved_kept W (ms_mem ms) mem2); [|exact HSV1].
    intros a' Ha'. apply Hfr2; [lia | lia | intros []]. }
assert (P2 : forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr (ms_regs ms) r).
{ intros r Hr. specialize (HP2 (bv_unsigned r) Hr). rewrite !Z_to_bv_bv_unsigned in HP2. exact HP2. }
assert (CH2 : forall r, In r NK_KR -> getr regs2 r = getr regs r).
{ intros r Hr. cbv [NK_KR In] in Hr.
  repeat (destruct Hr as [<- | Hr];
    [ rewrite P2 by (unfold acallee_saved;
        match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in
          change (bv_unsigned x) with v end; lia);
      apply KA; cbv; tauto |]). destruct Hr. }
set (r2 := bv_unsigned (getr regs2 10)).
assert (Hr2 : getr regs2 10 = w64 r2) by (subst r2; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (Hr2r : 0 <= r2 < 2 ^ 64) by (subst r2; pose proof (bv_unsigned_in_range 64 (getr regs2 10)) as Hq;
  change (bv_modulus 64) with (2 ^ 64) in Hq; exact Hq).
assert (HAL : r2 <> 0 <-> SegModel.isalnum c = true).
{ change (RtSeg.alnum_b c) with (isalnum_c.alnum_b c) in Ha2.
  rewrite <- (SegBridge.bridge_isalnum c ltac:(lia)). split.
  - intros Hne. apply Ha2. rewrite Hr2. unfold w64. intros Heq.
    apply Hne. apply (f_equal bv_unsigned) in Heq. rewrite !unsigned_lit_small in Heq by lia. exact Heq.
  - intros Hal Hz. apply (proj2 Ha2 Hal). rewrite Hr2, Hz. reflexivity. }
apply (nk_after B LAWS nm W ly S mem0 md0 regs0 regs2 mem2 md2 s k r2 HI2 Hra HSTR Hk);
  [ refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))) | exact Hr2 | exact Hr2r | exact HAL
  | exact HM | ].
- rewrite CH2 by (cbv; tauto). exact H2.
- rewrite CH2 by (cbv; tauto). exact H18.
- rewrite CH2 by (cbv; tauto). exact H19.
- rewrite CH2 by (cbv; tauto). exact H20.
- rewrite CH2 by (cbv; tauto). exact H21.
- rewrite CH2 by (cbv; tauto). exact H8.
- rewrite CH2 by (cbv; tauto). exact H9.
- rewrite CH2 by (cbv; tauto). exact H22.
- intros r0 Hr0. rewrite CH2 by (cbv in Hr0 |- *; tauto). apply HK0. exact Hr0.
- (* the byte passed: the next turn of the loop, by the induction hypothesis at k + 1 *)
  intros Hlt Hinv regs' memc' mdc' HI' HRL'.
  apply (IH nm W ly S mem0 md0 regs0 regs' memc' mdc' s (Datatypes.S k));
  [ lia | lia | exact HI' | exact Hra | exact Hgp0 | exact Htp0 | exact HSTR | exact HRL' | exact Hinv ].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
Theorem name_ok_walk : name_ok_contract SEGS B (BASE + AF_name_ok) SegInstB.STK_name_ok SegInstB.RLO_A SegInstB.RHI_A.
Proof using LAWS TL HSTK HSTKE ISALNUM.
unfold name_ok_contract.
intros ly S W regs mem md ch s nm HPRE HROD H10 Hs64 HPRES HEV.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (nk_pre_str B LAWS ly S W regs mem md s nm HAR Hstk HPRES) as HSTR.
pose proof HSTR as (HB0 & HNZ & HRA & Hs4 & Hs47 & HWIN).
eapply SRr_mono.
- apply (nk_head B LAWS TL W ly S regs mem md ch s nm HPRE H10 HSTR).
  intros Hlt regs' memc' mdc' HI' HRL'.
  apply (nk_loop (length nm) nm W ly S mem md regs regs' memc' mdc' s 0);
  [ lia | lia | exact HI' | exact Hra | exact Hgp | exact Htp | exact HSTR | exact HRL' | ].
  apply nk_start; [intros Enil; rewrite Enil in Hlt; cbn [length] in Hlt; lia | exact HNZ].
- cbv beta. intros W' c' _ (ly' & S' & regs' & mem' & md' & -> & HJ & HP & (HQ & -> & -> & HKEPT)).
  exists ly, S, regs', mem', md'. split; [reflexivity|]. split; [exact HJ|]. split; [exact HP|].
  split; [rewrite nk_b2z_eq; exact HQ|].
  split; [intros a Ha Hw _; exact (HKEPT a Ha Hw)|].
  split; [apply Permutation_refl|]. split; [reflexivity | exists (st_fs S); apply nk_set_fs_id].
Qed.

End e.
End f.
End d.
