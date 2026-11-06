(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of lib/A/W_send_line_cx.v, the interface of the send_line walk
   (step 1 of route (b)), from its text at a78a220dc8e (sha256 16a473213818; internal record,
   the kit's too). W_send_line_cx.v is NOT edited: this file sits beside it, and every walk that cites it builds
   unchanged.
   - Each AR-stated definition or lemma NAME of W_send_line_cx.v has its twin NAME_x here, in its Section nesting, over
     a Section relation `ARx` (its third argument the ghost list Hp), the laws `LAWS : AR_laws_x SEGS B ARx hl`
     (YCbqG.v:184) and the placement parameter PST of the journal W_journal_x.ajournal_gx_x. PST and ARx follow B among
     the Section variables, so a twin's arguments are the original's with PST ARx after B.
   - The entry's ghost list Hp follows S (SLI_x, sl_loop_stmt_x, sl_epi_x); the loop head's own ghost list HpL is an
     existential right after SL in SLI_x; sl_epi_x's journal ends at HpX (after SX), which its continuation keeps.
   - The Section hypotheses are their twins: AERRNO W_sites_x.aerrno_realizes_x, AMEMCPY W_sites_x.aintrin_realizes_x,
     AREALLOC W_journal_x.arealloc_cf_rule_c_x (caller-context form, CTX_R / HCTX_slr); the run chain RUN / RUNTO is W_journal_x's paj_run_x_x /
     paj_run_to_x_x. The other hypotheses name no AR and are W_send_line_cx.v's text.
   - sl_epi_x is proved: W_send_line_cx.v's proof with W_kit_x.v's paj_run_tok_x and W_journal_x.v's
     ajournal_gx_materialize_x (ajournal_x has YCbq.ajournal's conjuncts in the same order).
   - The AR-free names of W_send_line_cx.v are CITED, not copied: A_send_line A_send_lineP A_sl_loop A_sl_epi SL_SAVED
     sl_saved Bspan BxX epi_regions epi_facts ss_epi epi_extra nth_epi_extra sl_epi_entry sl_regsL.
   - The BRIDGES: Section br at ARx := W_journal_x.ARi (cgif's AR, Hp ignored), PST := []: SLI_x, sl_loop_stmt_x and
     sl_entry_stmt_x are iff-equal to the originals at every Hp, and sl_epi_x gives sl_epi from
     `LX : AR_laws_x SEGS B ARi 0`. Section br0 at ARx := W_journal_x.ARi0 (AR /\ Hp = [], a Theorem Labs lane's HP0 ruling),
     PST := []: for SLI the two one-directional forms SLI_x_AR0 (generic -> AR, any Hp) and SLI_x_of_AR0 (AR -> generic,
     any Hp, HpL := []), and for each statement *_x_AR0 (generic at ARi0 -> AR) and *_x_of_AR0 (AR -> generic at ARi0).
   No statement difference is forced by ARx: no premise or conclusion is added or dropped, only Hp threaded.
   THE ROOM FORM (a Theorem Labs lane, row A-SL_x of a Theorem Labs lane's FREE-PIECES, 2026-10-30; base A top 7ee1e6d5094, from W7's
   stopped 7561b427559): the Section gains `Variable RP : roomp` after MT, as W_contract_x.v Section s7, whose sl_spec_x
   and sl_post_x take it; AREALLOC is W_journal_x.arealloc_cf_rule_c_x at RP and CTX_R; HP0 (a Theorem Labs lane's HP0 ruling) joins LAWS.
   SLI_x carries C3's peak (W_send_line_cx.v SLI at 76be6190eff: tr_peak of send_line_tr) and, after frames, three
   room conjuncts: the room budget of the rounds still to come (sl_cost_run at W_contract_x.MT_rk, on top of the
   caller's kr) on a live send, kr on a dead one, and the entry's count premise cnt_ok_pk RP sl_pk (ablocks B ly S)
   (the growth round derives the realloc rule's cnt_ok from it and the two Permutation conjuncts). SLI_x and
   sl_loop_stmt_x take the post's kr after eiL. The bridges are at RP := RP_AR (W_journal_x.v), where the room is True
   and every count predicate is `fun _ => false` (acnt 0) under bounds 8. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require send_line_c send_line_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_rebase W_sites W_contract W_send_line_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_kit_x W_journal_x W_sites_x W_contract_x.
(* route R: the send_line contract texts at a world relation R (a Theorem Labs lane's W_send_line_xR.v) and SRrG *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_send_line_xR.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* a Theorem Labs lane's HP0 ruling: the generic relation holds at the empty ghost list only *)
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
(* a live block's request is below 2 ^ 30 (W_LLVMFuzzerTestOneInput_exit_x.v:236 BLKM's text; the top states it at ARX,
   top_x.v:972, from the cf instance's AR_blocks_law_cf): the memcpy at 0x82864 needs n < 2 ^ 32 (a Theorem Labs lane) *)
Hypothesis BLKM : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> n < 2 ^ 30.
(* W_send_line_cx.v:80-88, AR-free *)
Hypothesis HG : gx_ok SEGS B (G_SL B RG).
Hypothesis HGR : forall a, inG (G_SL B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_SL B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* W_send_line_cx.v:90-92, the runtime and allocator sites over ARx *)
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
(* The realloc site rule in its caller-context form (W_journal_x.v Section hc), as the top's ARE_x states it
   (CTX_AREALLOC, ACk0.v:45, holds [0x82844]); send_line hands the rule a cut chain (ch = []), so the trace is the
   return address alone (W7's ccd62d4c6f6 form). *)
Variable CTX_R : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis HCTX_slr : In [BASE + AF_fr_send_line + 0x110] CTX_R.   (* realloc returns to 0x82844 *)
(* W_send_line_cx.v:94-122, AR-free *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
(* errno's 4 bytes in an 8-aligned zero-shadow range (W_contract.azs; W_drain_cx_x.v:189's form): the loop's errno
   stores need range_addressable of errno at an ARx state (W_contract_x.azs_range_addressable_x) *)
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HV10 : VAL (A_OBJ 10) = rg_client_broken RG.
Hypothesis HV11 : VAL (A_OBJ 11) = rg_send_eintr RG.
Hypothesis HV12 : VAL (A_OBJ 12) = rg_send_dead RG.
Hypothesis HV13 : VAL (A_OBJ 13) = rg_nout RG.
Hypothesis HV14 : VAL (A_OBJ 14) = rg_capout RG.
Hypothesis HV15 : VAL (A_OBJ 15) = rg_out RG.
Hypothesis HH17 : VAL (A_HI 17) + 92 = rg_client_broken RG.
Hypothesis HH19 : VAL (A_HI 19) + 248 = rg_send_eintr RG.
Hypothesis HH21 : VAL (A_HI 21) + 140 = rg_send_max RG.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= 0x5fb000.
Hypothesis HH22 : VAL (A_HI 22) + 260 = rg_nout RG.
Hypothesis HH23 : VAL (A_HI 23) + 864 = rg_capout RG.
Hypothesis HH24 : VAL (A_HI 24) + 892 = rg_out RG.
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 32), VAL (A_OBJ 32) + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4)].
(* W_send_line_cx.v:123-126, the run chain over the generic journal (W_journal_x.v Section g) *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_SL B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* W_send_line_cx.v:177 sl_epi: the epilogue writes nothing; the caller's continuation gets the same restricted memory
   and the same journal (at the epilogue's ghost list HpX). *)
Lemma sl_epi_x : forall W ly S Hp mem md sp0 FP lyX SX HpX WX regsX memX mdX k regsE (Q : world SEGS -> config -> Prop),
ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] SL_STK sp0 FP ly S Hp W mem md [] lyX SX HpX WX memX mdX k ->
spZ regsE = sp0 -> spZ regsX = sp0 - SL_FRAME ->
getr regsX 3 = getr regsE 3 -> getr regsX 4 = getr regsE 4 -> YK0s.ret_ok (getr regsE 1) ->
sl_saved WX memX (sp0 - SL_FRAME) regsE ->
(forall regs' mem' md', aregs_preserved regsE regs' ->
  (forall x, mrestrict (w_H WX) mem' x = mrestrict (w_H WX) memX x) ->
  ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] SL_STK sp0 FP ly S Hp W mem md [] lyX SX HpX WX mem' md' k ->
  Q WX (mkCfg (mkst regs' (getr regsE 1) mem' (seg_rom SEGS)) md')) ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX) Q.
Proof.
intros W ly S Hp mem md sp0 FP lyX SX HpX WX regsX memX mdX k regsE Q HJ HspE HspX H3 H4 HraE HSV HQ.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : SL_STK = 16512) by reflexivity. rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
pose proof (sl_epi_entry WX regsX memX regsE ltac:(unfold SL_FRAME in *; lia) ltac:(unfold SL_FRAME in *; lia)
  ltac:(unfold SL_FRAME in *; lia) ltac:(unfold SL_FRAME in *; rewrite HspX; rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite HspX; exact HSV)) as HS.
remember (Eimg (Ereg regsX (epi_extra regsE))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall i, (i < 13)%nat -> ew E (32 + i) = getr regsE (nth i SL_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_epi_extra regsE i Hi). }
assert (E2 : ew E 2 = getr regsX 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsX 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsX 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS BxX [] E (mrestrict (w_H WX) memX)) by constructor.
clear HE.
paj_run_tok_x RUN HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
eapply (RET WX _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RA : getr (ms_regs ms) 1 = getr regsE 1) by (rewrite R1; exact (EX 12%nat ltac:(lia))).
rewrite RA, HraE. apply HQ.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, Usp, HspX. replace (sp0 - SL_FRAME + 128) with sp0 by (unfold SL_FRAME; lia).
    rewrite <- HspE. unfold spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, E3. exact H3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, E4. exact H4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX 0%nat ltac:(lia)).
- intros x. apply HFr. intros (r & Hin & Hr). cbn [ss_mem ss_epi epi_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
- apply (ajournal_gx_materialize_x SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.

(* W_send_line_cx.v:254 SLI: the loop head L (0x827c8), the entry's ghost list Hp after S, the head's HpL after SL;
   kr is the room the caller keeps after the call (sl_post_x's kr) *)
Definition SLI_x (regsE : bvmap 5 word) ly S (Hp : list Z) W mem md (c : ctl) (O : list byte) (mx no cap out line : Z)
(Bl : list byte) (WL : world SEGS) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) (sent eiL : Z)
(kr : nat) : Prop :=
let len := Z.of_nat (length Bl) in
let sp0 := spZ regsE in
exists lyL SL HpL kL evL capL outL spent rest,
ajournal_gx_x SEGS B PST ARx (G_SL B RG) 0 [] SL_STK sp0 (ablocks_fp (aout_blks cap out)) ly S Hp W mem md []
  lyL SL HpL WL memL mdL kL /\
spZ regsL = sp0 - SL_FRAME /\ getr regsL 3 = getr regsE 3 /\ getr regsL 4 = getr regsE 4 /\
getr regsE 3 = w64 (as_gp B) /\ getr regsE 4 = w64 (as_tp B) /\
YK0s.ret_ok (getr regsE 1) /\ sl_regsL regsL len line sent /\
val_mem SEGS (mrestrict (w_H WL) memL) (sp0 - SL_FRAME + 8) 8 (VAL (A_HI 17)) /\
val_mem SEGS (mrestrict (w_H WL) memL) (sp0 - SL_FRAME + 16) 8 (VAL (A_HI 21)) /\
sl_saved WL memL (sp0 - SL_FRAME) regsE /\
ct_cl c = 3 /\ ct_br c = 0 /\ 0 <= sent < len /\ (eiL = ct_ei c \/ eiL = 0) /\ (0 < sent -> eiL = 0) /\
(ct_dd c = 1 -> sent = 0) /\
evL = (if (ct_ei c =? 1) && (eiL =? 0) then send_line_c.EINTR_V else ct_ev c) /\
aout_at B RG lyL SL WL memL (CTL 3 0 (ct_dd c) eiL evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) capL outL /\
garr8 SEGS (arm WL memL) line (bzs Bl) /\ 0 <= line /\ line + len < 2 ^ 63 /\ rom_view SEGS WL memL /\
sl_line_ok_x B ARx lyL SL outL line len /\ (forall a, line <= a < line + len -> ~ inG (G_SL B RG) a) /\
(ct_dd c = 0 -> sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx (no + sent) capL (len - sent)) /\
(ct_dd c = 1 -> capL = cap /\ outL = out) /\
(ct_dd c = 0 -> sl_max_run (Z.to_nat (len - sent)) mx (no + sent) capL (len - sent) < MMAX) /\
(ct_dd c = 0 -> blocks_bytes SL +
  tr_peak (send_line_b_c.send_line_tr true mx (no + sent) capL (len - sent) 0 RelayRunF.adr0) <= LIVE_MAX) /\
apres_kept B W mem WL memL /\
mo_ok MT S (sl_cost MT c mx no cap len) /\ mo_le MT S SL spent /\
(ct_dd c = 0 -> spent + sl_cost_run MT (Z.to_nat (len - sent)) mx (no + sent) capL (len - sent) <= sl_cost MT c mx no cap len) /\
(ct_dd c = 1 -> spent = 0) /\
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\ Permutation (ablocks B lyL SL) (aout_blks capL outL ++ rest) /\
frames SL = frames S /\
(ct_dd c = 0 -> rp_RM RP SL (Z.to_nat (sl_cost_run MT_rk (Z.to_nat (len - sent)) mx (no + sent) capL (len - sent)) + kr)) /\
(ct_dd c = 1 -> rp_RM RP SL kr) /\
cnt_ok_pk RP sl_pk (ablocks B ly S).
(* W_send_line_cx.v:284 sl_loop_stmt *)
Definition sl_loop_stmt_x : Prop :=
forall (n : nat) regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr,
SLI_x regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr ->
2 * (Z.of_nat (length Bl) - sent) + eiL <= Z.of_nat n ->
SRr SEGS WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post_x B PST ARx MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr).
(* W_send_line_cx.v:292 sl_entry_stmt: the entry over the loop gives W_contract_x.v's sl_spec_x *)
Definition sl_entry_stmt_x : Prop := sl_loop_stmt_x -> sl_spec_x B PST ARx MT RP MMAX RG A_send_lineP.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): this Section's texts at a world relation R.  Each <name>_xR below is <name>_x
   with the journal ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, sl_post_x / sl_spec_x -> their R
   twins (W_send_line_xR.v, R right after ARx), and every carrier it names -> its R twin; every other token is the
   strict text's.  At R := wle each is its strict twin by conversion. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Variable HA : alayout -> astate -> bvmap 5 word -> list (Z * Z * Z) -> Z -> Z -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis HA_call : forall lyc Sc regsT ch p n, mo_ok MT Sc (mo_malloc MT n + mo_free MT) -> HA lyc Sc regsT ch p n.
Hypothesis AREALLOC_R : arealloc_cf_rule_c_xR SEGS B PST ARx MT MMAX RP RO HA CTX_R R (SIGMA WS_realloc).
Let RUNR := paj_run_x_xR B PST ARx LAWS R (G_SL B RG) HG 0 [].
(* The send_line walks that apply SRrG facts (a continuation premise, the realloc rule at R, a call step at R) walk
   on W_journal_x.v's G chain (paj_run_x_xG / paj_run_to_x_xG with W_kit_x.v's paj_run_tok_xR) and branch by
   W_kit.v's paj_branch_xR (route-r-twins 4a42051dec74); the walks that apply none are lifted by SRr_SRrG. *)

(* W_send_line_cx.v:177 sl_epi at R (sl_epi_x's text): the walk names no SRrG fact, so it is the strict walk lifted by
   SRr_SRrG, on the R journal's SRr run chain paj_run_x_xR *)
Lemma sl_epi_xR : forall W ly S Hp mem md sp0 FP lyX SX HpX WX regsX memX mdX k regsE (Q : world SEGS -> config -> Prop),
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK sp0 FP ly S Hp W mem md [] lyX SX HpX WX memX mdX k ->
spZ regsE = sp0 -> spZ regsX = sp0 - SL_FRAME ->
getr regsX 3 = getr regsE 3 -> getr regsX 4 = getr regsE 4 -> YK0s.ret_ok (getr regsE 1) ->
sl_saved WX memX (sp0 - SL_FRAME) regsE ->
(forall regs' mem' md', aregs_preserved regsE regs' ->
  (forall x, mrestrict (w_H WX) mem' x = mrestrict (w_H WX) memX x) ->
  ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK sp0 FP ly S Hp W mem md [] lyX SX HpX WX mem' md' k ->
  Q WX (mkCfg (mkst regs' (getr regsE 1) mem' (seg_rom SEGS)) md')) ->
SRrG SEGS R WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX) Q.
Proof.
intros W ly S Hp mem md sp0 FP lyX SX HpX WX regsX memX mdX k regsE Q HJ HspE HspX H3 H4 HraE HSV HQ.
apply (SRr_SRrG SEGS R WLE_R).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (_ & _ & (memS & HJi & _) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & _) & _).
assert (WS : SL_STK = 16512) by reflexivity. rewrite !Z.add_0_r in Hal16, Hslo, Hshi, Hstk0.
pose proof (sl_epi_entry WX regsX memX regsE ltac:(unfold SL_FRAME in *; lia) ltac:(unfold SL_FRAME in *; lia)
  ltac:(unfold SL_FRAME in *; lia) ltac:(unfold SL_FRAME in *; rewrite HspX; rewrite Zminus_mod, Hal16; reflexivity)
  ltac:(rewrite HspX; exact HSV)) as HS.
remember (Eimg (Ereg regsX (epi_extra regsE))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EX : forall i, (i < 13)%nat -> ew E (32 + i) = getr regsE (nth i SL_SAVED 0%bv)).
{ intros i Hi. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra. exact (nth_epi_extra regsE i Hi). }
assert (E2 : ew E 2 = getr regsX 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 2 2%bv eq_refl)).
assert (E3 : ew E 3 = getr regsX 3) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 3 3%bv eq_refl)).
assert (E4 : ew E 4 = getr regsX 4) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsX _ 4 4%bv eq_refl)).
assert (Usp : bv_unsigned (ew E 2) = spZ regsX) by (rewrite E2; reflexivity).
assert (SHOK : sh_ok SEGS BxX [] E (mrestrict (w_H WX) memX)) by constructor.
clear HE.
paj_run_tok_x RUNR HS HJ SHOK Bspan. { apply awr_ok_x_of0. awr_ok_tac. }
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
prreg HS (8%bv : bv 5) R8. prreg HS (9%bv : bv 5) R9. prreg HS (18%bv : bv 5) R18. prreg HS (19%bv : bv 5) R19.
prreg HS (20%bv : bv 5) R20. prreg HS (21%bv : bv 5) R21. prreg HS (22%bv : bv 5) R22. prreg HS (23%bv : bv 5) R23.
prreg HS (24%bv : bv 5) R24. prreg HS (25%bv : bv 5) R25. prreg HS (26%bv : bv 5) R26. prreg HS (27%bv : bv 5) R27.
eapply (RET WX _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'.
assert (RA : getr (ms_regs ms) 1 = getr regsE 1) by (rewrite R1; exact (EX 12%nat ltac:(lia))).
rewrite RA, HraE. apply HQ.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/
    r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R2, Usp, HspX. replace (sp0 - SL_FRAME + 128) with sp0 by (unfold SL_FRAME; lia).
    rewrite <- HspE. unfold spZ. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R3, E3. exact H3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R4, E4. exact H4.
  + replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R8. exact (EX 11%nat ltac:(lia)).
  + replace (Z_to_bv 5 9) with (9%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R9. exact (EX 10%nat ltac:(lia)).
  + replace (Z_to_bv 5 18) with (18%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R18. exact (EX 9%nat ltac:(lia)).
  + replace (Z_to_bv 5 19) with (19%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R19. exact (EX 8%nat ltac:(lia)).
  + replace (Z_to_bv 5 20) with (20%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R20. exact (EX 7%nat ltac:(lia)).
  + replace (Z_to_bv 5 21) with (21%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R21. exact (EX 6%nat ltac:(lia)).
  + replace (Z_to_bv 5 22) with (22%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R22. exact (EX 5%nat ltac:(lia)).
  + replace (Z_to_bv 5 23) with (23%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R23. exact (EX 4%nat ltac:(lia)).
  + replace (Z_to_bv 5 24) with (24%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R24. exact (EX 3%nat ltac:(lia)).
  + replace (Z_to_bv 5 25) with (25%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R25. exact (EX 2%nat ltac:(lia)).
  + replace (Z_to_bv 5 26) with (26%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R26. exact (EX 1%nat ltac:(lia)).
  + replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity). rewrite R27. exact (EX 0%nat ltac:(lia)).
- intros x. apply HFr. intros (r & Hin & Hr). cbn [ss_mem ss_epi epi_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_wlo YP09.r_whi] in Hr. lia.
- apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS pa_segs_low). exact HJ.
Qed.

(* W_send_line_cx.v:254 SLI at R (SLI_x's text) *)
Definition SLI_xR (regsE : bvmap 5 word) ly S (Hp : list Z) W mem md (c : ctl) (O : list byte) (mx no cap out line : Z)
(Bl : list byte) (WL : world SEGS) (regsL : bvmap 5 word) (memL : word -> option byte) (mdL : Model) (sent eiL : Z)
(kr : nat) : Prop :=
let len := Z.of_nat (length Bl) in
let sp0 := spZ regsE in
exists lyL SL HpL kL evL capL outL spent rest,
ajournal_gx_xR SEGS B PST ARx R (G_SL B RG) 0 [] SL_STK sp0 (ablocks_fp (aout_blks cap out)) ly S Hp W mem md []
  lyL SL HpL WL memL mdL kL /\
spZ regsL = sp0 - SL_FRAME /\ getr regsL 3 = getr regsE 3 /\ getr regsL 4 = getr regsE 4 /\
getr regsE 3 = w64 (as_gp B) /\ getr regsE 4 = w64 (as_tp B) /\
YK0s.ret_ok (getr regsE 1) /\ sl_regsL regsL len line sent /\
val_mem SEGS (mrestrict (w_H WL) memL) (sp0 - SL_FRAME + 8) 8 (VAL (A_HI 17)) /\
val_mem SEGS (mrestrict (w_H WL) memL) (sp0 - SL_FRAME + 16) 8 (VAL (A_HI 21)) /\
sl_saved WL memL (sp0 - SL_FRAME) regsE /\
ct_cl c = 3 /\ ct_br c = 0 /\ 0 <= sent < len /\ (eiL = ct_ei c \/ eiL = 0) /\ (0 < sent -> eiL = 0) /\
(ct_dd c = 1 -> sent = 0) /\
evL = (if (ct_ei c =? 1) && (eiL =? 0) then send_line_c.EINTR_V else ct_ev c) /\
aout_at B RG lyL SL WL memL (CTL 3 0 (ct_dd c) eiL evL) (O ++ firstn (Z.to_nat sent) Bl) mx (no + sent) capL outL /\
garr8 SEGS (arm WL memL) line (bzs Bl) /\ 0 <= line /\ line + len < 2 ^ 63 /\ rom_view SEGS WL memL /\
sl_line_ok_x B ARx lyL SL outL line len /\ (forall a, line <= a < line + len -> ~ inG (G_SL B RG) a) /\
(ct_dd c = 0 -> sl_cap c mx no cap len = send_line_b_c.send_line_cap true mx (no + sent) capL (len - sent)) /\
(ct_dd c = 1 -> capL = cap /\ outL = out) /\
(ct_dd c = 0 -> sl_max_run (Z.to_nat (len - sent)) mx (no + sent) capL (len - sent) < MMAX) /\
(ct_dd c = 0 -> blocks_bytes SL +
  tr_peak (send_line_b_c.send_line_tr true mx (no + sent) capL (len - sent) 0 RelayRunF.adr0) <= LIVE_MAX) /\
apres_kept B W mem WL memL /\
mo_ok MT S (sl_cost MT c mx no cap len) /\ mo_le MT S SL spent /\
(ct_dd c = 0 -> spent + sl_cost_run MT (Z.to_nat (len - sent)) mx (no + sent) capL (len - sent) <= sl_cost MT c mx no cap len) /\
(ct_dd c = 1 -> spent = 0) /\
Permutation (ablocks B ly S) (aout_blks cap out ++ rest) /\ Permutation (ablocks B lyL SL) (aout_blks capL outL ++ rest) /\
frames SL = frames S /\
(ct_dd c = 0 -> rp_RM RP SL (Z.to_nat (sl_cost_run MT_rk (Z.to_nat (len - sent)) mx (no + sent) capL (len - sent)) + kr)) /\
(ct_dd c = 1 -> rp_RM RP SL kr) /\
cnt_ok_pk RP sl_pk (ablocks B ly S).
(* W_send_line_cx.v:284 sl_loop_stmt at R (sl_loop_stmt_x's text) *)
Definition sl_loop_stmt_xR : Prop :=
forall (n : nat) regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr,
SLI_xR regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr ->
2 * (Z.of_nat (length Bl) - sent) + eiL <= Z.of_nat n ->
SRrG SEGS R WL (mkCfg (mkst regsL (Z_to_bv 64 (BASE + A_sl_loop)) memL (seg_rom SEGS)) mdL)
(sl_post_xR B PST ARx R MT RP RG regsE ly S Hp W mem md c O mx no cap out Bl kr).
(* W_send_line_cx.v:292 sl_entry_stmt at R (sl_entry_stmt_x's text): the entry over the loop gives sl_spec_xR *)
Definition sl_entry_stmt_xR : Prop := sl_loop_stmt_xR -> sl_spec_xR B PST ARx R MT RP MMAX RG A_send_lineP.
End wR.
(* at R := wle the R texts are the strict ones (conversion) *)
Lemma SLI_x_wle : SLI_x = SLI_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma sl_loop_stmt_x_wle : sl_loop_stmt_x = sl_loop_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
Lemma sl_entry_stmt_x_wle : sl_entry_stmt_x = sl_entry_stmt_xR (@wle SEGS). Proof. reflexivity. Qed.
End c.
End b.
End a.

(* ---- Shared by the three send_line twin files: rebuilding a cut's conjunction after its AR-stated conjuncts are
   turned (each conjunct is a hypothesis of the context, the cut's own ghost list dropped or set to []). ---- *)
Ltac sl_decomp :=
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
Ltac sl_rebuild :=
  first [ assumption | refine (conj _ _); [sl_rebuild | sl_rebuild] ].
(* the same at RP := RP_AR: the room conjuncts are True, the entry's counts are 0 under bounds 8 *)
Ltac sl_rebuild_rm :=
  first [ assumption | exact (rp_RM_AR _ _) | exact (fun _ => rp_RM_AR _ _)
        | (apply cnt_ok_pk_AR; cbv [sl_pk]; lia)
        | refine (conj _ _); [sl_rebuild_rm | sl_rebuild_rm] ].

(* THE BRIDGES at ARx := W_journal_x.ARi (cgif's AR, Hp ignored) and PST := []. *)
Section br.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
#[local] Abbreviation ARI := (ARi SEGS B).

(* send_line's post inside SRr, at every Hp and kr *)
Lemma SRr_sl_post_x_AR : forall regsE ly S Hp W mem md c O mx no cap out Bl kr W1 c1,
SRr SEGS W1 c1 (sl_post_x B [] ARI MT RP_AR RG regsE ly S Hp W mem md c O mx no cap out Bl kr) <->
SRr SEGS W1 c1 (sl_post B MT RG regsE ly S W mem md c O mx no cap out Bl).
Proof.
intros regsE ly S Hp W mem md c O mx no cap out Bl kr W1 c1.
split; intros H; (eapply SRr_mono; [exact H|]); intros W' c' _ HQ;
[exact (proj1 (sl_post_x_AR B MT RG regsE ly S Hp W mem md c O mx no cap out Bl kr W' c') HQ)
|exact (proj2 (sl_post_x_AR B MT RG regsE ly S Hp W mem md c O mx no cap out Bl kr W' c') HQ)].
Qed.
Lemma SLI_x_AR : forall regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr,
SLI_x B [] ARI MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr <->
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL.
Proof.
intros. unfold SLI_x, SLI. cbv zeta.
setoid_rewrite (@ajournal_gx_x_AR fx rc SK). setoid_rewrite sl_line_ok_x_AR.
split.
- intros (l & s & h & kL & evL & capL & outL & spent & rest & HH).
  exists l, s, kL, evL, capL, outL, spent, rest. sl_decomp. sl_rebuild.
- intros (l & s & kL & evL & capL & outL & spent & rest & HH).
  exists l, s, [], kL, evL, capL, outL, spent, rest. sl_decomp. sl_rebuild_rm.
Qed.
Lemma sl_loop_stmt_x_AR : sl_loop_stmt_x B [] ARI MT RP_AR MMAX RG <-> sl_loop_stmt B MT MMAX RG.
Proof.
unfold sl_loop_stmt_x, sl_loop_stmt. setoid_rewrite SLI_x_AR. setoid_rewrite SRr_sl_post_x_AR.
split.
- intros H n regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL.
  exact (H n regsE ly S [] W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL 0%nat).
- intros H n regsE ly S _ W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL _.
  exact (H n regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL).
Qed.
Lemma sl_entry_stmt_x_AR : sl_entry_stmt_x B [] ARI MT RP_AR MMAX RG <-> sl_entry_stmt B MT MMAX RG.
Proof. unfold sl_entry_stmt_x, sl_entry_stmt. rewrite sl_loop_stmt_x_AR, sl_spec_x_AR. reflexivity. Qed.
(* the lemma twin at that instance gives W_send_line_cx.v's sl_epi *)
Hypothesis LX : AR_laws_x SEGS B ARI 0.
Lemma sl_epi_AR : gx_ok SEGS B (G_SL B RG) ->
forall W ly S mem md sp0 FP lyX SX WX regsX memX mdX k regsE (Q : world SEGS -> config -> Prop),
ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK sp0 FP ly S W mem md [] lyX SX WX memX mdX k ->
spZ regsE = sp0 -> spZ regsX = sp0 - SL_FRAME ->
getr regsX 3 = getr regsE 3 -> getr regsX 4 = getr regsE 4 -> YK0s.ret_ok (getr regsE 1) ->
sl_saved WX memX (sp0 - SL_FRAME) regsE ->
(forall regs' mem' md', aregs_preserved regsE regs' ->
  (forall x, mrestrict (w_H WX) mem' x = mrestrict (w_H WX) memX x) ->
  ajournal_gx SEGS B (G_SL B RG) 0 [] SL_STK sp0 FP ly S W mem md [] lyX SX WX mem' md' k ->
  Q WX (mkCfg (mkst regs' (getr regsE 1) mem' (seg_rom SEGS)) md')) ->
SRr SEGS WX (mkCfg (mkst regsX (Z_to_bv 64 (BASE + A_sl_epi)) memX (seg_rom SEGS)) mdX) Q.
Proof.
intros HG W ly S mem md sp0 FP lyX SX WX regsX memX mdX k regsE Q HJ HspE HspX H3 H4 HraE HSV HQ.
apply (sl_epi_x B [] ARI RG LX HG W ly S [] mem md sp0 FP lyX SX [] WX regsX memX mdX k regsE Q);
[apply ajournal_gx_x_AR; exact HJ | exact HspE | exact HspX | exact H3 | exact H4 | exact HraE | exact HSV |].
intros regs' mem' md' Hr Hm HJ'. apply ajournal_gx_x_AR in HJ'. exact (HQ regs' mem' md' Hr Hm HJ').
Qed.
End br.

(* THE ARi0 BRIDGES (a Theorem Labs lane's HP0 ruling): at ARx := W_journal_x.ARi0 (AR /\ Hp = []) and PST := []. *)
Section br0.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
#[local] Abbreviation ARI0 := (ARi0 SEGS B).

(* W_contract_x.v's sl_post_x_of_AR0 at any entry ghost list Hp (the journal's start Hp is free at ARi0) *)
Lemma sl_post_x_of_AR0_hp : forall regs ly S Hp W mem md c O mx no cap out Bl kr W' c',
sl_post B MT RG regs ly S W mem md c O mx no cap out Bl W' c' ->
sl_post_x B [] ARI0 MT RP_AR RG regs ly S Hp W mem md c O mx no cap out Bl kr W' c'.
Proof.
intros regs ly S Hp W mem md c O mx no cap out Bl kr W' c'
  (ly' & S' & regs' & mem' & md' & k & out' & Hc & HJ & Hr1 & Hr2 & Hr3 & HR).
exists ly', S', [], regs', mem', md', k, out'.
refine (conj Hc (conj _ (conj Hr1 (conj Hr2 (conj Hr3 (conj (rp_RM_AR _ _) HR)))))).
apply ajournal_gx_AR_x_ARi0. exact HJ.
Qed.
Lemma SLI_x_AR0 : forall regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr,
SLI_x B [] ARI0 MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr ->
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL.
Proof.
intros regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr H.
unfold SLI_x in H. unfold SLI. cbv zeta in H |- *.
destruct H as (lyL & SL & HpL & kL & evL & capL & outL & spent & rest & H).
exists lyL, SL, kL, evL, capL, outL, spent, rest. sl_decomp.
repeat match goal with Hj : context [@ajournal_gx_x] |- _ => apply ajournal_gx_x_ARi0_AR in Hj end.
repeat match goal with Hl : context [@sl_line_ok_x] |- _ => apply sl_line_ok_of_x_ARi0 in Hl end.
sl_rebuild.
Qed.
Lemma SLI_x_of_AR0 : forall regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr,
SLI B MT MMAX RG regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL ->
SLI_x B [] ARI0 MT RP_AR MMAX RG regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr.
Proof.
intros regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr H.
unfold SLI in H. unfold SLI_x. cbv zeta in H |- *.
destruct H as (lyL & SL & kL & evL & capL & outL & spent & rest & H).
exists lyL, SL, [], kL, evL, capL, outL, spent, rest. sl_decomp.
repeat match goal with Hj : context [@W_journal.ajournal_gx] |- _ => apply ajournal_gx_AR_x_ARi0 with (Hp := Hp) in Hj end.
repeat match goal with Hl : context [@sl_line_ok] |- _ => apply sl_line_ok_x_ARi0_of in Hl end.
sl_rebuild_rm.
Qed.
Lemma sl_loop_stmt_x_AR0 : sl_loop_stmt_x B [] ARI0 MT RP_AR MMAX RG -> sl_loop_stmt B MT MMAX RG.
Proof.
intros H n regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL HI Hb.
eapply SRr_mono; [eapply (H n regsE ly S [] W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL 0%nat);
  [apply SLI_x_of_AR0; exact HI | exact Hb]|].
intros W' c' _ HQ. revert HQ. apply sl_post_x_AR0.
Qed.
Lemma sl_loop_stmt_x_of_AR0 : sl_loop_stmt B MT MMAX RG -> sl_loop_stmt_x B [] ARI0 MT RP_AR MMAX RG.
Proof.
intros H n regsE ly S Hp W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL kr HI Hb.
eapply SRr_mono; [eapply (H n regsE ly S W mem md c O mx no cap out line Bl WL regsL memL mdL sent eiL);
  [eapply SLI_x_AR0; exact HI | exact Hb]|].
intros W' c' _ HQ. apply sl_post_x_of_AR0_hp. exact HQ.
Qed.
Lemma sl_entry_stmt_x_AR0 : sl_entry_stmt_x B [] ARI0 MT RP_AR MMAX RG -> sl_entry_stmt B MT MMAX RG.
Proof.
intros H Hl. apply sl_spec_x_AR0. apply H. apply sl_loop_stmt_x_of_AR0. exact Hl.
Qed.
Lemma sl_entry_stmt_x_of_AR0 : sl_entry_stmt B MT MMAX RG -> sl_entry_stmt_x B [] ARI0 MT RP_AR MMAX RG.
Proof.
intros H Hl. apply sl_spec_x_of_AR0. apply H. apply sl_loop_stmt_x_AR0. exact Hl.
Qed.
End br0.
