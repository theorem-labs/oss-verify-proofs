(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: rec_shape_of's loop on fuzz_command.asan-ubsan (0x8973c .. 0x897d4), ported from
   the ASan walk's loop lib/A/Prog/rec_shape_of_s.v (a working branch 6648665b722), itself in the form of
   proofs/cgif/cgif_file_fuzzer/lib/A/ACh2.v and ACh1.v (segment steps from one statement to the next, each seeded
   by the walk kit and run by the token-aware executor): the loop head with the inline check of the row and the
   strlen wrapper's call (HEAD -> R1), the length compare and the bcmp wrapper's call (R1 -> R2 / latch), the
   result test, the found branch's inline check and the return of the row's reply, and the latch to the next row
   or the return of "resp 0" after the last (R2 -> HEAD / return). One lemma per segment, for each of the 28
   rows. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaTable PaSym PaStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import PaRun PaShadow PaJournal CmdSyms CmdList CmdPa.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdPaLib PaSB PaDenot CmdAddr CmdObj.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B Require YF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Rt Require Import RtDefs RtString.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import RecFacts.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.B.Prog Require Import CmdBase CmdRep rec_shape_of_c rec_shape_of_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac rso_awr :=
lazymatch goal with |- awr_ok _ _ ?Ex ?rs _ _ _ _ _ _ _ _ => let rs' := eval vm_compute in rs in change rs with rs' end;
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac csav := unfold acallee_saved;
lazymatch goal with |- context [bv_unsigned ?x] => let z := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with z end; lia.
(* a register's value at a stop, as the denotation of its symbolic value (not normalised) *)
Ltac rawreg HS r H :=
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
(* a register the run left at its seed expression keeps the value it had at the seed *)
Ltac same_reg HS HREG r H :=
rawreg HS r H;
let H2 := fresh "H2" in pose proof (HREG r) as H2;
lazymatch type of H2 with getr _ _ = sv_denot _ (sr_get ?sr _) =>
  let e2 := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with e2 in H2 end;
rewrite <- H2 in H; clear H2.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
Variables RLO RHI : Z.
Hypothesis ASTRLEN : forall fx0 : YK11.FPState, @astrlen_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_strlen).
Hypothesis ABCMP : forall fx0 : YK11.FPState, @abcmp_realizes fx0 rc SEGS B (SIGMA CS___interceptor_trampoline_bcmp).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HB : YF0m.CmdBSyms B.
(* the shadow facts of the image ranges the walk reads, at every AR state (the top file's rso_zsh_of) *)
Hypothesis RSO_ZSH : forall ly S (W : world SEGS) mem md, AR SEGS B ly S W mem md -> rso_zsh (rdW W mem).
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_cmd) (PI := PI).
(* the values of a symbolic expression over the image's atoms *)
Ltac uval :=
lazymatch goal with |- sv_denot ?Ex ?e = _ => rewrite (denot_lit_U Ex e) end;
apply bv_eq; rewrite !Z_to_bv_unsigned;
rewrite ?U_SAlu; cbn [zalu_raw]; rewrite ?U_SOff, ?U_SLit;
lazymatch goal with E32 : ew _ 32 = _, E41 : ew _ 282 = _, E42 : ew _ 283 = _, E43 : ew _ 284 = _ |- _ =>
  rewrite ?E32, ?E41, ?E42, ?E43 end;
rewrite ?unsigned_lit_small by (unfold SB; lia);
vm_compute; reflexivity.
(* open a segment statement at row i and program point pc: unpack the entry facts and the state, and seed *)
Ltac rso_open i pc CX MID HR ly S W regs mem md memc mdc regs1 :=
pose proof pa_wx as Hwx; pose proof pa_segs_low as Hsegs; pose proof pa_B_ok as HBASE; pose proof pa_base_lo as HBLO;
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5);
pose proof CX as (HPRE & H10 & H11 & HVO & HRO & HROIN & HTAIL & HVERB & HGAP);
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp & Htp & Hstk & Hpres0 & HQT);
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2);
pose proof MID as (HJ & HK & HFR);
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R21 & R22 & R23 & R24 & R25 & R26 & R27);
assert (HSTK : REC_SHAPE_OF_STK = 8288) by reflexivity;
set (sp0 := spZ regs) in *;
pose proof (proj1 HJ) as HAR;
assert (HL : rso_low W mem memc) by (apply (rso_low_of_kept W mem memc (sp0 - REC_SHAPE_OF_STK) sp0); [lia | exact HK]);
destruct HRO as (HROW & HDEF);
destruct (HROW i ltac:(lia)) as (Rnm & Rrp & Snm & Srp);
pose proof (RSO_ZSH ly S W memc mdc HAR) as (Zg & Zrow);
pose proof (rso_regs_ok i regs regs1 HVO ltac:(lia) HR) as HREG;
destruct (rso_seed pc (rso_regs_head i) i W regs regs1 memc sp0 HVO ltac:(lia) ltac:(vm_compute; reflexivity)
  ltac:(lia) ltac:(lia) Hal16 ltac:(rewrite R2; apply unsigned_lit_small; lia) HREG HFR
  (low_rdword W mem memc (0xa5a20 + 16 * i) (rso_nm i) HL ltac:(lia) ltac:(lia) Rnm)
  (low_rdword W mem memc (0xa5a28 + 16 * i) (rso_rp i) HL ltac:(lia) ltac:(lia) Rrp) Zg) as [HS SHOK];
destruct (rso_val_objs HVO) as (V41 & V42 & V43);
set (E := Eimg (Ereg regs1 (rso_extra regs))) in *; assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env);
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs1 r) by
  (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
   rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn);
assert (ES : forall j r, nth_error rso_saved j = Some r -> ew E (33 + j) = getr regs (Z_to_bv 5 r)) by
  (intros j r Hj; subst E; apply rso_E_saved; exact Hj);
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0));
assert (E41 : ew E 282 = Z_to_bv 64 0xa5a20) by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 282%nat with (A_OBJ 41); rewrite V41; reflexivity);
assert (E42 : ew E 283 = Z_to_bv 64 0x21d20) by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 283%nat with (A_OBJ 42); rewrite V42; reflexivity);
assert (E43 : ew E 284 = Z_to_bv 64 0xa5a28) by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia); change 284%nat with (A_OBJ 43); rewrite V43; reflexivity);
assert (Usp : bv_unsigned (ew E 2) = sp0 - 96) by (rewrite (EE 2%nat 2%bv eq_refl), R2; apply unsigned_lit_small; lia);
assert (NM : rso_nm i = ltac:(let x := eval vm_compute in (rso_nm i) in exact x)) by reflexivity;
assert (NR : rso_rp i = ltac:(let x := eval vm_compute in (rso_rp i) in exact x)) by reflexivity;
assert (NL : astr_len (rso_name i) = ltac:(let x := eval vm_compute in (astr_len (rso_name i)) in exact x)) by (vm_compute; reflexivity);
assert (RL : astr_len (rso_reply i) = ltac:(let x := eval vm_compute in (astr_len (rso_reply i)) in exact x)) by (vm_compute; reflexivity);
unfold astr_len in NL, RL.
(* after a run that wrote nothing: the memory at the stop agrees with memc everywhere *)
Ltac rso_after W mem memc HL :=
lazymatch goal with HFr : frame_of _ _ (mrestrict _ memc) (mrestrict _ (ms_mem ?ms)) |- _ =>
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun _ => False) HFr
  ltac:(let b := fresh in let wlo := fresh in let whi := fresh in let a := fresh in let Hin := fresh in let Hrr := fresh in
        intros b wlo whi a Hin Hrr; vm_compute in Hin;
        repeat (let Hq := fresh in destruct Hin as [Hq | Hin]; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia|]); destruct Hin)) as UN1;
assert (HLm : rso_low W memc (ms_mem ms)) by (let a := fresh in let Ha := fresh in intros a Ha; apply UN1; [lia | intros []]);
assert (HL2 : rso_low W mem (ms_mem ms)) by exact (rso_low_trans W mem memc (ms_mem ms) HL HLm)
end;
repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
(* the return (0x897d4): the post of rec_shape_of_c.v:99-111; ra, the journal, the callee-saved registers, the reply *)
Ltac rso_F_ret HS ES Hra :=
lazymatch goal with
| |- mkCfg (mkst ?rg (v_jalr (getr ?rg 1) 0) ?mm ?ro) ?d = mkCfg (mkst ?rg ?pc ?mm ?ro) ?d =>
  let Hret := fresh "Hret" in
  assert (Hret : v_jalr (getr rg 1) 0 = pc);
  [ rewrite (st_ok_pi_restrict_reg _ _ _ _ _ HS);
    lazymatch goal with |- context [sr_get ?a ?rr2] => let w := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with w end;
    cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
    let E33 := fresh "E33" in pose proof (ES 0%nat 1 eq_refl) as E33; change (33 + 0)%nat with 33%nat in E33;
    rewrite E33; unfold YK0s.ret_ok in Hra;
    replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity); exact Hra
  | rewrite Hret; reflexivity ]
end.
Ltac rso_F_pres HS ES EE Usp sp0 regs R3 R4 R26 R27 :=
apply rso_pres_ret;
rewrite (st_ok_pi_restrict_reg _ _ _ _ _ HS);
lazymatch goal with |- context [sr_get ?a ?rr2] => let w := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with w end;
cbn [sv_denot];
first
[ rewrite Usp; replace (sp0 - 96 + 96) with sp0 by lia; change sp0 with (spZ regs); unfold spZ; apply Z_to_bv_bv_unsigned
| rewrite Z.add_0_r, Z_to_bv_bv_unsigned;
  lazymatch goal with |- ew _ ?n = getr _ ?k =>
    first
    [ let j := eval compute in (n - 33)%nat in let r' := eval compute in (nth j rso_saved 0) in
      etransitivity; [exact (ES j r' eq_refl)|]; f_equal; apply bv_eq; reflexivity
    | rewrite (EE n k eq_refl); first [exact R3 | exact R4 | exact R26 | exact R27] ] end ].
(* the reply: the read-only arm of astr_argA for every O (its bytes, each byte a read-only one no runtime entry owns,
   and the record's checks cmd_addr_b and cmd_hull_b of it and its end among cmd_ro_ends, each by computation);
   nothing allocated, no frame: layout and allocator state as at the entry *)
Ltac rso_F_Q HS Hshape Hast Hro :=
unfold rso_Q; split; [|split; [apply Permutation_refl | split; reflexivity]];
lazymatch type of Hast with astr_atR _ ?q _ => exists q;
  let q' := eval vm_compute in q in change q with q' in Hast, Hro |- * end;
split;
[ rewrite (st_ok_pi_restrict_reg _ _ _ _ _ HS);
  lazymatch goal with |- context [sr_get ?a ?rr2] => let w := eval vm_compute in (sr_get a rr2) in change (sr_get a rr2) with w end;
  uval |];
split; [lia|];
intros ?; rewrite Hshape; cbv beta iota zeta delta [astr_argA];
split; [let Hq := fresh in intro Hq; discriminate Hq|];
split; [exact Hast|];
split; [vm_compute; let Hq := fresh in intro Hq; discriminate Hq|];
right; split; [exact Hro|];
split; [vm_compute; reflexivity|]; split; [vm_compute; reflexivity|]; apply In_Z_of_existsb; vm_compute; reflexivity.
Ltac rso_fin HS W ly S ES Hra HJ Hsegs Usp sp0 regs EE R3 R4 R26 R27 Hshape Hast Hro :=
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
let mat' := fresh "mat" in intros mat'; unfold rso_post, apost_base; cbv beta;
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, r, m, d end;

refine (conj _ (conj _ (conj _ _)));
[ rso_F_ret HS ES Hra
| apply (ajournal_materialize _ _ LAWS Hsegs); exact HJ
| rso_F_pres HS ES EE Usp sp0 regs R3 R4 R26 R27
| rso_F_Q HS Hshape Hast Hro ].
(* the 28 rows, one goal each, the row index a numeral *)
Ltac rso_rows i :=
let Hc := fresh "Hc" in
assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8 \/ i = 9 \/ i = 10 \/ i = 11 \/
  i = 12 \/ i = 13 \/ i = 14 \/ i = 15 \/ i = 16 \/ i = 17 \/ i = 18 \/ i = 19 \/ i = 20 \/ i = 21 \/ i = 22 \/ i = 23 \/
  i = 24 \/ i = 25 \/ i = 26 \/ i = 27) by lia;
repeat (destruct Hc as [-> | Hc]); [..| subst i].
(* HEAD -> R1 (0x8973c .. 0x8974c): the row's inline check, the load of its name, the strlen wrapper's call *)
Lemma rso_head_ok : forall i, 0 <= i < 28 -> R1_stmt B RLO RHI i -> HEAD_stmt B RLO RHI i.
Proof.
intros i Hi R1 ly S W regs mem md p v regs1 memc mdc CX MID HR UN RV.
rso_rows i.
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- _ => rso_open i RS_HEAD CX MID HR ly S W regs mem md memc mdc regs1 end.
all: unfold cfg_at.
all: paj_run_tok RUN HS HJ SHOK RBspan; [rso_awr|].
all: pmkst HS; rso_after W mem memc HL.
all: pose proof (RSO_ZSH ly S W _ _ (proj1 HJ)) as (Zg' & Zrow').
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- _ => destruct (Zrow' i ltac:(lia)) as (Znm & Hnm) end.
all: rawreg HS (10%bv : bv 5) Q10; rawreg HS (1%bv : bv 5) Q1; rawreg HS (2%bv : bv 5) Q2;
     rawreg HS (3%bv : bv 5) Q3; rawreg HS (4%bv : bv 5) Q4.
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
eapply SRr_bind;
[ exact (aj_strlen_at B LAWS (SIGMA CS___interceptor_trampoline_strlen) (ASTRLEN fx) W rg mm REC_SHAPE_OF_STK sp0 [] ly S W mem md [] ly S mdq 0
  (rso_nm i) (rso_name i) (-96) (Z_to_bv 64 (BASE + RS_R1)) HJ
  ltac:(rewrite Q10; uval)
  ltac:(rewrite NM; lia)
  ltac:(unfold spZ; rewrite Q2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Usp; lia)
  ltac:(reflexivity) ltac:(lia) ltac:(unfold ESTACK; lia)
  ltac:(rewrite Q3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat 3%bv eq_refl), R3; exact Hgp)
  ltac:(rewrite Q4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat 4%bv eq_refl), R4; exact Htp)
  ltac:(rewrite Q1; cbn [sv_denot]; rewrite (img_env_codeptr E HEI); reflexivity)
  ltac:(apply ret_ok_codeptr_v; [unfold RS_R1, AF_rec_shape_of; lia | reflexivity])
  ltac:(apply astr_atR_view; apply (low_astr W mem _ _ _ HL2); [rewrite NM; lia | rewrite NM, NL; lia | exact Snm])
  ltac:(apply aread_ok_lit; [apply (low_astr W mem _ _ _ HL2); [rewrite NM; lia | rewrite NM, NL; lia | exact Snm]
        | exact Znm | exact Hnm | rewrite NM; lia | rewrite NM; unfold astr_len; rewrite NL; unfold kLowMemEnd; lia
        | unfold spZ; rewrite Q2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Usp; unfold kLowMemEnd, ESTACK; lia ])
  ltac:(apply (low_tail W mem _ _ HL2); [rewrite NM; unfold astr_len; lia | rewrite NM; unfold astr_len; rewrite NL; lia
        | exact (HTAIL i ltac:(lia))])
  ltac:(exact (low_rt_rom W memc _ HLm RV)))
| ] end.
all: intros W' c' _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Ha0 & HK2).
all: same_reg HS HREG (2%bv : bv 5) S2; same_reg HS HREG (3%bv : bv 5) S3; same_reg HS HREG (4%bv : bv 5) S4;
     same_reg HS HREG (8%bv : bv 5) S8; same_reg HS HREG (9%bv : bv 5) S9;
     same_reg HS HREG (18%bv : bv 5) S18; same_reg HS HREG (19%bv : bv 5) S19; same_reg HS HREG (21%bv : bv 5) S21;
     same_reg HS HREG (22%bv : bv 5) S22; same_reg HS HREG (23%bv : bv 5) S23; same_reg HS HREG (24%bv : bv 5) S24;
     same_reg HS HREG (25%bv : bv 5) S25; same_reg HS HREG (26%bv : bv 5) S26; same_reg HS HREG (27%bv : bv 5) S27;
     rawreg HS (20%bv : bv 5) Q20.
all: assert (HLc2 : rso_low W memc mem2) by
       (intros a Ha; rewrite (HK2 a ltac:(lia)) by (unfold ESTACK; lia); apply UN1; [lia | intros []]).
all: exact (R1 ly S W regs mem md p v regs2 mem2 md2 CX
  (rso_mid_call B ly S W regs mem md memc mdc _ mem2 md2 (sp0 - 96 - ESTACK) MID (fun a Ha => UN1 a Ha (fun x => x)) HJ2 HK2
     ltac:(unfold ESTACK; lia))
  (rso_regs_at_pres regs regs1 _ regs2 _ HR HP2 S2 S3 S4 S8 S9 S18 S19 S21 S22 S23 S24 S25 S26 S27)
  Ha0
  ltac:(rewrite (pres_reg _ _ 20%bv HP2) by csav; rewrite Q20; uval)
  UN (low_rt_rom W memc mem2 HLc2 RV)).
Qed.
(* R2 (0x89764): the bcmp result's test; on a match the inline check of the row's reply pointer, its load and the
   return; otherwise on to the latch *)
Lemma rso_r2_ok : forall i, 0 <= i < 28 -> LATCH_stmt B RLO RHI i -> R2_stmt B RLO RHI i.
Proof.
intros i Hi HLT ly S W regs mem md p v regs1 memc mdc CX MID HR H20 HLEN HEQ UN RV.
rso_rows i.
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- _ => rso_open i RS_R2 CX MID HR ly S W regs mem md memc mdc regs1 end.
all: unfold cfg_at.
all: psrr_branch_tok RUN BR HS SHOK RBspan.
all: rewrite branch_eq_U in Hc.
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- _ =>
  lazymatch type of Hc with
  | _ = true =>
    apply Z.eqb_eq in Hc;
    assert (Hm : map bv_unsigned (rso_name i) = map bv_unsigned v) by
      (apply (proj1 HEQ); rewrite <- (EE 10%nat 10%bv eq_refl); apply bv_eq;
       rewrite U_SOff, U_SLit, Z.add_0_r in Hc;
       rewrite (YP0m.zcanon_small (bv_unsigned (ew E 10))) in Hc by (pose proof (bv_unsigned_in_range 64 (ew E 10)) as Hr; exact Hr);
       rewrite Hc; reflexivity)
  | _ = false =>
    apply Z.eqb_neq in Hc;
    assert (Hm : map bv_unsigned (rso_name i) <> map bv_unsigned v) by
      (intros Hmm; apply Hc; rewrite U_SOff, U_SLit, (EE 10%nat 10%bv eq_refl), (proj2 HEQ Hmm); reflexivity)
  end end.
(* the found branch: the reply's inline check, its load, the return *)
all: lazymatch goal with Hm : map bv_unsigned (rso_name _) = _ |- _ =>
  paj_run_tok RUN HS HJ SHOK RBspan; [rso_awr|]; rso_after W mem memc HL | _ => idtac end.
all: lazymatch goal with HR : rso_regs_at _ _ ?i, Hm : map bv_unsigned (rso_name ?i) = _,
                          HS : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
  assert (Hast : astr_atR (rdW W (ms_mem ms)) (rso_rp i) (rso_reply i)) by
      (apply (low_astr W mem _ _ _ HL2); [rewrite NR; lia | rewrite NR, RL; lia | exact Srp]);
  pose proof (rso_shape_found i v ltac:(lia) UN Hm) as Hshape;
  assert (Hro : forall k, 0 <= k < Z.of_nat (length (rso_reply i)) + 1 -> rso_rob B RLO RHI (rso_rp i + k)) by
    (intros k Hk; exact (proj1 HROIN i k ltac:(lia) Hk));
  rso_fin HS W ly S ES Hra HJ Hsegs Usp sp0 regs EE R3 R4 R26 R27 Hshape Hast Hro | _ => idtac end.
(* no match: one step to the latch *)
all: lazymatch goal with HR : rso_regs_at _ _ ?i, Hm : map bv_unsigned (rso_name ?i) <> _ |- _ =>
  paj_run_to_tok RUNTO HS HJ SHOK RBspan RS_LATCH; [rso_awr|]; pmkst HS; rso_after W mem memc HL | _ => idtac end.
all: lazymatch goal with HR : rso_regs_at _ _ ?i, Hm : map bv_unsigned (rso_name ?i) <> _ |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  
  same_reg HS HREG (2%bv : bv 5) S2; same_reg HS HREG (3%bv : bv 5) S3; same_reg HS HREG (4%bv : bv 5) S4;
  same_reg HS HREG (8%bv : bv 5) S8; same_reg HS HREG (9%bv : bv 5) S9; same_reg HS HREG (18%bv : bv 5) S18;
  same_reg HS HREG (19%bv : bv 5) S19; same_reg HS HREG (21%bv : bv 5) S21; same_reg HS HREG (22%bv : bv 5) S22;
  same_reg HS HREG (23%bv : bv 5) S23; same_reg HS HREG (24%bv : bv 5) S24; same_reg HS HREG (25%bv : bv 5) S25;
  same_reg HS HREG (26%bv : bv 5) S26; same_reg HS HREG (27%bv : bv 5) S27;
  
  apply (HLT ly S W regs mem md p v rg mm mdq CX);
  [ split; [exact HJ|]; split;
    [ intros a Ha Hna; rewrite (UN1 a Ha (fun x => x)); exact (HK a Ha Hna)
    | apply (rso_frame_kept (w_H W) (w_H W) memc mm sp0 regs HFR); intros a Ha; apply UN1; [|intros []];
      change sp0 with (spZ regs) in *; unfold spZ in *; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rr;
      change (bv_modulus 64) with (2 ^ 64) in Rr; lia ]
  | unfold rso_regs_at; repeat split;
    first [ rewrite S2; exact R2 | rewrite S3; exact R3 | rewrite S4; exact R4 | rewrite S8; exact R8 | rewrite S9; exact R9
          | rewrite S18; exact R18 | rewrite S19; exact R19 | rewrite S21; exact R21 | rewrite S22; exact R22
          | rewrite S23; exact R23 | rewrite S24; exact R24 | rewrite S25; exact R25 | rewrite S26; exact R26
          | rewrite S27; exact R27 ]
  | exact (rso_unseen_next i v ltac:(lia) UN Hm)
  | exact (low_rt_rom W memc mm HLm RV) ] | _ => idtac end.
Qed.
(* the latch (0x89768): the next row's head, or after the last row the return of "resp 0" *)
Lemma rso_latch_ok : forall i, 0 <= i < 28 -> (i < 27 -> HEAD_stmt B RLO RHI (i + 1)) -> LATCH_stmt B RLO RHI i.
Proof.
intros i Hi HN ly S W regs mem md p v regs1 memc mdc CX MID HR UN RV.
rso_rows i.
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- _ => rso_open i RS_LATCH CX MID HR ly S W regs mem md memc mdc regs1 end.
all: unfold cfg_at.
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- _ =>
  lazymatch eval vm_compute in (i <? 27) with
  | true => paj_run_to_tok RUNTO HS HJ SHOK RBspan RS_HEAD; [rso_awr|]; pmkst HS; rso_after W mem memc HL
  | false => idtac end end.
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  lazymatch eval vm_compute in (i <? 27) with
  | true =>
    
    same_reg HS HREG (2%bv : bv 5) S2; same_reg HS HREG (3%bv : bv 5) S3; same_reg HS HREG (4%bv : bv 5) S4;
    same_reg HS HREG (8%bv : bv 5) S8; same_reg HS HREG (9%bv : bv 5) S9; same_reg HS HREG (19%bv : bv 5) S19;
    same_reg HS HREG (23%bv : bv 5) S23; same_reg HS HREG (25%bv : bv 5) S25; same_reg HS HREG (26%bv : bv 5) S26;
    same_reg HS HREG (27%bv : bv 5) S27;
    rawreg HS (18%bv : bv 5) Q18; rawreg HS (21%bv : bv 5) Q21; rawreg HS (22%bv : bv 5) Q22; rawreg HS (24%bv : bv 5) Q24;
    
    apply (HN ltac:(lia) ly S W regs mem md p v rg mm mdq CX);
    [ split; [exact HJ|]; split;
      [ intros a Ha Hna; rewrite (UN1 a Ha (fun x => x)); exact (HK a Ha Hna)
      | apply (rso_frame_kept (w_H W) (w_H W) memc mm sp0 regs HFR); intros a Ha; apply UN1; [|intros []];
        change sp0 with (spZ regs) in *; unfold spZ in *; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rr;
        change (bv_modulus 64) with (2 ^ 64) in Rr; lia ]
    | unfold rso_regs_at; repeat split;
      first [ rewrite S2; exact R2 | rewrite S3; exact R3 | rewrite S4; exact R4 | rewrite S8; exact R8 | rewrite S9; exact R9
            | rewrite S19; exact R19 | rewrite S23; exact R23 | rewrite S25; exact R25 | rewrite S26; exact R26
            | rewrite S27; exact R27 | rewrite Q18; uval | rewrite Q21; uval | rewrite Q22; uval | rewrite Q24; uval ]
    | exact UN
    | exact (low_rt_rom W memc mm HLm RV) ]
  | false => idtac end | _ => idtac end.
(* the last row: "resp 0" *)
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- SRr _ _ (mkCfg ?ms0 _) _ =>
  lazymatch eval vm_compute in (i <? 27) with
  | false =>
    paj_run_tok RUN HS HJ SHOK RBspan; [rso_awr|]; rso_after W mem memc HL;
    lazymatch goal with HS : st_ok_pi _ _ _ _ (restrict _ ?ms) |- _ =>
      assert (Hast : astr_atR (rdW W (ms_mem ms)) 0x21d20 REC_MOD_HOST_SHAPE) by
        (apply (low_astr W mem _ _ _ HL2); [lia | change (length REC_MOD_HOST_SHAPE) with 6%nat; lia | exact HDEF]) end;
    pose proof (rso_shape_default v UN) as Hshape;
    assert (Hro : forall k, 0 <= k < Z.of_nat (length REC_MOD_HOST_SHAPE) + 1 -> rso_rob B RLO RHI (0x21d20 + k)) by
      (intros k Hk; change (length REC_MOD_HOST_SHAPE) with 6%nat in Hk; exact (proj2 HROIN k ltac:(lia)));
    rso_fin HS W ly S ES Hra HJ Hsegs Usp sp0 regs EE R3 R4 R26 R27 Hshape Hast Hro
  | true => idtac end | _ => idtac end.
Qed.
(* R1 (0x89750): the length compare; on equal lengths the bcmp wrapper's call on (name, verb, len) and back at R2,
   otherwise on to the latch *)
Lemma rso_r1_ok : forall i, 0 <= i < 28 -> R2_stmt B RLO RHI i -> LATCH_stmt B RLO RHI i -> R1_stmt B RLO RHI i.
Proof.
intros i Hi HR2 HLT ly S W regs mem md p v regs1 memc mdc CX MID HR H10' H20 UN RV.
rso_rows i.
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- _ => rso_open i RS_R1 CX MID HR ly S W regs mem md memc mdc regs1 end.
all: unfold cfg_at.
all: pose proof HGAP as (_ & Hlen64).
all: lazymatch goal with HR : rso_regs_at _ _ ?i |- _ =>
  assert (UA : U E (SOff 10 0) = astr_len (rso_name i)) by
    (apply U_atom; [rewrite (EE 10%nat 10%bv eq_refl); exact H10' | unfold astr_len; rewrite NL; lia]);
  assert (UB : U E (SOff 8 0) = Z.of_nat (length v)) by
    (apply U_atom; [rewrite (EE 8%nat 8%bv eq_refl), R8; exact H11 | lia]) end.
all: psrr_branch_tok RUN BR HS SHOK RBspan.
all: first [rewrite branch_ne_U in Hc | rewrite branch_eq_U in Hc]; rewrite ?UA, ?UB in Hc.
all: lazymatch type of Hc with
  | negb _ = true => apply negb_true_iff, Z.eqb_neq in Hc
  | negb _ = false => apply negb_false_iff, Z.eqb_eq in Hc
  end.
(* different lengths: one step to the latch *)
all: lazymatch goal with HR : rso_regs_at _ _ ?i, Hc : astr_len (rso_name ?i) <> _ |- _ =>
  assert (Hm : map bv_unsigned (rso_name i) <> map bv_unsigned v) by
    (intros Hmm; apply (f_equal (@length Z)) in Hmm; rewrite !length_map in Hmm; unfold astr_len in Hc; lia);
  paj_run_to_tok RUNTO HS HJ SHOK RBspan RS_LATCH; [rso_awr|]; pmkst HS; rso_after W mem memc HL | _ => idtac end.
all: lazymatch goal with HR : rso_regs_at _ _ ?i, Hm : map bv_unsigned (rso_name ?i) <> _ |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  
  same_reg HS HREG (2%bv : bv 5) S2; same_reg HS HREG (3%bv : bv 5) S3; same_reg HS HREG (4%bv : bv 5) S4;
  same_reg HS HREG (8%bv : bv 5) S8; same_reg HS HREG (9%bv : bv 5) S9; same_reg HS HREG (18%bv : bv 5) S18;
  same_reg HS HREG (19%bv : bv 5) S19; same_reg HS HREG (21%bv : bv 5) S21; same_reg HS HREG (22%bv : bv 5) S22;
  same_reg HS HREG (23%bv : bv 5) S23; same_reg HS HREG (24%bv : bv 5) S24; same_reg HS HREG (25%bv : bv 5) S25;
  same_reg HS HREG (26%bv : bv 5) S26; same_reg HS HREG (27%bv : bv 5) S27;
  apply (HLT ly S W regs mem md p v rg mm mdq CX);
  [ split; [exact HJ|]; split;
    [ intros a Ha Hna; rewrite (UN1 a Ha (fun x => x)); exact (HK a Ha Hna)
    | apply (rso_frame_kept (w_H W) (w_H W) memc mm sp0 regs HFR); intros a Ha; apply UN1; [|intros []];
      change sp0 with (spZ regs) in *; unfold spZ in *; pose proof (bv_unsigned_in_range 64 (getr regs 2)) as Rr;
      change (bv_modulus 64) with (2 ^ 64) in Rr; lia ]
  | unfold rso_regs_at; repeat split;
    first [ rewrite S2; exact R2 | rewrite S3; exact R3 | rewrite S4; exact R4 | rewrite S8; exact R8 | rewrite S9; exact R9
          | rewrite S18; exact R18 | rewrite S19; exact R19 | rewrite S21; exact R21 | rewrite S22; exact R22
          | rewrite S23; exact R23 | rewrite S24; exact R24 | rewrite S25; exact R25 | rewrite S26; exact R26
          | rewrite S27; exact R27 ]
  | exact (rso_unseen_next i v ltac:(lia) UN Hm)
  | exact (low_rt_rom W memc mm HLm RV) ] | _ => idtac end.
(* equal lengths: the bcmp wrapper's call *)
all: lazymatch goal with HR : rso_regs_at _ _ ?i, Hc : astr_len (rso_name ?i) = _ |- _ =>
  paj_run_tok RUN HS HJ SHOK RBspan; [rso_awr|]; pmkst HS; rso_after W mem memc HL | _ => idtac end.
all: lazymatch goal with HR : rso_regs_at _ _ ?i, Hc : astr_len (rso_name ?i) = _ |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
  
  assert (HLEN : Z.of_nat (length v) = astr_len (rso_name i)) by lia;
  assert (Hln : length (rso_name i) = length v) by (unfold astr_len in HLEN; lia);
  pose proof (RSO_ZSH ly S W _ _ (proj1 HJ)) as (Zg' & Zrow');
  destruct (Zrow' i ltac:(lia)) as (Znm & Hnm);
  destruct (rso_verb_call B RLO RHI LAWS HB ly S W mem mm mdq p v (proj1 HJ) HL2 HVERB HGAP
    ltac:(unfold astr_len in HLEN; rewrite HLEN, NL; lia) ltac:(unfold astr_len in HLEN; rewrite HLEN, NL; lia))
    as (Bv & Hp0 & Hpc & Hmv & Hrv & Hhv);
  assert (Bn : abytes_atR (rdW W mm) (rso_nm i) (rso_name i)) by
    (apply (abytes_prefix _ _ _ [Z_to_bv 8 0]); apply (proj1 (low_astr W mem mm (rso_nm i) (rso_name i) HL2 ltac:(rewrite NM; lia) ltac:(rewrite NM, NL; lia) Snm)));
  rawreg HS (10%bv : bv 5) Q10; rawreg HS (11%bv : bv 5) Q11; rawreg HS (12%bv : bv 5) Q12; rawreg HS (1%bv : bv 5) Q1;
  rawreg HS (2%bv : bv 5) Q2; rawreg HS (3%bv : bv 5) Q3; rawreg HS (4%bv : bv 5) Q4;
  assert (Hsp' : spZ rg = sp0 + -96) by
    (unfold spZ; rewrite Q2; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, Usp; lia);
  
  eapply SRr_bind;
  [ exact (aj_bcmp_at SEGS B LAWS Hsegs (SIGMA CS___interceptor_trampoline_bcmp) (ABCMP fx) W rg mm REC_SHAPE_OF_STK sp0 [] ly S W mem md
      [] ly S mdq 0 (rso_nm i) p (Z.of_nat (length v)) (-96) (Z_to_bv 64 (BASE + RS_R2)) HJ
      ltac:(rewrite Q10; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 20%nat 20%bv eq_refl); exact H20)
      ltac:(rewrite Q11; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 9%nat 9%bv eq_refl), R9; exact H10)
      ltac:(rewrite Q12; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 8%nat 8%bv eq_refl), R8; exact H11)
      ltac:(unfold astr_len in HLEN; rewrite HLEN, NL; lia)
      ltac:(rewrite NM; lia) ltac:(rewrite NM; unfold astr_len in HLEN; rewrite HLEN, NL; lia)
      Hp0 ltac:(lia)
      Hsp' eq_refl ltac:(lia) ltac:(unfold REC_SHAPE_OF_STK, ESTACK; lia)
      ltac:(rewrite Q3; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 3%nat 3%bv eq_refl), R3; exact Hgp)
      ltac:(rewrite Q4; cbn [sv_denot]; rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 4%nat 4%bv eq_refl), R4; exact Htp)
      ltac:(rewrite Q1; cbn [sv_denot]; rewrite (img_env_codeptr E HEI); reflexivity)
      ltac:(apply ret_ok_codeptr_v; [unfold RS_R2, AF_rec_shape_of; lia | reflexivity])
      ltac:(rewrite <- Hln; apply src_ok_low; [exact Bn | rewrite NM; lia | rewrite Hsp', NM, NL; unfold ESTACK; lia])
      ltac:(apply src_ok_low; [exact Bv | exact Hp0 | rewrite Hsp'; unfold ESTACK; lia])
      ltac:(intros a Ha; rewrite NM in Ha; unfold astr_len in HLEN; rewrite HLEN, NL in Ha; unfold ESTACK; lia)
      ltac:(intros a Ha; unfold ESTACK; lia)
      ltac:(unfold amem_range, kLowMemEnd; left; rewrite NM; unfold astr_len in HLEN; rewrite HLEN, NL; lia)
      Hmv
      ltac:(apply (range_addressable_sub _ _ _ _ _ _ Znm); lia)
      ltac:(intros _; apply (hull_sub _ (rso_nm i) _ (astr_len (rso_name i) + 1)); [lia | lia | rewrite NM; lia | exact Hnm])
      Hrv ltac:(intros _; exact Hhv))
  | ] | _ => idtac end.
all: lazymatch goal with HR : rso_regs_at _ _ ?i, Hc : astr_len (rso_name ?i) = _ |- _ =>
  cbv beta; intros W' c' _ (-> & regs2 & mem2 & md2 & vv & -> & HJ2 & HP2 & Hres & Hcmp & HK2 & Hpres2);
  same_reg HS HREG (2%bv : bv 5) S2; same_reg HS HREG (3%bv : bv 5) S3; same_reg HS HREG (4%bv : bv 5) S4;
  same_reg HS HREG (8%bv : bv 5) S8; same_reg HS HREG (9%bv : bv 5) S9; same_reg HS HREG (18%bv : bv 5) S18;
  same_reg HS HREG (19%bv : bv 5) S19; same_reg HS HREG (21%bv : bv 5) S21; same_reg HS HREG (22%bv : bv 5) S22;
  same_reg HS HREG (23%bv : bv 5) S23; same_reg HS HREG (24%bv : bv 5) S24; same_reg HS HREG (25%bv : bv 5) S25;
  same_reg HS HREG (26%bv : bv 5) S26; same_reg HS HREG (27%bv : bv 5) S27;
  rawreg HS (20%bv : bv 5) Q20;
  assert (HLc2 : rso_low W memc mem2) by
    (intros a Ha; rewrite (HK2 a ltac:(lia)) by (unfold ESTACK; lia); apply UN1; [lia | intros []]);
  
  apply (HR2 ly S W regs mem md p v regs2 mem2 md2 CX
    (rso_mid_call B ly S W regs mem md memc mdc _ mem2 md2 (sp0 - 96 - 2 * ESTACK) MID (fun a Ha => UN1 a Ha (fun x => x)) HJ2 HK2
       ltac:(unfold ESTACK; lia))
    (rso_regs_at_pres regs regs1 _ regs2 _ HR HP2 S2 S3 S4 S8 S9 S18 S19 S21 S22 S23 S24 S25 S26 S27));
  [ rewrite (pres_reg _ _ 20%bv HP2) by csav; rewrite Q20; cbn [sv_denot];
    rewrite Z.add_0_r, Z_to_bv_bv_unsigned, (EE 20%nat 20%bv eq_refl); exact H20
  | exact HLEN
  | rewrite Hres, Hcmp;
    let Hiff := fresh "Hiff" in
    pose proof (bytes_eq_iff _ (rso_nm i) p (rso_name i) v Hln Bn Bv) as Hiff; rewrite Hln in Hiff; exact Hiff
  | exact UN
  | exact (low_rt_rom W memc mem2 HLc2 RV) ] | _ => idtac end.
Qed.
(* the loop: the head of every row, from the last row down *)
Lemma rso_heads_all : forall i, 0 <= i < 28 -> HEAD_stmt B RLO RHI i.
Proof.
assert (G : forall n i, 0 <= i < 28 -> 27 - i = Z.of_nat n -> HEAD_stmt B RLO RHI i).
{ induction n as [|n IH]; intros i Hi Hn.
  - assert (LT : LATCH_stmt B RLO RHI i) by (apply rso_latch_ok; [exact Hi | intros Hlt; lia]).
    apply rso_head_ok; [exact Hi|]. apply rso_r1_ok; [exact Hi | apply rso_r2_ok; [exact Hi | exact LT] | exact LT].
  - assert (LT : LATCH_stmt B RLO RHI i) by (apply rso_latch_ok; [exact Hi | intros Hlt; apply (IH (i + 1)); lia]).
    apply rso_head_ok; [exact Hi|]. apply rso_r1_ok; [exact Hi | apply rso_r2_ok; [exact Hi | exact LT] | exact LT]. }
intros i Hi. apply (G (Z.to_nat (27 - i)) i Hi). lia.
Qed.
End e.
End f.
End d.
