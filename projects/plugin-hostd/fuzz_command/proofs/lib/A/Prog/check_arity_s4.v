(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the shared blocks of the recorder calls of plugin-hostd/fuzz_command.asan
   (recorder.c:205-227, :252-277), after proofs/cgif/cgif_file_fuzzer/lib/A/AChc.v (the seed, the region and fact
   tables and the walk style of cgif_close) over fuzz_command's listing. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/RecBTemplate.v, with its module names changed; 481 of its 528 lines of code are new or changed and 141 lines of the source are left out. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP0i YCbn.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YN3v YI04 YI00 YG0s YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YG0q YC5d YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Rt Require Import RtDefs.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdSyms CmdList CmdPa CmdPaLib PaCall PaCallRun PaDenot PaLibF PaLibG PaLibH PaSB.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import CmdGlob CmdBase CmdRep CmdObj CmdAddr CmdRo CmdZsh.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A Require Import AF0m.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.A.Prog Require Import check_arity_s1 check_arity_s2 check_arity_s3.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition ca_final_ok (sr : list sv) : bool :=
sv_eqb (sr_get sr 1) (SOff 33 0) && sv_eqb (sr_get sr 2) (SOff 2 112) &&
sv_eqb (sr_get sr 3) (SOff 3 0) && sv_eqb (sr_get sr 4) (SOff 4 0) &&
sv_eqb (sr_get sr 8) (SOff 34 0) && sv_eqb (sr_get sr 9) (SOff 35 0) &&
sv_eqb (sr_get sr 18) (SOff 36 0) && sv_eqb (sr_get sr 19) (SOff 37 0) &&
sv_eqb (sr_get sr 20) (SOff 38 0) && sv_eqb (sr_get sr 21) (SOff 39 0) &&
sv_eqb (sr_get sr 22) (SOff 40 0) && sv_eqb (sr_get sr 23) (SOff 41 0) &&
sv_eqb (sr_get sr 24) (SOff 42 0) && sv_eqb (sr_get sr 25) (SOff 43 0) &&
sv_eqb (sr_get sr 26) (SOff 44 0) && sv_eqb (sr_get sr 27) (SOff 45 0).

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg cmd_listing}.
#[local] Notation SEGS := (@pa_segs _ cmd_listing PI).
#[local] Notation VAL := (@pa_val _ cmd_listing PI).
#[local] Notation BASE := (@pa_val _ cmd_listing PI A_TEXT).

Ltac ca_rb z lit j :=
  replace (Z_to_bv 5 z) with (lit : bv 5) by (apply bv_eq; reflexivity);
  match goal with GR : forall r, getr _ r = sv_denot _ (sr_get _ r) |- _ => rewrite GR end;
  match goal with Hq : sr_get (ss_regs _) lit = SOff ?n 0 |- _ => rewrite Hq;
    match goal with D0 : forall n, sv_denot _ (SOff n 0) = ew _ n |- _ => rewrite D0 end;
    change n with (32 + j)%nat end;
  match goal with EX : forall j, (j < 14)%nat -> ew _ (32 + j) = _ |- _ => rewrite (EX j ltac:(lia)) end;
  reflexivity.

Lemma ca_regs_back : forall (H : word -> bool) ss ms (regs regs0 : bvmap 5 word) s3v,
st_ok_pi SEGS VAL (Eimg (Ereg regs (ca_extra s3v regs0))) ss (restrict H ms) ->
ca_final_ok (ss_regs ss) = true ->
getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
spZ regs + 112 = spZ regs0 ->
aregs_preserved regs0 (ms_regs ms) /\ getr (ms_regs ms) 1 = getr regs0 1.
Proof.
intros H ss ms regs regs0 s3v HS Hf R3 R4 Hsp.
set (E := Eimg (Ereg regs (ca_extra s3v regs0))) in *.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r).
{ intros n r Hn. subst E. pose proof (bv_unsigned_in_range 5 r) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn. }
assert (EX : forall j, (j < 14)%nat -> ew E (32 + j) = nth j (ca_extra s3v regs0) (Z_to_bv 64 0)).
{ intros j Hj. subst E. rewrite Eimg_low by (unfold A_TEXT; lia). apply ew_Ereg_extra. }
assert (GR : forall r, getr (ms_regs ms) r = sv_denot E (sr_get (ss_regs ss) r)).
{ intros r. exact (st_ok_pi_restrict_reg H E ss ms r HS). }
unfold ca_final_ok in Hf. repeat rewrite andb_true_iff in Hf.
repeat match type of Hf with
| _ /\ _ => let A := fresh "Hq" in destruct Hf as [Hf A]; apply sv_eqb_eq in A
end.
apply sv_eqb_eq in Hf.
assert (D0 : forall n, sv_denot E (SOff n 0) = ew E n).
{ intros n. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. }
split.
- intros r Hr. unfold acallee_saved in Hr.
  assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
  clear Hr.
  destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]]]]]].
  + replace (Z_to_bv 5 2) with (2%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 2%bv = _ |- _ => rewrite Hq end.
    cbn [sv_denot]. rewrite (EE 2%nat 2%bv eq_refl). unfold spZ in Hsp. rewrite Hsp. apply Z_to_bv_bv_unsigned.
  + replace (Z_to_bv 5 3) with (3%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 3%bv = _ |- _ => rewrite Hq end.
    rewrite D0, (EE 3%nat 3%bv eq_refl). exact R3.
  + replace (Z_to_bv 5 4) with (4%bv : bv 5) by (apply bv_eq; reflexivity). rewrite GR.
    match goal with Hq : sr_get (ss_regs _) 4%bv = _ |- _ => rewrite Hq end.
    rewrite D0, (EE 4%nat 4%bv eq_refl). exact R4.
  + ca_rb 8 (8%bv : bv 5) 2%nat.
  + ca_rb 9 (9%bv : bv 5) 3%nat.
  + ca_rb 18 (18%bv : bv 5) 4%nat.
  + ca_rb 19 (19%bv : bv 5) 5%nat.
  + ca_rb 20 (20%bv : bv 5) 6%nat.
  + ca_rb 21 (21%bv : bv 5) 7%nat.
  + ca_rb 22 (22%bv : bv 5) 8%nat.
  + ca_rb 23 (23%bv : bv 5) 9%nat.
  + ca_rb 24 (24%bv : bv 5) 10%nat.
  + ca_rb 25 (25%bv : bv 5) 11%nat.
  + ca_rb 26 (26%bv : bv 5) 12%nat.
  + ca_rb 27 (27%bv : bv 5) 13%nat.
- rewrite GR. match goal with Hq : sr_get (ss_regs _) 1%bv = _ |- _ => rewrite Hq end.
  rewrite D0. change 33%nat with (32 + 1)%nat. rewrite (EX 1%nat ltac:(lia)). reflexivity.
Qed.

Section e.
Variable B : asyms.
Hypothesis HB : CmdBSyms B.
Let LAWS : AR_laws SEGS B := AR_laws_ok SEGS B.
Let RUNP := SRr_run_pi_AJ (L := cmd_listing) B LAWS.
Let RUNC := SRr_run_pi_AJ_call (L := cmd_listing) B LAWS.

Definition ca_post (regs0 : bvmap 5 word) ly S (W0 : world SEGS) mem0 md0 : world SEGS -> config -> Prop :=
apost_base SEGS B CHECK_ARITY_STK [] regs0 ly S W0 mem0 md0 EV_CHECK_ARITY
(fun ly' S' _ _ _ _ => ly' = ly /\ S' = S).

Definition ca_row_pre (k : nat) (mn mx : Z) ly S (W0 : world SEGS) (regs0 : bvmap 5 word) mem0 md0
(W : world SEGS) (regs : bvmap 5 word) memc mdc s3v : Prop :=
ajournal SEGS B CHECK_ARITY_STK (spZ regs0) [] ly S W0 mem0 md0 [] ly S W memc mdc 0 /\
YK0s.ret_ok (getr regs0 1) /\
cmd_ro_ok (aview SEGS (w_H W) memc) /\
spZ regs = spZ regs0 - 112 /\
ca_frame_at W memc (spZ regs) regs0 /\
getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
getr regs 9 = w64 (CA_GP + 24 * Z.of_nat k) /\ getr regs 18 = w64 SHADOW_OFF /\ getr regs 19 = w64 s3v /\
getr regs 21 = w64 (zcanon (- SHADOW_OFF - 3 * Z.of_nat k)) /\ getr regs 22 = w64 CA_GP /\
mn <= s3v <= mx /\ 0 <= s3v <= 63.

Lemma ca_row_open : forall k mn mx ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
(k < 22)%nat -> 0 <= mn ->
ca_row_pre k mn mx ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ca_extra s3v regs0))) (ca_ss k mn mx)
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + CA_SEG)) memc (seg_rom SEGS))).
Proof.
intros k mn mx ly S W0 regs0 mem0 md0 W regs memc mdc s3v Hk Hmn
(HJ & Hra & HRO & Hsp & HFR & R3 & R4 & R9 & R18 & R19 & R21 & R22 & Hs3 & Hs63).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal16 & _ & Hceil & Hslo & Hshi & H47 & _).
pose proof alloc_ceiling_value as [[Hc1 Hc2] _].
unfold CHECK_ARITY_STK, ESTACK in *.
apply (ca_seed B HB k mn mx s3v (spZ regs) ly S W regs0 regs memc mdc Hk Hmn ltac:(lia) ltac:(lia) HAR HRO eq_refl);
try lia.
- rewrite Hsp. replace (spZ regs0 - 112) with (spZ regs0 + (-7) * 16) by lia. rewrite Z_mod_plus_full. exact Hal16.
- intros a Ha. apply Hpres. lia.
- exact HFR.
- exact R9.
- exact R18.
- exact R19.
- exact R21.
- exact R22.
Qed.

Ltac ca_awr Usp :=
unfold ca_ss; cbn [ss_mem];
eapply awr_ok_cons_stack_off with (n := 2%nat) (d := -112);
[ reflexivity | rewrite Usp; lia | unfold CHECK_ARITY_STK, ESTACK; cbn; lia | cbn; lia |];
repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

Lemma ca_row_1 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 1 0 0 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 1 0 0 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_2 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 2 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 2 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_4 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 4 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 4 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_5 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 5 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 5 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_6 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 6 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 6 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_7 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 7 3 3 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 7 3 3 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_9 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 9 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 9 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_10 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 10 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 10 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_11 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 11 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 11 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_12 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 12 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 12 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_13 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 13 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 13 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_15 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 15 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 15 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_16 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 16 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 16 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_17 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 17 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 17 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_18 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 18 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 18 1 1 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_19 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 19 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 19 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_20 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 20 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 20 2 2 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

Lemma ca_row_21 : forall ly S W0 regs0 mem0 md0 W regs memc mdc s3v,
ca_row_pre 21 0 0 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ->
SRr SEGS W (cfg_at SEGS (BASE + CA_SEG) regs memc mdc) (ca_post regs0 ly S W0 mem0 md0).
Proof.
intros ly S W0 regs0 mem0 md0 W regs memc mdc s3v HP.
pose proof (ca_row_open 21 0 0 ly S W0 regs0 mem0 md0 W regs memc mdc s3v ltac:(lia) ltac:(lia) HP) as HS.
destruct HP as (HJ & Hra & HRO & Hsp & HFR & R3 & R4 & _).
unfold cfg_at. change (w64 (BASE + CA_SEG)) with (Z_to_bv 64 (BASE + CA_SEG)).
assert (Usp : bv_unsigned (ew (Eimg (Ereg regs (ca_extra s3v regs0))) 2) = spZ regs).
{ rewrite Eimg_low by (unfold A_TEXT; lia). rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl). reflexivity. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg regs (ca_extra s3v regs0)))) by apply Eimg_env.
paj_run_shc RUNP RUNC HS HJ.
{ ca_awr Usp. }
destruct (ca_regs_back (w_H W) _ ms regs regs0 s3v HS ltac:(vm_compute; reflexivity) R3 R4 ltac:(lia)) as [HPR Hra'].
eapply (paj_ret_at (L := cmd_listing) (PL := PL_cmd) (PI := PI) W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ca_post, apost_base.
lazymatch goal with |- exists _ _ _ _ _, mkCfg (mkst ?rg _ ?m _) ?d = _ /\ _ => exists ly, S, rg, m, d end.
split; [rewrite Hra'; unfold YK0s.ret_ok in Hra; rewrite Hra; reflexivity|].
split; [|split; [exact HPR | split; reflexivity]].
unfold EV_CHECK_ARITY. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
Qed.

End e.
End f.
End d.
