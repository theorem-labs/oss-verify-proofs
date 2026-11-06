(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC45.v for libreac/fuzz_grant's program walk: the listing's names are gsym and YC44 is GrantFrame; module paths changed. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import PaRun PaShadow GrantSyms GrantPa PaJournal GrantPaLib YC1g GrantFrame.
Import ListNotations.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Context {L : ptable gsym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Hypothesis LAWS : AR_laws pa_segs B.
#[local] Notation SEGS := (pa_segs).
#[local] Notation VAL := (pa_val).
Definition run_post_pi_AJ_call (W : world SEGS) (E : env) (ss ssc : sstate)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S W0 mem md own lyc Sc (mdc : Model) (k : Z)
(Q : world SEGS -> config -> Prop) : Prop :=
forall ms' mat',
st_ok SEGS E ssc (restrict (w_H W) ms') ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr SEGS W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma SRr_run_pi_AJ_call : forall W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q,
img_env VAL A_LIM E ->
st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) ->
sym_runN_pi pl_tpi n ss = (ss', PRS_call s) ->
ajournal SEGS B STK sp0 FP ly S W0 mem md own lyc Sc W (ms_mem ms) mdc k ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_pi_AJ_call W E ss (setpc ss' (pa_sigma s)) ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q ->
SRr SEGS W (mkCfg ms mdc) Q.
Proof.
intros W n E ss ss' s ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q HE HS Hrun HJ Hwr Hk.
unfold sym_runN_pi in Hrun. rewrite <- pl_tpi_eq in Hrun.
destruct (PaRun.sym_run_pi_sound gsym SEGS (clookup pa_tbl) VAL pa_sigma L pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim
_ E ss ss' (PRS_call s) _ HE HS Hrun) as (msr' & Hms & HP & _ & Hfr).
cbn [PaRun.prun_post] in HP.
eapply (SRr_chain_AJ SEGS B LAWS pa_segs_low pa_wx W E (abs_ss VAL ss) (setpc ss' (pa_sigma s)) ms msr');
[ exact Hms | exact HP | destruct ss; exact Hfr | exact HJ | destruct ss; exact Hwr | ].
intros ms' mat' HS' HJ' HF HF' HG. apply (Hk ms' mat' HS' HJ'); destruct ss; first [exact HF | exact HF' | exact HG].
Qed.
End e.
End d.
Lemma zone2_of_app {rc : YM05.RunCeil} : forall a n, in_app a n -> off_img a n -> zone2 a n.
Proof. intros a n [_ H] Hi. split; [exact Hi|]. unfold kLowShadowBeg, kHighMemBeg in H. lia. Qed.
Ltac paj_run_shc RUNP RUNC HS HJ :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_runN_pi tpi FUEL ss) in
lazymatch r with
| (?ss', PRS_call ?s) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', PRS_call s)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_shc: no hypothesis  img_env _ _ E" end in
eapply (RUNC W FUEL E ss ss' s ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun HJ);
[ clear Hrun | clear Hrun HS HJ; cbn [setpc];
let ms' := fresh "ms" in let mat := fresh "mat" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ms' mat HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ ]
| (?ss', ?st) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_pi tpi FUEL ss = (ss', st)) by (vm_compute; reflexivity);
let HEI := lazymatch goal with HEI : img_env _ _ E |- _ => HEI | _ => fail "paj_run_shc: no hypothesis  img_env _ _ E" end in
eapply (RUNP W FUEL E ss ss' st ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ HEI HS Hrun I HJ);
[ clear Hrun | clear Hrun HS HJ;
let ms' := fresh "ms" in let mat := fresh "mat" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ms' mat HS HJ HF HFr HG; cbn [ms_mem mkst] in HF, HFr, HG, HJ ]
end
end
| _ => fail "paj_run_shc: HS must be  st_ok_pi segs val E ss (restrict (w_H W) ms)"
end.
Ltac paj_run_to_shc RUNTOP HS HJ stop :=
paj_run_to_sh RUNTOP HS HJ stop;
[ | try (lazymatch goal with HFx : frame_of _ _ _ _ |- _ =>
repeat match goal with H : context [ms_mem (mkst _ _ _ _)] |- _ => progress cbn [ms_mem mkst] in H end end) ].
Ltac psrr_branch_pi RUNP BR HS :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of RUNP with
| forall W n E ss ss' st ms STK sp0 FP ly S W0 mem md own lyc Sc mdc k Q, _ -> _ -> sym_runN_pi ?tpi n ss = _ -> _ =>
let r := eval vm_compute in (sym_step_pi tpi ss) in
lazymatch r with
| PStop (SR_branch ?c ?a ?b) => apply (BR W E ss ms _ _ c a b HS); clear HS; let Hc := fresh "Hc" in intros Hc HS
| _ => fail "psrr_branch_pi: state is not stuck at a branch:" r
end end
end.
