(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: hex4 of fuzz_preset's asan-ubsan image (B, img_sigma AS_hex4, 260 bytes) KEEPS memnorm, proved from its run. One added property of lib/B/Prog/hex4_x.v's hex4_x_holds; no new walk.
   rule 24: proves function hex4 (reuse search: `proof-index skip_ws hex4 put_utf8 literal`, 2026-10-28T21:1xZ, exit 0, index built 2026-10-28T20:16:23Z; named-list cold grep 2026-10-29 exit 0; CONFIRM R24ReaderLeaf 2026-10-28T21:15Z). VERBATIM: `hex4: 8 file(s) named for it, 4 file(s) use its address, 4 related; in an earlier delivery 28 named for it and 196 name(s) that hold it, in 131 tree(s)` - named hits are fuzz_preset/fuzz_state released PLAIN + UBSAN proofs; none on asan builds; cold AsanRT walks template only. Adds one property to MY proved hex4_x_holds (A and B); no new walk.
   WHAT: hex4_x_holds_mnI : thex4_leafXmn SK rsegs B PST ARx (img_sigma AS_hex4) (lib/Prog/hex4_xs_mn.v), under the section context of hex4_x_holds (fx rc SK B PST ARx HL, LAWS, TL). thex4_leafXmn is thex4_leafX with the conjunct YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem' appended last to the post, and no entry premise.
   HOW: hex4_final / hex4_failret / hex4_turn / hex4_loop and hex4_x_holds's proof of hex4_x.v, re-run as hex4_finalP / hex4_failretP / hex4_turnP / hex4_loopP / hex4_mainP with an invariant Pinv of the full overlay: Pinv of the entry memory is a premise, Pinv of each continuation's memory is a premise of the continuation (after its journal premise), and Pinv of the end memory is a conjunct of each post (after the journal conjunct; last in hex4_mainP). The hypothesis is msteps_keeps rsegs Pinv (the statement of YSRrMemnorm.SRr_msteps_inv). Each runner segment is SRr_run_tok_AJxP / SRr_run_to_tok_AJxP over SRr_chain_tok_AJxP (YCbqG.SRr_chain_tok_AJx with SRr_msteps replaced by msteps_keeps; the Section tw lemmas of lib/B/Prog/skip_ws_mn.v at origin/cold/h-verbs-1-skip-mn 7c2e551b8f21, as there); a branch (YA0o.SRr_sym_branch) does not change the state; the return (YA0o.SRr_ret_at) leaves the memory as it is. The lemmas of hex4_x.v that make no run (hex4_entry_ok, the keeps / frame / garr8 lemmas, regs_pres_of_kept, ret_ok_mod2) and its tactic hexval_solve are used as they are; its section tactics xbr / prreg_raw / zcond / kept_at / acc_tac / cnt_tac (local to hex4_x.v's Section a) are copied verbatim, and xrun / xrunto / xafter / xafter2 / xtail are copied as xrunP / xruntoP / xafterP / xafter2P / xtailP, which pass and re-introduce the Pinv hypothesis HPM after the journal hypothesis HJ.
   INSTANCE: Pinv m := YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs m (memc fixed by the theorem's binder), so Pinv memc holds by (fun h => h) and Pinv mem' is the appended conjunct. Its laws srr_inv_laws_memnorm_from rsegs memc are YSRrMemnorm.srr_inv_laws_memnorm's three laws under the premise (YAkMemnorm.memnorm is YAjMemnorm.memnorm by conversion, YAkMemnormJ.memnorm_kit_j); msteps_keeps rsegs Pinv := YSRrMemnorm.SRr_msteps_inv rsegs img_wx Pinv (srr_inv_laws_memnorm_from rsegs memc). The proof uses no fact about where hex4 stores: YAkMemnorm.memnorm_msteps holds of every LPS run.
   ORDER: the walk proofs come before `Require YAjMemnorm YSRrMemnorm` (YAjMemnorm loads lib/Lib/LiaTwx2.v, which redefines lia), so they run under the lia hex4_x.v was proved with.
   Taken by path from origin/cold/h-srr-inv 11b525112ae: lib/Reusable/YAjMemnorm.v 4372e77e66c5, YAkMemnorm.v 96c72061b4d4, YAkMemnormJ.v f6dbdc03064b, YSRrMemnorm.v 39aa827e68cb. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YPsym YC4aP YC1fP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import hex4_xs hex4_xs_mn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_leaves PAImg_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import hex4_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section tw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Variable tbl : ctable.
Hypothesis tbl_ok : table_ok segs tbl.
Variable Pinv : (word -> option byte) -> Prop.
Definition msteps_keeps : Prop :=
forall (W : world segs) ms msr' model (Q : world segs -> config -> Prop),
msteps segs (restrict (w_H W) ms) msr' ->
Pinv (ms_mem ms) ->
(forall model', same_but_materialized model model' ->
hclean (w_H W) msr' ->
Pinv (ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) ->
SRr segs W (mkCfg (unrestrict (w_H W) (ms_mem ms) msr') model') Q) ->
SRr segs W (mkCfg ms model) Q.
Hypothesis MSI : msteps_keeps.
Definition run_post_tok_AJxP (W : world segs) (E : env) (K : nat) (Bx : sv) (SH : list shent) (ss : sstate) (st' : shst)
(ms : machine_state) (STK sp0 : Z) (FP : list (Z * Z)) ly S Hp W0 mem md own lyc Sc Hpc (mdc : Model) (k : Z)
(Q : world segs -> config -> Prop) : Prop :=
forall ws ms' mat',
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
Pinv (ms_mem ms') ->
frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q.
Lemma SRr_chain_tok_AJxP : forall W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
st_ok segs (extK E K ws) (sh_ss st') msr' ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJxP W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (MSI W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen).
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec (SK := SK) segs B PST ARx LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_tok_AJxP : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_tok segs tbl K Bx Bspan SH n ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJxP W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hk.
destruct (sym_run_tok_sound segs tbl K Bx Bspan SH tbl_ok n E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJxP; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
Qed.
Lemma SRr_run_to_tok_AJxP : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
st_ok segs E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_tok segs tbl K Bx Bspan SH n stop ss = (st', r) ->
match r with TS_ecall => False | _ => True end ->
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Pinv (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own ->
run_post_tok_AJxP W E K Bx SH ss st' ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hk.
destruct (sym_run_to_tok_sound segs tbl K Bx Bspan SH tbl_ok n stop E ss _ st' r HS Hsh Hchk Hrun Hobl)
as (ws & msr' & Hlen & Hms & HS' & Hsh' & _ & Hfr).
eapply SRr_chain_tok_AJxP; [exact Hms | exact Hlen | destruct r; [exact HS' | destruct Hr | exact HS'] | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
Qed.
End tw.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis TL : PALibCore (PI := PI_hex4) B.
Variable Pinv : (word -> option byte) -> Prop.
Hypothesis MSI : msteps_keeps rsegs Pinv.
Let RUNP := SRr_run_tok_AJxP SK rsegs B PST ARx LAWS img_segs_low hex4_tbl hex4_tbl_ok Pinv MSI.
Let RUNTOP := SRr_run_to_tok_AJxP SK rsegs B PST ARx LAWS img_segs_low hex4_tbl hex4_tbl_ok Pinv MSI.
Let RET := @SRr_ret_at rsegs fx hex4_tbl hex4_tbl_ok img_wx.
Ltac xbr cnd a b HS Hc := apply (SRr_sym_branch rsegs _ _ _ _ _ _ cnd a b HS); clear HS; intros Hc HS.
Ltac prreg_raw HS r Hr :=
lazymatch type of HS with
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
Ltac zcond H :=
rewrite ?branch_geu_U, ?branch_ltu_U, ?branch_ne_U, ?branch_eq_U in H;
rewrite ?U_SOff, ?U_SLit in H;
repeat (rewrite ew_ewset_other in H by lia);
repeat match goal with
| H' : negb _ = true |- _ => apply negb_true_iff in H'
| H' : negb _ = false |- _ => apply negb_false_iff in H'
| H' : (_ <? _) = true |- _ => apply Z.ltb_lt in H'
| H' : (_ <? _) = false |- _ => apply Z.ltb_ge in H'
| H' : (_ =? _) = true |- _ => apply Z.eqb_eq in H'
| H' : (_ =? _) = false |- _ => apply Z.eqb_neq in H'
end;
unfold zcanon, M64 in H.
Ltac kept_at regs0 extra0 HS HAE HKK :=
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs0 extra0 HEX4_KEPT HS
ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKK;
cbn [ms_regs restrict] in HKK.
Ltac acc_tac cc vv delta U33 U34 :=
apply (acc_or _ 33 34 cc vv delta);
[ repeat (rewrite ew_ewset_other by lia); exact U33
| repeat (rewrite ew_ewset_other by lia); exact U34
| lia | lia ].
Ltac cnt_tac ii Hcnt U35 :=
zcond Hcnt; rewrite U35 in Hcnt;
rewrite (Z.mod_small (4 - ii + -1)) in Hcnt by lia; rewrite (Z.mod_small 0) in Hcnt by lia; lia.
Ltac xrunP HS HJ HPM SHOK :=
lazymatch type of HS with
| st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 36 Bx SH ss) in
let res := eval vm_compute in (sym_runN_tok rsegs hex4_tbl K Bx XSPAN SH 200000%N ss) in
lazymatch res with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok rsegs hex4_tbl K Bx XSPAN SH 200000%N ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNP W 200000%N E K Bx XSPAN SH ss st' rs ms);
[ exact HS | exact SHOK | vm_compute; reflexivity | exact Hrun | exact I | exact HJ | exact HPM
| clear Hrun; cbn [sh_obls]; apply Forall_nil | clear Hrun | clear Hrun HS HJ HPM SHOK ]
end end end.
Ltac xruntoP stop HS HJ HPM SHOK :=
lazymatch type of HS with
| st_ok _ ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 36 Bx SH ss) in
let res := eval vm_compute in (sym_run_toN_tok rsegs hex4_tbl K Bx XSPAN SH 200000%N stop ss) in
lazymatch res with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok rsegs hex4_tbl K Bx XSPAN SH 200000%N stop ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNTOP W 200000%N stop E K Bx XSPAN SH ss st' rs ms);
[ exact HS | exact SHOK | vm_compute; reflexivity | exact Hrun | exact I | exact HJ | exact HPM
| clear Hrun; cbn [sh_obls]; apply Forall_nil | clear Hrun | clear Hrun HS HJ HPM SHOK ]
end end end.
Ltac xafterP HS HJ HPM SHOK :=
let ws := fresh "ws" in let ms' := fresh "msx" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HPM HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ, HPM.
Ltac xafter2P W HKEEP HGROW HS HJ HPM SHOK :=
let ws := fresh "ws" in let ms' := fresh "msx" in let mat' := fresh "mat" in let Hlen := fresh "Hlen" in
let HFa := fresh "HFa" in let HFb := fresh "HFb" in let HGc := fresh "HGc" in
let HK2 := fresh "HK2" in let HG2 := fresh "HG2" in
intros ws ms' mat' Hlen HS SHOK HJ HPM HFa HFb HGc;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HFa, HFb, HGc, HJ, HPM;
pose proof (keeps_trans W _ _ _ HKEEP (keeps_of_frame W _ _ _ _ (no_wrange_lc _) HFb)) as HK2;
clear HKEEP; rename HK2 into HKEEP;
pose proof (mem_grows_trans _ _ _ HGROW HGc) as HG2;
clear HGROW; rename HG2 into HGROW;
clear HFa HFb HGc.
Ltac xtailP W regs0 extra0 pp ii cc vv delta KS KE E2 E10 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ HPM SHOK :=
let Hcnt := fresh "Hcnt" in
let Q2 := fresh "Q2" in let Q5 := fresh "Q5" in let Q6 := fresh "Q6" in let Q7 := fresh "Q7" in
let Q10 := fresh "Q10" in let Q11 := fresh "Q11" in let Q12 := fresh "Q12" in let Q13 := fresh "Q13" in
let Q14 := fresh "Q14" in let Q15 := fresh "Q15" in let Q16 := fresh "Q16" in let Q17 := fresh "Q17" in
let HKK := fresh "HKK" in
xruntoP (HEX4_B + 0xa0) HS HJ HPM SHOK; [ apply awr_ok_lc | ];
xafter2P W HKEEP HGROW HS HJ HPM SHOK;
xbr BC_NE (SOff 35 (-1)) (SLit 0) HS Hcnt;
[ xruntoP (HEX4_B + 0x34) HS HJ HPM SHOK; [ apply awr_ok_lc | ];
xafter2P W HKEEP HGROW HS HJ HPM SHOK;
prreg HS (2%bv : bv 5) Q2; prreg HS (5%bv : bv 5) Q5; prreg HS (6%bv : bv 5) Q6;
prreg HS (7%bv : bv 5) Q7; prreg HS (10%bv : bv 5) Q10; prreg HS (11%bv : bv 5) Q11;
prreg HS (12%bv : bv 5) Q12; prreg_raw HS (13%bv : bv 5) Q13; prreg HS (14%bv : bv 5) Q14;
prreg HS (15%bv : bv 5) Q15; prreg HS (16%bv : bv 5) Q16; prreg HS (17%bv : bv 5) Q17;
kept_at regs0 extra0 HS HAE HKK; pmkst HS;
eapply (KS (cc + delta));
[ hexval_solve | cnt_tac ii Hcnt U35 | exact HKEEP | exact HGROW | exact HJ | exact HPM
| unfold turn_regs_ok; repeat split;
  [ rewrite Q2, E2; reflexivity | rewrite Q5; reflexivity | rewrite Q6; reflexivity
  | rewrite Q7, U32; unfold w64; f_equal; lia
  | rewrite Q10, E10; reflexivity | rewrite Q11, E11; reflexivity
  | rewrite Q12, U32; unfold w64; f_equal; lia
  | rewrite Q13; acc_tac cc vv delta U33 U34
  | rewrite Q14, E14; reflexivity
  | rewrite Q15, U35; unfold w64; f_equal; lia
  | rewrite Q16; reflexivity | rewrite Q17; reflexivity ]
| exact HKK ]
| xruntoP (HEX4_B + 0xb8) HS HJ HPM SHOK; [ apply awr_ok_lc | ];
xafter2P W HKEEP HGROW HS HJ HPM SHOK;
prreg HS (2%bv : bv 5) Q2; prreg HS (11%bv : bv 5) Q11; prreg_raw HS (13%bv : bv 5) Q13;
prreg HS (14%bv : bv 5) Q14; kept_at regs0 extra0 HS HAE HKK; pmkst HS;
eapply (KE (cc + delta));
[ hexval_solve | cnt_tac ii Hcnt U35 | exact HKEEP | exact HGROW | exact HJ | exact HPM
| rewrite Q2, E2; reflexivity | rewrite Q11, E11; reflexivity | rewrite Q13; acc_tac cc vv delta U33 U34
| rewrite Q14, E14; reflexivity | exact HKK ] ].
Lemma hex4_finalP : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp h ra0,
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 ->
getr regs 2 = w64 sp -> getr regs 11 = w64 o -> getr regs 13 = w64 h -> getr regs 14 = w64 SHADOW_OFF ->
0 <= h < 65536 ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 -> sp0 - STK <= sp -> sp + 16 <= sp0 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
hex4_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x) ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(sp + 16 <= o \/ o + 4 <= sp) ->
SRr rsegs W (mkCfg (mkst regs (w64 (HEX4_B + 0xb8)) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
(forall r, In r HEX4_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\ getr regs' 10 = w64 0 /\
val_mem rsegs (mrestrict (w_H W) mem') o 4 h /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (o <= x < o + 4) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)).
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp h ra0
HJ HPM R1 Hra Hra2 R2 R11 R13 R14 Hh Hsp16 Hsplo Hsphi Hsp0a Hsp0b Mra HOa HOal RAo HAWR HOpres HOsep.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
destruct HOa as (HOlo & HOhi).
set (E := Ereg regs [w64 h]).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E11 : ew E 11 = w64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E14 : ew E 14 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact R14).
assert (E32 : ew E 32 = w64 h) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (U1 : bv_unsigned (ew E 1) = ra0) by (rewrite E1; apply unsigned_lit_small; lia).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U14 : bv_unsigned (ew E 14) = SHADOW_OFF) by (rewrite E14; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = h) by (rewrite E32; apply unsigned_lit_small; lia).
assert (UBx : U E XBxL = SHADOW_OFF) by (unfold XBxL; apply (U_atom E 14 SHADOW_OFF E14); unfold SHADOW_OFF; lia).
assert (HS : st_ok rsegs E ss_f (restrict (w_H W) (mkst regs (w64 (HEX4_B + 0xb8)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_f. unfold w64 at 1. apply entry_st_ok_full.
- unfold fin_regs. apply regs_ok_pin; [unfold E; apply regs_ok_Ereg | discriminate |].
cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. exact R13.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stkL, outR;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
+ rewrite U11. split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|]. split; [|constructor].
intros x Hx. apply (apresent_writable rsegs). apply HOpres. lia.
- apply pairwise_disjoint_of_extents. unfold stkL, outR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U11.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, OUTx, SPfact, SBfact. cbn [af_lo af_hi af_al2].
rewrite U2, U11, U14, U32. change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 2) with 4.
rewrite !Z.mod_1_r. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs XBxL SHf E (mrestrict (w_H W) memc)).
{ unfold sh_ok, SHf. constructor; [|constructor].
apply (shent_ok_of_range rsegs (w_H W) memc E XBxL 11 o 4 o 0 4 RAo UBx);
[apply (U_atom E 11 o E11); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
xrunP HS HJ HPM SHOK.
{ intros a (r & Hin & Hr); cbn [ss_mem ss_f In] in Hin;
destruct Hin as [<-|[<-|[]]]; unfold stkL, outR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ rewrite U2 in Hr; lia | rewrite U11 in Hr; apply HAWR; lia ]. }
intros ws ms' mat' Hlen HS' SHOK' HJ' HPM' HF HFr HG.
cbn [sh_j sh_ss] in Hlen, HS', SHOK'.
repeat (destruct ws as [|? ws]; [discriminate Hlen | cbn [length] in Hlen; injection Hlen as Hlen]).
destruct ws; [clear Hlen | discriminate Hlen].
cbn [extK length Nat.add] in HS', SHOK'.
cbn [ms_mem mkst] in HF, HFr, HG, HJ', HPM'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (10%bv : bv 5) P10.
assert (HAE : env_agree 32 (Ereg regs [w64 h]) E) by (unfold E; apply env_agree_refl).
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs [w64 h] HEX4_KEPT HS' ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK, P1, P2, P10.
pose proof (st_ok_region_nth _ _ _ 1%nat
(YP09.mkRegion (Some 11%nat) 0 4 0 4 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))]) HS' eq_refl) as HRout.
destruct HRout as (_ & _ & _ & Hcs).
eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. clear HS' SHOK' HF HG. srr_norm_model.
cbn [YP09.r_base YP09.r_chunks YP09.c_off YP09.c_val base_val] in Hcs.
rewrite !ew_ewset_other in Hcs by lia. rewrite U11 in Hcs.
pose proof (proj1 (Forall_forall _ _) Hcs _ ltac:(left; reflexivity)) as Hchunk. clear Hcs.
split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite P1, E1, R1; unfold w64;
rewrite (v_jalr_lit_even ra0 ltac:(lia) Hra2); reflexivity|].
split; [pose proof (ajournal_x_materialize rsegs B PST ARx LAWS img_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ') as HJ2;
rewrite wvb_collapse in HJ2; exact HJ2|].
split; [exact HPM'|].
split; [exact HK|].
split; [cbn [ms_regs]; rewrite P2, U2; reflexivity|].
split; [cbn [ms_regs]; rewrite P10; reflexivity|].
split.
- cbn [ms_mem restrict] in Hchunk |- *.
assert (HV : val_mem rsegs (mrestrict (w_H W) (ms_mem ms')) (o + 0) (N.to_nat 4) h).
{ lazymatch type of Hchunk with YP09.chunk_ok _ ?EE _ _ _ =>
apply (val_of_chunk_ok rsegs EE _ o 0 4 (SOff 32 0) h) end;
[ exact Hchunk
| cbn [sv_denot]; rewrite !ew_ewset_other by lia; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| cbn; lia | lia]. }
cbn [N.to_nat Pos.to_nat Pos.iter_op Nat.add] in HV. rewrite Z.add_0_r in HV. exact HV.
- intros x Hx Hnot. cbn [ms_mem].
apply (frame_aview E (ss_mem ss_f) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_f In] in Hin.
destruct Hin as [<-|[<-|[]]]; unfold stkL, outR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ rewrite U2 in Hr; lia | rewrite U11 in Hr; apply Hnot; lia ].
Qed.
Lemma hex4_failretP : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0,
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 -> getr regs 2 = w64 sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
SRr rsegs W (mkCfg (mkst regs (w64 (HEX4_B + 0xdc)) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
(forall r, In r HEX4_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\ getr regs' 10 = w64 (-1) /\ keeps W memc mem').
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0
HJ HPM R1 Hra Hra2 R2 Hsp16 Hsplo Hsphi Mra.
set (E := Ereg regs (@nil word)).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_q (restrict (w_H W) (mkst regs (w64 (HEX4_B + 0xdc)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_q. unfold w64 at 1. apply entry_st_ok_full.
- unfold E. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stkL;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, SPfact. cbn [af_lo af_hi af_al2].
rewrite U2. change (2 ^ 4) with 16. repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs XBxL (@nil shent) E (mrestrict (w_H W) memc)) by (unfold sh_ok; apply Forall_nil).
xrunP HS HJ HPM SHOK.
{ intros a (r & Hin & Hr); cbn [ss_mem ss_q In] in Hin;
destruct Hin as [<-|[]]; unfold stkL in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia. }
xafterP HS' HJ' HPM' SHOK'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (10%bv : bv 5) P10.
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E) by (unfold E; apply env_agree_refl).
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs (@nil word) HEX4_KEPT HS' ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK, P1, P2, P10.
eapply (RET W _ _ _ _ _ HS' eq_refl ltac:(vm_compute; reflexivity)).
intros mat2. clear HS' SHOK' HF HG. srr_norm_model.
split; [reflexivity|].
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite P1, E1, R1; unfold w64;
rewrite (v_jalr_lit_even ra0 ltac:(lia) Hra2); reflexivity|].
split; [pose proof (ajournal_x_materialize rsegs B PST ARx LAWS img_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mat2 HJ') as HJ2;
rewrite wvb_collapse in HJ2; exact HJ2|].
split; [exact HPM'|].
split; [exact HK|].
split; [cbn [ms_regs]; rewrite P2, U2; reflexivity|].
split; [cbn [ms_regs]; rewrite P10; apply bv_eq; vm_compute; reflexivity|].
intros x Hx. cbn [ms_mem].
apply (frame_aview E (ss_mem ss_q) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_q In] in Hin.
destruct Hin as [<-|[]]; unfold stkL in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; lia.
Qed.
Lemma hex4_turnP : forall (W : world rsegs) regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k
p o sp ra0 i v c (Q : world rsegs -> config -> Prop),
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
0 <= i <= 3 -> 0 <= v < 4096 -> 0 <= c < 256 ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 ->
turn_regs_ok regs p i o v sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
hex4_src_ok p -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
val_mem rsegs (mrestrict (w_H W) memc) (p + i) 1 c ->
hex4_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(sp + 16 <= p \/ p + 4 <= sp) ->
(forall d mem2 mdc2 regs2, PjGrammar.hexval c = Some d -> 4 - i - 1 <> 0 ->
keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
Pinv mem2 ->
turn_regs_ok regs2 p (i + 1) o (16 * v + d) sp ->
(forall r, In r HEX4_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (HEX4_B + 0x34)) mem2 (seg_rom rsegs)) mdc2) Q) ->
(forall d mem2 mdc2 regs2, PjGrammar.hexval c = Some d -> 4 - i - 1 = 0 ->
keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
Pinv mem2 ->
getr regs2 2 = w64 sp -> getr regs2 11 = w64 o -> getr regs2 13 = w64 (16 * v + d) ->
getr regs2 14 = w64 SHADOW_OFF ->
(forall r, In r HEX4_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (HEX4_B + 0xb8)) mem2 (seg_rom rsegs)) mdc2) Q) ->
(forall mem2 mdc2 regs2, PjGrammar.hexval c = None ->
keeps W memc mem2 -> mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) mem2) ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem2 mdc2 k ->
Pinv mem2 ->
getr regs2 2 = w64 sp ->
(forall r, In r HEX4_KEPT -> getr regs2 r = getr regs r) ->
SRr rsegs W (mkCfg (mkst regs2 (w64 (HEX4_B + 0xdc)) mem2 (seg_rom rsegs)) mdc2) Q) ->
SRr rsegs W (mkCfg (mkst regs (w64 (HEX4_B + 0x34)) memc (seg_rom rsegs)) mdc) Q.
Proof.
intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 i v c Q
HJ HPM Hi Hv Hc256 R1 Hra (R2 & R5 & R6 & R7 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17)
Hsp16 Hsplo Hsphi Mra HPa RAp Mc HOa HOal RAo Hsp_p KS KE KF.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
destruct HPa as (HPlo & HPhi).
destruct HOa as (HOlo & HOhi).
set (E := Ereg regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)]).
assert (E1 : ew E 1 = w64 ra0) by (unfold E; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1).
assert (E2 : ew E 2 = w64 sp) by (unfold E; rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl); exact R2).
assert (E10 : ew E 10 = w64 p) by (unfold E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10).
assert (E11 : ew E 11 = w64 o) by (unfold E; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E14 : ew E 14 = w64 SHADOW_OFF) by (unfold E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact R14).
assert (E32 : ew E 32 = w64 (p + i)) by (unfold E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 c) by (unfold E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 v) by (unfold E; exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = w64 (4 - i)) by (unfold E; exact (ew_Ereg_extra regs _ 3)).
assert (U2 : bv_unsigned (ew E 2) = sp) by (rewrite E2; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = p) by (rewrite E10; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U14 : bv_unsigned (ew E 14) = SHADOW_OFF) by (rewrite E14; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = p + i) by (rewrite E32; apply unsigned_lit_small; unfold kLowShadowBeg, kHighMemBeg in *; lia).
assert (U33 : bv_unsigned (ew E 33) = c) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = v) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = 4 - i) by (rewrite E35; apply unsigned_lit_small; lia).
assert (UBx : U E XBxL = SHADOW_OFF) by (unfold XBxL; apply (U_atom E 14 SHADOW_OFF E14); unfold SHADOW_OFF; lia).
assert (HS : st_ok rsegs E ss_l (restrict (w_H W) (mkst regs (w64 (HEX4_B + 0x34)) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_l. unfold w64 at 1. apply entry_st_ok_full.
- unfold loop_regs.
repeat (apply regs_ok_pin; [|discriminate|cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned;
first [exact R12 | exact R7 | exact R15 | exact R16 | exact R17 | exact R5 | exact R6 | exact R13
| rewrite E32; reflexivity | rewrite E35; reflexivity | rewrite E34; reflexivity]]).
unfold E. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- repeat apply Forall_cons; try apply Forall_nil; unfold region_ok, stkL, curR;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite U2. split; [lia|]. split; [lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ sp 8 8 (SOff 1 0) ra0);
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | lia | lia | exact Mra].
+ rewrite U32. split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|].
split; [unfold kLowShadowBeg, kHighMemBeg in *; lia|]. split; [intros x Hx; lia|].
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ (p + i) 0 1 (SOff 33 0) c);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact Mc.
- apply pairwise_disjoint_of_extents. unfold stkL, curR, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U2, U32.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok, SRCx, OUTx, SPfact, SBfact. cbn [af_lo af_hi af_al2].
rewrite U2, U10, U11, U14, U32, U33, U34, U35.
change (2 ^ 4) with 16. change (2 ^ 0) with 1. change (2 ^ 2) with 4. rewrite !Z.mod_1_r.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *.
repeat match goal with |- _ /\ _ => split end; lia. }
assert (SHOK : sh_ok rsegs XBxL SHl E (mrestrict (w_H W) memc)).
{ unfold sh_ok, SHl. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range rsegs (w_H W) memc E XBxL 32 p 4 (p + i) 0 1 RAp UBx);
[apply (U_atom E 32 (p + i) E32); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- apply (shent_ok_of_range rsegs (w_H W) memc E XBxL 11 o 4 o 0 4 RAo UBx);
[apply (U_atom E 11 o E11); unfold kLowShadowBeg, kHighMemBeg in *; lia | lia | lia |].
intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia. }
assert (HAE : env_agree 32 (Ereg regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)]) E)
by (unfold E; apply env_agree_refl).
assert (HKEEP : keeps W memc memc) by apply keeps_refl.
assert (HGROW : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) memc)) by apply mem_grows_refl.
xbr BC_LTU (SOff 32 0) (SOff 10 0) HS Hb1.
- exfalso. zcond Hb1. rewrite U32, U10 in Hb1.
rewrite (Z.mod_small (p + i + 0)) in Hb1 by (unfold kLowShadowBeg, kHighMemBeg in *; lia).
rewrite (Z.mod_small (p + 0)) in Hb1 by (unfold kLowShadowBeg, kHighMemBeg in *; lia). lia.
- clear Hb1. xrunP HS HJ HPM SHOK. { apply awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
xbr BC_GEU (SOff 33 (-48)) (SLit 10) HS Hb2.
+
zcond Hb2. rewrite U33 in Hb2.
assert (Nd : ~ (0 <= c + (-48) < 10)) by (intros Hx; apply (proj2 (lt_mod_iff c (-48) 10 Hc256 ltac:(lia) ltac:(lia))) in Hx; lia).
clear Hb2.
xrunP HS HJ HPM SHOK. { apply awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
xbr BC_GEU (SOff 33 (-97)) (SLit 6) HS Hb3.
*
zcond Hb3. rewrite U33 in Hb3.
assert (Nl : ~ (0 <= c + (-97) < 6)) by (intros Hx; apply (proj2 (lt_mod_iff c (-97) 6 Hc256 ltac:(lia) ltac:(lia))) in Hx; lia).
clear Hb3.
xrunP HS HJ HPM SHOK. { apply awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
xbr BC_LTU (SLit 5) (SOff 33 (-65)) HS Hb4.
--
zcond Hb4. rewrite U33 in Hb4.
apply (proj1 (lt_mod_iff2 c (-65) 5 Hc256 ltac:(lia) ltac:(lia))) in Hb4.
xruntoP (HEX4_B + 0xdc) HS HJ HPM SHOK. { apply awr_ok_lc. } xafter2P W HKEEP HGROW HS HJ HPM SHOK.
prreg HS (2%bv : bv 5) Q2. kept_at regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] HS HAE HKK.
pmkst HS.
eapply KF; [ hexval_solve | exact HKEEP | exact HGROW | exact HJ | exact HPM | rewrite Q2, E2; reflexivity | exact HKK ].
--
zcond Hb4. rewrite U33 in Hb4.
assert (Nu : 65 <= c <= 70)
by (assert (Hx : ~ (c + (-65) < 0 \/ 5 < c + (-65)))
by (intros Hy; apply (proj2 (lt_mod_iff2 c (-65) 5 Hc256 ltac:(lia) ltac:(lia))) in Hy; lia); lia).
clear Hb4.
xtailP W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-55) KS KE E2 E10 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ HPM SHOK.
*
zcond Hb3. rewrite U33 in Hb3.
apply (proj1 (lt_mod_iff c (-97) 6 Hc256 ltac:(lia) ltac:(lia))) in Hb3.
assert (Nu : 0 <= c + (-87) < 16) by lia.
xtailP W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-87) KS KE E2 E10 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ HPM SHOK.
+
zcond Hb2. rewrite U33 in Hb2.
apply (proj1 (lt_mod_iff c (-48) 10 Hc256 ltac:(lia) ltac:(lia))) in Hb2.
assert (Nu : 0 <= c + (-48) < 16) by lia.
xtailP W regs [w64 (p + i); w64 c; w64 v; w64 (4 - i)] p i c v (-48) KS KE E2 E10 E11 E14 U32 U33 U34 U35 HAE HKEEP HGROW HS HJ HPM SHOK.
Qed.
Definition loop_postP (W : world rsegs) regs (STK sp0 : Z) FP ly S Hp W0 mem0 md0 own lyc Sc Hpc
(memc : word -> option byte) (k o sp : Z) (res : option Z) : world rsegs -> config -> Prop :=
fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
(forall r, In r HEX4_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (sp + 16) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (o <= x < o + 4) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
match res with
| Some h => getr regs' 10 = w64 0 /\ val_mem rsegs (mrestrict (w_H W) mem') o 4 h
| None => getr regs' 10 = w64 (-1) /\
(forall x, o <= x < o + 4 -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)
end.
Lemma hex4_loopP : forall (n : nat) (i v : Z) (W : world rsegs) regs memc mdc
STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 (rest : list Z),
Z.of_nat n = 3 - i -> 0 <= i <= 3 -> 0 <= v < 16 ^ i ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
getr regs 1 = w64 ra0 -> 4096 <= ra0 < 2 ^ 64 -> ra0 mod 2 = 0 ->
turn_regs_ok regs p i o v sp ->
sp mod 16 = 0 -> 2 ^ 46 <= sp -> sp + 16 <= 2 ^ 47 -> sp0 - STK <= sp -> sp + 16 <= sp0 ->
val_mem rsegs (mrestrict (w_H W) memc) (sp + 8) 8 ra0 ->
hex4_src_ok p -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
garr8 rsegs (mrestrict (w_H W) memc) (p + i) rest -> Z.of_nat (length rest) = 4 - i ->
hex4_out_ok o -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x) ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(sp + 16 <= p \/ p + 4 <= sp) -> (sp + 16 <= o \/ o + 4 <= sp) ->
SRr rsegs W (mkCfg (mkst regs (w64 (HEX4_B + 0x34)) memc (seg_rom rsegs)) mdc)
(loop_postP W regs STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc memc k o sp (hacc v rest)).
Proof.
induction n as [|n IH]; intros i v W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 rest
Hn Hi Hv HJ HPM R1 Hra Hra2 TR Hsp16 Hsplo Hsphi Hsp0a Hsp0b Mra HPa RAp GBS Hlen HOa HOal RAo HAWR HOpres Hsp_p Hsp_o;
(pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL);
(pose proof HPa as (HPlo & HPhi));
(pose proof HOa as (HOlo & HOhi));
(destruct rest as [|c rest']; [cbn [length] in Hlen; exfalso; lia|]);
(destruct (garr8_hd W memc (p + i) c rest' GBS) as (Mc & Hc256));
(cbn [length] in Hlen);
(assert (Hvb : 0 <= v < 4096)
by (assert (16 ^ i <= 16 ^ 3) by (apply Z.pow_le_mono_r; lia); cbn in *; lia));
(eapply (hex4_turnP W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 i v c _
HJ HPM Hi Hvb Hc256 R1 Hra TR Hsp16 Hsplo Hsphi Mra HPa RAp Mc HOa HOal RAo Hsp_p)).
{ intros d mem2 mdc2 regs2 Hhv Hne HK2 HG2 HJ2 HPM2 TR2 HKK. exfalso. lia. }
{ intros d mem2 mdc2 regs2 Hhv Heq HK2 HG2 HJ2 HPM2 R2' R11' R13' R14' HKK.
pose proof (hexval_range c d Hhv) as Hd.
assert (Hi3 : i = 3) by lia.
eapply SRr_mono.
- eapply (hex4_finalP W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k o sp (16 * v + d) ra0 HJ2 HPM2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2' | exact R11' | exact R13' | exact R14'
| subst i; cbn in Hv; lia | exact Hsp16 | exact Hsplo | exact Hsphi | exact Hsp0a | exact Hsp0b
| exact (keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra)
| exact HOa | exact HOal
| exact (keeps_ra W memc mem2 o 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAo)
| exact HAWR | intros x Hx; exact (apresent_grows (w_H W) memc mem2 x HG2 (HOpres x Hx))
| exact Hsp_o ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HPM' & HKK' & R2'' & R10' & MV & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [exact HPM'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx Hnot); exact (HK2 x Hx)|].
cbn [hacc]. rewrite Hhv.
assert (Hr0 : rest' = []) by (destruct rest' as [|y r2]; [reflexivity | cbn [length] in Hlen; exfalso; lia]).
rewrite Hr0. cbn [hacc]. split; [exact R10' | exact MV]. }
{ intros mem2 mdc2 regs2 Hhv HK2 HG2 HJ2 HPM2 R2' HKK.
eapply SRr_mono.
- eapply (hex4_failretP W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0 HJ2 HPM2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2'
| exact Hsp16 | exact Hsplo | exact Hsphi
| exact (keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra) ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HPM' & HKK' & R2'' & R10' & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [exact HPM'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx); exact (HK2 x Hx)|].
cbn [hacc]. rewrite Hhv.
split; [exact R10' | intros x Hx; rewrite (HKEEP' x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia));
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
{ intros d mem2 mdc2 regs2 Hhv Hne HK2 HG2 HJ2 HPM2 TR2 HKK.
pose proof (hexval_range c d Hhv) as Hd.
eapply SRr_mono.
- eapply (IH (i + 1) (16 * v + d) W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k p o sp ra0 rest');
[ lia | lia | rewrite Z.pow_add_r by lia; cbn [Z.pow Z.pow_pos Pos.iter]; lia
| exact HJ2 | exact HPM2 | rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2
| exact TR2 | exact Hsp16 | exact Hsplo | exact Hsphi | exact Hsp0a | exact Hsp0b
| exact (keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra)
| exact HPa
| exact (keeps_ra W memc mem2 p 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAp)
| replace (p + (i + 1)) with (p + i + 1) by lia;
exact (keeps_garr8 W memc mem2 (p + i + 1) rest' HK2 ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) (garr8_tl W memc (p + i) c rest' GBS))
| lia | exact HOa | exact HOal
| exact (keeps_ra W memc mem2 o 4 HK2 ltac:(lia) ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) RAo)
| exact HAWR | intros x Hx; exact (apresent_grows (w_H W) memc mem2 x HG2 (HOpres x Hx))
| exact Hsp_p | exact Hsp_o ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HPM' & HKK' & R2'' & HKEEP' & Hres).
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [exact HPM'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx Hnot); exact (HK2 x Hx)|].
cbn [hacc]. rewrite Hhv.
destruct (hacc (16 * v + d) rest') as [h|].
+ destruct Hres as (R10' & MV). split; [exact R10' | exact MV].
+ destruct Hres as (R10' & Hk). split; [exact R10' | intros x Hx; rewrite (Hk x Hx);
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
{ intros d mem2 mdc2 regs2 Hhv Heq HK2 HG2 HJ2 HPM2 R2' R11' R13' R14' HKK. exfalso. lia. }
{ intros mem2 mdc2 regs2 Hhv HK2 HG2 HJ2 HPM2 R2' HKK.
eapply SRr_mono.
- eapply (hex4_failretP W regs2 mem2 mdc2 STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k sp ra0 HJ2 HPM2);
[ rewrite (HKK 1%bv ltac:(cbv; tauto)); exact R1 | exact Hra | exact Hra2 | exact R2'
| exact Hsp16 | exact Hsplo | exact Hsphi
| exact (keeps_val_mem W memc mem2 (sp + 8) 8 ra0 HK2 ltac:(lia) ltac:(cbn; lia) Mra) ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ' & HPM' & HKK' & R2'' & R10' & HKEEP').
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', (HKK 1%bv ltac:(cbv; tauto)); reflexivity|].
split; [exact HJ'|].
split; [exact HPM'|].
split; [intros r Hr; rewrite (HKK' r Hr); exact (HKK r Hr)|].
split; [exact R2''|].
split; [intros x Hx Hnot; rewrite (HKEEP' x Hx); exact (HK2 x Hx)|].
cbn [hacc]. rewrite Hhv.
split; [exact R10' | intros x Hx; rewrite (HKEEP' x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia));
exact (HK2 x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia))]. }
Qed.
Lemma hex4_mainP : forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (p o : Z) (BS : list Z),
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 10 = w64 p -> getr regs 11 = w64 o ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - HEX4_STK -> spZ regs <= sp0 ->
(forall x, spZ regs - HEX4_STK <= x < spZ regs -> apresent (w_H W) memc x) ->
4096 <= p -> amem_range p 4 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF p 4 ->
garr8 rsegs (mrestrict (w_H W) memc) p BS -> Z.of_nat (length BS) = 4 ->
spZ regs <= o -> o + 4 <= sp0 -> o mod 4 = 0 -> range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF o 4 ->
(forall x, o <= x < o + 4 -> apresent (w_H W) memc x) ->
(o + 4 <= p \/ p + 4 <= o) ->
(spZ regs <= p \/ p + 4 <= spZ regs - HEX4_STK) ->
SRr rsegs W (cfg_at rsegs (img_sigma AS_hex4) regs memc mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
aregs_preserved regs regs' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - HEX4_STK <= x < spZ regs) -> ~ (o <= x < o + 4) ->
aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
match PjGrammar.hex4 BS with
| Some h => getr regs' 10 = w64 0 /\ val_mem rsegs (mrestrict (w_H W) mem') o 4 h
| None => getr regs' 10 = w64 (-1) /\
(forall x, o <= x < o + 4 -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x)
end /\ Pinv mem').
Proof.
change (img_sigma AS_hex4) with HEX4_B.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs p o BS
HJ HPM Hret Hra4 R10 R11 Hsp16 Hsp0a Hsp0b HPres HPlo HPam RAp GBS Hlen HOlo HOhi HOal RAo HOpres Hsep Hsp_p.
pose proof (proj1 (@ASAN_CEIL_range _)) as HCEIL.
assert (HPhi : p + 4 < 2 ^ 47) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HPam; lia).
assert (HPa : hex4_src_ok p)
by (split; [exact HPlo | unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HPam; lia]).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _ & _).
pose proof Hstk as (Hsp016 & HSTK0 & Hceil & Hslo & Hshi & H47 & _ & _ & _).
pose proof (ret_ok_mod2 _ Hret) as Hra2.
assert (Hra64 : 4096 <= raZ regs < 2 ^ 64).
{ pose proof (bv_unsigned_in_range 64 (getr regs 1)) as Hx.
change (bv_modulus 64) with (2 ^ 64) in Hx. unfold raZ in *. lia. }
set (spE := spZ regs) in *. set (ra0 := raZ regs) in *.
assert (R1 : getr regs 1 = w64 ra0) by (unfold ra0, raZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (R2 : getr regs 2 = w64 spE) by (unfold spE, spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (HspL : 2 ^ 46 <= spE - 16) by (unfold spE, HEX4_STK, ASAN_CEIL in *; lia).
assert (HspH : spE <= 2 ^ 47) by (unfold spE, HEX4_STK, ASAN_CEIL in *; lia).
assert (HOa : hex4_out_ok o) by (unfold hex4_out_ok; split; lia).
assert (HAWR : forall x, o <= x < o + 4 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x)
by (intros x Hx; unfold awr_byte; left; unfold HEX4_STK in Hsp0a; lia).
assert (Hsp_o : spE <= o \/ o + 4 <= spE - HEX4_STK) by (left; exact HOlo).
destruct (hex4_entry_ok B ARx LAWS TL W regs memc mdc lyc Sc Hpc p o spE (proj1 HJ) R2 HspL HspH Hsp16
R10 R11 HPa HOa HOal RAp RAo HPres) as (HS & SHOK).
unfold cfg_at.
xruntoP (HEX4_B + 0x34) HS HJ HPM SHOK.
{ intros a (r & Hin & Hr). cbn [ss_mem ss_e In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; unfold stkE, gotR, cellR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr;
[ | lia | lia ].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hr. unfold w64 in Hr.
rewrite (unsigned_lit_small spE) in Hr by lia. left. unfold HEX4_STK in *. lia. }
xafterP HS' HJ' HPM' SHOK'.
prreg HS' (1%bv : bv 5) P1. prreg HS' (2%bv : bv 5) P2. prreg HS' (5%bv : bv 5) P5.
prreg HS' (6%bv : bv 5) P6. prreg HS' (7%bv : bv 5) P7. prreg HS' (10%bv : bv 5) P10.
prreg HS' (11%bv : bv 5) P11. prreg HS' (12%bv : bv 5) P12. prreg HS' (13%bv : bv 5) P13.
prreg HS' (14%bv : bv 5) P14. prreg HS' (15%bv : bv 5) P15. prreg HS' (16%bv : bv 5) P16.
prreg HS' (17%bv : bv 5) P17.
assert (HAE : env_agree 32 (Ereg regs [w64 SHADOW_OFF]) (Ereg regs [w64 SHADOW_OFF])) by apply env_agree_refl.
pose proof (regs_kept_of_st_ok rsegs _ _ _ regs [w64 SHADOW_OFF] HEX4_KEPT HS'
ltac:(env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HKE.
cbn [ms_regs restrict] in HKE, P1, P2, P5, P6, P7, P10, P11, P12, P13, P14, P15, P16, P17.
pose proof (st_ok_region_nth _ _ _ 0%nat
(YP09.mkRegion (Some 2%nat) (-16) 0 (-16) 0 [YP09.mkChunk (-8) (CVal 8 (SOff 1 0))]) HS' eq_refl) as HRstk.
destruct HRstk as (_ & _ & _ & Hcs). cbn [YP09.r_base YP09.r_chunks base_val] in Hcs.
assert (HKO : keeps_out W (spE - 16) spE memc (ms_mem msx)).
{ intros x Hx Hnot. apply (frame_aview (Ereg regs [w64 SHADOW_OFF]) (ss_mem ss_e) memc _ (w_H W) x HFr Hx).
intros (r & Hin & Hr). cbn [ss_mem ss_e In] in Hin.
destruct Hin as [<-|[<-|[<-|[]]]]; unfold stkE, gotR, cellR in Hr;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; [|lia|lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hr. unfold w64 in Hr.
rewrite (unsigned_lit_small spE) in Hr by lia. lia. }
assert (Mra : val_mem rsegs (mrestrict (w_H W) (ms_mem msx)) (spE - 16 + 8) 8 ra0).
{ replace (spE - 16 + 8) with (spE + -8) by lia.
apply (val_of_chunk_ok rsegs (Ereg regs [w64 SHADOW_OFF]) _ spE (-8) 8 (SOff 1 0) ra0);
[ | cbn [sv_denot]; rewrite (ew_Ereg_nat regs _ 1 1%bv eq_refl), R1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| lia | lia].
rewrite (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2 in Hcs. unfold w64 in Hcs.
rewrite (unsigned_lit_small spE) in Hcs by lia.
exact (proj1 (Forall_forall _ _) Hcs _ ltac:(left; reflexivity)). }
pmkst HS'.
eapply SRr_mono.
- eapply (hex4_loopP 3%nat 0 0 W (ms_regs msx) (ms_mem msx) _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k
p o (spE - 16) ra0 BS);
[ cbn; reflexivity | lia | cbn; lia | exact HJ' | exact HPM'
| rewrite P1, (ew_Ereg_nat regs _ 1 1%bv eq_refl); exact R1 | exact Hra64 | exact Hra2
| unfold turn_regs_ok; repeat split;
  [ rewrite P2, (ew_Ereg_nat regs _ 2 2%bv eq_refl), R2; unfold w64;
rewrite (unsigned_lit_small spE) by lia; f_equal; lia
  | rewrite P5; reflexivity | rewrite P6; reflexivity
  | rewrite P7, (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; unfold w64; f_equal; lia
  | rewrite P10, (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact R10
  | rewrite P11, (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11
  | rewrite P12, (ew_Ereg_nat regs _ 10 10%bv eq_refl), R10; unfold w64; f_equal; lia
  | rewrite P13; reflexivity
  | rewrite P14; cbn [ew Ereg nth Nat.ltb Nat.leb]; reflexivity
  | rewrite P15; unfold w64; f_equal; lia
  | rewrite P16; reflexivity | rewrite P17; reflexivity ]
| lia | lia | lia | unfold HEX4_STK in Hsp0a; lia | lia
| exact Mra | exact HPa
| exact (out_ra W (spE - 16) spE memc (ms_mem msx) p 4 HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold SHADOW_OFF; lia) RAp)
| rewrite Z.add_0_r;
exact (out_garr8 W (spE - 16) spE memc (ms_mem msx) p BS HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia)
ltac:(unfold HEX4_STK in Hsp_p; lia) GBS)
| rewrite Z.sub_0_r; exact Hlen | exact HOa | exact HOal
| exact (out_ra W (spE - 16) spE memc (ms_mem msx) o 4 HKO ltac:(lia)
ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold SHADOW_OFF; lia) RAo)
| exact HAWR
| intros x Hx; exact (apresent_grows (w_H W) memc (ms_mem msx) x HG (HOpres x Hx))
| unfold HEX4_STK in Hsp_p; lia | unfold HEX4_STK in Hsp_o; lia ].
- cbv beta. intros W' c' Hwle (-> & regs' & mem' & md' & Hc' & HJ2 & HPM2 & HKK & R2' & HKEEP & Hres).
split; [reflexivity|]. exists regs', mem', md'.
split; [rewrite Hc', P1, (ew_Ereg_nat regs _ 1 1%bv eq_refl); reflexivity|].
split; [exact HJ2|].
split.
{ apply (regs_pres_of_kept regs regs').
- intros r Hr. rewrite (HKK r Hr). exact (HKE r Hr).
- rewrite R2', R2. unfold w64. f_equal. lia. }
split.
{ intros x Hx Hn1 Hn2. unfold HEX4_STK in Hn1.
rewrite (HKEEP x Hx Hn2). exact (HKO x Hx ltac:(lia)). }
split; [|exact HPM2].
rewrite (hacc_hex4 BS Hlen) in Hres.
destruct (PjGrammar.hex4 BS) as [h|].
+ exact Hres.
+ destruct Hres as (R10' & Hk). split; [exact R10'|].
intros x Hx. rewrite (Hk x Hx).
exact (HKO x ltac:(unfold kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *; lia) ltac:(unfold HEX4_STK in *; lia)).
Qed.
End a.
(* ENGINE s1b 459129c18903 (h-rw-pre-5-hex4m): srr_inv_laws, its fields sil_* and SRr_msteps_inv moved from YSRrMemnorm
   to YC80x, and srr_inv_laws_memnorm (the YAjMemnorm instance) to YSRrMemnormJ, with the same statements. The names
   below are re-pointed there; no statement and no proof step changed. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAjMemnorm YC80x YSRrMemnormJ.
Lemma srr_inv_laws_memnorm_from : forall (segs : list Segment) (m0 : word -> option byte),
YC80x.srr_inv_laws segs (fun m => YAkMemnorm.memnorm segs m0 -> YAkMemnorm.memnorm segs m).
Proof.
intros segs m0. pose proof (YSRrMemnormJ.srr_inv_laws_memnorm segs) as L. split.
- intros H m Hm H0. exact (@YC80x.sil_mrestrict segs _ L H m (Hm H0)).
- intros ms ms' Hms Hm H0. exact (@YC80x.sil_msteps segs _ L ms ms' Hms (Hm H0)).
- intros H full m' Hf Hm H0. exact (@YC80x.sil_munrestrict segs _ L H full m' (Hf H0) (Hm H0)).
Qed.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis TL : PALibCore (PI := PI_hex4) B.
Theorem hex4_x_holds_mnI : thex4_leafXmn SK rsegs B PST ARx (img_sigma AS_hex4).
Proof.
unfold thex4_leafXmn.
intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs p o BS HJ.
pose (Pm := fun m : word -> option byte => YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs m).
exact (hex4_mainP SK B PST ARx LAWS TL Pm
(YC80x.SRr_msteps_inv rsegs img_wx Pm (srr_inv_laws_memnorm_from rsegs memc))
STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs p o BS HJ (fun h => h)).
Qed.
End f.
