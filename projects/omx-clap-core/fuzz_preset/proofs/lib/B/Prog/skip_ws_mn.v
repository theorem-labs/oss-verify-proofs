(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: skip_ws of fuzz_preset's asan-ubsan image (B' = the #102 pin d663f82d7f48, unstripped twin c90d4fa54d43; skip_ws at 0x86948) KEEPS memnorm, proved from its run. One added property of lib/B/Prog/skip_ws_x.v's skip_ws_x_holds; no new walk.
   #102 BASE: branch cold/h-verbs-1-skipws-102 from origin/cold/h-verbs-1-leaves102 6240a87c3eb7 (int102 911184e64317 + the #102 leaf listings lib/B/Listing_leaves.v a5b1100728d4 / PAImg_leaves.v 6b3656ad1a67), then MERGED with int102 2dfa8b73a537, whose K0 kit is the kit of record f97c8b2f046b's (lib/A/PRH_FnReader.v c30f1da6a2d1, PRH_Base.v fdb45545469b; tskip_ws_specX's text is the same as at decff67d721f) and whose engine files are s1b 8a01e111a410's (YAjMemnorm 4372e77e66c5, YAkMemnorm 96c72061b4d4, YAkMemnormJ f6dbdc03064b, YC80x 14f84f225e8f, YSRrMemnormJ caf72f711a64, YCbqG c3b5d0111037). RELOCATED from the old-pin file (origin/cold/h-verbs-1-skip-union ad1c5072e3e7, blob bac31d88bfc3) by alreloc c4338d099cfb8025 (comment addresses only; the walk names the listing). Changes beyond relocation: (1) the q-off-image premise states image B's bounds, off_img_at IMG_LO_B IMG_TOP_B (as skip_ws_x.v); (2) skip_ws_holds is K1's text: tskip_ws_specX binds most own and prh_ledger carries them (prh_glob's cells g_most / g_own_ran_out), kept here like the five alloc.c cells, each bounded by the image top IMG_TOP_B, no numeral. fpre's later conjuncts (the relro view, the caller-frame bound, the ra ceiling, f97c's frm_zero (fp_csr fx)) are entry facts this leaf does not use: skip_ws calls nothing, so no fpre is rebuilt here.
   rule 24: proves function skip_ws (reuse search: `proof-index skip_ws hex4 put_utf8 literal`, 2026-10-28T21:1xZ, exit 0; CONFIRM R24ReaderLeaf 2026-10-28T21:15Z). Named hits are fuzz_preset / fuzz_state released PLAIN + UBSAN proofs, none on an asan build; this file relocates my own old-pin walk (the #102 code of skip_ws is the old code at new addresses).
   memnorm: the m-form keep (lib/A/PRH_Base.v fQmn mem Q := Q .. /\ (YAkMemnorm.memnorm segs mem -> YAkMemnorm.memnorm segs mem'), fpostWm := fpostW .. (fQmn mem Q)). YAjMemnorm.memnorm segs m := Lib.Mem.mem_inv segs m /\ MemNorm.task_mem segs m (lib/Reusable/YAjMemnorm.v:41), the same body as YAkMemnorm.memnorm (YAkMemnorm.v:41; YAkMemnormJ.memnorm_kit_j).
   WHAT: skip_ws_x_holds_mn (tskip_ws_leafXmn): tskip_ws_leafX with the premise YAjMemnorm.memnorm segs memc right after the journal premise and the conjunct YAjMemnorm.memnorm segs mem' right after the post's journal conjunct (the post has one arm). skip_ws_holds: the tskip_ws_specX (lib/A/PRH_FnReader.v at f97c8b2f046b, blob c30f1da6a2d1: fpostWm post, S' = S, no memnorm premise) at (PI := prh_img_B) (PA := PI_prog_B), from skip_ws_x_holds_mnI; the keep by YAkMemnormJ.memnorm_kit_j, S' = S by reflexivity.
   skip_ws_x_holds_mnI (tskip_ws_leafXmnI): tskip_ws_leafX with NO entry premise and ONE conjunct appended LAST to the post, the keep (YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem'). Proof: skwP_main at the invariant (fun m => YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs m), true of memc, whose srr_inv_laws come from YAkMemnorm's memnorm_mrestrict / memnorm_msteps / memnorm_munrestrict (srr_inv_laws_memnormK) through srr_inv_laws_imp.
   HOW: skw_loop / skw_main of skip_ws_x.v, re-run with an invariant Pinv of the full overlay, over the hypothesis msteps_keeps segs Pinv (the statement of YC80x.SRr_msteps_inv). Each runner segment is SRr_chain_tok_AJxP (YCbqG.SRr_chain_tok_AJx with SRr_msteps replaced by msteps_keeps: Pinv of the start memory gives Pinv of the merged end memory); a branch (YA0o.SRr_sym_branch) does not change the state; the return (YA0o.SRr_ret_at) leaves the memory as it is. The instance is msteps_keeps := YC80x.SRr_msteps_inv rsegs img_wx (YAjMemnorm.memnorm rsegs) (YSRrMemnormJ.srr_inv_laws_memnorm rsegs), whose msteps law is YAkMemnorm.memnorm_msteps. The proof uses no fact about where skip_ws stores: memnorm_msteps holds of every LPS run, because LPS makes a store only under store_ok.
   ORDER: the walk proofs come before `Require YAjMemnorm YAkMemnorm YAkMemnormJ YC80x YSRrMemnormJ` (YAjMemnorm loads lib/Lib/LiaTwx2.v, which redefines lia), so they run under the lia skip_ws_x.v was proved with; the bridge part comes after the lib/A Requires, which load LiaTwx2.v as skip_ws_bridge.v does. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import skip_ws_x.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
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
Section bP. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Section cP.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable Pinv : (word -> option byte) -> Prop.
Definition tskip_ws_leafXP (a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (q text len p : Z) (txt : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
YK0s.ret_ok (getr regs 1) -> getr regs 10 = w64 q ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SKIP_WS_TSTK -> spZ regs <= sp0 ->
4096 <= q -> q mod 8 = 0 -> amem_range q 16 -> off_img_at IMG_LO_B IMG_TOP_B q 16 ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q 16 ->
val_mem segs (mrestrict (w_H W) memc) q 8 p -> val_mem segs (mrestrict (w_H W) memc) (q + 8) 8 (text + len) ->
4096 <= text -> amem_range text len -> text <= p <= text + len ->
garr8 segs (mrestrict (w_H W) memc) text txt -> Z.of_nat (length txt) = len ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF text len ->
(q + 16 <= text \/ text + len <= q) ->
(spZ regs <= q \/ q + 16 <= spZ regs - SKIP_WS_TSTK) ->
(spZ regs <= text \/ text + len <= spZ regs - SKIP_WS_TSTK) ->
SRr segs W (cfg_at segs a regs memc mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
aregs_preserved regs regs' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - SKIP_WS_TSTK <= x < spZ regs) -> ~ (q <= x < q + 8) ->
aview segs (w_H W) mem' x = aview segs (w_H W) memc x) /\
val_mem segs (mrestrict (w_H W) mem') q 8 (text + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (p - text)) txt))))).
End cP.
End bP.
Ltac skwP_after_run HS HJ SHOK HPM :=
let ws := fresh "ws" in let ms' := fresh "ms" in let mat' := fresh "mat" in
let Hlen := fresh "Hlen" in let HF := fresh "HF" in let HFr := fresh "HFr" in let HG := fresh "HG" in
intros ws ms' mat' Hlen HS SHOK HJ HPM HF HFr HG;
cbn [sh_j sh_ss] in Hlen, HS, SHOK;
repeat (let w := fresh "w" in
destruct ws as [|w ws]; [discriminate Hlen | cbn [length] in Hlen; apply eq_add_S in Hlen || injection Hlen as Hlen]);
(destruct ws; [clear Hlen | discriminate Hlen]);
cbn [extK length Nat.add] in HS, SHOK;
cbn [ms_mem mkst] in HF, HFr, HG, HJ, HPM;
try match type of HS with context [restrict _ ?msn] =>
repeat match goal with
| old : machine_state |- _ => lazymatch old with msn => fail | _ => clear old end
end
end;
srr_norm_model.
Ltac skwP_run RUN HS HJ SHOK HPM :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_runN_tok sg SKW_TBL K Bx BAND_SPAN SH FUEL ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_runN_tok sg SKW_TBL K Bx BAND_SPAN SH FUEL ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUN W FUEL E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
skwP_after_run HS HJ SHOK HPM ]
end end
end.
Ltac skwP_run_to RUNTO HS HJ SHOK HPM stop :=
lazymatch type of HS with
| st_ok ?sg ?E ?ss (restrict (w_H ?W) ?ms) =>
lazymatch type of SHOK with
| sh_ok _ ?Bx ?SH _ _ =>
let K := eval vm_compute in (run_K 0 Bx SH ss) in
let r := eval vm_compute in (sym_run_toN_tok sg SKW_TBL K Bx BAND_SPAN SH FUEL stop ss) in
lazymatch r with
| (?st', ?rs) =>
let Hrun := fresh "Hrun" in
assert (Hrun : sym_run_toN_tok sg SKW_TBL K Bx BAND_SPAN SH FUEL stop ss = (st', rs)) by (vm_compute; reflexivity);
eapply (RUNTO W FUEL stop E K Bx BAND_SPAN SH ss st' rs ms _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HS SHOK
ltac:(vm_compute; reflexivity) Hrun I HJ HPM);
[ clear Hrun; cbn [sh_obls]; srr_obls
| clear Hrun
| clear Hrun HS HJ SHOK HPM; try match type of ms with machine_state => clear ms | _ => idtac end;
skwP_after_run HS HJ SHOK HPM ]
end end
end.
Section mP. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis TL : PALibCore (PI := PAImg_leaves.PI_skip_ws) B.
Variable Pinv : (word -> option byte) -> Prop.
Hypothesis MSI : msteps_keeps rsegs Pinv.
Let RUN := SRr_run_tok_AJxP SK rsegs B PST ARx LAWS PAImg_leaves.img_segs_low SKW_TBL PAImg_leaves.skip_ws_tbl_ok Pinv MSI.
Let RUNTO := SRr_run_to_tok_AJxP SK rsegs B PST ARx LAWS PAImg_leaves.img_segs_low SKW_TBL PAImg_leaves.skip_ws_tbl_ok Pinv MSI.
Lemma skwP_loop : forall (n : nat) W (regs : bvmap 5 word) memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len P (txt : list Z),
Z.of_nat n = text + len - P -> text <= P < text + len ->
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
Pinv memc ->
YK0s.ret_ok (getr regs 1) ->
getr regs 10 = w64 q -> getr regs 11 = w64 P -> getr regs 15 = w64 P -> getr regs 12 = w64 SKW_SB ->
getr regs 13 = w64 (SKW_SB + q / 8) -> getr regs 14 = w64 (text + len) -> getr regs 16 = w64 32 ->
getr regs 17 = w64 SKW_MASK -> getr regs 5 = w64 1 ->
spZ regs mod 16 = 0 -> 2 ^ 46 <= spZ regs -> spZ regs + 16 <= 2 ^ 47 ->
val_mem rsegs (mrestrict (w_H W) memc) (spZ regs + 8) 8 (bv_unsigned (getr regs 1)) ->
4096 <= q -> q mod 8 = 0 -> amem_range q 16 ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF q 16 ->
val_mem rsegs (mrestrict (w_H W) memc) q 8 P ->
4096 <= text -> amem_range text len ->
garr8 rsegs (mrestrict (w_H W) memc) text txt -> Z.of_nat (length txt) = len ->
range_addressable (aview rsegs (w_H W) memc) SHADOW_OFF text len ->
(q + 16 <= text \/ text + len <= q) ->
(spZ regs + 16 <= q \/ q + 16 <= spZ regs) ->
(spZ regs + 16 <= text \/ text + len <= spZ regs) ->
SRr rsegs W (mkCfg (mkst regs (Z_to_bv 64 SKW_LOOP) memc (seg_rom rsegs)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom rsegs)) md' /\
ajournal_x (SK := SK) rsegs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
Pinv mem' /\
(forall r, In r SKW_KEPT -> getr regs' r = getr regs r) /\
getr regs' 2 = w64 (spZ regs + 16) /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (q <= x < q + 8) -> aview rsegs (w_H W) mem' x = aview rsegs (w_H W) memc x) /\
val_mem rsegs (mrestrict (w_H W) mem') q 8 (text + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (P - text)) txt))))).
Proof.
induction n as [|n IH]; intros W regs memc mdc STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len P txt
Hn HP HJ HPM Hra H10 H11 H15 H12 H13 H14 H16 H17 H5 Hal Hsplo Hsphi Vra Hq4 Hq8 Hqam Hqw Hqra Vq Ht4 Htam GT Hlen Htra Hdqt Hdsq Hdst; [lia|].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
unfold YK0s.ret_ok in Hra.
destruct (skipn (Z.to_nat (P - text)) txt) as [|c rest] eqn:SKP.
{ exfalso. pose proof (length_skipn (Z.to_nat (P - text)) txt) as L. rewrite SKP in L. cbn in L. lia. }
pose proof (length_skipn (Z.to_nat (P - text)) txt) as LS. rewrite SKP in LS. cbn [length] in LS.
assert (Vc : val_mem rsegs (mrestrict (w_H W) memc) (P + 0) 1 c /\ 0 <= c < 256).
{ destruct (GT (Z.to_nat (P - text)) ltac:(lia)) as [V R].
rewrite (skw_nth_skipn txt _ c rest SKP) in V, R. replace (P + 0) with (text + Z.of_nat (Z.to_nat (P - text))) by lia. auto. }
destruct Vc as [Vc Hc8].
assert (Hend : text + len <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia).
assert (Hqend : q + 16 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam; lia).
remember (Ereg regs [Z_to_bv 64 c]) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E12 : ew E 12 = Z_to_bv 64 SKW_SB) by (subst E; rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E14 : ew E 14 = Z_to_bv 64 (text + len)) by (subst E; rewrite (ew_Ereg_nat regs _ 14 14%bv eq_refl); exact H14).
assert (E15 : ew E 15 = Z_to_bv 64 P) by (subst E; rewrite (ew_Ereg_nat regs _ 15 15%bv eq_refl); exact H15).
assert (E32 : ew E 32 = Z_to_bv 64 c) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U12 : bv_unsigned (ew E 12) = SKW_SB) by (rewrite E12; apply unsigned_lit_small; rewrite ?skw_sb_lit; lia).
assert (U14 : bv_unsigned (ew E 14) = text + len) by (rewrite E14; apply unsigned_lit_small; lia).
assert (U15 : bv_unsigned (ew E 15) = P) by (rewrite E15; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = c) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok rsegs E ss_skl (restrict (w_H W) (mkst regs (Z_to_bv 64 SKW_LOOP) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_skl. apply skw_st_ok_full.
- unfold skw_lregs.
apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [rewrite HE; apply regs_ok_Ereg| |]| |]| |]| |]| |];
try (intros X; discriminate X).
+ cbn [sv_denot]. rewrite U15, Z.add_0_r. exact H11.
+ rewrite (skw_denot_shx E 10 12 q SKW_SB E10 E12) by (rewrite ?skw_sb_lit; lia). exact H13.
+ exact H16.
+ exact H17.
+ exact H5.
- vm_compute. reflexivity.
- unfold skw_lregions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ (spZ regs) 8 8 (SOff 1 0) (bv_unsigned (getr regs 1)));
[cbn [sv_denot]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia | zside | exact Vra].
+ rewrite U10. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable rsegs). apply (proj2 (Hqw (q + o) ltac:(lia))). }
constructor; [|constructor].
apply (chunk_ok_val rsegs E _ q 0 8 (SOff 15 0) P); [cbn [sv_denot]; rewrite U15, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vq].
+ rewrite U15. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ P 0 1 (SOff 32 0) c); [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | cbn; lia | zside | exact Vc].
- apply pairwise_disjoint_of_extents. unfold skw_lregions. cbn [map]. unfold extent_of_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U10, U15.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok skw_lfacts]. unfold afact_ok, SKW_SPF, SKW_PTRQ, SKW_PTRT. cbn [af_lo af_hi af_al2].
rewrite Usp, U10, U12, U14, U15, U32. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?skw_sb_lit. repeat split; lia. }
assert (HBx : U E skw_BxL = SHADOW_OFF) by (unfold skw_BxL; rewrite (U_atom E 12 SKW_SB E12) by (rewrite ?skw_sb_lit; lia); reflexivity).
assert (SHOK : sh_ok rsegs skw_BxL skw_SHL E (mrestrict (w_H W) memc)).
{ unfold skw_SHL. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range rsegs (w_H W) memc E skw_BxL 15 text len P 0 1 Htra HBx); [rewrite (U_atom E 15 P E15) by lia; reflexivity | lia | lia |].
intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam. unfold SHADOW_OFF. lia.
- apply (shent_ok_of_range rsegs (w_H W) memc E skw_BxL 10 q 16 q 0 8 Hqra HBx); [rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam. unfold SHADOW_OFF. lia. }
skwP_run RUN HS HJ SHOK HPM.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K1. rename HG into G1. clear HF HFr.
lazymatch type of HS with st_ok _ ?Ex _ _ =>
assert (AG1 : env_agree 32 (Ereg regs [Z_to_bv 64 c]) Ex) by (rewrite <- HE; apply skw_agree2) end.
skw_branch HS SHOK.
- rewrite branch_ltu_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset Nat.eqb] in Hc.
rewrite U32, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc.
assert (WSF : PjGrammar.ws c = false)
by (unfold PjGrammar.ws; repeat match goal with |- context [Z.eqb ?a ?b] => destruct (Z.eqb_spec a b); [lia|] end; reflexivity).
skwP_run RUN HS HJ SHOK HPM.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K2. clear HF HFr HG.
eapply (SRr_ret_at rsegs SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low); exact HJ|].
split; [exact HPM|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K2, K1 by assumption; reflexivity|].
pose proof (skw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 0) P RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WSF. cbn [length]. replace (text + len - Z.of_nat (Datatypes.S (length rest))) with P by lia. exact VQ.
- rewrite branch_ltu_U, U_lit, U_SOff in Hc by lia. cbn [ew ewset Nat.eqb] in Hc.
rewrite U32, Z.add_0_r, zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc. rename Hc into Hc32.
skwP_run RUN HS HJ SHOK HPM.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K2. rename HG into G2. clear HF HFr.
skw_branch HS SHOK.
+ rewrite branch_eq_U, (skw_mask_U _ c) in Hc by (first [skw_ew E32 | lia]). rewrite U_lit in Hc by lia.
assert (WSF : PjGrammar.ws c = false) by (revert Hc; destruct (PjGrammar.ws c); cbn; intros Hc'; [discriminate Hc' | reflexivity]).
skwP_run RUN HS HJ SHOK HPM.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K3. clear HF HFr HG.
eapply (SRr_ret_at rsegs SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low); exact HJ|].
split; [exact HPM|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K3, K2, K1 by assumption; reflexivity|].
pose proof (skw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 0) P RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WSF. cbn [length]. replace (text + len - Z.of_nat (Datatypes.S (length rest))) with P by lia. exact VQ.
+ rewrite branch_eq_U, (skw_mask_U _ c) in Hc by (first [skw_ew E32 | lia]). rewrite U_lit in Hc by lia.
assert (WST : PjGrammar.ws c = true) by (revert Hc; destruct (PjGrammar.ws c); cbn; intros Hc'; [reflexivity | discriminate Hc']). clear Hc.
skwP_run RUN HS HJ SHOK HPM.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K3. rename HG into G3. clear HF HFr.
skw_branch HS SHOK.
* rewrite branch_ltu_U, !U_SOff in Hc. cbn [ew ewset Nat.eqb] in Hc.
rewrite U15, U14, !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_lt in Hc.
skwP_run_to RUNTO HS HJ SHOK HPM SKW_LOOP.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K4. rename HG into G4. clear HF HFr.
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ (q <= a < q + 8) ->
aview rsegs (w_H W) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a = aview rsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite K4, K3, K2, K1 by assumption; reflexivity).
assert (GALL : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a)
by (intros a Ha; apply (apresent_grows _ _ _ a G4), (apresent_grows _ _ _ a G3), (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (15%bv : bv 5) R15. prreg HS (12%bv : bv 5) R12. prreg HS (14%bv : bv 5) R14.
prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17. prreg HS (5%bv : bv 5) R5.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ _ 13%bv HS) as R13.
lazymatch type of R13 with _ = sv_denot ?Ex (sr_get ?l _) =>
let e := eval vm_compute in (sr_get l 13%bv) in change (sr_get l 13%bv) with e in R13;
rewrite (skw_denot_shx Ex 10 12 q SKW_SB ltac:(skw_ew E10) ltac:(skw_ew E12)) in R13 by (rewrite ?skw_sb_lit; lia) end.
cbn [ms_regs restrict] in R13.
assert (SP4 : spZ (ms_regs ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) = spZ regs) by (unfold spZ; rewrite R2, E2; reflexivity).
pose proof (skw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RS. cbn [ms_mem restrict] in RS.
pose proof (skw_field rsegs _ _ 2%nat (spZ regs) _ _ _ _ _ 8 8 (SOff 1 0) (bv_unsigned (getr regs 1)) RS
ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(left; reflexivity)
ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia) ltac:(zside)) as VS.
pose proof (skw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 1) (P + 1) RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
pmkst HS.
eapply SRr_mono.
{ eapply (IH W _ _ _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len (P + 1) txt);
[ lia | lia | exact HJ | exact HPM
| cbn [ms_regs]; rewrite R1, E1; exact Hra
| cbn [ms_regs]; rewrite R10, E10; reflexivity
| cbn [ms_regs]; rewrite R11, U15; reflexivity
| cbn [ms_regs]; rewrite R15, U15; reflexivity
| cbn [ms_regs]; rewrite R12, E12; reflexivity
| cbn [ms_regs]; rewrite R13; reflexivity
| cbn [ms_regs]; rewrite R14, E14; reflexivity
| cbn [ms_regs]; rewrite R16; reflexivity
| cbn [ms_regs]; rewrite R17; reflexivity
| cbn [ms_regs]; rewrite R5; reflexivity
| cbn [ms_regs]; rewrite SP4; exact Hal
| cbn [ms_regs]; rewrite SP4; exact Hsplo
| cbn [ms_regs]; rewrite SP4; exact Hsphi
| cbn [ms_regs ms_mem]; rewrite SP4, R1, E1; exact VS
| exact Hq4 | exact Hq8 | exact Hqam
| intros x Hx; split; [exact (proj1 (Hqw x Hx)) | apply GALL; exact (proj2 (Hqw x Hx))]
| apply (skw_ra_kept rsegs (w_H W) memc); [|exact Hqra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hqam; lia
| exact VQ | exact Ht4 | exact Htam
| apply (skw_garr8_kept rsegs (w_H W) memc); [|exact GT]; intros x Hx; apply KALL; lia
| exact Hlen
| apply (skw_ra_kept rsegs (w_H W) memc); [|exact Htra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hqam; lia
| exact Hdqt
| cbn [ms_regs]; rewrite SP4; exact Hdsq
| cbn [ms_regs]; rewrite SP4; exact Hdst ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HPM5 & HK5 & Hsp5 & Hkp5 & V5).
split; [reflexivity|]. exists regs5, mem5, md5.
split; [cbn [ms_regs]; rewrite R1, E1; reflexivity|].
split; [exact HJ5|].
split; [exact HPM5|].
split; [intros r Hr; rewrite (HK5 r Hr); exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Hsp5; cbn [ms_regs]; rewrite SP4; reflexivity|].
split; [intros x Hx Hnq; rewrite (Hkp5 x Hx Hnq); exact (KALL x Hx Hnq)|].
cbn [PjGrammar.skip]. rewrite WST.
replace (Z.to_nat (P + 1 - text)) with (Datatypes.S (Z.to_nat (P - text))) in V5 by lia.
rewrite (skw_skipn_S txt _ c rest SKP) in V5. exact V5.
* rewrite branch_ltu_U, !U_SOff in Hc. cbn [ew ewset Nat.eqb] in Hc.
rewrite U15, U14, !zcanon_id in Hc by (unfold M64; lia). apply Z.ltb_ge in Hc.
assert (RN : rest = []) by (apply length_zero_iff_nil; lia).
skwP_run RUN HS HJ SHOK HPM.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => q <= a < q + 8) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?U10 in h).
rename KEPT into K4. clear HF HFr HG.
eapply (SRr_ret_at rsegs SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low); exact HJ|].
split; [exact HPM|].
split; [intros r Hr; exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AG1 ltac:(vm_compute; reflexivity) r Hr)|].
split; [rewrite Rsp, Usp; reflexivity|].
split; [intros x Hx Hnq; rewrite K4, K3, K2, K1 by assumption; reflexivity|].
pose proof (skw_region_nth rsegs _ _ _ 1 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 15 1) (P + 1) RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U15; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. cbn [PjGrammar.skip]. rewrite WST, RN. cbn [PjGrammar.skip length].
replace (text + len - Z.of_nat 0) with (P + 1) by lia. exact VQ.
Qed.
Theorem skwP_main : tskip_ws_leafXP SK rsegs B PST ARx Pinv SKW_PC.
Proof.
unfold tskip_ws_leafXP. intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q text len p txt
HJ HPM Hra H10 Hal Hstk1 Hstk2 Hq4 Hq8 Hqam Hqoff Hqw Hqra Vp Ve Ht4 Htam Hpr GT Hlen Htra Hdqt Hdsq Hdst.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hastk & _ & _).
pose proof Hastk as (Hal0 & HSTK0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop1 & Htop2).
unfold SKIP_WS_TSTK in Hstk1, Hdsq, Hdst.
assert (Hend : text + len <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam; lia).
assert (Hqend : q + 16 <= 2 ^ 47 - 1) by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam; lia).
pose proof Hqoff as Hqoff'. unfold off_img_at in Hqoff'. rewrite IMG_LO_B_val, IMG_TOP_B_val in Hqoff'.
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR) as (Kcell & _ & Kgot & _).
rewrite (palc_got_shadow B TL), (palc_cell B TL), skw_got_val, skw_cell_val in Kgot.
rewrite (palc_cell B TL), skw_cell_val in Kcell.
remember (Ereg regs (skw_extra p (text + len))) as E eqn:HE.
assert (E1 : ew E 1 = getr regs 1) by (subst E; exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (subst E; exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 q) by (subst E; rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SKW_SB) by (subst E; exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 p) by (subst E; exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (text + len)) by (subst E; exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (U10 : bv_unsigned (ew E 10) = q) by (rewrite E10; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = SKW_SB) by (rewrite E32; apply unsigned_lit_small; rewrite ?skw_sb_lit; lia).
assert (U33 : bv_unsigned (ew E 33) = p) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = text + len) by (rewrite E34; apply unsigned_lit_small; lia).
assert (AGE : env_agree 32 (Ereg regs (skw_extra p (text + len))) E) by (rewrite <- HE; apply env_agree_refl).
assert (HS : st_ok rsegs E ss_skw (restrict (w_H W) (mkst regs (Z_to_bv 64 SKW_PC) memc (seg_rom rsegs)))).
{ rewrite restrict_mkst_fx. unfold ss_skw. apply skw_st_ok_full.
- rewrite HE. apply regs_ok_Ereg.
- vm_compute. reflexivity.
- unfold skw_regions, stack_region. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable rsegs). apply Hpres. lia.
+ split; [rewrite ?skw_got_lit; lia|]. split; [rewrite ?skw_got_lit; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 SKW_GOT 8 (SLit SKW_CELL) SKW_CELL); [reflexivity | rewrite ?skw_cell_lit; cbn; lia | zside |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kgot).
+ split; [rewrite ?skw_cell_lit; lia|]. split; [rewrite ?skw_cell_lit; lia|]. split; [intros o Ho; lia|]. constructor; [|constructor].
apply (chunk_ok_val rsegs E _ 0 SKW_CELL 8 (SOff 32 0) SHADOW_OFF); [cbn [sv_denot]; rewrite U32, Z.add_0_r; reflexivity | unfold SHADOW_OFF; cbn; lia | zside |].
rewrite Z.add_0_l. exact (val_mem_of_rdword rsegs _ _ _ _ Kcell).
+ rewrite U10. split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (apresent_writable rsegs). apply (proj2 (Hqw (q + o) ltac:(lia))). }
constructor; [|constructor; [|constructor]].
* apply (chunk_ok_val rsegs E _ q 0 8 (SOff 33 0) p); [cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity | cbn; lia | zside | rewrite Z.add_0_r; exact Vp].
* apply (chunk_ok_val rsegs E _ q 8 8 (SOff 34 0) (text + len)); [cbn [sv_denot]; rewrite U34, Z.add_0_r; reflexivity | cbn; lia | zside | exact Ve].
- apply pairwise_disjoint_of_extents. unfold skw_regions, stack_region. cbn [map]. unfold extent_of_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite Usp, U10.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. rewrite ?skw_got_lit, ?skw_cell_lit. repeat split; lia.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok skw_facts]. unfold afact_ok, SKW_SPF, SKW_PTRQ, SKW_PTRT. cbn [af_lo af_hi af_al2].
rewrite Usp, U10, U32, U33, U34. change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
rewrite ?skw_sb_lit. repeat split; lia. }
assert (HBx : U E skw_BxE = SHADOW_OFF) by (unfold skw_BxE; rewrite (U_atom E 32 SKW_SB E32) by (rewrite ?skw_sb_lit; lia); reflexivity).
assert (SHOK : sh_ok rsegs skw_BxE skw_SHE E (mrestrict (w_H W) memc)).
{ unfold skw_SHE. constructor; [|constructor].
apply (shent_ok_of_range rsegs (w_H W) memc E skw_BxE 10 q 16 q 0 16 Hqra HBx); [rewrite (U_atom E 10 q E10) by lia; reflexivity | lia | lia |].
intros x Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hqam. unfold SHADOW_OFF. lia. }
unfold cfg_at. change (w64 SKW_PC) with (Z_to_bv 64 SKW_PC).
skwP_run RUN HS HJ SHOK HPM.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
rename KEPT into K1. rename HG into G1. clear HF HFr.
skw_branch HS SHOK.
- rewrite branch_geu_U, !U_SOff in Hc. rewrite U33, U34, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
assert (Hpe : p = text + len) by (destruct (Z.ltb_spec p (text + len)); [discriminate Hc | lia]). clear Hc.
skwP_run RUN HS HJ SHOK HPM.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
rename KEPT into K2. clear HF HFr HG.
eapply (SRr_ret_at rsegs SKW_TBL PAImg_leaves.skip_ws_tbl_ok PAImg_leaves.img_wx W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. cbv beta. split; [reflexivity|].
lazymatch goal with |- exists _ _ _, {| cfg_ms := mkst ?rg _ ?m _; cfg_model := ?d |} = _ /\ _ => exists rg, m, d end.
prreg HS (1%bv : bv 5) Rra.
unfold YK0s.ret_ok in Hra.
split; [rewrite Rra, E1, Hra; reflexivity|].
split; [apply (ajournal_x_materialize (SK := SK) rsegs B PST ARx LAWS PAImg_leaves.img_segs_low); exact HJ|].
split; [exact HPM|].
split; [exact (aregs_preserved_of_st_ok rsegs _ _ _ _ regs _ HS AGE ltac:(vm_compute; reflexivity))|].
split.
{ intros x Hx H1 H2. unfold SKIP_WS_TSTK in H1.
assert (NZ : ~ ((spZ regs - 16 <= x < spZ regs) \/ (q <= x < q + 8))) by tauto.
rewrite K2, K1 by assumption. reflexivity. }
pose proof (skw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 33 0) p RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ. rewrite skipn_all2 by lia. cbn [PjGrammar.skip length]. replace (text + len - Z.of_nat 0) with p by lia. exact VQ.
- rewrite branch_geu_U, !U_SOff in Hc. rewrite U33, U34, !Z.add_0_r, !zcanon_id in Hc by (unfold M64; lia).
assert (Hpe : p < text + len) by (destruct (Z.ltb_spec p (text + len)); [lia | discriminate Hc]). clear Hc.
skwP_run_to RUNTO HS HJ SHOK HPM SKW_LOOP.
{ skw_awr Hqw Usp U10. }
skw_kept_of HFr (fun a => (spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ltac:(fun h => cbn [ew ewset Nat.eqb] in h; rewrite ?Usp, ?U10 in h).
rename KEPT into K2. rename HG into G2. clear HF HFr.
assert (KALL : forall a, 0 <= a < 2 ^ 64 -> ~ ((spZ regs - 16 <= a < spZ regs) \/ (q <= a < q + 8)) ->
aview rsegs (w_H W) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a = aview rsegs (w_H W) memc a)
by (intros a Ha Hna; rewrite K2, K1 by assumption; reflexivity).
assert (GALL : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) a)
by (intros a Ha; apply (apresent_grows _ _ _ a G2), (apresent_grows _ _ _ a G1), Ha).
prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (10%bv : bv 5) R10. prreg HS (11%bv : bv 5) R11.
prreg HS (15%bv : bv 5) R15. prreg HS (12%bv : bv 5) R12. prreg HS (14%bv : bv 5) R14.
prreg HS (16%bv : bv 5) R16. prreg HS (17%bv : bv 5) R17. prreg HS (5%bv : bv 5) R5.
pose proof (st_ok_restrict_reg rsegs (w_H W) _ _ _ 13%bv HS) as R13.
lazymatch type of R13 with _ = sv_denot ?Ex (sr_get ?l _) =>
let e := eval vm_compute in (sr_get l 13%bv) in change (sr_get l 13%bv) with e in R13;
rewrite (skw_denot_shx Ex 10 32 q SKW_SB ltac:(skw_ew E10) ltac:(skw_ew E32)) in R13 by (rewrite ?skw_sb_lit; lia) end.
cbn [ms_regs restrict] in R13.
assert (SP1 : spZ (ms_regs ltac:(lazymatch type of HS with st_ok _ _ _ (restrict _ ?mx) => exact mx end)) = spZ regs - 16)
by (unfold spZ at 1; rewrite R2, Usp; apply unsigned_lit_small; lia).
pose proof (skw_region_nth rsegs _ _ _ 0 _ HS eq_refl) as RS. cbn [ms_mem restrict] in RS.
pose proof (skw_field rsegs _ _ 2%nat (spZ regs) _ _ _ _ _ (-8) 8 (SOff 1 0) (bv_unsigned (getr regs 1)) RS
ltac:(cbn [ew ewset Nat.eqb]; exact Usp) ltac:(left; reflexivity)
ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite E1, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
ltac:(pose proof (bv_unsigned_in_range 64 (getr regs 1)) as R; unfold bv_modulus in R; cbn in R |- *; lia) ltac:(zside)) as VS.
pose proof (skw_region_nth rsegs _ _ _ 3 _ HS eq_refl) as RQ. cbn [ms_mem restrict] in RQ.
pose proof (skw_field rsegs _ _ 10%nat q _ _ _ _ _ 0 8 (SOff 33 0) p RQ ltac:(cbn [ew ewset Nat.eqb]; exact U10)
ltac:(left; reflexivity) ltac:(cbn [sv_denot ew ewset Nat.eqb]; rewrite U33, Z.add_0_r; reflexivity) ltac:(cbn; lia) ltac:(zside)) as VQ.
rewrite Z.add_0_r in VQ.
pmkst HS.
eapply SRr_mono.
{ eapply (skwP_loop (Z.to_nat (text + len - p)) W _ _ _ STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc k q text len p txt);
[ lia | lia | exact HJ | exact HPM
| cbn [ms_regs]; rewrite R1, E1; exact Hra
| cbn [ms_regs]; rewrite R10, E10; reflexivity
| cbn [ms_regs]; rewrite R11, E33; reflexivity
| cbn [ms_regs]; rewrite R15, E33; reflexivity
| cbn [ms_regs]; rewrite R12, E32; reflexivity
| cbn [ms_regs]; rewrite R13; reflexivity
| cbn [ms_regs]; rewrite R14, E34; reflexivity
| cbn [ms_regs]; rewrite R16; reflexivity
| cbn [ms_regs]; rewrite R17; reflexivity
| cbn [ms_regs]; rewrite R5; reflexivity
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs ms_mem]; rewrite SP1, R1, E1; replace (spZ regs - 16 + 8) with (spZ regs + -8) by lia; exact VS
| exact Hq4 | exact Hq8 | exact Hqam
| intros x Hx; split; [exact (proj1 (Hqw x Hx)) | apply GALL; exact (proj2 (Hqw x Hx))]
| apply (skw_ra_kept rsegs (w_H W) memc); [|exact Hqra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hqam; lia
| exact VQ | exact Ht4 | exact Htam
| apply (skw_garr8_kept rsegs (w_H W) memc); [|exact GT]; intros x Hx; apply KALL; lia
| exact Hlen
| apply (skw_ra_kept rsegs (w_H W) memc); [|exact Htra]; intros x Hx; apply KALL;
unfold shadow_of_addr, SHADOW_OFF; unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Htam, Hqam; lia
| exact Hdqt
| cbn [ms_regs]; rewrite SP1; lia
| cbn [ms_regs]; rewrite SP1; lia ]. }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HPM5 & HK5 & Hsp5 & Hkp5 & V5).
split; [reflexivity|]. exists regs5, mem5, md5.
split; [cbn [ms_regs]; rewrite R1, E1; reflexivity|].
split; [exact HJ5|].
split; [exact HPM5|].
split.
{ apply skw_aregs.
- intros r Hr. rewrite (HK5 r Hr). exact (regs_kept_of_st_ok rsegs _ _ _ regs _ SKW_KEPT HS AGE ltac:(vm_compute; reflexivity) r Hr).
- rewrite Hsp5. cbn [ms_regs]. rewrite SP1. replace (spZ regs - 16 + 16) with (spZ regs) by lia. unfold w64, spZ. apply Z_to_bv_bv_unsigned. }
split.
{ intros x Hx H1 H2. unfold SKIP_WS_TSTK in H1. rewrite (Hkp5 x Hx H2). apply KALL; [exact Hx | tauto]. }
exact V5.
Qed.
End mP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAjMemnorm YAkMemnorm YAkMemnormJ YC80x YSRrMemnormJ.
Section bM. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Section cM.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Definition tskip_ws_leafXmn (a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (q text len p : Z) (txt : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
YAjMemnorm.memnorm segs memc ->
YK0s.ret_ok (getr regs 1) -> getr regs 10 = w64 q ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SKIP_WS_TSTK -> spZ regs <= sp0 ->
4096 <= q -> q mod 8 = 0 -> amem_range q 16 -> off_img_at IMG_LO_B IMG_TOP_B q 16 ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q 16 ->
val_mem segs (mrestrict (w_H W) memc) q 8 p -> val_mem segs (mrestrict (w_H W) memc) (q + 8) 8 (text + len) ->
4096 <= text -> amem_range text len -> text <= p <= text + len ->
garr8 segs (mrestrict (w_H W) memc) text txt -> Z.of_nat (length txt) = len ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF text len ->
(q + 16 <= text \/ text + len <= q) ->
(spZ regs <= q \/ q + 16 <= spZ regs - SKIP_WS_TSTK) ->
(spZ regs <= text \/ text + len <= spZ regs - SKIP_WS_TSTK) ->
SRr segs W (cfg_at segs a regs memc mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
YAjMemnorm.memnorm segs mem' /\
aregs_preserved regs regs' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - SKIP_WS_TSTK <= x < spZ regs) -> ~ (q <= x < q + 8) ->
aview segs (w_H W) mem' x = aview segs (w_H W) memc x) /\
val_mem segs (mrestrict (w_H W) mem') q 8 (text + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (p - text)) txt))))).
End cM.
End bM.
Theorem skip_ws_x_holds_mn : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head) (B : asyms) (PST : list (Z * Z))
(ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop) {HL : Z},
AR_laws_x rsegs B ARx HL -> PALibCore (PI := PAImg_leaves.PI_skip_ws) B ->
tskip_ws_leafXmn SK rsegs B PST ARx (PAImg_leaves.img_sigma AS_skip_ws).
Proof.
intros fx rc SK B PST ARx HL LAWS TL.
exact (skwP_main SK B PST ARx LAWS TL (YAjMemnorm.memnorm rsegs)
(YC80x.SRr_msteps_inv rsegs PAImg_leaves.img_wx (YAjMemnorm.memnorm rsegs) (YSRrMemnormJ.srr_inv_laws_memnorm rsegs))).
Qed.
Section bI. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Section cI.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Definition tskip_ws_leafXmnI (a : Z) : Prop :=
forall STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k (regs : bvmap 5 word) (q text len p : Z) (txt : list Z),
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> getr regs 10 = w64 q ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - SKIP_WS_TSTK -> spZ regs <= sp0 ->
4096 <= q -> q mod 8 = 0 -> amem_range q 16 -> off_img_at IMG_LO_B IMG_TOP_B q 16 ->
(forall x, q <= x < q + 8 -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own x /\ apresent (w_H W) memc x) ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF q 16 ->
val_mem segs (mrestrict (w_H W) memc) q 8 p -> val_mem segs (mrestrict (w_H W) memc) (q + 8) 8 (text + len) ->
4096 <= text -> amem_range text len -> text <= p <= text + len ->
garr8 segs (mrestrict (w_H W) memc) text txt -> Z.of_nat (length txt) = len ->
range_addressable (aview segs (w_H W) memc) SHADOW_OFF text len ->
(q + 16 <= text \/ text + len <= q) ->
(spZ regs <= q \/ q + 16 <= spZ regs - SKIP_WS_TSTK) ->
(spZ regs <= text \/ text + len <= spZ regs - SKIP_WS_TSTK) ->
SRr segs W (cfg_at segs a regs memc mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom segs)) md' /\
ajournal_x (SK := SK) segs B PST ARx STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W mem' md' k /\
aregs_preserved regs regs' /\
(forall x, 0 <= x < 2 ^ 64 -> ~ (spZ regs - SKIP_WS_TSTK <= x < spZ regs) -> ~ (q <= x < q + 8) ->
aview segs (w_H W) mem' x = aview segs (w_H W) memc x) /\
val_mem segs (mrestrict (w_H W) mem') q 8 (text + len - Z.of_nat (length (PjGrammar.skip (skipn (Z.to_nat (p - text)) txt)))) /\
(YAkMemnorm.memnorm segs memc -> YAkMemnorm.memnorm segs mem')).
End cI.
End bI.
Lemma srr_inv_laws_imp : forall segs (P : (word -> option byte) -> Prop) (A : Prop),
YC80x.srr_inv_laws segs P -> YC80x.srr_inv_laws segs (fun m => A -> P m).
Proof.
intros segs P A [Hr Hs Hu]. split.
- intros H m Hm HA. exact (Hr H m (Hm HA)).
- intros ms ms' Hms Hm HA. exact (Hs ms ms' Hms (Hm HA)).
- intros H full m' Hf Hm HA. exact (Hu H full m' (Hf HA) (Hm HA)).
Qed.
Lemma srr_inv_laws_memnormK : forall segs, YC80x.srr_inv_laws segs (YAkMemnorm.memnorm segs).
Proof.
intros segs. split.
- exact (YAkMemnorm.memnorm_mrestrict segs).
- exact (YAkMemnorm.memnorm_msteps segs).
- exact (YAkMemnorm.memnorm_munrestrict segs).
Qed.
Theorem skip_ws_x_holds_mnI : forall {fx : YK11.FPState} {rc : YM05.RunCeil} (SK : YI16.sink_head) (B : asyms) (PST : list (Z * Z))
(ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop) {HL : Z},
AR_laws_x rsegs B ARx HL -> PALibCore (PI := PAImg_leaves.PI_skip_ws) B ->
tskip_ws_leafXmnI SK rsegs B PST ARx (PAImg_leaves.img_sigma AS_skip_ws).
Proof.
intros fx rc SK B PST ARx HL LAWS TL.
unfold tskip_ws_leafXmnI. intros STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q text len p txt
HJ Hra H10 Hal Hstk1 Hstk2 Hq4 Hq8 Hqam Hqoff Hqw Hqra Vp Ve Ht4 Htam Hpr GT Hlen Htra Hdqt Hdsq Hdst.
eapply SRr_mono.
{ exact (skwP_main SK B PST ARx LAWS TL
    (fun m : word -> option byte => YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs m)
    (YC80x.SRr_msteps_inv rsegs PAImg_leaves.img_wx
      (fun m : word -> option byte => YAkMemnorm.memnorm rsegs memc -> YAkMemnorm.memnorm rsegs m)
      (srr_inv_laws_imp rsegs (YAkMemnorm.memnorm rsegs) (YAkMemnorm.memnorm rsegs memc) (srr_inv_laws_memnormK rsegs)))
    STK sp0 FP ly S Hp W0 mem0 md0 own lyc Sc Hpc W memc mdc k regs q text len p txt
    HJ (fun h => h) Hra H10 Hal Hstk1 Hstk2 Hq4 Hq8 Hqam Hqoff Hqw Hqra Vp Ve Ht4 Htam Hpr GT Hlen Htra Hdqt Hdsq Hdst). }
cbv beta. intros W' c' _ (-> & regs' & mem' & md' & Hc & HJ' & HK & Hpr' & Hkp & V).
split; [reflexivity|]. exists regs', mem', md'.
split; [exact Hc|]. split; [exact HJ'|]. split; [exact Hpr'|]. split; [exact Hkp|]. split; [exact V | exact HK].
Qed.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07 YI00 YI16 YK06 YK04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YCbqG YGcfNames.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YImgTop YC1fP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_Reader PRH_FnReader.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require PAImg_leaves.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import skip_ws_x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import skip_ws_bridge.
Import ListNotations.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Close Scope bv_scope.
Open Scope Z_scope.
Section bmn. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {RL : PrhRoomLive}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world rsegs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x rsegs B ARx HL.
Hypothesis TLP : PALibCore (PI := PI_prog_B) B.

Theorem skip_ws_holds : tskip_ws_specX (PI := prh_img_B) (PA := PI_prog_B) B ARx SK.
Proof.
unfold tskip_ws_specX.
intros ly S Hp W regs mem md ch e q text len p d tb Lam peak cnt fail ran most own.
intros (Hafn & Hro) H10 HQ HWIN Hsq Hqe Hqra HSRC HHOME HLED.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj2 alloc_ceiling_val) as Cmod.
destruct HWIN as (He0 & He16 & Hetop & Hepres).
pose proof Hafn as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof HQ as (Vp & Ve & Vd & Hrw & Hq8 & Ht0 & Htend & Hprange & Hlen & GT & Hdisj & Hd32).
pose proof HSRC as (HBY & Ht4 & Htceil & Htam & Htra & Thull).
assert (HSTK : @STK_skip_ws prh_img_B = 16) by reflexivity.
assert (Hceil16 : alloc_ceiling + 16 <= spZ regs) by (rewrite HSTK in Hslo; lia).
(* the text end below alloc_ceiling: the batch kit's src_rd (SRC-CEIL) gives p + len <= alloc_ceiling; kit f97c's gives
   + 8 more; only the bound without the + 8 is used below *)
assert (Htlen : text + len <= alloc_ceiling) by (rewrite <- Hlen; lia).
assert (TL : PALibCore (PI := PAImg_leaves.PI_skip_ws) B).
{ constructor.
  - rewrite (palc_got_shadow B TLP). vm_compute. reflexivity.
  - rewrite (palc_cell B TLP). vm_compute. reflexivity.
  - left. vm_compute. discriminate.
  - exact (palc_env B TLP).
  - rewrite <- (palc_free B TLP). vm_compute. reflexivity.
  - rewrite <- (palc_malloc B TLP). vm_compute. reflexivity.
  - pose proof (palc_rt_below B TLP) as (R1 & R2).
    assert (HBB : @pa_val _ _ PI_prog_B A_TEXT <= @pa_val _ _ PAImg_leaves.PI_skip_ws A_TEXT)
      by (vm_compute; discriminate).
    split; lia. }
pose proof (skip_ws_x_holds_mnI SK B (@prh_pst prh_img_B) ARx LAWS TL) as LEAF.
unfold tskip_ws_leafXmnI in LEAF.
assert (HJ : ajournal_x (SK := SK) rsegs B (@prh_pst prh_img_B) ARx (@STK_skip_ws prh_img_B + e) (spZ regs + e)
  [(q, q + 8)] ly S Hp W mem md [] ly S Hp W mem md 0)
  by exact (skwb_init SK B ARx (@prh_pst prh_img_B) (@STK_skip_ws prh_img_B) e [(q, q + 8)] ly S Hp W regs mem md ch
             Hafn He0 He16 Hetop Hepres).
assert (A5 : spZ regs + e - (@STK_skip_ws prh_img_B + e) <= spZ regs - SKIP_WS_TSTK)
  by (unfold SKIP_WS_TSTK; rewrite HSTK; lia).
assert (A6 : spZ regs <= spZ regs + e) by lia.
assert (A7 : 4096 <= q) by lia.
assert (A9 : amem_range q 16) by (unfold amem_range; right; lia).
assert (A10 : off_img_at IMG_LO_B IMG_TOP_B q 16) by (unfold off_img_at; right; rewrite IMG_TOP_B_val; lia).
assert (A11 : forall x, q <= x < q + 8 ->
  awr_byte (@STK_skip_ws prh_img_B + e) (spZ regs + e) [(q, q + 8)] (ablocks B ly S) (ablocks B ly S) ly [] x
  /\ apresent (w_H W) mem x).
{ intros x Hx. split; [left; rewrite HSTK; lia | apply Hepres; lia]. }
assert (A12 : range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF q 16) by (intros x Hx; apply Hqra; lia).
assert (A16 : amem_range text len) by (rewrite <- Hlen; exact Htam).
assert (A20 : range_addressable (aview rsegs (w_H W) mem) SHADOW_OFF text len) by (rewrite <- Hlen; exact Htra).
assert (A21 : q + 16 <= text \/ text + len <= q) by (destruct Hdisj as [Hx|Hx]; [left | right]; lia).
assert (A22 : spZ regs <= q \/ q + 16 <= spZ regs - SKIP_WS_TSTK) by (left; lia).
assert (A23 : spZ regs <= text \/ text + len <= spZ regs - SKIP_WS_TSTK)
  by (right; unfold SKIP_WS_TSTK; lia).
eapply SRr_mono.
{ exact (LEAF (@STK_skip_ws prh_img_B + e) (spZ regs + e) [(q, q + 8)] ly S Hp W mem md [] ly S Hp W mem md 0
    regs q text len p tb HJ Hra H10 Hal A5 A6 A7 Hq8 A9 A10 A11 A12 Vp Ve Ht4 A16 Hprange HBY Hlen A20 A21 A22 A23). }
cbv beta. intros W5 c5 _ (-> & regs5 & mem5 & md5 & Hc5 & HJ5 & HPR5 & KEEP & V5 & HK5).
pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES5 & _).
assert (KLOW : forall a, 0 <= a < alloc_ceiling -> aview rsegs (w_H W) mem5 a = aview rsegs (w_H W) mem a).
{ intros a Ha. apply KEEP.
  - lia.
  - unfold SKIP_WS_TSTK. lia.
  - lia. }
assert (KHI : forall a, q + 8 <= a < q + 24 -> aview rsegs (w_H W) mem5 a = aview rsegs (w_H W) mem a).
{ intros a Ha. apply KEEP.
  - lia.
  - unfold SKIP_WS_TSTK. lia.
  - lia. }
assert (KVAL : forall a (n : nat) v, 0 <= a -> a + Z.of_nat n <= alloc_ceiling ->
  val_mem rsegs (mrestrict (w_H W) mem) a n v -> val_mem rsegs (mrestrict (w_H W) mem5) a n v).
{ intros a n v Ha Han Hv. eapply (skw_val_kept rsegs); [intros x Hx; apply KLOW; lia | exact Hv]. }
exists ly, S, Hp, regs5, mem5, md5, 0.
split; [exact Hc5|].
split; [exact HJ5|].
split.
{ intros a Ha Hfp. apply KEEP.
  - lia.
  - unfold SKIP_WS_TSTK. lia.
  - intros Hin. apply Hfp. exists (q, q + 8). split; [left; reflexivity | cbn; lia]. }
split; [exact HPR5|].
split; [| intros HMN; apply YAkMemnormJ.memnorm_kit_j; exact (HK5 HMN)].
split; [exact (fun h => h)|].
split; [reflexivity|].
split; [reflexivity|].
split; [reflexivity|].
split.
{ destruct HLED as (HG & HND & HFA & HPM).
  split; [| split; [exact HND | split; [| exact HPM]]].
  { (* prh_glob's seven cells (K1 decff67d721f: alloc.c's five, then #102's g_most / g_own_ran_out as prh_most /
       prh_own), each below the B' image top and so below alloc_ceiling, are kept by KLOW *)
    destruct HG as (G1 & G2 & G3 & G4 & G5 & (G6 & G6r) & (G7 & G7r) & Grest).
    assert (GB : 0 <= @pi_g_live prh_img_B /\ @pi_g_live prh_img_B + Z.of_nat (@pi_gz_live prh_img_B) <= IMG_TOP_B
               /\ 0 <= @pi_g_peak prh_img_B /\ @pi_g_peak prh_img_B + Z.of_nat (@pi_gz_peak prh_img_B) <= IMG_TOP_B
               /\ 0 <= @pi_g_count prh_img_B /\ @pi_g_count prh_img_B + Z.of_nat (@pi_gz_count prh_img_B) <= IMG_TOP_B
               /\ 0 <= @pi_g_fail prh_img_B /\ @pi_g_fail prh_img_B + Z.of_nat (@pi_gz_fail prh_img_B) <= IMG_TOP_B
               /\ 0 <= @pi_g_ran_out prh_img_B
               /\ @pi_g_ran_out prh_img_B + Z.of_nat (@pi_gz_ran_out prh_img_B) <= IMG_TOP_B
               /\ 0 <= @pi_g_most prh_img_B /\ @pi_g_most prh_img_B + Z.of_nat (@pi_gz_most prh_img_B) <= IMG_TOP_B
               /\ 0 <= @pi_g_own_ran_out prh_img_B
               /\ @pi_g_own_ran_out prh_img_B + Z.of_nat (@pi_gz_own_ran_out prh_img_B) <= IMG_TOP_B)
      by (vm_compute; repeat split; discriminate).
    pose proof IMG_TOP_B_val as HTB.
    destruct GB as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14).
    split; [eapply KVAL; [exact B1 | lia | exact G1]|].
    split; [eapply KVAL; [exact B3 | lia | exact G2]|].
    split; [eapply KVAL; [exact B5 | lia | exact G3]|].
    split; [eapply KVAL; [exact B7 | lia | exact G4]|].
    split; [eapply KVAL; [exact B9 | lia | exact G5]|].
    split; [split; [eapply KVAL; [exact B11 | lia | exact G6] | exact G6r]|].
    split; [split; [eapply KVAL; [exact B13 | lia | exact G7] | exact G7r] | exact Grest]. }
  { apply Forall_forall. intros ak Hak.
    pose proof (proj1 (Forall_forall _ _) HFA ak Hak) as (Hk0 & Hin & Hhp & Hal16 & Hv).
    split; [exact Hk0|]. split; [exact Hin|]. split; [exact Hhp|]. split; [exact Hal16|].
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (Hmod & Hlo & Hhi & _).
    pose proof cf_head_nonneg as CH.
    assert (Hr1 : 1 <= req_size (snd ak + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (snd ak + cf_head) 0); lia).
    eapply KVAL; [lia | | exact Hv]. lia. } }
split; [exact V5|].
split; [eapply (skw_val_kept rsegs); [intros x Hx; apply KHI; cbn in Hx; lia | exact Ve]|].
split; [eapply (skw_val_kept rsegs); [intros x Hx; apply KHI; cbn in Hx; lia | exact Vd]|].
split.
{ intros x Hx. apply (apresent_writable rsegs). apply HPRES5. rewrite HSTK. lia. }
split; [exact Hq8|].
split; [exact Ht0|].
split; [exact Htend|].
split.
{ pose proof (skwb_skip_len (rest_atR tb text p)) as HSL.
  assert (HRL : (length (rest_atR tb text p) <= length tb)%nat)
    by (unfold rest_atR; rewrite length_skipn; lia).
  lia. }
split; [exact Hlen|].
split; [eapply (skw_garr8_kept rsegs); [intros x Hx; apply KLOW; rewrite Hlen in Hx; lia | exact HBY]|].
split; [exact Hdisj | exact Hd32].
Qed.
End bmn.
