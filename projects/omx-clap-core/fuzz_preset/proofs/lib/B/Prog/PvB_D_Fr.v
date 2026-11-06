(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: for omx-clap-core/fuzz_preset, the position-abstract-listing runner of
   proofs/cgif/cgif_file_fuzzer/lib/YC80.v (origin/ossv/recipes c8557374ad2e :52-140), as YC80x.v restates it over
   YCbqG.v's journal ajournal_x, for a straight-line stretch that also writes an output through a caller's pointer into
   a frame of the journal's entry state S that the footprint names (YCbqG.v wr_fp_frame):
   - f twins (SRr_*_pi_tok_AJxf): write premise YCbqG.v's awr_ok_fr (awr_byte \/ wr_fp_frame), journal step YCbqG.v's
     ajournal_x_exec_fr; the PA-listing counterparts of YCbqG.v's table-engine runners SRr_*_AJx_fr;
   - mf twins (SRr_*_pi_tok_AJxmf): write premise awr_byte \/ PST \/ wr_fp_frame, journal step ajournal_x_exec_fr_pst
     below (YCbqG.v's ajournal_x_exec_fr, then ajournal_x_pst_write, split as YC80x.v's ajournal_x_exec_mixed);
   - the PAImg-level runners paj_run_xf / paj_run_to_xf / paj_run_xmf / paj_run_to_xmf (as YC1fPx.v's paj_run_x).
   The post of every runner is YC80x.v's run_post_pi_tok_AJx: the post has no write premise (YCbqG.v's _fr runners keep
   run_post_AJx / run_post_tok_AJx the same way). The binders and the premise order are YC80x.v's, so YC1fPx.v's tactics
   paj_run_tok_x / paj_run_to_tok_x drive these runners unchanged (RUN := paj_run_xf / paj_run_xmf, RUNTO :=
   paj_run_to_xf / paj_run_to_xmf), as YC1fPx.v says of its _m runners. Generic: no image instance, no address, no ledger.
   SK (YI16.sink_head) is a Context parameter of every lemma and definition here; the journal and the post are written
   with (rc := rc) (SK := SK). Global sink_head instances exist in this tree (YI5b.v src0_sink_head, YE2k.v / AE2k.v
   tfib_sink_head): write `@paj_run_xf fx rc SK L PL PI B PST ARx _ LAWS` (and `@paj_run_xmf ... _ LAWS PST_ok`; the `_`
   is AR_laws_x's head length, implicit, so a plain citation infers it from LAWS) with SK
   explicit at every use, never let it be inferred. *)
(* Modified by Theorem Labs, 2026-10: the forms over a world relation R (suffix R), as YC80x.v states its runners over
   R. A free or realloc of a live block can hide shadow again, so a walk that crosses one proves YA0nH.SRrG at a
   relation wider than wle (YA0nH.wle' at a zone). ajournal_x_exec_fr_pstR is ajournal_x_exec_fr_pst over YCbqG.v's
   ajournal_x_exec_frR / ajournal_x_pst_writeR. Section ei (Section e's binders, then P and its laws PLAW, YC80x.v's
   srr_inv_laws) holds the _invR forms SRr_chain / run / run_to_pi_tok_AJxf_invR and _AJxmf_invR: the journal at R
   (YCbqG.v ajournal_xR), the premise P (ms_mem ms) right after it, the post YC80x.v's run_post_pi_tok_AJx_invR and
   the conclusion SRrG segs R; the run step is YC80x.v's SRr_msteps_invR. Each runner's R form (SRr_*_AJxfR /
   SRr_*_AJxmfR, post run_post_pi_tok_AJxR) is its _invR form at P := fun _ => True, and each plain runner is its R
   form at wle (wle_refl / wle_trans), statement unchanged.
   Every R form takes R and its two laws (reflexive, transitive) first, so paj_run_xfR / paj_run_to_xfR /
   paj_run_xmfR / paj_run_to_xmfR applied to them have the plain runner's binders in the plain order, and YC1fPx.v's
   paj_run_tok_xR / paj_run_to_tok_xR drive them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YC80xf.v; 99 of its 287 lines of code are new or changed and 343 lines of the source are left out. *)
(* fuzz_preset image B (asan-ubsan), parse_value 0x8637c (segment D helper): the PA-listing runner of
   YC80x.v / YC1fPx.v with the CALLER-FRAME write premise. parse_value's string arm stores the node's type word
   (`sw a0, 0(s3)`, B 0x86554) through its caller's pointer v, and rd_pre's prhReader_at lets v lie in a fake frame of
   a caller (frames S); awr_byte reaches only the function's own frames and live blocks, so this stretch needs YCbqG.v's
   caller-frame form (wr_fp_frame, ajournal_x_exec_fr :674) under the PA engine. The three lemmas are YC80x.v's
   SRr_chain_pi_tok_AJxm / SRr_run_pi_tok_AJxm / SRr_run_to_pi_tok_AJxm with that write premise and that journal step;
   paj_run_x_fr / paj_run_to_x_fr wrap them as YC1fPx.v wraps its runners, with the same binders, so YC1fPx.v's
   tactics paj_run_tok_x / paj_run_to_tok_x drive them unchanged. Generic: no image, no address.
   The memory-invariant twins (suffix _inv): the same three lemmas with YC80x.v's invariant P (laws srr_inv_laws) on
   the start memory, right after the journal premise, and on the end memory in the post (run_post_pi_tok_AJx_inv),
   as YC80x.v's SRr_*_AJx_inv carry it; paj_run_x_fr_inv / paj_run_to_x_fr_inv wrap them as YC1fPx.v wraps
   paj_run_x_inv, so YC1fPx.v's paj_run_tok_x_inv / paj_run_to_tok_x_inv drive them unchanged. Segment D runs its
   string-arm stretches with P := YAkMemnorm.memnorm (the exit cut carries it).
   The R twins (suffix _invR), BESIDE the _inv lemmas: the journal at a world relation R and the conclusion SRrG segs R
   (YC80x.v's SRr_chain_pi_tok_AJx_invR with the caller-frame write premise; the journal step YCbqG.v's
   ajournal_x_exec_frR): the exit stretch after a call whose span frees runs on a journal at the re-hiding relation.
   paj_run_to_x_fr_invR wraps the run-to twin.
   Rule 24: proves no function (kind: kit twin). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section e.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis Hwx : wx_segs_nowrap segs.
Variable fetch : Z -> option Z.
Variable val : nat -> Z.
Variable sigma : psym -> Z.
Variable listing : ptable psym.
Variable tpi0 : ptree psym.
Variable tw0 : ctable.
Hypothesis Hfetch : forall pc w, fetch pc = Some w -> fetch_word segs (Z_to_bv 64 pc) = Some (Z_to_bv 32 w).
Hypothesis Hcert : pi_check psym fetch val sigma listing = true.
Hypothesis HB : 0 <= val A_TEXT /\ val A_TEXT + 2 ^ 40 < 2 ^ 64 /\ val A_TEXT mod 4 = 0.
Variable A_LIM : nat.
Hypothesis HLIM0 : (A_TEXT < A_LIM)%nat.
Hypothesis HLIM : forallb (pinstr_atoms_ltb A_LIM) listing = true.
Hypothesis HLEN : 4 * Z.of_nat (length listing) <= 2 ^ 40.
Hypothesis Htpi : ptree_of_list listing = tpi0.
Hypothesis Htw : tw_of 0 listing = tw0.
Local Notation AJ := (ajournal_x segs B PST ARx).
Local Notation AJR R := (ajournal_xR segs B PST ARx R).
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).

Lemma SRr_chain_pi_tok_AJxfr : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
run_post_pi_tok_AJx psym segs B PST ARx val sigma A_LIM W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_msteps segs Hwx W ms msr' mdc Q Hms).
intros model' Hsame Hcl.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_fr segs B PST ARx LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_pi_tok_AJxfr : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
run_post_pi_tok_AJx psym segs B PST ARx val sigma A_LIM W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJxfr; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_run_to_pi_tok_AJxfr : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
run_post_pi_tok_AJx psym segs B PST ARx val sigma A_LIM W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJxfr; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
(* The memory-invariant twins: P and its laws, then the three lemmas above with P (ms_mem ms) after the journal and
   the _inv post (YC80x.v SRr_chain_pi_tok_AJx_inv, with the caller-frame write premise and journal step). *)
Section ei.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Lemma SRr_chain_pi_tok_AJxfr_inv : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
run_post_pi_tok_AJx_inv psym segs B PST ARx val sigma A_LIM P W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (SRr_msteps_inv segs Hwx P PLAW W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_fr segs B PST ARx LAWS segs_low) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_pi_tok_AJxfr_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
run_post_pi_tok_AJx_inv psym segs B PST ARx val sigma A_LIM P W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJxfr_inv; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_run_to_pi_tok_AJxfr_inv : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
run_post_pi_tok_AJx_inv psym segs B PST ARx val sigma A_LIM P W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof.
intros W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply SRr_chain_pi_tok_AJxfr_inv; [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
Lemma SRr_chain_pi_tok_AJxfr_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
msteps segs (restrict (w_H W) ms) msr' ->
length ws = sh_j st' ->
img_env (extK E K ws) ->
match r with
| PTS_call s => st_ok segs (extK E K ws) (setpc (sh_ss st') (sigma s)) msr'
| _ => st_ok_pi (extK E K ws) (sh_ss st') msr'
end ->
sh_ok segs Bx SH (extK E K ws) (ms_mem msr') ->
frame_of E (ss_mem ss) (ms_mem (restrict (w_H W) ms)) (ms_mem msr') ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
run_post_pi_tok_AJx_invR psym segs B PST ARx val sigma A_LIM P R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
YA0nH.SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R _ _ W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ HPm Hwr Hk.
apply (SRr_msteps_invR segs Hwx P PLAW R W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_exec_frR segs B PST ARx LAWS segs_low R) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
Lemma SRr_run_to_pi_tok_AJxfr_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ wr_fp_frame FP S lyc a) ->
run_post_pi_tok_AJx_invR psym segs B PST ARx val sigma A_LIM P R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
YA0nH.SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJxfr_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
End ei.
End e.
Section g.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
Definition paj_run_x_fr := SRr_run_pi_tok_AJxfr asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_x_fr := SRr_run_to_pi_tok_AJxfr asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws pa_segs P.
Definition paj_run_x_fr_inv := SRr_run_pi_tok_AJxfr_inv asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_x_fr_inv := SRr_run_to_pi_tok_AJxfr_inv asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_x_fr_invR := SRr_run_to_pi_tok_AJxfr_invR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
End g.
End d.
