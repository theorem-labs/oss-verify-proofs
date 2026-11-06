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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
(* Numerals in this file, all as YC80x.v states them: 64 and 32 (WORD: bit widths), 2 ^ 40 and 2 ^ 64 (LENGTH:
   code-span bound, word range), 4 (LENGTH: instruction bytes; text alignment), 0 (DERIVED: listing start offset; lower
   bound). No ADDRESS. *)
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section j.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Local Notation AJ := (ajournal_x (rc := rc) (SK := SK) segs B PST ARx).
Local Notation AJR R := (ajournal_xR (rc := rc) (SK := SK) segs B PST ARx R).
(* ajournal_x_exec_fr_pst below over a world relation R: the same split at memi, over YCbqG.v's ajournal_x_exec_frR and
   ajournal_x_pst_writeR. *)
Lemma ajournal_x_exec_fr_pstR : forall (R : world segs -> world segs -> Prop),
forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
AJR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST \/
  wr_fp_frame FP S lyc a) ->
AJR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof.
intros R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' Wr HJ Hfr Hgr Hhid Hsame HW.
unfold mem_grows, mrestrict in Hgr. unfold mrestrict in Hfr.
pose (memi := fun x : word => if Exists_in_zr_dec PST (bv_unsigned x) then memc x else memc' x).
assert (HJi : AJR R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memi mdc' k).
{ apply (ajournal_x_exec_frR segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memi mdc'
(fun a => Wr a /\ ~ Exists (in_zr a) PST) HJ).
- intros x Hx. specialize (Hfr x). revert Hfr. unfold mrestrict, memi. destruct (w_H Wc x); intros Hfr; [reflexivity|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [reflexivity|].
apply Hfr. intros Hw. exact (Hx (conj Hw Hq)).
- unfold mem_grows, mrestrict, memi. intros x. specialize (Hgr x). revert Hgr. destruct (w_H Wc x); intros Hgr; [exact (fun H => H)|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact (fun H => H) | exact Hgr].
- intros x Hh. unfold memi. destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [reflexivity | exact (Hhid x Hh)].
- exact Hsame.
- intros a [Hw Hq]. destruct (HW a Hw) as [Hb | [Hb | Hb]]; [left; exact Hb | contradiction | right; exact Hb]. }
apply (ajournal_x_pst_writeR segs B PST ARx LAWS segs_low PST_ok R STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memi mdc' k memc' mdc' HJi).
- intros x Hx. unfold mrestrict, memi. destruct (w_H Wc x); [reflexivity|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [contradiction | reflexivity].
- unfold mem_grows, mrestrict, memi. intros x. specialize (Hgr x). revert Hgr. destruct (w_H Wc x); intros Hgr; [exact (fun H => H)|].
destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact Hgr | exact (fun H => H)].
- intros x Hh. unfold memi. destruct (Exists_in_zr_dec PST (bv_unsigned x)) as [Hq|Hq]; [exact (Hhid x Hh) | reflexivity].
- apply same_but_materialized_refl.
Qed.
(* YCbqG.v's ajournal_x_exec_fr with a write set Wr that may also cover the program's own statics PST. The memory change
   splits at an intermediate memory memi (memc' off PST, memc on PST), as YC80x.v's ajournal_x_exec_mixed splits it:
   memc -> memi is ajournal_x_exec_fr over Wr minus PST, memi -> memc' is YCbqG.v's ajournal_x_pst_write. No premise
   beyond ajournal_x_exec_fr's and PST_ok. *)
Lemma ajournal_x_exec_fr_pst : forall STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k memc' mdc' (Wr : Z -> Prop),
AJ STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc mdc k ->
(forall x : word, ~ Wr (bv_unsigned x) -> mrestrict (w_H Wc) memc' x = mrestrict (w_H Wc) memc x) ->
mem_grows (mrestrict (w_H Wc) memc) (mrestrict (w_H Wc) memc') ->
(forall x : word, w_H Wc x = true -> memc' x = memc x) ->
same_but_materialized mdc mdc' ->
(forall a, Wr a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/ Exists (in_zr a) PST \/
  wr_fp_frame FP S lyc a) ->
AJ STK sp0 FP ly S Hp W mem md own lyc Sc Hpc Wc memc' mdc' k.
Proof. exact (ajournal_x_exec_fr_pstR (@wle segs)). Qed.
End j.
Section e.
Variable psym : Type.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img segs a /\ ~ Exists (in_zr a) (as_owned_static B).
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
Local Notation AJ := (ajournal_x (rc := rc) (SK := SK) segs B PST ARx).
Local Notation RPOST := (run_post_pi_tok_AJx (rc := rc) (SK := SK) psym segs B PST ARx val sigma A_LIM).
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).
Local Notation AJR R := (ajournal_xR (rc := rc) (SK := SK) segs B PST ARx R).
Local Notation RPOSTR R := (run_post_pi_tok_AJxR (rc := rc) (SK := SK) psym segs B PST ARx val sigma A_LIM R).
(* The forms with the memory invariant P over a world relation R (suffix _invR): Section e's binders, then P and its
   laws PLAW, then R and its two laws. *)
Section ei.
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Local Notation RPOSTIR R := (run_post_pi_tok_AJx_invR (rc := rc) (SK := SK) psym segs B PST ARx val sigma A_LIM P R).
(* SRr_chain_pi_tok_AJxf below over R with the premise P (ms_mem ms); the journal step is YCbqG.v's
   ajournal_x_exec_frR, the run step YC80x.v's SRr_msteps_invR. *)
Lemma SRr_chain_pi_tok_AJxf_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
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
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTIR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
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
(* SRr_run_pi_tok_AJxf below over R with the premise P (ms_mem ms). *)
Lemma SRr_run_pi_tok_AJxf_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTIR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJxf_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
(* SRr_run_to_pi_tok_AJxf below over R with the premise P (ms_mem ms). *)
Lemma SRr_run_to_pi_tok_AJxf_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
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
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTIR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJxf_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
(* SRr_chain_pi_tok_AJxmf below over R with the premise P (ms_mem ms); the journal step is ajournal_x_exec_fr_pstR. *)
Lemma SRr_chain_pi_tok_AJxmf_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
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
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTIR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
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
- eapply (ajournal_x_exec_fr_pstR segs B PST ARx LAWS segs_low PST_ok R) with (Wr := in_wrange E (ss_mem ss)); [exact HJ | | | | | exact Hwr].
+ rewrite Hmm. exact Hfr.
+ rewrite Hmm. exact Hgr.
+ intros x Hx. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hx. reflexivity.
+ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- rewrite Hmm. exact Hfr.
- rewrite Hmm. exact Hgr.
Qed.
(* SRr_run_pi_tok_AJxmf below over R with the premise P (ms_mem ms). *)
Lemma SRr_run_pi_tok_AJxmf_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTIR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJxmf_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
(* SRr_run_to_pi_tok_AJxmf below over R with the premise P (ms_mem ms). *)
Lemma SRr_run_to_pi_tok_AJxmf_invR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
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
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTIR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ HPm Hobl Hwr Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_to_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n stop E ss _ st' r
HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
eapply (SRr_chain_pi_tok_AJxmf_invR R Rr Rt); [exact Hms | exact Hlen | exact HE' | | exact Hsh' | exact Hfr | exact HJ | exact HPm | exact Hwr | exact Hk].
destruct r; cbn [ptok_post] in HP; first [exact HP | destruct HP].
Qed.
End ei.
(* SRr_chain_pi_tok_AJxf_invR at P := fun _ => True. *)
Lemma SRr_chain_pi_tok_AJxfR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
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
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_chain_pi_tok_AJxf_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ I Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* YC80x.v's SRr_chain_pi_tok_AJx with the write premise YCbqG.v's awr_ok_fr; the journal step is YCbqG.v's
   ajournal_x_exec_fr (as YCbqG.v's SRr_chain_tok_AJx_fr takes it for the table engine). *)
Lemma SRr_chain_pi_tok_AJxf : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
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
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOST W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_pi_tok_AJxfR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_pi_tok_AJxf_invR at P := fun _ => True. *)
Lemma SRr_run_pi_tok_AJxfR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
apply (SRr_run_pi_tok_AJxf_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ I Hobl Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* YC80x.v's SRr_run_pi_tok_AJx with the write premise awr_ok_fr. *)
Lemma SRr_run_pi_tok_AJxf : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOST W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_pi_tok_AJxfR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_pi_tok_AJxf_invR at P := fun _ => True. *)
Lemma SRr_run_to_pi_tok_AJxfR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
apply (SRr_run_to_pi_tok_AJxf_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ I Hobl Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* YC80x.v's SRr_run_to_pi_tok_AJx with the write premise awr_ok_fr. *)
Lemma SRr_run_to_pi_tok_AJxf : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOST W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_tok_AJxfR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* Mixed twins over R: SRr_chain_pi_tok_AJxmf_invR at P := fun _ => True. *)
Lemma SRr_chain_pi_tok_AJxmfR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
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
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ Hwr Hk.
apply (SRr_chain_pi_tok_AJxmf_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W E K Bx SH ws ss st' r ms msr' STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q Hms Hlen HE' HS' Hsh' Hfr HJ I Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
(* Mixed twins: the stretch may write, besides awr_byte's bytes and the caller-frame output bytes (wr_fp_frame), the
   program's own statics PST. The journal step is ajournal_x_exec_fr_pst above; otherwise the three lemmas above. *)
Lemma SRr_chain_pi_tok_AJxmf : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
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
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOST W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_pi_tok_AJxmfR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_pi_tok_AJxmf_invR at P := fun _ => True. *)
Lemma SRr_run_pi_tok_AJxmfR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
apply (SRr_run_pi_tok_AJxmf_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ I Hobl Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
Lemma SRr_run_pi_tok_AJxmf : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOST W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_pi_tok_AJxmfR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* SRr_run_to_pi_tok_AJxmf_invR at P := fun _ => True. *)
Lemma SRr_run_to_pi_tok_AJxmfR : forall (R : world segs -> world segs -> Prop), (forall W, R W W) ->
(forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3) ->
forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJR R STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTR R W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ Hobl Hwr Hk.
apply (SRr_run_to_pi_tok_AJxmf_invR (fun _ => True) (srr_inv_laws_true segs) R Rr Rt W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0
mem md own lyc Sc Hpc mdc k Q HK HE HS Hsh Hchk Hrun HJ I Hobl Hwr).
intros ws' ms' mat' H1 H2 H3 H4 H5 _. exact (Hk ws' ms' mat' H1 H2 H3 H4 H5).
Qed.
Lemma SRr_run_to_pi_tok_AJxmf : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOST W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_tok_AJxmfR (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End e.
Section g.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img pa_segs a /\ ~ Exists (in_zr a) (as_owned_static B).
(* YC1fPx.v's paj_run_x / paj_run_to_x / paj_run_x_m / paj_run_to_x_m at the runners above. *)
Definition paj_run_xf := SRr_run_pi_tok_AJxf asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_xf := SRr_run_to_pi_tok_AJxf asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_xmf := SRr_run_pi_tok_AJxmf asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_xmf := SRr_run_to_pi_tok_AJxmf asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
(* The runners over a world relation R: R and its two laws first, then the plain runner's binders. *)
Definition paj_run_xfR := SRr_run_pi_tok_AJxfR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_xfR := SRr_run_to_pi_tok_AJxfR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_xmfR := SRr_run_pi_tok_AJxmfR asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
Definition paj_run_to_xmfR := SRr_run_to_pi_tok_AJxmfR asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq.
End g.
End d.
