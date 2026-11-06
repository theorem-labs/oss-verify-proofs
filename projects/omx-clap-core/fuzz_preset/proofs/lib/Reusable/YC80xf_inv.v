(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, the twins of YC80xf.v's runners that carry a memory invariant P across the
   symbolic run, as YSRrMemnorm.v (h-w6u-pre's override-free split, origin/cold/h-srr-inv ee86d811008, blob
   898b7550dec7) carries it for YC80x.v's runners. Written once at the lead's approval (h-hpreset-7 11:20Z), for the
   walks that also write an output through a caller's pointer into a frame of the journal's entry state (YCbqG.v
   wr_fp_frame). GENERIC in
   P : (word -> option byte) -> Prop with its laws PLAW : srr_inv_laws segs P (YSRrMemnorm.v), as SRr_msteps_inv is.
   rule 24: no function proved. rule 24: proves no function (kind: segment lemma / runner invariant twin).
   WHAT, each the YC80xf.v lemma of the same name without _inv, its proof unchanged but for YA0n.SRr_msteps ->
   YSRrMemnorm.SRr_msteps_inv and the post run_post_pi_tok_AJx -> YSRrMemnorm.run_post_pi_tok_AJx_inv:
   - SRr_chain_pi_tok_AJxf_inv / SRr_run_pi_tok_AJxf_inv / SRr_run_to_pi_tok_AJxf_inv: write premise YCbqG.v's
     awr_ok_fr, journal step YCbqG.v's ajournal_x_exec_fr;
   - SRr_chain_pi_tok_AJxmf_inv / SRr_run_pi_tok_AJxmf_inv / SRr_run_to_pi_tok_AJxmf_inv: write premise awr_byte \/ PST
     \/ wr_fp_frame, journal step YC80xf.v's ajournal_x_exec_fr_pst;
   - the PAImg-level runners paj_run_xf_inv / paj_run_to_xf_inv / paj_run_xmf_inv / paj_run_to_xmf_inv (YC80xf.v's
     paj_run_xf .. with P and PLAW last, as YSRrMemnorm.v's paj_run_x_inv).
   The binders and the premise order are YSRrMemnorm.v's (the P premise right after the journal premise), so its tactics
   paj_run_tok_x_inv / paj_run_to_tok_x_inv drive these runners unchanged (RUN := paj_run_xf_inv .. P PLAW).
   SK (YI16.sink_head) is a Context parameter, as in YC80xf.v: pass SK explicitly at every use.
   ORDER: YSRrMemnorm.v is Required here; it Requires YAkMemnorm.v only (no lib/Lib/LiaTwx2.v in its closure), so the
   proofs below see Stdlib's lia. Numerals: none beyond YC80xf.v's (2 ^ 40, 2 ^ 64, 4, 0: LENGTH / DERIVED). No ADDRESS. *)
(* Modified by Theorem Labs, 2026-10: over a world relation R. YC80xf.v's Section ei states the six runners above over
   R (suffix _invR: R and its two laws, reflexive and transitive, after P and PLAW; journal YCbqG.v ajournal_xR, post
   YC80x.v run_post_pi_tok_AJx_invR, conclusion YA0nH.SRrG segs R); each runner here is its _invR form at wle
   (wle_refl / wle_trans), statement unchanged. paj_run_xf_invR / paj_run_to_xf_invR / paj_run_xmf_invR /
   paj_run_to_xmf_invR are the PAImg-level runners over them, Section g's binders then P and PLAW as the plain ones
   take them, so a caller writes `pose (RUN := @paj_run_xf_invR fx rc SK L PL PI B PST ARx _ LAWS P PLAW R R_refl
   R_trans)` and YC1fPx.v's paj_run_tok_x_invR / paj_run_to_tok_x_invR drive it. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YC80xf YSRrMemnorm.
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
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws segs P.
Local Notation AJ := (ajournal_x (rc := rc) (SK := SK) segs B PST ARx).
Local Notation RPOSTI := (run_post_pi_tok_AJx_inv (rc := rc) (SK := SK) psym segs B PST ARx val sigma A_LIM P).
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).
(* YC80xf.v's SRr_chain_pi_tok_AJxf; SRr_msteps -> SRr_msteps_inv. *)
Lemma SRr_chain_pi_tok_AJxf_inv : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
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
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTI W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_pi_tok_AJxf_invR (rc := rc) (SK := SK) psym segs B PST ARx LAWS segs_low Hwx val sigma A_LIM P PLAW
(@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* YC80xf.v's SRr_run_pi_tok_AJxf over the chain twin. *)
Lemma SRr_run_pi_tok_AJxf_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTI W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_pi_tok_AJxf_invR (rc := rc) (SK := SK) psym segs B PST ARx LAWS segs_low Hwx fetch val sigma listing
tpi0 tw0 Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN Htpi Htw P PLAW (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* YC80xf.v's SRr_run_to_pi_tok_AJxf over the chain twin. *)
Lemma SRr_run_to_pi_tok_AJxf_inv : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
awr_ok_fr E (ss_mem ss) STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) S lyc own ->
RPOSTI W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_tok_AJxf_invR (rc := rc) (SK := SK) psym segs B PST ARx LAWS segs_low Hwx fetch val sigma listing
tpi0 tw0 Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN Htpi Htw P PLAW (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
(* Mixed twins (YC80xf.v's _AJxmf): the stretch may also write the program's own statics PST; the journal step is
   YC80xf.v's ajournal_x_exec_fr_pst. *)
Lemma SRr_chain_pi_tok_AJxmf_inv : forall W E K Bx SH ws ss (st' : shst) (r : ptrun_status psym) ms msr' STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
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
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTI W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_chain_pi_tok_AJxmf_invR (rc := rc) (SK := SK) psym segs B PST ARx LAWS segs_low PST_ok Hwx val sigma A_LIM P
PLAW (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
Lemma SRr_run_pi_tok_AJxmf_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTI W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_pi_tok_AJxmf_invR (rc := rc) (SK := SK) psym segs B PST ARx LAWS segs_low PST_ok Hwx fetch val sigma
listing tpi0 tw0 Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN Htpi Htw P PLAW (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
Lemma SRr_run_to_pi_tok_AJxmf_inv : forall W n stop E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q,
(A_LIM <= K)%nat -> img_env E ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_run_toN_pi_tok tpi0 tw0 K Bx Bspan SH n stop ss = (st', r) ->
AJ STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a -> awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a \/
  Exists (in_zr a) PST \/ wr_fp_frame FP S lyc a) ->
RPOSTI W E K Bx SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k Q ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (SRr_run_to_pi_tok_AJxmf_invR (rc := rc) (SK := SK) psym segs B PST ARx LAWS segs_low PST_ok Hwx fetch val sigma
listing tpi0 tw0 Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN Htpi Htw P PLAW (@wle segs) (wle_refl segs) (wle_trans segs)). Qed.
End e.
(* YC80xf.v Section g (:279-296), then P and its laws (as YSRrMemnorm.v's paj_run_x_inv). *)
Section g.
Context {L : ptable asym} {PL : PAListing L} {PI : PAImg L}.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx HL.
Hypothesis PST_ok : forall a, Exists (in_zr a) PST -> in_img pa_segs a /\ ~ Exists (in_zr a) (as_owned_static B).
Variable P : (word -> option byte) -> Prop.
Hypothesis PLAW : srr_inv_laws pa_segs P.
Definition paj_run_xf_inv := SRr_run_pi_tok_AJxf_inv asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_xf_inv := SRr_run_to_pi_tok_AJxf_inv asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_xmf_inv := SRr_run_pi_tok_AJxmf_inv asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_xmf_inv := SRr_run_to_pi_tok_AJxmf_inv asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
(* The runners over a world relation R: P and its laws, then R and its two laws (YC80xf.v's _invR runner lemmas). *)
Definition paj_run_xf_invR := SRr_run_pi_tok_AJxf_invR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_xf_invR := SRr_run_to_pi_tok_AJxf_invR asym pa_segs B PST ARx LAWS pa_segs_low pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_xmf_invR := SRr_run_pi_tok_AJxmf_invR asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
Definition paj_run_to_xmf_invR := SRr_run_to_pi_tok_AJxmf_invR asym pa_segs B PST ARx LAWS pa_segs_low PST_ok pa_wx (clookup pa_tbl) pa_val pa_sigma L
pl_tpi pl_tw pa_fetch_ok pa_cert pa_B_ok A_LIM A_LIM_text pl_lim pl_len pl_tpi_eq pl_tw_eq P PLAW.
End g.
End d.

Check SRr_chain_pi_tok_AJxf_inv.
Check SRr_run_pi_tok_AJxf_inv.
Check SRr_run_to_pi_tok_AJxf_inv.
Check SRr_chain_pi_tok_AJxmf_inv.
Check SRr_run_pi_tok_AJxmf_inv.
Check SRr_run_to_pi_tok_AJxmf_inv.
Check paj_run_xf_inv.
Check paj_run_to_xf_inv.
Check paj_run_xmf_inv.
Check paj_run_to_xmf_inv.
Print Assumptions paj_run_xf_inv.
Print Assumptions paj_run_xmf_inv.
