(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/Ent102L6AFlag.v, with its module paths and module names changed; 324 of its 494 lines of code are new or changed and 85 lines of the source are left out. *)
(* fuzz_preset, slice S5b, image A' (asan 1be0f53d96cb, the #102 pin): parse_value's SHARED EPILOGUE (rows 225..265)
   with a memory invariant P carried across the run. Lane PV-arms-LC (worker a Theorem Labs lane); the P twin of the epilogue
   step (lib/A/VrdEpi.v vrd_epi_holds, lib/A/VrdEpiA.v vrd_epi_step), at the lead's 15:59Z ruling (vrd_epi_step_P is
   ours; one copy, every arm that reaches row 225 cites it).

   rule 24: no function proved. rule 24: proves no function (kind: segment lemma / runner invariant twin).

   WHAT.
   - aj_flag_store_x_invR / aj_flag_store_x_inv: YGcallSx.aj_flag_store_x (the cut's lib/Reusable/YGcallSx.v blob
     cbe8592c72da, the inline release under the frame-area free law) with the generic binder P and its laws
     srr_inv_laws segs P: P of the memory at the run's start (right after the journal premise) and P of the memory at
     its end (right after the journal in the continuation), as YSRrMemnorm.v's runner twins place it. Its proof is the
     cut's aj_flag_store_x proof, copied, with the one run primitive YA0n.SRr_msteps replaced by its P twin; nothing
     else changes. aj_flag_store_x_invR states it over a journal at a world relation R (YCbqG.v ajournal_xR) and the
     step relation YA0nH.SRrG R (the run by YC80x.SRr_msteps_invR, the journal by the ajxR_* projections,
     awr_byte_cases_xR and ajournal_x_after_writeR): the run keeps the world, so no law of R is read, and a caller
     whose journal spans an earlier free takes it at that wider R. aj_flag_store_x_inv is its instance at wle, its
     statement unchanged. It is an ENGINE twin kept in this file: the engine owner may lift it into YGcallSx.v by
     path.
   - vrd_epi_holds_P: VrdEpi.vrd_epi_holds with P: from the join state at row 225 with P of its memory, the call
     returns, meets the budget-free caller-window post, and P holds of the memory at the return. The journal from
     parse_value's entry spans the frees of the subtree, so the join journal and the post's journal are at
     YA0nH.wle' segs YGcfRehidePost.RZ_cf (premise ajournal_xR at that relation, post PRH_Base.fpostWFR at it) and
     the step relation is SRr' segs RZ_cf. The proof is vrd_epi_holds's, with aj_flag_store_x replaced by
     aj_flag_store_x_invR at wle' segs RZ_cf; the `ret` (YC1fP.paj_ret_at) keeps the world and the memory and is
     lifted by YA0nH.SRr_SRrG, so P of the run's end memory is P of the return state's. The journal is read by the
     engine's ajxR_* projections, astk_ok and region_ok's chunk conjunct by the shape guards vep_astk /
     vep_region_chunks.
   - vrd_epi_step_P: VrdEpiA.vrd_epi_step with P, from the join state VrdNum.vrd_epi_aR at wle' segs RZ_cf (the
     container arm's join) to the BUDGETED post fpostWFb at the text's budget wbudget CW 0, by VrdEpiA's budget
     bridge over R (ajournal_xw_rebaseR, then vrd_epi_holds_P at the join's depot, then ajournal_xw_unbase0R at the WS
     the join names).
   - vrd_epi_step_true: the P := True instance of vrd_epi_step_P, whose statement is vrd_epi_step's word for word: a
     join at wle (vrd_epi_a) reaches the R form by VrdEpiA.vrd_epi_a_wle'.
   SECTION HYPOTHESES: those of VrdEpi.v's Section c, verbatim (LAWS, ASFX, FFLX, FPRES, SFX), and of YGcallSx.v's
   Sections x / e that aj_flag_store_x reads. P is a binder of each statement, abstract in every proof.

   SET: the kit's cut 7cdbb61b5fa0 (a working branch) with a Theorem Labs lane's value-side interface
   a working branch e942c5680fa7 (VrdNum.v 636d54d20156, VrdEpi.v 38bfc716a234); engine on the cut:
   YGcallSx.v cbe8592c72da, YCbqG.v 219748197d6b, YCbqGwild.v 0c63874858e4, YC80x.v 14f84f225e8f (SRr_msteps_inv),
   YSRrMemnorm.v 5ffa8525936b, YAkMemnorm.v 96c72061b4d4. History: first proved on image A
   (a working branch 52a6304ca913, blob e7b3eeaca63b) over YGcallSx.v 17d7d2cdbcd1.

   NUMERALS: those of vrd_epi_holds (8, 56, 64, 104, 512, 4096, 2 ^ 64: LENGTH; atom indices 3, 4, 8, 18, 21, 24,
   26, 32..45: DERIVED). No ADDRESS: the entry is A_prog_sigma AS_parse_value + VrdEpi.VE_EPI. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcallx YGcallSx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH YSRrG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_Img.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
Img0 Listing_prog PAImg_prog VrdPro VrdNum VrdEpi VrdEpiA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------------- *)
(* 1. THE RELEASE RULE WITH P: YGcallSx.aj_flag_store_x's twin.                                          *)
(* ---------------------------------------------------------------------------------------------------- *)
Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Notation AJ := (ajournal_x (SK := SK) segs B PST ARx).
Local Notation AJR := (ajournal_xR (SK := SK) segs B PST ARx).
Context {HL : Z}.  (* AR_laws_x's head length (YCbqG.v), implicit: inferred from LAWS *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* YGcallSx.v's ASFX / FFLX / SFX, verbatim *)
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview segs (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, aview segs (w_H W) mem a <> None -> aview segs (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world segs) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img segs (flag_addr ly cid pos)).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.
Section e.
Variable psym : Type.
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
Local Notation img_env := (img_env val A_LIM).
Local Notation st_ok_pi := (st_ok_pi segs val).

(* the rule over a journal at a world relation R, the run and its continuation over SRrG R: the run keeps the world,
   so no law of R is read *)
Lemma aj_flag_store_x_invR : forall (R : world segs -> world segs -> Prop),
forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q,
(A_LIM <= K)%nat -> img_env E -> 0 <= cid ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
AJR R STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
(forall ws msr, length ws = sh_j st' -> st_ok_pi (extK E K ws) (sh_ss st') msr ->
  mbyte segs (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
(forall ws ms' mat',
  length ws = sh_j st' -> img_env (extK E K ws) ->
  st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
  sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
  AJR R STK sp0 FP ly S Hp W0 mem md own' lyc (stack_free_state cid pos Sc) Hpc W (ms_mem ms')
    (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  P (ms_mem ms') ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  YA0nH.SRrG segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
YA0nH.SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q
HK HE Hcid HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hflag0 Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
  HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
assert (HS' : st_ok_pi (extK E K ws) (sh_ss st') msr') by (destruct r; cbn [ptok_post] in HP; first [exact HP | destruct Hr | destruct HP]).
clear HP.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_frs HJ) as Hfrs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFLX lyc Sc Hpc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfo & Hfr_rng).
(* the one change from aj_flag_store_x: the run primitive's P twin *)
apply (SRr_msteps_invR segs Hwx P PLAW R W ms msr' mdc Q Hms HPm).
intros model' Hsame Hcl HPm'.
rewrite (same_but_materialized_wvb mdc model' Hsame).
pose proof (restrict_unrestrict_clean (w_H W) (ms_mem ms) msr' Hcl) as Hrr.
pose proof (mrestrict_unrestrict_mem (w_H W) (ms_mem ms) msr' Hcl) as Hmm.
pose proof (msteps_mem_grows segs _ _ Hms) as Hgr. cbn [ms_mem restrict] in Hgr.
set (memc' := ms_mem (unrestrict (w_H W) (ms_mem ms) msr')) in *.
assert (Hfr' : forall x : word, ~ in_wrange E (ss_mem ss) (bv_unsigned x) -> mrestrict (w_H W) memc' x = mrestrict (w_H W) (ms_mem ms) x).
{ subst memc'. rewrite Hmm. exact Hfr. }
assert (Hgr' : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) memc')) by (subst memc'; rewrite Hmm; exact Hgr).
assert (Heqw : forall a, 0 <= a < 2 ^ 64 -> ~ in_wrange E (ss_mem ss) a -> aview segs (w_H W) memc' a = aview segs (w_H W) (ms_mem ms) a).
{ intros a Ha HWa. apply aview_eq_of. apply Hfr'. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 64) with (2 ^ 64). rewrite Z.mod_small by zlia. exact HWa. }
assert (Hsame' : same_but_materialized mdc (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ rewrite <- (same_but_materialized_wvb mdc model' Hsame). exact Hsame. }
pose proof (same_but_materialized_wvb mdc _ Hsame') as Emd.
destruct (SFX lyc Sc Hpc W (ms_mem ms) mdc cid pos HAR Hin) as (l1 & l2 & E1 & E2).
assert (El1 : l1 = []).
{ destruct l1 as [|f l1']; [reflexivity|]. exfalso.
  rewrite Hfrs in E1. cbn in E1. injection E1 as <- E1'.
  pose proof (sep_frames_pos_x segs B ARx LAWS lyc Sc Hpc W (ms_mem ms) mdc (cid, pos) (cid, pos) [] l1' l2 HAR
    ltac:(rewrite Hfrs; cbn; rewrite E1'; reflexivity)) as Hd.
  unfold zdisjoint, frame_rng in Hd. cbn [fst snd] in Hd. pose proof (fs_frame_bytes_pos cid Hcid). zlia. }
subst l1. cbn in E1, E2. rewrite Hfrs in E1. cbn in E1. injection E1 as E1.
assert (HAR' : ARx lyc (stack_free_state cid pos Sc) Hpc W memc' (with_vm_backing (m_vm_lazy mdc) (m_vm_materialized model') mdc)).
{ eapply (ASFX lyc Sc Hpc W (ms_mem ms) mdc memc' _ cid pos HAR Hin).
  - unfold aview. subst memc'. rewrite Hmm. rewrite (Hflag0 ws msr' Hlen HS'). reflexivity.
  - intros a Ha Ho Hne. apply Heqw; [exact Ha|]. intros HWa.
    destruct (Hwr a HWa) as [Hw | Hw]; [|exact (Hne Hw)].
    exact (proj1 (awr_byte_cases_xR segs B PST ARx LAWS R _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a _ Hh. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- subst memc'. rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_after_writeR segs B PST ARx LAWS segs_low R STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc
    Hpc W (ms_mem ms) mdc k memc' _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc) Hpc own' HJ Heqw
    ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
  + intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  + exact HAR'.
  + unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  + reflexivity.
  + cbn. zlia.
  + etransitivity; [exact E2 | symmetry; exact E1].
  + pose proof (ajxR_qt HJ) as HQT.
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact HQT].
  + reflexivity.
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.

(* the instance at wle, the statement of before *)
Lemma aj_flag_store_x_inv : forall W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q,
(A_LIM <= K)%nat -> img_env E -> 0 <= cid ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
AJ STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W (ms_mem ms) mdc k ->
P (ms_mem ms) ->
Forall (ob_holds segs Bx E (mrestrict (w_H W) (ms_mem ms))) (sh_obls st') ->
(forall a, in_wrange E (ss_mem ss) a ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc ((cid, pos) :: own') a \/ a = flag_addr lyc cid pos) ->
(forall ws msr, length ws = sh_j st' -> st_ok_pi (extK E K ws) (sh_ss st') msr ->
  mbyte segs (ms_mem msr) (flag_addr lyc cid pos) = Some (Z_to_bv 8 0)) ->
(forall ws ms' mat',
  length ws = sh_j st' -> img_env (extK E K ws) ->
  st_ok_pi (extK E K ws) (sh_ss st') (restrict (w_H W) ms') ->
  sh_ok segs Bx SH (extK E K ws) (mrestrict (w_H W) (ms_mem ms')) ->
  AJ STK sp0 FP ly S Hp W0 mem md own' lyc (stack_free_state cid pos Sc) Hpc W (ms_mem ms') (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  P (ms_mem ms') ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRr segs W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
SRr segs W (mkCfg ms mdc) Q.
Proof. exact (aj_flag_store_x_invR (@wle segs)). Qed.
End e.
End x.

(* ---------------------------------------------------------------------------------------------------- *)
(* 2. THE EPILOGUE WITH P: VrdEpi.vrd_epi_holds's and VrdEpiA.vrd_epi_step's twins.                       *)
(* ---------------------------------------------------------------------------------------------------- *)
Section c.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg} {RL : PrhRoomLive}.
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
(* VrdEpi.v's Section c hypotheses, verbatim *)
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx HL.
Hypothesis ASFX : forall ly S Hp W mem md mem' md' cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aview SEGS (w_H W) mem' (flag_addr ly cid pos) = Some 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> aowned B ly S a -> a <> flag_addr ly cid pos ->
     aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
  (forall a, aview SEGS (w_H W) mem a <> None -> aview SEGS (w_H W) mem' a <> None) ->
  m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md -> eager_used md' = eager_used md ->
  (forall a, in_band_rw a -> w_H W (w64 a) = true -> mem' (w64 a) = mem (w64 a)) ->
  ARx ly (stack_free_state cid pos S) Hp W mem' md'.
Hypothesis FFLX : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  aowned B ly S (flag_addr ly cid pos) /\ (app_addr (flag_addr ly cid pos) /\ ~ in_img SEGS (flag_addr ly cid pos)).
Hypothesis FPRES : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> apresent (w_H W) mem (flag_addr ly cid pos).
Hypothesis SFX : forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  exists l1 l2, frames S = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos S) = l1 ++ l2.


(* SHAPE GUARDS: the engine predicates this file reads, stated as their definitions have them on the cut (YCbq.v
   astk_ok, YP09.v region_ok's chunk conjunct). A change of either fails here, not by a silent rebinding. *)
Lemma vep_astk {STK : Z} {ly : alayout} {sp0 : Z} : astk_ok STK ly sp0 ->
  sp0 mod 16 = 0 /\ 0 <= STK /\ alloc_ceiling <= ly_stk_lo ly /\ ly_stk_lo ly + STK <= sp0 /\ sp0 <= ly_stk_hi ly /\
  ly_stk_hi ly <= 2 ^ 47 /\ ly_bot ly + STK + ACALL_PREFIX < sp0 + ASTACK /\ sp0 <= ly_top ly /\ ly_top ly <= ly_stk_hi ly.
Proof. intros H. exact H. Qed.
Lemma vep_region_chunks {sg : list Segment} {E : env} {m : word -> option byte} {r : YP09.region} :
  YP09.region_ok sg E m r -> Forall (YP09.chunk_ok sg E m (YP09.base_val E (YP09.r_base r))) (YP09.r_chunks r).
Proof. unfold YP09.region_ok. cbv zeta. tauto. Qed.

(* VrdEpi.vrd_epi_stmt with P: P of the join memory as the last premise, P of the reached memory as a conjunct of
   the continuation. The journal from parse_value's entry spans the subtree's frees, so it is at the after-free
   relation wle' segs RZ_cf in the premise and in the post (fpostWFR at that relation), and the step relation is
   SRr' segs RZ_cf *)
Definition vrd_epi_stmt_P (P : (word -> option byte) -> Prop) (d : nat) : Prop :=
  forall (fxj : YK11.FPState)
    (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world SEGS) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model)
    (ly : alayout) (S : astate) (Hp : list Z) (W : world SEGS) (regs : bvmap 5 word)
    (mem : word -> option byte) (md : Model)
    (e q v pos rv k : Z)
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop),
  104 <= STK_parse_value d ->
  ajournal_xR (SK := SK) SEGS B prh_pst ARx (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_value d + e) (spZ regs0 + e)
    (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview SEGS (w_H W) mem a = aview SEGS (w_H W0) mem0 a) ->
  getr regs 8 = w64 (spZ regs0) ->
  getr regs 18 = w64 (frame_addr ly 0 pos) -> getr regs 26 = w64 (frame_addr ly 0 pos) ->
  getr regs 24 = w64 (SHADOW_OFF + frame_addr ly 0 pos / 8) -> getr regs 21 = w64 rv ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 -> YK0s.ret_ok (getr regs0 1) ->
  vrd_saved (rdW W mem) (spZ regs0) regs0 ->
  val_mem SEGS (rdW W mem) (frame_addr ly 0 pos + 56) 8 (flag_addr ly 0 pos) ->
  frm_zero (@YK11.fp_csr fxj) -> fregs_kept_x fx fxj ->
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     getr regs' 10 = w64 rv -> aregs_preserved regs0 regs' ->
     frames (stack_free_state 0 pos S) = frames S0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ in_frames ly [(0, pos)] a -> a <> flag_addr ly 0 pos ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     Q ly (stack_free_state 0 pos S) Hp W regs' mem' md') ->
  P mem ->
  SRr' SEGS YGcfRehidePost.RZ_cf W
    (mkCfg (@YK11.mkst fxj regs (w64 (A_prog_sigma AS_parse_value + VE_EPI)) mem (YK11.seg_rom SEGS)) md)
    (fun W' c' => fpostWFR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) (STK_parse_value d) e (rd_fp q v) regs0
                    ly0 S0 Hp0 W0 mem0 md0 Q W' c' /\
                  P (ms_mem (cfg_ms c'))).

(* VrdEpi.v's ve_fin (a Section-local Ltac there), verbatim *)
Ltac ve_fin HS :=
  lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
    rewrite (st_ok_pi_restrict_reg _ _ _ _ r HS);
    lazymatch goal with |- context [sr_get (ss_regs ?ss) r] =>
      let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e end;
    cbn [sv_denot]; rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned
  end.

(* ---- rows 225..265 in ONE run under the release rule with P, then the return: vrd_epi_holds's proof with
   aj_flag_store_x -> aj_flag_store_x_invR at wle' segs RZ_cf ---- *)
Lemma vrd_epi_holds_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall d, vrd_epi_stmt_P P d.
Proof.
intros P PLAW d fxj ly0 S0 Hp0 W0 regs0 mem0 md0 ly S Hp W regs mem md e q v pos rv k Q
  H104 HJ HWIN H8 H18 H26 H24 H21 H3 H4 HRA HSAV HFLG HFRM HFRK HQ HPM.
pose proof (ajxR_ar HJ) as HAR. pose proof (ajxR_frs HJ) as Hfrs. pose proof (ajxR_stk HJ) as Hstk.
assert (Hin : In (0, pos) (frames S)) by (rewrite Hfrs; left; reflexivity).
destruct (vep_astk Hstk) as (_ & _ & Hceil & Hslo & Hshi & Hhi47 & _ & _ & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hlo : alloc_ceiling + 104 <= spZ regs0) by lia.
destruct (ve_geom B ARx LAWS FFLX FPRES ly S Hp W mem md pos HAR Hin)
  as (HF4096 & HFceil & Hmod & HF8 & HSB & Hfl4096 & Hflceil & HflF & HflSH & HFp & HSp & HFLp).
destruct (ve_entry B ARx LAWS FFLX FPRES fxj ly S Hp W regs regs0 mem md pos HAR Hin H8 H18 H26 H24 HSAV HFLG Hlo)
  as [HS SHOK].
destruct (ve_E_vals regs regs0 (flag_addr ly 0 pos)) as (E3 & E4 & E8 & E18 & E21 & E24 & E26 & E32 & EX).
assert (HEI : img_env (@pa_val _ A_prog_listing PI_prog_A) A_LIM (ve_E regs regs0 (flag_addr ly 0 pos)))
  by (unfold ve_E; apply Eimg_env).
assert (HFB64 : fs_frame_bytes 0 = 64) by (vm_compute; reflexivity).
assert (Hsp64 : 0 <= spZ regs0 < 2 ^ 64) by (unfold spZ; apply u64_range).
assert (UF : bv_unsigned (ew (ve_E regs regs0 (flag_addr ly 0 pos)) 26) = frame_addr ly 0 pos)
  by (rewrite E26, H26; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
assert (USH : bv_unsigned (ew (ve_E regs regs0 (flag_addr ly 0 pos)) 24) = SHADOW_OFF + frame_addr ly 0 pos / 8).
{ rewrite E24, H24. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. unfold SHADOW_OFF. lia. }
assert (UFL : bv_unsigned (ew (ve_E regs regs0 (flag_addr ly 0 pos)) 32) = flag_addr ly 0 pos)
  by (rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; reflexivity).
(* the atoms of the final registers, as the entry's registers *)
assert (G3 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 3 = getr regs0 3) by (rewrite E3; exact H3).
assert (G4 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 4 = getr regs0 4) by (rewrite E4; exact H4).
assert (G8 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 8 = getr regs0 2)
  by (rewrite E8, H8; unfold w64, spZ; apply Z_to_bv_bv_unsigned).
assert (G21 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 21 = w64 rv) by (rewrite E21; exact H21).
assert (G33 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 33 = getr regs0 1) by exact (EX 0%nat ltac:(lia)).
assert (G34 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 34 = getr regs0 8) by exact (EX 1%nat ltac:(lia)).
assert (G35 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 35 = getr regs0 9) by exact (EX 2%nat ltac:(lia)).
assert (G36 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 36 = getr regs0 18) by exact (EX 3%nat ltac:(lia)).
assert (G37 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 37 = getr regs0 19) by exact (EX 4%nat ltac:(lia)).
assert (G38 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 38 = getr regs0 20) by exact (EX 5%nat ltac:(lia)).
assert (G39 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 39 = getr regs0 21) by exact (EX 6%nat ltac:(lia)).
assert (G40 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 40 = getr regs0 22) by exact (EX 7%nat ltac:(lia)).
assert (G41 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 41 = getr regs0 23) by exact (EX 8%nat ltac:(lia)).
assert (G42 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 42 = getr regs0 24) by exact (EX 9%nat ltac:(lia)).
assert (G43 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 43 = getr regs0 25) by exact (EX 10%nat ltac:(lia)).
assert (G44 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 44 = getr regs0 26) by exact (EX 11%nat ltac:(lia)).
assert (G45 : ew (ve_E regs regs0 (flag_addr ly 0 pos)) 45 = getr regs0 27) by exact (EX 12%nat ltac:(lia)).
clear E3 E4 E8 E18 E21 E24 E26 E32 EX.
remember (ve_E regs regs0 (flag_addr ly 0 pos)) as E eqn:HE.
unfold YK0s.ret_ok in HRA.
replace (w64 (A_prog_sigma AS_parse_value + VE_EPI)) with (Z_to_bv 64 (BASE + VE_PC))
  by (unfold w64, VE_PC; f_equal; change BASE with A_prog_base; lia).
(* the run, rows 225..265: a closed term *)
let r := eval vm_compute in (sym_runN_pi_tok (@pl_tpi A_prog_listing PL_prog_A) (@pl_tw A_prog_listing PL_prog_A)
                               512%nat ve_Bx ve_Bspan ve_SH FUEL ve_ss) in
lazymatch r with (?st', ?rs) =>
  assert (Hrun : sym_runN_pi_tok (@pl_tpi A_prog_listing PL_prog_A) (@pl_tw A_prog_listing PL_prog_A)
                   512%nat ve_Bx ve_Bspan ve_SH FUEL ve_ss = (st', rs)) by (vm_compute; reflexivity)
end.
assert (HK : (A_LIM <= 512)%nat) by (unfold A_LIM; lia).
assert (Hstat : sh_static_ok 512 ve_Bx ve_Bspan ve_SH (ss_facts ve_ss) (ss_mem ve_ss) = true)
  by (vm_compute; reflexivity).
(* the release rule over the journal's relation wle' segs RZ_cf: the goal's SRr' is SRrG at that relation *)
unfold SRr'.
refine (@aj_flag_store_x_invR fxj rc SK SEGS B prh_pst ARx _ LAWS (@pa_segs_low _ A_prog_listing PI_prog_A) ASFX FFLX SFX
  asym (@pa_wx _ A_prog_listing PI_prog_A) (clookup (@pa_tbl _ A_prog_listing PI_prog_A))
  (@pa_val _ A_prog_listing PI_prog_A) (@pa_sigma _ A_prog_listing PI_prog_A) A_prog_listing
  (@pl_tpi A_prog_listing PL_prog_A) (@pl_tw A_prog_listing PL_prog_A)
  (pa_fetch_ok (L := A_prog_listing) (PI := PI_prog_A)) (@pa_cert _ A_prog_listing PI_prog_A)
  (@pa_B_ok _ A_prog_listing PI_prog_A) A_LIM A_LIM_text (@pl_lim A_prog_listing PL_prog_A)
  (@pl_len A_prog_listing PL_prog_A) (@pl_tpi_eq A_prog_listing PL_prog_A) (@pl_tw_eq A_prog_listing PL_prog_A)
  P PLAW (wle' SEGS YGcfRehidePost.RZ_cf)
  W FUEL E 512%nat ve_Bx ve_Bspan ve_SH ve_ss _ _ _ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
  ly0 S0 Hp0 W0 mem0 md0 [] ly S Hp md k 0 pos _ HK HEI ltac:(lia) HS SHOK Hstat Hrun I HJ HPM _ _ _ _).
- (* no shadow obligation: the tail runs no instrumented check *)
  cbn [sh_obls]. apply Forall_nil.
- (* every byte the run writes: the header word and the eight shadow bytes are this call's own frame (in_frames),
     the last is the flag byte *)
  intros a Ha.
  destruct (ve_wrange E a (frame_addr ly 0 pos) (SHADOW_OFF + frame_addr ly 0 pos / 8) (flag_addr ly 0 pos)
              UF USH UFL Ha) as [Hh|[Hs|Hf]].
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists 0, pos.
    split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd]. rewrite HFB64. lia.
  + left. unfold awr_byte. right; right; right. unfold in_frames. exists 0, pos.
    split; [left; reflexivity|]. right. unfold in_zr, shadow_addr. cbn [fst snd]. rewrite HFB64.
    change (64 / 8) with 8. lia.
  + right. exact Hf.
- (* the flag byte is 0 at the end of the run: the last region's one chunk *)
  intros ws msr Hlen HS'.
  cbn [sh_j] in Hlen. destruct ws as [|w ws]; [|discriminate Hlen].
  cbn [extK] in HS'.
  pose proof (st_ok_mem_ok SEGS _ _ _ HS') as (_ & HRS & _).
  lazymatch type of HRS with Forall _ ?rs0 => let rs1 := eval vm_compute in rs0 in change rs0 with rs1 in HRS end.
  do 4 apply Forall_inv_tail in HRS. apply Forall_inv in HRS.
  pose proof (vep_region_chunks HRS) as HCk. clear HRS.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val] in HCk.
  apply Forall_inv in HCk.
  destruct (HCk 0 ltac:(cbn; lia)) as (b & Hb & Hm).
  cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as Hb. subst b.
  rewrite UFL, !Z.add_0_r in Hm. rewrite Hm. f_equal; apply bv_eq; vm_compute; reflexivity.
- (* the return, the post, and P: the `ret` keeps the memory the run ended with *)
  intros ws ms' mat' Hlen HEI' HS' SHOK' HJ' HPM' HF HFr HG.
  cbn [sh_j] in Hlen. destruct ws as [|w ws]; [|discriminate Hlen].
  cbn [extK] in HS', SHOK', HEI'.
  cbn [ms_mem mkst] in HF, HFr, HG.
  pose proof (ajxR_frs HJ') as Hfrs'.
  assert (R1 : getr (ms_regs ms') 1 = getr regs0 1) by (ve_fin HS'; exact G33).
  assert (R10 : getr (ms_regs ms') 10 = w64 rv) by (ve_fin HS'; exact G21).
  assert (HAP : aregs_preserved regs0 (ms_regs ms')).
  { unfold aregs_preserved, acallee_saved. intros r Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
    ve_fin HS';
    rewrite ?G3, ?G4, ?G8, ?G34, ?G35, ?G36, ?G37, ?G38, ?G39, ?G40, ?G41, ?G42, ?G43, ?G44, ?G45;
    f_equal; apply bv_eq; reflexivity. }
  (* the `ret` keeps the world: its SRr step lifts to the relation wle' segs RZ_cf *)
  apply (SRr_SRrG SEGS (wle' SEGS YGcfRehidePost.RZ_cf) (wle_wle' SEGS YGcfRehidePost.RZ_cf)).
  eapply (paj_ret_at (fx := fxj) (L := A_prog_listing) (PL := PL_prog_A) (PI := PI_prog_A) W E _ ms' _ _ HS' eq_refl
            ltac:(vm_compute; reflexivity)).
  intros mat2.
  split; [|exact HPM'].
  unfold fpostWFR.
  exists fxj, ly, (stack_free_state 0 pos S), Hp, (ms_regs ms'), (ms_mem ms'). eexists. exists k.
  split; [rewrite R1, HRA; reflexivity|].
  split; [exact HFRM|]. split; [exact HFRK|].
  split; [apply (ajournal_x_materializeR SEGS B prh_pst ARx LAWS (@pa_segs_low _ A_prog_listing PI_prog_A));
          exact HJ'|].
  split.
  { intros a Ha Hfp. rewrite <- (HWIN a Ha Hfp). apply (aview_eq_of SEGS). apply HFr.
    rewrite unsigned_lit_small by lia. intros Hw.
    destruct (ve_wrange E a _ _ _ UF USH UFL Hw) as [Hh|[Hs|Hf]]; unfold SHADOW_OFF in *; lia. }
  split; [exact HAP|].
  apply HQ; [exact R10 | exact HAP | exact Hfrs' |].
  intros a Ha Hnf Hnfl. apply (aview_eq_of SEGS). apply HFr. rewrite unsigned_lit_small by lia. intros Hw.
  destruct (ve_wrange E a _ _ _ UF USH UFL Hw) as [Hh|[Hs|Hf]].
  + apply Hnf. unfold in_frames. exists 0, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
    rewrite HFB64. lia.
  + apply Hnf. unfold in_frames. exists 0, pos. split; [left; reflexivity|]. right. unfold in_zr, shadow_addr.
    cbn [fst snd]. rewrite HFB64. change (64 / 8) with 8. lia.
  + exact (Hnfl Hf).
Qed.

(* ---- VrdEpiA.vrd_epi_step with P: an arm that reaches row 225 in VrdNum.vrd_epi_aR at wle' segs RZ_cf (its run
   crossed a free: the container arm, after parse_items) with P of the join memory meets the BUDGETED post fpostWFb
   at the text's budget wbudget CW 0, under SRr' segs RZ_cf, and P holds of the memory at the return. The budget
   bridge is VrdEpiA.vrd_epi_step's over R (ajournal_xw_rebaseR to the join's depot, vrd_epi_holds_P there,
   ajournal_xw_unbase0R back at the WS the join names); the join is read BY NAME through VrdNum's record vrd_epi_R
   (vrd_epi_R_of, then its vepi_* projections), fpostWFR through VrdEpiA's shape guard vfpwR. Both implicit float
   states pinned to the Section's fx, the join's is the explicit fx2. ---- *)
Theorem vrd_epi_step_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws SEGS P ->
  forall (fx2 : YK11.FPState) (d : nat) (CW : list (list Z)) (e q v : Z)
    (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world SEGS) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (pos rv : Z)
    (RQ : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Prop)
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (W : world SEGS) (c : config),
  104 <= STK_parse_value d ->
  (forall (ly : alayout) (S : astate) (Hp : list Z) (mem : word -> option byte)
          (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     RQ ly S Hp W mem ->
     getr regs' 10 = w64 rv -> aregs_preserved regs0 regs' ->
     frames (stack_free_state 0 pos S) = frames S0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ in_frames ly [(0, pos)] a -> a <> flag_addr ly 0 pos ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     Q ly (stack_free_state 0 pos S) Hp W regs' mem' md') ->
  VrdNum.vrd_epi_aR (fx := fx) B ARx SK (wle' SEGS YGcfRehidePost.RZ_cf) fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0
    pos rv RQ W c ->
  P (ms_mem (cfg_ms c)) ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c
    (fun W' c' => fpostWFb (fx := fx) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_value d) e (rd_fp q v)
                    regs0 ly0 S0 Hp0 W0 mem0 md0 Q W' c' /\
                  P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ Q W c H104 HQ HD HPM.
apply vrd_epi_R_of in HD. destruct HD as (regs & mem & md & ly & S & Hp & k & HR).
pose proof (vepi_cfg HR) as Ec. subst c.
destruct (vepi_jrn HR) as (WS & HJ & HWB).
pose proof (vepi_win HR) as HWIN. pose proof (vepi_s0 HR) as H8. pose proof (vepi_s2 HR) as H18.
pose proof (vepi_s10 HR) as H26. pose proof (vepi_s8 HR) as H24. pose proof (vepi_s5 HR) as H21.
pose proof (vepi_gp HR) as H3. pose proof (vepi_tp HR) as H4. pose proof (vepi_ra HR) as HRA.
pose proof (vepi_saved HR) as HSAV. pose proof (vepi_flag HR) as HFLG. pose proof (vepi_frm HR) as HFRM.
pose proof (vepi_fregs HR) as HFRK. pose proof (vepi_rq HR) as HRQ.
pose proof (ajxR_wild HJ) as HWild.
apply (YCbqGwild.ajournal_xw_rebaseR SEGS B prh_pst ARx) in HJ.
eapply (SRr'_mono SEGS YGcfRehidePost.RZ_cf).
- exact (vrd_epi_holds_P P PLAW d fx2 ly0 (set_depot (st_depot S) S0) Hp0 W0 regs0 mem0 md0
    ly S Hp W regs mem md e q v pos rv k Q H104 HJ HWIN H8 H18 H26 H24 H21 H3 H4 HRA HSAV HFLG HFRM HFRK
    (fun regs' mem' md' H10 HAP HFR HMEM => HQ ly S Hp mem regs' mem' md' HRQ H10 HAP HFR HMEM) HPM).
- intros W' c' _ (HP & HPm). split; [|exact HPm].
  destruct (vfpwR B ARx SK HP) as (fx' & ly' & S' & Hp' & regs' & mem' & md' & k' & Ec & HFZ & HFK & HJ' & HW' & HAP &
    HQ').
  exists fx', ly', S', Hp', regs', mem', md', k', WS.
  split; [exact Ec|]. split; [exact HFZ|]. split; [exact HFK|]. split; [exact HWB|].
  split; [eapply (YCbqGwild.ajournal_xw_unbase0R SEGS B prh_pst ARx); [exact HJ' | exact HWild]|].
  split; [exact HW'|]. split; [exact HAP|]. exact HQ'.
Qed.

(* ---- the P := True instance: its statement is VrdEpiA.vrd_epi_step's, word for word (a join at wle, lifted to the
   R form by VrdEpiA.vrd_epi_a_wle') ---- *)
Lemma vrd_true_laws_epi : srr_inv_laws SEGS (fun _ => True).
Proof. split; intros; exact I. Qed.

Theorem vrd_epi_step_true :
  forall (fx2 : YK11.FPState) (d : nat) (CW : list (list Z)) (e q v : Z)
    (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world SEGS) (regs0 : bvmap 5 word)
    (mem0 : word -> option byte) (md0 : Model) (pos rv : Z)
    (RQ : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Prop)
    (Q : alayout -> astate -> list Z -> world SEGS -> bvmap 5 word -> (word -> option byte) -> Model -> Prop)
    (W : world SEGS) (c : config),
  104 <= STK_parse_value d ->
  (forall (ly : alayout) (S : astate) (Hp : list Z) (mem : word -> option byte)
          (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     RQ ly S Hp W mem ->
     getr regs' 10 = w64 rv -> aregs_preserved regs0 regs' ->
     frames (stack_free_state 0 pos S) = frames S0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ in_frames ly [(0, pos)] a -> a <> flag_addr ly 0 pos ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) mem a) ->
     Q ly (stack_free_state 0 pos S) Hp W regs' mem' md') ->
  vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ W c ->
  SRr' SEGS YGcfRehidePost.RZ_cf W c
    (fpostWFb (fx := fx) B ARx SK (YCbqGwild.wbudget CW 0) (STK_parse_value d) e (rd_fp q v) regs0
       ly0 S0 Hp0 W0 mem0 md0 Q).
Proof.
intros fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ Q W c H104 HQ HEA.
eapply (SRr'_bind SEGS YGcfRehidePost.RZ_cf).
- exact (vrd_epi_step_P (fun _ => True) vrd_true_laws_epi fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv RQ Q W c
           H104 HQ (vrd_epi_a_wle' B ARx SK HEA) I).
- intros W' c' _ (HF & _). apply (SRr'_ret SEGS YGcfRehidePost.RZ_cf). exact HF.
Qed.

End c.

(* acceptance checks, printed into the build log *)
Print Assumptions aj_flag_store_x_inv.
Print Assumptions aj_flag_store_x_invR.
Print Assumptions vrd_epi_holds_P.
Print Assumptions vrd_epi_step_P.
Print Assumptions vrd_epi_step_true.
Set Printing All.
Check @vrd_epi_step_P.
Unset Printing All.
