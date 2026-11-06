(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* omx-clap-core/fuzz_preset, support for segment L6x of image A''s LLVMFuzzerTestOneInput (pin sha256
   1be0f53d96cb9d6c2d5c92820c254e9db28e4830054a02631390e27c9547dc44; lib/A/Prog/Ent102L6A.v): the FLAG-STORE RULE
   WITH A RUN INVARIANT. A function that releases its own ASan fake frame inline in its epilogue (`ld a0, (frame slot);
   sb zero, 0(a0)`) writes 0 to the frame's flag byte; the journal moves from own = (cid, pos) :: own' to own' at the
   allocator state stack_free_state cid pos Sc. The rule is lib/Reusable/YGcallSx.v aj_flag_store_x (blob
   17d7d2cdbcd1, :248-335), restated with a memory invariant P carried across the run in the form of YC80x.v's
   run-invariant runners (srr_inv_laws, SRr_msteps_inv; the engine set of record, YSRrMemnorm.v's memnorm instance
   srr_inv_laws_memnorm_k is the P the lane takes). The only change to the proof: SRr_msteps -> SRr_msteps_inv, with
   P on the start memory (a premise after the journal) and on the end memory (a premise of the continuation, after
   the journal), as YC80x.v's _inv twins place it.
   PORTED FROM (by path, image-free): lib/B/Prog/EntS7FlagB.v of a working branch c3e54cc5ad62 (the
   lane's own flag rule at the old pins), here replaced by the engine's aj_flag_store_x.
   Generic: no image class instance, no address, no ledger, no ARcf; the Section hypotheses are YGcallSx.v's.
   rule 24: proves function LLVMFuzzerTestOneInput, segment L6x (reuse search: main / ossv/recipes / ossv/candidates /
   release/pau-projects-recipes + the internal lemma index / `proof-index LLVMFuzzerTestOneInput` exit=0, output
   the lane's index output, the internal file idx-llvm-newpin.txt; checker R24CheckLLVMF CONFIRM; NEW walk on the #102 pins).
   This file: the support rule only (no function proved here).
   LISTING / STATEMENT / THE KIT TEXTS: none read here (the lane file names lib/A/Listing_prog.v 7ed1529926bd,
   lib/A/Ent102CutsA.v f40892fb5ddb, lib/A/PRH_FnPj.v 79e2637972c6, lib/A/PRH_Base.v 48ee9034967e).
   Numerals: 0 (the flag value), 8 (byte width), 64 / 2 ^ 64 (word width / range), 2 ^ 40 (code-span bound,
   YC80x.v's): LENGTH / DERIVED. No ADDRESS. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbq YCbqG YGcallx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0s YG0q YG0t YF0v FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YP0a YP0d YP0c YC80x.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Local Notation AJ := (ajournal_x segs B PST ARx).
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis segs_low : forall a, in_img segs a -> 0 <= a < kLowMemEnd.
(* YGcallSx.v:214-226, verbatim: the free law, the flag facts and the model's stack_free post, in ARx form *)
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

(* YGcallSx.v aj_flag_store_x with the invariant P, OVER A WORLD RELATION R (the re-hiding move: a lane after a
   free runs at wle'): the journal and the continuation at R (YCbqG.ajournal_xR, YA0nH.SRrG); a run keeps the world, so the
   proof is the plain one over the engine's R forms (YC80x.SRr_msteps_invR, YCbqG.awr_byte_cases_xR /
   ajournal_x_after_writeR). A COPY beside the plain lemma below, which keeps its own proof. *)
Lemma aj_flag_store_x_invR : forall (R : world segs -> world segs -> Prop)
  W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q,
(A_LIM <= K)%nat -> img_env E -> 0 <= cid ->
st_ok_pi E ss (restrict (w_H W) ms) ->
sh_ok segs Bx SH E (mrestrict (w_H W) (ms_mem ms)) ->
sh_static_ok K Bx Bspan SH (ss_facts ss) (ss_mem ss) = true ->
sym_runN_pi_tok tpi0 tw0 K Bx Bspan SH n ss = (st', r) ->
match r with PTS_call _ => False | PTS_ecall => False | _ => True end ->
ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W (ms_mem ms) mdc k ->
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
  ajournal_xR segs B PST ARx R STK sp0 FP ly S Hp W0 mem md own' lyc (stack_free_state cid pos Sc) Hpc W (ms_mem ms')
    (with_vm_backing (m_vm_lazy mdc) mat' mdc) k ->
  P (ms_mem ms') ->
  frame_of E (ss_mem ss) (ms_mem ms) (ms_mem ms') ->
  frame_of E (ss_mem ss) (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms')) ->
  SRrG segs R W (mkCfg ms' (with_vm_backing (m_vm_lazy mdc) mat' mdc)) Q) ->
SRrG segs R W (mkCfg ms mdc) Q.
Proof.
intros R W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q
HK HE Hcid HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hflag0 Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
  HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
assert (HS' : st_ok_pi (extK E K ws) (sh_ss st') msr') by (destruct r; cbn [ptok_post] in HP; first [exact HP | destruct Hr | destruct HP]).
clear HP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFLX lyc Sc Hpc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfo & Hfr_rng).
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
  + pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact (proj1 HQT)].
  + first [reflexivity | unfold stack_free_state; cbn; reflexivity | destruct Sc; reflexivity].
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.
(* YGcallSx.v aj_flag_store_x with the invariant P: P (ms_mem ms) after the journal premise, P (ms_mem ms') after
   the journal premise of the continuation *)
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
Proof.
intros W n E K Bx Bspan SH ss st' r ms STK sp0 FP ly S Hp W0 mem md own' lyc Sc Hpc mdc k cid pos Q
HK HE Hcid HS Hsh Hchk Hrun Hr HJ HPm Hobl Hwr Hflag0 Hk.
rewrite <- Htpi, <- Htw in Hrun.
destruct (sym_run_pi_tok_sound psym segs fetch val sigma listing Hfetch Hcert HB A_LIM HLIM0 HLIM HLEN K Bx Bspan SH HK n E ss _ st' r
  HE HS Hsh Hchk Hrun Hobl) as (ws & msr' & Hlen & Hms & HE' & HP & Hsh' & _ & Hfr).
assert (HS' : st_ok_pi (extK E K ws) (sh_ss st') msr') by (destruct r; cbn [ptok_post] in HP; first [exact HP | destruct Hr | destruct HP]).
clear HP.
pose proof HJ as (HAR & Hly & Hsecs & Hwle & Hio & Hfrs & Hnev & Hkk & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct (FFLX lyc Sc Hpc W (ms_mem ms) mdc cid pos HAR Hin) as (Hfo & Hfr_rng).
apply (SRr_msteps_inv segs Hwx P PLAW W ms msr' mdc Q Hms HPm).
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
    exact (proj1 (awr_byte_cases_x segs B PST ARx LAWS _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ a HJ Hw) Ho).
  - intros a Hv. eapply aview_keeps_vis; [exact Hgr' | exact Hv].
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - rewrite Emd. destruct mdc as [f [mp lz mt] io fs pr li ti sg sc]; reflexivity.
  - intros a _ Hh. subst memc'. cbn [unrestrict ms_mem]. unfold munrestrict. rewrite Hh. reflexivity. }
apply (Hk ws (unrestrict (w_H W) (ms_mem ms) msr') (m_vm_materialized model') Hlen HE').
- rewrite Hrr. exact HS'.
- subst memc'. rewrite Hmm. exact Hsh'.
- eapply (ajournal_x_after_write segs B PST ARx LAWS segs_low STK sp0 FP ly S Hp W0 mem md ((cid, pos) :: own') lyc Sc Hpc W
    (ms_mem ms) mdc k memc' _ (in_wrange E (ss_mem ss)) (stack_free_state cid pos Sc) Hpc own' HJ Heqw
    ltac:(intros a Ha; eapply apresent_grows; [exact Hgr' | exact Ha]) Hsame').
  + intros a Ha. destruct (Hwr a Ha) as [Hw | ->]; [left; exact Hw | right; split; [exact Hfo | exact Hfr_rng]].
  + exact HAR'.
  + unfold ablocks. rewrite blocks_stack_free_state. reflexivity.
  + reflexivity.
  + cbn. zlia.
  + etransitivity; [exact E2 | symmetry; exact E1].
  + pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HQT).
    apply (qtight_ext Sc); [reflexivity | reflexivity | reflexivity | exact (proj1 HQT)].
  + first [reflexivity | unfold stack_free_state; cbn; reflexivity | destruct Sc; reflexivity].
- exact HPm'.
- cbn [unrestrict ms_mem]. apply frame_of_unrestrict. exact Hfr.
- exact Hfr'.
- exact Hgr'.
Qed.
End e.
End x.
