(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v (entry state, region and fact proofs, the run/branch loop and its leaf) with the caller-journal leaf of lib/A/ACeu.v rfc_A_ok, aview_frame_off of lib/A/AD28.v (as kept_step) and frm_off_img of lib/A/ACeh.v (as frame_not_img) at c8557374ad2e to libreac/fuzz_knock: lib_asan3_0_listing -> knock_asan_listing, AF_asan3_cmpPixel -> AF_asan_reac_knock_step, tcmp_spec / tcmp_post -> tknock_step_specX / kn_post_step of lib/A/APgCSpec.v, cmp_entry / cmp_regions / cmp_facts / ss_cmp / cmp_SH / cmp_extra / EC / CBx / CBspan / pb_cmpPixel -> step_entry / step_regions / step_facts / ss_step / step_SH / step_extra / EK / KBx / KBspan / pb_knock_stepX; constants: TCMP_STK 16 + ESTACK -> T_step_STK 16, shadow-base atom 42 -> 39, GOT shadow slot / shadow-base cell A_OBJ 0 / A_OBJ 12 -> A_OBJ 1 / A_OBJ 7 (lib/Reusable/YC1f.v got_regionP / bcell_regionP / PALib), image bounds only through lib/Reusable/YImgTop.v (knock's 0x10000 .. 0x5f3000); the struct kp lies in a caller frame (cid, pos) of any class, written through awr_byte's in_frames case by In (cid, pos) own. *)
(* Modified by Theorem Labs, 2026-10: made from proofs/reac-pw/fuzz_qdisc/lib/A/QPgCheck.v at 236fd9c95ca (itself made from proofs/libreac/fuzz_knock/lib/A/APgStep.v at origin/ossv/recipes 6ebe35ba632: the save-slot region, its write obligation awr_stk / kwr_stk, the run / keep / leaf chain) with the kit-only plumbing of lib/A/RPgCfgChanges.v at 964efd2f474 (the image's own code table, cfg_wx / cfg_segs_low, kept_run, the leaf into lib/A/RPgCSpec.v's rl_post) for reac-pw/fuzz_role's image A (fuzz_role.asan): it walks check_absent 0x82bb4, check_role 0x82bdc and check_malformed 0x82c04 against rl_check_absent_specX / rl_check_role_specX / rl_check_malformed_specX on the concrete image lib/A/Img0.v rsegs; the entry state carries the registers the contract fixes (a0, a1, and a2 = a1 for check_role) as literals or as the atom they equal, so the engine decides every abort branch itself; qdisc's divisor-constant region, its arithmetic lemmas and its branch splits are dropped. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgCheck.v at 77f59d02b018 for reac-pw/fuzz_rate's
   image A (fuzz_rate.asan): module paths changed; the image is images.Asan's loaded segments instead of a lib/A/Img0
   module; the contracts are lib/A/RtPgCSpec.v's rt_check_absent_specX / rt_check_rate_specX / rt_check_malformed_specX
   (rt_cpre / rt_cpost, the same texts as role's rl_pre / rl_post) at rate's addresses; check_absent's and
   check_malformed's second literal is 0x5a5a5a5a (`lui` + `addiw`) where role's is 0x5a; check_decide (a0 = a1, the
   override a1 := the atom of a0) is added; the code table covers the four functions; the call-cut plumbing of
   proofs/reac-pw/fuzz_role/lib/A/RPgCheckStr.v at 77f59d02b018 (cs_eq, cs_eq_trans, cs_eq_of_pres, cs_eq_of_st_ok,
   sp_of_st_ok, L_ANS, L_ANS_cs, pres_of_cs) is added for the walks with a call. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgCheck.v; 692 of its 736 lines of code are new or changed and 246 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_rate/lib/A/RtPgEnt0Hd.v, with its module paths and module names changed; 145 of its 173 lines of code are new or changed and 708 lines of the source are left out. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the walk piece "ent_build C"
   of LLVMFuzzerTestOneInput (0x80bc0) as lib/A/HPgSeg.v states it (hs_piece_W6c_stmt), from the three block
   statements of lib/A/HPgW6cBase.v (w6c_case_stmt 6, 7, 8). Proves no function (kind: segment lemma).

   HOW. At the case entry the cut hs_cut_D gives, through lib/A/HPgEntBCut.v's eb_D_facts and eb_D_input, every fact
   of w6c_ctx and w6c_in_D but two: the tables' shadow (hs_glob_now below, from hd_seg_pre's hi_globs
   clause) and the frame's distance from the tables (the client-image law AR_client_img_law: a frame never meets
   the image). The block's post w6c_jpost at J is what lib/A/HPgEntBCut.v's eb_J_of turns into hs_cut_J, with the
   pod Model.ent_build makes of the turn's input (w6c_build_kind: these cases read the kind byte only through
   kind % 10) and the cursor moved by what the turn read (w6c_ent_rest). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgMem HPgSteps HPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgEntBCut HPgW6cKit HPgW6cTail HPgW6cBase.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

(* ---- the model side ---- *)
Local Ltac w6c_rest_step :=
  repeat match goal with
  | |- context [Cursor.fuzz_u8 ?i] => let E := fresh in pose proof (fuzz_u8_rest i) as E;
       destruct (Cursor.fuzz_u8 i) as [? ?]; cbn [snd] in E
  | |- context [Cursor.fuzz_u16 ?i] => let E := fresh in pose proof (fuzz_u16_rest' i) as E;
       destruct (Cursor.fuzz_u16 i) as [? ?]; cbn [snd] in E
  | |- context [Cursor.fuzz_u32 ?i] => let E := fresh in pose proof (fuzz_u32_rest' i) as E;
       destruct (Cursor.fuzz_u32 i) as [? ?]; cbn [snd] in E
  | |- context [Cursor.fuzz_take ?n ?i] => let E := fresh in pose proof (fuzz_take_rest n i) as E;
       destruct (Cursor.fuzz_take n i) as [? ?]; cbn [snd] in E
  end.
(* every case reads only after the kind byte *)
Lemma w6c_ent_rest : forall c r, is_rest (snd (w6c_ent c r)) r.
Proof.
intros c r. unfold w6c_ent, ent_build, ent_headamp_key. cbn [Cursor.fuzz_u8].
destruct (Z.to_nat (bv_unsigned (Z_to_bv 8 c) mod 10)) as [|[|[|[|[|[|[|[|[|k]]]]]]]]]; w6c_rest_step;
  repeat (match goal with |- context [if ?b then _ else _] => destruct b end; w6c_rest_step);
  cbn [snd]; eauto 6 using is_rest_trans, is_rest_refl.
Qed.
Lemma w6c_ent_len : forall c r, (length (snd (w6c_ent c r)) <= length r)%nat.
Proof. intros c r. destruct (w6c_ent_rest c r) as [j Hj]. rewrite Hj, length_skipn. lia. Qed.

Lemma w6c_pc_D : forall kd, In (kd mod 10) [6; 7; 8] -> hs_pc_D kd = w6c_pc (kd mod 10).
Proof. intros kd Hin. unfold hs_pc_D, w6c_pc. cbv [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; rewrite <- E; reflexivity. Qed.

(* the two tables lie in the image *)
Lemma w6c_tbl_img : forall a, W6C_T6 <= a < W6C_T8 + 16 -> in_img rsegs a.
Proof.
intros a Ha.
assert (HB : existsb (fun s : Segment => (Z.of_N (seg_base s) <=? W6C_T6) &&
  (W6C_T8 + 16 <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))) rsegs = true) by (vm_compute; reflexivity).
apply existsb_exists in HB as (sg & Hsg & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2.
exists sg. split; [exact Hsg | lia].
Qed.

(* the registers eb_J_of asks kept are w6c_keep *)
Lemma w6c_keep_Z : forall (regs2 regs3 : bvmap 5 word), (forall r, In r w6c_keep -> getr regs3 r = getr regs2 r) ->
forall rg : Z, In rg [2; 3; 4; 8; 9; 18; 19; 21; 22; 23; 26; 27] -> getr regs3 (Z_to_bv 5 rg) = getr regs2 (Z_to_bv 5 rg).
Proof.
intros regs2 regs3 Hk rg Hrg. apply Hk. cbv [In] in Hrg.
repeat (destruct Hrg as [<-|Hrg];
  [cbv [w6c_keep In]; repeat (first [left; apply bv_eq; reflexivity | right]) |]).
destruct Hrg.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Local Arguments x_STK {segs} _. Local Arguments x_sp0 {segs} _. Local Arguments x_FP {segs} _.
Local Arguments x_ly {segs} _. Local Arguments x_S {segs} _. Local Arguments x_W0 {segs} _.
Local Arguments x_mem0 {segs} _. Local Arguments x_md0 {segs} _. Local Arguments x_own {segs} _.
Local Arguments x_k {segs} _. Local Arguments x_regs {segs} _. Local Arguments x_lyc {segs} _.
Local Arguments x_Sc {segs} _. Local Arguments x_W {segs} _. Local Arguments x_memc {segs} _.
Local Arguments x_mdc {segs} _. Local Arguments x_RLO {segs} _. Local Arguments x_RHI {segs} _.
Local Arguments x_e {segs} _. Local Arguments x_pos {segs} _.

(* a registered global's bytes at a cut: marked usable as at the start (hd_seg_pre's hi_globs clause); their shadow
   bytes are in the low shadow band, apart from everything a cut may have written *)
Lemma hs_glob_now : forall cx ly2 S2 W2 regs2 mem2 md2 x n,
hs_pre rsegs B cx (hi_shA headamp_himg_A) -> hs_core rsegs B MT cx (hs_E1 rsegs cx) ly2 S2 W2 regs2 mem2 md2 ->
In (x, n) (hi_globs headamp_himg_A) ->
range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF x n.
Proof.
intros cx ly2 S2 W2 regs2 mem2 md2 x n HP HC Hin.
pose proof (hs_core_kept rsegs B MT cx ly2 S2 W2 regs2 mem2 md2 HP HC) as HK.
assert (Hg : range_addressable (aview rsegs (w_H (x_W cx)) (x_memc cx)) SHADOW_OFF x n).
{ pose proof HP as HP'. unfold hs_pre, hd_seg_pre in HP'.
  destruct HP' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HG & _).
  exact (proj1 (Forall_forall _ _) HG (x, n) Hin). }
assert (Hb : 0 <= x /\ x + n <= kLowMemEnd).
{ assert (HB : forallb (fun g => (0 <=? fst g) && (fst g + snd g <=? kLowMemEnd)) (hi_globs headamp_himg_A) = true)
    by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) HB (x, n) Hin) as H. cbn [fst snd] in H.
  apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
apply (hm_ra_kept_wr rsegs (hs_wr rsegs cx) _ _ _ _ SHADOW_OFF x n Hg HK).
intros y Hy. apply (hs_wr_shadow rsegs B); [exact HP | unfold kLowMemEnd, kHighMemEnd in *; lia |].
apply (range_addressable_sub _ _ x n); [exact Hg | lia | lia].
Qed.

Theorem w6c_piece_of : w6c_case6_stmt B -> w6c_case7_stmt B -> w6c_case8_stmt B -> hs_piece_W6c_stmt rsegs B MT.
Proof.
intros C6 C7 C8. unfold hs_piece_W6c_stmt. intros cx POST rest i k kd HST Hkd HFJ.
unfold hs_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hps Hes HD.
pose proof asan_consts as (Hceil & _).
pose proof (eb_D_facts B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
  (HJ & R2 & R3 & R4 & R9 & R23 & R24 & R14 & R25 & R21 & R27 & V20 & V70 & V80 & Vb0 & Vc0 & Vf0 & Vf8
   & BR1 & BR2 & BR3 & BR4 & BR5 & Hown & HinF & EF2 & HF1 & HF2 & HF32 & HFapp & Hpp & Hpp1 & Hpp2 & Hsep
   & Hc1 & Hc2 & Ez & HFp & HraE & Hpres & HFSHD & HromD).
pose proof (eb_D_input B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 HST HD) as
  (Hg & Hra & Hhull & Hamr & Hdis).
pose proof HST as (HPRE & _).
pose proof HD as (HPB & HAT & HFSH & HPP & HE0 & Hsrr & Hfu & Hkd0 & Hrr).
pose proof HPB as (HCORE & _).
set (R := e_R (x_e cx)) in *. set (F := e_F (x_e cx)) in *. set (cur := hs_cur rsegs cx rest r) in *.
set (sa := shadow_addr (e_pp (x_e cx) + 0x4000)) in *.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
(* the cell R+0x18 *)
assert (V0 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0x18) 8 0x15555556).
{ assert (Hin : In (LCell XR 0x18, 0x15555556) (hs_L_D rsegs cx sh np ps cnt es rest r kd)).
  { cbn [hs_L_D hs_L_Dc hs_L_Dc0 hs_Rc0 hs_Kc app]. repeat (first [left; reflexivity | right]). }
  pose proof (eb_at _ _ _ _ _ _ _ HAT Hin) as H. cbn [hd_at hd_xv] in H. exact H. }
(* the tables *)
assert (HT6 : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF W6C_T6 16).
{ apply (hs_glob_now cx ly2 S2 W2 regs2 mem2 md2 W6C_T6 16 HPRE HCORE).
  cbn [hi_globs headamp_himg_A]. unfold headamp_A_globs, W6C_T6. repeat (first [left; reflexivity | right]). }
assert (HT8 : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF W6C_T8 16).
{ apply (hs_glob_now cx ly2 S2 W2 regs2 mem2 md2 W6C_T8 16 HPRE HCORE).
  cbn [hi_globs headamp_himg_A]. unfold headamp_A_globs, W6C_T8. repeat (first [left; reflexivity | right]). }
assert (HTF : forall a, W6C_T6 <= a < W6C_T8 + 16 -> ~ (F <= a < F + 1024)).
{ intros a Ha HaF. pose proof HJ as (HAR2 & _).
  pose proof (al_client_img _ _ (AR_laws_ok rsegs B) _ _ _ _ _ a HAR2) as Hcl.
  assert (HinF' : frame_addr ly2 4 (x_pos cx) <= a < frame_addr ly2 4 (x_pos cx) + fs_frame_bytes 4)
    by (rewrite <- EF2; change (fs_frame_bytes 4) with 1024; lia).
  apply (proj2 (Hcl (or_intror (or_introl (ex_intro _ 4 (ex_intro _ (x_pos cx) (conj HinF HinF'))))))).
  exact (w6c_tbl_img a Ha). }
(* the case *)
assert (CC : w6c_case_stmt B (kd mod 10)).
{ cbv [In] in Hkd. destruct Hkd as [E|[E|[E|[]]]]; rewrite <- E; assumption. }
rewrite (w6c_pc_D kd Hkd).
eapply SRr_bind.
{ apply (CC (x_STK cx) (x_sp0 cx) (x_FP cx) (x_ly cx) (x_S cx) (x_W0 cx) (x_mem0 cx) (x_md0 cx) (x_own cx) (x_k cx)
    ly2 S2 W2 mem2 md2 regs2 R F (x_pos cx) cur sa r).
  - split; [exact HJ|]. split; [|exact HromD].
    unfold w6c_geo. split; [exact BR4|]. split; [exact BR5|]. split; [exact BR2|].
    split; [unfold kHighMemBeg; rewrite HTS in *; lia|]. split; [exact Hown|]. split; [exact EF2|].
    split; [exact HFapp | exact HF32].
  - unfold w6c_in_D.
    assert (Hsa : 0 <= sa < 2 ^ 64).
    { unfold sa, shadow_addr, SHADOW_OFF. unfold Layout.PP_SIZE in Hpp2.
      pose proof (Z.div_pos (e_pp (x_e cx) + 0x4000) 8 ltac:(lia) ltac:(lia)).
      assert ((e_pp (x_e cx) + 0x4000) / 8 <= e_pp (x_e cx) + 0x4000) by (apply Z.div_le_upper_bound; lia). lia. }
    split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R9|]. split; [exact R23|].
    split; [exact R24|]. split; [exact R14|]. split; [exact R25|].
    split; [exact V0|]. split; [exact Vb0|]. split; [exact Hsa|]. split; [exact Vc0|]. split; [exact Vf0|].
    split; [exact Vf8|]. split; [exact HE0|]. split; [exact HFSHD|].
    split; [exact Hg|]. split; [exact Hra|]. split; [exact Hhull|]. split; [exact Hamr|].
    split; [lia|]. split; [lia|].
    split; [intros a Ha; destruct (Hdis a Ha) as (D1 & D2 & _); split; assumption|].
    split; [exact HT6|]. split; [exact HT8 | exact HTF]. }
cbv beta. intros W3 c3 _ (regs3 & mem3 & md3 & -> & -> & HJ3 & Hio3 & Hk3 & H20 & H25 & Hm3 & He3 & Hs3).
set (ed := fst (w6c_ent (kd mod 10) r)) in *. set (r' := snd (w6c_ent (kd mod 10) r)) in *.
assert (Hl : (length r' <= length r)%nat) by apply w6c_ent_len.
assert (Hed : (ed, r') = ent_build rr).
{ rewrite (w6c_build_kind rr kd r Hfu ltac:(exact Hrr) Hkd). unfold ed, r'. symmetry. apply surjective_pairing. }
pose proof (eb_J_of B MT cx rest sh np ps cnt es rr r kd ly2 S2 W2 regs2 mem2 md2 regs3 mem3 md3 ed r' HST HD HJ3 Hio3
  (w6c_keep_Z regs2 regs3 Hk3) H20) as HJof.
assert (H25' : getr regs3 25 = w64 (hs_cur rsegs cx rest r')).
{ rewrite H25. unfold cur, hs_cur. f_equal. lia. }
specialize (HJof H25').
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (R - T_SEG_STK <= a < R) ->
  ~ (R + 0x68 <= a < R + 0x70) -> ~ (R + 0x118 <= a < R + 0x120) -> ~ (F + 0xf0 <= a < F + 0x158) ->
  aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 _ H3 H4. apply Hm3; [exact Ha | unfold ESTACK in *; rewrite HTS in H1; lia | exact H4 | exact H3]. }
specialize (HJof K3).
assert (V3 : val_mem rsegs (mrestrict (w_H W2) mem3) (R + 0x118) 8 (Z.of_nat (length r'))).
{ rewrite Z.mod_small in Hs3; [exact Hs3|]. split; [lia|]. pose proof (w6c_ent_len (kd mod 10) r). unfold r'.
  assert (Z.of_nat (length r) <= 2 ^ 47) by lia. lia. }
specialize (HJof V3 He3 Hed).
change (cfg_at rsegs W6C_J regs3 mem3 md3) with (cfg_at rsegs HS_J regs3 mem3 md3).
exact (HFJ ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es rr r' ed Hps Hes HJof).
Qed.
End d.
End b.

Print Assumptions w6c_piece_of.
