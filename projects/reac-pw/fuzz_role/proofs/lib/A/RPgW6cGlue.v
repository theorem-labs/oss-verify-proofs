(* reac-pw/fuzz_role image A (fuzz_role.asan, pinned sha256
   614cffc0864cc31d9d1ced61322c4efd567b64bc89fe09a227a05b5126e0debb; every address measured on the unstripped twin
   6da77bafc5c050954dd89149e1e55a24064c2211e3cbd351822d1c0a20900ad6, same loaded bytes): the walk piece "ent_build C"
   of LLVMFuzzerTestOneInput (0x7ff88) as lib/A/RPgSeg.v states it (rs_piece_W6c_stmt), from the three block
   statements of lib/A/RPgW6cBase.v (w6c_case_stmt 6, 7, 8). Proves no function (kind: segment lemma).

   HOW. At the case entry the cut rs_cut_D gives, through lib/A/RPgEntBCut.v's eb_D_facts and eb_D_input, every fact
   of w6c_ctx and w6c_in_D but two: the tables' shadow (rs_glob_now of lib/A/RPgW6cKit.v, from rl_seg_pre's hi_globs
   clause) and the frame's distance from the tables (the client-image law AR_client_img_law: a frame never meets
   the image). The block's post w6c_jpost at J is what lib/A/RPgEntBCut.v's eb_J_of turns into rs_cut_J, with the
   pod Model.ent_build makes of the turn's input (w6c_build_kind: these cases read the kind byte only through
   kind % 10) and the cursor moved by what the turn read (w6c_ent_rest). *)
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import Img0 RPgBase RPgCSpec RPgImgA RPgMem RPgSteps RPgSeg.
From OSSVerify.Proofs.reac_pw.fuzz_role.lib.A Require Import RPgEntBCut RPgW6cKit RPgW6cTail RPgW6cBase.
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

Lemma w6c_pc_D : forall kd, In (kd mod 10) [6; 7; 8] -> rs_pc_D kd = w6c_pc (kd mod 10).
Proof. intros kd Hin. unfold rs_pc_D, w6c_pc. cbv [In] in Hin. destruct Hin as [E|[E|[E|[]]]]; rewrite <- E; reflexivity. Qed.

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

Theorem w6c_piece_of : w6c_case6_stmt B -> w6c_case7_stmt B -> w6c_case8_stmt B -> rs_piece_W6c_stmt rsegs B MT.
Proof.
intros C6 C7 C8. unfold rs_piece_W6c_stmt. intros cx POST rest i k kd HST Hkd HFJ.
unfold rs_from_D. intros ly2 S2 W2 regs2 mem2 md2 sh np ps cnt es rr r Hps Hes HD.
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
set (R := e_R (x_e cx)) in *. set (F := e_F (x_e cx)) in *. set (cur := rs_cur rsegs cx rest r) in *.
set (sa := shadow_addr (e_pp (x_e cx) + 0x4000)) in *.
assert (HTS : T_SEG_STK = 16384) by reflexivity.
(* the cell R+0 *)
assert (V0 : val_mem rsegs (mrestrict (w_H W2) mem2) (R + 0) 8 0x15555556).
{ assert (Hin : In (LCell XR 0x0, 0x15555556) (rs_L_D rsegs cx sh np ps cnt es rest r kd)).
  { cbn [rs_L_D rs_L_Dc rs_L_Dc0 rs_Rc0 rs_Kc app]. repeat (first [left; reflexivity | right]). }
  pose proof (eb_at _ _ _ _ _ _ _ HAT Hin) as H. cbn [rl_at rl_xv] in H. exact H. }
(* the tables *)
assert (HT6 : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF W6C_T6 16).
{ apply (rs_glob_now rsegs B MT cx ly2 S2 W2 regs2 mem2 md2 W6C_T6 16 HPRE HCORE).
  cbn [hi_globs role_himg_A]. unfold role_A_globs, W6C_T6. repeat (first [left; reflexivity | right]). }
assert (HT8 : range_addressable (aview rsegs (w_H W2) mem2) SHADOW_OFF W6C_T8 16).
{ apply (rs_glob_now rsegs B MT cx ly2 S2 W2 regs2 mem2 md2 W6C_T8 16 HPRE HCORE).
  cbn [hi_globs role_himg_A]. unfold role_A_globs, W6C_T8. repeat (first [left; reflexivity | right]). }
assert (HTF : forall a, W6C_T6 <= a < W6C_T8 + 16 -> ~ (F <= a < F + 512)).
{ intros a Ha HaF. pose proof HJ as (HAR2 & _).
  pose proof (al_client_img _ _ (AR_laws_ok rsegs B) _ _ _ _ _ a HAR2) as Hcl.
  assert (HinF' : frame_addr ly2 3 (x_pos cx) <= a < frame_addr ly2 3 (x_pos cx) + fs_frame_bytes 3)
    by (rewrite <- EF2; change (fs_frame_bytes 3) with 512; lia).
  apply (proj2 (Hcl (or_intror (or_introl (ex_intro _ 3 (ex_intro _ (x_pos cx) (conj HinF HinF'))))))).
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
assert (H25' : getr regs3 25 = w64 (rs_cur rsegs cx rest r')).
{ rewrite H25. unfold cur, rs_cur. f_equal. lia. }
specialize (HJof H25').
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (R - T_SEG_STK <= a < R) ->
  ~ (R + 0xc8 <= a < R + 0xd0) -> ~ (R + 0xf8 <= a < R + 0x100) -> ~ (F + 0xf0 <= a < F + 0x158) ->
  aview rsegs (w_H W2) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha H1 _ H3 H4. apply Hm3; [exact Ha | unfold ESTACK in *; rewrite HTS in H1; lia | exact H4 | exact H3]. }
specialize (HJof K3).
assert (V3 : val_mem rsegs (mrestrict (w_H W2) mem3) (R + 0xf8) 8 (Z.of_nat (length r'))).
{ rewrite Z.mod_small in Hs3; [exact Hs3|]. split; [lia|]. pose proof (w6c_ent_len (kd mod 10) r). unfold r'.
  assert (Z.of_nat (length r) <= 2 ^ 47) by lia. lia. }
specialize (HJof V3 He3 Hed).
change (cfg_at rsegs W6C_J regs3 mem3 md3) with (cfg_at rsegs RS_J regs3 mem3 md3).
exact (HFJ ly2 S2 W2 regs3 mem3 md3 sh np ps cnt es rr r' ed Hps Hes HJof).
Qed.
End d.
End b.

Print Assumptions w6c_piece_of.
