(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the head of ent_build's case 6 (pod.h:342-345)
   inside LLVMFuzzerTestOneInput (0x80c40), HPgW6cCase.w6c_head6_stmt: from the case entry 0x81f08 to the take block
   0x8227c. Proves no function (kind: segment lemma).

   THE CODE (registers as HPgW6cCase.w6c_in gives them: s1 = R, s11 = K, s2 = cur, a7 = cur - 1, t1 = |r| + 1,
   s4 = |r|, a6 = 1):
     0x81f08  beqz s4 -> 0x82228                      nothing left: a1 := 0; a2 := 0; a0 := 0x21120;
                                                     s7 := [R+0x148] (= pp); -> 0x8223c
     0x81f0c  a0 := s2 + 1; bltu a6,a0 -> 0x81f18 (else the UBSan trap, never taken: 1 <u cur + 1)
     0x81f18  the shadow check of s2 (slow block 0x82834); s7 := [R+0x148]
     0x81f2c  lbu a2,0(s2) (= t); a0 := 0x21120; a2 := t & 3; a3 := a2 << 2; a1 := ~a0; bgeu a1,a3 -> 0x81f4c
              (else the trap: never taken, 4 (t & 3) <= 12); a1 := t1 - 2 (= |r| - 1); s2 := a7 + 2; a0 := a0 + a3
     0x8223c  the shadow check of a0 (ent_build.t[t & 3], slow block 0x827a4); s4 := [R+0x130] (= F + 0x210);
              lw a0,0(a0) (= t6[t & 3]); sw a0,0(s4) (e62.type); a0 := 8, or 4 when t & 3 = 2;
              a2 := a0 unless t & 3 = 3 (then 0)                                          -> 0x8227c
   THE PROOF: the entry state HPgW6cCase.w6c_head_entry; the branch on s4 split by srr_branch_tok; one engine run
   to 0x8223c; there the input region is dropped and the table's added (HPgW6cHKit.w6c_drop3, w6c_add_RT), the index
   t & 3 split into its four values with a2 and a0 pinned to literals (HPgSteps.st_ok_pin_lit); one run to 0x8227c;
   the post read off the run's final state. *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout Tables.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgMem HPgSeg HPgSteps HPgCaseBJ
  HPgW6cEng HPgW6cCase HPgW6cHKit HPgCaseB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope Z_scope.

Lemma w6c6_ty_range : forall j, 0 <= j < 4 -> 0 <= w6c6_ty j < 2 ^ 32.
Proof.
intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3) by lia.
destruct Hc as [->|[->|[->| ->]]]; vm_compute; split; first [discriminate | reflexivity].
Qed.

(* an env fact at the env of HS *)
Local Ltac w6c_ewn HS H Hn :=
  lazymatch type of HS with st_ok _ ?Ev _ _ =>
  lazymatch type of H with
  | ew _ ?n = ?v => assert (Hn : ew Ev n = v) by (rewrite ?ew_ewset_other by lia; exact H)
  | bv_unsigned (ew _ ?n) = ?v => assert (Hn : bv_unsigned (ew Ev n) = v) by (rewrite ?ew_ewset_other by lia; exact H)
  end end.
(* the write windows of a head run lie in e62.type *)
Local Ltac w6c_hwrl U32 :=
  let a := fresh "a" in let Ha := fresh "Ha" in let X := fresh "X" in
  intros a Ha; pose proof (fun Hl => w6c_hw _ _ _ a eq_refl Hl Ha) as X;
  specialize (X ltac:(vm_compute; reflexivity)); rewrite U32 in X; exact X.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Theorem w6c_head6 : w6c_head6_stmt B MT.
Proof using MTL.
unfold w6c_head6_stmt, w6c_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp r Hctx Hin.
pose proof Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & V10 & V118 & V130 & V138 & V148
  & Hpp1 & Hpp2 & Hez & HraE & HhE & Hr & Hrar & Hhr & Hamr & Hc2 & Hdis & Ht6 & Ht8 & Hrom).
pose proof Hctx as (HJ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof asan_consts as (Hceil & _).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (w6c_frame_not_img B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc F pos HJ Hown HF) as HFni.
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (Hsp16 & _).
assert (HRb : 0x10007fffc000 <= R) by (unfold T_SEG_STK, ASTACK in *; lia).
assert (Hcr : cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
unfold cfg_at. change (w64 (w6c_pc 6)) with (Z_to_bv 64 W6C_D6).
destruct r as [|b0 r'].
- (* ======================= nothing left: 0x81f08 -> 0x82228 -> 0x8223c ======================= *)
  destruct (w6c_head_entry B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp []
    W6C_D6 0 0 0 (2 ^ 47 - 2) Hctx Hin ltac:(unfold W6C_D6; lia) ltac:(cbn [length] in Hcr; lia) ltac:(cbn; lia)
    ltac:(cbn; lia) ltac:(lia)) as [HS SHOK].
  remember (Ereg regs (w6c_extra F (u32_b [] 0) (u32_b [] 1) pp)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (w6c_extra F (u32_b [] 0) (u32_b [] 1) pp)) E)
    by (subst E; apply env_agree_refl).
  assert (E17 : ew E 17 = Z_to_bv 64 (cur - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E20 : ew E 20 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F _ _ pp)).
  assert (E33 : ew E 33 = Z_to_bv 64 0) by (subst E; exact (w6c_e33 regs F _ _ pp)).
  assert (E35 : ew E 35 = Z_to_bv 64 pp) by (subst E; exact (w6c_e35 regs F _ _ pp)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (w6c_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  clear HE.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6c_wrH F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
    by reflexivity.
  (* ---- the branch on s4 (the engine does not decide s4 = 0 from its range), then run 1: 0x82228 .. 0x8223c ---- *)
  srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan.
  2: { exfalso. cbn [sv_denot] in Hc. rewrite E20 in Hc. discriminate Hc. }
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x8223c;
    [ eapply (w6c_hawr _ _ _ _ _ _ _ _ _ _ F pos); [reflexivity | vm_compute; reflexivity | exact U32 | exact Hown | exact HF]
    | ].
  w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32).
  w6c_pres HFp.
  rename ms into ms1.
  assert (Hrom1 : rom_view rsegs W (ms_mem ms1)).
  { intros a Ha. assert (Ia : in_img rsegs a) by (destruct Ha as (sg & Hsg & _ & Hrg); exists sg; split; [exact Hsg | exact Hrg]).
    pose proof (Hsegs a Ia) as Hlow.
    rewrite (KE a ltac:(unfold kLowMemEnd in Hlow; lia) ltac:(unfold w6c_wrH; intros X; apply (HFni a); [lia | exact Ia])).
    exact (Hrom a Ha). }
  (* ---- at 0x8223c: the table in; a0 = 0x21120 as atom 33 (= 0) + 0x21120, so that its check is a token ---- *)
  w6c_ewn HS U9 U9a. w6c_ewn HS U32 U32a. w6c_ewn HS E33 E33a. w6c_ewn HS E27 E27a.
  pose proof (w6c_add_RT _ _ _ _ _ _ _ W ms1 W6C_TB6 R F HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl U9a U32a HRb
    ltac:(intros a Ha; apply HFni; lia) Hrom1 w6c_rom_tb6_seg w6c_rom_tb6 ltac:(unfold W6C_TB6; lia) w6c_RT6_wf) as HS'.
  clear HS. rename HS' into HS.
  pose proof (st_ok_pin_sv rsegs _ _ _ (10%bv : bv 5) (SOff 33 0x21120) HS eq_refl
    ltac:(cbn [ms_regs restrict]; w6c_reg HS (10%bv : bv 5); rewrite (w6c_den_off _ 33 0 0x21120 E33a) by lia;
          rewrite w6c_den_lit by lia; reflexivity)) as HSa.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSa. clear HS. rename HSa into HS.
  assert (Ht6' : range_addressable (aview rsegs (w_H W) (ms_mem ms1)) SHADOW_OFF W6C_TB6 16).
  { apply (hm_ra_kept rsegs (w_H W) memc); [exact Ht6|]. intros x Hx. unfold W6C_TB6 in Hx. apply KE.
    - pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X. unfold kLowMemEnd, kHighMemBeg in X. lia.
    - pose proof (hm_shadow_not_app x F 1024 ltac:(unfold kHighMemEnd; lia) HFapp) as Y. unfold w6c_wrH. lia. }
  (* ---- run 2: the table element's shadow check, 0x8223c .. 0x82250 ---- *)
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x82250.
  { apply (obl_of_range rsegs (w_H W) (ms_mem ms1) _ w6c_Bx _ _ W6C_TB6 16 Ht6').
    - apply (U_atom _ 27 SHADOW_OFF E27a). unfold SHADOW_OFF. lia.
    - rewrite (U_atom_off _ 33 0 0x21120 E33a) by lia. unfold W6C_TB6. lia.
    - rewrite (U_atom_off _ 33 0 0x21120 E33a) by lia. unfold W6C_TB6. lia. }
  { eapply (w6c_hawr _ _ _ _ _ _ _ _ _ _ F pos); [reflexivity | vm_compute; reflexivity | exact U32a | exact Hown | exact HF]. }
  w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32a).
  w6c_pres HFp.
  rename ms into ms2.
  w6c_ewn HS E33 E33b. w6c_ewn HS U32 U32b.
  pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) 0x21120 HS eq_refl
    ltac:(cbn [ms_regs restrict]; w6c_reg HS (10%bv : bv 5); rewrite (w6c_den_off _ 33 0 0x21120 E33b) by lia;
          reflexivity)) as HSa.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSa. clear HS. rename HSa into HS.
  (* ---- run 3: 0x82250 .. 0x8227c ---- *)
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_T6;
    [ eapply (w6c_hawr _ _ _ _ _ _ _ _ _ _ F pos); [reflexivity | vm_compute; reflexivity | exact U32b | exact Hown | exact HF]
    | ].
  w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32b). w6c_pres HFp.
  (* ---- the post at 0x8227c ---- *)
  w6c_ewn HS E17 E17f. w6c_ewn HS E32 E32f. w6c_ewn HS E35 E35f. w6c_ewn HS U32 U32f.
  apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_T6 w6c_clob
    (w6c_wrH F) (w6c_hpostT 6 R F cur pp [] W) _ _ ms _ HS eq_refl eq_refl HJ).
  + cb_kio.
  + eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + exact KE.
  + split; [reflexivity|]. exists (w6c6_ty 0), (w6c6_sz 0), [].
    split.
    { unfold w6c_tk_model. split; [pose proof (w6c6_sz_range 0 ltac:(lia)); lia|].
      split; [exact (w6c6_ty_range 0 ltac:(lia))|]. split; [exists 0%nat; reflexivity|].
      rewrite w6c6_model. reflexivity. }
    split; [w6c_reg HS (12%bv : bv 5); unfold w64; rewrite w6c_den_lit by lia; reflexivity|].
    split; [w6c_reg HS (11%bv : bv 5); unfold w64; rewrite w6c_den_lit by lia; reflexivity|].
    split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 _ 1 E17f) by (cbn [length] in *; lia);
            f_equal; cbn [length]; lia|].
    split; [w6c_reg HS (20%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32f | lia | lia]|].
    split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35f | unfold Layout.PP_SIZE in Hpp2; lia]|].
    split; [| exact HFp].
    w6c_rnth HS 1%nat Hr1.
    refine (w6c_field _ _ 32%nat F _ _ _ _ _ 0x210 4 _ (w6c6_ty 0) Hr1 U32f ltac:(cbn; left; reflexivity) _ _ _);
      [ rewrite w6c_den_lit by lia; reflexivity | exact (w6c6_ty_range 0 ltac:(lia)) | cbn; lia ].
- destruct (w6c_head_entry B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp (b0 :: r')
    W6C_D6 1 1 (2 ^ 47) (2 ^ 47 - 3) Hctx Hin ltac:(unfold W6C_D6; lia) ltac:(cbn [length] in Hcr; lia) ltac:(cbn [length] in *; lia)
    ltac:(cbn; lia) ltac:(lia)) as [HS SHOK].
  remember (Ereg regs (w6c_extra F (u32_b (b0 :: r') 0) (u32_b (b0 :: r') 1) pp)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (w6c_extra F (u32_b (b0 :: r') 0) (u32_b (b0 :: r') 1) pp)) E)
    by (subst E; apply env_agree_refl).
  assert (E17 : ew E 17 = Z_to_bv 64 (cur - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat (length (b0 :: r'))))
    by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F _ _ pp)).
  assert (E33 : ew E 33 = Z_to_bv 64 (u32_b (b0 :: r') 0)) by (subst E; exact (w6c_e33 regs F _ _ pp)).
  assert (E35 : ew E 35 = Z_to_bv 64 pp) by (subst E; exact (w6c_e35 regs F _ _ pp)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (w6c_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  clear HE.
  set (t := u32_b (b0 :: r') 0) in *.
  pose proof (u32_b_range (b0 :: r') 0) as Ht. fold t in Ht.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6c_wrH F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
    by reflexivity.
  (* ---- run 1: 0x81f08 .. 0x8223c ---- *)
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x8223c.
  { apply (obl_of_range rsegs (w_H W) memc _ w6c_Bx _ _ cur (Z.of_nat (length (b0 :: r'))) Hrar).
    - apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
    - rewrite (U_atom_off _ 17 (cur - 1) 1 E17) by lia. lia.
    - rewrite (U_atom_off _ 17 (cur - 1) 1 E17) by lia. cbn [length] in *. lia. }
  { eapply (w6c_hawr _ _ _ _ _ _ _ _ _ _ F pos); [reflexivity | vm_compute; reflexivity | exact U32 | exact Hown | exact HF]. }
  w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32).
  w6c_pres HFp.
  rename ms into ms1.
  assert (Hrom1 : rom_view rsegs W (ms_mem ms1)).
  { intros a Ha. assert (Ia : in_img rsegs a) by (destruct Ha as (sg & Hsg & _ & Hrg); exists sg; split; [exact Hsg | exact Hrg]).
    pose proof (Hsegs a Ia) as Hlow.
    rewrite (KE a ltac:(unfold kLowMemEnd in Hlow; lia) ltac:(unfold w6c_wrH; intros X; apply (HFni a); [lia | exact Ia])).
    exact (Hrom a Ha). }
  (* ---- at 0x8223c: the input region out, the table in ---- *)
  apply w6c_drop3 in HS.
  w6c_ewn HS U9 U9a. w6c_ewn HS U32 U32a. w6c_ewn HS E33 E33a. w6c_ewn HS E27 E27a.
  pose proof (w6c_add_RT _ _ _ _ _ _ _ W ms1 W6C_TB6 R F HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl U9a U32a HRb
    ltac:(intros a Ha; apply HFni; lia) Hrom1 w6c_rom_tb6_seg w6c_rom_tb6 ltac:(unfold W6C_TB6; lia) w6c_RT6_wf) as HS'.
  clear HS. rename HS' into HS.
  (* ---- the index t & 3, split into its four values, a2 and a0 pinned ---- *)
  pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as Hjb.
  assert (Ht6' : range_addressable (aview rsegs (w_H W) (ms_mem ms1)) SHADOW_OFF W6C_TB6 16).
  { apply (hm_ra_kept rsegs (w_H W) memc); [exact Ht6|]. intros x Hx. unfold W6C_TB6 in Hx. apply KE.
    - pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X. unfold kLowMemEnd, kHighMemBeg in X. lia.
    - pose proof (hm_shadow_not_app x F 1024 ltac:(unfold kHighMemEnd; lia) HFapp) as Y. unfold w6c_wrH. lia. }
  (* ---- run 2: the table element's shadow check, 0x8223c .. 0x82250 ---- *)
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x82250.
  { apply (obl_of_range rsegs (w_H W) (ms_mem ms1) _ w6c_Bx _ _ W6C_TB6 16 Ht6').
    - apply (U_atom _ 27 SHADOW_OFF E27a). unfold SHADOW_OFF. lia.
    - unfold U. lazymatch goal with |- context [sv_denot ?Ev ?x] =>
        assert (Ex0 : sv_denot Ev x = Z_to_bv 64 (0x21120 + 4 * (t mod 4)))
          by (change (Z_to_bv 64 (0x21120 + 4 * (t mod 4))) with
                (Z_to_bv 64 ((fun v => 0x21120 + 4 * (v mod 4)) t)); w6c_by256 E33a Ht) end.
      rewrite Ex0. rewrite unsigned_lit_small by lia. unfold W6C_TB6. lia.
    - unfold U. lazymatch goal with |- context [sv_denot ?Ev ?x] =>
        assert (Ex0 : sv_denot Ev x = Z_to_bv 64 (0x21120 + 4 * (t mod 4)))
          by (change (Z_to_bv 64 (0x21120 + 4 * (t mod 4))) with
                (Z_to_bv 64 ((fun v => 0x21120 + 4 * (v mod 4)) t)); w6c_by256 E33a Ht) end.
      rewrite Ex0. rewrite unsigned_lit_small by lia. unfold W6C_TB6. lia. }
  { eapply (w6c_hawr _ _ _ _ _ _ _ _ _ _ F pos); [reflexivity | vm_compute; reflexivity | exact U32a | exact Hown | exact HF]. }
  w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32a).
  w6c_pres HFp.
  rename ms into ms2.
  w6c_ewn HS E33 E33b. w6c_ewn HS U32 U32b.
  assert (Ea2 : getr (ms_regs ms2) 12 = Z_to_bv 64 (t mod 4)).
  { w6c_reg HS (12%bv : bv 5).
    change (Z_to_bv 64 (t mod 4)) with (Z_to_bv 64 ((fun v => v mod 4) t)). w6c_by256 E33b Ht. }
  assert (Ea0 : getr (ms_regs ms2) 10 = Z_to_bv 64 (0x21120 + 4 * (t mod 4))).
  { w6c_reg HS (10%bv : bv 5).
    change (Z_to_bv 64 (0x21120 + 4 * (t mod 4))) with (Z_to_bv 64 ((fun v => 0x21120 + 4 * (v mod 4)) t)).
    w6c_by256 E33b Ht. }
  assert (Hj : t mod 4 = 0 \/ t mod 4 = 1 \/ t mod 4 = 2 \/ t mod 4 = 3) by lia.
  destruct Hj as [Ej|[Ej|[Ej|Ej]]]; rewrite Ej in Ea2, Ea0;
  (pose proof (st_ok_pin_lit rsegs _ _ _ (12%bv : bv 5) _ HS eq_refl ltac:(cbn [ms_regs restrict]; exact Ea2)) as HSa;
   cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSa;
   pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) _ HSa eq_refl ltac:(cbn [ms_regs restrict]; exact Ea0)) as HSb;
   cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSb; clear HS HSa; rename HSb into HS).
  (* ---- run 3: 0x82250 .. 0x8227c, at each value of the index ---- *)
  all: aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_T6;
    [ eapply (w6c_hawr _ _ _ _ _ _ _ _ _ _ F pos); [reflexivity | vm_compute; reflexivity | exact U32b | exact Hown | exact HF]
    | ].
  all: w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32b); w6c_pres HFp.
  (* ---- the post at 0x8227c ---- *)
  all: w6c_ewn HS E17 E17f; w6c_ewn HS E20 E20f; w6c_ewn HS E32 E32f; w6c_ewn HS E35 E35f; w6c_ewn HS U32 U32f.
  all: lazymatch goal with Ej : _ mod 4 = ?c |- _ =>
    apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_T6 w6c_clob
      (w6c_wrH F) (w6c_hpostT 6 R F cur pp (b0 :: r') W) _ _ ms _ HS eq_refl eq_refl HJ);
    [ cb_kio
    | eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity]
    | exact KE
    | split; [reflexivity|]; exists (w6c6_ty c), (w6c6_sz c), r';
      split;
      [ unfold w6c_tk_model; split; [pose proof (w6c6_sz_range c ltac:(lia)); lia|];
        split; [exact (w6c6_ty_range c ltac:(lia))|];
        split; [exists 1%nat; reflexivity|];
        rewrite w6c6_model; cbn [Cursor.fuzz_u8 fst snd];
        replace (bv_unsigned b0 mod 4) with c by (rewrite <- Ej; reflexivity); reflexivity
      | ];
      split; [w6c_reg HS (12%bv : bv 5); unfold w64; rewrite w6c_den_lit by lia; reflexivity|];
      split; [w6c_reg HS (11%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 20 _ (-1) E20f) by (cbn [length] in *; lia);
              f_equal; cbn [length] in *; lia|];
      split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 _ 2 E17f) by (cbn [length] in *; lia);
              f_equal; cbn [length] in *; lia|];
      split; [w6c_reg HS (20%bv : bv 5); unfold w64; apply w6c_den_off; [exact E32f | lia | lia]|];
      split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35f | unfold Layout.PP_SIZE in Hpp2; lia]|];
      split; [| exact HFp];
      let Hr1 := fresh "Hr1" in w6c_rnth HS 1%nat Hr1;
      refine (w6c_field _ _ 32%nat F _ _ _ _ _ 0x210 4 _ (w6c6_ty c) Hr1 U32f ltac:(cbn; left; reflexivity) _ _ _);
      [ rewrite w6c_den_lit by lia; reflexivity | exact (w6c6_ty_range c ltac:(lia)) | cbn; lia ] ]
  end.
Qed.
End d.
End b.

Print Assumptions w6c_head6.
