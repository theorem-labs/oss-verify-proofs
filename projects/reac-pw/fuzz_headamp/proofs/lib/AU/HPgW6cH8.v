(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address measured on the unstripped twin
   1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff): the head of ent_build's case 8 (pod.h:360-363)
   inside LLVMFuzzerTestOneInput (0x80c40), HPgW6cCase.w6c_head8_stmt: from the case entry 0x81f5c to the fill
   block 0x822b0. Proves no function (kind: segment lemma).

   THE CODE (registers as HPgW6cCase.w6c_in gives them: s1 = R, s11 = K, s2 = cur, a7 = cur - 1, t1 = |r| + 1,
   s4 = |r|, a6 = 1):
     0x81f5c  beqz s4 -> 0x8229c                      nothing left: s7 := pp; a2 := 0; e62.type := 4 (= t8[0])
     0x81f60  a0 := s2 + 1; s7 := [R+0x148] (= pp); bltu a6,a0 -> 0x81f70 (else the UBSan trap, never taken)
     0x81f70  the shadow check of s2 (slow block 0x827d0); 0x81f80 lbu a1,0(s2) (= t); a0 := 0x21140;
              a1 := t & 3; a2 := a1 << 2; bgeu ~a0,a2 -> 0x81fa0 (else the trap: never taken, a2 <= 12)
     0x81fa0  a0 := a0 + a2; the shadow check of a0 (ent_build.t.11[t & 3], slow block 0x827dc)
     0x81fb4  lw a0,0(a0) (= t8[t & 3]); s4 := t1 - 2 (= |r| - 1); s2 := a7 + 2; a2 := [R+0x130] (= F + 0x210);
              sw a0,0(a2) (e62.type); beq a1,3 -> 0x82070 (STRING: size 0)
     0x81fd0  beqz s4 -> 0x82070 (nothing left: size 0)
     0x81fd4  a0 := s2 + 1; bltu a6,a0 (never the trap); the shadow check of s2 (slow block 0x82880);
              0x81ff0 lbu a2,0(s2) (= s); s4 := t1 - 3; s2 := a7 + 3; a2 := s & 3           -> 0x822b0
     0x82070  a2 := 0                                                                            -> 0x822b0
   THE PROOF: the entry state HPgW6cCase.w6c_head_entry with t in the input region; one engine run to 0x81fa0;
   there the input region is dropped and the table's added (HPgW6cHKit.w6c_drop3, w6c_add_RT); one run over the
   table element's check to 0x81fb4; the index t & 3 split into its four values with a0 and a1 pinned; one run to
   0x822b0 (index 3) or to the branch 0x81fd0 (split by srr_branch_tok); for the second byte the table dropped and
   the byte's region added (w6c_add_RI2) and one run to 0x822b0. *)
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

Lemma w6c8_ty_range : forall j, 0 <= j < 4 -> 0 <= w6c8_ty j < 2 ^ 32.
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
Local Ltac w6c_hawr_tac U32 F pos Hown HF :=
  eapply (w6c_hawr _ _ _ _ _ _ _ _ _ _ F pos); [reflexivity | vm_compute; reflexivity | exact U32 | exact Hown | exact HF].

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.

Theorem w6c_head8 : w6c_head8_stmt B MT.
Proof using MTL.
unfold w6c_head8_stmt, w6c_head_stmt.
intros STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp r Hctx Hin.
pose proof Hin as (H2 & H3 & H4 & H9 & H27 & H18 & H17 & H6 & H20 & H16 & V10 & V118 & V130 & V138 & V148
  & Hpp1 & Hpp2 & Hez & HraE & HhE & Hr & Hrar & Hhr & Hamr & Hc2 & Hdis & Ht6 & Ht8 & Hrom).
pose proof Hctx as (HJ & HR32 & HRc & HRsp & Hsp47 & HSTK & Hown & HF & HF1 & HF2 & HF32 & HFapp & HFp).
pose proof asan_consts as (Hceil & _).
pose proof img_wx as Hwx. pose proof img_segs_low as Hsegs.
pose proof (AR_laws_ok rsegs B) as LAWS.
pose proof (w6c_frame_not_img B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc F pos HJ Hown HF) as HFni.
assert (HRb : 0x10007fffc000 <= R) by (unfold T_SEG_STK, ASTACK in *; lia).
assert (Hcr : cur + Z.of_nat (length r) <= 2 ^ 47 - 1)
  by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hamr; lia).
assert (Hpp : 0 <= pp <= 2 ^ 47) by (unfold Layout.PP_SIZE in Hpp2; lia).
unfold cfg_at. change (w64 (w6c_pc 8)) with (Z_to_bv 64 W6C_D8).
destruct r as [|b0 r'].
- (* ======================= nothing left: 0x81f5c -> 0x8229c -> 0x822b0 ======================= *)
  destruct (w6c_head_entry B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp []
    W6C_D8 0 0 0 (2 ^ 47 - 2) Hctx Hin ltac:(unfold W6C_D8; lia) ltac:(cbn [length] in Hcr; lia) ltac:(cbn; lia)
    ltac:(cbn; lia) ltac:(lia)) as [HS SHOK].
  remember (Ereg regs (w6c_extra F (u32_b [] 0) (u32_b [] 1) pp)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (w6c_extra F (u32_b [] 0) (u32_b [] 1) pp)) E)
    by (subst E; apply env_agree_refl).
  assert (E17 : ew E 17 = Z_to_bv 64 (cur - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E20 : ew E 20 = Z_to_bv 64 0) by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F _ _ pp)).
  assert (E35 : ew E 35 = Z_to_bv 64 pp) by (subst E; exact (w6c_e35 regs F _ _ pp)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  clear HE.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6c_wrH F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
    by reflexivity.
  srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan.
  2: { exfalso. cbn [sv_denot] in Hc. rewrite E20 in Hc. discriminate Hc. }
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_F8; [ w6c_hawr_tac U32 F pos Hown HF | ].
  w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32). w6c_pres HFp.
  w6c_ewn HS E17 E17f. w6c_ewn HS E20 E20f. w6c_ewn HS E32 E32f. w6c_ewn HS E35 E35f. w6c_ewn HS U32 U32f.
  apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_F8 w6c_clob
    (w6c_wrH F) (w6c_hpostF R F cur pp [] W) _ _ ms _ HS eq_refl eq_refl HJ).
  + cb_kio.
  + eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
  + exact KE.
  + split; [reflexivity|]. exists (w6c8_ty 0), 0, [].
    split.
    { unfold w6c_fl_model. split; [lia|]. split; [exact (w6c8_ty_range 0 ltac:(lia))|].
      split; [exists 0%nat; reflexivity|]. rewrite w6c8_model. reflexivity. }
    split; [w6c_reg HS (12%bv : bv 5); unfold w64; rewrite w6c_den_lit by lia; reflexivity|].
    split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 _ 1 E17f) by (cbn [length] in *; lia);
            f_equal; cbn [length]; lia|].
    split; [w6c_reg HS (20%bv : bv 5); unfold w64; rewrite (w6c_den0 _ 20 0 E20f) by lia; reflexivity|].
    split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35f | lia]|].
    split; [| exact HFp].
    w6c_rnth HS 1%nat Hr1.
    refine (w6c_field _ _ 32%nat F _ _ _ _ _ 0x210 4 _ (w6c8_ty 0) Hr1 U32f ltac:(cbn; left; reflexivity) _ _ _);
      [ rewrite w6c_den_lit by lia; reflexivity | exact (w6c8_ty_range 0 ltac:(lia)) | cbn; lia ].
- (* ======================= at least one byte left ======================= *)
  destruct (w6c_head_entry B STK sp0 FP ly S W0 mem0 md0 own k lyc Sc W memc mdc regs R F pos cur pp (b0 :: r')
    W6C_D8 1 1 (2 ^ 47) (2 ^ 47 - 3) Hctx Hin ltac:(unfold W6C_D8; lia) ltac:(cbn [length] in Hcr; lia)
    ltac:(cbn [length] in *; lia) ltac:(cbn; lia) ltac:(lia)) as [HS SHOK].
  remember (Ereg regs (w6c_extra F (u32_b (b0 :: r') 0) (u32_b (b0 :: r') 1) pp)) as E eqn:HE.
  assert (HAE : env_agree 32 (Ereg regs (w6c_extra F (u32_b (b0 :: r') 0) (u32_b (b0 :: r') 1) pp)) E)
    by (subst E; apply env_agree_refl).
  assert (E17 : ew E 17 = Z_to_bv 64 (cur - 1)) by (subst E; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact H17).
  assert (E20 : ew E 20 = Z_to_bv 64 (Z.of_nat (length (b0 :: r'))))
    by (subst E; rewrite (ew_Ereg_nat regs _ 20 20%bv eq_refl); exact H20).
  assert (E27 : ew E 27 = Z_to_bv 64 SHADOW_OFF) by (subst E; rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 F) by (subst E; exact (w6c_e32 regs F _ _ pp)).
  assert (E33 : ew E 33 = Z_to_bv 64 (u32_b (b0 :: r') 0)) by (subst E; exact (w6c_e33 regs F _ _ pp)).
  assert (E34 : ew E 34 = Z_to_bv 64 (u32_b (b0 :: r') 1)) by (subst E; exact (w6c_e34 regs F _ _ pp)).
  assert (E35 : ew E 35 = Z_to_bv 64 pp) by (subst E; exact (w6c_e35 regs F _ _ pp)).
  assert (U32 : bv_unsigned (ew E 32) = F) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (U9 : bv_unsigned (ew E 9) = R) by (subst E; exact (w6c_U_reg regs _ 9 9%bv R eq_refl H9 ltac:(lia))).
  assert (U17 : bv_unsigned (ew E 17) = cur - 1) by (rewrite E17; apply unsigned_lit_small; lia).
  clear HE.
  set (t := u32_b (b0 :: r') 0) in *.
  pose proof (u32_b_range (b0 :: r') 0) as Ht. fold t in Ht.
  assert (KE : forall a, 0 <= a < 2 ^ 64 -> ~ w6c_wrH F a -> aview rsegs (w_H W) memc a = aview rsegs (w_H W) memc a)
    by reflexivity.
  (* ---- run 1: 0x81f5c .. 0x81fa0 ---- *)
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x81fa0.
  { apply (obl_of_range rsegs (w_H W) memc _ w6c_Bx _ _ cur (Z.of_nat (length (b0 :: r'))) Hrar).
    - apply (U_atom _ 27 SHADOW_OFF E27). unfold SHADOW_OFF. lia.
    - rewrite (U_atom_off _ 17 (cur - 1) 1 E17) by lia. lia.
    - rewrite (U_atom_off _ 17 (cur - 1) 1 E17) by lia. cbn [length] in *. lia. }
  { w6c_hawr_tac U32 F pos Hown HF. }
  w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32).
  w6c_pres HFp.
  rename ms into ms1.
  assert (Hrom1 : rom_view rsegs W (ms_mem ms1)).
  { intros a Ha. assert (Ia : in_img rsegs a) by (destruct Ha as (sg & Hsg & _ & Hrg); exists sg; split; [exact Hsg | exact Hrg]).
    pose proof (Hsegs a Ia) as Hlow.
    rewrite (KE a ltac:(unfold kLowMemEnd in Hlow; lia) ltac:(unfold w6c_wrH; intros X; apply (HFni a); [lia | exact Ia])).
    exact (Hrom a Ha). }
  (* ---- at 0x81fa0: the input region out, the table in ---- *)
  apply w6c_drop3 in HS.
  w6c_ewn HS U9 U9a. w6c_ewn HS U32 U32a. w6c_ewn HS E33 E33a. w6c_ewn HS E27 E27a.
  pose proof (w6c_add_RT _ _ _ _ _ _ _ W ms1 W6C_TB8 R F HS eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl U9a U32a HRb
    ltac:(intros a Ha; apply HFni; lia) Hrom1 w6c_rom_tb8_seg w6c_rom_tb8 ltac:(unfold W6C_TB8; lia) w6c_RT8_wf) as HS'.
  clear HS. rename HS' into HS.
  pose proof (Z.mod_pos_bound t 4 ltac:(lia)) as Hjb.
  assert (Ht8' : range_addressable (aview rsegs (w_H W) (ms_mem ms1)) SHADOW_OFF W6C_TB8 16).
  { apply (hm_ra_kept rsegs (w_H W) memc); [exact Ht8|]. intros x Hx. unfold W6C_TB8 in Hx. apply KE.
    - pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; lia)) as X. unfold kLowMemEnd, kHighMemBeg in X. lia.
    - pose proof (hm_shadow_not_app x F 1024 ltac:(unfold kHighMemEnd; lia) HFapp) as Y. unfold w6c_wrH. lia. }
  (* ---- run 2: the table element's shadow check, 0x81fa0 .. 0x81fb4 ---- *)
  aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan 0x81fb4.
  { apply (obl_of_range rsegs (w_H W) (ms_mem ms1) _ w6c_Bx _ _ W6C_TB8 16 Ht8').
    - apply (U_atom _ 27 SHADOW_OFF E27a). unfold SHADOW_OFF. lia.
    - unfold U. lazymatch goal with |- context [sv_denot ?Ev ?x] =>
        assert (Ex0 : sv_denot Ev x = Z_to_bv 64 (0x21140 + 4 * (t mod 4)))
          by (change (Z_to_bv 64 (0x21140 + 4 * (t mod 4))) with
                (Z_to_bv 64 ((fun v => 0x21140 + 4 * (v mod 4)) t)); w6c_by256 E33a Ht) end.
      rewrite Ex0. rewrite unsigned_lit_small by lia. unfold W6C_TB8. lia.
    - unfold U. lazymatch goal with |- context [sv_denot ?Ev ?x] =>
        assert (Ex0 : sv_denot Ev x = Z_to_bv 64 (0x21140 + 4 * (t mod 4)))
          by (change (Z_to_bv 64 (0x21140 + 4 * (t mod 4))) with
                (Z_to_bv 64 ((fun v => 0x21140 + 4 * (v mod 4)) t)); w6c_by256 E33a Ht) end.
      rewrite Ex0. rewrite unsigned_lit_small by lia. unfold W6C_TB8. lia. }
  { w6c_hawr_tac U32a F pos Hown HF. }
  w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32a).
  w6c_pres HFp.
  rename ms into ms2.
  w6c_ewn HS E33 E33b. w6c_ewn HS U32 U32b.
  assert (Ea1 : getr (ms_regs ms2) 11 = Z_to_bv 64 (t mod 4)).
  { w6c_reg HS (11%bv : bv 5).
    change (Z_to_bv 64 (t mod 4)) with (Z_to_bv 64 ((fun v => v mod 4) t)). w6c_by256 E33b Ht. }
  assert (Ea0 : getr (ms_regs ms2) 10 = Z_to_bv 64 (0x21140 + 4 * (t mod 4))).
  { w6c_reg HS (10%bv : bv 5).
    change (Z_to_bv 64 (0x21140 + 4 * (t mod 4))) with (Z_to_bv 64 ((fun v => 0x21140 + 4 * (v mod 4)) t)).
    w6c_by256 E33b Ht. }
  (* ---- the index t & 3, split into its four values, a1 and a0 pinned ---- *)
  assert (Hj : t mod 4 = 0 \/ t mod 4 = 1 \/ t mod 4 = 2 \/ t mod 4 = 3) by lia.
  destruct Hj as [Ej|[Ej|[Ej|Ej]]]; rewrite Ej in Ea1, Ea0;
  (pose proof (st_ok_pin_lit rsegs _ _ _ (11%bv : bv 5) _ HS eq_refl ltac:(cbn [ms_regs restrict]; exact Ea1)) as HSa;
   cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSa;
   pose proof (st_ok_pin_lit rsegs _ _ _ (10%bv : bv 5) _ HSa eq_refl ltac:(cbn [ms_regs restrict]; exact Ea0)) as HSb;
   cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSb; clear HS HSa; rename HSb into HS).
  (* ---- run 3: 0x81fb4 .. 0x822b0 (index 3) or .. the branch 0x81fd0 ---- *)
  all: aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_F8; [ w6c_hawr_tac U32b F pos Hown HF | ].
  all: w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32b); w6c_pres HFp.
  all: w6c_ewn HS E17 E17c; w6c_ewn HS E20 E20c; w6c_ewn HS E32 E32c; w6c_ewn HS E35 E35c; w6c_ewn HS U32 U32c.
  (* ---- index 3: the STRING pod, size 0, at 0x822b0 ---- *)
  4: { apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_F8 w6c_clob
         (w6c_wrH F) (w6c_hpostF R F cur pp (b0 :: r') W) _ _ ms _ HS eq_refl eq_refl HJ).
       - cb_kio.
       - eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity].
       - exact KE.
       - split; [reflexivity|]. exists (w6c8_ty 3), 0, r'.
         split.
         { unfold w6c_fl_model. split; [lia|]. split; [exact (w6c8_ty_range 3 ltac:(lia))|].
           split; [exists 1%nat; reflexivity|].
           rewrite w6c8_model. cbn [Cursor.fuzz_u8 fst snd].
           replace (bv_unsigned b0 mod 4) with 3 by (rewrite <- Ej; reflexivity). reflexivity. }
         split; [w6c_reg HS (12%bv : bv 5); unfold w64; rewrite w6c_den_lit by lia; reflexivity|].
         split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 _ 2 E17c) by (cbn [length] in *; lia);
                 f_equal; cbn [length] in *; lia|].
         split; [w6c_reg HS (20%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 20 _ (-1) E20c) by (cbn [length] in *; lia);
                 f_equal; cbn [length] in *; lia|].
         split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35c | lia]|].
         split; [| exact HFp].
         w6c_rnth HS 1%nat Hr1.
         refine (w6c_field _ _ 32%nat F _ _ _ _ _ 0x210 4 _ (w6c8_ty 3) Hr1 U32c ltac:(cbn; left; reflexivity) _ _ _);
           [ rewrite w6c_den_lit by lia; reflexivity | exact (w6c8_ty_range 3 ltac:(lia)) | cbn; lia ]. }
  (* ---- indexes 0, 1, 2: the branch on s4 at 0x81fd0 ---- *)
  all: srr_branch_tok w6c_tbl_ok HS SHOK w6c_Bspan.
  all: lazymatch goal with Ej : _ mod 4 = ?c |- _ => lazymatch type of Hc with
  | _ = true =>
    (* s4 = 0: one byte was left; 0x81fd0 -> 0x82070 -> 0x822b0, size 0 *)
    assert (Hl : Z.of_nat (length (b0 :: r')) - 1 = 0);
    [ lazymatch goal with HSx : st_ok _ ?Ev _ _ |- _ =>
        let Hc' := fresh "Hc'" in let E20x := fresh "E20x" in
        assert (Hc' : (U Ev (SOff 20 (-1)) =? U Ev (SLit 0)) = true) by exact Hc;
        assert (E20x : ew Ev 20 = Z_to_bv 64 (Z.of_nat (length (b0 :: r')))) by (rewrite ?ew_ewset_other by lia; exact E20);
        rewrite (U_atom_off _ 20 _ (-1) E20x), U_SLit, zcanon_id in Hc' by (unfold M64; cbn [length] in *; lia);
        apply Z.eqb_eq in Hc'; exact Hc' end
    | ];
    destruct r' as [|b1 r'']; [| cbn [length] in Hl; lia];
    aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_F8; [ w6c_hawr_tac U32c F pos Hown HF | ];
    w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32c); w6c_pres HFp;
    w6c_ewn HS E17 E17d; w6c_ewn HS E20 E20d; w6c_ewn HS E35 E35d; w6c_ewn HS U32 U32d;
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_F8 w6c_clob
      (w6c_wrH F) (w6c_hpostF R F cur pp [b0] W) _ _ msf _ HSx eq_refl eq_refl HJ) end;
    [ cb_kio
    | eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity]
    | exact KE
    | split; [reflexivity|]; exists (w6c8_ty c), 0, [];
      split;
      [ unfold w6c_fl_model; split; [lia|]; split; [exact (w6c8_ty_range c ltac:(lia))|];
        split; [exists 1%nat; reflexivity|];
        rewrite w6c8_model; cbn [Cursor.fuzz_u8 fst snd];
        replace (bv_unsigned b0 mod 4) with c by (rewrite <- Ej; reflexivity); reflexivity
      | ];
      split; [w6c_reg HS (12%bv : bv 5); unfold w64; rewrite w6c_den_lit by lia; reflexivity|];
      split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 _ 2 E17d) by (cbn [length] in *; lia);
              f_equal; cbn [length] in *; lia|];
      split; [w6c_reg HS (20%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 20 _ (-1) E20d) by (cbn [length] in *; lia);
              f_equal; cbn [length] in *; lia|];
      split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35d | lia]|];
      split; [| exact HFp];
      let Hr1 := fresh "Hr1" in w6c_rnth HS 1%nat Hr1;
      refine (w6c_field _ _ 32%nat F _ _ _ _ _ 0x210 4 _ (w6c8_ty c) Hr1 U32d ltac:(cbn; left; reflexivity) _ _ _);
      [ rewrite w6c_den_lit by lia; reflexivity | exact (w6c8_ty_range c ltac:(lia)) | cbn; lia ] ]
  | _ = false =>
    (* s4 <> 0: the second byte s; the table out, s in; 0x81fd4 -> 0x822b0, size s & 3 *)
    assert (Hl : Z.of_nat (length (b0 :: r')) - 1 <> 0);
    [ lazymatch goal with HSx : st_ok _ ?Ev _ _ |- _ =>
        let Hc' := fresh "Hc'" in let E20x := fresh "E20x" in
        assert (Hc' : (U Ev (SOff 20 (-1)) =? U Ev (SLit 0)) = false) by exact Hc;
        assert (E20x : ew Ev 20 = Z_to_bv 64 (Z.of_nat (length (b0 :: r')))) by (rewrite ?ew_ewset_other by lia; exact E20);
        rewrite (U_atom_off _ 20 _ (-1) E20x), U_SLit, zcanon_id in Hc' by (unfold M64; cbn [length] in *; lia);
        apply Z.eqb_neq in Hc'; exact Hc' end
    | ];
    destruct r' as [|b1 r'']; [cbn [length] in Hl; lia|];
    apply w6c_drop3 in HS;
    w6c_ewn HS U9 U9d; w6c_ewn HS U32 U32d; w6c_ewn HS U17 U17d; w6c_ewn HS E34 E34d; w6c_ewn HS E27 E27d;
    w6c_ewn HS E17 E17d;
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msc) |- _ =>
      let Vs := fresh "Vs" in let HS' := fresh "HS'" in let Hrar' := fresh "Hrar'" in
      assert (Vs : val_mem rsegs (mrestrict (w_H W) (ms_mem msc)) (cur - 1 + 2) 1 (u32_b (b0 :: b1 :: r'') 1));
      [ apply (w6c_val_kept (w_H W) (w_H W) memc (ms_mem msc));
        [ replace (cur - 1 + 2) with (cur + Z.of_nat 1) by lia; rewrite u32_b_eq;
          exact (hm_bytes_byte rsegs (w_H W) memc cur _ 1 Hr ltac:(cbn; lia))
        | intros i Hi; cbn in Hi; apply KE; [lia|]; unfold w6c_wrH;
          destruct (Hdis (cur - 1 + 2 + i) ltac:(cbn [length]; lia)) as [_ X]; lia ]
      | ];
      pose proof (w6c_add_RI2 _ _ _ _ _ _ _ W msc R F (cur - 1) (u32_b (b0 :: b1 :: r'') 1) HS eq_refl eq_refl eq_refl
        eq_refl eq_refl eq_refl U9d U32d U17d E34d (u32_b_range _ 1) ltac:(lia) ltac:(lia)
        ltac:(destruct (Hdis (cur - 1 + 2) ltac:(cbn [length]; lia)) as [X _]; unfold T_SEG_STK, ASTACK in X; lia)
        ltac:(destruct (Hdis (cur - 1 + 2) ltac:(cbn [length]; lia)) as [_ X]; exact X) Vs) as HS';
      clear HS; rename HS' into HS;
      assert (Hrar' : range_addressable (aview rsegs (w_H W) (ms_mem msc)) SHADOW_OFF cur
                        (Z.of_nat (length (b0 :: b1 :: r''))));
      [ apply (hm_ra_kept rsegs (w_H W) memc); [exact Hrar|]; intros x Hx; apply KE;
        [ pose proof (hm_shadow_band x ltac:(unfold kHighMemEnd; cbn [length] in *; lia)) as X;
          unfold kLowMemEnd, kHighMemBeg in X; lia
        | pose proof (hm_shadow_not_app x F 1024 ltac:(unfold kHighMemEnd; cbn [length] in *; lia) HFapp) as Y;
          unfold w6c_wrH; lia ]
      | ];
      aj_run_to_tok w6c_tbl_ok HS HJ SHOK w6c_Bspan W6C_F8;
      [ apply (obl_of_range rsegs (w_H W) (ms_mem msc) _ w6c_Bx _ _ cur (Z.of_nat (length (b0 :: b1 :: r''))) Hrar');
        [ apply (U_atom _ 27 SHADOW_OFF E27d); unfold SHADOW_OFF; lia
        | rewrite (U_atom_off _ 17 (cur - 1) 2 E17d) by lia; lia
        | rewrite (U_atom_off _ 17 (cur - 1) 2 E17d) by lia; cbn [length] in *; lia ]
      | w6c_hawr_tac U32d F pos Hown HF
      | ]
    end;
    w6c_keep (w6c_wrH F) ltac:(w6c_hwrl U32d); w6c_pres HFp;
    w6c_ewn HS E17 E17e; w6c_ewn HS E20 E20e; w6c_ewn HS E34 E34e; w6c_ewn HS E35 E35e; w6c_ewn HS U32 U32e;
    lazymatch goal with HSx : st_ok _ _ _ (restrict _ ?msf) |- _ =>
    apply (w6c_post_of_run B MT MTL STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc W6C_F8 w6c_clob
      (w6c_wrH F) (w6c_hpostF R F cur pp (b0 :: b1 :: r'') W) _ _ msf _ HSx eq_refl eq_refl HJ) end;
    [ cb_kio
    | eapply (regs_kept_of_st_ok rsegs _ _ _ regs _ (w_H W) _ HS); [env_agree_chain HAE | vm_compute; reflexivity]
    | exact KE
    | split; [reflexivity|]; exists (w6c8_ty c), (u32_b (b0 :: b1 :: r'') 1 mod 4), r'';
      split;
      [ unfold w6c_fl_model; split; [pose proof (Z.mod_pos_bound (u32_b (b0 :: b1 :: r'') 1) 4 ltac:(lia)); lia|];
        split; [exact (w6c8_ty_range c ltac:(lia))|];
        split; [exists 2%nat; reflexivity|];
        rewrite w6c8_model; cbn [Cursor.fuzz_u8 fst snd];
        replace (bv_unsigned b0 mod 4) with c by (rewrite <- Ej; reflexivity); reflexivity
      | ];
      split; [w6c_reg HS (12%bv : bv 5); unfold w64;
              change (Z_to_bv 64 (u32_b (b0 :: b1 :: r'') 1 mod 4)) with
                (Z_to_bv 64 ((fun v => v mod 4) (u32_b (b0 :: b1 :: r'') 1)));
              w6c_by256 E34e (u32_b_range (b0 :: b1 :: r'') 1)|];
      split; [w6c_reg HS (18%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 17 _ 3 E17e) by (cbn [length] in *; lia);
              f_equal; cbn [length] in *; lia|];
      split; [w6c_reg HS (20%bv : bv 5); unfold w64; rewrite (w6c_den_off _ 20 _ (-2) E20e) by (cbn [length] in *; lia);
              f_equal; cbn [length] in *; lia|];
      split; [w6c_reg HS (23%bv : bv 5); unfold w64; apply w6c_den0; [exact E35e | lia]|];
      split; [| exact HFp];
      let Hr1 := fresh "Hr1" in w6c_rnth HS 1%nat Hr1;
      refine (w6c_field _ _ 32%nat F _ _ _ _ _ 0x210 4 _ (w6c8_ty c) Hr1 U32e ltac:(cbn; left; reflexivity) _ _ _);
      [ rewrite w6c_den_lit by lia; reflexivity | exact (w6c8_ty_range c ltac:(lia)) | cbn; lia ] ]
  end end.
Qed.
End d.
End b.

Print Assumptions w6c_head8.
