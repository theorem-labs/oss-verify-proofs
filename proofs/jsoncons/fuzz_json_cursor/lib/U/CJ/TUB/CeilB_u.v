(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.CJ.Lib Require Import Tac ZBridge FP.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.CJ.TUB Require Import DgWalkB_u G3PureB_u.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Ltac fget_simp := repeat first [ rewrite freg_get_same by reflexivity | rewrite freg_get_other by reflexivity ].

Ltac fnorm F := fget_simp; set (f10 := reg_get F 10) in *; set (f15 := reg_get F 15) in *; clearbody f10 f15.

Ltac fx_goal F x HF0 := let f := fresh "f" in set (f := reg_get F 10); assert (f = x) by (unfold f; exact HF0); clearbody f; subst f.
Ltac fx_in F x HF0 H := let f := fresh "f" in set (f := reg_get F 10) in H; assert (f = x) by (unfold f; exact HF0); clearbody f; subst f.

Lemma ceil_e_range : forall x, (0 <= ceil_e x < 2048)%Z.
Proof.
  intros x. unfold ceil_e. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.mod_pos_bound (Z.shiftl (bv_unsigned x) 1) 18446744073709551616 ltac:(lia)) as B.
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; [lia | change (2 ^ 53 * 2048)%Z with 18446744073709551616%Z; lia]].
Qed.

Section CEIL.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word.
Definition CSP : Z := bv_unsigned sp.
Hypothesis CSPR : (2 ^ 40 <= CSP < 2 ^ 47)%Z.

Variable SLO : Z.
Hypothesis SLOR : (SLO <= CSP - 16)%Z.
Definition ceil_post (x : word) (m0 : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists a0' a1' a2' F' fc' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F' (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ reg_get F' 10 = ceil_m x /\ frm0 fc'
    /\ munch [((CSP - 16)%Z, CSP)] m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ stk rsegs m' SLO CSP.

Lemma ceil_tail : forall a2 (F : bvmap 5 word) fc (m : word -> option byte) (x : word),
  reg_get F 10 = x -> fsub_d RNE (reg_get F 15) x = ceil_y x -> frm0 fc -> stk rsegs m SLO CSP -> mem_inv rsegs m ->
  (ceil_e x <= 1074)%Z -> feq_d x (fcvt_d_w RNE (Z_to_bv 64 0)) = false ->
  evt rsegs (ceil_post x m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 x (Z_to_bv 64 (ceil_e x)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0xab120) fc None m (seg_rom rsegs)).
Proof using All.
  intros a2 F fc m x HF HY FRM ST MI HE HZ.
  pose proof (munch_refl [((CSP - 16)%Z, CSP)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold ceil_post, CSP in *.
  assert (HE' : (1074 <? ceil_e x)%Z = false) by (apply Z.ltb_ge; exact HE).
  pose proof (ceil_e_range x) as ER.
  zstep. zstep. zstep. if_cases K4; zify_cond K4; rewrite ?(Z.mod_small (ceil_e x)) in K4 by lia.
  -
    assert (HK4 : (1022 <? ceil_e x)%Z = true) by (apply Z.ltb_lt; exact K4).
    zstep. zstep. zstep. zstep. if_cases K5.
    + zstep. finish; [ | ..].
      { fnorm F. subst f10. rewrite HY. unfold ceil_m. rewrite HE', HZ, HK4. rewrite HY in K5.
        destruct (flt_d (ceil_y x) (fcvt_d_w RNE (Z_to_bv 64 0))); [cbv in K5; discriminate | reflexivity]. }
    + do 4 zstep. finish; [ | ..].
      { fnorm F. subst f10. rewrite HY. unfold ceil_m. rewrite HE', HZ, HK4. rewrite HY in K5.
        destruct (flt_d (ceil_y x) (fcvt_d_w RNE (Z_to_bv 64 0))); [reflexivity | cbv in K5; discriminate]. }
  -
    assert (HK4 : (1022 <? ceil_e x)%Z = false) by (apply Z.ltb_ge; lia).
    zstep. carve_frame 16%nat ST. zstep. zstep.
    release_frame FR ST (bv_unsigned sp).
    zstep. if_cases K6; zify_cond K6.
    +
      do 3 zstep. finish; [ | ..].
      { fnorm F. unfold ceil_m. rewrite HE', HZ, HK4. subst f10.
        replace (2 ^ 63 <=? bv_unsigned x)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    +
      do 3 zstep. finish; [ | ..].
      { fnorm F. unfold ceil_m. rewrite HE', HZ, HK4. subst f10.
        replace (2 ^ 63 <=? bv_unsigned x)%Z with true by (symmetry; apply Z.leb_le; lia). apply bv_eq. vm_compute. reflexivity. }
Qed.

Lemma ceil_spec : forall a0 a1 a2 (F : bvmap 5 word) fc (m : word -> option byte) (x : word),
  reg_get F 10 = x -> frm0 fc -> stk rsegs m SLO CSP -> mem_inv rsegs m ->
  evt rsegs (ceil_post x m) (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                              F (Z_to_bv 64 0xab0d4) fc None m (seg_rom rsegs)).
Proof using All.
  intros a0 a1 a2 F fc m x HF FRM ST MI.
  pose proof (munch_refl [((CSP - 16)%Z, CSP)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold ceil_post, CSP in *.
  pose proof HF as HF0.
  zstep. zstep. zstep. zstep. zstep. set (f10 := reg_get F 10). assert (E10 : f10 = x) by (unfold f10; exact HF0). clearbody f10. subst f10. fold (ceil_e x).
  pose proof (ceil_e_range x) as ER.
  if_cases K1; zify_cond K1.
  -
    zstep. finish; [ | ..].
    { fget_simp. rewrite HF0. unfold ceil_m. replace (1074 <? ceil_e x)%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  - assert (HE' : (1074 <? ceil_e x)%Z = false) by (apply Z.ltb_ge; lia).
    zstep. zstep. zstep. if_cases K2.
    +
      assert (HZ : feq_d x (fcvt_d_w RNE (Z_to_bv 64 0)) = false).
      { fx_in F x HF0 K2. destruct (feq_d x (fcvt_d_w RNE (Z_to_bv 64 0))) eqn:Eq; [ | reflexivity]. cbv in K2. discriminate. }
      zstep. if_cases K3; zify_cond K3.
      *
        do 4 zstep.
        eapply ceil_tail; [ | | eassumption .. | lia | exact HZ].
        { fget_simp. exact HF0. }
        { fget_simp. fx_goal F x HF0. unfold ceil_y. replace (2 ^ 63 <=? bv_unsigned x)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity. }
      *
        do 5 zstep.
        eapply ceil_tail; [ | | eassumption .. | lia | exact HZ].
        { fget_simp. exact HF0. }
        { fget_simp. fx_goal F x HF0. unfold ceil_y. replace (2 ^ 63 <=? bv_unsigned x)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    +
      zstep. finish; [ | ..].
      { fget_simp. rewrite HF0. unfold ceil_m. rewrite HE'.
        fx_in F x HF0 K2. destruct (feq_d x (fcvt_d_w RNE (Z_to_bv 64 0))) eqn:Eq; [reflexivity | cbv in K2; discriminate]. }
Qed.
End CEIL.
