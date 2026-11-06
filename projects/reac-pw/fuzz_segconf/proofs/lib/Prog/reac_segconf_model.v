(** reac_segconf_model (plain build, 0x15984): proof of [reac_segconf_model_contract] (reac_segconf_model_c.v)
    from the contract of its callee reac_segconf_find (reac_segconf_find_c.v).

    Shape (the plain binary): `addi sp,sp,-16; sd ra,8(sp)`; `jal
    reac_segconf_find` with a0 = c, a1 = name unchanged (find's premise is query_pre FIND_STACK at sp - 16); `beqz
    a0` to the epilogue (a0 = 0 there); else `lw a1,0x3c(a0); seqz a1; addi a0,a0,0x24; addi a1,a1,-1; and
    a0,a1,a0`: s + 0x24 when seg[i].model_set (0 or 1: Prog/seg_query_facts.v sq_model_set), else 0; the epilogue
    restores ra and returns. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import Tac Bytes ZBridge.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pin_spec seg_spec seg_query_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import reac_segconf_find_c reac_segconf_model_c.
Import ListNotations.
Open Scope Z_scope.

(* A branch whose condition is false (tkn) or true (ntk) by arithmetic. *)
Ltac tkn := let K := fresh "K" in if_cases K; [clear K | exfalso; zify_cond K; Z.div_mod_to_equations; lia].
Ltac ntk := let K := fresh "K" in if_cases K; [exfalso; zify_cond K; Z.div_mod_to_equations; lia | clear K].
(* `and a0,a1,a0` with a1 = seqz(flag) - 1, a closed mask: all ones (flag 1) or 0 (flag 0). *)
Ltac fold_mask :=
  match goal with |- context [Z.land ?k ?x] =>
    let k' := eval vm_compute in k in replace k with k' by (vm_compute; reflexivity)
  end.

Theorem reac_segconf_model_holds : reac_segconf_find_contract -> reac_segconf_model_contract.
Proof.
  intros FIND. unfold reac_segconf_model_contract, REAC_SEGCONF_MODEL, MODEL_STACK.
  change (16 + FIND_STACK) with 48.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo rc nm
    (HC0 & HC16 & (bs & HB & HE) & HAC & HN0 & (bn & HBN & HZN & HNN) & HAN & (ST & HLO & HSP & HRO) & MI).
  unfold apart, SEG_C_SIZE in HAC, HAN.
  destruct (sq_rconf_len rc bs HE) as [HL HLS].
  assert (LN : length nm = length bn) by (rewrite <- HZN; unfold zs; apply length_map).
  pose proof (bytes_at_bound _ _ _ _ HB) as B1.
  pose proof (bytes_at_bound _ _ _ _ HBN) as B2. rewrite length_app in B2. cbn [length] in B2.
  pose proof (bv_unsigned_in_range 64 sp) as RS. unfold bv_modulus in RS. cbn in RS.
  pose proof (bv_unsigned_in_range 64 a0) as RA0. unfold bv_modulus in RA0. cbn in RA0.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  zstep. carve_frame 16%nat ST.
  zstep. zstep.
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    eapply evt_cut; [eapply FIND with (lo := lo) (rc := rc) (nm := nm) | let ms' := fresh "ms'" in let PO := fresh "PO" in
      intros ms' PO; unfold FIND_STACK in PO; rewrite ?unsigned_lit in PO by lia; revert ms' PO;
      post_call segs mm ]
  end.
  { unfold query_pre, stack_ok, apart, SEG_C_SIZE, FIND_STACK. rewrite !unsigned_lit by lia.
    refine (conj HC0 (conj HC16 (conj _ (conj _ (conj HN0 (conj _ (conj _ (conj (conj _ (conj _ (conj _ _))) _)))))))).
    - exists bs. split; assumption.
    - lia.
    - exists bn. split; [assumption|]. split; assumption.
    - lia.
    - exact ST.
    - lia.
    - Z.div_mod_to_equations. lia.
    - intros a Ha. apply HRO. lia.
    - assumption. }
  match goal with H : stk _ _ lo _ |- _ => rename H into ST end. rewrite unsigned_lit in ST by lia.
  rewrite sq_find_ptr. unfold model_ptr, r_model, rseg_addr, RSEG_SIZE, RS_MODEL.
  destruct (r_find rc nm) as [i|] eqn:RF.
  - pose proof (sq_find_lt rc nm i RF) as Hi.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (sq_model_set rsegs mm (bv_unsigned a0) bs rc i HB HE Hi) as RD end.
    unfold RS_MODEL_SET in RD.
    zstep. ntk.
    destruct (rs_model_set (r_seg rc i)) eqn:MS1; unfold b2z in RD |- *.
    + do 5 zstep.
      fold_mask. rewrite (Z.land_comm 18446744073709551615), Z_to_bv_land64.
      do 3 zstep.
      release_frame FR ST (bv_unsigned sp).
      finish.
    + do 5 zstep.
      fold_mask. rewrite Z.land_0_l.
      do 3 zstep.
      release_frame FR ST (bv_unsigned sp).
      finish.
  - zstep. tkn.
    do 3 zstep.
    release_frame FR ST (bv_unsigned sp).
    finish.
Qed.
