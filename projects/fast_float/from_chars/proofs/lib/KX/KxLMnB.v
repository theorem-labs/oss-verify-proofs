(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxFrame FxCall FxRgs FxFn.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFn.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_app2 B_rt_stmt B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_app2 OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_normalize_stmt.

Module B_normalize.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Wbig_tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_normalize_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_app2.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section Loop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Variables (vec x5 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte) (j8 : list byte).
  Variables (ws : list word) (len : Z).
  Hypothesis Hlen : length ws = 62%nat.
  Hypothesis LEN : (0 < len <= 62)%Z.
  Hypothesis SEP : (bv_unsigned sp <= bv_unsigned vec \/ bv_unsigned vec + 498 <= bv_unsigned sp + -16)%Z.
  Hypothesis RO3 : (IMG_END <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp + -16)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (bv_unsigned vec) (bv_unsigned vec + 504))%Z.
  Hypothesis KA1 : (bv_unsigned vec + 504 <= KTOP)%Z.

  Notation A := (bv_unsigned vec).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Notation A4 := (Z_to_bv 64 ((A + 496) / 8 + ASAN_B)).
  Notation POST := (normalize_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc A ws len m0).
  Notation NOTA := (Z_to_bv 64 (Z.lxor A 18446744073709551615)).

  (* [comment removed for export] *)
  Definition loop_ok (k : nat) : Prop :=
    forall (l : Z) (a2 x7 : word) (m : word -> option byte),
      (Z.to_nat l = k)%nat -> (1 <= l <= len)%Z ->
      u64arr BSEGS m A ws ->
      rw_cells BSEGS m (A + 496) [C2 (Z_to_bv 64 l)] ->
      norm_len ws (Z.to_nat len) = norm_len ws (Z.to_nat l) ->
      munch (normalize_W A sp) m0 m -> wmono BSEGS m0 m ->
      rw_cells BSEGS m (bv_unsigned sp + -16) [CB 8 j8; C8 ra] ->
      stk BSEGS m (bv_unsigned sp + -16) (bv_unsigned sp + -16) ->
      shz BSEGS m (ASAN_B + A / 8) 63 ->
      evt BSEGS POST
        (MS (mkR ra SP' gp tp x5 (Z_to_bv 64 l) x7 s0 s1 (Z_to_bv 64 (A + 496)) vec a2 BB A4 (Z_to_bv 64 len) NOTA (Z_to_bv 64 64)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x98214) fc None m (seg_rom BSEGS)).

  #[using="Hlen LEN SEP KSP KSP2 KA0 KA1"] Lemma norm_loop : forall k, loop_ok k.
  Proof. LiaFast.lf_pins (fun (Hlen LEN SEP KSP KSP2 KA0 KA1 : LiaFast.U) => LiaFast.u0).
    induction k as [|k IH]; unfold loop_ok; intros l a2 x7 m Hk Hl LIMBS LC NL MU WM FR ST SHZ.
    { exfalso. lia. }
    pose proof (bv_unsigned_in_range 64 vec) as RA. unfold bv_modulus in RA.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bd. rewrite Hlen in Bd.
    pose proof (rw_cells_bound _ _ _ _ LC) as BL. cbn [cells_size csize Nat.add] in BL.
    cbv delta [normalize_W] in MU.
    step. (* [comment removed for export] *)
    try if_not_taken.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit l) by lia. rewrite shl48_shr48 by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite (unsigned_lit (l + -1)) by lia. rewrite Z.shiftl_mul_pow2 by lia.
    replace ((l + -1) * 2 ^ 3)%Z with (8 * (l - 1))%Z by lia.
    step. (* [comment removed for export] *)
    try if_not_taken.
    step. (* [comment removed for export] *)
    destruct (nth_error ws (Z.to_nat (l - 1))) as [w|] eqn:Hn. 2:{ exfalso. apply nth_error_None in Hn. lia. }
    assert (Hw : nth (Z.to_nat (l - 1)) ws w0 = w) by (apply nth_error_nth; exact Hn).
    step. (* [comment removed for export] *) shr3.
    replace ((A + 8 * (l - 1)) / 8)%Z with (A / 8 + (l - 1))%Z by (Z.div_mod_to_equations; lia).
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (u64arr_read BSEGS m A ws (l - 1) w (Z_to_bv 64 (A + 8 * (l - 1))) LIMBS Hn ltac:(lia) eq_refl) as RD.
    step. (* [comment removed for export] *)
    clear RD.
    assert (Hk1 : Z.to_nat l = S (Z.to_nat (l - 1))) by lia.
    rewrite Hk1 in NL. cbn [norm_len] in NL. unfold limbZ in NL. rewrite Hw in NL.
    step. (* [comment removed for export] *)
    if_cases Hnz.
    - cond_cleanup Hnz.
      replace (bv_unsigned w =? 0)%Z with false in NL by (symmetry; apply Z.eqb_neq; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      unfold normalize_post. rewrite NL. replace (Z.of_nat (S (Z.to_nat (l - 1)))) with l by lia.
      finish. all: try eassumption.
    - cond_cleanup Hnz.
      replace (bv_unsigned w =? 0)%Z with true in NL by (symmetry; apply Z.eqb_eq; lia).
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hc.
      + cond_cleanup Hc. rewrite Z.shiftl_mul_pow2 in Hc by lia. rewrite Z.mod_small in Hc by lia.
        replace (l + -1)%Z with (l - 1)%Z by lia.
        eapply (IH (l - 1)%Z); try eassumption; try lia.
      + cond_cleanup Hc. rewrite Z.shiftl_mul_pow2 in Hc by lia. rewrite Z.mod_small in Hc by lia.
        assert (Hl1 : l = 1%Z) by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        release_frame FR ST (bv_unsigned sp).
        unfold normalize_post. rewrite NL. subst l. change (Z.to_nat (1 - 1)) with 0%nat. cbn [norm_len Z.of_nat].
        change (1 + -1)%Z with 0%Z.
        finish. all: try eassumption.
  Qed.
End Loop.

Lemma normalize_spec : normalize_stmt.
Proof.
  unfold normalize_stmt. intros until len. intros LIMBS Hlen LC LEN ST PRG BC SEP RO3 KSP KSP2 KA0 KA1 SHZ.
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (munch_refl (normalize_W (bv_unsigned a0) sp) m) as MU. cbv delta [normalize_W] in MU.
  pose proof (wmono_refl BSEGS m) as WM.
  carve_frame 16%nat ST.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *) shr3.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  rewrite zx16_lit by lia.
  step. (* [comment removed for export] *)
  if_cases Hz.
  { cond_cleanup Hz.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    release_frame FR ST (bv_unsigned sp).
    unfold normalize_post. subst len. change (Z.to_nat 0) with 0%nat. cbn [norm_len Z.of_nat]. finish. all: try eassumption. }
  cond_cleanup Hz.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  eapply (norm_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 a0); try eassumption; try reflexivity; try lia.
Qed.
End B_normalize.

From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn.
From OSSVerify.Proofs.fast_float.from_chars.lib Require M4B_kfn M4B_lm.
Import OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn.M4B_tmpl OSSVerify.Proofs.fast_float.from_chars.lib.M4B_kfn OSSVerify.Proofs.fast_float.from_chars.lib.M4B_lm.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun KxTac KxRtB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

Lemma fact_at : forall E fs k f, Forall (fact_ok E) fs -> nth_error fs k = Some f -> fact_ok E f.
Proof. intros E fs k f H Hk. rewrite Forall_forall in H. apply H. exact (nth_error_In _ _ Hk). Qed.

(* [comment removed for export] *)
Lemma diff_small : forall a b lo hi, 0 <= a < two64 -> 0 <= b -> b + hi < two64 -> 0 <= lo ->
  lo <= (a - b) mod two64 <= hi -> b + lo <= a <= b + hi.
Proof.
  intros a b lo hi Ha Hb Hbh Hlo H. destruct (Z.le_gt_cases b a) as [Hle|Hlt].
  - rewrite Z.mod_small in H by (unfold two64 in *; lia). lia.
  - assert (Hm : (a - b) mod two64 = a - b + two64) by (symmetry; apply Z.mod_unique with (q := -1); unfold two64 in *; lia).
    rewrite Hm in H. unfold two64 in *. lia.
Qed.

(* [comment removed for export] *)
Lemma lmn_facts : forall c E1 ms1, (c = 0 \/ c = 16) -> sden BSEGS E1 (with_pc (LM_TAIL_Q c) 0x981cc) ms1 ->
  let q := bv_unsigned (E1 10%positive) in let xq := bv_unsigned (E1 30%positive) in
  0 <= bv_unsigned (E1 235%positive) <= 62 /\ 0 <= bv_unsigned (E1 235%positive) - bv_unsigned (E1 31%positive) <= 6 /\
  1596 <= q <= 34359735543 /\ 512 * q + 528896 <= xq <= 512 * q + 528896 + 131072 - 79 /\
  (KHI <= 4096 * q \/ 4096 * q + 11571200 <= SH_LO) /\
  bv_unsigned (lden E1 XA) = 8 * xq /\ bv_unsigned (lden E1 XS) = ASAN_B + xq /\
  app2r (8 * xq) (8 * xq + 504) /\ 8 * xq + 504 <= KTOP /\ (8 * xq) mod 8 = 0.
Proof.
  intros c E1 ms1 Hcc HD1 q xq.
  destruct (sden_0 _ _ _ _ HD1) as (_ & _ & _ & _ & _ & _ & HF & _). cbn [s_facts with_pc LM_TAIL_Q] in HF.
  pose proof (bv_unsigned_in_range _ (E1 30%positive)) as B30. pose proof (bv_unsigned_in_range _ (E1 10%positive)) as B10.
  pose proof (bv_unsigned_in_range _ (E1 31%positive)) as B31. pose proof (bv_unsigned_in_range _ (E1 235%positive)) as B235.
  unfold bv_modulus in B30, B10, B31, B235. change (2 ^ Z.of_N 64) with two64 in B30, B10, B31, B235.
  assert (HFx : forall k f, nth_error (LM_FQ c) k = Some f -> fact_ok E1 f) by (intros k f Hk; exact (fact_at E1 _ k f HF Hk)).
  assert (X : Forall (fact_ok E1) [FRange LEN 0 56; FRange (lsub XS (fsh AR4)) 0 (2 ^ 17 - 63 - 16); FRange FSP (IMG_END / 4096) ((KTOP - 0xb09000) / 4096);
                                  FRange (lsub FS (lconst KHI)) 0 (2 ^ 64 + SH_LO - 0xb09000 - KHI); FRange L0V 0 62; FRange (lsub L0V LEN) 0 6]).
  { destruct Hcc as [->| ->]; repeat apply Forall_cons; try apply Forall_nil;
      [ exact (HFx 5%nat _ eq_refl) | exact (HFx 7%nat _ eq_refl) | exact (HFx 11%nat _ eq_refl) | exact (HFx 12%nat _ eq_refl) | exact (HFx 39%nat _ eq_refl) | exact (HFx 40%nat _ eq_refl)
      | exact (HFx 5%nat _ eq_refl) | exact (HFx 7%nat _ eq_refl) | exact (HFx 11%nat _ eq_refl) | exact (HFx 12%nat _ eq_refl) | exact (HFx 39%nat _ eq_refl) | exact (HFx 40%nat _ eq_refl) ]. }
  clear HF HFx.
  apply Forall_cons_iff in X as [F3 X]. apply Forall_cons_iff in X as [F5 X]. apply Forall_cons_iff in X as [F9 X]. apply Forall_cons_iff in X as [F10 X].
  apply Forall_cons_iff in X as [F40 X]. apply Forall_cons_iff in X as [F41 _].
  cbn [fact_ok] in F3, F5, F9, F10, F40, F41.
  lnorm_s_in F3. lnorm_s_in F5. lnorm_s_in F9. lnorm_s_in F10. lnorm_s_in F40. lnorm_s_in F41. rewrite ?u_Z_to_bv in F5, F10, F41. unfold vz in *.
  change (IMG_END / 4096) with 1596 in F9. change ((KTOP - 0xb09000) / 4096) with 34359735543 in F9.
  fold q xq in F5, F9, F10.
  assert (Hxq : 512 * q + 528896 <= xq <= 512 * q + 528896 + 131072 - 79).
  { replace (-528896 + (-512 * q + (1 * xq + 0))) with (xq - (512 * q + 528896)) in F5 by ring.
    pose proof (diff_small xq (512 * q + 528896) 0 (131072 - 79) ltac:(unfold two64 in *; lia) ltac:(lia) ltac:(unfold two64 in *; lia) ltac:(lia) F5) as D.
    lia. }
  assert (Hcls : KHI <= 4096 * q \/ 4096 * q + 11571200 <= SH_LO).
  { replace (-17594333495296 + (4096 * q + 0)) with (4096 * q - 17594333495296) in F10 by ring.
    destruct (Z.le_gt_cases 17594333495296 (4096 * q)) as [Hh|Hl]; [left; unfold KHI; lia | right].
    assert (Hm : (4096 * q - 17594333495296) mod two64 = 4096 * q - 17594333495296 + two64)
      by (symmetry; apply Z.mod_unique with (q := -1); unfold two64 in *; lia).
    rewrite Hm in F10. unfold two64, SH_LO, KHI in *. lia. }
  assert (HA : bv_unsigned (lden E1 XA) = 8 * xq).
  { lnorm. rewrite u_Z_to_bv. unfold vz. fold xq. rewrite Z.add_0_r, Z.add_0_l, Z.mod_small by (unfold two64 in *; lia). reflexivity. }
  assert (HS : bv_unsigned (lden E1 XS) = ASAN_B + xq).
  { lnorm. rewrite u_Z_to_bv. unfold vz. fold xq. rewrite Z.add_0_r, Z.mod_small by (unfold two64 in *; lia). unfold SHB. ring. }
  replace (0 + (-1 * bv_unsigned (E1 31%positive) + (1 * bv_unsigned (E1 235%positive) + 0))) with
          (bv_unsigned (E1 235%positive) - bv_unsigned (E1 31%positive)) in F41 by ring.
  assert (H41 : 0 <= bv_unsigned (E1 235%positive) - bv_unsigned (E1 31%positive) <= 6).
  { pose proof (diff_small (bv_unsigned (E1 235%positive)) (bv_unsigned (E1 31%positive)) 0 6 ltac:(unfold two64 in *; lia) ltac:(lia)
                  ltac:(unfold two64 in *; lia) ltac:(lia) F41) as D. lia. }
  refine (conj F40 (conj H41 (conj F9 (conj Hxq (conj Hcls (conj HA (conj HS _))))))).
  unfold app2r, KHI, KTOP, SH_LO in *. split; [|split; [lia | rewrite Z.mul_comm, Z_mod_mult; reflexivity]].
  destruct Hcls as [Hh|Hl]; [right | left]; lia.
Qed.

(* [comment removed for export] *)
Definition bs_wf (n : positive) (R : region) : bool := (lwf n (rg_base R) && lwf n (rg_size R))%bool.
Lemma rgs_disj_agree_bs : forall n E1 E2 rgs, forallb (bs_wf n) rgs = true -> agree n E1 E2 -> rgs_disj E1 rgs -> rgs_disj E2 rgs.
Proof.
  intros n E1 E2 rgs. induction rgs as [|R rs IH]; intros Hw Ha Hd; [exact I|].
  cbn [forallb] in Hw. apply andb_prop in Hw as [HwR Hws]. destruct Hd as [Hx Hrs]. split; [|exact (IH Hws Ha Hrs)].
  apply Forall_forall. intros R' HR'. rewrite Forall_forall in Hx. pose proof (Hx R' HR') as Hd.
  rewrite forallb_forall in Hws. pose proof (Hws R' HR') as HwR'.
  unfold bs_wf in HwR, HwR'. apply andb_prop in HwR as [HbR HsR]. apply andb_prop in HwR' as [HbR' HsR'].
  unfold rg_disj, rsz in *. rewrite <- (lden_agree n E1 E2 _ HbR Ha), <- (lden_agree n E1 E2 _ HbR' Ha),
    <- (lden_agree n E1 E2 _ HsR Ha), <- (lden_agree n E1 E2 _ HsR' Ha). exact Hd.
Qed.

(* [comment removed for export] *)
Lemma rg_ok_rw_rt : forall E m b sz c, rg_ok BSEGS E m (RG b sz RW c) -> rg_ok BSEGS E m (RG b sz FxCore.RT c).
Proof.
  intros E m b sz c (H1 & H2 & H3 & H4). unfold rg_ok, rsz in *. cbn [rg_base rg_size rg_kind rg_cont] in *.
  split; [exact H1|]. split; [exact H2|]. split; [|exact H4]. intros i Hi. exact (proj1 (H3 i Hi)).
Qed.

(* [comment removed for export] *)
Lemma rw_mix_t : forall E m m' R W lo hi,
  rg_ok BSEGS E m R -> rg_kind R = RW -> munch W m m' -> stk BSEGS m' lo hi ->
  (forall i, 0 <= i < rsz E R -> lo <= bv_unsigned (lden E (rg_base R)) + i < hi \/ Frame.outside W (bv_unsigned (lden E (rg_base R)) + i)) ->
  (forall p v, tget p (rg_cont R) = Some v -> Frame.outside W (bv_unsigned (lden E (rg_base R)) + (Zpos p - 1))) ->
  rg_ok BSEGS E m' R.
Proof.
  intros E m m' R W lo hi HR Hk Hm (S1 & S2 & S) Hw Ht. pose proof (rg_flat BSEGS E m R HR) as (F1 & F2).
  pose proof (u_lden_range E (rg_base R)) as U.
  destruct HR as (H1 & H2 & H3 & H4). split; [exact H1|]. split; [exact H2|]. split.
  - intros i Hi. rewrite Hk. destruct (Hw i Hi) as [Hin|Hout].
    + destruct (S _ Hin) as (Sw & b & Sr). unfold wa in Sr, Sw. rewrite rd1_mrd, Sr. split; [discriminate | exact Sw].
    + pose proof (H3 i Hi) as X. rewrite Hk in X.
      assert (Hx : m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i)) = m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + i))).
      { apply Hm. rewrite u_Z_to_bv, Z.mod_small by (unfold two64 in *; lia). exact Hout. }
      unfold rd1, wview in *. rewrite Hx. exact X.
  - intros p v Hp. destruct (H4 p v Hp) as (Hlt & Hr). split; [exact Hlt|].
    pose proof (Pos2Z.is_pos p).
    assert (Hx : m' (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (Zpos p - 1))) = m (Z_to_bv 64 (bv_unsigned (lden E (rg_base R)) + (Zpos p - 1)))).
    { apply Hm. rewrite u_Z_to_bv, Z.mod_small by (unfold two64 in *; lia). exact (Ht p v Hp). }
    unfold rd1 in *. rewrite Hx. exact Hr.
Qed.

Section EPI.
Variable c : Z.
Variable E1 : valu.
Variable ms1 : machine_state.
Variables (l' : Z) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' : word) (m2 : word -> option byte).
Local Abbreviation R1 := (ms_regs ms1).
Local Abbreviation A1 := (bv_unsigned (lden E1 XA)).
Definition E2 : valu := upds E1 [(205%positive, t0'); (206%positive, t1'); (207%positive, t2'); (210%positive, a0'); (211%positive, a1');
                                 (212%positive, a2'); (213%positive, a3'); (214%positive, a4'); (215%positive, a5'); (216%positive, a6');
                                 (217%positive, a7'); (235%positive, Z_to_bv 64 l')].
Definition ms2 : machine_state :=
  MS (mkR (getr R1 1) (getr R1 2) (getr R1 3) (getr R1 4) t0' t1' t2' (getr R1 8) (getr R1 9)
          a0' a1' a2' a3' a4' a5' a6' a7' (getr R1 18) (getr R1 19)
          (getr R1 20) (getr R1 21) (getr R1 22) (getr R1 23) (getr R1 24) (getr R1 25)
          (getr R1 26) (getr R1 27) (getr R1 28) (getr R1 29) (getr R1 30) (getr R1 31))
     (ms_fregs ms1) (Z_to_bv 64 0x97c30) (ms_fcsr ms1) None m2 (seg_rom BSEGS).

Hypothesis Hcc : c = 0 \/ c = 16.
Hypothesis HD1 : sden BSEGS E1 (with_pc (LM_TAIL_Q c) 0x981cc) ms1.
Hypothesis MU : munch [(A1 + 496, A1 + 498); (bv_unsigned (getr R1 2) - 16, bv_unsigned (getr R1 2))] (ms_mem ms1) m2.
Hypothesis LC2 : rw_cells BSEGS m2 (A1 + 496) [C2 (Z_to_bv 64 l')].
Hypothesis STF : stk BSEGS m2 (bv_unsigned (getr R1 2) - 16) (bv_unsigned (getr R1 2)).
Hypothesis Hl' : 0 <= l' <= 62.

#[using="Type"] Lemma E2_agree : agree 200 E1 E2.
Proof. LiaFast.lf_pins LiaFast.u0. apply upds_agree. repeat constructor; cbn [fst]; lia. Qed.
#[using="Type"] Lemma E2_235 : E2 235%positive = Z_to_bv 64 l'.
Proof. LiaFast.lf_pins LiaFast.u0. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tget_fold_put : forall (l : list (Z * lin)) t p v, Forall (fun q => 0 <= fst q) l ->
  tget p (List.fold_left (fun t '(o, l0) => put_bytes t o (bv8 l0)) l t) = Some v ->
  (exists q, In q l /\ fst q <= Zpos p - 1 < fst q + 8) \/ tget p t = Some v.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction l as [|[o l0] l IH]; intros t p v Hpos H; cbn [List.fold_left] in H; [right; exact H|].
  apply Forall_cons_iff in Hpos as [Ho Hpos]. cbn [fst] in Ho.
  destruct (IH _ p v Hpos H) as [(q & Hq & Hr)|Ht]; [left; exists q; split; [right; exact Hq | exact Hr]|].
  rewrite put_bytes_spec in Ht by exact Ho. unfold bv8 in Ht. rewrite length_map, length_seq in Ht.
  destruct (Z.leb o (Zpos p - 1) && Z.ltb (Zpos p - 1) (o + Z.of_nat 8))%bool eqn:Eb.
  - apply andb_prop in Eb as [E1' E2']. apply Z.leb_le in E1'. apply Z.ltb_lt in E2'.
    left. exists (o, l0). split; [left; reflexivity | cbn [fst]; lia].
  - right. exact Ht.
Qed.
#[using="E1 ms1 Hcc HD1"] Lemma lm_stk_above : forall p v, (c = 0 \/ c = 16) -> tget p (LM_STK c) = Some v -> 2384 - c <= Zpos p - 1 < 2528.
Proof. LiaFast.lf_pins (fun (E1 ms1 Hcc HD1 : LiaFast.U) => LiaFast.u0).
  intros p v Hc H. unfold LM_STK in H.
  destruct (tget_fold_put (LM_SAVED ++ [(2384 - c, SLOT5)]) TEmpty p v ltac:(destruct Hc as [->| ->]; vm_compute; repeat constructor; discriminate) H) as [(q & Hq & Hr)|Ht];
    [|rewrite tget_empty in Ht; discriminate].
  destruct Hc as [->| ->]; cbn in Hq; repeat (destruct Hq as [<-|Hq]; [cbn [fst] in Hr; lia|]); destruct Hq.
Qed.

#[using="Hcc HD1 MU LC2 STF Hl'"] Lemma lmn_epi : sden BSEGS E2 (LM_EPI_P0 c) ms2.
Proof. LiaFast.lf_pins (fun (Hcc HD1 MU LC2 STF Hl' : LiaFast.U) => LiaFast.u0).
  pose proof (lmn_facts c E1 ms1 Hcc HD1) as (F40 & F41 & F9 & Hxq & Hcls & HA & HS & KA & KA' & A8).
  destruct (sden_0 _ _ _ _ HD1) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm).
  cbn [s_pc s_regs s_rgs s_facts s_resv with_pc LM_TAIL_Q] in Hpc, Hresv, HR, HG, HD, HF.
  apply sden0_sden; [destruct Hcc as [->| ->]; vm_compute; reflexivity|].
  refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _))))))); cbn [s_pc s_regs s_rgs s_facts s_resv LM_EPI_P0 ms2 MS ms_pc_val ms_svc_pending ms_resv ms_regs ms_mem ms_fcsr].
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - (* [comment removed for export] *)
    apply regs_ok_of_cases. intros n Hn.
    destruct Hcc as [->| ->].
    all: do 32 (destruct n as [|n];
           [ getr_mkR_norm; rget_norm;
             first [ reflexivity
                   | (rewrite (HR _); rget_norm; reflexivity)
                   | (rewrite (HR _); rget_norm; apply (lden_agree 200 E1 E2); [vm_compute; reflexivity | exact E2_agree])
                   | (lnorm; reflexivity) ]
           |]).
    all: lia.
  - (* [comment removed for export] *)
    assert (Bsp : 0 <= bv_unsigned (E1 4%positive) < two64) by (pose proof (bv_unsigned_in_range _ (E1 4%positive)) as X; unfold bv_modulus in X; exact X).
    assert (FSP1 : fact_ok E1 (FRange (laddc SP (-2528)) KHI (KTOP - 2528))).
    { rewrite Forall_forall in HF. apply HF. unfold LM_FQ, LM_F. destruct Hcc as [->| ->]; cbn [app]; right; left; reflexivity. }
    cbn [fact_ok] in FSP1. lnorm_s_in FSP1. rewrite ?u_Z_to_bv in FSP1. unfold vz in FSP1.
    assert (HSP : KHI + 2528 <= bv_unsigned (E1 4%positive) <= KTOP).
    { destruct (Z.le_gt_cases 2528 (bv_unsigned (E1 4%positive))) as [Hle|Hlt].
      - rewrite Z.mod_small in FSP1 by (unfold two64, KHI, KTOP in *; lia). unfold KHI, KTOP in *; lia.
      - assert (Hm : (-2528 + (1 * bv_unsigned (E1 4%positive) + 0)) mod two64 = -2528 + bv_unsigned (E1 4%positive) + two64)
          by (symmetry; apply Z.mod_unique with (q := -1); unfold two64 in *; lia).
        rewrite Hm in FSP1. unfold two64, KHI, KTOP in *. lia. }
    assert (R2' : getr R1 2 = lden E1 (LM_S1 c)).
    { rewrite (HR _). assert (X : rget (LM_TQ_R c) (rkey 2) = LM_S1 c) by (destruct Hcc as [->| ->]; vm_compute; reflexivity). rewrite X. reflexivity. }
    assert (BS1 : bv_unsigned (getr R1 2) = bv_unsigned (E1 4%positive) - 160 - c).
    { rewrite R2'. unfold LM_S1, SP. rewrite lden_laddc, lden_lvar, u_Z_to_bv, Z.mod_small by (unfold two64, KHI, KTOP in *; destruct Hcc as [->| ->]; lia). ring. }
    assert (B0 : bv_unsigned (lden E1 (laddc SP (-2528))) = bv_unsigned (E1 4%positive) - 2528).
    { unfold SP. rewrite lden_laddc, lden_lvar, u_Z_to_bv, Z.mod_small by (unfold two64, KHI, KTOP in *; lia). ring. }
    assert (B2 : bv_unsigned (lden E1 (laddc XA 496)) = A1 + 496).
    { rewrite lden_laddc, u_Z_to_bv, HA, Z.mod_small by (unfold app2r, two64, KTOP in *; lia). reflexivity. }
    assert (HW : forall x, (forall j Rj, In j [0%nat; 2%nat] -> nth_error (LM_RGS_T c RW false) j = Some Rj ->
                   ~ (bv_unsigned (lden E1 (rg_base Rj)) <= x < bv_unsigned (lden E1 (rg_base Rj)) + rsz E1 Rj)) ->
                 Frame.outside [(A1 + 496, A1 + 498); (bv_unsigned (getr R1 2) - 16, bv_unsigned (getr R1 2))] x).
    { intros x Hx. pose proof (Hx 2%nat _ ltac:(cbn; tauto) ltac:(destruct Hcc as [->| ->]; reflexivity)) as N2.
      pose proof (Hx 0%nat _ ltac:(cbn; tauto) ltac:(destruct Hcc as [->| ->]; reflexivity)) as N0.
      unfold rsz in N2, N0. cbn [rg_base rg_size track] in N2, N0. rewrite B2 in N2. rewrite B0 in N0.
      change (bv_unsigned (lden E1 (lconst 2))) with 2 in N2. change (bv_unsigned (lden E1 (lconst 2528))) with 2528 in N0.
      cbn [Frame.outside]. rewrite BS1. destruct Hcc as [->| ->]; lia. }
    assert (UW : forall i R, nth_error (LM_RGS_T c RW false) i = Some R -> ~ In i [0%nat; 2%nat] -> rg_ok BSEGS E1 (ms_mem ms1) R -> rg_ok BSEGS E1 m2 R).
    { intros i R Hi Hni HR0. exact (rg_ok_unwritten BSEGS E1 (ms_mem ms1) m2 (LM_RGS_T c RW false) _ [0%nat; 2%nat] i R HD Hi Hni MU HW HR0). }
    assert (D02 : rg_disj E1 (nth 0 (LM_RGS_T c RW false) (RGz (lconst 0) 0 RW TEmpty)) (nth 2 (LM_RGS_T c RW false) (RGz (lconst 0) 0 RW TEmpty))).
    { apply (rgs_disj_nth E1 _ 0 2 _ _ HD ltac:(discriminate)); destruct Hcc as [->| ->]; reflexivity. }
    clear HW. pose proof lm_stk_above as LSA.
    destruct Hcc as [->| ->].
    all: pose proof HG as HG'; unfold LM_RGS_T in HG' |- *; cbn [app] in HG' |- *.
    all: clear HG; rename HG' into HG; apply Forall_cons_iff in HG as [G0 HG]; apply Forall_cons_iff in HG as [G1 HG]; apply Forall_cons_iff in HG as [G2 HG]; apply Forall_cons_iff in HG as [G3 HG]; apply Forall_cons_iff in HG as [G4 HG]; apply Forall_cons_iff in HG as [G5 HG]; apply Forall_cons_iff in HG as [G6 HG]; apply Forall_cons_iff in HG as [G7 HG]; apply Forall_cons_iff in HG as [G8 HG]; apply Forall_cons_iff in HG as [G9 HG]; apply Forall_cons_iff in HG as [G10 HG]; apply Forall_cons_iff in HG as [G11 HG]; apply Forall_cons_iff in HG as [G12 HG]; apply Forall_cons_iff in HG as [G13 HG]; apply Forall_cons_iff in HG as [G14 HG]; apply Forall_cons_iff in HG as [G15 HG]; apply Forall_cons_iff in HG as [G16 HG]; apply Forall_cons_iff in HG as [G17 HG]; apply Forall_cons_iff in HG as [G18 HG]; apply Forall_cons_iff in HG as [G19 HG]; apply Forall_cons_iff in HG as [G20 HG]; apply Forall_cons_iff in HG as [G21 HG]; apply Forall_cons_iff in HG as [G22 HG]; apply Forall_cons_iff in HG as [G23 HG]; apply Forall_cons_iff in HG as [G24 HG]; apply Forall_cons_iff in HG as [G25 HG]; apply Forall_cons_iff in HG as [G26 HG]; apply Forall_cons_iff in HG as [G27 HG]; apply Forall_cons_iff in HG as [G28 HG]; apply Forall_cons_iff in HG as [G29 HG]; apply Forall_cons_iff in HG as [G30 HG]; clear HG.
    all: unfold rg_disj, rsz, LM_RGS_T in D02; cbn [app nth rg_base rg_size track] in D02; rewrite B0, B2 in D02;
         change (bv_unsigned (lden E1 (lconst 2528))) with 2528 in D02; change (bv_unsigned (lden E1 (lconst 2))) with 2 in D02.
    all: constructor; [ apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree |];
                        apply (rw_mix_t E1 (ms_mem ms1) m2 _ _ (bv_unsigned (getr R1 2) - 16) (bv_unsigned (getr R1 2)) G0 eq_refl MU STF);
                        [ intros i Hi; unfold rsz in Hi; cbn [rg_base rg_size] in Hi |- *; rewrite B0; change (bv_unsigned (lden E1 (lconst 2528))) with 2528 in Hi;
                          destruct (Z.ltb_spec (bv_unsigned (E1 4%positive) - 2528 + i) (bv_unsigned (getr R1 2) - 16)) as [Hl|Hl];
                          [right; cbn [Frame.outside]; lia | destruct (Z.ltb_spec (bv_unsigned (E1 4%positive) - 2528 + i) (bv_unsigned (getr R1 2))) as [Hl2|Hl2]; [left; lia | right; cbn [Frame.outside]; lia]]
                        | intros p v Hp; cbn [rg_base rg_cont] in Hp |- *; rewrite B0; pose proof (LSA p v ltac:(tauto) Hp) as X; pose proof (Pos2Z.is_pos p);
                          cbn [Frame.outside]; rewrite BS1; lia ] |].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | apply rg_ok_rw_rt; exact (UW 1%nat _ eq_refl ltac:(cbn; intuition discriminate) G1)]|].
    all: constructor; [|].
    1, 3: (* [comment removed for export] *)
      apply track_of_bytes_at; [ | lia | unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); cbn [length]; lia | ];
      [ apply (rg_ok_of_rw_cells BSEGS E2 m2 _ (A1 + 496) [C2 (Z_to_bv 64 l')]); [reflexivity | reflexivity | | | exact LC2];
        [ cbn [rg_base]; change (lden E2 (laddc XA 496)) with (lden E1 (laddc XA 496)); exact B2
        | unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); reflexivity ]
      | cbn [rg_base]; change (lden E2 (laddc XA 496)) with (lden E1 (laddc XA 496)); rewrite B2, Z.add_0_r;
        apply (bytes_at_ext BSEGS _ _ _ _ (proj2 (proj1 LC2))); cbn [cells_bytes cbytes List.map bden]; rewrite app_nil_r; unfold le2; cbn [Z_to_le_bytes];
        change (lden E2 L0V) with (lden E2 (lvar 235)); rewrite lden_lvar, E2_235, Z.shiftr_0_r; reflexivity ].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 3%nat _ eq_refl ltac:(cbn; intuition discriminate) G3)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 4%nat _ eq_refl ltac:(cbn; intuition discriminate) G4)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 5%nat _ eq_refl ltac:(cbn; intuition discriminate) G5)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 6%nat _ eq_refl ltac:(cbn; intuition discriminate) G6)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 7%nat _ eq_refl ltac:(cbn; intuition discriminate) G7)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 8%nat _ eq_refl ltac:(cbn; intuition discriminate) G8)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 9%nat _ eq_refl ltac:(cbn; intuition discriminate) G9)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 10%nat _ eq_refl ltac:(cbn; intuition discriminate) G10)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 11%nat _ eq_refl ltac:(cbn; intuition discriminate) G11)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 12%nat _ eq_refl ltac:(cbn; intuition discriminate) G12)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 13%nat _ eq_refl ltac:(cbn; intuition discriminate) G13)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 14%nat _ eq_refl ltac:(cbn; intuition discriminate) G14)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 15%nat _ eq_refl ltac:(cbn; intuition discriminate) G15)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 16%nat _ eq_refl ltac:(cbn; intuition discriminate) G16)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 17%nat _ eq_refl ltac:(cbn; intuition discriminate) G17)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 18%nat _ eq_refl ltac:(cbn; intuition discriminate) G18)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 19%nat _ eq_refl ltac:(cbn; intuition discriminate) G19)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 20%nat _ eq_refl ltac:(cbn; intuition discriminate) G20)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 21%nat _ eq_refl ltac:(cbn; intuition discriminate) G21)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 22%nat _ eq_refl ltac:(cbn; intuition discriminate) G22)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 23%nat _ eq_refl ltac:(cbn; intuition discriminate) G23)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 24%nat _ eq_refl ltac:(cbn; intuition discriminate) G24)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 25%nat _ eq_refl ltac:(cbn; intuition discriminate) G25)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 26%nat _ eq_refl ltac:(cbn; intuition discriminate) G26)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 27%nat _ eq_refl ltac:(cbn; intuition discriminate) G27)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 28%nat _ eq_refl ltac:(cbn; intuition discriminate) G28)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 29%nat _ eq_refl ltac:(cbn; intuition discriminate) G29)]|].
    all: constructor; [apply (rg_ok_agree BSEGS 200 E1 E2); [vm_compute; reflexivity | exact E2_agree | exact (UW 30%nat _ eq_refl ltac:(cbn; intuition discriminate) G30)]|].
    all: constructor.
  - (* [comment removed for export] *)
    apply (rgs_disj_agree_bs 200 E1 E2); [destruct Hcc as [->| ->]; vm_compute; reflexivity | exact E2_agree |].
    apply (rgs_disj_shape E1 (LM_RGS_T c RW false)); [destruct Hcc as [->| ->]; vm_compute; reflexivity | exact HD].
  - (* [comment removed for export] *)
    unfold LM_FE. apply Forall_app. split.
    + unfold LM_FQ in HF. apply Forall_app in HF as [HF1 _].
      assert (Hw : forallb (fwf 200) (LM_F c) = true) by (destruct Hcc as [->| ->]; vm_compute; reflexivity).
      rewrite forallb_forall in Hw. rewrite Forall_forall in HF1 |- *. intros f Hf.
      exact (fact_ok_agree 200 E1 E2 f (Hw f Hf) E2_agree (HF1 f Hf)).
    + constructor; [|constructor]. cbn [fact_ok]. change (lden E2 L0V) with (lden E2 (lvar 235)). rewrite lden_lvar, E2_235, u_Z_to_bv.
      rewrite Z.mod_small by (unfold two64; lia). lia.
  - exact Hfrm.
Qed.
End EPI.

(* [comment removed for export] *)
Theorem lmn_run : forall c E1 ms1 (POST : machine_state -> Prop), (c = 0 \/ c = 16) ->
  sden BSEGS E1 (with_pc (LM_TAIL_Q c) 0x981cc) ms1 -> ms_rom ms1 = seg_rom BSEGS ->
  (forall ws1 l' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' m2,
     u64arr BSEGS (ms_mem ms1) (bv_unsigned (lden E1 XA)) ws1 -> length ws1 = 62%nat ->
     bnorm ws1 (Z.to_nat l') -> 0 <= l' <= bv_unsigned (E1 235%positive) ->
     munch [(bv_unsigned (lden E1 XA) + 496, bv_unsigned (lden E1 XA) + 498);
            (bv_unsigned (getr (ms_regs ms1) 2) - 16, bv_unsigned (getr (ms_regs ms1) 2))] (ms_mem ms1) m2 ->
     wmono BSEGS (ms_mem ms1) m2 ->
     sden BSEGS (E2 E1 l' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7') (LM_EPI_P0 c)
                (ms2 ms1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' m2) ->
     evt BSEGS POST (ms2 ms1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' m2)) ->
  evt BSEGS POST ms1.
Proof.
  intros c E1 ms1 POST Hcc HD1 Hrom K.
  pose proof (lmn_facts c E1 ms1 Hcc HD1) as (F40 & F41 & F9 & Hxq & Hcls & HA & HS & KA & KA' & A8).
  destruct (sden_0 _ _ _ _ HD1) as (Hpc & Hsvc & Hresv & HR & HG & HD & HF & Hfrm).
  cbn [s_pc s_regs s_rgs s_facts s_resv with_pc LM_TAIL_Q] in Hpc, Hresv, HR, HG, HD, HF. unfold rsv_ok in Hresv.
  set (A1 := bv_unsigned (lden E1 XA)) in *.
  assert (KA1 : app2r A1 (A1 + 504)) by (rewrite HA; exact KA). assert (KA1' : A1 + 504 <= KTOP) by (rewrite HA; exact KA').
  (* [comment removed for export] *)
  assert (Bsp : 0 <= bv_unsigned (E1 4%positive) < two64) by (pose proof (bv_unsigned_in_range _ (E1 4%positive)) as X; unfold bv_modulus in X; exact X).
  assert (FSP1 : fact_ok E1 (FRange (laddc SP (-2528)) KHI (KTOP - 2528))).
  { rewrite Forall_forall in HF. apply HF. unfold LM_FQ, LM_F. destruct Hcc as [->| ->]; cbn [app]; right; left; reflexivity. }
  cbn [fact_ok] in FSP1. lnorm_s_in FSP1. rewrite ?u_Z_to_bv in FSP1. unfold vz in FSP1.
  assert (HSP : KHI + 2528 <= bv_unsigned (E1 4%positive) <= KTOP).
  { destruct (Z.le_gt_cases 2528 (bv_unsigned (E1 4%positive))) as [Hle|Hlt].
    - rewrite Z.mod_small in FSP1 by (unfold two64, KHI, KTOP in *; lia). unfold KHI, KTOP in *; lia.
    - assert (Hm : (-2528 + (1 * bv_unsigned (E1 4%positive) + 0)) mod two64 = -2528 + bv_unsigned (E1 4%positive) + two64)
        by (symmetry; apply Z.mod_unique with (q := -1); unfold two64 in *; lia).
      rewrite Hm in FSP1. unfold two64, KHI, KTOP in *. lia. }
  clear FSP1.
  assert (R2' : getr (ms_regs ms1) 2 = lden E1 (LM_S1 c)).
  { rewrite (HR _). assert (X : rget (LM_TQ_R c) (rkey 2) = LM_S1 c) by (destruct Hcc as [->| ->]; vm_compute; reflexivity). rewrite X. reflexivity. }
  assert (BS1 : bv_unsigned (getr (ms_regs ms1) 2) = bv_unsigned (E1 4%positive) - 160 - c).
  { rewrite R2'. unfold LM_S1, SP. rewrite lden_laddc, lden_lvar, u_Z_to_bv, Z.mod_small by (unfold two64, KHI, KTOP in *; destruct Hcc as [->| ->]; lia). ring. }
  assert (B0 : bv_unsigned (lden E1 (laddc SP (-2528))) = bv_unsigned (E1 4%positive) - 2528).
  { unfold SP. rewrite lden_laddc, lden_lvar, u_Z_to_bv, Z.mod_small by (unfold two64, KHI, KTOP in *; lia). ring. }
  assert (R1r : getr (ms_regs ms1) 1 = Z_to_bv 64 0x97c30) by (rewrite (HR _); destruct Hcc as [->| ->]; rget_norm; lnorm; reflexivity).
  assert (R10 : getr (ms_regs ms1) 10 = lden E1 XA) by (rewrite (HR _); destruct Hcc as [->| ->]; rget_norm; reflexivity).
  (* [comment removed for export] *)
  assert (RGAT : forall k R, nth_error (LM_RGS_T c RW false) k = Some R -> rg_ok BSEGS E1 (ms_mem ms1) R).
  { intros k R Hk. rewrite Forall_forall in HG. apply HG. exact (nth_error_In _ _ Hk). }
  pose proof (RGAT 0%nat (RG (laddc SP (-2528)) (lconst 2528) RW (LM_STK c)) ltac:(destruct Hcc as [->| ->]; reflexivity)) as G0.
  pose proof (RGAT 1%nat (RG XA (lconst 496) RW TEmpty) ltac:(destruct Hcc as [->| ->]; reflexivity)) as G1.
  pose proof (RGAT 2%nat (track (RG (laddc XA 496) (lconst 2) RW TEmpty) 0 [BV L0V 0; BV L0V 1]) ltac:(destruct Hcc as [->| ->]; reflexivity)) as G2.
  pose proof (RGAT 3%nat xsh_c ltac:(destruct Hcc as [->| ->]; reflexivity)) as G3.
  pose proof (RGAT 16%nat sb_uar_c ltac:(destruct Hcc as [->| ->]; reflexivity)) as G16.
  pose proof (RGAT 28%nat (RGz (lconst 0xda000) 0x6000 RO TEmpty) ltac:(destruct Hcc as [->| ->]; reflexivity)) as G28.
  assert (D01 : rg_disj E1 (RG (laddc SP (-2528)) (lconst 2528) RW (LM_STK c)) (RG XA (lconst 496) RW TEmpty)).
  { apply (rgs_disj_nth E1 _ 0 1 _ _ HD ltac:(discriminate)); destruct Hcc as [->| ->]; reflexivity. }
  assert (D02 : rg_disj E1 (RG (laddc SP (-2528)) (lconst 2528) RW (LM_STK c)) (track (RG (laddc XA 496) (lconst 2) RW TEmpty) 0 [BV L0V 0; BV L0V 1])).
  { apply (rgs_disj_nth E1 _ 0 2 _ _ HD ltac:(discriminate)); destruct Hcc as [->| ->]; reflexivity. }
  clear RGAT.
  assert (B2 : bv_unsigned (lden E1 (laddc XA 496)) = A1 + 496).
  { rewrite lden_laddc, u_Z_to_bv, Z.mod_small by (rewrite HA in *; unfold app2r, two64, KTOP in *; lia). reflexivity. }
  unfold rg_disj, rsz in D01, D02. cbn [rg_base rg_size track] in D01, D02. rewrite B0 in D01, D02. rewrite B2 in D02. fold A1 in D01.
  change (bv_unsigned (lden E1 (lconst 2528))) with 2528 in D01, D02. change (bv_unsigned (lden E1 (lconst 496))) with 496 in D01.
  change (bv_unsigned (lden E1 (lconst 2))) with 2 in D02.
  destruct (u64arr_of_rg BSEGS E1 _ _ A1 62 G1 ltac:(left; reflexivity) eq_refl
              ltac:(unfold rsz; cbn [rg_size]; rewrite lden_lconst, u_Z_to_bv, Z.mod_small by (unfold two64; lia); reflexivity)) as (ws1 & CUR & L62).
  assert (LENC1 : rw_cells BSEGS (ms_mem ms1) (A1 + 496) [C2 (Z_to_bv 64 (bv_unsigned (E1 235%positive)))]).
  { split; [split; [cbn; tauto|] |].
    - pose proof (track_bytes_at BSEGS E1 (ms_mem ms1) _ 0 _ G2 ltac:(lia) ltac:(cbn; lia)) as X. cbn [rg_base] in X. rewrite B2, Z.add_0_r in X.
      apply (bytes_at_ext BSEGS _ _ _ _ X). cbn [cells_bytes cbytes List.map bden]. rewrite app_nil_r. unfold le2. cbn [Z_to_le_bytes].
      change (lden E1 L0V) with (lden E1 (lvar 235)). rewrite lden_lvar, Z_to_bv_bv_unsigned, Z.shiftr_0_r. reflexivity.
    - cbn [cells_size csize]. change (Z.of_nat (2 + 0)) with 2.
      pose proof (wr_at_of_rg BSEGS E1 _ _ _ _ (rg_ok_untrack BSEGS E1 _ _ _ _ _ _ G2) ltac:(left; reflexivity) ltac:(cbn [rg_base]; exact B2) eq_refl) as W.
      unfold rsz in W. cbn [rg_size] in W. rewrite lden_lconst, u_Z_to_bv, Z.mod_small in W by (unfold two64; lia). exact W. }
  assert (SHX1 : shz BSEGS (ms_mem ms1) (ASAN_B + A1 / 8) 63).
  { split; [lia|]. replace (A1 / 8) with (bv_unsigned (E1 30%positive)) by (rewrite HA, Z.mul_comm, Z.div_mul by lia; reflexivity).
    exact (zeros_bytes_of_rt BSEGS E1 _ _ _ 63 G3 ltac:(vm_compute; reflexivity) ltac:(lia) HS). }
  assert (STK : stk BSEGS (ms_mem ms1) (bv_unsigned (getr (ms_regs ms1) 2) - 16) (bv_unsigned (getr (ms_regs ms1) 2))).
  { pose proof (stk_of_rg BSEGS E1 _ _ (bv_unsigned (E1 4%positive) - 2528) (bv_unsigned (E1 4%positive)) G0 ltac:(left; reflexivity) ltac:(cbn [rg_base]; exact B0)
                  ltac:(unfold rsz; cbn [rg_size]; change (bv_unsigned (lden E1 (lconst 2528))) with 2528; ring)) as X.
    rewrite BS1. destruct (stk_split BSEGS _ _ (bv_unsigned (E1 4%positive) - 160 - c - 16) _ X ltac:(destruct Hcc as [->| ->]; lia)) as (_ & X2).
    destruct (stk_split BSEGS _ _ (bv_unsigned (E1 4%positive) - 160 - c) _ X2 ltac:(destruct Hcc as [->| ->]; lia)) as (X3 & _). exact X3. }
  assert (PRG : pristine (ms_mem ms1) RELRO_LO RELRO_HI).
  { exact (pristine_of_rg_ro BSEGS E1 _ _ _ _ G28 eq_refl ltac:(reflexivity) ltac:(reflexivity)). }
  assert (BC : ro_cells BSEGS (ms_mem ms1) BCELL [C8 (Z_to_bv 64 ASAN_B)]).
  { rewrite sb_uar_c_eq in G16. unfold sb_uar_t in G16.
    pose proof (cont_bytes_at BSEGS E1 (ms_mem ms1) _ 0 (bk8 SHB) G16 ltac:(lia) ltac:(cbn; lia) ltac:(vm_compute; reflexivity)) as Y.
    cbn [rg_base track RGz] in Y. change (bv_unsigned (lden E1 (lconst 943736))) with 943736 in Y. rewrite Z.add_0_r in Y.
    apply (ro_cells_of_bytes BSEGS _ _ _ _ Y); [vm_compute; reflexivity | cbn; tauto]. }
  assert (SEP : bv_unsigned (getr (ms_regs ms1) 2) <= A1 \/ A1 + 498 <= bv_unsigned (getr (ms_regs ms1) 2) - 16).
  { rewrite BS1. clear -D01 D02 Hcc BS1 HSP. clearbody A1. unfold KHI, KTOP in *. destruct Hcc as [->| ->]; lia. }
  assert (IMGE : IMG_END <= bv_unsigned (getr (ms_regs ms1) 2) - 16) by (rewrite BS1; clear -HSP Hcc; unfold IMG_END, KHI, KTOP in *; destruct Hcc as [->| ->]; lia).
  assert (KH : KHI <= bv_unsigned (getr (ms_regs ms1) 2) - 16) by (rewrite BS1; clear -HSP Hcc; unfold KHI, KTOP in *; destruct Hcc as [->| ->]; lia).
  assert (KT : bv_unsigned (getr (ms_regs ms1) 2) <= KTOP) by (rewrite BS1; clear -HSP Hcc; unfold KHI, KTOP in *; destruct Hcc as [->| ->]; lia).
  (* [comment removed for export] *)
  assert (Heqv : ms_eqv (kms BSEGS ms1) ms1).
  { pose proof (kms_eqv BSEGS ms1 Hsvc) as X. rewrite <- Hrom, with_rom_eta in X. exact X. }
  apply (evt_eqv_l BSEGS _ ms1 (kms BSEGS ms1) (ms_eqv_sym _ _ Heqv)).
  unfold kms, mkR_of. rewrite Hpc, Hresv, R10.
  eapply evt_cut.
  { exact (B_normalize.normalize_spec (getr (ms_regs ms1) 1) (getr (ms_regs ms1) 2) (getr (ms_regs ms1) 3) (getr (ms_regs ms1) 4)
             (getr (ms_regs ms1) 5) (getr (ms_regs ms1) 6) (getr (ms_regs ms1) 7) (getr (ms_regs ms1) 8) (getr (ms_regs ms1) 9)
             (lden E1 XA) (getr (ms_regs ms1) 11) (getr (ms_regs ms1) 12) (getr (ms_regs ms1) 13) (getr (ms_regs ms1) 14)
             (getr (ms_regs ms1) 15) (getr (ms_regs ms1) 16) (getr (ms_regs ms1) 17) (getr (ms_regs ms1) 18) (getr (ms_regs ms1) 19)
             (getr (ms_regs ms1) 20) (getr (ms_regs ms1) 21) (getr (ms_regs ms1) 22) (getr (ms_regs ms1) 23) (getr (ms_regs ms1) 24)
             (getr (ms_regs ms1) 25) (getr (ms_regs ms1) 26) (getr (ms_regs ms1) 27) (getr (ms_regs ms1) 28) (getr (ms_regs ms1) 29)
             (getr (ms_regs ms1) 30) (getr (ms_regs ms1) 31) (ms_fregs ms1) (ms_fcsr ms1) (ms_mem ms1) ws1 (bv_unsigned (E1 235%positive))
             CUR L62 LENC1 F40 STK PRG BC SEP IMGE KH KT KA1 KA1' SHX1). }
  intros ms' HP. unfold normalize_post in HP.
  destruct HP as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m2 & Hms & MU & WM & CUR2 & LC2 & STF). subst ms'.
  replace (ret_pc (getr (ms_regs ms1) 1)) with (Z_to_bv 64 0x97c30)
    by (rewrite R1r; symmetry; apply ret_pc_even_w; reflexivity).
  set (l' := Z.of_nat (norm_len ws1 (Z.to_nat (bv_unsigned (E1 235%positive))))) in *.
  assert (Hl' : 0 <= l' <= bv_unsigned (E1 235%positive)).
  { pose proof (norm_len_le ws1 (Z.to_nat (bv_unsigned (E1 235%positive)))) as X. unfold l'. lia. }
  assert (BN : bnorm ws1 (Z.to_nat l')) by (unfold l'; rewrite Nat2Z.id; apply norm_len_bnorm).
  unfold normalize_W in MU.
  apply (K ws1 l' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' m2 CUR L62 BN Hl' MU WM).
  exact (lmn_epi c E1 ms1 l' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' m2 Hcc HD1 MU LC2 STF ltac:(lia)).
Qed.
(* [comment removed for export] *)
Definition is_ro (k : rkind) : bool := match k with RO => true | _ => false end.
Fixpoint kinds_ok_acc (wi : list nat) (j : nat) (rgs : list region) : bool :=
  match rgs with
  | [] => true
  | R :: rs => ((existsb (Nat.eqb j) wi || is_rt (rg_kind R) || is_ro (rg_kind R)) && kinds_ok_acc wi (S j) rs)%bool
  end.
Definition kinds_ok (wi : list nat) (rgs : list region) : bool := kinds_ok_acc wi 0 rgs.

Lemma kinds_ok_acc_spec : forall wi rgs j0 j R, kinds_ok_acc wi j0 rgs = true -> nth_error rgs j = Some R -> ~ In (j0 + j)%nat wi ->
  is_rt (rg_kind R) = true \/ rg_kind R = RO.
Proof.
  intros wi rgs. induction rgs as [|R0 rs IH]; intros j0 j R H Hj Hni; [destruct j; discriminate|].
  cbn [kinds_ok_acc] in H. apply andb_prop in H as [H1 H2]. destruct j as [|j].
  - cbn in Hj. injection Hj as ->. rewrite Nat.add_0_r in Hni.
    apply orb_prop in H1 as [H1|H1]; [apply orb_prop in H1 as [H1|H1]|].
    + exfalso. apply existsb_exists in H1 as (k & Hk & Hk2). apply Nat.eqb_eq in Hk2. subst k. exact (Hni Hk).
    + left. exact H1.
    + right. unfold is_ro in H1. destruct (rg_kind R); try discriminate. reflexivity.
  - cbn in Hj. apply (IH (S j0) j R H2 Hj). replace (S j0 + j)%nat with (j0 + S j)%nat by lia. exact Hni.
Qed.
Lemma kinds_ok_spec : forall wi rgs j R, kinds_ok wi rgs = true -> nth_error rgs j = Some R -> ~ In j wi ->
  is_rt (rg_kind R) = true \/ rg_kind R = RO.
Proof. intros wi rgs j R H Hj Hni. exact (kinds_ok_acc_spec wi rgs 0 j R H Hj Hni). Qed.

Lemma ro_none : forall segs E m rgs R x, Forall (rg_ok segs E m) rgs -> In R rgs -> rg_kind R = RO -> in_rg E R x -> m x = None.
Proof.
  intros segs E m rgs R x HF Hin Hk Hx. rewrite Forall_forall in HF. destruct (HF R Hin) as (H1 & H2 & H3 & _).
  unfold in_rg in Hx. pose proof (H3 (bv_unsigned x - bv_unsigned (lden E (rg_base R))) ltac:(lia)) as X. rewrite Hk in X.
  destruct X as (X & _). replace (bv_unsigned (lden E (rg_base R)) + (bv_unsigned x - bv_unsigned (lden E (rg_base R)))) with (bv_unsigned x) in X by ring.
  rewrite Z_to_bv_bv_unsigned in X. exact X.
Qed.

Lemma frame_idx : forall E rgs (wi : list nat) (m m' : word -> option byte) x,
  kinds_ok wi rgs = true ->
  (forall j R, In j wi -> nth_error rgs j = Some R -> ~ in_rg E R x) ->
  (fr_pt E rgs x -> m' x = m x) ->
  (forall R, In R rgs -> rg_kind R = RO -> in_rg E R x -> m x = None /\ m' x = None) ->
  m' x = m x.
Proof.
  intros E rgs wi m m' x Hk Hw Hfr Hro.
  assert (Hcl : fr_pt E rgs x \/ exists R, In R rgs /\ rg_kind R = RO /\ in_rg E R x).
  { destruct (Exists_dec (fun R => in_rg E R x) rgs) as [He|Hn].
    - intros R. unfold in_rg. destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R))) (bv_unsigned x)) as [A1|A1];
        [destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [B1|B1]|]; [left; lia | right; lia | right; lia].
    - apply Exists_exists in He as (R & HR & Hx). apply In_nth_error in HR as (j & Hj).
      destruct (In_dec Nat.eq_dec j wi) as [Hi|Hni]; [exfalso; exact (Hw j R Hi Hj Hx)|].
      destruct (kinds_ok_spec wi rgs j R Hk Hj Hni) as [Hrt|Hro'].
      + left. right. apply Exists_exists. exists R. split; [exact (nth_error_In _ _ Hj) | split; [exact Hrt | exact Hx]].
      + right. exists R. split; [exact (nth_error_In _ _ Hj) | split; [exact Hro' | exact Hx]].
    - left. left. unfold FxStep.outside. rewrite Forall_forall. intros R HR.
      destruct (Z_le_gt_dec (bv_unsigned (lden E (rg_base R))) (bv_unsigned x)) as [A1|A1]; [|left; lia].
      destruct (Z_lt_ge_dec (bv_unsigned x) (bv_unsigned (lden E (rg_base R)) + rsz E R)) as [B1|B1]; [|right; lia].
      exfalso. apply Hn. apply Exists_exists. exists R. split; [exact HR | unfold in_rg; lia]. }
  destruct Hcl as [Hf|(R & HR & Hro' & Hx)]; [exact (Hfr Hf)|].
  destruct (Hro R HR Hro' Hx) as (H1 & H2). rewrite H1, H2. reflexivity.
Qed.
