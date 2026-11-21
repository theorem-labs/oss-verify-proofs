(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition hx (hd : Z) : Z := hd mod 2 ^ 8 * 2 ^ 8 + hd / 2 ^ 8.

Definition head_B (w1 : iw) : ares unit :=
  let s := w_s w1 in let c := w_c w1 in let r := w_r w1 in
  let hd := ir_hold r in
  let hd2 := hd / 2 ^ 4 in
  let len := hd2 mod 2 ^ 4 + 8 in
  let r2 := irset_bits (irset_hold r hd2) (ir_bits r - 4) in
  if negb (hx hd mod 31 =? 0) then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_incorrect_header_check) r)
  else if negb (hd mod 2 ^ 4 =? 8) then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_unknown_compression_method) r)
  else if 15 <? len then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_window_size) r2)
  else ARun tt (mkW (iset_mode (iset_check (iset_flags (iset_dmax s (2 ^ len)) 0) 1) (if negb (Z.land hd2 512 =? 0) then DICTID else TYPE))
                    (icset_adler c 1) (irset_bits (irset_hold r2 0) 0)).

Lemma BITSv_mod : forall h n, 0 <= h -> 0 <= n <= 32 -> BITSv h n = h mod 2 ^ n.
Proof. intros h n Hh Hn. rewrite BITSv_land, Z.land_ones by lia. reflexivity. Qed.

Lemma hx_eq : forall hd, 0 <= hd < 2 ^ 64 -> wrap64 (shl32 (BITSv hd 8) 8 + Z.shiftr hd 8) = hx hd.
Proof.
  intros hd Hhd. unfold hx. rewrite BITSv_mod by lia.
  assert (H8 : 0 <= hd mod 2 ^ 8 < 2 ^ 8) by (apply Z.mod_pos_bound; lia).
  assert (Hq : 0 <= hd / 2 ^ 8 < 2 ^ 56) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold shl32. rewrite Z.shiftl_mul_pow2 by lia. rewrite wrap32_id by lia. rewrite Z.shiftr_div_pow2 by lia.
  apply wrap64_id. lia.
Qed.

Lemma arm_HEAD_run : forall s c r s1 c1 r1,
  (is_wrap s = 5 \/ is_wrap s = 1) -> is_wbits s = 15 ->
  NEEDBITS 16 (mkW s c r) = ARun tt (mkW s1 c1 r1) -> s1 = s ->
  4 <= ir_bits r1 < 64 -> 0 <= ir_hold r1 < 2 ^ ir_bits r1 ->
  arm_HEAD ivar_ref (mkW s c r) = head_B (mkW s1 c1 r1).
Proof.
  intros s c r s1 c1 r1 Hw Hwb HN -> Hb Hh.
  assert (Hh64 : 0 <= ir_hold r1 < 2 ^ 64) by (pose proof (Z.pow_lt_mono_r 2 (ir_bits r1) 64 ltac:(lia) ltac:(lia)); lia).
  assert (Hq4 : 0 <= ir_hold r1 / 2 ^ 4 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Hm4 : 0 <= (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
  unfold arm_HEAD. mstep1 (@gs_eq inflate_state). rewrite (wrap15_eqb0 _ Hw). cbn [Z.eqb].
  rewrite abind_run, HN. mstep1 HOLD_eq. rewrite (wrap15_and2 _ Hw), (wrap15_and1 _ Hw). cbn [negb andb orb].
  mstep1 BITS_eq. rewrite hx_eq by exact Hh64.
  unfold head_B. cbn [w_s w_c w_r].
  destruct (hx (ir_hold r1) mod 31 =? 0); cbn [negb]; [| rewrite go_bad_eq; reflexivity].
  mstep1 BITS_eq. rewrite (BITSv_mod (ir_hold r1) 4) by lia. unfold Z_DEFLATED.
  destruct (ir_hold r1 mod 2 ^ 4 =? 8); cbn [negb]; [| rewrite go_bad_eq; reflexivity].
  mstep1 DROPBITS_eq. irnorm. rewrite Z.shiftr_div_pow2 by lia. rewrite wrap32_id by lia.
  mstep1 BITS_eq. irnorm. rewrite (BITSv_mod (ir_hold r1 / 2 ^ 4) 4) by lia.
  (* 1.4 (smodel14-r1's HEAD row): the window-size check first, then wbits := len only if wbits is 0 *)
  mstep1 (@gs_eq inflate_state). rewrite Hwb. cbn [Z.eqb negb andb].
  destruct (15 <? (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 + 8) eqn:L; cbn [orb]; [rewrite go_bad_eq; reflexivity|].
  try rewrite Hwb. cbn [Z.eqb]. mstep1 (@aret_eq unit).
  unfold aux. cbn [iv_aux ivar_ref]. mstep1 us_eq. mstep1 us_eq. mstep1 set_adler_check_eq. mstep1 HOLD_eq. mstep1 set_mode_eq.
  rewrite INITBITS_eq. irnorm. unfold iadler32_init. unfold shl32. rewrite Z.shiftl_1_l.
  apply Z.ltb_ge in L. rewrite wrap32_id; [reflexivity|].
  split; [apply Z.pow_nonneg; lia|]. apply (Z.pow_lt_mono_r 2); lia.
Qed.

Lemma arm_HEAD_leave : forall s c r w1,
  (is_wrap s = 5 \/ is_wrap s = 1) -> NEEDBITS 16 (mkW s c r) = ALeave w1 -> arm_HEAD ivar_ref (mkW s c r) = ALeave w1.
Proof.
  intros s c r w1 Hw HN. unfold arm_HEAD. mstep1 (@gs_eq inflate_state). rewrite (wrap15_eqb0 _ Hw). cbn [Z.eqb].
  rewrite abind_run, HN. reflexivity.
Qed.


Definition ilH : cfg := ilSx [0x1d0f4; 0x1da84] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section HeadLoop.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition HJS (wv : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ LVR v r R /\ getr R 13 = zw (ir_bits r) /\ getr R 12 = zw wv /\ getr R 27 = zw (cv_I0 v + ir_next r).
  Definition HJE (wv : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ LVR v r R /\ getr R 12 = zw wv /\ getr R 27 = zw (cv_I0 v + ir_next r) /\ getr R 26 = zw (cv_I0 v + ir_next r).

  Ltac open_hjs HJ :=
    let X := fresh in pose proof HJ as X; unfold HJS, LVR in X;
    destruct X as (HF & (G9 & G18 & G1 & G22 & G23) & G13 & G12 & G26); open_fix HF.

  Ltac hjs_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 :=
    let G9 := fresh in let G22 := fresh in let G23 := fresh in let G13 := fresh in let G26 := fresh in let G27 := fresh in
    symex_reg HR (18%bv : reg) as G9; symex_reg HR (23%bv : reg) as G22; symex_reg HR (24%bv : reg) as G23;
    symex_reg HR (13%bv : reg) as G13; symex_reg HR (27%bv : reg) as G26; symex_reg HR (26%bv : reg) as G27;
    cbn [famA] in G22; rewrite bmod_get in G22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in G22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold HJS, HJE, LVR, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ apply (LFIX_frame v _ _ _ HF Hfr); reflexivity
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite G9; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite G22; f_equal; lia
          | rewrite G23; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite G13; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite G26; f_equal; lia
          | rewrite G27; f_equal; lia
          | match goal with |- ?G => idtac "HJS LEFT" G end ].

  Lemma head_step_H : forall wv s c r R M,
    LMEM v (mkW s c r) M -> HJS wv c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < 16 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d0f4) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d0f4) M s6_rom)
               /\ HJS wv c (pull1 c r) R1.
  Proof.
    intros wv s c r R M HM HJ RI CI Hb Hh. open_hjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symex ilH 14%nat [true; true] (@nil (option expr)) [(13, EVar 41%nat)] (@nil (nat * Z)) v r (@nil Z) NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1d0f4) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    hjs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma head_step_E : forall wv s c r R M,
    LMEM v (mkW s c r) M -> HJS wv c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 16 -> 16 <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d0f4) M s6_rom) (mkst R1 (Z_to_bv 64 0x1da84) M s6_rom)
               /\ HJE wv c (pull1 c r) R1.
  Proof.
    intros wv s c r R M HM HJ RI CI Hb Hb8 Hh. open_hjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    arm_symex ilH 14%nat [true; false] (@nil (option expr)) [(13, EVar 41%nat)] (@nil (nat * Z)) v r (@nil Z) NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1d0f4) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    hjs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0.
  Qed.

  Lemma head_dry : forall wv s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> HJS wv c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 16 -> ir_have r = 0 ->
    exists R1, msteps s6_segs (mkst R (Z_to_bv 64 0x1d0f4) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros wv s c r R M HM HRC HJ RI CI Hb Hh. open_hjs HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    arm_symex ilH 8%nat [false] [RVal (EVar 45%nat)] [(13, EVar 41%nat)] [(45%nat, 2 ^ 64)] v r
      [ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1d0f4) M s6_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (9%bv : reg) as G8'.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. regs_via Hfr; first [exact G26 | rewrite G8'; apply zw_neg_mod].
  Qed.

  Lemma head_A : forall s c r R M,
    (is_wrap s = 5 \/ is_wrap s = 1) -> LMEM v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R -> RINV (cv_NI v) (cv_NO v) r ->
    exists R1,
      if 16 <=? ir_bits r
      then msteps s6_segs (mkst R (Z_to_bv 64 0x1d0e0) M s6_rom) (mkst R1 (Z_to_bv 64 0x1da84) M s6_rom) /\ HJE (is_wrap s) c r R1
      else msteps s6_segs (mkst R (Z_to_bv 64 0x1d0e0) M s6_rom) (mkst R1 (Z_to_bv 64 0x1d0f4) M s6_rom) /\ HJS (is_wrap s) c r R1.
  Proof.
    intros s c r R M Hw HM HF HV RI.
    open_ictx C. open_lmem HM. open_fix HF. open_vars HV. open_rinv RI. unfold mapped in *.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    pose proof (is6_wrap _ _ _ _ Msc) as C16. pose proof (wrap15_range _ Hw) as Hwr. pose proof (wrap15_ne0 _ Hw) as Hw0.
    destruct (Z.leb_spec 16 (ir_bits r)) as [GE|LT].
    - arm_symex ilH 8%nat [false; true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d0e0) M s6_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (12%bv : reg) as G12'. symex_reg HR1 (26%bv : reg) as G27'.
      unfold HJE, LVR. split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|]. regs_via Hfr; first [exact G12' | exact G27'].
    - arm_symex ilH 8%nat [false; false] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1d0e0) M s6_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (12%bv : reg) as G12'. symex_reg HR1 (13%bv : reg) as G13'.
      unfold HJS, LVR. split; [apply (LFIX_frame v R R1 _ HF Hfr); reflexivity|]. regs_via Hfr; first [exact G13' | exact G12'].
  Qed.

  Lemma head_need : forall s c r R M,
    (is_wrap s = 5 \/ is_wrap s = 1) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    match NEEDBITS 16 (mkW s c r) with
    | ARun _ w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6_segs (mkst R (Z_to_bv 64 0x1d0e0) M s6_rom) (mkst R1 (Z_to_bv 64 0x1da84) M s6_rom)
        /\ HJE (is_wrap s) c r1 R1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ same5 r r1 /\ 16 <= ir_bits r1
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6_segs (mkst R (Z_to_bv 64 0x1d0e0) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom)
        /\ LREG_leave v (mkW s c r1) R1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ same5 r r1
    | ARet _ _ => False
    end.
  Proof.
    intros s c r R M Hw HM HRC HF HV RI CI.
    pose proof RI as RI'. open_rinv RI'.
    destruct (head_A s c r R M Hw HM HF HV RI) as (R1 & HA).
    destruct (Z.leb_spec 16 (ir_bits r)) as [GE|LT].
    - destruct HA as (Hms1 & HJE1). unfold NEEDBITS. rewrite NEEDBITS_k_done by (cbn; exact GE).
      exists r, R1. split; [reflexivity|]. split; [exact Hms1|]. split; [exact HJE1|]. split; [exact RI|]. split; [apply same5_refl | exact GE].
    - destruct HA as (Hms1 & HJS1).
      pose proof (need_loop v 16 0x1d0f4 0x1da84 (HJS (is_wrap s)) (HJE (is_wrap s)) C ltac:(lia) (head_step_H (is_wrap s)) (head_step_E (is_wrap s)) (head_dry (is_wrap s))
                    8%nat s c r R1 M HM HRC HJS1 RI CI LT ltac:(cbn; clear - LT Rbits; lia)) as NL.
      change (NEEDBITS_k 8 16) with (NEEDBITS 16) in NL.
      destruct (NEEDBITS 16 (mkW s c r)) as [[] w1 | w1 | rc w1]; [| | exact NL].
      + destruct NL as (r1 & R2 & E & Hms2 & HJE & RI1 & S5 & Hb1 & _). exists r1, R2.
        split; [exact E|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HJE|]. split; [exact RI1|]. split; [exact S5 | clear - Hb1; lia].
      + destruct NL as (r1 & R2 & E & Hms2 & HL & RI1 & S5 & _). exists r1, R2.
        split; [exact E|]. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|]. split; [exact HL|]. split; [exact RI1 | exact S5].
  Qed.
End HeadLoop.
End FXG.
