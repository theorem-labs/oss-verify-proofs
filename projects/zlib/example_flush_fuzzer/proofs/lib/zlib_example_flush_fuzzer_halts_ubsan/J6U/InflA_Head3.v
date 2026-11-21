(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6.

Module InflA_Head1.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


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
  (* 1.4: the window-size check comes first, then wbits := len only if it is 0 (here it is 15) *)
  mstep1 (@gs_eq inflate_state). rewrite Hwb. cbn [Z.eqb negb andb].
  destruct (15 <? (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 + 8) eqn:L; cbn [orb]; [rewrite go_bad_eq; reflexivity|].
  mstep1 (@aret_eq unit).
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


Definition ilH : cfg := ilSx [0x1f0ac; 0x1fdf0] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section HeadLoop.
  Variable v : icv.
  Hypothesis C : ictx v.

  Definition LFIXa (R : bvmap 5 word) : Prop :=
    getr R 2 = zw (cv_sp v - INF_FRAME) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
    /\ getr R 1 = zw 16209 /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.
  Lemma LFIX_LFIXa : forall R, LFIX v R -> LFIXa R.
  Proof. intros R HF. unfold LFIX in HF. destruct HF as (G2 & G27 & G13 & G8 & G11 & G1 & G3 & G4). unfold LFIXa. repeat split; assumption. Qed.
  Ltac open_fixa HF :=
    let X := fresh in pose proof HF as X; unfold LFIXa, INF_FRAME in X;
    destruct X as (G2 & G27 & G8 & G1 & G3 & G4).

  Definition HJS (wv h0 n0 b0 : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXa R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r) /\ getr R 14 = zw wv
    /\ getr R 27 = zw (ir_have r) /\ getr R 16 = zw (cv_I0 v + ir_next r) /\ getr R 11 = zw (cv_I0 v + ir_next r)
    /\ getr R 15 = zw (ir_bits r) /\ getr R 12 = zw (ir_bits r)
    /\ getr R 23 = zw h0 /\ getr R 26 = zw (cv_I0 v + n0) /\ getr R 19 = zw b0
    /\ ir_have r + ir_next r = h0 + n0 /\ ir_bits r = b0 + 8 * (ir_next r - n0) /\ 0 <= h0 < 2 ^ 31 /\ 0 <= b0 /\ 0 <= n0.
  Definition HJE (wv : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIXa R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r) /\ getr R 14 = zw wv
    /\ getr R 20 = zw (cv_I0 v + ir_next r) /\ getr R 27 = zw (ir_have r) /\ getr R 12 = zw (ir_bits r).

  Ltac open_hjs HJ :=
    let X := fresh in pose proof HJ as X; unfold HJS in X;
    destruct X as (HF & G9 & G22 & G14 & G26 & G16 & G11 & G15 & G12 & G24 & G25 & G18 & E1 & E2 & Hh0 & Hb0 & Hn00); open_fixa HF.

  Definition hjs_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
     (27, EVar 36%nat); (16, EAdd (EVar 43%nat) (EVar 44%nat)); (11, EAdd (EVar 43%nat) (EVar 44%nat)); (15, EVar 41%nat); (12, EVar 41%nat);
     (23, EVar 45%nat); (26, EAdd (EVar 43%nat) (EVar 46%nat)); (19, EVar 47%nat)].

  Ltac lfixa_close Hfr HR :=
    unfold LFIXa, INF_FRAME;
    repeat match goal with |- _ /\ _ => split end;
    lazymatch goal with |- getr _ ?n = _ =>
      first [ rewrite (Hfr n eq_refl); assumption
            | let G := fresh "G" in symex_reg HR n as G; rewrite G; first [ reflexivity | assumption | apply zw_neg_mod | f_equal; lia ]
            | match goal with |- ?G => idtac "LFIXa LEFT" G end ]
    end.

  Ltac hjs_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00 :=
    let Q26 := fresh in let Q22 := fresh in let Q15 := fresh in let Q12 := fresh in let Q16 := fresh in let Q11 := fresh in let Q19 := fresh in
    symex_reg HR (27%bv : reg) as Q26; symex_reg HR (25%bv : reg) as Q22; symex_reg HR (15%bv : reg) as Q15; symex_reg HR (12%bv : reg) as Q12;
    symex_reg HR (16%bv : reg) as Q16; symex_reg HR (11%bv : reg) as Q11; symex_reg HR (20%bv : reg) as Q19;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold HJS, HJE, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- LFIXa _ => lfixa_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q26; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q22; f_equal; lia
          | rewrite Q15; f_equal; lia
          | rewrite Q12; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite Q16; f_equal; lia
          | rewrite Q11; f_equal; lia
          | rewrite Q19; f_equal; lia
          | clear - E1 E2 Hh0 Hb0 Hn00; lia
          | match goal with |- ?G => idtac "HJS LEFT" G end ].

  Lemma head_step_H : forall wv h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> HJS wv h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < 16 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f0ac) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f0ac) M s6u_rom)
               /\ HJS wv h0 n0 b0 c (pull1 c r) R1.
  Proof.
    intros wv h0 n0 b0 s c r R M HM HJ RI CI Hb Hh. open_hjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP hjs_pins ilH 20%nat [true; true; true] (@nil (option expr)) (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1f0ac) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    hjs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma head_step_E : forall wv h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> HJS wv h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 16 -> 16 <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f0ac) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fdf0) M s6u_rom)
               /\ HJE wv c (pull1 c r) R1.
  Proof.
    intros wv h0 n0 b0 s c r R M HM HJ RI CI Hb Hb8 Hh. open_hjs HJ.
    open_ictx C. open_lmem HM. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP hjs_pins ilH 20%nat [true; true; false] (@nil (option expr)) (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s) (mkst R (Z_to_bv 64 0x1f0ac) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    hjs_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma head_dry : forall wv h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> HJS wv h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 16 -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f0ac) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros wv h0 n0 b0 s c r R M HM HRC HJ RI CI Hb Hh. open_hjs HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP hjs_pins ilH 16%nat [false] [RVal (EVar 48%nat); RVal (EVar 35%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64)] v r
      [h0; n0; b0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f0ac) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (23%bv : reg) as Q24.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. repeat match goal with |- _ /\ _ => split end;
      first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
            | rewrite Q26; apply zw_neg_mod
            | rewrite Q24; f_equal; clear - Hh; lia
            | rewrite Q18; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | rewrite Q25; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | lazymatch goal with |- getr _ ?n = _ => let G := fresh in symex_reg HR1 n as G; rewrite G; first [reflexivity | assumption] end
            | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.

  Lemma head_A : forall s c r R M,
    (is_wrap s = 5 \/ is_wrap s = 1) -> LMEM v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R -> RINV (cv_NI v) (cv_NO v) r ->
    exists R1,
      if 16 <=? ir_bits r
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1f088) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fdf0) M s6u_rom) /\ HJE (is_wrap s) c r R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1f088) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f0ac) M s6u_rom) /\ HJS (is_wrap s) (ir_have r) (ir_next r) (ir_bits r) c r R1.
  Proof.
    intros s c r R M Hw HM HF HV RI.
    open_ictx C. open_lmem HM. open_fix HF. open_vars HV. open_rinv RI. unfold mapped in *.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    pose proof (is6_wrap _ _ _ _ Msc) as C16. pose proof (wrap15_range _ Hw) as Hwr. pose proof (wrap15_ne0 _ Hw) as Hw0.
    pose proof (LFIX_LFIXa R HF) as HFa.
    destruct (Z.leb_spec 16 (ir_bits r)) as [GE|LT].
    - arm_symex ilH 10%nat [false; true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f088) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (14%bv : reg) as G14'. symex_reg HR1 (20%bv : reg) as G19'. symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (12%bv : reg) as G12'.
      unfold HJE. split; [lfixa_close Hfr HR1|]. regs_via Hfr; first [exact G14' | exact G19' | exact G26' | exact G12' | idtac].
    - arm_symex ilH 12%nat [false; false] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 8)] v r [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f088) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (14%bv : reg) as G14'. symex_reg HR1 (27%bv : reg) as G26'. symex_reg HR1 (16%bv : reg) as G16'. symex_reg HR1 (11%bv : reg) as G11'.
      symex_reg HR1 (15%bv : reg) as G15'. symex_reg HR1 (12%bv : reg) as G12'.
      unfold HJS. split; [lfixa_close Hfr HR1|]. regs_via Hfr; first [exact G14' | exact G26' | exact G16' | exact G11' | exact G15' | exact G12' | idtac].
      + clear; lia.
      + clear; lia.
      + clear - Rhv0; lia.
      + clear - Rhv0 Rnh Rnx0 CI0; lia.
      + clear - Rbits; lia.
      + clear - Rnx0; lia.
  Qed.

  Lemma head_need : forall s c r R M,
    (is_wrap s = 5 \/ is_wrap s = 1) ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LFIX v R -> LVARS v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    match NEEDBITS 16 (mkW s c r) with
    | ARun _ w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 0x1f088) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1fdf0) M s6u_rom)
        /\ HJE (is_wrap s) c r1 R1 /\ RINV (cv_NI v) (cv_NO v) r1 /\ same5 r r1 /\ 16 <= ir_bits r1
    | ALeave w1 => exists r1 R1, w1 = mkW s c r1
        /\ msteps s6u_segs (mkst R (Z_to_bv 64 0x1f088) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
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
      pose proof (need_loop v 16 0x1f0ac 0x1fdf0 (HJS (is_wrap s) (ir_have r) (ir_next r) (ir_bits r)) (HJE (is_wrap s)) C ltac:(lia)
                    (head_step_H _ _ _ _) (head_step_E _ _ _ _) (head_dry _ _ _ _)
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
End InflA_Head1.

Module InflA_Head2.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvKit OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel.InflateInvRun.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U.Segs6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflArmLib6b OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U.InflNeed6 InflA_Head1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Definition INV31 : Z := 0xef7bdef7bdef7bdf.

Lemma mod31_magic : forall x, 0 <= x < 2 ^ 64 ->
  ((x * INV31) mod 2 ^ 64 <? MOD31_MAGIC) = (x mod 31 =? 0).
Proof.
  intros x Hx.
  assert (HI : (31 * INV31) mod 2 ^ 64 = 1) by reflexivity.
  assert (HC : 31 * (MOD31_MAGIC - 1) = 2 ^ 64 - 16) by reflexivity.
  set (y := (x * INV31) mod 2 ^ 64).
  assert (Hy : 0 <= y < 2 ^ 64) by (subst y; apply Z.mod_pos_bound; lia).
  assert (E31 : (31 * y) mod 2 ^ 64 = x).
  { subst y. rewrite Z.mul_mod_idemp_r by lia. rewrite (Z.mul_comm x INV31), Z.mul_assoc.
    rewrite <- Z.mul_mod_idemp_l by lia. rewrite HI. rewrite Z.mul_1_l. apply Z.mod_small. exact Hx. }
  unfold MOD31_MAGIC in *.
  destruct (Z.ltb_spec y 595056260442243601) as [LT|GE]; destruct (Z.eqb_spec (x mod 31) 0) as [D|ND]; try reflexivity; exfalso.
  - apply ND. rewrite <- E31. rewrite (Z.mod_small (31 * y) (2 ^ 64)) by lia. rewrite Z.mul_comm. apply Z.mod_mul. lia.
  - pose proof (Z.div_mod x 31 ltac:(lia)) as E. rewrite D, Z.add_0_r in E.
    assert (Hq : 0 <= x / 31 <= 595056260442243601 - 1) by (split; [apply Z.div_pos; lia | ]; apply Z.div_le_upper_bound; lia).
    assert (Ey : y = x / 31).
    { subst y. rewrite E at 1. rewrite <- Z.mul_assoc, (Z.mul_comm 31), <- Z.mul_assoc. rewrite <- Z.mul_mod_idemp_r by lia.
      rewrite (Z.mul_comm INV31 31), HI, Z.mul_1_r. apply Z.mod_small. lia. }
    lia.
Qed.

Definition INV31X : Z := -38083600668303590433.
Lemma hx_exec : forall h, 0 <= h < 2 ^ 64 -> (h * 2 ^ 56) mod 2 ^ 64 / 2 ^ 48 + h / 2 ^ 8 = hx h.
Proof.
  intros h Hh. unfold hx. f_equal.
  rewrite <- (Z.mod_small (h mod 2 ^ 8 * 2 ^ 8) (2 ^ 16)) by (pose proof (Z.mod_pos_bound h (2 ^ 8) ltac:(lia)); lia).
  rewrite <- !Z.shiftl_mul_pow2 by lia. rewrite <- !Z.shiftr_div_pow2 by lia. rewrite <- !Z.land_ones by lia.
  apply Z.bits_inj'. intros n Hn.
  rewrite Z.shiftr_spec, !Z.land_spec by lia.
  destruct (Z_lt_le_dec n 16).
  - rewrite (Z.ones_spec_low 16 n) by lia. rewrite (Z.ones_spec_low 64 (n + 48)) by lia. rewrite !andb_true_r.
    rewrite Z.shiftl_spec by lia. destruct (Z_lt_le_dec n 8).
    + rewrite (Z.shiftl_spec_low _ 8 n) by lia. rewrite Z.testbit_neg_r by lia. reflexivity.
    + rewrite Z.shiftl_spec_high by lia. rewrite Z.land_spec, Z.ones_spec_low by lia. rewrite andb_true_r. f_equal. lia.
  - rewrite (Z.ones_spec_high 16 n) by lia. rewrite (Z.ones_spec_high 64 (n + 48)) by lia. rewrite !andb_false_r. reflexivity.
Qed.
Lemma inv31_exec : forall x, (x * INV31X) mod 2 ^ 64 = (x * INV31) mod 2 ^ 64.
Proof. intros x. rewrite <- Z.mul_mod_idemp_r by lia. change (INV31X mod 2 ^ 64) with INV31. reflexivity. Qed.

Lemma land_pow2_0 : forall x n, 0 <= n -> (Z.land x (2 ^ n) = 0 <-> Z.testbit x n = false).
Proof.
  intros x n Hn. split.
  - intros H. apply (f_equal (fun z => Z.testbit z n)) in H. rewrite Z.land_spec, Z.pow2_bits_true, andb_true_r, Z.bits_0 in H by lia. exact H.
  - intros H. apply Z.bits_inj'. intros m Hm. rewrite Z.land_spec, Z.bits_0, Z.pow2_bits_eqb by lia.
    destruct (Z.eqb_spec n m) as [<-|NE]; [rewrite H; reflexivity | apply andb_false_r].
Qed.
Lemma szwrap64_nonneg : forall y, 0 <= y < 2 ^ 64 -> (0 <= szwrap 64 y <-> y < 2 ^ 63).
Proof.
  intros y Hy. unfold szwrap. change (2 ^ (64 - 1)) with (2 ^ 63).
  destruct (Z_lt_le_dec y (2 ^ 63)) as [L|G].
  - rewrite Z.mod_small by lia. lia.
  - rewrite <- (Z.mod_unique_pos (y + 2 ^ 63) (2 ^ 64) 1 (y + 2 ^ 63 - 2 ^ 64)) by lia. lia.
Qed.
Lemma lt63_testbit : forall y, 0 <= y < 2 ^ 64 -> (y < 2 ^ 63 <-> Z.testbit y 63 = false).
Proof.
  intros y Hy. rewrite Z.testbit_false by lia. split.
  - intros L. rewrite Z.div_small by lia. reflexivity.
  - intros H. destruct (Z_lt_le_dec y (2 ^ 63)) as [L|G]; [exact L|]. exfalso.
    assert (E : y / 2 ^ 63 = 1).
    { symmetry. apply Z.div_unique_pos with (r := y - 2 ^ 63); lia. }
    rewrite E in H. cbv in H. discriminate.
Qed.
Lemma bit13_exec : forall h, 0 <= h < 2 ^ 64 ->
  (Z.land (h / 2 ^ 4) 512 =? 0) = (0 <=? szwrap 64 (h * 2 ^ 50)).
Proof.
  intros h Hh. rewrite <- (szwrap_mod 64 (h * 2 ^ 50)) by lia.
  assert (Hy : 0 <= (h * 2 ^ 50) mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  assert (T1 : Z.testbit (h / 2 ^ 4) 9 = Z.testbit h 13) by (rewrite Z.div_pow2_bits by lia; reflexivity).
  assert (T2 : Z.testbit ((h * 2 ^ 50) mod 2 ^ 64) 63 = Z.testbit h 13).
  { rewrite Z.mod_pow2_bits_low by lia. rewrite Z.mul_pow2_bits by lia. reflexivity. }
  replace 512 with (2 ^ 9) by reflexivity.
  destruct (Z.eqb_spec (Z.land (h / 2 ^ 4) (2 ^ 9)) 0) as [E|NE]; destruct (Z.leb_spec 0 (szwrap 64 ((h * 2 ^ 50) mod 2 ^ 64))) as [G|L]; try reflexivity; exfalso.
  - apply (proj1 (land_pow2_0 (h / 2 ^ 4) 9 ltac:(lia))) in E. rewrite T1, <- T2 in E.
    apply (proj2 (lt63_testbit _ Hy)) in E. apply (proj2 (szwrap64_nonneg _ Hy)) in E. lia.
  - apply NE. apply (proj2 (land_pow2_0 (h / 2 ^ 4) 9 ltac:(lia))). rewrite T1, <- T2.
    apply (proj1 (lt63_testbit _ Hy)). apply (proj1 (szwrap64_nonneg _ Hy)). exact G.
Qed.

End FXG.
Ltac wrap_brc Hw :=
  lazymatch goal with
  | |- _ mod _ <> _ => clear - Hw; destruct Hw as [-> | ->]; cbv; discriminate
  | |- _ <> _ mod _ => clear - Hw; destruct Hw as [-> | ->]; cbv; discriminate
  | |- _ mod _ = _ => clear - Hw; destruct Hw as [-> | ->]; reflexivity
  | |- _ / _ = _ => clear - Hw; destruct Hw as [-> | ->]; reflexivity
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section HeadBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_fixa HF :=
    let X := fresh in pose proof HF as X; unfold LFIXa, INF_FRAME in X;
    destruct X as (G2 & G27 & G8 & G1 & G3 & G4).
  Ltac open_hje HJ :=
    let X := fresh in pose proof HJ as X; unfold HJE in X;
    destruct X as (HF & G9 & G22 & G14 & G19 & G26 & G12); open_fixa HF.
  Definition hje_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
     (20, EAdd (EVar 43%nat) (EVar 44%nat)); (27, EVar 36%nat); (12, EVar 41%nat)].

  Definition ilAd : cfg := CFG [] [] [EVar 32%nat] [] [].

  Lemma MFRAME_of_scratch : forall p M M',
    agree_out (SCR v) M M' -> (forall x : word, M x <> None -> M' x <> None) -> MFRAME v p p M M'.
  Proof.
    intros p M M' Hag Hg. split; [lia|]. split; [exact Hg|].
    intros x N1 N2 N3 N4. apply Hag. unfold SCR, INF_FRAME, INF_SCRATCH in *. clear - N1. intros [Hin | Hin]; [| exact Hin]. lia.
  Qed.

  Lemma adler_null6 : forall R M (ra : Z),
    getr R 11 = zw 0 -> getr R 12 = zw 0 -> getr R 1 = zw ra -> getr R 2 = zw (cv_sp v - 256) -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    mapped M (cv_sp v - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH) ->
    exists R' M', msteps s6u_segs (mkst R (Z_to_bv 64 0x1af3c) M s6u_rom) (mkst R' (Z_to_bv 64 ra) M' s6u_rom)
      /\ getr R' 10 = zw 1 /\ (forall rg, reg_in rg [12; 10; 13; 14]%bv = false -> getr R' rg = getr R rg)
      /\ agree_out (SCR v) M M' /\ (forall x : word, M x <> None -> M' x <> None).
  Proof.
    intros R M ra G11 G12 G1 G2 Hra Hra2 Hmap. pose proof (ic_sp _ C) as Csp. unfold INF_FRAME, INF_SCRATCH, IMG6_TOP in Csp, Hmap. unfold mapped in Hmap.
    symex s6u_segs ilAd 40%nat [true; true] (@nil (option expr))
      [(11, ELit 0); (12, ELit 0); (1, EVar 32%nat); (2, EVar 33%nat)] [(32%nat, 2 ^ 64); (33%nat, 2 ^ 63)] NoRegions [ra; cv_sp v - 256] NoVals F0 F0'
      (mkst R (Z_to_bv 64 0x1af3c) M s6u_rom) R' HR' Hfr Hms.
    all: try arm_side.
    all: try match goal with |- ?G => idtac "ADLNULL LEFT" G end.
    { rewrite land_m2_even by exact Hra2. reflexivity. }
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?Mx _) => exists R', Mx end.
    split; [by_run Hms|]. symex_reg HR' (10%bv : reg) as G10'. split; [exact G10'|]. split; [fr_weak Hfr|].
    split.
    - do 13 (apply (agree_scratch_store v C); [| unfold INF_FRAME, INF_SCRATCH; clear - Csp; lia | unfold INF_FRAME, INF_SCRATCH; cbn; clear - Csp; lia]). apply agree_out_refl.
    - intros x Hx. repeat apply wbytes_grows. exact Hx.
  Qed.

  Ltac regs_via3 HfrD Hfr3 :=
    repeat match goal with |- _ /\ _ => split end;
    try (rewrite HfrD by reflexivity);
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr3 n eq_refl); assumption end
          | match goal with |- ?G => idtac "REGS3 LEFT" G end ].

  Definition pinsB : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat));
     (20, EAdd (EVar 43%nat) (EVar 44%nat)); (27, EVar 36%nat); (25, EVar 40%nat); (10, ELit 1)].

  Lemma head_ok : forall s c r1 R M,
    is_mode s = HEAD -> (is_wrap s = 5 \/ is_wrap s = 1) -> is_wbits s = 15 -> is_head s = 0 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> HJE v (is_wrap s) c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 16 <= ir_bits r1 ->
    (((ir_hold r1 * 2 ^ 56) mod 2 ^ 64 / 2 ^ 48 + ir_hold r1 / 2 ^ 8) * -38083600668303590433) mod 2 ^ 64 < 595056260442243601 ->
    ir_hold r1 mod 2 ^ 4 = 8 -> ~ 15 < (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 + 8 ->
    let len := (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 + 8 in
    let r2 := irset_bits (irset_hold r1 (ir_hold r1 / 2 ^ 4)) (ir_bits r1 - 4) in
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fdf0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r1) M
           (ARun tt (mkW (iset_mode (iset_check (iset_flags (iset_dmax s (2 ^ len)) 0) 1) (if negb (Z.land (ir_hold r1 / 2 ^ 4) 512 =? 0) then DICTID else TYPE))
                         (icset_adler c 1) (irset_bits (irset_hold r2 0) 0))) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode Hw Hwb Hhd HM HRC HX HJ RI CI Hb16 DV M8 BW len r2. open_hje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_head _ _ _ _ Msc) as C48. rewrite Hhd in C48.
    pose proof (is6_wbits _ _ _ _ Msc) as C56. rewrite Hwb in C56.
    pose proof (wrap15_range _ Hw) as Hwr. pose proof (wrap15_and2 _ Hw) as Hw2. pose proof (wrap15_and1 _ Hw) as Hw1.
    pose proof (mod31_cell M Mrod : cell s6u_segs M (0 + 67208) 8 595056260442243601) as Crod.
    unfold head_B. cbn [w_s w_c w_r].
    assert (Hhx : 0 <= hx (ir_hold r1) < 2 ^ 57).
    { unfold hx. pose proof (Z.mod_pos_bound (ir_hold r1) (2 ^ 8) ltac:(lia)).
      assert (0 <= ir_hold r1 / 2 ^ 8 < 2 ^ 56) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
    assert (Hq4 : 0 <= ir_hold r1 / 2 ^ 4 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hm4 : 0 <= (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
    assert (Hm4' : 0 <= ir_hold r1 mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
    assert (BW' : ~ 7 < (ir_hold r1 / 2 ^ 4) mod 2 ^ 4) by (clear - BW; lia).
    (* zlib 1.4: the window-size tests come first (len > 15: bltu 7,k; then wbits = 0?; wbits >= len?), then
       `if (wbits == 0) wbits = len` (bnez, taken: wbits = 15) *)
    arm_symexP hje_pins ilS 60%nat [true; true; false; false; false; false; false; true; true]
      [RVal (ELit 0); RVal (EVar 35%nat); RVal (ELit 595056260442243601); RVal (ELit 15)]
      [(14, EVar 45%nat)] [(45%nat, 8)] v r1 [is_wrap s] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1fdf0) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try wrap_brc Hw.
    all: try arm_side.
    all: try match goal with |- ?G => idtac "LEFTA" G end.
    set (k := (ir_hold r1 / 2 ^ 4) mod 2 ^ 4) in *.
    assert (Edm : zaluw ALU_SLL 256 k = 2 ^ len).
    { rewrite zaluw_sll_small; [| lia | clear - Hm4; lia | clear - BW' Hm4; assert (2 ^ k <= 2 ^ 7) by (apply Z.pow_le_mono_r; lia); lia].
      subst len. change 256 with (2 ^ 8). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    rewrite Edm in Hms1.
    set (MA1 := wbytes M (zw (cv_S v + 28)) (Z_to_le_bytes 4 0)) in *.
    set (MA := wbytes MA1 (zw (cv_S v + 32)) (Z_to_le_bytes 4 (2 ^ len))) in *.
    set (sA := iset_dmax (iset_flags s 0) (2 ^ len)).
    assert (HMA1 : LMEM v (mkW (iset_flags s 0) c r1) MA1).
    { apply (LMEM_store_scalar v C s c r1 _ M 28 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_flags M (cv_S v) _ s 0 Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HMA : LMEM v (mkW sA c r1) MA).
    { apply (LMEM_store_scalar v C _ c r1 _ MA1 32 _ HMA1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_dmax MA1 (cv_S v) _ _ _ (lm_sc _ _ _ HMA1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    symex_reg HR1 (11%bv : reg) as A11. symex_reg HR1 (12%bv : reg) as A12. symex_reg HR1 (1%bv : reg) as A1.
    assert (A2 : getr R1 2 = zw (cv_sp v - 256)) by (rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2).
    assert (HmapA : mapped MA (cv_sp v - INF_FRAME - INF_SCRATCH) (INF_FRAME + INF_SCRATCH)) by (subst MA MA1; apply mapped_wbytes; apply mapped_wbytes; exact (lm_map_f _ _ _ HM)).
    destruct (adler_null6 R1 MA 135788 A11 A12 A1 A2 ltac:(lia) ltac:(reflexivity) HmapA) as (R2 & MA' & Hms2 & B10 & Hfr2 & HagA & HgA).
    assert (HMA' : LMEM v (mkW sA c r1) MA') by (exact (LMEM_agree_scratch v C sA c r1 MA MA' HMA Hput HagA HgA)).
    pose proof HMA' as HMA''. clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mleftc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
    clear Fsv Fflush Flens Fnlens Fm16224 Fjtab Fbad Fin Fsane Ffl5 Fnext Fwork Fcodes Flenb Fdistb.
    open_lmem HMA''. open_frame Mfr. unfold mapped in *.
    assert (B2 : getr R2 2 = zw (cv_sp v - 256)) by (rewrite (Hfr2 (2%bv : reg) eq_refl); exact A2).
    assert (B27 : getr R2 8 = zw (cv_S v)) by (rewrite (Hfr2 (8%bv : reg) eq_refl), (Hfr1 (8%bv : reg) eq_refl); exact G27).
    assert (B8 : getr R2 18 = zw (cv_ZP v)) by (rewrite (Hfr2 (18%bv : reg) eq_refl), (Hfr1 (18%bv : reg) eq_refl); exact G8).
    assert (B9 : getr R2 9 = zw (cv_P0 v + ir_put r1)) by (rewrite (Hfr2 (9%bv : reg) eq_refl), (Hfr1 (9%bv : reg) eq_refl); exact G9).
    assert (B19 : getr R2 20 = zw (cv_I0 v + ir_next r1)) by (rewrite (Hfr2 (20%bv : reg) eq_refl), (Hfr1 (20%bv : reg) eq_refl); exact G19).
    assert (B26 : getr R2 27 = zw (ir_have r1)) by (rewrite (Hfr2 (27%bv : reg) eq_refl), (Hfr1 (27%bv : reg) eq_refl); exact G26).
    assert (B22 : getr R2 25 = zw (ir_hold r1)) by (rewrite (Hfr2 (25%bv : reg) eq_refl), (Hfr1 (25%bv : reg) eq_refl); exact G22).
    assert (B3 : getr R2 3 = getr (cv_R0 v) 3) by (rewrite (Hfr2 (3%bv : reg) eq_refl), (Hfr1 (3%bv : reg) eq_refl); exact G3).
    assert (B4 : getr R2 4 = getr (cv_R0 v) 4) by (rewrite (Hfr2 (4%bv : reg) eq_refl), (Hfr1 (4%bv : reg) eq_refl); exact G4).
    clear HR1.
    rewrite bit13_exec by exact Rhold64.
    set (m := if negb (0 <=? szwrap 64 (ir_hold r1 * 2 ^ 50)) then DICTID else TYPE).
    assert (Hm : (0 <= szwrap 64 (ir_hold r1 * 2 ^ 50) /\ m = TYPE) \/ (szwrap 64 (ir_hold r1 * 2 ^ 50) < 0 /\ m = DICTID)).
    { subst m. destruct (Z.leb_spec 0 (szwrap 64 (ir_hold r1 * 2 ^ 50))); [left | right]; split; try reflexivity; lia. }
    assert (HB : exists R3,
      msteps s6u_segs (mkst R2 (Z_to_bv 64 135788) MA' s6u_rom)
             (mkst R3 (Z_to_bv 64 pc6_disp)
                (wbytes (wbytes (wbytes MA' (zw (cv_S v + 40)) (Z_to_le_bytes 8 1)) (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 1)) (zw (cv_S v + 8)) (Z_to_le_bytes 4 m)) s6u_rom)
      /\ getr R3 1 = zw 16209 /\ getr R3 13 = zw (cv_ZP v) /\ getr R3 11 = zw (cv_flush v)
      /\ getr R3 25 = zw 0 /\ getr R3 19 = zw 0 /\ getr R3 26 = zw (cv_I0 v + ir_next r1) /\ getr R3 23 = zw (ir_have r1)
      /\ (forall rg, reg_in rg [10; 25; 19; 26; 23; 11; 13; 1]%bv = false -> getr R3 rg = getr R2 rg)).
    { destruct Hm as [[Hs ->] | [Hs ->]].
      - arm_symexP (@nil (Z * expr)) ilS 30%nat [true]
          [RVal (EVar 35%nat); RVal (ELit 16209)]
          pinsB (@nil (nat * Z)) v r1 (@nil Z) NoVals F0
          (mkst R2 (Z_to_bv 64 135788) MA' s6u_rom) R3 HR3 Hfr3 Hms3.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTB1" G end.
        exists R3. split; [by_run Hms3|].
        symex_reg HR3 (1%bv : reg) as Q1. symex_reg HR3 (13%bv : reg) as Q13. symex_reg HR3 (11%bv : reg) as Q11.
        symex_reg HR3 (25%bv : reg) as Q22. symex_reg HR3 (19%bv : reg) as Q18. symex_reg HR3 (26%bv : reg) as Q25. symex_reg HR3 (23%bv : reg) as Q24.
        repeat match goal with |- _ /\ _ => split end; try assumption. fr_weak Hfr3.
      - arm_symexP (@nil (Z * expr)) ilS 30%nat [false]
          [RVal (EVar 35%nat); RVal (ELit 16209)]
          pinsB (@nil (nat * Z)) v r1 (@nil Z) NoVals F0
          (mkst R2 (Z_to_bv 64 135788) MA' s6u_rom) R3 HR3 Hfr3 Hms3.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTB2" G end.
        exists R3. split; [by_run Hms3|].
        symex_reg HR3 (1%bv : reg) as Q1. symex_reg HR3 (13%bv : reg) as Q13. symex_reg HR3 (11%bv : reg) as Q11.
        symex_reg HR3 (25%bv : reg) as Q22. symex_reg HR3 (19%bv : reg) as Q18. symex_reg HR3 (26%bv : reg) as Q25. symex_reg HR3 (23%bv : reg) as Q24.
        repeat match goal with |- _ /\ _ => split end; try assumption. fr_weak Hfr3. }
    clear Hm. destruct HB as (R3 & Hms3 & Q1 & Q13 & Q11 & Q22 & Q18 & Q25 & Q24 & Hfr3).
    set (MB1 := wbytes MA' (zw (cv_S v + 40)) (Z_to_le_bytes 8 1)) in *.
    set (MB2 := wbytes MB1 (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 1)) in *.
    set (MB := wbytes MB2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 m)) in *.
    set (r3 := mkIR (ir_next r1) (ir_have r1) (ir_put r1) (ir_left r1) 0 0 (ir_in r1) (ir_out r1) (ir_ret r1)).
    set (c' := icset_adler c 1).
    set (s' := iset_mode (iset_check (iset_flags (iset_dmax s (2 ^ len)) 0) 1) m).
    assert (HMB1 : LMEM v (mkW (iset_check sA 1) c r3) MB1).
    { apply (LMEM_regs v (iset_check sA 1) c r1 c r3); [| reflexivity ..].
      apply (LMEM_store_scalar v C sA c r1 _ MA' 40 _ HMA'); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_check MA' (cv_S v) _ sA 1 (lm_sc _ _ _ HMA')); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HMB2 : LMEM v (mkW (iset_check sA 1) c' r3) MB2) by (exact (LMEM_store_adler v C _ c r3 MB1 1 HMB1 Hput)).
    assert (HMB : LMEM v (mkW s' c' r3) MB).
    { replace s' with (iset_mode (iset_check sA 1) m) by (subst s' sA; destruct s; reflexivity).
      apply (LMEM_store_scalar v C _ c' r3 _ MB2 8 _ HMB2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode MB2 (cv_S v) _ _ m (lm_sc _ _ _ HMB2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (Hmv : m = TYPE \/ m = DICTID) by (subst m; destruct (0 <=? _); [left | right]; reflexivity).
    assert (Q2 : getr R3 2 = zw (cv_sp v - 256)) by (rewrite (Hfr3 (2%bv : reg) eq_refl); exact B2).
    assert (Q27 : getr R3 8 = zw (cv_S v)) by (rewrite (Hfr3 (8%bv : reg) eq_refl); exact B27).
    assert (Hsm : is_mode s' = m) by (subst s'; destruct s; reflexivity).
    assert (Hrange : HEAD <= is_mode s' <= HEAD + 30) by (rewrite Hsm; clear - Hmv; destruct Hmv as [E|E]; rewrite E; cbv [HEAD TYPE DICTID]; lia).
    destruct (disp6u v s' c' r3 R3 MB C HMB Q2 Q27 Hrange) as (R' & Hms4 & G26' & HfrD).
    pose proof (icset_adler_facts c 1) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
    exists R', MB, (arm6_pc (is_mode s')).
    split.
    { eapply msteps_trans; [| exact Hms4]. eapply msteps_trans; [| exact Hms3].
      eapply msteps_trans; [| exact Hms2]. subst MA MA1. by_run Hms1. }
    replace (irset_bits (irset_hold r2 0) 0) with r3 by (subst r2 r3; reflexivity).
    cbn [arm_post]. split; [reflexivity|]. split; [| split].
    - split; [exact HMB|]. split.
      { subst MB MB2 MB1. apply (RETC_regs v (mkW s c r1)); [| reflexivity].
        do 3 (apply (RETC_other _ C); [| solve [cbn; lia] | solve [cbn [length Z_to_le_bytes Z.of_nat Pos.of_succ_nat Pos.succ]; lia] | solve [retc_disj] ]).
        apply (RETC_agree_scratch v C _ MA MA'); [| exact HagA]. subst MA MA1. retc_tower C HRC. }
      split.
      + unfold LX; cbn [w_s w_c w_r]. subst s' c' r3. rewrite E9. cbn [ir_in ir_ret].
        replace (is_wrap (iset_mode _ m)) with (is_wrap s) by (destruct s; reflexivity).
        replace (is_wbits (iset_mode _ m)) with (is_wbits s) by (destruct s; reflexivity).
        replace (is_flags (iset_mode _ m)) with 0 by (destruct s; reflexivity).
        replace (is_mode (iset_mode _ m)) with m by (destruct s; reflexivity).
        replace (is_havedict (iset_mode _ m)) with (is_havedict s) by (destruct s; reflexivity).
        refine (conj Xwrap (conj Xwbits (conj _ (conj (or_introl eq_refl) (conj Xin (conj Xret (conj Xmsg (conj Xhd _))))))));
          [destruct Hmv as [-> | ->]; live_mode_tac | destruct Hmv as [-> | ->]; bk_side].
      + unfold LREG_arm. split; [| split].
        * unfold LFIX, INF_FRAME. regs_via3 HfrD Hfr3.
        * unfold LVARS; cbn [w_r r3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next]. regs_via3 HfrD Hfr3.
        * intros _; exact G26'.
    - subst s'. split; [destruct s; reflexivity | split; destruct s; reflexivity].
    - subst MB MB2 MB1 r3. cbn [ir_put].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_trans v (ir_put r1) (ir_put r1) (ir_put r1) M MA MA'); [| exact (MFRAME_of_scratch (ir_put r1) MA MA' HagA HgA)].
      subst MA MA1.
      do 2 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply MFRAME_refl.
  Qed.
End HeadBody.
End FXG.
End InflA_Head2.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6. Import InflA_Head1. Import InflA_Head2.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac wrap_brc Hw :=
  lazymatch goal with
  | |- _ mod _ <> _ => clear - Hw; destruct Hw as [-> | ->]; cbv; discriminate
  | |- _ <> _ mod _ => clear - Hw; destruct Hw as [-> | ->]; cbv; discriminate
  | |- _ mod _ = _ => clear - Hw; destruct Hw as [-> | ->]; reflexivity
  | |- _ / _ = _ => clear - Hw; destruct Hw as [-> | ->]; reflexivity
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Section HeadBody2.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_fixa HF :=
    let X := fresh in pose proof HF as X; unfold LFIXa, INF_FRAME in X;
    destruct X as (G2 & G27 & G8 & G1 & G3 & G4).
  Ltac open_hje HJ :=
    let X := fresh in pose proof HJ as X; unfold HJE in X;
    destruct X as (HF & G9 & G22 & G14 & G19 & G26 & G12); open_fixa HF.

  Lemma head_B_sim : forall s c r1 R M,
    is_mode s = HEAD -> (is_wrap s = 5 \/ is_wrap s = 1) -> is_wbits s = 15 -> is_head s = 0 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> HJE v (is_wrap s) c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 16 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1fdf0) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r1) M (head_B (mkW s c r1)) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode Hw Hwb Hhd HM HRC HX HJ RI CI Hb16. open_hje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_head _ _ _ _ Msc) as C48. rewrite Hhd in C48.
    pose proof (is6_wbits _ _ _ _ Msc) as C56. rewrite Hwb in C56.
    pose proof (wrap15_range _ Hw) as Hwr. pose proof (wrap15_and2 _ Hw) as Hw2. pose proof (wrap15_and1 _ Hw) as Hw1.
    pose proof (mod31_cell M Mrod : cell s6u_segs M (0 + 67208) 8 595056260442243601) as Crod.
    unfold head_B. cbn [w_s w_c w_r].
    assert (Hhx : 0 <= hx (ir_hold r1) < 2 ^ 57).
    { unfold hx. pose proof (Z.mod_pos_bound (ir_hold r1) (2 ^ 8) ltac:(lia)).
      assert (0 <= ir_hold r1 / 2 ^ 8 < 2 ^ 56) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
    assert (Hq4 : 0 <= ir_hold r1 / 2 ^ 4 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hm4 : 0 <= (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
    assert (Hm4' : 0 <= ir_hold r1 mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
    rewrite <- mod31_magic by (clear - Hhx; lia).
    rewrite <- (hx_exec (ir_hold r1)) by exact Rhold64. rewrite <- inv31_exec. unfold INV31X, MOD31_MAGIC.
    destruct (Z.ltb_spec ((((ir_hold r1 * 2 ^ 56) mod 2 ^ 64 / 2 ^ 48 + ir_hold r1 / 2 ^ 8) * -38083600668303590433) mod 2 ^ 64) 595056260442243601) as [DV|NDV]; cbn [negb].
    2:{
      arm_symexP hje_pins ilS 40%nat [true; true; false; true] [RVal (ELit 0); RVal (EVar 35%nat); RVal (ELit 595056260442243601)]
        [(14, EVar 45%nat)] [(45%nat, 8)] v r1 [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1fdf0) M s6u_rom) R' HR' Hfr Hms.
      all: try wrap_brc Hw.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFT1" G end.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66808)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_incorrect_header_check).
      assert (HM1 : LMEM v (mkW s c' r1) M1) by (exact (LMEM_store_msg v C s c r1 M MSG_incorrect_header_check HM Hput)).
      assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r1) M2).
      { apply (LMEM_store_scalar v C s c' r1 _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_incorrect_header_check) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      arm_disp C HM2 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode (iset_mode s BAD))). split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * unfold LX; cbn [w_s w_c w_r]. subst c'. rewrite E11. replace (is_wrap (iset_mode s BAD)) with (is_wrap s) by (destruct s; reflexivity).
          replace (is_wbits (iset_mode s BAD)) with (is_wbits s) by (destruct s; reflexivity). replace (is_flags (iset_mode s BAD)) with (is_flags s) by (destruct s; reflexivity).
          replace (is_mode (iset_mode s BAD)) with BAD by (destruct s; reflexivity).
          replace (is_havedict (iset_mode s BAD)) with (is_havedict s) by (destruct s; reflexivity).
          refine (conj Xwrap (conj Xwbits (conj _ (conj _ (conj Xin (conj Xret (conj _ (conj Xhd _)))))))); [live_mode_tac | | unfold MSG_incorrect_header_check; lia | bk_side].
          destruct Xflags as [X0 | (X1 & _ & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [right; reflexivity | exact XO].
        * symex_reg HR' (19%bv : reg) as G18'. symex_reg HR' (26%bv : reg) as G25'. symex_reg HR' (23%bv : reg) as G24'.
          unfold LREG_arm, LVARS; cbn [w_r]. split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
          regs_via2 Hfr2 Hfr; first [exact G18' | exact G25' | exact G24' | match goal with |- ?G => idtac "REG1 LEFT" G end].
      + subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    destruct (Z.eqb_spec (ir_hold r1 mod 2 ^ 4) 8) as [M8|M8]; cbn [negb].
    2:{
      arm_symexP hje_pins ilS 50%nat [true; true; false; false; true]
        [RVal (ELit 0); RVal (EVar 35%nat); RVal (ELit 595056260442243601); RVal (ELit 16209); RVal (EVar 35%nat)]
        [(14, EVar 45%nat)] [(45%nat, 8)] v r1 [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1fdf0) M s6u_rom) R' HR' Hfr Hms.
      all: try wrap_brc Hw.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFT2" G end.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66987)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_unknown_compression_method).
      assert (HM1 : LMEM v (mkW s c' r1) M1) by (exact (LMEM_store_msg v C s c r1 M MSG_unknown_compression_method HM Hput)).
      assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r1) M2).
      { apply (LMEM_store_scalar v C s c' r1 _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_unknown_compression_method) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      arm_disp C HM2 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode (iset_mode s BAD))). split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * unfold LX; cbn [w_s w_c w_r]. subst c'. rewrite E11. replace (is_wrap (iset_mode s BAD)) with (is_wrap s) by (destruct s; reflexivity).
          replace (is_wbits (iset_mode s BAD)) with (is_wbits s) by (destruct s; reflexivity). replace (is_flags (iset_mode s BAD)) with (is_flags s) by (destruct s; reflexivity).
          replace (is_mode (iset_mode s BAD)) with BAD by (destruct s; reflexivity).
          replace (is_havedict (iset_mode s BAD)) with (is_havedict s) by (destruct s; reflexivity).
          refine (conj Xwrap (conj Xwbits (conj _ (conj _ (conj Xin (conj Xret (conj _ (conj Xhd _)))))))); [live_mode_tac | | unfold MSG_unknown_compression_method; lia | bk_side].
          destruct Xflags as [X0 | (X1 & _ & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [right; reflexivity | exact XO].
        * symex_reg HR' (19%bv : reg) as G18'. symex_reg HR' (26%bv : reg) as G25'. symex_reg HR' (23%bv : reg) as G24'.
          unfold LREG_arm, LVARS; cbn [w_r]. split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
          regs_via2 Hfr2 Hfr; first [exact G18' | exact G25' | exact G24' | match goal with |- ?G => idtac "REG2 LEFT" G end].
      + subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    set (len := (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 + 8) in *.
    set (r2 := irset_bits (irset_hold r1 (ir_hold r1 / 2 ^ 4)) (ir_bits r1 - 4)) in *.
    destruct (Z.ltb_spec 15 len) as [BW|BW].
    {
      assert (BW' : 7 < (ir_hold r1 / 2 ^ 4) mod 2 ^ 4) by (clear - BW; lia).
      (* zlib 1.4: len > 15 is tested first (bltu 7,k), before wbits is read *)
      arm_symexP hje_pins ilS 60%nat [true; true; false; false; false; true]
        [RVal (ELit 0); RVal (EVar 35%nat); RVal (ELit 595056260442243601); RVal (ELit 16209); RVal (EVar 35%nat)]
        [(14, EVar 45%nat)] [(45%nat, 8)] v r1 [is_wrap s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1fdf0) M s6u_rom) R' HR' Hfr Hms.
      all: try wrap_brc Hw.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFT3" G end.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66704)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_invalid_window_size).
      assert (HM1 : LMEM v (mkW s c' r2) M1) by (apply (LMEM_regs v s c' r1 c' r2); [exact (LMEM_store_msg v C s c r1 M MSG_invalid_window_size HM Hput) | subst r2; reflexivity ..]).
      assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r2) M2).
      { apply (LMEM_store_scalar v C s c' r2 _ M1 8 _ HM1); [lia | cbn; lia | subst r2; exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_window_size) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      arm_disp C HM2 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode (iset_mode s BAD))). split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | subst r2; reflexivity]|]. split.
        * unfold LX; cbn [w_s w_c w_r]. subst c' r2. rewrite E11. cbn [ir_in ir_ret irset_bits irset_hold].
          replace (is_wrap (iset_mode s BAD)) with (is_wrap s) by (destruct s; reflexivity).
          replace (is_wbits (iset_mode s BAD)) with (is_wbits s) by (destruct s; reflexivity). replace (is_flags (iset_mode s BAD)) with (is_flags s) by (destruct s; reflexivity).
          replace (is_mode (iset_mode s BAD)) with BAD by (destruct s; reflexivity).
          replace (is_havedict (iset_mode s BAD)) with (is_havedict s) by (destruct s; reflexivity).
          refine (conj Xwrap (conj Xwbits (conj _ (conj _ (conj Xin (conj Xret (conj _ (conj Xhd _)))))))); [live_mode_tac | | unfold MSG_invalid_window_size; lia | bk_side].
          destruct Xflags as [X0 | (X1 & _ & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [right; reflexivity | exact XO].
        * symex_reg HR' (19%bv : reg) as G18'. symex_reg HR' (26%bv : reg) as G25'. symex_reg HR' (23%bv : reg) as G24'. symex_reg HR' (25%bv : reg) as G22'.
          unfold LREG_arm, LVARS; cbn [w_r]. subst r2. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
          split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
          regs_via2 Hfr2 Hfr; first [exact G24' | exact G22' | rewrite G18'; rewrite ?szwrap32_small by (clear - Rbits Hb16; lia); f_equal; lia | exact G25' | match goal with |- ?G => idtac "REG3 LEFT" G end].
      + subst M2 M1 r2. cbn [ir_put irset_bits irset_hold].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    exact (head_ok v C s c r1 R M Hmode Hw Hwb Hhd HM HRC HX HJ RI CI Hb16 DV M8 ltac:(subst len; clear - BW; lia)).
  Qed.
End HeadBody2.

Lemma sr_head : forall s, SRNGq s -> is_head s = 0.
Proof. intros s H. do 30 (destruct H as [_ H]). destruct H as [H _]. exact H. Qed.

Theorem arm_HEAD_sim : arm_stmt HEAD.
Proof.
  intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
  rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) HEAD) with (arm_HEAD ivar_ref).
  destruct HE as (HM & HRC & HX & (HF & HV & G26)).
  arm_begin C HM HRC HX HF HV HP.
  pose proof (sr_head s SR) as Hhd.
  pose proof (head_need v C s c r R M Xwrap HM HRC HF HV RI CI) as HN.
  destruct (NEEDBITS 16 (mkW s c r)) as [[] w1 | w1 | rc w1] eqn:EN; [| | destruct HN].
  - destruct HN as (r1 & R1 & -> & Hms1 & HJE & RI1 & S5 & Hb16).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
    pose proof RI1 as RI1'. unfold RINV in RI1'. destruct RI1' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Rb1 & Rh1).
    rewrite (arm_HEAD_run s c r s c r1 Xwrap Xwbits EN eq_refl ltac:(clear - Hb16 Rb1; lia) Rh1).
    assert (HM1 : LMEM v (mkW s c r1) M) by (apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | exact Q2 | reflexivity]).
    assert (HRC1 : RETC v (mkW s c r1) M) by (eapply RETC_regs; [exact HRC | exact Q5]).
    assert (HX1 : LX v (mkW s c r1)).
    { apply (LX_step v s c r s c r1 HX); try reflexivity; [exact Xlive | | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
      destruct Xflags as [X0 | (X1 & XM & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [exact XM|]. rewrite Q2, Q4. exact XO. }
    destruct (head_B_sim v C s c r1 R1 M Hmode Xwrap Xwbits Hhd HM1 HRC1 HX1 HJE RI1 CI Hb16) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
    apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
  - destruct HN as (r1 & R1 & -> & Hms1 & HL1 & RI1 & S5).
    destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5).
    rewrite (arm_HEAD_leave s c r _ Xwrap EN).
    exists R1, M, pc6_leave. split; [exact Hms1|].
    cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
    split; [apply (LMEM_regs v s c r c r1 M HM); first [exact Q1 | exact Q4 | exact Q2 | reflexivity]|].
    split; [| split; [apply same_blocks_refl | exact HL1]].
    apply (LX_step v s c r s c r1 HX); try reflexivity; [exact Xlive | | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
    destruct Xflags as [X0 | (X1 & XM & XO)]; [left; exact X0 | right]. split; [exact X1|]. split; [exact XM|]. rewrite Q2, Q4. exact XO.
Qed.
End FXG.
