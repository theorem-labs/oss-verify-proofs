(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun AdlerModel ZChecksum ZChkAdl.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflArmLib6c
     InflNeed6 InflA_Check1.
Import ListNotations.
Local Open Scope Z_scope.
#[local] Transparent UPDATE_CHECK_bytes iadler32_upd ZSWAP32.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition check_B (w1 : iw) : ares unit :=
  let s := w_s w1 in let c := w_c w1 in let r := w_r w1 in
  let out := ir_out r - ir_left r in
  let c2 := icset_total_out c (wrap64 (ic_total_out c + out)) in
  let s2 := iset_total s (wrap64 (is_total s + out)) in
  let A := iadler32_upd (is_check s) (arr_slice (ic_outbuf c) (ir_put r - out) out) in
  let s3 := if out =? 0 then s2 else iset_check s2 A in
  let c3 := if out =? 0 then c2 else icset_adler c2 A in
  let r3 := irset_out r (ir_left r) in
  if negb (ZSWAP32 (ir_hold r) =? is_check s3)
  then ARun tt (mkW (iset_mode s3 BAD) (icset_msg c3 MSG_incorrect_data_check) r3)
  else ALeave (mkW (iset_mode (iset_mode s3 LENGTH) DONE) c3 (irset_ret (irset_bits (irset_hold r3 0) 0) Z_STREAM_END)).

Lemma arm_CHECK_run : forall s c r c1 r1,
  is_wrap s = 5 -> is_flags s = 0 ->
  NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c1 r1) ->
  0 <= ir_out r1 - ir_left r1 < 2 ^ 32 ->
  arm_CHECK (mkW s c r) = check_B (mkW s c1 r1).
Proof.
  intros s c r c1 r1 Hw Hf HN Ho.
  unfold arm_CHECK. mstep1 (@gs_eq inflate_state). rewrite Hw. change (negb (5 =? 0)) with true. cbv iota.
  rewrite abind_run. rewrite abind_run, HN. mstep1 (@gr_eq iregs). rewrite (wrap32_id (ir_out r1 - ir_left r1)) by exact Ho.
  mstep1 ur_eq. mstep1 uc_eq. mstep1 us_eq. mstep1 (@gs_eq inflate_state). irnorm.
  replace (is_wrap (iset_total s _)) with 5 by (rewrite <- Hw; destruct s; reflexivity). change (negb (Z.land 5 4 =? 0)) with true. cbn [andb].
  unfold check_B. cbn [w_s w_c w_r].
  destruct (Z.eqb_spec (ir_out r1 - ir_left r1) 0) as [E0|E0]; cbn [negb].
  - mstep1 (@aret_eq unit). mstep1 ur_eq. mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state). irnorm.
    replace (is_flags (iset_total s _)) with 0 by (rewrite <- Hf; destruct s; reflexivity).
    replace (is_wrap (iset_total s _)) with 5 by (rewrite <- Hw; destruct s; reflexivity).
    change (negb (0 =? 0)) with false. change (negb (Z.land 5 4 =? 0)) with true. cbn [andb].
    replace (is_check (iset_total s (wrap64 (is_total s + (ir_out r1 - ir_left r1))))) with (is_check s) by (destruct s; reflexivity).
    destruct (negb (ZSWAP32 (ir_hold r1) =? is_check s)).
    + mstep1 go_bad_eq. rewrite aret_eq. cbv iota. rewrite aret_eq. reflexivity.
    + mstep1 INITBITS_eq. rewrite aret_eq. cbv iota. mstep1 set_mode_eq.
      unfold arm_LENGTH. mstep1 (@gs_eq inflate_state). irnorm.
      replace (is_flags (iset_mode _ LENGTH)) with 0 by (rewrite <- Hf; destruct s; reflexivity).
      change (negb (0 =? 0)) with false. rewrite andb_false_r. mstep1 (@aret_eq bool). mstep1 set_mode_eq.
      unfold arm_DONE. mstep1 ur_eq. rewrite aleave_eq. reflexivity.
  - rewrite abind_run. cbv beta. cbn [w_c w_r]. mstep1 set_adler_check_eq.
    unfold UPDATE_CHECK_bytes. replace (is_flags (iset_total s _)) with 0 by (rewrite <- Hf; destruct s; reflexivity). change (negb (0 =? 0)) with false. cbv iota.
    replace (is_check (iset_total s (wrap64 (is_total s + (ir_out r1 - ir_left r1))))) with (is_check s) by (destruct s; reflexivity).
    mstep1 ur_eq. mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state). irnorm.
    replace (is_flags (iset_check _ _)) with 0 by (rewrite <- Hf; destruct s; reflexivity).
    replace (is_wrap (iset_check _ _)) with 5 by (rewrite <- Hw; destruct s; reflexivity).
    change (negb (0 =? 0)) with false. change (negb (Z.land 5 4 =? 0)) with true. cbn [andb].
    replace (is_check (iset_check (iset_total s (wrap64 (is_total s + (ir_out r1 - ir_left r1)))) (iadler32_upd (is_check s) (arr_slice (ic_outbuf c1) (ir_put r1 - (ir_out r1 - ir_left r1)) (ir_out r1 - ir_left r1)))))
      with (iadler32_upd (is_check s) (arr_slice (ic_outbuf c1) (ir_put r1 - (ir_out r1 - ir_left r1)) (ir_out r1 - ir_left r1))) by (destruct s; reflexivity).
    destruct (negb (ZSWAP32 (ir_hold r1) =? _)).
    + mstep1 go_bad_eq. rewrite aret_eq. cbv iota. rewrite aret_eq. reflexivity.
    + mstep1 INITBITS_eq. rewrite aret_eq. cbv iota. mstep1 set_mode_eq.
      unfold arm_LENGTH. mstep1 (@gs_eq inflate_state). irnorm.
      replace (is_flags (iset_mode _ LENGTH)) with 0 by (rewrite <- Hf; destruct s; reflexivity).
      change (negb (0 =? 0)) with false. rewrite andb_false_r. mstep1 (@aret_eq bool). mstep1 set_mode_eq.
      unfold arm_DONE. mstep1 ur_eq. rewrite aleave_eq. reflexivity.
Qed.


Definition check_B1 (w1 : iw) : ares unit :=
  let s := w_s w1 in let c := w_c w1 in let r := w_r w1 in
  let out := ir_out r - ir_left r in
  let c2 := icset_total_out c (wrap64 (ic_total_out c + out)) in
  let s2 := iset_total s (wrap64 (is_total s + out)) in
  let r3 := irset_out r (ir_left r) in
  ALeave (mkW (iset_mode (iset_mode s2 LENGTH) DONE) c2 (irset_ret (irset_bits (irset_hold r3 0) 0) Z_STREAM_END)).

Lemma arm_CHECK_run1 : forall s c r c1 r1,
  is_wrap s = 1 -> is_flags s = 0 ->
  NEEDBITS 32 (mkW s c r) = ARun tt (mkW s c1 r1) ->
  0 <= ir_out r1 - ir_left r1 < 2 ^ 32 ->
  arm_CHECK (mkW s c r) = check_B1 (mkW s c1 r1).
Proof.
  intros s c r c1 r1 Hw Hf HN Ho.
  unfold arm_CHECK. mstep1 (@gs_eq inflate_state). rewrite Hw. change (negb (1 =? 0)) with true. cbv iota.
  rewrite abind_run. rewrite abind_run, HN. mstep1 (@gr_eq iregs). rewrite (wrap32_id (ir_out r1 - ir_left r1)) by exact Ho.
  mstep1 ur_eq. mstep1 uc_eq. mstep1 us_eq. mstep1 (@gs_eq inflate_state). irnorm.
  replace (is_wrap (iset_total s _)) with 1 by (rewrite <- Hw; destruct s; reflexivity). change (negb (Z.land 1 4 =? 0)) with false. cbn [andb].
  unfold check_B1. cbn [w_s w_c w_r].
  mstep1 (@aret_eq unit). mstep1 ur_eq. mstep1 HOLD_eq. mstep1 (@gs_eq inflate_state). irnorm.
  replace (is_flags (iset_total s _)) with 0 by (rewrite <- Hf; destruct s; reflexivity).
  replace (is_wrap (iset_total s _)) with 1 by (rewrite <- Hw; destruct s; reflexivity).
  change (negb (0 =? 0)) with false. change (negb (Z.land 1 4 =? 0)) with false. cbn [andb].
  mstep1 INITBITS_eq. rewrite aret_eq. cbv iota. mstep1 set_mode_eq.
  unfold arm_LENGTH. mstep1 (@gs_eq inflate_state). irnorm.
  replace (is_flags (iset_mode _ LENGTH)) with 0 by (rewrite <- Hf; destruct s; reflexivity).
  change (negb (0 =? 0)) with false. rewrite andb_false_r. mstep1 (@aret_eq bool). mstep1 set_mode_eq.
  unfold arm_DONE. mstep1 ur_eq. rewrite aleave_eq. reflexivity.
Qed.


Lemma add_lor : forall a b, Z.land a b = 0 -> a + b = Z.lor a b.
Proof. intros a b H. rewrite <- Z.lxor_lor by exact H. rewrite <- Z.add_nocarry_lxor by exact H. reflexivity. Qed.

Lemma cases32 : forall n, 0 <= n < 32 ->
  n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/ n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15
  \/ n = 16 \/ n = 17 \/ n = 18 \/ n = 19 \/ n = 20 \/ n = 21 \/ n = 22 \/ n = 23 \/ n = 24 \/ n = 25 \/ n = 26 \/ n = 27 \/ n = 28 \/ n = 29 \/ n = 30 \/ n = 31.
Proof. intros n Hn. lia. Qed.

End FXG.
Ltac tbn :=
  repeat first [ rewrite Z.lor_spec | rewrite Z.land_spec
               | rewrite Z.shiftl_spec by lia | rewrite Z.shiftr_spec by lia
               | rewrite Z.mul_pow2_bits by lia | rewrite Z.div_pow2_bits by lia
               | rewrite Z.mod_pow2_bits_low by lia | rewrite Z.mod_pow2_bits_high by lia
               | rewrite Z.testbit_neg_r by lia ];
  cbn -[Z.testbit]; 
  repeat match goal with |- context [Z.testbit ?h (?a + ?b)] => let c := eval vm_compute in (a + b) in change (a + b) with c
                         | |- context [Z.testbit ?h (?a - ?b)] => let c := eval vm_compute in (a - b) in change (a - b) with c end;
  repeat match goal with |- context [Z.testbit (Zpos ?p) ?k] => let c := eval vm_compute in (Z.testbit (Zpos p) k) in change (Z.testbit (Zpos p) k) with c end;
  cbn -[Z.testbit]; rewrite ?andb_true_r, ?andb_false_r, ?orb_false_r, ?andb_true_l; try reflexivity.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.

Section ZS.
  Variable h : Z.
  Definition LA := Z.land (Z.shiftr h 24) 255.
  Definition LB := Z.land (Z.shiftr h 8) 65280.
  Definition LC := Z.shiftl (Z.land h 65280) 8.
  Definition LD := Z.shiftl (Z.land h 255) 24.
  Definition MX := (Z.lor (Z.lor (h * 2 ^ 24) (Z.land h 65280 * 2 ^ 8)) (Z.lor (Z.land (h / 2 ^ 8) 65280) (h mod 2 ^ 32 / 2 ^ 24))) mod 2 ^ 32.


  Lemma lanes_high : forall n, 32 <= n ->
    Z.testbit LA n = false /\ Z.testbit LB n = false /\ Z.testbit LC n = false /\ Z.testbit LD n = false.
  Proof.
    intros n Hn. unfold LA, LB, LC, LD.
    rewrite !Z.land_spec, !Z.shiftl_spec, !Z.land_spec by lia.
    change 255 with (Z.ones 8). change 65280 with (Z.shiftl (Z.ones 8) 8).
    rewrite !Z.shiftl_spec by lia. rewrite !Z.ones_spec_high by lia. rewrite !andb_false_r. repeat split; reflexivity.
  Qed.

  Lemma disjAB : Z.land LA LB = 0.
  Proof.
    apply Z.bits_inj'. intros n Hn. rewrite Z.bits_0, Z.land_spec.
    destruct (Z_lt_le_dec n 32) as [L|G].
    - destruct (cases32 n ltac:(lia)) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
        subst n; unfold LA, LB; tbn.
    - destruct (lanes_high n G) as (-> & -> & _). reflexivity.
  Qed.
  Ltac by_bits32 :=
    apply Z.bits_inj'; intros n Hn; rewrite ?Z.bits_0, ?Z.land_spec, ?Z.lor_spec;
    destruct (Z_lt_le_dec n 32) as [L|G];
    [ destruct (cases32 n ltac:(lia)) as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|E]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]];
      subst n; unfold LA, LB, LC, LD, MX; tbn
    | destruct (lanes_high n G) as (EA & EB & EC & ED); rewrite ?EA, ?EB, ?EC, ?ED; try reflexivity ].

  Lemma disjABC : Z.land (Z.lor LA LB) LC = 0.
  Proof. by_bits32. Qed.
  Lemma disjABCD : Z.land (Z.lor (Z.lor LA LB) LC) LD = 0.
  Proof. by_bits32. Qed.

  Lemma sum_lor : LA + LB + LC + LD = Z.lor (Z.lor (Z.lor LA LB) LC) LD.
  Proof.
    rewrite (add_lor LA LB disjAB). rewrite (add_lor _ LC disjABC). rewrite (add_lor _ LD disjABCD). reflexivity.
  Qed.

  Lemma MX_eq : MX = Z.lor (Z.lor (Z.lor LA LB) LC) LD.
  Proof.
    by_bits32.
    unfold MX. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
  Qed.

  Lemma MX_range : 0 <= MX < 2 ^ 32.
  Proof. unfold MX. apply Z.mod_pos_bound. lia. Qed.

  Lemma zswap_exec0 : MX = ZSWAP32 h.
  Proof.
    unfold ZSWAP32. change (Z.land (Z.shiftr h 24) 255) with LA. change (Z.land (Z.shiftr h 8) 65280) with LB.
    change (Z.shiftl (Z.land h 65280) 8) with LC. change (Z.shiftl (Z.land h 255) 24) with LD.
    rewrite sum_lor, <- MX_eq. symmetry. apply wrap64_id. pose proof MX_range. lia.
  Qed.
End ZS.

Lemma zswap_exec : forall h,
  (Z.lor (Z.lor (h * 2 ^ 24) (Z.land h 65280 * 2 ^ 8)) (Z.lor (Z.land (h / 2 ^ 8) 65280) (h mod 2 ^ 32 / 2 ^ 24))) mod 2 ^ 32 = ZSWAP32 h.
Proof. intros h. exact (zswap_exec0 h). Qed.



Lemma bZ_cbytes : forall a so n,
  (forall i, so <= i < so + Z.of_nat n -> 0 <= arr_get a i < 256) ->
  bZ (cbytes (arr_get a) so n) = arr_slice a so (Z.of_nat n).
Proof.
  intros a so n. unfold arr_slice. rewrite Nat2Z.id. revert so. induction n as [|n IH]; intros so Hr; [reflexivity|].
  cbn [cbytes arr_slice_nat bZ map]. unfold bZ in IH. f_equal.
  - rewrite Z_to_bv_small; [reflexivity|]. unfold bv_modulus. cbn. pose proof (Hr so ltac:(lia)). lia.
  - apply IH. intros i Hi. apply Hr. lia.
Qed.

Lemma adler_canon_0 : adler_canon 0.
Proof. unfold adler_canon, lo16, hi16, ABASE. rewrite !Z.mod_0_l by lia. cbn. repeat split; cbv; try discriminate; reflexivity. Qed.
Lemma ck_adl_canon : forall x, ck_adl x -> adler_canon x.
Proof.
  intros x [-> | [-> | (a & bs & ->)]]; [apply adler_canon_0 | apply adler_canon_1 | apply adler32_model_canon].
Qed.

Section CheckBody.
  Variable v : icv.
  Hypothesis C : ictx v.
  Variable ROM : (word -> option byte) -> Prop.
  Hypothesis ROMok : forall M, rod6_clear M -> ROM M.
  Hypothesis ADLER : adler32_run6 ROM.

  Ltac open_cje HJ :=
    let X := fresh in pose proof HJ as X; unfold CJE, LVR in X;
    destruct X as (HF & (G9 & G18 & G1 & G22 & G23) & G13 & G26 & G27); open_fix HF.

  Definition kstops : list Z := [pc6_ret; pc6_leave; pc6_mem; pc6_need_dict; 0x1f188; 0x1f8c0; 0x1a3d4; 0x27800; 0x1ed04] ++ arm6_pcs.
  Definition ilK : cfg := CFG [] [] arm_rets kstops [].
  Definition ilKD : cfg := CFG [] [] arm_rets (pc6_disp :: kstops) [].
  Definition pinsP : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (20, ELit 16209); (18, EVar 36%nat); (19, EAdd (EVar 37%nat) (EVar 38%nat)); (9, EVar 39%nat);
     (23, EVar 40%nat); (24, EVar 41%nat); (27, EAdd (EVar 43%nat) (EVar 44%nat)); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (10, EVar 48%nat);
     (22, EAdd (EVar 33%nat) (ELit 168)); (25, ELit 0x12510)].

  Ltac regs_via2 Hfr Hfr1 :=
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ =>
              rewrite (Hfr n eq_refl); first [assumption | rewrite (Hfr1 n eq_refl); assumption] end
          | match goal with |- ?G => idtac "REGS2 LEFT" G end ].

  Ltac leave_regs HR Hfr :=
    let G8 := fresh in let G22 := fresh in let G23 := fresh in let G26 := fresh in let G10 := fresh in let G11 := fresh in let G1 := fresh in
    symex_reg HR (9%bv : reg) as G8; symex_reg HR (23%bv : reg) as G22; symex_reg HR (24%bv : reg) as G23;
    symex_reg HR (27%bv : reg) as G26; symex_reg HR (10%bv : reg) as G10; symex_reg HR (11%bv : reg) as G11; symex_reg HR (1%bv : reg) as G1;
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next ir_ret irset_ret irset_bits irset_hold irset_out];
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | exact G8 | exact G22 | exact G23 | exact G26 | exact G10 | exact G11 | exact G1
          | match goal with |- ?G => idtac "LEAVE LEFT" G end ].

  Lemma check_B_sim : forall s c r1 R M,
    is_mode s = CHECK -> is_wrap s = 5 -> is_flags s = 0 -> adler_canon (is_check s) ->
    0 <= is_total s < 2 ^ 64 -> 0 <= ic_total_out c < 2 ^ 64 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> CJE v 5 c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 32 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1dafc) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M (check_B (mkW s c r1)) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode Hw Hf Hcan Htot Htoto HM HRC HX HJ RI CI Hb32. open_cje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. open_frame Mfr. open_zs Mzs. unfold mapped in *.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof Hcan as Hcan'. destruct Hcan' as (Hck & _ & _).
    pose proof (is6_flags _ _ _ _ Msc) as C24. rewrite Hf in C24.
    pose proof (is6_wrap _ _ _ _ Msc) as C16. rewrite Hw in C16.
    pose proof (is6_total _ _ _ _ Msc) as C40. pose proof (is6_check _ _ _ _ Msc) as C32.
    assert (Hout : 0 <= ir_out r1 - ir_left r1 <= ir_put r1 /\ ir_out r1 - ir_left r1 < 2 ^ 31) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
    unfold check_B. cbn [w_s w_c w_r]. rewrite <- (zswap_exec (ir_hold r1)).
    set (X := (Z.lor (Z.lor (ir_hold r1 * 2 ^ 24) (Z.land (ir_hold r1) 65280 * 2 ^ 8)) (Z.lor (Z.land (ir_hold r1 / 2 ^ 8) 65280) (ir_hold r1 mod 2 ^ 32 / 2 ^ 24))) mod 2 ^ 32).
    set (s2 := iset_total s (wrap64 (is_total s + (ir_out r1 - ir_left r1)))).
    set (c2 := icset_total_out c (wrap64 (ic_total_out c + (ir_out r1 - ir_left r1)))).
    pose proof (icset_total_out_facts c (wrap64 (ic_total_out c + (ir_out r1 - ir_left r1)))) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11).
    set (M1 := wbytes M (zw (cv_ZP v + 40)) (Z_to_le_bytes 8 (wrap64 (ic_total_out c + (ir_out r1 - ir_left r1))))).
    set (M2 := wbytes M1 (zw (cv_S v + 48)) (Z_to_le_bytes 8 (wrap64 (is_total s + (ir_out r1 - ir_left r1))))).
    assert (HM1 : LMEM v (mkW s c2 r1) M1) by (exact (LMEM_store_total_out v C s c r1 M _ HM Hput)).
    assert (HM2 : LMEM v (mkW s2 c2 r1) M2).
    { apply (LMEM_store_scalar v C s c2 r1 _ M1 48 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_total M1 (cv_S v) _ s _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HF2 : MFRAME v (ir_put r1) (ir_put r1) M M2).
    { subst M2 M1. apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    assert (HRC2 : RETC v (mkW s2 c2 r1) M2) by (subst M2 M1; apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | reflexivity]).
    assert (SB2 : same_blocks s s2) by (subst s2; split; [reflexivity | split; reflexivity]).
    destruct (Z.eq_dec (ir_out r1 - ir_left r1) 0) as [E0|E0].
    -
      rewrite E0. cbn [Z.eqb].
      assert (Eol : ir_out r1 = ir_left r1) by (clear - E0; lia).
      replace (is_check s2) with (is_check s) by (subst s2; destruct s; reflexivity).
      destruct (Z.eqb_spec X (is_check s)) as [EQ|NE]; cbn [negb].
      +
        arm_symexP j1011_pins ilK 50%nat [false; true; false; false; false; false; true]
          [RVal (EVar 42%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (ELit 0); RVal (EVar 47%nat)]
          [(13, ELit 5)] [(45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)] v r1 [ic_total_out c; is_total s; is_check s] NoVals (famA c s)
          (mkst R (Z_to_bv 64 0x1dafc) M s6_rom) R' HR' Hfr Hms.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTAok" G end.
        rewrite E0 in Hms. rewrite (Z.mod_small 0 (2 ^ 32)) in Hms by lia.
        rewrite <- (le8_wrap64 (ic_total_out c + 0)), <- (le8_wrap64 (is_total s + 0)) in Hms.
        set (r1o := irset_out r1 (ir_left r1)).
        set (Mo := wbytes M2 (zw (cv_sp v - 224 + 80)) (Z_to_le_bytes 8 (ir_left r1))) in *.
        set (M3 := wbytes Mo (zw (cv_S v + 8)) (Z_to_le_bytes 4 16207)) in *.
        set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16208)) in *.
        set (r' := mkIR (ir_next r1) (ir_have r1) (ir_put r1) (ir_left r1) 0 0 (ir_in r1) (ir_left r1) Z_STREAM_END).
        assert (HMo : LMEM v (mkW s2 c2 r1o) Mo).
        { subst Mo r1o. apply (LMEM_store_outc v C s2 c2 r1 (irset_out r1 (ir_left r1)) M2 HM2 Hput); [reflexivity | cbn; clear - Rlf0 Rpl Rpt0 CP0; lia]. }
        assert (HM3 : LMEM v (mkW (iset_mode s2 LENGTH) c2 r') M3).
        { apply (LMEM_regs v (iset_mode s2 LENGTH) c2 r1o c2 r'); [| reflexivity ..].
          apply (LMEM_store_scalar v C s2 c2 r1o _ Mo 8 _ HMo); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode Mo (cv_S v) _ s2 LENGTH (lm_sc _ _ _ HMo)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4 : LMEM v (mkW (iset_mode (iset_mode s2 LENGTH) DONE) c2 r') M4).
        { apply (LMEM_store_scalar v C _ c2 r' _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M3 (cv_S v) _ _ DONE (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        exists R', M4, pc6_leave. split; [subst M4 M3 Mo M2 M1; rewrite E0; by_run Hms|].
        cbn [arm_post]. split; [reflexivity|]. split.
        2:{ subst M4 M3 Mo. do 2 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
            apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
            exact HF2. }
        split; [exact HM4|]. split.
        { apply (LX_step0 v s c r1 _ c2 r' HX NH NB); subst s2 r'; try reflexivity; [live_mode_tac | cbn; unfold Z_STREAM_END; lia | cbv delta [c2]; rewrite T9; exact Xmsg]. }
        split; [apply (same_blocks_trans _ _ _ SB2); split; [reflexivity | split; reflexivity]|].
        subst r'. leave_regs HR' Hfr.
      +
        arm_symexP j1011_pins ilK 50%nat [false; true; false; false; true; true]
          [RVal (EVar 42%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (ELit 0); RVal (EVar 47%nat); RVal (ELit (JT BAD))]
          [(13, ELit 5)] [(45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)] v r1 [ic_total_out c; is_total s; is_check s] NoVals (famA c s)
          (mkst R (Z_to_bv 64 0x1dafc) M s6_rom) R' HR' Hfr Hms.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTAbad" G end.
        rewrite E0 in Hms. rewrite (Z.mod_small 0 (2 ^ 32)) in Hms by lia.
        rewrite <- (le8_wrap64 (ic_total_out c + 0)), <- (le8_wrap64 (is_total s + 0)) in Hms.
        set (M3 := wbytes M2 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 67014)) in *.
        set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
        set (Mo := wbytes M4 (zw (cv_sp v - 224 + 80)) (Z_to_le_bytes 8 (ir_left r1))) in *.
        set (r' := irset_out r1 (ir_left r1)).
        set (c3 := icset_msg c2 MSG_incorrect_data_check).
        assert (HM3 : LMEM v (mkW s2 c3 r1) M3) by (exact (LMEM_store_msg v C s2 c2 r1 M2 MSG_incorrect_data_check HM2 Hput)).
        assert (HM4 : LMEM v (mkW (iset_mode s2 BAD) c3 r1) M4).
        { apply (LMEM_store_scalar v C s2 c3 r1 _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M3 (cv_S v) _ s2 BAD (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HMo : LMEM v (mkW (iset_mode s2 BAD) c3 r') Mo).
        { subst Mo r'. apply (LMEM_store_outc v C (iset_mode s2 BAD) c3 r1 (irset_out r1 (ir_left r1)) M4 HM4 Hput); [reflexivity | cbn; clear - Rlf0 Rpl Rpt0 CP0; lia]. }
        pose proof (icset_msg_facts c2 MSG_incorrect_data_check) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
        exists R', Mo, (arm6_pc BAD). split; [subst Mo M4 M3 M2 M1; rewrite E0; by_run Hms|].
        cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply (same_blocks_trans _ _ _ SB2); apply same_blocks_mode |]].
        * split; [exact HMo|]. split; [subst Mo M4 M3 M2 M1; apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | reflexivity]|]. split.
          -- apply (LX_step0 v s c r1 _ c3 r' HX NH NB); subst s2 r' c3; try reflexivity; [live_mode_tac | exact Xret | rewrite E11; unfold MSG_incorrect_data_check; lia].
          -- symex_reg HR' (9%bv : reg) as G8'.
             unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_out].
             split; [apply (LFIX_frame v R R' _ HF Hfr); reflexivity|]. split; [| intros _; exact G8']. regs_via Hfr.
        * subst Mo M4 M3 r'. cbn [ir_put irset_out].
          apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
          apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
          apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
          exact HF2.
    -
      replace ((ir_out r1 - ir_left r1) =? 0) with false by (symmetry; apply Z.eqb_neq; exact E0).
      assert (HNO : 0 < cv_NO v) by (clear - E0 Hout Hput; lia).
      arm_symexP j1011_pins ilK 30%nat [false; false; true]
        [RVal (EVar 42%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (ELit 0); RVal (EVar 47%nat)]
        [(13, ELit 5)] [(45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64)] v r1 [ic_total_out c; is_total s; is_check s] NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1dafc) M s6_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      rewrite (Z.mod_small (ir_out r1 - ir_left r1) (2 ^ 32)) in Hms1 by (clear - Hout; lia).
      rewrite <- (le8_wrap64 (ic_total_out c + _)), <- (le8_wrap64 (is_total s + _)) in Hms1. fold M1 in Hms1. fold M2 in Hms1.
      symex_reg HR1 (10%bv : reg) as A10. symex_reg HR1 (11%bv : reg) as A11. symex_reg HR1 (12%bv : reg) as A12. symex_reg HR1 (1%bv : reg) as A1.
      symex_reg HR1 (9%bv : reg) as A8.
      rewrite (Z.mod_small (ir_out r1 - ir_left r1) (2 ^ 32)) in A11 by (clear - Hout; lia).
      rewrite szwrap32_small in A12 by (clear - Hout; lia).
      assert (A2 : getr R1 2 = zw (cv_sp v - 224)) by (rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2).
      set (n := Z.to_nat (ir_out r1 - ir_left r1)).
      assert (Hn : Z.of_nat n = ir_out r1 - ir_left r1) by (subst n; apply Z2Nat.id; clear - Hout; lia).
      set (d := cbytes (arr_get (ic_outbuf c)) (ir_put r1 - (ir_out r1 - ir_left r1)) n).
      assert (Hlen : length d = n) by (subst d; apply cbytes_length).
      pose proof HM2 as HM2'. clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
      clear Fsv F104 F96 F88 F72 F56 F48 F40 F32 F24 F16 F8 Fd0 Z0 Z8 Z16 Z24 Z32 Z40 Z48 Z56 Z64 Z72 Z80 Z96 C24 C16 C40 C32.
      open_lmem HM2'. unfold mapped in *.
      pose proof (cells_rdn_bytes s6_segs M2 (cv_P0 v) (ir_put r1) (arr_get (ic_outbuf c)) (ir_put r1 - (ir_out r1 - ir_left r1)) n Mout
                    ltac:(clear - Hout; lia) ltac:(rewrite Hn; clear - Hout; lia) ltac:(clear - CP0; lia) ltac:(clear - CP0 Hput; lia)) as Hrdn.
      fold d in Hrdn. rewrite <- Hlen in Hrdn.
      destruct (ADLER M2 R1 (is_check s) (cv_P0 v + (ir_put r1 - (ir_out r1 - ir_left r1))) d (cv_sp v - 224) (zw 0x1df0c) Hrdn
                  ltac:(clear - Hcan; destruct Hcan as (H & _); lia) Hcan ltac:(clear - CP0 Hout Hput; lia)
                  ltac:(rewrite Hlen, Hn; clear - CP0 Hout Hput; lia) ltac:(rewrite Hlen, Hn; clear - Hout; lia)
                  ltac:(unfold ADLER_FR6; clear - Csp; lia) ltac:(clear - Csp; lia))
        as (R2 & mem3 & Hms2 & B10 & B2 & Hfr2 & AG & Hgrow).
      { intros x Hx. apply Mmap_f. unfold ADLER_FR6 in Hx. clear - Hx. lia. }
      { rewrite Hlen, Hn. intros _. specialize (CfP HNO). unfold sep, ADLER_FR6 in *. clear - CfP Hout Hput Rpl CP0. lia. }
      { apply ROMok. exact Mrod. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { exact A1. }
      { exact A2. }
      { exact A10. }
      { change (reg_get R1 11) with (getr R1 11). rewrite A11. f_equal. lia. }
      { change (reg_get R1 12) with (getr R1 12). rewrite A12, Hlen, Hn. reflexivity. }
      set (A := iadler32_upd (is_check s) (arr_slice (ic_outbuf c) (ir_put r1 - (ir_out r1 - ir_left r1)) (ir_out r1 - ir_left r1))) in *.
      assert (EA : adler32_z_spec (is_check s) (cv_P0 v + (ir_put r1 - (ir_out r1 - ir_left r1))) d = A).
      { rewrite (adler32_z_spec_canon _ _ _ Hcan) by (clear - CP0 Hout Hput; lia). subst A d. unfold iadler32_upd.
        rewrite bZ_cbytes; [rewrite Hn; reflexivity|]. intros i Hi. apply Coutb. rewrite Hn in Hi. clear - Hi Hout Hput. lia. }
      rewrite EA in B10. change (reg_get R2 10) with (getr R2 10) in B10. change (reg_get R2 2) with (getr R2 2) in B2.
      pose proof (adler32_model_canon (is_check s) (arr_slice (ic_outbuf c) (ir_put r1 - (ir_out r1 - ir_left r1)) (ir_out r1 - ir_left r1))) as HAc.
      change (adler32_model _ _) with A in HAc. destruct HAc as (HA32 & _ & _).
      assert (AG' : agree_out (SCR v) M2 mem3).
      { eapply agree_out_weaken; [exact AG|]. intros x Hx. unfold SCR, INF_FRAME, INF_SCRATCH, ADLER_FR6 in *. cbn in Hx |- *. clear - Hx. lia. }
      pose proof (LMEM_agree_scratch v C s2 c2 r1 M2 mem3 HM2 Hput AG' Hgrow) as HM3.
      pose proof (RETC_agree_scratch v C (mkW s2 c2 r1) M2 mem3 HRC2 AG') as HRC3.
      assert (HF3 : MFRAME v (ir_put r1) (ir_put r1) M mem3).
      { destruct HF2 as (_ & Hg2 & HE2). split; [lia|]. split; [intros x Hx; apply Hgrow, Hg2, Hx|].
        intros x N1 N2 N3 N4. rewrite (AG x) by (unfold in_franges, ADLER_FR6, INF_FRAME, INF_SCRATCH in *; cbn; clear - N1; lia). apply HE2; assumption. }
      assert (Q2 : getr R2 2 = zw (cv_sp v - 224)) by exact B2.
      assert (Q25 : getr R2 8 = zw (cv_S v)) by (rewrite (Hfr2 (8%bv : reg) eq_refl), (Hfr1 (8%bv : reg) eq_refl); exact G25).
      assert (Q21 : getr R2 20 = zw 16209) by (rewrite (Hfr2 (20%bv : reg) eq_refl), (Hfr1 (20%bv : reg) eq_refl); exact G19).
      assert (Q24 : getr R2 18 = zw (ir_have r1)) by (rewrite (Hfr2 (18%bv : reg) eq_refl), (Hfr1 (18%bv : reg) eq_refl); exact G9).
      assert (Q19 : getr R2 19 = zw (cv_P0 v + ir_put r1)) by (rewrite (Hfr2 (19%bv : reg) eq_refl), (Hfr1 (19%bv : reg) eq_refl); exact G18).
      assert (Q18 : getr R2 9 = zw (ir_left r1)) by (rewrite (Hfr2 (9%bv : reg) eq_refl); exact A8).
      assert (Q21' : getr R2 22 = zw (cv_S v + 168)) by (rewrite (Hfr2 (22%bv : reg) eq_refl), (Hfr1 (22%bv : reg) eq_refl); exact G21).
      assert (Q24' : getr R2 25 = zw 0x12510) by (rewrite (Hfr2 (25%bv : reg) eq_refl), (Hfr1 (25%bv : reg) eq_refl); exact G24).
      assert (Q23 : getr R2 23 = zw (ir_hold r1)) by (rewrite (Hfr2 (23%bv : reg) eq_refl), (Hfr1 (23%bv : reg) eq_refl); exact G22).
      assert (Q8 : getr R2 24 = zw (ir_bits r1)) by (rewrite (Hfr2 (24%bv : reg) eq_refl), (Hfr1 (24%bv : reg) eq_refl); exact G23).
      assert (Q26 : getr R2 27 = zw (cv_I0 v + ir_next r1)) by (rewrite (Hfr2 (27%bv : reg) eq_refl), (Hfr1 (27%bv : reg) eq_refl); exact G26).
      assert (Q27 : getr R2 26 = zw (cv_I0 v + ir_next r1)) by (rewrite (Hfr2 (26%bv : reg) eq_refl), (Hfr1 (26%bv : reg) eq_refl); exact G27).
      assert (Q3 : getr R2 3 = getr (cv_R0 v) 3) by (rewrite (Hfr2 (3%bv : reg) eq_refl), (Hfr1 (3%bv : reg) eq_refl); exact G3).
      assert (Q4 : getr R2 4 = getr (cv_R0 v) 4) by (rewrite (Hfr2 (4%bv : reg) eq_refl), (Hfr1 (4%bv : reg) eq_refl); exact G4).
      clear HR1.
      clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
      pose proof HM3 as HM3'. open_lmem HM3'. open_frame Mfr. unfold mapped in *.
      pose proof (is6_flags _ _ _ _ Msc) as C24. cbn [w_s] in C24. replace (is_flags s2) with 0 in C24 by (rewrite <- Hf; subst s2; destruct s; reflexivity).
      pose proof (is6_wrap _ _ _ _ Msc) as C16. cbn [w_s] in C16. replace (is_wrap s2) with 5 in C16 by (rewrite <- Hw; subst s2; destruct s; reflexivity).
      set (s3 := iset_check s2 A) in *. set (c3 := icset_adler c2 A) in *.
      pose proof (icset_adler_facts c2 A) as (U1 & U2 & U3 & U4 & U5 & U6 & U7 & U8 & U9 & U10 & U11).
      replace (is_check s3) with A by (subst s3 s2; destruct s; reflexivity).
      assert (SB3 : same_blocks s s3) by (subst s3 s2; split; [reflexivity | split; reflexivity]).
      destruct (Z.eqb_spec X A) as [EQ|NE]; cbn [negb].
      +
        arm_symexP (@nil (Z * expr)) ilK 50%nat [false; false; false; false; true]
          [RVal (ELit 5); RVal (EVar 34%nat); RVal (EVar 35%nat); RVal (ELit 18446744073709535436); RVal (ELit 0)]
          pinsP [(45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64); (48%nat, 2 ^ 32); (49%nat, 2 ^ 63)] v r1
          [ic_total_out c; is_total s; is_check s; A; cv_S v + 168] NoVals F0
          (mkst R2 (Z_to_bv 64 0x1df0c) mem3 s6_rom) R' HR' Hfr Hms.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTBok" G end.
        set (M3 := wbytes mem3 (zw (cv_S v + 40)) (Z_to_le_bytes 8 A)) in *.
        set (M4 := wbytes M3 (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 A)) in *.
        set (Mo := wbytes M4 (zw (cv_sp v - 224 + 80)) (Z_to_le_bytes 8 (ir_left r1))) in *.
        set (M5 := wbytes Mo (zw (cv_S v + 8)) (Z_to_le_bytes 4 16207)) in *.
        set (M6 := wbytes M5 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16208)) in *.
        set (r1o := irset_out r1 (ir_left r1)).
        set (r' := mkIR (ir_next r1) (ir_have r1) (ir_put r1) (ir_left r1) 0 0 (ir_in r1) (ir_left r1) Z_STREAM_END).
        assert (HM3b : LMEM v (mkW s3 c2 r1) M3).
        { apply (LMEM_store_scalar v C s2 c2 r1 _ mem3 40 _ HM3); [lia | cbn; lia | exact Hput | | subst s3; reflexivity ..].
          apply (is6_upd_check mem3 (cv_S v) _ s2 A (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4 : LMEM v (mkW s3 c3 r1) M4) by (exact (LMEM_store_adler v C s3 c2 r1 M3 A HM3b Hput)).
        assert (HMo : LMEM v (mkW s3 c3 r1o) Mo).
        { subst Mo r1o. apply (LMEM_store_outc v C s3 c3 r1 (irset_out r1 (ir_left r1)) M4 HM4 Hput); [reflexivity | cbn; clear - Rlf0 Rpl Rpt0 CP0; lia]. }
        assert (HM5 : LMEM v (mkW (iset_mode s3 LENGTH) c3 r') M5).
        { apply (LMEM_regs v (iset_mode s3 LENGTH) c3 r1o c3 r'); [| reflexivity ..].
          apply (LMEM_store_scalar v C s3 c3 r1o _ Mo 8 _ HMo); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode Mo (cv_S v) _ s3 LENGTH (lm_sc _ _ _ HMo)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM6 : LMEM v (mkW (iset_mode (iset_mode s3 LENGTH) DONE) c3 r') M6).
        { apply (LMEM_store_scalar v C _ c3 r' _ M5 8 _ HM5); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M5 (cv_S v) _ _ DONE (lm_sc _ _ _ HM5)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        exists R', M6, pc6_leave. split.
        { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 0x1a3d4) M2 s6_rom)); [subst M2 M1; by_run Hms1|].
          apply (msteps_trans _ _ (mkst R2 (Z_to_bv 64 0x1df0c) mem3 s6_rom)); [by_run Hms2|]. subst M6 M5 Mo M4 M3; by_run Hms. }
        cbn [arm_post]. split; [reflexivity|]. split.
        2:{ subst M6 M5 Mo M4 M3.
            do 2 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
            apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
            apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
            apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
            exact HF3. }
        split; [exact HM6|]. split.
        { apply (LX_step0 v s c r1 _ c3 r' HX NH NB); subst s3 s2 r' c3 c2; try reflexivity; [live_mode_tac | cbn; unfold Z_STREAM_END; lia | rewrite U9, T9; exact Xmsg]. }
        split; [apply (same_blocks_trans _ _ _ SB3); split; [reflexivity | split; reflexivity]|].
        subst r'. leave_regs HR' Hfr.
      +
        arm_symexP (@nil (Z * expr)) ilKD 40%nat [false; false; true]
          [RVal (ELit 5); RVal (EVar 34%nat); RVal (EVar 35%nat); RVal (ELit 18446744073709535436); RVal (ELit 0)]
          pinsP [(45%nat, 2 ^ 64); (46%nat, 2 ^ 64); (47%nat, 2 ^ 64); (48%nat, 2 ^ 32); (49%nat, 2 ^ 63)] v r1
          [ic_total_out c; is_total s; is_check s; A; cv_S v + 168] NoVals F0
          (mkst R2 (Z_to_bv 64 0x1df0c) mem3 s6_rom) R3 HR3 Hfr3 Hms3.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTBbad" G end.
        set (M3 := wbytes mem3 (zw (cv_S v + 40)) (Z_to_le_bytes 8 A)) in *.
        set (M4 := wbytes M3 (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 A)) in *.
        set (M5 := wbytes M4 (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 67014)) in *.
        set (M6' := wbytes M5 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
        set (M6 := wbytes M6' (zw (cv_sp v - 224 + 80)) (Z_to_le_bytes 8 (ir_left r1))) in *.
        set (r' := irset_out r1 (ir_left r1)).
        set (c4 := icset_msg c3 MSG_incorrect_data_check).
        assert (HM3b : LMEM v (mkW s3 c2 r1) M3).
        { apply (LMEM_store_scalar v C s2 c2 r1 _ mem3 40 _ HM3); [lia | cbn; lia | exact Hput | | subst s3; reflexivity ..].
          apply (is6_upd_check mem3 (cv_S v) _ s2 A (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (Hput' : 0 <= ir_put r' <= cv_NO v) by (subst r'; exact Hput).
        assert (HM4 : LMEM v (mkW s3 c3 r1) M4) by (exact (LMEM_store_adler v C s3 c2 r1 M3 A HM3b Hput)).
        assert (HM5 : LMEM v (mkW s3 c4 r1) M5) by (exact (LMEM_store_msg v C s3 c3 r1 M4 MSG_incorrect_data_check HM4 Hput)).
        assert (HM6' : LMEM v (mkW (iset_mode s3 BAD) c4 r1) M6').
        { apply (LMEM_store_scalar v C s3 c4 r1 _ M5 8 _ HM5); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_mode M5 (cv_S v) _ s3 BAD (lm_sc _ _ _ HM5)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM6 : LMEM v (mkW (iset_mode s3 BAD) c4 r') M6).
        { subst M6 r'. apply (LMEM_store_outc v C (iset_mode s3 BAD) c4 r1 (irset_out r1 (ir_left r1)) M6' HM6' Hput); [reflexivity | cbn; clear - Rlf0 Rpl Rpt0 CP0; lia]. }
        pose proof (lm_rod _ _ _ HM6) as Mrod6. pose proof (is6_mode _ _ _ _ (lm_sc _ _ _ HM6)) as C8'. cbn [w_s] in C8'.
        replace (is_mode (iset_mode s3 BAD)) with BAD in C8' by (subst s3 s2; destruct s; reflexivity).
        symex_reg HR3 (1%bv : reg) as W1. symex_reg HR3 (10%bv : reg) as W10. symex_reg HR3 (11%bv : reg) as W11.
        symex_reg HR3 (29%bv : reg) as W29. symex_reg HR3 (31%bv : reg) as W31.
        change 18446744073709535436 with ((-16180) mod 2 ^ 64) in W31. rewrite zw_neg_mod in W31.
        j1011_symex ilS 12%nat [true] [RVal (ELit 16209); RVal (ELit (JT BAD))] (@nil (Z * expr)) (@nil (nat * Z)) v
          (mkIR (ir_next r1) (ir_have r1) (ir_put r1) (ir_left r1) (ir_hold r1) (ir_bits r1) (ir_in r1) (ir_left r1) (ir_ret r1))
          (@nil Z) NoVals F0
          (mkst R3 (Z_to_bv 64 pc6_disp) M6 s6_rom) R' HR' Hfr Hms.
        all: cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
        all: try (lazymatch goal with |- getr _ ?n = zw _ => first [assumption | rewrite (Hfr3 n eq_refl); assumption] end).
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTBbad2" G end.
        pose proof (icset_msg_facts c3 MSG_incorrect_data_check) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
        exists R', M6, (arm6_pc BAD). split.
        { apply (msteps_trans _ _ (mkst R1 (Z_to_bv 64 0x1a3d4) M2 s6_rom)); [subst M2 M1; by_run Hms1|].
          apply (msteps_trans _ _ (mkst R2 (Z_to_bv 64 0x1df0c) mem3 s6_rom)); [by_run Hms2|].
          apply (msteps_trans _ _ (mkst R3 (Z_to_bv 64 pc6_disp) M6 s6_rom)); subst M6 M6' M5 M4 M3; [by_run Hms3 | by_run Hms]. }
        cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply (same_blocks_trans _ _ _ SB3); apply same_blocks_mode |]].
        * split; [exact HM6|]. split; [subst M6 M6' M5 M4 M3; apply (RETC_regs v (mkW s2 c2 r1)); [retc_tower C HRC3 | subst r'; reflexivity]|]. split.
          -- apply (LX_step0 v s c r1 _ c4 r' HX NH NB); subst s3 s2 r' c4 c3 c2; try reflexivity; [live_mode_tac | exact Xret | rewrite E11; unfold MSG_incorrect_data_check; lia].
          -- symex_reg HR' (9%bv : reg) as G8'.
             unfold LREG_arm, LVARS; cbn [w_r]. subst r'. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_out].
             split; [| split; [| intros _; exact G8']].
             ++ unfold LFIX, INF_FRAME, A6_JTAB. regs_via2 Hfr Hfr3.
             ++ regs_via2 Hfr Hfr3.
        * subst M6 M6' M5 M4 M3 r'. cbn [ir_put irset_out].
          apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
          apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
          do 2 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]).
          apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
          exact HF3.
  Qed.
  Lemma check_B1_sim : forall s c r1 R M,
    is_mode s = CHECK -> is_wrap s = 1 -> is_flags s = 0 ->
    0 <= is_total s < 2 ^ 64 -> 0 <= ic_total_out c < 2 ^ 64 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> CJE v 1 c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 32 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1dafc) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M (check_B1 (mkW s c r1)) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode Hw Hf Htot Htoto HM HRC HX HJ RI CI Hb32. open_cje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. open_frame Mfr. open_zs Mzs. unfold mapped in *.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (is6_flags _ _ _ _ Msc) as C24. rewrite Hf in C24.
    pose proof (is6_total _ _ _ _ Msc) as C40.
    assert (Hout : 0 <= ir_out r1 - ir_left r1 <= ir_put r1 /\ ir_out r1 - ir_left r1 < 2 ^ 31) by (clear - Rout Routp Rpt0 Rpl Rlf0 CP0; lia).
    unfold check_B1. cbn [w_s w_c w_r].
    set (s2 := iset_total s (wrap64 (is_total s + (ir_out r1 - ir_left r1)))).
    set (c2 := icset_total_out c (wrap64 (ic_total_out c + (ir_out r1 - ir_left r1)))).
    pose proof (icset_total_out_facts c (wrap64 (ic_total_out c + (ir_out r1 - ir_left r1)))) as (T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11).
    set (M1 := wbytes M (zw (cv_ZP v + 40)) (Z_to_le_bytes 8 (wrap64 (ic_total_out c + (ir_out r1 - ir_left r1))))).
    set (M2 := wbytes M1 (zw (cv_S v + 48)) (Z_to_le_bytes 8 (wrap64 (is_total s + (ir_out r1 - ir_left r1))))).
    assert (HM1 : LMEM v (mkW s c2 r1) M1) by (exact (LMEM_store_total_out v C s c r1 M _ HM Hput)).
    assert (HM2 : LMEM v (mkW s2 c2 r1) M2).
    { apply (LMEM_store_scalar v C s c2 r1 _ M1 48 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_total M1 (cv_S v) _ s _ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HF2 : MFRAME v (ir_put r1) (ir_put r1) M M2).
    { subst M2 M1. apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia]. }
    assert (HRC2 : RETC v (mkW s2 c2 r1) M2) by (subst M2 M1; apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | reflexivity]).
    assert (SB2 : same_blocks s s2) by (subst s2; split; [reflexivity | split; reflexivity]).
    arm_symexP j1011_pins ilK 50%nat [true; true; false; true]
      [RVal (EVar 42%nat); RVal (EVar 45%nat); RVal (EVar 46%nat); RVal (ELit 0)]
      [(13, ELit 1)] [(45%nat, 2 ^ 64); (46%nat, 2 ^ 64)] v r1 [ic_total_out c; is_total s] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1dafc) M s6_rom) R' HR' Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTB1" G end.
    rewrite ?(Z.mod_small (ir_out r1 - ir_left r1) (2 ^ 32)) in Hms by (clear - Hout; lia).
    rewrite <- (le8_wrap64 (ic_total_out c + _)), <- (le8_wrap64 (is_total s + _)) in Hms.
    set (r1o := irset_out r1 (ir_left r1)).
    set (Mo := wbytes M2 (zw (cv_sp v - 224 + 80)) (Z_to_le_bytes 8 (ir_left r1))) in *.
    set (M3 := wbytes Mo (zw (cv_S v + 8)) (Z_to_le_bytes 4 16207)) in *.
    set (M4 := wbytes M3 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16208)) in *.
    set (r' := mkIR (ir_next r1) (ir_have r1) (ir_put r1) (ir_left r1) 0 0 (ir_in r1) (ir_left r1) Z_STREAM_END).
    assert (HMo : LMEM v (mkW s2 c2 r1o) Mo).
    { subst Mo r1o. apply (LMEM_store_outc v C s2 c2 r1 (irset_out r1 (ir_left r1)) M2 HM2 Hput); [reflexivity | cbn; clear - Rlf0 Rpl Rpt0 CP0; lia]. }
    assert (HM3 : LMEM v (mkW (iset_mode s2 LENGTH) c2 r') M3).
    { apply (LMEM_regs v (iset_mode s2 LENGTH) c2 r1o c2 r'); [| reflexivity ..].
      apply (LMEM_store_scalar v C s2 c2 r1o _ Mo 8 _ HMo); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode Mo (cv_S v) _ s2 LENGTH (lm_sc _ _ _ HMo)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM4 : LMEM v (mkW (iset_mode (iset_mode s2 LENGTH) DONE) c2 r') M4).
    { apply (LMEM_store_scalar v C _ c2 r' _ M3 8 _ HM3); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M3 (cv_S v) _ _ DONE (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    exists R', M4, pc6_leave. split; [subst M4 M3 Mo M2 M1; by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split.
    2:{ subst M4 M3 Mo. do 2 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
        exact HF2. }
    split; [exact HM4|]. split.
    { apply (LX_step0 v s c r1 _ c2 r' HX NH NB); subst s2 r'; try reflexivity; [live_mode_tac | cbn; unfold Z_STREAM_END; lia | cbv delta [c2]; rewrite T9; exact Xmsg]. }
    split; [apply (same_blocks_trans _ _ _ SB2); split; [reflexivity | split; reflexivity]|].
    subst r'. leave_regs HR' Hfr.
  Qed.
End CheckBody.
End FXG.
