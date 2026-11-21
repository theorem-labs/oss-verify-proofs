(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Segs6u Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6.

Module InflA_Copy.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.CatSim OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.SeqExec OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StoreOk OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.Hoare OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.StepTac.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Expr OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymEx2Tac OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.MemRel OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.SymAux OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1.RomRead.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Prog OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.ZIface OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateState OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateFast OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateArms OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.Inflate OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInv OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel.InflateInvKit.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Segs6u OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U.Callee6u.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.ISLayout OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S.InflMem.
Import OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.IS6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflRod6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflCtx6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6 OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U.InflArmLib6b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition cmin (s : inflate_state) (r : iregs) : Z :=
  let copy := is_length s in
  let copy := if ir_have r <? copy then ir_have r else copy in
  if ir_left r <? copy then ir_left r else copy.

Definition copy_s (s : inflate_state) (k : Z) : inflate_state := iset_length s (wrap32 (is_length s - k)).
Definition copy_c (c : icall) (r : iregs) (k : Z) : icall :=
  icset_outbuf c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) k).
Definition copy_r (r : iregs) (k : Z) : iregs :=
  irset_put (irset_left (irset_next (irset_have r (wrap32 (ir_have r - k))) (ir_next r + k)) (wrap32 (ir_left r - k))) (ir_put r + k).

Lemma arm_COPY_eq : forall s c r,
  arm_COPY (mkW s c r)
  = if is_length s =? 0 then ARun tt (mkW (iset_mode s TYPE) c r)
    else if cmin s r =? 0 then ALeave (mkW s c r)
    else ARun tt (mkW (copy_s s (cmin s r)) (copy_c c r (cmin s r)) (copy_r r (cmin s r))).
Proof.
  intros s c r. unfold arm_COPY. mstep1 (@gs_eq inflate_state).
  destruct (is_length s =? 0) eqn:E; cbn [negb].
  - rewrite set_mode_eq. reflexivity.
  - mstep1 (@gr_eq iregs). unfold cmin.
    destruct ((if ir_left r <? (if ir_have r <? is_length s then ir_have r else is_length s) then ir_left r
               else if ir_have r <? is_length s then ir_have r else is_length s) =? 0); [rewrite aleave_eq; reflexivity|].
    mstep1 uc_eq. mstep1 ur_eq. rewrite us_eq. reflexivity.
Qed.

Lemma cmin_range : forall s r, 0 <= ir_have r -> 0 <= ir_left r -> 0 < is_length s ->
  0 <= cmin s r <= ir_have r /\ cmin s r <= ir_left r /\ cmin s r <= is_length s
  /\ (cmin s r = 0 <-> ir_have r = 0 \/ ir_left r = 0).
Proof.
  intros s r Hh Hl HL. unfold cmin.
  destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)) | destruct (Z.ltb_spec (ir_left r) (is_length s))]; lia.
Qed.


Section ArmCOPY.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis MEMCPY : memcpy_run6u.

  Definition CREG (w : iw) (R : bvmap 5 word) : Prop := LFIX v R /\ LVARS v w R.

  Lemma copy_zero : forall s c r R M,
    is_mode s = COPY -> is_length s = 0 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> CREG (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (ARun tt (mkW (iset_mode s TYPE) c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HL HM HRC HX (HF & HV) RI CI.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI. open_frame Mfr.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    unfold mapped in *.
    pose proof (is6_length _ _ _ _ Msc) as C92. rewrite HL in C92.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    arm_symex ilS 8%nat [true] [RVal (ELit 0)] (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) R' HR' Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTZ" G end.
    set (M2 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16191)) in Hms.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HM2 : LMEM v (mkW (iset_mode s TYPE) c r) M2).
    { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s TYPE (lm_sc _ _ _ HM)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    arm_disp C HM2 Hfr R2 Hms2 G26' Hfr2.
    exists R2, M2, (arm6_pc (is_mode (iset_mode s TYPE))). split; [eapply msteps_trans; [| exact Hms2]; subst M2; by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
    - split; [exact HM2|]. split.
      { subst M2. retc_tower C HRC. }
      split.
      + apply (LX_step0 v s c r _ c r HX NH NB); try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side].
      + unfold LREG_arm. split.
        { lfix_close2 Hfr2 Hfr HR'. }
        split; [| cbn; unfold TYPE, BAD; intros; exfalso; lia].
        unfold LVARS; cbn [w_r]. regs_via2 Hfr2 Hfr.
    - subst M2.
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.

  Definition MREG (r : iregs) (k : Z) (R : bvmap 5 word) : Prop :=
    getr R 10 = zw (cv_P0 v + ir_put r) /\ getr R 11 = zw (cv_I0 v + ir_next r) /\ getr R 12 = zw k /\ getr R 1 = zw 0x1f610
    /\ getr R 27 = zw k /\ getr R 20 = zw k
    /\ getr R 2 = zw (cv_sp v - 256) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (cv_ZP v)
    /\ getr R 23 = zw (ir_have r) /\ getr R 9 = zw (cv_P0 v + ir_put r)
    /\ getr R 25 = zw (ir_hold r) /\ getr R 19 = zw (ir_bits r) /\ getr R 26 = zw (cv_I0 v + ir_next r)
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.

  Ltac mreg_close HR Hfr :=
    let G10 := fresh in let G11 := fresh in let G12 := fresh in let G1 := fresh in
    let G26 := fresh in let G19 := fresh in
    symex_reg HR (10%bv : reg) as G10; symex_reg HR (11%bv : reg) as G11; symex_reg HR (12%bv : reg) as G12; symex_reg HR (1%bv : reg) as G1;
    symex_reg HR (27%bv : reg) as G26; symex_reg HR (20%bv : reg) as G19;
    unfold MREG; repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite G10; f_equal; lia | rewrite G11; f_equal; lia | rewrite G12; rewrite ?Z.mod_small by lia; f_equal; lia | rewrite G1; reflexivity
          | rewrite G26; rewrite ?Z.mod_small by lia; f_equal; lia | rewrite G19; rewrite ?Z.mod_small by lia; f_equal; lia
          | match goal with |- ?G => idtac "MREG LEFT" G end ].

  Ltac lreg_leave_close HR Hfr :=
    let G26 := fresh in
    symex_reg HR (27%bv : reg) as G26;
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]; repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite G26; apply zw_neg_mod
          | match goal with |- ?G => idtac "LREG LEFT" G end ].

  Lemma copy_pre : forall s c r R M,
    0 < is_length s <= 65535 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> CREG (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    exists R1,
      if cmin s r =? 0
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom) /\ LREG_leave v (mkW s c r) R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) (mkst R1 (Z_to_bv 64 A6U_MEMCPY) M s6u_rom) /\ MREG r (cmin s r) R1.
  Proof.
    intros s c r R M HL HM HRC (HF & HV) RI CI.
    open_ictx C. open_lmem HM. open_retc HRC. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI. open_frame Mfr.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    unfold mapped in *.
    pose proof (is6_length _ _ _ _ Msc) as C92.
    pose proof (cmin_range s r Rhv0 Rlf0 (proj1 HL)) as (K1 & K2 & K3 & K4).
    destruct (Z_lt_le_dec (is_length s) (ir_have r)) as [A|B];
      [destruct (Z_lt_le_dec (is_length s) (ir_left r)) as [A1|A2]; [| destruct (Z.eq_dec (ir_left r) 0) as [Z0|Z0]]
      |destruct (Z_le_gt_dec (ir_left r) (ir_have r)) as [B1|B2]; [destruct (Z.eq_dec (ir_left r) 0) as [Z0|Z0] | destruct (Z.eq_dec (ir_have r) 0) as [Z0|Z0]]].
    -
      assert (EK : cmin s r = is_length s) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [lia|]; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
      rewrite EK. replace (is_length s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 20%nat [false; true; true; true] [RVal (EVar 45%nat); RVal (EVar 39%nat)] (@nil (Z * expr)) [(45%nat, 65536)] v r
        [is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP1" G end.
      exists R'. split; [by_run Hms|]. mreg_close HR' Hfr.
    -
      assert (EK : cmin s r = 0) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [lia|]; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
      rewrite EK. cbn [Z.eqb].
      arm_symex ilS 20%nat [false; true; false; false] [RVal (EVar 45%nat); RVal (EVar 39%nat); RVal (EVar 46%nat)] (@nil (Z * expr)) [(45%nat, 65536); (46%nat, 2 ^ 64)] v r
        [is_length s; ir_ret r mod 2 ^ 64] NoVals F0 (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP2" G end.
      exists R'. split; [by_run Hms|]. lreg_leave_close HR' Hfr.
    -
      assert (EK : cmin s r = ir_left r) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [lia|]; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
      rewrite EK. replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 20%nat [false; true; false; true] [RVal (EVar 45%nat); RVal (EVar 39%nat)] (@nil (Z * expr)) [(45%nat, 65536)] v r
        [is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP3" G end.
      exists R'. split; [by_run Hms|]. mreg_close HR' Hfr.
    -
      assert (EK : cmin s r = 0) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)); lia | destruct (Z.ltb_spec (ir_left r) (is_length s)); lia]).
      rewrite EK. cbn [Z.eqb].
      arm_symex ilS 20%nat [false; false; true; false] [RVal (EVar 45%nat); RVal (EVar 39%nat); RVal (EVar 46%nat)] (@nil (Z * expr)) [(45%nat, 65536); (46%nat, 2 ^ 64)] v r
        [is_length s; ir_ret r mod 2 ^ 64] NoVals F0 (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP4" G end.
      exists R'. split; [by_run Hms|]. lreg_leave_close HR' Hfr.
    -
      assert (EK : cmin s r = ir_left r) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)); lia | destruct (Z.ltb_spec (ir_left r) (is_length s)); lia]).
      rewrite EK. replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 20%nat [false; false; true; true] [RVal (EVar 45%nat); RVal (EVar 39%nat)] (@nil (Z * expr)) [(45%nat, 65536)] v r
        [is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP5" G end.
      exists R'. split; [by_run Hms|]. mreg_close HR' Hfr.
    -
      assert (EK : cmin s r = 0) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)); lia | destruct (Z.ltb_spec (ir_left r) (is_length s)); lia]).
      rewrite EK. cbn [Z.eqb].
      arm_symex ilS 20%nat [false; false; false; false] [RVal (EVar 45%nat); RVal (EVar 39%nat); RVal (EVar 46%nat)] (@nil (Z * expr)) [(45%nat, 65536); (46%nat, 2 ^ 64)] v r
        [is_length s; ir_ret r mod 2 ^ 64] NoVals F0 (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP6" G end.
      exists R'. split; [by_run Hms|]. lreg_leave_close HR' Hfr.
    -
      assert (EK : cmin s r = ir_have r) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)); lia | destruct (Z.ltb_spec (ir_left r) (is_length s)); lia]).
      rewrite EK. replace (ir_have r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 20%nat [false; false; false; true] [RVal (EVar 45%nat); RVal (EVar 39%nat)] (@nil (Z * expr)) [(45%nat, 65536)] v r
        [is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP7" G end.
      exists R'. split; [by_run Hms|]. mreg_close HR' Hfr.
  Qed.

  Definition copy_r1 (r : iregs) (k : Z) : iregs :=
    mkIR (ir_next r + k) (ir_have r - k) (ir_put r + k) (ir_left r) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r).

  Lemma copy_call : forall s c r R1 M1 k,
    LMEM v (mkW s c r) M1 -> MREG r k R1 -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    0 < k -> k <= ir_have r -> k <= ir_left r ->
    let M2 := wbytes M1 (zw (cv_P0 v + ir_put r)) (cbytes (arr_get (ic_input c)) (ir_next r) (Z.to_nat k)) in
    exists R2,
      msteps s6u_segs (mkst R1 (Z_to_bv 64 A6U_MEMCPY) M1 s6u_rom) (mkst R2 (Z_to_bv 64 0x1f610) M2 s6u_rom)
      /\ (forall rg, reg_in rg memcpy_clob = false -> getr R2 rg = getr R1 rg)
      /\ LMEM v (mkW s (copy_c c r k) (copy_r1 r k)) M2.
  Proof.
    intros s c r R1 M1 k HM1 HJ RI CI Hk Hkh Hkl. cbv zeta.
    destruct HJ as (G10 & G11 & G12 & G1 & _).
    open_ictx C. open_lmem HM1. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (HNI : 0 < cv_NI v) by (clear - Hk Hkh Rnx0 Rnh; lia). assert (HNO : 0 < cv_NO v) by (clear - Hk Hkl Rpt0 Rpl; lia).
    assert (Hn : Z.of_nat (Z.to_nat k) = k) by (apply Z2Nat.id; lia).
    pose proof (cells_rdn_bytes s6u_segs M1 (cv_I0 v) (cv_NI v) (arr_get (ic_input c)) (ir_next r) (Z.to_nat k) Minp
                  ltac:(lia) ltac:(rewrite Hn; clear - Hkh Rnh; lia) ltac:(lia) ltac:(lia)) as Hsrc.
    destruct (MEMCPY _ R1 (cv_P0 v + ir_put r) (cv_I0 v + ir_next r) (Z.to_nat k) _ (zw 0x1f610) Hsrc
               ltac:(clear - CP0 Rpt0; lia) ltac:(rewrite Hn; clear - CP0 Rpt0 Rpl Hkl; lia) ltac:(clear - CI0 Rnx0; lia) ltac:(rewrite Hn; clear - CI0 Rnx0 Rnh Hkh; lia))
      as (R2 & Hms & _ & Hfr).
    - rewrite Hn. unfold sep in CIP. clear - CIP Hkh Hkl Rnx0 Rnh Rpt0 Rpl CI0 CP0 Hk. lia.
    - rewrite Hn. intros x Hx. apply Mmap_P. clear - Hx Hkl Rpt0 Rpl Hk. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - exact G1.
    - exact G10.
    - exact G11.
    - change (reg_get R1 12) with (getr R1 12). rewrite G12. f_equal. lia.
    - exists R2. split; [change (Z_to_bv 64 A6U_MEMCPY) with (zw A6U_MEMCPY); exact Hms|]. split; [exact Hfr|].
      unfold copy_c. rewrite <- Hn at 1.
      apply (LMEM_blit_out v C s c r (copy_r1 r k) (Z.to_nat k) M1 HM1); rewrite ?Hn; try lia; first [exact Col | exact Cinb | cbn; lia | reflexivity].
  Qed.

  Definition post_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 34%nat); (23, EVar 36%nat); (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
     (26, EAdd (EVar 43%nat) (EVar 44%nat)); (20, EVar 45%nat); (27, EVar 45%nat)].

  Lemma copy_r_small : forall r k, 0 <= k <= ir_have r -> k <= ir_left r -> ir_have r < 2 ^ 32 -> ir_left r < 2 ^ 32 ->
    copy_r r k = mkIR (ir_next r + k) (ir_have r - k) (ir_put r + k) (ir_left r - k) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r).
  Proof.
    intros r k Hk Hkl Hh Hl. unfold copy_r. destruct r; cbn in *. rewrite !wrap32_id by lia. reflexivity.
  Qed.
  Lemma copy_s_small : forall s k, 0 <= k <= is_length s -> is_length s < 2 ^ 32 -> copy_s s k = iset_length s (is_length s - k).
  Proof. intros s k Hk HL. unfold copy_s. rewrite wrap32_id by lia. reflexivity. Qed.

  Lemma copy_post : forall s c r R2 M k,
    is_mode s = COPY -> 0 < k -> k <= ir_have r -> k <= ir_left r -> k <= is_length s <= 65535 ->
    LMEM v (mkW s c (copy_r1 r k)) M ->
    RINV (cv_NI v) (cv_NO v) r ->
    getr R2 20 = zw k -> getr R2 27 = zw k ->
    getr R2 2 = zw (cv_sp v - 256) -> getr R2 8 = zw (cv_S v) -> getr R2 18 = zw (cv_ZP v) -> getr R2 23 = zw (ir_have r) -> getr R2 9 = zw (cv_P0 v + ir_put r) ->
    getr R2 25 = zw (ir_hold r) -> getr R2 19 = zw (ir_bits r) -> getr R2 26 = zw (cv_I0 v + ir_next r) ->
    getr R2 3 = getr (cv_R0 v) 3 -> getr R2 4 = getr (cv_R0 v) 4 ->
    let M3 := wbytes (wbytes M (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r - k))) (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - k)) in
    exists R',
      msteps s6u_segs (mkst R2 (Z_to_bv 64 0x1f610) M s6u_rom) (mkst R' (Z_to_bv 64 (arm6_pc (is_mode (copy_s s k)))) M3 s6u_rom)
      /\ LFIX v R' /\ LVARS v (mkW s c (copy_r r k)) R' /\ getr R' 27 = zw (-3)
      /\ LMEM v (mkW (copy_s s k) c (copy_r r k)) M3.
  Proof.
    intros s c r R2 M k Hmode Hk Hkh Hkl HkL HM RI G19 G26 G2 G27 G8 G24 G9 G22 G18 G25 G3 G4. cbv zeta.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. unfold mapped in *.
    assert (Hh32 : ir_have r < 2 ^ 32) by (clear - Rnh Rnx0 CI0; lia). assert (Hl32 : ir_left r < 2 ^ 32) by (clear - Rpl Rpt0 CP0; lia).
    rewrite (copy_r_small r k) in * by lia. rewrite (copy_s_small s k) by lia.
    cbn [copy_r1 ir_put ir_out ir_left ir_next ir_have ir_hold ir_bits ir_in ir_ret] in *.
    pose proof (is6_length _ _ _ _ Msc) as C92. pose proof (is6_mode _ _ _ _ Msc) as C8. rewrite Hmode in C8.
    arm_symexP (@nil (Z * expr)) ilS 30%nat [true; true; true; true; true; true]
      [RVal (ELit 16209); RVal (EVar 46%nat); RVal (EVar 39%nat); RVal (EVar 35%nat)]
      post_pins [(45%nat, 65536); (46%nat, 65536)] v r
      [k; is_length s] NoVals F0
      (mkst R2 (Z_to_bv 64 0x1f610) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTQ1" G end.
    rewrite ?le4_szwrap in Hms1. rewrite (szwrap32_small (ir_left r - k)) in Hms1 by (clear - Hkl Hk Rpl Rpt0 CP0; lia).
    set (M2 := wbytes M (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r - k))) in *.
    set (M3 := wbytes M2 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - k))) in *.
    assert (Hput : 0 <= ir_put r + k <= cv_NO v) by (clear - Rpt0 Rpl Rlf0 Hkl Hk; lia).
    set (r3 := mkIR (ir_next r + k) (ir_have r - k) (ir_put r + k) (ir_left r - k) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r)) in *.
    assert (HM2 : LMEM v (mkW s c r3) M2).
    { subst M2. apply (LMEM_store_leftc v C s c _ r3 M HM); cbn [ir_put ir_left ir_out r3]; [exact Hput | reflexivity | clear - Hkl Hl32 Hk; lia | reflexivity]. }
    assert (HM3 : LMEM v (mkW (iset_length s (is_length s - k)) c r3) M3).
    { apply (LMEM_store_scalar v C s c _ _ M2 108 _ HM2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_length M2 (cv_S v) _ s _ (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    arm_disp C HM3 Hfr1 R' Hms2 G26' Hfr2. subst r3.
    exists R'. split.
    { eapply msteps_trans; [| exact Hms2]. subst M3 M2. by_run Hms1. }
    split; [| split; [| split; [exact G26' | exact HM3]]].
    - lfix_close2 Hfr2 Hfr1 HR1.
    - unfold LVARS; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next].
      symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (9%bv : reg) as Q9. symex_reg HR1 (26%bv : reg) as Q25.
      regs_via2 Hfr2 Hfr1.
      + rewrite Q24. rewrite ?szwrap32_small by (clear - Hkh Hk Rnh Rnx0 CI0 Rhv0; lia). f_equal; lia.
      + rewrite Q9. f_equal; lia.
      + rewrite Q25. f_equal; lia.
  Qed.

  Lemma copy_core : forall s c r R M,
    is_mode s = COPY -> 0 <= is_length s <= 65535 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> CREG (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f5c4) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_COPY (mkW s c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HL HM HRC HX HJ RI CI.
    rewrite arm_COPY_eq.
    destruct (Z.eq_dec (is_length s) 0) as [L0|L0].
    { rewrite (proj2 (Z.eqb_eq _ _) L0). exact (copy_zero s c r R M Hmode L0 HM HRC HX HJ RI CI). }
    rewrite (proj2 (Z.eqb_neq _ _) L0).
    pose proof HJ as (HF & HV).
    destruct (copy_pre s c r R M ltac:(lia) HM HRC HJ RI CI) as (R1 & H1).
    open_ictx C. pose proof RI as RI'. open_rinv RI'. pose proof CI as CI'. open_cinv CI'. open_lx HX. open_fix HF.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    pose proof (cmin_range s r Rhv0 Rlf0 ltac:(lia)) as (K1 & K2 & K3 & K4).
    destruct (Z.eqb_spec (cmin s r) 0) as [Kz|Kz].
    -
      destruct H1 as (Hms1 & HL1). exists R1, M, pc6_leave. split; [exact Hms1|].
      cbn [arm_post]. split; [reflexivity|]. split; [| apply MFRAME_refl].
      split; [exact HM|]. split; [exact HX|]. split; [apply same_blocks_refl | exact HL1].
    -
      destruct H1 as (Hms1 & HJ1). set (k := cmin s r) in *.
      destruct (copy_call s c r R1 M k HM HJ1 RI CI ltac:(lia) ltac:(lia) ltac:(lia)) as (R2 & Hms2 & Hfr2 & HM2).
      set (M2 := wbytes M (zw (cv_P0 v + ir_put r)) (cbytes (arr_get (ic_input c)) (ir_next r) (Z.to_nat k))) in *.
      assert (Hn : Z.of_nat (Z.to_nat k) = k) by (apply Z2Nat.id; lia).
      destruct HJ1 as (_ & _ & _ & _ & J26 & J19 & J2 & J27 & J8 & J24 & J9 & J22 & J18 & J25 & J3 & J4).
      destruct (copy_post s (copy_c c r k) r R2 M2 k Hmode ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HM2 RI
                  ltac:(rewrite (Hfr2 (20%bv : reg) eq_refl); exact J19) ltac:(rewrite (Hfr2 (27%bv : reg) eq_refl); exact J26)
                  ltac:(rewrite (Hfr2 (2%bv : reg) eq_refl); exact J2) ltac:(rewrite (Hfr2 (8%bv : reg) eq_refl); exact J27)
                  ltac:(rewrite (Hfr2 (18%bv : reg) eq_refl); exact J8) ltac:(rewrite (Hfr2 (23%bv : reg) eq_refl); exact J24)
                  ltac:(rewrite (Hfr2 (9%bv : reg) eq_refl); exact J9)
                  ltac:(rewrite (Hfr2 (25%bv : reg) eq_refl); exact J22) ltac:(rewrite (Hfr2 (19%bv : reg) eq_refl); exact J18)
                  ltac:(rewrite (Hfr2 (26%bv : reg) eq_refl); exact J25)
                  ltac:(rewrite (Hfr2 (3%bv : reg) eq_refl); exact J3)
                  ltac:(rewrite (Hfr2 (4%bv : reg) eq_refl); exact J4))
        as (R' & Hms3 & HF' & HV' & G26' & HM3).
      set (M3 := wbytes (wbytes M2 (zw (cv_sp v - 256 + 112)) (Z_to_le_bytes 8 (ir_left r - k))) (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - k))) in *.
      exists R', M3, (arm6_pc (is_mode (copy_s s k))).
      split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
      assert (Ers : copy_r r k = mkIR (ir_next r + k) (ir_have r - k) (ir_put r + k) (ir_left r - k) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r))
        by (apply copy_r_small; clear - K1 K2 Rnh Rnx0 CI0 Rpl Rpt0 CP0; lia).
      assert (Ess : copy_s s k = iset_length s (is_length s - k)) by (apply copy_s_small; lia).
      pose proof (icset_outbuf_facts c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) k)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      cbn [arm_post w_s w_r]. split; [reflexivity|].
      split; [| split].
      + split; [exact HM3|].
        split.
        { subst M3 M2. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS; cbn; lia].
          apply (RETC_other v C); [| clear - Csp; lia | clear - Csp; cbn; lia | clear; cbn; lia].
          apply (RETC_other v C); [| clear - CP0 Rpt0; lia | rewrite cbytes_length, Hn; clear - CP0 Rpt0 Rpl K2; lia
            | rewrite cbytes_length, Hn; specialize (CfP ltac:(clear - K2 Kz K1 Rpl Rpt0; lia)); unfold sep in CfP; clear - CfP Rpt0 Rpl K1 K2 Kz; lia].
          eapply RETC_regs; [exact HRC | rewrite Ers; reflexivity]. }
        split.
        { rewrite Ess, Ers. unfold copy_c. apply (LX_step0 v s c r _ _ _ HX NH NB); try reflexivity.
          - replace (is_mode (iset_length s _)) with (is_mode s) by (destruct s; reflexivity). exact Xlive.
          - exact Xret.
          - rewrite E11. exact Xmsg.
          - bk_side. }
        split; [exact HF'|]. split; [exact HV'|]. intros _; exact G26'.
      + rewrite Ess. apply same_blocks_length.
      + cbn [w_r]. rewrite Ers. cbn [ir_put]. subst M3 M2.
        apply (MFRAME_store v (ir_put r) (ir_put r + k) (ir_put r + k)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r + k) (ir_put r + k)); [| lia | clear - Csp; lia | clear - Csp; cbn; lia | left; unfold INF_FRAME, INF_SCRATCH; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r + k) M M); [apply MFRAME_refl | lia | clear - CP0 Rpt0; lia | rewrite cbytes_length, Hn; clear - CP0 Rpt0 Rpl K2; lia | right; right; right; rewrite cbytes_length, Hn; clear - K1; lia].
  Qed.

End ArmCOPY.

Section ArmCOPY2.
  Hypothesis MEMCPY : memcpy_run6u.

  Lemma sinv_copy_length : forall s, sinv s -> (is_mode s = COPY_ \/ is_mode s = COPY) -> 0 <= is_length s <= 65535.
  Proof. intros s HS Hm. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact (H Hm). Qed.

  Theorem arm_COPY_sim : arm_stmt COPY.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) COPY) with arm_COPY.
    destruct HE as (HM & HRC & HX & (HF & HV & G26)). open_pinv HP.
    exact (copy_core v C MEMCPY s c r R M Hmode (sinv_copy_length s PS (or_intror Hmode)) HM HRC HX (conj HF HV) RI CI).
  Qed.

  Lemma copy__core : forall v s c r R M,
    ictx v -> is_mode s = COPY_ -> 0 <= is_length s <= 65535 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> CREG v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f5bc) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r) M (arm_COPY (mkW (iset_mode s COPY) c r)) R' M' pc'.
  Proof.
    intros v s c r R M C Hmode HL HM HRC HX (HF & HV) RI CI.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    arm_symex ilS 4%nat (@nil bool) (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x1f5bc) M s6u_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16195)) in *.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HM1 : LMEM v (mkW (iset_mode s COPY) c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s COPY Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC1 : RETC v (mkW (iset_mode s COPY) c r) M1) by (subst M1; retc_tower C HRC).
    assert (HX1 : LX v (mkW (iset_mode s COPY) c r)).
    { apply (LX_step0 v s c r _ c r HX NH NB); try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side]. }
    assert (HJ1 : CREG v (mkW (iset_mode s COPY) c r) R1).
    { split; [apply (LFIX_frame v R R1 _ HF Hfr1); reflexivity|]. unfold LVARS; cbn [w_r]. regs_via Hfr1. }
    destruct (copy_core v C MEMCPY (iset_mode s COPY) c r R1 M1 ltac:(destruct s; reflexivity)
                ltac:(replace (is_length (iset_mode s COPY)) with (is_length s) by (destruct s; reflexivity); exact HL)
                HM1 HRC1 HX1 HJ1 RI CI) as (R' & M' & pc' & Hms2 & HPOST).
    exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M1; by_run Hms1|].
    apply (arm_post_chain v (mkW s c r) (mkW (iset_mode s COPY) c r) M M1); [apply same_blocks_mode | | exact HPOST].
    cbn [w_r]. subst M1.
    apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.

  Theorem arm_COPY__sim : arm_stmt COPY_.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) COPY_) with arm_COPY_.
    unfold arm_COPY_. rewrite abind_run, set_mode_eq.
    destruct HE as (HM & HRC & HX & (HF & HV & G26)). open_pinv HP.
    exact (copy__core v s c r R M C Hmode (sinv_copy_length s PS (or_introl Hmode)) HM HRC HX (conj HF HV) RI CI).
  Qed.
End ArmCOPY2.
End FXG.
End InflA_Copy.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6U Require Import Segs6u Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6. Import InflA_Copy.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.PropExec.FPState}.


Definition r_bb (r : iregs) : iregs :=
  irset_bits (irset_hold r (Z.shiftr (ir_hold r) (Z.land (ir_bits r) 7))) (wrap32 (ir_bits r - Z.land (ir_bits r) 7)).

Definition stored_B (w1 : iw) : ares unit :=
  let s := w_s w1 in let c := w_c w1 in let r := w_r w1 in
  let hold := ir_hold r in
  if negb (Z.land hold 65535 =? Z.lxor (Z.shiftr hold 16) 65535)
  then ARun tt (mkW (iset_mode s BAD) (icset_msg c MSG_invalid_stored_block_lengths) r)
  else arm_COPY (mkW (iset_mode (iset_mode (iset_length s (Z.land (wrap32 hold) 65535)) COPY_) COPY) c
                      (irset_bits (irset_hold r 0) 0)).

Lemma arm_STORED_run : forall flush s c r s1 c1 r1,
  flush <> Z_TREES ->
  NEEDBITS 32 (mkW s c (r_bb r)) = ARun tt (mkW s1 c1 r1) ->
  arm_STORED ivar_ref flush (mkW s c r) = stored_B (mkW s1 c1 r1).
Proof.
  intros flush s c r s1 c1 r1 Hf HN.
  unfold arm_STORED. mstep1 BYTEBITS_eq. change (irset_bits _ _) with (r_bb r). rewrite abind_run, HN.
  mstep1 HOLD_eq. unfold stored_B. cbn [w_s w_c w_r].
  destruct (negb (Z.land (ir_hold r1) 65535 =? Z.lxor (Z.shiftr (ir_hold r1) 16) 65535)); [rewrite go_bad_eq; reflexivity|].
  mstep1 us_eq. mstep1 INITBITS_eq. mstep1 set_mode_eq. cbn [iv_flush_exits ivar_ref andb].
  replace (flush =? Z_TREES) with false by (symmetry; apply Z.eqb_neq; exact Hf).
  unfold arm_COPY_. mstep1 set_mode_eq. reflexivity.
Qed.

Lemma arm_STORED_leave : forall flush s c r w1,
  NEEDBITS 32 (mkW s c (r_bb r)) = ALeave w1 -> arm_STORED ivar_ref flush (mkW s c r) = ALeave w1.
Proof.
  intros flush s c r w1 HN. unfold arm_STORED. mstep1 BYTEBITS_eq. change (irset_bits _ _) with (r_bb r). rewrite abind_run, HN. reflexivity.
Qed.

Lemma r_bb_small : forall r, 0 <= ir_bits r < 64 -> 0 <= ir_hold r < 2 ^ ir_bits r ->
  r_bb r = mkIR (ir_next r) (ir_have r) (ir_put r) (ir_left r) (ir_hold r / 2 ^ (ir_bits r mod 8)) (ir_bits r - ir_bits r mod 8)
                (ir_in r) (ir_out r) (ir_ret r)
  /\ 0 <= ir_hold r / 2 ^ (ir_bits r mod 8) < 2 ^ (ir_bits r - ir_bits r mod 8)
  /\ 0 <= ir_bits r mod 8 < 8 /\ ir_bits r mod 8 <= ir_bits r.
Proof.
  intros r Hb Hh. pose proof (land7_mod (ir_bits r)) as E7.
  assert (Hm8 : 0 <= ir_bits r mod 8 < 8) by (apply Z.mod_pos_bound; lia).
  assert (Hml : ir_bits r mod 8 <= ir_bits r) by (apply Z.mod_le; lia).
  pose proof (hold_drop (ir_hold r) (ir_bits r) (ir_bits r mod 8) ltac:(lia) Hh) as HD.
  split; [| split; [exact HD | split; [exact Hm8 | exact Hml]]].
  unfold r_bb. destruct r; cbn in *. rewrite E7. rewrite shiftr_div by lia. rewrite wrap32_id by lia. reflexivity.
Qed.


Definition ilN : cfg := ilSx [0x1f274; 0x1f578] [AV (EAdd (EVar 43%nat) (EVar 44%nat)) 0 1 0 (EVar 44%nat)].

Section ArmSTORED.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis MEMCPY : memcpy_run6u.

  Definition JS (h0 n0 b0 : Z) (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r)
    /\ getr R 12 = zw (ir_have r) /\ getr R 6 = zw (cv_I0 v + ir_next r) /\ getr R 16 = zw (cv_I0 v + ir_next r)
    /\ getr R 5 = zw (ir_bits r) /\ getr R 19 = zw (ir_bits r)
    /\ getr R 23 = zw h0 /\ getr R 26 = zw (cv_I0 v + n0) /\ getr R 15 = zw b0
    /\ ir_have r + ir_next r = h0 + n0 /\ ir_bits r = b0 + 8 * (ir_next r - n0) /\ 0 <= h0 < 2 ^ 31 /\ 0 <= b0 /\ 0 <= n0.
  Definition JE (c : icall) (r : iregs) (R : bvmap 5 word) : Prop :=
    LFIX v R /\ getr R 9 = zw (cv_P0 v + ir_put r) /\ getr R 25 = zw (ir_hold r)
    /\ getr R 14 = zw (cv_I0 v + ir_next r) /\ getr R 12 = zw (ir_have r) /\ getr R 19 = zw (ir_bits r).

  Ltac open_js HJ :=
    let X := fresh in pose proof HJ as X; unfold JS in X;
    destruct X as (HF & G9 & G22 & G12 & G6 & G16 & G5 & G18 & G24 & G25 & G15 & E1 & E2 & Hh0 & Hb0 & Hn00); open_fix HF.

  Definition js_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (11, EVar 35%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat);
     (12, EVar 36%nat); (6, EAdd (EVar 43%nat) (EVar 44%nat)); (16, EAdd (EVar 43%nat) (EVar 44%nat)); (5, EVar 41%nat); (19, EVar 41%nat);
     (23, EVar 45%nat); (26, EAdd (EVar 43%nat) (EVar 46%nat)); (15, EVar 47%nat)].

  Ltac js_close HR Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00 :=
    let Q12 := fresh in let Q22 := fresh in let Q5 := fresh in let Q18 := fresh in let Q6 := fresh in let Q16 := fresh in let Q14 := fresh in
    symex_reg HR (12%bv : reg) as Q12; symex_reg HR (25%bv : reg) as Q22; symex_reg HR (5%bv : reg) as Q5; symex_reg HR (19%bv : reg) as Q18;
    symex_reg HR (6%bv : reg) as Q6; symex_reg HR (16%bv : reg) as Q16; symex_reg HR (14%bv : reg) as Q14;
    cbn [famA] in Q22; rewrite bmod_get in Q22 by exact Hby;
    rewrite (zalu_sll_small (arr_get (ic_input c) (ir_next r)) (ir_bits r)) in Q22;
      [| clear - Hby; lia | clear - Rbits Hb; lia
       | clear - Hby Rbits Hb; pose proof (pull_hold_lt 0 _ _ (conj (Z.le_refl 0) (Z.pow_pos_nonneg 2 (ir_bits r) ltac:(lia) ltac:(lia))) ltac:(lia) Hby);
         assert (2 ^ (ir_bits r + 8) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia); lia];
    unfold JS, JE, pull1; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret];
    repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- LFIX _ _ => lfix_close Hfr HR end
          | lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite Q12; rewrite ?szwrap32_small by (clear - Hh Rnh Rnx0 CI0; lia); f_equal; lia
          | rewrite Q22; f_equal; lia
          | rewrite Q5; f_equal; lia
          | rewrite Q18; rewrite ?szwrap32_small by (clear - Rbits Hb; lia); f_equal; lia
          | rewrite Q6; f_equal; lia
          | rewrite Q16; f_equal; lia
          | rewrite Q14; f_equal; lia
          | clear - E1 E2 Hh0 Hb0 Hn00; lia
          | match goal with |- ?G => idtac "JS LEFT" G end ].

  Lemma stored_step_H : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> JS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r + 8 < 32 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f274) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f274) M s6u_rom)
               /\ JS h0 n0 b0 c (pull1 c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HJ RI CI Hb Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP js_pins ilN 20%nat [true; true; true] [RVal (EVar 35%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s)
      (mkst R (Z_to_bv 64 0x1f274) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: try match goal with |- ?G => idtac "LEFTH" G end.
    exists R1. split; [by_run Hms|].
    js_close HR1 Hfr HF c r Hby Rbits Rhold Hb Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma stored_step_E : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> JS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> 32 <= ir_bits r + 8 -> 0 < ir_have r ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f274) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f578) M s6u_rom)
               /\ JE c (pull1 c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HJ RI CI Hb Hb8 Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hby : 0 <= arr_get (ic_input c) (ir_next r) < 256) by (apply Cinb; clear - Hh Rnx0 Rhv0 Rnh; lia).
    pose proof (cells_bmod _ _ _ _ Minp Cinb) as Hin0.
    pose proof (fun j (_ : 0 <= j < cv_NI v) => bmod_range (arr_get (ic_input c)) j) as Hinr.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP js_pins ilN 20%nat [true; true; false] [RVal (EVar 35%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64)] v r [h0; n0; b0] NoVals
      (famA c s)
      (mkst R (Z_to_bv 64 0x1f274) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: try match goal with |- ?G => idtac "LEFTE" G end.
    exists R1. split; [by_run Hms|].
    assert (Hb' : ir_bits r + 8 < 64) by (clear - Hb; lia).
    js_close HR1 Hfr HF c r Hby Rbits Rhold Hb' Hh Rnh Rnx0 CI0 E1 E2 Hh0 Hb0 Hn00.
  Qed.

  Lemma stored_dry : forall h0 n0 b0 s c r R M,
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> JS h0 n0 b0 c r R -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    ir_bits r < 32 -> ir_have r = 0 ->
    exists R1, msteps s6u_segs (mkst R (Z_to_bv 64 0x1f274) M s6u_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6u_rom)
               /\ LREG_leave v (mkW s c r) R1.
  Proof.
    intros h0 n0 b0 s c r R M HM HRC HJ RI CI Hb Hh. open_js HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (Hn0 : 0 <= cv_I0 v + n0 < 2 ^ 63) by (clear - E1 Hh0 Hn00 Rnx0 Rhv0 Rnh CI0 Hh; lia).
    arm_symexP js_pins ilN 12%nat [false] [RVal (EVar 48%nat)] (@nil (Z * expr))
      [(45%nat, 2 ^ 31); (46%nat, 2 ^ 63); (47%nat, 2 ^ 64); (48%nat, 2 ^ 64)] v r
      [h0; n0; b0; ir_ret r mod 2 ^ 64] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1f274) M s6u_rom) R1 HR1 Hfr Hms.
    all: try arm_side.
    all: try match goal with |- ?G => idtac "LEFTD" G end.
    exists R1. split; [by_run Hms|].
    symex_reg HR1 (27%bv : reg) as Q26. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (26%bv : reg) as Q25. symex_reg HR1 (23%bv : reg) as Q24.
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]. repeat match goal with |- _ /\ _ => split end;
      first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
            | rewrite Q26; apply zw_neg_mod
            | rewrite Q24; f_equal; clear - Hh; lia
            | rewrite Q18; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | rewrite Q25; rewrite ?Z.mod_small by (clear - Hh0; lia); f_equal; clear - E1 E2 Hh Hh0; lia
            | match goal with |- ?G => idtac "DRY LEFT" G end ].
  Qed.

  Ltac open_je HJ :=
    let X := fresh in pose proof HJ as X; unfold JE in X;
    destruct X as (HF & G9 & G22 & G14 & G12 & G18); open_fix HF.
  Definition je_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (13, EVar 34%nat); (18, EVar 34%nat); (11, EVar 35%nat); (1, ELit 16209);
     (9, EAdd (EVar 37%nat) (EVar 38%nat)); (25, EVar 40%nat); (19, EVar 41%nat);
     (14, EAdd (EVar 43%nat) (EVar 44%nat)); (12, EVar 36%nat)].

  Lemma stored_chk : forall h, 0 <= h ->
    (Z.land h 65535 =? Z.lxor (Z.shiftr h 16) 65535) = (Z.lxor (h / 2 ^ 16) (h mod 2 ^ 16) =? 65535).
  Proof.
    intros h Hh.
    change 65535 with (Z.ones 16) at 1. rewrite Z.land_ones by lia. change (Z.ones 16) with 65535.
    rewrite Z.shiftr_div_pow2 by lia.
    set (hi := h / 2 ^ 16). set (lo := h mod 2 ^ 16).
    destruct (Z.eqb_spec lo (Z.lxor hi 65535)) as [E|N]; destruct (Z.eqb_spec (Z.lxor hi lo) 65535) as [E'|N']; try reflexivity; exfalso.
    - apply N'. rewrite E. rewrite <- Z.lxor_assoc. rewrite Z.lxor_nilpotent. rewrite Z.lxor_0_l. reflexivity.
    - apply N. rewrite <- E'. rewrite <- Z.lxor_assoc. rewrite Z.lxor_nilpotent. rewrite Z.lxor_0_l. reflexivity.
  Qed.
  Lemma stored_len : forall h, 0 <= h -> Z.land (wrap32 h) 65535 = h mod 2 ^ 16.
  Proof.
    intros h Hh. rewrite wrap32_mod. change 65535 with (Z.ones 16). rewrite Z.land_ones by lia.
    apply mod_pow2_le. lia.
  Qed.

  Lemma stored_B_sim : forall s c r1 R M,
    is_mode s = STORED ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> JE c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 32 <= ir_bits r1 ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 0x1f578) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v (mkW s c r1) M (stored_B (mkW s c r1)) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode HM HRC HX HJ RI CI Hb32. open_je HJ.
    open_ictx C. open_lmem HM. open_frame Mfr. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    unfold stored_B. cbn [w_s w_c w_r]. rewrite stored_chk by (clear - Rhold; lia). rewrite stored_len by (clear - Rhold; lia).
    assert (Hlo : 0 <= ir_hold r1 mod 2 ^ 16 < 65536) by (apply Z.mod_pos_bound; lia).
    destruct (Z.eqb_spec (Z.lxor (ir_hold r1 / 2 ^ 16) (ir_hold r1 mod 2 ^ 16)) 65535) as [EQ|NE]; cbn [negb].
    -
      arm_symexP je_pins ilS 20%nat [false; true] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f578) M s6u_rom) R1 HR1 Hfr1 Hms1.
      all: try arm_side.
      set (L := ir_hold r1 mod 2 ^ 16) in *.
      set (M1 := wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 L)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16194)) in *.
      set (s2 := iset_mode (iset_length s L) COPY_) in *.
      set (r2 := irset_bits (irset_hold r1 0) 0) in *.
      assert (HM1 : LMEM v (mkW (iset_length s L) c r1) M1).
      { apply (LMEM_store_scalar v C s c r1 _ M 108 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_length M (cv_S v) _ s L Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2' : LMEM v (mkW s2 c r1) M2).
      { apply (LMEM_store_scalar v C _ c r1 _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ _ COPY_ (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM2 : LMEM v (mkW s2 c r2) M2) by (apply (LMEM_regs v s2 c r1 c r2 M2 HM2'); subst r2; reflexivity).
      assert (HRC2 : RETC v (mkW s2 c r2) M2) by (subst M2 M1; retc_tower C HRC).
      assert (HX2 : LX v (mkW s2 c r2)).
      { apply (LX_step0 v s c r1 _ c r2 HX NH NB); subst s2 r2; try reflexivity; [live_mode_tac | exact Xret | exact Xmsg | bk_side]. }
      assert (HJ2 : CREG v (mkW s2 c r2) R1).
      { split; [lfix_close Hfr1 HR1|].
        symex_reg HR1 (25%bv : reg) as Q22. symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (23%bv : reg) as Q24. symex_reg HR1 (26%bv : reg) as Q25.
        unfold LVARS; cbn [w_r]. subst r2. cbn [ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next irset_bits irset_hold].
        regs_via Hfr1; first [exact Q22 | exact Q18 | exact Q24 | exact Q25 | match goal with |- ?G => idtac "CREG LEFT" G end]. }
      assert (RI2 : RINV (cv_NI v) (cv_NO v) r2).
      { subst r2. unfold RINV in *. cbn. clear - RI. change (2 ^ 0) with 1. lia. }
      destruct (copy__core MEMCPY v s2 c r2 R1 M2 C ltac:(subst s2; destruct s; reflexivity)
                  ltac:(subst s2; replace (is_length _) with L by (destruct s; reflexivity); clear - Hlo; lia)
                  HM2 HRC2 HX2 HJ2 RI2 CI) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms1|].
      apply (arm_post_chain v (mkW s c r1) (mkW s2 c r2) M M2); [subst s2; split; [reflexivity | split; reflexivity] | | exact HPOST].
      cbn [w_r]. subst r2. cbn [ir_put irset_bits irset_hold]. subst M2 M1.
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
    -
      arm_symexP je_pins ilS 20%nat [true] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r1 (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f578) M s6u_rom) R' HR' Hfr Hms.
      all: try arm_side.
      set (M1 := wbytes M (zw (cv_ZP v + 48)) (Z_to_le_bytes 8 66326)) in *.
      set (M2 := wbytes M1 (zw (cv_S v + 8)) (Z_to_le_bytes 4 16209)) in *.
      set (c' := icset_msg c MSG_invalid_stored_block_lengths).
      assert (HM1 : LMEM v (mkW s c' r1) M1) by (exact (LMEM_store_msg v C s c r1 M MSG_invalid_stored_block_lengths HM Hput)).
      assert (HM2 : LMEM v (mkW (iset_mode s BAD) c' r1) M2).
      { apply (LMEM_store_scalar v C s c' r1 _ M1 8 _ HM1); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_mode M1 (cv_S v) _ s BAD (lm_sc _ _ _ HM1)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      pose proof (icset_msg_facts c MSG_invalid_stored_block_lengths) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11).
      arm_disp C HM2 Hfr R2 Hms2 G26' Hfr2.
      exists R2, M2, (arm6_pc (is_mode (iset_mode s BAD))). split; [eapply msteps_trans; [| exact Hms2]; subst M2 M1; by_run Hms|].
      cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
      + split; [exact HM2|]. split; [subst M2 M1; retc_tower C HRC|]. split.
        * apply (LX_step0 v s c r1 _ c' r1 HX NH NB); subst c'; try reflexivity; [live_mode_tac | exact Xret | rewrite F11; unfold MSG_invalid_stored_block_lengths; lia | bk_side].
        * symex_reg HR' (23%bv : reg) as Q24. symex_reg HR' (26%bv : reg) as Q25.
          unfold LREG_arm, LVARS; cbn [w_r].
          split; [lfix_close2 Hfr2 Hfr HR'|]. split; [| intros _; exact G26'].
          regs_via2 Hfr2 Hfr; first [exact Q24 | exact Q25 | match goal with |- ?G => idtac "BADREG LEFT" G end].
      + subst M2 M1.
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1) M M); [apply MFRAME_refl | lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
  Qed.

  Lemma land24 : forall b, 0 <= b < 32 -> Z.land b 24 = b - b mod 8.
  Proof.
    intros b Hb.
    assert (H: forall k, 0 <= k < 32 -> Z.land k 24 = k - k mod 8).
    { intros k Hk. assert (k = 0 \/ k = 1 \/ k = 2 \/ k = 3 \/ k = 4 \/ k = 5 \/ k = 6 \/ k = 7 \/ k = 8 \/ k = 9 \/ k = 10 \/ k = 11 \/ k = 12 \/ k = 13 \/ k = 14 \/ k = 15
       \/ k = 16 \/ k = 17 \/ k = 18 \/ k = 19 \/ k = 20 \/ k = 21 \/ k = 22 \/ k = 23 \/ k = 24 \/ k = 25 \/ k = 26 \/ k = 27 \/ k = 28 \/ k = 29 \/ k = 30 \/ k = 31) by lia.
      repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; subst k; reflexivity. }
    apply H. exact Hb.
  Qed.

  Lemma stored_A : forall s c r R M,
    LFIX v R -> LVARS v (mkW s c r) R -> RINV (cv_NI v) (cv_NO v) r ->
    let rb := mkIR (ir_next r) (ir_have r) (ir_put r) (ir_left r) (ir_hold r / 2 ^ (ir_bits r mod 8)) (ir_bits r - ir_bits r mod 8)
                   (ir_in r) (ir_out r) (ir_ret r) in
    exists R1,
      if 32 <=? ir_bits r
      then msteps s6u_segs (mkst R (Z_to_bv 64 0x1f24c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f578) M s6u_rom) /\ JE c rb R1
      else msteps s6u_segs (mkst R (Z_to_bv 64 0x1f24c) M s6u_rom) (mkst R1 (Z_to_bv 64 0x1f274) M s6u_rom) /\ JS (ir_have r) (ir_next r) (ir_bits rb) c rb R1.
  Proof.
    intros s c r R M HF HV RI. cbv zeta.
    open_ictx C. open_fix HF. open_vars HV. open_rinv RI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P27 & P13 & P8 & P11 & P1 & P24 & P9 & P22 & P18 & P25).
    pose proof (land7_mod (ir_bits r)) as E7.
    assert (Hm8 : 0 <= ir_bits r mod 8 < 8) by (apply Z.mod_pos_bound; lia).
    assert (Hml : ir_bits r mod 8 <= ir_bits r) by (apply Z.mod_le; clear - Rbits; lia).
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    - arm_symex ilN 12%nat [true] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f24c) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (25%bv : reg) as G22'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (14%bv : reg) as G14'. symex_reg HR1 (12%bv : reg) as G12'.
      unfold JE; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
      split; [lfix_close Hfr HR1|]. regs_via Hfr.
      + rewrite G22'. change (2 ^ 3) with 8. rewrite zalu_srl_small by (clear - Rhold64 Hm8; lia). reflexivity.
      + exact G14'.
      + exact G12'.
      + rewrite G18'. match goal with |- ?G => idtac "G18" G end. rewrite land_m8 by (clear - Rbits; lia). rewrite E7. reflexivity.
    - arm_symex ilN 14%nat [false] (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals (famA c s)
        (mkst R (Z_to_bv 64 0x1f24c) M s6u_rom) R1 HR1 Hfr Hms.
      all: try arm_side.
      exists R1. split; [by_run Hms|].
      symex_reg HR1 (25%bv : reg) as G22'. symex_reg HR1 (19%bv : reg) as G18'. symex_reg HR1 (12%bv : reg) as G12'. symex_reg HR1 (6%bv : reg) as G6'.
      symex_reg HR1 (16%bv : reg) as G16'. symex_reg HR1 (5%bv : reg) as G5'. symex_reg HR1 (15%bv : reg) as G15'.
      unfold JS; cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
      split; [lfix_close Hfr HR1|]. regs_via Hfr.
      + rewrite G22'. change (2 ^ 3) with 8. rewrite zalu_srl_small by (clear - Rhold64 Hm8; lia). reflexivity.
      + exact G12'.
      + exact G6'.
      + exact G16'.
      + rewrite G5'. rewrite land24 by (clear - Rbits LT; lia). reflexivity.
      + rewrite G18'. rewrite land24 by (clear - Rbits LT; lia). reflexivity.
      + rewrite G15'. rewrite land24 by (clear - Rbits LT; lia). reflexivity.
      + clear; lia.
      + clear; lia.
      + clear - Rhv0; lia.
      + clear - Rhv0 Rnh Rnx0 CI0; lia.
      + clear - Rbits Hml; lia.
      + clear - Rnx0; lia.
  Qed.

  Theorem arm_STORED_sim0 : forall w R M,
    is_mode (w_s w) = STORED -> ENTRY v w R M -> pinv (cv_NI v) (cv_NO v) (cv_WN v) (cv_TOT0 v) w ->
    exists R' M' pc',
      msteps s6u_segs (mkst R (Z_to_bv 64 (arm6_pc STORED)) M s6u_rom) (mkst R' (Z_to_bv 64 pc') M' s6u_rom)
      /\ arm_post v w M (dispatch ivar_ref (cv_flush v) w) R' M' pc'.
  Proof.
    intros w R M Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) STORED) with (arm_STORED ivar_ref (cv_flush v)).
    destruct HE as (HM & HRC & HX & (HF & HV & G26)).
    arm_begin C HM HRC HX HF HV HP.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    assert (Hf6 : cv_flush v <> Z_TREES) by (unfold Z_TREES; clear - Cflush; lia).
    destruct (r_bb_small r Rbits Rhold) as (Ebb & Hhb & Hm8 & Hml).
    set (rb := mkIR (ir_next r) (ir_have r) (ir_put r) (ir_left r) (ir_hold r / 2 ^ (ir_bits r mod 8)) (ir_bits r - ir_bits r mod 8)
                    (ir_in r) (ir_out r) (ir_ret r)) in *.
    assert (RIb : RINV (cv_NI v) (cv_NO v) rb) by (subst rb; unfold RINV in *; cbn; clear - RI Hhb Hm8 Hml; lia).
    assert (HMb : LMEM v (mkW s c rb) M) by (apply (LMEM_regs v s c r c rb M HM); reflexivity).
    assert (HRCb : RETC v (mkW s c rb) M) by (eapply RETC_regs; [exact HRC | reflexivity]).
    assert (HXb : LX v (mkW s c rb)) by (apply (LX_step0 v s c r s c rb HX NH NB); try reflexivity; [exact Xlive | exact Xret | exact Xmsg | bk_side]).
    destruct (stored_A s c r R M HF HV RI) as (R1 & HA).
    change (arm6_pc STORED) with 0x1f24c.
    destruct (Z.leb_spec 32 (ir_bits r)) as [GE|LT].
    -
      destruct HA as (Hms1 & HJE).
      assert (Hb32 : 32 <= ir_bits r - ir_bits r mod 8).
      { pose proof (Z.div_mod (ir_bits r) 8 ltac:(lia)) as E. clear - GE Hm8 E. lia. }
      assert (HN : NEEDBITS 32 (mkW s c (r_bb r)) = ARun tt (mkW s c rb)).
      { rewrite Ebb. unfold NEEDBITS. apply NEEDBITS_k_done. cbn. exact Hb32. }
      rewrite (arm_STORED_run (cv_flush v) s c r s c rb Hf6 HN).
      destruct (stored_B_sim s c rb R1 M Hmode HMb HRCb HXb HJE RIb CI ltac:(subst rb; cbn; exact Hb32)) as (R' & M' & pc' & Hms2 & HPOST).
      exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
      apply (arm_post_rebase v s c r c rb); [reflexivity | exact HPOST].
    -
      destruct HA as (Hms1 & HJS).
      pose proof (need_loop v 32 0x1f274 0x1f578 (JS (ir_have r) (ir_next r) (ir_bits rb)) JE C ltac:(lia)
                    (stored_step_H _ _ _) (stored_step_E _ _ _) (stored_dry _ _ _)
                    8%nat s c rb R1 M HMb HRCb HJS RIb CI ltac:(subst rb; cbn; clear - LT Hm8; lia) ltac:(subst rb; cbn; clear - LT Hm8 Hml; lia)) as NL.
      change (NEEDBITS_k 8 32) with (NEEDBITS 32) in NL.
      destruct (NEEDBITS 32 (mkW s c rb)) as [[] w1 | w1 | rc w1] eqn:HN; [| | destruct NL].
      + destruct NL as (r1 & R2 & -> & Hms2 & HJE & RI1 & S5 & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5). subst rb. cbn in Q1, Q2, Q3, Q4, Q5.
        rewrite <- Ebb in HN. rewrite (arm_STORED_run (cv_flush v) s c r s c r1 Hf6 HN).
        assert (HX1 : LX v (mkW s c r1)) by (apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side]).
        destruct (stored_B_sim s c r1 R2 M Hmode HM1 HRC1 HX1 HJE RI1 CI ltac:(clear - Hb1; lia)) as (R' & M' & pc' & Hms3 & HPOST).
        exists R', M', pc'. split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
        apply (arm_post_rebase v s c r c r1); [symmetry; exact Q1 | exact HPOST].
      + destruct NL as (r1 & R2 & -> & Hms2 & HL1 & RI1 & S5 & Hz & Hb1 & HM1 & HRC1).
        destruct S5 as (Q1 & Q2 & Q3 & Q4 & Q5). subst rb. cbn in Q1, Q2, Q3, Q4, Q5.
        rewrite <- Ebb in HN. rewrite (arm_STORED_leave (cv_flush v) s c r _ HN).
        exists R2, M, pc6_leave. split; [eapply msteps_trans; [exact Hms1 | exact Hms2]|].
        cbn [arm_post w_r]. split; [reflexivity|]. rewrite Q1. split; [| apply MFRAME_refl].
        split; [exact HM1|]. split; [| split; [apply same_blocks_refl | exact HL1]].
        apply (LX_step0 v s c r s c r1 HX NH NB); try reflexivity; [exact Xlive | exact Q3 | rewrite Q5; exact Xret | exact Xmsg | bk_side].
  Qed.
End ArmSTORED.

Section ArmSTORED2.
  Hypothesis MEMCPY : memcpy_run6u.
  Theorem arm_STORED_sim : arm_stmt STORED.
  Proof. intros v w R M C Hmode HE HP. exact (arm_STORED_sim0 v C MEMCPY w R M Hmode HE HP). Qed.
End ArmSTORED2.
End FXG.
