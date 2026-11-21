(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.D6S Require Import Segs6 Callee6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.example_flush_fuzzer_ubsan.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b.
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
  Hypothesis MEMCPY : memcpy_run6.

  Definition CREG (w : iw) (R : bvmap 5 word) : Prop := LFIX v R /\ LVARS v w R.

  Lemma copy_zero : forall s c r R M,
    is_mode s = COPY -> is_length s = 0 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> CREG (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (ARun tt (mkW (iset_mode s TYPE) c r)) R' M' pc'.
  Proof.
    intros s c r R M Hmode HL HM HRC HX (HF & HV) RI CI.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI. open_frame Mfr.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    pose proof (is6_length _ _ _ _ Msc) as C92. rewrite HL in C92.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    arm_symex ilS 30%nat [true; true] [RVal (ELit 0); RVal (ELit 16209); RVal (ELit (JT TYPE))] (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) R' HR' Hfr Hms.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTZ" G end.
    set (M2 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16191)) in Hms.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HM2 : LMEM v (mkW (iset_mode s TYPE) c r) M2).
    { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s TYPE (lm_sc _ _ _ HM)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    exists R', M2, (arm6_pc TYPE). split; [subst M2; by_run Hms|].
    cbn [arm_post]. split; [reflexivity|]. split; [| split; [apply same_blocks_mode |]].
    - split; [exact HM2|]. split.
      { subst M2. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS; cbn; lia].
        eapply RETC_regs; [exact HRC | reflexivity]. }
      split.
      + apply (LX_step0 v s c r _ c r HX NH NB); try reflexivity; [live_mode_tac | exact Xret | exact Xmsg].
      + unfold LREG_arm. split.
        { symex_reg HR' (20%bv : reg) as G19'. unfold LFIX, INF_FRAME, A6_JTAB. regs_via Hfr; try exact G19'. }
        split; [| cbn; unfold TYPE, BAD; intros; exfalso; lia].
        unfold LVARS; cbn [w_r]. regs_via Hfr.
    - subst M2.
      apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r) M M); [apply MFRAME_refl | lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
  Qed.

  Definition MREG (r : iregs) (k : Z) (R : bvmap 5 word) : Prop :=
    getr R 10 = zw (cv_P0 v + ir_put r) /\ getr R 11 = zw (cv_I0 v + ir_next r) /\ getr R 12 = zw k /\ getr R 1 = zw 0x1d52c
    /\ getr R 9 = zw k /\ getr R 20 = zw k /\ getr R 26 = zw (ir_left r)
    /\ getr R 2 = zw (cv_sp v - 224) /\ getr R 8 = zw (cv_S v) /\ getr R 18 = zw (ir_have r) /\ getr R 19 = zw (cv_P0 v + ir_put r)
    /\ getr R 23 = zw (ir_hold r) /\ getr R 24 = zw (ir_bits r) /\ getr R 27 = zw (cv_I0 v + ir_next r)
    /\ getr R 22 = zw (cv_S v + 168) /\ getr R 25 = zw 0x12510
    /\ getr R 3 = getr (cv_R0 v) 3 /\ getr R 4 = getr (cv_R0 v) 4.

  Ltac mreg_close HR Hfr :=
    let G10 := fresh in let G11 := fresh in let G12 := fresh in let G1 := fresh in
    let G8 := fresh in let G19 := fresh in let G27 := fresh in
    symex_reg HR (10%bv : reg) as G10; symex_reg HR (11%bv : reg) as G11; symex_reg HR (12%bv : reg) as G12; symex_reg HR (1%bv : reg) as G1;
    symex_reg HR (9%bv : reg) as G8; symex_reg HR (20%bv : reg) as G19; symex_reg HR (26%bv : reg) as G27;
    unfold MREG; repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite G10; f_equal; lia | rewrite G11; f_equal; lia | rewrite G12; rewrite ?Z.mod_small by lia; f_equal; lia | rewrite G1; reflexivity
          | rewrite G8; rewrite ?Z.mod_small by lia; f_equal; lia | rewrite G19; rewrite ?Z.mod_small by lia; f_equal; lia | rewrite G27; f_equal; lia
          | match goal with |- ?G => idtac "MREG LEFT" G end ].

  Ltac lreg_leave_close HR Hfr :=
    let G8 := fresh in
    symex_reg HR (9%bv : reg) as G8;
    unfold LREG_leave, LVARS, INF_FRAME; cbn [w_r]; repeat match goal with |- _ /\ _ => split end;
    first [ lazymatch goal with |- getr _ ?n = _ => rewrite (Hfr n eq_refl); assumption end
          | rewrite G8; apply zw_neg_mod
          | match goal with |- ?G => idtac "LREG LEFT" G end ].

  Lemma copy_pre : forall s c r R M,
    0 < is_length s <= 65535 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> CREG (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    exists R1,
      if cmin s r =? 0
      then msteps s6_segs (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) (mkst R1 (Z_to_bv 64 pc6_leave) M s6_rom) /\ LREG_leave v (mkW s c r) R1
      else msteps s6_segs (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) (mkst R1 (Z_to_bv 64 A6_MEMCPY) M s6_rom) /\ MREG r (cmin s r) R1.
  Proof.
    intros s c r R M HL HM HRC (HF & HV) RI CI.
    open_ictx C. open_lmem HM. open_retc HRC. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    pose proof (is6_length _ _ _ _ Msc) as C92.
    pose proof (cmin_range s r Rhv0 Rlf0 (proj1 HL)) as (K1 & K2 & K3 & K4).
    destruct (Z_lt_le_dec (is_length s) (ir_have r)) as [A|B];
      [destruct (Z_lt_le_dec (is_length s) (ir_left r)) as [A1|A2]; [| destruct (Z.eq_dec (ir_left r) 0) as [Z0|Z0]]
      |destruct (Z_le_gt_dec (ir_left r) (ir_have r)) as [B1|B2]; [destruct (Z.eq_dec (ir_left r) 0) as [Z0|Z0] | destruct (Z.eq_dec (ir_have r) 0) as [Z0|Z0]]].
    -
      assert (EK : cmin s r = is_length s) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [lia|]; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
      rewrite EK. replace (is_length s =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 20%nat [false; true; true; true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 65536)] v r
        [is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP1" G end.
      exists R'. split; [by_run Hms|]. mreg_close HR' Hfr.
    -
      assert (EK : cmin s r = 0) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [lia|]; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
      rewrite EK. cbn [Z.eqb].
      arm_symex ilS 20%nat [false; true; false; false] [RVal (EVar 45%nat); RVal (EVar 46%nat)] (@nil (Z * expr)) [(45%nat, 65536); (46%nat, 2 ^ 64)] v r
        [is_length s; ir_ret r mod 2 ^ 64] NoVals F0 (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP2" G end.
      exists R'. split; [by_run Hms|]. lreg_leave_close HR' Hfr.
    -
      assert (EK : cmin s r = ir_left r) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [lia|]; destruct (Z.ltb_spec (ir_left r) (is_length s)); lia).
      rewrite EK. replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 20%nat [false; true; false; true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 65536)] v r
        [is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP3" G end.
      exists R'. split; [by_run Hms|]. mreg_close HR' Hfr.
    -
      assert (EK : cmin s r = 0) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)); lia | destruct (Z.ltb_spec (ir_left r) (is_length s)); lia]).
      rewrite EK. cbn [Z.eqb].
      arm_symex ilS 20%nat [false; false; true; false] [RVal (EVar 45%nat); RVal (EVar 46%nat)] (@nil (Z * expr)) [(45%nat, 65536); (46%nat, 2 ^ 64)] v r
        [is_length s; ir_ret r mod 2 ^ 64] NoVals F0 (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP4" G end.
      exists R'. split; [by_run Hms|]. lreg_leave_close HR' Hfr.
    -
      assert (EK : cmin s r = ir_left r) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)); lia | destruct (Z.ltb_spec (ir_left r) (is_length s)); lia]).
      rewrite EK. replace (ir_left r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 20%nat [false; false; true; true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 65536)] v r
        [is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP5" G end.
      exists R'. split; [by_run Hms|]. mreg_close HR' Hfr.
    -
      assert (EK : cmin s r = 0) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)); lia | destruct (Z.ltb_spec (ir_left r) (is_length s)); lia]).
      rewrite EK. cbn [Z.eqb].
      arm_symex ilS 20%nat [false; false; false; false] [RVal (EVar 45%nat); RVal (EVar 46%nat)] (@nil (Z * expr)) [(45%nat, 65536); (46%nat, 2 ^ 64)] v r
        [is_length s; ir_ret r mod 2 ^ 64] NoVals F0 (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP6" G end.
      exists R'. split; [by_run Hms|]. lreg_leave_close HR' Hfr.
    -
      assert (EK : cmin s r = ir_have r) by (unfold cmin; destruct (Z.ltb_spec (ir_have r) (is_length s)); [destruct (Z.ltb_spec (ir_left r) (ir_have r)); lia | destruct (Z.ltb_spec (ir_left r) (is_length s)); lia]).
      rewrite EK. replace (ir_have r =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      arm_symex ilS 20%nat [false; false; false; true] [RVal (EVar 45%nat)] (@nil (Z * expr)) [(45%nat, 65536)] v r
        [is_length s] NoVals F0 (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) R' HR' Hfr Hms.
      all: try arm_side.
      all: match goal with |- ?G => idtac "LEFTP7" G end.
      exists R'. split; [by_run Hms|]. mreg_close HR' Hfr.
  Qed.

  Lemma copy_call : forall s c r R1 M1 k,
    LMEM v (mkW s c r) M1 -> MREG r k R1 -> RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    0 < k -> k <= ir_have r -> k <= ir_left r ->
    let M2 := wbytes M1 (zw (cv_P0 v + ir_put r)) (cbytes (arr_get (ic_input c)) (ir_next r) (Z.to_nat k)) in
    exists R2,
      msteps s6_segs (mkst R1 (Z_to_bv 64 A6_MEMCPY) M1 s6_rom) (mkst R2 (Z_to_bv 64 0x1d52c) M2 s6_rom)
      /\ (forall rg, reg_in rg memcpy_clob = false -> getr R2 rg = getr R1 rg)
      /\ LMEM v (mkW s (copy_c c r k) (copy_r r k)) M2.
  Proof.
    intros s c r R1 M1 k HM1 HJ RI CI Hk Hkh Hkl. cbv zeta.
    destruct HJ as (G10 & G11 & G12 & G1 & _).
    open_ictx C. open_lmem HM1. open_rinv RI. open_cinv CI. unfold mapped in *.
    assert (HNI : 0 < cv_NI v) by (clear - Hk Hkh Rnx0 Rnh; lia). assert (HNO : 0 < cv_NO v) by (clear - Hk Hkl Rpt0 Rpl; lia).
    assert (Hn : Z.of_nat (Z.to_nat k) = k) by (apply Z2Nat.id; lia).
    pose proof (cells_rdn_bytes s6_segs M1 (cv_I0 v) (cv_NI v) (arr_get (ic_input c)) (ir_next r) (Z.to_nat k) Minp
                  ltac:(lia) ltac:(rewrite Hn; clear - Hkh Rnh; lia) ltac:(lia) ltac:(lia)) as Hsrc.
    destruct (MEMCPY _ R1 (cv_P0 v + ir_put r) (cv_I0 v + ir_next r) (Z.to_nat k) _ (zw 0x1d52c) Hsrc
               ltac:(clear - CP0 Rpt0; lia) ltac:(rewrite Hn; clear - CP0 Rpt0 Rpl Hkl; lia) ltac:(clear - CI0 Rnx0; lia) ltac:(rewrite Hn; clear - CI0 Rnx0 Rnh Hkh; lia))
      as (R2 & Hms & _ & Hfr).
    - rewrite Hn. unfold sep in CIP. clear - CIP Hkh Hkl Rnx0 Rnh Rpt0 Rpl CI0 CP0 Hk. lia.
    - rewrite Hn. intros x Hx. apply Mmap_P. clear - Hx Hkl Rpt0 Rpl Hk. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - exact G1.
    - exact G10.
    - exact G11.
    - change (reg_get R1 12) with (getr R1 12). rewrite G12. f_equal. lia.
    - exists R2. split; [change (Z_to_bv 64 A6_MEMCPY) with (zw A6_MEMCPY); exact Hms|]. split; [exact Hfr|].
      unfold copy_c. rewrite <- Hn at 1.
      apply (LMEM_blit_out v C s c r (copy_r r k) (Z.to_nat k) M1 HM1); rewrite ?Hn; try lia; first [exact Col | exact Cinb | cbn; lia].
  Qed.

  Definition post_pins : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (18, EVar 36%nat); (19, EAdd (EVar 37%nat) (EVar 38%nat)); (23, EVar 40%nat); (24, EVar 41%nat);
     (27, EAdd (EVar 43%nat) (EVar 44%nat)); (9, EVar 45%nat); (20, EVar 45%nat); (26, EVar 39%nat);
     (22, EAdd (EVar 33%nat) (ELit 168)); (25, ELit 0x12510)].

  Ltac jt_far Hrod :=
    lazymatch goal with
    | |- exists bs, rdn s6_segs _ (zw ?a) 4 = Some bs /\ _ =>
        rewrite <- (zw_neg_mod a); let a' := eval vm_compute in (a mod 2 ^ 64) in change (a mod 2 ^ 64) with a'; jt_read_close Hrod
    end.

  Definition ilD : cfg := CFG [] [] arm_rets (pc6_disp :: arm_stops) [].

  Lemma copy_r_small : forall r k, 0 <= k <= ir_have r -> k <= ir_left r -> ir_have r < 2 ^ 32 -> ir_left r < 2 ^ 32 ->
    copy_r r k = mkIR (ir_next r + k) (ir_have r - k) (ir_put r + k) (ir_left r - k) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r).
  Proof.
    intros r k Hk Hkl Hh Hl. unfold copy_r. destruct r; cbn in *. rewrite !wrap32_id by lia. reflexivity.
  Qed.
  Lemma copy_s_small : forall s k, 0 <= k <= is_length s -> is_length s < 2 ^ 32 -> copy_s s k = iset_length s (is_length s - k).
  Proof. intros s k Hk HL. unfold copy_s. rewrite wrap32_id by lia. reflexivity. Qed.

  Lemma copy_post : forall s c r R2 M k,
    is_mode s = COPY -> 0 < k -> k <= ir_have r -> k <= ir_left r -> k <= is_length s <= 65535 ->
    LMEM v (mkW s c (copy_r r k)) M ->
    RINV (cv_NI v) (cv_NO v) r ->
    getr R2 9 = zw k -> getr R2 20 = zw k -> getr R2 26 = zw (ir_left r) ->
    getr R2 2 = zw (cv_sp v - 224) -> getr R2 8 = zw (cv_S v) -> getr R2 18 = zw (ir_have r) -> getr R2 19 = zw (cv_P0 v + ir_put r) ->
    getr R2 23 = zw (ir_hold r) -> getr R2 24 = zw (ir_bits r) -> getr R2 27 = zw (cv_I0 v + ir_next r) ->
    getr R2 22 = zw (cv_S v + 168) -> getr R2 25 = zw 0x12510 ->
    getr R2 3 = getr (cv_R0 v) 3 -> getr R2 4 = getr (cv_R0 v) 4 ->
    let M3 := wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - k)) in
    exists R',
      msteps s6_segs (mkst R2 (Z_to_bv 64 0x1d52c) M s6_rom) (mkst R' (Z_to_bv 64 0x1d4e4) M3 s6_rom)
      /\ LFIX v R' /\ LVARS v (mkW s c (copy_r r k)) R' /\ getr R' 9 = zw (-3)
      /\ LMEM v (mkW (copy_s s k) c (copy_r r k)) M3.
  Proof.
    intros s c r R2 M k Hmode Hk Hkh Hkl HkL HM RI G8 G19 G27 G2 G25 G9 G18 G22 G23 G26 G21 G24 G3 G4. cbv zeta.
    open_ictx C. open_lmem HM. open_frame Mfr. open_rinv RI. unfold mapped in *.
    assert (Hh32 : ir_have r < 2 ^ 32) by (clear - Rnh Rnx0 CI0; lia). assert (Hl32 : ir_left r < 2 ^ 32) by (clear - Rpl Rpt0 CP0; lia).
    rewrite (copy_r_small r k) in * by lia. rewrite (copy_s_small s k) by lia.
    cbn [ir_put ir_out] in *.
    pose proof (is6_length _ _ _ _ Msc) as C92. pose proof (is6_mode _ _ _ _ Msc) as C8. rewrite Hmode in C8.
    (* 1.4: after memcpy the arm reloads flush (sp + 104) before strm (sp + 96) *)
    arm_symexP (@nil (Z * expr)) ilD 20%nat (@nil bool)
      [RVal (EVar 35%nat); RVal (EVar 34%nat); RVal (EVar 46%nat); RVal (ELit 16209); RVal (ELit 18446744073709535436)]
      post_pins [(45%nat, 65536); (46%nat, 65536)] v r
      [k; is_length s] NoVals F0
      (mkst R2 (Z_to_bv 64 0x1d52c) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    all: match goal with |- ?G => idtac "LEFTQ1" G end.
    rewrite le4_szwrap in Hms1.
    set (M3 := wbytes M (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - k))) in *.
    assert (Hput : 0 <= ir_put r + k <= cv_NO v) by (clear - Rpt0 Rpl Rlf0 Hkl Hk; lia).
    assert (HM3 : LMEM v (mkW (iset_length s (is_length s - k)) c
                            (mkIR (ir_next r + k) (ir_have r - k) (ir_put r + k) (ir_left r - k) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r))) M3).
    { apply (LMEM_store_scalar v C s c _ _ M 108 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_length M (cv_S v) _ s _ Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    pose proof (lm_rod _ _ _ HM3) as Mrod3. pose proof (is6_mode _ _ _ _ (lm_sc _ _ _ HM3)) as C8'. cbn [w_s] in C8'.
    replace (is_mode (iset_length s _)) with COPY in C8' by (rewrite <- Hmode; destruct s; reflexivity).
    symex_reg HR1 (1%bv : reg) as Q1. symex_reg HR1 (10%bv : reg) as Q10. symex_reg HR1 (11%bv : reg) as Q11.
    symex_reg HR1 (19%bv : reg) as Q18. symex_reg HR1 (20%bv : reg) as Q19. symex_reg HR1 (18%bv : reg) as Q9. symex_reg HR1 (26%bv : reg) as Q27.
    symex_reg HR1 (29%bv : reg) as Q29. symex_reg HR1 (31%bv : reg) as Q31.
    rewrite szwrap32_small in Q1 by (clear - Hkl Hk Rpl Rpt0 CP0; lia). rewrite szwrap32_small in Q9 by (clear - Hkh Hk Rnh Rnx0 CI0; lia).
    change 18446744073709535436 with ((-16180) mod 2 ^ 64) in Q31. rewrite zw_neg_mod in Q31.
    assert (Q2 : getr R1 2 = zw (cv_sp v - 224)) by (rewrite (Hfr1 (2%bv : reg) eq_refl); exact G2).
    assert (Q25 : getr R1 8 = zw (cv_S v)) by (rewrite (Hfr1 (8%bv : reg) eq_refl); exact G25).
    assert (Q22 : getr R1 23 = zw (ir_hold r)) by (rewrite (Hfr1 (23%bv : reg) eq_refl); exact G22).
    assert (Q23 : getr R1 24 = zw (ir_bits r)) by (rewrite (Hfr1 (24%bv : reg) eq_refl); exact G23).
    assert (Q21 : getr R1 22 = zw (cv_S v + 168)) by (rewrite (Hfr1 (22%bv : reg) eq_refl); exact G21).
    assert (Q24 : getr R1 25 = zw 0x12510) by (rewrite (Hfr1 (25%bv : reg) eq_refl); exact G24).
    assert (Q3 : getr R1 3 = getr (cv_R0 v) 3) by (rewrite (Hfr1 (3%bv : reg) eq_refl); exact G3).
    assert (Q4 : getr R1 4 = getr (cv_R0 v) 4) by (rewrite (Hfr1 (4%bv : reg) eq_refl); exact G4).
    assert (Q18' : getr R1 19 = zw (cv_P0 v + (ir_put r + k))) by (rewrite Q18; f_equal; lia).
    assert (Q27' : getr R1 26 = zw (cv_I0 v + (ir_next r + k))) by (rewrite Q27; f_equal; lia).
    clear Hfr1 HR1.
    j11_symex ilS 12%nat [true] [RVal (ELit 16195); RVal (ELit (JT COPY))] (@nil (Z * expr)) (@nil (nat * Z)) v
      (mkIR (ir_next r + k) (ir_have r - k) (ir_put r + k) (ir_left r - k) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r))
      (@nil Z) NoVals F0
      (mkst R1 (Z_to_bv 64 pc6_disp) M3 s6_rom) R' HR' Hfr Hms.
    all: cbn [ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret]; try arm_side.
    all: match goal with |- ?G => idtac "LEFTQ2" G end.
    exists R'. split; [eapply msteps_trans; [by_run Hms1 | subst M3; by_run Hms]|].
    split; [| split; [| split; [| exact HM3]]].
    - unfold LFIX, INF_FRAME, A6_JTAB. regs_via Hfr.
    - unfold LVARS; cbn [w_r ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next].
      symex_reg HR' (27%bv : reg) as G26'. regs_via Hfr. exact G26'.
    - symex_reg HR' (9%bv : reg) as G8'. exact G8'.
  Qed.

  Lemma copy_core : forall s c r R M,
    is_mode s = COPY -> 0 <= is_length s <= 65535 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> CREG (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d4e4) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
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
      destruct HJ1 as (_ & _ & _ & _ & J8 & J19 & J27 & J2 & J25 & J9 & J18 & J22 & J23 & J26 & J21 & J24 & J3 & J4).
      destruct (copy_post s (copy_c c r k) r R2 M2 k Hmode ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) HM2 RI
                  ltac:(rewrite (Hfr2 (9%bv : reg) eq_refl); exact J8) ltac:(rewrite (Hfr2 (20%bv : reg) eq_refl); exact J19)
                  ltac:(rewrite (Hfr2 (26%bv : reg) eq_refl); exact J27)
                  ltac:(rewrite (Hfr2 (2%bv : reg) eq_refl); exact J2) ltac:(rewrite (Hfr2 (8%bv : reg) eq_refl); exact J25)
                  ltac:(rewrite (Hfr2 (18%bv : reg) eq_refl); exact J9) ltac:(rewrite (Hfr2 (19%bv : reg) eq_refl); exact J18)
                  ltac:(rewrite (Hfr2 (23%bv : reg) eq_refl); exact J22) ltac:(rewrite (Hfr2 (24%bv : reg) eq_refl); exact J23)
                  ltac:(rewrite (Hfr2 (27%bv : reg) eq_refl); exact J26)
                  ltac:(rewrite (Hfr2 (22%bv : reg) eq_refl); exact J21) ltac:(rewrite (Hfr2 (25%bv : reg) eq_refl); exact J24)
                  ltac:(rewrite (Hfr2 (3%bv : reg) eq_refl); exact J3)
                  ltac:(rewrite (Hfr2 (4%bv : reg) eq_refl); exact J4))
        as (R' & Hms3 & HF' & HV' & G8' & HM3).
      set (M3 := wbytes M2 (zw (cv_S v + 108)) (Z_to_le_bytes 4 (is_length s - k))) in *.
      exists R', M3, 0x1d4e4.
      split; [eapply msteps_trans; [exact Hms1|]; eapply msteps_trans; [exact Hms2 | exact Hms3]|].
      assert (Ers : copy_r r k = mkIR (ir_next r + k) (ir_have r - k) (ir_put r + k) (ir_left r - k) (ir_hold r) (ir_bits r) (ir_in r) (ir_out r) (ir_ret r))
        by (apply copy_r_small; clear - K1 K2 Rnh Rnx0 CI0 Rpl Rpt0 CP0; lia).
      assert (Ess : copy_s s k = iset_length s (is_length s - k)) by (apply copy_s_small; lia).
      pose proof (icset_outbuf_facts c (arr_blit (ic_outbuf c) (ir_put r) (ic_input c) (ir_next r) k)) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
      cbn [arm_post w_s w_r]. split; [rewrite Ess; replace (is_mode (iset_length s (is_length s - k))) with (is_mode s) by (destruct s; reflexivity); rewrite Hmode; reflexivity|].
      split; [| split].
      + split; [exact HM3|].
        split.
        { subst M3 M2. apply (RETC_other v C); [| clear - CS; lia | clear - CS; cbn; lia | unfold sep in CfS; clear - CfS; cbn; lia].
          apply (RETC_other v C); [| clear - CP0 Rpt0; lia | rewrite cbytes_length, Hn; clear - CP0 Rpt0 Rpl K2; lia
            | rewrite cbytes_length, Hn; specialize (CfP ltac:(clear - K2 Kz K1 Rpl Rpt0; lia)); unfold sep in CfP; clear - CfP Rpt0 Rpl K1 K2 Kz; lia].
          eapply RETC_regs; [exact HRC | rewrite Ers; reflexivity]. }
        split.
        { rewrite Ess, Ers. unfold copy_c. apply (LX_step0 v s c r _ _ _ HX NH NB); try reflexivity.
          - replace (is_mode (iset_length s _)) with (is_mode s) by (destruct s; reflexivity). exact Xlive.
          - exact Xret.
          - rewrite E11. exact Xmsg. }
        split; [exact HF'|]. split; [exact HV'|]. intros _; exact G8'.
      + rewrite Ess. apply same_blocks_length.
      + cbn [w_r]. rewrite Ers. cbn [ir_put]. subst M3 M2.
        apply (MFRAME_store v (ir_put r) (ir_put r + k) (ir_put r + k)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply (MFRAME_store v (ir_put r) (ir_put r) (ir_put r + k) M M); [apply MFRAME_refl | lia | clear - CP0 Rpt0; lia | rewrite cbytes_length, Hn; clear - CP0 Rpt0 Rpl K2; lia | right; right; right; rewrite cbytes_length, Hn; clear - K1; lia].
  Qed.

End ArmCOPY.

Section ArmCOPY2.
  Hypothesis MEMCPY : memcpy_run6.

  Lemma sinv_copy_length : forall s, sinv s -> (is_mode s = COPY_ \/ is_mode s = COPY) -> 0 <= is_length s <= 65535.
  Proof. intros s HS Hm. destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H & _). exact (H Hm). Qed.

  Theorem arm_COPY_sim : arm_stmt COPY.
  Proof.
    intros v w R M C Hmode HE HP. destruct w as [s c r]. cbn [w_s] in Hmode.
    rewrite dispatch_eq. cbn [w_s]. rewrite Hmode. change (arm_for ivar_ref (cv_flush v) COPY) with arm_COPY.
    destruct HE as (HM & HRC & HX & (HF & HV & G8)). open_pinv HP.
    exact (copy_core v C MEMCPY s c r R M Hmode (sinv_copy_length s PS (or_intror Hmode)) HM HRC HX (conj HF HV) RI CI).
  Qed.

  Lemma copy__core : forall v s c r R M,
    ictx v -> is_mode s = COPY_ -> 0 <= is_length s <= 65535 ->
    LMEM v (mkW s c r) M -> RETC v (mkW s c r) M -> LX v (mkW s c r) -> CREG v (mkW s c r) R ->
    RINV (cv_NI v) (cv_NO v) r -> CINV (cv_NI v) (cv_NO v) c ->
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1d4dc) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r) M (arm_COPY (mkW (iset_mode s COPY) c r)) R' M' pc'.
  Proof.
    intros v s c r R M C Hmode HL HM HRC HX (HF & HV) RI CI.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_fix HF. open_vars HV. open_rinv RI. open_cinv CI.
    pose proof (pins_of_regs _ _ _ _ _ HF HV) as (P2 & P25 & P10 & P11 & P21 & P31 & P29 & P24 & P19 & P9 & P18 & P1 & P22 & P23 & P26).
    unfold mapped in *.
    assert (NH : is_mode s <> HEAD) by (rewrite Hmode; cbv; discriminate).
    assert (NB : is_mode s <> BAD) by (rewrite Hmode; cbv; discriminate).
    arm_symex ilS 4%nat (@nil bool) (@nil (option expr)) (@nil (Z * expr)) (@nil (nat * Z)) v r (@nil Z) NoVals F0
      (mkst R (Z_to_bv 64 0x1d4dc) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try arm_side.
    set (M1 := wbytes M (zw (cv_S v + 8)) (Z_to_le_bytes 4 16195)) in *.
    assert (Hput : 0 <= ir_put r <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    assert (HM1 : LMEM v (mkW (iset_mode s COPY) c r) M1).
    { apply (LMEM_store_scalar v C s c r _ M 8 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode M (cv_S v) _ s COPY Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HRC1 : RETC v (mkW (iset_mode s COPY) c r) M1) by (subst M1; retc_tower C HRC).
    assert (HX1 : LX v (mkW (iset_mode s COPY) c r)).
    { apply (LX_step0 v s c r _ c r HX NH NB); try reflexivity; [live_mode_tac | exact Xret | exact Xmsg]. }
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
    destruct HE as (HM & HRC & HX & (HF & HV & G8)). open_pinv HP.
    exact (copy__core v s c r R M C Hmode (sinv_copy_length s PS (or_introl Hmode)) HM HRC HX (conj HF HV) RI CI).
  Qed.
End ArmCOPY2.
End FXG.
