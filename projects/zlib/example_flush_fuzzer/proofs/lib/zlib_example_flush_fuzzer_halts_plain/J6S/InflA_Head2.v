(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate
     InflateInv InflateInvKit InflateInvRun.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.D6S Require Import Segs6.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.J6S Require Import ISLayout IS6 InflMem InflRod6 InflCtx6 InflArmLib6 InflArmLib6b InflNeed6 InflA_Head1.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.

End FXG.
Ltac wrap_brc Hw :=
  lazymatch goal with
  | |- _ mod _ <> _ => clear - Hw; destruct Hw as [-> | ->]; cbv; discriminate
  | |- _ <> _ mod _ => clear - Hw; destruct Hw as [-> | ->]; cbv; discriminate
  | |- _ mod _ = _ => clear - Hw; destruct Hw as [-> | ->]; reflexivity
  | |- _ / _ = _ => clear - Hw; destruct Hw as [-> | ->]; reflexivity
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_plain.PropExec.FPState}.


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

Section HeadBody.
  Variable v : icv.
  Hypothesis C : ictx v.

  Ltac open_hje HJ :=
    let X := fresh in pose proof HJ as X; unfold HJE, LVR in X;
    destruct X as (HF & (G9 & G18 & G1 & G22 & G23) & G12 & G26 & G27); open_fix HF.

  Definition ilD : cfg := CFG [] [] arm_rets (pc6_disp :: arm_stops) [].
  Definition ilAd : cfg := CFG [] [] [EVar 32%nat] [] [].

  Lemma adler_null6 : forall R M (ra : Z),
    getr R 11 = zw 0 -> getr R 12 = zw 0 -> getr R 1 = zw ra -> 0 <= ra < 2 ^ 64 -> ra mod 2 = 0 ->
    exists R', msteps s6_segs (mkst R (Z_to_bv 64 0x1a3d4) M s6_rom) (mkst R' (Z_to_bv 64 ra) M s6_rom)
      /\ getr R' 10 = zw 1 /\ (forall rg, reg_in rg [10; 13; 14]%bv = false -> getr R' rg = getr R rg).
  Proof.
    intros R M ra G11 G12 G21 Hra Hra2.
    symex s6_segs ilAd 12%nat [true; true] (@nil (option expr))
      [(11, ELit 0); (12, ELit 0); (1, EVar 32%nat)] [(32%nat, 2 ^ 64)] NoRegions [ra] NoVals F0 F0'
      (mkst R (Z_to_bv 64 0x1a3d4) M s6_rom) R' HR' Hfr Hms.
    all: try arm_side.
    { rewrite land_m2_even by exact Hra2. reflexivity. }
    exists R'. split; [by_run Hms|]. symex_reg HR' (10%bv : reg) as G10'. split; [exact G10' | exact Hfr].
  Qed.

  Ltac reload_regs HR Q1 Q10 Q11 Q29 Q30 Q31 :=
    symex_reg HR (1%bv : reg) as Q1; symex_reg HR (10%bv : reg) as Q10; symex_reg HR (11%bv : reg) as Q11;
    symex_reg HR (29%bv : reg) as Q29; symex_reg HR (25%bv : reg) as Q30; symex_reg HR (31%bv : reg) as Q31;
    change 75024 with A6_JTAB in Q30;
    change 18446744073709535436 with ((-16180) mod 2 ^ 64) in Q31; rewrite zw_neg_mod in Q31.

  Ltac regs_via2 Hfr Hfr1 :=
    repeat match goal with |- _ /\ _ => split end;
    first [ assumption
          | lazymatch goal with |- getr _ ?n = _ =>
              rewrite (Hfr n eq_refl); first [assumption | rewrite (Hfr1 n eq_refl); assumption] end
          | match goal with |- ?G => idtac "REGS2 LEFT" G end ].

  Definition pinsB : list (Z * expr) :=
    [(2, EVar 32%nat); (8, EVar 33%nat); (20, ELit 16209); (18, EVar 36%nat); (19, EAdd (EVar 37%nat) (EVar 38%nat)); (9, EVar 39%nat);
     (23, EVar 40%nat); (24, EVar 41%nat); (27, EAdd (EVar 43%nat) (EVar 44%nat)); (26, EAdd (EVar 43%nat) (EVar 44%nat)); (10, ELit 1);
     (22, EAdd (EVar 33%nat) (ELit 168)); (25, ELit 0x12510)].

  Lemma head_ok : forall s c r1 R M,
    is_mode s = HEAD -> (is_wrap s = 5 \/ is_wrap s = 1) -> is_wbits s = 15 -> is_head s = 0 ->
    LMEM v (mkW s c r1) M -> RETC v (mkW s c r1) M -> LX v (mkW s c r1) -> HJE v (is_wrap s) c r1 R ->
    RINV (cv_NI v) (cv_NO v) r1 -> CINV (cv_NI v) (cv_NO v) c -> 16 <= ir_bits r1 ->
    (((ir_hold r1 * 2 ^ 56) mod 2 ^ 64 / 2 ^ 48 + ir_hold r1 / 2 ^ 8) * -38083600668303590433) mod 2 ^ 64 < 595056260442243601 ->
    ir_hold r1 mod 2 ^ 4 = 8 -> ~ 15 < (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 + 8 ->
    let len := (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 + 8 in
    let r2 := irset_bits (irset_hold r1 (ir_hold r1 / 2 ^ 4)) (ir_bits r1 - 4) in
    exists R' M' pc',
      msteps s6_segs (mkst R (Z_to_bv 64 0x1da84) M s6_rom) (mkst R' (Z_to_bv 64 pc') M' s6_rom)
      /\ arm_post v (mkW s c r1) M
           (ARun tt (mkW (iset_mode (iset_check (iset_flags (iset_dmax s (2 ^ len)) 0) 1) (if negb (Z.land (ir_hold r1 / 2 ^ 4) 512 =? 0) then DICTID else TYPE))
                         (icset_adler c 1) (irset_bits (irset_hold r2 0) 0))) R' M' pc'.
  Proof.
    intros s c r1 R M Hmode Hw Hwb Hhd HM HRC HX HJ RI CI Hb16 DV M8 BW len r2. open_hje HJ.
    open_ictx C. open_lmem HM. open_retc HRC. open_lx HX. open_rinv RI. open_cinv CI. open_frame Mfr. unfold mapped in *.
    assert (Hput : 0 <= ir_put r1 <= cv_NO v) by (clear - Rpt0 Rpl Rlf0; lia).
    pose proof (is6_head _ _ _ _ Msc) as C48. rewrite Hhd in C48.
    pose proof (is6_wbits _ _ _ _ Msc) as C56. rewrite Hwb in C56.
    pose proof (mod31_cell M Mrod : cell s6_segs M (0 + 67208) 8 595056260442243601) as Crod.
    unfold head_B. cbn [w_s w_c w_r].
    assert (Hhx : 0 <= hx (ir_hold r1) < 2 ^ 57).
    { unfold hx. pose proof (Z.mod_pos_bound (ir_hold r1) (2 ^ 8) ltac:(lia)).
      assert (0 <= ir_hold r1 / 2 ^ 8 < 2 ^ 56) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia. }
    assert (Hq4 : 0 <= ir_hold r1 / 2 ^ 4 < 2 ^ 60) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    assert (Hm4 : 0 <= (ir_hold r1 / 2 ^ 4) mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
    assert (Hm4' : 0 <= ir_hold r1 mod 2 ^ 4 < 16) by (apply Z.mod_pos_bound; lia).
    assert (XflagsB : forall rr, is_flags s = 0 \/ is_flags s = -1 /\ (BAD = HEAD \/ BAD = BAD) /\ ir_out rr = ir_left rr -> True) by (intros; exact I).
    assert (BW' : ~ 7 < (ir_hold r1 / 2 ^ 4) mod 2 ^ 4) by (clear - BW; lia).
    pose proof (wrap15_range _ Hw) as Hwr. pose proof (wrap15_and2 _ Hw) as Hw2. pose proof (wrap15_and1 _ Hw) as Hw1.
    (* 1.4 order (smodel14-r1's HEAD row): len > 15, then wbits == 0, then wbits >= len, then the wbits store test *)
    arm_symexP j1011_pins ilS 60%nat [true; true; false; true; false; false; false; true; true]
      [RVal (ELit 0); RVal (ELit 595056260442243601); RVal (ELit 15)]
      [(12, EVar 45%nat)] [(45%nat, 8)] v r1 [is_wrap s] NoVals (famA c s)
      (mkst R (Z_to_bv 64 0x1da84) M s6_rom) R1 HR1 Hfr1 Hms1.
    all: try wrap_brc Hw.
    all: try arm_side.
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
    symex_reg HR1 (11%bv : reg) as A11. symex_reg HR1 (12%bv : reg) as A12. symex_reg HR1 (1%bv : reg) as A1. symex_reg HR1 (9%bv : reg) as A8.
    destruct (adler_null6 R1 MA 125408 A11 A12 A1 ltac:(lia) ltac:(reflexivity)) as (R2 & Hms2 & B10 & Hfr2).
    pose proof HMA as HMA'. clear Mrod Msc Mlens Mwork Mcodes Mwin Minp Mout Mzs Mfr Moutc Mmap_f Mmap_Z Mmap_S Mmap_P Mmap_W.
    clear Fsv F104 F96 F88 F72 F56 F48 F40 F32 F24 F16 F8 Fd0.
    open_lmem HMA'. open_frame Mfr. unfold mapped in *.
    assert (B2 : getr R2 2 = zw (cv_sp v - 224)) by (rewrite (Hfr2 (2%bv : reg) eq_refl), (Hfr1 (2%bv : reg) eq_refl); exact G2).
    assert (B25 : getr R2 8 = zw (cv_S v)) by (rewrite (Hfr2 (8%bv : reg) eq_refl), (Hfr1 (8%bv : reg) eq_refl); exact G25).
    assert (B21 : getr R2 20 = zw 16209) by (rewrite (Hfr2 (20%bv : reg) eq_refl), (Hfr1 (20%bv : reg) eq_refl); exact G19).
    assert (B24 : getr R2 18 = zw (ir_have r1)) by (rewrite (Hfr2 (18%bv : reg) eq_refl), (Hfr1 (18%bv : reg) eq_refl); exact G9).
    assert (B19 : getr R2 19 = zw (cv_P0 v + ir_put r1)) by (rewrite (Hfr2 (19%bv : reg) eq_refl), (Hfr1 (19%bv : reg) eq_refl); exact G18).
    assert (B18 : getr R2 9 = zw (ir_left r1)) by (rewrite (Hfr2 (9%bv : reg) eq_refl); exact A8).
    assert (Blens : getr R2 22 = zw (cv_S v + 168)) by (rewrite (Hfr2 (22%bv : reg) eq_refl), (Hfr1 (22%bv : reg) eq_refl); exact G21).
    assert (Bjt : getr R2 25 = zw A6_JTAB) by (rewrite (Hfr2 (25%bv : reg) eq_refl), (Hfr1 (25%bv : reg) eq_refl); exact G24).
    assert (B23 : getr R2 23 = zw (ir_hold r1)) by (rewrite (Hfr2 (23%bv : reg) eq_refl), (Hfr1 (23%bv : reg) eq_refl); exact G22).
    assert (B8 : getr R2 24 = zw (ir_bits r1)) by (rewrite (Hfr2 (24%bv : reg) eq_refl), (Hfr1 (24%bv : reg) eq_refl); exact G23).
    assert (B26 : getr R2 27 = zw (cv_I0 v + ir_next r1)) by (rewrite (Hfr2 (27%bv : reg) eq_refl), (Hfr1 (27%bv : reg) eq_refl); exact G26).
    assert (B27 : getr R2 26 = zw (cv_I0 v + ir_next r1)) by (rewrite (Hfr2 (26%bv : reg) eq_refl), (Hfr1 (26%bv : reg) eq_refl); exact G27).
    assert (B3 : getr R2 3 = getr (cv_R0 v) 3) by (rewrite (Hfr2 (3%bv : reg) eq_refl), (Hfr1 (3%bv : reg) eq_refl); exact G3).
    assert (B4 : getr R2 4 = getr (cv_R0 v) 4) by (rewrite (Hfr2 (4%bv : reg) eq_refl), (Hfr1 (4%bv : reg) eq_refl); exact G4).
    clear HR1.
    rewrite bit13_exec by exact Rhold64.
    set (m := if negb (0 <=? szwrap 64 (ir_hold r1 * 2 ^ 50)) then DICTID else TYPE).
    assert (Hm : (0 <= szwrap 64 (ir_hold r1 * 2 ^ 50) /\ m = TYPE) \/ (szwrap 64 (ir_hold r1 * 2 ^ 50) < 0 /\ m = DICTID)).
    { subst m. destruct (Z.leb_spec 0 (szwrap 64 (ir_hold r1 * 2 ^ 50))); [left | right]; split; try reflexivity; lia. }
    assert (HB : exists R3,
      msteps s6_segs (mkst R2 (Z_to_bv 64 125408) MA s6_rom)
             (mkst R3 (Z_to_bv 64 pc6_disp)
                (wbytes (wbytes (wbytes MA (zw (cv_S v + 40)) (Z_to_le_bytes 8 1)) (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 1)) (zw (cv_S v + 8)) (Z_to_le_bytes 4 m)) s6_rom)
      /\ getr R3 1 = zw (ir_left r1) /\ getr R3 10 = zw (cv_ZP v) /\ getr R3 11 = zw (cv_flush v)
      /\ getr R3 29 = zw 30 /\ getr R3 25 = zw A6_JTAB /\ getr R3 31 = zw (-16180) /\ getr R3 23 = zw 0 /\ getr R3 24 = zw 0
      /\ (forall rg, reg_in rg [1; 24; 10; 11; 12; 13; 14; 15; 23; 29; 25; 31]%bv = false -> getr R3 rg = getr R2 rg)).
    { destruct Hm as [[Hs ->] | [Hs ->]].
      - arm_symexP (@nil (Z * expr)) ilD 30%nat [true]
          [RVal (EVar 34%nat); RVal (EVar 35%nat); RVal (ELit 16209); RVal (ELit 18446744073709535436)]
          pinsB [(45%nat, 2 ^ 63)] v r1 [cv_S v + 168] NoVals F0
          (mkst R2 (Z_to_bv 64 125408) MA s6_rom) R3 HR3 Hfr3 Hms3.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTB1" G end.
        exists R3. split; [by_run Hms3|]. reload_regs HR3 Q1 Q10 Q11 Q29 Q30 Q31. symex_reg HR3 (23%bv : reg) as Q23. symex_reg HR3 (24%bv : reg) as Q8.
        repeat match goal with |- _ /\ _ => split end; try assumption. fr_weak Hfr3.
      - arm_symexP (@nil (Z * expr)) ilD 30%nat [false]
          [RVal (EVar 34%nat); RVal (EVar 35%nat); RVal (ELit 16209); RVal (ELit 18446744073709535436)]
          pinsB [(45%nat, 2 ^ 63)] v r1 [cv_S v + 168] NoVals F0
          (mkst R2 (Z_to_bv 64 125408) MA s6_rom) R3 HR3 Hfr3 Hms3.
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTB2" G end.
        exists R3. split; [by_run Hms3|]. reload_regs HR3 Q1 Q10 Q11 Q29 Q30 Q31. symex_reg HR3 (23%bv : reg) as Q23. symex_reg HR3 (24%bv : reg) as Q8.
        repeat match goal with |- _ /\ _ => split end; try assumption. fr_weak Hfr3. }
    clear Hm. destruct HB as (R3 & Hms3 & Q1 & Q10 & Q11 & Q29 & Q30 & Q31 & Q23 & Q8 & Hfr3).
    set (MB1 := wbytes MA (zw (cv_S v + 40)) (Z_to_le_bytes 8 1)) in *.
    set (MB2 := wbytes MB1 (zw (cv_ZP v + 96)) (Z_to_le_bytes 8 1)) in *.
    set (MB := wbytes MB2 (zw (cv_S v + 8)) (Z_to_le_bytes 4 m)) in *.
    set (r3 := mkIR (ir_next r1) (ir_have r1) (ir_put r1) (ir_left r1) 0 0 (ir_in r1) (ir_out r1) (ir_ret r1)).
    set (c' := icset_adler c 1).
    set (s' := iset_mode (iset_check (iset_flags (iset_dmax s (2 ^ len)) 0) 1) m).
    assert (HMB1 : LMEM v (mkW (iset_check sA 1) c r3) MB1).
    { apply (LMEM_regs v (iset_check sA 1) c r1 c r3); [| reflexivity ..].
      apply (LMEM_store_scalar v C sA c r1 _ MA 40 _ HMA); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_check MA (cv_S v) _ sA 1 (lm_sc _ _ _ HMA)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HMB2 : LMEM v (mkW (iset_check sA 1) c' r3) MB2) by (exact (LMEM_store_adler v C _ c r3 MB1 1 HMB1 Hput)).
    assert (HMB : LMEM v (mkW s' c' r3) MB).
    { replace s' with (iset_mode (iset_check sA 1) m) by (subst s' sA; destruct s; reflexivity).
      apply (LMEM_store_scalar v C _ c' r3 _ MB2 8 _ HMB2); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
      apply (is6_upd_mode MB2 (cv_S v) _ _ m (lm_sc _ _ _ HMB2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    pose proof (lm_rod _ _ _ HMB) as MrodB. pose proof (is6_mode _ _ _ _ (lm_sc _ _ _ HMB)) as C8'. cbn [w_s] in C8'.
    replace (is_mode s') with m in C8' by (subst s'; destruct s; reflexivity).
    assert (Hmv : m = TYPE \/ m = DICTID) by (subst m; destruct (0 <=? _); [left | right]; reflexivity).
    assert (HC : exists R',
      msteps s6_segs (mkst R3 (Z_to_bv 64 pc6_disp) MB s6_rom) (mkst R' (Z_to_bv 64 (arm6_pc m)) MB s6_rom)
      /\ LFIX v R' /\ LVARS v (mkW s' c' r3) R').
    { pose proof (fun (n : reg) (Hn : reg_in n [1; 24; 10; 11; 12; 13; 14; 15; 23; 29; 25; 31]%bv = false) => Hfr3 n Hn) as HF3.
      destruct Hmv as [Em | Em]; rewrite Em in C8' |- *.
      - j1011_symex ilS 12%nat [true] [RVal (ELit 16191); RVal (ELit (JT TYPE))] (@nil (Z * expr)) (@nil (nat * Z)) v r3 (@nil Z) NoVals F0
          (mkst R3 (Z_to_bv 64 pc6_disp) MB s6_rom) R' HR' Hfr Hms.
        all: cbn [r3 ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
        all: try (lazymatch goal with |- getr _ ?n = zw _ => first [assumption | rewrite (Hfr3 n eq_refl); assumption] end).
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTC1" G end.
        exists R'. split; [by_run Hms|]. split; [unfold LFIX, INF_FRAME, A6_JTAB; regs_via2 Hfr Hfr3|].
        unfold LVARS; cbn [w_r r3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next]. symex_reg HR' (27%bv : reg) as G26'. regs_via2 Hfr Hfr3.
      - j1011_symex ilS 12%nat [true] [RVal (ELit 16189); RVal (ELit (JT DICTID))] (@nil (Z * expr)) (@nil (nat * Z)) v r3 (@nil Z) NoVals F0
          (mkst R3 (Z_to_bv 64 pc6_disp) MB s6_rom) R' HR' Hfr Hms.
        all: cbn [r3 ir_next ir_have ir_put ir_left ir_hold ir_bits ir_in ir_out ir_ret].
        all: try (lazymatch goal with |- getr _ ?n = zw _ => first [assumption | rewrite (Hfr3 n eq_refl); assumption] end).
        all: try arm_side.
        all: match goal with |- ?G => idtac "LEFTC2" G end.
        exists R'. split; [by_run Hms|]. split; [unfold LFIX, INF_FRAME, A6_JTAB; regs_via2 Hfr Hfr3|].
        unfold LVARS; cbn [w_r r3 ir_have ir_put ir_left ir_hold ir_bits ir_out ir_next]. symex_reg HR' (27%bv : reg) as G26'. regs_via2 Hfr Hfr3. }
    destruct HC as (R' & Hms4 & HF' & HV').
    pose proof (icset_adler_facts c 1) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
    exists R', MB, (arm6_pc m).
    split.
    { eapply msteps_trans; [| exact Hms4]. eapply msteps_trans; [| exact Hms3].
      eapply msteps_trans; [| exact Hms2]. subst MA MA1. by_run Hms1. }
    replace (irset_bits (irset_hold r2 0) 0) with r3 by (subst r2 r3; reflexivity).
    cbn [arm_post]. split; [subst s'; destruct s; reflexivity|]. split; [| split].
    - split; [exact HMB|]. split; [subst MB MB2 MB1 MA MA1; apply (RETC_regs v (mkW s c r1)); [retc_tower C HRC | reflexivity]|]. split.
      + unfold LX; cbn [w_s w_c w_r]. subst s' c' r3. rewrite E9. cbn [ir_in ir_ret].
        replace (is_wrap (iset_mode _ m)) with (is_wrap s) by (destruct s; reflexivity).
        replace (is_wbits (iset_mode _ m)) with (is_wbits s) by (destruct s; reflexivity).
        replace (is_flags (iset_mode _ m)) with 0 by (destruct s; reflexivity).
        replace (is_mode (iset_mode _ m)) with m by (destruct s; reflexivity).
        replace (is_havedict (iset_mode _ m)) with (is_havedict s) by (destruct s; reflexivity).
        refine (conj Xwrap (conj Xwbits (conj _ (conj (or_introl eq_refl) (conj Xin (conj Xret (conj Xmsg Xhd))))))).
        destruct Hmv as [-> | ->]; live_mode_tac.
      + split; [exact HF'|]. split; [exact HV'|]. subst s'. cbn [w_s].
        replace (is_mode (iset_mode (iset_check (iset_flags (iset_dmax s (2 ^ len)) 0) 1) m)) with m by (destruct s; reflexivity).
        intros Hb; exfalso; destruct Hmv as [Em|Em]; rewrite Em in Hb; cbv in Hb; discriminate.
    - subst s'. split; [destruct s; reflexivity | split; destruct s; reflexivity].
    - subst MB MB2 MB1 MA MA1 r3. cbn [ir_put].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CZP; lia | clear - CZP; cbn; lia | right; right; left; clear; cbn; lia].
      do 3 (apply (MFRAME_store v (ir_put r1) (ir_put r1) (ir_put r1)); [| lia | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia]).
      apply MFRAME_refl.
  Qed.
End HeadBody.
End FXG.
