(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare StepTac.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel SymAux RomRead.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import Prog ZIface InflateState InflateFast InflateArms Inflate InflateInv InflateInvKit HarnessKit HarnessFacts.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.D6U Require Import Segs6u Callee6u.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6S Require Import ISLayout InflMem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.J6U Require Import IS6 InflRod6 InflCtx6 InflArmLib6 InflArmLib6b.
Import ListNotations.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

Definition pc6_uw : Z := 0x21728.
Definition pc6_uw_ret : Z := 0x2163c.
Definition pc6_tzw : Z := 0x21794.
Definition pc6_zb : Z := 0x21798.
Definition pc6_uwj : Z := 0x217a0.
Lemma mod16_mod8 : forall a, a mod 16 = 0 -> a mod 2 ^ 3 = 0.
Proof.
  intros a H. change (2 ^ 3) with 8. apply Z.mod_divide in H; [|lia]. destruct H as [k Hk]. subst a.
  replace (k * 16) with ((k * 2) * 8) by lia. apply Z.mod_mul. lia.
Qed.

Lemma lxor_m1_mod64 : forall a, 0 <= a < 2 ^ 64 -> Z.lxor a (-1) mod 2 ^ 64 = 2 ^ 64 - 1 - a.
Proof.
  intros a Ha. rewrite Z.lxor_m1_r. unfold Z.lnot. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia.
Qed.


Definition uw_s1 (s : inflate_state) : inflate_state :=
  if is_wsize s =? 0 then iset_whave (iset_wnext (iset_wsize s 32768) 0) 0 else s.
Definition uw_dist (s : inflate_state) (copy : Z) : Z :=
  let d0 := 32768 - is_wnext (uw_s1 s) in if copy <? d0 then copy else d0.
Definition uwc (s : inflate_state) (src : arr) (e copy : Z) : inflate_state :=
  let s1 := uw_s1 s in
  if 32768 <=? copy then iset_whave (iset_wnext (iset_window s1 (arr_blit (is_window s1) 0 src (e - 32768) 32768)) 0) 32768 else
  let dist := uw_dist s copy in
  let s2 := iset_window s1 (arr_blit (is_window s1) (is_wnext s1) src (e - copy) dist) in
  let copy' := copy - dist in
  if negb (copy' =? 0)
  then iset_whave (iset_wnext (iset_window s2 (arr_blit (is_window s2) 0 src (e - copy') copy')) copy') 32768
  else
    let wn := is_wnext s1 + dist in
    let s3 := iset_wnext s2 (if wn =? 32768 then 0 else wn) in
    if is_whave s1 <? 32768 then iset_whave s3 (is_whave s1 + dist) else s3.

Lemma uw_s1_facts : forall s,
  (is_wsize s = 0 \/ is_wsize s = 32768) -> 0 <= is_wnext s /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s) -> 0 <= is_whave s /\ (is_wsize s <> 0 -> is_whave s <= is_wsize s) ->
  is_wsize (uw_s1 s) = 32768 /\ 0 <= is_wnext (uw_s1 s) <= 32768 /\ 0 <= is_whave (uw_s1 s) <= 32768
  /\ is_wbits (uw_s1 s) = is_wbits s /\ is_window (uw_s1 s) = is_window s /\ is_window_blk (uw_s1 s) = is_window_blk s
  /\ is_mode (uw_s1 s) = is_mode s /\ is_lens (uw_s1 s) = is_lens s /\ is_work (uw_s1 s) = is_work s /\ is_codes (uw_s1 s) = is_codes s.
Proof.
  intros s Hws Hwn Hwh. unfold uw_s1. destruct (Z.eqb_spec (is_wsize s) 0) as [E|E]; destruct s; cbn in *; repeat split; try reflexivity; lia.
Qed.

Lemma uw_core_eq : forall s src e copy,
  is_wbits s = 15 -> (is_wsize s = 0 \/ is_wsize s = 32768) -> 0 <= is_wnext s /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s) -> 0 <= is_whave s /\ (is_wsize s <> 0 -> is_whave s <= is_wsize s) ->
  0 <= copy ->
  uw_core s src e copy = uwc s src e copy.
Proof.
  intros s src e copy Hwb Hws Hwn Hwh Hc0.
  pose proof (uw_s1_facts s Hws Hwn Hwh) as (F1 & F2 & F3 & _).
  unfold uw_core, uwc, uw_dist. rewrite Hwb. change (shl32 1 15) with 32768. fold (uw_s1 s).
  remember (uw_s1 s) as s1 eqn:Es1. clear Es1.
  destruct s1; cbn -[Z.sub Z.add Z.ltb Z.leb Z.eqb arr_blit wrap32] in *. subst is_wsize.
  destruct (Z.leb_spec 32768 copy) as [Hbig|Hsmall]; [reflexivity|].
  assert (Hc : 0 <= copy < 32768) by lia.
  rewrite (wrap32_id (32768 - is_wnext)) by lia.
  set (dist := if copy <? 32768 - is_wnext then copy else 32768 - is_wnext).
  assert (Hd : 0 <= dist <= copy /\ dist <= 32768 - is_wnext) by (subst dist; destruct (Z.ltb_spec copy (32768 - is_wnext)); lia).
  rewrite (wrap32_id (copy - dist)) by lia.
  destruct (negb (copy - dist =? 0)) eqn:E; [reflexivity|].
  rewrite (wrap32_id (is_wnext + dist)) by lia.
  destruct (is_wnext + dist =? 32768); cbn -[Z.sub Z.add Z.ltb Z.leb Z.eqb arr_blit wrap32];
    destruct (is_whave <? 32768); rewrite ?(wrap32_id (is_whave + dist)) by lia; reflexivity.
Qed.

Section UpdWin.
  Variable v : icv.
  Hypothesis C : ictx v.
  Hypothesis MEMCPY : memcpy_run6u.

  Local Abbreviation spi := (cv_sp v - INF_FRAME).

  Ltac uw_ub_side :=
    first [ change (2 ^ 3) with 8; lia
          | apply mod16_mod8; lia
          | rewrite lxor_m1_mod64 by lia; lia
          | rewrite ?szwrap32_small by lia; rewrite ?Z.mod_small by lia; ub_ptr_side
          | ub_ptr_side ].
  Ltac uw_s5 := first [ reflexivity | f_equal; match goal with |- context [if ?a <? ?b then 1 else 0] => destruct (Z.ltb_spec a b); [reflexivity | exfalso; lia] end ].

  Definition uw_frame (M : word -> option byte) (ra : Z) (R : bvmap 5 word) : Prop :=
    cell s6u_segs M (spi - 8) 8 ra
    /\ cell s6u_segs M (spi - 16) 8 (bv_unsigned (getr R 8)) /\ cell s6u_segs M (spi - 24) 8 (bv_unsigned (getr R 9))
    /\ cell s6u_segs M (spi - 32) 8 (bv_unsigned (getr R 18)) /\ cell s6u_segs M (spi - 40) 8 (bv_unsigned (getr R 19))
    /\ cell s6u_segs M (spi - 48) 8 (bv_unsigned (getr R 20)) /\ cell s6u_segs M (spi - 56) 8 (bv_unsigned (getr R 21)).

  Definition uw_regs (R : bvmap 5 word) (pend copy : Z) : Prop :=
    getr R 8 = zw pend /\ getr R 9 = zw copy /\ getr R 19 = zw (cv_S v) /\ getr R 2 = zw (spi - 64).

  Lemma uw_stop6 : forall s c r R M (ra pend copy : Z),
    cv_WN v = 0 -> LMEM v (mkW s c r) M -> LX v (mkW s c r) -> 0 <= ir_put r <= cv_NO v ->
    getr R 10 = zw (cv_ZP v) -> getr R 11 = zw pend -> getr R 12 = zw copy -> getr R 1 = zw ra -> getr R 2 = zw spi ->
    0 <= pend < 2 ^ 63 -> 0 <= copy < 2 ^ 31 -> 0 <= ra < 2 ^ 64 ->
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uw) M s6u_rom) (mkst R' (Z_to_bv 64 pc6_tzw) M' s6u_rom)
      /\ getr R' 13 = zw (cv_fa v) /\ getr R' 10 = zw (cv_opq v) /\ getr R' 11 = zw 32768 /\ getr R' 12 = zw 1
      /\ uw_regs R' pend copy /\ getr R' 18 = zw 1
      /\ (forall rg, reg_in rg [2; 8; 9; 10; 11; 12; 13; 18; 19]%bv = false -> getr R' rg = getr R rg)
      /\ uw_frame M' ra R /\ LMEM v (mkW s c r) M' /\ agree_out (SCR v) M M' /\ (forall x, M x <> None -> M' x <> None).
  Proof.
    intros s c r R M ra pend copy HWN HM HX Hput G10 G11 G12 G1 G2 Bpend Bcopy Bra.
    open_ictx C. open_lmem HM. open_lx HX. open_zs Mzs. unfold mapped in *.
    assert (HWB : cv_WB v = 0) by (clear - CWB HWN; lia).
    pose proof (is6_window _ _ _ _ Msc) as C72. cbn [q_window] in C72. rewrite HWB in C72.
    pose proof (is6_wbits _ _ _ _ Msc) as C56. rewrite Xwbits in C56.
    symex s6u_segs (CFG [] [] [EVar 1%nat] [pc6_tzw; 0x2a824] []) 40%nat [false; false; false; false; false]
      [RVal (EVar 33%nat); RVal (ELit 0); RVal (ELit 15); RVal (EVar 37%nat); RVal (EVar 38%nat)]
      [(2, EVar 32%nat); (10, EVar 34%nat); (11, EVar 35%nat); (12, EVar 39%nat); (1, EVar 36%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 63); (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 31)]
      NoRegions [spi; cv_S v; cv_ZP v; pend; ra; cv_fa v; cv_opq v; copy] NoVals F0 F0'
      (mkst R (Z_to_bv 64 pc6_uw) M s6u_rom) R' HR' Hfr Hms.
    all: try (unfold INF_FRAME in *; arm_side).
    all: try uw_ub_side.
    all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT_S" G end.
    match type of Hms with msteps _ _ (mkst _ _ ?Mx _) => exists R', Mx end.
    split; [by_run Hms|].
    symex_reg HR' (13%bv : reg) as G13'. symex_reg HR' (10%bv : reg) as G10'. symex_reg HR' (11%bv : reg) as G11'. symex_reg HR' (12%bv : reg) as G12'.
    symex_reg HR' (8%bv : reg) as G8'. symex_reg HR' (9%bv : reg) as G9'. symex_reg HR' (19%bv : reg) as G19'. symex_reg HR' (2%bv : reg) as G2'. symex_reg HR' (18%bv : reg) as G18'.
    split; [exact G13'|]. split; [exact G10'|]. split; [exact G11'|]. split; [exact G12'|].
    split; [unfold uw_regs; unfold INF_FRAME; rewrite G8', G9', G19', G2'; repeat split; try reflexivity; f_equal; lia|].
    split; [exact G18'|].
    split; [intros rg Hrg; apply Hfr; exact Hrg|].
    lazymatch type of Hms with msteps _ _ (mkst _ _ ?Mx _) =>
      assert (AG : agree_out (SCR v) M Mx)
        by (unfold INF_FRAME in *; do 7 (apply (agree_scratch_store v C); [| unfold INF_FRAME, INF_SCRATCH; cbn; lia | unfold INF_FRAME, INF_SCRATCH; cbn; lia]); apply agree_out_refl)
    end.
    split; [| split; [| split; [exact AG | intros x Hx; repeat apply wbytes_grows; exact Hx]]].
    - unfold uw_frame. unfold INF_FRAME in *. repeat match goal with |- _ /\ _ => split end; tower_cell.
    - apply (LMEM_agree_scratch v C s c r M _ HM Hput AG). intros x Hx; repeat apply wbytes_grows; exact Hx.
  Qed.


  Lemma wnext_sel : forall a, 0 <= a < 2 ^ 62 ->
    Z.land ((if Z.lxor a 32768 <? 1 then 1 else 0) + -1) a = (if a =? 32768 then 0 else a).
  Proof.
    intros a Ha. pose proof (Z.lxor_nonneg a 32768) as X.
    destruct (Z.eqb_spec a 32768) as [E|NE].
    - subst a. cbn. reflexivity.
    - assert (Z.lxor a 32768 <> 0) by (intros E; apply NE; apply Z.lxor_eq; exact E).
      destruct (Z.ltb_spec (Z.lxor a 32768) 1); [exfalso; lia|]. cbn. apply Z.land_m1_l.
  Qed.

  Definition UWF (M : word -> option byte) (f8 f9 f18 f19 f20 f21 : Z) : Prop :=
    cell s6u_segs M (spi - 8) 8 pc6_uw_ret
    /\ cell s6u_segs M (spi - 16) 8 f8 /\ cell s6u_segs M (spi - 24) 8 f9
    /\ cell s6u_segs M (spi - 32) 8 f18 /\ cell s6u_segs M (spi - 40) 8 f19 /\ cell s6u_segs M (spi - 48) 8 f20
    /\ cell s6u_segs M (spi - 56) 8 f21.
  Definition JUW (R : bvmap 5 word) (M : word -> option byte) (pend copy f8 f9 f18 f19 f20 f21 : Z) : Prop :=
    uw_regs R pend copy /\ getr R 10 = zw (cv_WB v) /\ UWF M f8 f9 f18 f19 f20 f21.

  Definition UWFR (M M' : word -> option byte) : Prop :=
    (forall x : word, M x <> None -> M' x <> None)
    /\ (forall x : word,
          ~ (cv_sp v - INF_FRAME - INF_SCRATCH <= bv_unsigned x < cv_sp v - INF_FRAME) ->
          ~ (cv_S v <= bv_unsigned x < cv_S v + 7176) ->
          ~ (cv_WB v <= bv_unsigned x < cv_WB v + cv_WN v) -> M' x = M x).
  Lemma UWFR_refl : forall M, UWFR M M.
  Proof. intros M. split; [intros x Hx; exact Hx | intros; reflexivity]. Qed.
  Lemma UWFR_store : forall M M' (a : Z) bs,
    UWFR M M' -> 0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 ->
    ((cv_sp v - INF_FRAME - INF_SCRATCH <= a /\ a + Z.of_nat (length bs) <= cv_sp v - INF_FRAME)
     \/ (cv_S v <= a /\ a + Z.of_nat (length bs) <= cv_S v + 7176)
     \/ (cv_WB v <= a /\ a + Z.of_nat (length bs) <= cv_WB v + cv_WN v)) ->
    UWFR M (wbytes M' (zw a) bs).
  Proof.
    intros M M' a bs [Hg HE] Ha0 Ha1 Hz. split; [intros x Hx; apply wbytes_grows; exact (Hg x Hx)|].
    intros x N1 N2 N3. rewrite wbytes_inside; [| exact Ha0 | exact Ha1 |].
    - apply HE; assumption.
    - pose proof (u64_range x). lia.
  Qed.

  Lemma uw_segA : forall s c r R M pend copy f8 f9 f18 f19 f20 f21,
    cv_WN v = 32768 -> LMEM v (mkW s c r) M -> LX v (mkW s c r) -> 0 <= ir_put r <= cv_NO v ->
    (is_wsize s = 0 \/ is_wsize s = 32768) -> 0 <= is_wnext s /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s) -> 0 <= is_whave s /\ (is_wsize s <> 0 -> is_whave s <= is_wsize s) ->
    0 <= copy < 32768 -> copy <= ir_put r -> pend = cv_P0 v + ir_put r ->
    JUW R M pend copy f8 f9 f18 f19 f20 f21 ->
    let s1 := uw_s1 s in let dist := uw_dist s copy in
    exists R1 M1,
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) (mkst R1 (Z_to_bv 64 A6U_MEMCPY) M1 s6u_rom)
      /\ getr R1 10 = zw (cv_WB v + is_wnext s1) /\ getr R1 11 = zw (pend - copy) /\ getr R1 12 = zw dist
      /\ getr R1 1 = zw 0x217fc /\ getr R1 18 = zw (32768 - is_wnext s1) /\ getr R1 20 = zw dist /\ getr R1 21 = zw 1
      /\ uw_regs R1 pend copy
      /\ (forall rg, reg_in rg [1; 10; 11; 12; 13; 18; 20; 21]%bv = false -> getr R1 rg = getr R rg)
      /\ LMEM v (mkW s1 c r) M1 /\ UWF M1 f8 f9 f18 f19 f20 f21
      /\ UWFR M M1.
  Proof.
    intros s c r R M pend copy f8 f9 f18 f19 f20 f21 HWN HM HX Hput Hws Hwn Hwh Hc Hcp Hpend HJ.
    destruct HJ as ((G8 & G9 & G19 & G2) & G10 & (F8c & F16 & F24 & F32 & F40 & F48 & F56)).
    open_ictx C. open_lmem HM. open_lx HX. unfold mapped in *.
    pose proof (is6_wsize _ _ _ _ Msc) as C60. pose proof (is6_wnext _ _ _ _ Msc) as C68. pose proof (is6_wbits _ _ _ _ Msc) as C56. rewrite Xwbits in C56.
    assert (HWB0 : 0 < cv_WB v) by (clear - CWB HWN; lia).
    cbv zeta.
    destruct Hws as [W0 | W1].
    -
      rewrite W0 in C60.
      assert (Es1 : uw_s1 s = iset_whave (iset_wnext (iset_wsize s 32768) 0) 0) by (unfold uw_s1; rewrite W0; reflexivity).
      assert (Ed : uw_dist s copy = copy).
      { unfold uw_dist. rewrite Es1. replace (is_wnext _) with 0 by (destruct s; reflexivity). destruct (Z.ltb_spec copy (32768 - 0)); lia. }
      rewrite Ed.
      symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; 0x21888] []) 50%nat [true; false; true; false; false; false; false]
        [RVal (ELit 0); RVal (ELit 15)]
        [(2, EVar 32%nat); (19, EVar 33%nat); (8, EVar 34%nat); (9, EVar 35%nat); (10, EVar 36%nat)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 32768); (36%nat, 2 ^ 63)]
        NoRegions [spi - 64; cv_S v; pend; copy; cv_WB v] NoVals F0 F0'
        (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) R1 HR1 Hfr Hms.
      all: try (unfold INF_FRAME in *; arm_side).
      all: try uw_ub_side.
      all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT_A0" G end.
      set (M0 := wbytes M (zw (cv_S v + 72)) (Z_to_le_bytes 4 32768)) in Hms.
      set (M1a := wbytes M0 (zw (cv_S v + 76)) (Z_to_le_bytes 4 0)) in Hms. set (M1 := wbytes M1a (zw (cv_S v + 80)) (Z_to_le_bytes 4 0)) in Hms.
      assert (HM0 : LMEM v (mkW (iset_wsize s 32768) c r) M0).
      { apply (LMEM_store_scalar v C s c r _ M 72 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_wsize M (cv_S v) _ s 32768 Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM1 : LMEM v (mkW (uw_s1 s) c r) M1).
      { rewrite Es1. replace (iset_whave (iset_wnext (iset_wsize s 32768) 0) 0) with (iset_wnext (iset_whave (iset_wsize s 32768) 0) 0) by (destruct s; reflexivity).
        assert (HM1a : LMEM v (mkW (iset_whave (iset_wsize s 32768) 0) c r) M1a).
        { apply (LMEM_store_scalar v C _ c r _ M0 76 _ HM0); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_whave M0 (cv_S v) _ _ 0 (lm_sc _ _ _ HM0)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        apply (LMEM_store_scalar v C _ c r _ M1a 80 _ HM1a); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
        apply (is6_upd_wnext M1a (cv_S v) _ _ 0 (lm_sc _ _ _ HM1a)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      exists R1, M1. split; [subst M1 M1a M0; by_run Hms|].
      symex_reg HR1 (10%bv : reg) as G10'. symex_reg HR1 (11%bv : reg) as G11'. symex_reg HR1 (12%bv : reg) as G12'.
      symex_reg HR1 (1%bv : reg) as G1'. symex_reg HR1 (18%bv : reg) as G18'. symex_reg HR1 (20%bv : reg) as G20'. symex_reg HR1 (21%bv : reg) as G21'.
      rewrite Es1. replace (is_wnext (iset_whave (iset_wnext (iset_wsize s 32768) 0) 0)) with 0 by (destruct s; reflexivity).
      rewrite <- Es1.
      split; [rewrite G10'; f_equal; lia|]. split; [rewrite G11'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|]. split; [rewrite G12'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|].
      split; [exact G1'|]. split; [rewrite G18'; f_equal; lia|]. split; [rewrite G20'; f_equal; lia|]. split; [rewrite G21'; uw_s5|].
      split; [unfold uw_regs; regs_via Hfr|].
      split; [fr_weak Hfr|].
      split; [exact HM1|].
      split.
      { unfold UWF. subst M1 M1a M0. unfold INF_FRAME in *.
        repeat match goal with |- _ /\ _ => split end;
          (eapply cell_write_other; [eapply cell_write_other; [eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | sep_side] | lia | cbn; lia | lia | cbn; lia | sep_side] | lia | cbn; lia | lia | cbn; lia | sep_side]). }
      subst M1 M1a M0.
      apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply UWFR_store; [apply UWFR_refl | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
    -
      rewrite W1 in C60.
      assert (Es1 : uw_s1 s = s) by (unfold uw_s1; rewrite W1; reflexivity). rewrite Es1.
      assert (Hd0 : 0 <= 32768 - is_wnext s <= 32768) by (clear - Hwn W1; lia).
      unfold uw_dist. rewrite Es1.
      destruct (Z_lt_le_dec (32768 - is_wnext s) copy) as [GT|LE].
      +
        replace (if copy <? 32768 - is_wnext s then copy else 32768 - is_wnext s) with (32768 - is_wnext s)
          by (destruct (Z.ltb_spec copy (32768 - is_wnext s)); lia).
symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; 0x21888] []) 50%nat [false; false; true; false; false; false]
          [RVal (ELit 32768); RVal (EVar 37%nat)]
          [(2, EVar 32%nat); (19, EVar 33%nat); (8, EVar 34%nat); (9, EVar 35%nat); (10, EVar 36%nat)]
          [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 32768); (36%nat, 2 ^ 63); (37%nat, 32769)]
          NoRegions [spi - 64; cv_S v; pend; copy; cv_WB v; is_wnext s] NoVals F0 F0'
          (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) R1 HR1 Hfr Hms.
        all: try (unfold INF_FRAME in *; arm_side).
        all: try uw_ub_side.
        all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT_A1" G end.
        exists R1, M. split; [by_run Hms|].
        symex_reg HR1 (10%bv : reg) as G10'. symex_reg HR1 (11%bv : reg) as G11'. symex_reg HR1 (12%bv : reg) as G12'.
        symex_reg HR1 (1%bv : reg) as G1'. symex_reg HR1 (18%bv : reg) as G18'. symex_reg HR1 (20%bv : reg) as G20'. symex_reg HR1 (21%bv : reg) as G21'.
        rewrite ?szwrap32_small in G12' by (clear - Hd0; lia). rewrite ?szwrap32_small in G18' by (clear - Hd0; lia). rewrite ?szwrap32_small in G20' by (clear - Hd0; lia).
        split; [rewrite G10'; f_equal; lia|]. split; [rewrite G11'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|]. split; [rewrite G12'; rewrite ?Z.mod_small by (clear - Hd0; lia); f_equal; lia|].
        split; [exact G1'|]. split; [rewrite G18'; f_equal; lia|]. split; [rewrite G20'; f_equal; lia|]. split; [rewrite G21'; uw_s5|].
        split; [unfold uw_regs; regs_via Hfr|]. split; [fr_weak Hfr|]. split; [exact HM|].
        split; [unfold UWF; repeat (split; [assumption|]); assumption|]. apply UWFR_refl.
      +
        replace (if copy <? 32768 - is_wnext s then copy else 32768 - is_wnext s) with copy
          by (destruct (Z.ltb_spec copy (32768 - is_wnext s)); lia).
symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; 0x21888] []) 50%nat [false; false; false; false; false; false]
          [RVal (ELit 32768); RVal (EVar 37%nat)]
          [(2, EVar 32%nat); (19, EVar 33%nat); (8, EVar 34%nat); (9, EVar 35%nat); (10, EVar 36%nat)]
          [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 32768); (36%nat, 2 ^ 63); (37%nat, 32769)]
          NoRegions [spi - 64; cv_S v; pend; copy; cv_WB v; is_wnext s] NoVals F0 F0'
          (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) R1 HR1 Hfr Hms.
        all: try (unfold INF_FRAME in *; arm_side).
        all: try uw_ub_side.
        all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT_A1" G end.
        exists R1, M. split; [by_run Hms|].
        symex_reg HR1 (10%bv : reg) as G10'. symex_reg HR1 (11%bv : reg) as G11'. symex_reg HR1 (12%bv : reg) as G12'.
        symex_reg HR1 (1%bv : reg) as G1'. symex_reg HR1 (18%bv : reg) as G18'. symex_reg HR1 (20%bv : reg) as G20'. symex_reg HR1 (21%bv : reg) as G21'.
        rewrite ?szwrap32_small in G12' by (clear - Hd0; lia). rewrite ?szwrap32_small in G18' by (clear - Hd0; lia). rewrite ?szwrap32_small in G20' by (clear - Hd0; lia).
        split; [rewrite G10'; f_equal; lia|]. split; [rewrite G11'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|]. split; [rewrite G12'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|].
        split; [exact G1'|]. split; [rewrite G18'; f_equal; lia|]. split; [rewrite G20'; f_equal; lia|]. split; [rewrite G21'; uw_s5|].
        split; [unfold uw_regs; regs_via Hfr|]. split; [fr_weak Hfr|]. split; [exact HM|].
        split; [unfold UWF; repeat (split; [assumption|]); assumption|]. apply UWFR_refl.
  Qed.

  Definition uw_clob : list reg := [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 28; 29; 30; 31]%bv.

  Lemma uw_call1 : forall s c r R1 M1 pend copy,
    let s1 := uw_s1 s in let dist := uw_dist s copy in
    cv_WN v = 32768 -> LMEM v (mkW s1 c r) M1 -> arr_len (is_window s1) = 32768 ->
    0 <= is_wnext s1 <= 32768 -> 0 <= copy < 32768 -> copy <= ir_put r -> ir_put r <= cv_NO v ->
    (forall i, 0 <= i < cv_NO v -> 0 <= arr_get (ic_outbuf c) i < 256) -> pend = cv_P0 v + ir_put r ->
    getr R1 10 = zw (cv_WB v + is_wnext s1) -> getr R1 11 = zw (pend - copy) -> getr R1 12 = zw dist -> getr R1 1 = zw 0x217fc ->
    exists R2,
      msteps s6u_segs (mkst R1 (Z_to_bv 64 A6U_MEMCPY) M1 s6u_rom)
             (mkst R2 (Z_to_bv 64 0x217fc) (wbytes M1 (zw (cv_WB v + is_wnext s1)) (cbytes (arr_get (ic_outbuf c)) (ir_put r - copy) (Z.to_nat dist))) s6u_rom)
      /\ (forall rg, reg_in rg memcpy_clob = false -> getr R2 rg = getr R1 rg)
      /\ LMEM v (mkW (iset_window s1 (arr_blit (is_window s1) (is_wnext s1) (ic_outbuf c) (ir_put r - copy) dist)) c r)
                (wbytes M1 (zw (cv_WB v + is_wnext s1)) (cbytes (arr_get (ic_outbuf c)) (ir_put r - copy) (Z.to_nat dist))).
  Proof.
    intros s c r R1 M1 pend copy. cbv zeta. intros HWN HM1 Hwl Hwn1 Hc Hcp Hput Houtb Hpend G10 G11 G12 G1.
    open_ictx C.
    assert (HW : cv_WN v = 32768 /\ 0 < cv_WB v /\ cv_WB v mod 16 = 0) by (clear - CWB HWN; lia). destruct HW as (_ & HWB0 & _).
    assert (Hd : 0 <= uw_dist s copy <= copy /\ uw_dist s copy <= 32768 - is_wnext (uw_s1 s)).
    { unfold uw_dist. destruct (Z.ltb_spec copy (32768 - is_wnext (uw_s1 s))); lia. }
    pose proof (lm_out _ _ _ HM1) as Mout. cbn [w_c w_r] in Mout.
    pose proof (cells_rdn_bytes s6u_segs M1 (cv_P0 v) (ir_put r) (arr_get (ic_outbuf c)) (ir_put r - copy) (Z.to_nat (uw_dist s copy)) Mout
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
    pose proof (lm_map_W _ _ _ HM1 ltac:(lia)) as MW. cbn in MW.
    assert (Hn : Z.of_nat (Z.to_nat (uw_dist s copy)) = uw_dist s copy) by (apply Z2Nat.id; lia).
    destruct (MEMCPY _ R1 (cv_WB v + is_wnext (uw_s1 s)) (cv_P0 v + (ir_put r - copy)) (Z.to_nat (uw_dist s copy)) _ (zw 0x217fc) Hsrc
               ltac:(clear - HWB0 Hwn1; lia) ltac:(rewrite Hn; clear - CWB HWN Hwn1 Hd; lia) ltac:(clear - CP0 Hcp Hput; lia) ltac:(rewrite Hn; clear - CP0 Hd Hcp Hput; lia))
      as (R2 & Hms & _ & Hfr).
    - rewrite Hn. destruct (Z.eq_dec (uw_dist s copy) 0) as [E0|E0]; [clear - E0; lia|].
      specialize (CPW ltac:(clear - E0 Hd Hcp Hput; lia)). unfold sep in CPW. clear - CPW Hd Hcp Hput Hwn1 CP0 HWN. lia.
    - rewrite Hn. intros x Hx. apply MW. clear - Hx Hd Hwn1 HWN. lia.
    - apply ret_ok_lit; [lia | reflexivity].
    - exact G1.
    - exact G10.
    - change (reg_get R1 11) with (getr R1 11). rewrite G11. f_equal. lia.
    - change (reg_get R1 12) with (getr R1 12). rewrite G12. f_equal. lia.
    - exists R2. split; [change (Z_to_bv 64 A6U_MEMCPY) with (zw A6U_MEMCPY); exact Hms|]. split; [exact Hfr|].
      rewrite <- Hn at 1.
      apply (LMEM_blit_win v C); try assumption; rewrite ?Hn; lia.
  Qed.

  Lemma uw_body6 : forall s c r R M pend copy f8 f9 f18 f19 f20 f21,
    cv_WN v = 32768 -> LMEM v (mkW s c r) M -> LX v (mkW s c r) -> 0 <= ir_put r <= cv_NO v ->
    arr_len (is_window s) = 32768 -> (is_wsize s = 0 \/ is_wsize s = 32768) ->
    0 <= is_wnext s /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s) -> 0 <= is_whave s /\ (is_wsize s <> 0 -> is_whave s <= is_wsize s) ->
    (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s) ->
    0 <= copy < 32768 -> copy <= ir_put r ->
    (forall i, 0 <= i < cv_NO v -> 0 <= arr_get (ic_outbuf c) i < 256) -> pend = cv_P0 v + ir_put r ->
    JUW R M pend copy f8 f9 f18 f19 f20 f21 ->
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) (mkst R' (Z_to_bv 64 pc6_uw_ret) M' s6u_rom)
      /\ LMEM v (mkW (uwc s (ic_outbuf c) (ir_put r) copy) c r) M'
      /\ getr R' 10 = zw 0 /\ getr R' 8 = zw f8 /\ getr R' 9 = zw f9 /\ getr R' 18 = zw f18 /\ getr R' 19 = zw f19 /\ getr R' 20 = zw f20
      /\ getr R' 21 = zw f21 /\ getr R' 2 = zw spi
      /\ (forall rg, reg_in rg uw_clob = false -> getr R' rg = getr R rg)
      /\ UWFR M M'.
  Proof.
    intros s c r R M pend copy f8 f9 f18 f19 f20 f21 HWN HM HX Hput Hwl Hws Hwn Hwh Hwhn Hc Hcp Houtb Hpend HJ.
    pose proof HJ as ((G8 & G9 & G19 & G2) & G10 & HF).
    open_ictx C.
    assert (HW : cv_WN v = 32768 /\ 0 < cv_WB v /\ cv_WB v mod 16 = 0) by (clear - CWB HWN; lia). destruct HW as (_ & HWB0 & _).
    pose proof (uw_s1_facts s Hws Hwn Hwh) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8l & F9w & F10c).
    assert (Hd : 0 <= uw_dist s copy <= copy /\ uw_dist s copy <= 32768 - is_wnext (uw_s1 s)).
    { unfold uw_dist. destruct (Z.ltb_spec copy (32768 - is_wnext (uw_s1 s))); lia. }
    destruct (uw_segA s c r R M pend copy f8 f9 f18 f19 f20 f21 HWN HM HX Hput Hws Hwn Hwh Hc Hcp Hpend HJ)
      as (R1 & M1 & Hms1 & A10 & A11 & A12 & A1 & A18 & A20 & A21 & AU & Afr & HM1 & HF1 & MF1).
    assert (Hwl1 : arr_len (is_window (uw_s1 s)) = 32768) by (rewrite F5; exact Hwl).
    destruct (uw_call1 s c r R1 M1 pend copy HWN HM1 Hwl1 F2 Hc Hcp (proj2 Hput) Houtb Hpend A10 A11 A12 A1) as (R2 & Hms2 & Bfr & HM2).
    set (s2 := iset_window (uw_s1 s) (arr_blit (is_window (uw_s1 s)) (is_wnext (uw_s1 s)) (ic_outbuf c) (ir_put r - copy) (uw_dist s copy))) in HM2.
    set (M2 := wbytes M1 (zw (cv_WB v + is_wnext (uw_s1 s))) (cbytes (arr_get (ic_outbuf c)) (ir_put r - copy) (Z.to_nat (uw_dist s copy)))) in Hms2, HM2.
    assert (HF2 : UWF M2 f8 f9 f18 f19 f20 f21).
    { subst M2. unfold UWF in *. unfold INF_FRAME in *. destruct HF1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      repeat match goal with |- _ /\ _ => split end;
        (eapply cell_write_other; [eassumption | lia | cbn; lia | clear - HWB0 F2; lia | rewrite cbytes_length, Z2Nat.id by lia; clear - CWB HWN F2 Hd; lia
                                   | rewrite cbytes_length, Z2Nat.id by lia; unfold sep in CfW; clear - CfW Csp CWB HWN F2 Hd; lia]). }
    assert (B8 : getr R2 8 = zw pend) by (rewrite (Bfr (8%bv : reg) eq_refl); exact (proj1 AU)).
    assert (B9 : getr R2 9 = zw copy) by (rewrite (Bfr (9%bv : reg) eq_refl); exact (proj1 (proj2 AU))).
    assert (B19 : getr R2 19 = zw (cv_S v)) by (rewrite (Bfr (19%bv : reg) eq_refl); exact (proj1 (proj2 (proj2 AU)))).
    assert (B2 : getr R2 2 = zw (spi - 64)) by (rewrite (Bfr (2%bv : reg) eq_refl); exact (proj2 (proj2 (proj2 AU)))).
    assert (B18 : getr R2 18 = zw (32768 - is_wnext (uw_s1 s))) by (rewrite (Bfr (18%bv : reg) eq_refl); exact A18).
    assert (B20 : getr R2 20 = zw (uw_dist s copy)) by (rewrite (Bfr (20%bv : reg) eq_refl); exact A20).
    assert (B21 : getr R2 21 = zw 1) by (rewrite (Bfr (21%bv : reg) eq_refl); exact A21).
    pose proof HM2 as HM2'. open_lmem HM2'. unfold mapped in *.
    pose proof (is6_wsize _ _ _ _ Msc) as C60. pose proof (is6_wnext _ _ _ _ Msc) as C68. pose proof (is6_whave _ _ _ _ Msc) as C64. pose proof (is6_window _ _ _ _ Msc) as C72.
    cbn [q_window] in C72.
    replace (is_wsize s2) with 32768 in C60 by (subst s2; rewrite <- F1; destruct (uw_s1 s); reflexivity).
    replace (is_wnext s2) with (is_wnext (uw_s1 s)) in C68 by (subst s2; destruct (uw_s1 s); reflexivity).
    replace (is_whave s2) with (is_whave (uw_s1 s)) in C64 by (subst s2; destruct (uw_s1 s); reflexivity).
    destruct HF2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). unfold INF_FRAME in *.
    unfold uwc. replace (32768 <=? copy) with false by (symmetry; apply Z.leb_gt; clear - Hc; lia). fold s2.
    destruct (Z_lt_le_dec (32768 - is_wnext (uw_s1 s)) copy) as [GT|LE].
    -
      assert (Ed : uw_dist s copy = 32768 - is_wnext (uw_s1 s)) by (unfold uw_dist; destruct (Z.ltb_spec copy (32768 - is_wnext (uw_s1 s))); lia).
      replace (negb (copy - uw_dist s copy =? 0)) with true by (symmetry; rewrite Ed; apply (proj2 (negb_true_iff _)); apply Z.eqb_neq; lia).
      rewrite Ed in B20.
      symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; 0x21888] []) 30%nat [false; false; false]
        [RVal (EVar 37%nat)]
        [(2, EVar 32%nat); (19, EVar 33%nat); (8, EVar 34%nat); (9, EVar 35%nat); (18, EVar 36%nat); (20, EVar 36%nat); (21, ELit 1)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 32768); (36%nat, 32769); (37%nat, 2 ^ 63)]
        NoRegions [cv_sp v - 256 - 64; cv_S v; pend; copy; 32768 - is_wnext (uw_s1 s); cv_WB v] NoVals F0 F0'
        (mkst R2 (Z_to_bv 64 0x217fc) M2 s6u_rom) R3 HR3 Hfr3 Hms3.
      all: try (unfold INF_FRAME in *; arm_side).
      all: try (rewrite B2; f_equal; lia).
      all: try uw_ub_side.
      all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT_B1" G end.
      symex_reg HR3 (10%bv : reg) as D10. symex_reg HR3 (11%bv : reg) as D11. symex_reg HR3 (12%bv : reg) as D12. symex_reg HR3 (1%bv : reg) as D1. symex_reg HR3 (9%bv : reg) as D9.
      rewrite ?szwrap32_small in D9 by (clear - Hc Hd GT F2; lia). rewrite ?Z.mod_small in D11 by (clear - Hc Hd GT F2; lia). rewrite ?Z.mod_small in D12 by (clear - Hc Hd GT F2; lia).
      set (copy' := copy - (32768 - is_wnext (uw_s1 s))).
      assert (Hcp' : 0 < copy' <= copy /\ copy' <= 32768) by (subst copy'; clear - Hc Hd GT F2; lia).
      pose proof (cells_rdn_bytes s6u_segs M2 (cv_P0 v) (ir_put r) (arr_get (ic_outbuf c)) (ir_put r - copy') (Z.to_nat copy') Mout
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc2.
      assert (Hn2 : Z.of_nat (Z.to_nat copy') = copy') by (apply Z2Nat.id; lia).
      destruct (MEMCPY _ R3 (cv_WB v) (cv_P0 v + (ir_put r - copy')) (Z.to_nat copy') _ (zw 0x2182c) Hsrc2
                 ltac:(clear - HWB0; lia) ltac:(rewrite Hn2; clear - CWB HWN Hcp'; lia) ltac:(clear - CP0 Hcp Hput Hcp'; lia) ltac:(rewrite Hn2; clear - CP0 Hcp Hput Hcp'; lia))
        as (R4 & Hms4 & _ & Hfr4).
      { rewrite Hn2. specialize (CPW ltac:(clear - Hcp' Hcp Hput; lia)). unfold sep in CPW. clear - CPW Hcp' Hcp Hput CP0 HWN. lia. }
      { rewrite Hn2. intros x Hx. apply Mmap_W; [clear - HWN; lia|]. clear - Hx Hcp' HWN. lia. }
      { apply ret_ok_lit; [lia | reflexivity]. }
      { exact D1. }
      { exact D10. }
      { change (reg_get R3 11) with (getr R3 11). rewrite D11. f_equal. subst copy'. lia. }
      { change (reg_get R3 12) with (getr R3 12). rewrite D12. f_equal. subst copy'. lia. }
      set (M4 := wbytes M2 (zw (cv_WB v)) (cbytes (arr_get (ic_outbuf c)) (ir_put r - copy') (Z.to_nat copy'))) in Hms4.
      assert (HM4 : LMEM v (mkW (iset_window s2 (arr_blit (is_window s2) 0 (ic_outbuf c) (ir_put r - copy') copy')) c r) M4).
      { subst M4. rewrite <- Hn2 at 1.
        assert (Hwl2 : arr_len (is_window s2) = 32768) by (subst s2; rewrite <- Hwl1; destruct (uw_s1 s); cbn; apply arr_len_blit).
        pose proof (LMEM_blit_win v C s2 c r (Z.to_nat copy') 0 (ir_put r - copy') M2 HM2 HWN Hwl2 ltac:(lia)
                      ltac:(rewrite Hn2; clear - Hcp'; lia) ltac:(clear - Hcp' Hcp; lia) ltac:(rewrite Hn2; clear - Hcp'; lia) (proj2 Hput) Houtb) as X.
        rewrite Z.add_0_r, Hn2 in X. rewrite Hn2. exact X. }
      pose proof (lm_sc _ _ _ HM4) as Msc4. cbn [w_s] in Msc4. pose proof (is6_wsize _ _ _ _ Msc4) as C60'.
      replace (is_wsize (iset_window s2 _)) with 32768 in C60' by (subst s2; rewrite <- F1; destruct (uw_s1 s); reflexivity).
      assert (Q1' : cell s6u_segs M4 (cv_sp v - 256 - 64 + 56) 8 pc6_uw_ret).
      { subst M4. replace (cv_sp v - 256 - 64 + 56) with (cv_sp v - 256 - 8) by lia. eapply cell_write_other; [exact Q1 | lia | cbn; lia | clear - HWB0; lia | rewrite cbytes_length, Hn2; clear - CWB HWN Hcp'; lia | rewrite cbytes_length, Hn2; unfold sep in CfW; clear - CfW Csp CWB HWN Hcp'; lia]. }
      assert (Q2' : cell s6u_segs M4 (cv_sp v - 256 - 64 + 48) 8 f8).
      { subst M4. replace (cv_sp v - 256 - 64 + 48) with (cv_sp v - 256 - 16) by lia. eapply cell_write_other; [exact Q2 | lia | cbn; lia | clear - HWB0; lia | rewrite cbytes_length, Hn2; clear - CWB HWN Hcp'; lia | rewrite cbytes_length, Hn2; unfold sep in CfW; clear - CfW Csp CWB HWN Hcp'; lia]. }
      assert (Q3' : cell s6u_segs M4 (cv_sp v - 256 - 64 + 40) 8 f9).
      { subst M4. replace (cv_sp v - 256 - 64 + 40) with (cv_sp v - 256 - 24) by lia. eapply cell_write_other; [exact Q3 | lia | cbn; lia | clear - HWB0; lia | rewrite cbytes_length, Hn2; clear - CWB HWN Hcp'; lia | rewrite cbytes_length, Hn2; unfold sep in CfW; clear - CfW Csp CWB HWN Hcp'; lia]. }
      assert (Q4' : cell s6u_segs M4 (cv_sp v - 256 - 64 + 32) 8 f18).
      { subst M4. replace (cv_sp v - 256 - 64 + 32) with (cv_sp v - 256 - 32) by lia. eapply cell_write_other; [exact Q4 | lia | cbn; lia | clear - HWB0; lia | rewrite cbytes_length, Hn2; clear - CWB HWN Hcp'; lia | rewrite cbytes_length, Hn2; unfold sep in CfW; clear - CfW Csp CWB HWN Hcp'; lia]. }
      assert (Q5' : cell s6u_segs M4 (cv_sp v - 256 - 64 + 24) 8 f19).
      { subst M4. replace (cv_sp v - 256 - 64 + 24) with (cv_sp v - 256 - 40) by lia. eapply cell_write_other; [exact Q5 | lia | cbn; lia | clear - HWB0; lia | rewrite cbytes_length, Hn2; clear - CWB HWN Hcp'; lia | rewrite cbytes_length, Hn2; unfold sep in CfW; clear - CfW Csp CWB HWN Hcp'; lia]. }
      assert (Q6' : cell s6u_segs M4 (cv_sp v - 256 - 64 + 16) 8 f20).
      { subst M4. replace (cv_sp v - 256 - 64 + 16) with (cv_sp v - 256 - 48) by lia. eapply cell_write_other; [exact Q6 | lia | cbn; lia | clear - HWB0; lia | rewrite cbytes_length, Hn2; clear - CWB HWN Hcp'; lia | rewrite cbytes_length, Hn2; unfold sep in CfW; clear - CfW Csp CWB HWN Hcp'; lia]. }
      assert (Q7' : cell s6u_segs M4 (cv_sp v - 256 - 64 + 8) 8 f21).
      { subst M4. replace (cv_sp v - 256 - 64 + 8) with (cv_sp v - 256 - 56) by lia. eapply cell_write_other; [exact Q7 | lia | cbn; lia | clear - HWB0; lia | rewrite cbytes_length, Hn2; clear - CWB HWN Hcp'; lia | rewrite cbytes_length, Hn2; unfold sep in CfW; clear - CfW Csp CWB HWN Hcp'; lia]. }
      pose proof (lm_map_S _ _ _ HM4) as MS4. pose proof (lm_map_f _ _ _ HM4) as Mf4. unfold mapped, INF_FRAME, INF_SCRATCH in MS4, Mf4.
      assert (E9 : getr R4 9 = zw copy') by (rewrite (Hfr4 (9%bv : reg) eq_refl), D9; f_equal; subst copy'; lia).
      assert (E19 : getr R4 19 = zw (cv_S v)) by (rewrite (Hfr4 (19%bv : reg) eq_refl), (Hfr3 (19%bv : reg) eq_refl); exact B19).
      assert (E2 : getr R4 2 = zw (cv_sp v - 256 - 64)) by (rewrite (Hfr4 (2%bv : reg) eq_refl), (Hfr3 (2%bv : reg) eq_refl), B2; f_equal; lia).
      symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; pc6_uw_ret] []) 24%nat (@nil bool)
        [RVal (ELit 32768); RVal (ELit pc6_uw_ret); RVal (EVar 36%nat); RVal (EVar 37%nat); RVal (EVar 38%nat); RVal (EVar 39%nat); RVal (EVar 40%nat); RVal (EVar 41%nat)]
        [(2, EVar 32%nat); (19, EVar 33%nat); (9, EVar 35%nat)]
        [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (35%nat, 32769); (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64)]
        NoRegions [cv_sp v - 256 - 64; cv_S v; 0; copy'; f8 mod 2 ^ 64; f9 mod 2 ^ 64; f18 mod 2 ^ 64; f19 mod 2 ^ 64; f20 mod 2 ^ 64; f21 mod 2 ^ 64] NoVals F0 F0'
        (mkst R4 (Z_to_bv 64 0x2182c) M4 s6u_rom) R5 HR5 Hfr5 Hms5.
      all: try (unfold INF_FRAME in *; arm_side).
      set (M5 := wbytes M4 (zw (cv_S v + 76)) (Z_to_le_bytes 4 32768)) in Hms5.
      set (M6 := wbytes M5 (zw (cv_S v + 80)) (Z_to_le_bytes 4 copy')) in Hms5.
      set (s4 := iset_window s2 (arr_blit (is_window s2) 0 (ic_outbuf c) (ir_put r - copy') copy')) in HM4.
      assert (HM5 : LMEM v (mkW (iset_whave s4 32768) c r) M5).
      { apply (LMEM_store_scalar v C s4 c r _ M4 76 _ HM4); [lia | cbn; lia | exact Hput | | subst s4 s2; destruct (uw_s1 s); reflexivity ..].
        apply (is6_upd_whave M4 (cv_S v) _ s4 32768 (lm_sc _ _ _ HM4)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      assert (HM6 : LMEM v (mkW (iset_wnext (iset_whave s4 32768) copy') c r) M6).
      { apply (LMEM_store_scalar v C _ c r _ M5 80 _ HM5); [lia | cbn; lia | exact Hput | | subst s4 s2; destruct (uw_s1 s); reflexivity ..].
        apply (is6_upd_wnext M5 (cv_S v) _ _ copy' (lm_sc _ _ _ HM5)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
      exists R5, M6. split.
      { eapply msteps_trans; [by_run Hms1|]. eapply msteps_trans; [by_run Hms2|]. eapply msteps_trans; [by_run Hms3|].
        eapply msteps_trans; [by_run Hms4|]. subst M6 M5. by_run Hms5. }
      rewrite !Ed. fold copy'. fold s4.
      split; [replace (iset_whave (iset_wnext s4 copy') 32768) with (iset_wnext (iset_whave s4 32768) copy') by (subst s4 s2; destruct (uw_s1 s); reflexivity); exact HM6|].
      symex_reg HR5 (10%bv : reg) as E10'. symex_reg HR5 (8%bv : reg) as E8'. symex_reg HR5 (9%bv : reg) as E9'. symex_reg HR5 (18%bv : reg) as E18'.
      symex_reg HR5 (19%bv : reg) as E19'. symex_reg HR5 (20%bv : reg) as E20'. symex_reg HR5 (21%bv : reg) as E21'. symex_reg HR5 (2%bv : reg) as E2'.
      split; [exact E10'|]. split; [rewrite E8'; apply zw_neg_mod|]. split; [rewrite E9'; apply zw_neg_mod|]. split; [rewrite E18'; apply zw_neg_mod|].
      split; [rewrite E19'; apply zw_neg_mod|]. split; [rewrite E20'; apply zw_neg_mod|]. split; [rewrite E21'; apply zw_neg_mod|]. split; [rewrite E2'; f_equal; lia|].
      split.
      { intros rg Hrg. rewrite (Hfr5 rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity). rewrite (Hfr4 rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity).
        rewrite (Hfr3 rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity). rewrite (Bfr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity).
        rewrite (Afr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity). reflexivity. }
      subst M6 M5 M4 M2.
      apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      apply UWFR_store; [| clear - HWB0; lia | rewrite cbytes_length, Hn2; clear - CWB HWN Hcp'; lia | right; right; rewrite cbytes_length, Hn2; clear - HWN Hcp'; lia].
      apply UWFR_store; [exact MF1 | clear - HWB0 F2; lia | rewrite cbytes_length, Z2Nat.id by lia; clear - CWB HWN Hd F2; lia | right; right; rewrite cbytes_length, Z2Nat.id by lia; clear - HWN Hd F2; lia].
    -
      assert (Ed : uw_dist s copy = copy) by (unfold uw_dist; destruct (Z.ltb_spec copy (32768 - is_wnext (uw_s1 s))); lia).
      replace (negb (copy - uw_dist s copy =? 0)) with false by (symmetry; rewrite Ed, Z.sub_diag; reflexivity).
      rewrite Ed in B20. rewrite !Ed.
      cbv zeta.
      pose proof (lm_map_S _ _ _ HM2) as MS2. pose proof (lm_map_f _ _ _ HM2) as Mf2. unfold mapped, INF_FRAME, INF_SCRATCH in MS2, Mf2.
      replace (cv_sp v - 256 - 8) with (cv_sp v - 256 - 64 + 56) in Q1 by lia.
      replace (cv_sp v - 256 - 16) with (cv_sp v - 256 - 64 + 48) in Q2 by lia.
      replace (cv_sp v - 256 - 24) with (cv_sp v - 256 - 64 + 40) in Q3 by lia.
      replace (cv_sp v - 256 - 32) with (cv_sp v - 256 - 64 + 32) in Q4 by lia.
      replace (cv_sp v - 256 - 40) with (cv_sp v - 256 - 64 + 24) in Q5 by lia.
      replace (cv_sp v - 256 - 48) with (cv_sp v - 256 - 64 + 16) in Q6 by lia.
      replace (cv_sp v - 256 - 56) with (cv_sp v - 256 - 64 + 8) in Q7 by lia.
      destruct (Z.ltb_spec (is_whave (uw_s1 s)) 32768) as [WL|WG].
      + symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; pc6_uw_ret] []) 44%nat [true; false]
          [RVal (EVar 36%nat); RVal (ELit 32768); RVal (EVar 37%nat); RVal (ELit pc6_uw_ret); RVal (EVar 38%nat); RVal (EVar 39%nat); RVal (EVar 40%nat); RVal (EVar 41%nat); RVal (EVar 42%nat); RVal (EVar 44%nat)]
          [(2, EVar 32%nat); (19, EVar 33%nat); (9, EVar 35%nat); (18, EVar 43%nat); (20, EVar 35%nat)]
          [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (35%nat, 32768); (36%nat, 32769); (37%nat, 32769); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64); (43%nat, 32769); (44%nat, 2 ^ 64)]
          NoRegions [cv_sp v - 256 - 64; cv_S v; 0; copy; is_wnext (uw_s1 s); is_whave (uw_s1 s); f8 mod 2 ^ 64; f9 mod 2 ^ 64; f18 mod 2 ^ 64; f19 mod 2 ^ 64; f20 mod 2 ^ 64; 32768 - is_wnext (uw_s1 s); f21 mod 2 ^ 64] NoVals F0 F0'
          (mkst R2 (Z_to_bv 64 0x217fc) M2 s6u_rom) R3 HR3 Hfr3 Hms3.
        all: try (unfold INF_FRAME in *; arm_side).
        all: try (rewrite B2; f_equal; lia).
        set (wn := is_wnext (uw_s1 s) + copy) in *.
        rewrite (wnext_sel wn) in Hms3 by (subst wn; clear - F2 Hc; lia).
        set (M3 := wbytes M2 (zw (cv_S v + 80)) (Z_to_le_bytes 4 (if wn =? 32768 then 0 else wn))) in Hms3.
        set (M4 := wbytes M3 (zw (cv_S v + 76)) (Z_to_le_bytes 4 (is_whave (uw_s1 s) + copy))) in Hms3.
        assert (HM3 : LMEM v (mkW (iset_wnext s2 (if wn =? 32768 then 0 else wn)) c r) M3).
        { apply (LMEM_store_scalar v C s2 c r _ M2 80 _ HM2); [lia | cbn; lia | exact Hput | | subst s2; destruct (uw_s1 s); reflexivity ..].
          apply (is6_upd_wnext M2 (cv_S v) _ s2 _ (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM4 : LMEM v (mkW (iset_whave (iset_wnext s2 (if wn =? 32768 then 0 else wn)) (is_whave (uw_s1 s) + copy)) c r) M4).
        { apply (LMEM_store_scalar v C _ c r _ M3 76 _ HM3); [lia | cbn; lia | exact Hput | | subst s2; destruct (uw_s1 s); reflexivity ..].
          apply (is6_upd_whave M3 (cv_S v) _ _ _ (lm_sc _ _ _ HM3)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        exists R3, M4. split.
        { eapply msteps_trans; [by_run Hms1|]. eapply msteps_trans; [by_run Hms2|]. subst M4 M3. by_run Hms3. }
        split; [exact HM4|].
        symex_reg HR3 (10%bv : reg) as E10'. symex_reg HR3 (8%bv : reg) as E8'. symex_reg HR3 (9%bv : reg) as E9'. symex_reg HR3 (18%bv : reg) as E18'.
        symex_reg HR3 (19%bv : reg) as E19'. symex_reg HR3 (20%bv : reg) as E20'. symex_reg HR3 (21%bv : reg) as E21'. symex_reg HR3 (2%bv : reg) as E2'.
        split; [exact E10'|]. split; [rewrite E8'; apply zw_neg_mod|]. split; [rewrite E9'; apply zw_neg_mod|]. split; [rewrite E18'; apply zw_neg_mod|].
        split; [rewrite E19'; apply zw_neg_mod|]. split; [rewrite E20'; apply zw_neg_mod|]. split; [rewrite E21'; apply zw_neg_mod|]. split; [rewrite E2'; f_equal; lia|].
        split.
        { intros rg Hrg. rewrite (Hfr3 rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity). rewrite (Bfr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity).
          rewrite (Afr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity). reflexivity. }
        subst M4 M3 M2.
        apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply UWFR_store; [exact MF1 | clear - HWB0 F2; lia | rewrite cbytes_length, Z2Nat.id by lia; clear - CWB HWN Hd F2; lia | right; right; rewrite cbytes_length, Z2Nat.id by lia; clear - HWN Hd F2; lia].
      + symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; pc6_uw_ret] []) 44%nat [true; true]
          [RVal (EVar 36%nat); RVal (ELit 32768); RVal (EVar 37%nat); RVal (ELit pc6_uw_ret); RVal (EVar 38%nat); RVal (EVar 39%nat); RVal (EVar 40%nat); RVal (EVar 41%nat); RVal (EVar 42%nat); RVal (EVar 44%nat)]
          [(2, EVar 32%nat); (19, EVar 33%nat); (9, EVar 35%nat); (18, EVar 43%nat); (20, EVar 35%nat)]
          [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (35%nat, 32768); (36%nat, 32769); (37%nat, 32769); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64); (42%nat, 2 ^ 64); (43%nat, 32769); (44%nat, 2 ^ 64)]
          NoRegions [cv_sp v - 256 - 64; cv_S v; 0; copy; is_wnext (uw_s1 s); is_whave (uw_s1 s); f8 mod 2 ^ 64; f9 mod 2 ^ 64; f18 mod 2 ^ 64; f19 mod 2 ^ 64; f20 mod 2 ^ 64; 32768 - is_wnext (uw_s1 s); f21 mod 2 ^ 64] NoVals F0 F0'
          (mkst R2 (Z_to_bv 64 0x217fc) M2 s6u_rom) R3 HR3 Hfr3 Hms3.
        all: try (unfold INF_FRAME in *; arm_side).
        all: try (rewrite B2; f_equal; lia).
        set (wn := is_wnext (uw_s1 s) + copy) in *.
        rewrite (wnext_sel wn) in Hms3 by (subst wn; clear - F2 Hc; lia).
        set (M3 := wbytes M2 (zw (cv_S v + 80)) (Z_to_le_bytes 4 (if wn =? 32768 then 0 else wn))) in Hms3.
        assert (HM3 : LMEM v (mkW (iset_wnext s2 (if wn =? 32768 then 0 else wn)) c r) M3).
        { apply (LMEM_store_scalar v C s2 c r _ M2 80 _ HM2); [lia | cbn; lia | exact Hput | | subst s2; destruct (uw_s1 s); reflexivity ..].
          apply (is6_upd_wnext M2 (cv_S v) _ s2 _ (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        exists R3, M3. split.
        { eapply msteps_trans; [by_run Hms1|]. eapply msteps_trans; [by_run Hms2|]. subst M3. by_run Hms3. }
        split; [exact HM3|].
        symex_reg HR3 (10%bv : reg) as E10'. symex_reg HR3 (8%bv : reg) as E8'. symex_reg HR3 (9%bv : reg) as E9'. symex_reg HR3 (18%bv : reg) as E18'.
        symex_reg HR3 (19%bv : reg) as E19'. symex_reg HR3 (20%bv : reg) as E20'. symex_reg HR3 (21%bv : reg) as E21'. symex_reg HR3 (2%bv : reg) as E2'.
        split; [exact E10'|]. split; [rewrite E8'; apply zw_neg_mod|]. split; [rewrite E9'; apply zw_neg_mod|]. split; [rewrite E18'; apply zw_neg_mod|].
        split; [rewrite E19'; apply zw_neg_mod|]. split; [rewrite E20'; apply zw_neg_mod|]. split; [rewrite E21'; apply zw_neg_mod|]. split; [rewrite E2'; f_equal; lia|].
        split.
        { intros rg Hrg. rewrite (Hfr3 rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity). rewrite (Bfr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity).
          rewrite (Afr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity). reflexivity. }
        subst M3 M2.
        apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply UWFR_store; [exact MF1 | clear - HWB0 F2; lia | rewrite cbytes_length, Z2Nat.id by lia; clear - CWB HWN Hd F2; lia | right; right; rewrite cbytes_length, Z2Nat.id by lia; clear - HWN Hd F2; lia].
  Qed.
  Lemma uw_big6 : forall s c r R M pend copy f8 f9 f18 f19 f20 f21,
    cv_WN v = 32768 -> LMEM v (mkW s c r) M -> LX v (mkW s c r) -> 0 <= ir_put r <= cv_NO v ->
    arr_len (is_window s) = 32768 -> (is_wsize s = 0 \/ is_wsize s = 32768) ->
    0 <= is_wnext s /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s) -> 0 <= is_whave s /\ (is_wsize s <> 0 -> is_whave s <= is_wsize s) ->
    32768 <= copy < 2 ^ 31 -> copy <= ir_put r ->
    (forall i, 0 <= i < cv_NO v -> 0 <= arr_get (ic_outbuf c) i < 256) -> pend = cv_P0 v + ir_put r ->
    JUW R M pend copy f8 f9 f18 f19 f20 f21 ->
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) (mkst R' (Z_to_bv 64 pc6_uw_ret) M' s6u_rom)
      /\ LMEM v (mkW (uwc s (ic_outbuf c) (ir_put r) copy) c r) M'
      /\ getr R' 10 = zw 0 /\ getr R' 8 = zw f8 /\ getr R' 9 = zw f9 /\ getr R' 18 = zw f18 /\ getr R' 19 = zw f19 /\ getr R' 20 = zw f20
      /\ getr R' 21 = zw f21 /\ getr R' 2 = zw spi
      /\ (forall rg, reg_in rg uw_clob = false -> getr R' rg = getr R rg)
      /\ UWFR M M'.
  Proof.
    intros s c r R M pend copy f8 f9 f18 f19 f20 f21 HWN HM HX Hput Hwl Hws Hwn Hwh Hc Hcp Houtb Hpend HJ.
    destruct HJ as ((G8 & G9 & G19 & G2) & G10 & (F8c & F16 & F24 & F32 & F40 & F48 & F56)).
    open_ictx C.
    assert (HW : cv_WN v = 32768 /\ 0 < cv_WB v /\ cv_WB v mod 16 = 0) by (clear - CWB HWN; lia). destruct HW as (_ & HWB0 & _).
    pose proof (uw_s1_facts s Hws Hwn Hwh) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8l & F9w & F10c).
    unfold uwc. replace (32768 <=? copy) with true by (symmetry; apply Z.leb_le; clear - Hc; lia).
    assert (SEGA : exists R1 M1,
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) (mkst R1 (Z_to_bv 64 A6U_MEMCPY) M1 s6u_rom)
      /\ getr R1 10 = zw (cv_WB v) /\ getr R1 11 = zw (pend - 32768) /\ getr R1 12 = zw 32768 /\ getr R1 1 = zw 0x21878
      /\ uw_regs R1 pend copy
      /\ (forall rg, reg_in rg [1; 10; 11; 12]%bv = false -> getr R1 rg = getr R rg)
      /\ LMEM v (mkW (uw_s1 s) c r) M1 /\ UWF M1 f8 f9 f18 f19 f20 f21 /\ UWFR M M1).
    { pose proof HM as HM'. open_lmem HM'. open_lx HX. unfold mapped in *.
      pose proof (is6_wsize _ _ _ _ Msc) as C60. pose proof (is6_wbits _ _ _ _ Msc) as C56. rewrite Xwbits in C56.
      destruct Hws as [W0 | W1].
      - rewrite W0 in C60.
        assert (Es1 : uw_s1 s = iset_whave (iset_wnext (iset_wsize s 32768) 0) 0) by (unfold uw_s1; rewrite W0; reflexivity).
        symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; 0x21888] []) 50%nat [true; false; false; false]
          [RVal (ELit 0); RVal (ELit 15)]
          [(2, EVar 32%nat); (19, EVar 33%nat); (8, EVar 34%nat); (9, EVar 35%nat); (10, EVar 36%nat)]
          [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 31); (36%nat, 2 ^ 63)]
          NoRegions [spi - 64; cv_S v; pend; copy; cv_WB v] NoVals F0 F0'
          (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) R1 HR1 Hfr Hms.
        all: try (unfold INF_FRAME in *; arm_side).
        all: try uw_ub_side.
        all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT_BIGA0" G end.
        set (M0 := wbytes M (zw (cv_S v + 72)) (Z_to_le_bytes 4 32768)) in Hms.
        set (M1a := wbytes M0 (zw (cv_S v + 76)) (Z_to_le_bytes 4 0)) in Hms. set (M1 := wbytes M1a (zw (cv_S v + 80)) (Z_to_le_bytes 4 0)) in Hms.
        assert (HM0 : LMEM v (mkW (iset_wsize s 32768) c r) M0).
        { apply (LMEM_store_scalar v C s c r _ M 72 _ HM); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_wsize M (cv_S v) _ s 32768 Msc); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        assert (HM1 : LMEM v (mkW (uw_s1 s) c r) M1).
        { rewrite Es1. replace (iset_whave (iset_wnext (iset_wsize s 32768) 0) 0) with (iset_wnext (iset_whave (iset_wsize s 32768) 0) 0) by (destruct s; reflexivity).
          assert (HM1a : LMEM v (mkW (iset_whave (iset_wsize s 32768) 0) c r) M1a).
          { apply (LMEM_store_scalar v C _ c r _ M0 76 _ HM0); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
            apply (is6_upd_whave M0 (cv_S v) _ _ 0 (lm_sc _ _ _ HM0)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
          apply (LMEM_store_scalar v C _ c r _ M1a 80 _ HM1a); [lia | cbn; lia | exact Hput | | reflexivity | reflexivity | reflexivity | reflexivity].
          apply (is6_upd_wnext M1a (cv_S v) _ _ 0 (lm_sc _ _ _ HM1a)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
        exists R1, M1. split; [subst M1 M1a M0; by_run Hms|].
        symex_reg HR1 (10%bv : reg) as G10'. symex_reg HR1 (11%bv : reg) as G11'. symex_reg HR1 (12%bv : reg) as G12'. symex_reg HR1 (1%bv : reg) as G1'.
        split; [rewrite G10'; f_equal; lia|]. split; [rewrite G11'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|].
        split; [rewrite G12'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|]. split; [exact G1'|].
        split; [unfold uw_regs; regs_via Hfr|]. split; [fr_weak Hfr|]. split; [exact HM1|].
        split.
        { unfold UWF. subst M1 M1a M0. unfold INF_FRAME in *.
          repeat match goal with |- _ /\ _ => split end;
            (eapply cell_write_other; [eapply cell_write_other; [eapply cell_write_other; [eassumption | lia | cbn; lia | lia | cbn; lia | sep_side] | lia | cbn; lia | lia | cbn; lia | sep_side] | lia | cbn; lia | lia | cbn; lia | sep_side]). }
        subst M1 M1a M0.
        apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
        apply UWFR_store; [apply UWFR_refl | clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
      - rewrite W1 in C60.
        assert (Es1 : uw_s1 s = s) by (unfold uw_s1; rewrite W1; reflexivity). rewrite Es1.
        symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; 0x21888] []) 50%nat [false; true; false]
          [RVal (ELit 32768)]
          [(2, EVar 32%nat); (19, EVar 33%nat); (8, EVar 34%nat); (9, EVar 35%nat); (10, EVar 36%nat)]
          [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (34%nat, 2 ^ 63); (35%nat, 2 ^ 31); (36%nat, 2 ^ 63)]
          NoRegions [spi - 64; cv_S v; pend; copy; cv_WB v] NoVals F0 F0'
          (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) R1 HR1 Hfr Hms.
        all: try (unfold INF_FRAME in *; arm_side).
        all: try uw_ub_side.
        all: match goal with |- exists _ _, _ => idtac | |- ?G => idtac "LEFT_BIGA1" G end.
        exists R1, M. split; [by_run Hms|].
        symex_reg HR1 (10%bv : reg) as G10'. symex_reg HR1 (11%bv : reg) as G11'. symex_reg HR1 (12%bv : reg) as G12'. symex_reg HR1 (1%bv : reg) as G1'.
        split; [rewrite G10'; f_equal; lia|]. split; [rewrite G11'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|].
        split; [rewrite G12'; rewrite ?Z.mod_small by (clear - Hc; lia); f_equal; lia|]. split; [exact G1'|].
        split; [unfold uw_regs; regs_via Hfr|]. split; [fr_weak Hfr|]. split; [exact HM|].
        split; [unfold UWF; repeat (split; [assumption|]); assumption|]. apply UWFR_refl. }
    destruct SEGA as (R1 & M1 & Hms1 & A10 & A11 & A12 & A1 & AU & Afr & HM1 & HF1 & MF1).
    assert (Hwl1 : arr_len (is_window (uw_s1 s)) = 32768) by (rewrite F5; exact Hwl).
    pose proof (lm_out _ _ _ HM1) as Mout1. cbn [w_c w_r] in Mout1.
    pose proof (cells_rdn_bytes s6u_segs M1 (cv_P0 v) (ir_put r) (arr_get (ic_outbuf c)) (ir_put r - 32768) (Z.to_nat 32768) Mout1
                  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hsrc.
    pose proof (lm_map_W _ _ _ HM1 ltac:(lia)) as MW1. cbn in MW1.
    destruct (MEMCPY _ R1 (cv_WB v) (cv_P0 v + (ir_put r - 32768)) (Z.to_nat 32768) _ (zw 0x21878) Hsrc
               ltac:(clear - HWB0; lia) ltac:(clear - CWB HWN; lia) ltac:(clear - CP0 Hcp Hput Hc; lia) ltac:(clear - CP0 Hcp Hput Hc; lia))
      as (R2 & Hms2 & _ & Bfr).
    { specialize (CPW ltac:(clear - Hcp Hput Hc; lia)). unfold sep in CPW. clear - CPW Hcp Hput Hc CP0 HWN. lia. }
    { intros x Hx. apply MW1. clear - Hx HWN. lia. }
    { apply ret_ok_lit; [lia | reflexivity]. }
    { exact A1. }
    { exact A10. }
    { change (reg_get R1 11) with (getr R1 11). rewrite A11; f_equal; lia. }
    { change (reg_get R1 12) with (getr R1 12). rewrite A12; f_equal; lia. }
    set (M2 := wbytes M1 (zw (cv_WB v)) (cbytes (arr_get (ic_outbuf c)) (ir_put r - 32768) (Z.to_nat 32768))) in Hms2.
    set (s2 := iset_window (uw_s1 s) (arr_blit (is_window (uw_s1 s)) 0 (ic_outbuf c) (ir_put r - 32768) 32768)).
    assert (HM2 : LMEM v (mkW s2 c r) M2).
    { subst M2 s2. pose proof (LMEM_blit_win v C (uw_s1 s) c r (Z.to_nat 32768) 0 (ir_put r - 32768) M1 HM1 HWN Hwl1 ltac:(lia)
                    ltac:(lia) ltac:(clear - Hcp Hc; lia) ltac:(lia) (proj2 Hput) Houtb) as X.
      rewrite Z.add_0_r in X. exact X. }
    assert (HF2 : UWF M2 f8 f9 f18 f19 f20 f21).
    { subst M2. unfold UWF in *. unfold INF_FRAME in *. destruct HF1 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
      repeat match goal with |- _ /\ _ => split end;
        (eapply cell_write_other; [eassumption | lia | cbn; lia | clear - HWB0; lia | rewrite cbytes_length; clear - CWB HWN; lia
                                   | rewrite cbytes_length; unfold sep in CfW; clear - CfW Csp CWB HWN; lia]). }
    assert (B19 : getr R2 19 = zw (cv_S v)) by (rewrite (Bfr (19%bv : reg) eq_refl); exact (proj1 (proj2 (proj2 AU)))).
    assert (B2 : getr R2 2 = zw (spi - 64)) by (rewrite (Bfr (2%bv : reg) eq_refl); exact (proj2 (proj2 (proj2 AU)))).
    pose proof HM2 as HM2'. open_lmem HM2'. unfold mapped in *.
    pose proof (is6_wsize _ _ _ _ Msc) as C60.
    replace (is_wsize s2) with 32768 in C60 by (subst s2; rewrite <- F1; destruct (uw_s1 s); reflexivity).
    destruct HF2 as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7). unfold INF_FRAME in *.
    pose proof (lm_map_S _ _ _ HM2) as MS2. pose proof (lm_map_f _ _ _ HM2) as Mf2. unfold mapped, INF_FRAME, INF_SCRATCH in MS2, Mf2.
    replace (cv_sp v - 256 - 8) with (cv_sp v - 256 - 64 + 56) in Q1 by lia.
    replace (cv_sp v - 256 - 16) with (cv_sp v - 256 - 64 + 48) in Q2 by lia.
    replace (cv_sp v - 256 - 24) with (cv_sp v - 256 - 64 + 40) in Q3 by lia.
    replace (cv_sp v - 256 - 32) with (cv_sp v - 256 - 64 + 32) in Q4 by lia.
    replace (cv_sp v - 256 - 40) with (cv_sp v - 256 - 64 + 24) in Q5 by lia.
    replace (cv_sp v - 256 - 48) with (cv_sp v - 256 - 64 + 16) in Q6 by lia.
    replace (cv_sp v - 256 - 56) with (cv_sp v - 256 - 64 + 8) in Q7 by lia.
    symex s6u_segs (CFG [] [] [ELit pc6_uw_ret] [A6U_MEMCPY; pc6_uw_ret] []) 30%nat (@nil bool)
      [RVal (ELit 32768); RVal (ELit pc6_uw_ret); RVal (EVar 36%nat); RVal (EVar 37%nat); RVal (EVar 38%nat); RVal (EVar 39%nat); RVal (EVar 40%nat); RVal (EVar 41%nat)]
      [(2, EVar 32%nat); (19, EVar 33%nat)]
      [(32%nat, 2 ^ 63); (33%nat, 2 ^ 63); (36%nat, 2 ^ 64); (37%nat, 2 ^ 64); (38%nat, 2 ^ 64); (39%nat, 2 ^ 64); (40%nat, 2 ^ 64); (41%nat, 2 ^ 64)]
      NoRegions [cv_sp v - 256 - 64; cv_S v; 0; 0; f8 mod 2 ^ 64; f9 mod 2 ^ 64; f18 mod 2 ^ 64; f19 mod 2 ^ 64; f20 mod 2 ^ 64; f21 mod 2 ^ 64] NoVals F0 F0'
      (mkst R2 (Z_to_bv 64 0x21878) M2 s6u_rom) R5 HR5 Hfr5 Hms5.
    all: try (unfold INF_FRAME in *; arm_side).
    all: try (rewrite B2; f_equal; lia).
    all: lazymatch goal with |- @ex _ _ => idtac | |- ?G => idtac "LEFT_BIG" G end.
    set (M5 := wbytes M2 (zw (cv_S v + 76)) (Z_to_le_bytes 4 32768)) in Hms5.
    set (M6 := wbytes M5 (zw (cv_S v + 80)) (Z_to_le_bytes 4 0)) in Hms5.
    assert (HM5 : LMEM v (mkW (iset_whave s2 32768) c r) M5).
    { apply (LMEM_store_scalar v C s2 c r _ M2 76 _ HM2); [lia | cbn; lia | exact Hput | | destruct s2; reflexivity ..].
      apply (is6_upd_whave M2 (cv_S v) _ s2 32768 (lm_sc _ _ _ HM2)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    assert (HM6 : LMEM v (mkW (iset_wnext (iset_whave s2 32768) 0) c r) M6).
    { apply (LMEM_store_scalar v C _ c r _ M5 80 _ HM5); [lia | cbn; lia | exact Hput | | destruct s2; reflexivity ..].
      apply (is6_upd_wnext M5 (cv_S v) _ _ 0 (lm_sc _ _ _ HM5)); [clear - CS; lia | clear - CS; unfold is6_SIZE; lia]. }
    exists R5, M6. split.
    { eapply msteps_trans; [by_run Hms1|]. eapply msteps_trans; [by_run Hms2|]. subst M6 M5. by_run Hms5. }
    split; [replace (iset_whave (iset_wnext s2 0) 32768) with (iset_wnext (iset_whave s2 32768) 0) by (clear; destruct s2; reflexivity); exact HM6|].
    symex_reg HR5 (10%bv : reg) as E10'. symex_reg HR5 (8%bv : reg) as E8'. symex_reg HR5 (9%bv : reg) as E9'. symex_reg HR5 (18%bv : reg) as E18'.
    symex_reg HR5 (19%bv : reg) as E19'. symex_reg HR5 (20%bv : reg) as E20'. symex_reg HR5 (21%bv : reg) as E21'. symex_reg HR5 (2%bv : reg) as E2'.
    split; [exact E10'|]. split; [rewrite E8'; apply zw_neg_mod|]. split; [rewrite E9'; apply zw_neg_mod|]. split; [rewrite E18'; apply zw_neg_mod|].
    split; [rewrite E19'; apply zw_neg_mod|]. split; [rewrite E20'; apply zw_neg_mod|]. split; [rewrite E21'; apply zw_neg_mod|]. split; [rewrite E2'; f_equal; lia|].
    split.
    { intros rg Hrg. rewrite (Hfr5 rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity).
      rewrite (Bfr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity).
      rewrite (Afr rg) by (eapply reg_in_sub; [| exact Hrg]; reflexivity). reflexivity. }
    subst M6 M5 M2.
    apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
    apply UWFR_store; [| clear - CS; lia | clear - CS; cbn; lia | right; left; clear; cbn; lia].
    apply UWFR_store; [exact MF1 | clear - HWB0; lia | rewrite cbytes_length; clear - CWB HWN; lia | right; right; rewrite cbytes_length; clear - HWN; lia].
  Qed.

  Lemma uw_all6 : forall s c r R M pend copy f8 f9 f18 f19 f20 f21,
    cv_WN v = 32768 -> LMEM v (mkW s c r) M -> LX v (mkW s c r) -> 0 <= ir_put r <= cv_NO v ->
    arr_len (is_window s) = 32768 -> (is_wsize s = 0 \/ is_wsize s = 32768) ->
    0 <= is_wnext s /\ (is_wsize s <> 0 -> is_wnext s <= is_wsize s) -> 0 <= is_whave s /\ (is_wsize s <> 0 -> is_whave s <= is_wsize s) ->
    (is_wsize s <> 0 -> is_whave s < is_wsize s -> is_wnext s = is_whave s) ->
    0 <= copy < 2 ^ 31 -> copy <= ir_put r ->
    (forall i, 0 <= i < cv_NO v -> 0 <= arr_get (ic_outbuf c) i < 256) -> pend = cv_P0 v + ir_put r ->
    JUW R M pend copy f8 f9 f18 f19 f20 f21 ->
    exists R' M',
      msteps s6u_segs (mkst R (Z_to_bv 64 pc6_uwj) M s6u_rom) (mkst R' (Z_to_bv 64 pc6_uw_ret) M' s6u_rom)
      /\ LMEM v (mkW (uwc s (ic_outbuf c) (ir_put r) copy) c r) M'
      /\ getr R' 10 = zw 0 /\ getr R' 8 = zw f8 /\ getr R' 9 = zw f9 /\ getr R' 18 = zw f18 /\ getr R' 19 = zw f19 /\ getr R' 20 = zw f20
      /\ getr R' 21 = zw f21 /\ getr R' 2 = zw spi
      /\ (forall rg, reg_in rg uw_clob = false -> getr R' rg = getr R rg)
      /\ UWFR M M'.
  Proof.
    intros s c r R M pend copy f8 f9 f18 f19 f20 f21 HWN HM HX Hput Hwl Hws Hwn Hwh Hwhn Hc Hcp Houtb Hpend HJ.
    destruct (Z_lt_le_dec copy 32768) as [Hsm|Hbg].
    - apply (uw_body6 s c r R M pend copy f8 f9 f18 f19 f20 f21); try assumption. lia.
    - apply (uw_big6 s c r R M pend copy f8 f9 f18 f19 f20 f21); try assumption. lia.
  Qed.
End UpdWin.
End FXG.
