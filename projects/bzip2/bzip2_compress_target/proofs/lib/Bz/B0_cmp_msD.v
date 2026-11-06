(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV B0_cmp_gtu B0_cmp_msW.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Definition gtU_apostZ (ra : word) (spz : Z) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (A2 Bud : Z) (a2 : zarr) (r : bool * Z) (lo : Z)
    (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 x12 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 x12 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom b0segs)
    /\ munch [(Bud, Bud + 4); (spz - 32, spz)]%Z m m' /\ wmono b0segs m m' /\ mem_inv b0segs m'
    /\ stk b0segs m' lo spz
    /\ a0 = Z_to_bv 64 (Z.b2z (fst r))
    /\ u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) /\ rw_cells b0segs m' Bud [C4 (Z_to_bv 64 (snd r))].

Lemma B0_mainGtU_Z : forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (A2 qoff n i1 i2 budget Bud lo spz : Z) (a2z : zarr),
  (0 <= spz < 18446744073709551616)%Z ->
  a0 = Z_to_bv 64 i1 -> a1 = Z_to_bv 64 i2 -> a2 = Z_to_bv 64 A2 -> a3 = Z_to_bv 64 (A2 + qoff) -> a4 = Z_to_bv 64 n -> a5 = Z_to_bv 64 Bud ->
  u8arr b0segs m A2 (zb8 a2z ARR2_SIZE) -> rw_cells b0segs m Bud [C4 (Z_to_bv 64 budget)] -> mem_inv b0segs m ->
  zbok a2z -> (0 <= i1 <= n + 14)%Z -> (0 <= i2 <= n + 14)%Z -> (10000 <= n <= NBLOCKMAX + 19)%Z -> (n + 34 <= qoff <= n + 35)%Z ->
  ((A2 + qoff) mod 2 = 0)%Z -> (0 < A2)%Z -> (A2 + ARR2_SIZE <= CEIL)%Z -> (0 < Bud)%Z -> (Bud + 4 <= 18446744073709551616)%Z -> (Bud mod 4 = 0)%Z ->
  apart A2 ARR2_SIZE Bud 4 ->
  (-2147483648 <= snd (mainGtU i1 i2 a2z qoff n budget))%Z -> (budget < 2147483648)%Z ->
  stk b0segs m lo spz -> (lo + 32 <= spz)%Z ->
  (spz <= A2 \/ A2 + ARR2_SIZE <= spz - 32)%Z -> (spz <= Bud \/ Bud + 4 <= spz - 32)%Z ->
  aconsts B0C m -> (0x62b000 <= lo)%Z -> (0x62b000 <= A2)%Z -> (0x62b000 <= Bud)%Z ->
  shzW b0segs [(Bud, Bud + 4); (spz - 32, spz)]%Z m A2 (A2 + ARR2_SIZE) -> shpW b0segs [(Bud, Bud + 4); (spz - 32, spz)]%Z m Bud (Bud + 4) ->
  evt b0segs (gtU_apostZ ra spz gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A2 Bud a2z (mainGtU i1 i2 a2z qoff n budget) lo m)
      (MS (mkR ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0xa70c4) fc None m (seg_rom b0segs)).
Proof.
  intros ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m A2 qoff n i1 i2 budget Bud lo spz a2z Hsp.
  pose proof (B0_mainGtU ra (Z_to_bv 64 spz) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                         A2 qoff n i1 i2 budget Bud lo a2z) as G.
  cbv zeta in G. cbn [aci_segs aci_c ci_segs B0C aci_hi ci_hi ci_mainGtU] in G. unfold gtU_apostF in G.
  rewrite (unsigned_lit spz) in G by lia. exact G.
Qed.

Section B0MS.
  Variable X : msenv. Variable Y : amenv. Variables SHF SHn : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok X. Hypothesis XSEP : msenv_sep X. Hypothesis YOK : amenv_ok X Y.
  (* [comment removed for export] *)
  Variables (w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 w480 : word).
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y).
  Notation A1 := (me_A1 X). Notation A2 := (me_A2 X). Notation FT := (me_FT X). Notation n := (me_n X). Notation qo := (me_qo X).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WSH := [(A1, A1 + ARR1_SIZE); (P + 496, P + 500); (P - 32, P)]%Z.
  (* [comment removed for export] *)
  Notation SLD := (slm_cells X Y SHF SHn (mkSLQ w80 w88 w96 w104 w160 w168 w176 w184 w224 w232 w240 w248 w264 w272 w312 w328 w336 w344 w352 w392 w408 w416 (Z_to_bv 64 0) w480)).
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac rdptr AR1 AOK idx :=
    lazymatch type of AR1 with u8arr ?segs ?mm ?A (zb8 ?a ?nn) =>
      let RD := fresh "RD" in
      pose proof (zb8_read4 segs mm A a nn idx _ AR1 ltac:(lia) ltac:(lia) AOK ltac:(unfold wa; f_equal; lia)) as RD;
      wstep; clear RD; try rewrite (sx32_of_Z (rd32 a idx)) by lia
    end.
  (* [comment removed for export] *)
  Ltac sw_ptr AR1 j v :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of AR1 with u8arr ?segs mm ?A (zb8 ?a ?nn) =>
        let SO := fresh "SO" in
        assert (SO : store_ok segs mm (wa (A + 4 * j)) 4 = true)
          by (eapply (u8arr_storeN_ok segs mm A _ (4 * j) 4 _ AR1); [lia| rewrite zb8_length_nat; lia| unfold wa; f_equal; lia]);
        wstep;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mm ?ad (le4 ?w)) _) =>
          let H := fresh "ARw" in
          pose proof (zb8_write4 segs mm A a nn j w AR1 ltac:(lia) ltac:(lia)) as H; clear AR1; store_done; rename H into AR1;
          rewrite unsigned_lit in AR1 by lia;
          lazymatch type of AR1 with u8arr _ _ _ (zb8 (wr32 _ _ ?x) _) => replace x with v in AR1 by lia end
        end; try clear SO end end.

  (* [comment removed for export] *)
  Lemma B0_shift1 : forall (d h lo hi v : Z) (a2 : zarr) (f : nat) (j : Z) (a1 : zarr) (b : Z)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x20 x21 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= j <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= v < n)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (j - lo < h * Z.of_nat f)%Z ->
    (-2147483648 < snd (mss_shift f a1 a2 qo n d h lo j v b))%Z -> (b < 2147483648)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> rw_cells b0segs m P SLD ->
    rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P -> mem_inv b0segs m ->
    munch WSH me m -> wmono b0segs me m ->
    acoW WSH me ->
    shzW b0segs WSH me A1 (A1 + ARR1_SIZE) -> shzW b0segs WSH me A2 (A2 + ARR2_SIZE) -> shpW b0segs WSH me (P + 496) (P + 500) ->
    (forall m' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x28' x29' x30' x31' : word),
      let r := mss_shift f a1 a2 qo n d h lo j v b in let a1' := fst (fst r) in let j' := snd (fst r) in let b' := snd r in
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> rw_cells b0segs m' P SLD ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' ->
      munch WSH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (lo <= j' <= j)%Z -> (-2147483648 < b' <= b)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            (Z_to_bv 64 (snd (fst (mss_shift f a1 a2 qo n d h lo j v b)))) x19' (Z_to_bv 64 (A1 + 4 * snd (fst (mss_shift f a1 a2 qo n d h lo j v b)))) x21' (Z_to_bv 64 (lo + h - 1))
                            (Z_to_bv 64 (snd (fst (mss_shift f a1 a2 qo n d h lo j v b)))) (Z_to_bv 64 d) (Z_to_bv 64 (v + d)) (Z_to_bv 64 h) cSB
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa33d8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 j) x19 x20 x21 (Z_to_bv 64 (lo + h - 1)) x23 (Z_to_bv 64 d) (Z_to_bv 64 (v + d)) (Z_to_bv 64 h) cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa3298) fc None m (seg_rom b0segs)).
  Proof.
    intros d h lo hi v a2. induction f as [|f IH]; [intros; lia|].
    intros j a1 b x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x20 x21 x28 x29 x30 x31 me m
           Hh Hlo Hj Hhi Hd Hv A1OK A2OK PR Hf BL BH AR1 AR2 SLB BUD STK MI MU WM ACW SH1 SH2 SHB K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params. pose proof alloc_ceiling_range as ACR. open_slb_in SLB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR (j - h)%Z ltac:(lia)) as Pjh. set (pv := rd32 a1 (j - h)) in Pjh.
    pose proof (mss_shift_budget_le (S f) a1 a2 qo n d h lo j v b) as BLE.
    pose proof (mss_shift_budget_le_gtu f a1 a2 qo n d h lo j v b) as BG. fold pv in BG.
    pose proof BL as BL2. rewrite mss_shift_S in K, BL2, BLE. fold pv in K. fold pv in BL2. fold pv in BLE.
    pose proof (mainGtU_budget_le (pv + d) (v + d) a2 qo n b) as GL.
    destruct (mainGtU (pv + d) (v + d) a2 qo n b) as [gt b1] eqn:GT. cbn [fst snd] in BG, GL.
    assert (Epv : rd32 a1 (j - h) = pv) by reflexivity. clearbody pv.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
    (* [comment removed for export] *)
    brun_to 0xa330c%Z. wstep.
    pose proof (ACW m MU) as AC.
    call (B0_mainGtU_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ A2 qo n (pv + d)%Z (v + d)%Z b (P + 496)%Z (me_lo X) P a2);
      [lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AR2| exact BUD| exact MI| exact A2OK
      | lia| lia| bz_params; lia| lia| lia| lia| bz_ceil; bz_params; unfold CEIL; lia| lia| lia| lia| unfold apart; lia
      | rewrite GT; cbn [snd]; lia| lia| exact STK| lia| lia| lia| exact AC| lia| lia| lia
      | eapply (shzW_sub b0segs _ _ me m); [exact SH2| exact MU| sub_fp_solve| lia| lia]
      | eapply (shpW_sub b0segs _ _ me m); [exact SHB| exact MU| sub_fp_solve| lia| lia] | ].
    clear AC. rewrite GT in *. cbn [fst snd] in *.
    match goal with H : ?x = Z_to_bv 64 (Z.b2z gt) |- _ => subst x end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    match goal with H : rw_cells _ _ (P + 496)%Z _ |- _ => rename H into BUD end.
    match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
    match goal with H : u8arr _ ?mm A2 (zb8 a2 ARR2_SIZE), H' : u8arr _ ?mm A2 (zb8 a2 ARR2_SIZE) |- _ => clear H' end.
    (* [comment removed for export] *)
    destruct gt; cbn [Z.b2z] in *.
    - (* [comment removed for export] *)
      brun. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
      brun. sw_ptr AR1 j pv.
      set (a1a := wr32 a1 j pv) in *.
      assert (A1OKa : zbok a1a) by (subst a1a; apply zbok_wr32; exact A1OK).
      assert (PRa : pr n a1a 0 (n - 1)).
      { intros y Hy. subst a1a. pose proof (PR y Hy). destruct (Z.eq_dec y j) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
      (* [comment removed for export] *)
      brun. if_cases Kc; zify_cond_z Kc.
      + replace (j - h <=? lo + h - 1) with false in K, BL2 by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z a1a b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me);
          [st_eq| lia| lia| lia| lia| lia| lia| exact A1OKa| exact A2OK| exact PRa| lia| exact BL2| lia
          | exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact ACW| exact SH1| exact SH2| exact SHB|].
        intros m' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x19' x21' x28' x29' x30' x31'. cbv zeta.
        intros AR1' AR2' SLB' BUD' STK' MI' MU' WM' OK' PR' J' B'.
        eapply (K m'); [exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia].
      + replace (j - h <=? lo + h - 1) with true in K, BL2 by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K, BL2.
        (* [comment removed for export] *)
        brun_to 0xa33d8%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OKa| exact PRa| lia| lia].
    - (* [comment removed for export] *)
      cbn [fst snd] in K, BL2.
      brun_to 0xa33d8%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_shift2 : forall (d h lo hi v : Z) (a2 : zarr) (f : nat) (j : Z) (a1 : zarr) (b : Z)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= j <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= v < n)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (j - lo < h * Z.of_nat f)%Z ->
    (-2147483648 < snd (mss_shift f a1 a2 qo n d h lo j v b))%Z -> (b < 2147483648)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> rw_cells b0segs m P SLD ->
    rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P -> mem_inv b0segs m ->
    munch WSH me m -> wmono b0segs me m ->
    acoW WSH me ->
    shzW b0segs WSH me A1 (A1 + ARR1_SIZE) -> shzW b0segs WSH me A2 (A2 + ARR2_SIZE) -> shpW b0segs WSH me (P + 496) (P + 500) ->
    (forall m' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x21' x28' x29' x30' x31' : word),
      let r := mss_shift f a1 a2 qo n d h lo j v b in let a1' := fst (fst r) in let j' := snd (fst r) in let b' := snd r in
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> rw_cells b0segs m' P SLD ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' ->
      munch WSH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (lo <= j' <= j)%Z -> (-2147483648 < b' <= b)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' (Z_to_bv 64 n) (Z_to_bv 64 (A1 + 4 * snd (fst (mss_shift f a1 a2 qo n d h lo j v b)))) x21' (Z_to_bv 64 (lo + h - 1))
                            (Z_to_bv 64 (snd (fst (mss_shift f a1 a2 qo n d h lo j v b)))) (Z_to_bv 64 d) (Z_to_bv 64 (v + d)) (Z_to_bv 64 h) cSB
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa35c8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 (Z_to_bv 64 n) x20 x21 (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 j) (Z_to_bv 64 d) (Z_to_bv 64 (v + d)) (Z_to_bv 64 h) cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa3490) fc None m (seg_rom b0segs)).
  Proof.
    intros d h lo hi v a2. induction f as [|f IH]; [intros; lia|].
    intros j a1 b x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31 me m
           Hh Hlo Hj Hhi Hd Hv A1OK A2OK PR Hf BL BH AR1 AR2 SLB BUD STK MI MU WM ACW SH1 SH2 SHB K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params. pose proof alloc_ceiling_range as ACR. open_slb_in SLB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR (j - h)%Z ltac:(lia)) as Pjh. set (pv := rd32 a1 (j - h)) in Pjh.
    pose proof (mss_shift_budget_le (S f) a1 a2 qo n d h lo j v b) as BLE.
    pose proof (mss_shift_budget_le_gtu f a1 a2 qo n d h lo j v b) as BG. fold pv in BG.
    pose proof BL as BL2. rewrite mss_shift_S in K, BL2, BLE. fold pv in K. fold pv in BL2. fold pv in BLE.
    pose proof (mainGtU_budget_le (pv + d) (v + d) a2 qo n b) as GL.
    destruct (mainGtU (pv + d) (v + d) a2 qo n b) as [gt b1] eqn:GT. cbn [fst snd] in BG, GL.
    assert (Epv : rd32 a1 (j - h) = pv) by reflexivity. clearbody pv.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
    (* [comment removed for export] *)
    brun_to 0xa3500%Z. wstep.
    pose proof (ACW m MU) as AC.
    call (B0_mainGtU_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ A2 qo n (pv + d)%Z (v + d)%Z b (P + 496)%Z (me_lo X) P a2);
      [lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AR2| exact BUD| exact MI| exact A2OK
      | lia| lia| bz_params; lia| lia| lia| lia| bz_ceil; bz_params; unfold CEIL; lia| lia| lia| lia| unfold apart; lia
      | rewrite GT; cbn [snd]; lia| lia| exact STK| lia| lia| lia| exact AC| lia| lia| lia
      | eapply (shzW_sub b0segs _ _ me m); [exact SH2| exact MU| sub_fp_solve| lia| lia]
      | eapply (shpW_sub b0segs _ _ me m); [exact SHB| exact MU| sub_fp_solve| lia| lia] | ].
    clear AC. rewrite GT in *. cbn [fst snd] in *.
    match goal with H : ?x = Z_to_bv 64 (Z.b2z gt) |- _ => subst x end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    match goal with H : rw_cells _ _ (P + 496)%Z _ |- _ => rename H into BUD end.
    match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
    match goal with H : u8arr _ ?mm A2 (zb8 a2 ARR2_SIZE), H' : u8arr _ ?mm A2 (zb8 a2 ARR2_SIZE) |- _ => clear H' end.
    (* [comment removed for export] *)
    destruct gt; cbn [Z.b2z] in *.
    - (* [comment removed for export] *)
      brun. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
      brun. sw_ptr AR1 j pv.
      set (a1a := wr32 a1 j pv) in *.
      assert (A1OKa : zbok a1a) by (subst a1a; apply zbok_wr32; exact A1OK).
      assert (PRa : pr n a1a 0 (n - 1)).
      { intros y Hy. subst a1a. pose proof (PR y Hy). destruct (Z.eq_dec y j) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
      (* [comment removed for export] *)
      brun. if_cases Kc; zify_cond_z Kc.
      + replace (j - h <=? lo + h - 1) with false in K, BL2 by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z a1a b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me);
          [st_eq| lia| lia| lia| lia| lia| lia| exact A1OKa| exact A2OK| exact PRa| lia| exact BL2| lia
          | exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact ACW| exact SH1| exact SH2| exact SHB|].
        intros m' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x21' x28' x29' x30' x31'. cbv zeta.
        intros AR1' AR2' SLB' BUD' STK' MI' MU' WM' OK' PR' J' B'.
        eapply (K m'); [exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia].
      + replace (j - h <=? lo + h - 1) with true in K, BL2 by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K, BL2.
        (* [comment removed for export] *)
        brun_to 0xa35c8%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OKa| exact PRa| lia| lia].
    - (* [comment removed for export] *)
      cbn [fst snd] in K, BL2.
      brun_to 0xa35c8%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_shift3 : forall (d h lo hi v : Z) (a2 : zarr) (f : nat) (j : Z) (a1 : zarr) (b : Z)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31 : word) (me m : word -> option byte),
    (1 <= h)%Z -> (0 <= lo)%Z -> (lo + h <= j <= hi)%Z -> (hi < n)%Z -> (0 <= d <= 15)%Z -> (0 <= v < n)%Z ->
    zbok a1 -> zbok a2 -> pr n a1 0 (n - 1) -> (j - lo < h * Z.of_nat f)%Z ->
    (-2147483648 < snd (mss_shift f a1 a2 qo n d h lo j v b))%Z -> (b < 2147483648)%Z ->
    u8arr b0segs m A1 (zb8 a1 ARR1_SIZE) -> u8arr b0segs m A2 (zb8 a2 ARR2_SIZE) -> rw_cells b0segs m P SLD ->
    rw_cells b0segs m (P + 496) [C4 (Z_to_bv 64 b)] -> stk b0segs m (me_lo X) P -> mem_inv b0segs m ->
    munch WSH me m -> wmono b0segs me m ->
    acoW WSH me ->
    shzW b0segs WSH me A1 (A1 + ARR1_SIZE) -> shzW b0segs WSH me A2 (A2 + ARR2_SIZE) -> shpW b0segs WSH me (P + 496) (P + 500) ->
    (forall m' (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x21' x28' x29' x30' x31' : word),
      let r := mss_shift f a1 a2 qo n d h lo j v b in let a1' := fst (fst r) in let j' := snd (fst r) in let b' := snd r in
      u8arr b0segs m' A1 (zb8 a1' ARR1_SIZE) -> u8arr b0segs m' A2 (zb8 a2 ARR2_SIZE) -> rw_cells b0segs m' P SLD ->
      rw_cells b0segs m' (P + 496) [C4 (Z_to_bv 64 b')] -> stk b0segs m' (me_lo X) P -> mem_inv b0segs m' ->
      munch WSH me m' -> wmono b0segs me m' ->
      zbok a1' -> pr n a1' 0 (n - 1) -> (lo <= j' <= j)%Z -> (-2147483648 < b' <= b)%Z ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5' x6' x7' (me_sp X) (Z_to_bv 64 P)
                            x10' x11' x12' x13' x14' x15' x16' x17'
                            x18' (Z_to_bv 64 n) (Z_to_bv 64 (A1 + 4 * snd (fst (mss_shift f a1 a2 qo n d h lo j v b)))) x21' (Z_to_bv 64 (lo + h - 1))
                            (Z_to_bv 64 (snd (fst (mss_shift f a1 a2 qo n d h lo j v b)))) (Z_to_bv 64 d) (Z_to_bv 64 (v + d)) (Z_to_bv 64 h) cSB
                            x28' x29' x30' x31')
                       F (Z_to_bv 64 0xa37b0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (Z_to_bv 64 A1) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          x10 x11 x12 x13 x14 x15 x16 x17
                          x18 (Z_to_bv 64 n) x20 x21 (Z_to_bv 64 (lo + h - 1)) (Z_to_bv 64 j) (Z_to_bv 64 d) (Z_to_bv 64 (v + d)) (Z_to_bv 64 h) cSB
                          x28 x29 x30 x31)
                     F (Z_to_bv 64 0xa3678) fc None m (seg_rom b0segs)).
  Proof.
    intros d h lo hi v a2. induction f as [|f IH]; [intros; lia|].
    intros j a1 b x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x28 x29 x30 x31 me m
           Hh Hlo Hj Hhi Hd Hv A1OK A2OK PR Hf BL BH AR1 AR2 SLB BUD STK MI MU WM ACW SH1 SH2 SHB K.
    msenv_open XOK. amenv_open YOK. pose proof XSEP as SP. unfold msenv_sep, apartm in SP. cps_destruct SP as (AP12 & AP1F & AP2F & _).
    bz_params. pose proof alloc_ceiling_range as ACR. open_slb_in SLB.
    pose proof (zb8_length a1 ARR1_SIZE ltac:(lia)) as L1. pose proof (zb8_length a2 ARR2_SIZE ltac:(lia)) as L2.
    pose proof (PR (j - h)%Z ltac:(lia)) as Pjh. set (pv := rd32 a1 (j - h)) in Pjh.
    pose proof (mss_shift_budget_le (S f) a1 a2 qo n d h lo j v b) as BLE.
    pose proof (mss_shift_budget_le_gtu f a1 a2 qo n d h lo j v b) as BG. fold pv in BG.
    pose proof BL as BL2. rewrite mss_shift_S in K, BL2, BLE. fold pv in K. fold pv in BL2. fold pv in BLE.
    pose proof (mainGtU_budget_le (pv + d) (v + d) a2 qo n b) as GL.
    destruct (mainGtU (pv + d) (v + d) a2 qo n b) as [gt b1] eqn:GT. cbn [fst snd] in BG, GL.
    assert (Epv : rd32 a1 (j - h) = pv) by reflexivity. clearbody pv.
    (* [comment removed for export] *)
    brun. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
    (* [comment removed for export] *)
    brun_to 0xa36e8%Z. wstep.
    pose proof (ACW m MU) as AC.
    call (B0_mainGtU_Z _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ A2 qo n (pv + d)%Z (v + d)%Z b (P + 496)%Z (me_lo X) P a2);
      [lia| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| exact AR2| exact BUD| exact MI| exact A2OK
      | lia| lia| bz_params; lia| lia| lia| lia| bz_ceil; bz_params; unfold CEIL; lia| lia| lia| lia| unfold apart; lia
      | rewrite GT; cbn [snd]; lia| lia| exact STK| lia| lia| lia| exact AC| lia| lia| lia
      | eapply (shzW_sub b0segs _ _ me m); [exact SH2| exact MU| sub_fp_solve| lia| lia]
      | eapply (shpW_sub b0segs _ _ me m); [exact SHB| exact MU| sub_fp_solve| lia| lia] | ].
    clear AC. rewrite GT in *. cbn [fst snd] in *.
    match goal with H : ?x = Z_to_bv 64 (Z.b2z gt) |- _ => subst x end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    match goal with H : rw_cells _ _ (P + 496)%Z _ |- _ => rename H into BUD end.
    match goal with H : stk _ _ _ _ |- _ => rename H into STK end.
    match goal with H : u8arr _ ?mm A2 (zb8 a2 ARR2_SIZE), H' : u8arr _ ?mm A2 (zb8 a2 ARR2_SIZE) |- _ => clear H' end.
    (* [comment removed for export] *)
    destruct gt; cbn [Z.b2z] in *.
    - (* [comment removed for export] *)
      brun. rdptr AR1 A1OK (j - h)%Z. rewrite Epv.
      brun. sw_ptr AR1 j pv.
      set (a1a := wr32 a1 j pv) in *.
      assert (A1OKa : zbok a1a) by (subst a1a; apply zbok_wr32; exact A1OK).
      assert (PRa : pr n a1a 0 (n - 1)).
      { intros y Hy. subst a1a. pose proof (PR y Hy). destruct (Z.eq_dec y j) as [->|NE]; [rewrite rd32_wr32_same by lia; lia| rewrite rd32_wr32_other by lia; lia]. }
      (* [comment removed for export] *)
      brun. if_cases Kc; zify_cond_z Kc.
      + replace (j - h <=? lo + h - 1) with false in K, BL2 by (symmetry; apply Z.leb_gt; lia).
        enter_with (IH (j - h)%Z a1a b1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ me);
          [st_eq| lia| lia| lia| lia| lia| lia| exact A1OKa| exact A2OK| exact PRa| lia| exact BL2| lia
          | exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact ACW| exact SH1| exact SH2| exact SHB|].
        intros m' x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x21' x28' x29' x30' x31'. cbv zeta.
        intros AR1' AR2' SLB' BUD' STK' MI' MU' WM' OK' PR' J' B'.
        eapply (K m'); [exact AR1'| exact AR2'| exact SLB'| exact BUD'| exact STK'| exact MI'| exact MU'| exact WM'| exact OK'| exact PR'| lia| lia].
      + replace (j - h <=? lo + h - 1) with true in K, BL2 by (symmetry; apply Z.leb_le; lia). cbn [fst snd] in K, BL2.
        (* [comment removed for export] *)
        brun_to 0xa37b0%Z.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OKa| exact PRa| lia| lia].
    - (* [comment removed for export] *)
      cbn [fst snd] in K, BL2.
      brun_to 0xa37b0%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact AR1| exact AR2| exact SLB| exact BUD| exact STK| exact MI| exact MU| exact WM| exact A1OK| exact PR| lia| lia].
  Qed.
End B0MS.
End ACeilS1.
