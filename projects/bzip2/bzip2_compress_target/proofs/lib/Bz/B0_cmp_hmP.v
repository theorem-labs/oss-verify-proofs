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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCHuff BzArrD CmpMem CmpCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFsKit0 CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0 B0_cmp_hmV B0_cmp_hmA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.
(* [comment removed for export] *)
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).

Lemma rw_cells_cutB : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. exact (proj1 (rw_cells_app_iff_c segs m A _ _) H). Qed.

(* [comment removed for export] *)
Ltac sb_lit :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite (le1_lit w); mem_after_store
  end.

Section B0HMP1.
  Variable X : hmenv. Variable P : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : hmenv_ok X.
  (* [comment removed for export] *)
  Hypothesis YPl : (he_lo X <= P)%Z. Hypothesis YPh : (P + 288 <= bv_unsigned (he_sp X))%Z. Hypothesis YPa : (bv_unsigned (he_sp X) <= P + 304)%Z.
  Notation usp := (bv_unsigned (he_sp X)).
  Notation A := (he_A X). Notation El := (he_El X). Notation Ef := (he_Ef X). Notation lb := (he_lb X). Notation fb := (he_fb X).
  Notation gp := (he_gp X). Notation tp := (he_tp X). Notation F := (he_F X). Notation fc := (he_fc X). Notation lo := (he_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  (* [comment removed for export] *)
  Notation SAVED := [C8 (he_s11 X); C8 (he_s10 X); C8 (he_s9 X); C8 (he_s8 X); C8 (he_s7 X); C8 (he_s6 X); C8 (he_s5 X); C8 (he_s4 X); C8 (he_s3 X);
                     C8 (he_s2 X); C8 (he_s1 X); C8 (he_s0 X); C8 (he_ra X)].

  (* [comment removed for export] *)

  Lemma land_m32B : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (32 * (x / 32))%Z.
  Proof.
    intros x Hx. change 18446744073709551584%Z with (Z.ldiff (Z.ones 64) (Z.ones 5)).
    rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
    rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
    change (2^5)%Z with 32%Z. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_hm_P1 : forall (qP : Z) (m : word -> option byte) (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (P = 32 * qP)%Z ->
    stk b0segs m lo usp -> mem_inv b0segs m -> aconsts B0C m -> aconsts_uar B0C m ->
    (forall m' (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 v176 : word) (a1 a2 : word),
      rw_cells b0segs m' P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 A); C8 v104; C8 v112;
                            C8 (Z_to_bv 64 17); C8 v128; C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168; C8 v176] ->
      stk b0segs m' (P + 184) (usp + -104) -> rw_cells b0segs m' (usp + -104) SAVED ->
      stk b0segs m' lo P -> mem_inv b0segs m' -> munch [(P, usp)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (mkR (Z_to_bv 64 0xa7eec) (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) (Z_to_bv 64 5600) a1 a2 (Z_to_bv 64 17) a4 a5 a6 a7
                            (he_s2 X) (he_s3 X) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (he_s8 X) (he_s9 X) (Z_to_bv 64 (Ef + 4 * fb)) cSB t3 t4 t5 t6)
                       F (Z_to_bv 64 0x3e334) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR (he_ra X) (he_sp X) gp tp t0 t1 t2 (he_s0 X) (he_s1 X) (Z_to_bv 64 (El + lb)) (Z_to_bv 64 (Ef + 4 * fb)) (Z_to_bv 64 A) (Z_to_bv 64 17)
                          a4 a5 a6 a7 (he_s2 X) (he_s3 X) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (he_s8 X) (he_s9 X) (he_s10 X) (he_s11 X) t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa7e6c) fc None m (seg_rom b0segs)).
  Proof.
    intros qP m t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 EqP ST MI AC AU K.
    hmenv_open XOK.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar B0C ci_segs] in GOT, SBV, GOTU, UARV.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    assert (CASE : (P = usp - 288 \/ P = usp - 304)%Z) by lia.
    assert (ELAND : Z.land (usp + -288) 18446744073709551584 = P).
    { rewrite land_m32B by lia. clear - CASE EqP XAL. Z.div_mod_to_equations. lia. }
    destruct CASE as [EP|EP].
    - (* [comment removed for export] *)
      carve_frame 288%nat ST.
      apply (rw_cells_split_CB b0segs _ _ [] 288 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      (* [comment removed for export] *)
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -288)%Z with P in FR, ST by lia.
      (* [comment removed for export] *)
      wstep. wstep. lit_store. wstep. wstep.
      (* [comment removed for export] *)
      brun_to 0xa7ed8%Z. wstep.
      (* [comment removed for export] *)
      brun_to 0x3e334%Z.
      cb8_all FR.
      destruct (rw_cells_cutB b0segs _ P _ 23%nat FR) as [SLc SVc]. cbn [firstn skipn cells_size csize Nat.add] in SLc, SVc.
      change (Z.of_nat 184) with 184%Z in SVc. replace (P + 184)%Z with (usp + -104)%Z in SVc by lia.
      eapply K; [exact SLc| | exact SVc| exact ST| assumption| exact MU| exact WM].
      split; [lia|]. split; [lia|]. intros a Ha. lia.
    - (* [comment removed for export] *)
      carve_frame 304%nat ST.
      apply (rw_cells_split_CB b0segs _ _ [] 304 _ [] [8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -304)%Z with P in FR, ST by lia.
      wstep. wstep. lit_store. wstep. wstep.
      brun_to 0xa7ed8%Z. wstep.
      brun_to 0x3e334%Z.
      cb8_all FR.
      destruct (rw_cells_cutB b0segs _ P _ 23%nat FR) as [SLc RESTc]. cbn [firstn skipn cells_size csize Nat.add] in SLc, RESTc.
      change (Z.of_nat 184) with 184%Z in RESTc.
      destruct (rw_cells_cutB b0segs _ (P + 184)%Z _ 2%nat RESTc) as [GAPc SVc]. cbn [firstn skipn cells_size csize Nat.add] in GAPc, SVc.
      change (Z.of_nat 16) with 16%Z in SVc. replace (P + 184 + 16)%Z with (usp + -104)%Z in SVc by lia.
      pose proof (stk_of_rw_cells b0segs _ _ _ GAPc) as GAPs. cbn [cells_size csize Nat.add] in GAPs. change (Z.of_nat 16) with 16%Z in GAPs.
      replace (P + 184 + 16)%Z with (usp + -104)%Z in GAPs by lia.
      eapply K; [exact SLc| exact GAPs| exact SVc| exact ST| assumption| exact MU| exact WM].
  Qed.
End B0HMP1.

Section B0HMP.
  Variable X : hmenv. Variable Y : ahenv. Variable Q : machine_state -> Prop.
  Hypothesis XOK : hmenv_ok X. Hypothesis YOK : ahenv_ok X Y.
  Notation usp := (bv_unsigned (he_sp X)). Notation P := (ah_P Y). Notation FB := (ah_FB Y). Notation SHF := (ah_SHF Y).
  Notation HP := (ah_HP Y). Notation WT := (ah_WT Y). Notation PR := (ah_PR Y).
  Notation A := (he_A X). Notation El := (he_El X). Notation Ef := (he_Ef X). Notation lb := (he_lb X). Notation fb := (he_fb X).
  Notation gp := (he_gp X). Notation tp := (he_tp X). Notation F := (he_F X). Notation fc := (he_fc X). Notation lo := (he_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation SAVED := [C8 (he_s11 X); C8 (he_s10 X); C8 (he_s9 X); C8 (he_s8 X); C8 (he_s7 X); C8 (he_s6 X); C8 (he_s5 X); C8 (he_s4 X); C8 (he_s3 X);
                     C8 (he_s2 X); C8 (he_s1 X); C8 (he_s0 X); C8 (he_ra X)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis YOFF : ahenv_offsh X Y. Hypothesis AX : sanchor FB SHF.
  Notation RQ ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 (Ef + 4 * fb)) cSB t3 t4 t5 t6).
  Ltac openY :=
    hmenv_open XOK; ahenv_open YOK; pose proof alloc_ceiling_range as ACR; unfold CEILh in *;
    let H := fresh "YO" in pose proof YOFF as H; unfold ahenv_offsh, SH_LO, SH_HI in H; destruct H as (_ & _ & ?YOF).

  (* [comment removed for export] *)
  Lemma B0_hm_P2 : forall (m : word -> option byte) (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 v176 h0 h1 h2 : word) (bs : list byte)
      (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 : word),
    rw_cells b0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 v56; C8 v64; C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 A); C8 v104; C8 v112;
                         C8 (Z_to_bv 64 17); C8 v128; C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168; C8 v176] ->
    rw_cells b0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells b0segs m SHF [CB 4 bs] -> mem_inv b0segs m ->
    (forall m' (a2 a3 : word),
      rw_cells b0segs m' P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 A);
                            C8 v104; C8 v112; C8 (Z_to_bv 64 17); C8 v128; C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168; C8 (Z_to_bv 64 FB)] ->
      rw_cells b0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1af99); C8 (Z_to_bv 64 0xa7e6c)] ->
      mem_inv b0segs m' ->
      munch [(P + 56, P + 72); (P + 176, P + 184); (FB, FB + 24); (SHF, SHF + 4)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RQ (Z_to_bv 64 0xa7f80) t0 t1 t2 (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 130) a2 a3 (Z_to_bv 64 FB) a5 a6 a7
                           s2 (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) s5 s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RQ (Z_to_bv 64 0xa7eec) t0 t1 t2 (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa7eec) fc None m (seg_rom b0segs)).
  Proof.
    intros m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 v176 h0 h1 h2 bs
      t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 t3 t4 t5 t6 SL HD SH4 MI K.
    openY.
    pose proof (munch_refl [(P + 56, P + 72); (P + 176, P + 184); (FB, FB + 24); (SHF, SHF + 4)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    apply (rw_cells_split_CB b0segs _ _ [] 4 _ [] [1;1;1;1]%nat) in SH4; [| reflexivity]. cbn [mk_CB_cells app] in SH4.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    brun_to 0xa7f48%Z. wstep. lit_store. wstep. lit_store. wstep. wstep. lit_store.
    (* [comment removed for export] *)
    wstep. wstep. sh_norm.
    (* [comment removed for export] *)
    wstep. sb_lit. wstep. sb_lit. wstep. sb_lit. wstep. sb_lit.
    brun_to 0x55430%Z.
    eapply K; [exact SL| exact HD| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Ltac rz_split RZ n sizes := apply (rw_cells_split_CB b0segs _ _ [] n _ [] sizes) in RZ; [| reflexivity]; cbn [mk_CB_cells app] in RZ.

  (* [comment removed for export] *)
  Lemma B0_hm_P3 : forall (m : word -> option byte) (bs : list byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 134) [CB 16 bs] -> mem_inv b0segs m ->
    (forall m', mem_inv b0segs m' -> munch [(SHF + 134, SHF + 150)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RQ (Z_to_bv 64 0xa7fd4) t0 t1 t2 (Z_to_bv 64 (SHF + 150)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (-14)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RQ (Z_to_bv 64 0xa7f80) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         s2 (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) s5 s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa7f80) fc None m (seg_rom b0segs)).
  Proof.
    intros m bs t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s9 t3 t4 t5 t6 RZ MI K.
    openY. pose proof (munch_refl [(SHF + 134, SHF + 150)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    rz_split RZ 16%nat [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat.
    wstep. do 16 (wstep; sb_lit).
    brun_to 0x55430%Z.
    eapply K; [assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hm_P4 : forall (m : word -> option byte) (bs : list byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 : word),
    rw_cells b0segs m (SHF + 408) [CB 16 bs] -> mem_inv b0segs m ->
    (forall m', mem_inv b0segs m' -> munch [(SHF + 408, SHF + 424)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RQ (Z_to_bv 64 0xa8024) t0 t1 t2 (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55430) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RQ (Z_to_bv 64 0xa7fd4) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 (-14)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa7fd4) fc None m (seg_rom b0segs)).
  Proof.
    intros m bs t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 RZ MI K.
    openY. pose proof (munch_refl [(SHF + 408, SHF + 424)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    rz_split RZ 16%nat [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat.
    do 16 (wstep; sb_lit).
    brun_to 0x55430%Z.
    eapply K; [assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hm_P5 : forall (m : word -> option byte) (bs : list byte) (v0 v8 v16 v24 v32 v40 v48 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 : word)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 : word),
    rw_cells b0segs m P [C8 v0; C8 v8; C8 v16; C8 v24; C8 v32; C8 v40; C8 v48; C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 A);
                         C8 v104; C8 v112; C8 (Z_to_bv 64 17); C8 v128; C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168; C8 (Z_to_bv 64 FB)] ->
    rw_cells b0segs m (SHF + 682) [CB 18 bs] -> mem_inv b0segs m ->
    (forall m',
      rw_cells b0segs m' P [C8 v0; C8 v8; C8 v16; C8 (Z_to_bv 64 SHF); C8 v32; C8 v40; C8 (Z_to_bv 64 (SHF + 4)); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 v72; C8 v80; C8 v88;
                            C8 (Z_to_bv 64 A); C8 v104; C8 v112; C8 (Z_to_bv 64 17); C8 v128; C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168; C8 (Z_to_bv 64 FB)] ->
      mem_inv b0segs m' -> munch [(SHF + 682, SHF + 700); (P + 24, P + 32); (P + 48, P + 56)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RQ (Z_to_bv 64 0xa8084) t0 t1 t2 (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 130) a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55310) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RQ (Z_to_bv 64 0xa8024) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa8024) fc None m (seg_rom b0segs)).
  Proof.
    intros m bs v0 v8 v16 v24 v32 v40 v48 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 SL RZ MI K.
    openY. pose proof (munch_refl [(SHF + 682, SHF + 700); (P + 24, P + 32); (P + 48, P + 56)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    rz_split RZ 18%nat [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat.
    (* [comment removed for export] *)
    wstep. do 17 (wstep; sb_lit). wstep. wstep; sb_lit. wstep. wstep.
    brun_to 0x55310%Z.
    eapply K; [exact SL| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hm_P6 : forall (m : word -> option byte) (v0 v8 v16 v32 v40 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 : word)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 : word),
    rw_cells b0segs m P [C8 v0; C8 v8; C8 v16; C8 (Z_to_bv 64 SHF); C8 v32; C8 v40; C8 (Z_to_bv 64 (SHF + 4)); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 v72; C8 v80; C8 v88;
                         C8 (Z_to_bv 64 A); C8 v104; C8 v112; C8 (Z_to_bv 64 17); C8 v128; C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168; C8 (Z_to_bv 64 FB)] ->
    mem_inv b0segs m ->
    (forall m',
      rw_cells b0segs m' P [C8 v0; C8 v8; C8 v16; C8 (Z_to_bv 64 SHF); C8 v32; C8 (Z_to_bv 64 (SHF + 150)); C8 (Z_to_bv 64 (SHF + 4)); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB);
                            C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 A); C8 v104; C8 v112; C8 (Z_to_bv 64 17); C8 v128; C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168;
                            C8 (Z_to_bv 64 FB)] ->
      mem_inv b0segs m' -> munch [(P + 40, P + 48)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RQ (Z_to_bv 64 0xa8094) t0 t1 t2 (Z_to_bv 64 (SHF + 150)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55310) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RQ (Z_to_bv 64 0xa8084) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa8084) fc None m (seg_rom b0segs)).
  Proof.
    intros m v0 v8 v16 v32 v40 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 SL MI K.
    openY. pose proof (munch_refl [(P + 40, P + 48)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    (* [comment removed for export] *)
    wstep. wstep. brun_to 0x55310%Z.
    eapply K; [exact SL| assumption| exact MU| exact WM].
  Qed.

  Lemma B0_hm_P7 : forall (m : word -> option byte) (v0 v8 v16 v32 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 : word)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 : word),
    rw_cells b0segs m P [C8 v0; C8 v8; C8 v16; C8 (Z_to_bv 64 SHF); C8 v32; C8 (Z_to_bv 64 (SHF + 150)); C8 (Z_to_bv 64 (SHF + 4)); C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB);
                         C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 A); C8 v104; C8 v112; C8 (Z_to_bv 64 17); C8 v128; C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168;
                         C8 (Z_to_bv 64 FB)] ->
    mem_inv b0segs m ->
    (forall m',
      rw_cells b0segs m' P [C8 v0; C8 v8; C8 v16] ->
      rw_cells b0segs m' (P + 24) [C8 (Z_to_bv 64 SHF); C8 (Z_to_bv 64 (SHF + 424)); C8 (Z_to_bv 64 (SHF + 150)); C8 (Z_to_bv 64 (SHF + 4));
                                   C8 (Z_to_bv 64 FB); C8 (Z_to_bv 64 FB); C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 A); C8 v104; C8 v112; C8 (Z_to_bv 64 17); C8 v128;
                                   C8 v136; C8 v144; C8 (Z_to_bv 64 (El + lb)); C8 v160; C8 v168; C8 (Z_to_bv 64 FB)] ->
      mem_inv b0segs m' -> munch [(P + 32, P + 40)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RQ (Z_to_bv 64 0xa80a4) t0 t1 t2 (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7
                           (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x55310) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RQ (Z_to_bv 64 0xa8094) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
                         (Z_to_bv 64 (SHF + 424)) (Z_to_bv 64 SHF) (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 (SHF + 150)) s6 s7 (Z_to_bv 64 (FB + 1200)) s9 t3 t4 t5 t6)
                     F (Z_to_bv 64 0xa8094) fc None m (seg_rom b0segs)).
  Proof.
    intros m v0 v8 v16 v32 v72 v80 v88 v104 v112 v128 v136 v144 v160 v168 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s9 t3 t4 t5 t6 SL MI K.
    openY. pose proof (munch_refl [(P + 32, P + 40)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    (* [comment removed for export] *)
    wstep. wstep. brun_to 0x55310%Z.
    destruct (rw_cells_cutB b0segs _ P _ 3%nat SL) as [SL0 SLr]. cbn [firstn skipn cells_size csize Nat.add] in SL0, SLr. change (Z.of_nat 24) with 24%Z in SLr.
    eapply K; [exact SL0| exact SLr| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (he_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 PR) (Z_to_bv 64 516) (Z_to_bv 64 515) (NOT PR) (Z_to_bv 64 259) (NOT WT) (Z_to_bv 64 WT) (NOT HP) (Z_to_bv 64 HP) cSB t3 t4 t5 t6).

  Lemma B0_hm_E1 : forall (m : word -> option byte) (v136 v144 v160 v168 : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rw_cells b0segs m (P + 24) (SLb X Y v136 v144 v160 v168) ->
    (evt b0segs Q (MS (RB (Z_to_bv 64 0xa8bf0) t0 t1 t2 (Z_to_bv 64 (SHF + 150)) (Z_to_bv 64 258) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x55430) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa8be4) fc None m (seg_rom b0segs)).
  Proof. intros m v136 v144 v160 v168 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SL K. unfold SLb in SL. brun_to 0x55430%Z. exact K. Qed.
  Lemma B0_hm_E2 : forall (m : word -> option byte) (v136 v144 v160 v168 : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rw_cells b0segs m (P + 24) (SLb X Y v136 v144 v160 v168) ->
    (evt b0segs Q (MS (RB (Z_to_bv 64 0xa8bfc) t0 t1 t2 (Z_to_bv 64 (SHF + 4)) (Z_to_bv 64 130) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x55430) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa8bf0) fc None m (seg_rom b0segs)).
  Proof. intros m v136 v144 v160 v168 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SL K. unfold SLb in SL. brun_to 0x55430%Z. exact K. Qed.

  (* [comment removed for export] *)
  Lemma B0_hm_E3 : forall (m : word -> option byte) (v136 v144 v160 v168 h0 : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rw_cells b0segs m (P + 24) (SLb X Y v136 v144 v160 v168) -> rw_cells b0segs m FB [C8 h0] -> mem_inv b0segs m ->
    (forall m', rw_cells b0segs m' (P + 24) (SLb X Y v136 v144 v160 v168) -> rw_cells b0segs m' FB [C8 (Z_to_bv 64 0x45e0360e)] -> mem_inv b0segs m' ->
      munch [(FB, FB + 8)]%Z m m' -> wmono b0segs m m' ->
      evt b0segs Q (MS (RB (Z_to_bv 64 0xa8c20) t0 t1 t2 (Z_to_bv 64 FB) (Z_to_bv 64 5600) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x3e4b0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa8bfc) fc None m (seg_rom b0segs)).
  Proof.
    intros m v136 v144 v160 v168 h0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SL HD MI K.
    openY. pose proof SL as SLu. unfold SLb in SLu. pose proof (munch_refl [(FB, FB + 8)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. lit_store.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
    brun_to 0x3e4b0%Z.
    eapply K; [exact SL| exact HD| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_hm_E4 : forall (m : word -> option byte) (v0 v8 v16 v136 v144 v160 v168 : word) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    rw_cells b0segs m P [C8 v0; C8 v8; C8 v16] -> rw_cells b0segs m (P + 24) (SLb X Y v136 v144 v160 v168) -> stk b0segs m (P + 184) (usp + -104) ->
    rw_cells b0segs m (usp + -104) SAVED -> stk b0segs m lo P ->
    (stk b0segs m lo usp ->
      evt b0segs Q (MS (mkR (he_ra X) (he_sp X) gp tp t0 t1 t2 (he_s0 X) (he_s1 X) a0 a1 a2 a3 a4 a5 a6 a7
                            (he_s2 X) (he_s3 X) (he_s4 X) (he_s5 X) (he_s6 X) (he_s7 X) (he_s8 X) (he_s9 X) (he_s10 X) (he_s11 X) t3 t4 t5 t6)
                       F (ret_pc (he_ra X)) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) F (Z_to_bv 64 0xa8c20) fc None m (seg_rom b0segs)).
  Proof.
    intros m v0 v8 v16 v136 v144 v160 v168 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 SL0 SL GAP SAV ST K.
    openY.
    (* [comment removed for export] *)
    wstep. wstep. do 13 wstep. wstep.
    (* [comment removed for export] *)
    pose proof (stk_of_rw_cells b0segs _ _ _ SL0) as K0. cbn [cells_size csize Nat.add] in K0. change (Z.of_nat 24) with 24%Z in K0.
    pose proof (stk_of_rw_cells b0segs _ _ _ SL) as K1. cbn [SLb cells_size csize Nat.add] in K1. change (Z.of_nat 160) with 160%Z in K1.
    pose proof (stk_of_rw_cells b0segs _ _ _ SAV) as K3. cbn [cells_size csize Nat.add] in K3. change (Z.of_nat 104) with 104%Z in K3.
    stk_add ST K0. stk_add ST K1. stk_add ST GAP. stk_add ST K3.
    lazymatch type of ST with stk _ _ _ ?hi => replace hi with usp in ST by lia end.
    (* [comment removed for export] *)
    wstep.
    exact (K ST).
  Qed.
End B0HMP.
End ACeilS1.
