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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpCarve CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV B0_b2c_cbV A0_cmp_smV B0_b2c_hcV B0_b2c_wrV AsanKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0F_b2d_wrV.
Section ACeilS1. Context {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Ltac dead := let KD := fresh "KD" in if_cases KD; zify_cond_z KD; [exfalso; lia|]; clear KD.
Ltac live := let KD := fresh "KD" in if_cases KD; zify_cond_z KD; [|exfalso; lia]; clear KD.
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac sbl := wstep; lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite (CmpMem.le1_lit w); mem_after_store end.
Ltac sbz := wstep; lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 (Z_to_bv 64 0))) _) => change (le1 (Z_to_bv 64 0)) with [z8]; mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 0)) _) => change (Z_to_le_bytes 1 0) with [z8]; mem_after_store
  | _ => idtac end.
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
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma land_m32 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551584 = (32 * (x / 32))%Z.
Proof.
  intros x Hx. change 18446744073709551584%Z with (Z.ldiff (Z.ones 64) (Z.ones 5)).
  rewrite Z.ldiff_land, Z.land_assoc, Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite <- Z.ldiff_land, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
  change (2^5)%Z with 32%Z. lia.
Qed.

Section B0FWRW.
  Variable Q : machine_state -> Prop.
  Variables (P FB SHF STRM lo : Z) (dst dl src len small verb : Z).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  (* [comment removed for export] *)
  Hypothesis LLO : (CEILv <= lo)%Z. Hypothesis PLO : (lo <= P)%Z. Hypothesis PCASE : (P = usp - 160 \/ P = usp - 176)%Z.
  Hypothesis USPQ : exists q, usp = (16 * q)%Z. Hypothesis PQ : exists q, P = (32 * q)%Z.
  (* [comment removed for export] *)
  Hypothesis DST : (0 < dst < 18446744073709551616)%Z. Hypothesis DLR : (0 < dl)%Z. Hypothesis DLH : (dl + 4 <= CEILv)%Z.
  Hypothesis SRC : (0 < src < 18446744073709551616)%Z. Hypothesis LEN : (0 <= len < 4294967296)%Z.
  Hypothesis SMALL : (0 <= small <= 1)%Z. Hypothesis VERB : (0 <= verb <= 4)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_b2d_D1 : forall (m : amem) (ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    stk b0segs m lo usp -> mem_inv b0segs m -> aconsts B0C m -> aconsts_uar B0C m ->
    (forall m' (v0 v8 v16 v32 v40 v48 a1' a2' : word),
        rw_cells b0segs m' P (WSLOTS v0 v8 v16 (Z_to_bv 64 len) v32 v40 v48) ->
        stk b0segs m' (P + 56) (usp + -104) -> rw_cells b0segs m' (usp + -104) (HSAVED s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
        stk b0segs m' lo P -> mem_inv b0segs m' -> munch [(P, usp)]%Z m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 0x88c74) cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 160) a1' a2' (Z_to_bv 64 len) (Z_to_bv 64 small) (Z_to_bv 64 verb) a6 a7
                              s2 cSB s4 s5 (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 small) (Z_to_bv 64 verb) (Z_to_bv 64 dl) s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x3de08) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 dst) (Z_to_bv 64 dl) (Z_to_bv 64 src) (Z_to_bv 64 len) (Z_to_bv 64 small) (Z_to_bv 64 verb) a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88bf0) fc None m (seg_rom b0segs)).
  Proof.
    intros m ra t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ST MI AC AU K.
    unfold CEILv in *. bz_ceil.
    destruct AC as [GOT SBV]. destruct AU as [GOTU UARV].
    cbn [aci_segs aci_c aci_got_sh aci_shvar aci_got_uar aci_uarvar B0C ci_segs] in GOT, SBV, GOTU, UARV.
    pose proof (munch_refl [(P, usp)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RSP.
    destruct USPQ as [qu EQU]. destruct PQ as [qP EqP].
    assert (ELAND : Z.land (usp + -160) 18446744073709551584 = P).
    { rewrite land_m32 by lia. clear - PCASE EqP EQU. Z.div_mod_to_equations. lia. }
    destruct PCASE as [EP|EP].
    - (* [comment removed for export] *)
      carve_frame 160%nat ST.
      apply (rw_cells_split_CB b0segs _ _ [] 160 _ [] [8;8;8;8;8;8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      (* [comment removed for export] *)
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -160)%Z with P in FR, ST by lia.
      replace (Z_to_bv 64 (P + 160)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
      (* [comment removed for export] *)
      brun_to 0x3de08%Z.
      cb8_all FR.
      destruct (rw_cells_cutZ b0segs _ P _ 7%nat FR) as [SLa SVc]. cbn [firstn skipn cells_size csize Nat.add] in SLa, SVc. change (Z.of_nat 56) with 56%Z in SVc.
      replace (P + 56)%Z with (usp + -104)%Z in SVc by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [ st_eq | unfold WSLOTS; exact SLa | | unfold HSAVED; exact SVc | exact ST | assumption | exact MU | exact WM ].
      split; [lia|]. split; [lia|]. intros a Ha. lia.
    - (* [comment removed for export] *)
      carve_frame 176%nat ST.
      apply (rw_cells_split_CB b0segs _ _ [] 176 _ [] [8;8;8;8;8;8;8; 8;8; 8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
      cbn [mk_CB_cells app] in FR.
      wstep. wstep. lit_store. do 13 wstep. wstep. wstep.
      rewrite ELAND. replace (usp + -176)%Z with P in FR, ST by lia.
      replace (Z_to_bv 64 (usp + -160 + 160)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
      brun_to 0x3de08%Z.
      cb8_all FR.
      destruct (rw_cells_cutZ b0segs _ P _ 7%nat FR) as [SLa R1]. cbn [firstn skipn cells_size csize Nat.add] in SLa, R1. change (Z.of_nat 56) with 56%Z in R1.
      destruct (rw_cells_cutZ b0segs _ _ _ 2%nat R1) as [GAPc SVc]. cbn [firstn skipn cells_size csize Nat.add] in GAPc, SVc. change (Z.of_nat 16) with 16%Z in SVc.
      replace (P + 56 + 16)%Z with (usp + -104)%Z in SVc by lia.
      pose proof (stk_of_rw_cells b0segs _ _ _ GAPc) as GAPs. cbn [cells_size csize Nat.add] in GAPs. change (Z.of_nat 16) with 16%Z in GAPs.
      replace (P + 56 + 16)%Z with (usp + -104)%Z in GAPs by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
        [ st_eq | unfold WSLOTS; exact SLa | exact GAPs | unfold HSAVED; exact SVc | exact ST | assumption | exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis AX : sanchor FB SHF. Hypothesis ESTR : STRM = (FB + 32)%Z.
  Hypothesis FBL : (0x62b000 <= FB)%Z. Hypothesis FBH : (FB + 256 <= CEILv)%Z.
  Hypothesis SHL : (SH_LO <= SHF)%Z. Hypothesis SHH : (SHF + 32 <= SH_HI)%Z.
  (* [comment removed for export] *)
  Hypothesis SFSH : apartv FB 256 SHF 32.

  Definition b2d_W2 : list (Z * Z) := [(P + 16, P + 24); (P + 48, P + 56); (FB, FB + 24); (SHF, SHF + 20)]%Z.

  (* [comment removed for export] *)
  Lemma B0_b2d_D2 : forall (m : amem) (v0 v8 v16 v32 v40 v48 h0 h1 h2 : word) (bs : list byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m P (WSLOTS v0 v8 v16 (Z_to_bv 64 len) v32 v40 v48) ->
    rw_cells b0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells b0segs m SHF [CB 20 bs] -> mem_inv b0segs m ->
    (forall m' (a3' : word),
        rw_cells b0segs m' P (WSLOTS v0 v8 (Z_to_bv 64 dl) (Z_to_bv 64 len) v32 v40 (Z_to_bv 64 FB)) ->
        rw_cells b0segs m' FB [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x17ecc); C8 (Z_to_bv 64 0x88bf0)] -> rw_cells b0segs m' SHF b2c_shadow ->
        mem_inv b0segs m' -> munch b2d_W2 m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 0x88d64) cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 (FB + 88)) (Z_to_bv 64 0) (Z_to_bv 64 24) a3' a4 a5 a6 a7
                              (Z_to_bv 64 FB) cSB (Z_to_bv 64 (-2)) (Z_to_bv 64 FB) (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 small) (Z_to_bv 64 verb)
                              (Z_to_bv 64 STRM) (Z_to_bv 64 SHF) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x528ec) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 FB) a1 a2 a3 a4 a5 a6 a7
                          s2 cSB s4 s5 (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 small) (Z_to_bv 64 verb) (Z_to_bv 64 dl) s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88c74) fc None m (seg_rom b0segs)).
  Proof.
    intros m v0 v8 v16 v32 v40 v48 h0 h1 h2 bs ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s11 t3 t4 t5 t6 SL HD SH20 MI K.
    unfold CEILv, SH_LO, SH_HI, apartv in *. bz_ceil. box_ors.
    pose proof (munch_refl b2d_W2 m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold b2d_W2 in MU.
    unfold WSLOTS in SL.
    apply (rw_cells_split_CB b0segs _ _ [] 20 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in SH20; [| reflexivity]. cbn [mk_CB_cells app] in SH20.
    (* [comment removed for export] *)
    brun. live.
    (* [comment removed for export] *)
    brun_to 0x88cc4%Z. wstep. lit_store. wstep. lit_store. wstep. lit_store.
    (* [comment removed for export] *)
    wstep. wstep. sh_norm.
    (* [comment removed for export] *)
    do 4 sbl. wstep. sbz. sbz. do 6 sbl. do 8 sbz.
    (* [comment removed for export] *)
    brun. dead. brun. dead. brun. dead. brun. dead.
    (* [comment removed for export] *)
    brun. dead.
    (* [comment removed for export] *)
    brun_to 0x528ec%Z. replace (FB + 32)%Z with STRM by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end;
      [ st_eq | unfold WSLOTS; exact SL | exact HD | unfold b2c_shadow, A0_cmp_smV.sf1b, A0_cmp_smV.sf3b; exact SH20 | assumption | unfold b2d_W2; exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_b2d_D3 : forall (m : amem) (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    evt b0segs Q (MS (mkR (Z_to_bv 64 0x88d74) spw gp tp t0 t1 t2 s0 s1 s10 s9 s8 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x83a20) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88d64) fc None m (seg_rom b0segs)).
  Proof.
    intros m ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 K.
    (* [comment removed for export] *)
    do 4 wstep. exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable SHD : Z.
  Hypothesis AD : sanchor dl SHD. Hypothesis DLLO : (0x62b000 <= dl)%Z.
  Hypothesis DLF : apartv dl 4 FB 256.

  Definition b2d_W4 : list (Z * Z) := [(STRM, STRM + 36)]%Z.

  (* [comment removed for export] *)
  Lemma B0_b2d_D4 : forall (m : amem) (cap : Z) (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w32 w36 w40 : word) (q2 : list byte) (w48 w56 w64 w72 v0 v8 v32 v40 : word)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
    (0 <= cap < 2147483648)%Z ->
    rw_cells b0segs m STRM (STRMD w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 w56 w64 w72) ->
    rw_cells b0segs m P (WSLOTS v0 v8 (Z_to_bv 64 dl) (Z_to_bv 64 len) v32 v40 (Z_to_bv 64 FB)) ->
    rw_cells b0segs m dl [C4 (Z_to_bv 64 cap)] -> mem_inv b0segs m -> shpW b0segs b2d_W4 m dl (dl + 4) ->
    (forall m' (a1' a2' : word),
        rw_cells b0segs m' STRM (STRMD (Z_to_bv 64 src) (Z_to_bv 64 len) w12 w16 q1 (Z_to_bv 64 dst) (Z_to_bv 64 cap) w36 w40 q2 w48 w56 w64 w72) ->
        rw_cells b0segs m' P (WSLOTS v0 v8 (Z_to_bv 64 dl) (Z_to_bv 64 len) v32 v40 (Z_to_bv 64 FB)) ->
        rw_cells b0segs m' dl [C4 (Z_to_bv 64 cap)] -> mem_inv b0segs m' -> munch b2d_W4 m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 0x88f18) cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 STRM) a1' a2' a3 a4 a5 a6 a7
                              (Z_to_bv 64 FB) (Z_to_bv 64 SHD) (Z_to_bv 64 0) (Z_to_bv 64 FB) (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 small) (Z_to_bv 64 verb)
                              (Z_to_bv 64 STRM) (Z_to_bv 64 SHF) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x83eb0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 FB) cSB s4 (Z_to_bv 64 FB) (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 small) (Z_to_bv 64 verb)
                          (Z_to_bv 64 STRM) (Z_to_bv 64 SHF) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88d74) fc None m (seg_rom b0segs)).
  Proof.
    intros m cap w0 w8 w12 w16 q1 w24 w32 w36 w40 q2 w48 w56 w64 w72 v0 v8 v32 v40 ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 CAPR SM SL DLC MI SHd K.
    unfold CEILv, SH_LO, SH_HI, apartv in *. bz_ceil. box_ors.
    pose proof (munch_refl b2d_W4 m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold b2d_W4 in MU, SHd.
    unfold STRMD in SM. unfold WSLOTS in SL.
    pose proof (proj1 AD) as DLAL8. assert (DLAL4 : (dl mod 4 = 0)%Z) by (clear - DLAL8; Z.div_mod_to_equations; lia).
    (* [comment removed for export] *)
    brun_to 0x88f00%Z.
    (* [comment removed for export] *)
    ack_rd dl 4%Z.
    ack_merge.
    sh_norm.
    (* [comment removed for export] *)
    brun_to 0x88f10%Z.
    try rewrite (sx32_of_Z cap) in SM by lia.
    brun_to 0x83eb0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
      [ st_eq | unfold STRMD; first [exact SM | cells_eq_by SM] | unfold WSLOTS; exact SL | exact DLC | assumption | unfold b2d_W4; exact MU | exact WM ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition b2d_ra (ret : Z) : Z := if (ret =? 0)%Z then 0x88f64%Z else if (ret =? 4)%Z then 0x88f4c%Z else 0x88f74%Z.
  Definition b2d_s3 (ret avo : Z) : Z := if (ret =? 0)%Z then (if (avo =? 0)%Z then 1%Z else 0%Z) else SHD.
  Definition b2d_dlv (ret cap avo : Z) : Z := if (ret =? 4)%Z then (cap - avo)%Z else cap.
  Definition b2d_W5 : list (Z * Z) := [(dl, dl + 4)]%Z.

  Lemma B0_b2d_D5 : forall (m : amem) (ret cap avo : Z) (w0 w8 w12 w16 : word) (q1 : list byte) (w24 w36 w40 : word) (q2 : list byte) (w48 w56 w64 w72 v0 v8 v32 v40 : word)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (-5 <= ret <= 4)%Z -> (0 <= avo <= cap)%Z -> (cap < 2147483648)%Z ->
    rw_cells b0segs m STRM (STRMD w0 w8 w12 w16 q1 w24 (Z_to_bv 64 avo) w36 w40 q2 w48 w56 w64 w72) ->
    rw_cells b0segs m P (WSLOTS v0 v8 (Z_to_bv 64 dl) (Z_to_bv 64 len) v32 v40 (Z_to_bv 64 FB)) ->
    rw_cells b0segs m dl [C4 (Z_to_bv 64 cap)] -> mem_inv b0segs m -> shpW b0segs b2d_W5 m dl (dl + 4) ->
    (forall m' (a1' a2' : word),
        rw_cells b0segs m' STRM (STRMD w0 w8 w12 w16 q1 w24 (Z_to_bv 64 avo) w36 w40 q2 w48 w56 w64 w72) ->
        rw_cells b0segs m' P (WSLOTS v0 v8 (Z_to_bv 64 dl) (Z_to_bv 64 len) v32 v40 (Z_to_bv 64 FB)) ->
        rw_cells b0segs m' dl [C4 (Z_to_bv 64 (b2d_dlv ret cap avo))] -> mem_inv b0segs m' -> munch b2d_W5 m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR (Z_to_bv 64 (b2d_ra ret)) cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 STRM) a1' a2' a3 a4 a5 a6 a7
                              (Z_to_bv 64 FB) (Z_to_bv 64 (b2d_s3 ret avo)) (Z_to_bv 64 ret) (Z_to_bv 64 FB) (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 small) (Z_to_bv 64 verb)
                              (Z_to_bv 64 STRM) (Z_to_bv 64 SHF) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x885f4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 sp cP (Z_to_bv 64 ret) a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 FB) (Z_to_bv 64 SHD) (Z_to_bv 64 0) (Z_to_bv 64 FB) (Z_to_bv 64 src) (Z_to_bv 64 dst) (Z_to_bv 64 small) (Z_to_bv 64 verb)
                          (Z_to_bv 64 STRM) (Z_to_bv 64 SHF) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88f18) fc None m (seg_rom b0segs)).
  Proof.
    intros m ret cap avo w0 w8 w12 w16 q1 w24 w36 w40 q2 w48 w56 w64 w72 v0 v8 v32 v40 ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 RET AVO CAPR SM SL DLC MI SHd K.
    unfold CEILv, SH_LO, SH_HI, apartv in *. bz_ceil. box_ors.
    pose proof (munch_refl b2d_W5 m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold b2d_W5 in MU, SHd.
    pose proof (proj2 AD : saddr dl SHD) as ADs.
    unfold STRMD in SM. unfold WSLOTS in SL.
    assert (CASES : (ret = 0 \/ ret = 4 \/ ret = -5 \/ ret = -4 \/ ret = -3 \/ ret = -2 \/ ret = -1 \/ ret = 1 \/ ret = 2 \/ ret = 3)%Z) by lia.
    clear RET.
    destruct CASES as [-> | [-> | OTHER]].
    - (* [comment removed for export] *)
      brun_to 0x88f58%Z. try rewrite (sx32_of_Z avo) by lia.
      brun_to 0x885f4%Z.
      destruct (Z.eqb_spec avo 0) as [EA|NA].
      + subst avo.
        enter_with (K m _ _); [ st_eq | unfold STRMD; exact SM | unfold WSLOTS; exact SL | exact DLC | exact MI | unfold b2d_W5; exact MU | exact WM ].
      + replace (avo <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
        enter_with (K m _ _); [ unfold b2d_ra, b2d_s3; cbn [Z.eqb]; replace (avo =? 0)%Z with false by (symmetry; apply Z.eqb_neq; exact NA); st_eq
                              | unfold STRMD; exact SM | unfold WSLOTS; exact SL | exact DLC | exact MI | unfold b2d_W5; exact MU | exact WM ].
    - (* [comment removed for export] *)
      brun_to 0x88f28%Z.
      ack_rd_saddr dl 4%Z ADs.
      (* [comment removed for export] *)
      wstep.
      ack_merge.
      (* [comment removed for export] *)
      brun_to 0x88f44%Z.
      reword_C4 DLC 0%nat (cap - avo)%Z. { try rewrite (sx32_of_Z cap) by lia. try rewrite (sx32_of_Z avo) by lia. now low32. }
      (* [comment removed for export] *)
      brun_to 0x885f4%Z.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end;
        [ st_eq | unfold STRMD; exact SM | unfold WSLOTS; exact SL | exact DLC | assumption | unfold b2d_W5; exact MU | exact WM ].
    - (* [comment removed for export] *)
      destruct OTHER as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]];
        (brun_to 0x885f4%Z;
         enter_with (K m _ _); [ st_eq | unfold STRMD; exact SM | unfold WSLOTS; exact SL | exact DLC | exact MI | unfold b2d_W5; exact MU | exact WM ]).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_b2d_D6a : forall (m : amem) (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 0) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88d7c) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88f4c) fc None m (seg_rom b0segs)).
  Proof.
    intros m ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 K.
    (* [comment removed for export] *)
    do 2 wstep. exact K.
  Qed.
  Lemma B0_b2d_D6b : forall (m : amem) (full : bool) (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (if full then 1 else 0)) (Z_to_bv 64 (if full then -8 else -7)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88d7c) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (if full then 1 else 0)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88f64) fc None m (seg_rom b0segs)).
  Proof.
    intros m full ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 K.
    (* [comment removed for export] *)
    destruct full; do 2 wstep.
    - replace (Z_to_bv 64 18446744073709551608) with (Z_to_bv 64 (-8)) by (apply bv_eq; reflexivity). exact K.
    - replace (Z_to_bv 64 18446744073709551609) with (Z_to_bv 64 (-7)) by (apply bv_eq; reflexivity). exact K.
  Qed.
  Lemma B0_b2d_D6c : forall (m : amem) (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88d7c) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88f74) fc None m (seg_rom b0segs)).
  Proof.
    intros m ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 K.
    (* [comment removed for export] *)
    wstep. exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable FL : Z.
  Hypothesis FLL : (0 < FL)%Z. Hypothesis FLH : (FL + 1 <= 18446744073709551616)%Z.
  Definition b2d_WE1 : list (Z * Z) := [(SHF, SHF + 32); (FB, FB + 8)]%Z.

  (* [comment removed for export] *)
  Lemma B0_b2d_E1 : forall (m : amem) (sh : list byte) (h0 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word),
    Z.of_nat (length sh) = 32%Z ->
    u8arr b0segs m SHF sh -> rw_cells b0segs m FB [C8 h0] -> mem_inv b0segs m ->
    (forall m' (a0' : word),
        rw_cells b0segs m' SHF b2c_sh_f5 -> rw_cells b0segs m' FB [C8 (Z_to_bv 64 0x45e0360e)] ->
        mem_inv b0segs m' -> munch b2d_WE1 m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 sp cP a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 FB) s3 s4 (Z_to_bv 64 FB) s6 s7 s8 s9 s10 (Z_to_bv 64 SHF) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x88e3c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 sp cP a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 FB) s3 s4 (Z_to_bv 64 FB) s6 s7 s8 s9 s10 (Z_to_bv 64 SHF) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88d7c) fc None m (seg_rom b0segs)).
  Proof.
    intros m sh h0 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s6 s7 s8 s9 s10 t3 t4 t5 t6 L32 SHU HD MI K.
    unfold CEILv, SH_LO, SH_HI, apartv in *. bz_ceil. box_ors.
    pose proof (munch_refl b2d_WE1 m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold b2d_WE1 in MU.
    pose proof (rw_cells_of_u8arr b0segs m SHF sh SHU) as SHC. replace (length sh) with 32%nat in SHC by lia. clear SHU.
    apply (rw_cells_split_CB b0segs _ _ [] 32 _ [] (repeat 1%nat 32)) in SHC; [| reflexivity].
    cbn [repeat mk_CB_cells app] in SHC.
    repeat (match type of SHC with context [CB 1 (firstn ?a ?b)] => let v := fresh "shb" in set (v := firstn a b) in SHC; clearbody v end).
    (* [comment removed for export] *)
    wstep. do 10 sbl.
    (* [comment removed for export] *)
    wstep. wstep. wstep. lit_store.
    (* [comment removed for export] *)
    wstep. dead.
    (* [comment removed for export] *)
    wstep. do 32 sbl.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (K mm) end; [unfold b2c_sh_f5, sf5b; exact SHC| exact HD| assumption| unfold b2d_WE1; exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_b2d_E1b : forall (m : amem) (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    ro_cells b0segs m (FB + 248) [C8 (Z_to_bv 64 FL)] ->
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 FB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88e40) fc None m (seg_rom b0segs)) ->
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 (Z_to_bv 64 FB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88e3c) fc None m (seg_rom b0segs)).
  Proof.
    intros m ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FLP K.
    unfold CEILv in *. bz_ceil.
    wstep. exact K.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_b2d_E2 : forall (m : amem) (b1 : byte) (ra spw t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m FL [C1 b1] -> mem_inv b0segs m ->
    (forall m', rw_cells b0segs m' FL [C1 z8] -> mem_inv b0segs m' -> munch [(FL, FL + 1)]%Z m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x88e44) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 FL) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88e40) fc None m (seg_rom b0segs)).
  Proof.
    intros m b1 ra spw t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 FLG MI K.
    pose proof (munch_refl [(FL, FL + 1)]%Z m) as MU. pose proof (wmono_refl b0segs m) as WM.
    sbz.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (K mm) end; [exact FLG| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_b2d_E3 : forall (m : amem) (v0 v8 v16 v24 v32 v40 v48 : word) (c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra : word)
      (ra spw t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m P (WSLOTS v0 v8 v16 v24 v32 v40 v48) -> stk b0segs m (P + 56) (usp + -104) ->
    rw_cells b0segs m (usp + -104) (HSAVED c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra) -> stk b0segs m lo P ->
    (stk b0segs m lo usp ->
       evt b0segs Q (MS (mkR cra sp gp tp t0 t1 t2 c0 c1 s4 a1 a2 a3 a4 a5 a6 a7 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 t3 t4 t5 t6)
                        F (ret_pc cra) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra spw gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88e44) fc None m (seg_rom b0segs)).
  Proof.
    intros m v0 v8 v16 v24 v32 v40 v48 c11 c10 c9 c8 c7 c6 c5 c4 c3 c2 c1 c0 cra ra spw t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SL GAP SAV ST K.
    unfold CEILv in *. bz_ceil.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RSP.
    unfold WSLOTS in SL. unfold HSAVED in SAV.
    (* [comment removed for export] *)
    wstep. wstep. wstep. do 13 wstep. wstep.
    pose proof (stk_of_rw_cells b0segs _ _ _ SL) as K0. cbn [cells_size csize Nat.add] in K0. change (Z.of_nat 56) with 56%Z in K0.
    pose proof (stk_of_rw_cells b0segs _ _ _ SAV) as K5. cbn [cells_size csize Nat.add] in K5. change (Z.of_nat 104) with 104%Z in K5.
    pose proof (stk_join b0segs m lo P P (P + 56) ST K0 eq_refl ltac:(lia)) as ST1.
    pose proof (stk_join b0segs m lo (P + 56) (P + 56) (usp + -104) ST1 GAP eq_refl ltac:(lia)) as ST2.
    pose proof (stk_join b0segs m lo (usp + -104) (usp + -104) (usp + -104 + 104) ST2 K5 eq_refl ltac:(lia)) as ST3.
    replace (usp + -104 + 104)%Z with usp in ST3 by lia.
    replace (Z_to_bv 64 (usp + -160 + 160)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    (* [comment removed for export] *)
    wstep. exact (K ST3).
  Qed.

End B0FWRW.
End ACeilS1.

