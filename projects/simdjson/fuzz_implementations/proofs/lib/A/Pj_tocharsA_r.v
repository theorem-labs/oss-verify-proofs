(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP StoreFast.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjPjNum SjPjDig.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_implementations.lib.A Require Import Layout Shadow RT_iface RT_iface2 D_defs D_kit Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem
     Sj_num_aframe Sj_num_lm_kit Sj_num_lm_pro Pj_defsA Pj_tocharsA_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac solve_load ::= first [ solve_load_base | asan_load_hook | asan_zc_hook | num_load_hook | solve_load_image ].
Local Ltac solve_store ::= first [ num_solve_store0 | num_store_hook ].

Section Rel.
  Variable J : tcI.
  Hypothesis OK : tc_ok J.
  Variable mb : mem.
  Variable Q : machine_state -> Prop.

  Notation q := (ti_q J). Notation spq := (ti_spq J). Notation NB := (ti_NB J). Notation f := (ti_f J). Notation Sh := (ti_S J). Notation lo := (ti_lo J).
  Notation TCS pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc m :=
    (MS (mkR xra (Z_to_bv 64 spq) (ti_gp J) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 q) (Z_to_bv 64 spq) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
              (Z_to_bv 64 f) xs3 xs4 xs5 (Z_to_bv 64 Sh) (Z_to_bv 64 f) (Z_to_bv 64 2147450880) xs9 (ti_s10 J) (ti_s11 J) xt3 xt4 xt5 xt6)
        xF (Z_to_bv 64 pc) xfc None m (seg_rom asegs)).

  Lemma tc_rel1 : forall xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc (mm : mem),
    TINV J sh_poison mb mm ->
    (forall mm', TINV J sh_f5 mb mm' ->
       evt asegs Q (TCS 0xbe50c xra xt0 xt1 xt2 xa0 (Z_to_bv 64 (-11)) xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc mm')) ->
    evt asegs Q (TCS 0xbe4c8 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros TI HK. ti_open TI. ti_env OK. unfold tc_W, ti_spq, ti_S in MU. unfold sh_poison, pz in SH.
    do 17 astep.
    apply HK. ti_close.
  Qed.

  Lemma tc_rel2 : forall (e fl : Z) xra xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc (mm : mem),
    TINV J sh_f5 mb mm ->
    ro_cells asegs mm (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells asegs mm fl [C1 (Z_to_bv 8 1)] ->
    (0 < fl)%Z -> (fl + 1 <= lo)%Z -> (fl + 1 <= NB \/ NB + 40 <= fl)%Z ->
    (forall xt0' xa1' (mm' : mem) (nb : list byte),
       munch [(fl, fl + 1)]%Z mm mm' -> wmono asegs mm mm' -> mem_inv asegs mm' -> stk asegs mm' lo q ->
       rw_cells asegs mm' fl [C1 (Z_to_bv 8 0)] -> rw_cells asegs mm' NB [CB 40 nb] ->
       Q (MS (mkR (ti_ra J) (Z_to_bv 64 q) (ti_gp J) (Z_to_bv 64 TPV_A) xt0' xt1 xt2 (ti_s0 J) (ti_s1 J) (Z_to_bv 64 e) xa1' xa2 xa3 xa4 xa5 xa6 xa7
                   (ti_s2 J) (ti_s3 J) (ti_s4 J) (ti_s5 J) (ti_s6 J) (ti_s7 J) (ti_s8 J) (ti_s9 J) (ti_s10 J) (ti_s11 J) xt3 xt4 xt5 xt6)
             (bvmap_set 8 (ti_fs0 J) xF) (ret_pc (ti_ra J)) xfc None mm' (seg_rom asegs))) ->
    evt asegs Q (TCS 0xbe50c xra xt0 xt1 xt2 (Z_to_bv 64 e) (Z_to_bv 64 (-11)) xa2 xa3 xa4 xa5 xa6 xa7 xs3 xs4 xs5 xs9 xt3 xt4 xt5 xt6 xF xfc mm).
  Proof using OK.
    intros until mm. intros TI LAST FLAG FL0 FL1 FLNB HK. ti_open TI. ti_env OK.
    clear MU WM HDR TA SH.
    pose proof (munch_refl [(fl, fl + 1)]%Z mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    unfold tc_saved in SAVED.
    astep. astep. astep.

    astep.
    do 12 astep. astep. replace (q + -128 + 128)%Z with q by lia. astep.

    pose proof (stk_release asegs _ lo _ _ ST LOC ltac:(lia)) as ST1.
    lazymatch type of ST1 with stk _ _ _ ?hi => replace hi with (q + -96)%Z in ST1 by (destruct (c_d J OK) as [Ed | Ed]; rewrite Ed; cbn; lia) end.
    pose proof (stk_release asegs _ lo _ _ ST1 SAVED ltac:(lia)) as ST2. cbn [cells_size csize Nat.add] in ST2.
    replace (q + -96 + Z.of_nat 96)%Z with q in ST2 by lia.
    apply evt_done. eapply HK; [exact MU| exact WM| exact MI| exact ST2| exact FLAG|].
    rewrite <- NL. exact (rw_cells_of_u8arr asegs _ _ _ NA).
  Qed.
End Rel.
