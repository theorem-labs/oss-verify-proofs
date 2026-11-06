(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem Atp_defsA Atp_kitA Atp_arrlA Atp_objdA Atp_objfA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma sub_fp_b16 : forall q b out f, q + -272 <= b -> b <= q -> sub_fp [(b + -16, b)] (obj_W q out f).
Proof. intros q b out f H1 H2 x Hx. unfold obj_W in Hx. cbn [outside] in *. lia. Qed.

Definition obj_WL (b : Z) : list (Z * Z) := [(b + -16, b + 152)].
Lemma sub_fp_b16L : forall b, sub_fp [(b + -16, b)] (obj_WL b).
Proof. intros b x Hx. unfold obj_WL in Hx. cbn [outside] in *. lia. Qed.

Section ObjPro.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_p1 : forall (K : machine_state -> Prop) (q out node P L : Z)
      (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv bsegs m -> stk bsegs m (ae_lo E) q -> ae_lo E + 272 <= q -> q mod 16 = 0 -> q <= ae_hi E -> 0 <= out < 2^64 ->
    client_consts m ->
    (forall (d : Z) (m1 : mem) (jA jH : list byte) (xa1 xa2 : word), (d = 0 \/ d = 16) -> (q + -256 - d) mod 32 = 0 ->
       munch (obj_W0 q) m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> stk bsegs m1 (ae_lo E) (q + -256 - d) ->
       rw_cells bsegs m1 (q + -256 - d) [CB 152 jA] ->
       rw_cells bsegs m1 (q + -104 - d) [CB (Z.to_nat d) jH] ->
       rw_cells bsegs m1 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       K (MS (mkR (wz OBJ_SM1_RA) (wz (q + -256 - d)) gp (wz TPV) t0 t1 t2 (wz q) (wz (q + -256 - d)) (wz 96) xa1 xa2 (wz L) a4 a5 a6 a7
                  (wz out) s3 (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz e_stack_malloc_1) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (lvl_entry ATP_OBJ_A ra q gp t0 t1 t2 s0 s1 out node P L a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof using OK.
    intros until m. intros MI ST LO Q16 QH OUTR (G1 & G2 & G3 & G4) HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
    unfold lvl_entry, ATP_OBJ_A, OBJ_SM1_RA, e_stack_malloc_1 in *.
    pose proof (munch_refl (obj_W0 q) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold obj_W0 in MU.
    destruct (obj_land_m32u (q + -256) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (d & Hd & LAND & B32).

    step.
    destruct Hd as [-> | ->].
    -
      carve_frame 256%nat ST.
      apply (rw_cells_split_CB bsegs _ _ [] 256 junk [] [152; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.

      lstep. do 13 step. astep. astep. rewrite LAND. replace (q + -256 - 0) with (q + -256) by lia.
      step. step. step. step.

      step. step. step. step. step. step. step. step. if_false. astep. step.
      name_mem m1.
      apply (proj1 (rw_cells_app bsegs m1 _ [_; _] _)) in FR. destruct FR as [LOC SAVED]. cbn [cells_size csize Nat.add] in SAVED.
      replace (q + -256 + Z.of_nat 152) with (q + -104) in SAVED by lia.
      lazymatch type of LOC with rw_cells _ _ _ [?c0; ?c1] => pose proof (rw_cells_merge bsegs m1 _ [] [c0; c1] [] LOC) as LOC' end.
      cbn [cells_size csize Nat.add app] in LOC'.
      eapply evt_eq; [| apply evt_done; eapply (HK 0 m1 _ [] _ _)];
        [ atp_st_eq | left; reflexivity | exact B32 | exact MU | exact WM | assumption
        | replace (q + -256 - 0) with (q + -256) by lia; assumption
        | replace (q + -256 - 0) with (q + -256) by lia; exact LOC'
        | replace (q + -104 - 0) with (q + -104) by lia; apply rw_cells_nil_CB'; lia
        | exact SAVED ].
    -
      carve_frame 256%nat ST.
      apply (rw_cells_split_CB bsegs _ _ [] 256 junk [] [136; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
      destruct (stk_carve bsegs m (ae_lo E) (q + -256) 16 ST ltac:(lia)) as [ST2 [jl LOWc]]. clear ST. change (Z.of_nat 16) with 16 in ST2, LOWc.
      replace (q + -256 - 16) with (q + -272) in ST2, LOWc by lia.
      lstep. do 13 step. astep. astep. rewrite LAND. replace (q + -256 - 16) with (q + -272) by lia.
      step. step. step. step.
      step. step. step. step. step. step. step. step. if_false. astep. step.
      name_mem m1.
      apply (proj1 (rw_cells_app bsegs m1 _ [_; _] _)) in FR. destruct FR as [MID REST]. cbn [cells_size csize Nat.add] in REST.
      replace (q + -256 + Z.of_nat 136) with (q + -120) in REST by lia.
      apply (proj1 (rw_cells_app bsegs m1 _ [_] _)) in REST. destruct REST as [HIGH SAVED]. cbn [cells_size csize Nat.add] in SAVED.
      replace (q + -120 + Z.of_nat 16) with (q + -104) in SAVED by lia.
      lazymatch type of MID with rw_cells _ _ _ ?cs => assert (LOC : rw_cells bsegs m1 (q + -272) ([CB 16 jl] ++ cs)) end.
      { apply (proj2 (rw_cells_app bsegs m1 (q + -272) [CB 16 jl] _)). split; [exact LOWc|]. cbn [cells_size csize Nat.add].
        replace (q + -272 + Z.of_nat 16) with (q + -256) by lia. exact MID. }
      cbn [app] in LOC.
      lazymatch type of LOC with rw_cells _ _ _ [?c0; ?c1; ?c2] =>
        pose proof (rw_cells_merge bsegs m1 _ [] [c0; c1; c2] [] LOC) as LOC' end.
      cbn [cells_size csize Nat.add app] in LOC'.
      eapply evt_eq; [| apply evt_done; eapply (HK 16 m1 _ _ _ _)];
        [ atp_st_eq | right; reflexivity | exact B32 | exact MU | exact WM | assumption
        | replace (q + -256 - 16) with (q + -272) by lia; exact ST2
        | replace (q + -256 - 16) with (q + -272) by lia; exact LOC'
        | replace (q + -104 - 16) with (q + -120) by lia; exact HIGH
        | exact SAVED ].
  Qed.

  Lemma obj_p2a : forall (K : machine_state -> Prop) (q d out node P L f : Z)
      (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jA h0 h1 h2 js : list byte),
    mem_inv bsegs m -> (d = 0 \/ d = 16) -> ae_lo E + 272 <= q -> q <= ae_hi E ->
    f mod 64 = 0 -> 0x6d9000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    rw_cells bsegs m (q + -256 - d) [CB 152 jA] ->
    rw_cells bsegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells bsegs m (shad f) [CB 16 js] ->
    (forall (m1 : mem) (xa0 xa1 xa2 xa3 xa4 : word) (j0 jB js4 : list byte),
       munch [(q + -256 - d, q + -104 - d); (f, f + 24); (shad f, shad f + 16)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (q + -256 - d) [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 64 jB; C8 (Z_to_bv 64 P); C8 (Z_to_bv 64 L)] ->
       rw_cells bsegs m1 f [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1335b); C8 (Z_to_bv 64 0xb867c)] ->
       rw_cells bsegs m1 (shad f) [C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13)))); CB 4 js4] ->
       K (MS (mkR (wz OBJ_SM1_RA) (wz (q + -256 - d)) gp (wz TPV) t0 t1 t2 (wz q) (wz (q + -256 - d)) xa0 xa1 xa2 xa3 xa4 (wz f) a6 a7
                  (wz out) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz 0xb87a8) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz OBJ_SM1_RA) (wz (q + -256 - d)) gp (wz TPV) t0 t1 t2 (wz q) (wz (q + -256 - d)) (wz f) a1 a2 a3 a4 a5 a6 a7
                       (wz out) s3 (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz OBJ_SM1_RA) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until js. intros MI Hd LO QH F64 FLO FHI FSH S0 SHI LOC HDR SH HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OBJ_SM1_RA in *.
    pose proof (munch_refl [(q + -256 - d, q + -104 - d); (f, f + 24); (shad f, shad f + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold shad, SHB in *.
    apply (rw_cells_split_CB bsegs _ _ [] 16 js [] [1;1;1;1;1;1;1;1;1;1;1;1;4]%nat) in SH; [| reflexivity]. cbn [mk_CB_cells app] in SH.
    repeat match type of SH with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jz" in set (j := t) in SH; clearbody j end.
    apply (rw_cells_split_CB bsegs _ _ [] 152 jA [] [40; 8; 8; 8; 8; 64; 8; 8]%nat) in LOC; [| reflexivity]. cbn [mk_CB_cells app] in LOC.
    repeat match type of LOC with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jl" in set (j := t) in LOC; clearbody j end.

    step. step. step. if_cases K0; zify_cond K0; [clear K0| exfalso; rewrite ?land64_mod in K0; clear - K0 FLO FHI LOW; lia].

    step. step. step. astep. astep. astep. step. astep. astep. astep. astep. astep. astep. lstep. lstep. step. lstep. astep. astep.

    do 12 nstep.

    step. step.
    name_mem m1.
    eapply evt_eq; [| apply evt_done; eapply (HK m1); [exact MU| exact WM| assumption| exact LOC| exact HDR| exact SH]]. atp_st_eq.
  Qed.

  Definition obj_locB (j0 jB : list byte) (f out : Z) (pv lv : word) : list cell :=
    [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 64 jB; C8 pv; C8 lv].

  Lemma obj_p2b : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q b out node P f : Z) (ptr : list Z)
      (gp t0 t1 t2 xa0 xa1 xa2 xa3 xa4 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word) (j0 jB : list byte),
    mem_inv bsegs m -> stk bsegs m (ae_lo E) b -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> b mod 32 = 0 -> q <= ae_hi E ->
    ae_lo E <= out -> out + 24 <= ae_hi E -> 0 <= f -> 0 <= node < 2^64 ->
    ptr_atA E P ptr -> AINV_A E m ->
    (ptr <> [] -> acc bsegs m (ae_PB E) (ae_NPB E)) ->
    rw_cells bsegs m b (obj_locB j0 jB f out (Z_to_bv 64 P) (Z_to_bv 64 (zlength ptr))) ->
    (forall m', munch (obj_WL b) m m' -> wmono bsegs m m' -> shb_cells m') ->
    (forall m', munch (obj_WL b) m m' -> wmono bsegs m m' -> shz m' b 152) ->

    (forall (ya3 ya4 : word), ptr = [] ->
       evt bsegs K (MS (mkR (wz 0xb88a0) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz out) (wz node) (wz 16) ya3 ya4 (wz f) a6 a7
                          (wz out) (wz (shad f)) (wz node) (wz 0) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz e_asan_memcpy) fc None m (seg_rom bsegs))) ->

    (forall (ya3 ya4 : word) (c0 : Z) (ptr0 : list Z), ptr = c0 :: ptr0 -> c0 <> 47 ->
       evt bsegs K (MS (mkR (wz 0xb88d4) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz out) (wz 0) (wz 16) ya3 ya4 (wz f) a6 a7
                          (wz out) (wz (shad f)) (wz (out + 16)) (wz (zlength ptr)) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz e_asan_memset) fc None m (seg_rom bsegs))) ->

    (forall (m' : mem) (ya1 ya2 ya4 ya5 : word), ptr = [47] ->
       munch (obj_WL b) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) b ->
       rw_cells bsegs m' b (obj_locB j0 jB f out (Z_to_bv 64 (P + 1)) (Z_to_bv 64 0)) ->
       evt bsegs K (MS (mkR (wz 0xb87f8) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz 18446744073709551615) ya1 ya2 (wz 0) ya4 ya5 a6 a7
                          (wz out) (wz (shad f)) (wz node) (wz (zlength ptr)) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz 0xb87f8) fc None m' (seg_rom bsegs))) ->

    (forall (m' : mem) (ya3 ya4 ya5 : word) (c1 : Z) (ptr1 : list Z), ptr = 47 :: c1 :: ptr1 ->
       munch (obj_WL b) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) (b + -16) ->
       rw_cells bsegs m' (b + -16) [C8 (wz q); C8 (wz 0xb87f8)] ->
       rw_cells bsegs m' b (obj_locB j0 jB f out (Z_to_bv 64 (P + 1)) (Z_to_bv 64 (zlength ptr1 + 1))) ->
       evt bsegs K (MS (mkR (wz 0xb915c) (wz (b + -16)) gp (wz TPV) t0 t1 t2 (wz (P + 1)) (wz b) (wz (P + 1)) (wz 47) (wz (zlength ptr1 + 1)) ya3 ya4 ya5 a6 a7
                          (wz out) (wz (shad f)) (wz node) (wz (zlength ptr)) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz e_memchr) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz OBJ_SM1_RA) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) xa0 xa1 xa2 xa3 xa4 (wz f) a6 a7
                       (wz out) (wz (shad f)) (wz node) (wz (zlength ptr)) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb87a8) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jB. intros MI ST LO BL BH B32 QH OLO OHI F0 NDR PAT AI ACCP LOC SHBW SHZLW XCPY XSET XNPOS XCHR.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L _ _ PTRR P0' _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OBJ_SM1_RA in *.
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & PTRF & PP0 & PP1 & PL). hide AI.
    pose proof (zlength_nonneg ptr) as ZL. pose proof (zlength_nonneg (ae_p1 E)) as ZL1.
    pose proof (munch_refl (obj_WL b) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold obj_WL in MU.
    assert (B16 : b mod 16 = 0) by (clear - B32; Z.div_mod_to_equations; lia).
    unfold obj_locB in LOC.

    step. if_cases K0; zify_cond K0.
    {
      step. step. if_dead1 by OLO LOW. astep. step. step. step.
      eapply evt_eq; [| eapply XCPY]; [unfold e_asan_memcpy; rewrite K0; atp_st_eq|].
      destruct ptr as [|cx lx]; [reflexivity| exfalso; rewrite zlength_cons in K0; pose proof (zlength_nonneg lx); lia]. }
    destruct ptr as [|c0 ptr0]; [exfalso; apply K0; reflexivity|].
    assert (NE0 : c0 :: ptr0 <> []) by discriminate. specialize (ACCP NE0).
    pose proof (lvl_ptr_range E OK P _ PAT NE0) as (PB0 & PB1 & PB2 & PB3).
    assert (C0R : 0 <= c0 < 256) by (inversion PTRF; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg ptr0) as ZL0.
    pose proof (zbytes_read1 m P (c0 :: ptr0) 0 PTRB ltac:(rewrite zlength_cons; lia)) as RD0.
    change (nth (Z.to_nat 0) (c0 :: ptr0) 0) with c0 in RD0. rewrite Z.add_0_r in RD0.

    step. step. if_dead1 by PB0 PB1.

    assert (JA : forall ya1 ya2 : word,
      evt bsegs K
        (MS (mkR (Z_to_bv 64 0xb86f8) (Z_to_bv 64 b) gp (Z_to_bv 64 TPV) t0 t1 t2 (Z_to_bv 64 q) (Z_to_bv 64 b) (Z_to_bv 64 P) ya1 ya2 xa3 xa4 (Z_to_bv 64 f) a6 a7
                 (Z_to_bv 64 out) (Z_to_bv 64 (shad f)) (Z_to_bv 64 node) (Z_to_bv 64 (zlength ptr0 + 1)) (Z_to_bv 64 P) s7 s8 s9 s10 (Z_to_bv 64 2147450880) t3 t4 t5 t6)
            F (Z_to_bv 64 0xb87c4) fc None m (seg_rom bsegs))).
    { intros ya1 ya2.

      astep. astep. step. if_cases K1; zify_cond K1.
      {
        step. step. if_dead1 by OLO LOW. astep. astep. astep. step.
        eapply evt_eq; [| eapply (XSET _ _ c0 ptr0)]; [unfold e_asan_memset; rewrite ?zlength_cons; atp_st_eq| reflexivity| exact K1]. }
      subst c0.

      astep. astep. astep. step.
      pose proof LOC as SV1.
      apply (proj1 (rw_cells_app bsegs m _ [_; _; _; _; _; _] _)) in SV1. destruct SV1 as [_ SV1]. cbn [cells_size csize Nat.add] in SV1.
      replace (b + Z.of_nat 136) with (b + 136) in SV1 by lia.
      hide LOC.
      eapply evt_eq; [| eapply (substr_cps E OK K m F fc b (b + 136) P (zlength ptr0 + 1) 1 18446744073709551615 (zlength ptr0 + 1 - 1) 0xb87e0);
        [ exact SV1| lia| lia| clear - B32; Z.div_mod_to_equations; lia| lia| lia| lia| left; split; reflexivity| exact (SHBW m MU WM)
        | intros m' MU' WM'; apply (shz_sub m' b 152); [exact (SHZLW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_b16L b) MU')) (wmono_trans bsegs _ _ _ WM WM'))| lia| lia]
        | exact ST| lia| lia| exact B16| exact MI| lia| reflexivity| ] ]; [atp_st_eq|].
      clear ST MI. intros m2 xb2 xb3 xb4 xb5 MU12 WM12 MI2 ST2.
      unhide LOC. clear SV1 RD0 PTRB.
      transport_after_call bsegs m m2 MU12 WM12. clear MU12 WM12.
      replace (zlength ptr0 + 1 - 1) with (zlength ptr0) by lia.

      step. step. astep. astep. astep. step.
      name_mem m3.
      lazymatch goal with H : rw_cells bsegs m3 b _ |- _ => rename H into LOC3 end.
      lazymatch goal with H : stk bsegs m3 _ _ |- _ => rename H into ST3 end.
      lazymatch goal with H : mem_inv bsegs m3 |- _ => rename H into MI3 end.
      pose proof LOC3 as SV3.
      apply (proj1 (rw_cells_app bsegs m3 _ [_; _; _; _; _; _] _)) in SV3. destruct SV3 as [_ SV3]. cbn [cells_size csize Nat.add] in SV3.
      replace (b + Z.of_nat 136) with (b + 136) in SV3 by lia.
      hide LOC3.
      eapply (svfind_cps E OK K m3 F fc b (b + 136) (P + 1) (zlength ptr0) 47 0xb87f8);
        [ exact SV3| lia| lia| clear - B32; Z.div_mod_to_equations; lia| lia| lia| lia| lia| exact (SHBW m3 MU WM)
        | intros m' MU' WM'; apply (shz_sub m' b 152); [exact (SHZLW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_b16L b) MU')) (wmono_trans bsegs _ _ _ WM WM'))| lia| lia]
        | exact ST3| lia| lia| exact B16| exact MI3| lia| reflexivity| | ].
      -
        clear ST3 MI3. intros m4 ya1' ya2' ya4' ya5' N0 MU34 WM34 MI4 ST4. unhide LOC3.
        pose proof (rw_cells_transport bsegs _ m3 m4 _ _ LOC3 MU34 WM34 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia)) as LOC4.
        destruct ptr0 as [|cx lx]; [| exfalso; rewrite zlength_cons in N0; pose proof (zlength_nonneg lx); lia].
        rewrite zlength_nil in *.
        eapply evt_eq; [| eapply (XNPOS m4)];
          [ atp_st_eq| reflexivity
          | exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_b16L b) MU34))| exact (wmono_trans bsegs _ _ _ WM WM34)
          | exact MI4| exact ST4| unfold obj_locB; replace (0 + 1) with 1 in LOC4 by lia; exact LOC4 ].
      -
        clear ST3 MI3. intros m4 ya3' ya4' ya5' N1 MU34 WM34 MI4 ST4 FF4. unhide LOC3.
        pose proof (rw_cells_transport bsegs _ m3 m4 _ _ LOC3 MU34 WM34 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia)) as LOC4.
        destruct ptr0 as [|c1 ptr1]; [exfalso; rewrite zlength_nil in N1; lia|]. rewrite zlength_cons in *.
        eapply evt_eq; [| eapply (XCHR m4 _ _ _ c1 ptr1)];
          [ atp_st_eq| reflexivity
          | exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_b16L b) MU34))| exact (wmono_trans bsegs _ _ _ WM WM34)
          | exact MI4| exact ST4| exact FF4| unfold obj_locB; exact LOC4 ]. }

    destruct (acc_read1 m (ae_PB E) (ae_NPB E) P ACCP ltac:(lia)) as (b0 & RDS0 & OK0).
    destruct (sh_ok_cases b0 P OK0) as [-> | (k0 & -> & K0x & KM0)].
    - astep. astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply JA]; [atp_st_eq].
    - astep. astep. step. rewrite (sxb_small7 k0) by lia. step. if_dead2 by K0x. astep. step. if_dead2 by K0x KM0 PB0 PB1. eapply evt_eq; [| eapply JA]; [atp_st_eq].
  Qed.

  Lemma obj_p3 : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q b out node P f P1 L1 sl Lk : Z) (L : Z)
      (gp t0 t1 t2 xa1 xa2 xa3 xa4 xa5 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word) (j0 jB : list byte),
    mem_inv bsegs m -> stk bsegs m (ae_lo E) b -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> b mod 32 = 0 -> q <= ae_hi E -> 0 <= f ->
    0 < P1 -> 0 <= L1 -> P1 + L1 < 2^47 ->
    ((sl = 18446744073709551615 /\ Lk = L1) \/ (0 <= sl < L1 /\ Lk = sl)) ->
    rw_cells bsegs m b (obj_locB j0 jB f out (Z_to_bv 64 P1) (Z_to_bv 64 L1)) ->
    (forall m', munch (obj_WL b) m m' -> wmono bsegs m m' -> shb_cells m') ->
    (forall m', munch (obj_WL b) m m' -> wmono bsegs m m' -> shz m' b 152) ->
    (forall (m' : mem) (ya3 ya4 ya5 : word) (jB' : list byte),
       munch (obj_WL b) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) b ->
       rw_cells bsegs m' b [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 48 jB';
                           C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 L1)] ->
       evt bsegs K (MS (mkR (wz 0xb8824) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz (b + 96)) (wz 0) (wz 16) ya3 ya4 ya5 a6 a7
                          (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz e_asan_memset) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb87f8) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz sl) xa1 xa2 xa3 xa4 xa5 a6 a7
                       (wz out) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb87f8) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jB. intros MI ST LO BL BH B32 QH F0 P10 L10 PL1 SL LOC SHBW SHZLW XMS.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (obj_WL b) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold obj_WL in MU.
    assert (B16 : b mod 16 = 0) by (clear - B32; Z.div_mod_to_equations; lia).
    assert (SLR : 0 <= sl < 2^64) by lia.
    unfold obj_locB in LOC.

    step. astep. astep. step. step.
    pose proof LOC as SV1.
    apply (proj1 (rw_cells_app bsegs m _ [_; _; _; _; _; _] _)) in SV1. destruct SV1 as [_ SV1]. cbn [cells_size csize Nat.add] in SV1.
    replace (b + Z.of_nat 136) with (b + 136) in SV1 by lia.
    hide LOC.
    eapply evt_eq; [| eapply (substr_cps E OK K m F fc b (b + 136) P1 L1 0 sl Lk 0xb880c);
      [ exact SV1| lia| lia| clear - B32; Z.div_mod_to_equations; lia| lia| lia| lia
      | destruct SL as [[A1 A2]|[A1 A2]]; [left| right]; split; lia
      | exact (SHBW m MU WM)
      | intros m' MU' WM'; apply (shz_sub m' b 152); [exact (SHZLW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_b16L b) MU')) (wmono_trans bsegs _ _ _ WM WM'))| lia| lia]
      | exact ST| lia| lia| exact B16| exact MI| lia| reflexivity| ] ]; [atp_st_eq|].
    clear ST MI. intros m2 xb2 xb3 xb4 xb5 MU12 WM12 MI2 ST2.
    unhide LOC. clear SV1.
    transport_after_call bsegs m m2 MU12 WM12. clear MU12 WM12.
    replace (P1 + 0) with P1 by lia.

    step. step. astep. astep. astep. step.
    name_mem m3.
    lazymatch goal with H : rw_cells bsegs m3 b _ |- _ => rename H into LOC3 end.
    lazymatch goal with H : stk bsegs m3 _ _ |- _ => rename H into ST3 end.
    lazymatch goal with H : mem_inv bsegs m3 |- _ => rename H into MI3 end.
    eapply evt_eq; [| eapply (XMS m3)]; [unfold e_asan_memset; atp_st_eq| exact MU| exact WM| exact MI3| exact ST3| exact LOC3].
  Qed.

  Lemma obj_p4 : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q b out node P f P1 L1 sl Lk : Z) (L : Z)
      (gp t0 t1 t2 xa1 xa2 xa3 xa4 xa5 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word) (j0 jC : list byte) (zb j2 : list byte),
    mem_inv bsegs m -> stk bsegs m (ae_lo E) b -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> b mod 32 = 0 -> q <= ae_hi E -> 0 <= f ->
    0 < P1 -> 0 <= Lk -> P1 + Lk < 2^47 -> 0 <= sl < 2^64 ->
    rw_cells bsegs m b [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 24 jC; CB 16 zb; CB 8 j2;
                       C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 L1)] ->
    (forall m', munch (obj_WL b) m m' -> wmono bsegs m m' -> shb_cells m') ->
    (forall m', munch (obj_WL b) m m' -> wmono bsegs m m' -> shz m' b 152) ->

    (forall (m' : mem) (ya1 ya2 ya4 ya5 : word) (j2' : list byte), Lk = 0 ->
       munch (obj_WL b) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) b ->
       rw_cells bsegs m' b [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 24 jC; CB 16 zb; C4 (Z_to_bv 64 12); CB 4 j2';
                           C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 L1)] ->
       evt bsegs K (MS (mkR (wz 0xb883c) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz 18446744073709551615) ya1 ya2 (wz Lk) ya4 ya5 a6 a7
                          (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz 0xb883c) fc None m' (seg_rom bsegs))) ->

    (forall (m' : mem) (ya3 ya4 ya5 : word) (j2' : list byte), 0 < Lk ->
       munch (obj_WL b) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) (b + -16) ->
       rw_cells bsegs m' (b + -16) [C8 (wz q); C8 (wz 0xb883c)] ->
       rw_cells bsegs m' b [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 24 jC; CB 16 zb; C4 (Z_to_bv 64 12); CB 4 j2';
                           C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 L1)] ->
       evt bsegs K (MS (mkR (wz 0xb915c) (wz (b + -16)) gp (wz TPV) t0 t1 t2 (wz P1) (wz b) (wz P1) (wz 126) (wz Lk) ya3 ya4 ya5 a6 a7
                          (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz e_memchr) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb8824) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz (b + 96)) xa1 xa2 xa3 xa4 xa5 a6 a7
                       (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb8824) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until j2. intros MI ST LO BL BH B32 QH F0 P10 LK0 PL1 SLR LOC SHBW SHZLW XNPOS XCHR.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (obj_WL b) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold obj_WL in MU.
    assert (B16 : b mod 16 = 0) by (clear - B32; Z.div_mod_to_equations; lia).

    astep. lstep. astep. astep. astep. step.
    name_mem m1.
    lazymatch goal with H : rw_cells bsegs m1 b _ |- _ => rename H into LOC1 end.
    lazymatch goal with H : stk bsegs m1 _ _ |- _ => rename H into ST1 end.
    lazymatch goal with H : mem_inv bsegs m1 |- _ => rename H into MI1 end.
    pose proof LOC1 as SV1.
    apply (proj1 (rw_cells_app bsegs m1 _ [_; _; _; _; _; _; _; _; _] _)) in SV1. destruct SV1 as [_ SV1]. cbn [cells_size csize Nat.add] in SV1.
    replace (b + Z.of_nat 120) with (b + 120) in SV1 by lia.
    apply (proj1 (rw_cells_app bsegs m1 _ [_; _] _)) in SV1. destruct SV1 as [SV1 _].
    hide LOC1.
    eapply (svfind_cps E OK K m1 F fc b (b + 120) P1 Lk 126 0xb883c);
      [ exact SV1| lia| lia| clear - B32; Z.div_mod_to_equations; lia| lia| lia| lia| lia| exact (SHBW m1 MU WM)
      | intros m' MU' WM'; apply (shz_sub m' b 152); [exact (SHZLW m' (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_b16L b) MU')) (wmono_trans bsegs _ _ _ WM WM'))| lia| lia]
      | exact ST1| lia| lia| exact B16| exact MI1| lia| reflexivity| | ].
    - clear ST1 MI1. intros m2 ya1 ya2 ya4 ya5 N0 MU12 WM12 MI2 ST2. unhide LOC1.
      pose proof (rw_cells_transport bsegs _ m1 m2 _ _ LOC1 MU12 WM12 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia)) as LOC2.
      eapply evt_eq; [| eapply (XNPOS m2)];
        [ atp_st_eq| exact N0
        | exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_b16L b) MU12))| exact (wmono_trans bsegs _ _ _ WM WM12)
        | exact MI2| exact ST2| exact LOC2 ].
    - clear ST1 MI1. intros m2 ya3 ya4 ya5 N1 MU12 WM12 MI2 ST2 FF2. unhide LOC1.
      pose proof (rw_cells_transport bsegs _ m1 m2 _ _ LOC1 MU12 WM12 ltac:(cbn [disjoint_from cells_size csize Nat.add length fst snd]; lia)) as LOC2.
      eapply evt_eq; [| eapply (XCHR m2)];
        [ atp_st_eq| exact N1
        | exact (munch_trans _ _ _ _ MU (munch_weaken _ _ _ _ (sub_fp_b16L b) MU12))| exact (wmono_trans bsegs _ _ _ WM WM12)
        | exact MI2| exact ST2| exact FF2| exact LOC2 ].
  Qed.

  Lemma obj_p5a : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q b out node P f P1 L1 sl Lk te : Z) (L : Z)
      (x1 gp t0 t1 t2 xa1 xa2 xa3 xa4 xa5 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word) (j0 jC zb j2 : list byte),
    mem_inv bsegs m -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E ->
    ((te = 18446744073709551615) \/ (0 <= te < Lk /\ Lk < 2^47)) ->
    rw_cells bsegs m b [CB 40 j0; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f); CB 24 jC; CB 16 zb; C4 (Z_to_bv 64 12); CB 4 j2;
                       C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 L1)] ->

    (te = 18446744073709551615 ->
       evt bsegs K (MS (mkR (wz 0xb8904) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz (b + 72)) (wz node) (wz P1) (wz Lk) xa4 xa5 a6 a7
                          (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz ATP_ATKEY_A) fc None m (seg_rom bsegs))) ->

    (0 <= te < Lk ->
       evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz te) (wz 18446744073709551615) xa2 xa3 xa4 xa5 a6 a7
                          (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz 0xb8844) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz te) xa1 xa2 xa3 xa4 xa5 a6 a7
                       (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb883c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until j2. intros MI BL BH QH TE LOC XKEY XESC.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold ATP_ATKEY_A in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.

    astep. step. if_cases KT; zify_cond KT; rewrite ?land64_mod in KT.
    -
      step. step. astep. step. step.
      eapply evt_eq; [| eapply XKEY]; [atp_st_eq| destruct TE as [T|[T U]]; [exact T| exfalso; clear - KT T U; lia]].
    - eapply evt_eq; [| eapply XESC]; [atp_st_eq| destruct TE as [T|[T LK]]; [exfalso; clear - KT T; lia| exact T]].
  Qed.
End ObjPro.
