(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Sj_num_amem. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma find_or_foundM : forall y x, 0 < y -> Z.lor ((Z.b2z (0 <? y) + -1) mod 18446744073709551616) x = x.
Proof.
  intros y x Hy. replace (0 <? y) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0.
  apply Z.lor_0_l.
Qed.
Lemma find_or_nposM : forall x, 0 <= x < 2^64 -> Z.lor ((Z.b2z (0 <? 0) + -1) mod 18446744073709551616) x = 18446744073709551615.
Proof.
  intros x Hx. cbn [Z.ltb Z.compare Z.b2z]. change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
  pose proof (Z.add_lor_land 18446744073709551615 x) as EQ.
  rewrite (Z.land_comm 18446744073709551615 x) in EQ. rewrite land64_mod, Z.mod_small in EQ by lia. lia.
Qed.

Section ObjPro.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_p1 : forall (K : machine_state -> Prop) (q out node P L : Z)
      (ra gp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv asegs m -> stk asegs m (ae_lo E) q -> ae_lo E + 304 <= q -> q mod 16 = 0 -> q <= ae_hi E -> 0 <= out < 2^64 ->
    client_consts m ->
    (forall (d : Z) (m1 : mem) (jA jB jH : list byte) (xa1 xa2 : word), (d = 0 \/ d = 16) -> (q + -288 - d) mod 32 = 0 ->
       munch (obj_W0 q) m m1 -> wmono asegs m m1 -> mem_inv asegs m1 -> stk asegs m1 (ae_lo E) (q + -288 - d) ->
       rw_cells asegs m1 (q + -288 - d) [CB 112 jA; C8 (Z_to_bv 64 out); CB 64 jB] ->
       rw_cells asegs m1 (q + -104 - d) [CB (Z.to_nat d) jH] ->
       rw_cells asegs m1 (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
       K (MS (mkR (wz OBJ_SM1_RA) (wz (q + -288 - d)) gp (wz TPV) t0 t1 t2 (wz q) (wz (q + -288 - d)) (wz 96) xa1 xa2 (wz L) a4 a5 a6 a7
                  s2 s3 (wz L) (wz P) s6 s7 (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz e_stack_malloc_1) fc None m1 (seg_rom asegs))) ->
    evt asegs K (lvl_entry ATP_OBJ_A ra q gp t0 t1 t2 s0 s1 out node P L a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m).
  Proof using OK.
    intros until m. intros MI ST LO Q16 QH OUTR (G1 & G2 & G3 & G4) HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    unfold g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return, SHB in G1, G2, G3, G4.
    unfold lvl_entry, ATP_OBJ_A, OBJ_SM1_RA, e_stack_malloc_1 in *.
    pose proof (munch_refl (obj_W0 q) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold obj_W0 in MU.
    destruct (obj_land_m32u (q + -288) ltac:(lia) ltac:(Z.div_mod_to_equations; lia)) as (d & Hd & LAND & B32).

    step.
    destruct Hd as [-> | ->].
    -
      carve_frame 288%nat ST.
      apply (rw_cells_split_CB asegs _ _ [] 288 junk [] [112; 8; 64; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.

      lstep. do 13 step. astep. astep. rewrite LAND. replace (q + -288 - 0) with (q + -288) by lia.
      step. step. step. step.

      step. step. step. step. step. step. step. step. if_false. astep. step.
      name_mem m1.
      apply (proj1 (rw_cells_app asegs m1 _ [_; _; _; _] _)) in FR. destruct FR as [LOC SAVED]. cbn [cells_size csize Nat.add] in SAVED.
      replace (q + -288 + Z.of_nat 184) with (q + -104) in SAVED by lia.
      lazymatch type of LOC with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3] =>
        pose proof (rw_cells_merge asegs m1 _ [] [c0; c1] [c2; c3] LOC) as LOC' end.
      cbn [cells_size csize Nat.add app] in LOC'.
      eapply evt_eq; [| apply evt_done; eapply (HK 0 m1 _ _ [] _ _)];
        [ atp_st_eq | left; reflexivity | exact B32 | exact MU | exact WM | exact MI
        | replace (q + -288 - 0) with (q + -288) by lia; exact ST
        | replace (q + -288 - 0) with (q + -288) by lia; exact LOC'
        | replace (q + -104 - 0) with (q + -104) by lia; apply rw_cells_nil_CB'; lia
        | exact SAVED ].
    -
      carve_frame 288%nat ST.
      apply (rw_cells_split_CB asegs _ _ [] 288 junk [] [96; 8; 64; 16; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
      repeat match type of FR with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jk" in set (j := t) in FR; clearbody j end.
      destruct (stk_carve asegs m (ae_lo E) (q + -288) 16 ST ltac:(lia)) as [ST2 [jl LOWc]]. clear ST. change (Z.of_nat 16) with 16 in ST2, LOWc.
      replace (q + -288 - 16) with (q + -304) in ST2, LOWc by lia.
      lstep. do 13 step. astep. astep. rewrite LAND. replace (q + -288 - 16) with (q + -304) by lia.
      step. step. step. step.
      step. step. step. step. step. step. step. step. if_false. astep. step.
      name_mem m1.
      apply (proj1 (rw_cells_app asegs m1 _ [_; _; _; _] _)) in FR. destruct FR as [MID REST]. cbn [cells_size csize Nat.add] in REST.
      replace (q + -288 + Z.of_nat 168) with (q + -120) in REST by lia.
      apply (proj1 (rw_cells_app asegs m1 _ [_] _)) in REST. destruct REST as [HIGH SAVED]. cbn [cells_size csize Nat.add] in SAVED.
      replace (q + -120 + Z.of_nat 16) with (q + -104) in SAVED by lia.
      lazymatch type of MID with rw_cells _ _ _ ?cs => assert (LOC : rw_cells asegs m1 (q + -304) ([CB 16 jl] ++ cs)) end.
      { apply (proj2 (rw_cells_app asegs m1 (q + -304) [CB 16 jl] _)). split; [exact LOWc|]. cbn [cells_size csize Nat.add].
        replace (q + -304 + Z.of_nat 16) with (q + -288) by lia. exact MID. }
      cbn [app] in LOC.
      lazymatch type of LOC with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4] =>
        pose proof (rw_cells_merge asegs m1 _ [] [c0; c1; c2] [c3; c4] LOC) as LOC' end.
      cbn [cells_size csize Nat.add app] in LOC'.
      eapply evt_eq; [| apply evt_done; eapply (HK 16 m1 _ _ _ _ _)];
        [ atp_st_eq | right; reflexivity | exact B32 | exact MU | exact WM | exact MI
        | replace (q + -288 - 16) with (q + -304) by lia; exact ST2
        | replace (q + -288 - 16) with (q + -304) by lia; exact LOC'
        | replace (q + -104 - 16) with (q + -120) by lia; exact HIGH
        | exact SAVED ].
  Qed.

  Lemma obj_p2a : forall (K : machine_state -> Prop) (q d out node P L f : Z)
      (gp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s6 s7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jA jB h0 h1 h2 js : list byte),
    mem_inv asegs m -> (d = 0 \/ d = 16) -> ae_lo E + 304 <= q -> q <= ae_hi E ->
    f mod 64 = 0 -> 0x6ca000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    rw_cells asegs m (q + -288 - d) [CB 112 jA; C8 (Z_to_bv 64 out); CB 64 jB] ->
    rw_cells asegs m f [CB 8 h0; CB 8 h1; CB 8 h2] -> rw_cells asegs m (shad f) [CB 16 js] ->
    (forall (m1 : mem) (xa0 xa1 xa2 xa3 xa4 : word) (jB1 jB2 js4 : list byte),
       munch [(q + -288 - d, q + -104 - d); (f, f + 24); (shad f, shad f + 16)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (q + -288 - d) [CB 112 jA; C8 (Z_to_bv 64 out); CB 8 jB1; C8 (Z_to_bv 64 f); CB 48 jB2] ->
       rw_cells asegs m1 f [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13317); C8 (Z_to_bv 64 0xb5e4c)] ->
       rw_cells asegs m1 (shad f) [C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-8)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13))));
                                   C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13)))); C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-13)))); CB 4 js4] ->
       K (MS (mkR (wz OBJ_SM1_RA) (wz (q + -288 - d)) gp (wz TPV) t0 t1 t2 (wz q) (wz (q + -288 - d)) xa0 xa1 xa2 xa3 xa4 a5 a6 a7
                  (wz f) (wz (shad f)) (wz L) (wz P) (wz f) s7 (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz 0xb5f64) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz OBJ_SM1_RA) (wz (q + -288 - d)) gp (wz TPV) t0 t1 t2 (wz q) (wz (q + -288 - d)) (wz f) a1 a2 a3 a4 a5 a6 a7
                       s2 s3 (wz L) (wz P) s6 s7 (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz OBJ_SM1_RA) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until js. intros MI Hd LO QH F64 FLO FHI FSH S0 SHI LOC HDR SH HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OBJ_SM1_RA in *.
    pose proof (munch_refl [(q + -288 - d, q + -104 - d); (f, f + 24); (shad f, shad f + 16)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold shad, SHB in *.
    apply (rw_cells_split_CB asegs _ _ [] 16 js [] [1;1;1;1;1;1;1;1;1;1;1;1;4]%nat) in SH; [| reflexivity]. cbn [mk_CB_cells app] in SH.
    repeat match type of SH with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jz" in set (j := t) in SH; clearbody j end.

    step. step. step. step. if_cases K0; zify_cond K0; [clear K0| exfalso; rewrite ?land64_mod in K0; clear - K0 FLO FHI LOW; lia].

    step. astep. astep. astep. astep. astep. astep. astep. astep. astep. lstep. lstep. lstep. astep. astep.

    do 12 nstep.
    name_mem m1.
    eapply evt_eq; [| apply evt_done; eapply (HK m1); [exact MU| exact WM| exact MI| exact LOC| exact HDR| exact SH]]. atp_st_eq.
  Qed.

  Lemma obj_p2b : forall (K : machine_state -> Prop) (q b out node P f : Z) (ptr : list Z)
      (gp t0 t1 t2 xa0 xa1 xa2 xa3 xa4 a5 a6 a7 s7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jA jB1 jB2 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> ae_lo E <= out -> out + 24 <= ae_hi E ->
    bytes_at asegs m P (map (Z_to_bv 8) ptr) -> Forall (fun c => 0 <= c < 256) ptr -> (ptr <> [] -> 0 < P) -> (ptr <> [] -> P + zlength ptr <= ae_lo E) ->
    (ptr <> [] -> acc asegs m (ae_PB E) (ae_NPB E) /\ ae_PB E <= P /\ P + zlength ptr <= ae_PB E + ae_NPB E) ->
    rw_cells asegs m b [CB 112 jA; C8 (Z_to_bv 64 out); CB 8 jB1; C8 (Z_to_bv 64 f); CB 48 jB2] ->

    (forall (xa3' : word), ptr = [] ->
       K (MS (mkR (wz 0xb5fcc) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz out) (wz node) (wz 16) xa3' xa4 a5 a6 a7
                  (wz f) (wz (shad f)) (wz out) (wz P) (wz f) s7 (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz e_asan_memcpy) fc None m (seg_rom asegs))) ->

    (forall (c0 : Z) (ptr0 : list Z), ptr = c0 :: ptr0 -> c0 <> 47 ->
       K (MS (mkR (wz 0xb5ffc) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz out) (wz 0) (wz 16) xa3 xa4 a5 a6 a7
                  (wz f) (wz (shad f)) (wz (out + 16)) (wz P) (wz f) s7 (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz e_asan_memset) fc None m (seg_rom asegs))) ->

    (forall (m1 : mem), ptr = [47] -> munch [(b, b + 184)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b [CB 112 jA; C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 node); C8 (Z_to_bv 64 f); CB 48 jB2] ->
       K (MS (mkR (wz 0xb5ec8) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz (-1)) (wz 47) xa2 xa3 xa4 a5 a6 a7
                  (wz f) (wz (shad f)) (wz (zlength ptr)) (wz (P + 1)) (wz f) (wz 0) (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz 0xb601c) fc None m1 (seg_rom asegs))) ->

    (forall (m1 : mem) (ptr0 : list Z), ptr = 47 :: ptr0 -> ptr0 <> [] -> munch [(b, b + 184)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b [CB 112 jA; C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 node); C8 (Z_to_bv 64 f); CB 48 jB2] ->
       K (MS (mkR (wz 0xb5fa4) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz (P + 1)) (wz 47) (wz (zlength ptr0)) xa3 xa4 a5 a6 a7
                  (wz f) (wz (shad f)) (wz (zlength ptr)) (wz (P + 1)) (wz f) (wz (zlength ptr0)) (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz e_memchr) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz OBJ_SM1_RA) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) xa0 xa1 xa2 xa3 xa4 a5 a6 a7
                       (wz f) (wz (shad f)) (wz (zlength ptr)) (wz P) (wz f) s7 (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb5f64) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jB2. intros MI LO B0 B1 QH OLO OHI RB RF P0 PHI PBX LOC KCPY KSET KONE KCHR.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OBJ_SM1_RA, e_asan_memcpy, e_asan_memset, e_memchr in *.
    pose proof (munch_refl [(b, b + 184)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (zlength_nonneg ptr) as ZL.

    step. if_cases K0; zify_cond K0.
    {
      astep. step. step. step. step.
      eapply evt_eq; [| apply evt_done; apply (KCPY xa3)]; [atp_st_eq|].
      destruct ptr as [|cx lx]; [reflexivity| exfalso; specialize (PHI ltac:(discriminate)); specialize (P0 ltac:(discriminate)); rewrite zlength_cons in K0, PHI; pose proof (zlength_nonneg lx); lia]. }
    destruct ptr as [|c0 ptr0]; [exfalso; apply K0; reflexivity|].
    assert (NE0 : c0 :: ptr0 <> []) by discriminate. destruct (PBX NE0) as (ACC & PB1 & PB2). clear PBX. specialize (P0 NE0). specialize (PHI NE0).
    assert (C0R : 0 <= c0 < 256) by (inversion RF; assumption).
    rewrite zlength_cons in *. pose proof (zlength_nonneg ptr0) as ZL0.
    pose proof (zbytes_read1 m P (c0 :: ptr0) 0 RB ltac:(rewrite zlength_cons; lia)) as RD0.
    change (nth (Z.to_nat 0) (c0 :: ptr0) 0) with c0 in RD0. rewrite Z.add_0_r in RD0.

    assert (J0 : forall ya0 ya1 : word,
      evt asegs K (MS (mkR (wz 0xb5ec8) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) ya0 ya1 xa2 xa3 xa4 a5 a6 a7
                         (wz f) (wz (shad f)) (wz (zlength ptr0 + 1)) (wz P) (wz f) s7 (wz node) s9 s10 (wz 2147450880) t3 t4 t5 t6)
                     F (wz 0xb5f78) fc None m (seg_rom asegs))).
    { intros ya0 ya1.

      astep. astep. step. if_cases K1; zify_cond K1.
      -
        step. astep. step. step. step.
        eapply evt_eq; [| apply evt_done; apply (KSET c0 ptr0 eq_refl K1)]. atp_st_eq.
      - subst c0.

        astep. astep. step. name_mem m1.
        step. if_cases K2; zify_cond K2.
        +
          astep.
          assert (E0 : ptr0 = []) by (destruct ptr0 as [|cx lx]; [reflexivity| exfalso; rewrite zlength_cons in K2; pose proof (zlength_nonneg lx); lia]).
          subst ptr0. rewrite zlength_nil in *.
          eapply evt_eq; [| apply evt_done; apply (KONE m1 eq_refl MU WM MI LOC)]. atp_st_eq.
        +
          astep. step. step. step.
          assert (NE1 : ptr0 <> []) by (intros ->; rewrite zlength_nil in K2; lia).
          eapply evt_eq; [| apply evt_done; apply (KCHR m1 ptr0 eq_refl NE1 MU WM MI LOC)]. rewrite ?zlength_cons. atp_st_eq. }

    destruct (acc_read1 m (ae_PB E) (ae_NPB E) P ACC ltac:(lia)) as (b0 & RDS0 & OK0).
    destruct (sh_ok_cases b0 P OK0) as [-> | (k0 & -> & K0' & KM0)].
    - astep. astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply J0]; [atp_st_eq].
    - astep. astep. step. rewrite (sxb_small7 k0) by lia. step. if_dead2 by K0'. astep. step. if_dead2 by K0' KM0 P0. eapply evt_eq; [| eapply J0]; [atp_st_eq].
  Qed.

  Lemma obj_p3a : forall (K : machine_state -> Prop) (b P r : Z) (rest : list Z)
      (gp x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv asegs m -> Forall (fun c => 0 <= c < 256) rest -> 0 < P -> P + 1 + zlength rest < 2^47 ->
    r = memchr_res (P + 1) 47 (zlength rest) (map (Z_to_bv 8) rest) ->
    (forall (ya1 : word) (ix : nat), (ix < length rest)%nat -> nth ix rest 0 = 47 -> (forall j, (j < ix)%nat -> nth j rest 0 <> 47) ->
       K (MS (mkR (wz 0xb5fa4) (wz b) gp (wz TPV) x5 x6 x7 x8 (wz b) (wz (Z.of_nat ix)) ya1 x12 x13 x14 x15 x16 x17
                  x18 x19 x20 (wz (P + 1)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (wz 0xb601c) fc None m (seg_rom asegs))) ->
    (forall (ya1 : word), (forall j, (j < length rest)%nat -> nth j rest 0 <> 47) ->
       K (MS (mkR (wz 0xb5fa4) (wz b) gp (wz TPV) x5 x6 x7 x8 (wz b) (wz 18446744073709551615) ya1 x12 x13 x14 x15 x16 x17
                  x18 x19 x20 (wz (P + 1)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
             F (wz 0xb601c) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb5fa4) (wz b) gp (wz TPV) x5 x6 x7 x8 (wz b) (wz r) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 (wz (P + 1)) x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                   F (wz 0xb5fa4) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros MI RF P0 PH ER KF KN.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (zlength_nonneg rest) as ZL. unfold memchr_res in ER.
    destruct (find_byte 47 (firstn (Z.to_nat (zlength rest)) (map (Z_to_bv 8) rest))) as [ix|] eqn:FB.
    - pose proof (find_byte_zlist_SomeA 47 rest _ ix RF ltac:(lia) FB) as (IX1 & IX2 & IXC & IXN). subst r.

      astep. astep. astep. astep. rewrite find_or_foundM by lia. step.
      eapply evt_eq; [| apply evt_done; eapply (KF _ ix IX1 IXC IXN)]. atp_st_eq.
    - pose proof (find_byte_zlist_NoneA 47 rest _ RF ltac:(lia) FB) as IXN. subst r.
      astep. astep. astep. astep. rewrite find_or_nposM by lia. step.
      eapply evt_eq; [| apply evt_done; eapply (KN _)]; [atp_st_eq|].
      intros j Hj. apply IXN; [unfold zlength; lia| exact Hj].
  Qed.

  Lemma obj_p3b : forall (K : machine_state -> Prop) (b out node f sl L0 Lk : Z)
      (gp x1 x5 x6 x7 x8 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x24 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jA jB2 : list byte),
    mem_inv asegs m -> ae_lo E + 16 <= b -> b + 304 <= ae_hi E -> 0 <= sl < 2^64 -> 0 <= L0 < 2^47 -> ((sl < L0 /\ Lk = sl) \/ (L0 <= sl /\ Lk = L0)) ->
    rw_cells asegs m b [CB 112 jA; C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 node); C8 (Z_to_bv 64 f); CB 48 jB2] ->
    (forall (m1 : mem) (jA1 jA2 : list byte), munch [(b, b + 184)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b [CB 80 jA1; C8 (Z_to_bv 64 sl); CB 24 jA2; C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 node); C8 (Z_to_bv 64 f); CB 48 jB2] ->
       K (MS (mkR (wz 0xb603c) (wz b) gp (wz TPV) x5 x6 x7 x8 (wz b) (wz (b + 160)) (wz 0) (wz 16) x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 (wz L0) (wz Lk) x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz e_asan_memset) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 x8 (wz b) (wz sl) x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb601c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jB2. intros MI BL BH SL L0R MIN LOC HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_asan_memset in *.
    pose proof (munch_refl [(b, b + 184)] m) as MU. pose proof (wmono_refl asegs m) as WM.

    lazymatch goal with |- evt asegs ?Q (MS (mkR ?r1 ?r2 ?r3 ?r4 ?r5 ?r6 ?r7 ?r8 ?r9 ?r10 ?r11 ?r12 ?r13 ?r14 ?r15 ?r16 ?r17 ?r18 ?r19 ?r20 ?r21 ?r22 ?r23 _ ?r25 ?r26 ?r27 ?r28 ?r29 ?r30 ?r31) ?FF _ ?fcx _ ?mx ?rom) =>
      assert (J : evt asegs Q (MS (mkR r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16 r17 r18 r19 r20 r21 r22 r23 (Z_to_bv 64 Lk) r25 r26 r27 r28 r29 r30 r31) FF (Z_to_bv 64 0xb6028) fcx None mx rom))
    end.
    {
      step. astep. astep. astep. step. name_mem m1.
      eapply evt_eq; [| apply evt_done; eapply (HK m1); [exact MU| exact WM| exact MI| exact LOC]]. atp_st_eq. }
    step. step. if_cases K1; zify_cond K1.
    -   destruct MIN as [(X & ->)|(X & ->)]; [exfalso; rewrite ?land64_mod in K1; lia|]. exact J.
    - destruct MIN as [(X & ->)|(X & ->)].
      + step. exact J.
      + step. assert (EQL : sl = L0) by (rewrite ?land64_mod in K1; lia). rewrite EQL. rewrite EQL in J. exact J.
  Qed.
End ObjPro.
