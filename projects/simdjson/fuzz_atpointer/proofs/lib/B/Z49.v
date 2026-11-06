(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Z45 Z48.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma lor_ones64 : forall x, 0 <= x < 2^64 -> Z.lor 18446744073709551615 x = 18446744073709551615.
Proof.
  intros x Hx. pose proof (Z.add_lor_land 18446744073709551615 x) as E.
  rewrite (Z.land_comm 18446744073709551615 x) in E. rewrite land64_mod, Z.mod_small in E by lia. lia.
Qed.

Section ElemExits.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma elem_walk2 : forall (K : machine_state -> Prop) (ptr0 : list Z) (q out P r node : Z)
      (ra gp s0 s1 s2 s3 s4 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    rw_cells bsegs m (q + -64) (elem_frame ra s0 s1 s2 s3 s4 (le8 (wz P) ++ le8 (wz (zlength ptr0 + 1)))) ->
    rw_cells bsegs m (q + -80) [C8 (wz out); C8 (wz 0x9769c)] -> stk bsegs m (ae_lo E) (q + -80) -> ae_lo E <= q + -80 -> 0x676000 <= q + -80 -> q < 2^47 ->
    bytes_at bsegs m P (map (Z_to_bv 8) (47 :: ptr0)) -> Forall (fun c => 0 <= c < 256) (47 :: ptr0) ->
    0 < P -> P + zlength ptr0 + 1 < 2^47 -> mem_inv bsegs m ->
    acc bsegs m (ae_PB E) (ae_NPB E) -> ae_PB E <= P -> P + zlength ptr0 + 1 <= ae_PB E + ae_NPB E ->
    r = memchr_res P 126 (zlength ptr0 + 1) (map (Z_to_bv 8) (47 :: ptr0)) -> 0 < out -> out + 24 < 2^47 ->
    (forall (ra' code : Z) (ya3 : word), elem_set_site ra' code -> stk bsegs m (ae_lo E) (q + -64) ->
       K (MS (mkR (wz ra') (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) (wz out) (wz 0) (wz 16) ya3 x14 x15 x16 x17
                  (wz (zlength ptr0 + 1)) (wz node) (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (wz e_asan_memset) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0x9a564) (wz (q + -80)) gp (wz TPV) x5 x6 x7 (wz P) (wz P) (wz r) x11 x12 x13 x14 x15 x16 x17
                       (wz (zlength ptr0 + 1)) (wz node) (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0x9a564) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros FR FF ST LO QL QH RB RF P0 PH MI ACC PB1 PB2 ER O0 OH HK.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (zlength_nonneg ptr0) as ZL0.
    unfold elem_frame in FR. apply Z5k.rec_node16 in FR.

    assert (XSET : forall (pc ra' code : Z) (ya0 ya1 ya2 ya3 : word), ((pc = 0x97748 /\ ra' = 0x97760 /\ code = 22) \/ (pc = 0x976e8 /\ ra' = 0x97700 /\ code = 20)) ->
      stk bsegs m (ae_lo E) (q + -64) ->
      evt bsegs K (MS (mkR (wz 0x9769c) (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz P) ya0 ya1 ya2 ya3 x14 x15 x16 x17
                         (wz (zlength ptr0 + 1)) (wz node) (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                     F (wz pc) fc None m (seg_rom bsegs))).
    { intros pc ra' code ya0 ya1 ya2 ya3 SITE ST'.
      destruct SITE as [(-> & -> & ->)|(-> & -> & ->)];
        (step; if_lia; astep; step; step; step; step; eapply evt_eq; [| apply evt_done; eapply HK; [| exact ST']]; [unfold e_asan_memset; atp_st_eq| ]);
        [left | right]; split; reflexivity. }

    destruct (find_byte 126 (firstn (Z.to_nat (zlength ptr0 + 1)) (map (Z_to_bv 8) (47 :: ptr0)))) as [ix|] eqn:FB.
    - pose proof (find_byte_Some _ _ _ FB) as (Hl & _). rewrite length_firstn, length_map in Hl. cbn [length] in Hl.
      assert (IXR : 0 <= Z.of_nat ix < zlength ptr0 + 1) by (unfold zlength in *; lia).
      unfold memchr_res in ER. rewrite FB in ER. subst r.
      astep. replace (0 <? P + Z.of_nat ix) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z]. astep. astep. astep.
      rewrite Z.lor_0_l. replace (P + Z.of_nat ix - P) with (Z.of_nat ix) by lia.
      step. step. step. step. release_frame FF ST (q + -64). step.
      astep. step. if_cases K3; zify_cond K3; rewrite ?land64_mod in K3; [exfalso; clear - K3 IXR PH P0; lia|].

      step. astep. step. if_cases K4; zify_cond K4; [eapply (XSET 0x97748 0x97760 22); [left; repeat split; reflexivity| exact ST]|].

      step. step. if_lia. astep. astep. step. if_lia. step. if_lia.
      pose proof (zbytes_read1 m P (47 :: ptr0) (Z.of_nat ix + 1) RB ltac:(rewrite zlength_cons; lia)) as RD1.
      pose proof (Forall_nth_Z _ (47 :: ptr0) (Z.to_nat (Z.of_nat ix + 1)) RF ltac:(unfold zlength in *; cbn [length]; lia)) as C1R. cbv beta in C1R.
      set (c1 := nth (Z.to_nat (Z.of_nat ix + 1)) (47 :: ptr0) 0) in *.
      try replace (Z.of_nat ix + 1 + P) with (P + (Z.of_nat ix + 1)) by lia.
      assert (J48 : forall ya1 ya2 : word,
        evt bsegs K (MS (mkR (wz 0x9769c) (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz P) (wz (P + (Z.of_nat ix + 1))) ya1 ya2 x13 x14 x15 x16 x17
                           (wz (zlength ptr0 + 1)) (wz node) (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (wz 0x976d8) fc None m (seg_rom bsegs))).
      { intros ya1 ya2. astep. astep. astep. step. if_cases K5; zify_cond K5.
        - eapply (XSET 0x97748 0x97760 22); [left; repeat split; reflexivity| exact ST].
        - eapply (XSET 0x976e8 0x97700 20); [right; repeat split; reflexivity| exact ST]. }
      destruct (acc_read1 m (ae_PB E) (ae_NPB E) (P + (Z.of_nat ix + 1)) ACC ltac:(lia)) as (b1 & RDS1 & OK1).
      destruct (sh_ok_cases b1 (P + (Z.of_nat ix + 1)) OK1) as [-> | (k1 & -> & K1 & KM1)].
      + astep. astep. step. shz_norm. step. if_false. eapply evt_eq; [| eapply J48]; [atp_st_eq].
      + astep. astep. step. rewrite (sxb_small7 k1) by lia. step. if_lia. astep. step. if_lia. eapply evt_eq; [| eapply J48]; [atp_st_eq].
    -
      unfold memchr_res in ER. rewrite FB in ER. subst r.
      astep. cbn [Z.ltb Z.compare Z.b2z]. astep. astep. astep. rewrite lor_ones64 by (apply Z.mod_pos_bound; lia).
      step. step. step. step. release_frame FF ST (q + -64). step.
      astep. step. if_cases K2; zify_cond K2; rewrite ?land64_mod in K2; [| exfalso; clear - K2; lia].
      eapply (XSET 0x976e8 0x97700 20); [right; repeat split; reflexivity| exact ST].
  Qed.

  Lemma elem_child_glue : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out P L node ra' : Z)
      (gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word),
    mem_inv bsegs m -> 0x676000 <= q + -64 -> q <= 2^47 -> (ra' = 0x97620 \/ ra' = 0x97648) ->
    K (MS (mkR (wz (ra' + 20)) (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz P) (wz out) (wz (q + -64)) (wz P) (wz L) x14 x15 x16 x17
               (wz L) (wz node) (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (wz (if ra' =? 0x97620 then ATP_OBJ_A else ATP_ARR_A)) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR (wz ra') (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz P) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz L) (wz node) (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz ra') fc None m (seg_rom bsegs)).
  Proof.
    intros until x31. intros MI QL QH RA HK.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    destruct RA as [-> | ->]; cbn [Z.eqb Pos.eqb] in HK; unfold ATP_OBJ_A, ATP_ARR_A in HK;
      (step; step; step; step; step; eapply evt_eq; [| apply evt_done; exact HK]; atp_st_eq).
  Qed.

  Lemma elem_after_child : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q rac : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jn : list byte)
      (x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -64) (elem_frame ra s0 s1 s2 s3 s4 jn) -> stk bsegs m (ae_lo E) (q + -64) -> mem_inv bsegs m -> ae_lo E <= q + -64 ->
    (rac = 0x97634 \/ rac = 0x9765c) ->
    (forall (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word), stk bsegs m (ae_lo E) q ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz rac) (wz (q + -64)) gp (wz TPV) x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                    F (wz rac) fc None m (seg_rom bsegs)).
  Proof.
    intros until x31. intros FR ST MI LO RA HK.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    destruct RA as [-> | ->]; (step; eapply elem_epi; [exact FR| exact ST| exact MI| exact LO| exact HK]).
  Qed.

  Lemma elem_after_cpy : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (jn b16 j1 j2 : list byte)
      (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -64) (elem_frame ra s0 s1 s2 s3 s4 jn) -> stk bsegs m (ae_lo E) (q + -64) -> mem_inv bsegs m -> ae_lo E <= q + -64 ->
    rw_cells bsegs m out [CB 16 b16; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 ->
    (forall (m' : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (elem_WO out) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 b16; C4 (Z_to_bv 64 0); CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0x9772c) (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0x9772c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (elem_WO out) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold elem_WO in MU. unfold elem_frame in FR.

    astep. chk0 SHZO (out + 16). step. if_false. lstep. step.
    name_mem m1.
    eapply elem_epi; [unfold elem_frame; exact FR| exact ST| exact MI| exact LO|].
    intros until y31. intros ST'. apply (HK m1); [exact MU| exact WM| exact MI| exact ST'| exact OUT].
  Qed.

  Lemma elem_after_set : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out ra' code : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x18 x19 : word) (jn zb j1 j2 : list byte)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    rw_cells bsegs m (q + -64) (elem_frame ra s0 s1 s2 s3 s4 jn) -> stk bsegs m (ae_lo E) (q + -64) -> mem_inv bsegs m -> ae_lo E <= q + -64 ->
    rw_cells bsegs m out [CB 16 zb; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 -> elem_set_site ra' code ->
    (forall (m' : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (elem_WO out) m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (ae_lo E) q ->
       rw_cells bsegs m' out [CB 16 zb; C4 (Z_to_bv 64 code); CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz ra') (wz (q + -64)) gp (wz TPV) x5 x6 x7 (wz out) (wz (out + 16)) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 (wz 2147450880) s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz ra') fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO SITE HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (elem_WO out) m) as MU. pose proof (wmono_refl bsegs m) as WM. unfold elem_WO in MU. unfold elem_frame in FR.
    destruct SITE as [(-> & ->)|(-> & ->)].
    -
      chk0 SHZO (out + 16). step. if_false. astep. lstep.
      name_mem m1. eapply elem_epi; [unfold elem_frame; exact FR| exact ST| exact MI| exact LO|].
      intros until y31. intros ST'. apply (HK m1); [exact MU| exact WM| exact MI| exact ST'| exact OUT].
    -
      chk0 SHZO (out + 16). step. if_false. astep. step. lstep.
      name_mem m1. eapply elem_epi; [unfold elem_frame; exact FR| exact ST| exact MI| exact LO|].
      intros until y31. intros ST'. apply (HK m1); [exact MU| exact WM| exact MI| exact ST'| exact OUT].
  Qed.
End ElemExits.
