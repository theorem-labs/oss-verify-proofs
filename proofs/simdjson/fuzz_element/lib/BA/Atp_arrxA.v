(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_arrlA Atp_arratA Atp_arrwA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition arr_WO (out : Z) : list (Z * Z) := [(out, out + 24)].

Section ArrExits.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma arr_after_cpy : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (j0 jc b16 j1 j2 : list byte)
      (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc) -> stk asegs m (ae_lo E) (q + -96) -> mem_inv asegs m -> ae_lo E <= q + -96 ->
    rw_cells asegs m out [CB 16 b16; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 ->
    (forall (m' : mem) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (arr_WO out) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (ae_lo E) q ->
       rw_cells asegs m' out [CB 16 b16; C4 (Z_to_bv 64 0); CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6a64) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (wz 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb6a64) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (arr_WO out) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold arr_WO in MU. unfold arr_frame in FR.

    astep. chk0 SHZO (out + 16). step. if_false. lstep. step.
    name_mem m1.
    apply arr_epi with (lo := ae_lo E) (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (j0 := j0) (jc := jc);
      [unfold arr_frame; exact FR| exact ST| exact MI| exact LO|].
    intros until y31. intros ST'. apply (HK m1); [exact MU| exact WM| exact MI| exact ST'| exact OUT].
  Qed.

  Lemma arr_after_set : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out ra' : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s1' s2' : word) (j0 jc zb j1 j2 : list byte)
      (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc) -> stk asegs m (ae_lo E) (q + -96) -> mem_inv asegs m -> ae_lo E <= q + -96 ->
    rw_cells asegs m out [CB 16 zb; CB 4 j1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    (forall m', munch (arr_WO out) m m' -> wmono asegs m m' -> shz m' out 24) ->
    arr_set_site ra' s1' s2' out ->
    (forall (m' : mem) (code : Z) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (arr_WO out) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (ae_lo E) q ->
       rw_cells asegs m' out [CB 16 zb; C4 (Z_to_bv 64 code); CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz ra') (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) s1' x10 x11 x12 x13 x14 x15 x16 x17
                       s2' (wz 2147450880) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz ra') fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO SITE HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (arr_WO out) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold arr_WO in MU, SHZO. unfold arr_frame in FR.
    assert (EPI : forall (m1 : mem) (code : Z) (z1 z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 z28 z29 z30 z31 : word),
      munch [(out, out + 24)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
      rw_cells asegs m1 (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jc) -> stk asegs m1 (ae_lo E) (q + -96) ->
      rw_cells asegs m1 out [CB 16 zb; C4 (Z_to_bv 64 code); CB 4 j2] ->
      evt asegs K (MS (mkR z1 (wz (q + -96)) gp (wz TPV) z5 z6 z7 z8 z9 z10 z11 z12 z13 z14 z15 z16 z17 z18 z19 z20 z21 z22 s7 s8 s9 s10 s11 z28 z29 z30 z31)
                      F (wz 0xb6ba8) fc None m1 (seg_rom asegs))).
    { intros until z31. intros MU1 WM1 MI1 FR1 ST1 OUT1.
      apply arr_epi with (lo := ae_lo E) (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (j0 := j0) (jc := jc);
        [exact FR1| exact ST1| exact MI1| exact LO|].
      intros until y31. intros ST'. apply (HK m1 code); [exact MU1| exact WM1| exact MI1| exact ST'| exact OUT1]. }
    destruct SITE as [(-> & ->)|[(-> & -> & (code & -> & CODE))|[(-> & ->)|(-> & ->)]]].
    -
      chk0 SHZO (out + 16). step. if_false. astep. lstep. step.
      eapply EPI; [exact MU| exact WM| exact MI| unfold arr_frame; exact FR| exact ST| exact OUT].
    -
      chk0 SHZO (out + 16). step. if_false. lstep.
      eapply EPI; [exact MU| exact WM| exact MI| unfold arr_frame; exact FR| exact ST| exact OUT].
    -
      chk0 SHZO (out + 16). step. if_false. astep. step. lstep. step.
      eapply EPI; [exact MU| exact WM| exact MI| unfold arr_frame; exact FR| exact ST| exact OUT].
    -
      chk0 SHZO (out + 16). step. if_false. astep. lstep. step.
      astep. chk0 SHZO (out + 16). step. if_false. astep. step. if_cases KR.
      + eapply EPI; [exact MU| exact WM| exact MI| unfold arr_frame; exact FR| exact ST| exact OUT].
      +
        astep. step. if_true.
        eapply EPI; [exact MU| exact WM| exact MI| unfold arr_frame; exact FR| exact ST| exact OUT].
  Qed.

  Lemma arr_rec_glue : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out : Z)
      (gp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31 : word),
    mem_inv asegs m -> 0x6ca000 <= q + -96 -> q <= 2^47 ->
    K (MS (mkR (wz 0xb6ddc) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 (wz out) (wz (q + -88)) (wz 16) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
         F (wz e_asan_memcpy) fc None m (seg_rom asegs)) ->
    evt asegs K (MS (mkR (wz 0xb6dcc) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb6dcc) fc None m (seg_rom asegs)).
  Proof.
    intros until x31. intros MI QL QH HK.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
    astep. astep. step. step.
    eapply evt_eq; [| apply evt_done; exact HK]. unfold e_asan_memcpy. atp_st_eq.
  Qed.

  Lemma arr_after_rec : forall (K : machine_state -> Prop) (m : mem) (F : bvmap 5 word) (fc : bv 32) (q out : Z)
      (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 w1 : word) (j0 jr b16 j2 eb : list byte)
      (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x28 x29 x30 x31 : word),
    rw_cells asegs m (q + -96) (arr_frame ra s0 s1 s2 s3 s4 s5 s6 j0 jr) -> stk asegs m (ae_lo E) (q + -96) -> mem_inv asegs m -> ae_lo E <= q + -96 ->
    rw_cells asegs m out [CB 16 b16; C4 w1; CB 4 j2] -> q <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 ->
    shz m out 24 ->
    ov_read_bytes asegs m (wa (q + -72)) 4 = Some eb -> length eb = 4%nat ->
    (forall (m' : mem) (err : word) (y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       munch (arr_WO out) m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (ae_lo E) q ->
       rw_cells asegs m' out [CB 16 b16; C4 err; CB 4 j2] ->
       K (MS (mkR ra (wz q) gp (wz TPV) y5 y6 y7 s0 s1 y10 y11 y12 y13 y14 y15 y16 y17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 y28 y29 y30 y31)
             F (ret_pc ra) fc None m' (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6ddc) (wz (q + -96)) gp (wz TPV) x5 x6 x7 (wz out) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       (wz (out + 16)) (wz ((out + 16) / 8 + 2147450880)) x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                   F (wz 0xb6ddc) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until x31. intros FR ST MI LO OUT QO OB O8 SHZO RDE LEB HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl (arr_WO out) m) as MU. pose proof (wmono_refl asegs m) as WM. unfold arr_WO in MU. unfold arr_frame in FR.

    pose proof (SHZO (out + 16) ltac:(lia)) as SHRD.
    hide FR. step. shz_norm.

    step.
    unhide FR.

    step. if_false. step. step.
    name_mem m1.
    apply arr_epi with (lo := ae_lo E) (ra := ra) (s0 := s0) (s1 := s1) (s2 := s2) (s3 := s3) (s4 := s4) (s5 := s5) (s6 := s6) (j0 := j0) (jc := jr);
      [unfold arr_frame; exact FR| exact ST| exact MI| exact LO|].
    intros until y31. intros ST'. eapply (HK m1); [exact MU| exact WM| exact MI| exact ST'| exact OUT].
  Qed.
End ArrExits.
