(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(** Functional multiplication loop adapted from the pinned Varnish proof to
    the actual zlib checksum_fuzzer instruction layout and register allocation. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Import Tac Bytes.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import Img0 CrcLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.transport_chunks segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.footprint_after_store segs m a bs ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.transport_after_call segs m m' MU WM ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.addr_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.mlia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require StepFast.
#[local] Ltac2 Set OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.step_core segs R F pc fc rv m ro ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.zstep ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Destzna.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_exs PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_exs PO.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Tac.destruct_ands PO ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require WeqGuard TacDiet2.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.WeqGuard.weq_guard; OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Stor0fe.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.mem_after_store ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib Require Dieta54.
Local Ltac lia ::= OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Dieta54.dlia.
(* [comment removed for export] *)

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcModel CrcByteStep CrcTables CrcLoads CrcLinearBasis.

From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum Require Import
  CrcBraidMachine CrcBraidWord CrcBraidModel CrcMergeWord CrcWord CrcMergeLast.
From Stdlib Require Import Btauto.
Opaque csteps.
Definition merge_model (c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 : Z) : Z :=
  csteps 32 (Z.lxor (Z.lxor c4 w4)
    (csteps 32 (Z.lxor (Z.lxor c3 w3)
      (csteps 32 (Z.lxor (Z.lxor c2 w2)
        (csteps 32 (Z.lxor (Z.lxor c1 w1) (csteps 32 (Z.lxor w0 c0))))))))).
Lemma merge_model_finish : forall c0 c1 c2 c3 c4 w0 w1 w2 w3 w4,
  merge_model c0 c1 c2 c3 c4 w0 w1 w2 w3 w4 = braid_finish c0 c1 c2 c3 c4 w0 w1 w2 w3 w4.
Proof.
  intros. unfold merge_model,braid_finish,word_update. rewrite !csteps_xor.
  repeat rewrite <-csteps_add. cbn [Nat.add].
  apply Z.bits_inj'. intros k Hk. rewrite !Z.lxor_spec. btauto.
Qed.
Lemma crc_byte_table_low_read : forall m a,
  bytes_at rsegs m CRC_TABS crc_table_bytes ->
  ov_read_bytes rsegs m (wa (CRC_TABS+Z.shiftl (Z.land a 255) 2)) 4 =
  Some (le4 (Z_to_bv 64 (csteps 8 (Z.land (a mod 2^32) 255)))).
Proof.
  intros m a HT. pose proof (land255_range a) as HI.
  pose proof (crc_byte_table_at m (Z.land a 255) HT ltac:(lia)) as RT.
  replace (4*Z.land a 255)%Z with (Z.shiftl (Z.land a 255) 2) in RT
    by (rewrite Z.shiftl_mul_pow2 by lia;ring).
  assert (E : csteps 8 (Z.land a 255) = csteps 8 (Z.land (a mod 2^32) 255)).
  { rewrite (land_right_u32 a 255 ltac:(lia)). reflexivity. }
  rewrite E in RT. exact RT.
Qed.
Local Ltac crc_bound32 :=
  first [assumption|
    lazymatch goal with |- (0 <= ?v < ?cap)%Z =>
      unify cap (4294967296%Z);
      lazymatch v with
      | csteps ?n ?q => apply csteps_range;crc_bound32
      | Z.lxor ?a ?b => apply lxor_bound;[lia|crc_bound32|crc_bound32]
      | Z.modulo ?a ?b => apply Z.mod_pos_bound;lia
      | bv_unsigned (bword4 ?bs ?k) => apply bword4_unsigned_range
      | Z.shiftr ?q 8 => let H := fresh "Hshift" in
          pose proof (shiftr8_u32_range q ltac:(crc_bound32)) as H;lia
      | Z.land ?a 255 => pose proof (land255_range a);lia
      end
    end].
Local Ltac crc_bound64 :=
  first [assumption|
    lazymatch goal with |- (0 <= ?v < ?cap)%Z =>
      unify cap (18446744073709551616%Z);
      first [
        lazymatch v with
        | SX ?q => apply SX_range;crc_bound32
        | Z.lxor ?a ?b => apply lxor_bound;[lia|crc_bound64|crc_bound64]
        | Z.modulo ?a ?b => apply Z.mod_pos_bound;lia
        | bv_unsigned ?w => let H := fresh "Hword" in
            pose proof (bv_unsigned_in_range 64 w) as H;change (bv_modulus 64) with (2^64)%Z in H;exact H
        end
      |let H := fresh "Hsmall" in assert (H : (0 <= v < 2^32)%Z) by crc_bound32;lia]
    end].
Local Ltac crc_low_eq :=
  repeat first [rewrite low32_mod64|rewrite low32_xor|rewrite SX_mod32 by crc_bound32];
  first [reflexivity|rewrite Z.mod_small by crc_bound32;reflexivity].
Local Ltac solve_merge_table :=
  match goal with
  | HT : bytes_at rsegs ?m CRC_TABS crc_table_bytes |- context [ov_read_bytes rsegs ?m ?a 4] =>
    idtac "MERGE LOOKUP address:" a;
    let E := addr_expr a in
    idtac "MERGE LOOKUP expression:" E;
    lazymatch E with
    | Z.add ?base (Z.shiftl (Z.land ?R 255) 2) =>
      idtac "MERGE LOOKUP base:" base "register:" R;
      unify base CRC_TABS;idtac "MERGE LOOKUP base matches";
      let RD := fresh "CRCREAD" in pose proof (crc_byte_table_low_read m R HT) as RD;idtac "MERGE LOOKUP fact created";
      repeat match goal with EH : (?v mod 2^32 = ?q)%Z |- _ => progress rewrite EH in RD end;
      let tv := lazymatch type of RD with _ = Some (le4 (Z_to_bv 64 ?v)) => v end in
      let HV := fresh "HTABLE32" in assert (HV : (0 <= tv < 2^32)%Z) by crc_bound32;
      let HVS := fresh "HTABLE64" in pose proof (SX_range tv HV) as HVS;
      cbv delta [wa] in RD;idtac "MERGE LOOKUP fact normalized";rewrite RD;idtac "MERGE LOOKUP fact applied";
      load_post;idtac "MERGE LOOKUP loadpost done";
      rewrite ?(sx32_of_small tv HV);
      idtac "MERGE LOOKUP extension done"
    end
  end.
Local Ltac OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Checksum.Lib.Step.solve_load ::=
  first [solve_merge_table|solve_load_base|solve_load_sym].
Local Ltac merge_norm :=
  repeat first
    [match goal with |- context [sx32 (bword4 ?bs ?k)] => rewrite (sx32_bword4 bs k) end
    |match goal with |- context [sx32 (Z_to_bv 64 ?v)] => rewrite (sx32_of_small v ltac:(crc_bound32)) end
    |match goal with |- context [zx32 (Z_to_bv 64 ?v)] => rewrite (Exec.DA_Myrk.zx32_small v ltac:(crc_bound32)) end
    |match goal with |- context [bv_swrap 32 (Z.shiftr (bv_wrap 32 ?a) 8)] => rewrite (srliw8_raw a) end
    |match goal with |- context [(?v mod 18446744073709551616)%Z] =>
        rewrite (Z.mod_small v 18446744073709551616) by crc_bound64 end
    |rewrite low32_mod64
    |rewrite low32_xor
    |rewrite SX_mod32 by crc_bound32
    |match goal with |- context [(Z.shiftr ?q 8 mod 4294967296)%Z] =>
        rewrite (Z.mod_small (Z.shiftr q 8) 4294967296) by crc_bound32 end
    |match goal with
      | |- context [Z.lxor (Z.shiftr ?q 8) (SX (csteps 8 (Z.land ?a 255)))] =>
        rewrite (zero_byte_signed_low a q) by crc_low_eq;idtac "MERGE MODEL signed"
      | |- context [Z.lxor (SX (csteps 8 (Z.land ?a 255))) (Z.lxor ?rest (Z.shiftr ?q 8))] =>
        rewrite (zero_byte_insert_signed_low a q rest) by crc_low_eq;idtac "MERGE MODEL inserted"
      | |- context [Z.lxor (Z.shiftr ?q 8) (csteps 8 (Z.land ?a 255))] =>
        rewrite (zero_byte_unsigned_low a q) by crc_low_eq;idtac "MERGE MODEL unsigned"
      end];
  repeat rewrite <-csteps_add;cbn [Nat.add].
Section BraidMergeInstructions.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 a2 a3 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (B : Z) (inp : list byte).
  Hypothesis INP : bytes_at rsegs m B inp.
  Hypothesis TABLE : bytes_at rsegs m CRC_TABS crc_table_bytes.
  Variable Q : machine_state -> Prop.
  Notation AT pc x5 x6 x7 x11 x12 x14 x15 x16 x17 x28 x29 :=
    (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 CRC_TABS) x11 x12 a3 x14 x15 x16 x17
      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 t5 t6)
      F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
  Theorem crc_braid_merge : forall (i R0 R1 R2 R3 R4 : Z) g6 g7 g28 g29,
    (0 <= i)%Z -> (i+20 <= Z.of_nat (length inp))%Z ->
    (0 <= R0 < 2^64)%Z -> (0 <= R1 < 2^64)%Z -> (0 <= R2 < 2^64)%Z ->
    (0 <= R3 < 2^64)%Z -> (0 <= R4 < 2^64)%Z ->
    (forall h5 h6 h7 h15 h16 h17 h28 h29, evt rsegs Q
      (AT 0x14a60 h5 h6 h7 (Z_to_bv 64 (B+(i+20)))
        (Z_to_bv 64 (bv_unsigned a3+bv_unsigned a2)) (Z_to_bv 64 (merge_model (R0 mod 2^32) (R1 mod 2^32) (R2 mod 2^32) (R3 mod 2^32) (R4 mod 2^32) (bv_unsigned (bword4 inp i)) (bv_unsigned (bword4 inp (i+4))) (bv_unsigned (bword4 inp (i+8))) (bv_unsigned (bword4 inp (i+12))) (bv_unsigned (bword4 inp (i+16))))) h15 h16 h17 h28 h29)) ->
    evt rsegs Q (AT 0x14840 (Z_to_bv 64 R1) g6 g7 (Z_to_bv 64 (B+i)) a2
      (Z_to_bv 64 R0) (Z_to_bv 64 R4) (Z_to_bv 64 R3) (Z_to_bv 64 R2) g28 g29).
  Proof.
    intros i R0 R1 R2 R3 R4 g6 g7 g28 g29 Hi HL HR0 HR1 HR2 HR3 HR4 CONT.
    pose proof (bytes_at_bound _ _ _ _ INP) as BB.
    set (W0 := (bv_unsigned (bword4 inp i))).
    assert (HW0 : (0 <= W0 < 2^32)%Z) by (unfold W0;apply bword4_unsigned_range).
    pose proof (SX_range W0 HW0) as HSW0.
    set (Q0 := Z.lxor W0 (R0 mod 2^32)).
    set (MIX0 := Z.lxor (SX W0) R0).
    assert (HQ0 : (0 <= Q0 < 2^32)%Z) by (unfold Q0;crc_bound32).
    set (P0 := csteps 32 Q0).
    assert (HP0 : (0 <= P0 < 2^32)%Z) by (unfold P0;apply csteps_range;exact HQ0).
    pose proof (SX_range P0 HP0) as HSP0.
    assert (HMIX0 : (0 <= MIX0 < 2^64)%Z) by (unfold MIX0;crc_bound64).
    assert (EMIX0 : (MIX0 mod 2^32 = Q0)%Z).
    { unfold MIX0,Q0. rewrite low32_xor,(SX_mod32 W0 HW0). reflexivity. }
    assert (HC0_8 : (0 <= csteps 8 Q0 < 2^32)%Z) by (apply csteps_range;exact HQ0).
    pose proof (SX_range (csteps 8 Q0) HC0_8) as HSC0_8.
    assert (HC0_16 : (0 <= csteps 16 Q0 < 2^32)%Z) by (apply csteps_range;exact HQ0).
    pose proof (SX_range (csteps 16 Q0) HC0_16) as HSC0_16.
    assert (HC0_24 : (0 <= csteps 24 Q0 < 2^32)%Z) by (apply csteps_range;exact HQ0).
    pose proof (SX_range (csteps 24 Q0) HC0_24) as HSC0_24.
    set (W1 := (bv_unsigned (bword4 inp (i+4)))).
    assert (HW1 : (0 <= W1 < 2^32)%Z) by (unfold W1;apply bword4_unsigned_range).
    pose proof (SX_range W1 HW1) as HSW1.
    set (Q1 := Z.lxor (Z.lxor (R1 mod 2^32) W1) P0).
    set (MIX1 := Z.lxor (Z.lxor R1 (SX W1)) (SX P0)).
    assert (HQ1 : (0 <= Q1 < 2^32)%Z) by (unfold Q1;crc_bound32).
    set (P1 := csteps 32 Q1).
    assert (HP1 : (0 <= P1 < 2^32)%Z) by (unfold P1;apply csteps_range;exact HQ1).
    pose proof (SX_range P1 HP1) as HSP1.
    assert (HMIX1 : (0 <= MIX1 < 2^64)%Z) by (unfold MIX1;crc_bound64).
    assert (EMIX1 : (MIX1 mod 2^32 = Q1)%Z).
    { unfold MIX1,Q1. rewrite !low32_xor,(SX_mod32 W1 HW1),(SX_mod32 P0 HP0). reflexivity. }
    assert (HC1_8 : (0 <= csteps 8 Q1 < 2^32)%Z) by (apply csteps_range;exact HQ1).
    pose proof (SX_range (csteps 8 Q1) HC1_8) as HSC1_8.
    assert (HC1_16 : (0 <= csteps 16 Q1 < 2^32)%Z) by (apply csteps_range;exact HQ1).
    pose proof (SX_range (csteps 16 Q1) HC1_16) as HSC1_16.
    assert (HC1_24 : (0 <= csteps 24 Q1 < 2^32)%Z) by (apply csteps_range;exact HQ1).
    pose proof (SX_range (csteps 24 Q1) HC1_24) as HSC1_24.
    set (W2 := (bv_unsigned (bword4 inp (i+8)))).
    assert (HW2 : (0 <= W2 < 2^32)%Z) by (unfold W2;apply bword4_unsigned_range).
    pose proof (SX_range W2 HW2) as HSW2.
    set (Q2 := Z.lxor (Z.lxor (R2 mod 2^32) W2) P1).
    set (MIX2 := Z.lxor (Z.lxor R2 (SX W2)) (SX P1)).
    assert (HQ2 : (0 <= Q2 < 2^32)%Z) by (unfold Q2;crc_bound32).
    set (P2 := csteps 32 Q2).
    assert (HP2 : (0 <= P2 < 2^32)%Z) by (unfold P2;apply csteps_range;exact HQ2).
    pose proof (SX_range P2 HP2) as HSP2.
    assert (HMIX2 : (0 <= MIX2 < 2^64)%Z) by (unfold MIX2;crc_bound64).
    assert (EMIX2 : (MIX2 mod 2^32 = Q2)%Z).
    { unfold MIX2,Q2. rewrite !low32_xor,(SX_mod32 W2 HW2),(SX_mod32 P1 HP1). reflexivity. }
    assert (HC2_8 : (0 <= csteps 8 Q2 < 2^32)%Z) by (apply csteps_range;exact HQ2).
    pose proof (SX_range (csteps 8 Q2) HC2_8) as HSC2_8.
    assert (HC2_16 : (0 <= csteps 16 Q2 < 2^32)%Z) by (apply csteps_range;exact HQ2).
    pose proof (SX_range (csteps 16 Q2) HC2_16) as HSC2_16.
    assert (HC2_24 : (0 <= csteps 24 Q2 < 2^32)%Z) by (apply csteps_range;exact HQ2).
    pose proof (SX_range (csteps 24 Q2) HC2_24) as HSC2_24.
    set (W3 := (bv_unsigned (bword4 inp (i+12)))).
    assert (HW3 : (0 <= W3 < 2^32)%Z) by (unfold W3;apply bword4_unsigned_range).
    pose proof (SX_range W3 HW3) as HSW3.
    set (Q3 := Z.lxor (Z.lxor (R3 mod 2^32) W3) P2).
    set (MIX3 := Z.lxor (Z.lxor R3 (SX W3)) (SX P2)).
    assert (HQ3 : (0 <= Q3 < 2^32)%Z) by (unfold Q3;crc_bound32).
    set (P3 := csteps 32 Q3).
    assert (HP3 : (0 <= P3 < 2^32)%Z) by (unfold P3;apply csteps_range;exact HQ3).
    pose proof (SX_range P3 HP3) as HSP3.
    assert (HMIX3 : (0 <= MIX3 < 2^64)%Z) by (unfold MIX3;crc_bound64).
    assert (EMIX3 : (MIX3 mod 2^32 = Q3)%Z).
    { unfold MIX3,Q3. rewrite !low32_xor,(SX_mod32 W3 HW3),(SX_mod32 P2 HP2). reflexivity. }
    assert (HC3_8 : (0 <= csteps 8 Q3 < 2^32)%Z) by (apply csteps_range;exact HQ3).
    pose proof (SX_range (csteps 8 Q3) HC3_8) as HSC3_8.
    assert (HC3_16 : (0 <= csteps 16 Q3 < 2^32)%Z) by (apply csteps_range;exact HQ3).
    pose proof (SX_range (csteps 16 Q3) HC3_16) as HSC3_16.
    assert (HC3_24 : (0 <= csteps 24 Q3 < 2^32)%Z) by (apply csteps_range;exact HQ3).
    pose proof (SX_range (csteps 24 Q3) HC3_24) as HSC3_24.
    set (W4 := (bv_unsigned (bword4 inp (i+16)))).
    assert (HW4 : (0 <= W4 < 2^32)%Z) by (unfold W4;apply bword4_unsigned_range).
    pose proof (SX_range W4 HW4) as HSW4.
    set (Q4 := Z.lxor (Z.lxor (R4 mod 2^32) W4) P3).
    set (MIX4 := Z.lxor (Z.lxor R4 (SX W4)) (SX P3)).
    assert (HQ4 : (0 <= Q4 < 2^32)%Z) by (unfold Q4;crc_bound32).
    set (P4 := csteps 32 Q4).
    assert (HP4 : (0 <= P4 < 2^32)%Z) by (unfold P4;apply csteps_range;exact HQ4).
    pose proof (SX_range P4 HP4) as HSP4.
    assert (HMIX4 : (0 <= MIX4 < 2^64)%Z) by (unfold MIX4;crc_bound64).
    assert (EMIX4 : (MIX4 mod 2^32 = Q4)%Z).
    { unfold MIX4,Q4. rewrite !low32_xor,(SX_mod32 W4 HW4),(SX_mod32 P3 HP3). reflexivity. }
    assert (HC4_8 : (0 <= csteps 8 Q4 < 2^32)%Z) by (apply csteps_range;exact HQ4).
    pose proof (SX_range (csteps 8 Q4) HC4_8) as HSC4_8.
    assert (HC4_16 : (0 <= csteps 16 Q4 < 2^32)%Z) by (apply csteps_range;exact HQ4).
    pose proof (SX_range (csteps 16 Q4) HC4_16) as HSC4_16.
    assert (HC4_24 : (0 <= csteps 24 Q4 < 2^32)%Z) by (apply csteps_range;exact HQ4).
    pose proof (SX_range (csteps 24 Q4) HC4_24) as HSC4_24.
    pose proof (rd4_at rsegs m B inp i _ INP ltac:(lia) ltac:(lia) eq_refl) as RD0.
    pose proof (rd4_at rsegs m B inp (i+4) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD1.
    pose proof (rd4_at rsegs m B inp (i+8) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD2.
    pose proof (rd4_at rsegs m B inp (i+12) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD3.
    pose proof (rd4_at rsegs m B inp (i+16) _ INP ltac:(lia) ltac:(lia) eq_refl) as RD4.
    do 131 (lazymatch goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "MERGE STEP" pc end;
      zstep;idtac "MERGE stepped";merge_norm;idtac "MERGE normalized";fold W0 W1 W2 W3 W4 Q0 Q1 Q2 Q3 Q4 P0 P1 P2 P3 P4 MIX0 MIX1 MIX2 MIX3 MIX4;
      idtac "MERGE folded";repeat first [rewrite EMIX0|rewrite EMIX1|rewrite EMIX2|rewrite EMIX3|rewrite EMIX4]).
    assert (HF : (0 <= csteps 8 (Z.land (csteps 24 Q4) 255) < 2^32)%Z) by crc_bound32.
    pose proof (crc_byte_table_low_read m (SX (csteps 24 Q4)) TABLE) as RDF.
    rewrite (SX_mod32 (csteps 24 Q4) HC4_24) in RDF.
    eapply crc_merge_last with (q:=csteps 24 Q4) (v:=csteps 8 (Z.land (csteps 24 Q4) 255));
      [exact HC4_24|exact HF|exact RDF|].
    assert (PU : bv_unsigned (Z_to_bv 64 (B+i)) = (B+i)%Z).
    { rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. lia. }
    rewrite PU,(zero_byte_unsigned_low (csteps 24 Q4) (csteps 24 Q4) ltac:(apply Z.mod_small;exact HC4_24)).
    rewrite <-csteps_add. cbn [Nat.add]. fold P4.
    replace (B+i+20)%Z with (B+(i+20))%Z by lia.
    apply CONT.
  Qed.
End BraidMergeInstructions.
