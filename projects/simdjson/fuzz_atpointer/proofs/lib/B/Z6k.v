(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw Rnd Zso Zvm.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2 Zqc Zqd
     Z45 Z5k Z3v Z5q Z5v Z6b Z60 Z6e Z6h Z63 Z65 Z5o.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition obj_shF : list cell :=
  [pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11); pz (-11)].

Definition obj_hdrR : list cell := [C8 (Z_to_bv 64 0x45e0360e); C8 (Z_to_bv 64 0x131f8); C8 (Z_to_bv 64 0x99a84)].

Section ObjX.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_xcpy : forall (K : machine_state -> Prop) (q b out : Z)
      (gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (nbs jB jC : list byte),
    mem_inv bsegs m -> ae_lo E <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> shz m out 24 ->
    rw_cells bsegs m out [CB 16 nbs; CB 4 jB; CB 4 jC] ->
    (forall (m1 : mem) (xa1 : word), munch [(out, out + 24)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 out [CB 16 nbs; C4 (Z_to_bv 64 0); CB 4 jC] ->
       K (MS (mkR (wz 0x99ca8) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (out + 16)) xa1 x12 x13 x14 x15 x16 x17
                  (wz out) x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0x99fc8) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0x99ca8) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz out) x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0x99ca8) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jC. intros MI OLO OHI O8 SZ OUT HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    astep. chk0 SZ (out + 16). step. if_false.

    lstep. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_xset : forall (K : machine_state -> Prop) (q b out : Z)
      (gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (nbs jB jC : list byte),
    mem_inv bsegs m -> ae_lo E <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> shz m out 24 ->
    rw_cells bsegs m out [CB 16 nbs; CB 4 jB; CB 4 jC] ->
    (forall (m1 : mem), munch [(out, out + 24)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 out [CB 16 nbs; C4 (Z_to_bv 64 22); CB 4 jC] ->
       K (MS (mkR (wz 0x99cdc) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz 22) x11 x12 x13 x14 x15 x16 x17
                  x18 x19 (wz (out + 16)) x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0x99fc8) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0x99cdc) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 (wz (out + 16)) x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0x99cdc) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jC. intros MI OLO OHI O8 SZ OUT HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    chk0 SZ (out + 16). step. if_false.

    astep. lstep. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_rel1 : forall (K : machine_state -> Prop) (q b f out v4 v5 v6 : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 w24 w32 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 js4 : list byte),
    mem_inv bsegs m -> f mod 64 = 0 -> 0x676000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    ae_lo E <= b -> b + 152 <= q -> q <= ae_hi E ->
    rw_cells bsegs m b (obj_loc72 j0 w24 w32 f out) ->
    rw_cells bsegs m f obj_hdrB -> rw_cells bsegs m (shad f) (obj_sh v4 v5 v6 js4) ->
    (forall (m1 : mem), munch [(f, f + 8); (shad f, shad f + 16)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 f obj_hdrR -> rw_cells bsegs m1 (shad f) obj_shF ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (-11)) (wz f) (wz f) x13 x14 x15 x16 x17
                  x18 (wz (shad f)) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0x9a024) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (wz (shad f)) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0x99fc8) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until js4. intros MI F64 FLO FHI FSH S0 SHI BLO BHI QH LOC HDR SH HK.
    unfold obj_loc72 in LOC.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(f, f + 8); (shad f, shad f + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold obj_hdrB in HDR. unfold obj_sh, pz in SH. unfold shad, SHB in *.
    assert (EB : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; lia).
    lazymatch type of SH with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: [CB 4 js4]) =>
      apply (rw_cells_split_CB bsegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11] 4 js4 [] [1; 1; 1; 1]%nat) in SH; [| reflexivity] end.
    cbn [mk_CB_cells app] in SH.
    repeat match type of SH with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jz" in set (j := t) in SH; clearbody j end.

    step.
    astep.
    astep.
    step.
    lstep.
    step. if_dead1 by FLO.
    astep.

    do 16 nstep.

    name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_rel2 : forall (K : machine_state -> Prop) (q b f fl : Z)
      (gp x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv bsegs m -> 0x676000 <= f -> f + 128 < 2^62 -> 0 < fl -> fl + 1 < 2^62 ->
    ro_cells bsegs m (f + 120) [C8 (Z_to_bv 64 fl)] -> rw_cells bsegs m fl [C1 (Z_to_bv 8 1)] ->
    (forall (m1 : mem), munch [(fl, fl + 1)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 fl [C1 (Z_to_bv 8 0)] ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz fl) (wz f) x12 x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0x9a060) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 (wz f) x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0x9a024) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros MI FLO FHI FL0 FL1 LAST FLAG HK.
    pose proof (munch_refl [(fl, fl + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.

    step. lstep. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_epi : forall (K : machine_state -> Prop) (q b dd : Z)
      (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
      (gp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
      (cL : list cell) (jH : list byte),
    mem_inv bsegs m -> ae_lo E + 272 <= q -> q <= ae_hi E -> (dd = 0 \/ dd = 16) -> b = q + -256 - dd ->
    stk bsegs m (ae_lo E) b ->
    rw_cells bsegs m b cL -> cells_size cL = 152%nat -> rw_cells bsegs m (b + 152) [CB (Z.to_nat dd) jH] ->
    rw_cells bsegs m (q + -104) (obj_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    (stk bsegs m (ae_lo E) q ->
       K (MS (mkR ra (wz q) gp (wz TPV) x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
             F (ret_pc ra) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) x9 x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                   F (wz 0x9a060) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jH. intros MI LO QH Hdd Hb ST LOC SZL HIGH SAVED HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    unfold obj_saved in SAVED.
    assert (ST' : stk bsegs m (ae_lo E) q).
    { pose proof (stk_release bsegs m (ae_lo E) b _ ST LOC ltac:(lia)) as S1. rewrite SZL in S1. change (Z.of_nat 152) with 152 in S1.
      pose proof (stk_release bsegs m (ae_lo E) (b + 152) _ S1 HIGH ltac:(lia)) as S4. cbn [cells_size csize Nat.add] in S4.
      replace (b + 152 + Z.of_nat (Z.to_nat dd + 0)) with (q + -104) in S4 by lia.
      pose proof (stk_release bsegs m (ae_lo E) (q + -104) _ S4 SAVED ltac:(lia)) as S5. cbn [cells_size csize Nat.add] in S5.
      replace (q + -104 + Z.of_nat 104) with q in S5 by lia. exact S5. }
    subst b.

    astep. do 13 step. astep. replace (q + -256 + 256) with q by lia. step.
    eapply evt_eq; [| apply evt_done; apply (HK ST')]. atp_st_eq_goal.
  Qed.
End ObjX.
