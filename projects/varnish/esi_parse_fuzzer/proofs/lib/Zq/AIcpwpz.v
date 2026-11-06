(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_mqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcp3q7.

Module AIcpdm8.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_mqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcp3q7.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LEN; @N1; @AFS; @AFD; @Hc; @Hj; @SB; @ESL; @A0R; @A1R; @ESF; @LOLE'; @HS2; @CEIL; @SFB; @K3; @CV; @SPR; @LBR; @H; @K; @LOLE; @K1; @N32; @SEPD; @K4; @HS1; @LB1; @SHhi; @K8; @LBD; @LBS])).
Ltac hot_lia_full := tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard.
(* [comment removed for export] *)
Local Ltac hs_lbr X :=
  first [ match goal with H : (X = 0 \/ ?m < X <= 7)%Z |- _ =>
            clear - H; lazymatch m with (?a mod ?b)%Z => pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) | _ => idtac end; lia end
        | lia ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_word_eq_tac ].
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

Definition memcpy_icpt_entry : Z := 0x574f8.
Definition MEMCPY_ICPT_STACK : Z := 2240.

Definition memcpy_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - MEMCPY_ICPT_STACK, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at rsegs m' (bv_unsigned a1) src.

Section Proofs.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (src junk : list byte) (lo : Z).
  Notation A := (bv_unsigned a0).
  Notation S := (bv_unsigned a1).
  Notation N := (bv_unsigned a2).
  Notation POST := (memcpy_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -80)
                          [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2160) [CB 2080 fjunk]).
  Hypothesis LOLE : (lo + MEMCPY_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis LEN : length src = Z.to_nat N.
  Hypothesis N32 : (N < 2^32)%Z.
  Notation SEPDt := ((A + N <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).
  Notation SEPSt := ((S + N <= lo \/ bv_unsigned sp <= S)%Z) (only parsing).
  Notation DISJt := ((S + N <= A \/ A + N <= S)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="LEN LOLE Clg"] Lemma my_tail : forall m1 fjunk x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x23 x24 x28 x29 x30 x31,
    SEPDt -> DISJt -> mem_inv rsegs m1 ->
    munch [(A, A + N); (bv_unsigned sp - MEMCPY_ICPT_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2160) -> FRAME m1 -> FRAMEB m1 fjunk ->
    rw_cells rsegs m1 A [CB (Z.to_nat N) junk] -> bytes_at rsegs m1 S src ->
    ro_cells rsegs m1 0xaaa10 [C8 (Z_to_bv 64 0xa1b8c)] ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
               a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2152)) x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x57fbc) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros SEPD DISJ MI1 MU1 WM1 ST1 FR1 FRB1 DST1 SRC1 Creal1. unfold MEMCPY_ICPT_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word a0) as A0R; unfold inr64 in A0R.
    pose proof (zr_word a1) as A1R; unfold inr64 in A1R. pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
    pose proof alloc_ceiling_val as CV.
    zstep. zstep.
    zstep. call memcpy_spec. 1:{ exact SRC1. } 1:{ exact LEN. } 1:{ exact DST1. } 1:{ exact DISJ. } 1:{ exact MI1. }
    do 13 zstep.
    release_frame FRB1 ST1 (bv_unsigned sp + -80)%Z. release_frame FR1 ST1 (bv_unsigned sp). finish.
  Qed.

  Section Facts.
    Variables (ngS ngD : nat) (lastbS lastbD : Z) (w1S w2S w1D w2D : word).
    Notation LBSt := ((lastbS = 0 \/ ((S + N - 1) mod 8 < lastbS <= 7))%Z) (only parsing).
    Notation LBDt := ((lastbD = 0 \/ ((A + N - 1) mod 8 < lastbD <= 7))%Z) (only parsing).
    Hypothesis AFS : (0 <= S /\ S + N + 8 <= 0x800000000000)%Z.
    Hypothesis AFD : (0 <= A /\ A + N + 8 <= 0x800000000000)%Z.
    Hypothesis IRS : inmem_range S N.
    Hypothesis IRD : inmem_range A N.
    Hypothesis NGS : ((S + N - 1) / 8 - S / 8 = Z.of_nat ngS)%Z.
    Hypothesis NGD : ((A + N - 1) / 8 - A / 8 = Z.of_nat ngD)%Z.
    Hypothesis N1 : (1 <= N)%Z.

    Section P2.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(A, A + N); (bv_unsigned sp - MEMCPY_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2160).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis DST1 : rw_cells rsegs m1 A [CB (Z.to_nat N) junk].
      Hypothesis SRC1 : bytes_at rsegs m1 S src.
      Hypothesis Creal1 : ro_cells rsegs m1 0xaaa10 [C8 (Z_to_bv 64 0xa1b8c)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SHD1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ngD ++ [Z_to_bv 8 lastbD]).
      Hypothesis QBD1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1D).
      Hypothesis QBD2 : bytes_at rsegs m1 (sha (A + N + -1) - sha (A + N + -1) mod 8) (le8 w2D).
      Hypothesis SHS1 : bytes_at rsegs m1 (S / 8 + shadow_off) (zeros ngS ++ [Z_to_bv 8 lastbS]).
      Hypothesis QBS1 : bytes_at rsegs m1 (sha S - sha S mod 8) (le8 w1S).
      Hypothesis QBS2 : bytes_at rsegs m1 (sha (S + N + -1) - sha (S + N + -1) mod 8) (le8 w2S).

      (* [comment removed for export] *)
      Section SlowD.
        Variables (sf sl : Z) (x1 x5 x6 x7 x9 x17 x18 x19 x23 x24 x28 x29 x30 x31 : word).
        Hypothesis SEPD : SEPDt. Hypothesis DISJ : DISJt.
        Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ngD)%Z.
        Notation AT pc x13 x15 x16 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 (Z_to_bv 64 sl) x15 x16 x17 x18 x19 (Z_to_bv 64 (A + N + -1)) (Z_to_bv 64 (bv_unsigned sp + -2152))
                   (Z_to_bv 64 (N + -65)) x23 x24 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        #[using="DISJ SEPD Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk ngD ngS LEN LOLE junk Clg"] Lemma my_slowD_end : forall x13 x16, evt rsegs POST (AT 0x58358 x13 (Z_to_bv 64 0) x16).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. all: try (deadK K).
          eapply my_tail; try eassumption.
        Qed.

        #[using="ESL ESF DISJ SEPD SHD1 Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 AFD AFS lastbD ngS LEN LOLE junk Clg"] Lemma my_slowD_loop : forall (c : nat) (j : Z) x13 x16,
          Z.to_nat (Z.of_nat ngD - j) = c -> (0 <= j < Z.of_nat ngD)%Z -> x13 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x58348 x13 (Z_to_bv 64 0) x16).
        Proof.
          induction c as [|c IH]; intros j x13 x16 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SHD1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (A / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SHD1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ngD lastbD (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ngD)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply my_slowD_end.
        Qed.
      End SlowD.

      (* [comment removed for export] *)
      #[using="QBS2 QBS1 SHS1 QBD2 QBD1 SHD1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGD NGS IRD AFD AFS w2D w1D w2S w1S lastbS ngD ngS N32 LEN CEIL LOLE junk Clg"] Lemma my_p2 : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x23 x24 x28 x29 x30 x31,
        SEPDt -> SEPSt -> DISJt -> LBDt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (A + N)) (Z_to_bv 64 (bv_unsigned sp + -2152))
                   (Z_to_bv 64 (N + -65)) x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x57f74) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEPD SEPS DISJ LBD. pose proof LOLE as LOLE'. unfold MEMCPY_ICPT_STACK in LOLE'.
        unfold MEMCPY_ICPT_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
        pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
        assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (A + N + -1) - sha (A + N + -1) mod 8 + Z.of_nat (length (le8 w2D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH3 : (sha S - sha S mod 8 + Z.of_nat (length (le8 w1S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH4 : (sha (S + N + -1) - sha (S + N + -1) mod 8 + Z.of_nat (length (le8 w2S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SHD1 as SH. remember (zeros ngD ++ [Z_to_bv 8 lastbD]) as sbs eqn:Esbs.
        assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof SHS1 as SHS. remember (zeros ngS ++ [Z_to_bv 8 lastbS]) as sbsS eqn:EsbsS.
        assert (SHShi : (S / 8 + shadow_off + Z.of_nat (length sbsS) <= 0x100080000000)%Z).
        { subst sbsS. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QBD1 as QB1. pose proof QBD2 as QB2. pose proof QBS1 as QB3. pose proof QBS2 as QB4.
        zstep. rewrite zb_lxor_ones by lia.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep.
        zstep. if_cases K2; zify_cond K2.
        - zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          do 4 zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IRD
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ngD, lastbD; subst sbs; split; [exact NGD| split; [exact SH| exact LBD]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          do 4 zstep.
          zstep. if_cases K4; zify_cond K4. all: try (deadK K4).
          subst sbs sbsS. eapply my_tail; try eassumption.
        - assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (A + N + -1) 3 <= A + N - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 10 zstep.
          pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + subst sbs.
            assert (LBR : (0 <= lastbD < 128)%Z) by (hs_lbr lastbD).
            pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ngD) (Z_to_bv 8 lastbD)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (A + N + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngD lastbD ngD), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (A + N + -1) lastbD) by
              (first [destruct LBD as [LB0|LB1]; [left; exact LB0| right; replace (A + N + -1)%Z with (A + N - 1)%Z by (clear - LB1; lia); (clear - LB1; lia)] | lia]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (A + N + -1) / 8)%Z).
            assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ngD)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl. subst sbsS.
            zstep. if_cases K8; zify_cond K8.
            * eapply my_slowD_end; eassumption.
            * eapply my_slowD_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs sbsS. eapply my_tail; try eassumption.
      Qed.

    End P2.

    Section P1.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(A, A + N); (bv_unsigned sp - MEMCPY_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2160).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis DST1 : rw_cells rsegs m1 A [CB (Z.to_nat N) junk].
      Hypothesis SRC1 : bytes_at rsegs m1 S src.
      Hypothesis Creal1 : ro_cells rsegs m1 0xaaa10 [C8 (Z_to_bv 64 0xa1b8c)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SHD1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ngD ++ [Z_to_bv 8 lastbD]).
      Hypothesis QBD1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1D).
      Hypothesis QBD2 : bytes_at rsegs m1 (sha (A + N + -1) - sha (A + N + -1) mod 8) (le8 w2D).
      Hypothesis SHS1 : bytes_at rsegs m1 (S / 8 + shadow_off) (zeros ngS ++ [Z_to_bv 8 lastbS]).
      Hypothesis QBS1 : bytes_at rsegs m1 (sha S - sha S mod 8) (le8 w1S).
      Hypothesis QBS2 : bytes_at rsegs m1 (sha (S + N + -1) - sha (S + N + -1) mod 8) (le8 w2S).

      (* [comment removed for export] *)
      Section SlowS.
        Variables (sf sl : Z) (x1 x5 x6 x7 x9 x17 x18 x22 x23 x24 x28 x29 x30 x31 : word).
        Hypothesis SEPD : SEPDt. Hypothesis SEPS : SEPSt. Hypothesis DISJ : DISJt. Hypothesis LBD : LBDt.
        Hypothesis ESF : (sf = S / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ngS)%Z.
        Notation AT pc x13 x15 x16 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 (Z_to_bv 64 sl) x15 x16 x17 x18 (Z_to_bv 64 (S + N + -1)) (Z_to_bv 64 (A + N)) (Z_to_bv 64 (bv_unsigned sp + -2152))
                   (Z_to_bv 64 (N + -65)) x23 x24 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        #[using="LBD DISJ SEPS SEPD QBS2 QBS1 SHS1 QBD2 QBD1 SHD1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGD NGS IRD AFD AFS w2D w1D w2S w1S lastbD lastbS ngD ngS N32 LEN CEIL LOLE junk Clg"] Lemma my_slowS_end : forall x13 x16, evt rsegs POST (AT 0x58258 x13 (Z_to_bv 64 0) x16).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. all: try (deadK K).
          eapply my_p2; try eassumption.
        Qed.

        #[using="ESL ESF LBD DISJ SEPS SEPD QBS2 QBS1 SHS1 QBD2 QBD1 SHD1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGD NGS IRD AFD AFS w2D w1D w2S w1S lastbD lastbS ngD N32 LEN CEIL LOLE junk Clg"] Lemma my_slowS_loop : forall (c : nat) (j : Z) x13 x16,
          Z.to_nat (Z.of_nat ngS - j) = c -> (0 <= j < Z.of_nat ngS)%Z -> x13 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x58248 x13 (Z_to_bv 64 0) x16).
        Proof.
          induction c as [|c IH]; intros j x13 x16 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SHS1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (S / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SHS1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ngS lastbS (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ngS)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply my_slowS_end.
        Qed.
      End SlowS.

      (* [comment removed for export] *)
      #[using="QBS2 QBS1 SHS1 QBD2 QBD1 SHD1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 NGD NGS IRD IRS AFD AFS w2D w1D w2S w1S ngD ngS N32 LEN CEIL LOLE junk Clg"] Lemma my_p1 : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x22 x23 x24 x28 x29 x30 x31,
        SEPDt -> SEPSt -> DISJt -> LBSt -> LBDt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2160)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (S + N)) (Z_to_bv 64 (A + N)) (Z_to_bv 64 (bv_unsigned sp + -2152))
                   x22 x23 x24 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x57f28) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEPD SEPS DISJ LBS LBD. pose proof LOLE as LOLE'. unfold MEMCPY_ICPT_STACK in LOLE'.
        unfold MEMCPY_ICPT_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
        pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
        assert (QH1 : (sha S - sha S mod 8 + Z.of_nat (length (le8 w1S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (S + N + -1) - sha (S + N + -1) mod 8 + Z.of_nat (length (le8 w2S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH3 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH4 : (sha (A + N + -1) - sha (A + N + -1) mod 8 + Z.of_nat (length (le8 w2D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SHS1 as SH. remember (zeros ngS ++ [Z_to_bv 8 lastbS]) as sbs eqn:Esbs.
        assert (SHhi : (S / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof SHD1 as SHD. remember (zeros ngD ++ [Z_to_bv 8 lastbD]) as sbsD eqn:EsbsD.
        assert (SHDhi : (A / 8 + shadow_off + Z.of_nat (length sbsD) <= 0x100080000000)%Z).
        { subst sbsD. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QBS1 as QB1. pose proof QBS2 as QB2. pose proof QBD1 as QB3. pose proof QBD2 as QB4.
        zstep. rewrite zb_lxor_ones by lia.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep. zstep.
        zstep. if_cases K2; zify_cond K2.
        - zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          do 5 zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IRS
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ngS, lastbS; subst sbs; split; [exact NGS| split; [exact SH| exact LBS]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          do 4 zstep.
          zstep. if_cases K4; zify_cond K4. all: try (deadK K4).
          subst sbs sbsD. eapply my_p2; try eassumption.
        - assert (HS1 : (0 <= Z.shiftr S 3 <= S)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (S + N + -1) 3 <= S + N - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 10 zstep.
          pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + subst sbs.
            assert (LBR : (0 <= lastbS < 128)%Z) by (hs_lbr lastbS).
            pose proof (u8ro_read rsegs _ (S / 8 + shadow_off) _ (Z.of_nat ngS) (Z_to_bv 8 lastbS)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (S + N + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngS lastbS ngS), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (S + N + -1) lastbS) by
              (first [destruct LBS as [LB0|LB1]; [left; exact LB0| right; replace (S + N + -1)%Z with (S + N - 1)%Z by (clear - LB1; lia); (clear - LB1; lia)] | lia]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + S / 8)%Z). set (sl := (2147450880 + (S + N + -1) / 8)%Z).
            assert (ESF : (sf = S / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ngS)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl. subst sbsD.
            zstep. if_cases K8; zify_cond K8.
            * eapply my_slowS_end; eassumption.
            * eapply my_slowS_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs sbsD. eapply my_p2; try eassumption.
      Qed.
    End P1.
  End Facts.
End Proofs.
End AIcpdm8.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpwpz.AIcpdm8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require JunkName.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.split_for_access H segs m A cs kn n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.JunkName.split_for_access_jn H segs m A cs kn n.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dl_first | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker | hot2_mid | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

(* [comment removed for export] *)
Local Ltac zero_tail N0 :=
  let K2 := fresh "K" in let K3 := fresh "K" in let K5 := fresh "K" in let K6 := fresh "K" in let K7 := fresh "K" in let K8 := fresh "K" in
  zstep; rewrite zb_lxor_ones by lia;
  zstep; if_cases K2; zify_cond K2; [exfalso; lia|];
  zstep; zstep;
  zstep; if_cases K3; zify_cond K3; [| exfalso; rewrite N0 in K3; try (generalize alloc_ceiling_val); clear -K3; try pose proof alloc_ceiling_val; cbv in K3; first [lia | discriminate]];
  zstep; if_cases K5; zify_cond K5; [exfalso; lia|];
  zstep;
  zstep; rewrite zb_lxor_ones by lia;
  zstep; if_cases K6; zify_cond K6; [exfalso; lia|];
  zstep;
  zstep; if_cases K7; zify_cond K7; [| exfalso; rewrite N0 in K7; try (generalize alloc_ceiling_val); clear -K7; try pose proof alloc_ceiling_val; cbv in K7; first [lia | discriminate]];
  zstep; if_cases K8; zify_cond K8; [exfalso; lia|];
  zstep.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma memcpy_icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte) (lo : Z),
  let A := bv_unsigned a0 in let S := bv_unsigned a1 in let N := bv_unsigned a2 in
  bytes_at rsegs m S src -> length src = Z.to_nat N ->
  rw_cells rsegs m A [CB (Z.to_nat N) junk] ->
  (S + N <= A \/ A + N <= S)%Z ->
  mem_inv rsegs m ->
  asan_memcpy_cells m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo + MEMCPY_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + N <= lo \/ bv_unsigned sp <= A)%Z -> (S + N <= lo \/ bv_unsigned sp <= S)%Z ->
  (N < 2^32)%Z ->
  (N = 0%Z \/ (range_ok m S N /\ range_ok m A N)) ->
  evt rsegs (memcpy_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x574f8) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros SRC LEN DST DISJ MI CELLS ST LOLE CEIL SEPD SEPS N32 RNG.
  pose proof LOLE as LOLE'. unfold MEMCPY_ICPT_STACK in LOLE'.
  (first [ dand4 CELLS as Gric Cric Creal MC | destruct CELLS as (Gric & Cric & Creal & MC) ]). pose proof MC as MC'. open_map_cells MC'. clear MC.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - MEMCPY_ICPT_STACK, bv_unsigned sp)]%Z m) as MU.
  unfold MEMCPY_ICPT_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a1) as A1R; unfold inr64 in A1R.
  pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (bytes_at_bound _ _ _ _ SRC) as SB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (NW : (bv_unsigned a0 + bv_unsigned a2 < 2^64 /\ bv_unsigned a1 + bv_unsigned a2 < 2^64)%Z).
  { destruct RNG as [N0|((IR1 & _) & (IR2 & _))]; [rewrite N0; lia| unfold inmem_range in IR1, IR2; lia]. }
  destruct (Z.eq_dec (bv_unsigned a2) 0) as [N0 | NZ].
  { (* [comment removed for export] *)
    freeze DST; freeze SRC; freeze Gric; freeze Cric; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb;
    freeze Gme; freeze Cme; freeze Ghe; freeze Che.
    pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m) as MUp.
    zstep. carve_frame 80%nat ST. carve_frame 2080%nat ST.
    do 13 zstep.
    thaw DST MUp WM; thaw SRC MUp WM; thaw Gric MUp WM; thaw Cric MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
    thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM. clear MUp.
    do 2 zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
    zstep. if_cases K0; zify_cond K0. { deadK K0. }
    do 4 zstep.
    zstep. if_cases Ka; zify_cond Ka.
    - zero_tail N0. eapply my_tail; try eassumption.
    - zstep. if_cases Kb; zify_cond Kb.
      + zero_tail N0. eapply my_tail; try eassumption.
      + zstep. if_cases Kc; zify_cond Kc. { exfalso. lia. }
        zero_tail N0. eapply my_tail; try eassumption. }
  (* [comment removed for export] *)
  destruct RNG as [N0 | (RS & RD)]; [exfalso; lia|].
  assert (N1 : (1 <= bv_unsigned a2)%Z) by lia.
  (first [ dand4 RS as IRS SOKS QWS1 QWS2 | destruct RS as (IRS & SOKS & QWS1 & QWS2) ]). (first [ dand4 RD as IRD SOKD QWD1 QWD2 | destruct RD as (IRD & SOKD & QWD1 & QWD2) ]).
  assert (AFS : (0 <= bv_unsigned a1 /\ bv_unsigned a1 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRS; lia).
  assert (AFD : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IRD; lia).
  destruct (mapped8_le8 m _ QWS1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1S QBS1].
  destruct (mapped8_le8 m _ QWS2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2S QBS2].
  destruct (mapped8_le8 m _ QWD1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1D QBD1].
  destruct (mapped8_le8 m _ QWD2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2D QBD2].
  replace (bv_unsigned a1 + bv_unsigned a2 - 1)%Z with (bv_unsigned a1 + bv_unsigned a2 + -1)%Z in QBS2 by lia.
  replace (bv_unsigned a0 + bv_unsigned a2 - 1)%Z with (bv_unsigned a0 + bv_unsigned a2 + -1)%Z in QBD2 by lia.
  assert (QH1 : (sha (bv_unsigned a1) - sha (bv_unsigned a1) mod 8 + Z.of_nat (length (le8 w1S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (bv_unsigned a1 + bv_unsigned a2 + -1) - sha (bv_unsigned a1 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2S)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH3 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH4 : (sha (bv_unsigned a0 + bv_unsigned a2 + -1) - sha (bv_unsigned a0 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  (first [ dex2 SOKS as ngS lastbS; dand3 SOKS as NGS SHS LBS | dand5 SOKS as ngS lastbS NGS SHS LBS | destruct SOKS as (ngS & lastbS & NGS & SHS & LBS) ]). (first [ dex2 SOKD as ngD lastbD; dand3 SOKD as NGD SHD LBD | dand5 SOKD as ngD lastbD NGD SHD LBD | destruct SOKD as (ngD & lastbD & NGD & SHD & LBD) ]).
  remember (zeros ngS ++ [Z_to_bv 8 lastbS]) as sbsS eqn:EsbsS.
  remember (zeros ngD ++ [Z_to_bv 8 lastbD]) as sbsD eqn:EsbsD.
  assert (SHShi : (bv_unsigned a1 / 8 + shadow_off + Z.of_nat (length sbsS) <= 0x100080000000)%Z).
  { subst sbsS. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  assert (SHDhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbsD) <= 0x100080000000)%Z).
  { subst sbsD. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  freeze DST; freeze SRC; freeze Gric; freeze Cric; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb;
  freeze Gme; freeze Cme; freeze Ghe; freeze Che; freeze SHS; freeze SHD; freeze QBS1; freeze QBS2; freeze QBD1; freeze QBD2.
  pose proof (munch_refl [(bv_unsigned sp - 2160, bv_unsigned sp)]%Z m) as MUp.
  zstep. carve_frame 80%nat ST. carve_frame 2080%nat ST.
  do 13 zstep.
  thaw DST MUp WM; thaw SRC MUp WM; thaw Gric MUp WM; thaw Cric MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
  thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM;
  thaw SHS MUp WM; thaw SHD MUp WM; thaw QBS1 MUp WM; thaw QBS2 MUp WM; thaw QBD1 MUp WM; thaw QBD2 MUp WM. clear MUp.
  do 2 zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
  zstep. if_cases K0; zify_cond K0. { deadK K0. }
  do 4 zstep.
  zstep. if_cases Ka; zify_cond Ka.
  - subst sbsS sbsD. eapply my_p1; try eassumption.
  - zstep. if_cases Kb; zify_cond Kb.
    + subst sbsS sbsD. eapply my_p1; try eassumption.
    + zstep. if_cases Kc; zify_cond Kc. { exfalso. lia. }
      subst sbsS sbsD. eapply my_p1; try eassumption.
Qed.

End CEIL.
