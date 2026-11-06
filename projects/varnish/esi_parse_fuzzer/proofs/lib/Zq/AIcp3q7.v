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
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_mqq1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LEN; @AFD; @AFS; @Hc; @Hj; @SB; @ESL; @A0R; @HS2; @ESF; @SPR; @CEIL; @LOLE'; @A2R; @SFB; @H; @CV; @LBR; @LOLE; @K; @K3; @DISJ; @K1; @N32; @K4; @HS1; @LBD; @LB1; @SHhi; @K8])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
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
Local Ltac hs_lbr X :=
  first [ match goal with H : (X = 0 \/ ?m < X <= 7)%Z |- _ =>
            clear - H; lazymatch m with (?a mod ?b)%Z => pose proof (Z.mod_pos_bound a b ltac:(reflexivity)) | _ => idtac end; lia end
        | lia ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition asan_memcpy_entry : Z := 0x574fc.
Definition ASAN_MEMCPY_STACK : Z := 2224.

(* [comment removed for export] *)
Definition asan_memcpy_cells (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xa96e0 [C8 (Z_to_bv 64 0xb5899)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb5899 [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaaa10 [C8 (Z_to_bv 64 0xa1b8c)]      (* [comment removed for export] *)
  /\ map_cells m.

Definition asan_memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - ASAN_MEMCPY_STACK, bv_unsigned sp)]%Z m m'
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
  Notation POST := (asan_memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src lo m).
  (* [comment removed for export] *)
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -72)
                          [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 2072 fjunk]).
  Hypothesis LOLE : (lo + ASAN_MEMCPY_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Hypothesis LEN : length src = Z.to_nat N.
  Hypothesis N32 : (N < 2^32)%Z.
  (* [comment removed for export] *)
  Notation SEPDt := ((A + N <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).
  Notation SEPSt := ((S + N <= lo \/ bv_unsigned sp <= S)%Z) (only parsing).
  Notation DISJt := ((S + N <= A \/ A + N <= S)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="LEN LOLE"] Lemma mc_tail : forall m1 fjunk x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x22 x23 x28 x29 x30 x31,
    SEPDt -> DISJt -> mem_inv rsegs m1 ->
    munch [(A, A + N); (bv_unsigned sp - ASAN_MEMCPY_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2144) -> FRAME m1 -> FRAMEB m1 fjunk ->
    rw_cells rsegs m1 A [CB (Z.to_nat N) junk] -> bytes_at rsegs m1 S src ->
    ro_cells rsegs m1 0xaaa10 [C8 (Z_to_bv 64 0xa1b8c)] ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
               a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2144)) x21 x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x575ec) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros SEPD DISJ MI1 MU1 WM1 ST1 FR1 FRB1 DST1 SRC1 Creal1. unfold ASAN_MEMCPY_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word a0) as A0R; unfold inr64 in A0R.
    pose proof (zr_word a1) as A1R; unfold inr64 in A1R. pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
    zstep. zstep.
    zstep. call memcpy_spec. 1:{ exact SRC1. } 1:{ exact LEN. } 1:{ exact DST1. } 1:{ exact DISJ. } 1:{ exact MI1. }
    do 12 zstep.
    release_frame FRB1 ST1 (bv_unsigned sp + -72)%Z. release_frame FR1 ST1 (bv_unsigned sp). finish.
  Qed.

  Section Facts.
    (* [comment removed for export] *)
    Variables (ngS ngD : nat) (lastbS lastbD : Z) (w1S w2S w1D w2D : word).
    Notation LBSt := ((lastbS = 0 \/ ((S + N - 1) mod 8 < lastbS <= 7))%Z) (only parsing).
    Notation LBDt := ((lastbD = 0 \/ ((A + N - 1) mod 8 < lastbD <= 7))%Z) (only parsing).
    Hypothesis AFS : (0 <= S /\ S + N + 8 <= 0x800000000000)%Z.
    Hypothesis AFD : (0 <= A /\ A + N + 8 <= 0x800000000000)%Z.
    Hypothesis IRS : inmem_range S N.
    Hypothesis IRD : inmem_range A N.
    Hypothesis NGS : ((S + N - 1) / 8 - S / 8 = Z.of_nat ngS)%Z.
    Hypothesis NGD : ((A + N - 1) / 8 - A / 8 = Z.of_nat ngD)%Z.

    Section Phase2.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(A, A + N); (bv_unsigned sp - ASAN_MEMCPY_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2144).
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

      Section SlowD.
        Variables (sf sl : Z) (x1 x5 x6 x7 x9 x17 x18 x21 x23 x28 x29 x30 x31 : word).
        Hypothesis SEPD : SEPDt. Hypothesis DISJ : DISJt.
        Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ngD)%Z.
        Notation AT pc x13 x15 x16 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 (Z_to_bv 64 sl) x15 x16 x17 x18 (Z_to_bv 64 (A + N + -1)) (Z_to_bv 64 (bv_unsigned sp + -2144))
                   x21 (Z_to_bv 64 (N + -65)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        (* [comment removed for export] *)
        #[using="DISJ SEPD Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk LEN LOLE junk Clg"] Lemma mc_slowD_end : forall x13 x16, evt rsegs POST (AT 0x57924 x13 (Z_to_bv 64 0) x16).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. unfold ASAN_MEMCPY_STACK in *.
          zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
          eapply mc_tail; try eassumption.
        Qed.

        (* [comment removed for export] *)
        #[using="ESL ESF DISJ SEPD SHD1 Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk AFD AFS lastbD ngS LEN LOLE junk Clg"] Lemma mc_slowD_loop : forall (c : nat) (j : Z) x13 x16,
          Z.to_nat (Z.of_nat ngD - j) = c -> (0 <= j < Z.of_nat ngD)%Z -> x13 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x57914 x13 (Z_to_bv 64 0) x16).
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
          - apply mc_slowD_end.
        Qed.
      End SlowD.

      (* [comment removed for export] *)
      #[using="QBD2 QBD1 SHD1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal1 SRC1 DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk NGD IRD AFD AFS w2D w1D ngD ngS N32 LEN CEIL LOLE junk Clg"] Lemma mc_p2 : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x21 x23 x28 x29 x30 x31,
        SEPDt -> SEPSt -> DISJt -> LBDt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 (A + N)) (Z_to_bv 64 (bv_unsigned sp + -2144))
                   x21 (Z_to_bv 64 (N + -65)) x23 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x575a4) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEPD SEPS DISJ LBD. pose proof LOLE as LOLE'. unfold ASAN_MEMCPY_STACK in LOLE'.
        unfold ASAN_MEMCPY_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
        assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (A + N + -1) - sha (A + N + -1) mod 8 + Z.of_nat (length (le8 w2D)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SHD1 as SH. remember (zeros ngD ++ [Z_to_bv 8 lastbD]) as sbs eqn:Esbs.
        assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QBD1 as QB1. pose proof QBD2 as QB2.
        zstep. rewrite zb_lxor_ones by lia.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3.
          + (* [comment removed for export] *)
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
            zstep. if_cases K4; zify_cond K4. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K4; try pose proof alloc_ceiling_val. cbv in K4. lia. }
            eapply mc_tail; try eassumption.
          + (* [comment removed for export] *)
            zstep. eapply mc_tail; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (A + N + -1) 3 <= A + N - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 9 zstep.
          pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
          zstep. zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + (* [comment removed for export] *)
            subst sbs.
            assert (LBR : (0 <= lastbD < 128)%Z) by (hs_lbr lastbD).
            pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ngD) (Z_to_bv 8 lastbD)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (A + N + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ngD lastbD ngD), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (A + N + -1) lastbD) by
              (first [destruct LBD as [LB0|LB1]; [left; exact LB0| right;
                 replace (A + N + -1)%Z with (A + N - 1)%Z by (clear - LB1; lia); (clear - LB1; lia)] | lia]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (A + N + -1) / 8)%Z).
            assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ngD)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl.
            zstep. if_cases K8; zify_cond K8.
            * eapply mc_slowD_end; eassumption.
            * eapply mc_slowD_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + eapply mc_tail; try eassumption.
      Qed.
    End Phase2.
  End Facts.
End Proofs.
