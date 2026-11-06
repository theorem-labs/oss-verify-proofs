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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA RA_m7de.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require CallLit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw.CallLit.AIcpmc7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc AIcp7wm AIcpya4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpdmn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpya4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
Local Ltac deadK K := exfalso; first [lia | (try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val; cbv in K; first [lia | discriminate | congruence | exact (K eq_refl)])].

Definition memset_icpt_entry : Z := 0x574f4.
Definition MEMSET_ICPT_STACK : Z := 2224.
(* [comment removed for export] *)

Definition memset_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - MEMSET_ICPT_STACK, bv_unsigned sp)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' (bv_unsigned a0)
         [CB (Z.to_nat (bv_unsigned a2)) (repeat (Z_to_bv 8 (bv_unsigned a1 mod 256)) (Z.to_nat (bv_unsigned a2)))].

Section Proofs.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (junk : list byte) (lo : Z).
  Notation A := (bv_unsigned a0).
  Notation N := (bv_unsigned a2).
  Notation POST := (memset_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).
  Notation FRAME m1 := (rw_cells rsegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
  Notation FRAMEB m1 fjunk := (rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 2080 fjunk]).
  Hypothesis LOLE : (lo + MEMSET_ICPT_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  Notation SEPt := ((A + N <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="LOLE Clg"] Lemma mi_tail : forall m1 fjunk x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x22 x28 x29 x30 x31,
    SEPt -> mem_inv rsegs m1 ->
    munch [(A, A + N); (bv_unsigned sp - MEMSET_ICPT_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2144) -> FRAME m1 -> FRAMEB m1 fjunk ->
    rw_cells rsegs m1 A [CB (Z.to_nat N) junk] ->
    ro_cells rsegs m1 0xaaa18 [C8 (Z_to_bv 64 0xa1f90)] ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
               a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x57c6c) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros SEP MI1 MU1 WM1 ST1 FR1 FRB1 DST1 Creal1. unfold MEMSET_ICPT_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word a0) as A0R; unfold inr64 in A0R.
    pose proof (zr_word a2) as A2R; unfold inr64 in A2R. pose proof alloc_ceiling_val as CV.
    zstep. zstep.
    zstep. call memset_spec. 1:{ exact DST1. } 1:{ exact MI1. }
    do 11 zstep.
    release_frame FRB1 ST1 (bv_unsigned sp + -64)%Z. release_frame FR1 ST1 (bv_unsigned sp). finish.
  Qed.

  Section Facts.
    Variables (ng : nat) (lastb : Z) (w1 w2 : word).
    Notation LBt := ((lastb = 0 \/ ((A + N - 1) mod 8 < lastb <= 7))%Z) (only parsing).
    Hypothesis AF : (0 <= A /\ A + N + 8 <= 0x800000000000)%Z.
    Hypothesis IR : inmem_range A N.
    Hypothesis NG : ((A + N - 1) / 8 - A / 8 = Z.of_nat ng)%Z.
    Hypothesis N1 : (1 <= N)%Z.
    Hypothesis N32 : (N < 2^32)%Z.

    Section M1.
      Variables (m1 : word -> option byte) (fjunk : list byte).
      Hypothesis MI1 : mem_inv rsegs m1.
      Hypothesis MU1 : munch [(A, A + N); (bv_unsigned sp - MEMSET_ICPT_STACK, bv_unsigned sp)]%Z m m1.
      Hypothesis WM1 : wmono rsegs m m1.
      Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2144).
      Hypothesis FR1 : FRAME m1.
      Hypothesis FRB1 : FRAMEB m1 fjunk.
      Hypothesis DST1 : rw_cells rsegs m1 A [CB (Z.to_nat N) junk].
      Hypothesis Creal : ro_cells rsegs m1 0xaaa18 [C8 (Z_to_bv 64 0xa1f90)].
      Hypothesis Gsh : ro_cells rsegs m1 0xa8b70 [C8 (Z_to_bv 64 0xb4bb8)].
      Hypothesis Csh : ro_cells rsegs m1 0xb4bb8 [C8 (Z_to_bv 64 0x7fff8000)].
      Hypothesis Gmb : ro_cells rsegs m1 0xa8b78 [C8 (Z_to_bv 64 0xb58a8)].
      Hypothesis Cmb : ro_cells rsegs m1 0xb58a8 [C8 (Z_to_bv 64 0)].
      Hypothesis Gme : ro_cells rsegs m1 0xa8b80 [C8 (Z_to_bv 64 0xb58b0)].
      Hypothesis Cme : ro_cells rsegs m1 0xb58b0 [C8 (Z_to_bv 64 0)].
      Hypothesis Ghe : ro_cells rsegs m1 0xa8b88 [C8 (Z_to_bv 64 0xb58a0)].
      Hypothesis Che : ro_cells rsegs m1 0xb58a0 [C8 (Z_to_bv 64 0x7fffffffffff)].
      Hypothesis SH1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
      Hypothesis QB1 : bytes_at rsegs m1 (sha A - sha A mod 8) (le8 w1).
      Hypothesis QB2 : bytes_at rsegs m1 (sha (A + N + -1) - sha (A + N + -1) mod 8) (le8 w2).

      Section Slow.
        Variables (sf sl : Z) (x1 x5 x6 x7 x9 x17 x18 x19 x20 x22 x28 x29 x30 x31 : word).
        Hypothesis SEP : SEPt.
        Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
        Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.
        Notation AT pc x13 x15 x16 :=
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 (Z_to_bv 64 sl) x15 x16 x17 x18 x19 x20 (Z_to_bv 64 (bv_unsigned sp + -2136)) x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

        #[using="SEP Creal DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk ng LOLE junk Clg"] Lemma mi_slow_end : forall x13 x16, evt rsegs POST (AT 0x57db0 x13 (Z_to_bv 64 0) x16).
        Proof.
          intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
          zstep. zstep. if_cases K; zify_cond K. all: try (deadK K).
          eapply mi_tail; try eassumption.
        Qed.

        #[using="ESL ESF SEP SH1 Creal DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N1 AF lastb LOLE junk Clg"] Lemma mi_slow_loop : forall (c : nat) (j : Z) x13 x16,
          Z.to_nat (Z.of_nat ng - j) = c -> (0 <= j < Z.of_nat ng)%Z -> x13 = Z_to_bv 64 (sf + j) ->
          evt rsegs POST (AT 0x57da0 x13 (Z_to_bv 64 0) x16).
        Proof.
          induction c as [|c IH]; intros j x13 x16 Hc Hj ->; [lia|].
          pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (bytes_at_bound _ _ _ _ SH1) as SB.
          rewrite length_app, zeros_length in SB. cbn [length] in SB.
          pose proof (u8ro_read rsegs m1 (A / 8 + shadow_off) _ j (Z_to_bv 8 0) (Z_to_bv 64 (sf + j)) SH1) as RD.
          specialize (RD ltac:(rewrite (shadow_nth ng lastb (Z.to_nat j)) by lia;
                                 replace (Z.to_nat j <? ng)%nat with true by (symmetry; apply Nat.ltb_lt; lia); reflexivity)
                         ltac:(lia) ltac:(unfold wa; f_equal; lia)).
          zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 0)) with 0%Z.
          zstep. zstep.
          zstep. if_cases K; zify_cond K.
          - apply (IH (j + 1)%Z); [lia|lia|f_equal; lia].
          - apply mi_slow_end.
        Qed.
      End Slow.

      (* [comment removed for export] *)
      #[using="QB2 QB1 SH1 Che Ghe Cme Gme Cmb Gmb Csh Gsh Creal DST1 FRB1 FR1 ST1 WM1 MU1 MI1 fjunk N32 N1 NG IR AF w2 w1 ng CEIL LOLE junk Clg"] Lemma mi_check : forall x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
        SEPt -> LBt ->
        evt rsegs POST
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
                   a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x57c14) fc None m1 (seg_rom rsegs)).
      Proof.
        intros until x31. intros SEP LB. pose proof LOLE as LOLE'. unfold MEMSET_ICPT_STACK in LOLE'.
        unfold MEMSET_ICPT_STACK in MU1.
        pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
        pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
        pose proof (rw_cells_bound _ _ _ _ DST1) as DB. cbn [cells_size csize Nat.add] in DB.
        assert (QH1 : (sha A - sha A mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        assert (QH2 : (sha (A + N + -1) - sha (A + N + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
        pose proof SH1 as SH. remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
        assert (SHhi : (A / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
        { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
        pose proof QB1 as QB1'. pose proof QB2 as QB2'.
        zstep. rewrite zb_lxor_ones by lia.
        zstep. zstep.
        zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
        zstep. zstep.
        zstep. if_cases K2; zify_cond K2.
        - (* [comment removed for export] *)
          zstep. if_cases K3; zify_cond K3. 2:{ exfalso. lia. }
          do 4 zstep.
          zstep. call_lit region_is_poisoned_spec by (idtac;
            lazymatch goal with
            | |- map_cells _ => repeat (split; [assumption|]); assumption
            | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST1
            | |- mem_inv _ _ => eassumption
            | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IR
            | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ng, lastb; subst sbs; split; [exact NG| split; [exact SH| exact LB]]
            | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
            end).
          do 4 zstep.
          zstep. if_cases K4; zify_cond K4. all: try (deadK K4).
          subst sbs. eapply mi_tail; try eassumption.
        - (* [comment removed for export] *)
          assert (HS1 : (0 <= Z.shiftr A 3 <= A)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          assert (HS2 : (0 <= Z.shiftr (A + N + -1) 3 <= A + N - 1)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
          do 11 zstep.
          pose proof (qc_read _ _ _ QB1' ltac:(lia)) as RD1.
          pose proof (qc_read _ _ _ QB2' ltac:(lia)) as RD2.
          zstep. zstep. zstep.
          zstep. if_cases K7; zify_cond K7.
          + subst sbs.
            assert (LBR : (0 <= lastb < 128)%Z) by lia.
            pose proof (u8ro_read rsegs _ (A / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                          (Z_to_bv 64 (2147450880 + Z.shiftr (A + N + -1) 3)) SH) as RD.
            specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                           ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
            zstep. rewrite sxb_small by lia.
            zstep. zstep. zstep. zstep. zstep.
            rewrite (poisoned_last_zero (A + N + -1) lastb) by
              (first [lia | destruct LB as [LB0|LB1]; [left; exact LB0| right; replace (A + N + -1)%Z with (A + N - 1)%Z by lia; lia]]).
            rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
            set (sf := (2147450880 + A / 8)%Z). set (sl := (2147450880 + (A + N + -1) / 8)%Z).
            assert (ESF : (sf = A / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
            assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
            assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
            { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
            clearbody sf sl.
            zstep. if_cases K8; zify_cond K8.
            * eapply mi_slow_end; eassumption.
            * eapply mi_slow_loop with (j := 0%Z); try eassumption; try reflexivity; try lia. f_equal; lia.
          + subst sbs. eapply mi_tail; try eassumption.
      Qed.
    End M1.
  End Facts.
End Proofs.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma memset_icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte) (lo : Z),
  let A := bv_unsigned a0 in let N := bv_unsigned a2 in
  rw_cells rsegs m A [CB (Z.to_nat N) junk] ->
  mem_inv rsegs m ->
  asan_memset_cells m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo + MEMSET_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + N <= lo \/ bv_unsigned sp <= A)%Z ->
  (N < 2^32)%Z ->
  (N = 0%Z \/ range_ok m A N) ->
  evt rsegs (memset_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x574f4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros DST MI CELLS ST LOLE CEIL SEP N32 RNG.
  pose proof LOLE as LOLE'. unfold MEMSET_ICPT_STACK in LOLE'.
  destruct CELLS as (Gric & Cric & Creal & MC). pose proof MC as MC'. open_map_cells MC'. clear MC.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - MEMSET_ICPT_STACK, bv_unsigned sp)]%Z m) as MU.
  unfold MEMSET_ICPT_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (NW : (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z).
  { destruct RNG as [N0|(IR & _)]; [rewrite N0; lia| unfold inmem_range in IR; lia]. }
  destruct (Z.eq_dec (bv_unsigned a2) 0) as [N0 | NZ].
  { (* [comment removed for export] *)
    freeze DST; freeze Gric; freeze Cric; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb; freeze Gme; freeze Cme; freeze Ghe; freeze Che.
    pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
    zstep. carve_frame 64%nat ST. carve_frame 2080%nat ST.
    do 11 zstep.
    thaw DST MUp WM; thaw Gric MUp WM; thaw Cric MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
    thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM. clear MUp.
    do 2 zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
    zstep. if_cases K0; zify_cond K0. { deadK K0. }
    do 3 zstep. rewrite zb_lxor_ones by lia.
    zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep.
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite N0 in K2. clear -K2; try pose proof alloc_ceiling_val. cbv in K2. first [lia | discriminate]. }
    zstep. if_cases K3; zify_cond K3. { exfalso. lia. }
    zstep. eapply mi_tail; try eassumption. }
  destruct RNG as [N0 | (IR & SOK & QW1 & QW2)]; [exfalso; lia|].
  assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  destruct (mapped8_le8 m _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
  destruct (mapped8_le8 m _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
  replace (bv_unsigned a0 + bv_unsigned a2 - 1)%Z with (bv_unsigned a0 + bv_unsigned a2 + -1)%Z in QB2 by lia.
  assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (bv_unsigned a0 + bv_unsigned a2 + -1) - sha (bv_unsigned a0 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  destruct SOK as (ng & lastb & NG & SH & LB).
  remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
  assert (SHhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
  { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  freeze DST; freeze Gric; freeze Cric; freeze Creal; freeze Gsh; freeze Csh; freeze Gmb; freeze Cmb; freeze Gme; freeze Cme; freeze Ghe; freeze Che;
  freeze SH; freeze QB1; freeze QB2.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m) as MUp.
  zstep. carve_frame 64%nat ST. carve_frame 2080%nat ST.
  do 11 zstep.
  thaw DST MUp WM; thaw Gric MUp WM; thaw Cric MUp WM; thaw Creal MUp WM; thaw Gsh MUp WM; thaw Csh MUp WM;
  thaw Gmb MUp WM; thaw Cmb MUp WM; thaw Gme MUp WM; thaw Cme MUp WM; thaw Ghe MUp WM; thaw Che MUp WM;
  thaw SH MUp WM; thaw QB1 MUp WM; thaw QB2 MUp WM. clear MUp.
  do 2 zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
  zstep. if_cases K0; zify_cond K0. { deadK K0. }
  subst sbs. eapply mi_check; try eassumption; lia.
Qed.

End CEIL.
