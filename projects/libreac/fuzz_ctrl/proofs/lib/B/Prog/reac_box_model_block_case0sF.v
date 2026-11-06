(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 788 of its 804 lines of code are new or changed and 128 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/reac_box_model_block_case0.v, with its addresses changed; 490 of its 586 lines of code are new or changed and 708 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcRecLib RcBox RcBoxLib
  RcSynth RcSynthLib RcParseLib RcKindLib RcLay RcAsan RcAsanLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c build_dt1_single_c dt1_head_c name_field_c reac_box_model_block_c
  reac_box_model_block reac_box_model_block_case0s reac_box_model_blockF.
(* Last: StepF's step / if_false / mem_after_store (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The footprint twin of reac_box_model_block_case0s.v (image B, asan-ubsan; RECIPE.md step 1, route 2 (a working note, not in this delivery)):
   the case-0 slot chain of reac_box_model_block, from the two sides of the lay test at 0x868c0 to the tail at
   0x8710c, as ExecF.evtF runs under the footprint RNG, by the scripts of the plain file over StepF's step.  The tail
   is the Section hypothesis Htail in its evtF form.  Every definition and every lemma of the plain file that does
   not mention `evt` (c0s_in_r, c0s_not, c0s_H8, c0s_R, c0s_at, c0s_Q, c0s_K, c0s_G, c0s_go, c0s_ac, c0s_chk,
   c0s_ok, c0s_ost) is reused from there with its Section arguments; this file restates the thirteen that do, each
   with the suffix F.  The Section preamble is the plain one with the callee contracts in their footprint forms, the
   footprint RNG and the run's footprint HRNG (reac_box_model_blockF.v's mbF_rng). *)

(* The hooks of reac_box_model_blockF.v (Local there, so repeated here verbatim). *)
Ltac mbF_fix_lit_store :=
  match goal with
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) => rewrite (le8_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?z)) _) => rewrite (le4_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 2 ?z)) _) => rewrite (le2_lit z) by lia
  | |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 1 ?z)) _) => rewrite (le1_zlit z) by lia
  | _ => idtac
  end.

Ltac mbF_store_opt :=
  try mbF_fix_lit_store;
  lazymatch goal with
  | |- evtF ?segs _ _ (MS _ _ _ _ _ (write_to_mem ?m (wa (?A + Z.of_nat _)) _) _) =>
      match goal with
      | H : rw_cells segs m A _ |- _ => mem_after_store
      | _ => idtac
      end
  | _ => idtac
  end.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= mbF_store_opt.

Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= mbF_acc_hint.

Section Body.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (p b o FS off A : Z) (row nb ob : list byte) (RNG : footprint).
  Hypothesis HSM : asan_stack_malloc_0_contract_F.
  Hypothesis Hoff : off = ASAN_K.
  Hypothesis HA : A = (bv_unsigned sp - 160) / 32 * 32.
  Hypothesis HS16 : bv_unsigned sp mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (bv_unsigned sp - 4272) (bv_unsigned sp).
  Hypothesis MI0 : mem_inv rsegs m.
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : shadow_rw m.
  Hypothesis HHM : HIGHMEM_BEG <= bv_unsigned sp - 4272.
  Hypothesis HAE : bv_unsigned sp <= APPMEM_END.
  Hypothesis AW0 : addressable m (bv_unsigned sp - 4272) 4272.
  Hypothesis FP0 : fp [0%nat] m (bv_unsigned tp) FS (bv_unsigned sp - 4272) (bv_unsigned sp)
    (reac_box_model_block_W o (bv_unsigned sp)) (reac_box_model_block_D p o).
  Hypothesis TLS0 : reac_box_model_block_tls m (bv_unsigned tp) FS (bv_unsigned sp - REAC_BOX_MODEL_BLOCK_K) (bv_unsigned sp).
  Hypothesis Rp : 0 <= p < 2^64.
  Hypothesis Rb : 0 <= b < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis HP : p <> 0 -> p mod 8 = 0 /\ length row = 296%nat /\ bytes_at rsegs m p row /\
    (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) /\ (o = 0 \/ o + 32 <= p \/ p + 296 <= o).
  Hypothesis HN : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    name_ok nb /\ bytes_at rsegs m (rname row) nb /\
    (bv_unsigned sp <= rname row \/ rname row + Z.of_nat (length nb) <= bv_unsigned sp - 4272) /\
    (o = 0 \/ o + 32 <= rname row \/ rname row + Z.of_nat (length nb) <= o).
  Hypothesis HO : o <> 0 -> rw_cells rsegs m o [CB 32 ob] /\
    (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) /\ (o + 32 <= JOIN_0013 \/ JOIN_0014 + 32 <= o).
  Hypothesis AP : p <> 0 -> addressable m p 296.
  Hypothesis ANB : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    addressable m (rname row) (Z.of_nat (length nb)).
  Hypothesis AO : o <> 0 -> addressable m o 32 /\ app_mem (o + 32) /\ (o + 32 <= RT_LO \/ RT_HI <= o).
  Hypothesis AJ1 : b = 1 -> addressable m JOIN_0014 32.
  Hypothesis AJ2 : b = 2 -> addressable m JOIN_0013 32.
  Hypothesis NDJ : p <> 0 -> (b = 5 \/ b = 6) -> has row <> 0 -> rname row <> 0 ->
    fp_dj [(rname row, rname row + Z.of_nat (length nb))] (fp_w [0%nat] FS).

  Hypothesis HMS : asan_memset_contract_F.
  Hypothesis HMC : asan_memcpy_contract_F.
  Hypothesis HBD : build_dt1_single_contract_F.
  Hypothesis HDH : dt1_head_contract_F.
  Hypothesis HNF : name_field_contract_F.

  (* The tail at 0x8710c (the evtF twin of c0_tailc of reac_box_model_block_case0.v). *)
  Hypothesis Htail :
  forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
         (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 : word),
      b = 0 -> synok row = true ->
      0 < p -> p mod 8 = 0 -> length row = 296%nat -> p + 296 <= APPMEM_END ->
      0 < o -> o + 32 <= APPMEM_END ->
      (p + 296 <= o \/ o + 32 <= p) ->
      (FS + 8 <= o \/ o + 32 <= FS) ->
      (fr + 64 <= o \/ o + 32 <= fr) ->
      (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) ->
      (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) ->
      (forall i, 0 <= i <= 32 -> app_mem (o + i)) ->
      FS + 8 <= bv_unsigned sp - 4272 ->
      bv_unsigned sp - 240 <= spc -> spc <= bv_unsigned sp - 160 ->
      (fr + 64 <= spc - 2224 \/ spc <= fr + 56) ->
      (o + 32 <= RT_LO \/ RT_HI <= o) ->
      addressable m p 296 -> addressable m o 32 -> bytes_at rsegs m p row ->
      (forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      (forall i, 0 <= i < 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (p + i))) ->
      (forall i, 0 <= i < 32 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (o + i))) ->
      (forall x, RT_LO <= x < RT_HI -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      FK FS A fr f spc j n w56 ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 ([bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row] ++ slots row ++ zeros 12)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x8710c) fc None mc (seg_rom rsegs)).

  Hypothesis HRNG : mbF_rng RNG m sp tp p b o FS row nb.

  Ltac c0s_clr := clear HSM HA HS16 ST0 MI0 AC0 SR0 HHM HAE AW0 FP0 TLS0 Rp Rb Ro HP HN HO AP ANB AO AJ1 AJ2 NDJ
    HMS HMC HBD HDH HNF.

  (* One step that stores a byte at offset kk of the output block, then the carried state at the new memory. *)
  Ltac c0s_vst kk :=
    lazymatch goal with
    | G : c0s_G sp m p b o FS A row ?fr ?f ?spc ?j ?n ?w56,
      HB : c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS ?fr ?j ?n ?w56 ?mm,
      HV : rw_cells rsegs ?mm o [CB 32 ?X] |- _ =>
        let HSo := fresh "HSo" in
        pose proof (c0s_ok o mm X kk ltac:(lia) HV) as HSo;
        step; clear HSo;
        lazymatch goal with |- context [write_to_mem mm (Z_to_bv 64 (o + Z.of_nat kk)) (le1 ?v)] =>
          let HB' := fresh "HB" in let HV' := fresh "HV" in
          destruct (c0s_ost ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m p b o FS A row fr f spc j n w56 mm X kk v
                      ltac:(lia) G HB HV) as (HB' & HV'); clear HB HV;
          let m2 := fresh "mc" in
          set (m2 := write_to_mem mm (Z_to_bv 64 (o + Z.of_nat kk)) (le1 v)) in HB', HV' |- *; clearbody m2;
          rename HB' into HB; rename HV' into HV
        end
    end.

  (* 0x8710c: the tail. *)
  Lemma c0s_tailF : forall fr f spc j n w56 mc (x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ slots row ++ zeros 12)] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x8710c (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29
                              x30 x31) mc).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 G HB HV.
    destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18
                   & G19 & G20 & G21 & G22 & G23 & G24 & G25 & G26 & G27).
    exact (Htail fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 G1 G2 G3 G4 G5 G6 G7 G8 G9
             G10 G11 G12 G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 HB HV).
  Qed.

  (* The fill loop of the empty slots (3), at 0x870d8. *)
  Lemma c0s_fillF : forall k P (a1w : word) (z2 z3 z4 : Z) fr f spc j n w56 mc
      (x1 x5 x6 x7 a0 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    (length P + k = 12)%nat -> (0 < k)%nat -> P ++ repeat (bz 3) k = slots row ->
    bv_unsigned a1w = 18446744073709551615 - o -> z2 = 3 -> z3 = Z.of_nat (8 + length P) -> z4 = 20 ->
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ P ++ zeros (24 - length P))] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x870d8 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 a1w (Z_to_bv 64 z2)
                              (Z_to_bv 64 z3) (Z_to_bv 64 z4) a5 a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    mbF_open HRNG.
    c0s_clr.
    induction k as [|k IH]; intros P a1w z2 z3 z4 fr f spc j n w56 mc x1 x5 x6 x7 a0 a5 a6 a7 x22 x28 x29 x30 x31
      Hk Hk0 EP H1w E2 E3 E4 G HB HV; [lia|].
    subst z2 z4.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    clear RROW RJ4 RJ3 RNM.
    destruct (ROUT ltac:(destruct G as (_ & _ & Gp & _); lia) ltac:(lia)) as (ROUTr & ROUTc & ROUTs & ROUTk).
    clear ROUT.
    pose proof (c0s_ac ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m p b o FS A row fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= o + z3 < 2^64) by lia.
    pose proof (c0s_chk off Hoff mc o 32 z3 1 (o + z3) HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (o + z3) 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    bstep. step.
    chk_core (o + z3) RX (Z_to_bv 5 16) SH pre_sr no_extra.
    step.
    c0s_vst (8 + length P)%nat.
    step.
    rewrite (rc_eqb_lit (z3 + 1) 20) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 3))) with (bz 3) in HV.
    destruct k as [|k].
    - replace (z3 + 1 =? 20) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step.
      replace (P ++ [bz 3]) with (slots row) in HV by (rewrite <- EP; reflexivity).
      rewrite (rs_slots_len row Hsy) in HV. change (24 - 12)%nat with 12%nat in HV.
      eapply c0s_tailF; [exact G | exact HB | exact HV].
    - replace (z3 + 1 =? 20) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      eapply (IH (P ++ [bz 3]) a1w 3 (z3 + 1) 20); [rewrite length_app; cbn [length]; lia | lia
        | rewrite <- EP, <- app_assoc; reflexivity | exact H1w | reflexivity | rewrite length_app; cbn [length]; lia
        | reflexivity | exact G | exact HB | exact HV].
  Qed.

  (* 0x870b4: both sides join; 12 slots done goes to the tail, else the fill loop. *)
  Lemma c0s_dd8F : forall P (z1 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a0 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    (length P <= 12)%nat -> P ++ repeat (bz 3) (12 - length P) = slots row -> z1 = Z.of_nat (length P) ->
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ P ++ zeros (24 - length P))] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x870b4 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) a2 a3 a4 a5 a6
                              a7 x22 x28 x29 x30 x31) mc).
  Proof.
    mbF_open HRNG. clear RROW ROUT RJ4 RJ3 RNM.
    intros P z1 fr f spc j n w56 mc x1 x5 x6 x7 a0 a2 a3 a4 a5 a6 a7 x22 x28 x29 x30 x31 LP EP E1 G HB HV.
    c0s_clr.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    unfold c0s_at, c0s_R.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    step. step. rewrite mb_lts_lit by lia.
    destruct (Z.ltb_spec 11 z1) as [C|C]; cbv iota.
    - assert (L12 : length P = 12%nat) by lia. rewrite L12 in EP, HV.
      change (12 - 12)%nat with 0%nat in EP. cbn [repeat] in EP. rewrite app_nil_r in EP.
      rewrite EP in HV. change (24 - 12)%nat with 12%nat in HV.
      eapply c0s_tailF; [exact G | exact HB | exact HV].
    - step. step. step. step. step. step.
      rewrite mb_zext32 by lia.
      eapply (c0s_fillF (12 - length P) P); [lia | lia | exact EP | apply c0s_not; lia
        | first [reflexivity | lia] | lia | first [reflexivity | lia] | exact G | exact HB | exact HV].
  Qed.

  (* lay = 1: the input slots (0), at 0x86fe8 (with the 32-bit overflow test of the slot index). *)
  Lemma c0s_l2aF : forall k P (z1 z2 z5 : Z) fr f spc j n w56 mc
      (x1 x5 x6 x7 a0 a3 a4 a6 a7 x22 x28 x29 x30 x31 : word),
    (length P + k <= 12)%nat -> (0 < k)%nat ->
    P ++ repeat (bz 0) k ++ repeat (bz 3) (12 - (length P + k)) = slots row ->
    z1 = Z.of_nat (length P) -> z2 = 2147483640 -> z5 = Z.of_nat k ->
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ P ++ zeros (24 - length P))] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x86fe8 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) (Z_to_bv 64 z2)
                              a3 a4 (Z_to_bv 64 z5) a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    mbF_open HRNG.
    c0s_clr.
    induction k as [|k IH]; intros P z1 z2 z5 fr f spc j n w56 mc x1 x5 x6 x7 a0 a3 a4 a6 a7 x22 x28 x29 x30 x31
      Hk Hk0 EP E1 E2 E5 G HB HV; [lia|].
    subst z2.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    clear RROW RJ4 RJ3 RNM.
    destruct (ROUT ltac:(destruct G as (_ & _ & Gp & _); lia) ltac:(lia)) as (ROUTr & ROUTc & ROUTs & ROUTk).
    clear ROUT.
    pose proof (c0s_ac ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m p b o FS A row fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= z1 + 8 + o < 2^64) by lia.
    pose proof (c0s_chk off Hoff mc o 32 (z1 + 8) 1 (z1 + 8 + o) HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (z1 + 8 + o) 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    bstep.
    step. rewrite mb_addiw by lia.
    step. bstep.
    step. rewrite mb_sltu0 by (rewrite ?unsigned_lit by lia; lia).
    step. rewrite mb_slti0 by lia.
    step. step. bst.
    chk_core (z1 + 8 + o) RX (Z_to_bv 5 14) SH pre_sr no_extra.
    c0s_vst (8 + length P)%nat.
    step. rewrite mb_addiw by lia.
    step. step.
    rewrite (rc_eqb_lit (z5 + -1) 0) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0))) with (bz 0) in HV.
    destruct k as [|k].
    - replace (z5 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step.
      eapply (c0s_dd8F (P ++ [bz 0]) (z1 + 1)); [rewrite length_app; cbn [length]; lia |
        | rewrite length_app; cbn [length]; lia | exact G | exact HB | exact HV].
      rewrite <- EP, <- app_assoc, length_app. reflexivity.
    - replace (z5 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      eapply (IH (P ++ [bz 0]) (z1 + 1) 2147483640 (z5 + -1)); [rewrite length_app; cbn [length]; lia | lia |
        | rewrite length_app; cbn [length]; lia | reflexivity | lia | exact G | exact HB | exact HV].
      rewrite <- EP, <- app_assoc, length_app. cbn [length app repeat].
      replace (length P + 1 + S k)%nat with (length P + S (S k))%nat by lia. reflexivity.
  Qed.

  (* lay <> 1: the output slots (1), at 0x8705c (with the 32-bit overflow test of the slot index). *)
  Lemma c0s_l2bF : forall k P (z1 z2 z3 z4 : Z) fr f spc j n w56 mc
      (x1 x5 x6 x7 a0 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    (length P + k <= 12)%nat -> (0 < k)%nat ->
    P ++ repeat (bz 1) k ++ repeat (bz 3) (12 - (length P + k)) = slots row ->
    z1 = Z.of_nat (length P) -> z2 = 2147483640 -> z3 = 1 -> z4 = Z.of_nat k ->
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ P ++ zeros (24 - length P))] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x8705c (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) (Z_to_bv 64 z2)
                              (Z_to_bv 64 z3) (Z_to_bv 64 z4) a5 a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    mbF_open HRNG.
    c0s_clr.
    induction k as [|k IH]; intros P z1 z2 z3 z4 fr f spc j n w56 mc x1 x5 x6 x7 a0 a5 a6 a7 x22 x28 x29 x30 x31
      Hk Hk0 EP E1 E2 E3 E4 G HB HV; [lia|].
    subst z2 z3.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    clear RROW RJ4 RJ3 RNM.
    destruct (ROUT ltac:(destruct G as (_ & _ & Gp & _); lia) ltac:(lia)) as (ROUTr & ROUTc & ROUTs & ROUTk).
    clear ROUT.
    pose proof (c0s_ac ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m p b o FS A row fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= z1 + 8 + o < 2^64) by lia.
    pose proof (c0s_chk off Hoff mc o 32 (z1 + 8) 1 (z1 + 8 + o) HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound (z1 + 8 + o) 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    step. first [rewrite mb_addiw by lia | rewrite mb_swrap_lit by lia]. rewrite ?Z.add_0_r.
    bstep.
    step. rewrite mb_addiw by lia.
    step. bstep.
    step. rewrite mb_sltu0 by (rewrite ?unsigned_lit by lia; lia).
    step. rewrite mb_slti0 by lia.
    step. step. bst.
    chk_core (z1 + 8 + o) RX (Z_to_bv 5 16) SH pre_sr no_extra.
    c0s_vst (8 + length P)%nat.
    step. rewrite mb_addiw by lia.
    step. step.
    rewrite (rc_eqb_lit (z4 + -1) 0) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (bz 1) in HV.
    destruct k as [|k].
    - replace (z4 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [negb]. cbv iota.
      step.
      eapply (c0s_dd8F (P ++ [bz 1]) (z1 + 1)); [rewrite length_app; cbn [length]; lia |
        | rewrite length_app; cbn [length]; lia | exact G | exact HB | exact HV].
      rewrite <- EP, <- app_assoc, length_app. reflexivity.
    - replace (z4 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb]. cbv iota.
      eapply (IH (P ++ [bz 1]) (z1 + 1) 2147483640 1 (z4 + -1)); [rewrite length_app; cbn [length]; lia | lia |
        | rewrite length_app; cbn [length]; lia | reflexivity | reflexivity | lia | exact G | exact HB | exact HV].
      rewrite <- EP, <- app_assoc, length_app. cbn [length app repeat].
      replace (length P + 1 + S k)%nat with (length P + S (S k))%nat by lia. reflexivity.
  Qed.

  (* lay = 1, after the output slots: 0x86fd4 (0x86fd0 sets a1 = 0 when there is none). *)
  Lemma c0s_ec4F : forall P (z1 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a0 a3 a4 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row = 1 -> P = repeat (bz 1) (Z.to_nat (oc row / 4)) -> z1 = Z.of_nat (length P) ->
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ P ++ zeros (24 - length P))] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x86fd4 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1)
                              (Z_to_bv 64 (ic row)) a3 a4 (Z_to_bv 64 (ic row / 4)) a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    mbF_open HRNG. clear RROW ROUT RJ4 RJ3 RNM.
    intros P z1 fr f spc j n w56 mc x1 x5 x6 x7 a0 a3 a4 a6 a7 x22 x28 x29 x30 x31 L1 EP E1 G HB HV.
    c0s_clr.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    pose proof (rs_ic_range row) as RI.
    assert (LP : length P = Z.to_nat (oc row / 4)) by (rewrite EP, repeat_length; reflexivity).
    assert (ES : slots row = P ++ repeat (bz 0) (Z.to_nat (ic row / 4)) ++
                             repeat (bz 3) (12 - (length P + Z.to_nat (ic row / 4)))).
    { rewrite (rs_slots_1 row L1), LP, <- EP.
      replace (12 - Z.to_nat (ic row / 4) - Z.to_nat (oc row / 4))%nat
        with (12 - (Z.to_nat (oc row / 4) + Z.to_nat (ic row / 4)))%nat by lia. reflexivity. }
    unfold c0s_at, c0s_R.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
    - eapply (c0s_dd8F P z1); [rewrite LP; lia | | exact E1 | exact G | exact HB | exact HV].
      rewrite ES, I0. change (Z.to_nat (0 / 4)) with 0%nat. rewrite Nat.add_0_r. reflexivity.
    - step. step. rewrite rs_seqz by lia. step. step.
      eapply (c0s_l2aF (Z.to_nat (ic row / 4)) P); [lia | lia | symmetry; exact ES | exact E1
        | first [reflexivity | vm_compute; reflexivity | lia] | lia | exact G | exact HB | exact HV].
  Qed.

  (* lay <> 1, after the input slots: 0x87044 (0x87040 sets a1 = 0 when there is none). *)
  Lemma c0s_f34F : forall P (z1 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a0 a2 a5 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row <> 1 -> P = repeat (bz 2) (Z.to_nat (ic row / 4)) -> z1 = Z.of_nat (length P) ->
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ P ++ zeros (24 - length P))] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x87044 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 (Z_to_bv 64 z1) a2
                              (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) a5 a6 a7 x22 x28 x29 x30 x31) mc).
  Proof.
    mbF_open HRNG. clear RROW ROUT RJ4 RJ3 RNM.
    intros P z1 fr f spc j n w56 mc x1 x5 x6 x7 a0 a2 a5 a6 a7 x22 x28 x29 x30 x31 L1 EP E1 G HB HV.
    c0s_clr.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    pose proof (rs_oc_range row) as RO.
    assert (LP : length P = Z.to_nat (ic row / 4)) by (rewrite EP, repeat_length; reflexivity).
    assert (ES : slots row = P ++ repeat (bz 1) (Z.to_nat (oc row / 4)) ++
                             repeat (bz 3) (12 - (length P + Z.to_nat (oc row / 4)))).
    { rewrite (rs_slots_2 row L1), LP, <- EP.
      replace (12 - Z.to_nat (ic row / 4) - Z.to_nat (oc row / 4))%nat
        with (12 - (Z.to_nat (ic row / 4) + Z.to_nat (oc row / 4)))%nat by lia. reflexivity. }
    unfold c0s_at, c0s_R.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
    - eapply (c0s_dd8F P z1); [rewrite LP; lia | | exact E1 | exact G | exact HB | exact HV].
      rewrite ES, O0. change (Z.to_nat (0 / 4)) with 0%nat. rewrite Nat.add_0_r. reflexivity.
    - step. step. step. rewrite rs_seqz by lia. step. step.
      eapply (c0s_l2bF (Z.to_nat (oc row / 4)) P); [lia | lia | symmetry; exact ES | exact E1
        | first [reflexivity | vm_compute; reflexivity | lia] | first [reflexivity | lia] | lia
        | exact G | exact HB | exact HV].
  Qed.

  (* lay = 1: the output slots (1), at 0x868e0. *)
  Lemma c0s_l1aF : forall k P nn (z0 z1 z3 z4 z6 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a7 x22 x28 x29 x30 x31 : word),
    lay row = 1 -> (length P + k = nn)%nat -> nn = Z.to_nat (oc row / 4) -> (0 < k)%nat -> P = repeat (bz 1) (length P) ->
    z0 = o + Z.of_nat (8 + length P) -> z3 = o + Z.of_nat (8 + length P) -> z1 = Z.of_nat nn -> z4 = 1 ->
    z6 = Z.of_nat k ->
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ P ++ zeros (24 - length P))] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x868e0 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 (Z_to_bv 64 z0) (Z_to_bv 64 z1)
                              (Z_to_bv 64 (ic row)) (Z_to_bv 64 z3) (Z_to_bv 64 z4) (Z_to_bv 64 (ic row / 4))
                              (Z_to_bv 64 z6) a7 x22 x28 x29 x30 x31) mc).
  Proof.
    mbF_open HRNG.
    c0s_clr.
    induction k as [|k IH]; intros P nn z0 z1 z3 z4 z6 fr f spc j n w56 mc x1 x5 x6 x7 a7 x22 x28 x29 x30 x31
      L1 Hn En Hk EP E0 E3 E1 E4 E6 G HB HV; [lia|].
    subst z4.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    clear RROW RJ4 RJ3 RNM.
    destruct (ROUT ltac:(destruct G as (_ & _ & Gp & _); lia) ltac:(lia)) as (ROUTr & ROUTc & ROUTs & ROUTk).
    clear ROUT.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    assert (LP : (length P < 12)%nat) by lia.
    pose proof (c0s_ac ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m p b o FS A row fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= z0 < 2^64) by lia.
    pose proof (c0s_chk off Hoff mc o 32 (Z.of_nat (8 + length P)) 1 z0 HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound z0 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    bstep. bstep.
    chk_core z0 RX (Z_to_bv 5 5) SH pre_sr no_extra.
    c0s_vst (8 + length P)%nat.
    step. step. step. step.
    rewrite (rc_eqb_lit (z6 + -1) 0) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1))) with (bz 1) in HV.
    assert (EP' : P ++ [bz 1] = repeat (bz 1) (length (P ++ [bz 1])))
      by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r, <- mb_rep_snoc, <- EP; reflexivity).
    destruct k as [|k].
    - replace (z6 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      eapply (c0s_ec4F (P ++ [bz 1])); [exact L1 | rewrite EP'; f_equal; rewrite length_app; cbn [length]; lia
        | rewrite length_app; cbn [length]; lia | exact G | exact HB | exact HV].
    - replace (z6 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      eapply (IH (P ++ [bz 1]) nn (z0 + 1) z1 (z3 + 1) 1 (z6 + -1)); [exact L1 | rewrite length_app; cbn [length]; lia
        | exact En | lia | exact EP' | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
        | exact E1 | reflexivity | lia | exact G | exact HB | exact HV].
  Qed.

  (* lay <> 1: the input slots (2), at 0x86f94. *)
  Lemma c0s_l1bF : forall k P nn (z0 z1 z2 z5 z6 : Z) fr f spc j n w56 mc (x1 x5 x6 x7 a7 x22 x28 x29 x30 x31 : word),
    lay row <> 1 -> (length P + k = nn)%nat -> nn = Z.to_nat (ic row / 4) -> (0 < k)%nat -> P = repeat (bz 2) (length P) ->
    z0 = o + Z.of_nat (8 + length P) -> z2 = o + Z.of_nat (8 + length P) -> z1 = Z.of_nat nn -> z5 = 2 ->
    z6 = Z.of_nat k ->
    c0s_G sp m p b o FS A row fr f spc j n w56 -> c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ P ++ zeros (24 - length P))] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x86f94 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 (Z_to_bv 64 z0) (Z_to_bv 64 z1)
                              (Z_to_bv 64 z2) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 z5)
                              (Z_to_bv 64 z6) a7 x22 x28 x29 x30 x31) mc).
  Proof.
    mbF_open HRNG.
    c0s_clr.
    induction k as [|k IH]; intros P nn z0 z1 z2 z5 z6 fr f spc j n w56 mc x1 x5 x6 x7 a7 x22 x28 x29 x30 x31
      L1 Hn En Hk EP E0 E2 E1 E5 E6 G HB HV; [lia|].
    subst z5.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    clear RROW RJ4 RJ3 RNM.
    destruct (ROUT ltac:(destruct G as (_ & _ & Gp & _); lia) ltac:(lia)) as (ROUTr & ROUTc & ROUTs & ROUTk).
    clear ROUT.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    assert (LP : (length P < 12)%nat) by lia.
    pose proof (c0s_ac ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m p b o FS A row fr f spc j n w56 mc G HB) as HAc.
    assert (RX : 0 <= z0 < 2^64) by lia.
    pose proof (c0s_chk off Hoff mc o 32 (Z.of_nat (8 + length P)) 1 z0 HAc ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(pose proof (Z.mod_pos_bound z0 8 ltac:(lia)); lia) ltac:(lia)) as SH.
    unfold c0s_at, c0s_R.
    bstep. bstep.
    chk_core z0 RX (Z_to_bv 5 5) SH pre_sr no_extra.
    c0s_vst (8 + length P)%nat.
    step. step. step. step.
    rewrite (rc_eqb_lit (z6 + -1) 0) by lia.
    rewrite mb_fill_step in HV by first [reflexivity | lia].
    change (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 2))) with (bz 2) in HV.
    assert (EP' : P ++ [bz 2] = repeat (bz 2) (length (P ++ [bz 2])))
      by (rewrite length_app; cbn [length]; rewrite Nat.add_1_r, <- mb_rep_snoc, <- EP; reflexivity).
    destruct k as [|k].
    - replace (z6 + -1 =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      eapply (c0s_f34F (P ++ [bz 2])); [exact L1 | rewrite EP'; f_equal; rewrite length_app; cbn [length]; lia
        | rewrite length_app; cbn [length]; lia | exact G | exact HB | exact HV].
    - replace (z6 + -1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      step.
      eapply (IH (P ++ [bz 2]) nn (z0 + 1) z1 (z2 + 1) 2 (z6 + -1)); [exact L1 | rewrite length_app; cbn [length]; lia
        | exact En | lia | exact EP' | rewrite length_app; cbn [length]; lia | rewrite length_app; cbn [length]; lia
        | exact E1 | reflexivity | lia | exact G | exact HB | exact HV].
  Qed.

  (* 0x868c4, lay = 1. *)
  Lemma c0s_s1F : forall fr f spc j n w56 mc (x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row = 1 -> c0s_G sp m p b o FS A row fr f spc j n w56 ->
    c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ zeros 24)] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x868c4 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 a1 (Z_to_bv 64 (ic row))
                              (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7 x22 x28
                              x29 x30 x31) mc).
  Proof.
    mbF_open HRNG. clear RROW ROUT RJ4 RJ3 RNM.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1 G HB HV.
    c0s_clr.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    pose proof (rs_oc_range row) as RO.
    unfold c0s_at, c0s_R.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (oc row) 0) as [O0|O0]; cbv iota.
    - step.
      eapply (c0s_ec4F []); [exact L1 | rewrite O0; reflexivity | first [reflexivity | lia] | exact G | exact HB
        | exact HV].
    - step. step. rewrite rs_seqz by lia. step. step. step. step.
      eapply (c0s_l1aF (Z.to_nat (oc row / 4)) [] (Z.to_nat (oc row / 4))); [exact L1 | cbn [length]; lia | reflexivity
        | lia | reflexivity | cbn [length]; lia | cbn [length]; lia | lia | first [reflexivity | lia] | lia
        | exact G | exact HB | exact HV].
  Qed.

  (* 0x86f78, lay <> 1. *)
  Lemma c0s_s2F : forall fr f spc j n w56 mc (x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row <> 1 -> c0s_G sp m p b o FS A row fr f spc j n w56 ->
    c0s_K ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m o FS fr j n w56 mc ->
    rw_cells rsegs mc o [CB 32 (c0s_H8 row ++ zeros 24)] ->
    evtF rsegs RNG (c0s_Q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (c0s_at F fc 0x86f78 (c0s_R sp gp tp s10 s11 p o off A fr spc f x1 x5 x6 x7 a0 a1 (Z_to_bv 64 (ic row))
                              (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7 x22 x28
                              x29 x30 x31) mc).
  Proof.
    mbF_open HRNG. clear RROW ROUT RJ4 RJ3 RNM.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1 G HB HV.
    c0s_clr.
    destruct (c0s_go sp m p b o FS A row fr f spc j n w56 G) as (Go0 & Goe & Hsy). unfold APPMEM_END in Goe.
    pose proof (proj1 (mb_synok_iff row) Hsy) as (Ri & Ro0 & Mi & Mo & Sum).
    pose proof (rs_ic_range row) as RI.
    unfold c0s_at, c0s_R.
    step. rewrite rc_eqb_lit by lia.
    destruct (Z.eqb_spec (ic row) 0) as [I0|I0]; cbv iota.
    - step.
      eapply (c0s_f34F []); [exact L1 | rewrite I0; reflexivity | first [reflexivity | lia] | exact G | exact HB
        | exact HV].
    - step. step. rewrite rs_seqz by lia. step. step. step. step.
      eapply (c0s_l1bF (Z.to_nat (ic row / 4)) [] (Z.to_nat (ic row / 4))); [exact L1 | cbn [length]; lia | reflexivity
        | lia | reflexivity | cbn [length]; lia | cbn [length]; lia | lia | first [reflexivity | lia] | lia
        | exact G | exact HB | exact HV].
  Qed.

  (* Statement (2b) of the pin, verbatim, as an evtF run. *)
  Lemma c0s_lay1F :
  forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
         (x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row = 1 ->
      b = 0 -> synok row = true ->
      0 < p -> p mod 8 = 0 -> length row = 296%nat -> p + 296 <= APPMEM_END ->
      0 < o -> o + 32 <= APPMEM_END ->
      (p + 296 <= o \/ o + 32 <= p) ->
      (FS + 8 <= o \/ o + 32 <= FS) ->
      (fr + 64 <= o \/ o + 32 <= fr) ->
      (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) ->
      (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) ->
      (forall i, 0 <= i <= 32 -> app_mem (o + i)) ->
      FS + 8 <= bv_unsigned sp - 4272 ->
      bv_unsigned sp - 240 <= spc -> spc <= bv_unsigned sp - 160 ->
      (fr + 64 <= spc - 2224 \/ spc <= fr + 56) ->
      (o + 32 <= RT_LO \/ RT_HI <= o) ->
      addressable m p 296 -> addressable m o 32 -> bytes_at rsegs m p row ->
      (forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      (forall i, 0 <= i < 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (p + i))) ->
      (forall i, 0 <= i < 32 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (o + i))) ->
      (forall x, RT_LO <= x < RT_HI -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      FK FS A fr f spc j n w56 ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 ([bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row] ++ zeros 24)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1
               (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x868c4) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12
      G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 HB HV.
    exact (c0s_s1F fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1
             (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj G9 (conj G10 (conj G11 (conj G12 (conj G13 (conj G14 (conj G15 (conj G16 (conj G17 (conj G18 (conj G19 (conj G20 (conj G21 (conj G22 (conj G23 (conj G24 (conj G25 (conj G26 G27))))))))))))))))))))))))))
             HB HV).
  Qed.

  (* Statement (2c) of the pin, verbatim, as an evtF run. *)
  Lemma c0s_lay2F :
  forall (fr f spc j n : Z) (w56 : word) (mc : word -> option byte)
         (x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 : word),
    lay row <> 1 ->
      b = 0 -> synok row = true ->
      0 < p -> p mod 8 = 0 -> length row = 296%nat -> p + 296 <= APPMEM_END ->
      0 < o -> o + 32 <= APPMEM_END ->
      (p + 296 <= o \/ o + 32 <= p) ->
      (FS + 8 <= o \/ o + 32 <= FS) ->
      (fr + 64 <= o \/ o + 32 <= fr) ->
      (bv_unsigned sp <= o \/ o + 32 <= bv_unsigned sp - 4272) ->
      (bv_unsigned sp <= p \/ p + 296 <= bv_unsigned sp - 4272) ->
      (forall i, 0 <= i <= 32 -> app_mem (o + i)) ->
      FS + 8 <= bv_unsigned sp - 4272 ->
      bv_unsigned sp - 240 <= spc -> spc <= bv_unsigned sp - 160 ->
      (fr + 64 <= spc - 2224 \/ spc <= fr + 56) ->
      (o + 32 <= RT_LO \/ RT_HI <= o) ->
      addressable m p 296 -> addressable m o 32 -> bytes_at rsegs m p row ->
      (forall x, p <= x < p + 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      (forall i, 0 <= i < 296 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (p + i))) ->
      (forall i, 0 <= i < 32 -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) (shadow_addr (o + i))) ->
      (forall x, RT_LO <= x < RT_HI -> outside (Wf sp FS fr j n ++ [(o, o + 32)]) x) ->
      FK FS A fr f spc j n w56 ->
      BI ra sp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 m FS (Wf sp FS fr j n ++ [(o, o + 32)]) fr w56 mc ->
    rw_cells rsegs mc o [CB 32 ([bz 1; bz 3; bz 0; bz 16; sel row; bz 0; bz 0; strap row] ++ zeros 24)] ->
    evtF rsegs RNG (Q0 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m p b o FS row nb)
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 sp (Z_to_bv 64 A) a0 a1
               (Z_to_bv 64 (ic row)) (Z_to_bv 64 (oc row)) (Z_to_bv 64 (oc row / 4)) (Z_to_bv 64 (ic row / 4)) a6 a7
               (Z_to_bv 64 f) (Z_to_bv 64 o) (Z_to_bv 64 p) (Z_to_bv 64 (-1)) x22 (Z_to_bv 64 fr)
               (Z_to_bv 64 (fr / 8 + off)) (Z_to_bv 64 off) s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x86f78) fc None mc (seg_rom rsegs)).
  Proof.
    intros fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1 G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11 G12
      G13 G14 G15 G16 G17 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 HB HV.
    exact (c0s_s2F fr f spc j n w56 mc x1 x5 x6 x7 a0 a1 a6 a7 x22 x28 x29 x30 x31 L1
             (conj G1 (conj G2 (conj G3 (conj G4 (conj G5 (conj G6 (conj G7 (conj G8 (conj G9 (conj G10 (conj G11 (conj G12 (conj G13 (conj G14 (conj G15 (conj G16 (conj G17 (conj G18 (conj G19 (conj G20 (conj G21 (conj G22 (conj G23 (conj G24 (conj G25 (conj G26 G27))))))))))))))))))))))))))
             HB HV).
  Qed.
End Body.
