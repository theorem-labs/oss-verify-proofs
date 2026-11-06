(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA RA_sp5c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.
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

Definition strlen_icpt_entry : Z := 0x479fc.
Definition STRLEN_ICPT_STACK : Z := 2224.

(* [comment removed for export] *)
Definition strlen_icpt_cells (m : word -> option byte) : Prop :=
     asan_inited_cell m                                          (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaaec8 [C8 (Z_to_bv 64 0xa28fc)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xa9180 [C8 (Z_to_bv 64 0x146ee8)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0x146fe3 [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ map_cells m.

Definition strlen_icpt_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 : word) (str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - STRLEN_ICPT_STACK, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack).

Section Proofs.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (str slack : list byte) (lo : Z).
  Notation A := (bv_unsigned a0).
  Notation n := (Z.of_nat (length str)).
  Notation POST := (strlen_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m).

  (* [comment removed for export] *)
  Lemma sl_exit : forall m1 junk x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x28 x29 x30 x31,
    mem_inv rsegs m1 -> munch [(bv_unsigned sp - STRLEN_ICPT_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2144) ->
    rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 2080 junk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    bytes_at rsegs m1 A (str ++ Z_to_bv 8 0 :: slack) ->
    (lo <= bv_unsigned sp - STRLEN_ICPT_STACK)%Z ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp x5 x6 x7 sp x9
               (Z_to_bv 64 n) x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x47b48) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros MI1 MU1 WM1 ST1 FR1 STR1 LOLE. unfold STRLEN_ICPT_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    do 11 zstep.
    release_frame FR1 ST1 (bv_unsigned sp). finish.
  Qed.

  Section Slow.
    Variables (m1 : word -> option byte) (junk : list byte) (ng : nat) (lastb sf sl : Z) (x1 x15 x16 s6' : word).
    Hypothesis MI1 : mem_inv rsegs m1.
    Hypothesis MU1 : munch [(bv_unsigned sp - STRLEN_ICPT_STACK, bv_unsigned sp)]%Z m m1.
    Hypothesis WM1 : wmono rsegs m m1.
    Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2144).
    Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -2144) [CB 2080 junk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis STR1 : bytes_at rsegs m1 A (str ++ Z_to_bv 8 0 :: slack).
    Hypothesis LOLE : (lo <= bv_unsigned sp - STRLEN_ICPT_STACK)%Z.
    Hypothesis SH1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
    Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
    Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.

    Notation AT pc x10 x11 x13 x14 :=
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 sp (Z_to_bv 64 (n + 1))
               x10 x11 (Z_to_bv 64 sl) x13 x14 x15 x16 a7 a0 (Z_to_bv 64 1339112) (Z_to_bv 64 (bv_unsigned sp + -2136))
               (Z_to_bv 64 n) s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

    (* [comment removed for export] *)
    #[using="LOLE STR1 FR1 ST1 WM1 MU1 MI1 junk Clg"] Lemma sl_tail : forall x11 x13 x14, evt rsegs POST (AT 0x47c50 (Z_to_bv 64 0) x11 x13 x14).
    Proof.
      intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. unfold STRLEN_ICPT_STACK in *.
      zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
      zstep. zstep. eapply sl_exit; try eassumption; try (unfold STRLEN_ICPT_STACK; lia).
    Qed.

    (* [comment removed for export] *)
    #[using="ESL ESF SH1 LOLE STR1 FR1 ST1 WM1 MU1 MI1 lastb junk Clg"] Lemma sl_loop : forall (c : nat) (j : Z) x11 x13 x14,
      Z.to_nat (Z.of_nat ng - j) = c -> (0 <= j < Z.of_nat ng)%Z -> x11 = Z_to_bv 64 (sf + j) ->
      evt rsegs POST (AT 0x47c40 (Z_to_bv 64 0) x11 x13 x14).
    Proof.
      induction c as [|c IH]; intros j x11 x13 x14 Hc Hj ->; [lia|].
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
      - apply sl_tail.
    Qed.
  End Slow.
End Proofs.

(* [comment removed for export] *)
Lemma a0_frame_join : forall m A B cs1 cs2,
  rw_cells rsegs m A cs1 -> rw_cells rsegs m B cs2 -> B = (A + Z.of_nat (cells_size cs1))%Z -> rw_cells rsegs m A (cs1 ++ cs2).
Proof.
  intros m A B cs1 cs2 [[W1 B1] R1] [[W2 B2] R2] ->. split; [split|].
  - apply cells_wf_app. tauto.
  - rewrite cells_bytes_app. apply bytes_at_app. rewrite (cells_bytes_length cs1 W1). tauto.
  - rewrite cells_size_app, Nat2Z.inj_add. destruct R1 as (R10 & R11 & R12), R2 as (R20 & R21 & R22).
    split; [lia|]. split; [lia|]. intros i Hi.
    destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))); [apply R12; lia|].
    replace (A + i)%Z with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1)))%Z by lia. apply R22. lia.
Qed.
Ltac a0_join :=
  match goal with
  | F0 : rw_cells _ ?m ?A [CB 2080 ?j], F1 : rw_cells _ ?m ?B (C8 _ :: _) |- _ =>
      let FRJ := fresh "FRJ" in
      pose proof (a0_frame_join m A B _ _ F0 F1 ltac:(cbn [cells_size csize Nat.add]; lia)) as FRJ; cbn [app] in FRJ; clear F0 F1
  end.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma strlen_icpt_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack : list byte) (lo : Z),
  let A := bv_unsigned a0 in let n := Z.of_nat (length str) in
  bytes_at rsegs m A (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (A + n + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  mem_inv rsegs m ->
  strlen_icpt_cells m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo + STRLEN_ICPT_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + Z.of_nat (length (str ++ Z_to_bv 8 0 :: slack)) <= bv_unsigned sp - STRLEN_ICPT_STACK)%Z ->
  (n + 1 <= 2^32)%Z ->
  inmem_range A (n + 1) ->
  shadow_ok m A (n + 1) ->
  mapped8 m (sha A - sha A mod 8) -> mapped8 m (sha (A + n) - sha (A + n) mod 8) ->
  evt rsegs (strlen_icpt_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x479fc) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros STR NONUL PAD MI CELLS ST LOLE CEIL SEP N32 IR SOK QW1 QW2.
  unfold STRLEN_ICPT_STACK in *.
  destruct CELLS as (CI & Creal & Gcf & Ccf & MC). pose proof MC as MC'. open_map_cells MC'.
  pose proof (munch_refl [(bv_unsigned sp - 2224, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (bytes_at_bound _ _ _ _ STR) as AB. rewrite length_app in AB, SEP. cbn [length] in AB, SEP.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + Z.of_nat (length str) + 1 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  (* [comment removed for export] *)
  destruct (mapped8_le8 m _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
  destruct (mapped8_le8 m _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
  assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  assert (QH2 : (sha (bv_unsigned a0 + Z.of_nat (length str)) - sha (bv_unsigned a0 + Z.of_nat (length str)) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  destruct SOK as (ng & lastb & NG & SH & LB).
  remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
  assert (SHhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
  { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  unfold asan_inited_cell in CI.
  zstep. (* [comment removed for export] *)
  carve_frame 64%nat ST. carve_frame 2080%nat ST.
  do 12 zstep.
  zstep. call asan_inited_spec. 1:{ exact CI. } 1:{ exact MI. }
  zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. cbv in K0. lia. }
  zstep. call_lit tryinit_spec by (idtac;
    lazymatch goal with
    | |- asan_inited_cell _ => exact CI
    | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
    | |- mem_inv _ _ => eassumption
    | |- _ => rewrite ?unsigned_lit by lia; lia
    end).
  rename POST into ST.
  do 4 zstep.
  zstep. call strlen_spec. 1:{ exact STR. } 1:{ exact NONUL. } 1:{ exact PAD. } 1:{ eassumption. }
  zstep. if_cases K1; zify_cond K1. { exfalso. try (generalize alloc_ceiling_val); clear -K1; try pose proof alloc_ceiling_val. cbv in K1. lia. }
  do 2 zstep.
  zstep. cbv beta.
  zstep. if_cases K2; zify_cond K2. { exfalso. try (generalize alloc_ceiling_val); clear -K2; try pose proof alloc_ceiling_val. cbv in K2. lia. }
  do 4 zstep.
  rewrite zb_lxor_ones by lia.
  zstep. if_cases K3; zify_cond K3. { exfalso. lia. }
  zstep. zstep. if_cases K4; zify_cond K4.
  - (* [comment removed for export] *)
    zstep. zstep. if_cases K5; zify_cond K5. 2:{ exfalso. lia. }
    zstep. zstep. zstep.
    call_lit region_is_poisoned_spec by (idtac;
      lazymatch goal with
      | |- map_cells _ => repeat (split; [assumption|]); assumption
      | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
      | |- mem_inv _ _ => eassumption
      | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IR
      | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ng, lastb; subst sbs; split; [exact NG| split; [exact SH| exact LB]]
      | |- _ => rewrite ?unsigned_lit by lia; lia
      end).
    zstep. if_cases K6; zify_cond K6. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K6; try pose proof alloc_ceiling_val. cbv in K6. lia. }
    zstep. zstep.
    a0_join. eapply sl_exit; try eassumption. unfold STRLEN_ICPT_STACK; lia.
  - (* [comment removed for export] *)
    assert (HS1 : (0 <= Z.shiftr (bv_unsigned a0) 3 <= bv_unsigned a0)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
    assert (HS2 : (0 <= Z.shiftr (Z.of_nat (length str) + bv_unsigned a0) 3 <= Z.of_nat (length str) + bv_unsigned a0)%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; mlia).
    replace (bv_unsigned a0 + Z.of_nat (length str))%Z with (Z.of_nat (length str) + bv_unsigned a0)%Z in QB2, QH2 by lia.
    do 2 zstep.
    do 7 zstep.
    pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
    pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
    zstep. zstep. zstep. zstep.
    zstep. if_cases K7; zify_cond K7.
    + (* [comment removed for export] *)
      subst sbs.
      assert (LBR : (0 <= lastb < 128)%Z) by lia.
      pose proof (u8ro_read rsegs _ (bv_unsigned a0 / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                    (Z_to_bv 64 (2147450880 + Z.shiftr (Z.of_nat (length str) + bv_unsigned a0) 3)) SH) as RD.
      specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                     ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
      zstep. zstep. rewrite sxb_small by lia.
      zstep. zstep. zstep. zstep. zstep.
      rewrite (poisoned_last_zero (Z.of_nat (length str) + bv_unsigned a0) lastb) by
        (first [lia | destruct LB as [LB0|LB1]; [left; exact LB0| right;
           replace (Z.of_nat (length str) + bv_unsigned a0)%Z with (bv_unsigned a0 + (Z.of_nat (length str) + 1) - 1)%Z by lia; lia]]).
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
      set (sf := (2147450880 + bv_unsigned a0 / 8)%Z). set (sl := (2147450880 + (Z.of_nat (length str) + bv_unsigned a0) / 8)%Z).
      assert (ESF : (sf = bv_unsigned a0 / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
      assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
      assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
      { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
      clearbody sf sl.
      zstep. if_cases K8; zify_cond K8.
      * a0_join. eapply sl_tail; eassumption || (unfold STRLEN_ICPT_STACK; lia).
      * a0_join. eapply (sl_loop _ _ _ _ _ _ _ _ _ a0) with (j := 0%Z); try eassumption; try reflexivity; try (unfold STRLEN_ICPT_STACK; lia).
        f_equal; lia.
    + (* [comment removed for export] *)
      a0_join. eapply sl_exit; try eassumption. unfold STRLEN_ICPT_STACK; lia.
Qed.

End CEIL.
