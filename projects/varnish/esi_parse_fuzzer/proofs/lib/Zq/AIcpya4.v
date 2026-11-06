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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq Require AIcpghc.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpjcb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zq.AIcpghc.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= hot_kdrop; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet.diet_transport_after_call segs m m' MU WM.
(* [comment removed for export] *)
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
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@DB; @A0R; @LOLE; @SEP; @HB; @dHa; @dHl; @A2R; @Hc; @CEIL; @Hj; @SB; @CV; @ESL; @N0; @HS2; @H; @ESF; @NW; @K3; @AF; @SFB; @SPR; @LBR; @K; @Hi; @IR; @K0; @K1; @R10; @R21; @N32; @K4; @HS1; @LB; @LB1; @SHhi; @K8])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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

Definition asan_memset_entry : Z := 0x57998.
Definition ASAN_MEMSET_STACK : Z := 2208.

(* [comment removed for export] *)
Definition asan_memset_cells (m : word -> option byte) : Prop :=
     ro_cells rsegs m 0xa96e0 [C8 (Z_to_bv 64 0xb5899)]      (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xb5899 [C1 (Z_to_bv 8 1)]              (* [comment removed for export] *)
  /\ ro_cells rsegs m 0xaaa18 [C8 (Z_to_bv 64 0xa1f90)]      (* [comment removed for export] *)
  /\ map_cells m.

Definition asan_memset_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - ASAN_MEMSET_STACK, bv_unsigned sp)]%Z m m'
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
  Notation POST := (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m).
  Hypothesis LOLE : (lo + ASAN_MEMSET_STACK <= bv_unsigned sp)%Z.
  Hypothesis CEIL : (alloc_ceiling <= lo)%Z.
  (* [comment removed for export] *)
  Notation SEPt := ((A + N <= lo \/ bv_unsigned sp <= A)%Z) (only parsing).

  (* [comment removed for export] *)
  #[using="LOLE"] Lemma am_tail : forall m1 fjunk x1 x5 x6 x7 x9 x13 x14 x15 x16 x17 x18 x19 x21 x28 x29 x30 x31,
    SEPt -> mem_inv rsegs m1 ->
    munch [(A, A + N); (bv_unsigned sp - ASAN_MEMSET_STACK, bv_unsigned sp)]%Z m m1 -> wmono rsegs m m1 ->
    stk rsegs m1 lo (bv_unsigned sp + -2128) ->
    rw_cells rsegs m1 (bv_unsigned sp + -2128) [CB 2072 fjunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    rw_cells rsegs m1 A [CB (Z.to_nat N) junk] ->
    ro_cells rsegs m1 0xaaa18 [C8 (Z_to_bv 64 0xa1f90)] ->
    evt rsegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x5 x6 x7 sp x9
               a0 a1 a2 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 (bv_unsigned sp + -2128)) x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x57a28) fc None m1 (seg_rom rsegs)).
  Proof.
    intros until x31. intros SEP MI1 MU1 WM1 ST1 FR1 DST1 Creal1. unfold ASAN_MEMSET_STACK in *.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof (zr_word a0) as A0R; unfold inr64 in A0R.
    pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
    zstep. zstep.
    zstep. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Creal1); call memset_spec. 1:{ exact DST1. } 1:{ exact MI1. }
    do 10 zstep.
    release_frame FR1 ST1 (bv_unsigned sp). finish.
  Qed.

  Section Slow.
    Variables (m1 : word -> option byte) (fjunk : list byte) (ng : nat) (lastb sf sl : Z) (x17 : word).
    Hypothesis SEP : SEPt.
    Hypothesis MI1 : mem_inv rsegs m1.
    Hypothesis MU1 : munch [(A, A + N); (bv_unsigned sp - ASAN_MEMSET_STACK, bv_unsigned sp)]%Z m m1.
    Hypothesis WM1 : wmono rsegs m m1.
    Hypothesis ST1 : stk rsegs m1 lo (bv_unsigned sp + -2128).
    Hypothesis FR1 : rw_cells rsegs m1 (bv_unsigned sp + -2128) [CB 2072 fjunk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Hypothesis DST1 : rw_cells rsegs m1 A [CB (Z.to_nat N) junk].
    Hypothesis Creal1 : ro_cells rsegs m1 0xaaa18 [C8 (Z_to_bv 64 0xa1f90)].
    Hypothesis SH1 : bytes_at rsegs m1 (A / 8 + shadow_off) (zeros ng ++ [Z_to_bv 8 lastb]).
    Hypothesis ESF : (sf = A / 8 + shadow_off)%Z.
    Hypothesis ESL : (sl = sf + Z.of_nat ng)%Z.

    Notation AT pc x13 x15 x16 :=
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1
               a0 a1 a2 x13 (Z_to_bv 64 sl) x15 x16 x17 s2 s3 (Z_to_bv 64 (bv_unsigned sp + -2128)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 pc) fc None m1 (seg_rom rsegs)) (only parsing).

    (* [comment removed for export] *)
    #[using="Creal1 DST1 FR1 ST1 WM1 MU1 MI1 SEP fjunk LOLE junk Clg"] Lemma am_slow_end : forall x13 x16, evt rsegs POST (AT 0x57b64 x13 (Z_to_bv 64 0) x16).
    Proof.
      intros. pose proof (zr_word sp) as SPR; unfold inr64 in SPR. unfold ASAN_MEMSET_STACK in *.
      zstep. zstep. if_cases K; zify_cond K. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K; try pose proof alloc_ceiling_val. cbv in K. lia. }
      eapply am_tail; try eassumption.
    Qed.

    (* [comment removed for export] *)
    #[using="ESL ESF SH1 Creal1 DST1 FR1 ST1 WM1 MU1 MI1 SEP lastb fjunk LOLE junk Clg"] Lemma am_slow_loop : forall (c : nat) (j : Z) x13 x16,
      Z.to_nat (Z.of_nat ng - j) = c -> (0 <= j < Z.of_nat ng)%Z -> x13 = Z_to_bv 64 (sf + j) ->
      evt rsegs POST (AT 0x57b54 x13 (Z_to_bv 64 0) x16).
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
      - apply am_slow_end.
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
  | F0 : rw_cells _ ?m ?A [CB 2072 ?j], F1 : rw_cells _ ?m ?B (C8 _ :: _) |- _ =>
      let FRJ := fresh "FRJ" in
      pose proof (a0_frame_join m A B _ _ F0 F1 ltac:(cbn [cells_size csize Nat.add]; lia)) as FRJ; cbn [app] in FRJ; clear F0 F1
  end.

Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma asan_memset_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (junk : list byte) (lo : Z),
  let A := bv_unsigned a0 in let N := bv_unsigned a2 in
  rw_cells rsegs m A [CB (Z.to_nat N) junk] ->
  mem_inv rsegs m ->
  asan_memset_cells m ->
  stk rsegs m lo (bv_unsigned sp) ->
  (lo + ASAN_MEMSET_STACK <= bv_unsigned sp)%Z -> (alloc_ceiling <= lo)%Z ->
  (A + N <= lo \/ bv_unsigned sp <= A)%Z ->
  (N < 2^32)%Z ->
  (N = 0%Z \/ range_ok m A N) ->
  evt rsegs (asan_memset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x57998) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. cbv zeta. intros DST MI CELLS ST LOLE CEIL SEP N32 RNG.
  pose proof LOLE as LOLE'. unfold ASAN_MEMSET_STACK in LOLE.
  destruct CELLS as (Gric & Cric & Creal & MC). pose proof MC as MC'. open_map_cells MC'.
  pose proof (munch_refl [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - ASAN_MEMSET_STACK, bv_unsigned sp)]%Z m) as MU.
  unfold ASAN_MEMSET_STACK in MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof alloc_ceiling_val as CV. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  pose proof (zr_word a0) as A0R; unfold inr64 in A0R. pose proof (zr_word a2) as A2R; unfold inr64 in A2R.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  assert (LO0 : (0 <= lo)%Z) by (destruct ST as [? _]; assumption).
  assert (NW : (bv_unsigned a0 + bv_unsigned a2 < 2^64)%Z).
  { destruct RNG as [N0|(IR & _)]; [rewrite N0; lia| unfold inmem_range in IR; lia]. }
  destruct RNG as [N0 | (IR & SOK & QW1 & QW2)].
  { (* [comment removed for export] *)
    carve_frame 56%nat ST. carve_frame 2072%nat ST.
    do 10 zstep.
    do 2 zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
    zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. lia. }
    do 3 zstep. rewrite zb_lxor_ones by lia.
    zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
    zstep. zstep.
    zstep. if_cases K2; zify_cond K2. 2:{ exfalso. rewrite N0 in K2. clear -K2; try pose proof alloc_ceiling_val. cbv in K2. first [lia | discriminate]. }
    zstep. if_cases K3; zify_cond K3. { exfalso. lia. }
    zstep. a0_join. eapply am_tail; try eassumption. }
  (* [comment removed for export] *)
  assert (AF : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + bv_unsigned a2 + 8 <= 0x800000000000)%Z) by (unfold inmem_range in IR; lia).
  destruct (mapped8_le8 m _ QW1 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w1 QB1].
  destruct (mapped8_le8 m _ QW2 ltac:(unfold sha, shadow_off; mlia) ltac:(unfold sha, shadow_off; mlia)) as [w2 QB2].
  assert (QH1 : (sha (bv_unsigned a0) - sha (bv_unsigned a0) mod 8 + Z.of_nat (length (le8 w1)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  replace (bv_unsigned a0 + bv_unsigned a2 - 1)%Z with (bv_unsigned a0 + bv_unsigned a2 + -1)%Z in QB2 by lia.
  assert (QH2 : (sha (bv_unsigned a0 + bv_unsigned a2 + -1) - sha (bv_unsigned a0 + bv_unsigned a2 + -1) mod 8 + Z.of_nat (length (le8 w2)) <= 0x100080000000)%Z) by (rewrite length_le8; unfold sha, shadow_off; mlia).
  pose proof SOK as SOK0. destruct SOK as (ng & lastb & NG & SH & LB).
  remember (zeros ng ++ [Z_to_bv 8 lastb]) as sbs eqn:Esbs.
  assert (SHhi : (bv_unsigned a0 / 8 + shadow_off + Z.of_nat (length sbs) <= 0x100080000000)%Z).
  { subst sbs. rewrite length_app, zeros_length. cbn [length]. unfold shadow_off. mlia. }
  carve_frame 56%nat ST. carve_frame 2072%nat ST.
  do 10 zstep.
  do 2 zstep. zstep. cbv beta. change (bv_unsigned (Z_to_bv 8 1)) with 1%Z.
  zstep. if_cases K0; zify_cond K0. { exfalso. try (generalize alloc_ceiling_val); clear -K0; try pose proof alloc_ceiling_val. lia. }
  do 3 zstep. rewrite zb_lxor_ones by lia.
  zstep. if_cases K1; zify_cond K1. { exfalso. lia. }
  zstep. zstep.
  zstep. if_cases K2; zify_cond K2.
  - (* [comment removed for export] *)
    zstep. if_cases K3; zify_cond K3.
    + (* [comment removed for export] *)
      do 4 zstep.
      zstep. call_lit region_is_poisoned_spec by (idtac;
        lazymatch goal with
        | |- map_cells _ => repeat (split; [assumption|]); assumption
        | |- stk _ _ _ _ => rewrite ?unsigned_lit by lia; exact ST
        | |- mem_inv _ _ => eassumption
        | |- inmem_range _ _ => rewrite ?unsigned_lit by lia; exact IR
        | |- shadow_ok _ _ _ => rewrite ?unsigned_lit by lia; exists ng, lastb; subst sbs; split; [exact NG| split; [exact SH| exact LB]]
        | |- _ => rewrite ?unsigned_lit by lia; first [lia | mlia]
        end).
      do 4 zstep.
      zstep. if_cases K4; zify_cond K4. 2:{ exfalso. try (generalize alloc_ceiling_val); clear -K4; try pose proof alloc_ceiling_val. cbv in K4. lia. }
      a0_join. eapply am_tail; try eassumption.
    + (* [comment removed for export] *)
      zstep. a0_join. eapply am_tail; try eassumption.
  - (* [comment removed for export] *)
    assert (HS1 : (0 <= Z.shiftr (bv_unsigned a0) 3 <= bv_unsigned a0)%Z) by (rewrite Z.shiftr_div_pow2 by lia; mlia).
    assert (HS2 : (0 <= Z.shiftr (bv_unsigned a0 + bv_unsigned a2 + -1) 3 <= bv_unsigned a0 + bv_unsigned a2 - 1)%Z)
      by (rewrite Z.shiftr_div_pow2 by lia; mlia).
    do 9 zstep.
    pose proof (qc_read _ _ _ QB1 ltac:(lia)) as RD1.
    pose proof (qc_read _ _ _ QB2 ltac:(lia)) as RD2.
    zstep. zstep. zstep. zstep. zstep.
    zstep. if_cases K7; zify_cond K7.
    + (* [comment removed for export] *)
      subst sbs.
      assert (LBR : (0 <= lastb < 128)%Z) by (hs_lbr lastb).
      pose proof (u8ro_read rsegs _ (bv_unsigned a0 / 8 + shadow_off) _ (Z.of_nat ng) (Z_to_bv 8 lastb)
                    (Z_to_bv 64 (2147450880 + Z.shiftr (bv_unsigned a0 + bv_unsigned a2 + -1) 3)) SH) as RD.
      specialize (RD ltac:(rewrite Nat2Z.id, (shadow_nth ng lastb ng), Nat.ltb_irrefl by lia; reflexivity) ltac:(lia)
                     ltac:(unfold wa, shadow_off; f_equal; rewrite Z.shiftr_div_pow2 by lia; mlia)).
      zstep. rewrite sxb_small by lia.
      zstep. zstep. zstep. zstep. zstep.
      rewrite (poisoned_last_zero (bv_unsigned a0 + bv_unsigned a2 + -1) lastb) by
        (first [destruct LB as [LB0|LB1]; [left; exact LB0| right;
           replace (bv_unsigned a0 + bv_unsigned a2 + -1)%Z with (bv_unsigned a0 + bv_unsigned a2 - 1)%Z by (clear - LB1; lia); (clear - LB1; lia)] | lia]).
      rewrite !Z.shiftr_div_pow2 by lia. change (2^3)%Z with 8%Z.
      set (sf := (2147450880 + bv_unsigned a0 / 8)%Z). set (sl := (2147450880 + (bv_unsigned a0 + bv_unsigned a2 + -1) / 8)%Z).
      assert (ESF : (sf = bv_unsigned a0 / 8 + shadow_off)%Z) by (unfold sf, shadow_off; lia).
      assert (ESL : (sl = sf + Z.of_nat ng)%Z) by (unfold sf, sl; mlia).
      assert (SFB : (0 <= sf /\ sl + 1 <= 0x100080000000)%Z).
      { rewrite length_app, zeros_length in SHhi. cbn [length] in SHhi. unfold shadow_off in *. lia. }
      clearbody sf sl.
      zstep. if_cases K8; zify_cond K8.
      * a0_join. eapply am_slow_end; eassumption.
      * a0_join. eapply (am_slow_loop _ _ _ _ _ _ _ _ _ a0) with (j := 0%Z); try eassumption; try reflexivity; try lia.
        f_equal; lia.
    + (* [comment removed for export] *)
      a0_join. eapply am_tail; try eassumption.
Qed.

End CEIL.
