(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AKit ECH_AsKit ECH_AC5_reserve.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition APU_RA : Z := R_sk_insert_sk_reserve.   (* [comment removed for export] *)
  Definition SHB : Z := 0x7fff8000.
  (* [comment removed for export] *)
  Definition ains_frame (j : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
    [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Local Ltac prep HDR := unfold sk_hdr_cells, wz in HDR; pose proof (rw_cells_bound _ _ _ _ HDR) as HB; cbn [cells_size csize Nat.add] in HB.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac b2z_lit :=
    repeat match goal with
    | |- context [Z.b2z (?x <? ?y)] =>
        first [ replace (x <? y) with true by (symmetry; apply Z.ltb_lt; lia)
              | replace (x <? y) with false by (symmetry; apply Z.ltb_ge; lia) ]; cbn [Z.b2z]
    end.
  (* [comment removed for export] *)
  Local Ltac reacc_with ACC' MU NSW ACC :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ACC' with id (accessible _ ?a ?n) =>
        assert (ACC : accessible mx a n) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW])
      end end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma apu_seg1 :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a p lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo -> 0 <= sk_num K <= 2^20 -> 0 < p < 2^64 ->
      accessible m a SK_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 128 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j (a3' a4' s7' : word),
          ms' = MS (mkR (Z_to_bv 64 APU_RA) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 0) a3' a4' a5 a6 a7
                       (Z_to_bv 64 (sk_num K)) s3 (Z_to_bv 64 p) s5 s6 s7' (Z_to_bv 64 (Z.shiftr a 3 + SHB)) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_sk_reserve) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -128, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -128)
          /\ rw_cells asegs m1 (bv_unsigned sp + -128) (ains_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_push) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros AL HDR POS BL NN PR ACC0 GSB SHB0 ST CEIL LO MI. unfold P_OPENSSL_sk_push, P_sk_reserve, APU_RA, R_sk_insert_sk_reserve, SHB.
    prep HDR. unfold SK_SIZE in *.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(bv_unsigned sp + -128, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    (* [comment removed for export] *)
    carve_frame 16%nat ST.
    do 4 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    reacc_with ACC' MU NSW ACC.
    step. ubal_by AL. step. if_lit. step. step. step. zstep. zstep. ck8_check ACC a. clear ACC.
    st1. rewrite sx32_wz by lia. unfold wz. do 3 step.
    release_frame FR ST (bv_unsigned sp). step.
    (* [comment removed for export] *)
    carve_frame 128%nat ST.
    do 15 step. step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    reacc_with ACC' MU NSW ACC.
    (* [comment removed for export] *)
    step. step. ubal_by AL. step. if_lit. step. step. step. step. step. zstep. zstep. ck8_check ACC a. clear ACC.
    (* [comment removed for export] *)
    st1. rewrite sx32_wz by lia. unfold wz. step. step.
    step. try (if_cases K0; zify_cond K0; [| kill K0]; clear K0).
    (* [comment removed for export] *)
    do 4 step.
    finish. all: try exact FR. all: unfold sk_hdr_cells, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma apu_seg2 :
    forall (sp gp tp t0 t1 t2 s0x s7x a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a p D cap srt cmp cth fth cpth : Z) (el : list Z) (hid did : bptr) (pad junk j : list byte),
      let K := mkSK el D cap srt cmp cth fth cpth hid did in
      let Q := D + 8 * zlength el in
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < a -> a + 56 <= bv_unsigned sp + -128 ->
      0 <= zlength el -> zlength el + 1 <= cap -> cap <= 2^20 -> 0 <= srt <= 1 -> (cmp = 0 \/ zlength el = 0 \/ srt = 0) ->
      0 < D -> D mod 8 = 0 -> D + 8 * cap <= bv_unsigned sp + -128 -> (a + 56 <= D \/ D + 8 * cap <= a) -> 0 < p < 2^64 ->
      (a + 56 <= ALOWSH_LO \/ AHI_LO <= a) -> (D + 8 * cap <= ALOWSH_LO \/ AHI_LO <= D) ->
      accessible m a 56 -> accessible m D (8 * cap) ->
      rw_cells asegs m Q [CB (Z.to_nat (8 * (cap - zlength el))) junk] ->
      rw_cells asegs m (bv_unsigned sp + -128) (ains_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength el + 1)) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(a, a + 56); (Q, Q + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 a (sk_hdr_cells (sk_after_push K p D cap did) pad)
          /\ rw_cells asegs m1 Q [C8 (wz p)]
          /\ rw_cells asegs m1 (Q + 8) [CB (Z.to_nat (8 * (cap - zlength el)) - 8)%nat (skipn 8 junk)])
        (MS (mkR (Z_to_bv 64 APU_RA) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (zlength el)) s3 (Z_to_bv 64 p) s5 s6 s7x (Z_to_bv 64 (Z.shiftr a 3 + SHB)) (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 APU_RA)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros K Q HDR POS HS NN ROOM CAP SRT NOC DP ALD DS DDJ PR NSA NSD ACCa0 ACCd0 JK FR MI. subst K. unfold APU_RA, R_sk_insert_sk_reserve, SHB.
    replace (ret_pc (Z_to_bv 64 0x1f9894)) with (Z_to_bv 64 0x1f9894) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. prep HDR. unfold sk_num in HDR; cbn [sk_elems sk_data sk_sorted sk_cap sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk] in HDR.
    unfold ains_frame in FR.
    pose proof ACCa0 as (_ & AHIa & _). pose proof ACCd0 as (_ & AHId & _). unfold AAPP_HI in AHIa, AHId.
    destruct (rw_cells_CB_split asegs _ Q _ 8 junk JK ltac:(lia)) as [JQ JR]. clear JK.
    pose proof (munch_refl [(a, a + 56); (Q, Q + 8)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(a, a + 56); (Q, Q + 8)]).
    { apply Forall_cons; [cbn [fst snd]; exact NSA|]. apply Forall_cons; [cbn [fst snd]; subst Q; lia| apply Forall_nil]. }
    pose proof ACCa0 as ACCa'. clear ACCa0. change (id (accessible m a 56)) in ACCa'.
    pose proof ACCd0 as ACCd'. clear ACCd0. change (id (accessible m D (8 * cap))) in ACCd'.
    (* [comment removed for export] *)
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    reacc_with ACCa' MU NSW ACCa. ck8_check ACCa a.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACCa (a + 8). clear ACCa.
    (* [comment removed for export] *)
    st1. rewrite sx32_wz by lia. unfold wz. step.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. rewrite !lxor_top by lia. rewrite Z.ltb_irrefl.
    replace (zlength el + 9223372036854775808 <? 9223372036854775808) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z Z.lxor Z.lor].
    step. first [if_cases K0; zify_cond K0; [kill K0|]; clear K0 | if_false | idtac].
    (* [comment removed for export] *)
    zstep. rewrite (Z.shiftl_mul_pow2 _ 3) by lia. change (2^3) with 8. zstep.
    replace (D + zlength el * 8) with Q by lia.
    zstep. zstep. b2z_lit. step. if_lit.
    zstep. zstep. rewrite ?lxor_top by lia. b2z_lit. zstep. zstep. step. if_lit.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    step. ubal_by ALD. step. if_lit.
    reacc_with ACCd' MU NSW ACCd. zstep. zstep. ck8_check ACCd Q. clear ACCd.
    st1. step. step.
    (* [comment removed for export] *)
    reacc_with ACCa' MU NSW ACCa. ck8_check ACCa a. clear ACCa.
    st1. rewrite sx32_wz by lia. unfold wz. zstep. rewrite ?swrap32_small by lia.
    step. if_cases K0; zify_cond K0; [kill K0|]; clear K0.
    reacc_with ACCa' MU NSW ACCa. ck8_check ACCa a. clear ACCa.
    st1. zstep. zstep. zstep.
    reacc_with ACCa' MU NSW ACCa. ck8_check ACCa (a + 16). clear ACCa.
    st1. rewrite sx32_wz by lia. unfold wz.
    (* [comment removed for export] *)
    assert (FIN : forall srt' mX (a0x a1x a2x a3x a4x s2x s3x s4x s5x s6x s10x s11x : word),
      munch [(a, a + 56); (Q, Q + 8)] m mX -> wmono asegs m mX -> mem_inv asegs mX ->
      rw_cells asegs mX a [C4 (Z_to_bv 64 (zlength el + 1)); CB 4 pad; C8 (Z_to_bv 64 D); C4 (Z_to_bv 64 srt'); C4 (Z_to_bv 64 cap);
                           C8 (Z_to_bv 64 cmp); C8 (Z_to_bv 64 cth); C8 (Z_to_bv 64 fth); C8 (Z_to_bv 64 cpth)] ->
      srt' = (if (srt =? 1) && (1 <=? zlength el) then 0 else srt) -> 0 <= srt' <= 1 ->
      rw_cells asegs mX Q [C8 (Z_to_bv 64 p)] ->
      rw_cells asegs mX (Q + Z.of_nat 8) [CB (Z.to_nat (8 * (cap - zlength el)) - 8) (skipn 8 junk)] ->
      rw_cells asegs mX (bv_unsigned sp + -128) [CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      evt asegs (fun ms' => exists (a1' a2' a3' a4' a5' : word) m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength el + 1)) a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(a, a + 56); (Q, Q + 8)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 a (sk_hdr_cells (sk_after_push (mkSK el D cap srt cmp cth fth cpth hid did) p D cap did) pad)
          /\ rw_cells asegs m1 Q [C8 (wz p)]
          /\ rw_cells asegs m1 (Q + 8) [CB (Z.to_nat (8 * (cap - zlength el)) - 8)%nat (skipn 8 junk)])
        (MS (mkR (Z_to_bv 64 0x1f9894) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a)
                 a0x a1x a2x a3x a4x a5 a6 a7
                 s2x s3x s4x s5x s6x s7x (Z_to_bv 64 (Z.shiftr a 3 + 2147450880)) (Z_to_bv 64 2147450880) s10x s11x t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f9b50) fc None mX (seg_rom asegs))).
    { intros srt' mX a0x a1x a2x a3x a4x s2x s3x s4x s5x s6x s10x s11x MUX WMX MIX HDRX E SB QX JX FRX.
      clear MU WM. rename MUX into MU. rename WMX into WM.
      reacc_with ACCa' MU NSW ACCa. ck8_check ACCa a. clear ACCa.
      st1. rewrite sx32_wz by lia. unfold wz.
      do 15 step. finish.
      unfold sk_hdr_cells, sk_after_push, sk_num, wz. cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk].
      unfold zlength in *. rewrite length_app. cbn [length]. rewrite Nat2Z.inj_add. cbn [Z.of_nat Pos.of_succ_nat]. rewrite <- E. exact HDRX. }
    cbv delta [mkR] in FIN.
    destruct (Z.eq_dec srt 0) as [S0|S1].
    - (* [comment removed for export] *)
      subst srt. step. try if_true.
      eapply (FIN 0); try eassumption; try lia. cbn. reflexivity.
    - assert (S1' : srt = 1) by lia. subst srt. step. try if_false.
      (* [comment removed for export] *)
      step. step.
      all: lazymatch goal with
      | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_cases Kb; try zify_cond Kb
      | _ => idtac
      end.
      all: lazymatch goal with
      | |- evt _ _ (MS _ _ (Z_to_bv 64 0x1f9b50) _ _ _ _) =>
          (* [comment removed for export] *)
          assert (N0 : zlength el = 0)
            by first [ lia
                     | revert Kb; rewrite ?signed_lit by lia; intros Kb; lia
                     | match goal with K : (_ && _) = false |- _ => apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; lia end ];
          eapply (FIN 1); try eassumption; try lia; rewrite N0; cbn; reflexivity
      | |- _ =>
          (* [comment removed for export] *)
          assert (N1 : 1 <= zlength el)
            by first [ lia
                     | revert Kb; rewrite ?signed_lit by lia; intros Kb; lia
                     | match goal with K : (_ && _) = true |- _ => apply Bool.andb_true_iff in K; destruct K as [K _]; apply Z.ltb_lt in K; lia end ];
          assert (C0 : cmp = 0) by lia; subst cmp;
          (* [comment removed for export] *)
          zstep; zstep; zstep;
          reacc_with ACCa' MU NSW ACCa; ck8_check ACCa (a + 24); clear ACCa;
          step; step; try if_true;
          (* [comment removed for export] *)
          reacc_with ACCa' MU NSW ACCb; ck8_check ACCb (a + 16); clear ACCb;
          st1;
          eapply (FIN 0); try eassumption; try lia; cbn [Z.eqb Pos.eqb andb]; destruct (Z.leb_spec 1 (zlength el)); [reflexivity| lia]
      end.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH0 : asan_rt_hyps H := proj1 HHx.

  Lemma u64arr_snoc : forall m A ws w,
    u64arr asegs m A ws -> rw_cells asegs m (A + 8 * Z.of_nat (length ws)) [C8 w] -> u64arr asegs m A (ws ++ [w]).
  Proof.
    intros m A ws w [B W] [[_ B1] W1]. cbn [cells_bytes cbytes app] in B1. rewrite app_nil_r in B1. cbn [cells_size csize Nat.add] in W1.
    split.
    - rewrite u64s_app. cbn [u64s map concat]. rewrite app_nil_r. apply bytes_at_app. split; [exact B|]. rewrite u64s_length.
      replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia. exact B1.
    - rewrite length_app. cbn [length]. replace (8 * Z.of_nat (length ws + 1)) with (8 * Z.of_nat (length ws) + 8) by lia.
      apply wr_at_app; [lia| lia|]. split; [exact W|]. replace 8 with (Z.of_nat (8 + 0)) at 2 by reflexivity. exact W1.
  Qed.

  Lemma askpush_spec : skpush_stmt H.
  Proof.
    unfold skpush_stmt. intros until CH.
    intros VIS A0 A1 PR SO NOC CAPX HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL [SH1 SH2] (MF & IM & GM). subst a0 a1.
    lazymatch type of LO with lo <= bv_unsigned sp - ?e => let v := eval cbv in e in change e with v in LO end.   (* [comment removed for export] *)
    unfold SK_CAP_MAX, SK_SIZE in *.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -128) by lia.
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    pose proof SO as SO'. destruct SO' as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    pose proof (ah_blocks H HH0 _ _ _ _ HP HIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. clear K6. unfold SK_SIZE in K3, K5, K7.
    pose proof (aapp_bounds a 56 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    assert (ACC0 : accessible m a 56) by (eapply addressable_accessible; [exact SH1| lia| lia| unfold AAPP_HI; lia]).
    unfold sk_num in *.
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH0); [exact KREL| exact VIS| eapply apu_seg1 with (lo := lo);
      [clear - K2; Z.div_mod_to_equations; lia| exact HDR| exact POS| unfold SK_SIZE; lia| unfold sk_num; clear - NC CAP; lia| exact PR| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| clear - LO; lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & j & c3 & c4 & c7 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -128, bv_unsigned sp)]) by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -128, bv_unsigned sp)])
      by (apply Forall_cons; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| apply Forall_nil]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH0); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH0); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (MF1 : MEMFLAG m1 v) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (SO1 : SKobj LB m1 a K).
    { eapply (SKobj_rehdr_gen LB m m1); [exact SO| exact PL| exact HDR1| exact MU1| exact WM1|].
      destruct DAT as [[C0 _]|(_ & _ & _ & DIN & _)]; [left; exact C0| right].
      pose proof (ah_blocks H HH0 _ _ _ _ HP DIN) as (E1 & _ & _ & _ & E5 & _). cbn [blk_addr blk_size fst snd] in E1, E5. cbn. clear - E5 LO CEIL. lia. }
    assert (SHH1 : addressable m1 a 56 /\ (sk_cap K <> 0 -> addressable m1 (sk_data K) (8 * sk_cap K))).
    { split; [| intros CNZ].
      - eapply addressable_transport; [exact SH1| exact MU1| exact WM1|].
        pose proof (sh_aapp_range a 56 K7 ltac:(lia)) as (Sx1 & Sx2 & Sx3). unfold AHI_LO in Sx3. cbn [disjoint_from fst snd]. split; [lia| exact I].
      - destruct DAT as [[C0 _]|(D4 & _ & _ & DIN & _)]; [lia|].
        pose proof (ah_blocks H HH0 _ _ _ _ HP DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E3, E5, E7.
        eapply addressable_transport; [exact (SH2 CNZ)| exact MU1| exact WM1|].
        pose proof (sh_aapp_range (sk_data K) (8 * sk_cap K) E7 ltac:(lia)) as (Sx1 & Sx2 & Sx3). unfold AHI_LO in Sx3. cbn [disjoint_from fst snd]. split; [lia| exact I]. }
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH0 m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]).
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { eapply (ah_chain_cons H HH0); [exact CH0| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold ains_frame in FR2.
      change ([CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
        with ([CB 24 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -128 + 112) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -128 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : (bv_unsigned sp + -128) mod 16 = 0) by (replace (bv_unsigned sp + -128) with (bv_unsigned sp - 128) by lia; rewrite Zminus_mod, SP16; reflexivity).
    clear CW AW.
    (* [comment removed for export] *)
    pose proof (askreserve_spec H HHx) as RS. unfold skreserve_stmt in RS.
    eapply (ah_seq H HH0).
    { eapply RS with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (K := K) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
        [exact VIS1| reflexivity| reflexivity| reflexivity| ..]; rewrite ?unsigned_lit by lia.
      all: first [exact SO1| exact HP1| exact KREL1| exact BUD| exact BUDC| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity| exact SP16'| exact AC1| exact CH1| exact CHS1
                 | exact HAL| exact SHH1| split; [exact MF1| split; [exact IM1| exact GM1]]
                 | unfold APU_RA; rewrite ?unsigned_lit by (unfold R_sk_insert_sk_reserve; lia); eapply pf_ok_call; [exact PF|]; unfold PF_skpush; intros x Hx; exact Hx
                 | unfold SK_CAP_MAX; lia
                 | unfold SKRESERVE_STACK, FR_sk_reserve, CARRAY_STACK, CREALLOC_ARRAY_STACK, CZALLOC_STACK, CREALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_realloc, FR_CRYPTO_malloc, AMALLOC_STACK, AREALLOC_STACK; clear - LO; lia
                 | lia
                 | match goal with |- ?G => idtac "LEFT:" G end]. }
    intros [msF2 mo2] PO. unfold skreserve_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & s' & LB' & Kr & data' & cap' & did' &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & EK1 & LBREL & ROOM & HEAP2 & SO2 & [SA2 SD2] & XP2 & (v2 & (MF2 & IM2 & GM2) & VLE) & AL2).
    subst Kr. rewrite (unsigned_lit (bv_unsigned sp + -128)) in ST2, XP2 by lia.
    pose proof SO2 as SO2'. destruct SO2' as ((pad2 & PL2 & HDR2) & _ & HIN2 & NC2 & CAP2 & _ & _ & DAT2).
    unfold sk_num in ROOM, NC2, CAP2, DAT2, SD2. cbn [sk_elems sk_cap sk_data sk_did sk_sorted sk_after_reserve] in ROOM, NC2, CAP2, DAT2, HIN2, SA2, SD2.
    destruct DAT2 as [[C0 _]|(D4 & DP & DDJ & DIN & AR2 & junk2 & JK2)]; [lia|]. specialize (SD2 ltac:(lia)). unfold SK_SIZE in SA2, DDJ.
    pose proof (ah_blocks H HH0 _ _ _ _ HEAP2 HIN2) as (L1 & L2 & L3 & L4 & L5 & L6 & L7). cbn [blk_addr blk_size fst snd] in L1, L3, L5, L7. clear L2 L4 L6. unfold SK_SIZE in L3, L5, L7.
    pose proof (ah_blocks H HH0 _ _ _ _ HEAP2 DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E5, E7. clear E4 E6.
    pose proof (aapp_bounds data' (8 * cap') E7 ltac:(lia)) as (DB1 & DB2 & DB3 & DB4 & DB5). unfold AAPP_HI in DB3.
    assert (ACC2 : accessible m2 a 56) by (eapply addressable_accessible; [exact SA2| lia| lia| unfold AAPP_HI; lia]).
    assert (ACD2 : accessible m2 data' (8 * cap')) by (eapply addressable_accessible; [exact SD2| lia| lia| unfold AAPP_HI; lia]).
    eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia|].
    2:{ unfold memflag_foot, A_mem_inited, ASK_foot, SK_foot, SK_SIZE. cbn [sk_cap sk_data sk_after_reserve].
        apply Forall_cons; [cbn; clear - SPR LO CEIL ACEILB; lia|]. apply Forall_cons; [cbn; clear - K5 SPR LO CEIL ACEILB; lia|].
        replace (cap' =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app].
        apply Forall_cons; [cbn; clear - E5 SPR LO CEIL ACEILB; lia|].
        apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. pose proof (sh_aapp_range data' (8 * cap') E7 ltac:(lia)) as (Sx1 & Sx2 & Sx3). unfold AHI_LO in Sx3.
        clear - Sx2 Sx3 SPR LO CEIL ACEILB. lia. }
    (* [comment removed for export] *)
    unfold sk_after_reserve in HDR2.
    eapply (ahh_evt H HH0); [exact KREL2| exact VIS2| eapply apu_seg2 with (hid := sk_id K);
      [exact HDR2| exact POS| clear - K5 LO CEIL; lia| lia| lia| lia| lia| exact NOC| exact DP| clear - E2; Z.div_mod_to_equations; lia| clear - E5 LO CEIL; lia| exact DDJ| exact PR
      | exact (aapp_not_shadowland _ _ L7)| exact (aapp_not_shadowland _ _ E7)| exact ACC2| exact ACD2| exact JK2| exact FR1| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 (a1' & a2' & a3' & a4' & a5' & m3 & VIS3 & MU3 & WM3 & MI3 & HDR3 & EQ3 & JR3).
    assert (APQ : aapp (data' + 8 * zlength (sk_elems K)) 8) by (eapply aapp_sub; [exact E7| lia| lia]).
    assert (CW3 : Forall (aclient_write_ok H LB') [(a, a + 56); (data' + 8 * zlength (sk_elems K), data' + 8 * zlength (sk_elems K) + 8)]).
    { apply Forall_cons; [right; right; left; exists (sk_id K, a, 56); cbn; split; [exact HIN2| lia]|].
      apply Forall_cons; [right; right; left; exists (did', data', 8 * cap'); cbn; split; [exact DIN| clear - NC2 ROOM; lia]| apply Forall_nil]. }
    unfold skpush_post. cbn [cfg_ms cfg_model]. unfold sk_num.
    exists u0, u1, u2, a1', a2', a3', a4', a5', b6, b7, u3, u4, u5, u6, m3, errv2, s', LB'.
    exists (sk_after_push K p data' cap' did'), data', cap', did'.
    split; [unfold zlength; exact VIS3|]. split; [exact KREL3|].
    split; [eapply (ah_mpres_trans H HH0); [| exact MP3]; eapply (ah_mpres_trans H HH0); [exact MP1| exact MP2]|].
    split; [exact MI3|].
    split. { eapply ACONST_frame; [exact AC2| exact MU3| exact WM3|].
             apply Forall_cons; [eapply aconst_ok_aapp; [exact L7| cbn; lia| cbn; lia]|].
             apply Forall_cons; [eapply aconst_ok_aapp; [exact APQ| cbn; lia| cbn; lia]| apply Forall_nil]. }
    split. { apply (rw_cells_transport asegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; clear - K5 E5 NC2 ROOM LO CEIL SPR; lia].
             apply (stk_transport_disjoint asegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; clear - K5 E5 NC2 ROOM LO CEIL SPR; lia].
             unfold ains_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
    split. { rewrite unsigned_lit in ERR2 |- * by (unfold ATP; lia). eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; clear - K4 E7 DB1 NC2 ROOM; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO in E7; lia]. }
    split. { eapply (ah_rauxv_frame H HH0); [exact AUX2| exact MU3| exact WM3| exact CW3]. }
    split; [reflexivity|]. split; [exact LBREL|].
    split. { eapply (ah_RHEAP_frame H HH0); [exact HEAP2| exact MU3| exact WM3| exact CW3]. }
    split.
    { unfold SKobj, sk_num. cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk sk_id sk_did sk_after_push].
      unfold sk_num. unfold zlength in *. rewrite length_app. cbn [length].
      split; [exists pad2; split; [exact PL2| exact HDR3]|]. split; [exact POS|]. split; [exact HIN2|].
      split; [lia|]. split; [lia|]. split; [destruct (sk_sorted K =? 1), (1 <=? Z.of_nat (length (sk_elems K))); cbn; lia|].
      split; [apply Forall_app; split; [exact EL| constructor; [lia| constructor]]|].
      right. split; [lia|]. split; [lia|]. split; [exact DDJ|]. split; [exact DIN|]. split.
      - rewrite map_app. cbn [map]. apply u64arr_snoc.
        + eapply u64arr_transport; [exact AR2| exact MU3| exact WM3|]. rewrite length_map. cbn. clear - DDJ NC2 ROOM. lia.
        + rewrite length_map. exact EQ3.
      - exists (skipn 8 junk2). replace (data' + 8 * Z.of_nat (length (sk_elems K) + 1)) with (data' + 8 * Z.of_nat (length (sk_elems K)) + 8) by lia.
        replace (Z.to_nat (8 * (cap' - Z.of_nat (length (sk_elems K) + 1)))) with (Z.to_nat (8 * (cap' - Z.of_nat (length (sk_elems K)))) - 8)%nat by lia.
        exact JR3. }
    split.
    { unfold SK_shad, SK_SIZE. cbn [sk_cap sk_data sk_after_push]. split; [| intros _].
      - eapply addressable_transport; [exact SA2| exact MU3| exact WM3|].
        pose proof (aapp_disjoint_sh a 56 a 56 K7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS1.
        pose proof (aapp_disjoint_sh _ 8 a 56 APQ ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS2.
        cbn [disjoint_from fst snd]. split; [clear - DS1; lia| split; [clear - DS2; lia| exact I]].
      - eapply addressable_transport; [exact SD2| exact MU3| exact WM3|].
        pose proof (aapp_disjoint_sh a 56 data' (8 * cap') K7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS1.
        pose proof (aapp_disjoint_sh _ 8 data' (8 * cap') APQ ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS2.
        cbn [disjoint_from fst snd]. split; [clear - DS1; lia| split; [clear - DS2; lia| exact I]]. }
    split.
    { assert (FEQ : ASK_foot a (sk_after_push K p data' cap' did') = ASK_foot a (sk_after_reserve K data' cap' did')) by reflexivity. rewrite FEQ.
      eapply xpres_trans; [| eapply xpres_trans].
      - eapply (xpres_of_munch H s' LB' _ _ _ m2 m m1); [exact HH0| exact HEAP2| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil].
      - eapply (xpres_weaken H); [exact XP2| lia| auto| auto].
      - eapply (xpres_of_munch_gen H); [exact MU3| exact WM3|]. intros q Hq [HC HX]. rewrite rin_ivs_app in HX. unfold ASK_foot, SK_foot, SK_SIZE in HX.
        cbn [sk_cap sk_data sk_after_reserve] in HX. replace (cap' =? 0) with false in HX by (symmetry; apply Z.eqb_neq; lia). cbn in HX |- *.
        clear - Hq HX NC2 ROOM. lia. }
    split.
    { exists v2. split; [| exact VLE]. split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; clear - K4 E7 DB1 NC2 ROOM; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO in E7; lia| exact MF2]|].
      split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; clear - K4 E7 DB1 NC2 ROOM; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO in E7; lia| exact IM2]|].
      eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; clear - K4 E7 DB1 NC2 ROOM; unfold aapp, aapp_lo, aapp_hi, AIMG_TOP, AHI_LO in E7; lia| exact GM2]. }
    exact AL2.
  Qed.
End W.
