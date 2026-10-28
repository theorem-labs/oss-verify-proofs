(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AKit ECH_AsKit ECH_AC1_malloc ECH_AC1_zalloc ECH_AC1_realloc.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma div5_magic : forall x, 0 <= x < 2^31 -> (x * 1717986919) / 2^33 = x / 5.
Proof.
  intros x Hx. set (q := x / 5). set (r := x mod 5).
  assert (E : x = 5 * q + r) by (subst q r; apply Z.div_mod; lia).
  assert (R : 0 <= r < 5) by (subst r; apply Z.mod_pos_bound; lia).
  assert (Q : 0 <= q <= x) by (subst q; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  replace (x * 1717986919) with (q * 2^33 + (3 * q + r * 1717986919)) by lia.
  rewrite Z.div_add_l by lia. rewrite (Z.div_small (3 * q + r * 1717986919)) by lia. lia.
Qed.
Lemma lxor_ones31 : forall x, 0 <= x < 2^31 -> Z.lxor x 2147483647 = 2147483647 - x.
Proof.
  intros x Hx. pose proof (Z.add_lxor_2land x 2147483647) as E.
  change 2147483647 with (Z.ones 31) in E |- *. rewrite Z.land_ones, Z.mod_small in E by lia. lia.
Qed.
(* [comment removed for export] *)
Lemma srl_check : forall cap, 0 <= cap < 2^20 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 ((cap + -268435456) mod 18446744073709551616)) 29) = 7.
Proof.
  intros cap H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 32) with 4294967296.
  rewrite Z.shiftr_div_pow2 by lia.
  replace ((cap + -268435456) mod 18446744073709551616) with (cap + -268435456 + 18446744073709551616).
  2:{ rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
  replace ((cap + -268435456 + 18446744073709551616) mod 4294967296) with (cap + 4026531840).
  2:{ symmetry. rewrite <- (Z.mod_add _ (-4294967295)) by lia. rewrite Z.mod_small by lia. lia. }
  pose proof (Z.div_le_lower_bound (cap + 4026531840) (2^29) 7 ltac:(lia) ltac:(lia)).
  pose proof (Z.div_lt_upper_bound (cap + 4026531840) (2^29) 8 ltac:(lia) ltac:(lia)).
  replace ((cap + 4026531840) / 2 ^ 29) with 7 by lia. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma srl_check_land : forall cap, 0 <= cap < 2^20 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 (Z.land (cap + -268435456) 18446744073709551615)) 29) = 7.
Proof.
  intros cap H. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  change (2 ^ 64) with 18446744073709551616. apply srl_check. exact H.
Qed.
Lemma sk_grow_ge : forall cap, 4 <= cap -> cap + 1 <= sk_grow cap <= 2 * cap.
Proof. intros cap H. unfold sk_grow. split; [apply Z.div_le_lower_bound; lia| apply Z.div_le_upper_bound; lia]. Qed.

Section S.
  Context {HCEIL : HeapCeil}.

  Definition ASK_FILE : Z := 0x4aa54.
  Definition ASR_RA1 : Z := R_sk_reserve_CRYPTO_calloc.          (* [comment removed for export] *)
  Definition ASR_RA2 : Z := R_sk_reserve_CRYPTO_realloc_array.   (* [comment removed for export] *)
  Definition SHB : Z := 0x7fff8000.
  (* [comment removed for export] *)
  Definition asr_frame (j : list byte) (s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
    [CB 8 j; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma sk_hdr_size : forall K pad, cells_size (sk_hdr_cells K pad) = 56%nat.
  Proof. reflexivity. Qed.
  Local Ltac prep HDR := unfold sk_hdr_cells, wz in HDR; pose proof (rw_cells_bound _ _ _ _ HDR) as HB; cbn [cells_size csize Nat.add] in HB.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  Local Ltac udead := first [ if_lit_strict | ub_dead ].
  (* [comment removed for export] *)
  Local Ltac reacc ACC' MU :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ACC' with id (accessible _ ?a ?n) =>
        let ACC := fresh "ACC" in
        assert (ACC : accessible mx a n) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU|]; apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil])
      end end.

  (* [comment removed for export] *)
  Local Ltac entry ST ACC' MU AL :=
    carve_frame 80%nat ST;
    do 11 step;
    reacc ACC' MU;
    lazymatch goal with ACC : accessible _ ?a _ |- _ =>
      (* [comment removed for export] *)
      step; step; ubal_by AL; step; if_lit;
      step; step; step; zstep; zstep; ck8_check ACC a;
      (* [comment removed for export] *)
      st1; rewrite ?sx32_wz by lia; unfold wz;
      zstep; zstep; zstep; zstep; rewrite ?swrap32_small by lia;
      step; udead;
      zstep; rewrite ?swrap32_small by lia;
      step;
      first [ if_lit_strict | let K0 := fresh "K0" in (if_cases K0; zify_cond K0; [| kill K0]; clear K0) ];
      (* [comment removed for export] *)
      zstep; zstep; rewrite ?swrap32_small by lia;
      step; udead;
      zstep; rewrite ?swrap32_small by lia; step
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma asr_segB :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo ->
      0 <= sk_num K -> sk_num K + 1 <= sk_cap K -> 4 <= sk_cap K <= 2^20 -> sk_data K <> 0 -> 0 <= sk_data K < 2^64 ->
      accessible m a SK_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (t0' a1' a3' a4' a5' : word) m1,
          ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' (Z_to_bv 64 0) a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_sk_reserve) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros AL HDR POS BL NN ROOM CAP DNZ DR ACC0 GSB SHB0 ST CEIL LO MI. unfold P_sk_reserve. prep HDR. unfold SK_SIZE in *.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    entry ST ACC' MU AL.
    (* [comment removed for export] *)
    assert (FIN : forall na (a3x a4x : word) mx, na = Z.max (sk_num K + 1) 4 -> munch [(lo, bv_unsigned sp)] m mx -> wmono asegs m mx -> mem_inv asegs mx ->
      stk asegs mx lo (bv_unsigned sp + -80) ->
      rw_cells asegs mx a [C4 (Z_to_bv 64 (sk_num K)); CB 4 pad; C8 (Z_to_bv 64 (sk_data K)); C4 (Z_to_bv 64 (sk_sorted K)); C4 (Z_to_bv 64 (sk_cap K));
                         C8 (Z_to_bv 64 (sk_comp K)); C8 (Z_to_bv 64 (sk_cmp_thunk K)); C8 (Z_to_bv 64 (sk_free_thunk K)); C8 (Z_to_bv 64 (sk_copy_thunk K))] ->
      (exists fr, rw_cells asegs mx (bv_unsigned sp + -80) fr /\ cells_size fr = 80%nat /\
         exists j, fr = asr_frame j s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      evt asegs (fun ms' => exists (t0' a1' a3' a4' a5' : word) m1,
          ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 1) a1' (Z_to_bv 64 0) a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
          /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) (Z_to_bv 64 4) (Z_to_bv 64 1) (Z_to_bv 64 0)
                 a3x a4x a5 a6 a7 s2 (Z_to_bv 64 na) s4 (Z_to_bv 64 SHB) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1f9460) fc None mx (seg_rom asegs))).
    { clear - POS BL NN ROOM CAP DNZ DR CEIL LO SPR LO0 AHI ACC' GSB SHB0 HB. unfold SHB.
      intros na a3x a4x mx NA MU WM MI ST HDR (fr & FR & FS & j & ->). unfold asr_frame in FR. pose proof aceil_range as AR.
      reacc ACC' MU.
      (* [comment removed for export] *)
      zstep. zstep. zstep. ck8_check ACC (a + 8).
      step. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
      (* [comment removed for export] *)
      zstep. zstep. zstep. ck8_check ACC (a + 20).
      st1. rewrite sx32_wz by lia. unfold wz. step. if_true.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; [| kill K2]. clear K2.
      (* [comment removed for export] *)
      do 12 step. release_frame FR ST (bv_unsigned sp). finish. }
    cbv delta [mkR SHB] in FIN.
    step. if_cases K1; zify_cond K1.
    - eapply FIN; [revert K1; rewrite ?signed_lit by lia; lia| exact MU| exact WM| assumption| exact ST| assumption| eexists; split; [exact FR| split; [reflexivity| eexists; reflexivity]]].
    - step. eapply FIN; [revert K1; rewrite ?signed_lit by lia; lia| exact MU| exact WM| assumption| exact ST| assumption| eexists; split; [exact FR| split; [reflexivity| eexists; reflexivity]]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma asr_segA :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo ->
      sk_num K = 0 -> sk_cap K = 0 -> sk_data K = 0 ->
      accessible m a SK_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (a4' : word) m1 j,
          ms' = MS (mkR (Z_to_bv 64 ASR_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 4) (Z_to_bv 64 8) (Z_to_bv 64 ASK_FILE) (Z_to_bv 64 194) a4' a5 a6 a7
                       (Z_to_bv 64 (a + 8)) (Z_to_bv 64 4) s4 (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (a + 8) 3 + SHB)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_calloc) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -80)
          /\ rw_cells asegs m1 (bv_unsigned sp + -80) (asr_frame j s7 s6 s5 s4 s3 s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_sk_reserve) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros AL HDR POS BL N0 C0 D0 ACC0 GSB SHB0 ST CEIL LO MI. unfold P_sk_reserve, P_CRYPTO_calloc, ASR_RA1, R_sk_reserve_CRYPTO_calloc, ASK_FILE, SHB.
    prep HDR. unfold SK_SIZE in *.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    rewrite N0, D0 in HDR.
    entry ST ACC' MU AL.
    step. first [if_lit_strict | if_cases K1; zify_cond K1; [kill K1|]; clear K1]. step.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC (a + 8).
    step. step. if_true.
    (* [comment removed for export] *)
    do 6 step.
    finish. all: try exact FR. all: unfold sk_hdr_cells, wz; rewrite ?N0, ?D0; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma asr_segC :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      a mod 8 = 0 ->
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < a -> a + SK_SIZE <= lo ->
      sk_num K = sk_cap K -> 4 <= sk_cap K <= SK_CAP_MAX -> 0 < sk_data K < 2^64 ->
      accessible m a SK_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 80 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1 j,
          ms' = MS (mkR (Z_to_bv 64 ASR_RA2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 sp (Z_to_bv 64 a)
                       (Z_to_bv 64 (sk_data K)) (Z_to_bv 64 (sk_grow (sk_cap K))) (Z_to_bv 64 8) (Z_to_bv 64 ASK_FILE) (Z_to_bv 64 212)
                       a5 a6 a7
                       (Z_to_bv 64 (a + 8)) (Z_to_bv 64 (sk_cap K + 1)) (Z_to_bv 64 (a + 20)) (Z_to_bv 64 (sk_grow (sk_cap K)))
                       (Z_to_bv 64 (Z.shiftr (a + 8) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (a + 20) 3 + SHB))
                       s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_realloc_array) fc None m1 (seg_rom asegs)
          /\ munch [(bv_unsigned sp + -80, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -80)
          /\ rw_cells asegs m1 (bv_unsigned sp + -80) (asr_frame j s7 s6 s5 s4 s3 s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 1) (Z_to_bv 64 0) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_sk_reserve) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros AL HDR POS BL FULL CAP DR ACC0 GSB SHB0 ST CEIL LO MI.
    unfold P_sk_reserve, P_CRYPTO_realloc_array, ASR_RA2, R_sk_reserve_CRYPTO_realloc_array, ASK_FILE, SHB, SK_CAP_MAX in *. prep HDR. unfold SK_SIZE in *.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(bv_unsigned sp + -80, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    rewrite FULL in HDR.
    entry ST ACC' MU AL.
    step. if_cases K1; zify_cond K1; [| kill K1]. clear K1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC (a + 8).
    step. step. if_cases K1; zify_cond K1; [kill K1|]. clear K1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. ck8_check ACC (a + 20).
    st1. rewrite sx32_wz by lia. unfold wz. step. if_true.
    step. if_cases K2; zify_cond K2; [kill K2|]. clear K2.
    (* [comment removed for export] *)
    do 5 step. zstep. zstep. first [rewrite srl_check_land by lia | rewrite srl_check by lia].
    step. if_lit.
    assert (X8 : 0 <= sk_cap K * 8 < 2^24) by lia.
    pose proof (div5_magic (sk_cap K * 8) ltac:(lia)) as DM.
    assert (PM : 0 <= sk_cap K * 8 * 1717986919 < 2^55) by lia.
    zstep. rewrite (Z.shiftl_mul_pow2 (sk_cap K) 3) by lia. change (2^3) with 8. rewrite (swrap32_small (sk_cap K * 8)) by lia.
    zstep.
    zstep. rewrite (Z.shiftr_div_pow2 _ 63) by lia. rewrite (Z.div_small _ (2^63)) by lia.
    zstep. rewrite signed_lit by lia. rewrite (Z.shiftr_div_pow2 _ 33), DM by lia.
    pose proof (sk_grow_ge (sk_cap K) ltac:(lia)) as GG. unfold sk_grow in GG |- *.
    zstep. rewrite ?Z.add_0_r, ?Z.add_0_l.
    step. if_cases K3; zify_cond K3; [kill K3|]. clear K3.
    do 6 step.
    finish. all: try exact FR. all: unfold sk_hdr_cells, wz; rewrite ?FULL; assumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma asr_segA2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s4x s7x s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a D : Z) (K : skrep) (pad j : list byte),
      0 < D < 2^64 -> 0 < a -> (a + 56 <= D \/ D + 32 <= a) -> a + 56 <= bv_unsigned sp + -80 -> (a + 56 <= ALOWSH_LO \/ AHI_LO <= a) ->
      accessible m a 56 ->
      rw_cells asegs m a (sk_hdr_cells K pad) ->
      rw_cells asegs m (bv_unsigned sp + -80) (asr_frame j s7 s6 s5 s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(a, a + 56)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 a (sk_hdr_cells (mkSK (sk_elems K) D 4 (sk_sorted K) (sk_comp K) (sk_cmp_thunk K) (sk_free_thunk K) (sk_copy_thunk K) (sk_id K) (sk_did K)) pad))
        (MS (mkR (Z_to_bv 64 ASR_RA1) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (a + 8)) (Z_to_bv 64 4) s4x (Z_to_bv 64 SHB) (Z_to_bv 64 (Z.shiftr (a + 8) 3 + SHB)) s7x s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ASR_RA1)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HD POS DJ HS NS ACC0 HDR FR MI. unfold ASR_RA1, R_sk_reserve_CRYPTO_calloc, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x1f94bc)) with (Z_to_bv 64 0x1f94bc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. prep HDR. unfold asr_frame in FR.
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(a, a + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(a, a + 56)]) by (constructor; [cbn; exact NS| constructor]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 56) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end.
    (* [comment removed for export] *)
    ck8_check ACC (a + 8). clear ACC. st1.
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 56) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end.
    zstep. zstep. zstep. ck8_check ACC (a + 20). clear ACC. st1.
    (* [comment removed for export] *)
    do 13 step. finish.
  Qed.

  Lemma asr_segC2 :
    forall (sp gp tp t0 t1 t2 s0x a1 a2 a3 a4 a5 a6 a7 s3x s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a D cap' : Z) (K : skrep) (pad j : list byte),
      0 < D < 2^64 -> 0 < a -> 0 <= cap' < 2^31 -> (a + 56 <= D \/ D + 8 * cap' <= a) -> 8 <= 8 * cap' -> a + 56 <= bv_unsigned sp + -80 ->
      (a + 56 <= ALOWSH_LO \/ AHI_LO <= a) -> accessible m a 56 ->
      rw_cells asegs m a (sk_hdr_cells K pad) ->
      rw_cells asegs m (bv_unsigned sp + -80) (asr_frame j s7 s6 s5 s4 s3 s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) (Z_to_bv 64 0) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc ra) fc None m1 (seg_rom asegs)
          /\ munch [(a, a + 56)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ rw_cells asegs m1 a (sk_hdr_cells (mkSK (sk_elems K) D cap' (sk_sorted K) (sk_comp K) (sk_cmp_thunk K) (sk_free_thunk K) (sk_copy_thunk K) (sk_id K) (sk_did K)) pad))
        (MS (mkR (Z_to_bv 64 ASR_RA2) (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 (a + 8)) s3x (Z_to_bv 64 (a + 20)) (Z_to_bv 64 cap') (Z_to_bv 64 (Z.shiftr (a + 8) 3 + SHB)) (Z_to_bv 64 (Z.shiftr (a + 20) 3 + SHB))
                 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 ASR_RA2)) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HD POS HC DJ C8P HS NS ACC0 HDR FR MI. unfold ASR_RA2, R_sk_reserve_CRYPTO_realloc_array, SHB in *.
    replace (ret_pc (Z_to_bv 64 0x1f953c)) with (Z_to_bv 64 0x1f953c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (aword_range sp) as SPR. prep HDR. unfold asr_frame in FR.
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(a, a + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(a, a + 56)]) by (constructor; [cbn; exact NS| constructor]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    (* [comment removed for export] *)
    step. if_cases K0; zify_cond K0; [kill K0|]. clear K0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 56) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end.
    (* [comment removed for export] *)
    ck8_check ACC (a + 8). clear ACC. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC : accessible mx a 56) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW]) end.
    (* [comment removed for export] *)
    ck8_check ACC (a + 20). clear ACC. st1.
    (* [comment removed for export] *)
    do 12 step. finish.
  Qed.
End S.

(* [comment removed for export] *)
Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHx : asan_rt_hyps_x H.
  Let HH0 : asan_rt_hyps H := proj1 HHx.

  (* [comment removed for export] *)
  Lemma SKobj_rehdr_gen : forall LB m m' a K pad W,
    SKobj LB m a K -> length pad = 4%nat -> rw_cells asegs m' a (sk_hdr_cells K pad) ->
    munch W m m' -> wmono asegs m m' -> (sk_cap K = 0 \/ disjoint_from W (sk_data K) (8 * sk_cap K)) ->
    SKobj LB m' a K.
  Proof.
    intros LB m m' a K pad W SO PL HDR MU WM DJ.
    destruct SO as (_ & POS & IN & NC & CAP & SRT & EL & DAT). unfold SKobj, sk_num in *.
    split; [exists pad; split; [exact PL| exact HDR]|]. split; [exact POS|]. split; [exact IN|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact EL|].
    destruct DAT as [D0|(D1 & D2 & D3 & D4 & AR & junk & JK)]; [left; exact D0| right].
    destruct DJ as [DJ|DJ]; [lia|]. unfold zlength in *.
    split; [exact D1|]. split; [exact D2|]. split; [exact D3|]. split; [exact D4|]. split.
    - eapply u64arr_transport; [exact AR| exact MU| exact WM|]. rewrite length_map. eapply disjoint_from_mono; [exact DJ| lia].
    - exists junk. eapply rw_cells_transport; [exact JK| exact MU| exact WM|]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact DJ| lia| lia| lia].
  Qed.

  (* [comment removed for export] *)
  Local Ltac frame_facts :=
    lazymatch goal with MU1 : munch [(bv_unsigned ?sp + -80, bv_unsigned _)] ?m ?m1, HP : as_RHEAP ?H ?s ?LB _ |- _ =>
    assert (CW : Forall (aclient_write_ok H LB) [(bv_unsigned sp + -80, bv_unsigned sp)]) by (constructor; [left; cbn; lia| constructor]);
    assert (AW : Forall aconst_ok [(bv_unsigned sp + -80, bv_unsigned sp)])
      by (constructor; [apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia| constructor]);
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(bv_unsigned sp + -80, bv_unsigned sp)])
      by (constructor; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| constructor]);
    lazymatch goal with AUX : as_rauxv_ok _ m ?B, AC : ACONST m, ERR : rw_cells _ m (ATP + -164) [C4 ?errv], MF : MEMFLAG m ?v, IM : IMPL_mem m, GM : GOT_mem m,
                        WM1 : wmono _ m m1, CHN : as_chain _ m (bv_unsigned ?s0) ?CH, CHS : forall fp' ra', In _ ?CH -> _, SP16 : bv_unsigned _ mod 16 = 0,
                        PF : pf_ok _ _ (bv_unsigned ?ra) _, FR1 : rw_cells _ m1 _ (asr_frame _ _ _ _ _ _ _ _ _ _), SH1 : addressable m ?a 56, ACC0 : accessible m ?a 56 |- _ =>
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH0); [exact HP| exact MU1| exact WM1| exact CW]);
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH0); [exact AUX| exact MU1| exact WM1| exact CW]);
    assert (AC1 : ACONST m1) by (eapply ACONST_frame; [exact AC| exact MU1| exact WM1| exact AW]);
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]);
    assert (MF1 : MEMFLAG m1 v) by (eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]);
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]);
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]);
    assert (SHH1 : addressable m1 a 56)
      by (eapply addressable_transport; [exact SH1| exact MU1| exact WM1|];
          lazymatch goal with K7 : aapp a _ |- _ => pose proof (sh_aapp_range a 56 K7 ltac:(lia)) as (Sx1 & Sx2 & Sx3); unfold AHI_LO in Sx3; pose proof aceil_range; cbn; lia end);
    assert (ACC1 : accessible m1 a 56) by (eapply accessible_across; [exact ACC0| exact MU1| exact NSW]);
    assert (CH0 : as_chain H m1 (bv_unsigned s0) CH)
      by (eapply (achain_below H HH0 m m1); [exact CHN| exact CHS| exact MU1|]; constructor; [left; cbn; lia| constructor]);
    assert (CH1 : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH));
    [ eapply (ah_chain_cons H HH0); [exact CH0| lia| lia| exact SP16| lia| lia|];
      let FR2 := fresh "FR2" in
      pose proof FR1 as FR2; unfold asr_frame in FR2;
      lazymatch type of FR2 with rw_cells _ _ _ [?c0; ?c1; ?c2; ?c3; ?c4; ?c5; ?c6; ?c7; C8 s0; C8 ra] =>
        change ([c0; c1; c2; c3; c4; c5; c6; c7; C8 s0; C8 ra]) with ([c0; c1; c2; c3; c4; c5; c6; c7] ++ [C8 s0; C8 ra]) in FR2 end;
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2; destruct FR2 as [_ FR2]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2;
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -80 + 64) by lia;
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]
    | ];
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -80 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]);
    assert (SP16' : (bv_unsigned sp + -80) mod 16 = 0) by (replace (bv_unsigned sp + -80) with (bv_unsigned sp - 80) by lia; rewrite Zminus_mod, SP16; reflexivity);
    clear CW AW
    end end.

  Lemma askreserve_spec : skreserve_stmt H.
  Proof.
    unfold skreserve_stmt. intros until CH.
    intros VIS A0 A1 A2 SO CAPX HP KREL BUD BUDC AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL [SH1 SH2] (MF & IM & GM). subst a0 a1 a2.
    lazymatch type of LO with lo <= bv_unsigned sp - ?e => let v := eval cbv in e in change e with v in LO end.   (* [comment removed for export] *)
    unfold SKPUSH_COST, SK_CAP_MAX, SK_SIZE in *.
    acb. subst tp. rewrite unsigned_lit in ERR by (unfold ATP; lia).
    pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -80) by lia.
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    pose proof SO as SO'. destruct SO' as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & EL & DAT).
    pose proof (ah_blocks H HH0 _ _ _ _ HP HIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. clear K6. unfold SK_SIZE in K3, K5, K7.
    assert (AL8 : a mod 8 = 0) by (clear - K2; Z.div_mod_to_equations; lia).
    pose proof (aapp_bounds a 56 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    assert (ACC0 : accessible m a 56) by (eapply addressable_accessible; [exact SH1| lia| lia| unfold AAPP_HI; lia]).
    pose proof (ah_costs H HH0) as (CM0 & CMM & CF0 & CFM & _).
    pose proof (sk_grow_ge (sk_cap K)) as GG.
    assert (G0 : 0 <= sk_grow (sk_cap K)) by (unfold sk_grow; apply Z.div_pos; lia).
    assert (MFF : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) memflag_foot).
    { unfold memflag_foot, A_mem_inited. constructor; [cbn; unfold ALOWSH_LO; lia| constructor]. }
    assert (OBH : ashobj H LB (bv_unsigned sp + -80) a 56) by (left; exists (sk_id K, a, 56); split; [exact HIN| cbn; lia]).
    destruct DAT as [[C0 D0]|(D4 & DP & DDJ & DIN & AR & junk & JK)].
    - (* [comment removed for export] *)
      assert (N0 : sk_num K = 0) by lia.
      eapply (ahh_evt_then H HH0); [exact KREL| exact VIS| eapply asr_segA with (lo := lo);
        [exact AL8| exact HDR| exact POS| unfold SK_SIZE; lia| exact N0| exact C0| exact D0| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
      intros msF1 mo1 KREL1 MP1 (a4' & m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
      frame_facts.
      assert (XP1 : xpres H LB (bv_unsigned sp) memflag_foot m m1)
        by (eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH0| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
      (* [comment removed for export] *)
      pose proof (accalloc_spec H HH0) as CC. unfold ccalloc_stmt, czalloc_stmt_gen in CC.
      eapply (ah_seq H HH0).
      { eapply CC with (lo := lo) (B := B) (LB := LB) (s := s) (v := v) (num := 4) (size := 8) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
          [exact VIS1| reflexivity| split; [reflexivity| lia]| ..]; rewrite ?unsigned_lit by lia; change (4 * 8) with 32.
        all: first [exact HP1| exact KREL1| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity| exact SP16'| exact AC1| exact CH1| exact CHS1
                   | exact MF1| exact IM1| exact GM1
                   | unfold ASR_RA1; rewrite ?unsigned_lit by (unfold R_sk_reserve_CRYPTO_calloc; lia); eapply pf_ok_call; [exact PF|]; unfold PF_skreserve; intros x Hx; apply in_app_iff; left; exact Hx
                   | lia
                   | unfold CARRAY_STACK, CZALLOC_STACK, CMALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_zalloc, FR_CRYPTO_malloc, AMALLOC_STACK; lia
                   | match goal with |- as_Cm _ _ <= _ => pose proof (CMM 32 (8 * sk_grow (sk_cap K) + 32) ltac:(lia)); pose proof (CF0 (8 * sk_cap K) ltac:(lia)); lia end
                   | match goal with |- ?G => idtac "LEFT:" G end]. }
      intros [msF2 mo2] PO. unfold czalloc_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & D & p' & s' &
                      VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & ADDR & MF2 & IM2 & GM2 & AL2).
      rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST2, XP2 by lia. change (4 * 8) with 32 in BR, HEAP2, BLK, ADDR, AL2.
      pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4. clear BR6.
      pose proof (aapp_bounds D 32 BR7 ltac:(lia)) as (DB1 & DB2 & DB3 & DB4 & DB5). unfold AAPP_HI in DB3.
      eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in HDR1; rewrite ?sk_hdr_size in *;
        [| apply (ashobj_client_range H); exact OBH| unfold memflag_foot, A_mem_inited; constructor; [cbn; lia| constructor]].
      pose proof (afresh_apart H HH0 _ _ _ _ _ _ _ a 56 HEAP2 CSP (ashobj_client_range H _ _ _ _ OBH) ltac:(lia) ltac:(lia)) as SEP.
      assert (ACC2 : accessible m2 a 56) by (eapply (ashobj_accessible_xpres H HH0); [exact HP1| exact CSP| exact OBH| exact ACC1| exact XP2| exact MFF]).
      assert (SHH2 : addressable m2 a 56) by (eapply (ashobj_addressable_xpres H HH0); [exact HP1| intros b Hb; exact Hb| exact CSP| exact OBH| unfold AAPP_HI; lia| exact SHH1| exact XP2| exact MFF]).
      (* [comment removed for export] *)
      eapply (ahh_evt H HH0); [exact KREL2| exact VIS2| eapply asr_segA2; [lia| exact POS| clear - SEP; lia| lia| exact (aapp_not_shadowland _ _ K7)| exact ACC2| exact HDR1| exact FR1| exact MI2]|].
      intros msF3 mo3 KREL3 MP3 (m3 & VIS3 & MU3 & WM3 & MI3 & HDR3).
      assert (CW3 : Forall (aclient_write_ok H ((p', D, 32) :: LB)) [(a, a + 56)]).
      { constructor; [| constructor]. right; right; left. exists (sk_id K, a, 56). split; [right; exact HIN| cbn; lia]. }
      unfold skreserve_post. cbn [cfg_ms cfg_model].
      exists u0, u1, u2, (Z_to_bv 64 0), b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, s', ((p', D, 32) :: LB).
      exists (sk_after_reserve K D 4 p'), D, 4, p'.
      split; [exact VIS3|]. split; [exact KREL3|].
      split; [eapply (ah_mpres_trans H HH0); [| exact MP3]; eapply (ah_mpres_trans H HH0); [exact MP1| exact MP2]|].
      split; [exact MI3|].
      split. { eapply ACONST_frame; [exact AC2| exact MU3| exact WM3|]. constructor; [eapply aconst_ok_aapp; [exact K7| cbn; lia| cbn; lia]| constructor]. }
      split. { apply (rw_cells_transport asegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
               apply (stk_transport_disjoint asegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
               unfold asr_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
      split. { rewrite unsigned_lit in ERR2 |- * by (unfold ATP; lia). eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]. }
      split. { eapply (ah_rauxv_frame H HH0); [exact AUX2| exact MU3| exact WM3| exact CW3]. }
      split; [reflexivity|].
      split. { right; left. cbn. split; [exact C0| split; reflexivity]. }
      split. { unfold sk_num. cbn. unfold sk_num in N0. lia. }
      split. { eapply (ah_RHEAP_frame H HH0); [exact HEAP2| exact MU3| exact WM3| exact CW3]. }
      split.
      { unfold SKobj, sk_num. cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk sk_id sk_did sk_after_reserve].
        unfold sk_num in N0, NC.
        split; [exists pad; split; [exact PL| exact HDR3]|]. split; [exact POS|]. split; [right; exact HIN|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [exact EL|].
        right. split; [lia|]. split; [lia|]. split; [unfold SK_SIZE; clear - SEP; lia|]. split; [left; reflexivity|]. split.
        - assert (E0 : sk_elems K = []) by (destruct (sk_elems K); [reflexivity| unfold zlength in N0; cbn [length] in N0; lia]).
          rewrite E0. cbn [map]. apply u64arr_nil. lia.
        - exists (zeros (Z.to_nat 32)). rewrite N0. replace (D + 8 * 0) with D by lia. change (Z.to_nat (8 * (4 - 0))) with (Z.to_nat 32).
          eapply rw_cells_transport; [exact BLK| exact MU3| exact WM3| cbn; clear - SEP; lia]. }
      split.
      { unfold SK_shad, SK_SIZE. cbn [sk_cap sk_data sk_after_reserve]. split.
        - eapply addressable_transport; [exact SHH2| exact MU3| exact WM3|].
          pose proof (aapp_disjoint_sh a 56 a 56 K7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS. cbn [disjoint_from fst snd]. split; [clear - DS; lia| exact I].
        - intros _. change (8 * 4) with 32. eapply addressable_transport; [exact ADDR| exact MU3| exact WM3|].
          pose proof (aapp_disjoint_sh a 56 D 32 K7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS. cbn [disjoint_from fst snd]. split; [clear - DS; lia| exact I]. }
      split.
      { unfold ASK_foot, SK_foot. cbn [sk_cap sk_data sk_after_reserve Z.eqb app]. unfold SK_SIZE. change (8 * 4) with 32.
        apply (xpres_cons_block H); [| intros q Hq; apply rin_ivs_app; right; cbn; lia| intros q Hq; apply rin_ivs_app; right; cbn; lia].
        eapply xpres_trans; [| eapply xpres_trans].
        - eapply (xpres_X_mono H); [exact XP1| intros q Hq; apply rin_ivs_app; left; exact Hq].
        - eapply (xpres_weaken H LB LB _ _ memflag_foot); [exact XP2| lia| auto| intros q Hq; apply rin_ivs_app; left; exact Hq].
        - eapply (xpres_of_munch_fresh H HH0); [exact HEAP2| lia| exact MU3| exact WM3|].
          constructor; [right; right; intros q Hq; apply rin_ivs_app; right; cbn; cbn in Hq; lia| constructor]. }
      split.
      { exists 1. split; [| destruct MF as (fb0 & _ & _ & V01); lia].
        split; [eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia| exact MF2]|].
        split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
        eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]. }
      unfold SKPUSH_COST. rewrite C0. unfold sk_grow. change (8 * (0 * 8 / 5) + 32) with 32. change (8 * 0) with 0. pose proof (CF0 0 ltac:(lia)). lia.
    - pose proof (rw_cells_bound _ _ _ _ JK) as JB. cbn [cells_size csize Nat.add] in JB.
      pose proof (ah_blocks H HH0 _ _ _ _ HP DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7. clear E6.
      pose proof (aapp_bounds (sk_data K) (8 * sk_cap K) E7 ltac:(lia)) as (EB1 & EB2 & EB3 & EB4 & EB5). unfold AAPP_HI in EB3.
      pose proof (u64arr_bound _ _ _ _ AR) as ARB. rewrite length_map in ARB. unfold sk_num, zlength in *.
      specialize (SH2 ltac:(lia)).
      destruct (Z_lt_le_dec (Z.of_nat (length (sk_elems K))) (sk_cap K)) as [ROOM|FULL].
      + (* [comment removed for export] *)
        eapply (ahh_evt H HH0); [exact KREL| exact VIS| eapply asr_segB with (lo := lo);
          [exact AL8| exact HDR| exact POS| unfold SK_SIZE; lia| unfold sk_num, zlength; lia| unfold sk_num, zlength; lia| lia| lia| lia| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
        intros msF1 mo1 KREL1 MP1 (t0' & a1' & a3' & a4' & a5' & m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & HDR1).
        assert (CW : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp)]) by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
        unfold skreserve_post. cbn [cfg_ms cfg_model].
        exists t0', t1, t2, a1', (Z_to_bv 64 0), a3', a4', a5', a6, a7, t3, t4, t5, t6, m1, errv, s, LB.
        exists (sk_after_reserve K (sk_data K) (sk_cap K) (sk_did K)), (sk_data K), (sk_cap K), (sk_did K).
        split; [exact VIS1|]. split; [exact KREL1|]. split; [exact MP1|]. split; [exact MI1|].
        split. { eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil].
                 apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
        split; [exact ST1|].
        split. { rewrite unsigned_lit by (unfold ATP; lia). eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]. }
        split. { eapply (ah_rauxv_frame H HH0); [exact AUX| exact MU1| exact WM1| exact CW]. }
        split; [reflexivity|].
        split. { left. cbn. unfold sk_num, zlength. repeat split; lia. }
        split. { unfold sk_num, zlength. cbn. lia. }
        split. { eapply (ah_RHEAP_frame H HH0); [exact HP| exact MU1| exact WM1| exact CW]. }
        split.
        { destruct K as [el da ca so co ct ft cpt id did]. cbn in *.
          eapply (SKobj_rehdr_gen LB m m1); [exact SO| exact PL| exact HDR1| exact MU1| exact WM1| right; cbn; lia]. }
        split.
        { unfold SK_shad, SK_SIZE. cbn [sk_cap sk_data sk_after_reserve]. split; [| intros _].
          - eapply addressable_transport; [exact SH1| exact MU1| exact WM1|].
            pose proof (sh_aapp_range a 56 K7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3. cbn [disjoint_from fst snd]. split; [lia| exact I].
          - eapply addressable_transport; [exact SH2| exact MU1| exact WM1|].
            pose proof (sh_aapp_range (sk_data K) (8 * sk_cap K) E7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3. cbn [disjoint_from fst snd]. split; [lia| exact I]. }
        split.
        { eapply (xpres_of_munch H s LB _ _ _ m m m1); [exact HH0| exact HP| exact MU1| exact WM1|]. apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]. }
        split.
        { exists v. split; [| lia]. split; [eapply MEMFLAG_across; [exact MU1| exact WM1| unfold A_mem_inited; cbn; lia| exact MF]|].
          split; [eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]|].
          eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]. }
        pose proof (CM0 (SKPUSH_COST K) ltac:(unfold SKPUSH_COST; lia)). pose proof (CF0 (8 * sk_cap K) ltac:(lia)). lia.
      + (* [comment removed for export] *)
        assert (FULLE : Z.of_nat (length (sk_elems K)) = sk_cap K) by lia.
        specialize (GG ltac:(lia)). destruct GG as [GG1 GG2].
        assert (GG3 : 5 * sk_grow (sk_cap K) <= sk_cap K * 8) by (unfold sk_grow; apply Z.mul_div_le; lia).
        eapply (ahh_evt_then H HH0); [exact KREL| exact VIS| eapply asr_segC with (lo := lo);
          [exact AL8| exact HDR| exact POS| unfold SK_SIZE; lia| unfold sk_num, zlength; lia| unfold SK_CAP_MAX; lia| lia| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
        intros msF1 mo1 KREL1 MP1 (m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
        frame_facts.
        apply (u64arr_transport asegs _ m m1 _ _ AR) in MU1 as AR1; [| exact WM1| rewrite length_map; cbn; lia].
        (* [comment removed for export] *)
        assert (JN : junk = []).
        { destruct JK as [[WF _] _]. cbn in WF. destruct junk; [reflexivity| cbn in WF; lia]. }
        subst junk.
        pose proof (u64arr_CB _ _ _ _ AR1) as OBS. rewrite length_map in OBS.
        replace (8 * length (sk_elems K))%nat with (Z.to_nat (8 * sk_cap K)) in OBS by lia.
        assert (SHD1 : addressable m1 (sk_data K) (8 * sk_cap K)).
        { eapply addressable_transport; [exact SH2| exact MU1| exact WM1|].
          pose proof (sh_aapp_range (sk_data K) (8 * sk_cap K) E7 ltac:(lia)) as (S1 & S2 & S3). unfold AHI_LO in S3. pose proof aceil_range.
          cbn [disjoint_from fst snd]. split; [lia| exact I]. }
        assert (XP1 : xpres H LB (bv_unsigned sp) memflag_foot m m1)
          by (eapply (xpres_of_munch H s LB _ memflag_foot _ m m m1); [exact HH0| exact HP| exact MU1| exact WM1|]; constructor; [left; cbn; lia| constructor]).
        (* [comment removed for export] *)
        pose proof (acrealloc_array_spec H HHx) as CR. unfold crealloc_array_stmt, crealloc_stmt_gen in CR.
        eapply (ah_seq H HH0).
        { eapply CR with (lo := lo) (B := B) (LB := LB) (s := s) (p := sk_did K) (A := sk_data K) (old := 8 * sk_cap K)
                           (num := sk_cap K * 8 / 5) (size := 8) (obs := u64s (map wz (sk_elems K))) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
            [exact VIS1| reflexivity| unfold sk_grow; reflexivity| split; [reflexivity| lia]| ..]; rewrite ?unsigned_lit by lia.
          all: first [exact HP1| exact KREL1| exact DIN| exact OBS| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| reflexivity| exact SP16'| exact AC1| exact CH1| exact CHS1
                     | exact SHD1| exact IM1| exact GM1
                     | unfold ASR_RA2; rewrite ?unsigned_lit by (unfold R_sk_reserve_CRYPTO_realloc_array; lia); eapply pf_ok_call; [exact PF|]; unfold PF_skreserve; intros x Hx; apply in_app_iff; right; exact Hx
                     | unfold AREALLOC_MAX; lia
                     | match goal with |- zlength _ = _ => unfold zlength; rewrite u64s_length, length_map; lia end
                     | match goal with |- as_Cm _ _ + _ <= _ => pose proof (CMM (sk_cap K * 8 / 5 * 8) (8 * sk_grow (sk_cap K) + 32) ltac:(unfold sk_grow; lia)); lia end
                     | match goal with |- lb_bytes _ + _ <= _ => unfold sk_grow in BUD; lia end
                     | lia
                     | unfold CREALLOC_ARRAY_STACK, CREALLOC_STACK, FR_CRYPTO_array, FR_CRYPTO_realloc, AREALLOC_STACK; lia
                     | match goal with |- ?G => idtac "LEFT:" G end]. }
        intros [msF2 mo2] PO. unfold crealloc_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & errv2 & A' & junk' & p' & s' &
                        VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & BR & HEAP2 & BLK & ADDR & IM2 & GM2 & AL2).
        rewrite (unsigned_lit (bv_unsigned sp + -80)) in ST2, XP2 by lia.
        set (g := sk_cap K * 8 / 5) in *.
        assert (Eg : g = sk_grow (sk_cap K)) by (unfold g, sk_grow; reflexivity). rewrite <- Eg in *.
        replace (g * 8) with (8 * g) in BR, HEAP2, BLK, ADDR, AL2 by lia.
        pose proof BR as (BR1 & BR2 & BR3 & BR4 & BR5 & BR6 & BR7). unfold AIMG_TOP in BR4. clear BR6.
        pose proof (aapp_bounds A' (8 * g) BR7 ltac:(lia)) as (DB1 & DB2 & DB3 & DB4 & DB5). unfold AAPP_HI in DB3.
        (* [comment removed for export] *)
        assert (HINR : In (sk_id K, a, 56) (as_lb_remove H (sk_did K) LB)).
        { apply (proj2 (proj2 (proj2 (alb_remove_exact H HH0 _ _ _ _ (ah_nodup H HH0 _ _ _ HP) DIN)) (sk_id K, a, 56))).
          split; [exact HIN|]. cbn. intros E.
          pose proof (nodup_id_inj LB _ _ (ah_nodup H HH0 _ _ _ HP) HIN DIN E) as EE. injection EE as EA EB. lia. }
        assert (SUBR : forall b, In b (as_lb_remove H (sk_did K) LB) -> In b LB) by (intros b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH0))); exact Hb).
        assert (OBHR : ashobj H (as_lb_remove H (sk_did K) LB) (bv_unsigned sp + -80) a 56) by (left; exists (sk_id K, a, 56); split; [exact HINR| cbn; lia]).
        eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in FR1; [| left; cbn; lia| constructor].
        eapply (xpres_rw_cells' H _ _ _ _ _ _ _ XP2) in HDR1; rewrite ?sk_hdr_size in *; [| apply (ashobj_client_range H); exact OBHR| constructor].
        pose proof (afresh_apart H HH0 _ _ _ _ _ _ _ a 56 HEAP2 CSP (ashobj_client_range H _ _ _ _ OBHR) ltac:(lia) ltac:(lia)) as SEP.
        assert (ACC2 : accessible m2 a 56) by (eapply (ashobj_accessible_xpres_sub H HH0); [exact HP1| exact SUBR| exact CSP| exact OBHR| exact ACC1| exact XP2| constructor]).
        assert (SHH2 : addressable m2 a 56) by (eapply (ashobj_addressable_xpres H HH0); [exact HP1| exact SUBR| exact CSP| exact OBHR| unfold AAPP_HI; lia| exact SHH1| exact XP2| constructor]).
        (* [comment removed for export] *)
        eapply (ahh_evt H HH0); [exact KREL2| exact VIS2| eapply asr_segC2;
          [lia| exact POS| lia| clear - SEP; lia| lia| lia| exact (aapp_not_shadowland _ _ K7)| exact ACC2| exact HDR1| exact FR1| exact MI2]|].
        intros msF3 mo3 KREL3 MP3 (m3 & VIS3 & MU3 & WM3 & MI3 & HDR3).
        assert (CW3 : Forall (aclient_write_ok H ((p', A', 8 * g) :: as_lb_remove H (sk_did K) LB)) [(a, a + 56)]).
        { apply Forall_cons; [| apply Forall_nil]. right; right; left. exists (sk_id K, a, 56). split; [right; exact HINR| cbn; lia]. }
        unfold skreserve_post. cbn [cfg_ms cfg_model].
        exists u0, u1, u2, (Z_to_bv 64 0), b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m3, errv2, s', ((p', A', 8 * g) :: as_lb_remove H (sk_did K) LB).
        exists (sk_after_reserve K A' g p'), A', g, p'.
        split; [exact VIS3|]. split; [exact KREL3|].
        split; [eapply (ah_mpres_trans H HH0); [| exact MP3]; eapply (ah_mpres_trans H HH0); [exact MP1| exact MP2]|].
        split; [exact MI3|].
        split. { eapply ACONST_frame; [exact AC2| exact MU3| exact WM3|]. apply Forall_cons; [eapply aconst_ok_aapp; [exact K7| cbn; lia| cbn; lia]| apply Forall_nil]. }
        split. { apply (rw_cells_transport asegs _ m2 m3 _ _ FR1) in MU3 as FR3; [| exact WM3| cbn; lia].
                 apply (stk_transport_disjoint asegs _ m2 m3 _ _ ST2) in MU3 as ST3; [| exact WM3| cbn; lia].
                 unfold asr_frame in FR3. release_frame FR3 ST3 (bv_unsigned sp). exact ST3. }
        split. { rewrite unsigned_lit in ERR2 |- * by (unfold ATP; lia). eapply errno_across; [exact ERR2| exact MU3| exact WM3| unfold ATP; cbn; lia]. }
        split. { eapply (ah_rauxv_frame H HH0); [exact AUX2| exact MU3| exact WM3| exact CW3]. }
        split; [reflexivity|].
        split. { right; right. cbn. split; [lia|]. split; [unfold sk_num, zlength; lia|]. split; [exact Eg|].
                 eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply (alb_remove_perm H HH0); [exact HP| exact DIN]. }
        split. { unfold sk_num, zlength. cbn. lia. }
        split. { eapply (ah_RHEAP_frame H HH0); [exact HEAP2| exact MU3| exact WM3| exact CW3]. }
        split.
        { (* [comment removed for export] *)
          rewrite Z.min_l in BLK by lia. rewrite firstn_all2 in BLK by (rewrite u64s_length, length_map; lia).
          change (rw_cells asegs m2 A' ([CB (Z.to_nat (8 * sk_cap K)) (u64s (map wz (sk_elems K)))] ++ [CB (Z.to_nat (8 * g - 8 * sk_cap K)) junk'])) in BLK.
          apply (proj1 (rw_cells_app _ _ _ _ _)) in BLK. destruct BLK as [BK BJ]. cbn [cells_size csize Nat.add] in BJ.
          unfold SKobj, sk_num. cbn [sk_elems sk_data sk_cap sk_sorted sk_comp sk_cmp_thunk sk_free_thunk sk_copy_thunk sk_id sk_did sk_after_reserve].
          split; [exists pad; split; [exact PL| exact HDR3]|]. split; [exact POS|]. split; [right; exact HINR|].
          unfold zlength. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact EL|].
          right. split; [lia|]. split; [lia|]. split; [unfold SK_SIZE; clear - SEP; lia|]. split; [left; reflexivity|]. split.
          - eapply u64arr_transport; [| exact MU3| exact WM3| rewrite length_map; cbn; clear - SEP FULLE GG1; lia].
            apply u64arr_of_CB. replace (8 * length (map wz (sk_elems K)))%nat with (Z.to_nat (8 * sk_cap K)) by (rewrite length_map; lia). exact BK.
          - exists junk'. replace (A' + 8 * Z.of_nat (length (sk_elems K))) with (A' + Z.of_nat (Z.to_nat (8 * sk_cap K) + 0)) by lia.
            replace (Z.to_nat (8 * (g - Z.of_nat (length (sk_elems K))))) with (Z.to_nat (8 * g - 8 * sk_cap K)) by lia.
            eapply rw_cells_transport; [exact BJ| exact MU3| exact WM3| cbn; clear - SEP FULLE GG1 GG2; lia]. }
        split.
        { unfold SK_shad, SK_SIZE. cbn [sk_cap sk_data sk_after_reserve]. split; [| intros _].
          - eapply addressable_transport; [exact SHH2| exact MU3| exact WM3|].
            pose proof (aapp_disjoint_sh a 56 a 56 K7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS. cbn [disjoint_from fst snd]. split; [clear - DS; lia| exact I].
          - eapply addressable_transport; [exact ADDR| exact MU3| exact WM3|].
            pose proof (aapp_disjoint_sh a 56 A' (8 * g) K7 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as DS. cbn [disjoint_from fst snd]. split; [clear - DS; lia| exact I]. }
        split.
        { unfold ASK_foot, SK_foot. cbn [sk_cap sk_data sk_after_reserve]. replace (g =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app]. unfold SK_SIZE.
          apply (xpres_cons_block H); [| intros q Hq; apply rin_ivs_app; right; cbn; lia| intros q Hq; apply rin_ivs_app; right; cbn; lia].
          eapply xpres_trans; [| eapply xpres_trans].
          - eapply (xpres_weaken H LB _ _ _ memflag_foot); [exact XP1| lia| exact SUBR| intros q Hq; apply rin_ivs_app; left; exact Hq].
          - eapply (xpres_weaken H _ _ _ _ []); [exact XP2| lia| auto| intros q Hq; destruct Hq].
          - eapply (xpres_of_munch_fresh H HH0); [exact HEAP2| lia| exact MU3| exact WM3|].
            apply Forall_cons; [right; right; intros q Hq; apply rin_ivs_app; right; cbn; cbn in Hq; lia| apply Forall_nil]. }
        split.
        { exists v. split; [| lia].
          split. { eapply MEMFLAG_across; [exact MU3| exact WM3| unfold A_mem_inited; cbn; lia|].
                   eapply (MEMFLAG_apres H); [apply (xpres_nil_apres H); exact XP2| exact MF1]. }
          split; [eapply IMPL_across; [exact MU3| exact WM3| unfold A_malloc_impl; cbn; lia| exact IM2]|].
          eapply GOT_across; [exact MU3| exact WM3| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM2]. }
        unfold SKPUSH_COST. rewrite <- Eg.
        pose proof (CMM (8 * g) (8 * g + 32) ltac:(lia)). lia.
  Qed.
End W.
