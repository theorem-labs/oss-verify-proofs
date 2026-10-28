(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr Bytes ZBridge SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap AsCall AsCallX ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface
  ECH_AStmt_C1 ECH_AStmt_C5 ECH_AKit ECH_AsKit ECH_AC1_malloc ECH_AC1_free ECH_AC5_small.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import N6_tac.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition APF_HEAD : Z := 0x1faa90.      (* [comment removed for export] *)
Definition APF_TAIL : Z := 0x1fab28.      (* [comment removed for export] *)
Definition APF_RA_ELEM : Z := 0x1faaf4.   (* [comment removed for export] *)
Definition APF_RA_FREE : Z := 0x1f964c.   (* [comment removed for export] *)
Definition APF_FILE : Z := 0x4aa54.       (* [comment removed for export] *)
Definition ASHB : Z := 0x7fff8000.
Definition apf_frame (j : list byte) (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
Definition asf_frame (s2 s1 s0 ra : word) : list cell := [C8 s2; C8 s1; C8 s0; C8 ra].

Section S.
  Context {HCEIL : HeapCeil}.
  Local Ltac kill K := exfalso; revert K; rewrite ?unsigned_lit, ?signed_lit by lia; lia.
  (* [comment removed for export] *)
  Local Ltac kill_lts K :=
    exfalso; first [ apply Bool.andb_false_iff in K; destruct K as [K|K]; apply Z.ltb_ge in K; lia
                   | apply Bool.andb_true_iff in K; destruct K as [K K']; apply Z.ltb_lt in K; lia ].
  Local Ltac reacc_with ACC' MU NSW ACC :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      lazymatch type of ACC' with id (accessible _ ?a ?n) =>
        assert (ACC : accessible mx a n) by (unfold id in ACC'; eapply accessible_across; [exact ACC'| exact MU| exact NSW])
      end end.

  (* [comment removed for export] *)
  Lemma apf_segL :
    forall (ra sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a FN i p lo : Z) (K : skrep) (pad : list byte),
      rw_cells asegs m a (sk_hdr_cells K pad) -> u64arr asegs m (sk_data K) (map wz (sk_elems K)) ->
      nth_error (sk_elems K) (Z.to_nat i) = Some p -> 0 <= i -> 0 < p < 2^64 -> 0 < sk_data K -> sk_data K mod 16 = 0 -> sk_data K + 8 * sk_cap K <= lo -> sk_num K <= sk_cap K ->
      is_sk_freefunc_thunk (sk_free_thunk K) -> 0 <= FN < 2^64 -> FN mod 2 = 0 ->
      0 < a -> a + SK_SIZE <= lo ->
      accessible m a SK_SIZE -> accessible m (sk_data K) (8 * sk_cap K) ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 16 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 m1,
          ms' = MS (mkR (Z_to_bv 64 APF_RA_ELEM) sp gp tp u0 u1 u2 s0 (Z_to_bv 64 a) (Z_to_bv 64 p) b1 b2 b3 b4 b5 b6 b7
                       (Z_to_bv 64 FN) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 (a + 40)) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr a 3 + ASHB))
                       (Z_to_bv 64 (i * 8)) (Z_to_bv 64 i) s10 (Z_to_bv 64 (Z.shiftr (a + 8) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (a + 40) 3 + ASHB)) u3 u4 u5 u6)
                   F (Z_to_bv 64 FN) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp) /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 FN) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 (a + 40)) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr a 3 + ASHB))
                 (Z_to_bv 64 (i * 8)) (Z_to_bv 64 i) s10 (Z_to_bv 64 (Z.shiftr (a + 8) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (a + 40) 3 + ASHB)) t3 t4 t5 t6)
            F (Z_to_bv 64 APF_HEAD) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros HDR ARR NTH I0 PR DP DAL DB NC TH FNR FNE POS BL ACCa0 ACCd0 ST CEIL LO MI.
    unfold APF_HEAD, APF_RA_ELEM, ASHB. unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACCa0 as (_ & AHIa & _). pose proof ACCd0 as (_ & AHId & _). unfold AAPP_HI in AHIa, AHId.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    pose proof (u64arr_bound _ _ _ _ ARR) as ARB. rewrite length_map in ARB. unfold sk_num, zlength in NC.
    pose proof (nth_error_lt _ _ _ NTH) as IL.
    (* [comment removed for export] *)
    ck8_check ACCa0 (a + 8).
    st1. zstep. step. ub_dead. zstep. zstep. zstep. rewrite ub_nullcons by lia. step. if_lit. step. ub_dead.
    zstep. zstep. ubal_by DAL. step. if_lit. zstep. zstep. ck8_check ACCd0 (sk_data K + i * 8).
    pose proof (u64arr_read asegs _ _ _ i (wz p) (wa (sk_data K + i * 8)) ARR ltac:(rewrite nth_error_map, NTH; reflexivity) ltac:(lia) ltac:(f_equal; lia)) as RD. unfold wz in RD. step. clear RD.
    step. try (if_cases K0; zify_cond K0; [kill K0|]; clear K0).
    (* [comment removed for export] *)
    ck8_check ACCa0 (a + 40).
    destruct TH as [E | [E | E]]; rewrite E in *; unfold P_sk_OSSL_ECHEXT_freefunc_thunk, P_sk_OSSL_ECHSTORE_ENTRY_freefunc_thunk, P_sk_X509_BUFFER_freefunc_thunk in *.
    all: st1; step; try if_false; step; step.
    (* [comment removed for export] *)
    all: carve_frame 16%nat ST; do 4 st1; step; step; st1; st1; step; step.
    all: replace (ret_pc (Z_to_bv 64 FN)) with (Z_to_bv 64 FN) by (symmetry; apply ret_pc_even; [lia| exact FNE]).
    all: release_frame FR ST (bv_unsigned sp); finish.
    all: unfold sk_hdr_cells, wz; rewrite E; assumption.
  Qed.

  (* [comment removed for export] *)
  Local Ltac entry ST ACC' MU NSW :=
    carve_frame 112%nat ST;
    do 15 step; step;
    first [ let K0 := fresh "K0" in (if_cases K0; zify_cond K0; [kill K0|]; clear K0) | idtac ];
    let ACC := fresh "ACC" in
    reacc_with ACC' MU NSW ACC;
    (* [comment removed for export] *)
    step; step; ubal_any; step; if_lit; step; step; step; step; zstep; zstep;
    lazymatch type of ACC with accessible _ ?a _ => ck8_check ACC a end; clear ACC;
    (* [comment removed for export] *)
    st1; rewrite ?sx32_wz by lia; unfold wz.

  (* [comment removed for export] *)
  Lemma apf_seg0_more :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a FN lo : Z) (K : skrep) (pad : list byte),
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < sk_num K <= 2^20 -> 0 < a -> a mod 16 = 0 -> a + SK_SIZE <= lo ->
      accessible m a SK_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 112 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (u0 b1 u9 : word) m1 j,
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) u0 b1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 FN) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 (a + 40)) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr a 3 + ASHB))
                       (Z_to_bv 64 (0 * 8)) (Z_to_bv 64 0) u9 (Z_to_bv 64 (Z.shiftr (a + 8) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (a + 40) 3 + ASHB))
                       t3 t4 t5 t6)
                   F (Z_to_bv 64 APF_HEAD) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -112)
          /\ rw_cells asegs m1 (bv_unsigned sp + -112) (apf_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 FN) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros HDR NR POS A16 BL ACC0 GSB SHB0 ST CEIL LO MI. unfold P_OPENSSL_sk_pop_free, APF_HEAD, apf_frame, ASHB.
    assert (AL : a mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    pose proof HDR as HDR0. unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    entry ST ACC' MU NSW.
    step. if_cases K0; zify_cond K0; try (kill_lts K0); try clear K0.
    (* [comment removed for export] *)
    step. step. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    finish. all: try exact FR. all: unfold sk_hdr_cells, wz; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma apf_seg0_none :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad : list byte),
      rw_cells asegs m a (sk_hdr_cells K pad) -> sk_num K = 0 -> 0 < a -> a mod 16 = 0 -> a + SK_SIZE <= lo ->
      accessible m a SK_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - 112 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists (u0 u9 : word) m1 j,
          ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) u0 a1 a2 a3 a4 a5 a6 a7
                       a1 s3 s4 (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr a 3 + ASHB)) s7 s8 u9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 APF_TAIL) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -112)
          /\ rw_cells asegs m1 (bv_unsigned sp + -112) (apf_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 P_OPENSSL_sk_pop_free) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros HDR NR POS A16 BL ACC0 GSB SHB0 ST CEIL LO MI. unfold P_OPENSSL_sk_pop_free, APF_TAIL, apf_frame, ASHB.
    assert (AL : a mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    pose proof HDR as HDR0. unfold sk_hdr_cells, wz in HDR. rewrite NR in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    entry ST ACC' MU NSW.
    step. try if_true.
    finish. all: try exact FR.
    all: unfold sk_hdr_cells, wz; rewrite NR; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma apf_segN_more :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a i : Z) (K : skrep) (pad : list byte),
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 <= i -> i + 1 < sk_num K -> sk_num K <= 2^20 -> accessible m a SK_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0,
          ms' = MS (mkR (Z_to_bv 64 APF_RA_ELEM) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) u0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 (Z.shiftr a 3 + ASHB)) (Z_to_bv 64 ((i + 1) * 8)) (Z_to_bv 64 (i + 1)) s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 APF_HEAD) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 APF_RA_ELEM) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 (Z_to_bv 64 (Z.shiftr a 3 + ASHB)) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 i) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 APF_RA_ELEM)) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros HDR I0 IL NR ACC MI. unfold APF_RA_ELEM, APF_HEAD, ASHB.
    replace (ret_pc (Z_to_bv 64 0x1faaf4)) with (Z_to_bv 64 0x1faaf4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold sk_hdr_cells, wz in HDR. pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
    step. ck8_check ACC a. st1. rewrite sx32_wz by lia. unfold wz. zstep. zstep.
    step. if_cases K0; zify_cond K0; try (kill K0); try clear K0.
    replace (i * 8 + 8) with ((i + 1) * 8) by lia.
    apply evt_done. eexists. reflexivity.
  Qed.
  Lemma apf_segN_last :
    forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a i : Z) (K : skrep) (pad : list byte),
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 <= i -> i + 1 = sk_num K -> sk_num K <= 2^20 -> accessible m a SK_SIZE -> mem_inv asegs m ->
      evt asegs (fun ms' => exists u0 u3 u4,
          ms' = MS (mkR (Z_to_bv 64 APF_RA_ELEM) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) u0 a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 (Z_to_bv 64 (Z.shiftr a 3 + ASHB)) u3 u4 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 APF_TAIL) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 APF_RA_ELEM) sp gp tp t0 t1 t2 s0 (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 (Z_to_bv 64 (Z.shiftr a 3 + ASHB)) (Z_to_bv 64 (i * 8)) (Z_to_bv 64 i) s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 APF_RA_ELEM)) fc None m (seg_rom asegs)).
  Proof.
    intros until pad. intros HDR I0 IL NR ACC MI. unfold APF_RA_ELEM, APF_TAIL, ASHB.
    replace (ret_pc (Z_to_bv 64 0x1faaf4)) with (Z_to_bv 64 0x1faaf4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    unfold sk_hdr_cells, wz in HDR. pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    pose proof ACC as (_ & AHI & _). unfold AAPP_HI in AHI.
    step. ck8_check ACC a. st1. rewrite sx32_wz by lia. unfold wz. zstep. zstep.
    step. if_cases K0; zify_cond K0; try (kill K0); try clear K0.
    step. apply evt_done. do 3 eexists. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma apf_tail1 :
    forall (rax sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a lo : Z) (K : skrep) (pad j : list byte),
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < a -> a mod 16 = 0 -> a + SK_SIZE <= lo -> accessible m a SK_SIZE ->
      rw_cells asegs m AGOT_SHBASE [C8 (wz ASHBASE_CELL)] -> rw_cells asegs m ASHBASE_CELL [C8 (wz ASHADOW_BASE)] ->
      rw_cells asegs m (bv_unsigned sp + -112) (apf_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      stk asegs m lo (bv_unsigned sp + -112) -> aceil <= lo -> lo <= bv_unsigned sp - 112 -> mem_inv asegs m ->
      evt asegs (fun ms' => exists m1,
          ms' = MS (mkR (Z_to_bv 64 APF_RA_FREE) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 sp (Z_to_bv 64 a) (Z_to_bv 64 (sk_data K)) (Z_to_bv 64 APF_FILE) (Z_to_bv 64 496) a3 a4 a5 a6 a7
                       (Z_to_bv 64 APF_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_CRYPTO_free) fc None m1 (seg_rom asegs)
          /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
          /\ stk asegs m1 lo (bv_unsigned sp + -32)
          /\ rw_cells asegs m1 (bv_unsigned sp + -32) (asf_frame s2 s1 s0 ra)
          /\ rw_cells asegs m1 a (sk_hdr_cells K pad))
        (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 s2x s3x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
            F (Z_to_bv 64 APF_TAIL) fc None m (seg_rom asegs)).
  Proof.
    intros until j. intros HDR POS A16 BL ACC0 GSB SHB0 FR ST CEIL LO MI.
    unfold APF_TAIL, APF_RA_FREE, APF_FILE, P_CRYPTO_free, P_OPENSSL_sk_free, apf_frame, asf_frame, ASHB.
    assert (AL : a mod 8 = 0) by (clear - A16; Z.div_mod_to_equations; lia).
    pose proof HDR as HDR0. unfold sk_hdr_cells, wz in HDR.
    pose proof (rw_cells_bound _ _ _ _ HDR) as HB. cbn [cells_size csize Nat.add] in HB. unfold SK_SIZE in *.
    unfold AGOT_SHBASE, ASHBASE_CELL, wz in GSB, SHB0. rewrite ASHADOW_BASE_val in SHB0.
    acb. pose proof (aword_range sp) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof ACC0 as (_ & AHI & _). unfold AAPP_HI in AHI.
    unfold apf_frame in FR. do 16 step.
    release_frame FR ST (bv_unsigned sp).
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned sp)])
      by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
    pose proof ACC0 as ACC'. clear ACC0. change (id (accessible m a 56)) in ACC'.
    carve_frame 32%nat ST.
    do 6 step. step.
    first [ let K0 := fresh "K0" in (if_cases K0; zify_cond K0; [kill K0|]; clear K0) | idtac ].
    reacc_with ACC' MU NSW ACC.
    step. step. ubal_any. step. if_lit.
    step. step. step. zstep. zstep. zstep. ck8_check ACC (a + 8).
    st1. do 5 step.
    finish. all: try exact FR. all: unfold sk_hdr_cells, wz; assumption.
  Qed.
  (* [comment removed for export] *)
  Lemma apf_tail2 :
    forall (sp gp tp t0 t1 t2 s0x a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 ra s0 s1 s2 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (a : Z),
      rw_cells asegs m (bv_unsigned sp + -32) (asf_frame s2 s1 s0 ra) -> mem_inv asegs m ->
      evt asegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 a) (Z_to_bv 64 APF_FILE) (Z_to_bv 64 497) a3 a4 a5 a6 a7
                                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 P_CRYPTO_free) fc None m (seg_rom asegs))
        (MS (mkR (Z_to_bv 64 APF_RA_FREE) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0x (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 APF_FILE) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (ret_pc (Z_to_bv 64 APF_RA_FREE)) fc None m (seg_rom asegs)).
  Proof.
    intros until a. intros FR MI.
    replace (ret_pc (Z_to_bv 64 APF_RA_FREE)) with (Z_to_bv 64 APF_RA_FREE) by (symmetry; apply ret_pc_even; [unfold APF_RA_FREE; lia| reflexivity]).
    unfold APF_RA_FREE, APF_FILE, P_CRYPTO_free.
    pose proof (aword_range sp) as SPR. unfold asf_frame in FR.
    do 9 step. apply evt_done. reflexivity.
  Qed.
End S.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_ids_excl : forall (l1 l2 : list block) b, List.NoDup (map blk_id (l1 ++ l2)) -> In b l1 -> In b l2 -> False.
Proof.
  induction l1 as [|c l1 IH]; intros l2 b ND H1 H2; [destruct H1|]. cbn in ND. inversion ND as [|x l NI ND']; subst.
  destruct H1 as [->|H1]; [| exact (IH _ _ ND' H1 H2)]. apply NI. rewrite map_app. apply in_or_app. right. apply in_map. exact H2.
Qed.
Lemma nodup_ids_drop_mid : forall (l1 l2 l3 : list block), List.NoDup (map blk_id (l1 ++ l2 ++ l3)) -> List.NoDup (map blk_id (l1 ++ l3)).
Proof.
  intros l1 l2 l3 ND. rewrite !map_app in *. induction (map blk_id l1) as [|c l IH]; cbn in *.
  - induction (map blk_id l2) as [|d l' IH']; cbn in *; [exact ND|]. inversion ND; subst. auto.
  - inversion ND as [|x l0 NI ND']; subst. constructor; [| exact (IH ND')]. intros K. apply NI. apply in_app_or in K. apply in_or_app.
    destruct K as [K|K]; [left; exact K| right; apply in_or_app; right; exact K].
Qed.
Lemma perm_in_rest : forall (Fr L' L : list block) b, Permutation (Fr ++ L') L -> In b L -> ~ In b Fr -> In b L'.
Proof.
  intros Fr L' L b P HI NF. apply Permutation_sym in P. pose proof (Permutation_in _ P HI) as K. apply in_app_or in K. destruct K as [K|K]; [contradiction| exact K].
Qed.

Section W.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Definition apf_tail_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (a : Z) (K : skrep) (lo B : Z) (errv : word) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (s' : as_St H) (LB' : list block),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (ATP + -164) [C4 errv] /\ as_rauxv_ok H m' B
      /\ Permutation (blocks_SK a K ++ LB') LB /\ as_RHEAP H s' LB' m'
      /\ xpres H LB' (bv_unsigned sp) [] m m'
      /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cf H (8 * sk_cap K) - as_Cf H 56.

  Lemma apf_tail_spec :
    forall (rax sp gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2x s3x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (a lo B : Z) (K : skrep) (pad j : list byte) (errv : word)
           (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 ATP) t0 t1 t2 sp (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                              s2x s3x s4x s5x s6x s7x s8x s9x s10x s11x t3 t4 t5 t6)
                         F (Z_to_bv 64 APF_TAIL) fc None m (seg_rom asegs) ->
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < a -> In (sk_id K, a, SK_SIZE) LB -> 0 <= sk_num K <= sk_cap K -> sk_cap K <= 2^20 ->
      ((sk_cap K = 0 /\ sk_data K = 0)
       \/ (4 <= sk_cap K /\ 0 < sk_data K /\ (a + SK_SIZE <= sk_data K \/ sk_data K + 8 * sk_cap K <= a) /\ In (sk_did K, sk_data K, 8 * sk_cap K) LB
           /\ u64arr asegs m (sk_data K) (map wz (sk_elems K))
           /\ (exists junk, rw_cells asegs m (sk_data K + 8 * sk_num K) [CB (Z.to_nat (8 * (sk_cap K - sk_num K))) junk])
           /\ addressable m (sk_data K) (8 * sk_cap K))) ->
      addressable m a SK_SIZE ->
      rw_cells asegs m (bv_unsigned sp + -112) (apf_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp + -112) -> aceil <= lo -> lo <= bv_unsigned sp - 112 - CFREE_STACK ->
      rw_cells asegs m (ATP + -164) [C4 errv] -> mem_inv asegs m -> bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') ->
      as_chain H m (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH) ->
      pf_ok (as_TR H) (pf_shift APF_RA_FREE PF_cfree ++ PF_cfree) (bv_unsigned ra) CH ->
      as_Cf H (8 * sk_cap K) + as_Cf H 56 <= as_AL H s ->
      IMPL_mem m -> GOT_mem m -> bv_unsigned ra mod 2 = 0 ->
      as_SR H (apf_tail_post ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a K lo B errv m mo) (mkCfg msF mo).
  Proof using HH.
    intros until CH. intros VIS HDR POS HIN NC CAP DAT SH1 FR HP KREL AUX SPB ST CEIL LO ERR MI SP16 AC CHN CHS CH1 PF HAL IM GM RAE.
    unfold CFREE_STACK, AFREE_STACK in LO. unfold SK_SIZE in *.
    acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -32) by lia.
    pose proof (ah_blocks H HH _ _ _ _ HP HIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K4, K5, K6, K7.
    unfold AIMG_TOP in K4. clear K6.
    pose proof (aapp_bounds a 56 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
    assert (SUBL : forall p L b, In b (as_lb_remove H p L) -> In b L) by (intros p L b Hb; eapply (proj2 (proj2 (ah_lb_remove H HH))); exact Hb).
    assert (ACC0 : accessible m a 56) by (eapply addressable_accessible; [exact SH1| lia| lia| unfold AAPP_HI; lia]).
    assert (OBH : ashobj H LB (bv_unsigned sp + -32) a 56) by (left; exists (sk_id K, a, 56); split; [exact HIN| cbn; lia]).
    pose proof (ah_costs H HH) as (CM0 & CMM & CF0 & CFM & _).
    assert (CHS1 : forall fp' ra', In (fp', ra') ((bv_unsigned sp, bv_unsigned ra) :: CH) -> bv_unsigned sp + -32 + 16 <= fp')
      by (intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]).
    assert (SP16' : (bv_unsigned sp + -32) mod 16 = 0) by (replace (bv_unsigned sp + -32) with (bv_unsigned sp - 32) by lia; rewrite Zminus_mod, SP16; reflexivity).
    pose proof (ACONST_shbase m AC) as [GSB SHB0].
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply apf_tail1 with (lo := lo);
      [exact HDR| exact POS| exact K2| unfold SK_SIZE; lia| exact ACC0| exact GSB| exact SHB0| exact FR| exact ST| exact CEIL| lia| exact MI]|].
    intros msF1 mo1 KREL1 MP1 (m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
    assert (CW : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp)]) by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
    assert (XP1 : xpres H LB (bv_unsigned sp) [] m m1)
      by (eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
    assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
    assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
    assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
    assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
    assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
    assert (AC1 : ACONST m1).
    { eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil].
      apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
    assert (SHa1 : addressable m1 a 56).
    { eapply addressable_transport; [exact SH1| exact MU1| exact WM1|].
      pose proof (sh_aapp_range a 56 K7 ltac:(lia)) as (Sx1 & Sx2 & Sx3). unfold AHI_LO in Sx3. cbn [disjoint_from fst snd]. split; [lia| exact I]. }
    assert (DAT1 : (sk_cap K = 0 /\ sk_data K = 0)
       \/ (4 <= sk_cap K /\ 0 < sk_data K /\ (a + 56 <= sk_data K \/ sk_data K + 8 * sk_cap K <= a) /\ In (sk_did K, sk_data K, 8 * sk_cap K) LB
           /\ u64arr asegs m1 (sk_data K) (map wz (sk_elems K))
           /\ (exists junk, rw_cells asegs m1 (sk_data K + 8 * sk_num K) [CB (Z.to_nat (8 * (sk_cap K - sk_num K))) junk])
           /\ addressable m1 (sk_data K) (8 * sk_cap K))).
    { destruct DAT as [D0|(D4 & DP & DDJ & DIN & AR & (junk & JK) & SH2)]; [left; exact D0| right].
      pose proof (ah_blocks H HH _ _ _ _ HP DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
      split; [exact D4|]. split; [exact DP|]. split; [exact DDJ|]. split; [exact DIN|]. split; [| split].
      - eapply u64arr_across; [exact MU1| exact WM1| | exact AR]. rewrite length_map. unfold sk_num, zlength in NC. cbn [disjoint_from fst snd length Z.of_nat]. split; [lia| exact I].
      - exists junk. eapply rw_cells_transport; [exact JK| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add fst snd]. unfold sk_num, zlength in NC |- *. split; [lia| exact I].
      - eapply addressable_transport; [exact SH2| exact MU1| exact WM1|].
        pose proof (sh_aapp_range (sk_data K) (8 * sk_cap K) E7 ltac:(lia)) as (Sx1 & Sx2 & Sx3). unfold AHI_LO in Sx3. cbn [disjoint_from fst snd]. split; [lia| exact I]. }
    assert (CHN1 : as_chain H m1 (bv_unsigned s0) CH).
    { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
    assert (CH1' : as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
    { pose proof (aword_range s0) as S0R. eapply (ah_chain_cons H HH); [exact CHN1| lia| lia| exact SP16| lia| lia|].
      pose proof FR1 as FR2. unfold asf_frame in FR2.
      change ([C8 s2; C8 s1; C8 s0; C8 ra]) with ([C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
      apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
      replace (bv_unsigned sp - 16) with (bv_unsigned sp + -32 + 16) by lia.
      first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
    clear HP AUX ERR IM GM AC SH1 DAT CHN CH1 ST MI FR HDR.
    rename HP1 into HP, AUX1 into AUX, ERR1 into ERR, IM1 into IM, GM1 into GM, AC1 into AC, SHa1 into SH1, DAT1 into DAT,
           CHN1 into CHN, CH1' into CH1, ST1 into ST, MI1 into MI, FR1 into FR, HDR1 into HDR.
    (* [comment removed for export] *)
    assert (MID : as_SR H (fun c => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m2 (s2' : as_St H) LB2,
                 as_VIS H s2' (cfg_ms c) = MS (mkR (Z_to_bv 64 APF_RA_FREE) (Z_to_bv 64 (bv_unsigned sp + -32)) gp (Z_to_bv 64 ATP) t0' t1' t2' sp (Z_to_bv 64 a)
                                    a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 APF_FILE) s3 s4 s5 s6
                                    s7 s8 s9 s10 s11 t3' t4' t5' t6')
                               F (ret_pc (Z_to_bv 64 APF_RA_FREE)) fc None m2 (seg_rom asegs)
                 /\ as_AKREL H s2' c /\ as_MPRES H mo (cfg_model c) /\ mem_inv asegs m2 /\ ACONST m2 /\ stk asegs m2 lo (bv_unsigned sp + -32)
                 /\ rw_cells asegs m2 (ATP + -164) [C4 errv] /\ as_rauxv_ok H m2 B
                 /\ as_RHEAP H s2' LB2 m2 /\ In (sk_id K, a, 56) LB2
                 /\ Permutation ((if sk_cap K =? 0 then [] else [(sk_did K, sk_data K, 8 * sk_cap K)]) ++ LB2) LB
                 /\ (forall b, In b LB2 -> In b LB)
                 /\ xpres H LB2 (bv_unsigned sp + -32) [] m1 m2 /\ IMPL_mem m2 /\ GOT_mem m2
                 /\ rw_cells asegs m2 (bv_unsigned sp + -32) (asf_frame s2 s1 s0 ra)
                 /\ rw_cells asegs m2 a (sk_hdr_cells K pad) /\ addressable m2 a 56
                 /\ as_AL H s2' >= as_AL H s - as_Cf H (8 * sk_cap K))
             (mkCfg msF1 mo1)).
    { destruct DAT as [[C0 D0]|(D4 & DP & DDJ & DIN & AR & (junk & JK) & SH2)].
      - (* [comment removed for export] *)
        rewrite D0 in VIS1. pose proof (acfree_null_spec H HH) as CF. unfold cfree_null_stmt in CF.
        assert (HAL0 : as_Cf H 0 + as_Cf H 56 <= as_AL H s) by (rewrite C0 in HAL; exact HAL).
        eapply (ah_mono H HH).
        { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH); [exact VIS1| ..];
            rewrite ?unsigned_lit by lia.
          all: first [exact HP| exact KREL1| exact AUX| exact ST| exact CEIL| exact ERR| exact MI| reflexivity| exact SP16'| exact AC| exact CH1| exact CHS1
                     | exact IM| exact GM| unfold CFREE_STACK, AFREE_STACK; lia| pose proof (CF0 0 ltac:(lia)); pose proof (CF0 56 ltac:(lia)); lia
                     | match goal with |- ?G => idtac "LEFT:" G end]. }
        intros [msF2 mo2] PO. unfold cfree_null_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                        VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite unsigned_lit in ERR2 by (unfold ATP; lia).
        exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s', LB.
        split; [exact VIS2|]. split; [exact KREL2|]. split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|]. split; [exact MI2|]. split; [exact AC2|].
        split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HEAP2|]. split; [exact HIN|].
        rewrite C0. cbn [Z.eqb app Z.mul]. split; [apply Permutation_refl|]. split; [auto|].
        split; [exact XP2|]. split; [exact IM2|]. split; [exact GM2|].
        split; [eapply (xpres_rw_cells' H); [exact XP2| exact FR| left; cbn; lia| constructor]|].
        split. { eapply (xpres_rw_cells' H); [exact XP2| exact HDR| | constructor]. apply (ashobj_client_range H). unfold sk_hdr_cells. cbn [cells_size csize Nat.add]. exact OBH. }
        split. { eapply (ashobj_addressable_xpres H HH); [exact HP| intros b Hb; exact Hb| exact CSP| exact OBH| unfold AAPP_HI; lia| exact SH1| exact XP2| constructor]. }
        exact AL2.
      - (* [comment removed for export] *)
        pose proof (ah_blocks H HH _ _ _ _ HP DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E2, E3, E4, E5, E6, E7.
        unfold sk_num, zlength in NC, JK. pose proof (u64arr_CB _ _ _ _ AR) as A1. rewrite length_map in A1.
        assert (DCB : rw_cells asegs m1 (sk_data K) [CB (Z.to_nat (8 * sk_cap K)) (u64s (map wz (sk_elems K)) ++ junk)]).
        { assert (J : rw_cells asegs m1 (sk_data K) ([CB (8 * length (sk_elems K))%nat (u64s (map wz (sk_elems K)))] ++ [CB (Z.to_nat (8 * (sk_cap K - Z.of_nat (length (sk_elems K))))) junk])).
          { apply (proj2 (rw_cells_app asegs _ _ _ _)). split; [exact A1|]. cbn [cells_size csize Nat.add].
            replace (sk_data K + Z.of_nat (8 * length (sk_elems K) + 0)) with (sk_data K + 8 * Z.of_nat (length (sk_elems K))) by lia. exact JK. }
          pose proof (rw_cells_flatten _ _ _ _ J) as T. cbn [cells_size csize Nat.add cells_bytes cbytes app] in T. rewrite app_nil_r in T.
          replace (Z.to_nat (8 * sk_cap K)) with (8 * length (sk_elems K) + (Z.to_nat (8 * (sk_cap K - Z.of_nat (length (sk_elems K)))) + 0))%nat by lia. exact T. }
        pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
        eapply (ah_mono H HH).
        { eapply CF with (lo := lo) (B := B) (LB := LB) (s := s) (p := sk_did K) (n := 8 * sk_cap K) (errv := errv) (CH := (bv_unsigned sp, bv_unsigned ra) :: CH);
            [exact VIS1| reflexivity| ..]; rewrite ?unsigned_lit by lia.
          all: first [exact HP| exact KREL1| exact DIN| exact AUX| exact ST| exact CEIL| exact ERR| exact MI| reflexivity| exact SP16'| exact AC| exact CH1| exact CHS1
                     | exact DCB| exact SH2| exact IM| exact GM| unfold CFREE_STACK, AFREE_STACK; lia
                     | unfold APF_RA_FREE; rewrite ?unsigned_lit by lia; eapply pf_ok_call; [exact PF|]; intros x Hx; apply in_app_iff; left; exact Hx
                     | pose proof (CF0 56 ltac:(lia)); lia | match goal with |- ?G => idtac "LEFT:" G end]. }
        intros [msF2 mo2] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & s' &
                        VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & XP2 & HEAP2 & IM2 & GM2 & AL2).
        rewrite (unsigned_lit (bv_unsigned sp + -32)) in ST2, XP2 by lia. rewrite unsigned_lit in ERR2 by (unfold ATP; lia).
        assert (HIN2 : In (sk_id K, a, 56) (as_lb_remove H (sk_did K) LB)).
        { apply (proj2 (proj2 (proj2 (alb_remove_exact H HH _ _ _ _ (ah_nodup H HH _ _ _ HP) DIN)) (sk_id K, a, 56))).
          split; [exact HIN|]. cbn. intros E.
          pose proof (nodup_id_inj LB _ _ (ah_nodup H HH _ _ _ HP) HIN DIN E) as EE. injection EE as EA EB. lia. }
        assert (OBH2 : ashobj H (as_lb_remove H (sk_did K) LB) (bv_unsigned sp + -32) a 56) by (left; exists (sk_id K, a, 56); split; [exact HIN2| cbn; lia]).
        exists u0, u1, u2, b0, b1, b2, b3, b4, b5, b6, b7, u3, u4, u5, u6, m2, s', (as_lb_remove H (sk_did K) LB).
        split; [exact VIS2|]. split; [exact KREL2|]. split; [eapply (ah_mpres_trans H HH); [exact MP1| exact MP2]|]. split; [exact MI2|]. split; [exact AC2|].
        split; [exact ST2|]. split; [exact ERR2|]. split; [exact AUX2|]. split; [exact HEAP2|]. split; [exact HIN2|].
        replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [app].
        split; [eapply (alb_remove_perm H HH); [exact HP| exact DIN]|]. split; [intros b Hb; eapply SUBL; exact Hb|].
        split; [exact XP2|]. split; [exact IM2|]. split; [exact GM2|].
        split; [eapply (xpres_rw_cells' H); [exact XP2| exact FR| left; cbn; lia| constructor]|].
        split. { eapply (xpres_rw_cells' H); [exact XP2| exact HDR| | constructor]. apply (ashobj_client_range H). unfold sk_hdr_cells. cbn [cells_size csize Nat.add]. exact OBH2. }
        split. { eapply (ashobj_addressable_xpres H HH); [exact HP| exact (SUBL (sk_did K) LB)| exact CSP| exact OBH2| unfold AAPP_HI; lia| exact SH1| exact XP2| constructor]. }
        exact AL2. }
    eapply (ah_seq H HH); [exact MID|].
    intros [msF2 mo2] PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & sx2 & LB2 &
                    VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & HEAP2 & HIN2 & PERM2 & SUB2 & XP2 & IM2 & GM2 & FR2 & HDR2 & SHH2 & AL2).
    (* [comment removed for export] *)
    eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply apf_tail2; [exact FR2| exact MI2]|].
    intros msF3 mo3 KREL3 MP3 VIS3.
    (* [comment removed for export] *)
    unfold asf_frame in FR2. release_frame FR2 ST2 (bv_unsigned sp). rename ST2 into ST3.
    pose proof (rw_cells_flatten _ _ _ _ HDR2) as HCB. unfold sk_hdr_cells in HCB. cbn [cells_size csize Nat.add] in HCB.
    assert (CH2 : as_chain H m2 (bv_unsigned s0) CH).
    { eapply (chain_via_apres H HH); [| apply (xpres_nil_apres H); exact XP2| intros fp' ra' Hin; specialize (CHS _ _ Hin); lia]. exact CHN. }
    pose proof (acfree_spec H HH) as CF. unfold cfree_stmt in CF.
    eapply (ah_mono H HH).
    { eapply CF with (lo := lo) (B := B) (LB := LB2) (s := sx2) (p := sk_id K) (n := 56) (errv := errv) (CH := CH);
        [exact VIS3| reflexivity| ..]; rewrite ?unsigned_lit by (unfold ATP; lia).
      all: first [exact HEAP2| exact KREL3| exact HIN2| exact AUX2| exact SPB| exact ST3| exact CEIL| exact ERR2| exact MI2| reflexivity| exact SP16| exact AC2| exact CH2| exact CHS
                 | exact HCB| exact SHH2| exact IM2| exact GM2| unfold CFREE_STACK, AFREE_STACK; lia
                 | eapply pf_ok_incl; [exact PF|]; intros x Hx; apply in_app_iff; right; exact Hx
                 | pose proof (CF0 (8 * sk_cap K) ltac:(lia)); lia | match goal with |- ?G => idtac "LEFT:" G end]. }
    intros [msF4 mo4] PO. unfold cfree_post in PO. cbn [cfg_ms cfg_model] in PO.
    destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m4 & s4' &
                    VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & XP4 & HEAP4 & IM4 & GM4 & AL4).
    unfold apf_tail_post. cbn [cfg_ms cfg_model].
    exists v0, v1, v2, c0, c1, c2, c3, c4, c5, c6, c7, v3, v4, v5, v6, m4, s4', (as_lb_remove H (sk_id K) LB2).
    split; [exact VIS4|]. split; [exact KREL4|]. split; [eapply (ah_mpres_trans H HH); [| exact MP4]; eapply (ah_mpres_trans H HH); [exact MP2| exact MP3]|].
    split; [exact MI4|]. split; [exact AC4|]. split; [exact ST4|].
    split; [rewrite unsigned_lit in ERR4 by (unfold ATP; lia); exact ERR4|]. split; [exact AUX4|].
    split.
    { unfold blocks_SK. cbn [app]. eapply Permutation_trans; [| exact PERM2].
      destruct (sk_cap K =? 0); cbn [app].
      - eapply (alb_remove_perm H HH); [exact HEAP2| exact HIN2].
      - eapply Permutation_trans; [apply perm_swap|]. apply perm_skip. eapply (alb_remove_perm H HH); [exact HEAP2| exact HIN2]. }
    split; [exact HEAP4|].
    split.
    { eapply xpres_trans; [| exact XP4]. eapply xpres_trans; [eapply (xpres_weaken H); [exact XP1| lia| intros b Hb; apply SUB2; eapply SUBL; exact Hb| auto]|].
      eapply (xpres_weaken H); [exact XP2| lia| intros b Hb; eapply SUBL; exact Hb| auto]. }
    split; [exact IM4|]. split; [exact GM4|]. lia.
  Qed.

  Lemma xpres_u64arr : forall LB SP X m m' A ws,
    xpres H LB SP X m m' -> u64arr asegs m A ws -> xclient_range H LB SP X A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
  Proof.
    intros LB SP X m m' A ws XP [B W] R. split.
    - eapply xpres_bytes_at; [exact XP| exact B|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact R.
    - eapply xpres_wr_at; [exact XP| exact W| exact R].
  Qed.

  Section Elem.
    Context (X : Type) (EP : list block -> mem -> Z -> X -> Prop) (blocks_E : Z -> X -> list block) (G : mem -> Prop).
    Context (PFe : list (Z * list Z)) (ecost : X -> Z) (eshad : mem -> Z -> X -> Prop).
    Variables (FN estack : Z).
    Hypothesis EF : efree_stmt_at H X EP blocks_E G PFe ecost eshad FN estack.
    Hypothesis EPF : EP_frame H X EP blocks_E.
    Hypothesis EPO : EP_owned X EP blocks_E.
    Hypothesis GF : G_frame H G.
    Hypothesis ESF : eshad_frame H X blocks_E eshad.
    Hypothesis EC0 : ecost_pos X ecost.
    Hypothesis FNR : 0 <= FN < 2^64.
    Hypothesis FNE : FN mod 2 = 0.

    Definition eblocks (ps : list Z) (xs : list X) : list block := concat (map (fun px => blocks_E (fst px) (snd px)) (combine ps xs)).

    (* [comment removed for export] *)
    Lemma ep_rest_frame : forall LB LB1 m m2 (SP : Z) (Bp : list block) rest xs,
      Forall2 (fun p x => EP LB m p x) rest xs -> Forall2 (fun p x => eshad m p x) rest xs ->
      (forall b, In b LB -> ~ In b Bp -> In b LB1) ->
      List.NoDup (map blk_id (Bp ++ eblocks rest xs)) ->
      xpres H LB1 SP [] m m2 -> (forall b, In b LB -> blk_addr b + blk_size b <= SP) ->
      Forall2 (fun p x => EP LB1 m2 p x) rest xs /\ Forall2 (fun p x => eshad m2 p x) rest xs.
    Proof using EPF EPO ESF.
      intros LB LB1 m m2 SP Bp rest xs F2. induction F2 as [|p' x' r' xs' E' F' IHF]; intros S2 KEEP ND XP BEL; [split; constructor|].
      inversion S2 as [|p0 x0 r0 xs0 SE0 S2' E1 E2]; subst p0 x0 r0 xs0.
      cbn [eblocks combine map concat fst snd] in ND. fold (eblocks r' xs') in ND.
      assert (OWN : forall b, In b (blocks_E p' x') -> In b LB1).
      { intros b Hb. apply KEEP; [eapply EPO; [exact E'| exact Hb]|]. intros Kb.
        eapply (nodup_ids_excl Bp (blocks_E p' x' ++ eblocks r' xs')); [exact ND| exact Kb| apply in_or_app; left; exact Hb]. }
      assert (BELp : forall b, In b (blocks_E p' x') -> blk_addr b + blk_size b <= SP) by (intros b Hb; apply BEL; eapply EPO; [exact E'| exact Hb]).
      destruct (IHF S2' KEEP ltac:(eapply nodup_ids_drop_mid; exact ND) XP BEL) as [IH1 IH2].
      split; constructor.
      - eapply EPF; [exact E'| exact OWN| exact XP| exact BELp].
      - exact IH1.
      - eapply ESF; [exact SE0| exact OWN| exact XP| exact BELp].
      - exact IH2.
    Qed.

    (* [comment removed for export] *)
    Lemma pf_loop : forall (rest : list Z) (xs : list X) (done : list Z)
        (rax spi gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10x t3 t4 t5 t6 : word)
        (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (a lo B : Z) (K : skrep) (pad junk : list byte) (errv : word)
        (fr : list cell) (CH : list (Z * Z)) (curc : Z) (CHc : list (Z * Z)) (Q : config -> Prop),
      rest <> [] -> sk_elems K = done ++ rest -> length xs = length rest ->
      Forall2 (fun p x => EP LB m p x) rest xs -> Forall2 (fun p x => eshad m p x) rest xs ->
      List.NoDup (map blk_id (blocks_SK a K ++ eblocks rest xs)) ->
      as_VIS H s msF = MS (mkR rax spi gp (Z_to_bv 64 ATP) t0 t1 t2 (Z_to_bv 64 (bv_unsigned spi + 112)) (Z_to_bv 64 a) a0 a1 a2 a3 a4 a5 a6 a7
                               (Z_to_bv 64 FN) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 (a + 40)) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr a 3 + ASHB))
                               (Z_to_bv 64 (Z.of_nat (length done) * 8)) (Z_to_bv 64 (Z.of_nat (length done)))
                               s10x (Z_to_bv 64 (Z.shiftr (a + 8) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (a + 40) 3 + ASHB)) t3 t4 t5 t6)
                          F (Z_to_bv 64 APF_HEAD) fc None m (seg_rom asegs) ->
      rw_cells asegs m a (sk_hdr_cells K pad) -> 0 < a -> In (sk_id K, a, SK_SIZE) LB ->
      sk_num K <= sk_cap K -> sk_cap K <= 2^20 -> Forall (fun p => 0 < p < 2^64) (sk_elems K) ->
      4 <= sk_cap K -> 0 < sk_data K -> In (sk_did K, sk_data K, 8 * sk_cap K) LB ->
      u64arr asegs m (sk_data K) (map wz (sk_elems K)) -> rw_cells asegs m (sk_data K + 8 * sk_num K) [CB (Z.to_nat (8 * (sk_cap K - sk_num K))) junk] ->
      is_sk_freefunc_thunk (sk_free_thunk K) ->
      addressable m a SK_SIZE -> addressable m (sk_data K) (8 * sk_cap K) -> ACONST m ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> as_rauxv_ok H m B -> bv_unsigned spi + 112 <= B ->
      stk asegs m lo (bv_unsigned spi) -> aceil <= lo -> lo <= bv_unsigned spi - (16 + Z.max estack CFREE_STACK) -> (bv_unsigned spi) mod 16 = 0 -> bv_unsigned spi + 112 < 2^64 ->
      rw_cells asegs m (ATP + -164) [C4 errv] -> mem_inv asegs m -> IMPL_mem m -> GOT_mem m -> G m ->
      rw_cells asegs m (bv_unsigned spi) fr ->
      as_chain H m (bv_unsigned spi + 112) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned spi + 16 <= fp') ->
      pf_ok (as_TR H) PFe APF_RA_ELEM CH ->
      as_chain H m curc CHc -> (forall fp' ra', In (fp', ra') CHc -> bv_unsigned spi + 128 <= fp') ->
      ecost_sum X ecost xs <= as_AL H s ->
      (forall (rax' u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 u3 u4 : word) (s10y : word) (u5 u6 u7 u8 : word) (msF' : machine_state) (m' : mem) (mo' : Model) (s' : as_St H) (LB' : list block),
         Permutation (eblocks rest xs ++ LB') LB -> as_RHEAP H s' LB' m' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
         as_rauxv_ok H m' B -> stk asegs m' lo (bv_unsigned spi) -> rw_cells asegs m' (ATP + -164) [C4 errv] -> mem_inv asegs m' ->
         IMPL_mem m' -> GOT_mem m' -> G m' -> rw_cells asegs m' (bv_unsigned spi) fr -> rw_cells asegs m' a (sk_hdr_cells K pad) ->
         u64arr asegs m' (sk_data K) (map wz (sk_elems K)) -> rw_cells asegs m' (sk_data K + 8 * sk_num K) [CB (Z.to_nat (8 * (sk_cap K - sk_num K))) junk] ->
         addressable m' a SK_SIZE -> addressable m' (sk_data K) (8 * sk_cap K) -> ACONST m' -> as_chain H m' (bv_unsigned spi + 112) CH -> as_chain H m' curc CHc ->
         as_AL H s' >= as_AL H s - ecost_sum X ecost xs ->
         xpres H LB' (bv_unsigned spi) [] m m' ->
         as_VIS H s' msF' = MS (mkR rax' spi gp (Z_to_bv 64 ATP) u0 u1 u2 (Z_to_bv 64 (bv_unsigned spi + 112)) (Z_to_bv 64 a) c0 c1 c2 c3 c4 c5 c6 c7
                                   (Z_to_bv 64 FN) (Z_to_bv 64 (a + 8)) (Z_to_bv 64 (a + 40)) (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr a 3 + ASHB))
                                   u3 u4 s10y (Z_to_bv 64 (Z.shiftr (a + 8) 3 + ASHB)) (Z_to_bv 64 (Z.shiftr (a + 40) 3 + ASHB)) u5 u6 u7 u8)
                              F (Z_to_bv 64 APF_TAIL) fc None m' (seg_rom asegs) ->
         as_SR H Q (mkCfg msF' mo')) ->
      as_SR H Q (mkCfg msF mo).
    Proof using HH EF EPF EPO GF ESF EC0 FNR FNE.
      intros rest. induction rest as [|p rest IH]; [intros; congruence|].
      intros xs done rax spi gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10x t3 t4 t5 t6 F fc msF m mo s LB a lo B K pad junk errv fr CH curc CHc Q.
      intros _ EL XL F2 S2 ND VIS HDR POS HIN NC CAP ELR CAP4 DP DIN ARR JK TH SHa SHd AC HP KREL AUX SPB ST CEIL LO SP16 SPH ERR MI IM GM GG FR CHN CHS PFE CHCN CHCS HAL KONT.
      destruct xs as [|x xs]; [cbn in XL; discriminate|]. cbn [length] in XL. injection XL as XL.
      inversion F2 as [|p0 x0 r0 xs0 EP0 F2' E1 E2]; subst p0 x0 r0 xs0. clear F2.
      inversion S2 as [|p0 x0 r0 xs0 SE0 S2' E1 E2]; subst p0 x0 r0 xs0. clear S2.
      unfold CFREE_STACK, AFREE_STACK in LO.
      acb. pose proof (aword_range spi) as SPR. assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (CSP : aceil <= bv_unsigned spi) by lia.
      unfold SK_SIZE in SHa |- *.
      pose proof (ah_blocks H HH _ _ _ _ HP HIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K3, K5, K7. clear K2 K4 K6.
      pose proof (ah_blocks H HH _ _ _ _ HP DIN) as (D1 & D2 & D3 & D4 & D5 & D6 & D7). cbn [blk_addr blk_size fst snd] in D1, D2, D3, D5, D7. clear D4 D6.
      pose proof (aapp_bounds a 56 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
      pose proof (aapp_bounds (sk_data K) (8 * sk_cap K) D7 ltac:(lia)) as (DB1 & DB2 & DB3 & DB4 & DB5). unfold AAPP_HI in DB3.
      set (i := Z.of_nat (length done)) in *.
      assert (NTH : nth_error (sk_elems K) (Z.to_nat i) = Some p).
      { rewrite EL. unfold i. rewrite Nat2Z.id. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
      assert (PR : 0 < p < 2^64).
      { apply (proj1 (Forall_forall _ _) ELR p). rewrite EL. apply in_or_app. right. left. reflexivity. }
      assert (NUM : sk_num K = i + 1 + Z.of_nat (length rest)).
      { unfold sk_num, zlength. rewrite EL, length_app. cbn [length]. unfold i. lia. }
      cbn [eblocks combine map concat fst snd] in ND. fold (eblocks rest xs) in ND.
      assert (STK : 16 <= bv_unsigned spi - lo /\ estack <= bv_unsigned spi - lo /\ CFREE_STACK <= bv_unsigned spi - lo - 16) by (unfold CFREE_STACK, AFREE_STACK; lia).
      assert (ACCa : accessible m a 56) by (eapply addressable_accessible; [exact SHa| lia| lia| unfold AAPP_HI; lia]).
      assert (ACCd : accessible m (sk_data K) (8 * sk_cap K)) by (eapply addressable_accessible; [exact SHd| lia| lia| unfold AAPP_HI; lia]).
      pose proof (EC0 x) as ECX. assert (ECR : 0 <= ecost_sum X ecost xs).
      { clear - EC0. unfold ecost_sum. induction xs as [|y ys IHy]; cbn [fold_right]; [lia|]. pose proof (EC0 y). lia. }
      cbn [ecost_sum fold_right] in HAL. fold (ecost_sum X ecost xs) in HAL.
      (* [comment removed for export] *)
      eapply (ahh_evt_then H HH); [exact KREL| exact VIS|
        eapply apf_segL with (lo := lo) (K := K) (pad := pad) (i := i) (p := p); try eassumption; unfold SK_SIZE; try lia|].
      intros msF1 mo1 KREL1 MP1 (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & VIS1 & MU1 & WM1 & MI1 & ST1 & HDR1).
      assert (CW : Forall (aclient_write_ok H LB) [(lo, bv_unsigned spi)]) by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
      assert (NSW : Forall (fun iv : Z * Z => snd iv <= ALOWSH_LO \/ AHI_LO <= fst iv) [(lo, bv_unsigned spi)])
        by (apply Forall_cons; [cbn [fst snd]; unfold AHI_LO, ALOWSH_LO in *; lia| apply Forall_nil]).
      assert (XP1 : xpres H LB (bv_unsigned spi) [] m m1)
        by (eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
      assert (HP1 : as_RHEAP H s LB m1) by (eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]).
      assert (AUX1 : as_rauxv_ok H m1 B) by (eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]).
      assert (AC1 : ACONST m1).
      { eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil].
        apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
      assert (ERR1 : rw_cells asegs m1 (ATP + -164) [C4 errv]) by (eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]).
      assert (IM1 : IMPL_mem m1) by (eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]).
      assert (GM1 : GOT_mem m1) by (eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]).
      assert (GG1 : G m1) by (eapply GF; [exact GG| exact XP1| lia]).
      assert (EP1 : EP LB m1 p x).
      { eapply EPF; [exact EP0| intros b Hb; eapply EPO; [exact EP0| exact Hb]| exact XP1|].
        intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP (EPO _ _ _ _ EP0 b Hb)) as (_ & _ & _ & _ & Q5 & _). pose proof aceil_range. lia. }
      assert (SE1 : eshad m1 p x).
      { eapply ESF; [exact SE0| intros b Hb; eapply EPO; [exact EP0| exact Hb]| exact XP1|].
        intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP (EPO _ _ _ _ EP0 b Hb)) as (_ & _ & _ & _ & Q5 & _). pose proof aceil_range. lia. }
      assert (CH1 : as_chain H m1 (bv_unsigned spi + 112) CH).
      { eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      assert (CHc1 : as_chain H m1 curc CHc).
      { eapply (achain_below H HH m m1); [exact CHCN| exact CHCS| exact MU1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      assert (NDE : List.NoDup (map blk_id (blocks_E p x))).
      { rewrite map_app in ND. apply NoDup_app_remove_l in ND. rewrite map_app in ND. apply NoDup_app_remove_r in ND. exact ND. }
      eapply (ah_seq H HH).
      { unfold efree_stmt_at in EF.
        eapply EF with (lo := lo) (B := B) (LB := LB) (s := s) (p := p) (x := x) (errv := errv) (CH := CH); [exact VIS1| ..]; rewrite ?unsigned_lit by lia; try reflexivity.
        all: first [exact EP1| exact SE1| exact NDE| exact HP1| exact KREL1| exact AUX1| exact ST1| exact CEIL| exact ERR1| exact MI1| exact SP16| exact AC1| exact CH1| exact CHS
                   | exact PFE| exact IM1| exact GM1| exact GG1| lia | match goal with |- ?G => idtac "LEFT:" G end]. }
      intros [msF2 mo2] PO. unfold efree_post in PO. cbn [cfg_ms cfg_model] in PO.
      destruct PO as (v0 & v1 & v2 & c0 & c1 & c2 & c3 & c4' & c5 & c6 & c7 & v3 & v4 & v5 & v6 & m2 & s2 & LB1 &
                      VIS2 & KREL2 & MP2 & MI2 & AC2 & ST2 & ERR2 & AUX2 & PERM2 & HP2 & XP2 & IM2 & GM2 & GG2 & AL2).
      rewrite unsigned_lit in ERR2 by (unfold ATP; lia).
      assert (SUB1 : forall b, In b LB1 -> In b LB).
      { intros b Hb. eapply Permutation_in; [exact PERM2| apply in_or_app; right; exact Hb]. }
      (* [comment removed for export] *)
      assert (KEEP : forall b, In b LB -> ~ In b (blocks_E p x) -> In b LB1) by (intros b Hb Nb; eapply perm_in_rest; [exact PERM2| exact Hb| exact Nb]).
      assert (HIN1 : In (sk_id K, a, 56) LB1).
      { apply KEEP; [exact HIN|]. intros Kb. eapply (nodup_ids_excl (blocks_SK a K) (blocks_E p x ++ eblocks rest xs)); [exact ND| left; reflexivity| apply in_or_app; left; exact Kb]. }
      assert (DIN1 : In (sk_did K, sk_data K, 8 * sk_cap K) LB1).
      { apply KEEP; [exact DIN|]. intros Kb. eapply (nodup_ids_excl (blocks_SK a K) (blocks_E p x ++ eblocks rest xs)); [exact ND| | apply in_or_app; left; exact Kb].
        unfold blocks_SK. replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity. }
      assert (XP02 : xpres H LB1 (bv_unsigned spi) [] m m2).
      { eapply xpres_trans; [| exact XP2]. eapply (xpres_weaken H); [exact XP1| lia| exact SUB1| auto]. }
      assert (OBH : ashobj H LB1 (bv_unsigned spi) a 56) by (left; exists (sk_id K, a, 56); split; [exact HIN1| cbn; lia]).
      assert (OBD : ashobj H LB1 (bv_unsigned spi) (sk_data K) (8 * sk_cap K)) by (left; exists (sk_did K, sk_data K, 8 * sk_cap K); split; [exact DIN1| cbn; lia]).
      assert (HDR2 : rw_cells asegs m2 a (sk_hdr_cells K pad)).
      { eapply (xpres_rw_cells' H); [exact XP2| exact HDR1| | constructor]. apply (ashobj_client_range H). unfold sk_hdr_cells. cbn [cells_size csize Nat.add]. exact OBH. }
      assert (ARR2 : u64arr asegs m2 (sk_data K) (map wz (sk_elems K))).
      { eapply xpres_u64arr; [exact XP02| exact ARR|]. split; [| constructor]. apply (ashobj_client_range H). eapply (ashobj_sub H); [exact OBD| lia|]. rewrite length_map. unfold sk_num, zlength in NC. lia. }
      assert (JK2 : rw_cells asegs m2 (sk_data K + 8 * sk_num K) [CB (Z.to_nat (8 * (sk_cap K - sk_num K))) junk]).
      { eapply (xpres_rw_cells' H); [exact XP02| exact JK| | constructor]. apply (ashobj_client_range H). eapply (ashobj_sub H); [exact OBD| unfold sk_num, zlength; lia|].
        cbn [cells_size csize Nat.add]. unfold sk_num, zlength in NC |- *. lia. }
      assert (FR2 : rw_cells asegs m2 (bv_unsigned spi) fr).
      { eapply (xpres_rw_cells' H); [exact XP02| exact FR| left; lia| constructor]. }
      assert (SHa2 : addressable m2 a 56).
      { eapply (ashobj_addressable_xpres H HH); [exact HP| exact SUB1| exact CSP| exact OBH| unfold AAPP_HI; lia| exact SHa| exact XP02| constructor]. }
      assert (SHd2 : addressable m2 (sk_data K) (8 * sk_cap K)).
      { eapply (ashobj_addressable_xpres H HH); [exact HP| exact SUB1| exact CSP| exact OBD| unfold AAPP_HI; lia| exact SHd| exact XP02| constructor]. }
      assert (ACCa2 : accessible m2 a 56) by (eapply addressable_accessible; [exact SHa2| lia| lia| unfold AAPP_HI; lia]).
      assert (CH2 : as_chain H m2 (bv_unsigned spi + 112) CH).
      { eapply (chain_via_apres H HH); [exact CH1| apply (xpres_nil_apres H); exact XP2| intros fp' ra' Hin; specialize (CHS _ _ Hin); lia]. }
      assert (CHc2 : as_chain H m2 curc CHc).
      { eapply (chain_via_apres H HH); [exact CHc1| apply (xpres_nil_apres H); exact XP2| intros fp' ra' Hin; specialize (CHCS _ _ Hin); lia]. }
      assert (ND' : List.NoDup (map blk_id (blocks_SK a K ++ eblocks rest xs))) by (eapply nodup_ids_drop_mid; exact ND).
      destruct (ep_rest_frame LB LB1 m m2 (bv_unsigned spi) (blocks_E p x) rest xs F2' S2' KEEP ltac:(rewrite map_app in ND; apply NoDup_app_remove_l in ND; exact ND) XP02
                  ltac:(intros b Hb; pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & Q5 & _); pose proof aceil_range; lia)) as [F2'' S2''].
      (* [comment removed for export] *)
      destruct rest as [|p2 rest'].
      - (* [comment removed for export] *)
        inversion F2''; subst. cbn [length] in NUM.
        eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply apf_segN_last with (K := K) (pad := pad) (i := i); [exact HDR2| lia| lia| lia| exact ACCa2| exact MI2]|].
        intros msF3 mo3 KREL3 MP3 (w0 & w3 & w4 & VIS3).
        eapply KONT; try eassumption.
        + cbn [eblocks combine map concat fst snd]. rewrite app_nil_r. exact PERM2.
        + eapply (ah_mpres_trans H HH); [| exact MP3]. eapply (ah_mpres_trans H HH); [exact MP1| exact MP2].
        + cbn [ecost_sum fold_right]. lia.
      - (* [comment removed for export] *)
        cbn [length] in NUM.
        eapply (ahh_evt_then H HH); [exact KREL2| exact VIS2| eapply apf_segN_more with (K := K) (pad := pad) (i := i); [exact HDR2| lia| lia| lia| exact ACCa2| exact MI2]|].
        intros msF3 mo3 KREL3 MP3 (w0 & VIS3).
        replace (i + 1) with (Z.of_nat (length (done ++ [p]))) in VIS3 by (rewrite length_app; cbn [length]; unfold i; lia).
        eapply (IH xs (done ++ [p])) with (lo := lo) (B := B) (LB := LB1) (s := s2) (K := K) (pad := pad) (errv := errv) (fr := fr) (junk := junk) (CH := CH) (curc := curc) (CHc := CHc);
          [congruence| rewrite <- app_assoc; exact EL| exact XL| exact F2''| exact S2''| exact ND'| exact VIS3| ..]; try eassumption; try lia.
        + intros rax' y0 y1 y2 d0 d1 d2 d3 d4 d5 d6 d7 y3 y4 s10y y5 y6 y7 y8 msF' m' mo' s' LB' PERM' HP' KREL' MP' AUX' ST' ERR' MI' IM' GM' GG' FR' HDR' ARR' JK' SHa' SHd' AC' CH' CHc' AL' XP' VIS'.
          eapply KONT; try eassumption.
          * change (eblocks (p :: p2 :: rest') (x :: xs)) with (blocks_E p x ++ eblocks (p2 :: rest') xs). rewrite <- app_assoc.
            eapply Permutation_trans; [apply Permutation_app_head; exact PERM'| exact PERM2].
          * eapply (ah_mpres_trans H HH); [| exact MP']. eapply (ah_mpres_trans H HH); [| exact MP3]. eapply (ah_mpres_trans H HH); [exact MP1| exact MP2].
          * cbn [ecost_sum fold_right] in *. fold (ecost_sum X ecost xs) in *. lia.
          * eapply xpres_trans; [| exact XP'].
            eapply (xpres_weaken H); [exact XP02| lia| | auto]. intros b Hb. eapply Permutation_in; [exact PERM'| apply in_or_app; right; exact Hb].
    Qed.

    Lemma skpopfree_spec_in : skpopfree_stmt_gen H X EP blocks_E G PFe ecost eshad FN estack.
    Proof using HH EF EPF EPO GF ESF EC0 FNR FNE.
      unfold skpopfree_stmt_gen. intros _ _ _ _ _ _ _ _. intros until CH.
      intros VIS A0 A1 SO [SH1 SH2] TH XL F2 S2 ND HP KREL AUX SPB ST CEIL LO ERR MI TP SP16 AC CHN CHS PF HAL IM GM GG RAE. subst a0 a1 tp.
      rewrite unsigned_lit in ERR by (unfold ATP; lia). fold (eblocks (sk_elems K) xs) in ND |- *.
      unfold SKPOPFREE_STACK, FR_sk_pop_free in LO.
      assert (LO' : lo <= bv_unsigned sp - 112 - 16 - estack /\ lo <= bv_unsigned sp - 112 - 16 - CFREE_STACK) by lia.
      acb. pose proof (aword_range sp) as SPR. pose proof (aword_range ra) as RAR. pose proof (aword_range s0) as S0R.
      assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
      assert (CF0 : 0 <= CFREE_STACK) by (unfold CFREE_STACK, AFREE_STACK; lia).
      assert (CSP0 : aceil <= bv_unsigned sp) by lia. assert (CSP : aceil <= bv_unsigned sp + -112) by lia.
      pose proof (ACONST_shbase m AC) as [GSB SHB0].
      destruct SO as ((pad & PL & HDR) & POS & HIN & NC & CAP & SRT & ELR & DAT).
      pose proof (ah_blocks H HH _ _ _ _ HP HIN) as (K1 & K2 & K3 & K4 & K5 & K6 & K7). cbn [blk_addr blk_size fst snd] in K1, K2, K3, K5, K7. clear K4 K6.
      unfold SK_SIZE in K3, K5, K7, SH1.
      pose proof (aapp_bounds a 56 K7 ltac:(lia)) as (AB1 & AB2 & AB3 & AB4 & AB5). unfold AAPP_HI in AB3.
      assert (ACC0 : accessible m a 56) by (eapply addressable_accessible; [exact SH1| lia| lia| unfold AAPP_HI; lia]).
      pose proof (ah_costs H HH) as (CMz & CMM & CFz & CFM & _).
      assert (ECR : 0 <= ecost_sum X ecost xs).
      { clear - EC0. unfold ecost_sum. induction xs as [|y ys IHy]; cbn [fold_right]; [lia|]. pose proof (EC0 y). lia. }
      unfold SK_SIZE in HAL. pose proof (CFz (8 * sk_cap K) ltac:(lia)) as CF8. pose proof (CFz 56 ltac:(lia)) as CF56.
      set (spi := Z_to_bv 64 (bv_unsigned sp + -112)).
      assert (SPI : bv_unsigned spi = bv_unsigned sp + -112) by (unfold spi; rewrite unsigned_lit by lia; reflexivity).
      assert (PFT : pf_ok (as_TR H) (pf_shift APF_RA_FREE PF_cfree ++ PF_cfree) (bv_unsigned ra) CH).
      { eapply pf_ok_incl; [exact PF|]. unfold PF_skpopfree, PF_skfree, APF_RA_FREE, R_sk_free_CRYPTO_free. intros q Hq. rewrite !in_app_iff in *. tauto. }
      assert (PFE : pf_ok (as_TR H) PFe APF_RA_ELEM ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { eapply pf_ok_call; [exact PF|]. unfold PF_skpopfree, APF_RA_ELEM, R_sk_pop_free_freefunc. intros q Hq. rewrite !in_app_iff. left. exact Hq. }
      set (Q := skpopfree_post H X blocks_E G ecost ra sp gp (Z_to_bv 64 ATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB a K xs lo B errv m mo).
      (* [comment removed for export] *)
      assert (FIN : forall (m1 : mem), xpres H LB (bv_unsigned sp) [] m m1 ->
                forall (rax' u0 u1 u2 c0 c1 c2 c3 c4 c5 c6 c7 : word) (s2y s3y s4y s7y s8y s9y s10y s11y : word) (u3 u4 u5 u6 : word) (msF' : machine_state) (m' : mem) (mo' : Model) (s' : as_St H) (LB' : list block) (j : list byte),
         Permutation (eblocks (sk_elems K) xs ++ LB') LB -> as_RHEAP H s' LB' m' -> as_AKREL H s' (mkCfg msF' mo') -> as_MPRES H mo mo' ->
         as_rauxv_ok H m' B -> stk asegs m' lo (bv_unsigned spi) -> rw_cells asegs m' (ATP + -164) [C4 errv] -> mem_inv asegs m' ->
         IMPL_mem m' -> GOT_mem m' -> G m' -> rw_cells asegs m' (bv_unsigned spi) (apf_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) -> rw_cells asegs m' a (sk_hdr_cells K pad) ->
         ((sk_cap K = 0 /\ sk_data K = 0)
          \/ (4 <= sk_cap K /\ 0 < sk_data K /\ (a + 56 <= sk_data K \/ sk_data K + 8 * sk_cap K <= a) /\ In (sk_did K, sk_data K, 8 * sk_cap K) LB
              /\ u64arr asegs m' (sk_data K) (map wz (sk_elems K))
              /\ (exists junk, rw_cells asegs m' (sk_data K + 8 * sk_num K) [CB (Z.to_nat (8 * (sk_cap K - sk_num K))) junk])
              /\ addressable m' (sk_data K) (8 * sk_cap K))) ->
         addressable m' a 56 -> ACONST m' -> as_chain H m' (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH) -> as_chain H m' (bv_unsigned s0) CH ->
         as_AL H s' >= as_AL H s - ecost_sum X ecost xs ->
         xpres H LB' (bv_unsigned spi) [] m1 m' ->
         as_VIS H s' msF' = MS (mkR rax' spi gp (Z_to_bv 64 ATP) u0 u1 u2 sp (Z_to_bv 64 a) c0 c1 c2 c3 c4 c5 c6 c7
                                   s2y s3y s4y (Z_to_bv 64 ASHB) (Z_to_bv 64 (Z.shiftr a 3 + ASHB)) s7y s8y s9y s10y s11y u3 u4 u5 u6)
                              F (Z_to_bv 64 APF_TAIL) fc None m' (seg_rom asegs) ->
         as_SR H Q (mkCfg msF' mo')).
      { intros m1 XP01. intros until j. intros PERM' HP' KREL' MP' AUX' ST' ERR' MI' IM' GM' GG' FR' HDR' DAT' SHa' AC' CH1' CHN' AL' XP' VIS'.
        rewrite SPI in ST', FR', XP'.
        assert (KEEP : forall b, In b (blocks_SK a K) -> In b LB -> In b LB').
        { intros b Hb HbL. eapply perm_in_rest; [exact PERM'| exact HbL|]. intros Kb. eapply (nodup_ids_excl (blocks_SK a K) (eblocks (sk_elems K) xs)); [exact ND| exact Hb| exact Kb]. }
        assert (SUB' : forall b, In b LB' -> In b LB) by (intros b Hb; eapply Permutation_in; [exact PERM'| apply in_or_app; right; exact Hb]).
        eapply (ah_mono H HH).
        { unfold spi in VIS'.
          eapply apf_tail_spec with (lo := lo) (B := B) (LB := LB') (s := s') (K := K) (pad := pad) (errv := errv) (CH := CH);
            [exact VIS'| exact HDR'| exact POS| ..]; try eassumption; try lia.
          all: first
            [ apply KEEP; [left; reflexivity| exact HIN]
            | destruct DAT' as [D0|(D4 & DP & DDJ & DIN & AR' & JK' & SD')]; [left; exact D0| right];
              split; [exact D4|]; split; [exact DP|]; split; [unfold SK_SIZE; exact DDJ|]; split; [| split; [exact AR'| split; [exact JK'| exact SD']]];
              apply KEEP; [| exact DIN]; unfold blocks_SK; replace (sk_cap K =? 0) with false by (symmetry; apply Z.eqb_neq; lia); right; left; reflexivity
            | unfold SK_SIZE; exact SHa'
            | unfold CFREE_STACK, AFREE_STACK in *; lia
            | match goal with |- ?G => idtac "LEFT:" G end ]. }
        intros [msF4 mo4] PO. unfold apf_tail_post in PO. cbn [cfg_ms cfg_model] in PO.
        destruct PO as (v0 & v1 & v2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & v3 & v4 & v5 & v6 & m4 & s4' & LB4 &
                        VIS4 & KREL4 & MP4 & MI4 & AC4 & ST4 & ERR4 & AUX4 & PERM4 & HP4 & XP4 & IM4 & GM4 & AL4).
        assert (SUB4 : forall b, In b LB4 -> In b LB') by (intros b Hb; eapply Permutation_in; [exact PERM4| apply in_or_app; right; exact Hb]).
        unfold Q, skpopfree_post. cbn [cfg_ms cfg_model].
        exists v0, v1, v2, d0, d1, d2, d3, d4, d5, d6, d7, v3, v4, v5, v6, m4, s4', LB4.
        split; [exact VIS4|]. split; [exact KREL4|]. split; [eapply (ah_mpres_trans H HH); [exact MP'| exact MP4]|]. split; [exact MI4|]. split; [exact AC4|]. split; [exact ST4|].
        split; [rewrite unsigned_lit by (unfold ATP; lia); exact ERR4|]. split; [exact AUX4|].
        split.
        { fold (eblocks (sk_elems K) xs). eapply Permutation_trans; [apply Permutation_app_swap_app|].
          eapply Permutation_trans; [apply Permutation_app_head; exact PERM4| exact PERM']. }
        split; [exact HP4|].
        split.
        { eapply xpres_trans; [eapply (xpres_weaken H); [exact XP01| lia| intros b Hb; apply SUB', SUB4; exact Hb| auto]|].
          eapply xpres_trans; [eapply (xpres_weaken H); [exact XP'| lia| exact SUB4| auto]| exact XP4]. }
        split; [exact IM4|]. split; [exact GM4|].
        split; [eapply GF; [exact GG'| exact XP4| lia]|].
        unfold SK_SIZE. lia. }
      assert (WORLD : forall m1, munch [(lo, bv_unsigned sp)] m m1 -> wmono asegs m m1 ->
                xpres H LB (bv_unsigned sp) [] m m1 /\ as_RHEAP H s LB m1 /\ as_rauxv_ok H m1 B /\ rw_cells asegs m1 (ATP + -164) [C4 errv]
                /\ IMPL_mem m1 /\ GOT_mem m1 /\ G m1 /\ ACONST m1 /\ addressable m1 a 56
                /\ (sk_cap K <> 0 -> addressable m1 (sk_data K) (8 * sk_cap K)) /\ as_chain H m1 (bv_unsigned s0) CH).
      { intros m1 MU1 WM1.
        assert (CW : Forall (aclient_write_ok H LB) [(lo, bv_unsigned sp)]) by (apply Forall_cons; [left; cbn [fst snd]; lia| apply Forall_nil]).
        assert (XP1 : xpres H LB (bv_unsigned sp) [] m m1)
          by (eapply (xpres_of_munch H s LB _ [] _ m m m1); [exact HH| exact HP| exact MU1| exact WM1|]; apply Forall_cons; [left; cbn; lia| apply Forall_nil]).
        split; [exact XP1|].
        split; [eapply (ah_RHEAP_frame H HH); [exact HP| exact MU1| exact WM1| exact CW]|].
        split; [eapply (ah_rauxv_frame H HH); [exact AUX| exact MU1| exact WM1| exact CW]|].
        split; [eapply errno_across; [exact ERR| exact MU1| exact WM1| unfold ATP; cbn; lia]|].
        split; [eapply IMPL_across; [exact MU1| exact WM1| unfold A_malloc_impl; cbn; lia| exact IM]|].
        split; [eapply GOT_across; [exact MU1| exact WM1| unfold A_got_CRYPTO_malloc; cbn; lia| exact GM]|].
        split; [eapply GF; [exact GG| exact XP1| lia]|].
        split. { eapply ACONST_frame; [exact AC| exact MU1| exact WM1|]. apply Forall_cons; [| apply Forall_nil].
                 apply aconst_ok_high; cbn [fst snd]; unfold sh, AIMG_TOP; rewrite ?ASHADOW_BASE_val; lia. }
        split. { eapply addressable_transport; [exact SH1| exact MU1| exact WM1|].
                 pose proof (sh_aapp_range a 56 K7 ltac:(lia)) as (Sx1 & Sx2 & Sx3). unfold AHI_LO in Sx3. cbn [disjoint_from fst snd]. split; [lia| exact I]. }
        split. { intros CNZ. destruct DAT as [[C0 _]|(D4 & DP & DDJ & DIN & _)]; [lia|].
                 pose proof (ah_blocks H HH _ _ _ _ HP DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E3, E5, E7.
                 eapply addressable_transport; [exact (SH2 CNZ)| exact MU1| exact WM1|].
                 pose proof (sh_aapp_range (sk_data K) (8 * sk_cap K) E7 ltac:(lia)) as (Sx1 & Sx2 & Sx3). unfold AHI_LO in Sx3. cbn [disjoint_from fst snd]. split; [lia| exact I]. }
        eapply (achain_below H HH m m1); [exact CHN| exact CHS| exact MU1|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
      (* [comment removed for export] *)
      assert (CHX : forall m1 j, rw_cells asegs m1 (bv_unsigned sp + -112) (apf_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) ->
                as_chain H m1 (bv_unsigned s0) CH -> as_chain H m1 (bv_unsigned sp) ((bv_unsigned sp, bv_unsigned ra) :: CH)).
      { intros m1 j FR1 CH0. eapply (ah_chain_cons H HH); [exact CH0| lia| lia| exact SP16| lia| lia|].
        pose proof FR1 as FR2. unfold apf_frame in FR2.
        change ([CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
          with ([CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] ++ [C8 s0; C8 ra]) in FR2.
        apply (proj1 (rw_cells_app asegs _ _ _ _)) in FR2. destruct FR2 as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ Nat.mul Pos.mul] in FR2.
        replace (bv_unsigned sp - 16) with (bv_unsigned sp + -112 + 96) by lia.
        first [exact FR2 | revert FR2; rewrite !Z_to_bv_bv_unsigned; intros FR2; exact FR2]. }
      destruct (sk_elems K) as [|p0 rest0] eqn:EL.
      - (* [comment removed for export] *)
        assert (N0 : sk_num K = 0) by (unfold sk_num, zlength; rewrite EL; reflexivity).
        eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply apf_seg0_none with (lo := lo) (K := K) (pad := pad);
          [exact HDR| exact N0| exact POS| exact K2| unfold SK_SIZE in *; lia| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
        intros msF1 mo1 KREL1 MP1 (w0 & w9 & m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
        destruct (WORLD m1 MU1 WM1) as (XP1 & HP1 & AUX1 & ERR1 & IM1 & GM1 & GG1 & AC1 & SHa1 & SHd1 & CHN1).
        eapply (FIN m1 XP1) with (LB' := LB) (s' := s); try eassumption; try (rewrite SPI; eassumption).
        + destruct xs; [| cbn in XL; discriminate]. cbn. apply Permutation_refl.
        + destruct DAT as [D0|(D4 & DP & DDJ & DIN & AR & JK)]; [left; exact D0| right]. unfold SK_SIZE in DDJ.
          split; [exact D4|]. split; [exact DP|]. split; [exact DDJ|]. split; [exact DIN|]. split; [| split].
          * pose proof (ah_blocks H HH _ _ _ _ HP DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E5.
            eapply u64arr_across; [exact MU1| exact WM1| | exact AR]. rewrite length_map. unfold sk_num, zlength in NC. cbn [disjoint_from fst snd length Z.of_nat]. split; [lia| exact I].
          * destruct JK as (junk & JK). exists junk. eapply rw_cells_transport; [exact JK| exact MU1| exact WM1|].
            pose proof (ah_blocks H HH _ _ _ _ HP DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E5. cbn [disjoint_from cells_size csize Nat.add fst snd].
            unfold sk_num, zlength in NC |- *. split; [lia| exact I].
          * apply SHd1. lia.
        + exact (CHX m1 j FR1 CHN1).
        + lia.
        + apply xpres_refl.
      - (* [comment removed for export] *)
        assert (NP : 0 < sk_num K) by (unfold sk_num, zlength; rewrite EL; cbn [length]; lia).
        destruct DAT as [[C0 _]|(D4 & DP & DDJ & DIN & ARR & JK)]; [lia|]. destruct JK as (junk & JK). unfold SK_SIZE in DDJ.
        pose proof (ah_blocks H HH _ _ _ _ HP DIN) as (E1 & E2 & E3 & E4 & E5 & E6 & E7). cbn [blk_addr blk_size fst snd] in E1, E3, E5, E7. clear E2 E4 E6.
        eapply (ahh_evt_then H HH); [exact KREL| exact VIS| eapply apf_seg0_more with (lo := lo) (K := K) (pad := pad);
          [exact HDR| lia| exact POS| exact K2| unfold SK_SIZE in *; lia| exact ACC0| exact GSB| exact SHB0| exact ST| exact CEIL| lia| exact MI]|].
        intros msF1 mo1 KREL1 MP1 (w0 & w1 & w9 & m1 & j & VIS1 & MU1 & WM1 & MI1 & ST1 & FR1 & HDR1).
        destruct (WORLD m1 MU1 WM1) as (XP1 & HP1 & AUX1 & ERR1 & IM1 & GM1 & GG1 & AC1 & SHa1 & SHd1 & CHN1).
        assert (ARR1 : u64arr asegs m1 (sk_data K) (map wz (sk_elems K))).
        { eapply u64arr_across; [exact MU1| exact WM1| | rewrite EL; exact ARR]. rewrite length_map. unfold sk_num, zlength in NC. cbn. lia. }
        assert (JK1 : rw_cells asegs m1 (sk_data K + 8 * sk_num K) [CB (Z.to_nat (8 * (sk_cap K - sk_num K))) junk]).
        { eapply rw_cells_transport; [exact JK| exact MU1| exact WM1|]. cbn [disjoint_from cells_size csize Nat.add fst snd]. unfold sk_num, zlength in NC |- *. split; [lia| exact I]. }
        assert (F21 : Forall2 (fun p x => EP LB m1 p x) (p0 :: rest0) xs /\ Forall2 (fun p x => eshad m1 p x) (p0 :: rest0) xs).
        { eapply (ep_rest_frame LB LB m m1 (bv_unsigned sp) []); [exact F2| exact S2| auto| | exact XP1|].
          - cbn [app]. rewrite map_app in ND. apply NoDup_app_remove_l in ND. exact ND.
          - intros b Hb. pose proof (ah_blocks H HH _ _ _ _ HP Hb) as (_ & _ & _ & _ & Q5 & _). pose proof aceil_range. lia. }
        destruct F21 as [F21 S21].
        assert (SP16' : (bv_unsigned sp + -112) mod 16 = 0) by (replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) by lia; rewrite Zminus_mod, SP16; reflexivity).
        eapply (pf_loop (p0 :: rest0) xs []) with (spi := spi) (lo := lo) (B := B) (LB := LB) (s := s) (K := K) (pad := pad) (errv := errv)
                                               (fr := apf_frame j s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra) (junk := junk)
                                               (CH := (bv_unsigned sp, bv_unsigned ra) :: CH) (curc := bv_unsigned s0) (CHc := CH); rewrite ?SPI;
          try eassumption; try congruence; try lia.
        all: try (replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia).
        all: lazymatch goal with
             | |- as_VIS _ _ _ = _ => rewrite Z_to_bv_bv_unsigned; cbn [length Z.of_nat Z.mul]; exact VIS1
             | |- u64arr _ _ _ _ => first [exact ARR1 | rewrite EL; exact ARR1 | rewrite <- EL; exact ARR1]
             | |- addressable _ (sk_data _) _ => apply SHd1; lia
             | |- as_chain _ _ ?c ((?c, _) :: _) => exact (CHX m1 j FR1 CHN1)
             | |- forall fp' ra', In _ (_ :: _) -> _ => intros fp' ra' [E|Hin]; [injection E as <- <-; lia| specialize (CHS _ _ Hin); lia]
             | |- forall fp' ra', In _ _ -> _ => intros fp' ra' Hin; specialize (CHS _ _ Hin); lia
             | |- _ mod 16 = 0 => exact SP16'
             | |- _ => idtac
             end.
        + intros rax' y0 y1 y2 d0 d1 d2 d3 d4 d5 d6 d7 y3 y4 s10y y5 y6 y7 y8 msF' m' mo' s' LB' PERM' HP' KREL' MP' AUX' ST' ERR' MI' IM' GM' GG' FR' HDR' ARR' JK' SHa' SHd' AC' CH' CHc' AL' XP' VIS'.
          rewrite ?SPI in CH', VIS', ST', FR', XP'. replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) in CH', VIS' by lia.
          rewrite Z_to_bv_bv_unsigned in VIS'.
          eapply (FIN m1 XP1); rewrite ?SPI; try eassumption.
          { eapply (ah_mpres_trans H HH); [exact MP1| exact MP']. }
          right. split; [exact D4|]. split; [exact DP|]. split; [exact DDJ|]. split; [exact DIN|]. split; [first [exact ARR' | rewrite EL in ARR'; exact ARR' | rewrite <- EL; exact ARR']| split; [exists junk; exact JK'| exact SHd']].
    Qed.
  End Elem.

  Theorem askpopfree_spec : forall X EP blocks_E G PFe ecost eshad FN estack, skpopfree_stmt_gen H X EP blocks_E G PFe ecost eshad FN estack.
  Proof using HH.
    intros X EP blocks_E G PFe ecost eshad FN estack EF EPF EPO GF ESF EC0 FNR FNE.
    exact (skpopfree_spec_in X EP blocks_E G PFe ecost eshad FN estack EF EPF EPO GF ESF EC0 FNR FNE EF EPF EPO GF ESF EC0 FNR FNE).
  Qed.
End W.
