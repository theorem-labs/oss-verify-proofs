(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun Stdio SjModel AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Atp_h_defs.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3 RT_iface5. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_libiface D_auxv Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_new Sj_h_alloc Sj_stage2_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA Atp_setcapA Atp_activewA Atp_defsA Atp_h_defsA Atp_pidiA Atp_pdtorA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_lf1A El_lf2A El_lf2bA El_costA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition chars (bs : list byte) : list Z := map bv_unsigned bs.
Definition el_remA (bs : list byte) : list byte := if 10 <=? Z.of_nat (length bs) then skipn 10 bs else [].
Lemma chars_length : forall bs, zlength (chars bs) = Z.of_nat (length bs).
Proof. intros bs. unfold zlength, chars. rewrite length_map. reflexivity. Qed.
Lemma to_bytes_chars : forall bs, to_bytes (chars bs) = bs.
Proof.
  intros bs. unfold to_bytes, chars. rewrite map_map. rewrite <- (map_id bs) at 2. apply map_ext. intros b.
  apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.
Lemma chars_range : forall bs, Forall (fun c => 0 <= c < 256) (chars bs).
Proof.
  induction bs as [|b bs IH]; [constructor|]. cbn. constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 8) with 256 in X. lia.
Qed.
Lemma el_remA_length : forall bs, Z.of_nat (length (el_remA bs)) = el_fdsA (Z.of_nat (length bs)).
Proof.
  intros bs. unfold el_remA, el_fdsA. destruct (Z.leb_spec 10 (Z.of_nat (length bs))); [| reflexivity]. rewrite length_skipn. lia.
Qed.

Definition el_PA (bs : list byte) : nat := atp_P (chars (el_remA bs)).
Definition el_elsA (d : Z) (bs : list byte) : list (Z * Z) := atp_elsA (el_fddA d (Z.of_nat (length bs))) (chars (el_remA bs)).

Definition el_s0A (d : Z) (bs : list byte) : Z * Z := nth 0 (el_elsA d bs) (0, 0).
Definition el_s1A (d : Z) (bs : list byte) : Z * Z := nth 1 (el_elsA d bs) (0, 0).

Definition el_vcostA (bs : list byte) : Z := 2 + vcost_pushes (el_PA bs) 0 0.

Lemma el_vcost_bound : forall bs, Z.of_nat (length bs) < 2^26 -> el_vcostA bs <= 2^31 + 2^26.
Proof.
  intros bs H. unfold el_vcostA, el_PA.
  assert (L : zlength (chars (el_remA bs)) < 2^26).
  { rewrite chars_length. unfold el_remA. destruct (Z.leb_spec 10 (Z.of_nat (length bs))); [rewrite length_skipn; lia| cbn; lia]. }
  pose proof (vcb_ok (chars (el_remA bs)) L). lia.
Qed.

Section Phases.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition el_baseA (Σ0 Σ : rts RT) (m0 m : mem) (X : lfA) (d : Z) (bs : list byte)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (h3 : list byte) : Prop :=
  ART RT Σ m /\ mem_inv asegs m /\ stk asegs m (lf_lo X) (lf_S1 X)
  /\ stk asegs m (lf_S1 X + 152) (lf_usp X - 104)
  /\ rw_cells asegs m (lf_usp X - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
  /\ rw_cells asegs m (lf_F X) (fz_hdr (C8 (wz 0x41b58ab3)) (C8 (wz 0x126fb)) (C8 (wz 0xb1608)) h3)
  /\ bytes_at asegs m d bs /\ el_libA m
  /\ rt_pres_fp (rt_live RT Σ0) [] (lf_usp X) EL_LIB_FP m0 m
  /\ rt_frames RT Σ = [(lf_F X, 4%nat)] /\ rt_sp0 RT Σ = rt_sp0 RT Σ0.

Definition cutS (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (K : config -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (t0 t1 t2 a2 a3 a4 a5 a6 a7 x9 x10 x11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (j0 j1 j2 j8 j10 j15 jr h3 t jv j56 jp j176 je j224 jos j528 : list byte) (idx : word) (act sel : Z),
    el_baseA Σ0 Σ m0 m X d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 ->
    rw_cells asegs m (lf_S1 X) (el_locals3 j0 j1 j2 idx act j8 (lf_F X) j10 sel (el_fddA d (Z.of_nat (length bs))) (el_fdsA (Z.of_nat (length bs))) j15 jr) ->
    0 <= act < 32 -> 0 <= sel < 8 ->
    rw_cells asegs m (shad (lf_F X)) (el_shadowA 0 (-8) (-8) (-8) t) ->
    rw_cells asegs m (lf_F X + 32) [CB 24 jv] -> rw_cells asegs m (lf_F X + 56) [CB 40 j56] -> rw_cells asegs m (lf_F X + 96) [CB 80 jp] ->
    rw_cells asegs m (lf_F X + 176) [CB 32 j176] -> rw_cells asegs m (lf_F X + 208) [CB 16 je] -> rw_cells asegs m (lf_F X + 224) [CB 16 j224] ->
    rw_cells asegs m (lf_F X + 240) [CB 288 jos] -> rw_cells asegs m (lf_F X + 528) [CB 488 j528] ->
    rt_live RT Σ = rt_live RT Σ0 -> rt_credit RT Σ0 - 1 <= rt_credit RT Σ -> frm0 fc ->
    aevt Σ K (MS (mkR (wz EL_SPLITRET_A) (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X))
                    (wz (lf_F X + 32)) (wz (lf_S1 X + 128)) a2 a3 a4 a5 a6 a7
                    (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 96)) (wz (lf_F X + 208)) (wz SHB) (wz (lf_F X)) x9 x10 x11 t3 t4 t5 t6)
               F (wz ATPA_SPLITINTO) fc None m (seg_rom asegs)).

Definition cutV (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (K : config -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (j0 j1 j2 j8 j10 j15 jr h3 t j56 jp j176 je j224 jos j528 : list byte) (idx : word) (act sel A : Z),
    el_baseA Σ0 Σ m0 m X d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 ->
    rw_cells asegs m (lf_S1 X) (el_locals3 j0 j1 j2 idx act j8 (lf_F X) j10 sel
                                  (el_fddA d (Z.of_nat (length bs)) + el_fdsA (Z.of_nat (length bs))) 0 j15 jr) ->
    0 <= act < 32 -> 0 <= sel < 8 ->
    rw_cells asegs m (shad (lf_F X)) (el_shadowA 0 (-8) (-8) (-8) t) ->
    vrepA m (lf_F X + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs) ->
    rw_cells asegs m (lf_F X + 56) [CB 40 j56] -> rw_cells asegs m (lf_F X + 96) [CB 80 jp] ->
    rw_cells asegs m (lf_F X + 176) [CB 32 j176] -> rw_cells asegs m (lf_F X + 208) [CB 16 je] -> rw_cells asegs m (lf_F X + 224) [CB 16 j224] ->
    rw_cells asegs m (lf_F X + 240) [CB 288 jos] -> rw_cells asegs m (lf_F X + 528) [CB 488 j528] ->
    vliveA (rt_live RT Σ) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (rt_live RT Σ0) ->
    rt_credit RT Σ0 - el_vcostA bs <= rt_credit RT Σ -> frm0 fc ->
    aevt Σ K (MS (mkR x1 (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X)) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 96)) (wz (lf_F X + 208)) (wz SHB) (wz (lf_F X)) (wz A) (wz 16) x11 t3 t4 t5 t6)
               F (wz EL_VEC2_A) fc None m (seg_rom asegs)).

Definition el_vec_cps : Prop :=
  forall (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (K : config -> Prop),
    fdfs_only PMc -> mat_stable PMc -> lfA_ok X -> rt_sp0 RT Σ0 - STACK_WIN <= lf_lo X ->
    0 < d -> Z.of_nat (length bs) < 2^26 ->
    ((exists p n, In (p, n) (rt_live RT Σ0) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
    (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) -> Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
    cutV Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K ->
    cutS Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K.

Definition cutX2 (Wx : rts RT -> mem -> Prop) (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (crd : Z) (K : config -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x9 x10 x11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (LC : list cell) (h3 t : list byte) (p e : Z) (A : Z),
    Wx Σ m -> mem_inv asegs m -> stk asegs m (lf_lo X) (lf_S1 X) ->
    stk asegs m (lf_S1 X + 152) (lf_usp X - 104) -> rw_cells asegs m (lf_usp X - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells asegs m (lf_F X) (fz_hdr (C8 (wz 0x41b58ab3)) (C8 (wz 0x126fb)) (C8 (wz 0xb1608)) h3) ->
    el_libA m -> rt_pres_fp (rt_live RT Σ0) [] (lf_usp X) EL_LIB_FP m0 m ->
    rt_frames RT Σ = [(lf_F X, 4%nat)] -> rt_sp0 RT Σ = rt_sp0 RT Σ0 ->
    cells_size LC = 152%nat -> rw_cells asegs m (lf_S1 X) LC ->
    rw_cells asegs m (shad (lf_F X)) (el_shadowA 0 p e (-8) t) ->
    vrepA m (lf_F X + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs) ->
    vliveA (rt_live RT Σ) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (rt_live RT Σ0) ->
    crd <= rt_credit RT Σ -> frm0 fc ->
    aevt Σ K (MS (mkR x1 (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X)) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 96)) x6 x7 (wz (lf_F X)) x9 x10 x11 t3 t4 t5 t6)
               F (wz EL_EXIT2_A) fc None m (seg_rom asegs)).

Definition el_gate_pcA (r : word) : Z := if bv_eqb r (wz 0) then EL_DISPATCH_A else EL_EXIT_A.
Definition el_localsG (X : lfA) (j0 : list byte) (p0 l0 : Z) (idx : word) (act : Z) (j64 j96 : list byte) (sel fdd : Z) (j121 : list byte) (r : word) (j20 : list byte) : list cell :=
  [CB 24 j0; C8 (wz p0); C8 (wz l0); C8 idx; C8 (wz (lf_F X + 240)); C8 (wz act); CB 24 j64; C8 (wz (lf_F X))] ++ res_cellsA (lf_F X + 120) r j20
  ++ [CB 4 j96; C4 (wz sel); C8 (wz fdd); C8 (wz 0); C1 (Z_to_bv 8 0); CB 7 j121].
Definition cutG (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (K : config -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x9 x10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (j0 j64 j96 j121 h3 t j56 j176 j224 jos j528 j20 : list byte) (idx : word) (act sel A impl ix oc ia tape sbuf cap : Z) (r : word),
    el_baseA Σ0 Σ m0 m X d bs ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 h3 ->
    rw_cells asegs m (lf_S1 X) (el_localsG X j0 (fst (el_s0A d bs)) (snd (el_s0A d bs)) idx act j64 j96 sel (el_fddA d (Z.of_nat (length bs)) + el_fdsA (Z.of_nat (length bs))) j121 r j20) ->
    0 <= act < 32 -> 0 <= sel < 8 -> bv_unsigned r < 64 ->
    rw_cells asegs m (shad (lf_F X)) (el_shadowA 0 0 0 (-8) t) ->
    vrepA m (lf_F X + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs) ->
    rw_cells asegs m (lf_F X + 56) [CB 40 j56] ->
    pdone RT Σ m (lf_F X + 96) (vblockA A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) ++ rt_live RT Σ0) ->
    pidA_st RT Σ m (lf_F X + 96) impl ix oc ia tape sbuf cap ->
    s2a_okres tape sbuf (roundup64 (cap + 3)) (al_sbuf cap) r m -> 32 <= cap <= 2^20 + 32 ->
    rw_cells asegs m (lf_F X + 176) [CB 32 j176] ->
    rw_cells asegs m (lf_F X + 208) (if bv_eqb r (wz 0) then [C8 (wz (lf_F X + 120)); C8 (wz 1)] else [C8 (wz 0); C8 (wz 0)]) ->
    rw_cells asegs m (lf_F X + 224) [CB 16 j224] -> rw_cells asegs m (lf_F X + 240) [CB 288 jos] -> rw_cells asegs m (lf_F X + 528) [CB 488 j528] ->
    rt_live RT Σ = (ia, 1024) :: (oc, 8192) :: (ix, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap)
                     :: vblockA A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) ++ rt_live RT Σ0 ->
    (impl mod 16 = 0 /\ ix mod 16 = 0 /\ oc mod 16 = 0 /\ ia mod 16 = 0 /\ tape mod 16 = 0 /\ sbuf mod 16 = 0) ->
    rt_credit RT Σ0 - el_vcostA bs - 2^28 <= rt_credit RT Σ -> frm0 fc ->
    aevt Σ K (MS (mkR x1 (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X)) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 96)) (wz (lf_F X + 208)) r (wz (lf_F X))
                    x9 x10 (wz (lf_F X + 120)) t3 t4 t5 t6)
               F (wz (el_gate_pcA r)) fc None m (seg_rom asegs)).

Definition cutX (Wx : rts RT -> mem -> Prop) (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (crd : Z) (K : config -> Prop) : Prop :=
  forall (Σ : rts RT) (m : mem) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x6 x7 x9 x10 x11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
         (LC : list cell) (h3 t : list byte) (A : Z) (L0 : list (Z * Z)) (j56 j176 : list byte) (ce : list cell) (jq : list byte),
    Wx Σ m -> mem_inv asegs m -> stk asegs m (lf_lo X) (lf_S1 X) ->
    stk asegs m (lf_S1 X + 152) (lf_usp X - 104) -> rw_cells asegs m (lf_usp X - 104) (fa_saved ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells asegs m (lf_F X) (fz_hdr (C8 (wz 0x41b58ab3)) (C8 (wz 0x126fb)) (C8 (wz 0xb1608)) h3) ->
    el_libA m -> rt_pres_fp (rt_live RT Σ0) [] (lf_usp X) EL_LIB_FP m0 m ->
    rt_frames RT Σ = [(lf_F X, 4%nat)] -> rt_sp0 RT Σ = rt_sp0 RT Σ0 ->
    cells_size LC = 152%nat -> rw_cells asegs m (lf_S1 X) LC ->
    rw_cells asegs m (shad (lf_F X)) (el_shadowA 0 0 0 (-8) t) ->
    vrepA m (lf_F X + 32) A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) (el_elsA d bs) -> rw_cells asegs m (lf_F X + 56) [CB 40 j56] ->
    L0 = vblockA A (vcap_iter (el_PA bs) 0 0) (Z.of_nat (el_PA bs)) ++ rt_live RT Σ0 ->
    pdone RT Σ m (lf_F X + 96) L0 ->
    (forall q, In q L0 -> In q (rt_live RT Σ)) -> Z.of_nat (length (rt_live RT Σ)) <= Z.of_nat (length L0) + 6 ->
    rw_cells asegs m (lf_F X + 176) [CB 32 j176] -> cells_size ce = 16%nat -> rw_cells asegs m (lf_F X + 208) ce -> rw_cells asegs m (lf_F X + 224) [CB 792 jq] ->
    crd <= rt_credit RT Σ -> frm0 fc ->
    aevt Σ K (MS (mkR x1 (wz (lf_S1 X)) gp (wz TPV_A) t0 t1 t2 (wz (lf_usp X)) (wz (lf_S1 X)) a0 a1 a2 a3 a4 a5 a6 a7
                    (wz (lf_F X)) (wz (shad (lf_F X))) (wz (lf_F X + 32)) (wz (lf_F X + 96)) x6 x7 (wz (lf_F X)) x9 x10 x11 t3 t4 t5 t6)
               F (wz EL_EXIT_A) fc None m (seg_rom asegs)).

Definition el_parse_cps : Prop :=
  forall (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (K : config -> Prop),
    fdfs_only PMc -> mat_stable PMc -> lfA_ok X -> rt_sp0 RT Σ0 - STACK_WIN <= lf_lo X ->
    0 < d -> Z.of_nat (length bs) < 2^26 ->
    ((exists p n, In (p, n) (rt_live RT Σ0) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
    (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) -> Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
    cutG Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K ->
    cutX (ART RT) Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rt_credit RT Σ0 - FUZZ_COST) K ->
    cutX2 (ART RT) Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rt_credit RT Σ0 - el_vcostA bs) K ->
    cutV Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K.

Definition el_tailP_cps : Prop :=
  forall (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (crd : Z) (K : config -> Prop),
    fdfs_only PMc -> mat_stable PMc -> lfA_ok X -> rt_sp0 RT Σ0 - STACK_WIN <= lf_lo X ->
    (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) ->
    cutX2 (ART RT) Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K ->
    cutX (ART RT) Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K.

Definition el_disp_cps (W : Z -> rts RT -> mem -> Prop)
    (cutXW : Z -> rts RT -> mem -> lfA -> Z -> list byte -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word -> word ->
             Z -> (config -> Prop) -> Prop) : Prop :=
  forall (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (K : config -> Prop),
    fdfs_only PMc -> mat_stable PMc -> lfA_ok X -> rt_sp0 RT Σ0 - STACK_WIN <= lf_lo X ->
    0 < d -> Z.of_nat (length bs) < 2^26 ->
    ((exists p n, In (p, n) (rt_live RT Σ0) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
    (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) -> Z.of_nat (length (rt_live RT Σ0)) + FUZZ_LIVE <= LIVE_MAX -> FUZZ_COST <= rt_credit RT Σ0 ->
    libc_nl m0 -> io_ssp m0 ->
    el_xdataA m0 -> el_auxvA (lf_usp X) m0 -> lf_usp X <= rt_sp0 RT Σ0 <= lf_usp X + FUZZ_SP0GAP ->
    (forall a, el_liveA a = true -> arm_cpsA RT PMc W a) ->
    cutX (ART RT) Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (rt_credit RT Σ0 - FUZZ_COST) K ->
    (forall c crd, rt_credit RT Σ0 - FUZZ_COST <= c -> cutXW c Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K) ->
    cutG Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 K.

Definition el_tail2_cps : Prop :=
  forall (Σ0 : rts RT) (m0 : mem) (X : lfA) (d : Z) (bs : list byte) (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (crd : Z) (K : config -> Prop),
    fdfs_only PMc -> mat_stable PMc -> lfA_ok X -> rt_sp0 RT Σ0 - STACK_WIN <= lf_lo X ->
    (forall p n, In (p, n) (rt_live RT Σ0) -> 0 < n) ->
    (forall (Σ' : rts RT) (m' : mem) (fc' : bv 32) (F' : bvmap 5 word) (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (lf_lo X) (lf_usp X) -> frm0 fc' ->
        el_libA m' -> rt_pres_fp (rt_live RT Σ0) [] (lf_usp X) EL_LIB_FP m0 m' ->
        rt_live RT Σ' = rt_live RT Σ0 -> rt_frames RT Σ' = [] -> rt_sp0 RT Σ' = rt_sp0 RT Σ0 -> crd <= rt_credit RT Σ' ->
        aevt Σ' K (MS (mkR ra (wz (lf_usp X)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                     F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
    cutX2 (ART RT) Σ0 m0 X d bs ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 crd K.

End Phases.
