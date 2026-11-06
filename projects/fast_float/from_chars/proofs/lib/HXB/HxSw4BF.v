(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Mem Cells Exec Frame Arr Step Image RegsEquiv MState.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require HxGenFp HxSemB HxBaseB HxIntBF HxDefsBF HxDigpBF.

Module HxSw4BWF.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text.Spf_swar.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxSw8BWF.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac ms_eq_tac ::=
  cbv beta delta [mkR];
  repeat first [ reflexivity
               | lazymatch goal with |- @eq (bv _) _ _ => ms_leaf_eq end
               | progress f_equal ].

#[local] Notation U := bv_unsigned.

Lemma Z_to_bv_bv_unsigned8 : forall (x : bv 8), Z_to_bv 8 (bv_unsigned x) = x.
Proof. intros. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma ortree4s : forall z0 z1 z2 (b3 : bv 8),
  (0 <= z0 < 256 -> 0 <= z1 < 256 -> 0 <= z2 < 256 ->
  let V := Z.lor (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (Z.shiftl (U (sxb b3)) 24))) (U (Z_to_bv 64 (Z.shiftl (U (Z_to_bv 64 z2)) 16))))))
                 (U (Z_to_bv 64 (Z.lor (U (Z_to_bv 64 (Z.shiftl (U (Z_to_bv 64 z1)) 8))) (U (Z_to_bv 64 z0))))) in
  0 <= V < 2^64 /\ V mod 2^32 = v4 z0 z1 z2 (U b3))%Z.
Proof.
  intros z0 z1 z2 b3 H0 H1 H2. cbv zeta.
  pose proof (bv_unsigned_in_range 8 b3) as R3. unfold bv_modulus in R3. change (2 ^ Z.of_N 8)%Z with 256%Z in R3.
  set (z3 := U b3) in *.
  rewrite <- (Z_to_bv_bv_unsigned8 b3). fold z3.
  destruct (Z.lt_ge_cases z3 128) as [Hs|Hs].
  - rewrite (sxb_lit_pos z3) by lia.
    rewrite (ortree4_eq z0 z1 z2 z3) by lia.
    pose proof (v4_range z0 z1 z2 z3 H0 H1 H2 ltac:(lia)). split; [lia|]. apply Z.mod_small. lia.
  - rewrite (sxb_lit_neg z3) by lia.
    rewrite (unsigned_lit_wrap (z3 - 256)).
    replace ((z3 - 256) mod 2 ^ 64)%Z with (z3 - 256 + 2^64)%Z by (Z.div_mod_to_equations; lia).
    rewrite !Z.shiftl_mul_pow2 by lia.
    rewrite (unsigned_lit_wrap ((z3 - 256 + 2 ^ 64) * 2 ^ 24)).
    replace (((z3 - 256 + 2 ^ 64) * 2 ^ 24) mod 2 ^ 64)%Z with ((z3 + 2^40 - 256) * 2^24)%Z by (Z.div_mod_to_equations; lia).
    rewrite (unsigned_lit z2), (unsigned_lit z1), (unsigned_lit z0) by lia.
    rewrite (unsigned_lit (z2 * 2^16)), (unsigned_lit (z1 * 2^8)) by lia.
    rewrite (lor_mul (z3 + 2^40 - 256) (z2 * 2^16) 24) by lia.
    rewrite (lor_mul z1 z0 8) by lia.
    rewrite (unsigned_lit ((z3 + 2 ^ 40 - 256) * 2 ^ 24 + z2 * 2 ^ 16)) by lia.
    rewrite (unsigned_lit (z1 * 2 ^ 8 + z0)) by lia.
    replace ((z3 + 2 ^ 40 - 256) * 2 ^ 24 + z2 * 2 ^ 16)%Z with (((z3 + 2 ^ 40 - 256) * 2 ^ 8 + z2) * 2 ^ 16)%Z by lia.
    rewrite (lor_mul ((z3 + 2 ^ 40 - 256) * 2 ^ 8 + z2) (z1 * 2 ^ 8 + z0) 16) by lia.
    unfold v4. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Section SW4.
  Variables (x1 x2 x3 x4 x5 x7 x8 x9 x10 x16 x17 x18 x20 x21 x22 x23 x25 x26 x27 x28 x29 x30 x31 : word).
  Variables (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (bs : list byte) (T FP Y0 Y1 : Z).
  #[local] Notation L := (Z.of_nat (length bs)).
  #[local] Notation Zw z := (Z_to_bv 64 z).
  Hypothesis TXT : bytes_at BSEGS m T bs.
  Hypothesis HL : (1 <= L <= 128)%Z.
  Hypothesis HT : (6537216 <= T <= 140737488355072)%Z.
  Hypothesis SHT : shz BSEGS m (ASAN_B + Y0) (Y1 - Y0).
  Hypothesis HY : (8 * Y0 <= T /\ T + L <= 8 * Y1)%Z.
  Hypothesis HFP : (T <= FP)%Z.

  #[local] Notation WST pc x6 x11 x12 x13 x14 x15 x24 :=
    (MS (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Zw ASAN_B) x20 x21 x22 x23 x24 x25 x26 x27
             x28 x29 x30 x31)
        F (Zw pc) fc None m (seg_rom BSEGS)) (only parsing).

  (* [comment removed for export] *)
  Definition sw4_post (kc : Z) : machine_state -> Prop := fun ms' =>
    exists y6 y11 y12 y13 y14 y15 y24 : word,
      ms' = WST 0x9b7f4 y6 y11 y12 y13 y14 y15 y24 /\ y6 = y24 /\
      (FP <= bv_unsigned y24 <= T + L)%Z /\ (T + kc <= bv_unsigned y24 <= T + kc + 4)%Z /\ digs bs (FP - T) (bv_unsigned y24 - T).

  #[using="HY"] Lemma tx_gran : forall A, (T <= A < T + L)%Z -> (ASAN_B + Y0 <= A / 8 + ASAN_B)%Z /\ (A / 8 + ASAN_B + 1 <= ASAN_B + Y0 + (Y1 - Y0))%Z.
  Proof. LiaFast.lf_pins (fun (HY : LiaFast.U) => LiaFast.u0). intros A HA. destruct HY as [Y1a Y2a]. Z.div_mod_to_equations. lia. Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HFP"] Lemma blockW4 : forall (kc : Z) (x11 x12 x13 x14 x15 : word),
      (FP - T <= kc)%Z -> (kc + 4 <= L)%Z -> digs bs (FP - T) kc ->
      evt BSEGS (sw4_post kc) (WST 0x9b724 (Zw (T + kc)) x11 x12 x13 x14 x15 (Zw (T + kc))).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HFP : LiaFast.U) => LiaFast.u0).
    intros kc x11 x12 x13 x14 x15 KC KC4 DGF.
    pose proof (shz_bound _ _ _ _ SHT) as BT.
    pose proof (tx_range bs kc) as R0. pose proof (tx_range bs (kc + 1)) as R1.
    pose proof (tx_range bs (kc + 2)) as R2. pose proof (tx_range bs (kc + 3)) as R3.
    pose proof (tx_gran (T + kc) ltac:(lia)) as G0.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (tx_gran (T + kc + 3) ltac:(lia)) as G3.
    step. (* [comment removed for export] *) shr3.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    txt_rd TXT (kc + 1)%Z RD. step. (* [comment removed for export] *) clear RD. fold_tx bs (kc + 1)%Z.
    txt_rd TXT (kc + 0)%Z RD. step. (* [comment removed for export] *) clear RD. fold_tx bs (kc + 0)%Z. try rewrite (Z.add_0_r kc).
    txt_rd TXT (kc + 2)%Z RD. step. (* [comment removed for export] *) clear RD. fold_tx bs (kc + 2)%Z.
    txt_rd TXT (kc + 3)%Z RD. step. (* [comment removed for export] *) clear RD.
    lazymatch goal with |- context [sxb ?b] =>
      destruct (ortree4s (tx bs kc) (tx bs (kc + 1)) (tx bs (kc + 2)) b R0 R1 R2) as [VR VM];
      change (bv_unsigned b) with (tx bs (kc + 3)) in VM end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    lazymatch type of VR with (0 <= ?v < _)%Z => set (Vv := v) in * end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit Vv) by lia.
    step. (* [comment removed for export] *)
    if_cases H4.
    - clear H4. apply evt_done. do 7 eexists. split; [reflexivity|]. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|]. split; [lia|].
      replace (T + kc - T)%Z with kc by lia. exact DGF.
    - rewrite ?(unsigned_lit Vv) in H4 by lia.
      destruct (swar4_dig Vv _ _ _ _ R0 R1 R2 R3 VR VM H4) as (D0 & D1 & D2 & D3). clear H4.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hu; [| cond_cleanup Hu; exfalso; lia].
      cond_cleanup Hu. clear Hu.
      do 16 step. (* [comment removed for export] *)
      apply evt_done. do 7 eexists. split; [reflexivity|]. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|]. split; [lia|].
      replace (T + kc + 4 - T)%Z with (kc + 4)%Z by lia. apply digs_snoc4; assumption.
  Qed.

  (* [comment removed for export] *)
  #[using="Y0 Y1 TXT HL HT SHT HY HFP"] Lemma blockW4C : forall (kc : Z) (x12 x13 x14 x15 : word),
      (FP - T <= kc <= L)%Z -> digs bs (FP - T) kc ->
      evt BSEGS (sw4_post kc) (WST 0x9b71c (Zw (T + kc)) (Zw (L - kc)) x12 x13 x14 x15 (Zw (T + kc))).
  Proof. LiaFast.lf_pins (fun (Y0 Y1 TXT HL HT SHT HY HFP : LiaFast.U) => LiaFast.u0).
    intros kc x12 x13 x14 x15 KC DGF.
    step. (* [comment removed for export] *)
    rewrite ?(unsigned_lit (L - kc)%Z) by lia.
    step. (* [comment removed for export] *)
    if_cases Hle.
    - cond_cleanup Hle. try rewrite signed_lit in Hle by lia.
      apply evt_done. do 7 eexists. split; [reflexivity|]. split; [reflexivity|]. rewrite unsigned_lit by lia. split; [lia|]. split; [lia|].
      replace (T + kc - T)%Z with kc by lia. exact DGF.
    - cond_cleanup Hle. try rewrite signed_lit in Hle by lia.
      goto (eapply (blockW4 kc)); [lia | lia | exact DGF].
  Qed.
End SW4.
End HxSw4BWF.

Import OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxGenFp OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxSemB OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxBaseB OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxIntBF OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxDefsBF OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxDigpBF OSSVerify.Proofs.fast_float.from_chars.lib.HXB.HxSw4BF.HxSw4BWF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma find_cell_lwf : forall n rgs a R o l, forallb (rwf n) rgs = true -> find_cell rgs a = Some (R, o, l) -> lwf n l = true.
Proof.
  intros n rgs a R o l Hw Hf. destruct (find_cell_spec _ _ _ _ _ Hf) as (HinR & _ & _ & Htr).
  rewrite forallb_forall in Hw. pose proof (Hw R HinR) as HwR. unfold rwf in HwR. apply andb_prop in HwR as [_ Hc].
  destruct Htr as [Htr|(-> & _)]; [|reflexivity].
  pose proof (tracked_b_spec _ _ _ Htr 0%nat (BV l 0) eq_refl) as Hg.
  exact (tforall_spec _ _ Hc _ _ Hg).
Qed.

(* [comment removed for export] *)
Section SW4G.
Variable facts : sst -> list fact.
Variable pc0 : Z.
(* [comment removed for export] *)
Hypothesis WALK : forall L XL E ms bs FPl,
  s_pc L = pc0 -> sw4g_chk facts (XST L XL) = true -> sden BSEGS E L ms -> fp_of L = Some FPl ->
  bytes_at BSEGS (ms_mem ms) (bv_unsigned (E 1%positive)) bs -> Z.of_nat (length bs) = bv_unsigned (E 2%positive) ->
  let R := ms_regs ms in let Tz := bv_unsigned (E 1%positive) in let Xz := bv_unsigned (lden E (rgl L 24)) in
  Tz <= Xz <= Tz + Z.of_nat (length bs) /\
  evt BSEGS (sw4_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 7) (getr R 8) (getr R 9) (getr R 10) (getr R 16) (getr R 17)
               (getr R 18) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29)
               (getr R 30) (getr R 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Xz (Xz - Tz))
      (kms BSEGS ms).

#[using="WALK"] Theorem sw4g_kit : hx_kitm_fp BSEGS xok_spd pc0 SW4_KEYS (sw4g_chk facts) [(0x9b7f4, sw4_newf, sw4_newx)].
Proof. LiaFast.lf_pins (fun (WALK : LiaFast.U) => LiaFast.u0).
  intros L XL E ms m0 Hpc Hchk Hw Hd HxF Hm0.
  pose proof Hchk as Hchk0.
  unfold sw4g_chk in Hchk. cbn [xs_st xs_x] in Hchk.
  destruct (s_resv L) eqn:Hrv; try discriminate.
  destruct (fp_of L) as [FPl|] eqn:Hfp; [|discriminate].
  apply andb_prop in Hchk as [Hchk Hx0]. apply andb_prop in Hchk as [Hchk Hfx]. apply andb_prop in Hchk as [Hrg H19].
  apply lin_eqb_eq in H19.
  rewrite forallb_app in Hfx. apply andb_prop in Hfx as [Hfx HfS].
  rewrite forallb_app in HfS. apply andb_prop in HfS as [HfS HfFP]. cbn [forallb] in HfFP. apply andb_prop in HfFP as [HfFP _].
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  destruct (txt_bytes E ms L Hd Hrg Hfx) as (bs & TXT & Hlen).
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  pose proof (fact_implied_ok E _ _ HF HfFP) as XFP. cbn [fact_ok] in XFP. rewrite (u_sub E) in XFP. unfold TXT_T in XFP. rewrite lden_lvar in XFP.
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  destruct (WALK L XL E ms bs FPl Hpc Hchk0 Hd Hfp TXT Hlen) as (HS & HK).
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Xl := rgl L 24) in *. set (Xz := bv_unsigned (lden E Xl)) in *.
  set (FPz := bv_unsigned (lden E FPl)).
  pose proof (bv_unsigned_in_range _ (lden E Xl)) as BX. unfold bv_modulus in BX. change (2 ^ Z.of_N 64) with two64 in BX.
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 19)); [exact (RG 19)|]. rewrite H19. rewrite lden_lconst. reflexivity. }
  (* [comment removed for export] *)
  apply existsb_exists in Hx0 as (f0 & Hf0 & Hq0). apply xf_eqb_eq in Hq0. subst f0.
  rewrite Forall_forall in HxF. pose proof (HxF _ Hf0) as XD.
  unfold xfact_ok in XD. cbn [xf_tag xf_args List.map xok_spd] in XD. fold Xl in XD. fold FPz Xz in XD.
  assert (TXT0 : bytes_at BSEGS m0 Tz bs).
  { apply (bytes_at_transport (ms_mem ms)); [exact TXT|]. intros i Hi.
    unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 Hk0].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. destruct (rg_kind R0) eqn:Hk; cbn in Hk0; try discriminate.
    rewrite <- Hr in Hm0. exact (txt_frame E L ms m0 R0 (R1 :: rs) i Hr Hb0 Hs0 Hk Hm0 ltac:(lia) ltac:(unfold two64 in *; lia)). }
  set (R := ms_regs ms) in *.
  destruct (kit_run BSEGS _ ms Hsvc0 HK) as (ms1 & ms2 & Hst & Heq & Hpost). clear HK.
  destruct Hpost as (y6 & y11 & y12 & y13 & y14 & y15 & y24 & Hms2 & H624 & HFE & HXP & HDG). subst ms2.
  destruct Heq as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
  cbn [with_rom MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in E1, E2, E3, E4, E5, E6, E7, E8.
  set (vs := [y6; y11; y12; y13; y14; y15; y24]).
  set (E' := E_of SW4_KEYS vs (s_next L) E).
  assert (Hy24 : E' (fv (s_next L) 6) = y24) by (exact (E_of_nth SW4_KEYS vs (s_next L) E 6 y24 eq_refl eq_refl)).
  assert (Hy6 : E' (fv (s_next L) 0) = y6) by (exact (E_of_nth SW4_KEYS vs (s_next L) E 0 y6 eq_refl eq_refl)).
  assert (Hag : agree (s_next L) E E') by apply E_of_agree.
  unfold state_wf in Hw. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hw _]. apply andb_prop in Hw as [Hwr Hwg].
  assert (HwX : lwf (s_next L) Xl = true) by (exact (regs_wf_n_spec _ _ 31 Hwr 24%nat ltac:(lia))).
  assert (EX : lden E' Xl = lden E Xl) by (symmetry; exact (lden_agree _ E E' Xl HwX Hag)).
  assert (HwFP : lwf (s_next L) FPl = true).
  { unfold fp_of in Hfp. destruct (find_cell (s_rgs L) (laddc (rgl L 9) 56)) as [[[Rc o] l0]|] eqn:Hfc; [|discriminate].
    injection Hfp as ->. exact (find_cell_lwf _ _ _ _ _ _ Hwg Hfc). }
  assert (EFP : lden E' FPl = lden E FPl) by (symmetry; exact (lden_agree _ E E' FPl HwFP Hag)).
  assert (Hv12 : (1 < s_next L)%positive /\ (2 < s_next L)%positive).
  { unfold txt_rgs_ok in Hrg. destruct (s_rgs L) as [|R0 [|R1 rs]] eqn:Hr; try discriminate.
    apply andb_prop in Hrg as [H0 _]. unfold rg_is in H0. apply andb_prop in H0 as [H0 _]. apply andb_prop in H0 as [H0 _].
    apply andb_prop in H0 as [Hb0 Hs0]. apply lin_eqb_eq in Hb0, Hs0. cbn [forallb] in Hwg. apply andb_prop in Hwg as [Hw0 _].
    unfold rwf in Hw0. apply andb_prop in Hw0 as [Hw0 _]. apply andb_prop in Hw0 as [Hw0a Hw0b]. rewrite Hb0 in Hw0a. rewrite Hs0 in Hw0b.
    unfold lwf, TXT_T, TXT_L, lvar in Hw0a, Hw0b. cbn in Hw0a, Hw0b. apply andb_prop in Hw0a as [Hw0a _]. apply andb_prop in Hw0b as [Hw0b _].
    apply Pos.ltb_lt in Hw0a, Hw0b. split; assumption. }
  assert (E1' : E' 1%positive = E 1%positive) by (unfold E'; apply E_of_old; lia).
  assert (E2' : E' 2%positive = E 2%positive) by (unfold E'; apply E_of_old; lia).
  assert (TLE : bv_unsigned (lden E' TXT_TL) = Tz + Lz).
  { unfold TXT_TL, TXT_T, TXT_L. rewrite lden_ladd, bv_add_unsigned, !lden_lvar, E1', E2'. fold Tz Lz. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 64) with two64. apply Z.mod_small. unfold two64 in *. lia. }
  (* [comment removed for export] *)
  assert (XD' : digp m0 FPz (bv_unsigned y24)).
  { apply (digp_extend m0 FPz Xz (bv_unsigned y24) Tz bs XD TXT0); [lia | lia | lia | exact HDG]. }
  pose proof XD as (Td & bsd & _ & (Hd1 & Hd2) & _). pose proof (bv_unsigned_in_range _ (lden E FPl)) as BFP.
  unfold bv_modulus in BFP. change (2 ^ Z.of_N 64) with two64 in BFP. fold FPz in BFP. fold FPz Tz in XFP.
  assert (HFT : Tz <= FPz) by (clear -XFP BFP B2; unfold two64 in *; Z.div_mod_to_equations; lia).
  exists 0x9b7f4, sw4_newf, sw4_newx, ms1, vs. split; [left; reflexivity|].
  split; [exact Hst|]. split; [reflexivity|]. split; [exact E7|]. split; [exact E6|]. split; [rewrite E5, Hresv0; reflexivity|].
  split; [exact E4|]. split; [exact E3|].
  split; [|split; [|split; [|split; [|exact E2]]]].
  - intros r Hr. rewrite (E1 r). destruct (reg_of_nat r) as (n & -> & Hn). rewrite getr_mkR. rewrite u5 by lia. rewrite Nat2Z.id.
    unfold SW4_KEYS in Hr. cbn [In] in Hr. rewrite u5 in Hr by lia.
    do 32 (destruct n as [|n]; [cbn; first [reflexivity | (symmetry; exact R19)
                                            | (exfalso; apply Hr; repeat (first [left; reflexivity | right]))]|]).
    lia.
  - intros i k v Hi Hv. rewrite (E1 _).
    destruct i as [|[|[|[|[|[|[|i]]]]]]]; cbn in Hi, Hv;
      first [ (injection Hi as <-; injection Hv as <-; reflexivity) | (destruct i; discriminate) ].
  - fold E'. unfold sw4_newf, fp_facts. rewrite Hfp. fold Xl. cbn [app].
    repeat apply Forall_cons; try apply Forall_nil; cbn [fact_ok].
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy24, EFP. fold FPz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). clear -HFE HXP HS Hd1 Hd2 B1 Hlen HFT. lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy24, EX. fold Xz. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). lia.
    + rewrite lden_lsub, bv_sub_unsigned, lden_lvar, Hy24. unfold TXT_T. rewrite lden_lvar, E1'. fold Tz. unfold bv_wrap, bv_modulus.
      change (2 ^ Z.of_N 64) with two64. rewrite Z.mod_small by (unfold two64 in *; lia). lia.
    + rewrite lden_lsub, bv_sub_unsigned, TLE, lden_lvar, Hy24. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.mod_small by (unfold two64 in *; lia). lia.
    + rewrite lden_lsub, bv_sub_unsigned, !lden_lvar, Hy6, Hy24, H624, Z.sub_diag. unfold bv_wrap. rewrite Z.mod_0_l by (unfold bv_modulus; lia). lia.
    + rewrite lden_lvar, Hy24. unfold P47. change (2 ^ 47) with 140737488355328. clear -HFE HXP HS B1 B2 Hlen. lia.
  - fold E'. unfold sw4_newx. rewrite Hfp. constructor; [|constructor]. unfold xfact_ok. cbn [xf_tag xf_args List.map xok_spd].
    rewrite EFP, lden_lvar, Hy24. fold FPz. exact XD'.
Qed.
End SW4G.

(* [comment removed for export] *)
Ltac open_sw4 Hchk Hfp Hd facts :=
  unfold sw4g_chk in Hchk; cbn [xs_st xs_x] in Hchk;
  match type of Hchk with context [s_resv ?L] => destruct (s_resv L) eqn:Hrv; try discriminate end;
  rewrite Hfp in Hchk;
  apply andb_prop in Hchk as [Hchk _]; apply andb_prop in Hchk as [Hchk Hfx]; apply andb_prop in Hchk as [Hrg H19];
  apply lin_eqb_eq in H19;
  rewrite forallb_app in Hfx; apply andb_prop in Hfx as [Hfx HfS]; rewrite forallb_app in HfS; apply andb_prop in HfS as [HfS _].

Lemma sw4_walk : forall L XL E ms bs FPl,
  s_pc L = 0x9b724 -> sw4g_chk sw4_facts (XST L XL) = true -> sden BSEGS E L ms -> fp_of L = Some FPl ->
  bytes_at BSEGS (ms_mem ms) (bv_unsigned (E 1%positive)) bs -> Z.of_nat (length bs) = bv_unsigned (E 2%positive) ->
  let R := ms_regs ms in let Tz := bv_unsigned (E 1%positive) in let Xz := bv_unsigned (lden E (rgl L 24)) in
  Tz <= Xz <= Tz + Z.of_nat (length bs) /\
  evt BSEGS (sw4_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 7) (getr R 8) (getr R 9) (getr R 10) (getr R 16) (getr R 17)
               (getr R 18) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29)
               (getr R 30) (getr R 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Xz (Xz - Tz))
      (kms BSEGS ms).
Proof.
  intros L XL E ms bs FPl Hpc Hchk Hd Hfp TXT Hlen. cbv zeta.
  open_sw4 Hchk Hfp Hd sw4_facts.
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (Xl := rgl L 24) in *. set (Xz := bv_unsigned (lden E Xl)).
  set (T1z := bv_unsigned (lden E (rgl L 6))).
  pose proof (bv_unsigned_in_range _ (lden E Xl)) as BX. pose proof (bv_unsigned_in_range _ (lden E (rgl L 6))) as BT1.
  unfold bv_modulus in BX, BT1. change (2 ^ Z.of_N 64) with two64 in BX, BT1.
  unfold sw4_facts in HfS. fold Xl in HfS. cbn [forallb] in HfS.
  repeat match type of HfS with (?a && ?b)%bool = true => apply andb_prop in HfS as [?F HfS] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  pose proof (fact_implied_ok E _ _ HF F1) as X3.
  cbn [fact_ok] in X1, X2, X3. rewrite (u_sub E) in X1, X2, X3. unfold TXT_TL, TXT_T, TXT_L in X1, X2.
  rewrite (u_add E) in X2. rewrite !lden_lvar in X1. rewrite !lden_lvar in X2. fold Tz Lz Xz T1z in X1, X2, X3.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2.
  assert (HS : Tz <= Xz /\ Xz + 4 <= Tz + Lz) by (clear -X1 X2 BX B1 B2; unfold two64 in *; split; Z.div_mod_to_equations; lia).
  assert (HT1 : T1z = Xz) by (clear -X3 BX BT1; unfold two64 in *; Z.div_mod_to_equations; lia).
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (Rw : forall k z, bv_unsigned (lden E (rgl L k)) = z -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 z).
  { intros k z Hz. rewrite RG. rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 19)); [exact (RG 19)|]. rewrite H19. rewrite lden_lconst. reflexivity. }
  assert (R24' : getr (ms_regs ms) 24%bv = Z_to_bv 64 (Tz + (Xz - Tz))) by (apply (Rw 24); fold Xl Xz; ring).
  assert (R6' : getr (ms_regs ms) 6%bv = Z_to_bv 64 (Tz + (Xz - Tz))) by (apply (Rw 6); fold T1z; rewrite HT1; ring).
  split; [rewrite Hlen; fold Lz; clear -HS; lia|].
  assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
  assert (P2 : 6537216 <= Tz <= 140737488355072) by (clear -B2; lia).
  assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
  unfold kms, mkR_of. rewrite Hpc0, Hresv0, R19, R24', R6', Hpc.
  eapply (blockW4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Xz Y0z Y1z);
    first [ exact TXT | exact P1 | exact P2 | exact SHT | exact P3 | apply digs_nil | (clear -HS Hlen; lia) ].
Qed.

Theorem sw4_kit : hx_kitm_fp BSEGS xok_spd 0x9b724 SW4_KEYS sw4_chk [(0x9b7f4, sw4_newf, sw4_newx)].
Proof. exact (sw4g_kit sw4_facts 0x9b724 sw4_walk). Qed.
Theorem H_SW4_ok : hand_okx_fp BSEGS xok_spd H_SW4.
Proof. apply hx_okm_fp. exact sw4_kit. Qed.

Lemma sw4c_walk : forall L XL E ms bs FPl,
  s_pc L = 0x9b71c -> sw4g_chk sw4c_facts (XST L XL) = true -> sden BSEGS E L ms -> fp_of L = Some FPl ->
  bytes_at BSEGS (ms_mem ms) (bv_unsigned (E 1%positive)) bs -> Z.of_nat (length bs) = bv_unsigned (E 2%positive) ->
  let R := ms_regs ms in let Tz := bv_unsigned (E 1%positive) in let Xz := bv_unsigned (lden E (rgl L 24)) in
  Tz <= Xz <= Tz + Z.of_nat (length bs) /\
  evt BSEGS (sw4_post (getr R 1) (getr R 2) (getr R 3) (getr R 4) (getr R 5) (getr R 7) (getr R 8) (getr R 9) (getr R 10) (getr R 16) (getr R 17)
               (getr R 18) (getr R 20) (getr R 21) (getr R 22) (getr R 23) (getr R 25) (getr R 26) (getr R 27) (getr R 28) (getr R 29)
               (getr R 30) (getr R 31) (ms_fregs ms) (ms_fcsr ms) (ms_mem ms) bs Tz Xz (Xz - Tz))
      (kms BSEGS ms).
Proof.
  intros L XL E ms bs FPl Hpc Hchk Hd Hfp TXT Hlen. cbv zeta.
  open_sw4 Hchk Hfp Hd sw4c_facts.
  pose proof (txt_bounds E ms L Hd Hfx) as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (txt_shadow E ms L Hd Hrg Hfx) as SHT.
  destruct (sden_0 _ _ _ _ Hd) as (Hpc0 & Hsvc0 & Hresv0 & HR & HG & HD & HF & Hfrm).
  rewrite Hrv in Hresv0. cbn [rsv_ok] in Hresv0.
  set (Tz := bv_unsigned (E 1%positive)) in *. set (Lz := bv_unsigned (E 2%positive)) in *.
  set (Y0z := bv_unsigned (E 7%positive)) in *. set (Y1z := bv_unsigned (E 8%positive)) in *.
  set (Xl := rgl L 24) in *. set (Xz := bv_unsigned (lden E Xl)).
  set (T1z := bv_unsigned (lden E (rgl L 6))). set (A1z := bv_unsigned (lden E (rgl L 11))).
  pose proof (bv_unsigned_in_range _ (lden E Xl)) as BX. pose proof (bv_unsigned_in_range _ (lden E (rgl L 6))) as BT1.
  pose proof (bv_unsigned_in_range _ (lden E (rgl L 11))) as BA1.
  unfold bv_modulus in BX, BT1, BA1. change (2 ^ Z.of_N 64) with two64 in BX, BT1, BA1.
  unfold sw4c_facts in HfS. fold Xl in HfS. cbn [forallb] in HfS.
  repeat match type of HfS with (?a && ?b)%bool = true => apply andb_prop in HfS as [?F HfS] end.
  pose proof (fact_implied_ok E _ _ HF F) as X1. pose proof (fact_implied_ok E _ _ HF F0) as X2.
  pose proof (fact_implied_ok E _ _ HF F1) as X3. pose proof (fact_implied_ok E _ _ HF F2) as X4.
  cbn [fact_ok] in X1, X2, X3, X4. rewrite (u_sub E) in X1, X2, X3, X4. rewrite (u_sub E) in X4. unfold TXT_TL, TXT_T, TXT_L in X1, X2, X4.
  rewrite (u_add E) in X2, X4. rewrite !lden_lvar in X1. rewrite !lden_lvar in X2. rewrite !lden_lvar in X4. fold Tz Lz Xz T1z A1z in X1, X2, X3, X4.
  assert (M3 : (Tz + Lz) mod two64 = Tz + Lz) by (apply Z.mod_small; unfold two64 in *; lia).
  rewrite M3 in X2, X4.
  assert (HS : Tz <= Xz /\ Xz <= Tz + Lz) by (clear -X1 X2 BX B1 B2; unfold two64 in *; split; Z.div_mod_to_equations; lia).
  assert (HT1 : T1z = Xz) by (clear -X3 BX BT1; unfold two64 in *; Z.div_mod_to_equations; lia).
  assert (HA1 : A1z = Tz + Lz - Xz).
  { clear -X4 HS BX BA1 B1 B2. unfold two64 in *. rewrite (Z.mod_small (Tz + Lz - Xz)) in X4 by lia. Z.div_mod_to_equations. lia. }
  assert (RG : forall k, getr (ms_regs ms) (Z_to_bv 5 k) = lden E (rgl L k)) by (intros k; rewrite (HR _); reflexivity).
  assert (Rw : forall k z, bv_unsigned (lden E (rgl L k)) = z -> getr (ms_regs ms) (Z_to_bv 5 k) = Z_to_bv 64 z).
  { intros k z Hz. rewrite RG. rewrite <- Hz. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (R19 : getr (ms_regs ms) 19%bv = Z_to_bv 64 ASAN_B).
  { transitivity (lden E (rgl L 19)); [exact (RG 19)|]. rewrite H19. rewrite lden_lconst. reflexivity. }
  assert (R24' : getr (ms_regs ms) 24%bv = Z_to_bv 64 (Tz + (Xz - Tz))) by (apply (Rw 24); fold Xl Xz; ring).
  assert (R6' : getr (ms_regs ms) 6%bv = Z_to_bv 64 (Tz + (Xz - Tz))) by (apply (Rw 6); fold T1z; rewrite HT1; ring).
  assert (R11 : getr (ms_regs ms) 11%bv = Z_to_bv 64 (Z.of_nat (length bs) - (Xz - Tz))) by (apply (Rw 11); fold A1z; rewrite HA1, Hlen; fold Lz; ring).
  split; [rewrite Hlen; fold Lz; clear -HS; lia|].
  assert (P1 : 1 <= Z.of_nat (length bs) <= 128) by (clear -Hlen B1; lia).
  assert (P2 : 6537216 <= Tz <= 140737488355072) by (clear -B2; lia).
  assert (P3 : 8 * Y0z <= Tz /\ Tz + Z.of_nat (length bs) <= 8 * Y1z) by (clear -Hlen B5 B6; lia).
  unfold kms, mkR_of. rewrite Hpc0, Hresv0, R19, R24', R6', R11, Hpc.
  eapply (blockW4C _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ bs Tz Xz Y0z Y1z);
    first [ exact TXT | exact P1 | exact P2 | exact SHT | exact P3 | apply digs_nil | (clear -HS Hlen; lia) ].
Qed.

Theorem sw4c_kit : hx_kitm_fp BSEGS xok_spd 0x9b71c SW4_KEYS sw4c_chk [(0x9b7f4, sw4_newf, sw4_newx)].
Proof. exact (sw4g_kit sw4c_facts 0x9b71c sw4c_walk). Qed.
Theorem H_SW4C_ok : hand_okx_fp BSEGS xok_spd H_SW4C.
Proof. apply hx_okm_fp. exact sw4c_kit. Qed.
