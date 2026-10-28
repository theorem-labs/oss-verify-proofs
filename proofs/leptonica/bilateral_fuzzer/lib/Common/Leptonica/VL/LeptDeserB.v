(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import RelocKitVL RelocTacVL CanonImgVL RCodeVL_237d4_24000 RCodeVL_24000_25000 RCodeVL_25000_25620.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import MuslTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import RelocImg CanonImg.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Musl Require Import RelocRW RelocPF.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.VL Require Import LeptStderr LeptBase LeptErr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac zval ::= rl_zval.      (* [comment removed for export] *)
#[local] Ltac condZ ::= rl_condZ.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

(* [comment removed for export] *)
Section Arith.
Local Open Scope Z_scope.
Lemma lxor_ones64 : forall p, 0 <= p < 2 ^ 64 -> Z.lxor p (2 ^ 64 - 1) = 2 ^ 64 - 1 - p.
Proof.
  intros p Hp. apply Z.bits_inj'. intros n Hn.
  rewrite Z.lxor_spec.
  replace (2 ^ 64 - 1 - p) with ((Z.lnot p) mod 2 ^ 64).
  2:{ unfold Z.lnot. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
  destruct (Z_lt_ge_dec n 64).
  - rewrite Z.mod_pow2_bits_low by lia. rewrite Z.lnot_spec by lia.
    replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_low by lia.
    apply Bool.xorb_true_r.
  - rewrite Z.mod_pow2_bits_high by lia.
    replace (2 ^ 64 - 1) with (Z.ones 64) by reflexivity. rewrite Z.ones_spec_high by lia.
    rewrite Bool.xorb_false_r.
    destruct (Z.eq_dec p 0) as [->|NZ]; [apply Z.bits_0|].
    apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 64); [|lia]. apply Z.log2_lt_pow2; lia.
Qed.

(* [comment removed for export] *)
Lemma zbv_not : forall p, 0 <= p < 2 ^ 64 -> v_xori (Z_to_bv 64 p) (-1) = Z_to_bv 64 (2 ^ 64 - 1 - p).
Proof.
  intros p Hp. unfold v_xori. rewrite u_Z2bv by lia. change (bv_wrap 64 (-1)) with (2 ^ 64 - 1).
  f_equal. apply lxor_ones64. lia.
Qed.

Lemma lor_mod4_0 : forall a b, 0 <= a -> 0 <= b -> a mod 4 = 0 -> b mod 4 = 0 -> (Z.lor a b) mod 4 = 0.
Proof.
  intros a b Ha Hb Ma Mb. change 4 with (2 ^ 2) in *. rewrite <- Z.land_ones in * by lia.
  rewrite Z.land_lor_distr_l, Ma, Mb. reflexivity.
Qed.

Lemma zbv_or : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> v_or (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (Z.lor a b).
Proof. intros a b Ha Hb. unfold v_or. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma mod4_plus : forall p k, p mod 4 = 0 -> k mod 4 = 0 -> (p + k) mod 4 = 0.
Proof.
  intros p k Hp Hk.
  apply Z.mod_divide in Hp; [|lia]. apply Z.mod_divide in Hk; [|lia]. destruct Hp as [a Ha]. destruct Hk as [b Hb].
  subst. replace (a * 4 + b * 4) with ((a + b) * 4) by lia. apply Z_mod_mult.
Qed.
End Arith.

Section DeserB.
Context {fx : FPState} {RLOC : Reloc} {RCODE : RelocCode RLOC} {RSITES : RelocSites RLOC} {RCODEF : RelocCodeVL RLOC} {RSITESF : RelocSitesVL RLOC} {RLEPT : RelocLept RLOC} {RIMGF : RelocImgVL RLOC} {RDATA : RelocData RLOC} {RIMG : RelocImg RLOC} {RRW : RelocRW RLOC RDATA} {RPF : RelocPF RLOC} {RENV : RelocLeptEnvVL RLOC} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLG} {P16 : PinsG}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  Ltac guard8 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_7; unorm; rewrite EQ; reflexivity).
  Ltac guard4 F D EQ := stepiv F D (Z_to_bv 64 0) ltac:(gres; pin; imm_norm; rewrite andi_3; unorm; rewrite EQ; reflexivity).
  Ltac rdn_out R := rewrite rdn_wbytes_out_Z; [exact R | rewrite ?length_N_to_le_bytes; lia].

  (* [comment removed for export] *)
  Lemma pd_F : forall regs m (dp nb ncr q dr wr hr : Z) bs20 bs12,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr <= 256)%Z -> (ncr + 7 < q)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 12)) 4 = Some bs12 -> bytes_le_to_Z bs12 = dr -> (0 <= dr < 2 ^ 32)%Z ->
    (0 <= wr < 2 ^ 64)%Z -> (0 <= hr < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 12 = Z_to_bv 64 (dp + 20) ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25360) m rom) (mkst regs' (rl dVL_239c0 0x239c0) m rom)
      /\ getr regs' 22 = Z_to_bv 64 ncr /\ getr regs' 20 = Z_to_bv 64 nb /\ getr regs' 23 = Z_to_bv 64 dp
      /\ getr regs' 19 = Z_to_bv 64 (zx (sw32 dr))
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 (zx (sw32 dr)) /\ getr regs' 1 = rl dVL_25134 0x25394
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 19; 20; 22; 23]%list) regs regs'.
  Proof.
    intros regs m dp nb ncr q dr wr hr bs20 bs12 Hdp Hdphi Hnb Hq R20 W20 Hncr Hq7 R12 W12 Hdr Hwr Hhr H10 H11 H12 H9 H18.
    assert (Hq4 : (0 <= q < 2 ^ 29)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    eexists. split.
    - stepLD F_25360 D_25360 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; rewrite ?Z.add_0_r; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
      sn F_25364 D_25364. stepb_ft F_25368 D_25368 ltac:(condZ).
      zv F_2536c D_2536c (Z_to_bv 64 (ncr + 7)).
      stepiv F_25370 D_25370 (Z_to_bv 64 q) ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; subst q; reflexivity).
      stepb_ft F_25374 D_25374 ltac:(condZ).
      sn F_25378 D_25378. sn F_2537c D_2537c.
      stepLD F_25380 D_25380 bs12 (Z_to_bv 64 dr) ltac:(addr_norm; exact R12) ltac:(rewrite u_Z2bv by lia; exact W12).
      rewrite (v_lw_Z dr), <- (zbv_zx (sw32 dr)).
      sn F_25384 D_25384. sn F_25388 D_25388. sn F_2538c D_2538c. sn F_25390 D_25390.
      apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Fbad : forall regs m (dp nb ncr q : Z) bs20,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr < 2 ^ 32)%Z -> ~ (ncr <= 256 /\ ncr + 7 < q)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 12 = Z_to_bv 64 (dp + 20) ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25360) m rom) (mkst regs' (rl dVL_25134 0x25470) m rom)
      /\ regs_agree (fun r => In r [12; 13; 22]%list) regs regs'.
  Proof.
    intros regs m dp nb ncr q bs20 Hdp Hdphi Hnb Hq R20 W20 Hncr NC H10 H11 H12.
    assert (Hq4 : (0 <= q < 2 ^ 29)%Z) by (subst q; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
    destruct (Z_lt_ge_dec 256 ncr) as [BIG|OK].
    - clear NC. eexists. split.
      { stepLD F_25360 D_25360 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; rewrite ?Z.add_0_r; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
        sn F_25364 D_25364. stepb_tk F_25368 D_25368 ltac:(condZ). apply mst_refl. }
      solve_regs_agree.
    - assert (NQ : (q <= ncr + 7)%Z) by lia. clear NC. eexists. split.
      { stepLD F_25360 D_25360 bs20 (Z_to_bv 64 ncr) ltac:(addr_norm; rewrite ?Z.add_0_r; exact R20) ltac:(rewrite u_Z2bv by lia; exact W20).
        sn F_25364 D_25364. stepb_ft F_25368 D_25368 ltac:(condZ).
        zv F_2536c D_2536c (Z_to_bv 64 (ncr + 7)).
        stepiv F_25370 D_25370 (Z_to_bv 64 q) ltac:(gres; pin; imm_norm; rewrite zbv_srli by lia; subst q; reflexivity).
        stepb_tk F_25374 D_25374 ltac:(condZ). apply mst_refl. }
      solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_G0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25394) m rom)
                              (mkst regs' (rl dVL_25134 0x25498) (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_25394 D_25394 (Z_to_bv 64 (s - 88)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_25398 D_25398 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_G : forall regs m (s dp nb nc pix1 wpl hr ir : Z) (v1 : pixv) bsi,
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    PIXat m pix1 v1 -> (4096 <= pix1)%Z -> (pix1 + 64 <= s - 96)%Z -> (pix1 mod 8 = 0)%Z -> p_wpl v1 = wpl ->
    (1 <= hr <= 1000000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * hr) <= 67108864)%Z ->
    (0 <= nc <= 256)%Z -> (28 <= nb < 2 ^ 31)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= dp)%Z -> (dp + nb <= s - 96)%Z -> (dp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4 * nc + 24)) 4 = Some bsi -> bytes_le_to_Z bsi = ir -> (0 <= ir < 2 ^ 32)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 22 = Z_to_bv 64 nc -> getr regs 20 = Z_to_bv 64 nb ->
    getr regs 23 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25394) m rom)
                              (mkst regs' (rl dVL_23d30 0x23d30) (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 (s - 88) /\ getr regs' 1 = rl dVL_25134 0x253e8
      /\ getr regs' 20 = Z_to_bv 64 (zx (sw32 ir))
      /\ getr regs' 8 = Z_to_bv 64 (4 * (wpl * hr)) /\ getr regs' 21 = Z_to_bv 64 (nb - 4 * nc - 28)
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 20; 21]%list) regs regs'.
  Proof.
    intros regs m s dp nb nc pix1 wpl hr ir v1 bsi Hs Hs64 SOK PX Gp Hp1 AL8 Hwpl Hhr Hw0 Hsz Hnc Hnb Hnc4 Hdp Hdpnb ALd Ri Wi Hir H2 H10 H22 H20 H23 H18.
    pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_wpl _ WF) as Rw. rewrite Hwpl in Rw.
    pose proof (zx_range (sw32 ir)) as Hzi.
    assert (PX1 : PIXat (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) pix1 v1).
    { apply PIXat_out; [exact PX | rewrite length_N_to_le_bytes, u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia]. }
    assert (ALe : ((dp + (4 * nc + 24)) mod 4 = 0)%Z).
    { apply mod4_plus; [exact ALd|]. replace (4 * nc + 24)%Z with ((nc + 6) * 4)%Z by lia. apply Z_mod_mult. }
    eexists. split.
    - stepST F_25394 D_25394 (Z_to_bv 64 (s - 88)) (Z_to_bv 64 pix1) ltac:(sok_in SOK).
      stepb_ft F_25398 D_25398 ltac:(condZ).
      sn F_2539c D_2539c. fixv (Z_to_bv 64 (4 * hr)) ltac:(rewrite v_slliw_2, sw32_small by lia; f_equal; lia).
      sn F_253a0 D_253a0.
      stepb_ft F_23ce4 D_23ce4 ltac:(condZ).
      guard8 F_23ce8 D_23ce8 AL8. stepb_ft F_23cec D_23cec ltac:(condZ).
      stepLD F_23cf0 D_23cf0 (Z_to_le_bytes 4 wpl) (Z_to_bv 64 wpl) ltac:(addr_norm; rewrite <- Hwpl; exact (PIX_rd_wpl SEGS _ _ _ PX1)) ltac:(apply lez4; lia).
      rewrite (v_lw_small wpl) by lia.
      stepretF F_23cf4 D_23cf4 F_253a4.
      sn F_253a4 D_253a4. fixv (Z_to_bv 64 (4 * (wpl * hr))) ltac:(rewrite zbv_mulw_small by lia; f_equal; lia).
      zv F_253a8 D_253a8 (Z_to_bv 64 (4 * (wpl * hr))).
      stepb_ft F_253ac D_253ac ltac:(condZ).
      stepiv F_253b0 D_253b0 (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      zv F_253b4 D_253b4 (Z_to_bv 64 (4 * nc + 24)).
      sn F_253b8 D_253b8. fixv (Z_to_bv 64 (2 ^ 64 - 1 - dp)) ltac:(apply zbv_not; lia).
      stepb_ft F_253bc D_253bc ltac:(condZ).
      zv F_253c0 D_253c0 (Z_to_bv 64 (dp + (4 * nc + 24))).
      guard4 F_253c4 D_253c4 ALe. stepb_ft F_253c8 D_253c8 ltac:(condZ).
      sn F_253cc D_253cc.
      stepLD F_253d0 D_253d0 bsi (Z_to_bv 64 ir) ltac:(addr_norm; replace (dp + (4 * nc + 24))%Z with (dp + 4 * nc + 24)%Z by lia; rdn_out Ri) ltac:(rewrite u_Z2bv by lia; exact Wi).
      rewrite (v_lw_Z ir), <- (zbv_zx (sw32 ir)).
      stepiv F_253d4 D_253d4 (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_253d8 D_253d8. fixv (Z_to_bv 64 (nb - 4 * nc)) ltac:(rewrite v_subw_Z, sw32_small by lia; reflexivity).
      sn F_253dc D_253dc. fixv (Z_to_bv 64 (nb - 4 * nc - 28)) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      zv F_253e0 D_253e0 (Z_to_bv 64 (s - 88)).
      sn F_253e4 D_253e4. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_H : forall regs m (sz wr hr d : Z),
    (0 <= sz < 2 ^ 32)%Z ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 sz -> getr regs 20 = Z_to_bv 64 sz ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr -> getr regs 19 = Z_to_bv 64 d ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x253e8) m rom) (mkst regs' (rl dVL_237d4 0x237d4) m rom)
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 1 = rl dVL_25134 0x25400
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m sz wr hr d Hsz H8 H21 H20 H9 H18 H19. eexists. split.
    - stepb_ft F_253e8 D_253e8 ltac:(condZ). stepb_ft F_253ec D_253ec ltac:(condZ).
      sn F_253f0 D_253f0. sn F_253f4 D_253f4. sn F_253f8 D_253f8. sn F_253fc D_253fc. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_Hbad : forall regs m (sz msz isz : Z),
    (0 <= sz < 2 ^ 32)%Z -> (0 <= msz < 2 ^ 32)%Z -> (0 <= isz < 2 ^ 64)%Z -> (sz <> msz \/ sz <> isz) ->
    rdn SEGS m (rl dA_1e3b0 0x1e3b0) 8 = Some (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) -> rdn SEGS m (rl dA_1f3f8 0x1f420) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 msz -> getr regs 20 = Z_to_bv 64 isz ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x253e8) m rom) (mkst regs' (rl dF_13694 0x13694) m rom)
      /\ getr regs' 10 = rl dVLS_104ff 0x104ff /\ getr regs' 11 = rl dVLS_105ea 0x105ea /\ getr regs' 1 = rl dVL_25134 0x254f4
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
  Proof. rl_dbounds (dA_1e3b0 :: dA_1f3f8 :: nil).
    intros regs m sz msz isz Hsz Hmsz Hisz NE Rg Rs H8 H21 H20.
    destruct (Z.eq_dec sz msz) as [E1|N1].
    - assert (N2 : sz <> isz) by lia. clear NE. eexists. split.
      { stepb_ft F_253e8 D_253e8 ltac:(condZ). stepb_tk F_253ec D_253ec ltac:(condZ).
        sn F_254c0 D_254c0.
        stepLD F_254c4 D_254c4 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_254c8 D_254c8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_254cc D_254cc. stepb_ft F_254d0 D_254d0 ltac:(condZ).
        sn F_254d4 D_254d4. sn F_254d8 D_254d8. sn F_254dc D_254dc. sn F_254e0 D_254e0.
        sn F_254e4 D_254e4. sn F_254e8 D_254e8. sn F_254ec D_254ec. sn F_254f0 D_254f0. apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
    - clear NE. eexists. split.
      { stepb_tk F_253e8 D_253e8 ltac:(condZ).
        sn F_254c0 D_254c0.
        stepLD F_254c4 D_254c4 (Z_to_le_bytes 8 (0x1f420 + dA_1f3f8)) (rl dA_1f3f8 0x1f420) ltac:(addr_norm; exact Rg) ltac:(apply lez8; lia).
        stepLD F_254c8 D_254c8 (Z_to_le_bytes 4 3) (Z_to_bv 64 3) ltac:(addr_norm; exact Rs) ltac:(apply lez4; lia).
        sn F_254cc D_254cc. stepb_ft F_254d0 D_254d0 ltac:(condZ).
        sn F_254d4 D_254d4. sn F_254d8 D_254d8. sn F_254dc D_254dc. sn F_254e0 D_254e0.
        sn F_254e4 D_254e4. sn F_254e8 D_254e8. sn F_254ec D_254ec. sn F_254f0 D_254f0. apply mst_refl. }
      repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25400) m rom)
                              (mkst regs' (rl dVL_25134 0x254f8) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
  Proof.
    intros regs m s Hs Hs64 SOK H2 H10. eexists. split.
    - stepST F_25400 D_25400 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 0) ltac:(sok_in SOK).
      stepb_tk F_25404 D_25404 ltac:(condZ). apply mst_refl.
    - solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I1 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> (1 <= pixd < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25400) m rom)
                              (mkst regs' (rl dVL_25134 0x2555c) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [9; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 SOK Hp H2 H10 H22. eexists. split.
    - stepST F_25400 D_25400 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepb_ft F_25404 D_25404 ltac:(condZ).
      sn F_25408 D_25408. fixv (Z_to_bv 64 0) ltac:(rewrite v_addiw_Z; reflexivity).
      stepb_tk F_2540c D_2540c ltac:(condZ).
      sn F_25520 D_25520. sn F_25524 D_25524. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_I2 : forall regs m (s pixd dp nc : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    (0 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 nc -> getr regs 23 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25400) m rom)
                              (mkst regs' (rl dVL_2486c 0x2486c) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (dp + 24) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 nc /\ getr regs' 1 = rl dVL_25134 0x25428
      /\ getr regs' 18 = Z_to_bv 64 nc
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs m s pixd dp nc Hs Hs64 SOK Hp Hnc Hdp Hdphi H2 H10 H22 H23. eexists. split.
    - stepST F_25400 D_25400 (Z_to_bv 64 (s - 96)) (Z_to_bv 64 pixd) ltac:(sok_in SOK).
      stepb_ft F_25404 D_25404 ltac:(condZ).
      sn F_25408 D_25408. fixv (Z_to_bv 64 nc) ltac:(rewrite v_addiw_Z, sw32_small by lia; f_equal; lia).
      stepb_ft F_2540c D_2540c ltac:(condZ).
      sn F_25410 D_25410. stepb_ft F_25414 D_25414 ltac:(condZ).
      zv F_25418 D_25418 (Z_to_bv 64 (dp + 24)). sn F_2541c D_2541c. sn F_25420 D_25420. sn F_25424 D_25424. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_J0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25428) m rom) (mkst regs' (rl dVL_23d30 0x23d30) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = rl dVL_25134 0x25530 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 H2 H10. eexists. split.
    - stepb_tk F_25428 D_25428 ltac:(condZ). zv F_25528 D_25528 (Z_to_bv 64 (s - 96)). sn F_2552c D_2552c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_J1 : forall regs m (s cm pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25428) m rom) (mkst regs' (rl dVL_23ecc 0x23ecc) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 1 = rl dVL_25134 0x2543c
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
  Proof.
    intros regs m s cm pixd Hs Hs64 Hcm Hp Rp H2 H10. eexists. split.
    - stepb_ft F_25428 D_25428 ltac:(condZ). sn F_2542c D_2542c.
      stepLD8 F_25430 D_25430 (Z_to_bv 64 pixd). sn F_25434 D_25434. sn F_25438 D_25438. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_K : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x2543c) m rom) (mkst regs' (rl dVL_25134 0x2555c) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rp H2 H10. eexists. split.
    - stepb_tk F_2543c D_2543c ltac:(condZ). stepLD8 F_25558 D_25558 (Z_to_bv 64 pixd). apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_GD : forall regs m (pixd dp nc sz : Z) (v : pixv),
    PIXat m pixd v -> (4096 <= pixd)%Z -> (pixd mod 8 = 0)%Z -> (0 <= nc <= 256)%Z -> (0 <= dp)%Z -> (dp + 4 * nc + 28 < 2 ^ 64)%Z ->
    (dp mod 4 = 0)%Z -> (p_data v mod 4 = 0)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x2555c) m rom) (mkst regs' (rl dF_1c9b4 0x1c9b4) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (dp + 4 * nc + 28) /\ getr regs' 12 = Z_to_bv 64 sz /\ getr regs' 1 = rl dVL_25134 0x25590
      /\ getr regs' 18 = Z_to_bv 64 (4 * nc)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
  Proof.
    intros regs m pixd dp nc sz v PX Gp AL8 Hnc Hdp Hdphi ALd ALv H10 H23 H18 H8. pose proof PX as (Hp0 & Hp64 & WF & _). pose proof (wf_data _ WF).
    assert (ALe : ((dp + 4 * nc + 28) mod 4 = 0)%Z).
    { replace (dp + 4 * nc + 28)%Z with (dp + (nc + 7) * 4)%Z by lia. apply mod4_plus; [exact ALd | apply Z_mod_mult]. }
    pose proof (lor_mod4_0 (p_data v) (dp + 4 * nc + 28) ltac:(lia) ltac:(lia) ALv ALe) as ALo.
    pose proof (Z_lor_range (p_data v) (dp + 4 * nc + 28) ltac:(lia) ltac:(lia)) as Ro.
    eexists. split.
    - sn F_2555c D_2555c. stepb_ft F_241e4 D_241e4 ltac:(condZ).
      guard8 F_241e8 D_241e8 AL8. stepb_ft F_241ec D_241ec ltac:(condZ).
      stepLD F_241f0 D_241f0 (Z_to_le_bytes 8 (p_data v)) (Z_to_bv 64 (p_data v)) ltac:(addr_norm; exact (PIX_rd_data SEGS _ _ _ PX)) ltac:(apply lez8; lia).
      stepretF F_241f4 D_241f4 F_25560.
      sn F_25560 D_25560. stepb_ft F_25564 D_25564 ltac:(condZ).
      zv F_25568 D_25568 (Z_to_bv 64 (dp + 28)).
      stepiv F_2556c D_2556c (Z_to_bv 64 (4 * nc)) ltac:(gres; pin; imm_norm; rewrite zbv_slli by lia; f_equal; change (2 ^ 2)%Z with 4%Z; lia).
      sn F_25570 D_25570. fixv (Z_to_bv 64 (2 ^ 64 - 1 - (dp + 28))) ltac:(apply zbv_not; lia).
      stepb_ft F_25574 D_25574 ltac:(condZ).
      zv F_25578 D_25578 (Z_to_bv 64 (dp + 4 * nc + 28)).
      sn F_2557c D_2557c. fixv (Z_to_bv 64 (Z.lor (p_data v) (dp + 4 * nc + 28))) ltac:(apply zbv_or; lia).
      guard4 F_25580 D_25580 ALo. stepb_ft F_25584 D_25584 ltac:(condZ).
      sn F_25588 D_25588. sn F_2558c D_2558c. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_L0 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25590) m rom) (mkst regs' (rl dVL_25134 0x255f0) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rp H2 H22. eexists. split.
    - stepb_tk F_25590 D_25590 ltac:(condZ). stepLD8 F_255ac D_255ac (Z_to_bv 64 pixd). sn F_255b0 D_255b0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_L1 : forall regs m (s pixd nc cm : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 22 = Z_to_bv 64 nc -> getr regs 9 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x25590) m rom) (mkst regs' (rl dVL_244bc 0x244bc) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 (s - 76) /\ getr regs' 1 = rl dVL_25134 0x255a4
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof.
    intros regs m s pixd nc cm Hs Hs64 Hp Hnc Rp H2 H22 H9. eexists. split.
    - stepb_ft F_25590 D_25590 ltac:(condZ). stepLD8 F_25594 D_25594 (Z_to_bv 64 pixd).
      zv F_25598 D_25598 (Z_to_bv 64 (s - 76)). sn F_2559c D_2559c. sn F_255a0 D_255a0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_M1 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x255a4) m rom) (mkst regs' (rl dVL_25134 0x255f0) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
  Proof.
    intros regs m s pixd Hs Hs64 Hp Rv Rp H2. eexists. split.
    - stepLD F_255a4 D_255a4 (Z_to_le_bytes 4 1) (Z_to_bv 64 1) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_ft F_255a8 D_255a8 ltac:(condZ). stepLD8 F_255ac D_255ac (Z_to_bv 64 pixd). sn F_255b0 D_255b0. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.

  (* [comment removed for export] *)
  Lemma pd_M0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (rl dVL_25134 0x255a4) m rom) (mkst regs' (rl dVL_23d30 0x23d30) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = rl dVL_25134 0x255bc /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
  Proof.
    intros regs m s Hs Hs64 Rv H2. eexists. split.
    - stepLD F_255a4 D_255a4 (Z_to_le_bytes 4 0) (Z_to_bv 64 0) ltac:(addr_norm; exact Rv) ltac:(apply lez4; lia).
      stepb_tk F_255a8 D_255a8 ltac:(condZ). zv F_255b4 D_255b4 (Z_to_bv 64 (s - 96)). sn F_255b8 D_255b8. apply mst_refl.
    - repeat split; gres; pin; try reflexivity. solve_regs_agree.
  Qed.
End Segs.
End DeserB.
