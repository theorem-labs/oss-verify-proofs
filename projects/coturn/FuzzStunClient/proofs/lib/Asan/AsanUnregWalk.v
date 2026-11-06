(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec MmapSim StepTac Hoare RefEnframeArith MemsetLib RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import Asan_code_ug Asan_code_cpm AsanRegionPoisoned AsanPartialGranule AsanMemset.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanNodesUG AsanNodesUGSoundG.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import RefReadLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section UG.
  Variables (mem rom : word -> option byte).

  (* [comment removed for export] *)
  Lemma ug_last : forall regs (g odr a1v : Z),
    (0 <= g)%Z -> (g + 64 < 2 ^ 64)%Z -> (0 <= odr < 2 ^ 64)%Z -> (0 <= a1v < 2)%Z ->
    v_addi (Z_to_bv 64 odr) 1 = Z_to_bv 64 a1v ->
    rdn SEGS mem (Z_to_bv 64 (g + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 odr)) ->
    getr regs 20 = Z_to_bv 64 g -> getr regs 27 = Z_to_bv 64 1 -> getr regs 18 = Z_to_bv 64 2 ->
    exists regs',
      msteps SEGS (mkst regs (0x41d44 : word) mem rom) (mkst regs' (0x41f60 : word) mem rom)
      /\ getr regs' 20 = Z_to_bv 64 (g + 64) /\ getr regs' 27 = Z_to_bv 64 0
      /\ (forall x, x <> 10 -> x <> 11 -> x <> 20 -> x <> 27 -> getr regs' x = getr regs x).
  Proof.
    intros regs g odr a1v Hg Hg64 Hodr Ha1 Ea1 Rodr H20 H27 H18.
    eexists. split; [|split; [|split]].
    - mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 odr) F_41d44 eq_refl D_41d44);
                   [ gr; rewrite ?H20; imm_norm; zn; exact Rodr | apply bytes_le_to_Z_8 ]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d48 eq_refl D_41d48)). gr. rewrite Ea1.
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_41d4c eq_refl D_41d4c); gr; rewrite ?H18; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d50 eq_refl D_41d50)). gr. rewrite H27. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d54 eq_refl D_41d54)). gr. rewrite H20. zn.
      mstep ltac:(eapply (step_beq_tk _ _ _ _ _ _ _ _ _ F_41d58 eq_refl D_41d58); gr; rewrite ?getr_zero; br_eq).
      apply mst_refl.
    - gr. f_equal; lia.
    - gr. f_equal; lia.
    - intros x N10 N11 N20 N27. repeat (rewrite getr_other by assumption). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma ret_41c44 : v_jalr (v_addi (0x41d5c : word) 4) (bv_signed (0 : bv 12)) = (0x41d60 : word).
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma ret_41d78 : v_jalr (v_addi (0x41e90 : word) 4) (bv_signed (0 : bv 12)) = (0x41e94 : word).
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma sltiu_0_1 : v_sltiu (Z_to_bv 64 (1 + -1)) 1 = Z_to_bv 64 1.
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma v_lw_1 : v_lw (Z_to_bv 64 1) = Z_to_bv 64 1.
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma jalr_ms : v_jalr (Z_to_bv 64 0xa45b0) (bv_signed (0 : bv 12)) = ms_entry.
  Proof. apply bv_eq. vm_compute. reflexivity. Qed.
  Lemma u8_small : forall z, (0 <= z < 256)%Z -> bv_unsigned (Z_to_bv 8 z) = z.
  Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. change (bv_modulus 8) with 256%Z. lia. Qed.
  (* [comment removed for export] *)
  Ltac ug_norm := repeat match goal with
    | |- context [v_sltu (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => wlit_closed (v_sltu (Z_to_bv 64 a) (Z_to_bv 64 b))
    | |- context [v_and (Z_to_bv 64 ?a) (Z_to_bv 64 ?b)] => wlit_closed (v_and (Z_to_bv 64 a) (Z_to_bv 64 b))
    | |- context [v_addi (Z_to_bv 64 0) ?i] => wlit_closed (v_addi (Z_to_bv 64 0) i)
    end.

  Definition SH : Z := 0x7fff8000.
  Definition MS : Z := 0xa45b0.

  (* [comment removed for export] *)
  Lemma ug_iter : forall regs (g cnt odr a1v beg swr sb thr : Z),
    (0 <= g)%Z -> (g + 128 < 2 ^ 64)%Z -> (0 <= odr < 2 ^ 64)%Z -> (0 <= a1v < 2)%Z -> (2 <= cnt < 2 ^ 32)%Z ->
    v_addi (Z_to_bv 64 odr) 1 = Z_to_bv 64 a1v ->
    (0 <= beg <= 0x7fff7fff)%Z -> (beg mod 8 = 0)%Z -> (8 <= swr < 2 ^ 40)%Z -> (0 <= sb < 256)%Z -> (sb mod 8 = 0)%Z ->
    (0 <= SH + (beg + swr - 8) / 8 + 1 - (SH + beg / 8) < thr)%Z -> (thr < 2 ^ 64)%Z ->
    rdn SEGS mem (Z_to_bv 64 (g + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 odr)) ->
    cell mem (g + 64) beg -> cell mem (g + 80) swr ->
    rdn SEGS mem (Z_to_bv 64 (g + 80)) 1 = Some [Z_to_bv 8 sb] ->
    rdn SEGS mem (Z_to_bv 64 0xb42d8) 1 = Some [Z_to_bv 8 1] ->
    rdn SEGS mem (Z_to_bv 64 0xb2e5c) 1 = Some [Z_to_bv 8 1] ->
    rdn SEGS mem (Z_to_bv 64 0xb0e10) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 1)) ->
    cell mem 0xb35f8 SH -> cell mem 0x1451a0 thr -> cell mem 0xaccf0 MS ->
    getr regs 20 = Z_to_bv 64 g -> getr regs 27 = Z_to_bv 64 cnt -> getr regs 18 = Z_to_bv 64 2 ->
    getr regs 9 = Z_to_bv 64 0x145128 -> getr regs 23 = Z_to_bv 64 0xaccf0 -> getr regs 25 = Z_to_bv 64 0xb0df8 -> getr regs 26 = Z_to_bv 64 0xb35f8 ->
    exists regs',
      msteps SEGS (mkst regs (0x41d44 : word) mem rom) (mkst regs' ms_entry mem rom)
      /\ getr regs' 10 = Z_to_bv 64 (SH + beg / 8) /\ getr regs' 11 = Z_to_bv 64 0
      /\ getr regs' 12 = Z_to_bv 64 (SH + (beg + swr - 8) / 8 + 1 - (SH + beg / 8))
      /\ getr regs' 1 = (0x41d44 : word) /\ getr regs' 8 = Z_to_bv 64 (SH + (beg + swr - 8) / 8 + 1)
      /\ getr regs' 20 = Z_to_bv 64 (g + 64) /\ getr regs' 27 = Z_to_bv 64 (cnt - 1)
      /\ (forall x, x <> 1 -> x <> 8 -> x <> 10 -> x <> 11 -> x <> 12 -> x <> 13 -> x <> 20 -> x <> 27 -> getr regs' x = getr regs x).
  Proof.
    intros regs g cnt odr a1v beg swr sb thr Hg Hg64 Hodr Ha1 Hcnt Ea1 Hbeg Hb8 Hswr Hsb Hsb8 Hthr Hthr64
           Rodr Rbeg Rswr Rswb Cin Ccp Crg Csh Cthr Cms H20 H27 H18 H9 H23 H25 H26.
    unfold SH, MS in *.
    assert (Q1 : (0 <= beg / 8 <= beg)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    assert (Q2 : (0 <= (beg + swr - 8) / 8 <= beg + swr - 8)%Z) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
    eexists. split.
    - mstep ltac:(eapply (@step_ld _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 odr) F_41d44 eq_refl D_41d44);
                   [ gr; rewrite ?H20; imm_norm; zn; exact Rodr | apply bytes_le_to_Z_8 ]).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d48 eq_refl D_41d48)). gr. rewrite Ea1.
      mstep ltac:(eapply (step_bgeu_ft _ _ _ _ _ _ _ _ _ F_41d4c eq_refl D_41d4c); gr; rewrite ?H18; br_lt).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d50 eq_refl D_41d50)). gr. rewrite H27. zn.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d54 eq_refl D_41d54)). gr. rewrite H20. zn.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_41d58 eq_refl D_41d58); gr; rewrite ?getr_zero; br_eq).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_41d5c eq_refl D_41d5c)).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3f30) F_5af30 eq_refl D_5af30);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_5af34 eq_refl D_5af34); gr; imm_norm; zn; exact Cin).
      rewrite v_lb_1.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_5af38 eq_refl D_5af38)).
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_5af3c eq_refl D_5af3c)). gr. zn.
      mstep ltac:(exact (step_sltiu _ _ _ _ _ _ _ _ _ F_5af40 eq_refl D_5af40)). gr. rewrite sltiu_0_1.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (v_addi (0x41d5c : word) 4) F_5af44 eq_refl D_5af44); gr; reflexivity |].
      rewrite ret_41c44.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_41d60 eq_refl D_41d60); gr; rewrite ?getr_zero; br_eq).
      (* [comment removed for export] *)
      mstep ltac:(eapply (@step_lw _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 1) F_41d64 eq_refl D_41d64);
                   [ gr; rewrite ?H25; imm_norm; zn; exact Crg | vm_compute; reflexivity ]).
      rewrite v_lw_1.
      mstep ltac:(eapply (step_blt_tk _ _ _ _ _ _ _ _ _ F_41d68 eq_refl D_41d68); gr; rewrite ?H18; rewrite c_lts_zbv by lia; apply Z.ltb_lt; lia).
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_41d7c eq_refl D_41d7c); gr; rewrite ?getr_zero; br_eq).
      (* [comment removed for export] *)
      mld F_41d80 D_41d80 2147450880%Z Csh H26.
      mld F_41d84 D_41d84 beg Rbeg H20.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d88 eq_refl D_41d88)). gr. zn.
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_41d8c eq_refl D_41d8c)). gr. ug_norm.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d90 eq_refl D_41d90)). gr. ug_norm.
      mstep ltac:(exact (step_and _ _ _ _ _ _ _ _ _ F_41d94 eq_refl D_41d94)). gr. ug_norm.
      mstep ltac:(eapply (step_bgeu_tk _ _ _ _ _ _ _ _ _ F_41d98 eq_refl D_41d98); gr; br_lt).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_41e7c eq_refl D_41e7c)). gr. rewrite v_andi_7 by lia. rewrite Hb8.
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_41e80 eq_refl D_41e80); gr; rewrite ?getr_zero; br_eq).
      mstep ltac:(eapply (@step_lbu _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 sb) F_41e84 eq_refl D_41e84); gr; imm_norm; zn;
                   replace (g + 64 + 16)%Z with (g + 80)%Z by lia; exact Rswb).
      rewrite (u8_small sb Hsb).
      mstep ltac:(exact (step_andi _ _ _ _ _ _ _ _ _ F_41e88 eq_refl D_41e88)). gr. rewrite v_andi_7 by lia. rewrite Hsb8.
      mstep ltac:(eapply (step_bne_ft _ _ _ _ _ _ _ _ _ F_41e8c eq_refl D_41e8c); gr; rewrite ?getr_zero; br_eq).
      (* [comment removed for export] *)
      mstep ltac:(exact (step_jal_link _ _ _ _ _ _ _ _ F_41e90 eq_refl D_41e90)).
      mstep ltac:(eapply (step_auipc_at _ _ _ _ _ _ _ _ (Z_to_bv 64 0xb3010) F_56010 eq_refl D_56010);
                   [reflexivity | apply bv_eq; vm_compute; reflexivity]).
      mstep ltac:(eapply (@step_lb _ _ _ _ _ _ _ _ _ _ (Z_to_bv 8 1) F_56014 eq_refl D_56014); gr; imm_norm; zn; exact Ccp).
      rewrite v_lb_1.
      mstep ltac:(exact (step_fence _ _ _ _ _ _ _ _ _ _ _ F_56018 eq_refl D_56018)).
      mstep ltac:(exact (step_sltu _ _ _ _ _ _ _ _ _ F_5601c eq_refl D_5601c)). gr. rewrite getr_zero, v_sltu_0_1.
      eapply mst_step; [reflexivity | eapply (step_jalr_x0 _ _ _ _ _ _ _ _ (v_addi (0x41e90 : word) 4) F_56020 eq_refl D_56020); gr; reflexivity |].
      rewrite ret_41d78.
      mstep ltac:(eapply (step_beq_ft _ _ _ _ _ _ _ _ _ F_41e94 eq_refl D_41e94); gr; rewrite ?getr_zero; br_eq).
      (* [comment removed for export] *)
      mld F_41e98 D_41e98 beg Rbeg H20.
      mld F_41e9c D_41e9c swr Rswr H20.
      mld F_41ea0 D_41ea0 2147450880%Z Csh H26.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_41ea4 eq_refl D_41ea4)). gr. rewrite (v_srli_3 beg) by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_41ea8 eq_refl D_41ea8)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_41eac eq_refl D_41eac)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41eb0 eq_refl D_41eb0)). gr. zn.
      mstep ltac:(exact (PropExec.step_srli _ _ _ _ _ _ _ _ _ F_41eb4 eq_refl D_41eb4)). gr. rewrite (v_srli_3 (beg + swr + -8)) by lia.
      replace (beg + swr + -8)%Z with (beg + swr - 8)%Z by lia.
      mld F_41eb8 D_41eb8 thr Cthr H9.
      mstep ltac:(exact (step_add _ _ _ _ _ _ _ _ _ F_41ebc eq_refl D_41ebc)). gr. rewrite v_add_zbv by lia.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41ec0 eq_refl D_41ec0)). gr. zn.
      mstep ltac:(exact (step_sub _ _ _ _ _ _ _ _ _ F_41ec4 eq_refl D_41ec4)). gr. rewrite v_sub_zbv by lia.
      mstep ltac:(eapply (step_bltu_tk _ _ _ _ _ _ _ _ _ F_41ec8 eq_refl D_41ec8); gr; br_lt).
      (* [comment removed for export] *)
      mld F_41d38 D_41d38 673200%Z Cms H23.
      mstep ltac:(exact (step_addi _ _ _ _ _ _ _ _ _ F_41d3c eq_refl D_41d3c)). gr. rewrite getr_zero. zn.
      eapply mst_step; [reflexivity | eapply (step_jalr_link _ _ _ _ _ _ _ _ _ (Z_to_bv 64 673200) F_41d40 eq_refl D_41d40); [reflexivity | gr; reflexivity] |].
      rewrite jalr_ms.
      apply mst_refl.
    - repeat split.
      + gr. reflexivity.
      + gr. f_equal; lia.
      + gr. reflexivity.
      + gr. apply bv_eq. vm_compute. reflexivity.
      + gr. reflexivity.
      + gr. reflexivity.
      + gr. f_equal; lia.
      + intros x N1 N8 N10 N11 N12 N13 N20 N27. repeat (rewrite getr_other by assumption). reflexivity.
  Qed.
End UG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition THR : Z := (2 ^ 64 - 1)%Z.
(* [comment removed for export] *)
Definition rec_okb (r : Z * Z * Z) : bool :=
  let '(beg, swr, odr) := r in
  let f := UGN.fill_of SH r in
  forallb (fun b : bool => b)
    [ (0 <=? beg)%Z; (beg <=? 0x7fff7fff)%Z; (beg mod 8 =? 0)%Z; (8 <=? swr)%Z; (swr <? 2 ^ 40)%Z; ((swr mod 256) mod 8 =? 0)%Z
    ; ((odr =? 0) || (odr =? 2 ^ 64 - 1))%Z; (0 <=? snd f)%Z; (snd f <? THR)%Z ].

Lemma odr_a1 : forall odr, (odr = 0 \/ odr = 2 ^ 64 - 1)%Z -> exists a1v, (0 <= a1v < 2)%Z /\ v_addi (Z_to_bv 64 odr) 1 = Z_to_bv 64 a1v.
Proof.
  intros odr [->| ->]; [exists 1%Z | exists 0%Z]; (split; [lia | apply bv_eq; vm_compute; reflexivity]).
Qed.

Lemma rec_okb_sound : forall beg swr odr, rec_okb (beg, swr, odr) = true ->
  (0 <= beg <= 0x7fff7fff /\ beg mod 8 = 0 /\ 8 <= swr < 2 ^ 40 /\ (swr mod 256) mod 8 = 0 /\ (odr = 0 \/ odr = 2 ^ 64 - 1)
   /\ 0 <= (beg + swr - 8) / 8 + 1 - beg / 8 < THR)%Z.
Proof.
  intros beg swr odr Hr. unfold rec_okb in Hr. cbn [forallb] in Hr.
  repeat match type of Hr with (?a && ?b)%bool = true => apply andb_prop in Hr; destruct Hr as [?X Hr]; revert X end.
  intros K9 K8 K7 K6 K5 K4 K3 K2 K1. clear Hr.
  apply Z.leb_le in K1. apply Z.leb_le in K2. apply Z.eqb_eq in K3. apply Z.leb_le in K4. apply Z.ltb_lt in K5. apply Z.eqb_eq in K6.
  apply Z.leb_le in K8. apply Z.ltb_lt in K9. unfold UGN.fill_of in K8, K9. cbn [fst snd] in K8, K9.
  assert (Kodr : (odr = 0 \/ odr = 2 ^ 64 - 1)%Z) by (apply orb_prop in K7 as [K7|K7]; apply Z.eqb_eq in K7; [left|right]; exact K7).
  repeat split; try assumption; lia.
Qed.

Lemma rd_fill : forall m f c lo, rd_ok SEGS m c -> (let '(a, w, _) := c in 0 <= a /\ a + Z.of_nat w <= lo)%Z ->
  (lo <= fst f)%Z -> (0 <= snd f)%Z -> (fst f + snd f < 2 ^ 64)%Z -> rd_ok SEGS (ug_fill1 m f) c.
Proof.
  intros m f [[a w] v] lo H (Ha & Haw) Hf Hl Hw. unfold rd_ok in *. unfold ug_fill1. rewrite <- H.
  pose proof (zbv_u a ltac:(lia)) as Ua. pose proof (zbv_u (fst f) ltac:(lia)) as Uf.
  apply rdn_wbytes_out; rewrite ?repeat_length, ?Ua, ?Uf, ?Z2Nat.id by lia; lia.
Qed.


Lemma glob_reads_bound : forall gl g, (0 <= g)%Z ->
  Forall (fun c : Z * nat * Z => let '(a, w, _) := c in 0 <= a /\ a + Z.of_nat w <= g + 64 * Z.of_nat (length gl))%Z (UGN.glob_reads g gl).
Proof.
  induction gl as [|[[beg swr] odr] gl IH]; intros g Hg; cbn [UGN.glob_reads length]; [constructor|].
  repeat (apply Forall_cons; [cbn; lia|]).
  eapply Forall_impl; [|apply (IH (g + 64)%Z); lia]. intros [[a w] v] H. cbn beta iota in H |- *. lia.
Qed.

Lemma ret_ok_41c28 : ret_ok (0x41d44 : word).
Proof. unfold ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.
Lemma cbyte_0 : cbyte (Z_to_bv 64 0) = Z_to_bv 8 0.
Proof. apply bv_eq. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Ltac ms_keep AG := apply AG; cbn [In ms_clob]; intros HH; repeat (destruct HH as [HH|HH]; [discriminate HH|]); exact HH.

Section LOOP.
  Variable rom : word -> option byte.
  Variables LO HI : Z.
  Hypothesis HLO : (0x1451a8 <= LO)%Z.
  Hypothesis HHI : (HI < 2 ^ 64)%Z.

  Definition cells_ok (m : word -> option byte) : Prop :=
    rd_ok SEGS m (0xb42d8, 1%nat, 1)%Z /\ rd_ok SEGS m (0xb2e5c, 1%nat, 1)%Z /\ rd_ok SEGS m (0xb0e10, 4%nat, 1)%Z
    /\ rd_ok SEGS m (0xb35f8, 8%nat, SH)%Z /\ rd_ok SEGS m (0x1451a0, 8%nat, THR)%Z /\ rd_ok SEGS m (0xaccf0, 8%nat, MS)%Z.

  Lemma cells_fill : forall m f, cells_ok m -> (LO <= fst f)%Z -> (0 <= snd f)%Z -> (fst f + snd f < 2 ^ 64)%Z -> cells_ok (ug_fill1 m f).
  Proof.
    intros m f (C1 & C2 & C3 & C4 & C5 & C6) Hf Hl Hw.
    repeat split; (eapply (rd_fill m f _ LO); [eassumption | cbn; lia | assumption | assumption | assumption]).
  Qed.

  Lemma ug_loop : forall gl (g : Z) mem regs,
    gl <> [] -> forallb rec_okb gl = true -> (0 <= g)%Z -> (g + 64 * Z.of_nat (length gl) + 64 <= LO)%Z -> (Z.of_nat (length gl) < 2 ^ 32)%Z ->
    Forall (fun f : Z * Z => LO <= fst f /\ fst f + snd f <= HI)%Z (map (UGN.fill_of SH) gl) ->
    Forall (rd_ok SEGS mem) (UGN.glob_reads g gl) -> cells_ok mem ->
    (forall j, (LO <= j < HI)%Z -> store_ok SEGS mem (Z_to_bv 64 j) 1 = true) ->
    getr regs 1 = (0x41d44 : word) -> getr regs 10 = Z_to_bv 64 (fst (UGN.fill_of SH (hd (0, 0, 0)%Z gl))) -> getr regs 11 = Z_to_bv 64 0 ->
    getr regs 12 = Z_to_bv 64 (snd (UGN.fill_of SH (hd (0, 0, 0)%Z gl))) ->
    getr regs 8 = Z_to_bv 64 (fst (UGN.fill_of SH (hd (0, 0, 0)%Z gl)) + snd (UGN.fill_of SH (hd (0, 0, 0)%Z gl))) ->
    getr regs 20 = Z_to_bv 64 g -> getr regs 27 = Z_to_bv 64 (Z.of_nat (length gl)) -> getr regs 18 = Z_to_bv 64 2 ->
    getr regs 9 = Z_to_bv 64 0x145128 -> getr regs 23 = Z_to_bv 64 0xaccf0 -> getr regs 25 = Z_to_bv 64 0xb0df8 -> getr regs 26 = Z_to_bv 64 0xb35f8 ->
    exists regs',
      msteps SEGS (mkst regs ms_entry mem rom) (mkst regs' (0x41f60 : word) (fold_left ug_fill1 (map (UGN.fill_of SH) gl) mem) rom)
      /\ getr regs' 8 = Z_to_bv 64 (let f := UGN.fill_of SH (last gl (0, 0, 0)%Z) in fst f + snd f)
      /\ getr regs' 20 = Z_to_bv 64 (g + 64 * Z.of_nat (length gl)) /\ getr regs' 27 = Z_to_bv 64 0
      /\ (forall x : reg, x <> 8 -> x <> 10 -> x <> 11 -> x <> 12 -> x <> 13 -> x <> 14 -> x <> 15 -> x <> 16 -> x <> 20 -> x <> 27 -> getr regs' x = getr regs x).
  Proof.
    induction gl as [|r gl IH]; intros g mem regs Hne Hok Hg HgLO Hlen Hf Hrd Hc Hst R1 R10 R11 R12 R8 R20 R27 R18 R9 R23 R25 R26; [congruence|].
    cbn [hd] in R10, R12, R8.
    destruct r as [[beg swr] odr].
    cbn [forallb] in Hok. apply andb_prop in Hok as [Hr Hok'].
    destruct (rec_okb_sound beg swr odr Hr) as (K1 & K3 & K4 & K6 & Kodr & K8).
    unfold UGN.fill_of in R10, R12, R8 |- *. cbn [fst snd] in R10, R12, R8.
    set (fa := (SH + beg / 8)%Z) in *. set (fl := ((beg + swr - 8) / 8 + 1 - beg / 8)%Z) in *.
    cbn [map] in Hf. apply Forall_cons_iff in Hf as [Hf0 Hf']. unfold UGN.fill_of in Hf0. cbn [fst snd] in Hf0. fold fa fl in Hf0. destruct Hf0 as [F1 F2].
    cbn [UGN.glob_reads] in Hrd.
    apply Forall_cons_iff in Hrd as [Rb Hrd]. apply Forall_cons_iff in Hrd as [Rs Hrd]. apply Forall_cons_iff in Hrd as [Rsb Hrd]. apply Forall_cons_iff in Hrd as [Ro Hrd].
    (* [comment removed for export] *)
    assert (Ufa : bv_unsigned (Z_to_bv 64 fa) = fa) by (apply zbv_u; lia).
    assert (Ufl : bv_unsigned (Z_to_bv 64 fl) = fl) by (apply zbv_u; unfold THR in K8; lia).
    destruct (memset_summary_w mem (Z_to_bv 64 fa) (Z_to_bv 64 0) (0x41d44 : word) (Z_to_bv 64 fl) rom regs
                ltac:(rewrite Ufa, Ufl; lia)
                ltac:(rewrite Ufl; apply store_ok_bytes; [lia | rewrite Z2Nat.id by lia; lia | intros j Hj; rewrite Z2Nat.id in Hj by lia; apply Hst; lia])
                ret_ok_41c28 R10 R11 R12 R1) as (regs1 & RUN1 & A10 & AG & _).
    rewrite Ufl, cbyte_0 in RUN1. change (wbytes mem (Z_to_bv 64 fa) (repeat (Z_to_bv 8 0) (Z.to_nat fl))) with (ug_fill1 mem (fa, fl)) in RUN1.
    set (m1 := ug_fill1 mem (fa, fl)) in *.
    assert (FILL : forall c, rd_ok SEGS mem c -> (let '(a, w, _) := c in 0 <= a /\ a + Z.of_nat w <= LO)%Z -> rd_ok SEGS m1 c).
    { intros c Hc0 Hb. apply (rd_fill mem (fa, fl) c LO Hc0 Hb); cbn [fst snd]; lia. }
    assert (Hc1 : cells_ok m1) by (apply cells_fill; cbn [fst snd]; [exact Hc | lia | lia | lia]).
    assert (Hst1 : forall j, (LO <= j < HI)%Z -> store_ok SEGS m1 (Z_to_bv 64 j) 1 = true).
    { intros j Hj. unfold m1, ug_fill1. apply store_ok1_wbytes. apply Hst. exact Hj. }
    assert (G1 : getr regs1 1 = (0x41d44 : word)) by (rewrite <- R1; ms_keep AG).
    assert (G8 : getr regs1 8 = Z_to_bv 64 (fa + fl)) by (rewrite <- R8; ms_keep AG).
    assert (G20 : getr regs1 20 = Z_to_bv 64 g) by (rewrite <- R20; ms_keep AG).
    assert (G27 : getr regs1 27 = Z_to_bv 64 (Z.of_nat (length ((beg, swr, odr) :: gl)))) by (rewrite <- R27; ms_keep AG).
    assert (G18 : getr regs1 18 = Z_to_bv 64 2) by (rewrite <- R18; ms_keep AG).
    assert (G9 : getr regs1 9 = Z_to_bv 64 0x145128) by (rewrite <- R9; ms_keep AG).
    assert (G23 : getr regs1 23 = Z_to_bv 64 0xaccf0) by (rewrite <- R23; ms_keep AG).
    assert (G25 : getr regs1 25 = Z_to_bv 64 0xb0df8) by (rewrite <- R25; ms_keep AG).
    assert (G26 : getr regs1 26 = Z_to_bv 64 0xb35f8) by (rewrite <- R26; ms_keep AG).
    destruct (odr_a1 odr Kodr) as (a1v & Ha1 & Ea1).
    assert (RoM : rdn SEGS m1 (Z_to_bv 64 (g + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 odr))).
    { apply (FILL (g + 56, 8%nat, odr)%Z Ro). cbn [length] in HgLO. lia. }
    destruct gl as [|r' gl'].
    - (* [comment removed for export] *)
      cbn [length] in G27, HgLO.
      destruct (ug_last m1 rom regs1 g odr a1v Hg ltac:(lia) ltac:(destruct Kodr; lia) Ha1 Ea1 RoM G20 G27 G18) as (regs2 & RUN2 & Q20 & Q27 & FR2).
      exists regs2. split; [eapply msteps_trans; [exact RUN1 | exact RUN2]|].
      cbn [map fold_left last length fst snd]. unfold UGN.fill_of. cbn [fst snd]. fold fa fl.
      split; [rewrite FR2 by discriminate; exact G8|].
      split; [rewrite Q20; f_equal; lia|]. split; [exact Q27|].
      intros x N8 N10 N11 N12 N13 N14 N15 N16 N20 N27. rewrite FR2 by assumption.
      apply AG. cbn [In ms_clob]. intros HH. repeat (destruct HH as [HH|HH]; [subst x; congruence|]). exact HH.
    - (* [comment removed for export] *)
      destruct r' as [[beg' swr'] odr'].
      pose proof Hok' as Hok2. cbn [forallb] in Hok2. apply andb_prop in Hok2 as [Hr' _].
      destruct (rec_okb_sound beg' swr' odr' Hr') as (L1 & L3 & L4 & L6 & _ & L8).
      cbn [UGN.glob_reads] in Hrd. pose proof Hrd as Hrd2.
      apply Forall_cons_iff in Hrd2 as [Rb' Hrd2]. apply Forall_cons_iff in Hrd2 as [Rs' Hrd2]. apply Forall_cons_iff in Hrd2 as [Rsb' _].
      pose proof (Z.mod_pos_bound swr' 256 ltac:(lia)) as Hsb'.
      cbn [length] in HgLO, Hlen, G27. rewrite !Nat2Z.inj_succ in HgLO, Hlen, G27.
      assert (RbM : cell m1 (g + 64) beg') by (apply (FILL (g + 64, 8%nat, beg')%Z Rb'); lia).
      assert (RsM : cell m1 (g + 80) swr').
      { replace (g + 80)%Z with (g + 64 + 16)%Z by lia. apply (FILL (g + 64 + 16, 8%nat, swr')%Z Rs'). lia. }
      assert (RsbM : rdn SEGS m1 (Z_to_bv 64 (g + 80)) 1 = Some [Z_to_bv 8 (swr' mod 256)]).
      { pose proof (FILL (g + 64 + 16, 1%nat, swr' mod 256)%Z Rsb' ltac:(cbn; lia)) as X. unfold rd_ok in X.
        replace (g + 80)%Z with (g + 64 + 16)%Z by lia. rewrite X. rewrite N_to_le_bytes_1_small, zbv_u by lia. reflexivity. }
      destruct Hc1 as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (ug_iter m1 rom regs1 g (Z.succ (Z.succ (Z.of_nat (length gl')))) odr a1v beg' swr' (swr' mod 256) THR
                  Hg ltac:(lia) ltac:(destruct Kodr; lia) Ha1 ltac:(lia) Ea1 L1 L3 L4 Hsb' L6
                  ltac:(unfold SH in *; lia) ltac:(unfold THR; lia) RoM RbM RsM RsbM C1 C2 C3 C4 C5 C6 G20 G27 G18 G9 G23 G25 G26)
        as (regs2 & RUN2 & Q10 & Q11 & Q12 & Q1 & Q8 & Q20 & Q27 & FR2).
      destruct (IH (g + 64)%Z m1 regs2 ltac:(discriminate) Hok' ltac:(lia) ltac:(cbn [length]; rewrite Nat2Z.inj_succ; lia)
                  ltac:(cbn [length]; rewrite Nat2Z.inj_succ; lia) Hf'
                  ltac:(apply Forall_forall; intros c Hin; apply FILL; [exact (proj1 (Forall_forall _ _) Hrd c Hin)|];
                        pose proof (proj1 (Forall_forall _ _) (glob_reads_bound ((beg', swr', odr') :: gl') (g + 64)%Z ltac:(lia)) c Hin) as Hb;
                        destruct c as [[a w] v]; cbn beta iota in Hb |- *; cbn [length] in Hb; rewrite Nat2Z.inj_succ in Hb; lia)
                  (conj C1 (conj C2 (conj C3 (conj C4 (conj C5 C6))))) Hst1 Q1
                  ltac:(cbn [hd]; unfold UGN.fill_of; cbn [fst snd]; exact Q10) Q11
                  ltac:(cbn [hd]; unfold UGN.fill_of; cbn [fst snd]; rewrite Q12; f_equal; lia)
                  ltac:(cbn [hd]; unfold UGN.fill_of; cbn [fst snd]; rewrite Q8; f_equal; lia)
                  Q20 ltac:(rewrite Q27; cbn [length]; rewrite Nat2Z.inj_succ; f_equal; lia)
                  ltac:(rewrite FR2 by discriminate; exact G18) ltac:(rewrite FR2 by discriminate; exact G9)
                  ltac:(rewrite FR2 by discriminate; exact G23) ltac:(rewrite FR2 by discriminate; exact G25)
                  ltac:(rewrite FR2 by discriminate; exact G26))
        as (regs3 & RUN3 & S8 & S20 & S27 & FR3).
      exists regs3. split; [eapply msteps_trans; [exact RUN1 | eapply msteps_trans; [exact RUN2 | exact RUN3]]|].
      split; [exact S8|]. split; [rewrite S20; cbn [length]; rewrite !Nat2Z.inj_succ; f_equal; lia|]. split; [exact S27|].
      intros x N8 N10 N11 N12 N13 N14 N15 N16 N20 N27. rewrite FR3 by assumption.
      destruct (bv_eq_dec 5 x 1) as [->|N1]; [rewrite Q1, R1; reflexivity|].
      rewrite FR2 by assumption.
      apply AG. cbn [In ms_clob]. intros HH. repeat (destruct HH as [HH|HH]; [subst x; congruence|]). exact HH.
  Qed.
End LOOP.
