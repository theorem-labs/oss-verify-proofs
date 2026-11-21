(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (recorded (KReplay) proofs re-proved by tactics). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import ImageA.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import Layout.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.K5.A02 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit LeptL_kit Lept_chain Lept_leaf Lept_objkit Lept_deserkit Pm_gaps_iface Pm_iface Pm_iface2 Pm_iface4 Pm_ckit Pm_okit Cf_iface Cf_kit Km_setelem Km_iface Km_kit RT_fk RT_fk_iface Bi_iface Bi_fktw Bi_fkkit Bi_ropkit Bi_ropl_wa Bi_ropl_gk Bi_ropl_gdef Bi_ropu_iface Bi_ropu_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* The last-word and first-word masks: the bytes of lmask32 (0x28d20) and rmask32 (0x28c60), read from the image. *)
Local Lemma ropu_lmask_bytes : forall m : mem, mem_inv asegs m ->
  exists bs, bytes_at asegs m 0x28d20 bs /\ Z.of_nat (length bs) = 132.
Proof.
  intros m MI. destruct (image_bytes asegs 0x28d20 132) as [bs|] eqn:IB; [| vm_compute in IB; discriminate IB].
  assert (OK : ro_bytes_b asegs 0x28d20 bs = true) by (vm_compute in IB; injection IB as <-; vm_compute; reflexivity).
  pose proof (image_bytes_length asegs _ _ _ IB) as LB.
  exists bs. split; [apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK]| rewrite LB; reflexivity].
Qed.
Local Lemma ropu_rmask_bytes : forall m : mem, mem_inv asegs m ->
  exists bs, bytes_at asegs m 0x28c60 bs /\ Z.of_nat (length bs) = 132.
Proof.
  intros m MI. destruct (image_bytes asegs 0x28c60 132) as [bs|] eqn:IB; [| vm_compute in IB; discriminate IB].
  assert (OK : ro_bytes_b asegs 0x28c60 bs = true) by (vm_compute in IB; injection IB as <-; vm_compute; reflexivity).
  pose proof (image_bytes_length asegs _ _ _ IB) as LB.
  exists bs. split; [apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK]| rewrite LB; reflexivity].
Qed.

(* The clipping of the rectangle to the image: what each clamp computes on a rectangle that lies inside the image. *)
Local Lemma ropu_srai63_nonneg : forall X, 0 <= X < 2^63 -> Z.shiftr (bv_signed (Z_to_bv 64 X)) 63 = 0.
Proof. intros X H. rewrite signed_lit64 by lia. rewrite Z.shiftr_div_pow2 by lia. apply Z.div_small. lia. Qed.
Local Lemma ropu_srai63_nonneg_div : forall X, 0 <= X < 2^63 -> bv_signed (Z_to_bv 64 X) / 9223372036854775808 = 0.
Proof. intros X H. rewrite signed_lit64 by lia. apply Z.div_small. lia. Qed.
Local Lemma ropu_lxor_sign_nonneg : forall X, 0 <= X < 2^63 -> Z.lxor X 9223372036854775808 = X + 9223372036854775808.
Proof.
  intros X H. change 9223372036854775808 with (2^63).
  rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.eq_dec n 63) as [->|NE].
  - rewrite (Z.bits_above_log2 X 63); [reflexivity| lia|]. destruct (Z.eq_dec X 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia.
  - rewrite Z.pow2_bits_false by lia. apply andb_false_r.
Qed.
Local Lemma ropu_sgtz_nonneg : forall X, 0 <= X < 2^63 -> Z.b2z (9223372036854775808 <? Z.lxor X 9223372036854775808) = Z.b2z (0 <? X).
Proof. intros X H. rewrite ropu_lxor_sign_nonneg by lia. f_equal. destruct (Z.ltb_spec 9223372036854775808 (X + 9223372036854775808)), (Z.ltb_spec 0 X); lia || reflexivity. Qed.
Local Lemma ropu_land_negw_sgtz : forall E, 0 <= E < 2^63 -> Z.land (bv_swrap 32 (0 - Z.b2z (0 <? E)) mod 18446744073709551616) E = E.
Proof.
  intros E H. destruct (Z.eq_dec E 0) as [->|NE]; [apply Z.land_0_r|].
  replace (0 <? E) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change (bv_swrap 32 (0 - 1) mod 18446744073709551616) with 18446744073709551615. apply land_ones64. lia.
Qed.
Local Lemma ropu_land_neg_sgtz : forall E, 0 <= E < 2^63 -> Z.land ((0 - Z.b2z (0 <? E)) mod 18446744073709551616) E = E.
Proof.
  intros E H. destruct (Z.eq_dec E 0) as [->|NE]; [apply Z.land_0_r|].
  replace (0 <? E) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
  change ((0 - 1) mod 18446744073709551616) with 18446744073709551615. apply land_ones64. lia.
Qed.
Local Lemma ropu_swrap32_modadd : forall A B, - 2^31 <= A + B < 2^31 -> bv_swrap 32 (A mod 18446744073709551616 + B) = A + B.
Proof.
  intros A B H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with 4294967296. change (4294967296 / 2) with 2147483648.
  change (2^31) with 2147483648 in H.
  Z.div_mod_to_equations. lia.
Qed.
Local Lemma ropu_lxor_sign_high : forall Y, 9223372036854775808 <= Y < 18446744073709551616 -> Z.lxor Y 9223372036854775808 = Y - 9223372036854775808.
Proof.
  intros Y H. set (Y' := Y - 9223372036854775808). replace Y with (Y' + 9223372036854775808) by (unfold Y'; lia).
  rewrite <- (ropu_lxor_sign_nonneg Y') by (unfold Y'; lia). rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r. unfold Y'. lia.
Qed.
Local Lemma ropu_sgtz_nonpos : forall E, - 2^63 <= E <= 0 ->
  Z.b2z (9223372036854775808 <? Z.lxor (E mod 18446744073709551616) 9223372036854775808) = 0.
Proof.
  intros E H. destruct (Z.eq_dec E 0) as [->|NE]; [reflexivity|].
  assert (M : E mod 18446744073709551616 = E + 18446744073709551616).
  { symmetry. apply (Z.mod_unique _ _ (-1)); lia. }
  rewrite M, ropu_lxor_sign_high by lia.
  replace (9223372036854775808 <? E + 18446744073709551616 - 9223372036854775808) with false; [reflexivity|].
  symmetry. apply Z.ltb_ge. lia.
Qed.
Local Lemma ropu_srliw5_small : forall j, 0 <= j < 2^31 -> bv_swrap 32 (bv_wrap 32 j / 32) = j / 32.
Proof.
  intros j Hj. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small j) by lia.
  apply bv_swrap_small. change (bv_half_modulus 32) with (2^31). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]| apply Z.div_lt_upper_bound; lia].
Qed.

(* The walk's normalisation between steps (BD: the hidden bounds of the rectangle). *)
Local Ltac ropu_cn BD :=
  rewrite ?Z.sub_0_r, ?Z.add_0_l, ?Z.add_0_r, ?Z.land_0_l;
  repeat match goal with |- context [bv_swrap 32 (?A mod 18446744073709551616 + ?B)] =>
    rewrite (ropu_swrap32_modadd A B) by (clear - BD; unfold hid in *; lia) end;
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD; unfold hid in *; lia) end;
  repeat match goal with
  | |- context [Z.b2z (9223372036854775808 <? Z.lxor (?E mod 18446744073709551616) 9223372036854775808)] =>
      rewrite (ropu_sgtz_nonpos E) by (clear - BD; unfold hid in *; lia)
  end;
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - BD; unfold hid in *; lia) end;
  repeat match goal with
  | |- context [Z.shiftr (bv_signed (Z_to_bv 64 ?X)) 63] => rewrite (ropu_srai63_nonneg X) by (clear - BD; unfold hid in *; lia)
  | |- context [bv_signed (Z_to_bv 64 ?X) / 9223372036854775808] => rewrite (ropu_srai63_nonneg_div X) by (clear - BD; unfold hid in *; lia)
  | |- context [Z.b2z (9223372036854775808 <? Z.lxor ?X 9223372036854775808)] => rewrite (ropu_sgtz_nonneg X) by (clear - BD; unfold hid in *; lia)
  | |- context [Z.land (bv_swrap 32 (0 - Z.b2z (0 <? ?E)) mod 18446744073709551616) ?E] => rewrite (ropu_land_negw_sgtz E) by (clear - BD; unfold hid in *; lia)
  | |- context [Z.land ((0 - Z.b2z (0 <? ?E)) mod 18446744073709551616) ?E] => rewrite (ropu_land_neg_sgtz E) by (clear - BD; unfold hid in *; lia)
  end;
  rewrite ?Z.sub_0_r, ?Z.add_0_l, ?Z.add_0_r, ?Z.land_0_l.
Local Ltac ropu_nwalk1 BD :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => first [ shbr | shbr0 | shbr_inv | shbr_x3 | br ]
  | |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) =>
      first [ shload; lstep; clear_shl | special_step | frame_step | lstep; try sb_fix; try fix_land32; shnorm ]; ropu_cn BD
  end.
Local Ltac ropu_nwalk stops BD := repeat (tryif at_stop stops then fail else ropu_nwalk1 BD).

(* What a walk may write, in the client's view: its own frame and the destination rows (D, N). *)
Local Ltac ropu_ivtw D N :=
  cbn [ivls_client]; split; [intros zz Hzz; left; ul| split; [intros zz Hzz; right; right; left; exists D, N; split; [solve [in_live_tac]| lia]| exact I]].
(* A client address outside the destination rows is outside what the walk wrote (PFS: it is not in the frame either). *)
Local Ltac ropu_pftw PFS Hx :=
  cbn [outside]; pose proof (PFS _ Hx); destruct Hx as [_ HxO]; cbn [outside] in HxO; split; [lia| split; [tauto| exact I]].
(* A lemma about a later memory starts afresh: forget what the walk knows of the memory it has reached. *)
Local Ltac ropu_restart :=
  repeat match goal with
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : acc _ _ _ _ |- _ => clear H
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  | H : LIBH _ |- _ => clear H
  | H : io_ssp _ |- _ => clear H
  | H : agree_on _ _ _ |- _ => clear H
  end.
(* The callee-saved F registers still agree with those at entry. *)
Local Ltac ropu_fk :=
  first [ eassumption | apply fs_agree_refl
        | match goal with FK1 : fs_agree ?F0 ?Fi, FK2 : fs_agree ?Fi ?Fn |- fs_agree ?F0 ?Fn => exact (fs_agree_trans _ _ _ FK1 FK2) end ].
(* A row of the destination: the bytes the loop touches in row dy + i' lie inside the dpixh rows of dwpl words. *)
Local Ltac ropu_rowfit dwpl dpixh dy :=
  let i' := fresh "i'" in let Hi := fresh "Hi'" in intros i' Hi;
  let M := fresh "M" in let N := fresh "N" in
  assert (M : dwpl * (dy + i' + 1) <= dwpl * dpixh) by (apply Z.mul_le_mono_nonneg_l; lia);
  assert (N : 0 <= dwpl * (dy + i')) by (apply Z.mul_nonneg_nonneg; lia);
  split; lia.
(* The side goals of a row lemma (uf_rows, ul_rows): the facts of the current memory, the bounds, and the row fit RF. *)
Local Ltac ropu_rows_side pf RF :=
  unfold parked, hid in *; unfold pf in *;
  lazymatch goal with
  | |- forall _ : Z, _ => RF
  | |- wr_at _ _ _ _ => eassumption
  | |- acc _ _ _ _ => eassumption
  | |- mem_inv _ _ => eassumption
  | |- _ \/ _ => eassumption
  | |- @eq Z (Z.of_nat _) _ => rewrite Z2Nat.id by lia; lia
  | |- _ => first [ lia | Z.div_mod_to_equations; lia ]
  end.

Section ROPUG.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis FKC : rt_fk_contracts RT.
Hypothesis TABR : In (167008, 132) ACC_LITS.
Hypothesis TABL : In (167200, 132) ACC_LITS.

Lemma ropu_clr_g3 : rasteropUniLow_clr_case RT 3.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    datad dpixw dpixh dwpl dx dy dw dh FDO MST -> -> -> -> -> -> -> -> SARGS DX0 DY0 DW0 DH0 DXW DYH DPW DPH
    DWPL DWC DNHI CH ENV RES DXMOD.
  set (op := PIX_CLR) in *.
  assert (OP : op = 0) by reflexivity.
  clearbody op.
  unfold lpost, lenv, keeps, keepsL, chunk in *.
  destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct CH as (DIN & D0 & D16 & DSZ).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R.
  pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_rasteropUniLow, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned).
  rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(datad, datad + 4 * (dwpl * dpixh))] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo)
    by (intros a [Ha _]; destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]).
  pose proof ST as (STa & STb & _).
  chunk_facts RT AF GP datad (4 * (dwpl * dpixh)).
  pose proof (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ TABL) as ACCL.
  cbn [fst snd] in ACCL.
  pose proof (proj1 (Forall_forall _ _) (af_acc_lits RT AF Σ m ART0) _ TABR) as ACCR.
  cbn [fst snd] in ACCR.
  refresh RT AF.
  unfold shad, SHB in *.
  park_disj.
  assert (BD : 0 <= dx /\ 0 <= dy /\ 0 < dw /\ 0 < dh /\ dx + dw <= dpixw /\ dy + dh <= dpixh /\ dpixw <= 20000 /\ dpixh <= 20000) by lia.
  hide BD.
  walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (dwpl * dpixh))] [0xaf9fc].
  ropu_cn BD.
  (* The clipping of the rectangle, up to the first-word mask. *)
  ropu_nwalk [0xafa88] BD.
  (* The epilogue from 0xafe8c: the saved registers, the frame, the return and the post-condition. *)
  assert (EPI : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word)
                       (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (pre : list cell),
    fs_agree F F' ->
    ART RT Σ m' -> mem_inv asegs m' -> stk asegs m' lo (usp + -128) -> LIBH m' -> io_ssp m' -> agree_on PF m m' -> wmono asegs m m' ->
    rw_cells asegs m' (usp + -128) pre -> cells_size pre = 24%nat ->
    rw_cells asegs m' (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                                     F' (Z_to_bv 64 0xafe8c) fc' None m' (seg_rom asegs)))) QF).
  {
    clear - AF MST USP ESP PFS STa STb LOW LOR SPT SPA SPB SP0R SP0W CKR CKS CKH DIN.
    intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' F' fc' m' pre
      FKe ARTe MIe STe LHe SSPe AGF WMe FRlo PRE FRe.
    walk_to AF MST [(usp - 128, usp)] (@nil Z).
    cps_stop.
    agf_munch AGF MU ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
    apply cps_finish.
    intros c Hc.
    subst QF.
    cbv beta.
    eapply (ASTA_conseq RT); [exact Hc|].
    intros ms <-.
    do 2 eexists.
    unfold ret_stF, ret_st, rt_after.
    split; [split; [try rewrite ESP; do 16 eexists; reflexivity| cbn [ms_fregs MS]; exact FKe]|].
    split; [split; [split; [exact ARTe| split; [exact MIe| split; [exact WMe|]]]| split; assumption]|].
    {
      eapply stk_release in FRlo; [| exact STe| lia].
      rewrite PRE in FRlo.
      eapply stk_release in FRe; [| replace (usp + -104) with (usp + -128 + Z.of_nat 24) by lia; exact FRlo| lia].
      cbn [cells_size csize Nat.add] in FRe.
      replace (usp + -104 + Z.of_nat 104) with usp in FRe by lia.
      exact FRe.
    }
    {
      intros a Ha Ho.
      exact (AGF a (conj Ha Ho)).
    }
  }
  ropu_nwalk [0xafa90] BD.
  change 31 with (Z.ones 5).
  rewrite (Z.land_ones (dx * 8) 5) by (clear - BD; unfold hid in *; lia).
  change (2^5) with 32.
  set (xb := (dx * 8) mod 32) in *.
  assert (XBR : 0 <= xb < 32) by (unfold xb; apply Z.mod_pos_bound; lia).
  assert (XBV : xb = 24) by (unfold xb; change 32 with (4 * 8); rewrite Z.mul_mod_distr_r by lia; rewrite DXMOD; reflexivity).
  hide XBR.
  lstep.
  brfork XB0.
  {
    exfalso.
    clear - XB0 XBV.
    lia.
  }
  (* The rectangle does not start on a word boundary: a first word, the full words, a last word. *)
  assert (XBN : 1 <= xb <= 31) by (clear - XBR XB0; unfold hid in *; lia).
  hide XBN.
  hide XBV.
  ropu_nwalk [0xafabc] BD.
  lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
    destruct (ropu_rmask_bytes mm MIx) as (rbs & RB & RBL);
    destruct (bytes_at_read4w mm 0x28c60 rbs ((32 - xb) * 4) RB ltac:(clear - XBN; unfold hid in *; lia) ltac:(rewrite RBL; clear - XBN; unfold hid in *; lia)) as (fm & RM) end.
  lstep.
  clear RM RB RBL rbs.
  ropu_nwalk [0xafad8] BD.
  assert (WPLB : 0 < dwpl <= 16777216) by (assert (dwpl * 1 <= dwpl * dpixh) by (apply Z.mul_le_mono_nonneg_l; lia); lia).
  assert (BD2 : 0 <= dy * dwpl /\ dy * dwpl + dh * dwpl <= dwpl * dpixh /\ dwpl * dpixh <= 16777216)
    by (clear - BD WPLB DNHI; unfold hid in *;
        pose proof (Z.mul_nonneg_nonneg dy dwpl ltac:(lia) ltac:(lia)) as N1;
        pose proof (Z.mul_le_mono_nonneg_r (dy + dh) dpixh dwpl ltac:(lia) ltac:(lia)) as N3;
        rewrite Z.mul_add_distr_r in N3; rewrite (Z.mul_comm dpixh dwpl) in N3; lia).
  assert (BD3 : dy * dwpl <= 16777216 /\ 0 <= dh * dwpl /\ dwpl <= dh * dwpl)
    by (clear - BD WPLB BD2; unfold hid in *;
        pose proof (Z.mul_nonneg_nonneg dh dwpl ltac:(lia) ltac:(lia));
        pose proof (Z.mul_le_mono_nonneg_r 1 dh dwpl ltac:(lia) ltac:(lia)); lia).
  rewrite !(ropu_srliw5_small (dx * 8)) by (clear - BD; unfold hid in *; lia).
  set (fw := dx * 8 / 32) in *.
  assert (FWD : 0 <= fw <= 5000) by (clear - BD; unfold hid in *; unfold fw; split; [apply Z.div_pos; lia| apply Z.div_le_upper_bound; lia]).
  repeat match goal with |- context [bv_swrap 32 ?z] =>
    rewrite (bv_swrap_small 32 z) by (change (bv_half_modulus 32) with (2^31); clear - BD BD2 BD3; unfold hid in *; lia) end.
  repeat match goal with |- context [?E mod 18446744073709551616] =>
    rewrite (Z.mod_small E 18446744073709551616) by (clear - BD BD2 BD3 FWD; unfold hid in *; lia) end.
  pose (dnf := (dw * 8 - (32 - xb)) / 32).
  pose (dlw := (dw * 8 + dx * 8) mod 32).
  pose (pfull := datad + dy * dwpl * 4 + fw * 4 + 4).
  assert (GF1 : fw + 1 <= dwpl) by (clear - BD DWC; unfold hid in *; unfold fw; Z.div_mod_to_equations; lia).
  assert (GF2 : 32 - xb <= dw * 8 -> fw + 1 + dnf <= dwpl)
    by (clear - BD DWC XBN; unfold hid in *; unfold fw, dnf, xb in *; intros; Z.div_mod_to_equations; lia).
  assert (GF2b : 32 - xb <= dw * 8 -> 0 <= dnf <= 5000)
    by (clear - BD XBN; unfold hid in *; unfold dnf, xb in *; intros; Z.div_mod_to_equations; lia).
  assert (GF3 : 32 - xb <= dw * 8 -> dlw <> 0 -> fw + 1 + dnf + 1 <= dwpl)
    by (clear - BD DWC XBN; unfold hid in *; unfold fw, dnf, dlw, xb in *; intros; Z.div_mod_to_equations; lia).
  assert (PFR0 : 0 < pfull) by (clear - BD2 FWD D0; unfold hid in *; unfold pfull; lia).
  assert (PFR1 : pfull <= datad + 4 * (dwpl * dpixh)) by (clear - GF1 BD2 BD3 FWD; unfold hid in *; unfold pfull; lia).
  assert (PFR2 : pfull <= 140737488355328) by (clear - PFR1 CKR SP0R; lia).
  assert (DLWR : 0 <= dlw < 32) by (unfold dlw; apply Z.mod_pos_bound; lia).
  hide DLWR.
  hide WPLB.
  hide BD2.
  hide BD3.
  hide FWD.
  (* The operation is PIX_CLR. *)
  subst op.
  (* After the full-word rows (0xafe88): the last-word rows when the rectangle ends inside a word, then the epilogue. *)
  assert (AFTER2C : forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s7' s9' s10' s11' t3' t4' t5' t6' v5 vs6 v8 : word)
                           (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) (j16 : list byte),
    (v8 = Z_to_bv 64 1 \/ (v8 = Z_to_bv 64 0 /\ v5 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)) ->
    fs_agree F F' ->
    ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -128) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
    rw_cells asegs mc (usp + -128) [CB 16 j16; C8 (Z_to_bv 64 dwpl)] ->
    rw_cells asegs mc (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                                          (Z_to_bv 64 (dwpl * 4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v5 vs6 s7' v8 s9' s10' s11' t3' t4' t5' t6')
                                     F' (Z_to_bv 64 0xafe88) fc' None mc (seg_rom asegs)))) QF).
  {
    ropu_restart.
    intros ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s7' s9' s10' s11' t3' t4' t5' t6' v5 vs6 v8 F' fc' mc j16
      GL FKc ARTc MI ST LH SSP AGF WMc FRlo FRe.
    refresh RT AF.
    unfold shad, SHB in *.
    park_disj.
    destruct GL as [V8|(V8 & V5 & DLWN & NDP)].
    {
      subst v8.
      walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (dwpl * dpixh))] [0xafe8c].
      cps_stop.
      art_now RT AF ltac:(ropu_ivtw datad (4 * (dwpl * dpixh))).
      lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ => agf_munch AGFx MUx ltac:(fun Hx => ropu_pftw PFS Hx) end.
      eapply EPI; try eassumption; try reflexivity; ropu_fk.
    }
    {
      subst v8 v5.
      walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (dwpl * dpixh))] [0xb0100].
      lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (wr_at_transport asegs mx mm datad (4 * (dwpl * dpixh)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (dwpl * dpixh)) A DIN)) WMx) as WRD end.
      pose proof (GF2 NDP) as GF2'.
      pose proof (GF2b NDP) as GF2b'.
      pose proof (GF3 NDP DLWN) as GF3'.
      regfix (Z_to_bv 5 10) (pfull + dnf * 4 + 4 * (dwpl * 0)).
      regfix (Z_to_bv 5 21) (pfull + dnf * 4 + 4 * (dwpl * 0)).
      regfix (Z_to_bv 5 20) (dh - 0).
      eapply evt_cut.
      {
        eapply (ul_rows (Z.to_nat dh) 0) with (DR := datad) (dn := 4 * (dwpl * dpixh)) (P := pfull + dnf * 4) (dh := dh) (dwpl := dwpl);
          ropu_rows_side pfull ltac:(ropu_rowfit dwpl dpixh dy).
      }
      intros ms' PO.
      unfold ul_exit in PO.
      destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & -> & MU' & WM' & MI').
      loop_art RT AF Σ m' lo MU' ltac:(ropu_ivtw datad (4 * (dwpl * dpixh))).
      lazymatch type of MU' with munch _ ?mm m' =>
        loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
      clear MU' WM'.
      cps_stop.
      lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ => agf_munch AGFx MUx ltac:(fun Hx => ropu_pftw PFS Hx) end.
      eapply EPI; try eassumption; try reflexivity; ropu_fk.
    }
  }
  (* The full-word rows from 0xb00e0: one __asan_memset per row, by induction on the rows left. *)
  assert (MLOOPC : forall (k : nat) (q : Z) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' s11' t3' t4' t5' t6' v5 vs6 v8 : word)
                          (F' : bvmap 5 word) (fc' : bv 32) (mc : mem) (j16 : list byte),
    (1 <= k)%nat -> Z.of_nat k <= 20000 -> 0 <= q -> q + (Z.of_nat k - 1) * dwpl + dnf <= dwpl * dpixh -> 1 <= dnf -> dnf <= 5000 ->
    (v8 = Z_to_bv 64 1 \/ (v8 = Z_to_bv 64 0 /\ v5 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)) ->
    fs_agree F F' ->
    ART RT Σ mc -> mem_inv asegs mc -> stk asegs mc lo (usp + -128) -> LIBH mc -> io_ssp mc -> agree_on PF m mc -> wmono asegs m mc ->
    rw_cells asegs mc (usp + -128) [CB 16 j16; C8 (Z_to_bv 64 dwpl)] ->
    rw_cells asegs mc (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    cps asegs (ASTA RT Σ PMc (eq (MS (mkR ra' (Z_to_bv 64 (usp + -128)) gp tp t0' t1' t2' (Z_to_bv 64 (dnf * 4)) (Z_to_bv 64 (datad + 4 * q))
                                          a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (dwpl * 4)) (Z_to_bv 64 2147450880) (Z_to_bv 64 dh) v5 vs6
                                          (Z_to_bv 64 dnf) v8 (Z_to_bv 64 (Z.of_nat k)) s10' s11' t3' t4' t5' t6')
                                     F' (Z_to_bv 64 0xb00e0) fc' None mc (seg_rom asegs)))) QF).
  {
    ropu_restart.
    induction k as [|k IH]; intros q ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' s11' t3' t4' t5' t6' v5 vs6 v8 F' fc' mc j16
      HK1 KB Q0 QB DNF1 DNF2 GL FKc ARTc MI ST LH SSP AGF WMc FRlo FRe.
    {
      lia.
    }
    assert (PQ : 0 <= Z.of_nat k * dwpl) by (clear - WPLB; unfold hid in *; apply Z.mul_nonneg_nonneg; lia).
    assert (RNG : datad <= datad + 4 * q /\ datad + 4 * q + dnf * 4 <= datad + 4 * (dwpl * dpixh) /\ 0 < dnf * 4 <= 20000)
      by (clear - Q0 QB DNF1 DNF2 PQ WPLB; unfold hid in *; rewrite Z.mul_sub_distr_r in QB; lia).
    assert (APD : datad + 4 * q + dnf * 4 <= 65536 \/ SEGTOP_A <= datad + 4 * q) by (clear - RNG CKS; unfold hid, parked, SEGTOP_A in *; lia).
    unfold SEGTOP_A in APD.
    assert (APL : datad + 4 * q + dnf * 4 <= lo) by (clear - RNG CKR LOW; unfold hid in *; lia).
    refresh RT AF.
    unfold shad, SHB in *.
    park_disj.
    walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (dwpl * dpixh))] [0x66814].
    at_call RT AF ltac:(ropu_ivtw datad (4 * (dwpl * dpixh))) ltac:(fun Hx => ropu_pftw PFS Hx).
    hide RNG.
    hide HK1.
    eapply cps_seq.
    {
      pose proof (fk_asan_memset RT FKC) as MS0.
      unfold memset_icontractF in MS0.
      eapply MS0 with (lo := lo) (d := datad + 4 * q) (n := dnf * 4) (c := Z_to_bv 8 0); rt_side idtac;
        lazymatch goal with
        | |- @eq word _ _ => f_equal; clear; lia
        | |- (0 <= _ <= _) => clear - RNG D0 CKR SP0R; unfold hid in *; lia
        | |- (0 <= _ < _) => clear - RNG; unfold hid in *; lia
        | |- checked_dst _ _ _ _ _ _ =>
            unfold checked_dst; rewrite ?unsigned_lit by lia;
            lazymatch goal with A : ART RT Σ ?mx |- context [acc asegs ?mx _ _] =>
              pose proof (af_acc_live RT AF Σ mx datad (4 * (dwpl * dpixh)) A DIN) as (WRD & ACD) end;
            split; [intros _; split; [eapply (acc_sub asegs _ datad (4 * (dwpl * dpixh))); [exact ACD| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia]
                                     | left; exists datad, (4 * (dwpl * dpixh)); split; [solve [in_live_tac]| clear - RNG; unfold hid in *; lia]]|];
            split; [intros j Hj; right; right; left; exists datad, (4 * (dwpl * dpixh)); split; [solve [in_live_tac]| clear - RNG Hj; unfold hid in *; lia]|];
            eapply wr_at_sub; [exact WRD| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia| clear - RNG; unfold hid in *; lia]
        end.
    }
    after_call RT AF.
    fold_ag ltac:(fun Hx => destruct Hx as [HxA HxO]; cbn [outside] in HxO; split;
                  [apply (aclient_mono _ _ usp _ _ _ _ HxA); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]| clear - HxO RNG; unfold hid in *; lia]).
    refresh RT AF.
    unfold shad, SHB in *.
    park_disj.
    walk_to AF MST [(usp - 128, usp); (datad, datad + 4 * (dwpl * dpixh))] [0xb00dc].
    rewrite (bv_swrap_small 32 (Z.of_nat (S k) + -1)) by (change (bv_half_modulus 32) with (2^31); clear - KB; lia).
    replace (Z.of_nat (S k) + -1) with (Z.of_nat k) by (clear; lia).
    replace (datad + 4 * q + dwpl * 4) with (datad + 4 * (q + dwpl)) by (clear; lia).
    lstep.
    destruct k as [|k].
    {
      brT.
      cps_stop.
      art_now RT AF ltac:(ropu_ivtw datad (4 * (dwpl * dpixh))).
      lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ => agf_munch AGFx MUx ltac:(fun Hx => ropu_pftw PFS Hx) end.
      eapply AFTER2C; try eassumption; try reflexivity; ropu_fk.
    }
    {
      brF.
      cps_stop.
      art_now RT AF ltac:(ropu_ivtw datad (4 * (dwpl * dpixh))).
      lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ => agf_munch AGFx MUx ltac:(fun Hx => ropu_pftw PFS Hx) end.
      eapply (IH (q + dwpl)); try eassumption; try reflexivity;
        first [ ropu_fk | clear - Q0 QB WPLB KB; unfold hid in *; lia ].
    }
  }
  (* Up to the first-word rows at 0xafd5c: the masks, the full-word count, the last-word flag. *)
  lstep.
  lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
    eapply (evt_cut asegs (fun ms' => exists (v5 v6 v7 v9 v14 v15 v21 v22 v23 v24 : word),
      ms' = MS (mkR ra (Z_to_bv 64 (usp + -128)) gp tp v5 v6 v7 s0 v9 (Z_to_bv 64 (datad + fw * 4 + dy * dwpl * 4)) v14 (Z_to_bv 64 (dwpl * 4))
                    (Z_to_bv 64 (datad + dy * dwpl * 4 + fw * 4)) (Z_to_bv 64 dh) v15 (Z_to_bv 64 (dy * dwpl * 4)) (Z_to_bv 64 (fw * 4)) s2 (Z_to_bv 64 2147450880) (Z_to_bv 64 dh)
                    v21 v22 v23 v24 s9 s10 s11 (Z_to_bv 64 dwpl) t4 t5 t6)
               F0 (Z_to_bv 64 0xafd5c) fc0 None mm (seg_rom asegs)
      /\ (v15 = Z_to_bv 64 1 \/ (v15 = Z_to_bv 64 0 /\ v23 = Z_to_bv 64 dnf /\ v9 = Z_to_bv 64 pfull /\ 32 <= dw * 8 - (32 - xb)))
      /\ (v24 = Z_to_bv 64 1 \/ (v24 = Z_to_bv 64 0 /\ v21 = Z_to_bv 64 (pfull + dnf * 4) /\ dlw <> 0 /\ 32 - xb <= dw * 8)))) end.
  {
    destruct (Z.ltb_spec (dw * 8) (32 - xb)) as [DP|NDP].
    {
      (* The first word is the only word of each row. *)
      exfalso.
      clear - DP DW0 XBV.
      unfold hid in *.
      lia.
    }
    {
      brT.
      ropu_nwalk [0xafb6c] BD.
      change 31 with (Z.ones 5).
      rewrite (Z.land_ones (dw * 8 + dx * 8) 5) by (clear - BD; unfold hid in *; lia).
      change (2^5) with 32.
      fold dlw.
      rewrite !(ropu_srliw5_small (dw * 8 - (32 - xb))) by (clear - BD NDP XBN; unfold hid in *; lia).
      fold dnf.
      fold pfull.
      lstep.
      destruct (Z.ltb_spec (dw * 8 - (32 - xb)) 32) as [NOFULL|FULL]; cbn [Z.b2z].
      {
        (* No full word: the first word and, when dlw <> 0, a last word. *)
        destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
        {
          rewrite DLW0.
          brT.
          ropu_nwalk [0xafd5c] BD.
          apply evt_done; do 10 eexists; split; [reflexivity|]; split; left; reflexivity.
        }
        {
          brF.
          ropu_nwalk [0xafb94] BD.
          lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
            destruct (ropu_lmask_bytes mm MIx) as (rbs & RB & RBL);
            destruct (bytes_at_read4w mm 0x28d20 rbs (dlw * 4) RB ltac:(clear - DLWR; unfold hid in *; lia) ltac:(rewrite RBL; clear - DLWR; unfold hid in *; lia)) as (lm & RM) end.
          lstep.
          clear RM RB RBL rbs.
          ropu_nwalk [0xafd5c] BD.
          apply evt_done; do 10 eexists; split; [reflexivity|];
            split; [left; reflexivity| right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
        }
      }
      {
        (* Full words: their count and their first address, then the last-word flag. *)
        change ((0 + -1) mod 18446744073709551616) with 18446744073709551615.
        rewrite ?(Z.mod_small pfull) by (clear - PFR0 PFR2; lia).
        rewrite (land_ones64 pfull) by (clear - PFR0 PFR2; lia).
        destruct (Z.eq_dec dlw 0) as [DLW0|DLWN].
        {
          rewrite DLW0.
          brT.
          ropu_nwalk [0xafd5c] BD.
          apply evt_done; do 10 eexists; split; [reflexivity|];
            split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]| left; reflexivity].
        }
        {
          brF.
          ropu_nwalk [0xafb94] BD.
          lazymatch goal with MIx : mem_inv asegs ?mm |- evt _ _ (MS ?R _ _ _ _ ?mm _) =>
            destruct (ropu_lmask_bytes mm MIx) as (rbs & RB & RBL);
            destruct (bytes_at_read4w mm 0x28d20 rbs (dlw * 4) RB ltac:(clear - DLWR; unfold hid in *; lia) ltac:(rewrite RBL; clear - DLWR; unfold hid in *; lia)) as (lm & RM) end.
          lstep.
          clear RM RB RBL rbs.
          ropu_nwalk [0xafd5c] BD.
          apply evt_done; do 10 eexists; split; [reflexivity|];
            split; [right; split; [reflexivity| split; [reflexivity| split; [reflexivity| exact FULL]]]
                   | right; split; [reflexivity| split; [reflexivity| split; [exact DLWN| exact NDP]]]].
        }
      }
    }
  }
  intros ms' (v5 & v6 & v7 & v9 & v14 & v15 & v21 & v22 & v23 & v24 & -> & GC & GL).
  (* The first-word rows. *)
  lazymatch goal with A : ART RT Σ ?mx, WMx : wmono asegs ?mx ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (wr_at_transport asegs mx mm datad (4 * (dwpl * dpixh)) (proj1 (af_acc_live RT AF Σ mx datad (4 * (dwpl * dpixh)) A DIN)) WMx) as WRD end.
  regfix (Z_to_bv 5 10) (datad + 4 * (dy * dwpl + fw) + 4 * (dwpl * 0)).
  regfix (Z_to_bv 5 13) (datad + 4 * (dy * dwpl + fw) + 4 * (dwpl * 0)).
  regfix (Z_to_bv 5 14) (dh - 0).
  eapply evt_cut.
  {
    eapply (uf_rows (Z.to_nat dh) 0) with (DR := datad) (dn := 4 * (dwpl * dpixh)) (P := datad + 4 * (dy * dwpl + fw)) (dh := dh) (dwpl := dwpl);
      ropu_rows_side pfull ltac:(ropu_rowfit dwpl dpixh dy).
  }
  intros ms' PO.
  unfold uf_exit in PO.
  destruct PO as (x1 & x2 & x3 & x4 & x5 & m' & -> & MU' & WM' & MI').
  loop_art RT AF Σ m' lo MU' ltac:(ropu_ivtw datad (4 * (dwpl * dpixh))).
  lazymatch type of MU' with munch _ ?mm m' =>
    loop_transport mm m' MU' ltac:(fun Hx => clear - Hx CKR CKS CKH LOW LOR SPT SPB STa USP SP0R SP0W; unfold parked in *; lia) end.
  clear MU' WM'.
  ropu_nwalk [0xafe84] BD.
  lstep.
  destruct GC as [V15|(V15 & V23 & V9 & FULL)].
  {
    (* No full words. *)
    subst v15.
    brF.
    cps_stop.
    lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ => agf_munch AGFx MUx ltac:(fun Hx => ropu_pftw PFS Hx) end.
    split_at FR 2%nat FRe.
    eapply AFTER2C; try eassumption; try reflexivity; ropu_fk.
  }
  (* The full-word rows, then the last word. *)
  subst v15 v23 v9.
  brT.
  ropu_nwalk [0xb00e0] BD.
  cps_stop.
  lazymatch goal with AGFx : agree_on PF m ?mx, MUx : munch _ ?mx _ |- _ => agf_munch AGFx MUx ltac:(fun Hx => ropu_pftw PFS Hx) end.
  split_at FR 2%nat FRe.
  replace pfull with (datad + 4 * (dy * dwpl + fw + 1)) at 1 by (unfold pfull; clear; lia).
  pose proof (MLOOPC (Z.to_nat dh) (dy * dwpl + fw + 1)) as ML.
  rewrite Z2Nat.id in ML by (clear - BD; unfold hid in *; lia).
  eapply ML; try eassumption; try reflexivity;
    first [ ropu_fk
          | clear - BD; unfold hid in *; lia
          | clear - BD2 FWD; unfold hid in *; lia
          | pose proof (GF2 ltac:(clear - FULL; lia)) as GF2'; clear - GF2' BD2 BD BD3; unfold hid in *; rewrite Z.mul_sub_distr_r; lia
          | clear - FULL; unfold dnf; apply Z.div_le_lower_bound; lia
          | pose proof (GF2b ltac:(clear - FULL; lia)) as GF2'; clear - GF2'; lia ].
Qed.
End ROPUG.
