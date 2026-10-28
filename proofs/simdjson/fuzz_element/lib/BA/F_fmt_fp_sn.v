(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import SFModel Arr ITree Nodes Decode.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim Monad PrintfModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import SoftFloat SoftFloatProps FmtFp FmtFpDig FmtFpTail FmtFp_facts FmtFp_facts2 FmtFp6 FmtFpNf.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Printf_mlib.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import FX_lib F_memset F_memcpy F_fwritex.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Fe_icalls F_fmt_fp_pre4 Fe_printf_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_m2s I_consts. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_achk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import F_fmt_fp F_fmt_fp_nf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac lia_nd := first [ (repeat match goal with H : _ \/ _ |- _ => clear H end); lia | lia ].
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Lemma zb_length : forall l, length (zb l) = length l.
Proof. intros. unfold zb. apply length_map. Qed.
Lemma zb_app : forall a b, zb (a ++ b) = zb a ++ zb b.
Proof. intros. unfold zb. apply map_app. Qed.

Lemma pad_id_sn : forall o c w l fl, (w <= l)%Z -> pad o c w l fl = Some o.
Proof. intros. unfold pad. rewrite (proj2 (Z.leb_le w l)) by lia. rewrite Bool.orb_true_r. reflexivity. Qed.
Lemma fmt_fp_nf_fin : forall o d w p fl t, dfin d -> fmt_fp_nf o (f128_of_d d) w p fl t = None.
Proof.
  intros o d w p fl t Hfin. destruct (prologue_ok_finite d Hfin) as [nz [fr [e0 [N0 (C1 & _)]]]].
  unfold fmt_fp_nf, nf_sign. unfold strip_sign in C1.
  destruct (negb (signbitl (f128_of_d d) =? 0)); [| destruct (negb (Z.land fl MARK_POS =? 0)); [| destruct (negb (Z.land fl PAD_POS =? 0))]];
    rewrite (proj2 (Z.leb_gt _ _)) by lia; reflexivity.
Qed.

Lemma fmt_fp_nf_inf : forall o d w p t, d_exp d = 2047 -> w <= 3 ->
  fmt_fp_nf o (f128_of_d d) w p 0 t =
    Some (o ++ (if negb (signbitl (f128_of_d d) =? 0) then [CHR_minus] else []) ++ nf_str (strip_sign (f128_of_d d)) t,
          3 + (if negb (signbitl (f128_of_d d) =? 0) then 1 else 0)).
Proof.
  intros o d w p t HE Hw. pose proof (fpclassifyl_infnan d HE) as C. unfold strip_sign in C |- *.
  unfold fmt_fp_nf, nf_sign.
  replace (negb (Z.land 0 MARK_POS =? 0)) with false by reflexivity. replace (negb (Z.land 0 PAD_POS =? 0)) with false by reflexivity.
  destruct (negb (signbitl (f128_of_d d) =? 0)); rewrite (proj2 (Z.leb_le _ _) C);
    rewrite !pad_id_sn by lia; cbv beta iota zeta; rewrite ?pad_id_sn by lia; cbv beta iota zeta;
    rewrite Z.max_r by lia; unfold out, zsub, PREFIX_STR, CHR_minus; cbn [Z.to_nat firstn skipn app Pos.to_nat]; rewrite <- ?app_assoc; reflexivity.
Qed.

Lemma yn_widened_infnan : forall d, d_exp d = 2047 ->
  let y := f128_of_d d in
  (Z.land (Z.shiftr (hi64 y) 48) 0x7fff <> 0 \/ f128_le y F128_ZERO = 0) /\
  (Z.land (Z.shiftr (hi64 (Z.lxor y F128_SIGNBIT)) 48) 0x7fff <> 0 \/ f128_le (Z.lxor y F128_SIGNBIT) F128_ZERO = 0).
Proof.
  intros d HE. cbv zeta. pose proof (d_fields d) as (Hs & He & Hf & Hd).
  destruct (f128_of_d_shape d) as (SHI & _ & _). rewrite (SHI HE).
  assert (XS : forall s E T, packed s E T -> Z.lxor (f128_pack s E T) F128_SIGNBIT = f128_pack (1 - s) E T).
  { intros s E T [A B0 C]. unfold F128_SIGNBIT, f128_pack. change 0x80000000000000000000000000000000 with (2^127).
    assert (D : s = 0 \/ s = 1) by lia. destruct D as [-> | ->].
    - rewrite lxor_bit_clear; [lia|lia|lia|]. rewrite Z.div_small; [reflexivity| lia].
    - rewrite lxor_bit_set; [lia|lia|lia|]. replace ((1 * 2 ^ 127 + E * 2 ^ 112 + T) / 2 ^ 127) with 1; [reflexivity|].
      apply Z.div_unique with (r := E * 2^112 + T); lia. }
  assert (PK : packed (d_sign d) 32767 (d_frac d * 2^60)) by (constructor; lia).
  assert (PK' : packed (1 - d_sign d) 32767 (d_frac d * 2^60)) by (constructor; lia).
  rewrite (XS _ _ _ PK). rewrite !f128_pack_hi by assumption.
  pose proof (T_split (d_frac d * 2^60) ltac:(lia)) as (A & B0 & C).
  split; left; rewrite hiword_expfield by lia; lia.
Qed.

Definition noxc (c : Z) : Prop := 0 <= c < 256 /\ Z.lor c 32 <> 120.
Lemma gch_noxc : forall c, gch c -> noxc c.
Proof.
  intros c H.
  assert (E : In c [43; 45; 46; 48; 49; 50; 51; 52; 53; 54; 55; 56; 57; 69; 101]) by (unfold gch in H; cbn; lia).
  cbn in E. repeat (destruct E as [<-|E]; [split; [lia | cbv; discriminate]|]). destruct E.
Qed.

Theorem fmt_fp_total_g6 : forall d, exists txt n,
  fmt_fp_total [] (f128_of_d d) 0 6 0 CHR_g = Some (txt, n) /\ zlength txt = n /\ 1 <= n <= 14 /\ Forall noxc txt.
Proof.
  intros d. destruct (Z.eq_dec (d_exp d) 2047) as [HE|Hfin].
  - exists ((if negb (signbitl (f128_of_d d) =? 0) then [CHR_minus] else []) ++ nf_str (strip_sign (f128_of_d d)) CHR_g).
    eexists. split; [| split; [reflexivity | split]].
    + apply fmt_fp_total_nf. rewrite (fmt_fp_nf_inf [] d 0 6 CHR_g HE ltac:(lia)). cbn [app].
      f_equal. f_equal. unfold zlength. rewrite length_app, nf_str_length. destruct (negb _); reflexivity.
    + unfold zlength. rewrite length_app, nf_str_length. destruct (negb (signbitl _ =? 0)); cbn [length Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; lia.
    + apply Forall_app. split.
      * destruct (negb (signbitl _ =? 0)); [| apply Forall_nil]. apply Forall_cons; [| apply Forall_nil]. unfold noxc, CHR_minus. split; [lia | cbv; discriminate].
      * unfold nf_str. change (Z.land CHR_g 32 =? 0) with false. cbv beta iota.
        destruct (negb (f128_le _ _ =? 0)); repeat (apply Forall_cons; [unfold noxc; split; [lia | cbv; discriminate]|]); apply Forall_nil.
  - destruct (fmt_fp_g_total6 d 0 Hfin (or_introl eq_refl)) as (txt & pl & l' & HF & HL & HG & HPL & HL').
    exists txt, (pl + l')%Z. split; [apply fmt_fp_total_of_finite; exact HF|]. split; [exact HL|]. split; [lia|].
    eapply Forall_impl; [| exact HG]. apply gch_noxc.
Qed.

Section SnFp.
  Variables (Fp : Z) (fl0 : byte) (j1 j2 : list byte) (lbfw : word) (frest : list cell) (B TOP : Z).
  Let SINK := SINK_sn Fp fl0 j1 j2 lbfw frest B TOP.

  Hypothesis RIP : rip_stmt.
  Hypothesis FXI : ifrexpl_stmt.

  Lemma sn_fpcall_fin : forall d w p, dfin d -> 1 <= p <= 26 ->
    fpcall_stmt Fp B 80 SINK (TOPOK_sn TOP) OUTFP_sn (f128_of_d d, w, p, 0, CHR_g).
  Proof.
    intros d w p Hfin Hp. unfold fpcall_stmt.
    intros until canary. intros HS Hy Ha0 Ha3 Ha4 Ha5 Ha6 Ha7 Hw Hp' Hfl Ht Hta ST LO GLO SPHI TQ SSP MI FRM D1 D2 HSH IC CKS CKB ROD IFX. rename st into o.
    destruct HS as (junk & WF & FR & FRL & LEN & SEPB & T1 & T2). unfold TOPOK_sn in TQ. unfold Fe_printf_iface.FMT_FP_DEPTH, F_fmt_fp.FMT_FP_DEPTH, GLOBALS_TOP, SN_CAP in *.
    pose proof (zb_length o) as LZo. unfold zlength in LEN.
    pose proof WF as WF'. destruct WF' as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size FILE_cells csize Nat.add] in FB. rewrite LZo in *.
    assert (EFp : bv_unsigned a0 = Fp) by (subst a0; apply unsigned_lit; lia).
    unfold OUTFP_sn. apply implM_get_l. unfold fmt_fp_total. rewrite (fmt_fp_nf_fin o d w p 0 CHR_g Hfin).
    destruct (fmt_fp o (f128_of_d d) w p 0 CHR_g) as [[o1 ret]|] eqn:HM; [| apply implM_unr].
    unfold zlength, SN_CAP.
    destruct (Z.leb_spec0 (Z.of_nat (length o)) (Z.of_nat (length o1))) as [GROW|]; [| cbn [andb]; apply implM_unr].
    destruct (Z.leb_spec0 (Z.of_nat (length o1)) 80) as [FIT|]; [| cbn [andb]; apply implM_unr].
    cbn [andb]. apply implM_put_l. apply implM_ret.
    destruct (stk_split _ _ _ (bv_unsigned sp - 6944) _ ST ltac:(lia)) as [ST1 ST2].
    pose proof (fmt_fp_facts_gen d p Hfin Hp) as FF.
    eapply evt_mono.
    { eapply (fmt_fp_spec RIP FXI ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                fl0 j1 j2 lbfw B junk canary w p 0 CHR_g o o1 ret); rewrite ?EFp, ?LZo, <- ?Hy; unfold F_fmt_fp.FMT_FP_DEPTH.
      - exact HM. - exact FF. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - unfold CHR_g; lia. - exact Hta.
      - lia. - apply Nat2Z.inj_lt. lia.
      - exact ST2. - exact MI. - exact FRM. - exact WF. - exact SSP.
      - exact Ha3. - exact Ha4. - exact Ha5. - exact Ha6. - exact Ha7.
      - lia. - exact IC. - intros q' n' H1 H2; apply CKS; lia. - replace (Z.of_nat (length o) + Z.of_nat (length junk))%Z with 80%Z by lia; exact CKB. - exact ROD. - exact IFX. }
    cbv beta. intros ms' P. unfold F_fmt_fp.fmt_fp_post, F_fmt_fp.FMT_FP_DEPTH in P. rewrite ?LZo, ?EFp in P. change F_fmt_fp_lib.zb with zb in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & WF2 & SSP' & FOK).
    unfold fpcall_post, SR. eexists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia_nd. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FOK|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split. { exists (skipn (length o1 - length o) junk). split; [exact WF2|].
             split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from]; lia]. }
             split; [exact FRL|]. unfold zlength, SN_CAP. rewrite length_skipn. split; [lia|]. split; [lia|]. split; assumption. }
    exact SSP'.
  Qed.

  Lemma sn_fpcall_nf : forall d w p, d_exp d = 2047 -> 0 <= w <= 1 -> 1 <= p <= 26 ->
    fpcall_stmt Fp B 80 SINK (TOPOK_sn TOP) OUTFP_sn (f128_of_d d, w, p, 0, CHR_g).
  Proof.
    intros d w p HE Hw0 Hp. unfold fpcall_stmt.
    intros until canary. intros HS Hy Ha0 Ha3 Ha4 Ha5 Ha6 Ha7 Hw Hp' Hfl Ht Hta ST LO GLO SPHI TQ SSP MI FRM D1 D2 HSH IC CKS CKB ROD IFX. rename st into o.
    destruct HS as (junk & WF & FR & FRL & LEN & SEPB & T1 & T2). unfold TOPOK_sn in TQ. unfold Fe_printf_iface.FMT_FP_DEPTH, F_fmt_fp.FMT_FP_DEPTH, GLOBALS_TOP, SN_CAP in *.
    pose proof (zb_length o) as LZo. unfold zlength in LEN.
    pose proof WF as WF'. destruct WF' as (FC & BUF & FL & LBF & Bpos & Bhi & SEPfb).
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size FILE_cells csize Nat.add] in FB. rewrite LZo in *.
    assert (EFp : bv_unsigned a0 = Fp) by (subst a0; apply unsigned_lit; lia).
    unfold OUTFP_sn. apply implM_get_l. unfold fmt_fp_total.
    destruct (fmt_fp_nf o (f128_of_d d) w p 0 CHR_g) as [[o1 ret]|] eqn:HM; [| exfalso; rewrite (fmt_fp_nf_inf o d w p CHR_g HE ltac:(lia)) in HM; discriminate HM].
    unfold zlength, SN_CAP.
    destruct (Z.leb_spec0 (Z.of_nat (length o)) (Z.of_nat (length o1))) as [GROW|]; [| cbn [andb]; apply implM_unr].
    destruct (Z.leb_spec0 (Z.of_nat (length o1)) 80) as [FIT|]; [| cbn [andb]; apply implM_unr].
    cbn [andb]. apply implM_put_l. apply implM_ret.
    destruct (stk_split _ _ _ (bv_unsigned sp - 6944) _ ST ltac:(lia)) as [ST1 ST2].
    pose proof (yn_widened_infnan d HE) as [YN0 YN1].
    eapply evt_mono.
    { eapply (fmt_fp_nf_spec RIP FXI ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                fl0 j1 j2 lbfw B junk canary w p 0 CHR_g o o1 ret); rewrite ?EFp, ?LZo, <- ?Hy; unfold F_fmt_fp.FMT_FP_DEPTH.
      - exact HM. - exact YN0. - exact YN1. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - lia. - unfold CHR_g; lia. - exact Hta.
      - lia. - apply Nat2Z.inj_lt. lia.
      - exact ST2. - exact MI. - exact FRM. - exact WF. - exact SSP.
      - exact Ha3. - exact Ha4. - exact Ha5. - exact Ha6. - exact Ha7.
      - lia. - exact IC. - intros q' n' H1 H2; apply CKS; lia. - replace (Z.of_nat (length o) + Z.of_nat (length junk))%Z with 80%Z by lia; exact CKB. - exact ROD. - exact IFX. }
    cbv beta. intros ms' P. unfold F_fmt_fp.fmt_fp_post, F_fmt_fp.FMT_FP_DEPTH in P. rewrite ?LZo, ?EFp in P. change F_fmt_fp_lib.zb with zb in P.
    destruct P as (x5 & x6 & x7 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & x28 & x29 & x30 & x31 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & ST' & WF2 & SSP' & FOK).
    unfold fpcall_post, SR. eexists x5, x6, x7, b1, b2, b3, b4, b5, b6, b7, x28, x29, x30, x31, Ft, fc', m'.
    split; [reflexivity|].
    split. { eapply munch_weaken; [|exact MU]. unfold sub_fp; cbn [outside]; intros; lia_nd. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact FRM'|]. split; [exact FOK|].
    split. { eapply stk_merge; [ eapply stk_transport_disjoint; [exact ST1 | exact MU | exact WM | cbn [disjoint_from]; lia] | exact ST' | lia ]. }
    split. { exists (skipn (length o1 - length o) junk). split; [exact WF2|].
             split. { eapply rw_cells_transport; [exact FR | exact MU | exact WM | cbn [disjoint_from]; lia]. }
             split; [exact FRL|]. unfold zlength, SN_CAP. rewrite length_skipn. split; [lia|]. split; [lia|]. split; assumption. }
    exact SSP'.
  Qed.

  Theorem sn_fpcall : forall d w p, 0 <= w <= 1 -> 1 <= p <= 26 ->
    fpcall_stmt Fp B 80 SINK (TOPOK_sn TOP) OUTFP_sn (f128_of_d d, w, p, 0, CHR_g).
  Proof.
    intros d w p Hw Hp. destruct (Z.eq_dec (d_exp d) 2047) as [HE|Hfin].
    - apply sn_fpcall_nf; assumption.
    - apply sn_fpcall_fin; assumption.
  Qed.
End SnFp.
