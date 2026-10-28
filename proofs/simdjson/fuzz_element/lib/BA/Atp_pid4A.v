(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_setcapA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_setmd. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_deldtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_pdtorA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_hkit3A. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage2_iface Sj_h_parsew. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_parseA Atp_createA Atp_activewA Atp_activeA Atp_pidwA Atp_pidw2A Atp_pidw3A Atp_hkit4A Atp_hkit5A Atp_hkit6A Atp_pid1A Atp_pidiA Atp_pid3A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma mcost_mono : forall a b, 0 <= a <= b -> mcost a <= mcost b.
Proof. intros a b H. unfold mcost, DCOST. destruct (Z.leb_spec a 64512), (Z.leb_spec b 64512); lia. Qed.

Lemma s2a_cost_mono : forall a b, 0 <= a <= b -> S2A_COST a <= S2A_COST b.
Proof. intros a b H. unfold S2A_COST, Sj_num_iface.NUMA_CREDIT. pose proof (mcost_mono (a + 64) (b + 64) ltac:(lia)). lia. Qed.

Section Pid4.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.
Hypothesis MCMP : memcmp_icontract_f RT.
Hypothesis PARSE : parse_cps RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Local Ltac nomod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac std_lia__ := lia.
Local Ltac lia := nomod; std_lia__.
Local Ltac ul := nomod; unfold PID_STACK, PARSE_STACK, S2A_STACK, Sj_num_iface.NUMA_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; std_lia__.

Theorem pid_main : forall (Σ2 : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (m2 : mem) (lo RES P d cap impl idx oc ia tape sbuf : Z) (bs : list byte)
    (L : list (Z * Z)) (jr j p1 p17 p57 p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc -> Z.of_nat (length bs) <= 1048512 -> cap = Z.max (Z.of_nat (length bs)) 32 ->
  0 < d -> bytes_at asegs m2 d (padded_bytes (map bv_unsigned bs)) ->
  In (d, Z.of_nat (length bs) + 64) L -> d mod 16 = 0 ->
  ART RT Σ2 m2 -> mem_inv asegs m2 -> stk asegs m2 lo (bv_unsigned sp + -112) ->
  rw_cells asegs m2 (bv_unsigned sp + -112) (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells asegs m2 P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                 (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  fobj RT Σ2 m2 P 80 ->
  rw_cells asegs m2 impl (impl16 (Z_to_bv 64 0x164ad0) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                 (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  rw_cells asegs m2 RES [CB 24 jr] -> lib1 m2 ->
  rt_live RT Σ2 = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: L ->
  lposx L ->
  impl mod 16 = 0 -> idx mod 16 = 0 -> oc mod 16 = 0 -> ia mod 16 = 0 -> tape mod 16 = 0 -> sbuf mod 16 = 0 ->
  (length (rt_frames RT Σ2) + S2A_FRAMES <= FRAMES_MAX)%nat ->
  S2A_COST (Z.of_nat (length bs)) <= rt_credit RT Σ2 -> Z.of_nat (length (rt_live RT Σ2)) < LIVE_MAX ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP ->
  rt_sp0 RT Σ2 - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc' ->
  cps_f (ASTA RT Σ2 PMc (eq (MS (mkR (Z_to_bv 64 0xb5a5c) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 RES) s1
                                     (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                     (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap)
                                     (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6)
                                F' (Z_to_bv 64 0xb5a5c) fc' None m2 (seg_rom asegs))))
        (pid_post RT Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo RES P L impl idx oc ia tape sbuf cap (S2A_COST (Z.of_nat (length bs))) m2).
Proof using AF MSET MCMP PARSE AFV.
  intros Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m2
    lo RES P d cap impl idx oc ia tape sbuf bs L jr j p1 p17 p57 p12 p28 p50
    FDO MST LEN ECAP D0 BUFB2 INDL D16 ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LPOS IM16 IX16 OC16 IA16 TP16 SB16 FRB CRB LVB RLO RHI LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ2 m2 ART2) as SP0R. pose proof (af_sp0_win RT AF Σ2 m2 ART2) as SP0W.
  set (usp := bv_unsigned sp) in *. set (len := Z.of_nat (length bs)) in *.
  assert (LEN0 : 0 <= len) by (subst len; lia).
  assert (IND : In (d, len + 64) (rt_live RT Σ2)) by (rewrite LV2; do 6 right; exact INDL).
  pose proof (af_live_range RT AF Σ2 m2 d _ ART2 IND) as (_ & DP1 & _).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -112) mod 16 = 0) by (replace (usp + -112) with (usp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).

  assert (TAILK : forall (mX : mem) (cX : config) (rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) FX fcX (BUF bl : Z) (bsz : list Z),
            ART RT Σ2 mX -> mem_inv asegs mX -> stk asegs mX lo (usp + -112) ->
            rw_cells asegs mX (usp + -112) (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
            rw_cells asegs mX P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                           (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
            fobj RT Σ2 mX P 80 ->
            rw_cells asegs mX impl (impl16 (Z_to_bv 64 0x164ad0) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                           (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
            rw_cells asegs mX RES [CB 24 jr] -> lib1 mX ->
            (forall a : word, aclient L (rt_frames RT Σ2) usp (bv_unsigned a) -> outside (pid_X P RES) (bv_unsigned a) -> mX a = m2 a) ->
            bytes_at asegs mX BUF (padded_bytes bsz) -> bytes_ok bsz -> blen bsz = bl -> bl <= len -> d <= BUF -> BUF + bl = d + len -> frm0 fcX ->
            ASTA RT Σ2 PMc (eq (MS (PIREGT rax (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) t0x t1x t2x RES P BUF bl a0x a1x a2x a3x a4x a5x a6x a7x
                                           s1 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3x t4x t5x t6x)
                                   FX (Z_to_bv 64 0xb585c) fcX None mX (seg_rom asegs))) cX ->
            realizes asegs cX T).
  { intros mX cX rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x FX fcX BUF bl bsz ARTX MIX STX FRX PCX FOBJX ICX RCX LIBX CHX BUFBX BOKX EBL BLE CBUF EBUF FRMX HcX.
    subst bl.
    apply (pid_tail RT AF MSET PARSE AFV Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rax t0x t1x t2x a0x a1x a2x a3x a4x a5x a6x a7x s1 t3x t4x t5x t6x
             FX fcX mX lo RES P len cap impl idx oc ia tape sbuf d BUF bsz L j jr p1 p17 p57 p12 p28 p50 FDO MST BOKX BLE LEN ECAP CBUF EBUF ARTX MIX STX
             FRX PCX FOBJX ICX RCX LIBX BUFBX LV2 INDL LPOS IM16 IX16 OC16 IA16 TP16 SB16 D16);
      [exact FRB| | exact LVB| exact RLO| exact RHI| exact LOW| exact LOR| exact SPT| exact SPA| exact FRMX
      | split; [exact HcX| apply (cfrm0_of_asta RT Σ2 PMc (eq _) cX HcX); intros ms0 <-; exact FRMX] |].
    - pose proof (s2a_cost_mono (blen bsz) len ltac:(unfold blen in *; lia)). lia.
    - intros c' ((Σ' & Hc' & LV' & FRS' & SP' & CR') & FC'). apply Hk. split; [| exact FC'].
      exists Σ'. split; [| split; [exact LV'| split; [exact FRS'| split; [exact SP'|]]]].
      + eapply ASTA_conseq; [exact Hc'|]. intros ms (v & m' & RS' & AFT' & PRES' & RC' & LIB' & PD'). exists v, m'.
        split; [exact RS'|]. split; [| split; [| split; [exact RC'| split; [exact LIB'| exact PD']]]].
        * exact AFT'.
        * intros a Ha Hout. rewrite (PRES' a Ha Hout). exact (CHX a Ha Hout).
      + pose proof (s2a_cost_mono (blen bsz) len ltac:(unfold blen in *; lia)). lia. }
  destruct (Z_lt_dec len 3) as [L3|L3].
  -
    pose proof (pi_walk4s RES P d len cap (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m2 ltac:(lia)) as W4.
    lazymatch type of W4 with evt asegs _ ?X =>
      assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
    clear W4.
    apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ2 PMc _ _ MST W4') Hc). clear W4'. intros c3 Hc3.
    exact (TAILK m2 c3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' d len (map bv_unsigned bs) ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 ltac:(intros a _ _; reflexivity)
             BUFB2 (bytes_ok_unsigned bs) (blen_unsigned bs) ltac:(lia) ltac:(lia) ltac:(lia) FRM Hc3).
  -
    pose proof (pi_walk4m RES P d len cap (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m2 ltac:(lia)) as W4.
    lazymatch type of W4 with evt asegs _ ?X =>
      assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
    clear W4.
    apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ2 PMc _ _ MST W4') Hc). clear W4'. intros c3 Hc3.
    assert (LF3 : length (firstn 3 (padded_bytes (map bv_unsigned bs))) = 3%nat).
    { apply firstn_length_le. pose proof (padded_bytes_blen (map bv_unsigned bs)). rewrite blen_unsigned in H. lia. }
    assert (CPF : bytes_at asegs m2 d (firstn 3 (padded_bytes (map bv_unsigned bs)))).
    { pose proof BUFB2 as X. rewrite <- (firstn_skipn 3 (padded_bytes (map bv_unsigned bs))) in X. apply bytes_at_app in X. exact (proj1 X). }
    destruct (af_acc_live RT AF Σ2 m2 d _ ART2 IND) as (_ & ACC2).
    apply (MCMP Σ2 PMc (Z_to_bv 64 0xb5850) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 RES) s1
             (Z_to_bv 64 d) (Z_to_bv 64 0x237e0) (Z_to_bv 64 3) a3 a4 a5 a6 a7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F' fc' m2 d BOM_LIT (firstn 3 (padded_bytes (map bv_unsigned bs))) BOM_BYTES lo FDO MST);
      try reflexivity; try assumption;
      [.. | split; [exact Hc3| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c3 Hc3); intros ms0 <-; exact FRM] |].
    + rewrite LF3. reflexivity.
    + rewrite LF3. reflexivity.
    + ul.
    + unfold BOM_LIT. lia.
    + rewrite LF3. lia.
    + rewrite LF3. lia.
    + exact (bom_at m2 MI2).
    + rewrite LF3. change (Z.of_nat 3) with 3. unfold checked_src. rewrite EU2. split; [| left; ul].
      intros _. split; [exact (acc_sub asegs m2 d (len + 64) d 3 ACC2 ltac:(lia) ltac:(lia))|]. left. exists d, (len + 64). split; [exact IND| lia].
    + rewrite LF3. change (Z.of_nat 3) with 3. unfold checked_src. rewrite EU2. split; [| left; unfold BOM_LIT; ul].
      intros _. split.
      * apply (acc_sub asegs m2 BOM_LIT 4 BOM_LIT 3); [| lia| lia]. apply (acc_lit RT AF Σ2 m2 _ _ ART2). unfold ACC_LITS, BOM_LIT. repeat (first [left; reflexivity | right]).
      * right; right; right. unfold BOM_LIT, SEGTOP_A. lia.
    + unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [exact LOW|]. split; [ul|]. split; [ul| exact SPA2].
    + intros c11 ((r & _ & Hc11) & FC11). unfold icpt_post in Hc11.
      destruct (ASTA_unpack_f RT Σ2 _ _ c11 Hc11 FC11) as (ms11 & (m8 & RS11 & (ART8 & MI8 & WM8 & ST8) & PRES8 & _) & FRM8 & Hc11'). clear Hc11.
      destruct RS11 as (y0 & y1 & y2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F8 & fc8 & ->).
      cbn [ms_fcsr] in FRM8. rewrite EU2 in ST8, PRES8. rewrite (ret_pc_even 0xb5850) in Hc11' by (clear; lia).

      pose proof FOBJ2 as (P8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
      assert (INM : In (impl, 96) (rt_live RT Σ2)) by (rewrite LV2; cbn [In]; tauto).
      assert (AGC : forall a : word, aclient (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -112) (bv_unsigned a) -> m8 a = m2 a).
      { intros a Ha. apply (PRES8 a Ha). clear; lia. }
      assert (FR8 : rw_cells asegs m8 (usp + -112) (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
      { apply (rw_cells_agree_nw asegs m2 m8 _ _ FR2). intros x Hx. unfold pid_frame in Hx. cbn [cells_size csize Nat.add] in Hx. apply AGC. left. ul. }
      assert (PC8 : rw_cells asegs m8 P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                                   (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0))).
      { apply (rw_cells_agree_nw asegs m2 m8 _ _ PC2). intros x Hx. unfold pid_cells in Hx. cbn [cells_size csize Nat.add] in Hx. apply AGC.
        right; right; right; left. exists f, k. split; [exact INF| lia]. }
      assert (IC8 : rw_cells asegs m8 impl (impl16 (Z_to_bv 64 0x164ad0) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                                   (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))).
      { apply (rw_cells_agree_nw asegs m2 m8 _ _ IC2). intros x Hx. unfold impl16 in Hx. cbn [cells_size csize Nat.add] in Hx. apply AGC.
        right; right; left. exists impl, 96. split; [exact INM| lia]. }
      assert (RC8 : rw_cells asegs m8 RES [CB 24 jr]).
      { apply (rw_cells_agree_nw asegs m2 m8 _ _ RC2). intros x Hx. cbn [cells_size csize Nat.add] in Hx. apply AGC. left. ul. }
      assert (LIB8 : lib1 m8).
      { apply (lib1_loc m2 m8 LIB2). intros a Ha. apply AGC. right; left. exact (proj1 (lib_fp_static _ Ha)). }
      assert (FOBJ8 : fobj RT Σ2 m8 P 80).
      { apply (fobj_agree RT AF Σ2 Σ2 m2 m8 P 80 ART2 FOBJ2 eq_refl). intros x Hx. cbv beta in Hx. apply AGC.
        exact (proj1 (fobj_shadow_client RT AF Σ2 m2 P 80 (usp + -112) (bv_unsigned x) ART2 FOBJ2 Hx)). }
      assert (BUFB8 : bytes_at asegs m8 d (padded_bytes (map bv_unsigned bs))).
      { apply (bytes_at_agree asegs m2 m8 _ _ BUFB2). intros x Hx. cbv beta in Hx. rewrite padded_bytes_blen, blen_unsigned in Hx. fold len in Hx.
        apply AGC. right; right; left. exists d, (len + 64). split; [exact IND| lia]. }
      assert (CH8 : forall a : word, aclient L (rt_frames RT Σ2) usp (bv_unsigned a) -> outside (pid_X P RES) (bv_unsigned a) -> m8 a = m2 a).
      { intros a Ha _. apply AGC. apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV2; do 6 right; exact He| auto| lia]. }
      pose proof (pi_walk8c RES P len d cap r (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) y0 y1 y2 s1 k1 k2 k3 k4 k5 k6 k7 y3 y4 y5 y6 F8 fc8 m8
                    ltac:(lia) D0 ltac:(ul)) as W9.
      lazymatch type of W9 with evt asegs _ ?X =>
        assert (W9' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W9) end.
      clear W9.
      apply (cps_realizes asegs _ _ _ c11 (asta_evt_c RT AF Σ2 PMc _ _ MST W9') Hc11'). clear W9'. intros c12 Hc12.
      destruct (ASTA_unpack RT Σ2 _ _ c12 Hc12) as (ms12 & (BUF & bl & CASE & ->) & Hc12'). clear Hc12.
      destruct CASE as [(-> & ->)|(-> & ->)].
      * exact (TAILK m8 c12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 d len (map bv_unsigned bs) ART8 MI8 ST8 FR8 PC8 FOBJ8 IC8 RC8 LIB8 CH8 BUFB8 (bytes_ok_unsigned bs)
                 (blen_unsigned bs) ltac:(lia) ltac:(lia) ltac:(lia) FRM8 Hc12').
      * assert (L3' : (3 <= length bs)%nat) by (subst len; lia).
        assert (EBL : blen (map bv_unsigned (skipn 3 bs)) = len - 3) by (rewrite blen_unsigned, skipn_length; subst len; lia).
        exact (TAILK m8 c12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 (d + 3) (len - 3) (map bv_unsigned (skipn 3 bs)) ART8 MI8 ST8 FR8 PC8 FOBJ8 IC8 RC8 LIB8 CH8
                 (padded_skip3 m8 d bs L3' BUFB8) (bytes_ok_unsigned _) EBL ltac:(lia) ltac:(lia) ltac:(lia) FRM8 Hc12').
Qed.

End Pid4.
