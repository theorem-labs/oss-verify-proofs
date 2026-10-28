(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Lemma stk_store_ok_at : forall segs (m : mem) lo hi x (j : nat) a,
  stk segs m lo hi -> (lo <= x)%Z -> (x + Z.of_nat j <= hi)%Z -> a = wa x -> store_ok segs m a j = true.
Proof.
  intros segs m lo hi x j a (H0 & H1 & H) Hx Hj ->.
  assert (W : wr_at segs m lo (hi - lo)).
  { split; [lia|]. split; [lia|]. intros i Hi. apply (H (lo + i)%Z). lia. }
  replace x with (lo + (x - lo))%Z by lia. apply (wr_at_store_ok segs m lo (hi - lo) (x - lo) j W); lia.
Qed.

Lemma stk_CB : forall segs (m : mem) lo hi, stk segs m lo hi -> (lo <= hi)%Z ->
  exists bs, rw_cells segs m lo [CB (Z.to_nat (hi - lo)) bs].
Proof.
  intros segs m lo hi H Hle.
  destruct (stk_carve segs m lo hi (Z.to_nat (hi - lo)) H ltac:(lia)) as [_ (junk & J)].
  exists junk. replace (hi - Z.of_nat (Z.to_nat (hi - lo)))%Z with lo in J by lia. exact J.
Qed.

Lemma stk_nil : forall segs (m : mem) a, 0 <= a <= 2^64 -> stk segs m a a.
Proof. intros segs m a Ha. split; [lia|]. split; [lia|]. intros x Hx. lia. Qed.

Lemma stk_of_bytes_wmono : forall (m m' : mem) a bs, bytes_at bsegs m' a bs -> stk bsegs m a (a + Z.of_nat (length bs)) ->
  wmono bsegs m m' -> stk bsegs m' a (a + Z.of_nat (length bs)).
Proof.
  intros m m' a bs HB (S0 & S1 & S) WM. split; [lia|]. split; [lia|]. intros x Hx.
  destruct (S x Hx) as [W _]. split; [apply WM; exact W|].
  destruct HB as (_ & _ & HB). specialize (HB (Z.to_nat (x - a)) ltac:(lia)).
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in HB by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:En; [| exfalso; apply nth_error_None in En; lia].
  exists b. exact HB.
Qed.

Ltac pj_solve_store0 :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
    rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff E A in addr_near_cells k cs0 n;
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_store_ok_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac]);
          cbv_concl_beta_iota;
          match goal with
          | |- context [write_to_mem m a ?bs] =>
              replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) bs) by (f_equal; addr_eq_tac)
          end
        end
    | HS : store_ok segs m ?a' n = true |- _ =>
        cbv delta [wa] in HS;
        first [ rewrite HS
              | replace (store_ok segs m a n) with true
                  by (rewrite <- HS; f_equal; word_eq_tac);
                try replace (write_to_mem m a) with (write_to_mem m a')
                  by (f_equal; word_eq_tac) ];
        cbv_concl_beta_iota
    end
  end.

Ltac pj_store_wr :=
  match goal with
  | |- context [store_ok ?segs ?m ?a ?n] =>
      rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1';
      let Ea := addr_expr a in
      match goal with
      | H : stk segs m ?lo ?hi |- _ =>
          rewrite (stk_store_ok_at segs m lo hi Ea n a H ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ltac:(unfold wa; f_equal; lia));
          cbv beta iota
      end
  end.

Ltac pj_store_done :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let Ea := addr_expr a in
      (match goal with
       | H : stk segs m ?lo ?hi |- _ =>
           let n := lazymatch bs with
                    | le8 _ => constr:(8%nat) | le4 _ => constr:(4%nat) | le2 _ => constr:(2%nat) | le1 _ => constr:(1%nat)
                    | Z_to_le_bytes 8 _ => constr:(8%nat) | Z_to_le_bytes 4 _ => constr:(4%nat)
                    | Z_to_le_bytes 2 _ => constr:(2%nat) | Z_to_le_bytes 1 _ => constr:(1%nat)
                    | [_] => constr:(1%nat) end in
           let HS := fresh "HSOK" in
           assert (HS : store_ok segs m a n = true)
             by (apply (stk_store_ok_at segs m lo hi Ea n a H); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia])
       end);
      store_done
  | _ => idtac
  end.

Lemma pj_shl1 : forall x, Z.shiftl x 1 = (2 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma pj_shl3 : forall x, Z.shiftl x 3 = (8 * x)%Z.
Proof. intros. rewrite Z.shiftl_mul_pow2 by lia. lia. Qed.
Lemma pj_shr3 : forall x, Z.shiftr x 3 = (x / 8)%Z.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. reflexivity. Qed.
Lemma pj_land64 : forall x, (0 <= x < 2^64)%Z -> Z.land x 18446744073709551615 = x.
Proof. intros x H. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.
Lemma pj_land1 : forall b : bool, Z.land (Z.b2z b) 1 = Z.b2z b.
Proof. intros [|]; reflexivity. Qed.
Lemma pj_zxb_small : forall x, (0 <= x < 256)%Z -> zxb (Z_to_bv 8 x) = Z_to_bv 64 x.
Proof. exact zxb_small. Qed.
Lemma pj_u8_small : forall c, (0 <= c < 256)%Z -> bv_unsigned (Z_to_bv 8 c) = c.
Proof. exact u8_small. Qed.

Ltac pjnorm :=
  cbv beta;
  repeat match goal with
  | |- context [Z.shiftl ?x 1] => rewrite (pj_shl1 x)
  | |- context [Z.shiftl ?x 3] => rewrite (pj_shl3 x)
  | |- context [Z.shiftr ?x 3] => rewrite (pj_shr3 x)
  | |- context [zxb (Z_to_bv 8 ?c)] => rewrite (pj_zxb_small c) by lia
  | |- context [bv_unsigned (Z_to_bv 8 ?c)] => rewrite (pj_u8_small c) by lia
  | |- context [Z.land ?x 18446744073709551615] => rewrite (pj_land64 x) by lia
  | |- context [Z.land (Z.b2z ?b) 1] => rewrite (pj_land1 b)
  end.
Ltac pjnorm_in H :=
  repeat match type of H with
  | context [Z.shiftl ?x 1] => rewrite (pj_shl1 x) in H
  | context [Z.shiftl ?x 3] => rewrite (pj_shl3 x) in H
  | context [Z.shiftr ?x 3] => rewrite (pj_shr3 x) in H
  | context [bv_unsigned (Z_to_bv 64 ?c)] => rewrite (unsigned_lit c) in H by lia
  | context [Z.land ?x 18446744073709551615] => rewrite (pj_land64 x) in H by lia
  | context [Z.land (Z.b2z ?b) 1] => rewrite (pj_land1 b) in H
  end.

Ltac pj_st_eq_leaf :=
  lazymatch goal with
  | |- Z_to_bv 64 _ = Z_to_bv 64 _ => first [reflexivity | f_equal; lia]
  | |- _ => reflexivity
  end.
Ltac pj_st_eq_tree :=
  lazymatch goal with
  | |- TNode _ _ _ = TNode _ _ _ => f_equal; pj_st_eq_tree
  | |- Some _ = Some _ => f_equal; pj_st_eq_leaf
  | |- _ => reflexivity
  end.
Ltac pj_st_eq :=
  cbv delta [mkR];
  lazymatch goal with
  | |- MS _ _ _ _ _ _ _ = MS _ _ _ _ _ _ _ => f_equal; pj_st_eq_tree
  end.

Ltac dlia := Z.div_mod_to_equations; lia.

Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Variable PMc : Model -> Prop.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Lemma aevt_eq : forall Σ K ms ms', ms = ms' -> aevt Σ K ms' -> aevt Σ K ms.
Proof. intros Σ K ms ms' -> H. exact H. Qed.

Lemma sb_pureA_ranges : forall E st, pjenvA_ok E -> sb_pureA E st ->
  0 < sa_buf st /\ 64 <= sa_cap st <= 134217728 /\ 0 <= sa_k st < 22
  /\ (sa_buf st + sa_cap st <= pa_lo E /\ sa_heap st = true \/ sa_buf st = pa_SB E /\ sa_cap st = 64 /\ sa_heap st = false).
Proof.
  intros E st OK ((K0 & C1 & C2) & HB).
  pose proof (PJ_CAPMAX_bound (pa_len E) (ok_len E OK)) as CMB.
  assert (0 < 2 ^ sa_k st) by (apply Z.pow_pos_nonneg; lia).
  pose proof (chain_fuel (pa_len E) (sa_cap st) (sa_k st) (ok_len E OK) K0 C1 C2) as KF.
  pose proof (ok_sb E OK) as (_ & S1 & _). pose proof (ok_frame E OK) as (_ & F1 & _). unfold SEGTOP_A in F1.
  destruct (sa_heap st); [destruct HB as (B0 & B16 & BL); lia| destruct HB as (-> & -> & _); lia].
Qed.

Lemma sb_pureA_below : forall E st, pjenvA_ok E -> sb_pureA E st -> sa_buf st + sa_cap st <= pa_lo E.
Proof.
  intros E st OK PU. pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & _ & R3).
  pose proof (ok_sb E OK) as (_ & _ & B2). pose proof (ok_frame E OK) as (_ & _ & FL).
  destruct R3 as [(BL & _)|(EB & EC & _)]; [exact BL| rewrite EB, EC; lia].
Qed.

Lemma sb_pureA_psi : forall E st, pjenvA_ok E -> sb_pureA E st -> 0 <= pj_psi (pa_len E) st.
Proof.
  intros E st OK PU. pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & K & _). pose proof PU as ((_ & _ & C2) & _).
  unfold pj_psi. rewrite PJ_GROWC_val. lia.
Qed.

Lemma CREDA_avail : forall E I Σc X st, pjenvA_ok E -> sb_pureA E st -> CREDA RT E I Σc X st -> 0 <= si_R I -> X <= rt_credit RT Σc.
Proof. intros E I Σc X st OK PU CR R0. pose proof (sb_pureA_psi E st OK PU). unfold CREDA in CR. lia. Qed.

Lemma env_rangesA : forall E, pjenvA_ok E ->
  0 < pa_TAPE E /\ pa_TAPE E + 8 * pa_n E <= pa_lo E /\ pa_TAPE E mod 16 = 0
  /\ 0 < pa_SBUF E /\ pa_SBUF E + pa_sn E <= pa_lo E /\ pa_SBUF E mod 16 = 0
  /\ pa_DOC E mod 8 = 0 /\ pa_SB E mod 32 = 0 /\ pa_F E mod 64 = 0 /\ SEGTOP_A <= pa_F E
  /\ pa_F E <= pa_SB E /\ pa_SB E + 88 <= pa_F E + fs_size (pa_kF E) - 8
  /\ pa_F E <= pa_DOC E /\ pa_DOC E + 16 <= pa_F E + fs_size (pa_kF E) - 8
  /\ pa_F E + fs_size (pa_kF E) <= pa_lo E /\ 0x7fff7f800000 <= pa_lo E
  /\ (pa_SB E + 88 <= pa_DOC E \/ pa_DOC E + 16 <= pa_SB E).
Proof.
  intros E OK. pose proof (ok_tape E OK) as (T16 & TN & T0 & TL & _). pose proof (ok_sbuf E OK) as (S16 & SN & S0 & SL & _).
  pose proof (ok_frame E OK) as (F64 & FS & FL). pose proof (ok_sb E OK) as (B32 & B1 & B2). pose proof (ok_doc E OK) as (D8 & D1 & D2).
  pose proof (ok_apart E OK) as AP. pose proof (ok_lo E OK) as LO.
  repeat (split; [first [assumption | lia]|]). exact AP.
Qed.

Lemma fs_size_64 : forall k, exists q, fs_size k = 64 * q /\ 1 <= q.
Proof.
  intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. exists (2 ^ Z.of_nat k).
  split; [lia|]. assert (0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia). lia.
Qed.

Lemma env_div8 : forall E D I, pjenvA_ok E -> sctxA E D I ->
  8 * (pa_DOC E / 8) = pa_DOC E /\ 8 * (pa_F E / 8) = pa_F E /\ 8 * (si_f I / 8) = si_f I /\ 8 * (pa_SB E / 8) = pa_SB E
  /\ (pa_F E + fs_size (pa_kF E)) / 8 = pa_F E / 8 + fs_size (pa_kF E) / 8 /\ 8 * (fs_size (pa_kF E) / 8) = fs_size (pa_kF E)
  /\ 64 <= fs_size (pa_kF E)
  /\ (pa_SB E + 64) / 8 = pa_SB E / 8 + 8 /\ (pa_SB E + 72) / 8 = pa_SB E / 8 + 9 /\ (pa_SB E + 80) / 8 = pa_SB E / 8 + 10
  /\ pa_TAPE E / 8 * 8 = pa_TAPE E /\ pa_SBUF E / 8 * 8 = pa_SBUF E.
Proof.
  intros E D I OK CX.
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & _).
  pose proof (c_f E D I CX) as (_ & f64 & _). destruct (fs_size_64 (pa_kF E)) as (q & EQ & Q1). rewrite EQ.
  repeat split; dlia.
Qed.

Lemma serWA_client : forall E D I Σc st m a, pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st m ->
  ~ aclient (rt_live RT Σc) (rt_frames RT Σc) (si_b I) a -> outside (serWA E I st) a.
Proof.
  intros E D I Σc st m a OK CX (ART0 & LV & FR & SP & _ & _ & PU & _) NA.
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (env_div8 E D I OK CX) as (_ & _ & Ef & _).
  pose proof (c_qtop E D I CX) as QT. pose proof (c_dd E D I CX) as DD. pose proof (c_f E D I CX) as (F0 & F64' & FSG & FLO).
  pose proof (c_F4 E D I CX) as IN4. pose proof (c_sp0 E D I CX) as (W1 & W2).
  unfold serWA, outside. unfold si_b in *. unfold aclient in NA.
  split. { intros C. apply NA. left. unfold USTACK_TOP in *. lia. }
  split. { intros C. apply NA. destruct R3 as [(BL & HP)|(EB & EC & HP)].
    - right; right; left. exists (sa_buf st), (sa_cap st). split; [| lia]. rewrite LV. unfold sbchunkA. rewrite HP. left. reflexivity.
    - right; right; right; left. exists (pa_F E), (pa_kF E). split; [rewrite FR; right; exact IN4| lia]. }
  split. { intros C. apply NA. right; right; right; left. exists (pa_F E), (pa_kF E). split; [rewrite FR; right; exact IN4| lia]. }
  split. { intros C. apply NA. right; right; right; left. exists (si_f I), 3%nat. split; [rewrite FR; left; reflexivity| rewrite fs3; lia]. }
  split; [| exact Logic.I]. intros C. apply NA. right; right; right; right. exists (si_f I), 3%nat. split; [rewrite FR; left; reflexivity|].
  rewrite fs3. clear - C Ef. unfold shad, SHB. dlia.
Qed.

Lemma ART_mu : forall E D I Σc st m m', pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st m ->
  munch (serWA E I st) m m' -> wmono bsegs m m' -> ART RT Σc m'.
Proof using AF.
  intros E D I Σc st m m' OK CX HR MU WM. pose proof HR as (ART0 & _ & _ & SP & _).
  pose proof (c_sp0 E D I CX) as (W1 & W2). pose proof (c_lo E D I CX) as LOQ. pose proof (c_dd E D I CX) as DD.
  apply (art_client_write RT AF Σc m m' (si_b I) ART0).
  - rewrite SP. unfold si_b. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. lia.
  - intros a Ha. apply MU. eapply serWA_client; eassumption.
  - exact WM.
Qed.

Lemma docrep_outside : forall E D I Σc st m x, pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st m ->
  docrep_rng E x -> outside (serWA E I st) x.
Proof using AF.
  intros E D I Σc st m x OK CX (ART0 & LV & FR & SP & _ & _ & PU & _) HX.
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (env_div8 E D I OK CX) as (ED & EF & Ef & ESB & EFS & Efs & FS64 & _).
  pose proof (c_f E D I CX) as (F0 & F64' & FSG & FLO). pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1.
  pose proof (c_f_shF E D I CX) as FSH2. pose proof (c_F_shF E D I CX) as FSH3. pose proof (c_sp0 E D I CX) as (W1 & W2).
  pose proof (c_lo E D I CX) as LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_F4 E D I CX) as IN4. pose proof (c_qtop E D I CX) as QT.
  pose proof (ok_tape E OK) as (_ & TN & _ & TNL & INT). pose proof (ok_sbuf E OK) as (_ & SN & _ & SNL & INS).
  rewrite EFS in FSH2, FSH3.
  unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT.
  assert (N0 : 0 <= pa_n E) by (clear; lia). assert (SN0 : 0 <= pa_sn E) by (clear; lia).
  assert (LS1 : pa_lo E + 16 <= si_q I - 416 - si_dd I) by (clear - LOQ DD; lia).
  assert (SD1 : pa_F E / 8 <= pa_DOC E / 8) by (clear - ED EF D1; lia).
  assert (SD2 : pa_DOC E / 8 + 2 <= pa_F E / 8 + fs_size (pa_kF E) / 8) by (clear - ED EF Efs D2; lia).
  assert (SDQ : pa_DOC E / 8 + 2147450880 + 2 <= pa_lo E) by (clear - ED D2 FL LS1 QT LO; lia).

  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR; right; exact IN4).
  assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σc)) by (rewrite FR; left; reflexivity).
  assert (INT' : In (pa_TAPE E, pa_NT E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INT).
  assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
  pose proof (af_frames_range RT AF Σc m _ _ ART0 INF4) as (_ & _ & _ & F4CH).
  pose proof (af_frames_range RT AF Σc m _ _ ART0 INF3) as (_ & _ & _ & F3CH).
  pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4)) as F4SH.
  pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF3)) as F3SH.
  unfold shad, SHB in F4SH, F3SH. rewrite fs3 in F3CH, F3SH. rewrite EFS in F4SH.
  pose proof (F4CH _ _ INT') as A1. pose proof (F4CH _ _ INS') as A2. pose proof (F3CH _ _ INT') as A3. pose proof (F3CH _ _ INS') as A4.
  pose proof (F4SH _ _ INT') as A5. pose proof (F4SH _ _ INS') as A6. pose proof (F3SH _ _ INT') as A7. pose proof (F3SH _ _ INS') as A8.
  replace ((si_f I + 512) / 8) with (si_f I / 8 + 64) in A7, A8 by (clear - Ef; dlia).

  assert (BUF : forall y, sa_buf st <= y < sa_buf st + sa_cap st ->
            ~ (pa_DOC E <= y < pa_DOC E + 16) /\ ~ (pa_DOC E / 8 + 2147450880 <= y < pa_DOC E / 8 + 2147450880 + 2)
            /\ ~ (pa_TAPE E <= y < pa_TAPE E + 8 * pa_n E) /\ ~ (pa_SBUF E <= y < pa_SBUF E + pa_sn E)).
  { intros y Hy. destruct R3 as [(BL & HP)|(EB & EC & HP)].
    - assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
      pose proof (F4CH _ _ INB) as C1. pose proof (F4SH _ _ INB) as C2.
      assert (LVE : rt_live RT Σc = [] ++ (sa_buf st, sa_cap st) :: pa_L E) by (rewrite LV; unfold sbchunkA; rewrite HP; reflexivity).
      pose proof (af_live_disj RT AF Σc m _ _ _ _ [] (pa_L E) ART0 LVE INT) as C3.
      pose proof (af_live_disj RT AF Σc m _ _ _ _ [] (pa_L E) ART0 LVE INS) as C4.
      split; [clear - Hy C1 D1 D2; lia|]. split; [clear - Hy C2 SD1 SD2; lia|]. split; [clear - Hy C3 TN; lia| clear - Hy C4 SN; lia].
    - rewrite EB, EC in Hy.
      split; [clear - Hy AP; lia|]. split; [clear - Hy FSH3 SD1 SD2 B1 B2; lia|]. split; [clear - Hy A1 B1 B2 TN; lia| clear - Hy A2 B1 B2 SN; lia]. }
  unfold docrep_rng in HX. unfold shad, SHB in HX. unfold serWA, outside, si_b. cbn [fst snd].
  destruct HX as [HX|[HX|[HX|HX]]].
  - split; [clear - HX LS1 FL D2; lia|]. split; [intros C; exact (proj1 (BUF x C) HX)|]. split; [clear - HX AP; lia|].
    split; [clear - HX FF D1 D2; lia|]. split; [clear - HX FSH1 D1 D2; lia| exact Logic.I].
  - split; [clear - HX SDQ LS1; lia|]. split; [intros C; exact (proj1 (proj2 (BUF x C)) HX)|]. split; [clear - HX FSH3 SD1 SD2 B1 B2; lia|].
    split; [clear - HX FSH2 SD1 SD2; lia|]. split; [clear - HX FF Ef EF Efs SD1 SD2 FS64; lia| exact Logic.I].
  - split; [clear - HX TNL TN LS1; lia|]. split; [intros C; exact (proj1 (proj2 (proj2 (BUF x C))) HX)|]. split; [clear - HX A1 B1 B2 TN; lia|].
    split; [clear - HX A3 TN; lia|]. split; [clear - HX A7 TN; lia| exact Logic.I].
  - split; [clear - HX SNL SN LS1; lia|]. split; [intros C; exact (proj2 (proj2 (proj2 (BUF x C))) HX)|]. split; [clear - HX A2 B1 B2 SN; lia|].
    split; [clear - HX A4 SN; lia|]. split; [clear - HX A8 SN; lia| exact Logic.I].
Qed.

Lemma serWA_below : forall E D I Σc st m a, pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st m ->
  aclient (pa_L E) (si_fr I) (si_q I) a -> outside [(pa_SB E, pa_SB E + 88)] a -> outside (serWA E I st) a.
Proof using AF.
  intros E D I Σc st m a OK CX (ART0 & LV & FR & SP & _ & _ & PU & _) CA OUT.
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (env_div8 E D I OK CX) as (ED & EF & Ef & ESB & EFS & Efs & FS64 & _).
  pose proof (c_f E D I CX) as (F0 & F64' & FSG & FLO). pose proof (c_fF E D I CX) as FF. pose proof (c_F_shf E D I CX) as FSH1.
  pose proof (c_f_shF E D I CX) as FSH2. pose proof (c_F_shF E D I CX) as FSH3. pose proof (c_sp0 E D I CX) as (W1 & W2).
  pose proof (c_lo E D I CX) as LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_F4 E D I CX) as IN4. pose proof (c_qtop E D I CX) as QT.
  unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT. unfold STACK_WIN in W1. unfold SEGTOP_A in FSG, FS.
  assert (LS1 : pa_lo E + 16 <= si_q I - 416 - si_dd I) by (clear - LOQ DD; lia).
  assert (LQ : pa_lo E + 416 <= si_q I) by (clear - LOQ; lia).
  assert (SHF : si_f I / 8 + 2147450880 + 64 <= pa_lo E) by (clear - Ef FLO LQ QT LO; lia).
  cbn [outside fst snd] in OUT. destruct OUT as [OUT _].
  unfold serWA, outside, si_b. cbn [fst snd].
  destruct CA as [CA|[CA|[CA|[CA|CA]]]].
  -
    assert (BUFp : ~ (sa_buf st <= a < sa_buf st + sa_cap st)).
    { destruct R3 as [(BL & HP)|(EB & EC & HP)]; [clear - CA BL LQ; lia| clear - CA EB EC FL B1 B2 LQ; lia]. }
    repeat split; [clear - CA; lia| exact BUFp| clear - CA FL B2 LQ; lia| clear - CA FLO LQ; lia| clear - CA SHF LQ; lia].
  -
    apply client_static_range in CA. unfold SEGTOP_A in CA.
    destruct R3 as [(BL & HP)|(EB & EC & HP)].
    + assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
      pose proof (af_live_range RT AF Σc m _ _ ART0 INB) as (_ & _ & BR). unfold SEGTOP_A in BR.
      repeat split; [clear - CA LS1 LO| clear - CA BR| clear - CA FS B1| clear - CA FSG| clear - CA Ef F0]; lia.
    + repeat split; [clear - CA LS1 LO| clear - CA EB EC FS B1| clear - CA FS B1| clear - CA FSG| clear - CA Ef F0]; lia.
  -
    destruct CA as (p & n & INp & Hp).
    assert (INp' : In (p, n) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INp).
    pose proof (af_live_range RT AF Σc m _ _ ART0 INp') as (_ & PR & _). unfold STACK_WIN in PR.
    assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR; right; exact IN4).
    assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σc)) by (rewrite FR; left; reflexivity).
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INF4) as (_ & _ & _ & F4CH). pose proof (F4CH _ _ INp') as A1.
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INF3) as (_ & _ & _ & F3CH). pose proof (F3CH _ _ INp') as A3. rewrite fs3 in A3.
    pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF3) _ _ INp') as A7. unfold shad, SHB in A7. rewrite fs3 in A7.
    replace ((si_f I + 512) / 8) with (si_f I / 8 + 64) in A7 by (clear - Ef; dlia).
    assert (BUFp : ~ (sa_buf st <= a < sa_buf st + sa_cap st)).
    { destruct R3 as [(BL & HP)|(EB & EC & HP)].
      - assert (LVE : rt_live RT Σc = [] ++ (sa_buf st, sa_cap st) :: pa_L E) by (rewrite LV; unfold sbchunkA; rewrite HP; reflexivity).
        pose proof (af_live_disj RT AF Σc m _ _ _ _ [] (pa_L E) ART0 LVE INp) as C3. clear - C3 Hp. lia.
      - clear - EB EC Hp A1 B1 B2. lia. }
    repeat split; [clear - Hp PR W1 LS1 SP; lia| exact BUFp| clear - Hp A1 B1 B2; lia| clear - Hp A3; lia| clear - Hp A7; lia].
  -
    destruct CA as (g & k & INg & Hg).
    assert (INg' : In (g, k) (rt_frames RT Σc)) by (rewrite FR; right; exact INg).
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INg') as (_ & GR & _ & GCH). unfold STACK_WIN in GR.
    pose proof (af_frames_disj RT AF Σc m (si_f I) 3%nat g k [] (si_fr I) ART0 ltac:(rewrite FR; reflexivity) INg) as GF. rewrite fs3 in GF.
    assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σc)) by (rewrite FR; left; reflexivity).
    pose proof (proj2 (af_fshadow_apart RT AF Σc m _ _ ART0 INF3) _ _ INg') as GS. unfold shad, SHB in GS. rewrite fs3 in GS.
    replace ((si_f I + 512) / 8) with (si_f I / 8 + 64) in GS by (clear - Ef; dlia).
    assert (BUFp : ~ (sa_buf st <= a < sa_buf st + sa_cap st)).
    { destruct R3 as [(BL & HP)|(EB & EC & HP)].
      - assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
        pose proof (GCH _ _ INB) as C1. clear - C1 Hg. lia.
      - clear - EB EC Hg OUT. lia. }
    repeat split; [clear - Hg GR W1 LS1 SP; lia| exact BUFp| clear - Hg OUT; lia| clear - Hg GF; lia| clear - Hg GS; lia].
  -
    destruct CA as (g & k & INg & Hg). unfold shad, SHB in Hg.
    assert (INg' : In (g, k) (rt_frames RT Σc)) by (rewrite FR; right; exact INg).
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INg') as (G0 & GR & _ & _). unfold STACK_WIN in GR.
    pose proof (af_frames_align RT AF Σc m _ _ ART0 INg') as [G64 _].
    pose proof (af_frames_disj RT AF Σc m (si_f I) 3%nat g k [] (si_fr I) ART0 ltac:(rewrite FR; reflexivity) INg) as GF. rewrite fs3 in GF.
    assert (INF3 : In (si_f I, 3%nat) (rt_frames RT Σc)) by (rewrite FR; left; reflexivity).
    assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR; right; exact IN4).
    pose proof (af_fshadow_apart RT AF Σc m _ _ ART0 INg') as [GSC GSF]. unfold shad, SHB in GSC, GSF.
    pose proof (GSF _ _ INF3) as B3. rewrite fs3 in B3. pose proof (GSF _ _ INF4) as B4.
    destruct (fs_size_64 k) as (qk & EK & QK1). rewrite EK in Hg, GR, GF, B3, B4.
    assert (EG : 8 * (g / 8) = g) by (clear - G64; dlia).
    assert (EGK : (g + 64 * qk) / 8 = g / 8 + 8 * qk) by (clear - G64; dlia).
    rewrite EGK in Hg, B3, B4.
    pose proof (af_sp0_range RT AF Σc m ART0) as SPR. unfold USTACK_TOP, SEGTOP_A, STACK_WIN in SPR.
    assert (TOP : g / 8 + 8 * qk + 2147450880 <= pa_lo E) by (clear - EG GR SPR LO QK1 G0; lia).
    assert (BUFp : ~ (sa_buf st <= a < sa_buf st + sa_cap st)).
    { destruct R3 as [(BL & HP)|(EB & EC & HP)].
      - assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
        pose proof (GSC _ _ INB) as C1. rewrite EK, EGK in C1. clear - C1 Hg. lia.
      - clear - EB EC Hg B4 B1 B2. lia. }
    repeat split; [clear - Hg TOP LS1; lia| exact BUFp| clear - Hg B4 B1 B2; lia| clear - Hg B3; lia|].
    clear - Hg GF EG Ef QK1. lia.
Qed.

Lemma shF4_outside : forall E D I Σc st m x, pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st m ->
  pa_F E / 8 + 2147450880 <= x < pa_F E / 8 + fs_size (pa_kF E) / 8 + 2147450880 -> outside (serWA E I st) x.
Proof using AF.
  intros E D I Σc st m x OK CX (ART0 & LV & FR & SP & _ & _ & PU & _) HX.
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (env_div8 E D I OK CX) as (ED & EF & Ef & ESB & EFS & Efs & FS64 & _).
  pose proof (c_fF E D I CX) as FF. pose proof (c_f_shF E D I CX) as FSH2. pose proof (c_F_shF E D I CX) as FSH3. pose proof (c_sp0 E D I CX) as (W1 & W2).
  pose proof (c_lo E D I CX) as LOQ. pose proof (c_dd E D I CX) as DD. pose proof (c_F4 E D I CX) as IN4. pose proof (c_qtop E D I CX) as QT.
  rewrite EFS in FSH2, FSH3.
  unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. unfold USTACK_TOP in QT.
  assert (LS1 : pa_lo E + 16 <= si_q I - 416 - si_dd I) by (clear - LOQ DD; lia).
  assert (TOP : pa_F E / 8 + fs_size (pa_kF E) / 8 + 2147450880 <= pa_lo E) by (clear - EF Efs FL LS1 QT LO; lia).
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR; right; exact IN4).
  pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4)) as F4SH. unfold shad, SHB in F4SH. rewrite EFS in F4SH.
  assert (BUFp : ~ (sa_buf st <= x < sa_buf st + sa_cap st)).
  { destruct R3 as [(BL & HP)|(EB & EC & HP)].
    - assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
      pose proof (F4SH _ _ INB) as C2. clear - C2 HX. lia.
    - clear - EB EC HX FSH3 B1 B2. lia. }
  unfold serWA, outside, si_b. cbn [fst snd].
  repeat split; [clear - HX TOP LS1; lia| exact BUFp| clear - HX FSH3 B1 B2; lia| clear - HX FSH2; lia| clear - HX FF Ef EF Efs FS64; lia].
Qed.

Lemma sb_pureA_sized : forall E st n, sb_pureA E (sb_sized st n) = sb_pureA E st.
Proof. intros E [b sz c h k] n. reflexivity. Qed.

Lemma SREFA_munch : forall E D I Σc st m m' n, pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st m ->
  munch (serWA E I st) m m' -> wmono bsegs m m' -> SREFA RT E I Σc (sb_sized st n) m'.
Proof using AF.
  intros E D I Σc st m m' n OK CX HR MU WM. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (env_div8 E D I OK CX) as (ED & EF & Ef & ESB & EFS & Efs & FS64 & _).
  unfold SREFA. rewrite sbchunk_sized, sb_pureA_sized.
  split; [eapply ART_mu; eassumption|]. split; [exact LV|]. split; [exact FR|]. split; [exact SP|].
  split. { eapply DOCREPA_agree; [exact DR|]. eapply agree_of_munch; [exact MU|]. intros x Hx. eapply docrep_outside; eassumption. }
  split. { eapply bytes_at_agree; [exact SBSH|]. eapply agree_of_munch; [exact MU|]. intros x Hx. rewrite repeat_length in Hx.
           unfold shad, SHB in Hx. eapply shF4_outside; [eassumption| eassumption| eassumption|]. clear - Hx ESB EF Efs B1 B2. lia. }
  split; [exact PU|].
  intros a CA OUT. rewrite <- (PRES a CA OUT). apply MU. eapply serWA_below; eassumption.
Qed.

Lemma u64s_read : forall (ws : list word) (i : nat), (i < length ws)%nat ->
  firstn 8 (skipn (8 * i) (u64s ws)) = le8 (nth i ws (Z_to_bv 64 0)).
Proof.
  induction ws as [|w ws IH]; intros i Hi; cbn [length] in Hi; [lia|].
  destruct i as [|i].
  - rewrite Nat.mul_0_r, skipn_O. cbn [u64s]. rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite firstn_all2 by (rewrite length_le8; lia). reflexivity.
  - replace (8 * S i)%nat with (8 + 8 * i)%nat by lia. cbn [u64s nth]. rewrite skipn_app, length_le8.
    replace (8 + 8 * i - 8)%nat with (8 * i)%nat by lia. rewrite skipn_all2 by (rewrite length_le8; lia). cbn [app].
    apply IH. lia.
Qed.

Lemma tape_read : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i)) 8 = Some (le8 (Z_to_bv 64 (Tf tws i))).
Proof.
  intros m TAPE tws i HB Hi.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i) 8 HB); [| lia| rewrite u64s_length, length_map; lia].
  replace (Z.to_nat (8 * i)) with (8 * Z.to_nat i)%nat by lia.
  rewrite u64s_read by (rewrite length_map; lia). f_equal. f_equal.
  unfold Tf. apply (map_nth (Z_to_bv 64)).
Qed.

Lemma le8_byte7 : forall w, 0 <= w < 2^64 -> skipn 7 (le8 (Z_to_bv 64 w)) = [Z_to_bv 8 (ttype w)].
Proof.
  intros w H. unfold le8, word_to_le_bytes. rewrite unsigned_lit by lia.
  cbn [Z_to_le_bytes skipn]. rewrite !Z.shiftr_shiftr by lia. cbn [Z.add Pos.add Pos.succ]. rewrite shr56_ttype. reflexivity.
Qed.

Lemma tape_read7 : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) -> 0 <= Tf tws i < 2^64 ->
  ov_read_bytes bsegs m (wa (TAPE + (8 * i + 7))) 1 = Some [Z_to_bv 8 (ttype (Tf tws i))].
Proof.
  intros m TAPE tws i HB Hi HW.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i + 7) 1 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal.
  replace (Z.to_nat (8 * i + 7)) with (7 + 8 * Z.to_nat i)%nat by lia.
  rewrite <- skipn_skipn. rewrite <- (le8_byte7 _ HW).
  assert (E8 : firstn 8 (skipn (8 * Z.to_nat i) (u64s (map (Z_to_bv 64) tws))) = le8 (Z_to_bv 64 (Tf tws i))).
  { rewrite u64s_read by (rewrite length_map; lia). f_equal. unfold Tf. apply (map_nth (Z_to_bv 64)). }
  rewrite <- E8.
  set (l := skipn (8 * Z.to_nat i) (u64s (map (Z_to_bv 64) tws))).
  assert (HL : (8 <= length l)%nat) by (unfold l; rewrite skipn_length, u64s_length, length_map; lia).
  clearbody l. clear - HL.
  do 8 (destruct l as [|? l]; [cbn [length] in HL; lia|]). reflexivity.
Qed.

Lemma tnext_back : forall w e, tnext w = e + 1 -> 0 <= e ->
  Z.land (Z.land (w + 4294967295) 18446744073709551615) 4294967295 = e.
Proof.
  intros w e H He. unfold tnext in H.
  rewrite <- Z.land_assoc. change (Z.land 18446744073709551615 4294967295) with (Z.ones 32).
  rewrite Z.land_ones by lia.
  pose proof (Z.mod_pos_bound w (2^32) ltac:(lia)) as B.
  rewrite Z.add_mod by lia. rewrite H.
  change (4294967295 mod 2 ^ 32) with 4294967295.
  replace (e + 1 + 4294967295) with (e + 1 * 2^32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma tnext_back2 : forall w e, tnext w = e + 1 -> 0 <= e -> Z.land (w + 4294967295) 4294967295 = e.
Proof.
  intros w e H He. unfold tnext in H.
  replace (Z.land (w + 4294967295) 4294967295) with ((w + 4294967295) mod 2 ^ 32)
    by (change 4294967295 with (Z.ones 32) at 3; rewrite Z.land_ones by lia; reflexivity).
  rewrite Z.add_mod, H by lia. change (4294967295 mod 2 ^ 32) with 4294967295.
  replace (e + 1 + 4294967295) with (e + 1 * 2 ^ 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma sbuf_read1 : forall m SBUF (sbs : list Z) (o : Z),
  bytes_at bsegs m SBUF (map (Z_to_bv 8) sbs) -> 0 <= o < Z.of_nat (length sbs) ->
  ov_read_bytes bsegs m (wa (SBUF + o)) 1 = Some [Z_to_bv 8 (Tf sbs o)].
Proof.
  intros m SBUF sbs o HB Ho.
  rewrite (bytes_at_read bsegs m SBUF _ o 1 HB); [| lia| rewrite length_map; lia]. f_equal.
  unfold Tf. rewrite <- (map_nth (Z_to_bv 8)).
  remember (map (Z_to_bv 8) sbs) as l eqn:El.
  assert (HL : (Z.to_nat o < length l)%nat) by (subst l; rewrite length_map; lia). clear El HB Ho.
  revert l HL. generalize (Z.to_nat o) as k. clear o.
  induction k as [|k IH]; intros [|c l] HL; cbn [length] in HL; try lia; [reflexivity|].
  cbn [skipn nth]. apply IH. lia.
Qed.

Section Mu.
  Variables (E : pjenvA) (D : nat) (I : serI).
  Hypothesis OK : pjenvA_ok E.
  Hypothesis CX : sctxA E D I.

  Lemma tape_read_mu : forall Σc st mr m i, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m ->
    0 <= i < pa_n E -> ov_read_bytes bsegs m (wa (pa_TAPE E + 8 * i)) 8 = Some (le8 (Z_to_bv 64 (pa_T E i))).
  Proof using AF OK CX.
    intros Σc st mr m i HR MU WM Hi.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & _ & TB & _) & _). apply tape_read; assumption.
  Qed.

  Lemma tape_read7_mu : forall Σc st mr m i, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m ->
    0 <= i < pa_n E -> 0 <= pa_T E i < 2^64 -> ov_read_bytes bsegs m (wa (pa_TAPE E + (8 * i + 7))) 1 = Some [Z_to_bv 8 (ttype (pa_T E i))].
  Proof using AF OK CX.
    intros Σc st mr m i HR MU WM Hi HW.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & _ & TB & _) & _). apply tape_read7; assumption.
  Qed.

  Lemma sbuf_read_mu : forall Σc st mr m o, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m ->
    0 <= o < pa_sn E -> ov_read_bytes bsegs m (wa (pa_SBUF E + o)) 1 = Some [Z_to_bv 8 (pa_S E o)].
  Proof using AF OK CX.
    intros Σc st mr m o HR MU WM Ho.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & _ & _ & SB) & _). apply sbuf_read1; assumption.
  Qed.

  Lemma doc_cells_mu : forall Σc st mr m, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m ->
    rw_cells bsegs m (pa_DOC E) [C8 (Z_to_bv 64 (pa_TAPE E)); C8 (Z_to_bv 64 (pa_SBUF E))].
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (DC & _) & _). exact DC.
  Qed.

  Lemma shz_sb_mu : forall Σc st mr m, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m -> shz m (pa_SB E) 88.
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & _ & SH & _).
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & B32 & _ & FS & B1 & _). unfold SEGTOP_A in FS.
    apply (shz_of_zero_run m (pa_SB E) 11); [clear - B32; dlia| clear - FS B1; lia| exact SH].
  Qed.

  Lemma shz_doc_mu : forall Σc st mr m, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m -> shz m (pa_DOC E) 16.
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & SH & _) & _).
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & D8 & _ & _ & FS & _ & _ & D1 & _). unfold SEGTOP_A in FS.
    apply (shz_of_zero_run m (pa_DOC E) 2); [exact D8| clear - FS D1; lia| exact SH].
  Qed.

  Lemma shz_tape_mu : forall Σc st mr m, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m -> shz m (pa_TAPE E) (8 * pa_n E).
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _). pose proof HR as (_ & LV & _).
    pose proof (ok_tape E OK) as (T16 & TN & T0 & _ & INT).
    assert (INT' : In (pa_TAPE E, pa_NT E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INT).
    pose proof (shz_live RT AF Σc m _ _ ART1 INT' ltac:(clear - T16; dlia)) as SH.
    eapply shz_sub; [exact SH| lia| clear - TN; dlia].
  Qed.

  Lemma acc_sbuf_mu : forall Σc st mr m, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m -> acc bsegs m (pa_SBUF E) (pa_NS E).
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _). pose proof HR as (_ & LV & _).
    pose proof (ok_sbuf E OK) as (_ & _ & _ & _ & INS).
    assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
    exact (proj2 (af_acc_live RT AF Σc m _ _ ART1 INS')).
  Qed.
  Lemma shz_sbuf_mu : forall Σc st mr m, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m -> shz m (pa_SBUF E) (8 * (pa_NS E / 8)).
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _). pose proof HR as (_ & LV & _).
    pose proof (ok_sbuf E OK) as (S16 & _ & _ & _ & INS).
    assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
    exact (shz_live RT AF Σc m _ _ ART1 INS' ltac:(clear - S16; dlia)).
  Qed.

  Lemma acc_buf_mu : forall Σc st mr m, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m -> acc bsegs m (sa_buf st) (sa_cap st).
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _ & _ & _ & _ & SH & _).
    pose proof HR as (_ & LV & _ & _ & _ & _ & PU & _).
    pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & B32 & _ & FS & B1 & _). unfold SEGTOP_A in FS.
    destruct R3 as [(BL & HP)|(EB & EC & HP)].
    - apply (proj2 (af_acc_live RT AF Σc m (sa_buf st) (sa_cap st) ART1 ltac:(rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity))).
    - rewrite EB, EC. eapply (acc_sub bsegs); [apply (acc_zero_run bsegs m (pa_SB E) 11); [clear - B32; dlia| clear - FS B1; lia| exact SH]| lia| lia].
  Qed.

  Lemma shz_static_mu : forall Σc st mr m a n, SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m ->
    a mod 8 = 0 -> 0 <= a -> n mod 8 = 0 -> 0 <= n -> (forall i, 0 <= i < n -> client_static (a + i) /\ ~ (0x184df0 <= a + i < 0x1862b0)) -> shz m a n.
  Proof using AF OK CX.
    intros Σc st mr m a n HR MU WM A8 A0 N8 N0 CS.
    pose proof (SREFA_munch E D I Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _).
    pose proof (af_acc_static RT AF Σc m a n ART1 A0 CS) as AC.
    replace n with (8 * (n / 8)) by (clear - N8; dlia). apply shz_of_acc; [exact AC| exact A8| exact A0].
  Qed.
End Mu.

Lemma isobj_sh_read : forall (m : mem) I dp x, u8arr bsegs m (SHFA I) ser_shpatA -> 8 * (si_f I / 8) = si_f I -> 0 <= dp <= 15 ->
  x = (si_f I + 304 + dp) / 8 + 2147450880 -> ov_read_bytes bsegs m (wa x) 1 = Some [Z_to_bv 8 0].
Proof.
  intros m I dp x U Ef Hdp ->.
  assert (C : (si_f I + 304 + dp) / 8 = si_f I / 8 + 38 \/ (si_f I + 304 + dp) / 8 = si_f I / 8 + 39) by (clear - Ef Hdp; dlia).
  destruct C as [C|C]; rewrite C.
  - apply (u8arr_read bsegs m (SHFA I) ser_shpatA 38 (Z_to_bv 8 0)); [exact U| reflexivity| lia| unfold wa; f_equal; lia].
  - apply (u8arr_read bsegs m (SHFA I) ser_shpatA 39 (Z_to_bv 8 0)); [exact U| reflexivity| lia| unfold wa; f_equal; lia].
Qed.

Lemma SERMA_intro : forall E D I w x shp isobj Σc st mr m size (h0 h1 h2 : word),
  pjenvA_ok E -> sctxA E D I -> SREFA RT E I Σc st mr -> munch (serWA E I st) mr m -> wmono bsegs mr m ->
  rw_cells bsegs m (si_b I) (ser_frameA E I w x) ->
  stk bsegs m (si_b I + 312) (si_q I - 104) -> rw_cells bsegs m (si_q I - 104) (ser_savedA I) ->
  rw_cells bsegs m (si_f I) [C8 h0; C8 h1; C8 h2] -> stk bsegs m (si_f I + 24) (si_f I + 304) ->
  u8arr bsegs m (si_f I + 304) isobj -> length isobj = 16%nat ->
  u8arr bsegs m (SHFA I) shp -> length shp = 44%nat -> stk bsegs m (SHFA I + 44) (SHFA I + 64) ->
  rw_cells bsegs m (pa_SB E + 64) [C8 (wz (sa_buf st)); C8 (wz size); C8 (wz (sa_cap st))] -> 0 <= size <= sa_cap st ->
  stk bsegs m (sa_buf st) (sa_buf st + sa_cap st) -> stk bsegs m (pa_SB E) (pa_SB E + 64) ->
  mem_inv bsegs m -> stk bsegs m (pa_lo E) (si_b I) ->
  SERMA RT E I w x shp isobj Σc (sb_sized st size) m.
Proof using AF.
  intros until h2. intros OK CX HR MU WM FR GAP FS FH F3S IS ISL SHF SHL SHT SV SZ BUFS INLS MI ST.
  split; [eapply SREFA_munch; eassumption|].
  unfold SCURA. destruct st as [buf sz cap hp k]. cbn [sb_sized sa_buf sa_size sa_cap sa_heap sa_k] in *.
  split; [exact FR|]. split; [exact GAP|]. split; [exact FS|].
  split; [exists h0, h1, h2; exact FH|]. repeat (split; [assumption|]). assumption.
Qed.

Lemma SBINVA_of_SERMA : forall E D I w x shp isobj Σc st m, pjenvA_ok E -> sctxA E D I ->
  SERMA RT E I w x shp isobj Σc st m -> SBINVA E m st.
Proof.
  intros until m. intros OK CX [(_ & _ & _ & _ & _ & SBSH & (PK & PH) & _) HC].
  destruct HC as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SV & SZ & BUFS & INLS & _ & _).
  pose proof (sb_pureA_ranges E st OK (conj PK PH)) as (R0 & R1 & _).
  unfold SBINVA. split; [exact SV|]. split; [exact SZ|].
  split. { destruct (stk_CB bsegs m _ _ BUFS ltac:(lia)) as (bs & HBS). exists bs.
           replace (sa_buf st + sa_cap st - sa_buf st) with (sa_cap st) in HBS by lia. exact HBS. }
  split. { destruct (stk_CB bsegs m _ _ INLS ltac:(lia)) as (bs & HBS). exists bs.
           replace (Z.to_nat (pa_SB E + 64 - pa_SB E)) with 64%nat in HBS by lia. exact HBS. }
  split; [exact SBSH|]. split; [exact PK| exact PH].
Qed.

Lemma pa_live_of_SERMA : forall E D I w x shp isobj Σc st m, sctxA E D I ->
  SERMA RT E I w x shp isobj Σc st m -> pa_live RT Σc E st.
Proof.
  intros until m. intros CX [(_ & LV & FR & SP & _) _]. split; [exact LV|]. split.
  - rewrite FR. right. exact (c_F4 E D I CX).
  - rewrite SP. exact (proj1 (c_sp0 E D I CX)).
Qed.

Lemma DOCREPA_of_SERMA : forall E I w x shp isobj Σc st m, SERMA RT E I w x shp isobj Σc st m -> DOCREPA E m.
Proof. intros until m. intros [(_ & _ & _ & _ & DR & _) _]. exact DR. Qed.

Lemma ART_of_SERMA : forall E I w x shp isobj Σc st m, SERMA RT E I w x shp isobj Σc st m -> ART RT Σc m.
Proof. intros until m. intros [(A & _) _]. exact A. Qed.

Lemma SBINVA_of_SERMC : forall E D I isobj Σc st m, pjenvA_ok E -> sctxA E D I -> SERMC RT E I isobj Σc st m -> SBINVA E m st.
Proof. intros until m. intros OK CX [x HM]. eapply SBINVA_of_SERMA; eassumption. Qed.
Lemma pa_live_of_SERMC : forall E D I isobj Σc st m, sctxA E D I -> SERMC RT E I isobj Σc st m -> pa_live RT Σc E st.
Proof. intros until m. intros CX [x HM]. eapply pa_live_of_SERMA; eassumption. Qed.
Lemma DOCREPA_of_SERMC : forall E I isobj Σc st m, SERMC RT E I isobj Σc st m -> DOCREPA E m.
Proof. intros until m. intros [x HM]. eapply DOCREPA_of_SERMA; eassumption. Qed.
Lemma ART_of_SERMC : forall E I isobj Σc st m, SERMC RT E I isobj Σc st m -> ART RT Σc m.
Proof. intros until m. intros [x HM]. eapply ART_of_SERMA; eassumption. Qed.
Lemma SBINVA_of_SERMK : forall E D I isobj Σc st m, pjenvA_ok E -> sctxA E D I -> SERMK RT E I isobj Σc st m -> SBINVA E m st.
Proof. intros until m. intros OK CX (x & x224 & HM). eapply SBINVA_of_SERMA; eassumption. Qed.
Lemma pa_live_of_SERMK : forall E D I isobj Σc st m, sctxA E D I -> SERMK RT E I isobj Σc st m -> pa_live RT Σc E st.
Proof. intros until m. intros CX (x & x224 & HM). eapply pa_live_of_SERMA; eassumption. Qed.
Lemma ART_of_SERMK : forall E I isobj Σc st m, SERMK RT E I isobj Σc st m -> ART RT Σc m.
Proof. intros until m. intros (x & x224 & HM). eapply ART_of_SERMA; eassumption. Qed.

Lemma SREFA_sized : forall E I Σc st m n, SREFA RT E I Σc st m -> SREFA RT E I Σc (sb_sized st n) m.
Proof. intros E I Σc st m n H. unfold SREFA in *. rewrite sbchunk_sized, sb_pureA_sized. exact H. Qed.

End Kit.

Definition boxP (P : Prop) : Prop := P.
Ltac box_disj := repeat match goal with H : ?A \/ ?B |- _ => change (boxP (A \/ B)) in H end.
Ltac unbox H := unfold boxP in H.

Ltac ser_envA OK CX :=
  lazymatch type of CX with sctxA ?E ?D ?I =>
  let H := fresh in
  pose proof (env_rangesA E OK) as H;
  let FS := fresh "FS" in let B1 := fresh "B1" in let B2 := fresh "B2" in let D1 := fresh "D1" in let D2 := fresh "D2" in let FL := fresh "FL" in
  let LO := fresh "LO" in
  let T0 := fresh in let TL := fresh in let S0 := fresh in let SL := fresh in
  destruct H as (T0 & TL & _ & S0 & SL & _ & _ & _ & _ & FS & B1 & B2 & D1 & D2 & FL & LO & AP);
  assert (TR : 0 < pa_TAPE E /\ pa_TAPE E + 8 * pa_n E <= pa_lo E) by (clear - T0 TL; split; assumption);
  assert (SR : 0 < pa_SBUF E /\ pa_SBUF E + pa_sn E <= pa_lo E) by (clear - S0 SL; split; assumption); clear T0 TL S0 SL;
  pose proof (c_dd E D I CX) as DD;
  let LOQ := fresh in pose proof (c_lo E D I CX) as LOQ; unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ;
  assert (LQ : pa_lo E + 656 + 65536 <= si_q I) by (clear - LOQ; lia); clear LOQ;
  assert (BQ : si_b I + 416 <= si_q I /\ si_q I <= si_b I + 432) by (unfold si_b; clear - DD; lia);
  assert (LB : pa_lo E + 65696 <= si_b I) by (unfold si_b; clear - DD LQ; lia);
  pose proof (c_qtop E D I CX) as QT; unfold USTACK_TOP in QT;
  let Hf := fresh in pose proof (c_f E D I CX) as Hf; destruct Hf as (F0 & _ & FSG & FLO); unfold SEGTOP_A in FSG;
  let H8 := fresh in pose proof (env_div8 E D I OK CX) as H8;
  let EF := fresh in let EFS := fresh in let Efs := fresh in
  destruct H8 as (_ & EF & Ef & _ & EFS & Efs & _);
  assert (SFL : si_f I / 8 + 2147450880 + 64 <= pa_lo E /\ 901120 <= si_f I / 8) by (clear - Ef FLO LQ QT F0 FSG LO; lia);
  assert (SBR : 7208960 <= pa_SB E /\ pa_SB E + 96 <= pa_lo E) by (clear - FS B1 B2 FL; unfold SEGTOP_A in *; lia);
  assert (DOCR : 7208960 <= pa_DOC E /\ pa_DOC E + 24 <= pa_lo E) by (clear - FS D1 D2 FL; unfold SEGTOP_A in *; lia);
  let FF := fresh in pose proof (c_fF E D I CX) as FF;
  assert (FSB : si_f I + 512 <= pa_SB E \/ pa_SB E + 96 <= si_f I) by (clear - FF B1 B2; lia);
  assert (FDOC : si_f I + 512 <= pa_DOC E \/ pa_DOC E + 24 <= si_f I) by (clear - FF D1 D2; lia);
  let F1 := fresh in pose proof (c_F_shf E D I CX) as F1;
  assert (SHSB : pa_SB E + 96 <= si_f I / 8 + 2147450880 \/ si_f I / 8 + 2147450880 + 64 <= pa_SB E) by (clear - F1 B1 B2; lia);
  assert (SHDC : pa_DOC E + 24 <= si_f I / 8 + 2147450880 \/ si_f I / 8 + 2147450880 + 64 <= pa_DOC E) by (clear - F1 D1 D2; lia);
  pose proof (c_f_shf E D I CX) as SHf;
  clear FS B1 B2 D1 D2 FL FF F1 EF EFS Efs;
  change (boxP (si_dd I = 0 \/ si_dd I = 16)) in DD;
  lazymatch type of AP with ?T => change (boxP T) in AP end;
  lazymatch type of FSB with ?T => change (boxP T) in FSB end; lazymatch type of FDOC with ?T => change (boxP T) in FDOC end;
  lazymatch type of SHSB with ?T => change (boxP T) in SHSB end; lazymatch type of SHDC with ?T => change (boxP T) in SHDC end;
  lazymatch type of SHf with ?T => change (boxP T) in SHf end
  end.

Ltac ser_open HM OK :=
  lazymatch type of HM with
  | SERMA ?RT ?E ?I ?w ?x _ _ _ _ _ =>
      unfold SERMA, sb_grownA, sb_sized in HM; cbn [sa_buf sa_size sa_cap sa_heap sa_k] in HM;
      destruct HM as [HREF HCUR];
      unfold SCURA in HCUR; cbn [sa_buf sa_size sa_cap sa_heap sa_k] in HCUR;
      let SZ := fresh "SZ" in
      destruct HCUR as (FR & GAP & FS & (?h0 & ?h1 & ?h2 & FH) & F3S & IS & ISL & SHF & SHL & SHT & SV & SZ & BUFS & INLS & MI & ST);

      first [ is_var x; destruct x as [?xj0 ?xj8 ?xj16 ?xj24 ?xj80 ?xj208 ?xj216 ?xj288 ?xj296] | idtac ];
      first [ is_var w; destruct w as [?w168 ?w176 ?w184 ?w224 ?w248 ?w256 ?w264] | idtac ];
      unfold ser_frameA, wkC, wkI in FR; cbn [xj0 xj8 xj16 xj24 xj80 xj208 xj216 xj288 xj296 w168 w176 w184 w224 w248 w256 w264] in FR; unfold ser_savedA in FS;
      lazymatch type of HREF with
      | SREFA _ _ _ _ ?st ?m =>
          pose proof (munch_refl (serWA E I st) m) as MU; pose proof (wmono_refl bsegs m) as WM;
          unfold serWA in MU; cbn [sa_buf sa_size sa_cap sa_heap sa_k] in MU;
          let PU := fresh "PU" in
          assert (PU : sb_pureA E st) by (apply HREF);
          let RK := fresh in let R0 := fresh "R0" in let R1 := fresh "R1" in let R3 := fresh "R3" in let BL := fresh "BL" in
          pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3);
          pose proof (sb_pureA_below E st OK PU) as BL;
          cbn [sa_buf sa_size sa_cap sa_heap sa_k] in R0, R1, R3, BL; clear PU RK;
          lazymatch type of R3 with ?T => change (boxP T) in R3 end
      end
  | SERMC _ _ _ _ _ _ _ => let x := fresh "x" in destruct HM as [x HM]; ser_open HM OK
  | SERMK _ _ _ _ _ _ _ => let x := fresh "x" in let v := fresh "x224" in destruct HM as (x & v & HM); ser_open HM OK
  | SERMH _ _ _ _ _ _ _ => let x := fresh "x" in let v := fresh "w" in destruct HM as (x & v & HM); ser_open HM OK
  end.

Ltac ser_close HM OK CX :=
  match goal with
  | HREF : SREFA ?RT ?E ?I ?Σc ?st ?mr, MU : munch _ ?mr ?m, WM : wmono _ ?mr ?m,
    FR : rw_cells _ ?m (si_b ?I) _, GAP : stk _ ?m (si_b ?I + 312) _, FS : rw_cells _ ?m (si_q ?I - 104) _,
    FH : rw_cells _ ?m (si_f ?I) [C8 ?h0; C8 ?h1; C8 ?h2], F3S : stk _ ?m (si_f ?I + 24) _,
    IS : u8arr _ ?m (si_f ?I + 304) ?isobj, ISL : length ?isobj = 16%nat,
    SHF : u8arr _ ?m (si_f ?I / 8 + 2147450880) ?shp, SHL : length ?shp = 44%nat, SHT : stk _ ?m (si_f ?I / 8 + 2147450880 + 44) _,
    SV : rw_cells _ ?m (pa_SB ?E + 64) [C8 (Z_to_bv 64 ?buf); C8 (Z_to_bv 64 ?size); C8 (Z_to_bv 64 ?cap)],
    BUFS : stk _ ?m ?buf (?buf + ?cap), INLS : stk _ ?m (pa_SB ?E) (pa_SB ?E + 64),
    MI : mem_inv _ ?m, ST : stk _ ?m (pa_lo ?E) _ |- _ =>
      let SZ' := fresh "SZc" in
      first [ assert (SZ' : 0 <= size <= sa_cap st) by (cbn [sa_cap]; lia) | fail 100 "ser_close: cannot prove 0 <= size <= cap" ];
      let x := lazymatch type of FR with
               | rw_cells _ _ _ [C8 ?a0; C8 ?a8; C8 ?a16; C8 ?a24; _; _; _; _; _; _; C8 ?a80; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; C8 ?a208; C8 ?a216;
                                _; _; _; _; _; _; _; _; C8 ?a288; C8 ?a296; _] => constr:(mkXJ a0 a8 a16 a24 a80 a208 a216 a288 a296)
               | _ => fail 100 "ser_close: the frame hypothesis FR has not the 39-word shape" end in
      let w := lazymatch type of FR with
               | rw_cells _ _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; _; C8 ?a168; C8 ?a176; C8 ?a184; _; _; _; _;
                                C8 ?a224; _; _; C8 ?a248; C8 ?a256; C8 ?a264; _; _; _; _; _] => constr:(mkWK a168 a176 a184 a224 a248 a256 a264)
               | _ => fail 100 "ser_close: the frame hypothesis FR has not the 39-word shape" end in
      first [ pose proof (SERMA_intro RT ltac:(assumption) E _ I w x shp isobj Σc st mr m size h0 h1 h2 OK CX HREF MU WM FR GAP FS FH F3S IS ISL SHF SHL SHT SV SZ' BUFS INLS MI ST) as HM
            | fail 100 "ser_close: SERMA_intro does not apply" ];
      unfold sb_sized in HM; cbn [sa_buf sa_size sa_cap sa_heap sa_k] in HM;
      clear SZ' MU WM; clear FR GAP FS FH F3S IS SHF SHT SV; try clear BUFS; try clear INLS; clear ST; clear MI; clear HREF; clear ISL; clear SHL
  | _ => fail 100 "ser_close: the open context is incomplete"
  end.

Lemma pj_sh_ok_cases : forall (b : byte) x, sh_ok b x -> b = Z_to_bv 8 0 \/ (exists k, b = Z_to_bv 8 k /\ 1 <= k <= 7 /\ x mod 8 < k).
Proof.
  intros b x [H|(H1 & H2)].
  - left. apply bv_eq. rewrite H. reflexivity.
  - right. exists (bv_unsigned b). split; [| lia]. apply bv_eq. rewrite Z_to_bv_unsigned. rewrite bv_wrap_small; [reflexivity|]. apply bv_unsigned_in_range.
Qed.
Lemma pj_sxb_small7 : forall k, 0 <= k < 128 -> sxb (Z_to_bv 8 k) = Z_to_bv 64 k.
Proof. intros k Hk. rewrite sxb_small by lia. destruct (Z.ltb_spec k 128); [reflexivity| lia]. Qed.
Lemma pj_signed_small : forall z, 0 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z H. unfold bv_signed. rewrite Z_to_bv_unsigned. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z. change (18446744073709551616 / 2)%Z with 9223372036854775808%Z.
  rewrite (Z.mod_small z) by lia. rewrite Z.mod_small by lia. lia.
Qed.
Lemma pj_land7 : forall x, 0 <= x -> Z.land x 7 = x mod 8.
Proof. intros x Hx. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma acc_read1 : forall (m : mem) a n x, acc bsegs m a n -> a <= x < a + n ->
  exists b : byte, ov_read_bytes bsegs m (wa (x / 8 + 2147450880)) 1 = Some [b] /\ sh_ok b x.
Proof.
  intros m a n x AC Hx. destruct (AC (x - a) ltac:(lia)) as (b & HB & OK). replace (a + (x - a)) with x in HB, OK by lia.
  exists b. split; [| exact OK]. unfold shad, SHB in HB.
  pose proof (bytes_at_read bsegs m _ _ 0 1 HB ltac:(lia) ltac:(cbn; lia)) as R. rewrite Z.add_0_r in R. exact R.
Qed.

