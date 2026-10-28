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
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_libiface Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit3A Atp_hkit4A Atp_hkit5A Pj_rtkA Pj_defsA Pj_cpsA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_trefA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Record conI : Type := mkCI {
  ci_q : Z;  ci_b : Z;
  ci_i : Z;  ci_e : Z;  ci_c' : Z;
  ci_R : Z;
  ci_ra : word;  ci_gp : word;
  ci_s0 : word;  ci_s1 : word;  ci_s2 : word;  ci_s3 : word;  ci_s4 : word;  ci_s5 : word;
  ci_s6 : word;  ci_s7 : word;  ci_s8 : word;  ci_s9 : word;  ci_s10 : word;  ci_s11 : word;
  ci_fr : list (Z * nat);
  ci_fr0 : list (Z * nat);
  ci_R_ : list (Z * Z);
  ci_sp0 : Z;
  ci_m0 : mem }.

Definition cr_R (C : conI) : list (Z * Z) := (ci_b C, ci_q C) :: ci_R_ C.
Definition in_R (R : list (Z * Z)) (a : Z) : Prop := exists lo hi, In (lo, hi) R /\ lo <= a < hi.

Section WithRT.
Variable RT : rt_sig.

Record cctxA (E : pjenvA) (d : nat) (C : conI) : Prop := mkCC {
  cc_b16 : ci_b C mod 16 = 0;
  cc_bq : ci_b C + 128 <= ci_q C;
  cc_lo : pa_lo E + ser_needA d <= ci_b C;
  cc_qtop : ci_q C + 16 <= USTACK_TOP;
  cc_sp0 : ci_sp0 C - STACK_WIN <= pa_lo E /\ 0x7fff80000000 <= ci_sp0 C;
  cc_e : 1 <= ci_i C /\ ci_i C < ci_e C /\ ci_e C + 1 <= pa_n E;
  cc_c' : 0 <= ci_c' C <= pa_sn E;
  cc_R : 0 <= ci_R C;
  cc_fr : exists top, ci_fr C = top ++ ci_fr0 C;
  cc_F4 : In (pa_F E, pa_kF E) (ci_fr0 C);
  cc_fr3 : fcount 3 (ci_fr C) + Z.of_nat d + 1 <= FRAMES_MAX3;
  cc_frl : Z.of_nat (length (ci_fr C)) + 2 * Z.of_nat d + 2 <= FRAMES_TOT;
  cc_L : Z.of_nat (length (pa_L E)) + 3 <= LIVE_MAX;

  cc_Rx : forall a, in_R (ci_R_ C) a ->
            (in_fframe (ci_fr C) a \/ in_fframe_shadow (ci_fr C) a) /\ ~ in_fframe (ci_fr0 C) a /\ ~ in_fframe_shadow (ci_fr0 C) a /\ a < pa_lo E }.

Definition CCREDA (E : pjenvA) (C : conI) (Σc : rts RT) (X : Z) (st : sbA) : Prop :=
  ci_R C + X + pj_psi (pa_len E) st <= rt_credit RT Σc.
Lemma CCREDA_le : forall E C Σc X X' st, CCREDA E C Σc X st -> X' <= X -> CCREDA E C Σc X' st.
Proof. intros E C Σc X X' st H HX. unfold CCREDA in *. lia. Qed.

Definition conWA (E : pjenvA) (C : conI) (st : sbA) : list (Z * Z) :=
  cr_R C ++ [(sa_buf st, sa_buf st + sa_cap st); (pa_SB E, pa_SB E + 88)].

Definition CREFA (E : pjenvA) (C : conI) (Σc : rts RT) (st : sbA) (m : mem) : Prop :=
  ART RT Σc m
  /\ rt_live RT Σc = sbchunkA st ++ pa_L E
  /\ rt_frames RT Σc = ci_fr C
  /\ rt_sp0 RT Σc = ci_sp0 C
  /\ DOCREPA E m
  /\ bytes_at bsegs m (shad (pa_SB E)) (repeat z8 11)
  /\ sb_pureA E st
  /\ rt_pres_fp (pa_L E) (ci_fr0 C) (ci_q C) [(pa_SB E, pa_SB E + 88)] (ci_m0 C) m.

Definition frp_local (C : conI) (FRP : mem -> Prop) : Prop :=
  forall m m', agree_on (in_R (cr_R C)) m m' -> FRP m -> FRP m'.

Definition CCURA (E : pjenvA) (C : conI) (FRP : mem -> Prop) (st : sbA) (m : mem) : Prop :=
  FRP m
  /\ rw_cells bsegs m (pa_SB E + 64) [C8 (wz (sa_buf st)); C8 (wz (sa_size st)); C8 (wz (sa_cap st))]
  /\ 0 <= sa_size st <= sa_cap st
  /\ stk bsegs m (sa_buf st) (sa_buf st + sa_cap st)
  /\ stk bsegs m (pa_SB E) (pa_SB E + 64)
  /\ mem_inv bsegs m
  /\ stk bsegs m (pa_lo E) (ci_b C).

Definition CERMA (E : pjenvA) (C : conI) (FRP : mem -> Prop) (Σc : rts RT) (st : sbA) (m : mem) : Prop :=
  CREFA E C Σc st m /\ CCURA E C FRP st m.
End WithRT.

Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Hypothesis GROW : grow_cpsA RT PMc.
Notation aevt := (aevt RT PMc).
Local Ltac dlia := Z.div_mod_to_equations; lia.

Lemma outside_app2 : forall (W1 W2 : list (Z * Z)) a, outside W1 a -> outside W2 a -> outside (W1 ++ W2) a.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a H1 H2; [exact H2|]. cbn [outside app] in H1 |- *. destruct H1 as [A B]. split; [exact A| apply IH; assumption]. Qed.
Lemma outside_app_l : forall (W1 W2 : list (Z * Z)) a, outside (W1 ++ W2) a -> outside W1 a /\ outside W2 a.
Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 a H; [exact (conj Logic.I H)|]. cbn [outside app] in H |- *. destruct H as [A B]. destruct (IH _ _ B) as [C D]. exact (conj (conj A C) D). Qed.

Lemma in_R_cons : forall lo hi R a, in_R ((lo, hi) :: R) a <-> (lo <= a < hi \/ in_R R a).
Proof.
  intros lo hi R a. unfold in_R. split.
  - intros (l & h & [E|Hin] & Ha); [inversion E; subst; left; exact Ha| right; exists l, h; exact (conj Hin Ha)].
  - intros [Ha|(l & h & Hin & Ha)]; [exists lo, hi; split; [left; reflexivity| exact Ha]| exists l, h; split; [right; exact Hin| exact Ha]].
Qed.

Lemma bytes_le_to_Z_range : forall bs : list byte, (0 <= bytes_le_to_Z bs < 2^(8 * Z.of_nat (length bs)))%Z.
Proof.
  induction bs as [|b bs IH]; cbn [bytes_le_to_Z length]; [cbn; lia|].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  assert (Hs : (0 <= Z.shiftl (bytes_le_to_Z bs) 8)%Z) by (apply Z.shiftl_nonneg; lia).
  split. { apply Z.lor_nonneg. lia. }
  pose proof (Z.add_lor_land (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as E.
  pose proof (Z.land_nonneg (bv_unsigned b) (Z.shiftl (bytes_le_to_Z bs) 8)) as L.
  rewrite Z.shiftl_mul_pow2 in * by lia.
  replace (2 ^ (8 * Z.of_nat (S (length bs))))%Z with (2^8 * 2 ^ (8 * Z.of_nat (length bs)))%Z.
  2:{ rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  nia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
  induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
  pose proof (bv_unsigned_in_range 8 b) as Hb. unfold bv_modulus in Hb. change (2^Z.of_N 8)%Z with (2^8)%Z in Hb.
  pose proof (bytes_le_to_Z_range bs) as HR.
  f_equal.
  - apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z.
    rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l.
    replace (Z.land (Z.shiftl (bytes_le_to_Z bs) 8) (Z.ones 8)) with 0%Z.
    2:{ symmetry. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
        destruct (Z.ltb_spec0 i 8).
        - rewrite Z.shiftl_spec_low by lia. reflexivity.
        - rewrite Z.ones_spec_high by lia. apply andb_false_r. }
    rewrite Z.lor_0_r, Z.land_ones by lia. apply Z.mod_small. lia.
  - rewrite Z.shiftr_lor, Z.shiftr_shiftl_l, Z.sub_diag, Z.shiftl_0_r by lia.
    rewrite (Z.shiftr_div_pow2 _ 8), Z.div_small by lia.
    rewrite Z.lor_0_l. exact IH.
Qed.

Lemma le8_of_bytes : forall bs : list byte, length bs = 8%nat -> le8 (le_bytes_to_word bs) = bs.
Proof.
  intros bs HL. unfold le8, word_to_le_bytes, le_bytes_to_word.
  pose proof (bytes_le_to_Z_range bs) as HR. rewrite HL in HR. change (2 ^ (8 * Z.of_nat 8))%Z with (2^64)%Z in HR.
  rewrite unsigned_lit by lia. rewrite <- HL. apply Z_to_le_bytes_to_Z.
Qed.
Definition c8c (c : cell) : cell := match c with CB n bs => if Nat.eqb n 8 then C8 (le_bytes_to_word bs) else c | _ => c end.
Lemma c8ify_ok : forall cs, cells_wf cs ->
  cells_wf (map c8c cs) /\ cells_bytes (map c8c cs) = cells_bytes cs /\ cells_size (map c8c cs) = cells_size cs.
Proof.
  induction cs as [|c cs IH]; intros Hwf; [repeat split; reflexivity|].
  destruct Hwf as [Hc Hcs]. destruct (IH Hcs) as (W & B & S).
  destruct c as [v|v|v|b|n bs]; cbn [map c8c cells_wf cells_bytes cells_size]; try (rewrite B, S; repeat split; auto; fail).
  destruct (Nat.eqb_spec n 8) as [->|NE]; cbn [cells_wf cells_bytes cells_size cbytes csize cell_wf]; rewrite B, S.
  - cbn in Hc. rewrite (le8_of_bytes bs Hc). repeat split; auto.
  - repeat split; auto.
Qed.
Lemma rw_cells_c8ify : forall (m : mem) A cs, rw_cells bsegs m A cs -> rw_cells bsegs m A (map c8c cs).
Proof.
  intros m A cs [[Hwf Hb] Hw]. destruct (c8ify_ok cs Hwf) as (W & B & S).
  split; [split; [exact W| rewrite B; exact Hb]| rewrite S; exact Hw].
Qed.

Lemma pa_n_32C : forall E, pjenvA_ok E -> pa_n E + 2 < 2^32.
Proof.
  intros E OK. pose proof (ok_sizes E OK) as [HT _]. pose proof (ok_len E OK) as HL.
  unfold SJ_TAPE, roundup64, sj_cap, SJ_PADMAX in *. Z.div_mod_to_equations. lia.
Qed.

Lemma cctx_out : forall E D C, pjenvA_ok E -> cctxA E D C -> 41 * ci_e C + 6 * ci_c' C + 2 <= PJ_OUTMAX (pa_len E).
Proof.
  intros E D C OK CX. pose proof (ok_sizes E OK) as [HT HS]. pose proof (cc_e E D C CX). pose proof (cc_c' E D C CX).
  replace (ci_e C) with (ci_e C + 1 - 1) by lia.
  eapply (pj_out_bound (pa_len E) (pa_n E) (pa_sn E) (ci_e C + 1) (ci_c' C)); [apply (ok_len E OK)| exact HT| exact HS| lia| lia| lia].
Qed.

Lemma cr_R_facts : forall E D C Σc st m a, pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st m -> in_R (cr_R C) a ->
  (forall L, aclient L (rt_frames RT Σc) (ci_b C) a)
  /\ ~ (pa_SB E <= a < pa_SB E + 88) /\ ~ (shad (pa_SB E) <= a < shad (pa_SB E) + 11) /\ ~ docrep_rng E a
  /\ ~ (sa_buf st <= a < sa_buf st + sa_cap st)
  /\ ~ aclient (pa_L E) (ci_fr0 C) (ci_q C) a.
Proof using AF.
  intros E D C Σc st m a OK CX (ART0 & LV & FR & SP & _ & _ & PU & _) Ha.
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3). pose proof (sb_pureA_below E st OK PU) as BL.
  pose proof (cc_qtop E D C CX) as QT. pose proof (cc_bq E D C CX) as BQ. pose proof (cc_lo E D C CX) as LOB. pose proof (cc_sp0 E D C CX) as [W1 W2].
  pose proof (cc_F4 E D C CX) as IN4. destruct (cc_fr E D C CX) as (top & EFR).
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR, EFR; apply in_or_app; right; exact IN4).
  unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOB.
  destruct (fs_size_64 (pa_kF E)) as (qF & EFS & QF1).
  unfold cr_R in Ha. apply in_R_cons in Ha. destruct Ha as [Ha|Ha].
  -
    split; [intros L; left; unfold USTACK_TOP in *; lia|].
    split; [clear - Ha LOB B2 FL; lia|]. split; [unfold shad, SHB; clear - Ha LOB B2 FL LO; dlia|].
    split. { unfold docrep_rng, shad, SHB. clear - Ha LOB D1 D2 FL LO TL SL T0 S0. intros [H|[H|[H|H]]]; first [lia| dlia]. }
    split; [clear - Ha LOB BL; lia|].
    intros CA. destruct (aclient_split_c RT AF Σc m (ci_q C) a ART0) as [H|H].
    + eapply aclient_mono; [exact CA| rewrite LV; intros e He; apply in_or_app; right; exact He| rewrite FR, EFR; intros e He; apply in_or_app; right; exact He| lia].
    + clear - H Ha; lia.
    + rewrite SP in H. clear - H Ha W1 LOB; lia.
  - pose proof (cc_Rx E D C CX a Ha) as (CL & NF & NS & ALO).
    assert (CA : forall L, aclient L (rt_frames RT Σc) (ci_b C) a).
    { intros L. rewrite FR. destruct CL as [CL|CL]; [right; right; right; left; exact CL| right; right; right; right; exact CL]. }
    split; [exact CA|].
    split. { intros H. apply NF. exists (pa_F E), (pa_kF E). split; [exact IN4| clear - H B1 B2; lia]. }
    split. { intros H. apply NS. exists (pa_F E), (pa_kF E). split; [exact IN4|]. unfold shad, SHB in H |- *.
             clear - H B1 B2 EFS QF1 F64 B32. Z.div_mod_to_equations. lia. }
    split. { pose proof (ok_tape E OK) as (_ & TN & _ & _ & INT). pose proof (ok_sbuf E OK) as (_ & SN & _ & _ & INS).
             assert (INT' : In (pa_TAPE E, pa_NT E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INT).
             assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
             unfold docrep_rng. intros [H|[H|[H|H]]].
             - apply NF. exists (pa_F E), (pa_kF E). split; [exact IN4| clear - H D1 D2; lia].
             - apply NS. exists (pa_F E), (pa_kF E). split; [exact IN4|]. unfold shad, SHB in H |- *. clear - H D1 D2 EFS QF1 F64 D8. Z.div_mod_to_equations. lia.
             - destruct CL as [(f & k & Hin & Hf)|(f & k & Hin & Hf)].
               + pose proof (af_frames_range RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) as (_ & _ & _ & CH). specialize (CH _ _ INT'). clear - H Hf CH TN. lia.
               + pose proof (proj1 (af_fshadow_apart RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) _ _ INT') as CH. clear - H Hf CH TN. lia.
             - destruct CL as [(f & k & Hin & Hf)|(f & k & Hin & Hf)].
               + pose proof (af_frames_range RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) as (_ & _ & _ & CH). specialize (CH _ _ INS'). clear - H Hf CH SN. lia.
               + pose proof (proj1 (af_fshadow_apart RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) _ _ INS') as CH. clear - H Hf CH SN. lia. }
    split. { destruct R3 as [(BL' & HP)|(EB & EC & HP)].
             - assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
               destruct CL as [(f & k & Hin & Hf)|(f & k & Hin & Hf)].
               + pose proof (af_frames_range RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) as (_ & _ & _ & CH). specialize (CH _ _ INB). clear - Hf CH. lia.
               + pose proof (proj1 (af_fshadow_apart RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) _ _ INB) as CH. clear - Hf CH. lia.
             - rewrite EB, EC. intros H. apply NF. exists (pa_F E), (pa_kF E). split; [exact IN4| clear - H B1 B2; lia]. }
    intros [H|[H|[H|[H|H]]]].
    + clear - H ALO LOB BQ. lia.
    + pose proof (client_static_range a H) as SR. destruct CL as [(f & k & Hin & Hf)|(f & k & Hin & Hf)].
      * pose proof (af_frames_range RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) as (F0 & _ & FSG & _).
        pose proof (af_frames_align RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) as [_ FSA]. clear - SR Hf FSA. unfold SEGTOP_A in *. lia.
      * pose proof (af_frames_align RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hin)) as [_ FSA]. unfold shad, SHB, SEGTOP_A in *. clear - SR Hf FSA. dlia.
    + destruct H as (p & n & Hin & Hp). assert (Hin' : In (p, n) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact Hin).
      destruct CL as [(f & k & Hinf & Hf)|(f & k & Hinf & Hf)].
      * pose proof (af_frames_range RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hinf)) as (_ & _ & _ & CH). specialize (CH _ _ Hin'). clear - Hp Hf CH. lia.
      * pose proof (proj1 (af_fshadow_apart RT AF Σc m f k ART0 ltac:(rewrite FR; exact Hinf)) _ _ Hin') as CH. clear - Hp Hf CH. lia.
    + exact (NF H).
    + exact (NS H).
Qed.

Lemma conWA_client : forall E D C Σc st m a, pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st m ->
  ~ aclient (rt_live RT Σc) (rt_frames RT Σc) (ci_b C) a -> outside (conWA E C st) a.
Proof using AF.
  intros E D C Σc st m a OK CX HR NA. pose proof HR as (ART0 & LV & FR & SP & _ & _ & PU & _).
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (cc_F4 E D C CX) as IN4. destruct (cc_fr E D C CX) as (top & EFR).
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR, EFR; apply in_or_app; right; exact IN4).
  assert (OR : forall R, (forall x, in_R R x -> aclient (rt_live RT Σc) (rt_frames RT Σc) (ci_b C) x) -> outside R a).
  { induction R as [|[lo hi] R IH]; intros HR'; [exact Logic.I|]. cbn [outside]. split.
    - intros H. apply NA. apply HR'. apply in_R_cons. left. exact H.
    - apply IH. intros x Hx. apply HR'. apply in_R_cons. right. exact Hx. }
  unfold conWA. apply outside_app2.
  - apply OR. intros x Hx. exact (proj1 (cr_R_facts E D C Σc st m x OK CX HR Hx) (rt_live RT Σc)).
  - cbn [outside]. split; [| split; [| exact Logic.I]].
    + intros H. apply NA. destruct R3 as [(BL & HP)|(EB & EC & HP)].
      * right; right; left. exists (sa_buf st), (sa_cap st). split; [rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity| lia].
      * right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| lia].
    + intros H. apply NA. right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| lia].
Qed.

Lemma docrep_apart_bufA : forall E Σc st m y, pjenvA_ok E -> ART RT Σc m -> rt_live RT Σc = sbchunkA st ++ pa_L E ->
  In (pa_F E, pa_kF E) (rt_frames RT Σc) -> sb_pureA E st -> docrep_rng E y ->
  ~ (sa_buf st <= y < sa_buf st + sa_cap st) /\ ~ (pa_SB E <= y < pa_SB E + 88).
Proof using AF.
  intros E Σc st m y OK ART0 LV INF4 PU HX.
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & S0 & SL & S16 & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (ok_tape E OK) as (_ & TN & _ & _ & INT). pose proof (ok_sbuf E OK) as (_ & SN & _ & _ & INS).
  destruct (fs_size_64 (pa_kF E)) as (qF & EFS & QF1).
  assert (INT' : In (pa_TAPE E, pa_NT E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INT).
  assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
  pose proof (af_frames_range RT AF Σc m _ _ ART0 INF4) as (_ & _ & _ & F4CH).
  pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4)) as F4SH.
  pose proof (proj2 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4) _ _ INF4) as F4SF.
  pose proof (F4CH _ _ INT') as A1. pose proof (F4CH _ _ INS') as A2. pose proof (F4SH _ _ INT') as A5. pose proof (F4SH _ _ INS') as A6.
  unfold docrep_rng in HX. split.
  - destruct R3 as [(BL & HP)|(EB & EC & HP)].
    + assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
      pose proof (F4CH _ _ INB) as C1. pose proof (F4SH _ _ INB) as C2.
      assert (LVE : rt_live RT Σc = [] ++ (sa_buf st, sa_cap st) :: pa_L E) by (rewrite LV; unfold sbchunkA; rewrite HP; reflexivity).
      pose proof (af_live_disj RT AF Σc m _ _ _ _ [] (pa_L E) ART0 LVE INT) as C3.
      pose proof (af_live_disj RT AF Σc m _ _ _ _ [] (pa_L E) ART0 LVE INS) as C4.
      destruct HX as [H|[H|[H|H]]]; [clear - H C1 D1 D2; lia| unfold shad, SHB in H, C2; clear - H C2 D1 D2 EFS QF1 F64 D8; Z.div_mod_to_equations; lia
                                   | clear - H C3 TN; lia| clear - H C4 SN; lia].
    + rewrite EB, EC. destruct HX as [H|[H|[H|H]]]; [clear - H AP; lia| unfold shad, SHB in H, F4SF; clear - H F4SF D1 D2 B1 B2 EFS QF1 F64 D8; Z.div_mod_to_equations; lia
                                                   | clear - H A1 B1 B2 TN; lia| clear - H A2 B1 B2 SN; lia].
  - destruct HX as [H|[H|[H|H]]]; [clear - H AP; lia| unfold shad, SHB in H, F4SF; clear - H F4SF D1 D2 B1 B2 EFS QF1 F64 D8; Z.div_mod_to_equations; lia
                                 | clear - H A1 B1 B2 TN; lia| clear - H A2 B1 B2 SN; lia].
Qed.

Lemma docrep_outsideC : forall E D C Σc st m x, pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st m -> docrep_rng E x -> outside (conWA E C st) x.
Proof using AF.
  intros E D C Σc st m x OK CX HR HX. pose proof HR as (ART0 & LV & FR & SP & _ & _ & PU & _).
  pose proof (cc_F4 E D C CX) as IN4. destruct (cc_fr E D C CX) as (top & EFR).
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR, EFR; apply in_or_app; right; exact IN4).
  destruct (docrep_apart_bufA E Σc st m x OK ART0 LV INF4 PU HX) as [N1 N2].
  unfold conWA. apply outside_app2.
  - assert (OR : forall R, (forall y, in_R R y -> ~ docrep_rng E y) -> outside R x).
    { induction R as [|[lo hi] R IH]; intros HR'; [exact Logic.I|]. cbn [outside]. split.
      - intros H. apply (HR' x); [apply in_R_cons; left; exact H| exact HX].
      - apply IH. intros y Hy. apply HR'. apply in_R_cons. right. exact Hy. }
    apply OR. intros y Hy. exact (proj1 (proj2 (proj2 (proj2 (cr_R_facts E D C Σc st m y OK CX HR Hy))))).
  - cbn [outside]. exact (conj N1 (conj N2 Logic.I)).
Qed.

Lemma ART_muC : forall E D C Σc st m m', pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st m -> munch (conWA E C st) m m' -> wmono bsegs m m' -> ART RT Σc m'.
Proof using AF.
  intros E D C Σc st m m' OK CX HR MU WM. pose proof HR as (ART0 & _ & _ & SP & _).
  pose proof (cc_sp0 E D C CX) as [W1 W2]. pose proof (cc_lo E D C CX) as LOB. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOB.
  apply (art_client_write RT AF Σc m m' (ci_b C) ART0); [rewrite SP; lia| | exact WM].
  intros a Ha. apply MU. eapply conWA_client; eassumption.
Qed.

Lemma CREFA_munch : forall E D C Σc st m m' n, pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st m ->
  munch (conWA E C st) m m' -> wmono bsegs m m' -> CREFA RT E C Σc (sb_sized st n) m'.
Proof using AF.
  intros E D C Σc st m m' n OK CX HR MU WM. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES).
  unfold CREFA. rewrite sbchunk_sized, sb_pureA_sized.
  split; [eapply ART_muC; eassumption|]. split; [exact LV|]. split; [exact FR|]. split; [exact SP|].
  split. { eapply DOCREPA_agree; [exact DR|]. eapply agree_of_munch; [exact MU|]. intros x Hx. eapply docrep_outsideC; eassumption. }
  split. { eapply bytes_at_agree; [exact SBSH|]. eapply agree_of_munch; [exact MU|]. intros x Hx. rewrite repeat_length in Hx.
           unfold conWA. apply outside_app2.
           - assert (OR : forall R, (forall y, in_R R y -> ~ (shad (pa_SB E) <= y < shad (pa_SB E) + 11)) -> outside R x).
             { induction R as [|[lo hi] R IH]; intros HR'; [exact Logic.I|]. cbn [outside]. split.
               - intros H. apply (HR' x); [apply in_R_cons; left; exact H| exact Hx].
               - apply IH. intros y Hy. apply HR'. apply in_R_cons. right. exact Hy. }
             apply OR. intros y Hy. exact (proj1 (proj2 (proj2 (cr_R_facts E D C Σc st m y OK CX HR Hy)))).
           - pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & B32 & F64 & FS & B1 & B2 & _ & _ & FL & LO & _).
             pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & _ & R3).
             pose proof (cc_F4 E D C CX) as IN4. destruct (cc_fr E D C CX) as (top & EFR).
             assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR, EFR; apply in_or_app; right; exact IN4).
             pose proof (proj2 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4) _ _ INF4) as F4SF.
             destruct (fs_size_64 (pa_kF E)) as (qF & EFS & QF1).
             cbn [outside]. split; [| split; [| exact Logic.I]].
             + destruct R3 as [(BL & HP)|(EB & EC & HP)].
               * pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4) (sa_buf st) (sa_cap st) ltac:(rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity)) as C2.
                 unfold shad, SHB in Hx, C2 |- *. clear - Hx C2 B1 B2 EFS QF1 F64 B32. Z.div_mod_to_equations. lia.
               * rewrite EB, EC. unfold shad, SHB in Hx, F4SF |- *. clear - Hx F4SF B1 B2 EFS QF1 F64 B32. Z.div_mod_to_equations. lia.
             + unfold shad, SHB in Hx, F4SF |- *. clear - Hx F4SF B1 B2 EFS QF1 F64 B32. Z.div_mod_to_equations. lia. }
  split; [exact PU|].
  intros a CA OUT. rewrite <- (PRES a CA OUT). apply MU.
  unfold conWA. apply outside_app2.
  - assert (OR : forall R, (forall y, in_R R y -> ~ aclient (pa_L E) (ci_fr0 C) (ci_q C) y) -> outside R (bv_unsigned a)).
    { induction R as [|[lo hi] R IH]; intros HR'; [exact Logic.I|]. cbn [outside]. split.
      - intros H. apply (HR' (bv_unsigned a)); [apply in_R_cons; left; exact H| exact CA].
      - apply IH. intros y Hy. apply HR'. apply in_R_cons. right. exact Hy. }
    apply OR. intros y Hy. exact (proj2 (proj2 (proj2 (proj2 (proj2 (cr_R_facts E D C Σc st m y OK CX HR Hy)))))).
  - cbn [outside] in OUT |- *. destruct OUT as [O1 _]. split; [| split; [exact O1| exact Logic.I]].
    pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & _ & R3). pose proof (cc_sp0 E D C CX) as [W1 _]. pose proof (cc_lo E D C CX) as LOB. pose proof (cc_bq E D C CX) as BQ.
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
    destruct R3 as [(BL & HP)|(EB & EC & HP)]; [| rewrite EB, EC; clear - O1; lia].
    pose proof (cc_F4 E D C CX) as IN4. destruct (cc_fr E D C CX) as (top & EFR). unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOB.
    intros Hb. refine (fresh_apart_l RT AF Σc m [(sa_buf st, sa_cap st)] (pa_L E) (sa_buf st) (sa_cap st) (ci_q C) (bv_unsigned a) ART0 _ ltac:(left; reflexivity) _ _ Hb).
    + rewrite LV. unfold sbchunkA. rewrite HP. reflexivity.
    + rewrite SP. clear - W1 LOB BQ. lia.
    + eapply aclient_mono; [exact CA| intros e He; exact He| rewrite FR, EFR; intros e He; apply in_or_app; right; exact He| clear; lia].
Qed.

Lemma le8_le4 : forall v, firstn 4 (le8 v) = le4 v.
Proof. intros v. unfold le8, le4, word_to_le_bytes. reflexivity. Qed.
Lemma tape_read4 : forall m TAPE (tws : list Z) (i : Z),
  bytes_at bsegs m TAPE (u64s (map (Z_to_bv 64) tws)) -> 0 <= i < Z.of_nat (length tws) ->
  ov_read_bytes bsegs m (wa (TAPE + 8 * i)) 4 = Some (le4 (Z_to_bv 64 (Tf tws i))).
Proof.
  intros m TAPE tws i HB Hi.
  rewrite (bytes_at_read bsegs m TAPE _ (8 * i) 4 HB); [| lia| rewrite u64s_length, length_map; lia].
  f_equal. rewrite <- le8_le4.
  assert (E8 : firstn 8 (skipn (8 * Z.to_nat i) (u64s (map (Z_to_bv 64) tws))) = le8 (Z_to_bv 64 (Tf tws i))).
  { rewrite u64s_read by (rewrite length_map; lia). f_equal. unfold Tf. apply (map_nth (Z_to_bv 64)). }
  rewrite <- E8. replace (Z.to_nat (8 * i)) with (8 * Z.to_nat i)%nat by lia.
  rewrite firstn_firstn. reflexivity.
Qed.
Lemma zx32_tnext : forall w, 0 <= w < 2^64 -> zx32 (Z_to_bv 64 w) = Z_to_bv 64 (tnext w).
Proof. intros w H. unfold zx32, tnext. f_equal. rewrite unsigned_lit by lia. reflexivity. Qed.
Lemma land7_mod8_0 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2 ^ 3) with 8. exact H. Qed.

Section Mu.
  Variables (E : pjenvA) (D : nat) (C : conI).
  Hypothesis OK : pjenvA_ok E.
  Hypothesis CX : cctxA E D C.

  Lemma tape_read_muC : forall Σc st mr m i, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m ->
    0 <= i < pa_n E -> ov_read_bytes bsegs m (wa (pa_TAPE E + 8 * i)) 8 = Some (le8 (Z_to_bv 64 (pa_T E i))).
  Proof using AF OK CX.
    intros Σc st mr m i HR MU WM Hi.
    pose proof (CREFA_munch E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & _ & TB & _) & _). apply tape_read; assumption.
  Qed.
  Lemma tape_read7_muC : forall Σc st mr m i, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m ->
    0 <= i < pa_n E -> 0 <= pa_T E i < 2^64 -> ov_read_bytes bsegs m (wa (pa_TAPE E + (8 * i + 7))) 1 = Some [Z_to_bv 8 (ttype (pa_T E i))].
  Proof using AF OK CX.
    intros Σc st mr m i HR MU WM Hi HW.
    pose proof (CREFA_munch E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & _ & TB & _) & _). apply tape_read7; assumption.
  Qed.
  Lemma tape_read4_muC : forall Σc st mr m i, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m ->
    0 <= i < pa_n E -> ov_read_bytes bsegs m (wa (pa_TAPE E + 8 * i)) 4 = Some (le4 (Z_to_bv 64 (pa_T E i))).
  Proof using AF OK CX.
    intros Σc st mr m i HR MU WM Hi.
    pose proof (CREFA_munch E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & _ & TB & _) & _). apply tape_read4; assumption.
  Qed.
  Lemma doc_cells_muC : forall Σc st mr m, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m ->
    rw_cells bsegs m (pa_DOC E) [C8 (Z_to_bv 64 (pa_TAPE E)); C8 (Z_to_bv 64 (pa_SBUF E))].
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (CREFA_munch E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (DC & _) & _). exact DC.
  Qed.
  Lemma shz_sb_muC : forall Σc st mr m, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m -> shz m (pa_SB E) 88.
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (CREFA_munch E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & _ & SH & _).
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & B32 & _ & FS & B1 & _). unfold SEGTOP_A in FS.
    apply (shz_of_zero_run m (pa_SB E) 11); [clear - B32; dlia| clear - FS B1; lia| exact SH].
  Qed.
  Lemma shz_doc_muC : forall Σc st mr m, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m -> shz m (pa_DOC E) 16.
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (CREFA_munch E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (_ & _ & _ & _ & (_ & SH & _) & _).
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & D8 & _ & _ & FS & _ & _ & D1 & _). unfold SEGTOP_A in FS.
    apply (shz_of_zero_run m (pa_DOC E) 2); [exact D8| clear - FS D1; lia| exact SH].
  Qed.
  Lemma shz_tape_muC : forall Σc st mr m, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m -> shz m (pa_TAPE E) (8 * pa_n E).
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (CREFA_munch E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _). pose proof HR as (_ & LV & _).
    pose proof (ok_tape E OK) as (T16 & TN & T0 & _ & INT).
    assert (INT' : In (pa_TAPE E, pa_NT E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INT).
    pose proof (shz_live RT AF Σc m _ _ ART1 INT' ltac:(clear - T16; dlia)) as SH.
    eapply shz_sub; [exact SH| lia| clear - TN; dlia].
  Qed.
  Lemma acc_buf_muC : forall Σc st mr m, CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m -> acc bsegs m (sa_buf st) (sa_cap st).
  Proof using AF OK CX.
    intros Σc st mr m HR MU WM.
    pose proof (CREFA_munch E D C Σc st mr m (sa_size st) OK CX HR MU WM) as (ART1 & _ & _ & _ & _ & SH & _).
    pose proof HR as (_ & LV & _ & _ & _ & _ & PU & _).
    pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & B32 & _ & FS & B1 & _). unfold SEGTOP_A in FS.
    destruct R3 as [(BL & HP)|(EB & EC & HP)].
    - apply (proj2 (af_acc_live RT AF Σc m (sa_buf st) (sa_cap st) ART1 ltac:(rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity))).
    - rewrite EB, EC. eapply (acc_sub bsegs); [apply (acc_zero_run bsegs m (pa_SB E) 11); [clear - B32; dlia| clear - FS B1; lia| exact SH]| lia| lia].
  Qed.

  Lemma buf_factsC : forall Σc st m, CREFA RT E C Σc st m ->
    sa_buf st + sa_cap st <= pa_lo E /\ 0 < sa_buf st
    /\ (forall n, 0 <= n <= sa_cap st -> rng_class RT Σc (sa_buf st) n)
    /\ (forall y, sa_buf st <= y < sa_buf st + sa_cap st -> aclient (rt_live RT Σc) (rt_frames RT Σc) (ci_b C) y)
    /\ (forall y, sa_buf st <= y < sa_buf st + sa_cap st -> ~ in_R (cr_R C) y /\ ~ (pa_SB E + 64 <= y < pa_SB E + 88) /\ ~ (shad (pa_SB E) <= y < shad (pa_SB E) + 11)).
  Proof using AF OK CX.
    intros Σc st m HR. pose proof HR as (ART0 & LV & FR & SP & _ & _ & PU & _).
    pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3). pose proof (sb_pureA_below E st OK PU) as BL.
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & B32 & F64 & FS & B1 & B2 & _ & _ & FL & LO & _).
    pose proof (cc_F4 E D C CX) as IN4. destruct (cc_fr E D C CX) as (top & EFR).
    assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σc)) by (rewrite FR, EFR; apply in_or_app; right; exact IN4).
    pose proof (proj2 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4) _ _ INF4) as F4SF. destruct (fs_size_64 (pa_kF E)) as (qF & EFS & QF1).
    split; [exact BL|]. split; [exact R0|].
    destruct R3 as [(BL' & HP)|(EB & EC & HP)].
    - assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σc)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
      pose proof (af_frames_range RT AF Σc m _ _ ART0 INF4) as (_ & _ & _ & F4CH). specialize (F4CH _ _ INB).
      pose proof (proj1 (af_fshadow_apart RT AF Σc m _ _ ART0 INF4) _ _ INB) as F4SH.
      split. { intros n Hn. left. exists (sa_buf st), (sa_cap st). split; [exact INB| clear - Hn; lia]. }
      split. { intros y Hy. right; right; left. exists (sa_buf st), (sa_cap st). split; [exact INB| clear - Hy; lia]. }
      intros y Hy. split; [| split; [clear - Hy F4CH B1 B2; lia| unfold shad, SHB in F4SH |- *; clear - Hy F4SH B1 B2 EFS QF1 F64 B32; Z.div_mod_to_equations; lia]].
      intros HRy. exact (proj1 (proj2 (proj2 (proj2 (proj2 (cr_R_facts E D C Σc st m y OK CX HR HRy))))) Hy).
    - rewrite EB, EC.
      split. { intros n Hn. right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - B1 B2 Hn; lia]. }
      split. { intros y Hy. right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - B1 B2 Hy; lia]. }
      intros y Hy. split; [| split; [clear - Hy; lia| unfold shad, SHB in F4SF |- *; clear - Hy F4SF B1 B2 EFS QF1 F64 B32; Z.div_mod_to_equations; lia]].
      intros HRy. apply (proj1 (proj2 (cr_R_facts E D C Σc st m y OK CX HR HRy))). clear - Hy. lia.
  Qed.
End Mu.

Lemma CERMA_intro : forall E D C FRP Σc st mr m size,
  pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st mr -> munch (conWA E C st) mr m -> wmono bsegs mr m ->
  FRP m ->
  rw_cells bsegs m (pa_SB E + 64) [C8 (wz (sa_buf st)); C8 (wz size); C8 (wz (sa_cap st))] -> 0 <= size <= sa_cap st ->
  stk bsegs m (sa_buf st) (sa_buf st + sa_cap st) -> stk bsegs m (pa_SB E) (pa_SB E + 64) ->
  mem_inv bsegs m -> stk bsegs m (pa_lo E) (ci_b C) ->
  CERMA RT E C FRP Σc (sb_sized st size) m.
Proof using AF.
  intros until size. intros OK CX HR MU WM HF SV SZ BUFS INLS MI ST.
  split; [eapply CREFA_munch; eassumption|].
  unfold CCURA. destruct st as [buf sz cap hp k]. cbn [sb_sized sa_buf sa_size sa_cap sa_heap sa_k] in *.
  repeat (split; [assumption|]). assumption.
Qed.

Lemma SBINVA_of_CERMA : forall E D C FRP Σc st m, pjenvA_ok E -> cctxA E D C -> CERMA RT E C FRP Σc st m -> SBINVA E m st.
Proof.
  intros until m. intros OK CX [(_ & _ & _ & _ & _ & SBSH & (PK & PH) & _) HC]. destruct HC as (_ & SV & SZ & BUFS & INLS & _ & _).
  pose proof (sb_pureA_ranges E st OK (conj PK PH)) as (R0 & R1 & _).
  unfold SBINVA. split; [exact SV|]. split; [exact SZ|].
  split. { destruct (stk_CB bsegs m _ _ BUFS ltac:(lia)) as (bs & HBS). exists bs. replace (sa_buf st + sa_cap st - sa_buf st) with (sa_cap st) in HBS by lia. exact HBS. }
  split. { destruct (stk_CB bsegs m _ _ INLS ltac:(lia)) as (bs & HBS). exists bs. replace (Z.to_nat (pa_SB E + 64 - pa_SB E)) with 64%nat in HBS by lia. exact HBS. }
  split; [exact SBSH|]. split; [exact PK| exact PH].
Qed.

Lemma pa_live_of_CERMA : forall E D C FRP Σc st m, cctxA E D C -> CERMA RT E C FRP Σc st m -> pa_live RT Σc E st.
Proof.
  intros until m. intros CX [(_ & LV & FR & SP & _) _]. split; [exact LV|]. split.
  - rewrite FR. destruct (cc_fr E D C CX) as (top & ->). apply in_or_app. right. exact (cc_F4 E D C CX).
  - rewrite SP. exact (proj1 (cc_sp0 E D C CX)).
Qed.

Lemma CERMA_after_call : forall E D C FRP Σ Σ' st st' m m' W,
  pjenvA_ok E -> cctxA E D C -> frp_local C FRP -> CERMA RT E C FRP Σ st m ->
  (forall x, outside (conWA E C st) x -> outside W x) ->
  (forall x, in_R (cr_R C) x -> outside W x) ->
  rt_pres_fp (pa_L E) (rt_frames RT Σ) (ci_b C) W m m' ->
  ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (pa_lo E) (ci_b C) ->
  rt_live RT Σ' = sbchunkA st' ++ pa_L E -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
  sb_pureA E st' -> bytes_at bsegs m' (shad (pa_SB E)) (repeat z8 11) ->
  rw_cells bsegs m' (pa_SB E + 64) [C8 (wz (sa_buf st')); C8 (wz (sa_size st')); C8 (wz (sa_cap st'))] -> 0 <= sa_size st' <= sa_cap st' ->
  stk bsegs m' (sa_buf st') (sa_buf st' + sa_cap st') -> stk bsegs m' (pa_SB E) (pa_SB E + 64) ->
  CERMA RT E C FRP Σ' st' m'.
Proof using AF.
  intros until W. intros OK CX LOC HSM SUB SPARE PRES ART' MI' ST' LV' FR' SP' PU' SBSH' SV' SZ' BUFS' INLS'.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0). pose proof HC as (HF & _).
  pose proof (cc_F4 E D C CX) as IN4. destruct (cc_fr E D C CX) as (top & EFR). pose proof (cc_bq E D C CX) as BQ.
  assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FR, EFR; apply in_or_app; right; exact IN4).
  pose proof (ok_tape E OK) as (_ & TN & _ & _ & INT). pose proof (ok_sbuf E OK) as (_ & SN & _ & _ & INS).
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & _). destruct (fs_size_64 (pa_kF E)) as (qF & EFS & QF1).
  pose proof (agree_of_pres_fp _ _ _ _ _ _ (fun x => aclient (pa_L E) (rt_frames RT Σ) (ci_b C) x /\ outside W x) PRES ltac:(intros x Hx; exact Hx)) as AG.
  split.
  - unfold CREFA. split; [exact ART'|]. split; [exact LV'|]. split; [rewrite FR'; exact FR|]. split; [rewrite SP'; exact SP|].
    split. { eapply DOCREPA_agree; [exact DR|]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
             split; [| apply SUB; eapply docrep_outsideC; eassumption].
             destruct Hx as [Hx|[Hx|[Hx|Hx]]].
             - right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx D1 D2; lia].
             - right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hx |- *. clear - Hx D1 D2 D8 F64 EFS QF1. Z.div_mod_to_equations. lia.
             - right; right; left. exists (pa_TAPE E), (pa_NT E). split; [exact INT| clear - Hx TN; lia].
             - right; right; left. exists (pa_SBUF E), (pa_NS E). split; [exact INS| clear - Hx SN; lia]. }
    split; [exact SBSH'|]. split; [exact PU'|].
    intros a CA OUT. rewrite <- (PRES0 a CA OUT). apply PRES.
    + eapply aclient_mono; [exact CA| intros e He; exact He| rewrite FR, EFR; intros e He; apply in_or_app; right; exact He| clear - BQ; lia].
    + apply SUB. pose proof (CREFA_munch E D C Σ st m m (sa_size st) OK CX HR (munch_refl _ m) (wmono_refl bsegs m)) as HR1.
      destruct HR as (_ & _ & _ & _ & _ & _ & _ & PRES1).

      unfold conWA. apply outside_app2.
      * assert (OR : forall R, (forall y, in_R R y -> ~ aclient (pa_L E) (ci_fr0 C) (ci_q C) y) -> outside R (bv_unsigned a)).
        { induction R as [|[lo hi] R IH]; intros HR'; [exact Logic.I|]. cbn [outside]. split.
          - intros H. apply (HR' (bv_unsigned a)); [apply in_R_cons; left; exact H| exact CA].
          - apply IH. intros y Hy. apply HR'. apply in_R_cons. right. exact Hy. }
        apply OR. intros y Hy. exact (proj2 (proj2 (proj2 (proj2 (proj2 (cr_R_facts E D C Σ st m y OK CX (proj1 HSM) Hy)))))).
      * cbn [outside] in OUT |- *. destruct OUT as [O1 _]. split; [| split; [exact O1| exact Logic.I]].
        pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & _ & R3). pose proof (cc_sp0 E D C CX) as [W1 _]. pose proof (cc_lo E D C CX) as LOB.
        destruct R3 as [(BL & HP)|(EB & EC & HP)]; [| rewrite EB, EC; clear - O1; lia]. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOB.
        intros Hb. refine (fresh_apart_l RT AF Σ m [(sa_buf st, sa_cap st)] (pa_L E) (sa_buf st) (sa_cap st) (ci_q C) (bv_unsigned a) ART0 _ ltac:(left; reflexivity) _ _ Hb).
        -- rewrite LV. unfold sbchunkA. rewrite HP. reflexivity.
        -- rewrite SP. clear - W1 LOB BQ. lia.
        -- eapply aclient_mono; [exact CA| intros e He; exact He| rewrite FR, EFR; intros e He; apply in_or_app; right; exact He| clear; lia].
  - unfold CCURA. split.
    { apply (LOC m m'); [| exact HF]. eapply agree_sub; [exact AG|]. intros x Hx. cbv beta.
      split; [| apply SPARE; exact Hx]. exact (proj1 (cr_R_facts E D C Σ st m x OK CX HR Hx) (pa_L E)). }
    split; [exact SV'|]. split; [exact SZ'|]. split; [exact BUFS'|]. split; [exact INLS'|]. split; [exact MI'| exact ST'].
Qed.

Lemma cont_growA : forall E D C FRP Σ st m (K : config -> Prop) (z X rpc : Z) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> cctxA E D C -> frp_local C FRP -> CERMA RT E C FRP Σ st m ->
  2 * sa_cap st <= z <= PJ_CAPMAX (pa_len E) -> CCREDA RT E C Σ X st -> 0 <= X ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (Σ' : rts RT) (NEW : Z) (m' : mem) (F' : bvmap 5 word) (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     CERMA RT E C FRP Σ' (sb_grownA st NEW z) m' -> CCREDA RT E C Σ' X (sb_grownA st NEW z) ->
     aevt Σ' K (MS (mkR (wz rpc) (wz (ci_b C)) (ci_gp C) (wz TPV_A) yt0 yt1 yt2 xs0 xs1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6)
                  F' (wz rpc) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR (wz rpc) (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 xs0 xs1 (wz (pa_SB E)) (wz z) xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6)
               F (wz PJ_GROW_A) fc None m (seg_rom bsegs)).
Proof using AF GROW.
  intros until xt6. intros OK CX LOC HSM ZB CR X0 RP0 RP2 HK.
  pose proof (SBINVA_of_CERMA E D C FRP Σ st m OK CX HSM) as INV. pose proof (pa_live_of_CERMA E D C FRP Σ st m CX HSM) as PL.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0). pose proof HC as (HF & SV0 & SZ0 & BUFS0 & INLS0 & MI & ST).
  pose proof (cc_lo E D C CX) as LOB. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOB. pose proof (cc_qtop E D C CX) as QT. pose proof (cc_bq E D C CX) as BQ.
  pose proof (cc_b16 E D C CX) as B16. pose proof (cc_L E D C CX) as LL. pose proof (cc_R E D C CX) as R0.
  pose proof (SBINVA_k E m st OK INV) as KB. pose proof (SBINVA_cap_pos E m st INV) as C64.
  pose proof (pj_psi_grow (pa_len E) st 0 z KB C64 ZB) as PSI.
  assert (PSI' : 0 <= pj_psi (pa_len E) (sb_grownA st 0 z)) by (unfold pj_psi, sb_grownA; cbn [sa_cap sa_k]; rewrite PJ_GROWC_val; lia).
  assert (PSIE : forall NEW, pj_psi (pa_len E) (sb_grownA st NEW z) = pj_psi (pa_len E) (sb_grownA st 0 z)) by (intros; reflexivity).
  unfold CCREDA in CR.
  eapply (GROW Σ K E st z (ci_b C) (wz rpc) (ci_gp C) xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m OK PL INV ZB ART0 MI ST).
  - unfold PJ_GROW_STACK_A, RT_STACK. clear - LOB. lia.
  - unfold USTACK_TOP in QT |- *. clear - QT BQ. lia.
  - exact B16.
  - rewrite LV, length_app. unfold sbchunkA. clear - LL. destruct (sa_heap st); cbn [length]; lia.
  - clear - PSI PSI' CR R0 X0. lia.
  - intros Σ' NEW t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' ART' MI' ST' INV' PL' FR' SP' CR' PRES'.
    rewrite (ret_pc_even rpc RP0 RP2). apply (HK Σ' NEW m' F').
    + pose proof INV' as (SV' & SZ' & (bs' & BUF') & (ji' & INL') & SBSH' & PK' & PH').
      eapply (CERMA_after_call E D C FRP Σ Σ' st (sb_grownA st NEW z) m m' [(pa_SB E + 64, pa_SB E + 88)]);
        [exact OK| exact CX| exact LOC| exact HSM| | | exact PRES'| exact ART'| exact MI'| exact ST'| exact (proj1 PL')| exact FR'| exact SP'
        | exact (conj PK' PH')| exact SBSH'| exact SV'| exact SZ'| | ].
      * intros x Hx. unfold conWA in Hx. destruct (outside_app_l _ _ _ Hx) as [_ H2]. cbn [outside] in H2 |- *. split; [clear - H2; lia| exact Logic.I].
      * intros x Hx. cbn [outside]. split; [| exact Logic.I]. pose proof (proj1 (proj2 (cr_R_facts E D C Σ st m x OK CX HR Hx))). clear - H. lia.
      * pose proof (stk_of_rw_cells bsegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S. unfold sb_grownA in *. cbn [sa_buf sa_cap] in *.
        rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
      * pose proof (stk_of_rw_cells bsegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S.
    + unfold CCREDA. rewrite PSIE. clear - CR CR' PSI R0 X0. lia.
Qed.

Lemma cont_req_ok2A : forall E D C FRP Σc st m, pjenvA_ok E -> cctxA E D C -> CERMA RT E C FRP Σc st m -> sa_cap st < PJ_OUTMAX (pa_len E) ->
  2 * sa_cap st <= 2 * sa_cap st <= PJ_CAPMAX (pa_len E).
Proof.
  intros until m. intros OK CX HSM H1. pose proof (SBINVA_cap_pos E m st (SBINVA_of_CERMA E D C FRP Σc st m OK CX HSM)). unfold PJ_CAPMAX. lia.
Qed.
Lemma cont_req_okA : forall E D C FRP Σc st m need, pjenvA_ok E -> cctxA E D C -> CERMA RT E C FRP Σc st m -> sa_cap st < need -> need <= PJ_OUTMAX (pa_len E) ->
  2 * sa_cap st <= Z.max (2 * sa_cap st) need <= PJ_CAPMAX (pa_len E).
Proof.
  intros until need. intros OK CX HSM H1 H2. eapply grow_request_okA; [exact OK| eapply SBINVA_of_CERMA; [exact OK| exact CX| exact HSM]| exact H1| exact H2].
Qed.

Lemma cont_call_serA : forall E D C FRP Σ st m (K : config -> Prop) (x x' c c1 X rpc : Z) (F : bvmap 5 word) (fc : bv 32)
    (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  ser_cpsA RT PMc D ->
  pjenvA_ok E -> cctxA E D C -> frp_local C FRP -> CERMA RT E C FRP Σ st m -> frm0 fc ->
  elemS (pa_T E) (pa_S E) (pa_sn E) ck_any D x x' c c1 -> 1 <= x -> x' <= pa_n E -> 0 <= c -> c1 <= pa_sn E -> sb_acc1A st x c ->
  CCREDA RT E C Σ X st -> 2 * (x' - x) <= X ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     frm0 fc' -> CERMA RT E C FRP Σ' st' m' -> sb_accA st' x' c1 -> CCREDA RT E C Σ' (X - 2 * (x' - x)) st' ->
     aevt Σ' K (MS (mkR (wz rpc) (wz (ci_b C)) (ci_gp C) (wz TPV_A) yt0 yt1 yt2 xs0 xs1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6)
                  F' (wz rpc) fc' None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR (wz rpc) (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 xs0 xs1 (wz (pa_SB E)) (wz (pa_DOC E)) (wz x) xa3 xa4 xa5 xa6 xa7
                    xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (wz PJ_APPEND_ELEM_A) fc None m (seg_rom bsegs)).
Proof using AF FDO MST.
  intros until xt6. intros SER OK CX LOC HSM FRM HEL X1 X2 C0 C1 ACC CR XX RP0 RP2 HK.
  pose proof (SBINVA_of_CERMA E D C FRP Σ st m OK CX HSM) as INV. pose proof (pa_live_of_CERMA E D C FRP Σ st m CX HSM) as PL.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0). pose proof HC as (HF & SV0 & SZ0 & BUFS0 & INLS0 & MI & ST).
  pose proof (cc_lo E D C CX) as LOB. pose proof (cc_qtop E D C CX) as QT. pose proof (cc_bq E D C CX) as BQ.
  pose proof (cc_b16 E D C CX) as B16. pose proof (cc_L E D C CX) as LL. pose proof (cc_R E D C CX) as R0.
  pose proof (cc_fr3 E D C CX) as FR3. pose proof (cc_frl E D C CX) as FRL.
  pose proof (sb_pureA_psi E st OK PU) as PSI0. unfold CCREDA in CR.
  eapply (SER Σ K E st x x' c c1 (ci_b C) (wz rpc) (ci_gp C) xt0 xt1 xt2 xs0 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m
            FDO MST OK PL INV DR HEL X1 X2 C0 C1 ACC ART0 MI ST LOB).
  - unfold USTACK_TOP in QT |- *. clear - QT BQ. lia.
  - exact B16.
  - exact FRM.
  - rewrite FR. exact FR3.
  - rewrite FR. clear - FRL. lia.
  - exact LL.
  - clear - CR XX R0; lia.
  - intros Σ' st' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' FRM' ART' MI' ST' INV' DR' ACC' PL' FR' SP' CR' PRES'.
    rewrite (ret_pc_even rpc RP0 RP2). apply (HK Σ' st' m' F' fc'); [exact FRM'| | exact ACC'| unfold CCREDA; clear - CR CR'; lia].
    pose proof INV' as (SV' & SZ' & (bs' & BUF') & (ji' & INL') & SBSH' & PK' & PH').
    pose proof (sb_pureA_ranges E st' OK (conj PK' PH')) as (_ & R1' & _).
    eapply (CERMA_after_call E D C FRP Σ Σ' st st' m m' [(pa_SB E, pa_SB E + 88)]);
      [exact OK| exact CX| exact LOC| exact HSM| | | exact PRES'| exact ART'| exact MI'| exact ST'| exact (proj1 PL')| exact FR'| exact SP'
      | exact (conj PK' PH')| exact SBSH'| exact SV'| exact SZ'| | ].
    + intros y Hy. unfold conWA in Hy. destruct (outside_app_l _ _ _ Hy) as [_ H2]. cbn [outside] in H2 |- *. split; [clear - H2; lia| exact Logic.I].
    + intros y Hy. cbn [outside]. split; [| exact Logic.I]. exact (proj1 (proj2 (cr_R_facts E D C Σ st m y OK CX HR Hy))).
    + pose proof (stk_of_rw_cells bsegs _ _ _ BUF') as S. cbn [cells_size csize Nat.add] in S. rewrite Nat.add_0_r, Z2Nat.id in S by lia. exact S.
    + pose proof (stk_of_rw_cells bsegs _ _ _ INL') as S. cbn [cells_size csize Nat.add] in S. exact S.
Qed.

Lemma cstackwin_not_client : forall E D C Σc st m a sp, pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st m ->
  aclient (pa_L E) (rt_frames RT Σc) sp a -> pa_lo E <= a < sp -> False.
Proof using AF.
  intros E D C Σc st m a sp OK CX (ART0 & LV & FR & SP & _) CA Ha.
  pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FS & _ & _ & _ & _ & FL & LO & _).
  pose proof (cc_sp0 E D C CX) as (W1 & W2). unfold STACK_WIN in W1. unfold SEGTOP_A in FS.
  destruct CA as [CA|[CA|[CA|[CA|CA]]]].
  - clear - CA Ha. lia.
  - apply client_static_range in CA. unfold SEGTOP_A in CA. destruct (fs_size_64 (pa_kF E)) as (qF & EF4 & QF1). clear - CA Ha FS FL EF4 QF1. lia.
  - destruct CA as (p & n & INp & Hp).
    assert (INp' : In (p, n) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INp).
    pose proof (af_live_range RT AF Σc m _ _ ART0 INp') as (_ & PR & _). unfold STACK_WIN in PR. clear - Hp PR W1 SP Ha. lia.
  - destruct CA as (g & k & INg & Hg).
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INg) as (_ & GR & _). unfold STACK_WIN in GR. clear - Hg GR W1 SP Ha. lia.
  - destruct CA as (g & k & INg & Hg).
    pose proof (af_frames_range RT AF Σc m _ _ ART0 INg) as (G0 & GR & _). unfold STACK_WIN in GR. unfold shad, SHB in Hg. clear - Hg G0 GR W1 SP Ha LO. lia.
Qed.

Lemma cont_trefA : forall E D C FRP Σc st m idx (F : bvmap 5 word) (fc : bv 32)
    (xra xt0 xt1 xt2 xs0 xs1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> cctxA E D C -> frp_local C FRP -> CERMA RT E C FRP Σc st m -> 0 <= idx <= pa_n E ->
  evt bsegs (fun ms => exists (m' : mem) (ya4 : word),
      ms = MS (mkR xra (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 xs0 xs1
                   (wz (pa_TAPE E + 8 * idx)) (wz 0) (wz (pa_TAPE E)) (wz 1152921504606846976) ya4 xa5 xa6 xa7
                   xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (ret_pc xra) fc None m' (seg_rom bsegs)
      /\ CERMA RT E C FRP Σc st m')
    (MS (mkR xra (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 xs0 xs1 (wz (pa_DOC E)) (wz idx) xa2 xa3 xa4 xa5 xa6 xa7
             xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (wz PJ_TREF_A) fc None m (seg_rom bsegs)).
Proof using AF.
  intros until xt6. intros OK CX LOC HSM HI.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0). pose proof DR as (DC0 & SHD & _).
  pose proof HC as (HF & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (env_rangesA E OK) as (T0 & TL & T16 & _ & _ & _ & D8 & B32 & F64 & FS0 & B1 & B2 & D1 & D2 & FL & LO & AP).
  pose proof (cc_lo E D C CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (cc_qtop E D C CX) as QT. unfold USTACK_TOP in QT.
  pose proof (cc_bq E D C CX) as BQ. pose proof (cc_sp0 E D C CX) as (W1 & W2). unfold SEGTOP_A in FS0.
  pose proof (buf_factsC E D C OK CX Σc st m HR) as (BL & _).
  assert (DC1 : rw_cells bsegs m (pa_DOC E) [C8 (wz (pa_TAPE E))])
    by (exact (proj1 (proj1 (rw_cells_app bsegs m (pa_DOC E) [C8 (wz (pa_TAPE E))] [C8 (wz (pa_SBUF E))]) DC0))).
  eapply evt_mono.
  { eapply (tref_walk (pa_DOC E) (pa_TAPE E) idx (ci_b C) (pa_lo E) xra (ci_gp C) (wz TPV_A) xt0 xt1 xt2 xs0 xs1
              xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m ST);
      [clear - LOQ; lia| clear - LO; lia| clear - QT BQ; lia| exact (af_client_consts RT AF Σc m ART0)
      | clear - FS0 D1; lia| clear - D2 FL LOQ QT BQ; lia| exact D8| exact SHD| exact DC1| exact T0| clear - T16; dlia| clear - HI; lia
      | clear - HI TL LOQ QT BQ; lia| left; clear - D2 FL LOQ; lia| exact MI]. }
  cbv beta. intros ms' (m' & a4' & -> & MU & WM & MI' & ST').
  exists m', a4'. split; [reflexivity|].
  assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ (ci_b C - 16 <= x < ci_b C)) -> agree_on P m m').
  { intros P HP. eapply agree_of_munch; [exact MU|]. intros x Hx. cbn [outside]. split; [exact (HP _ Hx)| exact Logic.I]. }
  assert (ART' : ART RT Σc m').
  { apply (art_client_write RT AF Σc m m' (ci_b C - 16) ART0); [rewrite SP; clear - LOQ W1; lia| | exact WM].
    apply AG. intros x Hx Cx. apply Hx. left. unfold USTACK_TOP in *. clear - Cx QT BQ. lia. }
  assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σc) (ci_b C) [] m m').
  { intros a Ha _. apply MU. cbn [outside]. split; [| exact Logic.I]. intros Ca.
    eapply (cstackwin_not_client E D C Σc st m (bv_unsigned a) (ci_b C)); [exact OK| exact CX| exact HR| exact Ha| clear - Ca LOQ; lia]. }
  destruct (fs_size_64 (pa_kF E)) as (qF & EFS & QF1).
  eapply (CERMA_after_call E D C FRP Σc Σc st st m m' []);
    [exact OK| exact CX| exact LOC| exact HSM| intros x _; exact Logic.I| intros x _; exact Logic.I| exact PRESW| exact ART'| exact MI'| exact ST'
    | exact LV| reflexivity| reflexivity| exact PU| | | exact SZ| | ].
  - eapply bytes_at_agree; [exact SBSH|]. apply AG. intros x Hx. rewrite repeat_length in Hx. unfold shad, SHB in *.
    clear - Hx B1 B2 FL LOQ QT LO F64 EFS QF1 B32. dlia.
  - eapply rw_cells_agree_nw; [exact SV|]. apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx B2 FL LOQ. lia.
  - eapply stk_agree_nw; [exact BUFS|]. apply AG. intros x Hx. clear - Hx BL LOQ. lia.
  - eapply stk_agree_nw; [exact INLS|]. apply AG. intros x Hx. clear - Hx B2 FL LOQ. lia.
Qed.
End Kit.

Ltac cont_envA OK CX :=
  lazymatch type of CX with cctxA ?E ?D ?C =>
  let H := fresh in
  pose proof (env_rangesA E OK) as H;
  let T0 := fresh in let TL := fresh in let S0 := fresh in let SL := fresh in
  let FS := fresh "FS" in let B1 := fresh "B1" in let B2 := fresh "B2" in let D1 := fresh "D1" in let D2 := fresh "D2" in let FL := fresh "FL" in
  let LO := fresh "LO" in let AP := fresh "AP" in
  destruct H as (T0 & TL & _ & S0 & SL & _ & _ & _ & _ & FS & B1 & B2 & D1 & D2 & FL & LO & AP);
  assert (TR : 0 < pa_TAPE E /\ pa_TAPE E + 8 * pa_n E <= pa_lo E) by (clear - T0 TL; split; assumption);
  assert (SR : 0 < pa_SBUF E /\ pa_SBUF E + pa_sn E <= pa_lo E) by (clear - S0 SL; split; assumption); clear T0 TL S0 SL;
  let LOQ := fresh in pose proof (cc_lo E D C CX) as LOQ; unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ;
  assert (LB : pa_lo E + 66096 <= ci_b C) by (clear - LOQ; lia); clear LOQ;
  pose proof (cc_bq E D C CX) as BQ;
  pose proof (cc_qtop E D C CX) as QT; unfold USTACK_TOP in QT;
  assert (SBR : 7208960 <= pa_SB E /\ pa_SB E + 96 <= pa_lo E) by (clear - FS B1 B2 FL; unfold SEGTOP_A in *; lia);
  assert (DOCR : 7208960 <= pa_DOC E /\ pa_DOC E + 24 <= pa_lo E) by (clear - FS D1 D2 FL; unfold SEGTOP_A in *; lia);
  clear FS B1 B2 D1 D2 FL; lazymatch type of AP with ?T => change (boxP T) in AP end
  end.

Ltac cont_open HM OK CX :=
  lazymatch type of HM with
  | CERMA ?RT ?E ?C ?FRP _ _ _ =>
      unfold CERMA, sb_grownA, sb_sized in HM; cbn [sa_buf sa_size sa_cap sa_heap sa_k] in HM;
      destruct HM as [HREF HCUR];
      unfold CCURA in HCUR; cbn [sa_buf sa_size sa_cap sa_heap sa_k] in HCUR;
      let SZ := fresh "SZ" in
      destruct HCUR as (HFRP & SV & SZ & BUFS & INLS & MI & ST);
      lazymatch type of HREF with
      | CREFA _ _ _ _ ?st ?m =>
          pose proof (munch_refl (conWA E C st) m) as MU; pose proof (wmono_refl bsegs m) as WM;
          unfold conWA, cr_R in MU; cbn [sa_buf sa_size sa_cap sa_heap sa_k app ci_b ci_q ci_R_] in MU;
          let PU := fresh "PU" in
          assert (PU : sb_pureA E st) by (apply HREF);
          let RK := fresh in let R0 := fresh "R0" in let R1 := fresh "R1" in let R3 := fresh "R3" in let BL := fresh "BL" in
          pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3);
          pose proof (sb_pureA_below E st OK PU) as BL;
          cbn [sa_buf sa_size sa_cap sa_heap sa_k] in R0, R1, R3, BL; clear PU RK;
          lazymatch type of R3 with ?T => change (boxP T) in R3 end
      end
  end.

Ltac cont_close HM HFRP OK CX :=
  match goal with
  | HREF : CREFA ?RT ?E ?C ?Σc ?st ?mr, MU : munch _ ?mr ?m, WM : wmono _ ?mr ?m,
    SV : rw_cells _ ?m (pa_SB ?E + 64) [C8 (Z_to_bv 64 ?buf); C8 (Z_to_bv 64 ?size); C8 (Z_to_bv 64 ?cap)],
    BUFS : stk _ ?m ?buf (?buf + ?cap), INLS : stk _ ?m (pa_SB ?E) (pa_SB ?E + 64),
    MI : mem_inv _ ?m, ST : stk _ ?m (pa_lo ?E) _ |- _ =>
      let SZ' := fresh "SZc" in
      first [ assert (SZ' : 0 <= size <= sa_cap st) by (cbn [sa_cap]; lia) | fail 100 "cont_close: cannot prove 0 <= size <= cap" ];
      lazymatch type of HFRP with ?FRP m =>
      first [ pose proof (CERMA_intro RT ltac:(assumption) E _ C FRP Σc st mr m size OK CX HREF MU WM HFRP SV SZ' BUFS INLS MI ST) as HM
            | fail 100 "cont_close: CERMA_intro does not apply" ] end;
      unfold sb_sized in HM; cbn [sa_buf sa_size sa_cap sa_heap sa_k] in HM;
      clear SZ' MU WM; clear SV; try clear BUFS; try clear INLS; clear ST; clear MI; clear HREF; clear HFRP
  | _ => fail 100 "cont_close: the open context is incomplete"
  end.
