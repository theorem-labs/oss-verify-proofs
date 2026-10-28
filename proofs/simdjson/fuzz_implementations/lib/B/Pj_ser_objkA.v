(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep Frame.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import Prelim SjModel PjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjTape SjTapeList SjTapeTile SjPjSer SjPjCont.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 RT_iface4 D_defs D_kit D_clx D_libiface I_lkit
     Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_hkit5A Atp_fzwA Pj_rtkA Pj_defsA Pj_cpsA Pj_copyA Pj_ser_defsA Pj_ser_kitA Pj_ser_callsA Pj_ser_trefA Pj_ser_ckitA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).
Local Ltac dlia := Z.div_mod_to_equations; lia.

Notation M32M1 := 4294967295 (only parsing).
Notation M32P1 := 4294967297 (only parsing).
Notation MNUMK := 67240448 (only parsing).
Notation M56M1 := 72057594037927935 (only parsing).
Notation M32M8 := 4294967288 (only parsing).

Definition obj_hdrA : list cell := [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x11664); C8 (Z_to_bv 64 PJ_APPEND_OBJ_A)].
Definition sh16 (b : list byte) : list cell := map C1 b.
Definition obj_shpatA : list byte := map (Z_to_bv 8) [0xf1; 0xf1; 0xf1; 0xf1; 0xf8; 0xf2; 0xf2; 0xf2; 0xf8; 0xf3; 0xf3; 0xf3; 0; 0; 0; 0].

Record owA : Type := mkOW { ow8 : word; ow16 : word; ow24 : word; ow32 : word; ow40 : word; ow48 : word; ow56 : word; ow64 : word; ow72 : word; ow80 : word; ow88 : word;
                             ow96 : word; ow104 : word; ow112 : word; ow120 : word; ow128 : word; ow136 : word; ow144 : word; ow152 : word; ow160 : word;
                             ow168 : word; ow176 : word; ow184 : word; ow192 : word; ow200 : word; ow208 : word; ow216 : word; ow224 : word; ow232 : word;
                             ow240 : word }.

Definition obj_slotsA (w : owA) : list cell :=
  [C8 (ow8 w); C8 (ow16 w); C8 (ow24 w); C8 (ow32 w); C8 (ow40 w); C8 (ow48 w); C8 (ow56 w); C8 (ow64 w); C8 (ow72 w); C8 (ow80 w); C8 (ow88 w); C8 (ow96 w); C8 (ow104 w);
   C8 (ow112 w); C8 (ow120 w); C8 (ow128 w); C8 (ow136 w); C8 (ow144 w); C8 (ow152 w); C8 (ow160 w); C8 (ow168 w); C8 (ow176 w); C8 (ow184 w);
   C8 (ow192 w); C8 (ow200 w); C8 (ow208 w); C8 (ow216 w); C8 (ow224 w); C8 (ow232 w); C8 (ow240 w)].

Definition owK (E : pjenvA) (C : conI) (f : Z) (x24 x32 x40 x48 x56 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232 : word) : owA :=
  mkOW (Z_to_bv 64 f) (Z_to_bv 64 f) x24 x32 x40 x48 x56 (Z_to_bv 64 (ci_e C)) x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 (Z_to_bv 64 (f / 8 + 2147450880)) x176
       (Z_to_bv 64 ((pa_SB E + 72) / 8 + 2147450880)) (Z_to_bv 64 ((pa_SB E + 64) / 8 + 2147450880)) (Z_to_bv 64 ((pa_SB E + 80) / 8 + 2147450880))
       (Z_to_bv 64 (pa_SB E + 80)) (Z_to_bv 64 (pa_SB E + 64)) x224 x232 (Z_to_bv 64 f).

Definition co_savedA (C : conI) : list cell :=
  [C8 (ci_s11 C); C8 (ci_s10 C); C8 (ci_s9 C); C8 (ci_s8 C); C8 (ci_s7 C); C8 (ci_s6 C); C8 (ci_s5 C); C8 (ci_s4 C);
   C8 (ci_s3 C); C8 (ci_s2 C); C8 (ci_s1 C); C8 (ci_s0 C); C8 (ci_ra C)].

Definition obj_frp (E : pjenvA) (C : conI) (f : Z) (w : owA) (shp : list byte) (m : mem) : Prop :=
  stk bsegs m (ci_b C) (ci_b C + 8)
  /\ rw_cells bsegs m (ci_b C + 8) (obj_slotsA w)
  /\ stk bsegs m (ci_b C + 248) (ci_q C - 104)
  /\ rw_cells bsegs m (ci_q C - 104) (co_savedA C)
  /\ rw_cells bsegs m f obj_hdrA
  /\ stk bsegs m (f + 24) (f + 120)
  /\ rw_cells bsegs m (f / 8 + 2147450880) (sh16 shp) /\ length shp = 16%nat.

Definition obj_R_ (f : Z) : list (Z * Z) := [(f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450896)].

Record octxA (E : pjenvA) (C : conI) (f : Z) : Prop := mkOC {
  oc_R : ci_R_ C = obj_R_ f;
  oc_fr : ci_fr C = (f, 1%nat) :: ci_fr0 C;
  oc_bq : ci_b C + 352 <= ci_q C <= ci_b C + 368;
  oc_b32 : ci_b C mod 32 = 0;
  oc_f : 0 < f /\ f mod 64 = 0 /\ SEGTOP_A <= f /\ f + 128 <= pa_lo E;
  oc_fF : f + 128 <= pa_F E \/ pa_F E + fs_size (pa_kF E) <= f;
  oc_f_shf : f + 128 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= f;
  oc_F_shf : pa_F E + fs_size (pa_kF E) <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= pa_F E;
  oc_f_shF : f + 128 <= pa_F E / 8 + 2147450880 \/ (pa_F E + fs_size (pa_kF E)) / 8 + 2147450880 <= f }.

Lemma sh16_size : forall shp, cells_size (sh16 shp) = length shp.
Proof. intros shp. unfold sh16. induction shp as [|b l IH]; [reflexivity| cbn [map cells_size csize]; rewrite IH; reflexivity]. Qed.

Lemma obj_frp_local : forall E C f w shp, octxA E C f -> frp_local C (obj_frp E C f w shp).
Proof.
  intros E C f w shp OX m m' AG (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8). pose proof (oc_R E C f OX) as HR. pose proof (oc_bq E C f OX) as BQ.
  pose proof (rw_cells_bound bsegs m _ _ H4) as B4. unfold co_savedA in B4. cbn [cells_size csize Nat.add] in B4.
  assert (AGs : forall lo hi, (forall x, lo <= x < hi -> in_R (cr_R C) x) -> agree_on (fun x => lo <= x < hi) m m')
    by (intros lo hi H x Hx; exact (AG x (H _ Hx))).
  assert (Ib : forall x, ci_b C <= x < ci_q C -> in_R (cr_R C) x) by (intros x Hx; exists (ci_b C), (ci_q C); split; [left; reflexivity| exact Hx]).
  assert (If : forall x, f <= x < f + 120 -> in_R (cr_R C) x) by (intros x Hx; exists f, (f + 120); split; [right; rewrite HR; left; reflexivity| exact Hx]).
  assert (Is : forall x, f / 8 + 2147450880 <= x < f / 8 + 2147450880 + 16 -> in_R (cr_R C) x)
    by (intros x Hx; exists (f / 8 + 2147450880), (f / 8 + 2147450896); split; [right; rewrite HR; right; left; reflexivity| lia]).
  pose proof (rw_cells_bound bsegs m _ _ H2) as B2. unfold obj_slotsA in B2. cbn [cells_size csize Nat.add] in B2.
  unfold obj_frp.
  split; [eapply stk_agree_nw; [exact H1| apply AGs; intros x Hx; apply Ib; lia]|].
  split; [eapply rw_cells_agree_nw; [exact H2| apply AGs; intros x Hx; apply Ib; unfold obj_slotsA in Hx; cbn [cells_size csize Nat.add] in Hx; lia]|].
  split; [eapply stk_agree_nw; [exact H3| apply AGs; intros x Hx; apply Ib; lia]|].
  split; [eapply rw_cells_agree_nw; [exact H4| apply AGs; intros x Hx; apply Ib; unfold co_savedA in Hx; cbn [cells_size csize Nat.add] in Hx; lia]|].
  split; [eapply rw_cells_agree_nw; [exact H5| apply AGs; intros x Hx; apply If; unfold obj_hdrA in Hx; cbn [cells_size csize Nat.add] in Hx; lia]|].
  split; [eapply stk_agree_nw; [exact H6| apply AGs; intros x Hx; apply If; lia]|].
  split; [eapply rw_cells_agree_nw; [exact H7| apply AGs; intros x Hx; apply Is; rewrite sh16_size, H8 in Hx; lia]| exact H8].
Qed.

Lemma munch_conWAf : forall E C f st m m', ci_R_ C = obj_R_ f ->
  munch [(ci_b C, ci_q C); (f, f + 120); (f / 8 + 2147450880, f / 8 + 2147450896); (sa_buf st, sa_buf st + sa_cap st); (pa_SB E, pa_SB E + 88)] m m' ->
  munch (conWA E C st) m m'.
Proof. intros E C f st m m' H MU. unfold conWA, cr_R. rewrite H. exact MU. Qed.

Notation OST E C pc xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xs2 xs4 xs5 xs6 xs7 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m :=
  (MS (mkR xra (Z_to_bv 64 (ci_b C)) (ci_gp C) (Z_to_bv 64 TPV_A) xt0 xt1 xt2 (Z_to_bv 64 (ci_q C)) (Z_to_bv 64 (ci_b C)) xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
           xs2 (Z_to_bv 64 (pa_SB E + 72)) xs4 xs5 xs6 xs7 (Z_to_bv 64 2147450880) xs9 xs10 xs11 xt3 xt4 xt5 xt6)
      F (Z_to_bv 64 pc) fc None m (seg_rom bsegs)).

Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Lemma buf_aclientC : forall E D C Σc st m sp y, pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st m ->
  sa_buf st <= y < sa_buf st + sa_cap st -> aclient (rt_live RT Σc) (rt_frames RT Σc) sp y.
Proof.
  intros until y. intros OK CX HR Hy. pose proof HR as (ART0 & LV & FR & _ & _ & _ & PU & _).
  pose proof (sb_pureA_ranges E st OK PU) as (_ & _ & _ & R3). pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
  destruct (cc_fr E D C CX) as (top & EFR).
  destruct R3 as [(BL' & HP)|(EB & EC & HP)].
  - right; right; left. exists (sa_buf st), (sa_cap st). split; [rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity| exact Hy].
  - right; right; right; left. exists (pa_F E), (pa_kF E). split; [rewrite FR, EFR; apply in_or_app; right; exact (cc_F4 E D C CX)| clear - Hy EB EC B1 B2; lia].
Qed.

Lemma cont_copyhA : forall E D C FRP Σ st m (K : config -> Prop) (Src n rpc : Z) (bs : list byte)
    (F : bvmap 5 word) (fc : bv 32) (xt0 xt1 xt2 xa3 xa4 xa5 xa6 xa7 xs0 xs1 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 : word),
  pjenvA_ok E -> cctxA E D C -> frp_local C FRP -> CERMA RT E C FRP Σ st m ->
  bytes_at bsegs m Src bs -> Z.of_nat (length bs) = n -> 0 <= n -> sa_size st + n <= sa_cap st ->
  (0 < n -> acc bsegs m Src n /\ rng_class RT Σ Src n) -> 0 < Src -> Src + n <= pa_lo E ->
  0 <= rpc < 2^64 -> rpc mod 2 = 0 ->
  (forall (m' : mem) (F' : bvmap 5 word) (yt0 yt1 yt2 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
     CERMA RT E C FRP Σ st m' -> bytes_at bsegs m' (sa_buf st + sa_size st) bs ->
     aevt Σ K (MS (mkR (wz rpc) (wz (ci_b C)) (ci_gp C) (wz TPV_A) yt0 yt1 yt2 xs0 xs1 (wz (Src + n)) (wz (sa_buf st + sa_size st + n)) ya2 ya3 ya4 ya5 ya6 ya7
                     xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 yt3 yt4 yt5 yt6) F' (wz rpc) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR (wz rpc) (wz (ci_b C)) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 xs0 xs1 (wz Src) (wz (Src + n)) (wz (sa_buf st + sa_size st)) xa3 xa4 xa5 xa6 xa7
                  xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6) F (wz PJ_COPY_S_A) fc None m (seg_rom bsegs)).
Proof using AF RC FDO MST.
  intros until xt6. intros OK CX LOC HSM BY LEN N0 ROOM SRCOK S0 SLO RP0 RP2 HK.
  pose proof HSM as [HR HC]. pose proof HR as (ART0 & LV & FR & SP & DR & SBSH & PU & PRES0). pose proof HC as (HF & SV & SZ & BUFS & INLS & MI & ST).
  pose proof (buf_factsC RT AF E D C OK CX Σ st m HR) as (BL & B0 & RCB & CLB & APB).
  pose proof (sb_pureA_ranges E st OK PU) as (R0 & R1 & RK & R3).
  pose proof (cc_lo E D C CX) as LOQ. unfold ser_needA, PJ_TC_STACK_A, RT_STACK in LOQ. pose proof (cc_qtop E D C CX) as QT. unfold USTACK_TOP in QT.
  pose proof (cc_bq E D C CX) as BQ. pose proof (cc_b16 E D C CX) as B16. pose proof (cc_sp0 E D C CX) as (W1 & W2). pose proof (ok_lo E OK) as LOW.
  pose proof (acc_buf_muC RT AF E D C OK CX Σ st m m HR (munch_refl _ m) (wmono_refl bsegs m)) as ACCB.
  subst n.
  eapply (copy_okA RT AF RC PMc FDO MST PJ_COPY_S_A (or_intror eq_refl) Σ K (ci_b C) (pa_lo E) Src (sa_buf st + sa_size st) (Z.of_nat (length bs)) bs
            (wz rpc) (ci_gp C) (wz TPV_A) xt0 xt1 xt2 xs0 xs1 xa3 xa4 xa5 xa6 xa7 xs2 xs3 xs4 xs5 xs6 xs7 xs8 xs9 xs10 xs11 xt3 xt4 xt5 xt6 F fc m
            BY eq_refl); [| exact S0| exact SLO| | | exact SRCOK| | | | exact ART0| exact MI| exact ST| rewrite SP; exact W1| | | |].
  - clear - ROOM SZ R1. lia.
  - clear - B0 SZ. lia.
  - clear - BL SZ ROOM. lia.
  - intros _. split; [apply (acc_sub bsegs m _ _ _ _ ACCB); clear - SZ ROOM; lia|].
    destruct R3 as [(BL' & HP)|(EB & EC & HP)].
    + left. exists (sa_buf st), (sa_cap st). split; [rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity| clear - SZ ROOM; lia].
    + right; left. exists (pa_F E), (pa_kF E). pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & _).
      destruct (cc_fr E D C CX) as (top0 & EFR0).
      split; [rewrite FR, EFR0; apply in_or_app; right; exact (cc_F4 E D C CX)| clear - EB EC SZ ROOM B1 B2; lia].
  - intros sp i Hi. apply (buf_aclientC E D C Σ st m sp _ OK CX HR). clear - Hi SZ ROOM. lia.
  - apply (stk_wr_at m _ _ _ _ BUFS); clear - SZ ROOM; lia.
  - unfold PJ_COPY_STACK_A, RT_STACK. clear - LOQ. lia.
  - unfold USTACK_TOP. clear - QT BQ. lia.
  - exact B16.
  - intros t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' ART' MI' ST' WM' BY' PRES'.
    rewrite (ret_pc_even rpc RP0 RP2). apply HK; [| exact BY'].
    set (W := [(sa_buf st + sa_size st, sa_buf st + sa_size st + Z.of_nat (length bs))]).
    assert (AGB : forall P : Z -> Prop,
              (forall x, P x -> aclient (rt_live RT Σ) (rt_frames RT Σ) (ci_b C) x /\ ~ (sa_buf st + sa_size st <= x < sa_buf st + sa_size st + Z.of_nat (length bs))) ->
              agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (PRES' a H1 H2). }
    assert (PRESW : rt_pres_fp (pa_L E) (rt_frames RT Σ) (ci_b C) W m m').
    { intros a Ha Ho. apply PRES'; [| cbn [outside] in Ho; exact (proj1 Ho)].
      eapply aclient_mono; [exact Ha| rewrite LV; intros e He; apply in_or_app; right; exact He| intros e He; exact He| clear; lia]. }
    pose proof (env_rangesA E OK) as (_ & _ & _ & _ & _ & _ & D8 & B32 & F64 & FS & B1 & B2 & D1 & D2 & FL & _).
    pose proof (cc_F4 E D C CX) as IN4. destruct (cc_fr E D C CX) as (top & EFR).
    assert (INF4 : In (pa_F E, pa_kF E) (rt_frames RT Σ)) by (rewrite FR, EFR; apply in_or_app; right; exact IN4).
    destruct (fs_size_64 (pa_kF E)) as (qF & EFS & QF1).
    assert (BUFS' : stk bsegs m' (sa_buf st) (sa_buf st + sa_cap st)).
    { destruct (stk_split bsegs m _ (sa_buf st + sa_size st) _ BUFS ltac:(clear - SZ ROOM; lia)) as [SLO' SREST].
      destruct (stk_split bsegs m _ (sa_buf st + sa_size st + Z.of_nat (length bs)) _ SREST ltac:(clear - SZ ROOM; lia)) as [SMID SHI].
      eapply stk_merge; [eapply stk_agree_nw; [exact SLO'| apply AGB; intros x Hx; split; [apply CLB; clear - Hx SZ ROOM; lia| clear - Hx; lia]]| | clear - SZ ROOM; lia].
      eapply stk_merge; [apply (stk_of_bytes_wmono m m' _ bs BY' SMID WM')| | clear - SZ ROOM; lia].
      eapply stk_agree_nw; [exact SHI| apply AGB; intros x Hx; split; [apply CLB; clear - Hx SZ ROOM; lia| clear - Hx; lia]]. }
    eapply (CERMA_after_call RT AF E D C FRP Σ Σ st st m m' W);
      [exact OK| exact CX| exact LOC| exact HSM| | | exact PRESW| exact ART'| exact MI'| exact ST'| exact LV| reflexivity| reflexivity| exact PU| | | exact SZ| exact BUFS'| ].
    + intros x Hx. unfold conWA in Hx. destruct (outside_app_l _ _ _ Hx) as [_ H2]. unfold W. cbn [outside] in H2 |- *. split; [clear - H2 SZ ROOM; lia| exact Logic.I].
    + intros x Hx. unfold W. cbn [outside]. split; [| exact Logic.I].
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (cr_R_facts RT AF E D C Σ st m x OK CX HR Hx)))))) as NB. clear - NB SZ ROOM. lia.
    + eapply bytes_at_agree; [exact SBSH|]. apply AGB. intros x Hx. rewrite repeat_length in Hx. split.
      * right; right; right; right. exists (pa_F E), (pa_kF E). split; [exact INF4|]. unfold shad, SHB in Hx |- *. clear - Hx D1 D2 D8 B1 B2 B32 F64 EFS QF1. dlia.
      * intros Cx. destruct (APB x ltac:(clear - Cx SZ ROOM; lia)) as (_ & _ & A3). apply A3. exact Hx.
    + eapply rw_cells_agree_nw; [exact SV|]. apply AGB. intros x Hx. cbn [cells_size csize Nat.add] in Hx. split.
      * right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
      * intros Cx. destruct (APB x ltac:(clear - Cx SZ ROOM; lia)) as (_ & A2 & _). apply A2. clear - Hx. lia.
    + destruct R3 as [(BL' & HP)|(EB & EC & HP)].
      * eapply stk_agree_nw; [exact INLS|]. apply AGB. intros x Hx. split.
        -- right; right; right; left. exists (pa_F E), (pa_kF E). split; [exact INF4| clear - Hx B1 B2; lia].
        -- intros Cx. assert (INB : In (sa_buf st, sa_cap st) (rt_live RT Σ)) by (rewrite LV; unfold sbchunkA; rewrite HP; left; reflexivity).
           pose proof (af_frames_range RT AF Σ m _ _ ART0 INF4) as (_ & _ & _ & F4CH). specialize (F4CH _ _ INB). clear - Hx Cx F4CH B1 B2 SZ ROOM. lia.
      * rewrite <- EB, <- EC. exact BUFS'.
Qed.

Lemma cont_sbuf_srcA : forall E D C Σc st m o n, pjenvA_ok E -> cctxA E D C -> CREFA RT E C Σc st m -> 0 <= o -> 0 <= n -> o + n <= pa_sn E ->
  exists src, bytes_at bsegs m (pa_SBUF E + o) src /\ Z.of_nat (length src) = n
    /\ acc bsegs m (pa_SBUF E + o) n /\ rng_class RT Σc (pa_SBUF E + o) n /\ 0 <= pa_SBUF E + o /\ pa_SBUF E + o + n <= pa_lo E.
Proof using AF.
  intros until n. intros OK CX HR Ho Hn Hb. pose proof HR as (ART0 & LV & _ & _ & (_ & _ & _ & SBUFB) & _).
  pose proof (ok_sbuf E OK) as (_ & SN & S0 & SL & INS).
  assert (INS' : In (pa_SBUF E, pa_NS E) (rt_live RT Σc)) by (rewrite LV; apply in_or_app; right; exact INS).
  exists (firstn (Z.to_nat n) (skipn (Z.to_nat o) (map (Z_to_bv 8) (pa_sbs E)))). split; [| split; [| split; [| split; [| lia]]]].
  - pose proof SBUFB as (B0 & B1 & BB). rewrite length_map in B1.
    split; [lia|]. split; [rewrite length_firstn, length_skipn, length_map; lia|].
    intros i Hi. rewrite length_firstn, length_skipn, length_map in Hi.
    replace (pa_SBUF E + o + Z.of_nat i) with (pa_SBUF E + Z.of_nat (Z.to_nat o + i)) by lia.
    rewrite BB by (rewrite length_map; lia).
    rewrite nth_error_firstn. destruct (Nat.ltb_spec i (Z.to_nat n)) as [L|L]; [| lia]. rewrite nth_error_skipn. reflexivity.
  - rewrite length_firstn, length_skipn, length_map. lia.
  - apply (acc_sub bsegs m (pa_SBUF E) (pa_NS E)); [exact (proj2 (af_acc_live RT AF Σc m _ _ ART0 INS'))| lia| lia].
  - left. exists (pa_SBUF E), (pa_NS E). split; [exact INS'| lia].
Qed.

Lemma f1_rngA : forall E D C f FRP Σc st m Src n w shp, pjenvA_ok E -> cctxA E D C -> octxA E C f ->
  CERMA RT E C FRP Σc st m -> FRP = obj_frp E C f w shp -> f + 24 <= Src -> 0 <= n -> Src + n <= f + 120 ->
  rng_class RT Σc Src n /\ 0 <= Src /\ Src + n <= pa_lo E /\ exists src, bytes_at bsegs m Src src /\ Z.of_nat (length src) = n.
Proof.
  intros until shp. intros OK CX OX [HR HC] -> H1 Hn H2. pose proof HR as (_ & _ & FR & _). pose proof HC as ((_ & _ & _ & _ & _ & F1S & _) & _).
  pose proof (oc_f E C f OX) as (F0 & _ & _ & FLO).
  split. { right; left. exists f, 1%nat. split; [rewrite FR, (oc_fr E C f OX); left; reflexivity| rewrite fs1; lia]. }
  split; [lia|]. split; [lia|].
  destruct (stk_split bsegs m _ Src _ F1S ltac:(lia)) as [_ S1].
  destruct (stk_split bsegs m _ (Src + n) _ S1 ltac:(lia)) as [S2 _].
  destruct (stk_bytes bsegs m _ _ S2 ltac:(lia)) as (bs & HL & HB).
  exists bs. split; [exact HB|]. rewrite HL. lia.
Qed.
End Kit.

Ltac obj_envA OK CX OX :=
  cont_envA OK CX;
  lazymatch type of OX with octxA ?E ?C ?f =>
  let Hf := fresh in pose proof (oc_f E C f OX) as Hf;
  let FSG := fresh "FSG" in destruct Hf as (F0 & F64 & FSG & FLO); unfold SEGTOP_A in FSG;
  assert (Ef : 8 * (f / 8) = f) by (clear - F64; Z.div_mod_to_equations; lia); clear F64;
  match goal with LOx : _ <= pa_lo E, QT : ci_q C + 16 <= _, LB : pa_lo E + 66096 <= ci_b C |- _ =>
    assert (SFL : f / 8 + 2147450880 + 16 <= pa_lo E /\ 901120 <= f / 8) by (clear - Ef FLO LOx F0 FSG; lia) end;
  pose proof (oc_bq E C f OX) as OBQ;
  let H := fresh in pose proof (env_rangesA E OK) as H;
  let B1 := fresh in let B2 := fresh in let D1 := fresh in let D2 := fresh in
  destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & B1 & B2 & D1 & D2 & _);
  let FF := fresh in pose proof (oc_fF E C f OX) as FF;
  assert (FSB : f + 128 <= pa_SB E \/ pa_SB E + 96 <= f) by (clear - FF B1 B2; lia);
  assert (FDOC : f + 128 <= pa_DOC E \/ pa_DOC E + 24 <= f) by (clear - FF D1 D2; lia);
  let F1 := fresh in pose proof (oc_F_shf E C f OX) as F1;
  assert (SHSB : pa_SB E + 96 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= pa_SB E) by (clear - F1 B1 B2; lia);
  assert (SHDC : pa_DOC E + 24 <= f / 8 + 2147450880 \/ f / 8 + 2147450880 + 16 <= pa_DOC E) by (clear - F1 D1 D2; lia);
  pose proof (oc_f_shf E C f OX) as SHf;
  clear B1 B2 D1 D2 FF F1 FSG;
  lazymatch type of FSB with ?T => change (boxP T) in FSB end; lazymatch type of FDOC with ?T => change (boxP T) in FDOC end;
  lazymatch type of SHSB with ?T => change (boxP T) in SHSB end; lazymatch type of SHDC with ?T => change (boxP T) in SHDC end;
  lazymatch type of SHf with ?T => change (boxP T) in SHf end
  end.

Ltac obj_open HM OK CX OX :=
  cont_open HM OK CX;
  let M := match goal with M : munch _ _ _ |- _ => M end in rewrite (oc_R _ _ _ OX) in M; unfold obj_R_ in M; cbn [app] in M;
  let H := match goal with H : obj_frp _ _ _ _ _ _ |- _ => H end in
  lazymatch type of H with obj_frp _ _ _ ?w _ _ =>
    destruct H as (FR0 & FR & GAP & FS & FH & F1S & SHF & SHL); unfold co_savedA in FS; unfold obj_hdrA in FH;
    unfold sh16 in SHF; try (unfold obj_shpatA in SHF; cbn [map] in SHF);
    first [ is_var w; destruct w as [?w8 ?w16 ?w24 ?w32 ?w40 ?w48 ?w56 ?w64 ?w72 ?w80 ?w88 ?w96 ?w104 ?w112 ?w120 ?w128 ?w136 ?w144 ?w152 ?w160 ?w168 ?w176 ?w184
                                     ?w192 ?w200 ?w208 ?w216 ?w224 ?w232 ?w240]
          | idtac ];
    unfold obj_slotsA, owK in FR;
    cbn [ow8 ow16 ow24 ow32 ow40 ow48 ow56 ow64 ow72 ow80 ow88 ow96 ow104 ow112 ow120 ow128 ow136 ow144 ow152 ow160 ow168 ow176 ow184 ow192 ow200 ow208 ow216 ow224 ow232 ow240] in FR
  end.

Ltac obj_close HM OX :=
  match goal with
  | HREF : CREFA ?RT ?E ?C ?Σc ?st ?mr, M : munch _ ?mr ?m, OK : pjenvA_ok ?E, CX : cctxA ?E _ ?C,
    FR0 : stk _ ?m (ci_b ?C) _, FR : rw_cells _ ?m (ci_b ?C + 8) _, GAP : stk _ ?m (ci_b ?C + 248) _, FS : rw_cells _ ?m (ci_q ?C - 104) _,
    FH : rw_cells _ ?m ?f [_; _; _], F1S : stk _ ?m (?f + 24) _, SHF : rw_cells _ ?m (?f / 8 + 2147450880) _, SHL : length ?shp = 16%nat |- _ =>
      let w := lazymatch type of FR with
               | rw_cells _ _ _ [C8 ?a8; C8 ?a16; C8 ?a24; C8 ?a32; C8 ?a40; C8 ?a48; C8 ?a56; C8 ?a64; C8 ?a72; C8 ?a80; C8 ?a88; C8 ?a96; C8 ?a104; C8 ?a112; C8 ?a120; C8 ?a128;
                                 C8 ?a136; C8 ?a144; C8 ?a152; C8 ?a160; C8 ?a168; C8 ?a176; C8 ?a184; C8 ?a192; C8 ?a200; C8 ?a208; C8 ?a216; C8 ?a224; C8 ?a232; C8 ?a240] =>
                   constr:(mkOW a8 a16 a24 a32 a40 a48 a56 a64 a72 a80 a88 a96 a104 a112 a120 a128 a136 a144 a152 a160 a168 a176 a184 a192 a200 a208 a216 a224 a232 a240)
               | _ => fail 100 "obj_close: FR has not the 30-word shape (a CB 8 junk cell left? apply rw_cells_c8ify in FR; cbn [map c8c Nat.eqb] in FR)" end in
      let HFRP := fresh "HFRP" in
      first [ assert (HFRP : obj_frp E C f w shp m)
                by (split; [exact FR0| split; [exact FR| split; [exact GAP| split; [exact FS| split; [exact FH| split; [exact F1S| split; [exact SHF| exact SHL]]]]]]])
            | fail 100 "obj_close: cannot rebuild obj_frp (SHF must be convertible with sh16 shp: the 16 shadow cells of obj_shpatA)" ];
      apply (munch_conWAf E C f st _ _ (oc_R _ _ _ OX)) in M;
      cont_close HM HFRP OK CX; clear FR0 FR GAP FS FH F1S SHF; try clear SHL
  | _ => fail 100 "obj_close: the open object context is incomplete (need HREF MU OK CX FR0 FR GAP FS FH F1S SHF SHL)"
  end.

Ltac omuc OX := match goal with HREF : CREFA _ ?E' ?C' _ ?st ?mr, M : munch _ ?mr ?m |- _ => constr:(munch_conWAf E' C' _ st mr m (oc_R _ _ _ OX) M) end.

Section Stmts.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Notation aevt := (aevt RT PMc).
Notation SH72 E := ((pa_SB E + 72) / 8 + 2147450880).
Notation SHD8 E := ((pa_DOC E + 8) / 8 + 2147450880).

Definition okey1_stmtA : Prop :=
  forall (E : pjenvA) (D : nat) (C : conI) (f : Z) (K : config -> Prop) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (x c l x1 cx A X : Z) (x24 x32 x40 x48 x56 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs6 xs10 xt3 xt4 xt5 xt6 : word),
    pjenvA_ok E -> cctxA E D C -> octxA E C f -> ser_cpsA RT PMc D ->
    CERMA RT E C (obj_frp E C f (owK E C f x24 x32 x40 x48 x56 x72 x80 x88 x96 x104 x112 x120 x128 x136 x144 x152 x160 x176 x224 x232) obj_shpatA) Σ st m -> frm0 fc ->
    2 <= x -> x + 1 < x1 -> x1 <= ci_e C -> pa_T E x = tword t_str c -> str_at (pa_S E) (pa_sn E) c l ->
    elemS (pa_T E) (pa_S E) (pa_sn E) ck_any D (x + 1) x1 (c + l + 5) cx -> cx <= pa_sn E ->
    sa_size st <= A -> A + (3 + 6 * l) <= 41 * x + 6 * (c + l + 5) + 3 -> A + (3 + 6 * l) <= PJ_OUTMAX (pa_len E) ->
    CCREDA RT E C Σ X st -> 2 * (x1 - (x + 1)) <= X ->
    (forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y24 y32 y40 y72 y104 y112 y120 y136 y224 y232 : word)
            (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys6 ys7 ys9 yt3 yt4 yt5 yt6 : word),
       CERMA RT E C (obj_frp E C f (owK E C f y24 y32 y40 (wz (x - 1)) (wz (pa_DOC E + 8)) y72 (wz (pa_DOC E)) (wz M56M1) (wz (SHD8 E)) y104 y112 y120
                                        (wz (f + 64)) y136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A) (wz (pa_SB E)) y224 y232) obj_shpatA) Σ' st' m' ->
       frm0 fc' -> sb_accA st' x1 cx -> CCREDA RT E C Σ' (X - 2 * (x1 - (x + 1))) st' ->
       aevt Σ' K (OST E C 0xbc88c yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) (wz (x + 1)) ys6 ys7 ys9
                      (wz PJ_NE_TAB_A) (wz (pa_SB E)) yt3 yt4 yt5 yt6 F' fc' m')) ->
    aevt Σ K (OST E C 0xbbb78 xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (wz (SH72 E)) xa5 xa6 xa7 (wz x) (wz f) xs5 xs6 (wz (pa_DOC E)) (wz (x - 1)) xs10 (wz (pa_SB E))
                   xt3 xt4 xt5 xt6 F fc m).

Definition okey2_stmtA : Prop :=
  forall (E : pjenvA) (D : nat) (C : conI) (f : Z) (K : config -> Prop) (Σ : rts RT) (st : sbA) (m : mem) (F : bvmap 5 word) (fc : bv 32)
         (x c l x1 cx A X : Z) (x48 x72 x104 x136 x224 x232 : word)
         (xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa5 xa6 xa7 xs5 xs9 xt3 xt4 xt5 xt6 : word),
    pjenvA_ok E -> cctxA E D C -> octxA E C f -> ser_cpsA RT PMc D ->
    CERMA RT E C (obj_frp E C f (owK E C f (wz M32M1) (wz M32P1) (wz MNUMK) x48 (wz (pa_DOC E + 8)) x72 (wz (pa_DOC E)) (wz M56M1) (wz (SHD8 E)) x104
                                     (wz (f + 65)) (wz (18446744073709551615 - (f + 65))) (wz (f + 64)) x136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A)
                                     (wz (pa_SB E)) x224 x232) obj_shpatA) Σ st m -> frm0 fc ->
    2 <= x -> x + 1 < x1 -> x1 <= ci_e C -> pa_T E x = tword t_str c -> str_at (pa_S E) (pa_sn E) c l ->
    elemS (pa_T E) (pa_S E) (pa_sn E) ck_any D (x + 1) x1 (c + l + 5) cx -> cx <= pa_sn E ->
    sa_size st <= A -> A + (3 + 6 * l) <= 41 * x + 6 * (c + l + 5) + 3 -> A + (3 + 6 * l) <= PJ_OUTMAX (pa_len E) ->
    CCREDA RT E C Σ X st -> 2 * (x1 - (x + 1)) <= X ->
    (forall (Σ' : rts RT) (st' : sbA) (m' : mem) (F' : bvmap 5 word) (fc' : bv 32) (y48 y72 y136 y224 y232 : word)
            (yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 ys5 ys9 yt3 yt4 yt5 yt6 : word),
       CERMA RT E C (obj_frp E C f (owK E C f (wz M32M1) (wz M32P1) (wz MNUMK) y48 (wz (pa_DOC E + 8)) y72 (wz (pa_DOC E)) (wz M56M1) (wz (SHD8 E)) (wz (x + 1))
                                        (wz (f + 65)) (wz (18446744073709551615 - (f + 65))) (wz (f + 64)) y136 (wz PJ_ESC_TAB_A) (wz PJ_RO184_A) (wz PJ_RO176_A)
                                        (wz (pa_SB E)) y224 y232) obj_shpatA) Σ' st' m' ->
       frm0 fc' -> sb_accA st' x1 cx -> CCREDA RT E C Σ' (X - 2 * (x1 - (x + 1))) st' ->
       aevt Σ' K (OST E C 0xbd6d4 yra yt0 yt1 yt2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) ys5 (wz (x + 1)) (wz x) ys9
                      (wz PJ_NE_TAB_A) (wz (pa_SB E)) yt3 yt4 yt5 yt6 F' fc' m')) ->
    aevt Σ K (OST E C 0xbcb9c xra xt0 xt1 xt2 xa0 xa1 xa2 xa3 (wz (SH72 E)) xa5 xa6 xa7 (wz (pa_DOC E)) (wz (18446744073709551615 - PJ_NE_TAB_A)) xs5 (wz (pa_DOC E + 8)) (wz x) xs9
                   (wz PJ_NE_TAB_A) (wz (pa_SB E)) xt3 xt4 xt5 xt6 F fc m).
End Stmts.
