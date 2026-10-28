(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.P Require Import Str_tac Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface RT_iface2 RT_iface3 D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit Atp_fzwA Atp_defsA Atp_kitA Pj_rtkA Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA Pj_ser_trefA Dmp_hdefsA Dmp_pj_ifaceA Dmp_pj_kitA Dmp_pj_leafA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition litA (A : Z) (n : nat) : list byte := match image_bytes bsegs A n with Some bs => bs | None => [] end.
Lemma litA_bytes : forall A n, ro_bytes_b bsegs A (litA A n) = true -> length (litA A n) = n -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  forall m, mem_inv bsegs m -> bytes_at bsegs m A (litA A n) /\ ro_bytes bsegs A (litA A n).
Proof.
  intros A n RB L A0 AH m MI. pose proof (ro_bytes_b_sound _ _ _ RB) as RO. split; [| exact RO].
  apply ro_bytes_at; [exact MI| lia| rewrite L; lia| exact RO].
Qed.

Lemma wr_at_cell : forall m A n i w, wr_at bsegs m A n -> 0 <= i -> 0 <= w -> i + w <= n -> exists j, rw_cells bsegs m (A + i) [CB (Z.to_nat w) j].
Proof.
  intros m A n i w WA I0 W0 IW. exact (wr_at_rw_CB m (A + i) w (wr_at_sub m A n (A + i) w WA ltac:(lia) ltac:(lia) W0) W0).
Qed.

Lemma wr_at_cells1 : forall m A (n : nat), wr_at bsegs m A (Z.of_nat n) -> exists ls, length ls = n /\ rw_cells bsegs m A (pj_shadow0 ls).
Proof.
  intros m A n WA. revert A WA. induction n as [|n IH]; intros A WA.
  - exists []. split; [reflexivity|]. pose proof WA as (A0 & AH & _). split; [split; [exact I| split; [lia| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]]|].
    split; [lia|]. split; [cbn; lia| intros i Hi; cbn in Hi; lia].
  - destruct (wr_at_cell m A (Z.of_nat (S n)) 0 1 WA ltac:(lia) ltac:(lia) ltac:(lia)) as [j FJ]. replace (A + 0) with A in FJ by lia.
    destruct (IH (A + 1) (wr_at_sub m A (Z.of_nat (S n)) (A + 1) (Z.of_nat n) WA ltac:(lia) ltac:(lia) ltac:(lia))) as (ls & LS & FL).
    exists (j :: ls). split; [cbn; rewrite LS; reflexivity|]. unfold pj_shadow0. cbn [map].
    change (CB 1 j :: map (fun l => CB 1 l) ls) with ([CB 1 j] ++ pj_shadow0 ls). apply rw_cells_app. split; [exact FJ|]. cbn [cells_size csize Nat.add].
    exact FL.
Qed.

Fixpoint inW (W : list (Z * Z)) (a : Z) : Prop := match W with [] => False | (lo, hi) :: W' => (lo <= a < hi) \/ inW W' a end.
Lemma outside_dec : forall W a, outside W a \/ inW W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a; [left; exact I|]. cbn [outside inW].
  destruct (IH a) as [O|IN]; [| right; right; exact IN].
  destruct (Z_le_dec lo a); [destruct (Z_lt_dec a hi); [right; left; lia|]|]; left; split; [lia| exact O| lia| exact O].
Qed.

Lemma rw_cells_mid : forall m A pre mid post, rw_cells bsegs m A (pre ++ mid ++ post) -> rw_cells bsegs m (A + Z.of_nat (cells_size pre)) mid.
Proof. intros m A pre mid post H. apply rw_cells_app in H. destruct H as [_ H]. apply rw_cells_app in H. destruct H as [H _]. exact H. Qed.
Lemma rw_cells_reasm : forall m m' A pre mid mid' post,
  rw_cells bsegs m A (pre ++ mid ++ post) ->
  agree_on (fun x => (A <= x < A + Z.of_nat (cells_size pre))
                     \/ (A + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid) <= x < A + Z.of_nat (cells_size (pre ++ mid ++ post)))) m m' ->
  rw_cells bsegs m' (A + Z.of_nat (cells_size pre)) mid' -> cells_size mid' = cells_size mid ->
  rw_cells bsegs m' A (pre ++ mid' ++ post).
Proof.
  intros m m' A pre mid mid' post H AG HM SZ. rewrite !cells_size_app in AG.
  apply rw_cells_app in H. destruct H as [H1 H]. apply rw_cells_app in H. destruct H as [_ H3].
  apply rw_cells_app. split.
  - apply (rw_cells_agree_nw bsegs m m' _ _ H1). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. left. exact Hx.
  - apply rw_cells_app. split; [exact HM|]. rewrite SZ. apply (rw_cells_agree_nw bsegs m m' _ _ H3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx |- *. right. lia.
Qed.

Lemma sbuf_sliceA : forall m (SBUF : Z) (sbs : list Z) (o l : Z),
  bytes_at bsegs m SBUF (map (Z_to_bv 8) sbs) -> 0 <= o -> 0 <= l -> o + 4 + l < Z.of_nat (length sbs) ->
  bytes_at bsegs m (SBUF + o + 4) (firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) sbs)))
  /\ Z.of_nat (length (firstn (Z.to_nat l) (skipn (Z.to_nat (o + 4)) (map (Z_to_bv 8) sbs)))) = l.
Proof.
  intros m SBUF sbs o l HB Ho Hl Hol. split.
  - replace (SBUF + o + 4) with (SBUF + Z.of_nat (Z.to_nat (o + 4))) by lia.
    apply bytes_at_firstn. apply bytes_at_skipn; [exact HB|]. rewrite length_map. lia.
  - rewrite firstn_length_le; [lia|]. rewrite length_skipn, length_map. lia.
Qed.

Record pctx : Type := mkG {
  g_E : aenvA;
  g_q : Z;
  g_OS : Z;
  g_fO : Z; g_kO : nat;
  g_ff : Z;
  g_rfr : list (Z * nat);
  g_L : list (Z * Z);
  g_sp0 : Z;
  g_cr : Z;
  g_m0 : mem;
  g_d : nat }.
Notation g_S1 G := (g_q G - 256).
Notation g_fr G := ((g_ff G, 2%nat) :: g_rfr G).
Notation g_lo G := (ae_lo (g_E G)).

Record pctx_ok (G : pctx) : Prop := mkGok {
  go_q : g_q G mod 32 = 0 /\ g_q G + 16 <= USTACK_TOP /\ g_lo G + pj_needA (g_d G) <= g_q G;
  go_lo : 0x7fff7f800000 <= g_lo G /\ g_sp0 G - STACK_WIN <= g_lo G;
  go_sp0 : SEGTOP_A + STACK_WIN <= g_sp0 G <= USTACK_TOP /\ 0x7fff80000000 <= g_sp0 G;
  go_E : aenvA_ok (g_E G) /\ In (ae_TAPE (g_E G), ae_NT (g_E G)) (g_L G) /\ In (ae_SBUF (g_E G), ae_NS (g_E G)) (g_L G)
         /\ (ae_p1 (g_E G) = [] \/ In (ae_PB (g_E G), ae_NPB (g_E G)) (g_L G)) /\ In (ae_fD (g_E G), ae_kD (g_E G)) (g_rfr G);
  go_OS : In (g_fO G, g_kO G) (g_rfr G) /\ g_fO G <= g_OS G /\ g_OS G + 288 <= g_fO G + fs_size (g_kO G) - 8 /\ g_OS G mod 16 = 0
         /\ (ae_DOC (g_E G) + 16 <= g_OS G \/ g_OS G + 288 <= ae_DOC (g_E G));
  go_ff : 0 < g_ff G /\ g_ff G mod 64 = 0 /\ SEGTOP_A <= g_ff G /\ g_ff G + 256 <= g_lo G
         /\ (g_ff G + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= g_ff G)
         /\ shad (g_ff G) + 32 + 1 <= g_lo G /\ (g_ff G + 256 <= shad (g_ff G) \/ shad (g_ff G) + 32 <= g_ff G);

  go_ffr : forall f k, In (f, k) (g_rfr G) ->
         (g_ff G + 256 <= f \/ f + fs_size k <= g_ff G) /\ (f + fs_size k <= shad (g_ff G) \/ shad (g_ff G) + 32 <= f)
         /\ (g_ff G + 256 <= shad f \/ shad (f + fs_size k) <= g_ff G);

  go_ffL : forall p n, In (p, n) (g_L G) -> (g_ff G + 256 <= p \/ p + n <= g_ff G) /\ (p + n <= shad (g_ff G) \/ shad (g_ff G) + 32 <= p);

  go_rfr : forall f k, In (f, k) (g_rfr G) -> 0 < f /\ SEGTOP_A <= f /\ f + fs_size k <= g_lo G /\ SHB <= shad f /\ shad (f + fs_size k) + 1 <= g_lo G
         /\ (f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f)
         /\ (forall p n, In (p, n) (g_L G) -> (f + fs_size k <= p \/ p + n <= f) /\ (p + n <= shad f \/ shad (f + fs_size k) <= p));
  go_rfr2 : forall f k f' k', In (f, k) (g_rfr G) -> In (f', k') (g_rfr G) -> f' + fs_size k' <= shad f \/ shad (f + fs_size k) <= f';
  go_L : forall p n, In (p, n) (g_L G) -> 0 < p /\ p + n <= g_lo G /\ (p + n <= 0x10000 \/ SEGTOP_A <= p);
  go_len : Z.of_nat (length (g_rfr G)) + Z.of_nat (g_d G) + 3 <= FRAMES_TOT }.

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Local Ltac ow := repeat split; try exact I; ul.

Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis SM2 : stack_malloc2_contract RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Definition PINVA (G : pctx) (fcs : list cell) (k : Z) (Σ : rts RT) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv bsegs m
  /\ rt_frames RT Σ = g_fr G /\ rt_live RT Σ = g_L G /\ rt_sp0 RT Σ = g_sp0 G /\ g_cr G - k <= rt_credit RT Σ
  /\ stk bsegs m (g_lo G) (g_S1 G)
  /\ OSXF m (g_OS G) /\ bytes_at bsegs m (shad (g_OS G)) (repeat z8 36)
  /\ el_tploc m /\ LOCBA m
  /\ (rw_cells bsegs m (g_S1 G) fcs /\ cells_size fcs = 256%nat)
  /\ wr_at bsegs m (g_ff G) 248 /\ wr_at bsegs m (shad (g_ff G)) 32
  /\ (forall a : word, aclient (g_L G) (g_rfr G) (g_q G) (bv_unsigned a) -> outside (pj_WA (g_OS G)) (bv_unsigned a) -> m a = g_m0 G a).

Lemma PINVA_mono_k : forall G fcs k k' Σ m, PINVA G fcs k Σ m -> k <= k' -> PINVA G fcs k' Σ m.
Proof.
  intros G fcs k k' Σ m (HA & MI & FRS & LV & SP0 & CR & REST) LE.
  split; [exact HA|]. split; [exact MI|]. split; [exact FRS|]. split; [exact LV|]. split; [exact SP0|]. split; [clear - CR LE; lia| exact REST].
Qed.

Definition KEXITA (G : pctx) (fcs : list cell) (kx : Z) (K : config -> Prop) (gp : word) : Prop :=
  forall (Σ' : rts RT) (m' : mem) (ra a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s8 s9 s10 t0 t1 t2 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (k' : Z),
    PINVA G fcs k' Σ' m' -> k' <= kx -> frm0 fc' ->
    aevt Σ' K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 (wz (g_q G)) (wz (g_S1 G)) a0 a1 a2 a3 a4 a5 a6 a7
                      s2 (wz (g_ff G)) s4 s5 s6 (wz (g_ff G)) s8 s9 s10 (wz (shad (g_ff G))) t3 t4 t5 t6) F' (wz DMP_PJ_EXIT_A) fc' None m' (seg_rom bsegs)).

Section G.
  Variable G : pctx.
  Hypothesis GOK : pctx_ok G.

  Definition own (a : Z) : Prop :=
    g_S1 G <= a < g_q G \/ g_ff G <= a < g_ff G + 248 \/ shad (g_ff G) <= a < shad (g_ff G) + 32.

  Lemma own_aclient : forall a, own a -> aclient (g_L G) (g_fr G) (g_S1 G) a.
  Proof using AF GOK.
    intros a [H|[H|H]].
    - left. destruct GOK as [(_ & Q & _) _ _ _ _ _ _ _ _ _ _ _]. ul.
    - right; right; right; left. exists (g_ff G), 2%nat. split; [left; reflexivity| change (fs_size 2) with 256; lia].
    - do 4 right. exists (g_ff G), 2%nat. split; [left; reflexivity|].
      destruct GOK as [_ _ _ _ _ (F0 & F64 & _) _ _ _ _ _ _]. change (fs_size 2) with 256. unfold shad in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma own_not_caller : forall a, own a -> ~ aclient (g_L G) (g_rfr G) (g_q G) a.
  Proof using AF GOK.
    intros a OW CA. destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ _ (F0 & F64 & FSEG & FLO & FHI & SHLO & SHAP) FFR FFL RFR _ LL _].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
    unfold own in OW. unfold shad in *.
    destruct CA as [H|[H|[H|[H|H]]]].
    - ul.
    - pose proof (client_static_range a H) as R. ul.
    - destruct H as (p & n & Hin & Hp). pose proof (FFL p n Hin) as [A1 A2]. pose proof (LL p n Hin) as (B1 & B2 & _). ul.
    - destruct H as (f & k & Hin & Hf). pose proof (FFR f k Hin) as (A1 & A2 & A3). pose proof (RFR f k Hin) as (B1 & B2 & B3 & B4 & B5 & _).
      assert (0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia). ul.
    - destruct H as (f & k & Hin & Hf). pose proof (FFR f k Hin) as (A1 & A2 & A3). pose proof (RFR f k Hin) as (B1 & B2 & B3 & B4 & B5 & _).
      assert (0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia). unfold shad in Hf.
      destruct OW as [O|[O|O]]; [ul| ul|].
      destruct A1 as [A1|A1].
      + pose proof (Z.div_le_mono (g_ff G + 256) f 8 ltac:(lia) A1). ul.
      + pose proof (Z.div_le_mono (f + fs_size k) (g_ff G) 8 ltac:(lia) A1) as X. ul.
  Qed.

  Lemma os_not_own : forall a, (g_OS G <= a < g_OS G + 288 \/ shad (g_OS G) <= a < shad (g_OS G) + 36 \/ 0 <= a < SEGTOP_A) -> ~ own a.
  Proof using AF GOK.
    intros a Ha OW. destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ (EIN & ELO & EHI & E16 & _) (F0 & F64 & FSEG & FLO & FHI & SHLO & SHAP) FFR FFL RFR _ LL _].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
    pose proof (FFR _ _ EIN) as (A1 & A2 & A3). pose proof (RFR _ _ EIN) as (B1 & B2 & B3 & B4 & B5 & _).
    assert (FS0 : 0 <= fs_size (g_kO G)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold own in OW. unfold shad in *.
    destruct Ha as [H|[H|H]]; [| | ul].
    - destruct OW as [O|[O|O]]; [ul| ul| ul].
    - destruct OW as [O|[O|O]]; [ul| | ].
      + destruct A3 as [A3|A3].
        * assert (g_OS G / 8 + 36 <= (g_fO G + fs_size (g_kO G)) / 8) by (clear - EHI E16; Z.div_mod_to_equations; lia).
          assert (g_fO G / 8 <= g_OS G / 8) by (apply Z.div_le_mono; lia). clear - H O A3 H0 H1 B4. Z.div_mod_to_equations. lia.
        * assert (g_OS G / 8 + 36 <= (g_fO G + fs_size (g_kO G)) / 8) by (clear - EHI E16; Z.div_mod_to_equations; lia). clear - H O A3 H0. lia.
      + destruct A1 as [A1|A1].
        * pose proof (Z.div_le_mono (g_ff G + 256) (g_fO G) 8 ltac:(lia) A1). assert (g_fO G / 8 <= g_OS G / 8) by (apply Z.div_le_mono; lia). ul.
        * pose proof (Z.div_le_mono (g_fO G + fs_size (g_kO G)) (g_ff G) 8 ltac:(lia) A1).
          assert (g_OS G / 8 + 36 <= (g_fO G + fs_size (g_kO G)) / 8) by (clear - EHI E16; Z.div_mod_to_equations; lia). clear - H O H0 H1 F64. Z.div_mod_to_equations. lia.
  Qed.

  Lemma PINVA_cw : forall fcs fcs' k Σ m m' W0,
    PINVA G fcs k Σ m -> munch W0 m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
    (forall a, outside W0 a \/ own a) -> rw_cells bsegs m' (g_S1 G) fcs' -> cells_size fcs' = 256%nat ->
    PINVA G fcs' k Σ m'.
  Proof using AF GOK.
    intros fcs fcs' k Σ m m' W0 GI MU WM MI' HW FR' FSZ'.
    destruct GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ _ (F0 & F64 & FSEG & FLO & FHI & SHLO & SHAP) FFR FFL RFR _ LL _].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
    assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ own x) -> agree_on P m m').
    { intros P HP a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X| exfalso; exact (HP _ Ha X)]. }
    split. { apply (art_client_write RT AF Σ m m' (g_S1 G) HA); [rewrite SP0; clear - LO2 LQ ND; ul| | exact WM].
             intros a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. apply Ha. rewrite FRS, LV. exact (own_aclient _ X). }
    split; [exact MI'|]. split; [exact FRS|]. split; [exact LV|]. split; [exact SP0|]. split; [exact CR|].
    split. { apply (stk_agree bsegs m m' _ _ ST); [| exact WM]. apply AG. intros x Hx OW. unfold own in OW. clear - Hx OW LQ FLO SHLO ND. unfold shad in *. ul. }
    split. { exists fill. split; [| exact FOK]. apply (OSX_agree m m' _ _ OX); [| exact WM]. apply AG. intros x Hx. apply os_not_own. left. exact Hx. }
    split. { apply (bytes_at_agree bsegs m m' _ _ SHO). apply AG. intros x Hx. apply os_not_own. right; left. rewrite repeat_length in Hx. lia. }
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ TPL). apply AG. intros x Hx. apply os_not_own. do 2 right. cbn [cells_size csize Nat.add] in Hx. ul. }
    split. { apply (LOCBA_agree m m' LB). apply AG. intros x Hx. apply os_not_own. do 2 right. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. ul. }
    split; [split; [exact FR'| exact FSZ']|]. split; [exact (wr_at_transport bsegs m m' _ _ WF1 WM)|]. split; [exact (wr_at_transport bsegs m m' _ _ WF2 WM)|].
    intros a CA OU. rewrite <- (REL a CA OU). apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. exact (own_not_caller _ X CA).
  Qed.

  Definition ownB (a : Z) : Prop :=
    g_lo G <= a < g_q G \/ g_ff G <= a < g_ff G + 248 \/ shad (g_ff G) <= a < shad (g_ff G) + 32.
  Lemma own_ownB : forall a, own a -> ownB a.
  Proof using AF GOK.
    intros a [H|[H|H]]; [| right; left; exact H| do 2 right; exact H]. left.
    destruct GOK as [(_ & _ & LQ) _ _ _ _ _ _ _ _ _ _ _]. pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND. lia.
  Qed.
  Lemma ownB_aclient : forall a, ownB a -> aclient (g_L G) (g_fr G) (g_lo G) a.
  Proof using AF GOK.
    intros a [H|[H|H]].
    - left. destruct GOK as [(_ & Q & _) _ _ _ _ _ _ _ _ _ _ _]. ul.
    - right; right; right; left. exists (g_ff G), 2%nat. split; [left; reflexivity| change (fs_size 2) with 256; lia].
    - do 4 right. exists (g_ff G), 2%nat. split; [left; reflexivity|].
      destruct GOK as [_ _ _ _ _ (F0 & F64 & _) _ _ _ _ _ _]. change (fs_size 2) with 256. unfold shad in *. Z.div_mod_to_equations. lia.
  Qed.
  Lemma ownB_not_caller : forall a, ownB a -> ~ aclient (g_L G) (g_rfr G) (g_q G) a.
  Proof using AF GOK.
    intros a OW CA. destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ _ (F0 & F64 & FSEG & FLO & FHI & SHLO & SHAP) FFR FFL RFR _ LL _].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
    unfold ownB in OW. unfold shad in *.
    destruct CA as [H|[H|[H|[H|H]]]].
    - ul.
    - pose proof (client_static_range a H) as R. ul.
    - destruct H as (p & n & Hin & Hp). pose proof (FFL p n Hin) as [A1 A2]. pose proof (LL p n Hin) as (B1 & B2 & _). ul.
    - destruct H as (f & k & Hin & Hf). pose proof (FFR f k Hin) as (A1 & A2 & A3). pose proof (RFR f k Hin) as (B1 & B2 & B3 & B4 & B5 & _).
      assert (0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia). ul.
    - destruct H as (f & k & Hin & Hf). pose proof (FFR f k Hin) as (A1 & A2 & A3). pose proof (RFR f k Hin) as (B1 & B2 & B3 & B4 & B5 & _).
      assert (0 <= fs_size k) by (unfold fs_size; apply Z.shiftl_nonneg; lia). unfold shad in Hf.
      destruct OW as [O|[O|O]]; [ul| ul|].
      destruct A1 as [A1|A1].
      + pose proof (Z.div_le_mono (g_ff G + 256) f 8 ltac:(lia) A1). ul.
      + pose proof (Z.div_le_mono (f + fs_size k) (g_ff G) 8 ltac:(lia) A1) as X. ul.
  Qed.

  Lemma PINVA_cwB : forall fcs fcs' k Σ m m' W0,
    PINVA G fcs k Σ m -> munch W0 m m' -> wmono bsegs m m' -> mem_inv bsegs m' ->
    (forall a, outside W0 a \/ ownB a) -> stk bsegs m' (g_lo G) (g_S1 G) -> rw_cells bsegs m' (g_S1 G) fcs' -> cells_size fcs' = 256%nat ->
    PINVA G fcs' k Σ m'.
  Proof using AF GOK.
    intros fcs fcs' k Σ m m' W0 GI MU WM MI' HW ST' FR' FSZ'.
    destruct GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ _ (F0 & F64 & FSEG & FLO & FHI & SHLO & SHAP) FFR FFL RFR _ LL _].
    assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ ownB x) -> agree_on P m m').
    { intros P HP a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X| exfalso; exact (HP _ Ha X)]. }
    assert (NOS : forall a, (g_OS G <= a < g_OS G + 288 \/ shad (g_OS G) <= a < shad (g_OS G) + 36 \/ 0 <= a < SEGTOP_A) -> ~ ownB a).
    { intros a Ha OW. destruct OW as [O|OW]; [| exact (os_not_own a Ha ltac:(right; exact OW))].
      destruct GOK as [_ _ _ _ (EIN & ELO & EHI & E16 & _) _ _ _ _ _ _ _]. pose proof (RFR _ _ EIN) as (B1 & B2 & B3 & B4 & B5 & _).
      assert (XS : g_OS G / 8 + 36 <= (g_fO G + fs_size (g_kO G)) / 8) by (clear - EHI E16; Z.div_mod_to_equations; lia).
      unfold shad in *. clear - Ha O B3 B5 ELO EHI LO1 XS. ul. }
    split. { apply (art_client_write RT AF Σ m m' (g_lo G) HA); [rewrite SP0; exact LO2| | exact WM].
             intros a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. apply Ha. rewrite FRS, LV. exact (ownB_aclient _ X). }
    split; [exact MI'|]. split; [exact FRS|]. split; [exact LV|]. split; [exact SP0|]. split; [exact CR|].
    split; [exact ST'|].
    split. { exists fill. split; [| exact FOK]. apply (OSX_agree m m' _ _ OX); [| exact WM]. apply AG. intros x Hx. apply NOS. left. exact Hx. }
    split. { apply (bytes_at_agree bsegs m m' _ _ SHO). apply AG. intros x Hx. apply NOS. right; left. rewrite repeat_length in Hx. lia. }
    split. { apply (rw_cells_agree_nw bsegs m m' _ _ TPL). apply AG. intros x Hx. apply NOS. do 2 right. cbn [cells_size csize Nat.add] in Hx. ul. }
    split. { apply (LOCBA_agree m m' LB). apply AG. intros x Hx. apply NOS. do 2 right. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. ul. }
    split; [split; [exact FR'| exact FSZ']|]. split; [exact (wr_at_transport bsegs m m' _ _ WF1 WM)|]. split; [exact (wr_at_transport bsegs m m' _ _ WF2 WM)|].
    intros a CA OU. rewrite <- (REL a CA OU). apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. exact (ownB_not_caller _ X CA).
  Qed.

  Lemma PINVA_lowB : forall fcs k Σ m m' W0,
    PINVA G fcs k Σ m -> munch W0 m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (g_lo G) (g_S1 G) ->
    (forall a, outside W0 a \/ g_lo G <= a < g_S1 G) -> PINVA G fcs k Σ m'.
  Proof using AF GOK.
    intros fcs k Σ m m' W0 GI MU WM MI' ST' HW.
    pose proof GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & FSZ) & _).
    eapply (PINVA_cwB fcs fcs k Σ m m' W0 GI MU WM MI'); [| exact ST'| | exact FSZ].
    - intros a. destruct (HW a) as [X|X]; [left; exact X| right; left; lia].
    - eapply rw_cells_agree_nw; [exact FR|]. apply (agree_of_munch _ _ _ _ MU). intros x Hx.
      destruct (HW x) as [X|X]; [exact X|]. exfalso. rewrite FSZ in Hx. lia.
  Qed.

  Lemma PINVA_reasmB : forall pre mid mid' post k Σ m m' W0,
    PINVA G (pre ++ mid ++ post) k Σ m -> munch W0 m m' -> wmono bsegs m m' -> mem_inv bsegs m' -> stk bsegs m' (g_lo G) (g_S1 G) ->
    (forall a, outside W0 a \/ g_lo G <= a < g_S1 G
               \/ g_S1 G + Z.of_nat (cells_size pre) <= a < g_S1 G + Z.of_nat (cells_size pre) + Z.of_nat (cells_size mid)) ->
    rw_cells bsegs m' (g_S1 G + Z.of_nat (cells_size pre)) mid' -> cells_size mid' = cells_size mid ->
    PINVA G (pre ++ mid' ++ post) k Σ m'.
  Proof using AF GOK.
    intros pre mid mid' post k Σ m m' W0 GI MU WM MI' ST' HW FM SZ.
    pose proof GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (FR & FSZ) & _).
    pose proof GOK as GK. destruct GK as [(_ & _ & LQ) _ _ _ _ _ _ _ _ _ _ _].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
    assert (FSZ' : cells_size (pre ++ mid' ++ post) = 256%nat) by (rewrite !cells_size_app in *; rewrite SZ; exact FSZ).
    rewrite !cells_size_app in FSZ.
    eapply (PINVA_cwB _ _ k Σ m m' W0 GI MU WM MI'); [| exact ST'| | exact FSZ'].
    - intros a. destruct (HW a) as [X|[X|X]]; [left; exact X| right; left; lia| right; left; lia].
    - apply (rw_cells_reasm m m' (g_S1 G) pre mid mid' post FR); [| exact FM| exact SZ].
      apply (agree_of_munch _ _ _ _ MU). intros x Hx. rewrite !cells_size_app in Hx.
      destruct (HW x) as [X|[X|X]]; [exact X| exfalso; lia| exfalso; lia].
  Qed.

  Lemma ainv_caller : forall x, ainv_rng (g_E G) x -> aclient (g_L G) (g_rfr G) (g_q G) x /\ outside (pj_WA (g_OS G)) x.
  Proof using AF GOK.
    intros x Hx.
    destruct GOK as [_ (LO1 & LO2) _ (OK & INT & INS & INP & IND) (EIN & ELO & EHI & E16 & DJ) _ _ _ RFR RFR2 LL _].
    pose proof (RFR _ _ EIN) as (_ & ESEG & _ & _ & _ & EHL & FAP). pose proof (RFR _ _ IND) as (D0' & DSEG & _ & DSH & DSHL & DHL & _).
    pose proof (RFR2 _ _ _ _ IND EIN) as XS.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) PTRR PTR0 (D8 & DF & DL & DS & DT) LOW' [HL HT]].
    assert (FS0 : 0 <= fs_size (g_kO G)) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    assert (FSD : 0 <= fs_size (ae_kD (g_E G))) by (unfold fs_size; apply Z.shiftl_nonneg; lia).
    unfold ainv_rng in Hx. unfold pj_WA, EL_TPLOC_A, TPV_A. cbn [outside].
    destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
    - pose proof (LL _ _ INT) as (L1 & L2 & L3). pose proof (FAP _ _ INT) as [F1 _]. split; [right; right; left; exists (ae_TAPE (g_E G)), (ae_NT (g_E G)); split; [exact INT| lia]|].
      clear - Hx L1 L2 L3 F1 TN ELO EHI ESEG FS0. ow.
    - pose proof (LL _ _ INS) as (L1 & L2 & L3). pose proof (FAP _ _ INS) as [F1 _]. split; [right; right; left; exists (ae_SBUF (g_E G)), (ae_NS (g_E G)); split; [exact INS| lia]|].
      clear - Hx L1 L2 L3 F1 SN ELO EHI ESEG FS0. ow.
    - destruct INP as [E0'|INPB]; [rewrite E0' in Hx; unfold zlength in Hx; cbn [length] in Hx; lia|].
      assert (NE : ae_p1 (g_E G) <> []) by (intros E1; rewrite E1 in Hx; unfold zlength in Hx; cbn [length] in Hx; lia).
      pose proof (PTRR NE) as (PB0 & PB1 & PB2 & PB3). pose proof (LL _ _ INPB) as (L1 & L2 & L3). pose proof (FAP _ _ INPB) as [F1 _].
      split; [right; right; left; exists (ae_PB (g_E G)), (ae_NPB (g_E G)); split; [exact INPB| lia]|]. clear - Hx PB0 PB1 PB2 PB3 L1 L2 L3 F1 ELO EHI ESEG FS0. ow.
    - split; [right; right; right; left; exists (ae_fD (g_E G)), (ae_kD (g_E G)); split; [exact IND| lia]|]. clear - Hx DF DL DJ DSEG FSD. ow.
    - split; [do 4 right; exists (ae_fD (g_E G)), (ae_kD (g_E G)); split; [exact IND| unfold shad in *; clear - Hx D8 DF DL FSD; Z.div_mod_to_equations; lia]|].
      assert (X1 : (ae_DOC (g_E G) + 16) / 8 <= (ae_fD (g_E G) + fs_size (ae_kD (g_E G))) / 8) by (apply Z.div_le_mono; lia).
      assert (X2 : ae_fD (g_E G) / 8 <= ae_DOC (g_E G) / 8) by (apply Z.div_le_mono; lia).
      unfold shad, SHB in *. clear - Hx D8 X1 X2 XS ELO EHI FS0 DSEG DSH ESEG. unfold SEGTOP_A in *. repeat split; try exact I; Z.div_mod_to_equations; lia.
  Qed.

  Lemma PINVA_ainv : forall fcs k Σ m, AINV_A (g_E G) (g_m0 G) -> PINVA G fcs k Σ m -> AINV_A (g_E G) m.
  Proof using AF GOK.
    intros fcs k Σ m AI0 GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REL).
    apply (AINV_A_agree (g_E G) (g_m0 G) m AI0). intros a Ha. destruct (ainv_caller _ Ha) as [H1 H2]. exact (REL a H1 H2).
  Qed.

  Lemma PINVA_alive : forall fcs k Σ m, PINVA G fcs k Σ m -> a_live RT Σ (g_E G).
  Proof using AF GOK.
    intros fcs k Σ m (_ & _ & FRS & LV & SP0 & _).
    destruct GOK as [_ (LO1 & LO2) _ (OK & INT & INS & INP & IND) _ _ _ _ _ _ _ _].
    unfold a_live. rewrite LV, FRS, SP0. split; [exact INT|]. split; [exact INS|]. split; [exact INP|]. split; [right; exact IND| exact LO2].
  Qed.

  Lemma PINVA_iossp : forall fcs k Σ m, io_ssp (g_m0 G) -> PINVA G fcs k Σ m -> io_ssp m.
  Proof using AF GOK.
    intros fcs k Σ m (g & G1 & G2) (HA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REL).
    destruct GOK as [_ _ _ _ (EIN & ELO & _) _ _ _ RFR _ _ _]. pose proof (RFR _ _ EIN) as (_ & ESEG & _).
    exists g. split; [exact (proj1 (af_got_lib RT AF Σ m HA))|]. apply (ro_cells_agree bsegs (g_m0 G) m _ _ G2).
    intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply REL.
    - right; left. apply client_static_intro; clear - Ha; lia.
    - unfold pj_WA, EL_TPLOC_A, TPV_A. cbn [outside]. clear - Ha ESEG ELO. ow.
  Qed.

  Lemma PINVA_shz : forall fcs k Σ m, AINV_A (g_E G) (g_m0 G) -> PINVA G fcs k Σ m ->
    shz m (ae_TAPE (g_E G)) (8 * ae_n (g_E G)) /\ shz m (ae_SBUF (g_E G)) (ae_NS (g_E G)) /\ shz m (ae_DOC (g_E G)) 16.
  Proof using AF GOK.
    intros fcs k Σ m AI0 GI. pose proof GI as (HA & _). destruct GOK as [_ _ _ (OK & INT & INS & _) _ _ _ _ _ _ _ _].
    split; [exact (lvl_shz_tape RT AF (g_E G) OK Σ m HA (PINVA_alive _ _ _ _ GI))|].
    split; [| exact (lvl_shz_doc (g_E G) OK m (PINVA_ainv _ _ _ _ AI0 GI))].
    destruct GI as (_ & _ & _ & LV & _). destruct (Atp_defsA.ok_sbuf (g_E G) OK) as (S16 & NS8 & _).
    pose proof (shz_live RT AF Σ m _ _ HA ltac:(rewrite LV; exact INS) ltac:(clear - S16; Z.div_mod_to_equations; lia)) as X.
    replace (8 * (ae_NS (g_E G) / 8)) with (ae_NS (g_E G)) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X.
  Qed.

  Lemma PINVA_wfacts : forall fcs k Σ m, AINV_A (g_E G) (g_m0 G) -> PINVA G fcs k Σ m ->
    forall W0 m', munch W0 m m' -> wmono bsegs m m' -> (forall a, outside W0 a \/ own a) ->
    ART RT Σ m' /\ AINV_A (g_E G) m' /\ shz m' (ae_TAPE (g_E G)) (8 * ae_n (g_E G)) /\ shz m' (ae_SBUF (g_E G)) (ae_NS (g_E G)) /\ shz m' (ae_DOC (g_E G)) 16.
  Proof using AF GOK.
    intros fcs k Σ m AI0 GI W0 m' MU WM HW.
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & _ & _ & _ & _ & _ & _ & _ & REL). destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) _ (OK & INT & INS & _) _ _ _ _ _ _ _ _].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
    assert (HA' : ART RT Σ m').
    { apply (art_client_write RT AF Σ m m' (g_S1 G) HA); [rewrite SP0; clear - LO2 LQ ND; ul| | exact WM].
      intros a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. apply Ha. rewrite FRS, LV. exact (own_aclient _ X). }
    assert (AI' : AINV_A (g_E G) m').
    { apply (AINV_A_agree (g_E G) m m' (PINVA_ainv _ _ _ _ AI0 GI)). intros a Ha. apply MU.
      destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. destruct (ainv_caller _ Ha) as [H1 _]. exact (own_not_caller _ X H1). }
    split; [exact HA'|]. split; [exact AI'|].
    split; [exact (lvl_shz_tape RT AF (g_E G) OK Σ m' HA' (PINVA_alive _ _ _ _ GI))|].
    split; [| exact (lvl_shz_doc (g_E G) OK m' AI')].
    destruct (Atp_defsA.ok_sbuf (g_E G) OK) as (S16 & NS8 & _).
    pose proof (shz_live RT AF Σ m' _ _ HA' ltac:(rewrite LV; exact INS) ltac:(clear - S16; Z.div_mod_to_equations; lia)) as X.
    replace (8 * (ae_NS (g_E G) / 8)) with (ae_NS (g_E G)) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X.
  Qed.

  Lemma PINVA_wfactsB : forall fcs k Σ m, AINV_A (g_E G) (g_m0 G) -> PINVA G fcs k Σ m ->
    forall W0 m', munch W0 m m' -> wmono bsegs m m' -> (forall a, outside W0 a \/ ownB a) ->
    ART RT Σ m' /\ AINV_A (g_E G) m' /\ shz m' (ae_TAPE (g_E G)) (8 * ae_n (g_E G)) /\ shz m' (ae_SBUF (g_E G)) (ae_NS (g_E G)) /\ shz m' (ae_DOC (g_E G)) 16.
  Proof using AF GOK.
    intros fcs k Σ m AI0 GI W0 m' MU WM HW.
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & _ & _ & _ & _ & _ & _ & _ & REL). destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) _ (OK & INT & INS & _) _ _ _ _ _ _ _ _].
    assert (HA' : ART RT Σ m').
    { apply (art_client_write RT AF Σ m m' (g_lo G) HA); [rewrite SP0; exact LO2| | exact WM].
      intros a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. apply Ha. rewrite FRS, LV. exact (ownB_aclient _ X). }
    assert (AI' : AINV_A (g_E G) m').
    { apply (AINV_A_agree (g_E G) m m' (PINVA_ainv _ _ _ _ AI0 GI)). intros a Ha. apply MU.
      destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. destruct (ainv_caller _ Ha) as [H1 _]. exact (ownB_not_caller _ X H1). }
    split; [exact HA'|]. split; [exact AI'|].
    split; [exact (lvl_shz_tape RT AF (g_E G) OK Σ m' HA' (PINVA_alive _ _ _ _ GI))|].
    split; [| exact (lvl_shz_doc (g_E G) OK m' AI')].
    destruct (Atp_defsA.ok_sbuf (g_E G) OK) as (S16 & NS8 & _).
    pose proof (shz_live RT AF Σ m' _ _ HA' ltac:(rewrite LV; exact INS) ltac:(clear - S16; Z.div_mod_to_equations; lia)) as X.
    replace (8 * (ae_NS (g_E G) / 8)) with (ae_NS (g_E G)) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X.
  Qed.

  Lemma PINVA_after : forall fcs k k' Σ Σ' m m' PW,
    PINVA G fcs k Σ m ->
    ART RT Σ' m' -> mem_inv bsegs m' -> stk bsegs m' (g_lo G) (g_S1 G) ->
    OSXF m' (g_OS G) -> os_hullA m' (g_OS G) -> el_tploc m' -> LOCBA m' ->
    rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> g_cr G - k' <= rt_credit RT Σ' ->
    rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (g_S1 G) PW m m' -> (forall a, outside (pj_WA (g_OS G)) a -> outside PW a) ->
    PINVA G fcs k' Σ' m'.
  Proof using AF GOK.
    intros fcs k k' Σ Σ' m m' PW GI HA' MI' ST' OX' [_ SHO'] TPL' LB' LV' FRS' SP0' CR' PRES HPW.
    destruct GI as (HA & MI & FRS & LV & SP0 & CR & ST & _ & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ (EIN & ELO & EHI & E16 & _) (F0 & F64 & FSEG & FLO & FHI & SHLO & SHAP) FFR FFL RFR _ LL _].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
    pose proof (FFR _ _ EIN) as (A1 & A2 & A3). pose proof (RFR _ _ EIN) as (_ & ESEG & EL & _).
    rewrite FRS, LV in PRES.
    assert (AG : forall P : Z -> Prop, (forall x, P x -> aclient (g_L G) (g_fr G) (g_S1 G) x /\ outside (pj_WA (g_OS G)) x) -> agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (PRES a H1 (HPW _ H2)). }
    split; [exact HA'|]. split; [exact MI'|]. split; [rewrite FRS'; exact FRS|]. split; [rewrite LV'; exact LV|]. split; [rewrite SP0'; exact SP0|]. split; [exact CR'|].
    split; [exact ST'|]. split; [exact OX'|]. split; [exact SHO'|]. split; [exact TPL'|]. split; [exact LB'|].
    split. { split; [| exact FSZ]. apply (rw_cells_agree_nw bsegs m m' _ _ FR). apply AG. intros x Hx. rewrite FSZ in Hx. split; [left; clear - Hx QT; ul|].
             unfold pj_WA, EL_TPLOC_A, TPV_A. cbn [outside]. clear - Hx LQ ND LO1 ELO EHI EL. ow. }
    split. { apply (wr_at_agree_nw bsegs m m' _ _ WF1). apply AG. intros x Hx. split; [apply own_aclient; right; left; clear - Hx; lia|].
             unfold pj_WA, EL_TPLOC_A, TPV_A. cbn [outside]. clear - Hx A1 ELO EHI FSEG. ow. }
    split. { apply (wr_at_agree_nw bsegs m m' _ _ WF2). apply AG. intros x Hx. split; [apply own_aclient; do 2 right; clear - Hx; lia|].
             unfold pj_WA, EL_TPLOC_A, TPV_A. cbn [outside]. unfold shad in *. clear - Hx A2 ELO EHI F0. repeat split; try exact I; unfold SEGTOP_A, SHB in *; Z.div_mod_to_equations; lia. }
    intros a CA OU. rewrite <- (REL a CA OU). apply PRES; [| exact (HPW _ OU)].
    apply (aclient_mono _ _ _ _ _ _ _ CA); [auto| intros e He; right; exact He| clear; lia].
  Qed.

  Lemma PINVA_callctx : forall fcs k Σ m, PINVA G fcs k Σ m ->
    In (g_fO G, g_kO G) (rt_frames RT Σ) /\ g_fO G <= g_OS G /\ g_OS G + 288 <= g_fO G + fs_size (g_kO G) - 8 /\ g_OS G mod 16 = 0
    /\ os_hullA m (g_OS G) /\ rt_sp0 RT Σ - STACK_WIN <= g_lo G /\ g_S1 G + 16 <= USTACK_TOP /\ g_S1 G mod 16 = 0 /\ g_S1 G mod 32 = 0
    /\ Z.of_nat (length (rt_frames RT Σ)) = Z.of_nat (length (g_rfr G)) + 1
    /\ g_lo G + DMP_PJ_LEAF_A + 256 <= g_q G /\ Z.of_nat (length (g_rfr G)) + 3 <= FRAMES_TOT.
  Proof using AF GOK.
    intros fcs k Σ m (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ (EIN & ELO & EHI & E16 & _) _ _ _ _ _ _ LEN].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A in ND.
    rewrite FRS, SP0. split; [right; exact EIN|]. split; [exact ELO|]. split; [exact EHI|]. split; [exact E16|].
    split. { split; [| exact SHO]. destruct OX as (pb & pp & ep & dum & j148 & j284 & H & _). apply rw_cells_forget in H. rewrite os_cellsX_size in H. exact H. }
    split; [exact LO2|]. split; [clear - QT; ul|]. split; [clear - Q32; Z.div_mod_to_equations; lia|]. split; [clear - Q32; Z.div_mod_to_equations; lia|]. split; [cbn [length]; lia|].
    split; [clear - LQ ND; lia| clear - LEN; lia].
  Qed.

  Lemma p_put : forall fcs k Σ (K : config -> Prop) (BUF N CAP : Z) (bs : list byte)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    os_put_cpsA RT PMc ->
    PINVA G fcs k Σ m ->
    bytes_at bsegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> CAP <= 2^40 -> 0 < BUF -> acc bsegs m BUF N -> srcA RT Σ (g_S1 G) BUF CAP bs ->
    (BUF + CAP <= g_OS G \/ g_OS G + 288 <= BUF) ->
    k + 2 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) m',
       PINVA G fcs (k + 2) Σ' m' ->
       aevt Σ' K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_OS G + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_OS G + 128)) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_PJ_PUT_A) fc None m (seg_rom bsegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros PUT GI BB BL NR CAPH B0 ACC SRC SEP CRK HK.
    pose proof (PINVA_callctx _ _ _ _ GI) as (INF & FLO & FHI & AL16 & HULL & WLO & QT & Q16 & Q32' & LEN & LFQ & LEN3).
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    unfold DMP_PJ_PUT_A.
    eapply (PUT Σ K (g_OS G) BUF N CAP (g_S1 G) (g_lo G) (g_fO G) fill (g_kO G)); try eassumption; try (clear HK; unfold DMP_PJ_LEAF_A, EL_PUT_STACK_A in *; lia).
    intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' HA' MI' ST' OX' HULL' LB' LV' FRS' SP0' CR' PRES.
    apply HK.
    eapply (PINVA_after fcs k (k + 2) Σ Σ' m m'); try eassumption.
    + exact (OSXF_after m' (g_OS G) fill OX' FOK).
    + apply (rw_cells_agree_nw bsegs m m' _ _ TPL). intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite FRS, LV in PRES. apply PRES.
      * right; left. apply client_static_intro; clear - Ha; lia.
      * cbn [outside]. destruct GOK as [_ _ _ _ (EIN & ELO' & _) _ _ _ RFR _ _ _]. pose proof (RFR _ _ EIN) as (_ & ESEG & _). clear - Ha ESEG ELO'. ow.
    + clear - CR CR'. lia.
    + intros a Ha. unfold pj_WA in Ha. cbn [outside] in Ha |- *. tauto.
  Qed.

  Lemma p_put_lit : forall fcs k Σ (K : config -> Prop) (BUF N CAPL : Z) (nb : nat)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    os_put_cpsA RT PMc ->
    PINVA G fcs k Σ m ->
    In (BUF, CAPL) ACC_LITS -> ro_bytes_b bsegs BUF (litA BUF nb) = true -> length (litA BUF nb) = nb -> Z.of_nat nb <= CAPL -> 0 <= N <= Z.of_nat nb ->
    0x10000 <= BUF -> BUF + CAPL <= SEGTOP_A ->
    k + 2 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) m',
       PINVA G fcs (k + 2) Σ' m' ->
       aevt Σ' K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_OS G + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_OS G + 128)) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_PJ_PUT_A) fc None m (seg_rom bsegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros PUT GI INL RB LL NBC NR BLO BHI CRK HK.
    pose proof GI as (HA & MI & _). destruct GOK as [_ _ _ _ (EIN & ELO & _) _ _ _ RFR _ _ _]. pose proof (RFR _ _ EIN) as (_ & ESEG & _).
    destruct (litA_bytes BUF nb RB LL ltac:(lia) ltac:(unfold SEGTOP_A in BHI; lia) m MI) as [LBY RO].
    eapply (p_put fcs k Σ K BUF N (Z.of_nat nb) (litA BUF nb)); try eassumption; try (clear HK; unfold SEGTOP_A in *; lia); try (rewrite LL; reflexivity).
    all: lazymatch goal with
         | |- acc _ _ _ _ => apply (acc_sub bsegs m BUF CAPL); [exact (acc_lit RT AF Σ m BUF CAPL HA INL)| lia| lia]
         | |- srcA _ _ _ _ _ _ => left; split; [exact RO|]; split; [lia|]; split; [unfold SEGTOP_A in BHI; lia|]; exists BUF, CAPL; split; [exact INL| lia]
         end.
  Qed.

  Lemma p_put_ownc : forall fcs k Σ (K : config -> Prop) (off : Z) (b : byte)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    os_put_cpsA RT PMc ->
    PINVA G fcs k Σ m ->
    rw_cells bsegs m (g_ff G + off) [C1 b] -> rw_cells bsegs m (shad (g_ff G) + off / 8) [C1 (Z_to_bv 8 1)] -> off mod 8 = 0 -> 0 <= off -> off + 8 <= 248 ->
    k + 2 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) m',
       PINVA G fcs (k + 2) Σ' m' ->
       aevt Σ' K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_OS G + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_OS G + 128)) (wz (g_ff G + off)) (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_PJ_PUT_A) fc None m (seg_rom bsegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros PUT GI CC CS O8 O0 OH CRK HK.
    pose proof GI as (HA & MI & FRS & _). destruct GOK as [_ _ _ _ (EIN & ELO & EHI & _) (F0 & F64 & FSEG & FLO & _) FFR _ _ _ _ _].
    pose proof (FFR _ _ EIN) as (A1 & _ & _).
    pose proof (rw_cells_bytes_at bsegs m _ _ CC) as BB. cbn [cells_bytes cbytes app] in BB.
    pose proof (rw_cells_bytes_at bsegs m _ _ CS) as BS. cbn [cells_bytes cbytes app] in BS.
    eapply (p_put fcs k Σ K (g_ff G + off) 1 1 [b]); try eassumption; try (clear HK; unfold SEGTOP_A in *; lia); try reflexivity.
    all: lazymatch goal with
         | |- acc _ _ _ _ => apply (acc_ushadow bsegs m (g_ff G + off) 1); [clear - F64 O8; Z.div_mod_to_equations; lia| lia| lia|];
               unfold ushadow; cbn [Z.div Z.modulo Z.eqb repeat app Z.to_nat Z.div_eucl Z.pos_div_eucl Pos.eqb];
               replace (shad (g_ff G + off)) with (shad (g_ff G) + off / 8); [exact BS|]; unfold shad; clear - F64 O8 O0; Z.div_mod_to_equations; lia
         | |- srcA _ _ _ _ _ _ => right; right; left; exists (g_ff G), 2%nat; rewrite FRS; split; [left; reflexivity| change (fs_size 2) with 256; lia]
         end.
  Qed.

  Lemma p_put_live : forall fcs k Σ (K : config -> Prop) (o l : Z)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    os_put_cpsA RT PMc ->
    PINVA G fcs k Σ m -> AINV_A (g_E G) (g_m0 G) ->
    str_at (ae_S (g_E G)) (ae_sn (g_E G)) o l ->
    k + 2 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) m',
       PINVA G fcs (k + 2) Σ' m' ->
       aevt Σ' K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_OS G + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_OS G + 128)) (wz (ae_SBUF (g_E G) + o + 4)) (wz l) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_PJ_PUT_A) fc None m (seg_rom bsegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros PUT GI AI0 SA CRK HK.
    pose proof GI as (HA & MI & FRS & LV & _). destruct GOK as [_ _ _ (OK & INT & INS & _) (EIN & ELO & EHI & _) _ _ _ RFR _ LL _].
    pose proof (RFR _ _ EIN) as (_ & _ & _ & _ & _ & _ & FAP). pose proof (FAP _ _ INS) as [SEP _]. pose proof (LL _ _ INS) as (S0 & _).
    pose proof OK as OK'. destruct OK' as [WF SBS _ _ _ (S16 & NS8 & SN & SS & SL) _ _ _ _ _].
    assert (HSN : 0 <= ae_sn (g_E G) < 2^56) by (destruct WF as (_ & X & _); exact X).
    pose proof (str_at_bounds _ _ (proj2 HSN) _ _ SA) as (O0 & L0 & OL & LE & O56).
    assert (L32 : l < 2^32).
    { rewrite <- LE. unfold le32.
      assert (B0 : 0 <= ae_S (g_E G) o < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
      assert (B1 : 0 <= ae_S (g_E G) (o + 1) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
      assert (B2 : 0 <= ae_S (g_E G) (o + 2) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]).
      assert (B3 : 0 <= ae_S (g_E G) (o + 3) < 256) by (unfold Tf; apply Forall_nth_Z; [exact SBS| lia]). lia. }
    pose proof (PINVA_ainv _ _ _ _ AI0 GI) as (_ & SB & _).
    destruct (sbuf_sliceA m (ae_SBUF (g_E G)) (ae_sbs (g_E G)) o l SB O0 L0 OL) as [QB QL].
    eapply (p_put fcs k Σ K (ae_SBUF (g_E G) + o + 4) l l); try eassumption; try (clear HK; lia).
    all: lazymatch goal with
         | |- acc _ _ _ _ => apply (acc_sub bsegs m (ae_SBUF (g_E G)) (ae_NS (g_E G))); [exact (proj2 (af_acc_live RT AF Σ m _ _ HA ltac:(rewrite LV; exact INS)))| lia| lia]
         | |- srcA _ _ _ _ _ _ => do 3 right; exists (ae_SBUF (g_E G)), (ae_NS (g_E G)); rewrite LV; split; [exact INS| lia]
         end.
  Qed.

  Lemma p_ins : forall ENTRY VOKP DEPTH fcs k Σ (K : config -> Prop) (v : Z)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ins_cpsA RT PMc ENTRY VOKP 0x1002 0 FILLOK DEPTH ->
    PINVA G fcs k Σ m -> io_ssp (g_m0 G) -> VOKP v -> frm0 fc -> DEPTH <= DMP_PJ_LEAF_A ->
    k + 1 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m',
       PINVA G fcs (k + 1) Σ' m' -> frm0 fc' ->
       aevt Σ' K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_OS G + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_OS G + 128)) (wz v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ENTRY) fc None m (seg_rom bsegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros INS GI IOS0 HV FRM DEP CRK HK.
    pose proof (PINVA_callctx _ _ _ _ GI) as (INF & FLO & FHI & AL16 & HULL & WLO & QT & Q16 & Q32' & LEN & LFQ & LEN3).
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    eapply (INS Σ K (g_OS G) (g_S1 G) (g_lo G) (g_fO G) fill v (g_kO G)); try eassumption;
      try (apply (proj1 (OSX_W m (g_OS G) fill)); exact OX); try exact (PINVA_iossp _ _ _ _ IOS0 GI); try (clear HK; lia).
    intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' HA' MI' ST' OX' HULL' LB' TPL' FRM' LV' FRS' SP0' CR' PRES.
    apply HK; [| exact FRM'].
    eapply (PINVA_after fcs k (k + 1) Σ Σ' m m'); try eassumption.
    + exact (OSXF_after m' (g_OS G) fill (proj2 (OSX_W m' (g_OS G) (fill_after fill)) OX') FOK).
    + clear - CR CR'. lia.
    + intros a Ha. exact Ha.
  Qed.

  Lemma p_insd : forall fcs k Σ (K : config -> Prop)
      (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ins_d_cpsA RT PMc ->
    PINVA G fcs k Σ m -> io_ssp (g_m0 G) -> frm0 fc ->
    k + 1 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m',
       PINVA G fcs (k + 1) Σ' m' -> frm0 fc' ->
       aevt Σ' K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_OS G + 128)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_OS G + 128)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_INS_D_A) fc None m (seg_rom bsegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros INS GI IOS0 FRM CRK HK.
    pose proof (PINVA_callctx _ _ _ _ GI) as (INF & FLO & FHI & AL16 & HULL & WLO & QT & Q16 & Q32' & LEN & LFQ & LEN3).
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    unfold DMP_INS_D_A.
    eapply (INS Σ K (g_OS G) (g_S1 G) (g_lo G) (g_fO G) fill (g_kO G) (reg_get F (Z_to_bv 5 10))); try eassumption;
      try (apply (proj1 (OSX_W m (g_OS G) fill)); exact OX); try exact (PINVA_iossp _ _ _ _ IOS0 GI); try reflexivity;
      try (clear HK; unfold DMP_PJ_LEAF_A, EL_INSD_STACK_A in *; lia).
    intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' HA' MI' ST' OX' HULL' LB' TPL' FRM' LV' FRS' SP0' CR' PRES.
    apply HK; [| exact FRM'].
    eapply (PINVA_after fcs k (k + 1) Σ Σ' m m'); try eassumption.
    + exact (OSXF_after m' (g_OS G) fill (proj2 (OSX_W m' (g_OS G) (fill_after fill)) OX') FOK).
    + clear - CR CR'. lia.
    + intros a Ha. exact Ha.
  Qed.

  Lemma p_child : forall (d' : nat) fcs k Σ (K : config -> Prop) (it j : Z)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    Dmp_pj_ifaceA.pj_cpsA RT PMc d' ->
    PINVA G fcs k Σ m -> AINV_A (g_E G) (g_m0 G) -> io_ssp (g_m0 G) -> frm0 fc ->
    elem (ae_T (g_E G)) (ae_S (g_E G)) (ae_sn (g_E G)) ck_any d' it j -> 0 <= it -> j <= ae_n (g_E G) -> g_d G = S d' ->
    k + pj_costE it j <= g_cr G ->
    (forall Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m',
       PINVA G fcs (k + pj_costE it j) Σ' m' -> frm0 fc' ->
       aevt Σ' K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom bsegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_OS G + 128)) (wz (ae_DOC (g_E G))) (wz it) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz DMP_PJ_A) fc None m (seg_rom bsegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros PJ GI AI0 IOS0 FRM EL I0 JN GD CRK HK.
    pose proof (PINVA_callctx _ _ _ _ GI) as (INF & FLO & FHI & AL16 & HULL & WLO & QT & Q16 & Q32' & LEN & LFQ & LEN3).
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & OX & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & QT' & LQ) (LO1 & LO2) (SP1 & SP2) (OK & INT & INS & INP & IND) (EIN & ELO & EHI & E16 & DJ) _ _ _ _ _ _ LEN'].
    rewrite GD, pj_needA_S in LQ. unfold DMP_PJ_FRAME_A in LQ.
    eapply (PJ Σ K (g_E G) (g_OS G) (g_S1 G) (g_fO G) (g_kO G) it j);
      [exact FDO| exact MST| exact OK| exact EL| exact I0| exact JN| exact (PINVA_alive _ _ _ _ GI)| exact (PINVA_ainv _ _ _ _ AI0 GI)| exact INF| exact ELO| exact EHI| exact E16| exact DJ
      | exact OX| exact HULL| exact LB| exact TPL| exact (PINVA_iossp _ _ _ _ IOS0 GI)| exact FRM| exact HA| exact MI| exact ST| clear - LQ; lia| exact QT| exact Q32'
      | rewrite FRS; cbn [length]; rewrite GD in LEN'; clear - LEN'; lia| clear - CR CRK; lia|].
    intros Σ' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' HA' MI' ST' OX' HULL' LB' TPL' FRM' AI' LV' FRS' SP0' CR' PRES.
    apply HK; [| exact FRM'].
    eapply (PINVA_after fcs k (k + pj_costE it j) Σ Σ' m m'); try eassumption.
    + clear - CR CR'. lia.
    + intros a Ha. exact Ha.
  Qed.

  Lemma p_tix : forall fcs k Σ (K : config -> Prop) (idx : Z)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    PINVA G fcs k Σ m -> AINV_A (g_E G) (g_m0 G) -> 0 <= idx -> ae_TAPE (g_E G) + 8 * idx < 2^63 ->
    (forall (a4' : word) (m' : mem), PINVA G fcs k Σ m' ->
       aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (ae_TAPE (g_E G) + 8 * idx)) (wz 0) (wz (ae_TAPE (g_E G))) (wz (2^60)) a4' a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom bsegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_S1 G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (ae_DOC (g_E G))) (wz idx) a2 a3 a4 a5 a6 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz PJ_TREF_A) fc None m (seg_rom bsegs)).
  Proof using AF MST GOK.
    intros until m. intros GI AI0 I0 IH HK.
    pose proof GI as (HA & MI & _ & _ & _ & _ & ST & _).
    pose proof GOK as GK. destruct GK as [(_ & QT & LQ) _ _ (OK & _) _ _ _ _ _ _ _ _].
    pose proof (pj_needA_0 (g_d G)) as ND. unfold DMP_PJ_FRAME_A, DMP_PJ_LEAF_A, RT_STACK in ND.
    apply (aevt_evt RT AF PMc MST).
    eapply evt_cut; [eapply (pj_tixE (g_E G) (g_S1 G) idx); [exact OK| exact (PINVA_ainv _ _ _ _ AI0 GI)| exact (af_client_consts RT AF Σ m HA)| exact ST
      | clear - LQ ND; lia| clear - QT; ul| exact I0| exact IH| exact MI]|].
    cbv beta. intros ms' (m' & a4' & -> & MU & WM & MI' & ST' & _ & _). apply evt_done.
    apply (HK a4' m').
    apply (PINVA_lowB fcs k Σ m m' _ GI MU WM MI' ST'). intros a. cbn [outside].
    destruct (Z_lt_dec a (g_S1 G - 16)) as [L|L]; [left; split; [lia| exact I]|].
    destruct (Z_lt_dec a (g_S1 G)) as [L2|L2]; [right; clear - L L2 LQ ND; lia| left; split; [lia| exact I]].
  Qed.
End G.

Lemma aevt_smalloc2 : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 0x6ab368 ->
  (length (rt_frames RT Σ) < FRAMES_MAX2B)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv bsegs m -> call_ok RT Σ m sp lo ->
  (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at bsegs m' f (fs_size 2 - 8) -> wr_at bsegs m' (shad f) (fs_size 2 / 8) ->
     rt_frames RT Σ' = (f, 2%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size 2 < USTACK_TOP ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom bsegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 e_stack_malloc_2) fc None m (seg_rom bsegs)).
Proof using SM2 FDO MST.
  intros until lo. intros ETP FRL CR ART0 MI0 COK TOPC HK.
  eapply (aevt_icall RT PMc).
  - exact (SM2 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST ETP FRL CR ART0 MI0 COK TOPC).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR W1 W2 E1 E2 E3 E4 F1 F2 F3).
Qed.

Lemma pctx_ok_intro : forall G Σ m,
  ART RT Σ m -> rt_frames RT Σ = g_fr G -> rt_live RT Σ = g_L G -> rt_sp0 RT Σ = g_sp0 G ->
  g_q G mod 32 = 0 -> g_q G + 16 <= USTACK_TOP -> g_lo G + pj_needA (g_d G) <= g_q G ->
  aenvA_ok (g_E G) -> In (ae_TAPE (g_E G), ae_NT (g_E G)) (g_L G) -> In (ae_SBUF (g_E G), ae_NS (g_E G)) (g_L G) ->
  (ae_p1 (g_E G) = [] \/ In (ae_PB (g_E G), ae_NPB (g_E G)) (g_L G)) -> In (ae_fD (g_E G), ae_kD (g_E G)) (g_rfr G) -> g_sp0 G - STACK_WIN <= g_lo G ->
  In (g_fO G, g_kO G) (g_rfr G) -> g_fO G <= g_OS G -> g_OS G + 288 <= g_fO G + fs_size (g_kO G) - 8 -> g_OS G mod 16 = 0 ->
  (ae_DOC (g_E G) + 16 <= g_OS G \/ g_OS G + 288 <= ae_DOC (g_E G)) ->
  Z.of_nat (length (g_rfr G)) + Z.of_nat (g_d G) + 3 <= FRAMES_TOT ->
  pctx_ok G.
Proof using AF.
  intros G Σ m HA FRS LV SP0 Q32 QT LQ OK INT INS INP IND WLO EIN ELO EHI E16 DJ LEN.
  assert (INff : In (g_ff G, 2%nat) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (INr : forall f k, In (f, k) (g_rfr G) -> In (f, k) (rt_frames RT Σ)) by (intros f k H; rewrite FRS; right; exact H).
  pose proof (af_sp0_range RT AF Σ m HA) as SPR. pose proof (af_sp0_win RT AF Σ m HA) as SPW. rewrite SP0 in SPR, SPW.
  pose proof (Atp_defsA.ok_lo (g_E G) OK) as LO1.
  assert (GEN : forall f k, In (f, k) (rt_frames RT Σ) ->
     0 < f /\ f mod 64 = 0 /\ SEGTOP_A <= f /\ f + fs_size k <= g_lo G /\ 0 <= fs_size k /\ SHB <= shad f /\ shad (f + fs_size k) + 1 <= g_lo G
     /\ (f + fs_size k <= 0x7fff7000 \/ 0x10007fff8000 <= f) /\ (f + fs_size k <= shad f \/ shad (f + fs_size k) <= f)
     /\ (forall p n, In (p, n) (g_L G) -> (f + fs_size k <= p \/ p + n <= f) /\ (p + n <= shad f \/ shad (f + fs_size k) <= p))).
  { intros f k Hin. pose proof (af_frames_range RT AF Σ m f k HA Hin) as (R0 & R1 & R2 & R3). pose proof (af_frames_align RT AF Σ m f k HA Hin) as [A1 A2].
    pose proof (fframe_ranges RT AF Σ m f k HA Hin) as (_ & _ & Z0 & S0 & S1). pose proof (af_frames_hi RT AF Σ m f k HA Hin) as HI.
    pose proof (af_fshadow_apart RT AF Σ m f k HA Hin) as [SL SF]. rewrite SP0 in R1, S1. rewrite LV in R3, SL.
    split; [exact R0|]. split; [exact A1|]. split; [exact A2|]. split; [lia|]. split; [exact Z0|]. split; [exact S0|]. split; [lia|]. split; [exact HI|].
    split; [exact (SF f k Hin)|]. intros p n Hp. split; [exact (R3 p n Hp)| exact (SL p n Hp)]. }
  constructor.
  - split; [exact Q32|]. split; [exact QT| exact LQ].
  - split; [exact LO1| exact WLO].
  - split; [exact SPR| exact SPW].
  - split; [exact OK|]. split; [exact INT|]. split; [exact INS|]. split; [exact INP| exact IND].
  - split; [exact EIN|]. split; [exact ELO|]. split; [exact EHI|]. split; [exact E16| exact DJ].
  - pose proof (GEN _ _ INff) as (R0 & A1 & A2 & R1 & _ & S0 & S1 & HI & SF & _). change (fs_size 2) with 256 in *.
    assert (SH8 : shad (g_ff G + 256) = shad (g_ff G) + 32) by (unfold shad; clear - A1; Z.div_mod_to_equations; lia). rewrite SH8 in *.
    repeat split; try assumption; lia.
  - intros f k Hin. pose proof (GEN _ _ INff) as (_ & A1 & _ & _ & _ & _ & _ & _ & _ & _).
    assert (SH8 : shad (g_ff G + fs_size 2) = shad (g_ff G) + 32) by (change (fs_size 2) with 256; unfold shad; clear - A1; Z.div_mod_to_equations; lia).
    pose proof (af_frames_disj RT AF Σ m (g_ff G) 2%nat f k [] (g_rfr G) HA FRS Hin) as D1. change (fs_size 2) with 256 in D1.
    pose proof (proj2 (af_fshadow_apart RT AF Σ m (g_ff G) 2%nat HA INff) f k (INr _ _ Hin)) as D2. rewrite SH8 in D2.
    pose proof (proj2 (af_fshadow_apart RT AF Σ m f k HA (INr _ _ Hin)) (g_ff G) 2%nat INff) as D3. change (fs_size 2) with 256 in D3.
    split; [exact D1|]. split; [exact D2| exact D3].
  - intros p n Hp. pose proof (GEN _ _ INff) as (_ & A1 & _ & _ & _ & _ & _ & _ & _ & LL).
    assert (SH8 : shad (g_ff G + fs_size 2) = shad (g_ff G) + 32) by (change (fs_size 2) with 256; unfold shad; clear - A1; Z.div_mod_to_equations; lia).
    rewrite SH8 in LL. change (fs_size 2) with 256 in LL. exact (LL p n Hp).
  - intros f k Hin. pose proof (GEN _ _ (INr _ _ Hin)) as (R0 & A1 & A2 & R1 & _ & S0 & S1 & HI & SF & LL).
    split; [exact R0|]. split; [exact A2|]. split; [exact R1|]. split; [exact S0|]. split; [exact S1|]. split; [exact HI| exact LL].
  - intros f k f' k' Hin Hin'. exact (proj2 (af_fshadow_apart RT AF Σ m f k HA (INr _ _ Hin)) f' k' (INr _ _ Hin')).
  - intros p n Hp. pose proof (af_live_range RT AF Σ m p n HA ltac:(rewrite LV; exact Hp)) as (P0 & P1 & P2). rewrite SP0 in P1.
    split; [exact P0|]. split; [lia| exact P2].
  - exact LEN.
Qed.

End Kit.
