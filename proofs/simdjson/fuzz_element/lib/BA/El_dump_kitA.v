(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList SjTapeTile.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Pj_os_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_iface3. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_num_akit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Pj_rtkA Pj_lftoi1A Pj_defsA Pj_os_defsA El_defsA El_os_defsA El_ins_ifaceA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition lit (A : Z) (n : nat) : list byte := match image_bytes asegs A n with Some bs => bs | None => [] end.
Lemma lit_bytes : forall A n, ro_bytes_b asegs A (lit A n) = true -> length (lit A n) = n -> 0 <= A -> A + Z.of_nat n <= 2^64 ->
  forall m, mem_inv asegs m -> bytes_at asegs m A (lit A n) /\ ro_bytes asegs A (lit A n).
Proof.
  intros A n RB L A0 AH m MI. pose proof (ro_bytes_b_sound _ _ _ RB) as RO. split; [| exact RO].
  apply ro_bytes_at; [exact MI| lia| rewrite L; lia| exact RO].
Qed.

Lemma wr_at_cell : forall m A n i w, wr_at asegs m A n -> 0 <= i -> 0 <= w -> i + w <= n -> exists j, rw_cells asegs m (A + i) [CB (Z.to_nat w) j].
Proof.
  intros m A n i w WA I0 W0 IW. exact (wr_at_rw_CB m (A + i) w (wr_at_sub m A n (A + i) w WA ltac:(lia) ltac:(lia) W0) W0).
Qed.

Definition WD (OS : Z) : list (Z * Z) := [(OS, OS + 288); (EL_TPLOC_A, EL_TPLOC_A + 8)].

Record gctx : Type := mkG {
  g_q : Z;
  g_fsz : Z;
  g_lo : Z;
  g_F : Z;
  g_ff : Z; g_ffk : nat;
  g_rfr : list (Z * nat);
  g_L : list (Z * Z);
  g_sp0 : Z;
  g_cr : Z;
  g_m0 : mem }.
Notation g_OS G := (g_F G + 240).
Notation g_fr G := ((g_ff G, g_ffk G) :: g_rfr G).
Notation g_usp G := (g_q G + g_fsz G).
Notation g_FS G := (fs_size (g_ffk G)).

Record gctx_ok (G : gctx) : Prop := mkGok {
  go_q : g_q G mod 32 = 0 /\ 0 <= g_fsz G /\ g_usp G + 16 <= USTACK_TOP /\ g_lo G + 12800 + RT_STACK <= g_q G;
  go_lo : 0x7fff7f800000 <= g_lo G /\ g_sp0 G - STACK_WIN <= g_lo G;
  go_sp0 : SEGTOP_A + STACK_WIN <= g_sp0 G <= USTACK_TOP /\ 0x7fff80000000 <= g_sp0 G;
  go_F : 0 < g_F G /\ g_F G mod 64 = 0 /\ SEGTOP_A <= g_F G /\ g_F G + 1024 <= g_lo G /\ In (g_F G, 4%nat) (g_rfr G)
         /\ (g_F G + 1024 <= shad (g_F G) \/ shad (g_F G) + 128 <= g_F G) /\ shad (g_F G) + 129 <= g_lo G
         /\ (g_F G + 1024 <= 0x7fff7000 \/ 0x10007fff8000 <= g_F G);
  go_ff : 0 < g_ff G /\ g_ff G mod 64 = 0 /\ SEGTOP_A <= g_ff G /\ g_ff G + g_FS G <= g_lo G /\ 56 <= g_FS G <= 128
         /\ (g_ff G + g_FS G <= 0x7fff7000 \/ 0x10007fff8000 <= g_ff G)
         /\ shad (g_ff G) + g_FS G / 8 + 1 <= g_lo G /\ (g_ff G + g_FS G <= shad (g_ff G) \/ shad (g_ff G) + g_FS G / 8 <= g_ff G);

  go_ffr : forall f k, In (f, k) (g_rfr G) ->
         (g_ff G + g_FS G <= f \/ f + fs_size k <= g_ff G) /\ (f + fs_size k <= shad (g_ff G) \/ shad (g_ff G) + g_FS G / 8 <= f)
         /\ (g_ff G + g_FS G <= shad f \/ shad (f + fs_size k) <= g_ff G);

  go_ffL : forall p n, In (p, n) (g_L G) -> (g_ff G + g_FS G <= p \/ p + n <= g_ff G) /\ (p + n <= shad (g_ff G) \/ shad (g_ff G) + g_FS G / 8 <= p);

  go_rfr : forall f k, In (f, k) (g_rfr G) -> 0 < f /\ SEGTOP_A <= f /\ f + fs_size k <= g_lo G /\ SHB <= shad f /\ shad (f + fs_size k) + 1 <= g_lo G
         /\ (forall p n, In (p, n) (g_L G) -> (f + fs_size k <= p \/ p + n <= f) /\ (p + n <= shad f \/ shad (f + fs_size k) <= p));
  go_L : forall p n, In (p, n) (g_L G) -> 0 < p /\ p + n <= g_lo G /\ (p + n <= 0x10000 \/ SEGTOP_A <= p) }.

Definition genv (G : gctx) (E : aenvA) : Prop :=
  aenvA_ok E /\ ae_lo E = g_lo G /\ ae_DOC E = g_F G + 120 /\ ae_fD E = g_F G /\ ae_kD E = 4%nat
  /\ In (ae_TAPE E, ae_NT E) (g_L G) /\ In (ae_SBUF E, ae_NS E) (g_L G) /\ (ae_p1 E = [] \/ In (ae_PB E, ae_NPB E) (g_L G))
  /\ g_q G <= ae_hi E.

Record dctx : Type := mkD {
  d_X : lfA; d_E : aenvA; d_f1 : Z; d_L : list (Z * Z); d_sp0 : Z; d_cr : Z; d_m0 : mem;
  d_gp : word; d_s0 : word; d_s1 : word; d_s2 : word; d_s3 : word; d_s4 : word; d_s5 : word; d_s6 : word;
  d_s7 : word; d_s8 : word; d_s9 : word; d_s10 : word; d_s11 : word; d_j : list (list byte) }.
Definition d_G (D : dctx) : gctx :=
  mkG (lf_S1 (d_X D) - 288) 288 (lf_lo (d_X D)) (lf_F (d_X D)) (d_f1 D) 1%nat [(lf_F (d_X D), 4%nat)] (d_L D) (d_sp0 D) (d_cr D) (d_m0 D).
Notation dq D := (lf_S1 (d_X D) - 288).
Notation dF D := (lf_F (d_X D)).
Notation dOS D := (lf_F (d_X D) + 240).
Notation dDOC D := (lf_F (d_X D) + 120).

Definition J (D : dctx) (k : nat) : cell := CB 8 (nth k (d_j D) []).

Definition dsaves (D : dctx) : list cell :=
  fa_saved (wz EL_DUMPRET_A) (d_s0 D) (d_s1 D) (d_s2 D) (d_s3 D) (d_s4 D) (d_s5 D) (d_s6 D)
           (d_s7 D) (d_s8 D) (d_s9 D) (d_s10 D) (d_s11 D).

Definition dfr0 (D : dctx) : list cell :=
  [C8 (wz 0); J D 0; J D 1; J D 2; J D 3; J D 4; J D 5; J D 6; J D 7; J D 8; J D 9; J D 10; J D 11; J D 12; J D 13; J D 14; J D 15;
   J D 16; J D 17; J D 18; J D 19; J D 20; J D 21] ++ dsaves D.

Definition dfr1 (D : dctx) (w15 : cell) : list cell :=
  [C8 (wz 0); J D 0; J D 1; J D 2; J D 3; J D 4; J D 5; J D 6; J D 7; J D 8; J D 9; J D 10; J D 11; J D 12; J D 13; J D 14; J D 15;
   C8 (wz (d_f1 D)); w15; J D 18; C8 (wz (d_f1 D)); J D 20; J D 21] ++ dsaves D.

Definition MASK56 : Z := 72057594037927935.
Definition dfrL (D : dctx) (sv1 sv2 : list byte) : list cell :=
  [C8 (wz 0); J D 0; J D 1; C8 (wz (d_f1 D + 64)); C8 (wz (d_f1 D + 80)); C8 (wz (d_f1 D + 96)); C8 (wz (d_f1 D + 48));
   C8 (wz 0x239a0); C8 (wz 0x23c00); C8 (wz 0x23ba0); C8 (wz 0x23c60); C8 (wz 0x23900); C8 (wz 0x239c0); C8 (wz 0x23b00);
   C8 (wz (shad (dDOC D + 8))); C8 (wz (dDOC D + 8)); C8 (wz 0x23a20); C8 (wz (d_f1 D)); C8 (wz MASK56); C8 (wz 0x23860); C8 (wz (d_f1 D)); CB 8 sv1; CB 8 sv2]
  ++ dsaves D.

Definition f1sh : list Z := [-15; -15; -15; -15; -8; -14; -8; -14; -8; -14; -8; -14; -8; -14; -8; -13].
Definition f1shadow (i v : Z) : list cell := map (fun z => C1 (Z_to_bv 8 z)) (firstn (Z.to_nat i) f1sh ++ [v] ++ skipn (Z.to_nat i + 1) f1sh).

Lemma dsaves_size : forall D, cells_size (dsaves D) = 104%nat. Proof. intros; reflexivity. Qed.
Lemma dfr0_size : forall D, cells_size (dfr0 D) = 288%nat. Proof. intros; reflexivity. Qed.
Lemma dfr1_size : forall D w15, csize w15 = 8%nat -> cells_size (dfr1 D w15) = 288%nat.
Proof. intros D w15 H. unfold dfr1. rewrite cells_size_app. cbn [cells_size]. unfold J. cbn [csize]. rewrite H. reflexivity. Qed.
Lemma dfrL_size : forall D sv1 sv2, cells_size (dfrL D sv1 sv2) = 288%nat.
Proof. intros D sv1 sv2. reflexivity. Qed.

Definition dctx_ok (D : dctx) : Prop :=
  gctx_ok (d_G D) /\ genv (d_G D) (d_E D) /\ lfA_ok (d_X D) /\ AINV_A (d_E D) (d_m0 D) /\ io_ssp (d_m0 D)
  /\ tape_wfS (ae_T (d_E D)) (ae_S (d_E D)) (ae_sn (d_E D)) ck_any (ae_n (d_E D))
  /\ length (d_j D) = 22%nat /\ lf_lo (d_X D) + EL_DUMP_STACK_A <= lf_S1 (d_X D) + 96.

Section Kit.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RC : rt_contracts RT.
Hypothesis RC2 : rt_contracts2 RT.
Variable PMc : Model -> Prop.
Hypothesis FDO : fdfs_only PMc.
Hypothesis MST : mat_stable PMc.
Notation aevt := (aevt RT PMc).

Definition GINVA (G : gctx) (FL W : Z) (FP : Z -> Prop) (fcs : list cell) (k : Z) (Σ : rts RT) (m : mem) : Prop :=
  ART RT Σ m /\ mem_inv asegs m
  /\ rt_frames RT Σ = g_fr G /\ rt_live RT Σ = g_L G /\ rt_sp0 RT Σ = g_sp0 G /\ g_cr G - k <= rt_credit RT Σ
  /\ stk asegs m (g_lo G) (g_q G)
  /\ (exists fill, OSXW m (g_OS G) FL W fill /\ FP fill) /\ bytes_at asegs m (shad (g_OS G)) (repeat z8 36)
  /\ el_tploc m /\ LOCBA m
  /\ (rw_cells asegs m (g_q G) fcs /\ Z.of_nat (cells_size fcs) = g_fsz G)
  /\ wr_at asegs m (g_ff G) (g_FS G - 8) /\ wr_at asegs m (shad (g_ff G)) (g_FS G / 8)
  /\ (forall a : word, aclient (g_L G) (g_rfr G) (g_usp G) (bv_unsigned a) -> outside (WD (g_OS G)) (bv_unsigned a) -> m a = g_m0 G a).

Local Ltac ul := unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK, SHB in *; lia.
Local Ltac ow := repeat split; try exact I; ul.

Section G.
  Variable G : gctx.
  Hypothesis GOK : gctx_ok G.

  Definition own (a : Z) : Prop :=
    g_q G <= a < g_usp G \/ g_ff G <= a < g_ff G + g_FS G - 8 \/ shad (g_ff G) <= a < shad (g_ff G) + g_FS G / 8.

  Lemma own_aclient : forall a, own a -> aclient (g_L G) (g_fr G) (g_q G) a.
  Proof using AF GOK.
    intros a [H|[H|H]].
    - left. destruct GOK as [(_ & _ & Q & _) _ _ _ _ _ _ _ _]. ul.
    - right; right; right; left. exists (g_ff G), (g_ffk G). split; [left; reflexivity| exact H].
    - do 4 right. exists (g_ff G), (g_ffk G). split; [left; reflexivity|].
      destruct GOK as [_ _ _ _ (F0 & F64 & _) _ _ _ _]. unfold shad in *. Z.div_mod_to_equations. lia.
  Qed.

  Lemma own_not_caller : forall a, own a -> ~ aclient (g_L G) (g_rfr G) (g_usp G) a.
  Proof using AF GOK.
    intros a OW CA. destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) _ (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL].
    unfold own, shad in OW. unfold shad in *.
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
      + pose proof (Z.div_le_mono (g_ff G + g_FS G) f 8 ltac:(lia) A1). ul.
      + pose proof (Z.div_le_mono (f + fs_size k) (g_ff G) 8 ltac:(lia) A1) as X. ul.
  Qed.

  Lemma os_not_own : forall a, (g_OS G <= a < g_OS G + 288 \/ shad (g_OS G) <= a < shad (g_OS G) + 36 \/ 0 <= a < SEGTOP_A) -> ~ own a.
  Proof using AF GOK.
    intros a Ha OW. destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL].
    pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 4) with 1024 in *.
    unfold own in OW. unfold shad in *.
    destruct Ha as [H|[H|H]]; [| | ul].
    - destruct OW as [O|[O|O]]; [ul| ul| ul].
    - destruct OW as [O|[O|O]]; [ul| | ].
      + clear - H O A3 F0 E0 FSR. Z.div_mod_to_equations. lia.
      + destruct A1 as [A1|A1].
        * pose proof (Z.div_le_mono (g_ff G + g_FS G) (g_F G) 8 ltac:(lia) A1). ul.
        * pose proof (Z.div_le_mono (g_F G + 1024) (g_ff G) 8 ltac:(lia) A1). clear - H O H0 FSR. Z.div_mod_to_equations. lia.
  Qed.

  Lemma GINVA_cw : forall FL W FP fcs fcs' k Σ m m' W0,
    GINVA G FL W FP fcs k Σ m -> munch W0 m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    (forall a, outside W0 a \/ own a) -> rw_cells asegs m' (g_q G) fcs' -> cells_size fcs' = cells_size fcs ->
    GINVA G FL W FP fcs' k Σ m'.
  Proof using AF GOK.
    intros FL W FP fcs fcs' k Σ m m' W0 GI MU WM MI' HW FR' FSZ'.
    destruct GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL].
    assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ own x) -> agree_on P m m').
    { intros P HP a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X| exfalso; exact (HP _ Ha X)]. }
    split. { apply (art_client_write RT AF Σ m m' (g_q G) HA); [rewrite SP0; clear - LO2 LQ; ul| | exact WM].
             intros a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. apply Ha. rewrite FRS, LV. exact (own_aclient _ X). }
    split; [exact MI'|]. split; [exact FRS|]. split; [exact LV|]. split; [exact SP0|]. split; [exact CR|].
    split. { apply (stk_agree asegs m m' _ _ ST); [| exact WM]. apply AG. intros x Hx OW. unfold own in OW. clear - Hx OW LQ FLO SHLO. unfold shad in *. ul. }
    split. { exists fill. split; [| exact FOK]. apply (OSXW_agree m m' _ _ _ _ OX); [| exact WM]. apply AG. intros x Hx. apply os_not_own. left. exact Hx. }
    split. { apply (bytes_at_agree asegs m m' _ _ SHO). apply AG. intros x Hx. apply os_not_own. right; left. rewrite repeat_length in Hx. lia. }
    split. { apply (rw_cells_agree_nw asegs m m' _ _ TPL). apply AG. intros x Hx. apply os_not_own. do 2 right. cbn [cells_size csize Nat.add] in Hx. ul. }
    split. { apply (LOCBA_agree m m' LB). apply AG. intros x Hx. apply os_not_own. do 2 right. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. ul. }
    split; [split; [exact FR'| rewrite FSZ'; exact FSZ]|]. split; [exact (wr_at_transport asegs m m' _ _ WF1 WM)|]. split; [exact (wr_at_transport asegs m m' _ _ WF2 WM)|].
    intros a CA OU. rewrite <- (REL a CA OU). apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. exact (own_not_caller _ X CA).
  Qed.
Lemma fs_size_nonneg : forall k, 0 <= fs_size k.
  Proof. intros k. unfold fs_size. rewrite Z.shiftl_mul_pow2 by lia. apply Z.mul_nonneg_nonneg; [lia| apply Z.pow_nonneg; lia]. Qed.

  Lemma below_not_caller : forall a, g_lo G <= a < g_q G -> ~ aclient (g_L G) (g_rfr G) (g_usp G) a.
  Proof using GOK.
    intros a X CA. destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) _ _ (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL].
    destruct CA as [C|[C|[C|[C|C]]]].
    - clear - C X FS0. lia.
    - pose proof (client_static_range _ C). clear - H X LO1. ul.
    - destruct C as (p & n & IN & R). pose proof (LL _ _ IN). clear - H R X. lia.
    - destruct C as (f & kk & IN & R). pose proof (RFR _ _ IN) as (_ & _ & Z1 & _). pose proof (fs_size_nonneg kk). clear - Z1 R X H. lia.
    - destruct C as (f & kk & IN & R). pose proof (RFR _ _ IN) as (_ & _ & _ & _ & Z1 & _). pose proof (fs_size_nonneg kk). unfold shad in *. clear - Z1 R X H. Z.div_mod_to_equations. lia.
  Qed.
  Lemma hw16 : forall a, outside [(g_q G + -16, g_q G)] a \/ own a \/ g_lo G <= a < g_q G.
  Proof using GOK.
    intros a. destruct GOK as [(Q32 & FS0 & QT & LQ) _ _ _ _ _ _ _ _]. cbn [outside].
    destruct (Z_lt_le_dec a (g_q G + -16)) as [L|GE]; [left; split; [lia| exact I]|].
    destruct (Z_lt_le_dec a (g_q G)) as [L2|GE2]; [right; right; clear - GE L2 LQ; ul| left; split; [lia| exact I]].
  Qed.
  Lemma hw16s : forall a, outside [(g_q G + -16, g_q G)] a \/ g_lo G <= a < g_q G.
  Proof using GOK.
    intros a. destruct GOK as [(Q32 & FS0 & QT & LQ) _ _ _ _ _ _ _ _]. cbn [outside].
    destruct (Z_lt_le_dec a (g_q G + -16)) as [L|GE]; [left; split; [lia| exact I]|].
    destruct (Z_lt_le_dec a (g_q G)) as [L2|GE2]; [right; clear - GE L2 LQ; ul| left; split; [lia| exact I]].
  Qed.

  Lemma GINVA_stk : forall FL W FP fcs k Σ m m' W0,
    GINVA G FL W FP fcs k Σ m -> munch W0 m m' -> wmono asegs m m' -> mem_inv asegs m' -> stk asegs m' (g_lo G) (g_q G) ->
    (forall a, outside W0 a \/ g_lo G <= a < g_q G) -> GINVA G FL W FP fcs k Σ m'.
  Proof using AF GOK.
    intros FL W FP fcs k Σ m m' W0 GI MU WM MI' ST' HW.
    destruct GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL].
    assert (AG : forall P : Z -> Prop, (forall x, P x -> ~ (g_lo G <= x < g_q G)) -> agree_on P m m').
    { intros P HP a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X| exfalso; exact (HP _ Ha X)]. }
    split. { apply (art_client_write RT AF Σ m m' (g_lo G) HA); [rewrite SP0; exact LO2| | exact WM].
             intros a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. apply Ha. left. clear - X QT FS0. ul. }
    split; [exact MI'|]. split; [exact FRS|]. split; [exact LV|]. split; [exact SP0|]. split; [exact CR|]. split; [exact ST'|].
    split. { exists fill. split; [| exact FOK]. apply (OSXW_agree m m' _ _ _ _ OX); [| exact WM]. apply AG. intros x Hx. clear - Hx ELO. lia. }
    split. { apply (bytes_at_agree asegs m m' _ _ SHO). apply AG. intros x Hx. rewrite repeat_length in Hx. unfold shad in *. clear - Hx E0 LO1 ELO LQ QT FS0. unfold USTACK_TOP, RT_STACK, SHB in *. Z.div_mod_to_equations. lia. }
    split. { apply (rw_cells_agree_nw asegs m m' _ _ TPL). apply AG. intros x Hx. cbn [cells_size csize Nat.add] in Hx. clear - Hx LO1. lia. }
    split. { apply (LOCBA_agree m m' LB). apply AG. intros x Hx. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Hx. clear - Hx LO1. lia. }
    split. { split; [| exact FSZ]. apply (rw_cells_agree_nw asegs m m' _ _ FR). apply AG. intros x Hx. clear - Hx. lia. }
    split. { apply (wr_at_agree_nw asegs m m' _ _ WF1). apply AG. intros x Hx. clear - Hx FLO FSR. lia. }
    split. { apply (wr_at_agree_nw asegs m m' _ _ WF2). apply AG. intros x Hx. clear - Hx SHLO FSR. lia. }
    intros a CA OU. rewrite <- (REL a CA OU). apply MU. destruct (HW (bv_unsigned a)) as [X|X]; [exact X|]. exfalso. exact (below_not_caller _ X CA).
  Qed.
  Lemma ainv_caller : forall E x, genv G E -> ainv_rng E x -> aclient (g_L G) (g_rfr G) (g_usp G) x /\ outside (WD (g_OS G)) x.
  Proof using AF GOK.
    intros E x (OK & ELO & EDOC & EFD & EKD & INT & INS & INP & QHI) Hx.
    destruct GOK as [_ (LO1 & LO2) _ (E0 & E64 & ESEG & ELO' & EIN & ESH & ESHL & EHI) _ _ _ RFR LL].
    pose proof (RFR _ _ EIN) as (_ & _ & _ & _ & _ & FAP). change (fs_size 4) with 1024 in FAP.
    pose proof OK as OK'. destruct OK' as [WF SBS P1 P1L (T16 & NT8 & TN & TS & TL) (S16 & NS8 & SN & SS & SL) PTRR PTR0 (D8 & DF & DL & DS & DT) LOW' [HL HT]].
    unfold ainv_rng in Hx. rewrite EDOC in Hx. unfold WD, EL_TPLOC_A, TPV_A. cbn [outside].
    destruct Hx as [Hx|[Hx|[Hx|[Hx|Hx]]]].
    - pose proof (LL _ _ INT) as (? & ? & ?). pose proof (FAP _ _ INT) as [? _]. split; [right; right; left; exists (ae_TAPE E), (ae_NT E); split; [exact INT| lia]|]. unfold shad in *. ow.
    - pose proof (LL _ _ INS) as (? & ? & ?). pose proof (FAP _ _ INS) as [? _]. split; [right; right; left; exists (ae_SBUF E), (ae_NS E); split; [exact INS| lia]|]. unfold shad in *. ow.
    - destruct INP as [E0'|INPB]; [rewrite E0' in Hx; unfold zlength in Hx; cbn [length] in Hx; lia|].
      assert (NE : ae_p1 E <> []) by (intros E1; rewrite E1 in Hx; unfold zlength in Hx; cbn [length] in Hx; lia).
      pose proof (PTRR NE) as (PB0 & PB1 & PB2 & PB3). pose proof (LL _ _ INPB) as (? & ? & ?). pose proof (FAP _ _ INPB) as [? _].
      split; [right; right; left; exists (ae_PB E), (ae_NPB E); split; [exact INPB| lia]|]. unfold shad in *. ow.
    - split; [right; right; right; left; exists (g_F G), 4%nat; split; [exact EIN| change (fs_size 4) with 1024; lia]|]. unfold shad in *. ow.
    - split; [do 4 right; exists (g_F G), 4%nat; split; [exact EIN| change (fs_size 4) with 1024; unfold shad in *; clear - Hx E64; Z.div_mod_to_equations; lia]|].
      unfold shad, SHB in *. clear - Hx E0 E64 ESH ESEG. unfold SEGTOP_A in ESEG. repeat split; try exact I; Z.div_mod_to_equations; lia.
  Qed.

  Lemma GINVA_ainv : forall E FL W FP fcs k Σ m, genv G E -> AINV_A E (g_m0 G) -> GINVA G FL W FP fcs k Σ m -> AINV_A E m.
  Proof using AF GOK.
    intros E FL W FP fcs k Σ m GE AI0 GI. destruct GI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REL).
    apply (AINV_A_agree E (g_m0 G) m AI0). intros a Ha. destruct (ainv_caller E _ GE Ha) as [H1 H2]. exact (REL a H1 H2).
  Qed.

  Lemma GINVA_alive : forall E FL W FP fcs k Σ m, genv G E -> GINVA G FL W FP fcs k Σ m -> a_live RT Σ E.
  Proof using AF GOK.
    intros E FL W FP fcs k Σ m (OK & ELO & EDOC & EFD & EKD & INT & INS & INP & QHI) (_ & _ & FRS & LV & SP0 & _).
    destruct GOK as [_ (LO1 & LO2) _ (_ & _ & _ & _ & EIN & _) _ _ _ _ _].
    unfold a_live. rewrite LV, FRS, SP0, EFD, EKD, ELO. split; [exact INT|]. split; [exact INS|]. split; [exact INP|]. split; [right; exact EIN| exact LO2].
  Qed.

  Lemma GINVA_iossp : forall FL W FP fcs k Σ m, io_ssp (g_m0 G) -> GINVA G FL W FP fcs k Σ m -> io_ssp m.
  Proof using AF GOK.
    intros FL W FP fcs k Σ m (g & G1 & G2) (HA & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & REL).
    destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) _ (E0 & E64 & ESEG & _) _ _ _ _ _].
    exists g. split; [exact (proj1 (af_got_lib RT AF Σ m HA))|]. apply (ro_cells_agree asegs (g_m0 G) m _ _ G2).
    intros a Ha. cbn [cells_size csize Nat.add] in Ha. apply REL.
    - right; left. apply client_static_intro; clear - Ha; lia.
    - unfold WD, EL_TPLOC_A, TPV_A. cbn [outside]. clear - Ha ESEG. ow.
  Qed.

  Lemma GINVA_shz : forall E FL W FP fcs k Σ m, genv G E -> AINV_A E (g_m0 G) -> GINVA G FL W FP fcs k Σ m ->
    shz m (ae_TAPE E) (8 * ae_n E) /\ shz m (ae_SBUF E) (ae_NS E) /\ shz m (ae_DOC E) 16.
  Proof using AF GOK.
    intros E FL W FP fcs k Σ m GE AI0 GI. pose proof GI as (HA & _). pose proof GE as (OK & _ & _ & _ & _ & _ & INS & _).
    split; [exact (lvl_shz_tape RT AF E OK Σ m HA (GINVA_alive E _ _ _ _ _ _ _ GE GI))|].
    split; [| exact (lvl_shz_doc E OK m (GINVA_ainv E _ _ _ _ _ _ _ GE AI0 GI))].
    destruct GI as (_ & _ & _ & LV & _). destruct (Atp_defsA.ok_sbuf E OK) as (S16 & NS8 & _).
    pose proof (shz_live RT AF Σ m _ _ HA ltac:(rewrite LV; exact INS) ltac:(clear - S16; Z.div_mod_to_equations; lia)) as X.
    replace (8 * (ae_NS E / 8)) with (ae_NS E) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X.
  Qed.

  Lemma GINVA_wfacts : forall E FL W FP fcs k Σ m, genv G E -> AINV_A E (g_m0 G) -> GINVA G FL W FP fcs k Σ m ->
    forall W0 m', munch W0 m m' -> wmono asegs m m' -> (forall a, outside W0 a \/ own a \/ g_lo G <= a < g_q G) ->
    ART RT Σ m' /\ AINV_A E m' /\ shz m' (ae_TAPE E) (8 * ae_n E) /\ shz m' (ae_SBUF E) (ae_NS E) /\ shz m' (ae_DOC E) 16.
  Proof using AF GOK.
    intros E FL W FP fcs k Σ m GE AI0 GI W0 m' MU WM HW.
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & _ & _ & _ & _ & _ & _ & _ & REL). pose proof GE as (OK & _ & _ & _ & _ & _ & INS & _).
    destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) _ _ _ _ _ _ _].
    assert (HA' : ART RT Σ m').
    { apply (art_client_write RT AF Σ m m' (g_lo G) HA); [rewrite SP0; exact LO2| | exact WM].
      intros a Ha. apply MU. destruct (HW (bv_unsigned a)) as [X|[X|X]]; [exact X| |]; exfalso; apply Ha; rewrite FRS, LV.
      - apply (aclient_mono _ _ _ _ _ _ _ (own_aclient _ X)); [auto| auto| clear - LQ; ul].
      - left. clear - X QT FS0. ul. }
    assert (AI' : AINV_A E m').
    { apply (AINV_A_agree E m m' (GINVA_ainv E _ _ _ _ _ _ _ GE AI0 GI)). intros a Ha. apply MU.
      destruct (ainv_caller E _ GE Ha) as [H1 _].
      destruct (HW (bv_unsigned a)) as [X|[X|X]]; [exact X| exfalso; exact (own_not_caller _ X H1)| exfalso; exact (below_not_caller _ X H1)]. }
    split; [exact HA'|]. split; [exact AI'|].
    split; [exact (lvl_shz_tape RT AF E OK Σ m' HA' (GINVA_alive E _ _ _ _ _ _ _ GE GI))|].
    split; [| exact (lvl_shz_doc E OK m' AI')].
    destruct (Atp_defsA.ok_sbuf E OK) as (S16 & NS8 & _).
    pose proof (shz_live RT AF Σ m' _ _ HA' ltac:(rewrite LV; exact INS) ltac:(clear - S16; Z.div_mod_to_equations; lia)) as X.
    replace (8 * (ae_NS E / 8)) with (ae_NS E) in X by (clear - NS8; Z.div_mod_to_equations; lia). exact X.
  Qed.

  Lemma GINVA_after : forall FL W FP FL' W' (FP' : Z -> Prop) fcs k k' Σ Σ' m m' PW,
    GINVA G FL W FP fcs k Σ m ->
    ART RT Σ' m' -> mem_inv asegs m' -> stk asegs m' (g_lo G) (g_q G) ->
    (exists fill, OSXW m' (g_OS G) FL' W' fill /\ FP' fill) -> el_tploc m' -> LOCBA m' ->
    rt_live RT Σ' = rt_live RT Σ -> rt_frames RT Σ' = rt_frames RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ -> g_cr G - k' <= rt_credit RT Σ' ->
    rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (g_q G) PW m m' -> (forall a, outside (WD (g_OS G)) a -> outside PW a) ->
    GINVA G FL' W' FP' fcs k' Σ' m'.
  Proof using AF GOK.
    intros FL W FP FL' W' FP' fcs k k' Σ Σ' m m' PW GI HA' MI' ST' OX' TPL' LB' LV' FRS' SP0' CR' PRES HPW.
    destruct GI as (HA & MI & FRS & LV & SP0 & CR & ST & _ & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO & FSR & FHI & SHLO & SHAP) FFR FFL RFR LL].
    rewrite FRS, LV in PRES.
    assert (AG : forall P : Z -> Prop, (forall x, P x -> aclient (g_L G) (g_fr G) (g_q G) x /\ outside (WD (g_OS G)) x) -> agree_on P m m').
    { intros P HP a Ha. destruct (HP _ Ha) as [H1 H2]. exact (PRES a H1 (HPW _ H2)). }
    split; [exact HA'|]. split; [exact MI'|]. split; [rewrite FRS'; exact FRS|]. split; [rewrite LV'; exact LV|]. split; [rewrite SP0'; exact SP0|]. split; [exact CR'|].
    split; [exact ST'|]. split; [exact OX'|].
    split. { apply (bytes_at_agree asegs m m' _ _ SHO). apply AG. intros x Hx. rewrite repeat_length in Hx. split.
             - do 4 right. exists (g_F G), 4%nat. split; [right; exact EIN|]. change (fs_size 4) with 1024. unfold shad in *. clear - Hx E64. Z.div_mod_to_equations. lia.
             - unfold WD, EL_TPLOC_A, TPV_A. cbn [outside]. unfold shad, SHB in *. clear - Hx E0 E64 ESH ESEG. unfold SEGTOP_A in ESEG.
               repeat split; try exact I; Z.div_mod_to_equations; lia. }
    split; [exact TPL'|]. split; [exact LB'|].
    split. { split; [| exact FSZ]. apply (rw_cells_agree_nw asegs m m' _ _ FR). apply AG. intros x Hx. rewrite FSZ in Hx. split; [left; clear - Hx QT; ul|]. unfold WD, EL_TPLOC_A, TPV_A. cbn [outside]. clear - Hx LQ LO1 ELO. ow. }
    split. { apply (wr_at_agree_nw asegs m m' _ _ WF1). apply AG. intros x Hx. split; [apply own_aclient; right; left; clear - Hx; lia|].
             pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 4) with 1024 in *. unfold WD, EL_TPLOC_A, TPV_A. cbn [outside]. clear - Hx A1 FSEG FSR. ow. }
    split. { apply (wr_at_agree_nw asegs m m' _ _ WF2). apply AG. intros x Hx. split; [apply own_aclient; do 2 right; clear - Hx; lia|].
             pose proof (FFR _ _ EIN) as (A1 & A2 & A3). change (fs_size 4) with 1024 in *. unfold WD, EL_TPLOC_A, TPV_A. cbn [outside]. unfold shad in *. clear - Hx A2 FSEG FSR F0. repeat split; try exact I; unfold SEGTOP_A, SHB in *; Z.div_mod_to_equations; lia. }
    intros a CA OU. rewrite <- (REL a CA OU). apply PRES; [| exact (HPW _ OU)].
    apply (aclient_mono _ _ _ _ _ _ _ CA); [auto| intros e He; right; exact He| clear - FS0; lia].
  Qed.

  Lemma GINVA_callctx : forall FL W FP fcs k Σ m, GINVA G FL W FP fcs k Σ m ->
    In (g_F G, 4%nat) (rt_frames RT Σ) /\ g_F G <= g_OS G /\ g_OS G + 288 <= g_F G + fs_size 4 - 8 /\ g_OS G mod 16 = 0
    /\ os_hullA m (g_OS G) /\ rt_sp0 RT Σ - STACK_WIN <= g_lo G /\ g_q G + 16 <= USTACK_TOP /\ g_q G mod 16 = 0 /\ g_q G mod 32 = 0
    /\ Z.of_nat (length (rt_frames RT Σ)) = Z.of_nat (length (g_rfr G)) + 1.
  Proof using AF GOK.
    intros FL W FP fcs k Σ m (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & FS0 & QT & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) _ _ _ _ _].
    rewrite FRS, SP0. split; [right; exact EIN|]. split; [lia|]. split; [change (fs_size 4) with 1024; lia|]. split; [clear - E64; Z.div_mod_to_equations; lia|].
    split. { split; [| exact SHO]. destruct OX as (pb & pp & ep & dum & j148 & j284 & H & _). apply rw_cells_forget in H. rewrite os_cellsX_size in H. exact H. }
    split; [exact LO2|]. split; [clear - QT FS0; lia|]. split; [clear - Q32; Z.div_mod_to_equations; lia|]. split; [exact Q32|]. cbn [length]. lia.
  Qed.

  Lemma g_ins : forall ENTRY VOKP FL W (FLS FP FP' : Z -> Prop) DEPTH fcs k Σ (K : config -> Prop) (v : Z)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ins_cpsA RT PMc ENTRY VOKP FL W FLS DEPTH ->
    GINVA G FL W FP fcs k Σ m -> io_ssp (g_m0 G) -> (forall f, FP f -> FLS f) -> (forall f, FP f -> FP' (fill_after f)) -> VOKP v -> frm0 fc ->
    g_lo G + DEPTH <= g_q G -> Z.of_nat (length (g_rfr G)) + 2 <= FRAMES_TOT -> k + 1 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m',
       GINVA G FL 0 FP' fcs (k + 1) Σ' m' -> frm0 fc' ->
       aevt Σ' K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_F G + 368)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_F G + 368)) (wz v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz ENTRY) fc None m (seg_rom asegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros INS GI IOS0 HFLS HFP' HV FRM DEP FRL CRK HK.
    replace (g_F G + 368) with (g_OS G + 128) by lia.
    pose proof (GINVA_callctx _ _ _ _ _ _ _ GI) as (INF & FLO & FHI & AL16 & HULL & WLO & QT & Q16 & Q32' & LEN).
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    eapply (INS Σ K (g_OS G) (g_q G) (g_lo G) (g_F G) fill v 4%nat); try eassumption;
      try (apply HFLS; exact FOK); try exact (GINVA_iossp _ _ _ _ _ _ _ IOS0 GI); try (clear HK; lia).
    intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' HA' MI' ST' OX' HULL' LB' TPL' FRM' LV' FRS' SP0' CR' PRES.
    replace (g_OS G + 128) with (g_F G + 368) by lia. apply HK; [| exact FRM'].
    eapply (GINVA_after FL W FP FL 0 FP' fcs k (k + 1) Σ Σ' m m'); try eassumption.
    + exists (fill_after fill). split; [exact OX'| apply HFP'; exact FOK].
    + lia.
    + intros a Ha. exact Ha.
  Qed.

  Lemma g_put : forall (FP FP' : Z -> Prop) fcs k Σ (K : config -> Prop) (BUF N CAP : Z) (bs : list byte)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    os_put_cpsA RT PMc ->
    GINVA G 0x1002 0 FP fcs k Σ m -> (forall f, FP f -> FILLOK f) -> (forall f, FP f -> FP' (fill_after f)) ->
    bytes_at asegs m BUF bs -> Z.of_nat (length bs) = CAP -> 0 <= N <= CAP -> CAP <= 2^40 -> 0 < BUF -> acc asegs m BUF N -> srcA RT Σ (g_q G) BUF CAP bs ->
    (BUF + CAP <= g_OS G \/ g_OS G + 288 <= BUF) ->
    g_lo G + EL_PUT_STACK_A <= g_q G -> Z.of_nat (length (g_rfr G)) + 3 <= FRAMES_TOT -> k + 2 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) m',
       GINVA G 0x1002 0 FP' fcs (k + 2) Σ' m' ->
       aevt Σ' K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_F G + 368)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_F G + 368)) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz EL_OSPUT) fc None m (seg_rom asegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros PUT GI HFLS HFP' BB BL NR CAPH B0 ACC SRC SEP DEP FRL CRK HK.
    replace (g_F G + 368) with (g_OS G + 128) by lia.
    pose proof (GINVA_callctx _ _ _ _ _ _ _ GI) as (INF & FLO & FHI & AL16 & HULL & WLO & QT & Q16 & Q32' & LEN).
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    eapply (PUT Σ K (g_OS G) BUF N CAP (g_q G) (g_lo G) (g_F G) fill 4%nat); try eassumption;
      try (apply (proj2 (OSX_W m (g_OS G) fill)); exact OX); try (apply HFLS; exact FOK); try (clear HK; lia).
    intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' HA' MI' ST' OX' HULL' LB' LV' FRS' SP0' CR' PRES.
    replace (g_OS G + 128) with (g_F G + 368) by lia. apply HK.
    eapply (GINVA_after 0x1002 0 FP 0x1002 0 FP' fcs k (k + 2) Σ Σ' m m'); try eassumption.
    + exists (fill_after fill). split; [apply (proj1 (OSX_W m' (g_OS G) _)); exact OX'| apply HFP'; exact FOK].
    + apply (rw_cells_agree_nw asegs m m' _ _ TPL). intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite FRS, LV in PRES. apply PRES.
      * right; left. apply client_static_intro; clear - Ha; lia.
      * cbn [outside]. destruct GOK as [_ _ _ (E0 & E64 & ESEG & _) _ _ _ _ _]. clear - Ha ESEG. ow.
    + lia.
    + intros a Ha. unfold WD in Ha. cbn [outside] in Ha |- *. tauto.
  Qed.

  Lemma g_put_lit : forall (FP FP' : Z -> Prop) fcs k Σ (K : config -> Prop) (BUF N CAPL : Z) (nb : nat)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    os_put_cpsA RT PMc ->
    GINVA G 0x1002 0 FP fcs k Σ m -> (forall f, FP f -> FILLOK f) -> (forall f, FP f -> FP' (fill_after f)) ->
    In (BUF, CAPL) ACC_LITS -> ro_bytes_b asegs BUF (lit BUF nb) = true -> length (lit BUF nb) = nb -> Z.of_nat nb <= CAPL -> 0 <= N <= Z.of_nat nb ->
    0x10000 <= BUF -> BUF + CAPL <= SEGTOP_A ->
    g_lo G + EL_PUT_STACK_A <= g_q G -> Z.of_nat (length (g_rfr G)) + 3 <= FRAMES_TOT -> k + 2 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) m',
       GINVA G 0x1002 0 FP' fcs (k + 2) Σ' m' ->
       aevt Σ' K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_F G + 368)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_F G + 368)) (wz BUF) (wz N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz EL_OSPUT) fc None m (seg_rom asegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros PUT GI HFLS HFP' INL RB LL NBC NR BLO BHI DEP FRL CRK HK.
    pose proof GI as (HA & MI & _). destruct GOK as [_ _ _ (E0 & E64 & ESEG & _) _ _ _ _ _].
    destruct (lit_bytes BUF nb RB LL ltac:(lia) ltac:(unfold SEGTOP_A in BHI; lia) m MI) as [LB RO].
    eapply (g_put FP FP' fcs k Σ K BUF N (Z.of_nat nb) (lit BUF nb)); try eassumption; try (clear HK; unfold SEGTOP_A in *; lia); try (rewrite LL; reflexivity).
    all: lazymatch goal with
         | |- acc _ _ _ _ => apply (acc_sub asegs m BUF CAPL); [exact (acc_lit RT AF Σ m BUF CAPL HA INL)| lia| lia]
         | |- srcA _ _ _ _ _ _ => left; split; [exact RO|]; split; [lia|]; split; [unfold SEGTOP_A in BHI; lia|]; exists BUF, CAPL; split; [exact INL| lia]
         end.
  Qed.

  Lemma g_put_ownc : forall (FP FP' : Z -> Prop) fcs k Σ (K : config -> Prop) (off : Z) (b : byte)
      (ra gp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    os_put_cpsA RT PMc ->
    GINVA G 0x1002 0 FP fcs k Σ m -> (forall f, FP f -> FILLOK f) -> (forall f, FP f -> FP' (fill_after f)) ->
    rw_cells asegs m (g_ff G + off) [C1 b] -> rw_cells asegs m (shad (g_ff G) + off / 8) [C1 (Z_to_bv 8 1)] -> off mod 8 = 0 -> 0 <= off -> off + 8 <= g_FS G - 8 ->
    g_lo G + EL_PUT_STACK_A <= g_q G -> Z.of_nat (length (g_rfr G)) + 3 <= FRAMES_TOT -> k + 2 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) m',
       GINVA G 0x1002 0 FP' fcs (k + 2) Σ' m' ->
       aevt Σ' K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_F G + 368)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_F G + 368)) (wz (g_ff G + off)) (wz 1) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz EL_OSPUT) fc None m (seg_rom asegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros PUT GI HFLS HFP' CC CS O8 O0 OH DEP FRL CRK HK.
    pose proof GI as (HA & MI & FRS & _). destruct GOK as [_ _ _ (E0 & E64 & ESEG & ELO & EIN & _) (F0 & F64 & FSEG & FLO & FSR & _) FFR _ _ _].
    pose proof (FFR _ _ EIN) as (A1 & _ & _). change (fs_size 4) with 1024 in A1.
    pose proof (rw_cells_bytes_at asegs m _ _ CC) as BB. cbn [cells_bytes cbytes app] in BB.
    pose proof (rw_cells_bytes_at asegs m _ _ CS) as BS. cbn [cells_bytes cbytes app] in BS.
    eapply (g_put FP FP' fcs k Σ K (g_ff G + off) 1 1 [b]); try eassumption; try (clear HK; unfold SEGTOP_A in *; lia); try reflexivity.
    all: lazymatch goal with
         | |- acc _ _ _ _ => apply (acc_ushadow asegs m (g_ff G + off) 1); [clear - F64 O8; Z.div_mod_to_equations; lia| lia| lia|];
               unfold ushadow; cbn [Z.div Z.modulo Z.eqb repeat app Z.to_nat Z.div_eucl Z.pos_div_eucl Pos.eqb];
               replace (shad (g_ff G + off)) with (shad (g_ff G) + off / 8); [exact BS|]; unfold shad; clear - F64 O8 O0; Z.div_mod_to_equations; lia
         | |- srcA _ _ _ _ _ _ => right; right; exists (g_ff G), (g_ffk G); rewrite FRS; split; [left; reflexivity| lia]
         end.
  Qed.

  Lemma g_insd : forall (FP FP' : Z -> Prop) fcs k Σ (K : config -> Prop)
      (ra gp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    ins_d_cpsA RT PMc ->
    GINVA G 0x1002 0 FP fcs k Σ m -> io_ssp (g_m0 G) -> (forall f, FP f -> FILLOK f) -> (forall f, FP f -> FP' (fill_after f)) -> frm0 fc ->
    g_lo G + EL_INSD_STACK_A <= g_q G -> Z.of_nat (length (g_rfr G)) + 2 <= FRAMES_TOT -> k + 1 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) (fc' : bv 32) m',
       GINVA G 0x1002 0 FP' fcs (k + 1) Σ' m' -> frm0 fc' ->
       aevt Σ' K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_F G + 368)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom asegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_F G + 368)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz EL_INS_D) fc None m (seg_rom asegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros INS GI IOS0 HFLS HFP' FRM DEP FRL CRK HK.
    replace (g_F G + 368) with (g_OS G + 128) by lia.
    pose proof (GINVA_callctx _ _ _ _ _ _ _ GI) as (INF & FLO & FHI & AL16 & HULL & WLO & QT & Q16 & Q32' & LEN).
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    eapply (INS Σ K (g_OS G) (g_q G) (g_lo G) (g_F G) fill 4%nat (reg_get F (Z_to_bv 5 10))); try eassumption;
      try (apply HFLS; exact FOK); try exact (GINVA_iossp _ _ _ _ _ _ _ IOS0 GI); try reflexivity; try (clear HK; lia).
    intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc' m' HA' MI' ST' OX' HULL' LB' TPL' FRM' LV' FRS' SP0' CR' PRES.
    replace (g_OS G + 128) with (g_F G + 368) by lia. apply HK; [| exact FRM'].
    eapply (GINVA_after 0x1002 0 FP 0x1002 0 FP' fcs k (k + 1) Σ Σ' m m'); try eassumption.
    + exists (fill_after fill). split; [exact OX'| apply HFP'; exact FOK].
    + lia.
    + intros a Ha. exact Ha.
  Qed.

  Lemma g_setfill : forall FL W (FP : Z -> Prop) fcs k Σ (K : config -> Prop) (CP c : Z)
      (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    setfill_cpsA RT PMc ->
    GINVA G FL W FP fcs k Σ m -> (forall f, FP f -> f = 0x20 \/ f = 0x30) ->
    bytes_at asegs m CP [Z_to_bv 8 c] -> 0 <= c < 256 -> g_q G <= CP -> CP + 1 <= g_usp G ->
    (length (g_rfr G) + 2 <= FRAMES_MAX)%nat -> k + 1 <= g_cr G ->
    (forall Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' (F' : bvmap 5 word) m',
       GINVA G FL W (fun f => f = c) fcs (k + 1) Σ' m' ->
       aevt Σ' K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0' t1' t2' s0 s1 (wz (g_F G + 368)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
    aevt Σ K (MS (mkR ra (wz (g_q G)) gp (wz TPV_A) t0 t1 t2 s0 s1 (wz (g_F G + 368)) (wz CP) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz EL_SETFILL) fc None m (seg_rom asegs)).
  Proof using AF FDO MST GOK.
    intros until m. intros SETF GI HF CPB CR8 CPL CPH FRL CRK HK.
    replace (g_F G + 368) with (g_OS G + 128) by lia.
    pose proof (GINVA_callctx _ _ _ _ _ _ _ GI) as (INF & FLO & FHI & AL16 & HULL & WLO & QT & Q16 & Q32' & LEN).
    pose proof GI as (HA & MI & FRS & LV & SP0 & CR & ST & (fill & OX & FOK) & SHO & TPL & LB & (FR & FSZ) & WF1 & WF2 & REL).
    destruct GOK as [(Q32 & FS0 & QT' & LQ) (LO1 & LO2) (SP1 & SP2) (E0 & E64 & ESEG & ELO & EIN & ESH & ESHL & EHI) (F0 & F64 & FSEG & FLO' & FSR & FHI' & SHLO & SHAP) FFR FFL RFR LL].
    eapply (SETF Σ K (g_OS G) (g_q G) (g_lo G) (g_F G) CP FL W fill c 4%nat); try eassumption;
      try (apply HF; exact FOK); try (rewrite FRS; cbn [length]; clear - FRL; lia); try (clear HK; unfold EL_SETFILL_STACK_A; ul).
    intros Σ' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' HA' MI' ST' OX' HULL' LV' FRS' SP0' CR' PRES.
    replace (g_OS G + 128) with (g_F G + 368) by lia. apply HK.
    eapply (GINVA_after FL W FP FL W (fun f => f = c) fcs k (k + 1) Σ Σ' m m'); try eassumption.
    + exists c. split; [exact OX'| reflexivity].
    + apply (rw_cells_agree_nw asegs m m' _ _ TPL). intros a Ha. cbn [cells_size csize Nat.add] in Ha. rewrite FRS, LV in PRES. apply PRES.
      * right; left. apply client_static_intro; clear - Ha; lia.
      * cbn [outside]. clear - Ha ESEG. ow.
    + apply (LOCBA_agree m m' LB). intros a Ha. rewrite FRS, LV in PRES. apply PRES.
      * right; left. apply client_static_intro; unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha; clear - Ha; lia.
      * cbn [outside]. unfold PJ_LOC_LO_A, PJ_LOC_HI_A in Ha. clear - Ha ESEG. ow.
    + lia.
    + intros a Ha. unfold WD in Ha. cbn [outside] in Ha |- *. clear - Ha. repeat split; try exact I. lia.
  Qed.
End G.

Definition DKH : Z := 11.
Definition LSTA (D : dctx) (pc i : Z) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state :=
  MS (mkR x1 (wz (dq D)) (d_gp D) (wz TPV_A) x5 x6 x7 (wz (lf_S1 (d_X D))) (wz (dq D)) x10 x11 x12 x13 x14 x15 x16 x17
          (wz (d_f1 D)) (wz (dF D + 368)) (wz (dDOC D)) (wz (ae_n (d_E D))) (wz (shad (dDOC D))) (wz (shad (d_f1 D))) x24 x25 (wz SHB) (wz i) x28 x29 x30 x31)
     F (wz pc) fc None m (seg_rom asegs).
Definition KLOOPA (D : dctx) (K : config -> Prop) (j c : Z) : Prop :=
  forall (Σ : rts RT) (m : mem) (k : Z) (sv1 sv2 : list byte) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32),
    GINVA (d_G D) 0x1002 0 FILLOK (dfrL D sv1 sv2) k Σ m -> frm0 fc -> 0 <= k -> k <= DKH + EL_DUMP_CW * (j - 1) + EL_DUMP_CSB * c ->
    aevt Σ K (LSTA D 0xb7508 j x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x24 x25 x28 x29 x30 x31 F fc m).

Lemma gctx_ok_intro : forall G Σ m,
  ART RT Σ m -> rt_frames RT Σ = g_fr G -> rt_live RT Σ = g_L G -> rt_sp0 RT Σ = g_sp0 G ->
  g_q G mod 32 = 0 -> 0 <= g_fsz G -> g_usp G + 16 <= USTACK_TOP -> g_lo G + 12800 + RT_STACK <= g_q G ->
  0x7fff7f800000 <= g_lo G -> g_sp0 G - STACK_WIN <= g_lo G ->
  In (g_F G, 4%nat) (g_rfr G) -> (g_ffk G = 0%nat \/ g_ffk G = 1%nat) ->
  gctx_ok G.
Proof using AF.
  intros G Σ m HA FRS LV SP0 Q32 FS0 QT LQ LO1 LO2 EIN FFK.
  assert (INff : In (g_ff G, g_ffk G) (rt_frames RT Σ)) by (rewrite FRS; left; reflexivity).
  assert (INr : forall f k, In (f, k) (g_rfr G) -> In (f, k) (rt_frames RT Σ)) by (intros f k H; rewrite FRS; right; exact H).
  pose proof (af_sp0_range RT AF Σ m HA) as SPR. pose proof (af_sp0_win RT AF Σ m HA) as SPW. rewrite SP0 in SPR, SPW.
  assert (FSZ : g_FS G = 64 \/ g_FS G = 128) by (destruct FFK as [E|E]; rewrite E; [left| right]; reflexivity).
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
  - repeat split; assumption.
  - split; assumption.
  - split; [exact SPR| exact SPW].
  - pose proof (GEN _ _ (INr _ _ EIN)) as (R0 & A1 & A2 & R1 & _ & S0 & S1 & HI & SF & _). change (fs_size 4) with 1024 in *.
    assert (SH8 : shad (g_F G + 1024) = shad (g_F G) + 128) by (unfold shad; clear - A1; Z.div_mod_to_equations; lia). rewrite SH8 in *.
    repeat split; try assumption; lia.
  - pose proof (GEN _ _ INff) as (R0 & A1 & A2 & R1 & _ & S0 & S1 & HI & SF & _).
    assert (SH8 : shad (g_ff G + g_FS G) = shad (g_ff G) + g_FS G / 8) by (unfold shad; clear - A1 FSZ; Z.div_mod_to_equations; lia). rewrite SH8 in *.
    repeat split; try assumption; lia.
  - intros f k Hin. pose proof (GEN _ _ INff) as (_ & A1 & _ & _ & _ & _ & _ & _ & _ & _).
    assert (SH8 : shad (g_ff G + g_FS G) = shad (g_ff G) + g_FS G / 8) by (unfold shad; clear - A1 FSZ; Z.div_mod_to_equations; lia).
    pose proof (af_frames_disj RT AF Σ m (g_ff G) (g_ffk G) f k [] (g_rfr G) HA FRS Hin) as D1.
    pose proof (proj2 (af_fshadow_apart RT AF Σ m (g_ff G) (g_ffk G) HA INff) f k (INr _ _ Hin)) as D2. rewrite SH8 in D2.
    pose proof (proj2 (af_fshadow_apart RT AF Σ m f k HA (INr _ _ Hin)) (g_ff G) (g_ffk G) INff) as D3.
    split; [exact D1|]. split; [exact D2| exact D3].
  - intros p n Hp. pose proof (GEN _ _ INff) as (_ & A1 & _ & _ & _ & _ & _ & _ & _ & LL).
    assert (SH8 : shad (g_ff G + g_FS G) = shad (g_ff G) + g_FS G / 8) by (unfold shad; clear - A1 FSZ; Z.div_mod_to_equations; lia).
    rewrite SH8 in LL. exact (LL p n Hp).
  - intros f k Hin. pose proof (GEN _ _ (INr _ _ Hin)) as (R0 & A1 & A2 & R1 & _ & S0 & S1 & HI & SF & LL).
    split; [exact R0|]. split; [exact A2|]. split; [exact R1|]. split; [exact S0|]. split; [exact S1| exact LL].
  - intros p n Hp. pose proof (af_live_range RT AF Σ m p n HA ltac:(rewrite LV; exact Hp)) as (P0 & P1 & P2). rewrite SP0 in P1.
    split; [exact P0|]. split; [lia| exact P2].
Qed.

Lemma aevt_smalloc0 : forall Σ K (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (lo : Z),
  tp = Z_to_bv 64 0x6a7e68 ->
  (length (rt_frames RT Σ) < FRAMES_MAX)%nat -> 1 <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo ->
  (rt_frames RT Σ = [] -> bv_unsigned sp + 0xa0 <= rt_sp0 RT Σ) ->
  (forall (Σ' : rts RT) (f : Z) t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m',
     rt_after RT Σ' (bv_unsigned sp) lo m m' -> rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m' ->
     wr_at asegs m' f (fs_size 0 - 8) -> wr_at asegs m' (shad f) (fs_size 0 / 8) ->
     rt_frames RT Σ' = (f, 0%nat) :: rt_frames RT Σ -> rt_live RT Σ' = rt_live RT Σ -> rt_sp0 RT Σ' = rt_sp0 RT Σ ->
     rt_credit RT Σ' = rt_credit RT Σ - 1 -> 0 < f -> f mod 64 = 0 -> f + fs_size 0 < USTACK_TOP ->
     aevt Σ' K (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 f) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc None m' (seg_rom asegs))) ->
  aevt Σ K (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 (e_stack_malloc 0)) fc None m (seg_rom asegs)).
Proof using RC FDO MST.
  intros until lo. intros ETP FRL CR ART0 MI0 COK TOPC HK.
  eapply (aevt_icall RT PMc).
  - exact (rc_stack_malloc_0 RT RC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc m lo FDO MST ltac:(left; reflexivity) ETP FRL CR ART0 MI0 COK TOPC).
  - intros c (Σ' & f & HQ & E1 & E2 & E3 & E4 & F1 & F2 & F3). eexists Σ', _. split; [exact HQ|].
    intros ms' (m' & RS & RA & PR & W1 & W2).
    apply (ret_stF_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m' ms' (fun ms => aevt Σ' K ms) RS).
    intros q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F'. exact (HK Σ' f q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 F' m' RA PR W1 W2 E1 E2 E3 E4 F1 F2 F3).
Qed.
End Kit.
