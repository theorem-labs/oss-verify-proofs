(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_dump.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc Atp_setcapA Sj_h_setmd Atp_fzwA Sj_h_deldtor Atp_pdtorA Sj_h_layout Atp_hkit3A Atp_createA Atp_activewA Atp_activeA Pj_pidwA Atp_hkit4A Pj_defsA Pj_hdefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition pid_cost6 (cap : Z) : Z := mcost (al_sbuf cap) + mcost (al_tape cap) + mcost 96 + mcost (sc_idx cap) + mcost 8192 + mcost 1024.

Section Pid1.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis ALLOC : allocate_cps RT.
Hypothesis CREATE : create_cps RT.
Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.

Local Ltac ul := unfold PID_STACK, CREATE_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Lemma fobj_pres_out : forall Σ Σ' live sp W m m' a n, ART RT Σ m -> fobj RT Σ m a n ->
  rt_pres_fp live (rt_frames RT Σ) sp W m m' -> rt_frames RT Σ' = rt_frames RT Σ ->
  (forall x, shad a <= x < shad a + (n + 7) / 8 -> outside W x) -> fobj RT Σ' m' a n.
Proof using AF.
  intros Σ Σ' live sp W m m' a n HA FO PRES FRS HW.
  apply (fobj_agree RT AF Σ Σ' m m' a n HA FO FRS).
  destruct (fobj_shadow_range RT AF Σ m a n HA FO) as (f & c & Hin & S1 & S2 & Q0).
  intros x Hx. cbv beta in Hx. apply PRES; [| exact (HW _ Hx)].
  right; right; right; right. exists f, c. split; [exact Hin| lia].
Qed.

Definition getact_cps2 : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z),
  fdfs_only PMc -> mat_stable PMc -> sj_lib m ->
  ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= USTACK_TOP -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                       t3 t4 t5 t6 F fc e_getact m)))
    (ASTA RT Σ PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 SJ_ACTIVE) m' ms
         /\ rt_after RT Σ (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) SJ_W m m' /\ lib1 m')).

Lemma getact_ok2 : getact_cps2.
Proof using AF.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    FDO MST LIB0 ART0 MI0 ST0 LOW LOR SPT FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (W1 : evt bsegs (ga_post ra usp gp (tp) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fc lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_getact m)).
  { rewrite ESP. destruct LIB0 as [L0|L1]; [apply ga_walk_fresh| apply ga_walk_init]; try assumption; ul. }
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  apply Hk. split; [| apply (cfrm0_of_asta RT Σ PMc _ c1 Hc1); intros ms (m1 & _ & E1 & _); rewrite E1; exact FRM].
  eapply ASTA_conseq; [exact Hc1|]. intros ms (m1 & RS1 & _ & MU1 & WM1 & MI1 & ST1 & LIB1). exists m1.
  split; [rewrite ESP; exact RS1|].
  assert (ART1 : ART RT Σ m1).
  { apply (art_client_write RT AF Σ m m1 (usp - 32) ART0 ltac:(ul)); [| exact WM1].
    intros a Ha. apply MU1. unfold ga_W. cbn [outside].
    split; [intros Hin; apply Ha; left; ul|].
    repeat (split; [intros Hin; apply Ha; right; left; apply client_static_intro; lia|]). exact I. }
  split; [split; [exact ART1| split; [exact MI1| split; [exact WM1| exact ST1]]]|].
  split; [| exact LIB1].
  intros a Ha Hout.
  pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
  apply MU1. unfold ga_W. cbn [outside].
  split; [clear - SPL LOW LOR; ul|].
  unfold SJ_W in Hout. cbn [outside] in Hout. destruct Hout as (O3 & O4 & O8 & O9 & _).
  split; [exact O3|]. split; [exact O4|]. split; [exact O8|]. split; [exact O9| exact I].
Qed.

Definition pid_k1 (Σ0 : rts RT) (PMc : Model -> Prop) (usp lo RES P d cap : Z) (bs jr : list byte)
    (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m0 : mem) : config -> Prop :=
  fun c => exists (Σ2 : rts RT) (impl idx oc ia tape sbuf : Z),
    ASTA RT Σ2 PMc (fun ms => exists (m2 : mem) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (j p1 p17 p57 p12 p28 p50 : list byte),
        ms = MS (mkR (Z_to_bv 64 0xb08ec) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6ab368) t0 t1 t2 (Z_to_bv 64 RES) s1
                     (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                     (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 cap)
                     (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6)
                F' (Z_to_bv 64 0xb08ec) fc' None m2 (seg_rom bsegs)
        /\ ART RT Σ2 m2 /\ mem_inv bsegs m2 /\ stk bsegs m2 lo (usp + -112)
        /\ rw_cells bsegs m2 (usp + -112) (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)
        /\ rw_cells bsegs m2 P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                          (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0))
        /\ fobj RT Σ2 m2 P 80
        /\ rw_cells bsegs m2 impl (impl16 (Z_to_bv 64 0x168a70) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                          (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))
        /\ rw_cells bsegs m2 RES [CB 24 jr] /\ bytes_at bsegs m2 d bs /\ lib1 m2
        /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) usp (pid_XA P RES) m0 m2) c
    /\ rt_live RT Σ2 = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: rt_live RT Σ0
    /\ rt_frames RT Σ2 = rt_frames RT Σ0 /\ rt_sp0 RT Σ2 = rt_sp0 RT Σ0
    /\ rt_credit RT Σ2 = rt_credit RT Σ0 - pid_cost6 cap
    /\ (0 < impl /\ impl mod 16 = 0) /\ (0 < idx /\ idx mod 16 = 0) /\ (0 < oc /\ oc mod 16 = 0) /\ (0 < ia /\ ia mod 16 = 0)
    /\ (0 < tape /\ tape mod 16 = 0) /\ (0 < sbuf /\ sbuf mod 16 = 0).

Lemma bundle_pres : forall live frames W (m m' : mem) usp' RES d (bs : list byte) fr jr,
  rt_pres_fp live frames usp' W m m' ->
  (forall x, (usp' <= x < usp' + 112) \/ (RES <= x < RES + 24) \/ (d <= x < d + Z.of_nat (length bs)) -> aclient live frames usp' x /\ outside W x) ->
  cells_size fr = 112%nat ->
  rw_cells bsegs m usp' fr -> rw_cells bsegs m RES [CB 24 jr] -> bytes_at bsegs m d bs ->
  rw_cells bsegs m' usp' fr /\ rw_cells bsegs m' RES [CB 24 jr] /\ bytes_at bsegs m' d bs.
Proof.
  intros live frames W m m' usp' RES d bs fr jr PRES HC SZ H1 H2 H3.
  assert (AG : agree_on (fun x => (usp' <= x < usp' + 112) \/ (RES <= x < RES + 24) \/ (d <= x < d + Z.of_nat (length bs))) m m').
  { apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES). exact HC. }
  split; [| split].
  - apply (rw_cells_agree_nw bsegs m m' _ _ H1). eapply agree_sub; [exact AG|]. intros x Hx. rewrite SZ in Hx. cbv beta. left. lia.
  - apply (rw_cells_agree_nw bsegs m m' _ _ H2). eapply agree_sub; [exact AG|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. right; left. lia.
  - apply (bytes_at_agree bsegs m m' _ _ H3). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in *. right; right. exact Hx.
Qed.

Lemma lib_pres : forall live frames sp W (m m' : mem) (L : mem -> Prop), fp_local LIB_FP L -> L m ->
  rt_pres_fp live frames sp W m m' -> (forall x, 0x10000 <= x < SEGTOP_A -> outside W x) -> L m'.
Proof.
  intros live frames sp W m m' L LOC HL PRES HW. apply (LOC m m' HL). intros a Ha.
  destruct (lib_fp_static _ Ha) as (CS & _). apply PRES; [right; left; exact CS| exact (HW _ (client_static_range _ CS))].
Qed.

Lemma pid_cells_init : forall (m : mem) P p1 p17 p57, rw_cells bsegs m P (parser_init p1 p17 p57) ->
  rw_cells bsegs m P (pid_cells z8 p1 (Z_to_bv 64 0) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4294967295) z8 p57
                                (Z_to_bv 64 0) (Z_to_bv 64 0)).
Proof.
  intros m P p1 p17 p57 H. pose proof H as ((W & _) & _). unfold parser_init, fz_parser in W. cbn [cells_wf cell_wf] in W.
  destruct W as (_ & L1 & _ & _ & L17 & _ & _ & _ & _ & L57 & _).
  apply (rw_cells_relayout m P _ _ H).
  - unfold pid_cells. cbn [cells_wf cell_wf]. repeat split; assumption.
  - unfold pid_cells, parser_init, fz_parser. cbn [cells_bytes cbytes]. rewrite le8_zero. rewrite <- ?app_assoc. reflexivity.
  - reflexivity.
Qed.

Theorem pid_front : forall (Σ : rts RT) PMc (ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    F fc (m : mem) (P RES d : Z) (bs p1 p17 p57 jr : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 < d -> Z.of_nat (length bs) < 2^26 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  fobj RT Σ m P 80 -> rw_cells bsegs m P (parser_init p1 p17 p57) ->
  bv_unsigned sp <= RES -> RES + 24 <= USTACK_TOP -> rw_cells bsegs m RES [CB 24 jr] ->
  Z.of_nat (length (rt_live RT Σ)) + 6 <= LIVE_MAX -> pid_cost6 (Z.max (Z.of_nat (length bs)) 32) <= rt_credit RT Σ ->
  sj_lib m -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 (Z_to_bv 64 RES) (Z_to_bv 64 P) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 d)
                                       (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 1) a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_pid m)))
        (pid_k1 Σ PMc (bv_unsigned sp) lo RES P d (Z.max (Z.of_nat (length bs)) 32) bs jr ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m).
Proof using AF ALLOC CREATE AFI.
  intros Σ PMc ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P RES d bs p1 p17 p57 jr lo
    FDO MST D0 BSL BS INLV FOBJ0 PINIT RLO RHI RC0 LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  set (usp := bv_unsigned sp) in *. set (len := Z.of_nat (length bs)) in *. set (cap := Z.max len 32) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (LEN0 : 0 <= len) by (subst len; lia).
  destruct (cap_arith len len cap eq_refl ltac:(lia) BSL) as (CAP & _).
  pose proof (al_sbuf_bounds cap CAP) as SBB. pose proof (al_tape_bounds cap CAP) as TPB. pose proof (sc_idx_bounds cap ltac:(lia)) as IXB.
  assert (MC : 0 <= mcost (al_sbuf cap) /\ 0 <= mcost (al_tape cap) /\ 0 <= mcost 96 /\ 0 <= mcost (sc_idx cap) /\ 0 <= mcost 8192 /\ 0 <= mcost 1024)
    by (repeat split; apply mcost_nonneg; lia).
  unfold pid_cost6 in CR0.
  pose proof FOBJ0 as (P8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
  pose proof (fframe_ranges RT AF Σ m f k ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ m f k ART0 INF) as (_ & FSEG).
  apply pid_cells_init in PINIT.

  assert (BCL : forall (Σx : rts RT) x, (forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σx)) -> rt_frames RT Σx = rt_frames RT Σ ->
            (usp + -112 <= x < usp + -112 + 112) \/ (RES <= x < RES + 24) \/ (d <= x < d + len) ->
            aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -112) x /\ ~ (P <= x < P + 80) /\ ~ (0x172920 <= x < 0x6cb6dc)).
  { intros Σx x SUB FRS Hx. destruct Hx as [Hx|[Hx|Hx]].
    - split; [left; ul|]. split; ul.
    - split; [left; ul|]. split; ul.
    - destruct INLV as [(p & n & Hin & P1 & P2)| (E & _)]; [| subst len; rewrite E in Hx; cbn [length] in Hx; lia].
      split; [right; right; left; exists p, n; split; [apply SUB; exact Hin| lia]|].
      pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (R0 & R1 & R2).
      pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (_ & _ & _ & FLV). specialize (FLV p n Hin).
      split; [clear - Hx P1 P2 FLV FLO FHI; lia| clear - Hx P1 P2 R2; unfold SEGTOP_A in *; lia]. }
  assert (OUTLIB : forall x, ~ (0x172920 <= x < 0x6cb6dc) -> outside SJ_W x).
  { intros x Hx. unfold SJ_W. cbn [outside]. repeat (split; [lia|]). exact I. }
  assert (FP1 : fp_client RT Σ lo [(usp - 112, usp)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).

  pose proof (pi_walk1a usp lo RES P d len ra gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                ST0 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(change (2^26) with 67108864 in BSL; lia) (conj G1 G2) MI0) as W1.
  rewrite <- ESP in W1.
  lazymatch type of W1 with evt bsegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ PMc _ _ MST W1') Hc). clear W1'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ _ _ c1 Hc1) as (ms1 & (m1 & j & a0' & -> & MU1 & WM1 & MI1 & ST1 & FR1) & Hc1'). clear Hc1.
  fold cap in Hc1'.
  pose proof (art_fp_client RT AF Σ m m1 lo _ ART0 LOW FP1 MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ m m1 lo _ P 80 ART0 LOW FP1 MU1 FOBJ0) as FOBJ1.
  assert (AG1 : agree_on (fun x => ~ (usp - 112 <= x < usp)) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
  assert (PC1 := PINIT). apply (rw_cells_agree bsegs m m1 _ _) in PC1; [| eapply agree_sub; [exact AG1|]; intros x Hx; unfold pid_cells in Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; ul| exact WM1].
  assert (RC1 := RC0). apply (rw_cells_agree bsegs m m1 _ _) in RC1; [| eapply agree_sub; [exact AG1|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; ul| exact WM1].
  assert (BS1 : bytes_at bsegs m1 d bs).
  { apply (bytes_at_agree bsegs m m1 _ _ BS). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *.
    destruct (BCL Σ x ltac:(auto) eq_refl ltac:(right; right; exact Hx)) as (HA & _).
    pose proof (aclient_split_c RT AF Σ m (usp + -112) x ART0 HA) as SPL.
    destruct INLV as [(p & n & Hin & P1 & P2)| (E & _)]; [| subst len; rewrite E in Hx; cbn [length] in Hx; lia].
    pose proof (af_live_range RT AF Σ m p n ART0 Hin) as (R0 & R1 & _). clear - Hx P1 P2 R1 LOW LOR. ul. }
  assert (LIBm1 : sj_lib m1).
  { apply (sj_lib_loc m m1 LIB0). intros a Ha. apply AG1. destruct (lib_fp_static _ Ha) as (_ & R). clear - R LOW LOR SP0R SP0W. ul. }

  pose proof (pi_walk1b RES P d len cap z8 z8 z8 p1 p17 p57 (Z_to_bv 64 12) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                ra (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6ab368) t0 t1 t2 s1 a0' a6 a7 s4 s7 s11 t3 t4 t5 t6 F fc m1
                ltac:(ul) ltac:(ul) CAP (fobj_shz RT AF Σ m1 P 80 ART1 FOBJ1) PC1) as W1b.
  lazymatch type of W1b with evt bsegs _ ?X =>
    assert (W1b' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W1b) end.
  clear W1b.
  apply (cps_realizes bsegs _ _ _ c1 (asta_evt_c RT AF Σ PMc _ _ MST W1b') Hc1'). clear W1b'. intros c1b Hc1b.
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -112) mod 16 = 0) by (replace (usp + -112) with (usp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).

  unfold pid_cells in PC1.
  change [C1 z8; CB 7 p1; C8 (Z_to_bv 64 0); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
          C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    with ([C1 z8; CB 7 p1; C8 (Z_to_bv 64 0); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12)] ++ [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
          ++ [C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in PC1.
  apply Sj_stage1_kit.rw_cells_app in PC1 as [PCa PC1]. apply Sj_stage1_kit.rw_cells_app in PC1 as [PCd PCz].
  cbn [cells_size csize Nat.add] in PCd, PCz. change (Z.of_nat 24) with 24 in PCd, PCz. replace (P + 24 + 24) with (P + 48) in PCz by lia.
  pose proof (fobj_sub RT AF Σ m1 P 80 24 24 FOBJ1 eq_refl ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as FOBJD1.

  apply (ALLOC Σ PMc (Z_to_bv 64 0xb0610) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6ab368) t0 t1 t2 (Z_to_bv 64 RES) s1
           (Z_to_bv 64 (P + 24)) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 d) (Z_to_bv 64 len) (Z_to_bv 64 1) a6 a7
           (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 1) s7 (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
           (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc m1 (P + 24) cap (Z_to_bv 64 0) lo FDO MST);
    try reflexivity; try assumption;
    [.. | split; [exact Hc1b| apply (cfrm0_of_asta RT Σ PMc (eq _) c1b Hc1b); intros ms0 <-; exact FRM] |].
  - lia.
  - lia.
  - rewrite EU2. exact ST1.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact SPA2.
  - intros c2 ((Σ1 & sbuf & tape & Hc2 & LV1 & FRS1 & SP1 & CR1 & SB0 & SB16 & TP0 & TP16) & FC2).
    destruct (ASTA_unpack_f RT Σ1 _ _ c2 Hc2 FC2) as (ms2 & (m2 & RS2 & (ART2 & MI2 & WM2 & ST2) & PRES2 & PCd2 & _) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb0610) in Hc2' by (clear; lia).
    assert (SUB1 : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σ1)) by (intros e He; rewrite LV1; right; right; exact He).
    assert (LOW1 : rt_sp0 RT Σ1 - STACK_WIN <= lo) by (rewrite SP1; exact LOW).
    assert (INF1 : In (f, k) (rt_frames RT Σ1)) by (rewrite FRS1; exact INF).
    assert (PCL : forall (Σx : rts RT) x, rt_frames RT Σx = rt_frames RT Σ -> P <= x < P + 80 -> aclient (rt_live RT Σx) (rt_frames RT Σx) (usp + -112) x).
    { intros Σx x E Hx. right; right; right; left. exists f, k. split; [rewrite E; exact INF| lia]. }
    destruct (bundle_pres _ _ _ m1 m2 (usp + -112) RES d bs (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) jr PRES2) as (FR2 & RC2 & BS2); [| reflexivity| exact FR1| exact RC1| exact BS1|].
    { intros x Hx. destruct (BCL Σ x ltac:(auto) eq_refl Hx) as (H1 & H2 & _). split; [exact H1|]. cbn [outside]. split; [lia| exact I]. }
    assert (PCa2 : rw_cells bsegs m2 P [C1 z8; CB 7 p1; C8 (Z_to_bv 64 0); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12)]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ PCa). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (PCL Σ); [reflexivity| lia]|]. cbn [outside]. split; [lia| exact I]. }
    assert (PCz2 : rw_cells bsegs m2 (P + 48) [C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
    { apply (rw_cells_agree_nw bsegs m1 m2 _ _ PCz). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (PCL Σ); [reflexivity| lia]|]. cbn [outside]. split; [lia| exact I]. }
    assert (PC2 : rw_cells bsegs m2 P (pid_cells z8 p1 (Z_to_bv 64 0) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                                 (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0))).
    { unfold pid_cells.
      change [C1 z8; CB 7 p1; C8 (Z_to_bv 64 0); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap);
              C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
        with ([C1 z8; CB 7 p1; C8 (Z_to_bv 64 0); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12)] ++ [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap)]
              ++ [C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
      apply Sj_stage1_kit.rw_cells_app. split; [exact PCa2|]. apply Sj_stage1_kit.rw_cells_app. cbn [cells_size csize Nat.add]. change (Z.of_nat 24) with 24.
      replace (P + 24 + 24) with (P + 48) by lia. split; [exact PCd2| exact PCz2]. }
    assert (FOBJ2 : fobj RT Σ1 m2 P 80).
    { apply (fobj_pres_fp RT AF Σ Σ1 _ _ _ m1 m2 P 80 ART1 FOBJ1 PRES2 FRS1).
      intros r [<-|[]]. exists f, k. cbn [fst snd]. split; [exact INF| lia]. }
    assert (LIBm2 : sj_lib m2).
    { apply (lib_pres _ _ _ _ m1 m2 sj_lib sj_lib_loc LIBm1 PRES2). intros x Hx. cbn [outside]. split; [clear - Hx FSEG FLO; unfold SEGTOP_A in *; lia| exact I]. }

    pose proof (pi_walk2 RES P d len cap z8 z8 z8 p1 p17 p57 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap) (Z_to_bv 64 4294967295)
                  (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6ab368) u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s7 u3 u4 u5 u6 F2 fc2 m2
                  ltac:(ul) ltac:(ul) (fobj_shz RT AF Σ1 m2 P 80 ART2 FOBJ2) PC2) as W2.
    lazymatch type of W2 with evt bsegs _ ?X =>
      assert (W2' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W2) end.
    clear W2.
    apply (cps_realizes bsegs _ _ _ c2 (asta_evt_c RT AF Σ1 PMc _ _ MST W2') Hc2'). clear W2'. intros c3 Hc3.

    apply (getact_ok2 Σ1 PMc (Z_to_bv 64 0xb0888) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6ab368) u0 u1 u2 (Z_to_bv 64 RES) s1
             (Z_to_bv 64 0) b1 b2 b3 b4 b5 b6 b7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) u3 u4 u5 u6 F2 fc2 m2 lo FDO MST LIBm2 ART2 MI2);
      [rewrite EU2; exact ST2| exact LOW1| rewrite EU2; ul| rewrite EU2; ul| exact FRM2
      | split; [exact Hc3| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c3 Hc3); intros ms0 <-; exact FRM2] |].
    intros c4 (Hc4 & FC4).
    destruct (ASTA_unpack_f RT Σ1 _ _ c4 Hc4 FC4) as (ms4 & (m4 & RS4 & (ART4 & MI4 & WM4 & ST4) & PRES4 & LIB4) & FRM4 & Hc4'). clear Hc4.
    destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F4 & fc4 & ->).
    cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even 0xb0888) in Hc4' by (clear; lia).
    destruct (bundle_pres _ _ _ m2 m4 (usp + -112) RES d bs (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) jr PRES4) as (FR4 & RC4 & BS4);
      [| reflexivity| exact FR2| exact RC2| exact BS2|].
    { intros x Hx. destruct (BCL Σ1 x SUB1 FRS1 Hx) as (H1 & _ & H3). split; [exact H1| exact (OUTLIB x H3)]. }
    assert (PC4 : rw_cells bsegs m4 P (pid_cells z8 p1 (Z_to_bv 64 0) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                                 (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0))).
    { apply (rw_cells_agree_nw bsegs m2 m4 _ _ PC2). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES4).
      intros x Hx. unfold pid_cells in Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (PCL Σ1 x FRS1); lia|].
      apply OUTLIB. clear - Hx FSEG FLO. unfold SEGTOP_A in *. lia. }
    assert (FOBJ4 : fobj RT Σ1 m4 P 80).
    { apply (fobj_pres_out Σ1 Σ1 _ _ _ m2 m4 P 80 ART2 FOBJ2 PRES4 eq_refl). intros x Hx. apply OUTLIB.
      assert (0 <= P / 8) by (apply Z.div_pos; lia). unfold shad, SHB in Hx. lia. }

    assert (SHA4 : shz m4 0x6a9840 8).
    { apply (shz_static RT AF Σ1 m4 _ _ ART4); [reflexivity| lia| reflexivity|]. intros i Hi. split; [apply client_static_intro; lia| lia]. }
    assert (SHS4 : shz m4 0x6a98e0 8).
    { apply (shz_static RT AF Σ1 m4 _ _ ART4); [reflexivity| lia| reflexivity|]. intros i Hi. split; [apply client_static_intro; lia| lia]. }
    assert (SHV4 : shz m4 0x1689a0 64).
    { apply (shz_lit RT AF Σ1 m4 _ _ ART4); [unfold ACC_LITS; repeat (first [left; reflexivity | right])| reflexivity| lia| reflexivity]. }
    pose proof (pi_walk3 RES P d len cap (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6ab368) w0 w1 w2 s1 g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6 F4 fc4 m4
                  ltac:(ul) ltac:(ul) ltac:(lia) SHA4 SHS4 SHV4 LIB4 (AFI Σ1 m4 ART4)) as W3.
    lazymatch type of W3 with evt bsegs _ ?X =>
      assert (W3' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W3) end.
    clear W3.
    apply (cps_realizes bsegs _ _ _ c4 (asta_evt_c RT AF Σ1 PMc _ _ MST W3') Hc4'). clear W3'. intros c5 Hc5.

    unfold pid_cells in PC4.
    change [C1 z8; CB 7 p1; C8 (Z_to_bv 64 0); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap);
            C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
      with ([C1 z8; CB 7 p1] ++ [C8 (Z_to_bv 64 0)]
            ++ [C1 z8; CB 3 p17; C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap);
                C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in PC4.
    apply Sj_stage1_kit.rw_cells_app in PC4 as [PCh PC4]. apply Sj_stage1_kit.rw_cells_app in PC4 as [PCi PCt].
    cbn [cells_size csize Nat.add] in PCi, PCt. change (Z.of_nat 8) with 8 in PCi, PCt. replace (P + 8 + 8) with (P + 16) in PCt by lia.
    pose proof (fobj_sub RT AF Σ1 m4 P 80 8 8 FOBJ4 eq_refl ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as FOBJI4.

    apply (CREATE Σ1 PMc (Z_to_bv 64 0xb08ec) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6ab368) w0 w1 w2 (Z_to_bv 64 RES) s1
             (Z_to_bv 64 0x6a98e0) (Z_to_bv 64 cap) (Z_to_bv 64 1024) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 0xb30ec) g5 g6 g7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) w3 w4 w5 w6 F4 fc4 m4 (P + 8) cap 1024 lo FDO MST);
      try reflexivity; try assumption;
      [.. | split; [exact Hc5| apply (cfrm0_of_asta RT Σ1 PMc (eq _) c5 Hc5); intros ms0 <-; exact FRM4] |].
    + lia.
    + rewrite LV1. cbn [length]. lia.
    + rewrite CR1. change (8 * 1024) with 8192. lia.
    + rewrite EU2. exact ST4.
    + rewrite EU2. ul.
    + rewrite EU2. ul.
    + rewrite EU2. exact SPA2.
    + intros c6 ((Σ2 & impl & idx & oc & ia & Hc6 & LV2 & FRS2 & SP2 & CR2 & IM & IX & OC & IA) & FC6).
      apply Hk. split; [| exact FC6].
      exists Σ2, impl, idx, oc, ia, tape, sbuf.
      split; [| split; [rewrite LV2, LV1; reflexivity| split; [rewrite FRS2; exact FRS1| split; [rewrite SP2, SP1; reflexivity|
                 split; [rewrite CR2, CR1; unfold pid_cost6; change (8 * 1024) with 8192; lia| repeat split; (lia || assumption || tauto)]]]]].
      eapply ASTA_conseq; [exact Hc6|].
      intros ms (m6 & RS6 & (ART6 & MI6 & WM6 & ST6) & PRES6 & PCi6 & _ & (p12 & p28 & p50 & IC6)).
      destruct RS6 as (x0 & x1 & x2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & x3 & x4 & x5 & x6 & F6 & fc6 & ->).
      rewrite EU2 in ST6, PRES6. rewrite (ret_pc_even 0xb08ec) by lia.
      exists m6, x0, x1, x2, h1, h2, h3, h4, h5, h6, h7, x3, x4, x5, x6, F6, fc6, j, p1, p17, p57, p12, p28, p50.
      split; [reflexivity|]. split; [exact ART6|]. split; [exact MI6|]. split; [exact ST6|].
      destruct (bundle_pres _ _ _ m4 m6 (usp + -112) RES d bs (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) jr PRES6) as (FR6 & RC6 & BS6);
        [| reflexivity| exact FR4| exact RC4| exact BS4|].
      { intros x Hx. destruct (BCL Σ1 x SUB1 FRS1 Hx) as (H1 & H2 & _). split; [exact H1|]. cbn [outside]. split; [lia| exact I]. }
      split; [exact FR6|].
      split.
      { unfold pid_cells.
        change [C1 z8; CB 7 p1; C8 (Z_to_bv 64 impl); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap);
                C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
          with ([C1 z8; CB 7 p1] ++ [C8 (Z_to_bv 64 impl)]
                ++ [C1 z8; CB 3 p17; C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap);
                    C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]).
        apply Sj_stage1_kit.rw_cells_app. split.
        - apply (rw_cells_agree_nw bsegs m4 m6 _ _ PCh). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES6).
          intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (PCL Σ1 x FRS1); lia|]. cbn [outside]. split; [lia| exact I].
        - apply Sj_stage1_kit.rw_cells_app. cbn [cells_size csize Nat.add]. change (Z.of_nat 8) with 8. replace (P + 8 + 8) with (P + 16) by lia.
          split; [exact PCi6|].
          apply (rw_cells_agree_nw bsegs m4 m6 _ _ PCt). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES6).
          intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [apply (PCL Σ1 x FRS1); lia|]. cbn [outside]. split; [lia| exact I]. }
      split.
      { apply (fobj_pres_fp RT AF Σ1 Σ2 _ _ _ m4 m6 P 80 ART4 FOBJ4 PRES6 FRS2).
        intros r [<-|[]]. exists f, k. cbn [fst snd]. split; [exact INF1| lia]. }
      split; [exact IC6|]. split; [exact RC6|]. split; [exact BS6|].
      split.
      { apply (lib_pres _ _ _ _ m4 m6 lib1 lib1_loc LIB4 PRES6). intros x Hx. cbn [outside]. split; [clear - Hx FSEG FLO; unfold SEGTOP_A in *; lia| exact I]. }

      intros a Ha Hout. unfold pid_XA in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & HO3).
      pose proof (aclient_split_c RT AF Σ m usp (bv_unsigned a) ART0 Ha) as SPL.
      assert (Ha0 : aclient (rt_live RT Σ) (rt_frames RT Σ) (usp + -112) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| auto| lia]).
      assert (Ha1 : aclient (rt_live RT Σ1) (rt_frames RT Σ1) (usp + -112) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUB1| rewrite FRS1; auto| lia]).
      rewrite (PRES6 a Ha1), (PRES4 a Ha1 HO3), (PRES2 a Ha0), (AG1 a); [reflexivity| | |].
      * clear - SPL LOW LOR. ul.
      * cbn [outside]. split; [lia| exact I].
      * cbn [outside]. split; [lia| exact I].
Qed.

End Pid1.
