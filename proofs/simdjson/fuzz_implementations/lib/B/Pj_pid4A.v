(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.P Require Import Sj_stage1_kit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc Atp_setcapA Sj_h_setmd Atp_fzwA Sj_h_deldtor Atp_pdtorA Sj_h_layout Atp_hkit3A Sj_stage2_iface Sj_h_parsew Atp_parseA Atp_createA Atp_activewA Atp_activeA Atp_pidiA Pj_defsA Pj_hdefsA Pj_pdtor2A Pj_pidwA Pj_pidw2A Pj_pidw3A Atp_hkit4A Atp_hkit5A Pj_pid1A Pj_pid2A Pj_pid3A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation PIREGF ra sp gp tp t0 t1 t2 s1 RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 :=
  (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1
       a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
       (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) (only parsing).

Lemma mcost_mono : forall a b, 0 <= a <= b -> mcost a <= mcost b.
Proof. intros a b H. unfold mcost, DCOST. destruct (Z.leb_spec a 64512), (Z.leb_spec b 64512); lia. Qed.

Lemma s2a_cost_mono : forall a b, 0 <= a <= b -> S2A_COST a <= S2A_COST b.
Proof. intros a b H. unfold S2A_COST, Sj_num_iface.NUMA_CREDIT. pose proof (mcost_mono (a + 64) (b + 64) ltac:(lia)). lia. Qed.

Section Pid4.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis NEWA : new_cps RT e_newarr_nt.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.
Hypothesis MCP : memcpy_icontract_f RT e_asan_memcpy.
Hypothesis MCMP : memcmp_icontract_f RT.
Hypothesis PARSE : parse_cps RT.
Hypothesis AFC : forall Σ m, ART RT Σ m -> cli_got_nothrow m.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Local Ltac nomod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac std_lia__ := lia.
Local Ltac lia := nomod; std_lia__.
Local Ltac ul := nomod; unfold PID_STACK, PARSE_STACK, S2A_STACK, Sj_num_iface.NUMA_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; std_lia__.

Theorem pid_main : forall (Σ2 : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (m2 : mem) (lo RES P d cap impl idx oc ia tape sbuf : Z) (bs : list byte)
    (L : list (Z * Z)) (jr j p1 p17 p57 p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc -> Z.of_nat (length bs) <= 1048512 -> cap = Z.max (Z.of_nat (length bs)) 32 ->
  0 < d -> bytes_at bsegs m2 d bs ->
  ((exists p n, In (p, n) L /\ p <= d /\ d + Z.of_nat (length bs) <= p + n) \/ (bs = [] /\ d < SEGTOP_A)) ->
  ART RT Σ2 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo (bv_unsigned sp + -112) ->
  rw_cells bsegs m2 (bv_unsigned sp + -112) (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m2 P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                 (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  fobj RT Σ2 m2 P 80 ->
  rw_cells bsegs m2 impl (impl16 (Z_to_bv 64 0x17a150) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                 (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  rw_cells bsegs m2 RES [CB 24 jr] -> lib1 m2 ->
  rt_live RT Σ2 = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: L ->
  (forall p n, In (p, n) L -> 0 < n) ->
  impl mod 16 = 0 -> idx mod 16 = 0 -> oc mod 16 = 0 -> ia mod 16 = 0 -> tape mod 16 = 0 -> sbuf mod 16 = 0 ->
  (length (rt_frames RT Σ2) + S2A_FRAMES <= FRAMES_MAX)%nat ->
  mcost (Z.of_nat (length bs) + 64) + S2A_COST (Z.of_nat (length bs)) <= rt_credit RT Σ2 -> Z.of_nat (length (rt_live RT Σ2)) + 1 < LIVE_MAX ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP ->
  rt_sp0 RT Σ2 - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc' ->
  cps_f (ASTA RT Σ2 PMc (eq (MS (mkR (Z_to_bv 64 0xb7aa0) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 RES) s1
                                     (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                     (Z_to_bv 64 (Z.of_nat (length bs))) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 cap)
                                     (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6)
                                F' (Z_to_bv 64 0xb7aa0) fc' None m2 (seg_rom bsegs))))
        (pid_post RT Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo RES P L impl idx oc ia tape sbuf cap (Z.of_nat (length bs))
                  (fun cp => exists COPY, cp = [(COPY, Z.of_nat (length bs) + 64)] /\ 0 < COPY)
                  (mcost (Z.of_nat (length bs) + 64) + S2A_COST (Z.of_nat (length bs))) m2).
Proof using AF NEWA MSET MCP MCMP PARSE AFC AFV.
  intros Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m2
    lo RES P d cap impl idx oc ia tape sbuf bs L jr j p1 p17 p57 p12 p28 p50
    FDO MST LEN ECAP D0 BS2 INLV ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LPOS IM16 IX16 OC16 IA16 TP16 SB16 FRB CRB LVB RLO RHI LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ2 m2 ART2) as SP0R. pose proof (af_sp0_win RT AF Σ2 m2 ART2) as SP0W.
  set (usp := bv_unsigned sp) in *. set (len := Z.of_nat (length bs)) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (LEN0 : 0 <= len) by (subst len; lia).
  pose proof FOBJ2 as (P8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
  pose proof (fframe_ranges RT AF Σ2 m2 f k ART2 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ2 m2 f k ART2 INF) as (_ & FSEG).
  assert (INM : In (impl, 96) (rt_live RT Σ2)) by (rewrite LV2; cbn [In]; tauto).
  pose proof (af_live_range RT AF Σ2 m2 impl 96 ART2 INM) as (IM0 & IM1 & _).
  assert (SUBL : forall e, In e L -> In e (rt_live RT Σ2)) by (intros e He; rewrite LV2; do 6 right; exact He).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -112) mod 16 = 0) by (replace (usp + -112) with (usp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  assert (MCN : 0 <= mcost (len + 64) /\ 0 <= S2A_COST len).
  { split; [apply mcost_nonneg; lia|]. unfold S2A_COST, Sj_num_iface.NUMA_CREDIT. pose proof (mcost_nonneg (len + 64) ltac:(lia)). lia. }
  assert (FPS : fp_client RT Σ2 lo [(usp - 112, usp - 104)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).

  assert (DR : d + len <= lo /\ d <= 2^47).
  { destruct INLV as [(p & n & Hin & P1 & P2)| (E & DS)].
    - pose proof (af_live_range RT AF Σ2 m2 p n ART2 (SUBL _ Hin)) as (R0 & R1 & _). ul.
    - subst len. rewrite E. cbn [length]. ul. }

  pose proof (pi_walk4 usp RES P d len cap z8 z8 z8 p1 p17 p57 j (Z_to_bv 64 impl) (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                (Z_to_bv 64 4294967295) (Z_to_bv 64 0) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F' fc' m2 ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul)
                (fobj_shz RT AF Σ2 m2 P 80 ART2 FOBJ2) PC2 FR2 MI2) as W4.
  lazymatch type of W4 with evt bsegs _ ?X =>
    assert (W4' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W4) end.
  clear W4.
  apply (cps_realizes bsegs _ _ _ c (asta_evt_c RT AF Σ2 PMc _ _ MST W4') Hc). clear W4'. intros c3 Hc3.
  destruct (ASTA_unpack RT Σ2 _ _ c3 Hc3) as (ms3 & (m3 & -> & MU3 & WM3 & MI3 & PC3 & FR3) & Hc3'). clear Hc3.
  pose proof (art_fp_client RT AF Σ2 m2 m3 lo _ ART2 LOW FPS MU3 WM3) as ART3.
  pose proof (fobj_munch RT AF Σ2 m2 m3 lo _ P 80 ART2 LOW FPS MU3 FOBJ2) as FOBJ3.
  assert (AG3 : agree_on (fun x => ~ (usp - 112 <= x < usp - 104)) m2 m3).
  { apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
  pose proof (stk_wmono m2 m3 _ _ ST2 WM3 ltac:(ul)) as ST3.

  pose proof (pi_walk5a RES P d len (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m3
                ltac:(lia) (AFC Σ2 m3 ART3)) as W5.
  lazymatch type of W5 with evt bsegs _ ?X =>
    assert (W5' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W5) end.
  clear W5.
  apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ2 PMc _ _ MST W5') Hc3'). clear W5'. intros c4 Hc4.

  apply (NEWA Σ2 PMc (Z_to_bv 64 0xb7754) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
           (Z_to_bv 64 (len + 64)) (Z_to_bv 64 0x31890) a2 a3 a4 a5 a6 a7
           (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
           (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F' fc' m3 (len + 64) lo FDO MST);
    try reflexivity; try assumption;
    [.. | split; [exact Hc4| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c4 Hc4); intros ms0 <-; exact FRM] |].
  - lia.
  - lia.
  - lia.
  - rewrite EU2. exact ST3.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact SPA2.
  - intros c5 ((Σ3 & copy & Hc5 & LV3 & FRS3 & SP3 & CR3 & CP0 & CP16 & CPTOP) & FC5).
    destruct (ASTA_unpack_f RT Σ3 _ _ c5 Hc5 FC5) as (ms5 & (m4 & RS5 & (ART4 & MI4 & WM4 & ST4) & PRES4 & _ & _) & FRM4 & Hc5'). clear Hc5.
    destruct RS5 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F4 & fc4 & ->).
    cbn [ms_fcsr] in FRM4. rewrite EU2 in ST4, PRES4. rewrite (ret_pc_even 0xb7754) in Hc5' by (clear; lia).
    assert (LV3' : rt_live RT Σ3 = [(copy, len + 64)] ++ rt_live RT Σ2) by exact LV3.
    assert (INC : In (copy, len + 64) (rt_live RT Σ3)) by (rewrite LV3; left; reflexivity).
    assert (SUB23 : forall e, In e (rt_live RT Σ2) -> In e (rt_live RT Σ3)) by (intros e He; rewrite LV3; right; exact He).
    assert (LOW3 : rt_sp0 RT Σ3 - STACK_WIN <= lo) by (rewrite SP3; exact LOW).
    assert (INF3 : In (f, k) (rt_frames RT Σ3)) by (rewrite FRS3; exact INF).
    pose proof (af_live_range RT AF Σ3 m4 copy _ ART4 INC) as (_ & CP1 & _). rewrite SP3 in CP1.

    set (REG := fun x => (usp - 112 <= x < USTACK_TOP) \/ (P <= x < P + 80) \/ (impl <= x < impl + 96) \/ in_ranges LIB_FP x
                          \/ (shad P <= x < shad P + (80 + 7) / 8) \/ (d <= x < d + len)).
    assert (CL2 : forall x, REG x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -112) x).
    { intros x [H|[H|[H|[H|[H|H]]]]].
      - left. lia.
      - right; right; right; left. exists f, k. split; [exact INF| lia].
      - right; right; left. exists impl, 96. split; [exact INM| lia].
      - right; left. exact (proj1 (lib_fp_static _ H)).
      - exact (proj1 (fobj_shadow_client RT AF Σ2 m2 P 80 (usp + -112) x ART2 FOBJ2 H)).
      - destruct INLV as [(p & n & Hin & P1 & P2)| (E & _)]; [| subst len; rewrite E in H; cbn [length] in H; lia].
        right; right; left. exists p, n. split; [exact (SUBL _ Hin)| lia]. }
    assert (CL3 : forall x, REG x -> aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -112) x /\ ~ (copy <= x < copy + (len + 64))).
    { intros x Hx. pose proof (CL2 x Hx) as C2. split.
      - apply (aclient_mono _ _ _ _ _ _ _ C2); [exact SUB23| rewrite FRS3; auto| lia].
      - exact (fresh_apart RT AF Σ2 Σ3 m4 [(copy, len + 64)] copy (len + 64) (usp + -112) x ART4 LV3' ltac:(left; reflexivity) FRS3 SP3 ltac:(ul) C2). }
    assert (AG34 : agree_on REG m3 m4) by (intros a Ha; exact (PRES4 a (CL2 _ Ha))).

    assert (KF : forall (mA mB : mem) frc, agree_on REG mA mB -> rw_cells bsegs mA (usp + -112) frc -> cells_size frc = 112%nat -> rw_cells bsegs mB (usp + -112) frc).
    { intros mA mB frc AG H SZ. apply (rw_cells_agree_nw bsegs mA mB _ _ H). eapply agree_sub; [exact AG|]. intros x Hx. rewrite SZ in Hx. left. ul. }
    assert (KP : forall (mA mB : mem) pc, agree_on REG mA mB -> rw_cells bsegs mA P pc -> cells_size pc = 80%nat -> rw_cells bsegs mB P pc).
    { intros mA mB pc AG H SZ. apply (rw_cells_agree_nw bsegs mA mB _ _ H). eapply agree_sub; [exact AG|]. intros x Hx. rewrite SZ in Hx. right; left. lia. }
    assert (KI : forall (mA mB : mem) ic, agree_on REG mA mB -> rw_cells bsegs mA impl ic -> cells_size ic = 96%nat -> rw_cells bsegs mB impl ic).
    { intros mA mB ic AG H SZ. apply (rw_cells_agree_nw bsegs mA mB _ _ H). eapply agree_sub; [exact AG|]. intros x Hx. rewrite SZ in Hx. right; right; left. lia. }
    assert (KR : forall (mA mB : mem) rc, agree_on REG mA mB -> rw_cells bsegs mA RES rc -> cells_size rc = 24%nat -> rw_cells bsegs mB RES rc).
    { intros mA mB rc AG H SZ. apply (rw_cells_agree_nw bsegs mA mB _ _ H). eapply agree_sub; [exact AG|]. intros x Hx. rewrite SZ in Hx. left. ul. }
    assert (KL : forall (mA mB : mem), agree_on REG mA mB -> lib1 mA -> lib1 mB).
    { intros mA mB AG H. apply (lib1_loc mA mB H). intros a Ha. apply AG. right; right; right; left. exact Ha. }
    assert (KB : forall (mA mB : mem), agree_on REG mA mB -> bytes_at bsegs mA d bs -> bytes_at bsegs mB d bs).
    { intros mA mB AG H. apply (bytes_at_agree bsegs mA mB _ _ H). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx. do 5 right. exact Hx. }
    assert (KO : forall (Σa Σb : rts RT) (mA mB : mem), agree_on REG mA mB -> ART RT Σa mA -> fobj RT Σa mA P 80 -> rt_frames RT Σb = rt_frames RT Σa -> fobj RT Σb mB P 80).
    { intros Σa Σb mA mB AG HA FO FRS. apply (fobj_agree RT AF Σa Σb mA mB P 80 HA FO FRS). eapply agree_sub; [exact AG|]. intros x Hx. cbv beta in Hx. do 4 right. left. exact Hx. }

    pose proof (KF m3 m4 _ AG34 FR3 eq_refl) as FR4. pose proof (KP m3 m4 _ AG34 PC3 eq_refl) as PC4.
    assert (IC3 := IC2). apply (rw_cells_agree_nw bsegs m2 m3 _ _) in IC3; [| eapply agree_sub; [exact AG3|]; intros x Hx; unfold impl16 in Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; ul].
    assert (RC3 := RC2). apply (rw_cells_agree_nw bsegs m2 m3 _ _) in RC3; [| eapply agree_sub; [exact AG3|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; ul].
    assert (LIB3 : lib1 m3).
    { apply (lib1_loc m2 m3 LIB2). intros a Ha. apply AG3. destruct (lib_fp_static _ Ha) as (_ & R). clear - R LOW LOR SP0R SP0W. ul. }
    assert (BS3 : bytes_at bsegs m3 d bs).
    { apply (bytes_at_agree bsegs m2 m3 _ _ BS2). eapply agree_sub; [exact AG3|]. intros x Hx. cbv beta in *. fold len in Hx. clear - Hx DR LOR. ul. }
    pose proof (KI m3 m4 _ AG34 IC3 eq_refl) as IC4. pose proof (KR m3 m4 _ AG34 RC3 eq_refl) as RC4.
    pose proof (KL m3 m4 AG34 LIB3) as LIB4. pose proof (KB m3 m4 AG34 BS3) as BS4.
    pose proof (KO Σ2 Σ3 m3 m4 AG34 ART3 FOBJ3 FRS3) as FOBJ4.

    pose proof (pi_walk6 RES P d len copy (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F4 fc4 m4
                  CP0 ltac:(ul) LEN0) as W6.
    lazymatch type of W6 with evt bsegs _ ?X =>
      assert (W6' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W6) end.
    clear W6.
    apply (cps_realizes bsegs _ _ _ c5 (asta_evt_c RT AF Σ3 PMc _ _ MST W6') Hc5'). clear W6'. intros c6 Hc6.
    destruct (af_acc_live RT AF Σ3 m4 copy _ ART4 INC) as (WRC4 & ACC4).

    apply (MSET Σ3 PMc (Z_to_bv 64 0xb7774) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) u0 u1 u2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
             (Z_to_bv 64 (copy + len)) (Z_to_bv 64 0) (Z_to_bv 64 64) b3 b4 b5 b6 b7
             (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 copy)
             (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) u3 u4 u5 u6 F4 fc4 m4 (copy + len) 64 (Z_to_bv 8 0) lo FDO MST);
      try reflexivity; try assumption;
      [.. | split; [exact Hc6| apply (cfrm0_of_asta RT Σ3 PMc (eq _) c6 Hc6); intros ms0 <-; exact FRM4] |].
    + ul.
    + lia.
    + unfold checked_dst. split; [| split].
      * intros _. split; [exact (acc_sub bsegs m4 copy (len + 64) (copy + len) 64 ACC4 ltac:(lia) ltac:(lia))|]. left. exists copy, (len + 64). split; [exact INC| lia].
      * intros i Hi. right; right; left. exists copy, (len + 64). split; [exact INC| lia].
      * exact (wr_at_sub m4 copy (len + 64) (copy + len) 64 WRC4 ltac:(lia) ltac:(lia) ltac:(lia)).
    + unfold call_ok. rewrite EU2. split; [exact ST4|]. split; [exact LOW3|]. split; [ul|]. split; [ul| exact SPA2].
    + intros c7 (Hc7 & FC7). unfold icpt_post in Hc7.
      destruct (ASTA_unpack_f RT Σ3 _ _ c7 Hc7 FC7) as (ms7 & (m5 & RS7 & (ART5 & MI5 & WM5 & ST5) & PRES5 & PAD5) & FRM5 & Hc7'). clear Hc7.
      destruct RS7 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F5 & fc5 & ->).
      cbn [ms_fcsr] in FRM5. rewrite EU2 in ST5, PRES5. rewrite (ret_pc_even 0xb7774) in Hc7' by (clear; lia).
      assert (AG45 : agree_on REG m4 m5) by (intros a Ha; destruct (CL3 _ Ha) as (C3 & NC); apply (PRES5 a C3); clear - NC LEN0; lia).
      pose proof (KF m4 m5 _ AG45 FR4 eq_refl) as FR5. pose proof (KP m4 m5 _ AG45 PC4 eq_refl) as PC5.
      pose proof (KI m4 m5 _ AG45 IC4 eq_refl) as IC5. pose proof (KR m4 m5 _ AG45 RC4 eq_refl) as RC5.
      pose proof (KL m4 m5 AG45 LIB4) as LIB5. pose proof (KB m4 m5 AG45 BS4) as BS5.
      pose proof (KO Σ3 Σ3 m4 m5 AG45 ART4 FOBJ4 eq_refl) as FOBJ5.

      assert (FPP : fp_client RT Σ3 lo [(P, P + 80)]).
      { constructor; [| constructor]. right; right. exists f, k. cbn [fst snd]. split; [exact INF3| lia]. }
      assert (SHZ5 : forall m' : mem, munch [(P, P + 80)] m5 m' -> wmono bsegs m5 m' -> shz m' P 80).
      { intros m' MU WM. apply (fobj_shz RT AF Σ3 m'); [exact (art_fp_client RT AF Σ3 m5 m' lo _ ART5 LOW3 FPP MU WM)|].
        exact (fobj_munch RT AF Σ3 m5 m' lo _ P 80 ART5 LOW3 FPP MU FOBJ5). }
      pose proof (pi_walk7 usp RES P d len copy z8 z8 z8 p1 p17 p57 (Z_to_bv 64 impl) (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                    (Z_to_bv 64 4294967295) (Z_to_bv 64 0) gp (Z_to_bv 64 0x6be3e8) w0 w1 w2 (Z_to_bv 64 (copy + len)) g1 g2 g3 g4 g5 g6 g7 w3 w4 w5 w6
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F5 fc5 m5 ltac:(ul) ltac:(lia) ltac:(ul) ltac:(ul) ltac:(ul) SHZ5 PC5 FR5 MI5) as W7.
      lazymatch type of W7 with evt bsegs _ ?X =>
        assert (W7' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W7) end.
      clear W7.
      apply (cps_realizes bsegs _ _ _ c7 (asta_evt_c RT AF Σ3 PMc _ _ MST W7') Hc7'). clear W7'. intros c8 Hc8.
      destruct (ASTA_unpack RT Σ3 _ _ c8 Hc8) as (ms8 & (m6 & -> & MU6 & WM6 & MI6 & PC6 & FR6) & Hc8'). clear Hc8.
      pose proof (art_fp_client RT AF Σ3 m5 m6 lo _ ART5 LOW3 FPP MU6 WM6) as ART6.
      pose proof (fobj_munch RT AF Σ3 m5 m6 lo _ P 80 ART5 LOW3 FPP MU6 FOBJ5) as FOBJ6.
      assert (AG56 : agree_on (fun x => ~ (P <= x < P + 80)) m5 m6).
      { apply (agree_of_munch _ _ _ _ MU6). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
      pose proof (stk_wmono m5 m6 _ _ ST5 WM6 ltac:(ul)) as ST6.
      pose proof (af_frames_range RT AF Σ3 m5 f k ART5 INF3) as (_ & _ & _ & FLV3).
      assert (IC6 := IC5). apply (rw_cells_agree_nw bsegs m5 m6 _ _) in IC6;
        [| eapply agree_sub; [exact AG56|]; intros x Hx; unfold impl16 in Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta;
           pose proof (FLV3 impl 96 (SUB23 _ INM)) as X; clear - Hx X FLO FHI; lia].
      assert (RC6 := RC5). apply (rw_cells_agree_nw bsegs m5 m6 _ _) in RC6; [| eapply agree_sub; [exact AG56|]; intros x Hx; cbn [cells_size csize Nat.add] in Hx; cbv beta; ul].
      assert (LIB6 : lib1 m6).
      { apply (lib1_loc m5 m6 LIB5). intros a Ha. apply AG56. destruct (lib_fp_static _ Ha) as (_ & R). clear - R FSEG FLO. unfold SEGTOP_A in *. lia. }
      assert (BS6 : bytes_at bsegs m6 d bs).
      { apply (bytes_at_agree bsegs m5 m6 _ _ BS5). eapply agree_sub; [exact AG56|]. intros x Hx. cbv beta in *. fold len in Hx.
        destruct (CL2 x ltac:(do 5 right; exact Hx)) as [H|[H|[H|[H|H]]]].
        - clear - H Hx DR LOR. ul.
        - pose proof (client_static_range x H). clear - H0 FSEG FLO. unfold SEGTOP_A in *. lia.
        - exact (fun Hp => not_live_frame RT AF Σ2 m2 f k x ART2 INF ltac:(lia) H).
        - destruct INLV as [(p & n & Hin & P1 & P2)| (E & _)]; [| subst len; rewrite E in Hx; cbn [length] in Hx; lia].
          pose proof (FLV3 p n (SUB23 _ (SUBL _ Hin))) as X. clear - Hx X P1 P2 FLO FHI. lia.
        - destruct INLV as [(p & n & Hin & P1 & P2)| (E & _)]; [| subst len; rewrite E in Hx; cbn [length] in Hx; lia].
          pose proof (FLV3 p n (SUB23 _ (SUBL _ Hin))) as X. clear - Hx X P1 P2 FLO FHI. lia. }
      assert (PAD6 : bytes_at bsegs m6 (copy + len) (repeat z8 64)).
      { apply (bytes_at_agree bsegs m5 m6 _ _ PAD5). eapply agree_sub; [exact AG56|]. intros x Hx. cbv beta in *. rewrite repeat_length in Hx.
        pose proof (FLV3 copy _ INC) as X. clear - Hx X FLO FHI LEN0. lia. }
      destruct (af_acc_live RT AF Σ3 m6 copy _ ART6 INC) as (WRC6 & ACC6).

      apply (MCP Σ3 PMc (Z_to_bv 64 0xb7828) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) w0 w1 w2 (Z_to_bv 64 RES) (Z_to_bv 64 ((P + 64) / 8 + 2147450880))
               (Z_to_bv 64 copy) (Z_to_bv 64 d) (Z_to_bv 64 len) g3 g4 g5 g6 g7
               (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) w3 w4 w5 w6 F5 fc5 m6 copy d bs lo FDO MST);
        try reflexivity; try assumption;
        [.. | split; [exact Hc8'| apply (cfrm0_of_asta RT Σ3 PMc (eq _) c8 Hc8'); intros ms0 <-; exact FRM5] |].
      * ul.
      * lia.
      * fold len. change (2^40) with 1099511627776. lia.
      * fold len. unfold checked_src. rewrite EU2. split; [| left; lia].
        intros LP. destruct INLV as [(p & n & Hin & P1 & P2)| (E & _)]; [| subst len; rewrite E in LP; cbn [length] in LP; lia].
        destruct (af_acc_live RT AF Σ3 m6 p n ART6 (SUB23 _ (SUBL _ Hin))) as (_ & ACP).
        split; [exact (acc_sub bsegs m6 p n d len ACP ltac:(lia) ltac:(lia))|]. left. exists p, n. split; [exact (SUB23 _ (SUBL _ Hin))| lia].
      * fold len. unfold checked_dst. split; [| split].
        -- intros _. split; [exact (acc_sub bsegs m6 copy (len + 64) copy len ACC6 ltac:(lia) ltac:(lia))|]. left. exists copy, (len + 64). split; [exact INC| lia].
        -- intros i Hi. right; right; left. exists copy, (len + 64). split; [exact INC| lia].
        -- exact (wr_at_sub m6 copy (len + 64) copy len WRC6 ltac:(lia) ltac:(lia) ltac:(lia)).
      * fold len. destruct INLV as [(p & n & Hin & P1 & P2)| (E & _)]; [| subst len; rewrite E; cbn [length]; lia].
        pose proof (af_live_disj RT AF Σ3 m6 copy (len + 64) p n [] (rt_live RT Σ2) ART6 LV3 (SUBL _ Hin)) as X. clear - X P1 P2 LEN0. lia.
      * unfold call_ok. rewrite EU2. split; [exact ST6|]. split; [exact LOW3|]. split; [ul|]. split; [ul| exact SPA2].
      * intros c9 (Hc9 & FC9). unfold icpt_post in Hc9.
        destruct (ASTA_unpack_f RT Σ3 _ _ c9 Hc9 FC9) as (ms9 & (m7 & RS9 & (ART7 & MI7 & WM7 & ST7) & PRES7 & CPB7) & FRM7 & Hc9'). clear Hc9.
        destruct RS9 as (x0 & x1 & x2 & h1 & h2 & h3 & h4 & h5 & h6 & h7 & x3 & x4 & x5 & x6 & F7 & fc7 & ->).
        cbn [ms_fcsr] in FRM7. rewrite EU2 in ST7, PRES7. fold len in PRES7. rewrite (ret_pc_even 0xb7828) in Hc9' by (clear; lia).
        assert (AG67 : agree_on REG m6 m7) by (intros a Ha; destruct (CL3 _ Ha) as (C3 & NC); apply (PRES7 a C3); clear - NC LEN0; lia).
        pose proof (KF m6 m7 _ AG67 FR6 eq_refl) as FR7. pose proof (KP m6 m7 _ AG67 PC6 eq_refl) as PC7.
        pose proof (KI m6 m7 _ AG67 IC6 eq_refl) as IC7. pose proof (KR m6 m7 _ AG67 RC6 eq_refl) as RC7.
        pose proof (KL m6 m7 AG67 LIB6) as LIB7.
        pose proof (KO Σ3 Σ3 m6 m7 AG67 ART6 FOBJ6 eq_refl) as FOBJ7.
        assert (PAD7 : bytes_at bsegs m7 (copy + len) (repeat z8 64)).
        { apply (bytes_at_agree bsegs m6 m7 _ _ PAD6). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES7). intros x Hx. cbv beta in Hx. rewrite repeat_length in Hx.
          split; [right; right; left; exists copy, (len + 64); split; [exact INC| lia]| lia]. }
        pose proof (padded_of_copy m7 copy bs CPB7 PAD7) as BUFB7.

        assert (CALLER : forall x, aclient L (rt_frames RT Σ2) usp x -> outside (pid_XA P RES) x ->
                  aclient (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -112) x /\ ~ (usp - 112 <= x < usp) /\ ~ (P <= x < P + 80)).
        { intros x Ha Hout. unfold pid_XA in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & _).
          assert (Ha2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp x) by (apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact SUBL| auto| lia]).
          pose proof (aclient_split_c RT AF Σ2 m2 usp x ART2 Ha2) as SPL.
          split; [apply (aclient_mono _ _ _ _ _ _ _ Ha2); [auto| auto| lia]|]. split; [clear - SPL LOW LOR; ul| exact HO1]. }
        assert (CH7 : forall a : word, aclient L (rt_frames RT Σ2) usp (bv_unsigned a) -> outside (pid_XA P RES) (bv_unsigned a) -> m7 a = m2 a).
        { intros a Ha Hout. destruct (CALLER _ Ha Hout) as (C2 & NFR & NP).
          assert (C3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -112) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ C2); [exact SUB23| rewrite FRS3; auto| lia]).
          pose proof (fresh_apart RT AF Σ2 Σ3 m4 [(copy, len + 64)] copy (len + 64) (usp + -112) (bv_unsigned a) ART4 LV3' ltac:(left; reflexivity) FRS3 SP3 ltac:(ul) C2) as NC.
          assert (N7 : ~ (copy <= bv_unsigned a < copy + len)) by (clear - NC LEN0; lia).
          assert (N5 : ~ (copy + len <= bv_unsigned a < copy + len + 64)) by (clear - NC LEN0; lia).
          assert (N3 : ~ (usp - 112 <= bv_unsigned a < usp - 104)) by (clear - NFR; lia).
          rewrite (PRES7 a C3 N7), (AG56 a NP), (PRES5 a C3 N5), (PRES4 a C2), (AG3 a N3). reflexivity. }

        assert (LV37 : rt_live RT Σ3 = (copy, len + 64) :: (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: L)
          by (rewrite LV3, LV2; reflexivity).
        assert (TAILK : forall (mX : mem) (cX : config) (rax t0x t1x t2x s1y a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x : word) FX fcX (BUF bl : Z) (bsz : list Z),
                  ART RT Σ3 mX -> mem_inv bsegs mX -> stk bsegs mX lo (usp + -112) -> agree_on REG m7 mX ->
                  (forall a : word, aclient L (rt_frames RT Σ2) usp (bv_unsigned a) -> outside (pid_XA P RES) (bv_unsigned a) -> mX a = m2 a) ->
                  bytes_at bsegs mX BUF (padded_bytes bsz) -> bytes_ok bsz -> blen bsz = bl -> bl <= len -> copy <= BUF -> BUF + bl = copy + len -> frm0 fcX ->
                  ASTA RT Σ3 PMc (eq (MS (PIREGF rax (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) t0x t1x t2x s1y RES P BUF bl a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x)
                                         FX (Z_to_bv 64 0xb785c) fcX None mX (seg_rom bsegs))) cX ->
                  realizes bsegs cX T).
        { intros mX cX rax t0x t1x t2x s1y a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x FX fcX BUF bl bsz ARTX MIX STX AGX CHX BUFBX BOKX EBL BLE CBUF EBUF FRMX HcX.
          subst bl.
          apply (pid_tail RT AF MSET PARSE AFV Σ3 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rax t0x t1x t2x s1y a0x a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x
                   FX fcX mX lo RES P len cap impl idx oc ia tape sbuf copy BUF bsz L jr p1 p17 p57 p12 p28 p50 FDO MST BOKX BLE LEN ECAP CBUF EBUF ARTX MIX STX
                   (KF m7 mX _ AGX FR7 eq_refl) (KP m7 mX _ AGX PC7 eq_refl) (KO Σ3 Σ3 m7 mX AGX ART7 FOBJ7 eq_refl) (KI m7 mX _ AGX IC7 eq_refl)
                   (KR m7 mX _ AGX RC7 eq_refl) (KL m7 mX AGX LIB7) BUFBX LV37 LPOS IM16 IX16 OC16 IA16 TP16 SB16 CP16);
            [rewrite FRS3; exact FRB| | rewrite LV3; cbn [length]; lia| exact RLO| exact RHI| exact LOW3| exact LOR| exact SPT| exact SPA| exact FRMX
            | split; [exact HcX| apply (cfrm0_of_asta RT Σ3 PMc (eq _) cX HcX); intros ms0 <-; exact FRMX] |].
          - rewrite CR3. pose proof (s2a_cost_mono (blen bsz) len ltac:(unfold blen in *; lia)). lia.
          - intros c' ((Σ' & cp' & Hc' & LV' & -> & FRS' & SP' & CR') & FC'). apply Hk. split; [| exact FC'].
            exists Σ', [(copy, len + 64)]. split; [| split; [rewrite LV'; exact LV3| split; [exists copy; split; [reflexivity| exact CP0]| split; [rewrite FRS'; exact FRS3| split; [rewrite SP'; exact SP3|]]]]].
            + eapply ASTA_conseq; [exact Hc'|]. intros ms (v & m' & RS' & AFT' & PRES' & RC' & LIB' & PD' & FO' & PC'). exists v, m'.
              split; [exact RS'|]. split; [exact AFT'|]. split; [| split; [exact RC'| split; [exact LIB'| split; [exact PD'| split; [exact FO'| exact PC']]]]].
              intros a Ha Hout. rewrite (PRES' a); [exact (CHX a Ha Hout)| rewrite FRS3; exact Ha| exact Hout].
            + rewrite CR3 in CR'. pose proof (s2a_cost_mono (blen bsz) len ltac:(unfold blen in *; lia)). lia. }
        assert (AG77 : agree_on REG m7 m7) by (intros a _; reflexivity).
        destruct (Z_lt_dec len 3) as [L3|L3].
        --
           pose proof (pi_walk8b RES P d len copy z8 z8 z8 p1 p17 p57 (Z_to_bv 64 impl) (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                         (Z_to_bv 64 4294967295) (Z_to_bv 64 len) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) x0 x1 x2 (Z_to_bv 64 copy) h1 h2 h3 h4 h5 h6 h7
                         x3 x4 x5 x6 F7 fc7 m7 ltac:(lia) ltac:(ul) ltac:(ul) PC7) as W8.
           lazymatch type of W8 with evt bsegs _ ?X =>
             assert (W8' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W8) end.
           clear W8.
           apply (cps_realizes bsegs _ _ _ c9 (asta_evt_c RT AF Σ3 PMc _ _ MST W8') Hc9'). clear W8'. intros c10 Hc10.
           exact (TAILK m7 c10 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F7 fc7 copy len (map bv_unsigned bs) ART7 MI7 ST7 AG77 CH7 BUFB7 (bytes_ok_unsigned bs)
                    (blen_unsigned bs) ltac:(lia) ltac:(lia) ltac:(lia) FRM7 Hc10).
        --
           pose proof (pi_walk8a RES P d len copy z8 z8 z8 p1 p17 p57 (Z_to_bv 64 impl) (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                         (Z_to_bv 64 4294967295) (Z_to_bv 64 len) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) x0 x1 x2 (Z_to_bv 64 copy) h1 h2 h3 h4 h5 h6 h7
                         x3 x4 x5 x6 F7 fc7 m7 ltac:(lia) ltac:(ul) ltac:(ul) PC7) as W8.
           lazymatch type of W8 with evt bsegs _ ?X =>
             assert (W8' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W8) end.
           clear W8.
           apply (cps_realizes bsegs _ _ _ c9 (asta_evt_c RT AF Σ3 PMc _ _ MST W8') Hc9'). clear W8'. intros c10 Hc10.
           assert (L3' : (3 <= length bs)%nat) by (subst len; lia).
           assert (LF3 : length (firstn 3 bs) = 3%nat) by (apply firstn_length_le; exact L3').
           assert (CPF7 : bytes_at bsegs m7 copy (firstn 3 bs)).
           { pose proof CPB7 as X. rewrite <- (firstn_skipn 3 bs) in X. apply bytes_at_app in X. exact (proj1 X). }
           destruct (af_acc_live RT AF Σ3 m7 copy _ ART7 INC) as (_ & ACC7).
           apply (MCMP Σ3 PMc (Z_to_bv 64 0xb784c) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) x0 x1 x2 (Z_to_bv 64 RES) (Z_to_bv 64 3)
                    (Z_to_bv 64 copy) (Z_to_bv 64 0x23a60) (Z_to_bv 64 3) h3 h4 h5 h6 h7
                    (Z_to_bv 64 len) (Z_to_bv 64 copy) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24))
                    (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) x3 x4 x5 x6 F7 fc7 m7 copy BOM_LIT (firstn 3 bs) BOM_BYTES lo FDO MST);
             try reflexivity; try assumption;
             [.. | split; [exact Hc10| apply (cfrm0_of_asta RT Σ3 PMc (eq _) c10 Hc10); intros ms0 <-; exact FRM7] |].
           ++ rewrite LF3. reflexivity.
           ++ rewrite LF3. reflexivity.
           ++ ul.
           ++ unfold BOM_LIT. lia.
           ++ rewrite LF3. lia.
           ++ rewrite LF3. lia.
           ++ exact (bom_at m7 MI7).
           ++ rewrite LF3. change (Z.of_nat 3) with 3. unfold checked_src. rewrite EU2. split; [| left; ul].
              intros _. split; [exact (acc_sub bsegs m7 copy (len + 64) copy 3 ACC7 ltac:(lia) ltac:(lia))|]. left. exists copy, (len + 64). split; [exact INC| lia].
           ++ rewrite LF3. change (Z.of_nat 3) with 3. unfold checked_src. rewrite EU2. split; [| left; unfold BOM_LIT; ul].
              intros _. split.
              ** apply (acc_sub bsegs m7 BOM_LIT 4 BOM_LIT 3); [| lia| lia]. apply (acc_lit RT AF Σ3 m7 _ _ ART7). unfold ACC_LITS, BOM_LIT. repeat (first [left; reflexivity | right]).
              ** right; right; right. unfold BOM_LIT, SEGTOP_A. lia.
           ++ unfold call_ok. rewrite EU2. split; [exact ST7|]. split; [exact LOW3|]. split; [ul|]. split; [ul| exact SPA2].
           ++ intros c11 ((r & _ & Hc11) & FC11). unfold icpt_post in Hc11.
              destruct (ASTA_unpack_f RT Σ3 _ _ c11 Hc11 FC11) as (ms11 & (m8 & RS11 & (ART8 & MI8 & WM8 & ST8) & PRES8 & _) & FRM8 & Hc11'). clear Hc11.
              destruct RS11 as (y0 & y1 & y2 & k1 & k2 & k3 & k4 & k5 & k6 & k7 & y3 & y4 & y5 & y6 & F8 & fc8 & ->).
              cbn [ms_fcsr] in FRM8. rewrite EU2 in ST8, PRES8. rewrite (ret_pc_even 0xb784c) in Hc11' by (clear; lia).
              assert (AG78 : agree_on REG m7 m8) by (intros a Ha; destruct (CL3 _ Ha) as (C3 & _); apply (PRES8 a C3); clear; lia).
              assert (CH8 : forall a : word, aclient L (rt_frames RT Σ2) usp (bv_unsigned a) -> outside (pid_XA P RES) (bv_unsigned a) -> m8 a = m2 a).
              { intros a Ha Hout. destruct (CALLER _ Ha Hout) as (C2 & _ & _).
                rewrite (PRES8 a ltac:(apply (aclient_mono _ _ _ _ _ _ _ C2); [exact SUB23| rewrite FRS3; auto| clear; lia]) ltac:(clear; lia)). exact (CH7 a Ha Hout). }
              assert (BUFB8 : bytes_at bsegs m8 copy (padded_bytes (map bv_unsigned bs))).
              { apply (bytes_at_agree bsegs m7 m8 _ _ BUFB7). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES8). intros x Hx. cbv beta in Hx.
                rewrite padded_bytes_blen, blen_unsigned in Hx. fold len in Hx. split; [right; right; left; exists copy, (len + 64); split; [exact INC| lia]| lia]. }
              pose proof (pi_walk8c RES P len copy r (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) y0 y1 y2 k1 k2 k3 k4 k5 k6 k7 y3 y4 y5 y6 F8 fc8 m8
                            ltac:(lia) CP0 ltac:(ul)) as W9.
              lazymatch type of W9 with evt bsegs _ ?X =>
                assert (W9' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W9) end.
              clear W9.
              apply (cps_realizes bsegs _ _ _ c11 (asta_evt_c RT AF Σ3 PMc _ _ MST W9') Hc11'). clear W9'. intros c12 Hc12.
              destruct (ASTA_unpack RT Σ3 _ _ c12 Hc12) as (ms12 & (BUF & bl & CASE & ->) & Hc12'). clear Hc12.
              destruct CASE as [(-> & ->)|(-> & ->)].
              ** exact (TAILK m8 c12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 copy len (map bv_unsigned bs) ART8 MI8 ST8 AG78 CH8 BUFB8 (bytes_ok_unsigned bs)
                          (blen_unsigned bs) ltac:(lia) ltac:(lia) ltac:(lia) FRM8 Hc12').
              ** assert (EBL : blen (map bv_unsigned (skipn 3 bs)) = len - 3) by (rewrite blen_unsigned, skipn_length; subst len; lia).
                 exact (TAILK m8 c12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F8 fc8 (copy + 3) (len - 3) (map bv_unsigned (skipn 3 bs)) ART8 MI8 ST8 AG78 CH8
                          (padded_skip3 m8 copy bs L3' BUFB8) (bytes_ok_unsigned _) EBL ltac:(lia) ltac:(lia) ltac:(lia) FRM8 Hc12').
Qed.

End Pid4.
