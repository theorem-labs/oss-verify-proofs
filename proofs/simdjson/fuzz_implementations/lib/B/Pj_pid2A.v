(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Spec Require Import SjModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Sj Require Import SjS1Out SjTape.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep FP.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc Atp_setcapA Sj_h_setmd Atp_fzwA Sj_h_deldtor Atp_pdtorA Sj_h_layout Atp_hkit3A Atp_createA Atp_activewA Atp_activeA Pj_pdtor2A Pj_pidwA Pj_pidw2A Pj_pidw3A Atp_hkit4A Atp_hkit5A Pj_pid1A Atp_pidiA Sj_stage2_iface Pj_defsA Pj_hdefsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma pd_of_pid : forall (m : mem) P b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 lb lbcap,
  rw_cells bsegs m P (pid_cells b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 lb lbcap) ->
  exists pre8 mid mid2 rest, rw_cells bsegs m P (pd_cells pre8 impl mid tape sbuf dcap mid2 lb rest).
Proof.
  intros until lbcap. intros H. pose proof H as ((W & _) & _). unfold pid_cells in W. cbn [cells_wf cell_wf] in W.
  destruct W as (_ & L1 & _ & _ & L17 & _ & _ & _ & _ & _ & _ & L57 & _).
  exists ([b0] ++ p1), ([b16] ++ p17 ++ le4 err), (le8 maxcap ++ [nas] ++ p57), (le8 lbcap).
  apply (rw_cells_relayout m P _ _ H).
  - unfold pd_cells. cbn [cells_wf cell_wf]. rewrite !length_app, !length_le8, !length_le4, L1, L17, L57. cbn [length]. repeat split; reflexivity.
  - unfold pd_cells, pid_cells. cbn [cells_bytes cbytes]. rewrite <- ?app_assoc. reflexivity.
  - reflexivity.
Qed.

Section Pid2.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.

Local Ltac ul := unfold PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Definition pid_post (Σ2 : rts RT) (PMc : Model -> Prop) (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (lo RES P : Z) (L : list (Z * Z))
    (impl idx oc ia tape sbuf cap len : Z) (CP : list (Z * Z) -> Prop) (cost : Z) (m2 : mem) : config -> Prop :=
  fun c => exists (Σ' : rts RT) (cp : list (Z * Z)),
    ASTA RT Σ' PMc (fun ms => exists v m', ret_st ra sp gp (Z_to_bv 64 0x6be3e8) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
      /\ rt_after_f RT Σ' (bv_unsigned sp) lo m2 m'
      /\ rt_pres_fp L (rt_frames RT Σ2) (bv_unsigned sp) (pid_XA P RES) m2 m'
      /\ (exists (r : word) j20, rw_cells bsegs m' RES (res_cellsA (P + 24) r j20) /\ bv_unsigned r < 64
                                /\ s2a_okres tape sbuf (roundup64 (cap + 3)) (al_sbuf cap) r m' /\ (r = Z_to_bv 64 0 -> len <= 1048512))
      /\ sj_lib m' /\ pdone2 RT Σ' m' P L /\ fobj RT Σ' m' P 80
      /\ (exists p1 p17 p57 (lb lbc : word), rw_cells bsegs m' P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf)
                                                         (Z_to_bv 64 cap) (Z_to_bv 64 4294967295) z8 p57 lb lbc))) c
    /\ rt_live RT Σ' = cp ++ rt_live RT Σ2 /\ CP cp
    /\ rt_frames RT Σ' = rt_frames RT Σ2 /\ rt_sp0 RT Σ' = rt_sp0 RT Σ2 /\ rt_credit RT Σ2 - cost <= rt_credit RT Σ'.

Theorem pid_big : forall (Σ2 : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (m2 : mem) (lo RES P d len cap impl idx oc ia tape sbuf : Z)
    (L : list (Z * Z)) (jr j p1 p17 p57 p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc -> 1048512 < len < 2^26 ->
  ART RT Σ2 m2 -> mem_inv bsegs m2 -> stk bsegs m2 lo (bv_unsigned sp + -112) ->
  rw_cells bsegs m2 (bv_unsigned sp + -112) (pid_frame (CB 8 j) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells bsegs m2 P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                 (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  fobj RT Σ2 m2 P 80 ->
  rw_cells bsegs m2 impl (impl16 (Z_to_bv 64 0x17a150) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                 (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  rw_cells bsegs m2 RES [CB 24 jr] -> lib1 m2 ->
  rt_live RT Σ2 = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: L ->
  (forall p n, In (p, n) L -> 0 < n) -> 32 <= cap <= 2^26 -> impl mod 16 = 0 ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP ->
  rt_sp0 RT Σ2 - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc' ->
  cps_f (ASTA RT Σ2 PMc (eq (MS (mkR (Z_to_bv 64 0xb7aa0) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 RES) s1
                                     (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                     (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 1) (Z_to_bv 64 0) (Z_to_bv 64 cap)
                                     (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6)
                                F' (Z_to_bv 64 0xb7aa0) fc' None m2 (seg_rom bsegs))))
        (pid_post Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo RES P L impl idx oc ia tape sbuf cap len (fun cp => cp = []) 0 m2).
Proof using AF MSET.
  intros Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m2
    lo RES P d len cap impl idx oc ia tape sbuf L jr j p1 p17 p57 p12 p28 p50
    FDO MST LEN ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LPOS CAP IM16 RLO RHI LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ2 m2 ART2) as SP0R. pose proof (af_sp0_win RT AF Σ2 m2 ART2) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  pose proof (al_sbuf_bounds cap CAP) as SBB. pose proof (al_tape_bounds cap CAP) as TPB. pose proof (sc_idx_bounds cap ltac:(lia)) as IXB.
  pose proof FOBJ2 as (P8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
  pose proof (fframe_ranges RT AF Σ2 m2 f k ART2 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ2 m2 f k ART2 INF) as (_ & FSEG).
  assert (INM : In (impl, 96) (rt_live RT Σ2)) by (rewrite LV2; cbn [In]; tauto).
  pose proof (af_live_range RT AF Σ2 m2 impl 96 ART2 INM) as (IM0 & IM1 & _).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -112) mod 16 = 0) by (replace (usp + -112) with (usp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  assert (FPS : fp_client RT Σ2 lo [(usp - 112, usp - 104)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
  assert (FPP : fp_client RT Σ2 lo [(P, P + 80)]).
  { constructor; [| constructor]. right; right. exists f, k. cbn [fst snd]. split; [exact INF| lia]. }
  assert (FPR : fp_client RT Σ2 lo [(usp - 112, usp); (RES, RES + 24)]).
  { constructor; [left; cbn [fst snd]; ul|]. constructor; [left; cbn [fst snd]; ul| constructor]. }

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

  assert (SHZ3 : forall m' : mem, munch [(P, P + 80)] m3 m' -> wmono bsegs m3 m' -> shz m' P 80).
  { intros m' MU WM. apply (fobj_shz RT AF Σ2 m'); [exact (art_fp_client RT AF Σ2 m3 m' lo _ ART3 LOW FPP MU WM)|].
    exact (fobj_munch RT AF Σ2 m3 m' lo _ P 80 ART3 LOW FPP MU FOBJ3). }
  pose proof (pi_walk5b RES P d len z8 z8 z8 p1 p17 p57 (Z_to_bv 64 impl) (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                (Z_to_bv 64 4294967295) (Z_to_bv 64 0) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 64) a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m3
                ltac:(change (2^26) with 67108864 in LEN; lia) ltac:(ul) ltac:(ul) ltac:(ul) ltac:(ul) SHZ3 PC3 MI3) as W5.
  lazymatch type of W5 with evt bsegs _ ?X =>
    assert (W5' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W5) end.
  clear W5.
  apply (cps_realizes bsegs _ _ _ c3 (asta_evt_c RT AF Σ2 PMc _ _ MST W5') Hc3'). clear W5'. intros c4 Hc4.
  destruct (ASTA_unpack RT Σ2 _ _ c4 Hc4) as (ms4 & (m4 & -> & MU4 & WM4 & MI4 & PC4) & Hc4'). clear Hc4.
  pose proof (art_fp_client RT AF Σ2 m3 m4 lo _ ART3 LOW FPP MU4 WM4) as ART4.
  pose proof (fobj_munch RT AF Σ2 m3 m4 lo _ P 80 ART3 LOW FPP MU4 FOBJ3) as FOBJ4.
  assert (AG4 : agree_on (fun x => ~ (P <= x < P + 80)) m3 m4).
  { apply (agree_of_munch _ _ _ _ MU4). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
  pose proof (stk_wmono m3 m4 _ _ ST3 WM4 ltac:(ul)) as ST4.
  assert (AG24 : agree_on (fun x => ~ (usp - 112 <= x < usp - 104) /\ ~ (P <= x < P + 80)) m2 m4).
  { intros a (H1 & H2). rewrite (AG4 a H2), (AG3 a H1). reflexivity. }
  assert (RC4 : rw_cells bsegs m4 RES [CB 24 jr]).
  { apply (rw_cells_agree_nw bsegs m2 m4 _ _ RC2). eapply agree_sub; [exact AG24|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. split; ul. }
  assert (FR4 : rw_cells bsegs m4 (usp + -112) (pid_frame (C8 (Z_to_bv 64 (P + 24))) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (rw_cells_agree_nw bsegs m3 m4 _ _ FR3). eapply agree_sub; [exact AG4|]. intros x Hx. unfold pid_frame in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }

  apply (rw_cells_split_CB bsegs _ _ [] 24 _ [] [16; 4; 4]%nat) in RC4; [| reflexivity]. cbn [mk_CB_cells app] in RC4.
  repeat match type of RC4 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jj" in set (j := t) in RC4; clearbody j end.
  apply (MSET Σ2 PMc (Z_to_bv 64 0xb7a1c) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6be3e8) t0 t1 t2 (Z_to_bv 64 RES) (Z_to_bv 64 (RES + 16))
           (Z_to_bv 64 RES) (Z_to_bv 64 0) (Z_to_bv 64 16) a3 a4 a5 a6 a7
           (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 0)
           (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F' fc' m4 RES 16 (Z_to_bv 8 0) lo FDO MST);
    try reflexivity; try assumption;
    [.. | split; [exact Hc4'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c4 Hc4'); intros ms0 <-; exact FRM] |].
  - ul.
  - lia.
  - unfold checked_dst. rewrite EU2. split; [| split].
    + intros _. split; [apply (af_acc_stack RT AF Σ2 m4 _ _ ART4); ul|]. right; right; left. ul.
    + intros i Hi. left. ul.
    + exact (rw_cells_wr_at bsegs m4 _ _ 16 RC4 ltac:(cbn; lia)).
  - unfold call_ok. rewrite EU2. split; [exact ST4|]. split; [exact LOW|]. split; [ul|]. split; [ul| exact SPA2].
  - intros c5 (Hc5 & FC5). unfold icpt_post in Hc5.
    destruct (ASTA_unpack_f RT Σ2 _ _ c5 Hc5 FC5) as (ms5 & (m5 & RS5 & (ART5 & MI5 & WM5 & ST5) & PRES5 & BS5) & FRM5 & Hc5'). clear Hc5.
    destruct RS5 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F5 & fc5 & ->).
    cbn [ms_fcsr] in FRM5. rewrite EU2 in ST5, PRES5. rewrite (ret_pc_even 0xb7a1c) in Hc5' by (clear; lia).
    assert (RC5 : rw_cells bsegs m5 RES [CB 16 (repeat z8 16); CB 4 jj0; CB 4 jj1]).
    { apply (cells_mid_update m4 m5 RES [] 16 jj (repeat z8 16) [CB 4 jj0; CB 4 jj1] RC4);
        [| exact WM5| cbn [cells_size]; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; exact BS5| reflexivity].
      apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES5). intros x Hx. cbn [cells_size csize Nat.add app] in Hx. cbv beta in Hx. split; [left; ul| lia]. }
    assert (FR5 : rw_cells bsegs m5 (usp + -112) (pid_frame (C8 (Z_to_bv 64 (P + 24))) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree_nw bsegs m4 m5 _ _ FR4). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES5).
      intros x Hx. unfold pid_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| ul]. }

    pose proof (pi_walk12 usp lo RES (repeat z8 16) jj0 jj1 (Z_to_bv 64 (P + 24)) gp (Z_to_bv 64 0x6be3e8) u0 u1 u2 (Z_to_bv 64 RES) b1 b2 b3 b4 b5 b6 b7
                  (Z_to_bv 64 len) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 (P + 64)) (Z_to_bv 64 (P + 72)) (Z_to_bv 64 0) (Z_to_bv 64 0)
                  (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) u3 u4 u5 u6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F5 fc5 m5
                  ST5 ltac:(ul) ltac:(ul) RLO ltac:(ul) (shz_stack RT AF Σ2 m5 RES 24 ART5 ltac:(ul) ltac:(lia) ltac:(ul)) RC5 FR5 MI5) as W6.
    lazymatch type of W6 with evt bsegs _ ?X =>
      assert (W6' : forall ms, eq X ms -> evt bsegs _ ms) by (intros ms <-; exact W6) end.
    clear W6.
    apply (cps_realizes bsegs _ _ _ c5 (asta_evt_c RT AF Σ2 PMc _ _ MST W6') Hc5'). clear W6'. intros c6 Hc6.
    apply Hk. split; [| apply (cfrm0_of_asta RT Σ2 PMc _ c6 Hc6); intros ms (m6 & _ & E6 & _); rewrite E6; exact FRM5].
    exists Σ2, []. split; [| split; [reflexivity| split; [reflexivity| split; [reflexivity| split; [reflexivity| lia]]]]].
    eapply ASTA_conseq; [exact Hc6|]. intros ms (m6 & RS6 & _ & MU6 & WM6 & MI6 & ST6 & RC6). exists (Z_to_bv 64 2), m6.
    split; [rewrite ESP; exact RS6|].
    pose proof (art_fp_client RT AF Σ2 m5 m6 lo _ ART5 LOW FPR MU6 WM6) as ART6.
    split; [split; [exact ART6| split; [exact MI6| exact ST6]]|].

    assert (AG26 : agree_on (fun x => aclient (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -112) x /\ ~ (usp - 112 <= x < usp) /\ ~ (P <= x < P + 80)
                                      /\ ~ (RES <= x < RES + 24)) m2 m6).
    { intros a (H0 & H1 & H2 & H3). rewrite (MU6 a), (PRES5 a H0 ltac:(lia)), (AG24 a ltac:(split; [lia| exact H2])); [reflexivity|].
      cbn [outside]. split; [exact H1|]. split; [exact H3| exact I]. }
    assert (STAT : forall x, in_ranges LIB_FP x -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -112) x /\ ~ (usp - 112 <= x < usp) /\ ~ (P <= x < P + 80)
                                      /\ ~ (RES <= x < RES + 24)).
    { intros x Hx. destruct (lib_fp_static _ Hx) as (CS & R). split; [right; left; exact CS|].
      clear - R FSEG FLO LOW LOR RLO SP0R SP0W. unfold SEGTOP_A in *. split; [ul|]. split; [lia| ul]. }
    split.
    { intros a Ha Hout. unfold pid_XA in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & _).
      assert (Ha2 : aclient (rt_live RT Σ2) (rt_frames RT Σ2) usp (bv_unsigned a)).
      { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV2; do 6 right; exact He| auto| lia]. }
      pose proof (aclient_split_c RT AF Σ2 m2 usp (bv_unsigned a) ART2 Ha2) as SPL.
      apply AG26. split; [apply (aclient_mono _ _ _ _ _ _ _ Ha2); [auto| auto| lia]|]. split; [clear - SPL LOW LOR; ul|]. split; [exact HO1| exact HO2]. }
    split.
    { exists (Z_to_bv 64 2), jj1. unfold res_cellsA. replace (bv_eqb (Z_to_bv 64 2) (Z_to_bv 64 0)) with false by reflexivity.
      split; [exact RC6|]. split; [rewrite unsigned_lit by lia; lia|]. split; [left; rewrite unsigned_lit by lia; lia|].
      intros E. exfalso. apply (f_equal bv_unsigned) in E. rewrite !unsigned_lit in E by lia. lia. }
    split.
    { right. apply (lib1_loc m2 m6 LIB2). intros a Ha. apply AG26. exact (STAT _ Ha). }

    assert (CLP : forall x, P <= x < P + 80 -> aclient (rt_live RT Σ2) (rt_frames RT Σ2) (usp + -112) x).
    { intros x Hx. right; right; right; left. exists f, k. split; [exact INF| lia]. }
    assert (PC6 : rw_cells bsegs m6 P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                                 (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0))).
    { apply (rw_cells_agree_nw bsegs m4 m6 _ _ PC4). intros a Ha. unfold pid_cells in Ha. cbn [cells_size csize Nat.add] in Ha. cbv beta in Ha.
      rewrite (MU6 a), (PRES5 a (CLP (bv_unsigned a) ltac:(lia)) ltac:(ul)); [reflexivity|]. cbn [outside]. split; [ul|]. split; [ul| exact I]. }
    assert (IC6 : rw_cells bsegs m6 impl (impl16 (Z_to_bv 64 0x17a150) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                                 (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0))).
    { apply (rw_cells_agree_nw bsegs m2 m6 _ _ IC2). eapply agree_sub; [exact AG26|]. intros x Hx. unfold impl16 in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
      pose proof (af_frames_range RT AF Σ2 m2 f k ART2 INF) as (_ & _ & _ & FLV). specialize (FLV impl 96 INM).
      split; [right; right; left; exists impl, 96; split; [exact INM| lia]|]. split; [ul|]. split; [clear - Hx FLV FLO FHI; lia| ul]. }
    assert (FOBJ6 : fobj RT Σ2 m6 P 80).
    { apply (fobj_agree RT AF Σ2 Σ2 m4 m6 P 80 ART4 FOBJ4 eq_refl). intros a Ha. cbv beta in Ha.
      destruct (fobj_shadow_client RT AF Σ2 m4 P 80 (usp + -112) (bv_unsigned a) ART4 FOBJ4 Ha) as (CL & XLO).
      rewrite (MU6 a), (PRES5 a CL ltac:(ul)); [reflexivity|]. cbn [outside]. split; [ul|]. split; [ul| exact I]. }
    split; [| split; [exact FOBJ6| exists p1, p17, p57, (Z_to_bv 64 0), (Z_to_bv 64 0); exact PC6]].
    left.
    destruct (pd_of_pid m6 P _ _ _ _ _ _ _ _ _ _ _ _ _ _ PC6) as (pre8 & mid & mid2 & rest & PD6).
    destruct (dl_of_impl16 m6 impl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IC6) as (ipre8 & imid & irest & DL6).
    assert (NDL : List.NoDup (map fst (rt_live RT Σ2))).
    { apply (live_starts_nodup RT AF Σ2 m2 ART2). intros p n Hin. rewrite LV2 in Hin. cbn [In] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin as <- <-; lia|]). exact (LPOS p n Hin). }
    exists impl, tape, sbuf, idx, oc, ia, (al_tape cap), (al_sbuf cap), (sc_idx cap), 8192, 1024, (Z_to_bv 64 cap), pre8, mid, mid2, rest, ipre8, imid, irest.
    split; [exact FOBJ6|]. split; [exact PD6|]. split; [exact INM|]. split; [clear - IM16; Z.div_mod_to_equations; lia|]. split; [exact DL6|].
    rewrite LV2. cbn [In].
    split; [tauto|]. split; [tauto|]. split; [tauto|]. split; [tauto|]. split; [tauto|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    rewrite LV2 in NDL. split; [exact (six_nodup0 _ _ _ _ _ _ _ NDL)|]. exact (six_removes _ _ _ _ _ _ _ _ _ _ _ _ L NDL).
Qed.

End Pid2.
