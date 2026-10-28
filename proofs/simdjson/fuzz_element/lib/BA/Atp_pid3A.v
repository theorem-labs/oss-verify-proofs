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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_setcapA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_setmd. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_deldtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_pdtorA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_hkit3A. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage2_iface Sj_h_parsew. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_parseA Atp_createA Atp_activewA Atp_activeA Atp_pidwA Atp_pidw2A Atp_pidw3A Atp_hkit4A Atp_hkit5A Atp_hkit6A Atp_pid1A Atp_pidw2A Atp_pidiA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation PIREGT ra sp gp tp t0 t1 t2 RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6 :=
  (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1v
       a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) s6v s7v s8v (Z_to_bv 64 (P + 24))
       (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) (only parsing).

Lemma pd_of_pid : forall (m : mem) P b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 lb lbcap,
  rw_cells asegs m P (pid_cells b0 p1 impl b16 p17 err tape sbuf dcap maxcap nas p57 lb lbcap) ->
  exists pre8 mid mid2 rest, rw_cells asegs m P (pd_cells pre8 impl mid tape sbuf dcap mid2 lb rest).
Proof.
  intros until lbcap. intros H. pose proof H as ((W & _) & _). unfold pid_cells in W. cbn [cells_wf cell_wf] in W.
  destruct W as (_ & L1 & _ & _ & L17 & _ & _ & _ & _ & _ & _ & L57 & _).
  exists ([b0] ++ p1), ([b16] ++ p17 ++ le4 err), (le8 maxcap ++ [nas] ++ p57), (le8 lbcap).
  apply (rw_cells_relayout m P _ _ H).
  - unfold pd_cells. cbn [cells_wf cell_wf]. rewrite !length_app, !length_le8, !length_le4, L1, L17, L57. cbn [length]. repeat split; reflexivity.
  - unfold pd_cells, pid_cells. cbn [cells_bytes cbytes]. rewrite <- ?app_assoc. reflexivity.
  - reflexivity.
Qed.

Section Pid3.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.
Hypothesis PARSE : parse_cps RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Local Ltac nomod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac std_lia__ := lia.
Local Ltac lia := nomod; std_lia__.
Local Ltac ul := nomod; unfold PID_STACK, PARSE_STACK, S2A_STACK, Sj_num_iface.NUMA_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; std_lia__.

Theorem pid_tail : forall (Σ3 : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1v t3 t4 t5 t6 : word) F fc (m : mem) (lo RES P len0 cap impl idx oc ia tape sbuf copy BUF : Z) (bsz : list Z)
    (L : list (Z * Z)) (jf jr p1 p17 p57 p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  bytes_ok bsz -> blen bsz <= len0 -> len0 <= 1048512 -> cap = Z.max len0 32 -> copy <= BUF -> BUF + blen bsz = copy + len0 ->
  ART RT Σ3 m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -112) ->
  rw_cells asegs m (bv_unsigned sp + -112) (pid_frame (CB 8 jf) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells asegs m P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  fobj RT Σ3 m P 80 ->
  rw_cells asegs m impl (impl16 (Z_to_bv 64 0x164ad0) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  rw_cells asegs m RES [CB 24 jr] -> lib1 m -> bytes_at asegs m BUF (padded_bytes bsz) ->
  rt_live RT Σ3 = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: L ->
  In (copy, len0 + 64) L ->
  lposx L ->
  impl mod 16 = 0 -> idx mod 16 = 0 -> oc mod 16 = 0 -> ia mod 16 = 0 -> tape mod 16 = 0 -> sbuf mod 16 = 0 -> copy mod 16 = 0 ->
  (length (rt_frames RT Σ3) + S2A_FRAMES <= FRAMES_MAX)%nat -> S2A_COST (blen bsz) <= rt_credit RT Σ3 -> Z.of_nat (length (rt_live RT Σ3)) < LIVE_MAX ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP ->
  rt_sp0 RT Σ3 - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ3 PMc (eq (MS (PIREGT rax (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 RES P BUF (blen bsz) a0 a1 a2 a3 a4 a5 a6 a7
                                        s1v (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3 t4 t5 t6)
                                F (Z_to_bv 64 0xb585c) fc None m (seg_rom asegs))))
        (pid_post RT Σ3 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo RES P L impl idx oc ia tape sbuf cap (S2A_COST (blen bsz)) m).
Proof using AF MSET PARSE AFV.
  intros Σ3 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1v t3 t4 t5 t6 F fc m
    lo RES P len0 cap impl idx oc ia tape sbuf copy BUF bsz L jf jr p1 p17 p57 p12 p28 p50
    FDO MST BOK BLE LEN0 ECAP CBUF EBUF ART0 MI0 ST0 FR0 PC0 FOBJ0 IC0 RC0 LIB0 BUFB0 LV3 INCL LPOS IM16 IX16 OC16 IA16 TP16 SB16 CP16
    FRB CRB LVB RLO RHI LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ3 m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ3 m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (BL0 : 0 <= blen bsz) by (unfold blen; lia).
  destruct (cap_arith len0 (blen bsz) cap ECAP ltac:(lia) ltac:(change (2^26) with 67108864; lia))
    as (CAP & TC1 & TC2 & SC1 & SC2 & SC8 & IC1' & IC2' & IC3' & ETAPE & EIDX).
  pose proof (al_sbuf_bounds cap CAP) as SBB.
  pose proof FOBJ0 as (P8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
  pose proof (fframe_ranges RT AF Σ3 m f k ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ3 m f k ART0 INF) as (_ & FSEG).

  assert (INC : In (copy, len0 + 64) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; do 6 right; exact INCL).
  assert (INA : In (ia, 1024) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INO : In (oc, 8192) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INX : In (idx, sc_idx cap) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INM : In (impl, 96) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INT : In (tape, al_tape cap) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INS : In (sbuf, al_sbuf cap) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  pose proof (af_live_range RT AF Σ3 m impl 96 ART0 INM) as (IM0 & IM1 & IMS).
  pose proof (af_live_range RT AF Σ3 m copy _ ART0 INC) as (CP0 & CP1 & _).
  assert (M8 : forall x, x mod 16 = 0 -> x mod 8 = 0) by (intros x Hx; clear - Hx; Z.div_mod_to_equations; lia).
  assert (EU2 : bv_unsigned (Z_to_bv 64 (usp + -112)) = usp + -112) by (apply unsigned_lit; ul).
  assert (SPA2 : (usp + -112) mod 16 = 0) by (replace (usp + -112) with (usp + (-7) * 16) by lia; rewrite Z.mod_add by lia; exact SPA).
  assert (FPI : fp_client RT Σ3 lo [(impl, impl + 96)]).
  { constructor; [| constructor]. right; left. exists impl, 96. cbn [fst snd]. split; [exact INM| lia]. }

  assert (SHZ0 : pt_shz [(impl, impl + 96)] m P impl).
  { intros m' MU WM. pose proof (art_fp_client RT AF Σ3 m m' lo _ ART0 LOW FPI MU WM) as ART'.
    split; [exact (fobj_shz RT AF Σ3 m' P 80 ART' (fobj_munch RT AF Σ3 m m' lo _ P 80 ART0 LOW FPI MU FOBJ0))|].
    split; [exact (shz_live RT AF Σ3 m' impl 96 ART' INM (M8 _ IM16))|].
    apply (shz_lit RT AF Σ3 m' _ _ ART'); [unfold ACC_LITS; repeat (first [left; reflexivity | right])| reflexivity| lia| reflexivity]. }
  pose proof (af_frames_range RT AF Σ3 m f k ART0 INF) as (_ & _ & _ & FLV).
  pose proof (pi_walk9 RES P BUF (blen bsz) impl z8 z8 z8 z8 p1 p17 p57 p12 p28 p50 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                (Z_to_bv 64 4294967295) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 idx) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                rax (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1v (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3 t4 t5 t6 F fc m
                ltac:(ul) ltac:(ul) IM0 ltac:(ul) IMS ltac:(pose proof (FLV impl 96 INM); clear - H FLO FHI; lia) SHZ0 (AFV Σ3 m ART0) PC0 IC0 MI0) as W9.
  lazymatch type of W9 with evt asegs _ ?X =>
    assert (W9' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W9) end.
  clear W9.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ3 PMc _ _ MST W9') Hc). clear W9'. intros c1 Hc1.
  destruct (ASTA_unpack RT Σ3 _ _ c1 Hc1) as (ms1 & (m1 & -> & MU1 & WM1 & MI1 & PC1 & IC1) & Hc1'). clear Hc1.
  pose proof (art_fp_client RT AF Σ3 m m1 lo _ ART0 LOW FPI MU1 WM1) as ART1.
  pose proof (fobj_munch RT AF Σ3 m m1 lo _ P 80 ART0 LOW FPI MU1 FOBJ0) as FOBJ1.
  assert (AG1 : agree_on (fun x => ~ (impl <= x < impl + 96)) m m1).
  { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. cbn [outside]. split; [exact Hx| exact I]. }
  pose proof (stk_wmono m m1 _ _ ST0 WM1 ltac:(ul)) as ST1.
  assert (FR1 : rw_cells asegs m1 (usp + -112) (pid_frame (CB 8 jf) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (rw_cells_agree_nw asegs m m1 _ _ FR0). eapply agree_sub; [exact AG1|]. intros x Hx. unfold pid_frame in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
  assert (RC1 : rw_cells asegs m1 RES [CB 24 jr]).
  { apply (rw_cells_agree_nw asegs m m1 _ _ RC0). eapply agree_sub; [exact AG1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta. ul. }
  assert (LIB1 : lib1 m1).
  { apply (lib1_loc m m1 LIB0). intros a Ha. apply AG1. destruct (lib_fp_static _ Ha) as (CS & _).
    intros Hr. apply (not_live_static RT AF Σ3 m _ ART0 CS). exists impl, 96. split; [exact INM| exact Hr]. }
  assert (BUFB1 : bytes_at asegs m1 BUF (padded_bytes bsz)).
  { apply (bytes_at_agree asegs m m1 _ _ BUFB0). eapply agree_sub; [exact AG1|]. intros x Hx. cbv beta in *. rewrite padded_bytes_blen in Hx.
    pose proof (af_live_disj RT AF Σ3 m impl 96 copy (len0 + 64) [(ia, 1024); (oc, 8192); (idx, sc_idx cap)] ((tape, al_tape cap) :: (sbuf, al_sbuf cap) :: L)
                  ART0 ltac:(rewrite LV3; reflexivity) ltac:(cbn [app In]; do 5 right; exact INCL)) as D.
    clear - Hx D CBUF EBUF. lia. }

  destruct (af_acc_live RT AF Σ3 m1 idx _ ART1 INX) as (WRX & _).
  destruct (af_acc_live RT AF Σ3 m1 oc _ ART1 INO) as (WRO & _).
  destruct (af_acc_live RT AF Σ3 m1 ia _ ART1 INA) as (WRA & _).
  assert (EK : 4 * Z.of_nat (Z.to_nat (roundup64 cap + 9)) = sc_idx cap) by (rewrite Z2Nat.id by lia; lia).
  rewrite <- EK in WRX. destruct (u32arr_of_wr m1 idx _ WRX) as (ws0 & ARR1 & LWS).
  change 8192 with (4 * Z.of_nat 2048) in WRO. destruct (u32arr_of_wr m1 oc _ WRO) as (ocs & OCA1 & LOCS).
  change 1024 with (Z.of_nat 1024) in WRA. destruct (u8arr_of_wr m1 ia _ WRA) as (ias & IAA1 & LIAS).
  assert (EWS : 4 * Z.of_nat (length ws0) = sc_idx cap) by (rewrite LWS; exact EK).
  assert (LWZ : Z.of_nat (length ws0) = roundup64 cap + 9) by (rewrite LWS, Z2Nat.id by lia; reflexivity).

  pose proof PC1 as PC1F.
  unfold pid_cells in PC1.
  change [C1 z8; CB 7 p1; C8 (Z_to_bv 64 impl); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12); C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap);
          C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]
    with ([C1 z8; CB 7 p1; C8 (Z_to_bv 64 impl); C1 z8; CB 3 p17; C4 (Z_to_bv 64 12)] ++ [C8 (Z_to_bv 64 tape); C8 (Z_to_bv 64 sbuf); C8 (Z_to_bv 64 cap)]
          ++ [C8 (Z_to_bv 64 4294967295); C1 z8; CB 7 p57; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]) in PC1.
  apply Sj_stage1_kit.rw_cells_app in PC1 as [PCa PC1]. apply Sj_stage1_kit.rw_cells_app in PC1 as [PCd PCz].
  cbn [cells_size csize Nat.add] in PCd, PCz. change (Z.of_nat 24) with 24 in PCd, PCz. replace (P + 24 + 24) with (P + 48) in PCz by lia.
  pose proof (fobj_sub RT AF Σ3 m1 P 80 24 24 FOBJ1 eq_refl ltac:(lia) ltac:(lia) ltac:(cbn; lia)) as FOBJD1.

  apply (PARSE Σ3 PMc (Z_to_bv 64 0xb58d0) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 RES) s1v
           (Z_to_bv 64 impl) (Z_to_bv 64 BUF) (Z_to_bv 64 (blen bsz)) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 0xe2cdc) a5 a6 a7
           (Z_to_bv 64 (blen bsz)) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
           (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc m1 lo
           impl (P + 24) idx BUF tape sbuf oc ia bsz ws0 (roundup64 (cap + 3)) (al_sbuf cap)
           (Z_to_bv 64 0x164ad0) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) p12 p28 p50 FDO MST);
    try reflexivity; try assumption.
  - lia.
  - lia.
  - lia.
  - rewrite EU2. exact ST1.
  - rewrite EU2. ul.
  - rewrite EU2. ul.
  - rewrite EU2. exact SPA2.
  - rewrite EWS. exact INX.
  - exists copy, (len0 + 64). split; [exact INC|]. split; [exact (M8 _ CP16)| lia].
  - rewrite <- ETAPE. apply live_reg_of_in; [exact INT| exact (M8 _ TP16)].
  - apply live_reg_of_in; [exact INS| exact (M8 _ SB16)].
  - apply live_reg_of_in; [exact INO| exact (M8 _ OC16)].
  - apply live_reg_of_in; [exact INA| exact (M8 _ IA16)].
  - exact (M8 _ IM16).
  - exact (M8 _ IX16).
  - exact (M8 _ TP16).
  - exact (M8 _ SB16).
  - exact (M8 _ OC16).
  - exact (M8 _ IA16).
  - rewrite EWS, <- ETAPE. cbn [pairwise_disj].
    assert (PDJ : forall (i j : nat) pa na pb nb, nth_error (rt_live RT Σ3) i = Some (pa, na) -> nth_error (rt_live RT Σ3) j = Some (pb, nb) -> i <> j ->
                    pa + na <= pb \/ pb + nb <= pa) by (intros i j pa na pb nb; exact (live_disj_nth RT AF Σ3 m1 i j pa na pb nb ART1)).
    rewrite LV3 in PDJ.

    assert (CD : forall p n l1 l2, rt_live RT Σ3 = l1 ++ (p, n) :: l2 -> In (copy, len0 + 64) (l1 ++ l2) -> p + n <= copy \/ copy + (len0 + 64) <= p)
      by (intros p n l1 l2 E HI; exact (af_live_disj RT AF Σ3 m1 p n copy (len0 + 64) l1 l2 ART1 E HI)).
    pose proof (CD ia 1024 [] _ ltac:(rewrite LV3; reflexivity) ltac:(cbn [app In]; do 5 right; exact INCL)) as C_IA.
    pose proof (CD oc 8192 [(ia, 1024)] _ ltac:(rewrite LV3; reflexivity) ltac:(cbn [app In]; do 5 right; exact INCL)) as C_OC.
    pose proof (CD idx (sc_idx cap) [(ia, 1024); (oc, 8192)] _ ltac:(rewrite LV3; reflexivity) ltac:(cbn [app In]; do 5 right; exact INCL)) as C_IX.
    pose proof (CD impl 96 [(ia, 1024); (oc, 8192); (idx, sc_idx cap)] _ ltac:(rewrite LV3; reflexivity) ltac:(cbn [app In]; do 5 right; exact INCL)) as C_IM.
    pose proof (CD tape (al_tape cap) [(ia, 1024); (oc, 8192); (idx, sc_idx cap); (impl, 96)] _ ltac:(rewrite LV3; reflexivity) ltac:(cbn [app In]; do 5 right; exact INCL)) as C_TP.
    pose proof (CD sbuf (al_sbuf cap) [(ia, 1024); (oc, 8192); (idx, sc_idx cap); (impl, 96); (tape, al_tape cap)] _ ltac:(rewrite LV3; reflexivity) ltac:(cbn [app In]; do 5 right; exact INCL)) as C_SB.
    split; [constructor; [exact (PDJ 3 2 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [unfold ivl_disj; cbn [fst snd]; clear - C_IM CBUF EBUF BL0; lia|
            constructor; [exact (PDJ 3 4 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 3 5 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 3 1 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 3 0 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat| constructor]]]]]]|].
    split; [constructor; [unfold ivl_disj; cbn [fst snd]; clear - C_IX CBUF EBUF BL0; lia|
            constructor; [exact (PDJ 2 4 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 2 5 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 2 1 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 2 0 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat| constructor]]]]]|].
    split; [constructor; [unfold ivl_disj; cbn [fst snd]; clear - C_TP CBUF EBUF BL0; lia|
            constructor; [unfold ivl_disj; cbn [fst snd]; clear - C_SB CBUF EBUF BL0; lia|
            constructor; [unfold ivl_disj; cbn [fst snd]; clear - C_OC CBUF EBUF BL0; lia|
            constructor; [unfold ivl_disj; cbn [fst snd]; clear - C_IA CBUF EBUF BL0; lia|
            constructor]]]]|].
    split; [constructor; [exact (PDJ 4 5 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 4 1 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 4 0 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat| constructor]]]|].
    split; [constructor; [exact (PDJ 5 1 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat|
            constructor; [exact (PDJ 5 0 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat| constructor]]|].
    split; [constructor; [exact (PDJ 1 0 _ _ _ _ eq_refl eq_refl ltac:(discriminate))%nat| constructor]|].
    split; [constructor| exact I].
  - exists ocs. split; assumption.
  - exists ias. split; assumption.
  - split; [exact Hc1'| apply (cfrm0_of_asta RT Σ3 PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM].
  - intros c2 ((Σ4 & Hc2 & FRS4 & LV4 & SP4 & CR4) & FC2).
    destruct (ASTA_unpack_f RT Σ4 _ _ c2 Hc2 FC2) as (ms2 & (m2 & v & RS2 & V64 & OK2 & (ART2 & MI2 & ST2) & PRES2 & (nsi' & nxt' & bufv' & lenv' & docv' & IC2)) & FRM2 & Hc2'). clear Hc2.
    destruct RS2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & ->).
    cbn [ms_fcsr] in FRM2. rewrite EU2 in ST2, PRES2. rewrite (ret_pc_even 0xb58d0) in Hc2' by (clear; lia).
    assert (LOW4 : rt_sp0 RT Σ4 - STACK_WIN <= lo) by (rewrite SP4; exact LOW).
    assert (INF4 : In (f, k) (rt_frames RT Σ4)) by (rewrite FRS4; exact INF).

    assert (OUTX : forall x, ~ in_live (rt_live RT Σ3) x ->
              outside (parse_X impl idx tape sbuf oc ia (Z.of_nat (length ws0)) (roundup64 (cap + 3)) (al_sbuf cap)) x).
    { intros x NL. apply (outside_of_not_live (rt_live RT Σ3)); [| exact NL]. unfold parse_X. rewrite EWS, <- ETAPE.
      intros r Hr. cbn [In] in Hr.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; cbn [fst snd];
        [exists impl, 96| exists idx, (sc_idx cap)| exists tape, (al_tape cap)| exists sbuf, (al_sbuf cap)| exists oc, 8192| exists ia, 1024];
        (split; [assumption| lia]). }
    assert (FR2 : rw_cells asegs m2 (usp + -112) (pid_frame (CB 8 jf) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ FR1). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. unfold pid_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul|]. apply OUTX. apply (not_live_stack RT AF Σ3 m1 x ART1). ul. }
    assert (RC2 : rw_cells asegs m2 RES [CB 24 jr]).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ RC1). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul|]. apply OUTX. apply (not_live_stack RT AF Σ3 m1 x ART1). ul. }
    assert (PC2 : rw_cells asegs m2 P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                                 (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0))).
    { apply (rw_cells_agree_nw asegs m1 m2 _ _ PC1F). apply (agree_of_pres_fp _ _ _ _ _ _ _ PRES2).
      intros x Hx. unfold pid_cells in Hx. cbn [cells_size csize Nat.add] in Hx.
      split; [right; right; right; left; exists f, k; split; [exact INF| lia]|]. apply OUTX. apply (not_live_frame RT AF Σ3 m1 f k x ART1 INF). lia. }
    assert (FOBJ2 : fobj RT Σ4 m2 P 80).
    { apply (fobj_pres_out RT AF Σ3 Σ4 _ _ _ m1 m2 P 80 ART1 FOBJ1 PRES2 FRS4). intros x Hx. apply OUTX.
      destruct (fobj_shadow_range RT AF Σ3 m1 P 80 ART1 FOBJ1) as (f' & k' & INF' & S1' & S2' & _).
      apply (not_live_fshadow RT AF Σ3 m1 f' k' x ART1 INF'). lia. }
    assert (LIB2 : lib1 m2).
    { apply (lib1_loc m1 m2 LIB1). intros a Ha. destruct (lib_fp_static _ Ha) as (CS & _).
      apply PRES2; [right; left; exact CS|]. apply OUTX. exact (not_live_static RT AF Σ3 m1 _ ART1 CS). }
    assert (FPR4 : fp_client RT Σ4 lo [(usp - 112, usp); (RES, RES + 24)]).
    { constructor; [left; cbn [fst snd]; ul|]. constructor; [left; cbn [fst snd]; ul| constructor]. }

    assert (FINAL : forall m3 : mem, ART RT Σ4 m3 -> mem_inv asegs m3 -> stk asegs m3 lo usp ->
              agree_on (fun x => aclient (rt_live RT Σ4) (rt_frames RT Σ4) (usp + -112) x /\ ~ (usp - 112 <= x < usp) /\ ~ (RES <= x < RES + 24)) m2 m3 ->
              (exists (r : word) j20, rw_cells asegs m3 RES (res_cellsA (P + 24) r j20) /\ bv_unsigned r < 64
                                     /\ s2a_okres tape sbuf (roundup64 (cap + 3)) (al_sbuf cap) r m3) ->
              rt_after_f RT Σ4 usp lo m m3 /\ rt_pres_fp L (rt_frames RT Σ3) usp (pid_X P RES) m m3
              /\ (exists (r : word) j20, rw_cells asegs m3 RES (res_cellsA (P + 24) r j20) /\ bv_unsigned r < 64
                                        /\ s2a_okres tape sbuf (roundup64 (cap + 3)) (al_sbuf cap) r m3)
              /\ sj_lib m3 /\ pdone RT Σ4 m3 P L /\ pidA_st RT Σ4 m3 P impl idx oc ia tape sbuf cap).
    { intros m3 ART3 MI3 ST3 AG23 RC3.
      split; [split; [exact ART3| split; [exact MI3| exact ST3]]|].
      split.
      { intros a Ha Hout. unfold pid_X in Hout. cbn [outside] in Hout. destruct Hout as (HO1 & HO2 & _).
        assert (Ha3 : aclient (rt_live RT Σ3) (rt_frames RT Σ3) usp (bv_unsigned a)).
        { apply (aclient_mono _ _ _ _ _ _ _ Ha); [intros e He; rewrite LV3; do 6 right; exact He| auto| lia]. }
        pose proof (aclient_split_c RT AF Σ3 m usp (bv_unsigned a) ART0 Ha3) as SPL.
        assert (NFR : ~ (usp - 112 <= bv_unsigned a < usp)) by (clear - SPL LOW LOR; ul).
        assert (Ha3' : aclient (rt_live RT Σ3) (rt_frames RT Σ3) (usp + -112) (bv_unsigned a)) by (apply (aclient_mono _ _ _ _ _ _ _ Ha3); [auto| auto| lia]).
        assert (FA : forall p n, In (p, n) [(ia, 1024); (oc, 8192); (idx, sc_idx cap); (impl, 96); (tape, al_tape cap); (sbuf, al_sbuf cap)] ->
                       ~ (p <= bv_unsigned a < p + n)).
        { intros p n Hin.
          exact (fresh_apart_l RT AF Σ3 m [(ia, 1024); (oc, 8192); (idx, sc_idx cap); (impl, 96); (tape, al_tape cap); (sbuf, al_sbuf cap)]
                   L p n usp (bv_unsigned a) ART0 LV3 Hin ltac:(ul) Ha). }
        rewrite (AG23 a), (PRES2 a Ha3'), (AG1 a); [reflexivity| | |].
        - apply (FA impl 96). cbn [In]. tauto.
        - unfold parse_X. rewrite EWS, <- ETAPE. cbn [outside].
          split; [apply (FA impl 96); cbn [In]; tauto|]. split; [apply (FA idx (sc_idx cap)); cbn [In]; tauto|].
          split; [apply (FA tape (al_tape cap)); cbn [In]; tauto|]. split; [apply (FA sbuf (al_sbuf cap)); cbn [In]; tauto|].
          split; [apply (FA oc 8192); cbn [In]; tauto|]. split; [apply (FA ia 1024); cbn [In]; tauto| exact I].
        - split; [rewrite LV4, FRS4; exact Ha3'|]. split; [exact NFR| exact HO2]. }
      split; [exact RC3|].
      split.
      { right. apply (lib1_loc m2 m3 LIB2). intros a Ha. destruct (lib_fp_static _ Ha) as (CS & R). apply AG23.
        split; [right; left; exact CS|]. clear - R LOW LOR RLO SP0R SP0W. unfold SEGTOP_A in *. split; ul. }
      assert (PC3 : rw_cells asegs m3 P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                                   (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0))).
      { apply (rw_cells_agree_nw asegs m2 m3 _ _ PC2). eapply agree_sub; [exact AG23|]. intros x Hx. unfold pid_cells in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
        split; [right; right; right; left; exists f, k; split; [exact INF4| lia]|]. split; ul. }
      assert (IC3 : rw_cells asegs m3 impl (impl16 (Z_to_bv 64 0x164ad0) nsi' p12 (Z_to_bv 64 idx) nxt' p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024) (Z_to_bv 8 0) (Z_to_bv 8 0) p50
                                                   (Z_to_bv 64 oc) (Z_to_bv 64 ia) bufv' lenv' docv')).
      { apply (rw_cells_agree_nw asegs m2 m3 _ _ IC2). eapply agree_sub; [exact AG23|]. intros x Hx. unfold impl16 in Hx. cbn [cells_size csize Nat.add] in Hx. cbv beta.
        split; [right; right; left; exists impl, 96; split; [rewrite LV4; exact INM| lia]|]. split; ul. }
      assert (FOBJ3 : fobj RT Σ4 m3 P 80).
      { apply (fobj_agree RT AF Σ4 Σ4 m2 m3 P 80 ART2 FOBJ2 eq_refl). intros a Ha. cbv beta in Ha.
        destruct (fobj_shadow_client RT AF Σ4 m2 P 80 (usp + -112) (bv_unsigned a) ART2 FOBJ2 Ha) as (CL & XLO).
        apply AG23. split; [exact CL|]. split; ul. }
      split.
      {
        destruct (pd_of_pid m3 P _ _ _ _ _ _ _ _ _ _ _ _ _ _ PC3) as (pre8 & mid & mid2 & rest & PD3).
        destruct (dl_of_impl16 m3 impl _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ IC3) as (ipre8 & imid & irest & DL3).
        destruct (six_facts RT AF Σ3 m ia oc idx impl tape sbuf 1024 8192 (sc_idx cap) 96 (al_tape cap) (al_sbuf cap) L ART0 LV3
                    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) LPOS) as [ND6 RM6].
        exists impl, tape, sbuf, idx, oc, ia, (al_tape cap), (al_sbuf cap), (sc_idx cap), 8192, 1024, (Z_to_bv 64 cap), pre8, mid, mid2, rest, ipre8, imid, irest.
        split; [exact FOBJ3|]. split; [exact PD3|]. rewrite LV4. split; [exact INM|]. split; [exact (M8 _ IM16)|]. split; [exact DL3|].
        split; [exact INS|]. split; [exact INT|]. split; [exact INA|]. split; [exact INO|]. split; [exact INX|].
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
        split; [exact ND6|]. rewrite LV3. exact RM6. }

      split; [exact FOBJ3|]. split; [exists p1, p17, p57; exact PC3|]. exists nsi', p12, nxt', p28, p50, bufv', lenv', docv'. exact IC3. }
    assert (CRF : rt_credit RT Σ3 - S2A_COST (blen bsz) <= rt_credit RT Σ4) by exact CR4.
    destruct (Z.eq_dec (bv_unsigned v) 0) as [V0|VN].
    +
      assert (EV : v = Z_to_bv 64 0) by (apply bv_eq; rewrite V0; reflexivity). subst v.
      apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [8; 8; 4; 4]%nat) in RC2; [| reflexivity]. cbn [mk_CB_cells app] in RC2.
      repeat match type of RC2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jj" in set (j := t) in RC2; clearbody j end.
      assert (SHZ2 : forall m' : mem, munch [(usp - 112, usp); (RES, RES + 24)] m2 m' -> wmono asegs m2 m' -> shz m' RES 24).
      { intros m' MU WM. apply (shz_stack RT AF Σ4 m' RES 24 (art_fp_client RT AF Σ4 m2 m' lo _ ART2 LOW4 FPR4 MU WM)); [rewrite SP4; ul| lia| ul]. }
      pose proof (pi_walk10a usp lo RES P BUF (blen bsz) jj jj0 jj1 jj2 jf gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1v (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) u3 u4 u5 u6
                    ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F2 fc2 m2 ST2 ltac:(ul) ltac:(ul) RLO ltac:(ul) ltac:(ul) ltac:(ul) SHZ2 RC2 FR2 MI2) as WA.
      lazymatch type of WA with evt asegs _ ?X =>
        assert (WA' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact WA) end.
      clear WA.
      apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ4 PMc _ _ MST WA') Hc2'). clear WA'. intros c3 Hc3.
      apply Hk. split; [| apply (cfrm0_of_asta RT Σ4 PMc _ c3 Hc3); intros ms (m3 & _ & E3 & _); rewrite E3; exact FRM2].
      exists Σ4. split; [| split; [exact LV4| split; [rewrite FRS4; reflexivity| split; [exact SP4| exact CRF]]]].
      eapply ASTA_conseq; [exact Hc3|]. intros ms (m3 & RS3 & _ & MU3 & WM3 & MI3 & ST3 & RC3). exists (Z_to_bv 64 (RES + 16)), m3.
      split; [rewrite ESP; exact RS3|].
      apply (FINAL m3 (art_fp_client RT AF Σ4 m2 m3 lo _ ART2 LOW4 FPR4 MU3 WM3) MI3 ST3).
      2:{ exists (Z_to_bv 64 0), jj2. split; [unfold res_cellsA; rewrite bv_eqb_refl; exact RC3|]. split; [exact V64|].

          pose proof (af_live_range RT AF Σ3 m tape _ ART0 INT) as (TP0 & TP1 & _). pose proof (af_live_range RT AF Σ3 m sbuf _ ART0 INS) as (SB0 & SB1 & _).
          apply (s2a_okres_agree (fun x => x < lo) m2 m3); [| intros a Ha; clear - Ha TP1 LOW LOR RLO ETAPE; ul| intros a Ha; clear - Ha SB1 LOW LOR RLO; ul| exact OK2].
          apply (agree_of_munch _ _ _ _ MU3). intros x Hx. cbn [outside]. clear - Hx LOR RLO; split; [ul| split; [ul| exact I]]. }
      intros a (_ & H1 & H2). apply MU3. cbn [outside]. split; [exact H1|]. split; [exact H2| exact I].
    +
      pose proof (pi_walk10b RES P BUF (blen bsz) v (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1v (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) u3 u4 u5 u6 F2 fc2 m2
                    VN ltac:(ul) ltac:(ul)) as WB.
      lazymatch type of WB with evt asegs _ ?X =>
        assert (WB' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact WB) end.
      clear WB.
      apply (cps_realizes asegs _ _ _ c2 (asta_evt_c RT AF Σ4 PMc _ _ MST WB') Hc2'). clear WB'. intros c3 Hc3.
      apply (rw_cells_split_CB asegs _ _ [] 24 _ [] [16; 4; 4]%nat) in RC2; [| reflexivity]. cbn [mk_CB_cells app] in RC2.
      repeat match type of RC2 with context [CB ?k ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jj" in set (j := t) in RC2; clearbody j end.
      apply (MSET Σ4 PMc (Z_to_bv 64 0xb58ec) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 (Z_to_bv 64 RES) (Z_to_bv 64 (RES + 16))
               (Z_to_bv 64 RES) (Z_to_bv 64 0) (Z_to_bv 64 16) b3 b4 b5 b6 b7
               v (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
               (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) u3 u4 u5 u6 F2 fc2 m2 RES 16 (Z_to_bv 8 0) lo FDO MST);
        try reflexivity; try assumption;
        [.. | split; [exact Hc3| apply (cfrm0_of_asta RT Σ4 PMc (eq _) c3 Hc3); intros ms0 <-; exact FRM2] |].
      * ul.
      * lia.
      * unfold checked_dst. rewrite EU2. split; [| split].
        -- intros _. split; [apply (af_acc_stack RT AF Σ4 m2 _ _ ART2); rewrite ?SP4; ul|]. right; right; left. rewrite SP4. ul.
        -- intros i Hi. left. ul.
        -- exact (rw_cells_wr_at asegs m2 _ _ 16 RC2 ltac:(cbn; lia)).
      * unfold call_ok. rewrite EU2. split; [exact ST2|]. split; [exact LOW4|]. split; [ul|]. split; [ul| exact SPA2].
      * intros c4 (Hc4 & FC4). unfold icpt_post in Hc4.
        destruct (ASTA_unpack_f RT Σ4 _ _ c4 Hc4 FC4) as (ms4 & (m3 & RS4 & (ART3 & MI3 & WM3 & ST3) & PRES3 & BS3) & FRM3 & Hc4'). clear Hc4.
        destruct RS4 as (w0 & w1 & w2 & g1 & g2 & g3 & g4 & g5 & g6 & g7 & w3 & w4 & w5 & w6 & F3 & fc3 & ->).
        cbn [ms_fcsr] in FRM3. rewrite EU2 in ST3, PRES3. rewrite (ret_pc_even 0xb58ec) in Hc4' by (clear; lia).
        assert (RC3 : rw_cells asegs m3 RES [CB 16 (repeat z8 16); CB 4 jj0; CB 4 jj1]).
        { apply (cells_mid_update m2 m3 RES [] 16 jj (repeat z8 16) [CB 4 jj0; CB 4 jj1] RC2);
            [| exact WM3| cbn [cells_size]; change (Z.of_nat 0) with 0; rewrite Z.add_0_r; exact BS3| reflexivity].
          apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3). intros x Hx. cbn [cells_size csize Nat.add app] in Hx. cbv beta in Hx. split; [left; ul| lia]. }
        assert (FR3 : rw_cells asegs m3 (usp + -112) (pid_frame (CB 8 jf) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
        { apply (rw_cells_agree_nw asegs m2 m3 _ _ FR2). apply (agree_of_pres_ex _ _ _ _ _ _ _ _ PRES3).
          intros x Hx. unfold pid_frame in Hx. cbn [cells_size csize Nat.add] in Hx. split; [left; ul| ul]. }
        pose proof (pi_walk11 usp lo RES (repeat z8 16) jj0 jj1 jf gp (Z_to_bv 64 0x6a7e68) w0 w1 w2 (Z_to_bv 64 RES) g1 g2 g3 g4 g5 g6 g7
                      v (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
                      (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) w3 w4 w5 w6 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F3 fc3 m3
                      ST3 ltac:(ul) ltac:(ul) RLO ltac:(ul) (shz_stack RT AF Σ4 m3 RES 24 ART3 ltac:(rewrite SP4; ul) ltac:(lia) ltac:(ul)) RC3 FR3 MI3) as WC.
        lazymatch type of WC with evt asegs _ ?X =>
          assert (WC' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact WC) end.
        clear WC.
        apply (cps_realizes asegs _ _ _ c4 (asta_evt_c RT AF Σ4 PMc _ _ MST WC') Hc4'). clear WC'. intros c5 Hc5.
        apply Hk. split; [| apply (cfrm0_of_asta RT Σ4 PMc _ c5 Hc5); intros ms (m4 & _ & E4 & _); rewrite E4; exact FRM3].
        exists Σ4. split; [| split; [exact LV4| split; [rewrite FRS4; reflexivity| split; [exact SP4| exact CRF]]]].
        eapply ASTA_conseq; [exact Hc5|]. intros ms (m4 & RS5 & _ & MU4 & WM4 & MI4 & ST4 & RC4). exists (Z_to_bv 64 0), m4.
        split; [rewrite ESP; exact RS5|].
        apply (FINAL m4 (art_fp_client RT AF Σ4 m3 m4 lo _ ART3 LOW4 FPR4 MU4 WM4) MI4 ST4).
        2:{ exists v, jj1. split; [| split; [exact V64|]].
            - unfold res_cellsA. destruct (bv_eqb v (Z_to_bv 64 0)) eqn:EQ; [| exact RC4].
              exfalso. apply VN. apply bv_eqb_eq in EQ. rewrite EQ. reflexivity.
            - destruct OK2 as [K|(E & _)]; [left; exact K|]. exfalso. apply VN. rewrite E. reflexivity. }
        intros a (H0 & H1 & H2). rewrite (MU4 a), (PRES3 a H0 ltac:(lia)); [reflexivity|]. cbn [outside]. split; [exact H1|]. split; [exact H2| exact I].
Qed.

End Pid3.
