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
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface I_lkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_hkit2 Sj_new Sj_h_dtor Sj_h_alloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_setcapA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_setmd. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_fzwA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_deldtor. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_pdtorA. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_h_layout. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_hkit3A. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Sj_stage2_iface Sj_h_parsew. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_parseA Atp_createA Atp_activewA Atp_activeA Atp_pidwA Atp_pidw2A Atp_pidw3A Atp_hkit4A Atp_hkit5A Atp_hkit6A Atp_pid1A Atp_pidiA Atp_pid3A Atp_pid4A Atp_pidA Atp_pid_s1zA Atp_pid_parse0A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Notation PIREGT ra sp gp tp t0 t1 t2 RES P BUF blen a0 a1 a2 a3 a4 a5 a6 a7 s1v s6v s7v s8v t3 t4 t5 t6 :=
  (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 RES) s1v
       a0 a1 a2 a3 a4 a5 a6 a7
       (Z_to_bv 64 blen) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) s6v s7v s8v (Z_to_bv 64 (P + 24))
       (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6) (only parsing).

Section Pid0Iface.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.

Definition pid0_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (P RES : Z) (p1 p17 p57 jr : list byte) (lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 RES -> a1 = Z_to_bv 64 P -> a2 = Z_to_bv 64 (P + 24) -> a3 = Z_to_bv 64 0 -> a4 = Z_to_bv 64 0 ->
  a5 = Z_to_bv 64 0 -> tp = Z_to_bv 64 0x6a7e68 ->
  fobj RT Σ m P 80 -> rw_cells asegs m P (parser_init p1 p17 p57) ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP -> rw_cells asegs m RES [CB 24 jr] ->
  lposx (rt_live RT Σ) ->
  Z.of_nat (length (rt_live RT Σ)) + 7 <= LIVE_MAX ->
  pid_costA 0 <= rt_credit RT Σ ->
  LIB m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_pid m)))
    (fun c => exists (Σ' : rts RT) (impl idx oc ia tape sbuf : Z),
       ASTA RT Σ' PMc (fun ms => exists v m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 v m' ms
         /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
         /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) ((P, P + 80) :: (RES, RES + 24) :: SJ_W) m m'
         /\ (exists (r : word) j20, rw_cells asegs m' RES (res_cellsA (P + 24) r j20) /\ bv_unsigned r < 64
                                   /\ s2a_okres tape sbuf (roundup64 (32 + 3)) (al_sbuf 32) r m')
         /\ LIB m' /\ pdone RT Σ' m' P (rt_live RT Σ) /\ pidA_st RT Σ' m' P impl idx oc ia tape sbuf 32) c
       /\ rt_live RT Σ' = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx 32) :: (impl, 96) :: (tape, al_tape 32) :: (sbuf, al_sbuf 32) :: rt_live RT Σ
       /\ (impl mod 16 = 0 /\ idx mod 16 = 0 /\ oc mod 16 = 0 /\ ia mod 16 = 0 /\ tape mod 16 = 0 /\ sbuf mod 16 = 0)
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ /\ rt_credit RT Σ - pid_costA 0 <= rt_credit RT Σ').
End Pid0Iface.

Section Pid0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis MSET : memset_icontract_f RT e_asan_memset.
Hypothesis PARSE0 : parse0_cps RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.

Local Ltac nomod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac std_lia__ := lia.
Local Ltac lia := nomod; std_lia__.
Local Ltac ul := nomod; unfold PID_STACK, PARSE_STACK, S2A_STACK, Sj_num_iface.NUMA_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; std_lia__.

Theorem pid_tail0 : forall (Σ3 : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1v t3 t4 t5 t6 : word) F fc (m : mem) (lo RES P cap impl idx oc ia tape sbuf BUF : Z)
    (L : list (Z * Z)) (jf jr p1 p17 p57 p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc ->
  cap = 32 -> 0 <= BUF < 2^64 ->
  ART RT Σ3 m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -112) ->
  rw_cells asegs m (bv_unsigned sp + -112) (pid_frame (CB 8 jf) ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  rw_cells asegs m P (pid_cells z8 p1 (Z_to_bv 64 impl) z8 p17 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
                                (Z_to_bv 64 4294967295) z8 p57 (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  fobj RT Σ3 m P 80 ->
  rw_cells asegs m impl (impl16 (Z_to_bv 64 0x164ad0) (Z_to_bv 64 0) p12 (Z_to_bv 64 idx) (Z_to_bv 64 0) p28 (Z_to_bv 64 cap) (Z_to_bv 64 1024)
                                (Z_to_bv 8 0) (Z_to_bv 8 0) p50 (Z_to_bv 64 oc) (Z_to_bv 64 ia) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)) ->
  rw_cells asegs m RES [CB 24 jr] -> lib1 m ->
  rt_live RT Σ3 = (ia, 1024) :: (oc, 8192) :: (idx, sc_idx cap) :: (impl, 96) :: (tape, al_tape cap) :: (sbuf, al_sbuf cap) :: L ->
  lposx L ->
  impl mod 16 = 0 -> idx mod 16 = 0 -> oc mod 16 = 0 -> ia mod 16 = 0 -> tape mod 16 = 0 -> sbuf mod 16 = 0 ->
  Z.of_nat (length (rt_live RT Σ3)) < LIVE_MAX ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP ->
  rt_sp0 RT Σ3 - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc ->
  cps_f (ASTA RT Σ3 PMc (eq (MS (PIREGT rax (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 RES P BUF 0 a0 a1 a2 a3 a4 a5 a6 a7
                                        s1v (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) t3 t4 t5 t6)
                                F (Z_to_bv 64 0xb585c) fc None m (seg_rom asegs))))
        (pid_post RT Σ3 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo RES P L impl idx oc ia tape sbuf cap 0 m).
Proof using AF MSET PARSE0 AFV.
  intros Σ3 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s1v t3 t4 t5 t6 F fc m
    lo RES P cap impl idx oc ia tape sbuf BUF L jf jr p1 p17 p57 p12 p28 p50
    FDO MST ECAP BUFR ART0 MI0 ST0 FR0 PC0 FOBJ0 IC0 RC0 LIB0 LV3 LPOS IM16 IX16 OC16 IA16 TP16 SB16
    LVB RLO RHI LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.
  pose proof (af_sp0_range RT AF Σ3 m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ3 m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  destruct (cap_arith 0 0 cap ECAP ltac:(lia) ltac:(lia))
    as (CAP & TC1 & TC2 & SC1 & SC2 & SC8 & IC1' & IC2' & IC3' & ETAPE & EIDX).
  pose proof (al_sbuf_bounds cap CAP) as SBB.
  pose proof FOBJ0 as (P8 & _ & (f & k & INF & FLO & FHI) & _). change ((80 + 7) / 8) with 10 in FHI.
  pose proof (fframe_ranges RT AF Σ3 m f k ART0 INF) as (F0 & F1 & FSZ & _).
  pose proof (af_frames_align RT AF Σ3 m f k ART0 INF) as (_ & FSEG).

  assert (INA : In (ia, 1024) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INO : In (oc, 8192) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INX : In (idx, sc_idx cap) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INM : In (impl, 96) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INT : In (tape, al_tape cap) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  assert (INS : In (sbuf, al_sbuf cap) (rt_live RT Σ3)) by (rewrite LV3; cbn [In]; tauto).
  pose proof (af_live_range RT AF Σ3 m impl 96 ART0 INM) as (IM0 & IM1 & IMS).
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
  pose proof (pi_walk9 RES P BUF 0 impl z8 z8 z8 z8 p1 p17 p57 p12 p28 p50 (Z_to_bv 64 12) (Z_to_bv 64 tape) (Z_to_bv 64 sbuf) (Z_to_bv 64 cap)
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

  pose proof (live_disj_nth RT AF Σ3 m1 3 2 impl 96 idx (sc_idx cap) ART1) as DTI. rewrite LV3 in DTI. specialize (DTI eq_refl eq_refl ltac:(discriminate)).
  rewrite <- EWS in DTI.
  assert (ST1' : stk asegs m1 lo (bv_unsigned (Z_to_bv 64 (usp + -112)))) by (rewrite EU2; exact ST1).
  assert (LOR' : lo + PARSE_STACK <= bv_unsigned (Z_to_bv 64 (usp + -112))) by (rewrite EU2; ul).
  assert (SPT' : bv_unsigned (Z_to_bv 64 (usp + -112)) + 16 <= USTACK_TOP) by (rewrite EU2; ul).
  assert (SPA2' : bv_unsigned (Z_to_bv 64 (usp + -112)) mod 16 = 0) by (rewrite EU2; exact SPA2).
  assert (INX' : In (idx, 4 * Z.of_nat (length ws0)) (rt_live RT Σ3)) by (rewrite EWS; exact INX).
  apply (PARSE0 Σ3 PMc (Z_to_bv 64 0xb58d0) (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 RES) s1v
           (Z_to_bv 64 impl) (Z_to_bv 64 BUF) (Z_to_bv 64 0) (Z_to_bv 64 (P + 24)) (Z_to_bv 64 0xe2cdc) a5 a6 a7
           (Z_to_bv 64 0) (Z_to_bv 64 BUF) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) (Z_to_bv 64 (P + 24))
           (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6 F fc m1 lo
           impl (P + 24) idx BUF tape sbuf oc ia ws0 (roundup64 (cap + 3)) (al_sbuf cap)
           (Z_to_bv 64 0x164ad0) (Z_to_bv 64 cap) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) p12 p28 p50 FDO MST
           eq_refl eq_refl eq_refl eq_refl eq_refl FRM BUFR ltac:(clear - LWZ IC1'; lia) ltac:(clear - LWZ IC2'; lia) ART1 MI1 ST1' LOW LOR' SPT' SPA2' INM INX'
           (M8 _ IM16) (M8 _ IX16) DTI IC1 ARR1);
    [split; [exact Hc1'| apply (cfrm0_of_asta RT Σ3 PMc (eq _) c1 Hc1'); intros ms0 <-; exact FRM] |].
  intros c2 ((Σ4 & Hc2 & FRS4 & LV4 & SP4 & CR4) & FC2).
    destruct (ASTA_unpack_f RT Σ4 _ _ c2 Hc2 FC2) as (ms2 & (m2 & v & RS2 & V13 & OK2 & (ART2 & MI2 & ST2) & PRES2 & (nsi' & nxt' & bufv' & lenv' & docv' & IC2)) & FRM2 & Hc2'). clear Hc2.
    assert (V64 : bv_unsigned v < 64) by (rewrite V13; lia). assert (VN : bv_unsigned v <> 0) by (rewrite V13; lia).
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
    assert (CRF : rt_credit RT Σ3 - 0 <= rt_credit RT Σ4) by (clear - CR4; lia).

      pose proof (pi_walk10b RES P BUF 0 v (Z_to_bv 64 (usp + -112)) gp (Z_to_bv 64 0x6a7e68) u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 s1v (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap) u3 u4 u5 u6 F2 fc2 m2
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

Theorem pid_main0 : forall (Σ2 : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) F' fc' (m2 : mem) (lo RES P d cap impl idx oc ia tape sbuf : Z)
    (L : list (Z * Z)) (jr j p1 p17 p57 p12 p28 p50 : list byte),
  fdfs_only PMc -> mat_stable PMc -> cap = 32 -> 0 <= d < 2^64 ->
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
  Z.of_nat (length (rt_live RT Σ2)) < LIVE_MAX ->
  bv_unsigned sp <= RES -> RES + 40 <= USTACK_TOP ->
  rt_sp0 RT Σ2 - STACK_WIN <= lo -> lo + PID_STACK <= bv_unsigned sp -> bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> frm0 fc' ->
  cps_f (ASTA RT Σ2 PMc (eq (MS (mkR (Z_to_bv 64 0xb5a5c) (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 (Z_to_bv 64 RES) s1
                                     (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                     (Z_to_bv 64 0) (Z_to_bv 64 d) (Z_to_bv 64 (P + 8)) (Z_to_bv 64 P) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 cap)
                                     (Z_to_bv 64 (P + 24)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ((P + 8) / 8 + 2147450880)) t3 t4 t5 t6)
                                F' (Z_to_bv 64 0xb5a5c) fc' None m2 (seg_rom asegs))))
        (pid_post RT Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lo RES P L impl idx oc ia tape sbuf cap 0 m2).
Proof using AF MSET PARSE0 AFV.
  intros Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m2
    lo RES P d cap impl idx oc ia tape sbuf L jr j p1 p17 p57 p12 p28 p50
    FDO MST ECAP DR ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LPOS IM16 IX16 OC16 IA16 TP16 SB16 LVB RLO RHI LOW LOR SPT SPA FRM.
  intros T c (Hc & FC0) Hk.

  pose proof (pi_walk4s RES P d 0 cap (Z_to_bv 64 (bv_unsigned sp + -112)) gp (Z_to_bv 64 0x6a7e68) t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F' fc' m2 ltac:(lia)) as W4.
  lazymatch type of W4 with evt asegs _ ?X =>
    assert (W4' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W4) end.
  clear W4.
  apply (cps_realizes asegs _ _ _ c (asta_evt_c RT AF Σ2 PMc _ _ MST W4') Hc). clear W4'. intros c3 Hc3.
  exact (pid_tail0 Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m2 lo RES P cap impl idx oc ia tape sbuf d L j jr
           p1 p17 p57 p12 p28 p50 FDO MST ECAP DR ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LPOS IM16 IX16 OC16 IA16 TP16 SB16 LVB RLO RHI LOW LOR SPT SPA FRM
           T c3 (conj Hc3 (cfrm0_of_asta RT Σ2 PMc (eq _) c3 Hc3 ltac:(intros ms0 <-; exact FRM))) Hk).
Qed.

End Pid0.

Section Pid0Ok.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis RTF : rt_contracts_f RT.
Hypothesis PARSE0 : parse0_cps RT.
Hypothesis ALLOC : allocate_cps RT.
Hypothesis CREATE : create_cps RT.
Hypothesis AFV : forall Σ m, ART RT Σ m -> vt_dpi m.
Hypothesis AFI : forall Σ m, ART RT Σ m -> vt_impl m.

Local Ltac ul := unfold PID_STACK in *; unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; lia.

Theorem pid0_ok : pid0_cps RT sj_lib.
Proof using AF RTF PARSE0 ALLOC CREATE AFV AFI.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P RES p1 p17 p57 jr lo
    FDO MST -> -> -> -> -> -> -> FOBJ0 PINIT RLO RHI RC0 LVPOS LVB CR0 LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM.
  rewrite (pid_costA_split 0) in CR0. change (Z.max 0 32) with 32 in CR0.
  assert (PC6 : 0 <= pid_cost6 32 /\ 0 <= S2A_COST 0).
  { pose proof (al_sbuf_bounds 32 ltac:(change (2^26) with 67108864; lia)) as B1. pose proof (al_tape_bounds 32 ltac:(change (2^26) with 67108864; lia)) as B2.
    pose proof (sc_idx_bounds 32 ltac:(lia)) as B3.
    unfold pid_cost6, S2A_COST, Sj_num_iface.NUMA_CREDIT.
    pose proof (mcost_nonneg (al_sbuf 32) ltac:(lia)). pose proof (mcost_nonneg (al_tape 32) ltac:(lia)). pose proof (mcost_nonneg 96 ltac:(lia)).
    pose proof (mcost_nonneg (sc_idx 32) ltac:(lia)). pose proof (mcost_nonneg 8192 ltac:(lia)). pose proof (mcost_nonneg 1024 ltac:(lia)).
    pose proof (mcost_nonneg (0 + 64) ltac:(lia)). lia. }
  intros T c HcF Hk.
  pose proof (pid_front RT AF ALLOC (getact_ok RT AF) CREATE AFI Σ PMc ra sp gp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P RES 0
                [] p1 p17 p57 jr lo FDO MST) as PF.
  cbn [length] in PF. change (Z.of_nat 0) with 0 in PF. change (Z.max 0 32) with 32 in PF.
  apply (PF ltac:(lia) ltac:(apply bytes_at_nil; lia) ltac:(right; split; [reflexivity| unfold SEGTOP_A; lia]) FOBJ0 PINIT RLO ltac:(ul) RC0
           ltac:(unfold LIVE_MAX in *; lia) ltac:(lia) LIB0 ART0 MI0 ST0 LOW LOR SPT SPA FRM T c HcF). clear PF.
  intros c2 ((Σ2 & impl & idx & oc & ia & tape & sbuf & Hc2 & LV2 & FRS2 & SP2 & CR2 & (IM0 & IM16) & (IX0 & IX16) & (OC0 & OC16) & (IA0 & IA16) & (TP0 & TP16) & (SB0 & SB16)) & FC2).
  destruct (ASTA_unpack_f RT Σ2 _ _ c2 Hc2 FC2) as (ms2 & (m2 & u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & F2 & fc2 & j & q1 & q17 & q57 & q12 & q28 & q50
                                                    & -> & ART2 & MI2 & ST2 & FR2 & PC2 & FOBJ2 & IC2 & RC2 & BS2 & LIB2 & CH2) & FRM2 & Hc2'). clear Hc2.
  cbn [ms_fcsr] in FRM2. cbn [length] in Hc2'. change (Z.of_nat 0) with 0 in Hc2'.
  assert (LOW2 : rt_sp0 RT Σ2 - STACK_WIN <= lo) by (rewrite SP2; exact LOW).
  apply (pid_main0 RT AF (rf_asan_memset RT RTF) PARSE0 AFV
           Σ2 PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u0 u1 u2 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 F2 fc2 m2 lo RES P 0 32 impl idx oc ia tape sbuf
           (rt_live RT Σ) jr j q1 q17 q57 q12 q28 q50 FDO MST eq_refl ltac:(lia) ART2 MI2 ST2 FR2 PC2 FOBJ2 IC2 RC2 LIB2 LV2 LVPOS IM16 IX16 OC16 IA16 TP16 SB16);
    [rewrite LV2; cbn [length]; unfold LIVE_MAX in *; lia| exact RLO| exact RHI| exact LOW2| exact LOR| exact SPT| exact SPA| exact FRM2
    | split; [exact Hc2'| apply (cfrm0_of_asta RT Σ2 PMc (eq _) c2 Hc2'); intros ms0 <-; exact FRM2] |].
  intros c' ((Σ' & Hc' & LV' & FRS' & SP' & CR') & FC'). apply Hk. split; [| exact FC'].
  exists Σ', impl, idx, oc, ia, tape, sbuf.
  split; [| split; [rewrite LV'; exact LV2| split; [repeat split; assumption| split; [rewrite FRS'; exact FRS2| split; [rewrite SP'; exact SP2|
            rewrite CR2 in CR'; rewrite pid_costA_split; change (Z.max 0 32) with 32; lia]]]]].
  eapply ASTA_conseq; [exact Hc'|]. intros ms (v & m' & RS' & AFT' & PRES' & RC' & LIB' & PD' & ST'). exists v, m'.
  split; [exact RS'|]. split; [exact AFT'|]. split; [| split; [exact RC'| split; [exact LIB'| split; [exact PD'| exact ST']]]].
  intros a Ha Hout. rewrite (PRES' a); [exact (CH2 a Ha Hout)| rewrite FRS2; exact Ha| exact Hout].
Qed.

End Pid0Ok.
