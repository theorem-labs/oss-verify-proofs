(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import ITree Nodes Decode Arr InitMem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg AProto ABase ABytes AQConst ADepot_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import StepF.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import AKit AKit2 AKitQ F_apoison F_aalloc_s F_aalloc1 F_afree_iseg F_afree_front F_afree_tail
     F_aenqueueR F_afree_tailR F_afree_icpt F_afree_icptR F_afreeC_iface F_afree_icptC F_afree_tailRC.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import LiaTuningK.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
(* [comment removed for export] *)
Local Ltac band_lin :=
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Ltac qlia := first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
                         | LiaTuning.zify_prune; Zify.zify; xlia zchecker ].
Local Ltac leaf2 := first [ left; qlia | right; qlia | qlia ].
Local Ltac band_leaf :=
  first [ leaf2
        | match goal with B : sclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold sclr, KLS in B'; destruct B' as [B'|B']; leaf2 end
        | match goal with B : iclr ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold iclr, AIMG_LO, AIMG_HI in B'; destruct B' as [_ [B'|B']]; leaf2 end
        | match goal with B : ablk ?a _ |- context [?a] =>
            let B' := fresh "BB" in pose proof B as B'; unfold ablk, KLS, AIMG_HI in B'; destruct B' as [[? B']|[B' ?]]; leaf2 end
        | lia ].
Local Ltac band_disj := cbn [disjoint_from fst snd]; repeat match goal with |- _ /\ _ => split end; first [exact I | band_leaf].
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6443008 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6443008 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

Notation freeC_W L sp t hm n lst ek g :=
  ([(bv_unsigned sp - 4096, bv_unsigned sp); (0xd0f00, 0xd0f00 + 0x81030); (0x15f788, 0x15f788 + 4);
    (t + 3168, t + 3169); (hm, hm + 4); (hm + 16, hm + 24); (t + 2800, t + 2800 + 368);
    (ADEPOT_LO, ADEPOT_HI); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608);
    (shad (hm + 16), shad (hm + 16) + shlen (rup n 8)); (t + 80, t + 112); (t + 2128, t + 2132); (t + 2784, t + 2792);
    (lst, lst + qsz lst); (ek_b ek lst, ek_b ek lst + 8192);
    (0xcca08, 0xcca08 + 4); (0xcca10, 0xcca10 + 32); (dk_glst g lst, dk_glst g lst + 8)]%Z) (only parsing).

Section CANSEC1. Context {rc : runConstT}.
Theorem free_from_refill_torec : forall DI, free_from_refill_torec_stmt DI.
Proof.
  intros DI. unfold free_from_refill_torec_stmt.
  intros until trt. cbv zeta.
  intros ST CEIL LO MI SS TB LTB FRS FRP FRE QK HD FC IDR N AL HLO HHI HCE SH QC NB QB QBN FST LST T0 T1 TAL DHT STATS LSJ UW FL IAS IAM
         FULL SB CR CH LCH CNT NTH IXS STS HBE BJ SBP B0 BL1 DTB DTL DBL DHB DHL RB ES DK DS DEP N0 N1 R0 R1 DTN DTS SP47
         RIMG RSTK RT RH RSH NI SI TI. band_lin. band_int TI. pose proof (ablk_lin _ _ HLO) as (HL1 & HL2 & HL3 & HL4). unfold AIMG_HI in HL1. band_int HLO. band_int T0. band_int N0. band_int R0.   (* [comment removed for export] *)
  assert (RUP : n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0) by (clear -N; unfold rup; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  assert (SHB : 2148256256 <= shad (hm + 16) /\ shad (hm + 16) + shlen (rup n 8) <= 0x10007fff8000 /\ 0 < shlen (rup n 8)).
  { clear -N HLO HL1 HHI HCE. unfold shad, shlen, ASHOFF, rup in *. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8. unfold Q_MAX in *. Z.div_mod_to_equations. lia. }
  pose proof (dk_preC_pure _ g RNG L t lst hm (qb + (n + 8192)) m DK DS TI ltac:(unfold AIMG_HI; lia) NI SI
                DHL DTL ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); destruct FULL as (_ & _ & _ & _ & L0 & _); exact (proj1 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(cbn [ek_seps] in ES; destruct full; [destruct ES as (_ & _ & _ & S4); exact (proj2 (proj2 (S4 eq_refl))) | destruct FULL as [_ ->]; unfold AIMG_HI in *; lia])
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & L1 & _) | destruct FULL as [_ ->]]; unfold AIMG_HI in *; atop_facts; lia)
                ltac:(destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right | destruct FULL as [_ ->]; left]; unfold AIMG_HI in *; lia))
    as (DF1 & DF2 & DF3 & DF4 & DG0 & DG1 & DG2).
  cbn [ek_seps] in ES. destruct ES as (SB1 & SB2 & SB3 & SL).
  assert (PL2 : lst = 0 \/ 0x10007fff8000 <= lst) by (destruct full; [destruct FULL as (_ & _ & _ & _ & L0 & _); right; exact L0 | destruct FULL as [_ E0]; left; exact E0]).
  assert (PLB : lst + 8192 <= ATOP) by (destruct full; [destruct FULL as (_ & _ & _ & _ & _ & L1 & _); exact L1 | destruct FULL as [_ E0]; rewrite E0; atop_facts; lia]).
  pose proof (qsz_int lst ltac:(clear -PL2; lia) ltac:(clear -PLB; atop_facts; lia)) as (zq & QZ0 & QZ1 & QZ2 & QZ3).   (* [comment removed for export] *)
  unfold AIMG_HI, AFREE_SYM, AFREE_PC in *.
  word_range sp SPR.
  box DHT. box DTN. box DTS. box DTB. box DTL. box DBL. box DHB. box DHL. box SB1. box SB2. box SB3. box DF1. box DF2. box DF3. box DF4. box DG2. box PL2.
  (* [comment removed for export] *)
  set (sp1 := Z_to_bv 64 (bv_unsigned sp + -2128)) in *.
  assert (Hsp : bv_unsigned sp1 = bv_unsigned sp + -2128) by (subst sp1; apply unsigned_lit; lia).
  replace (bv_unsigned sp + -2272) with (bv_unsigned sp1 + -144) in * by lia.
  replace (bv_unsigned sp + -2208) with (bv_unsigned sp1 + -80) in * by lia.
  (* [comment removed for export] *)
  eapply evtF_cut.
  { eapply (put_from_refill_torec full g t hm lst b RNG (Z_to_bv 64 0x55074) sp1 gp tp sp (Z_to_bv 64 (hm + 16)) (Z_to_bv 64 (t + 208)) sp1
              (Z_to_bv 64 0x55004) (Z_to_bv 64 1) sp1 (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11
              ra0 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 F fc m n nb fst0 qb b1 actx lo nx bsz cnt spacebeg maxc csz stj idxw chunks hs j0).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => first [exact ST | exact IAS]
         | |- mem_inv _ _ => exact MI
         | |- if _ then _ else _ => exact FULL
         | |- dk_preC _ _ _ _ _ _ _ _ => exact DK
         | |- @eq word _ _ => reflexivity
         | |- @eq Z _ _ => first [exact HBE | lia]
         | |- ex _ => exact BJ
         | |- _ \/ _ => first [ub DHT; lia_keep1 | ub DTB; lia_keep1 | ub DTL; lia_keep1 | ub DBL; lia_keep1 | ub DHB; lia_keep1 | ub DHL; lia_keep1]
         | |- rng _ _ _ => solve_rng
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HD
         | |- rw_cells _ _ (shad _) _ => exact SH
         | |- rw_cells _ _ (_ + 80) _ => exact QC
         | |- rw_cells _ _ (_ + 2128) _ => exact CR
         | |- rw_cells _ _ (_ + 2784) _ => exact STS
         | |- rw_cells _ _ (_ + -80) _ => exact FRP
         | |- iclr _ _ => exact TI
         | |- rw_cells _ _ (_ + -144) _ => exact FRE
         | |- u32arr _ _ _ _ => exact CH
         | |- nth_error _ _ = _ => exact NTH
         end.
    all: try eassumption. all: try (unfold AIMG_HI, Q_MAX in *; lia).
    all: match goal with |- ?G => idtac "REMQ" G end. }
  cbv beta. intros ms2 PP. unfold put_torec_post in PP.
  destruct PP as (t0b & t1b & t2b & xs0 & xs1 & xs2 & xs3 & xs4 & xs5 & xs6 & a4b & a5b & a6b & a7b & t3b & t4b & t5b & t6b & m2
                  & -> & MUp & WMp & MIp & STp & FRP2 & SH2 & HD2 & QC2 & EKP & DKP).
  (* [comment removed for export] *)
  cbn [ek_b] in MUp.
  xport FC MUp WMp ltac:(ub DHT; ub DHB; ub DHL; ub DF1; lia_keep4).
  xport STATS MUp WMp ltac:(rewrite LSJ; ub DTB; ub DTL; ub DF2; lia_keep3).
  xport UW MUp WMp ltac:(ub DTB; ub DTL; ub DF2; lia_keep3).
  xport FL MUp WMp ltac:(ub DG2; ub PL2; lia_keep2). xport IAS MUp WMp ltac:(ub DG2; ub PL2; lia_keep2).
  xport SS MUp WMp ltac:(lia). xport TB MUp WMp ltac:(rewrite LTB; lia). xport FRS MUp WMp ltac:(lia).
  assert (IAM2 : forall j, 0 <= j < 32768 -> bytes_at bsegs m2 (0xd0f08 + 8 * j) (le8 (Z_to_bv 64 0))).
  { (intros j Hj; eapply bytes_at_agree; [exact (IAM j Hj)|];
    intros i Hi; apply MUp; cbn [outside]; rewrite length_le8 in Hi; rewrite wa_unsigned by lia; ub DG2; ub PL2; lia_keep2). }
  clear IAM.
  assert (DEP2 : ADEPOT DI L m2).
  { eapply (adi_frame DI); [exact DEP | exact MUp | exact WMp |].
    (repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq;
      first [lia | ub DTN; ub DTS; lia_keep2 | ub SB2; ub SB3; lia_keep2 | ub DF3; ub DF4; ub DG2; lia_keep3
            | destruct full; [destruct (SL eq_refl) as (_ & S6 & S7); lia | destruct FULL as [_ LST0]; lia] ] |]); apply Forall_nil). }
  clear DEP.
  (* [comment removed for export] *)
  subst sp1. rewrite ?unsigned_lit in STp by lia. rewrite ?unsigned_lit in MUp by lia. rewrite ?unsigned_lit in FRP2 by lia.
  replace (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2128)) - 80)) with (Z_to_bv 64 (bv_unsigned sp - 2128 - 80)) by (f_equal; rewrite unsigned_lit by lia; lia).
  apply rw_cells_of_u64arr in TB. rewrite LTB in TB.
  assert (MU : munch (freeC_W L sp t hm n lst (EkNew full nx bsz cnt maxc csz stj idxw chunks spacebeg b hs) g) m m2).
  { eapply munch_weaken; [| exact MUp]. cbn [ek_b]. solve_sub_fp sp. }
  apply evtF_done. unfold free_torec_post. cbv zeta.
  exists id, t0b, t1b, t2b, xs0, xs1, xs2, xs3, xs4, xs5, xs6.
  do 6 eexists. exists sp. do 9 eexists. exists m2, sj. do 2 eexists. exists junk2.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WMp|]. split; [exact MIp|]. split; [exact STp|]. split; [exact IDR|].
  split; [exact FRP2|].
  split; [exact SS|]. split; [reflexivity|].
  split; [replace (bv_unsigned sp - 2128 + 16) with (bv_unsigned sp + -2128 + 16) by lia; exact TB|]. split; [reflexivity|].
  split; [exact FRS|].
  split; [exact HD2|]. split; [exact FC|]. split; [exact SH2|]. split; [exact QC2|]. split; [exact EKP|]. split; [exact DKP|].
  split; [exact STATS|]. split; [exact LSJ|]. split; [exact UW|]. split; [exact FL|]. split; [exact IAS|]. split; [exact IAM2|].
  exact DEP2.
  Unshelve. all: try exact ST; try exact STp.
Qed.
End CANSEC1.
