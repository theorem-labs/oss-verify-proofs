(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Agent Require Import F_malloc_free F_malloc_fast F_malloc_enframe F_malloc_entry MallocKit_A MallocKit_B3 MallocRep MallocFacts_B MallocFacts_inv2.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RMallocRep RMallocTree RMallocKit_A RMallocKit_B RF_get_meta RF_enframe RMalloc_fp F_memcpy RF_realloc_A RF_realloc_B RF_realloc_C
  RF_aalloc_A RF_aalloc_B RF_aalloc_C.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Inv MI_Kit MI_Geom MI_Ext MI_Pres2 MI_WFree MI_WGroup MI_WMalloc MI_WRelay MI_WRelay2.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import StoreDj.
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaRel.
Local Ltac lia ::=
  dle_wrap ltac:(first [ n8v_prune1p; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | n8v_prune1; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | n8v_prunep; Zify.zify; xlia zchecker
        | zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ]).
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section BLK.
  Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.
  Variables (st : mstate) (L : mled) (BL : list blk) (LS : lhead -> list aptr).
  Variables (c : cptr) (off n : Z) (mm bm : aptr) (i ai : Z) (a : aptr) (ar : area) (ka : Z) (r : region).
  Hypothesis INV : INVL x0 st L BL LS.
  Hypothesis Hk : In ((c, off), n) BL.
  Hypothesis BF : blk_facts st c off n mm bm i ai a ar ka.
  Hypothesis Hr : s_regions st !! (fst bm) = Some r.

  Definition bk_stride : Z := get_stride (MR st mm).
  Definition bk_P : Z := r_base r + snd c + UNIT * off.          (* [comment removed for export] *)
  Definition bk_E : Z := r_base r + snd c + bk_stride - IB.      (* [comment removed for export] *)
  Definition bk_res : Z := bk_E - bk_P - n.                      (* [comment removed for export] *)
  Definition bk_q : Z := (snd c + UNIT * off - snd bm - UNIT) / UNIT.   (* [comment removed for export] *)
  Definition bk_b3 : Z := i + 32 * Z.min bk_res 5.              (* [comment removed for export] *)
  Definition bk_mword : Z := meta_word (MR st mm).
  Definition bk_sc : Z := m_sizeclass (MR st mm).

  Let IM := proj1 (proj2 (proj2 INV)).
  Let IG := proj1 (proj2 (proj2 (proj2 (proj2 INV)))).
  Let IS := proj1 (proj2 (proj2 (proj2 (proj2 (proj2 INV))))).

  Lemma bk_Kr : r_kind r = RKGroup.
  Proof. destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as (r' & Hr' & K). rewrite Hr in Hr'. congruence. Qed.

  Lemma bk_hosts : hosts st bm mm.
  Proof. exists ai. exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF). Qed.

  Lemma bk_c : c = (fst bm, sstart (MR st mm) i). Proof. exact (bf_c _ _ _ _ _ _ _ _ _ _ _ BF). Qed.
  Lemma bk_gbase : gbase (MR st mm) = bm. Proof. exact (MI_WFree.gbase_bm st c off n mm bm i ai a ar ka BF). Qed.
  Lemma bk_snd_c : snd c = snd bm + UNIT + bk_stride * i.
  Proof. rewrite bk_c. cbn [snd]. unfold sstart. rewrite bk_gbase. reflexivity. Qed.

  Lemma bk_stride_facts : 16 <= bk_stride /\ bk_stride mod 16 = 0.
  Proof. pose proof (bf_stride _ _ _ _ _ _ _ _ _ _ _ BF) as [A B]. unfold bk_stride, UNIT in *. lia. Qed.

  Lemma bk_q16 : UNIT * bk_q = bk_stride * i + UNIT * off /\ 0 <= bk_q < 2 ^ 16.
  Proof. exact (MI_WFree.q16 st c off n mm bm i ai a ar ka BF). Qed.

  Lemma bk_res_nonneg : 0 <= bk_res.
  Proof.
    unfold bk_res, bk_E, bk_P. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF).
    unfold bk_stride, IB, UNIT in *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_region : rregions_wf st ->
    0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= snd bm /\ snd bm mod 16 = 0
    /\ snd bm + 16 + bk_stride * (m_last_idx (MR st mm) + 1) <= round_up_pg (r_len r)
    /\ r_base r + round_up_pg (r_len r) <= hceil.
  Proof.
    intros (_ & WR & _ & _ & WG). destruct (WR _ _ Hr) as (B0 & BAL & L0 & BC & _).
    pose proof (bf_b16 _ _ _ _ _ _ _ _ _ _ _ BF) as [S0 S16].
    destruct (MallocFacts_inv2.group_in_region x0 st L BL LS INV bm mm bk_hosts) as (r' & Hr' & _ & _ & GE).
    rewrite Hr in Hr'. injection Hr' as <-.
    unfold gend, sstart, cnt_of in GE. rewrite bk_gbase in GE. unfold bk_stride, UNIT in *.
    repeat split; try assumption; lia.
  Qed.

  Lemma bk_span : 0 <= bk_stride * i /\ bk_stride * i + bk_stride <= bk_stride * (m_last_idx (MR st mm) + 1).
  Proof.
    pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof bk_stride_facts as [S _].
    split; [apply Z.mul_nonneg_nonneg; lia|].
    rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma le4_byte_of v : 0 <= v < 2 ^ 32 ->
    le4 (wz v) = [b8 (byte_of v 0); b8 (byte_of v 1); b8 (byte_of v 2); b8 (byte_of v 3)].
  Proof.
    intros Hv. rewrite le4_bytes by lia. unfold byte_of. change 255 with (Z.ones 8). rewrite !Z.land_ones, !Z.shiftr_div_pow2 by lia.
    rewrite Z.mul_0_r, Z.mul_1_r. change (2 ^ 0) with 1. change (2 ^ (8 * 2)) with 65536. change (2 ^ (8 * 3)) with 16777216. change (2 ^ 8) with 256.
    rewrite Z.div_1_r. rewrite (Z.mod_small (v / 16777216) 256) by (Z.div_mod_to_equations; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_ranges : 0 <= i <= 31 /\ 0 <= off <= 258 /\ 0 <= n /\ UNIT * off + n <= bk_stride - IB
    /\ 0 <= bk_res /\ bk_res <= bk_stride - IB /\ 0 <= bk_b3 < 256 /\ Z.land bk_b3 31 = i /\ Z.shiftr bk_b3 5 = Z.min bk_res 5
    /\ (bk_sc < 48 -> bk_stride < 2 ^ 20).
  Proof.
    pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF).
    pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF). pose proof bk_res_nonneg.
    fold bk_stride in *.
    assert (B3 : 0 <= bk_b3 < 256) by (unfold bk_b3; lia).
    repeat split; try lia.
    - unfold bk_res, bk_E, bk_P, IB, UNIT in *. lia.
    - unfold bk_b3. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. change (2 ^ 5) with 32.
      replace (i + 32 * Z.min bk_res 5) with (i + Z.min bk_res 5 * 32) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
    - unfold bk_b3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 5) with 32. Z.div_mod_to_equations. lia.
    - intros SC. unfold bk_stride. exact (small_stride x0 st L BL LS bm mm INV bk_hosts SC).
  Qed.

  Section READS.
    Variable m : mem.
    Hypothesis MRm : rmrep st m.

    Let SHOK := bf_shadow _ _ _ _ _ _ _ _ _ _ _ BF.

    (* [comment removed for export] *)
    Lemma bk_known_read o v : 0 <= o < round_up_pg (r_len r) -> known st (fst bm, o) v ->
      ov_read_bytes rsegs m (wa (r_base r + o)) 1 = Some [b8 v] /\ bytes_at rsegs m (r_base r + o) [b8 v] /\ 0 <= v < 256.
    Proof.
      intros Ho K. unfold known, SHd in K. cbn [fst snd] in K.
      destruct (rmrep_shadow_read st m (fst bm) r o v MRm Hr bk_Kr Ho K) as [R V].
      pose proof MRm as (_ & _ & _ & _ & _ & SH). destruct (SH _ _ Hr bk_Kr) as [_ HB]. destruct (HB o v Ho K) as [B _].
      auto.
    Qed.

    (* [comment removed for export] *)
    Lemma bk_reads : rregions_wf st ->
      let po := snd c + UNIT * off in
      let e := snd c + bk_stride - IB in
         ov_read_bytes rsegs m (wa (bk_P - 4)) 1 = Some [b8 0]
      /\ ov_read_bytes rsegs m (wa (bk_P - 3)) 1 = Some [b8 bk_b3]
      /\ bytes_at rsegs m (bk_P - 3) [b8 bk_b3]
      /\ ov_read_bytes rsegs m (wa (bk_P - 2)) 2 = Some (le2 (wz bk_q))
      /\ (160 <= bk_b3 -> Z.shiftr bk_b3 5 = 5 /\ 5 <= bk_res < 2 ^ 32
            /\ ov_read_bytes rsegs m (wa (bk_E - 4)) 4 = Some (le4 (wz bk_res))
            /\ ov_read_bytes rsegs m (wa (bk_E - 5)) 1 = Some [b8 0])
      /\ ov_read_bytes rsegs m (wa (bk_E - bk_res)) 1 = Some [b8 0]
      /\ ov_read_bytes rsegs m (wa bk_E) 1 = Some [b8 0]
      /\ wr_at rsegs m (bk_P - 3) (bk_E - bk_P + 3).
    Proof.
      intros WF po e. pose proof (bk_region WF) as (B0 & BAL & S0 & S16 & SPAN & BC). pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & R0 & RS & B3 & L31 & SH5 & SST).
      pose proof bk_span as [SK SKL]. pose proof bk_stride_facts as [ST16 STM]. pose proof bk_snd_c as SC.
      destruct SHOK as (K4 & K3 & K2 & K1 & QR & K5 & KC & _). cbn [bslot boff bsize fst snd] in K4, K3, K2, K1, QR, K5, KC.
      assert (FC : fst c = fst bm) by (rewrite bk_c; reflexivity). rewrite FC in K4, K3, K2, K1, K5, KC.
      change (get_stride (MR st mm)) with bk_stride in K5, KC. rewrite bk_gbase in K2, K1, QR.
      fold bk_q in K2, K1, QR.
      assert (ERS : snd c + bk_stride - IB - (snd c + UNIT * off) - n = bk_res) by (unfold bk_res, bk_E, bk_P; lia). rewrite ERS in K3, K5, KC.
      fold bk_b3 in K3.
      assert (PO : 16 <= snd c + UNIT * off /\ snd c + bk_stride - IB + 1 <= round_up_pg (r_len r)) by (rewrite SC; unfold UNIT, IB in *; lia).
      split. { destruct (bk_known_read (snd c + UNIT * off - 4) 0 ltac:(unfold UNIT, IB in *; lia) K4) as (R & _). unfold bk_P. replace (r_base r + snd c + UNIT * off - 4) with (r_base r + (snd c + UNIT * off - 4)) by lia. exact R. }
      split. { destruct (bk_known_read (snd c + UNIT * off - 3) bk_b3 ltac:(unfold UNIT, IB in *; lia) K3) as (R & _). unfold bk_P. replace (r_base r + snd c + UNIT * off - 3) with (r_base r + (snd c + UNIT * off - 3)) by lia. exact R. }
      split. { destruct (bk_known_read (snd c + UNIT * off - 3) bk_b3 ltac:(unfold UNIT, IB in *; lia) K3) as (_ & B & _). unfold bk_P. replace (r_base r + snd c + UNIT * off - 3) with (r_base r + (snd c + UNIT * off - 3)) by lia. exact B. }
      split. { destruct (rmrep_shadow_read2 st m (fst bm) r (snd c + UNIT * off - 2) (byte_of bk_q 0) (byte_of bk_q 1) MRm Hr bk_Kr ltac:(unfold UNIT in *; lia) ltac:(unfold UNIT, IB in *; lia) K2
                          ltac:(replace (snd c + UNIT * off - 2 + 1) with (snd c + UNIT * off - 1) by lia; exact K1)) as (R & _ & _).
               unfold bk_P. replace (r_base r + snd c + UNIT * off - 2) with (r_base r + (snd c + UNIT * off - 2)) by lia. rewrite R. f_equal.
               rewrite le2_split by lia. unfold byte_of. rewrite Z.mul_0_r, Z.mul_1_r, Z.shiftr_0_r, Z.shiftr_div_pow2 by lia.
               change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. change (2 ^ 8) with 256. f_equal. f_equal. f_equal.
               apply Z.mod_small. pose proof bk_q16. Z.div_mod_to_equations. lia. }
      split. { intros B160. assert (R5 : 5 <= bk_res) by (unfold bk_b3 in B160; lia). destruct (K5 R5) as (E4 & E3 & E2 & E1 & E5 & R32).
               split; [rewrite SH5; lia|]. split; [lia|]. split.
               - destruct (bk_known_read (snd c + bk_stride - IB - 4) _ ltac:(unfold UNIT, IB in *; lia) E4) as (_ & A4 & _).
                 destruct (bk_known_read (snd c + bk_stride - IB - 3) _ ltac:(unfold UNIT, IB in *; lia) E3) as (_ & A3 & _).
                 destruct (bk_known_read (snd c + bk_stride - IB - 2) _ ltac:(unfold UNIT, IB in *; lia) E2) as (_ & A2 & _).
                 destruct (bk_known_read (snd c + bk_stride - IB - 1) _ ltac:(unfold UNIT, IB in *; lia) E1) as (_ & A1 & _).
                 assert (A : bytes_at rsegs m (bk_E - 4) ([b8 (byte_of bk_res 0)] ++ [b8 (byte_of bk_res 1)] ++ [b8 (byte_of bk_res 2)] ++ [b8 (byte_of bk_res 3)])).
                 { unfold bk_E. apply bytes_at_app. split; [replace (r_base r + snd c + bk_stride - IB - 4) with (r_base r + (snd c + bk_stride - IB - 4)) by lia; exact A4|].
                   apply bytes_at_app. split; [cbn; replace (r_base r + snd c + bk_stride - IB - 4 + 1) with (r_base r + (snd c + bk_stride - IB - 3)) by lia; exact A3|].
                   apply bytes_at_app. split; [cbn; replace (r_base r + snd c + bk_stride - IB - 4 + 1 + 1) with (r_base r + (snd c + bk_stride - IB - 2)) by lia; exact A2|].
                   cbn. replace (r_base r + snd c + bk_stride - IB - 4 + 1 + 1 + 1) with (r_base r + (snd c + bk_stride - IB - 1)) by lia. exact A1. }
                 cbn [app] in A. rewrite <- le4_byte_of in A by lia.
                 rewrite <- (Z.add_0_r (bk_E - 4)). rewrite (bytes_at_read rsegs m _ _ 0 4 A) by (rewrite ?length_le4; cbn; lia).
                 rewrite le4_byte_of by lia. reflexivity.
               - destruct (bk_known_read (snd c + bk_stride - IB - 5) _ ltac:(unfold UNIT, IB in *; lia) E5) as (R & _). unfold bk_E.
                 replace (r_base r + snd c + bk_stride - IB - 5) with (r_base r + (snd c + bk_stride - IB - 5)) by lia. exact R. }
      split. { destruct (Z.eq_dec bk_res 0) as [Z0|NZ].
               - rewrite Z0, Z.sub_0_r. pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. rewrite sstart_succ in H0. change (get_stride (MR st mm)) with bk_stride in H0.
                 destruct (bk_known_read (snd c + bk_stride - IB) 0 ltac:(unfold UNIT, IB in *; lia) ltac:(rewrite bk_c; cbn [fst snd]; exact H0)) as (R & _).
                 unfold bk_E. replace (r_base r + snd c + bk_stride - IB) with (r_base r + (snd c + bk_stride - IB)) by lia. exact R.
               - destruct (bk_known_read (snd c + bk_stride - IB - bk_res) _ ltac:(unfold UNIT, IB in *; lia) (KC ltac:(lia))) as (R & _). unfold bk_E.
                 replace (r_base r + snd c + bk_stride - IB - bk_res) with (r_base r + (snd c + bk_stride - IB - bk_res)) by lia. exact R. }
      split. { pose proof (bf_hdr0 _ _ _ _ _ _ _ _ _ _ _ BF) as H0. rewrite sstart_succ in H0. change (get_stride (MR st mm)) with bk_stride in H0.
               destruct (bk_known_read (snd c + bk_stride - IB) 0 ltac:(unfold UNIT, IB in *; lia) ltac:(rewrite bk_c; cbn [fst snd]; exact H0)) as (R & _).
               unfold bk_E. replace (r_base r + snd c + bk_stride - IB) with (r_base r + (snd c + bk_stride - IB)) by lia. exact R. }
      pose proof MRm as (_ & _ & _ & _ & _ & SH). destruct (SH _ _ Hr bk_Kr) as [HW _].
      eapply wr_at_sub; [exact HW| unfold bk_P, UNIT in *; lia| unfold bk_E, bk_P, UNIT, IB in *; lia].
    Qed.

    (* [comment removed for export] *)
    Lemma bk_slack_wr : rregions_wf st -> wr_at rsegs m (bk_P + n) ((- (bk_P + n)) mod 8).
    Proof.
      intros WF. pose proof (bk_region WF) as (B0 & BAL & S0 & S16 & SPAN & BC). pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & _).
      pose proof bk_span as [SK SKL]. pose proof bk_stride_facts as [ST16 STM]. pose proof bk_snd_c as SC.
      pose proof MRm as (_ & _ & _ & _ & _ & SH). destruct (SH _ _ Hr bk_Kr) as [HW _].
      assert (AL : (r_base r + snd c + bk_stride) mod 8 = 0).
      { rewrite SC. apply (proj2 (Z.mod_divide _ 8 ltac:(lia))).
        exists (r_base r / 4096 * 512 + snd bm / 16 * 2 + 2 + bk_stride / 16 * 2 * i + bk_stride / 16 * 2).
        clear - BAL S16 STM. unfold UNIT. Z.div_mod_to_equations. nia. }
      eapply wr_at_sub; [exact HW| unfold bk_P, UNIT in *; clear - S0 SC SK Hoff Hn; lia|].
      unfold bk_P, UNIT, IB in *. clear - AL Hfit Hoff Hn SPAN SKL SC S0 ST16. Z.div_mod_to_equations. lia.
    Qed.
  End READS.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Hypothesis GO : gmeta_ok st mm bm.
  Hypothesis SECR : 0 <= c_secret (ctx st) < 2 ^ 64.

  Lemma bk_area : s_areas st !! (area_of mm) = Some ar /\ a_check ar = c_secret (ctx st) /\ meta_slot st mm /\ 0 <= snd mm.
  Proof.
    destruct (bf_area _ _ _ _ _ _ _ _ _ _ _ BF) as (Ha & Hck & Hal & Hka & Emm).
    assert (EA : area_of mm = a).
    { rewrite Emm. unfold area_of, mslot, aadd. cbn [fst snd]. apply injective_projections; cbn [fst snd]; [reflexivity|].
      unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *.
      replace (snd a + (24 + 40 * ka)) with ((24 + 40 * ka) + (snd a / 4096) * 4096) by (Z.div_mod_to_equations; lia).
      rewrite Z.mod_add, Z.mod_small by lia. Z.div_mod_to_equations; lia. }
    rewrite EA. split; [exact Ha|]. split; [exact Hck|]. split.
    - exists a, ar, ka. rewrite Emm. unfold mslot. auto.
    - rewrite Emm. unfold mslot, aadd. cbn [snd]. unfold AREA_HDR, META_SIZE, NSLOTS, PGSZ in *.
      pose proof (Z.mod_pos_bound (snd a) 4096 ltac:(lia)). destruct (ia_areas _ (proj1 (proj2 INV)) _ _ Ha) as ((ra & _ & _ & _ & P4 & _) & _). unfold PGSZ in P4. lia.
  Qed.

  Lemma bk_guards :
       Z.land bk_b3 31 <= m_last_idx (MR st mm)
    /\ Z.testbit (m_avail (MR st mm)) (Z.land bk_b3 31) = false
    /\ Z.testbit (m_freed (MR st mm)) (Z.land bk_b3 31) = false
    /\ (bk_sc < 48 -> size_class bk_sc * Z.land bk_b3 31 <= bk_q < size_class bk_sc * (Z.land bk_b3 31 + 1))
    /\ (48 <= bk_sc -> bk_sc = 63)
    /\ (m_maplen (MR st mm) <> 0 -> bk_q <= m_maplen (MR st mm) * 256 - 1)
    /\ (m_maplen (MR st mm) = 0 \/ m_last_idx (MR st mm) <> 0 -> bk_sc < 48)
    /\ bk_stride = (if negb (m_maplen (MR st mm) =? 0) && (m_last_idx (MR st mm) =? 0) then 4096 * m_maplen (MR st mm) - 16 else 16 * size_class bk_sc).
  Proof.
    pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & R0 & RS & B3 & L31 & SH5 & SST). rewrite L31.
    pose proof (bf_notA _ _ _ _ _ _ _ _ _ _ _ BF) as NA. pose proof (bf_notF _ _ _ _ _ _ _ _ _ _ _ BF) as NF. unfold tbit in NA, NF.
    pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as SC. pose proof (bf_top _ _ _ _ _ _ _ _ _ _ _ BF) as TOP. pose proof (bf_maplen _ _ _ _ _ _ _ _ _ _ _ BF) as ML.
    pose proof bk_q16 as [Q16 QR]. pose proof bk_stride_facts as [S16 SM]. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as HI.
    destruct (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as [_ LI _ GSC _ _ _ _ _ _ GSTR _ _ _ _ _ _]. fold (MR st mm) in LI, GSC, GSTR.
    unfold bk_sc in *. fold bk_stride in GSTR.
    split; [lia|]. split; [exact NA|]. split; [exact NF|].
    split. { intros LT. destruct SC as [(SCR & SB & SE)|S63]; [| lia]. fold bk_stride in SB, SE.
             pose proof (size_class_range (m_sizeclass (MR st mm)) ltac:(lia)) as SZ.
             apply (guard16_arith (size_class (m_sizeclass (MR st mm))) bk_stride i off n bk_q (m_last_idx (MR st mm))); unfold UNIT, IB in *; try lia.
             destruct SB as [SB|SB]; [left; lia| right; apply size_class_28; lia]. }
    split; [intros GE; destruct SC as [(SCR & _)|S63]; [lia| exact S63]|].
    split. { intros NZ. destruct (TOP NZ) as [SB0 GE]. unfold gend, sstart, cnt_of in GE. rewrite bk_gbase in GE. fold bk_stride in GE.
             replace (m_maplen (MR st mm) * 256) with (m_maplen (MR st mm) * 4096 / 16) by (rewrite <- (Z.div_mul (m_maplen (MR st mm) * 256) 16) by lia; f_equal; lia).
             apply (guard17_arith bk_stride i off n bk_q (m_last_idx (MR st mm)) (m_maplen (MR st mm))); unfold UNIT, IB in *; try lia. }
    split. { intros H. destruct SC as [(SCR & _)|S63]; [lia|]. destruct GSC as [[? ?]|(_ & L0 & MNZ & _)]; lia. }
    unfold bk_stride, get_stride. destruct (m_last_idx (MR st mm) =? 0); destruct (m_maplen (MR st mm) =? 0); cbn [andb negb]; unfold UNIT; lia.
  Qed.

  (* [comment removed for export] *)
  Definition rre_front_post (ra sp gp tp s0 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 s1 s2 : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) (n' : Z) : machine_state -> Prop :=
    fun ms' => exists m1 t4',
      rre_dec_post ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp s0 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4' t5 t6 (wz (conc st mm)) F fc m1 n' bk_P bk_sc bk_E bk_res ms'
      /\ rw_cells rsegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk rsegs m1 lo (bv_unsigned sp + -64)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ rmrep st m1.

  Lemma rre_front : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n' : Z),
    rmrep st m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 64 ->
    a0 = Z_to_bv 64 bk_P -> a1 = Z_to_bv 64 n' -> 1 <= n' < MMAP_THRESHOLD ->
    evt rsegs (rre_front_post ra sp gp tp s0 a0 s3 s4 s5 s6 s7 s8 s9 s10 s11 t5 t6 s1 s2 F fc lo m n')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x27109c) fc None m (seg_rom rsegs)).
  Proof.
    intros until n'. intros RM MI ST CLO LO A0 A1 N.
    pose proof RM as (WF & _). pose proof (bk_region WF) as (B0 & BAL & S0 & S16 & SPAN & BC). pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & R0 & RS & B3 & L31 & SH5 & SST).
    pose proof bk_span as [SK SKL]. pose proof bk_stride_facts as [ST16 STM]. pose proof bk_snd_c as SC. pose proof bk_q16 as [Q16 QR].
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO.
    assert (NUM : bk_P = r_base r + snd c + 16 * off /\ bk_E = r_base r + snd c + bk_stride - 4 /\ bk_res = bk_E - bk_P - n /\ 16 * off + n <= bk_stride - 4)
      by (unfold bk_res, bk_E, bk_P, UNIT, IB in *; repeat split; lia).
    destruct NUM as (EP & EE & ERES & FIT).
    assert (PP : 16 <= snd c + 16 * off /\ snd c + bk_stride - 4 + 1 <= round_up_pg (r_len r)) by (rewrite SC; unfold UNIT in *; lia).
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rre_pro_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo bk_P n');
        [rewrite A0; apply unsigned_lit; rewrite EP; lia| rewrite EP; lia| exact A1| lia| exact ST| lia| exact LO| exact MI]. }
    intros ms1 (a2' & m1 & -> & FR & ST1 & MU & WM & MI1).
    assert (RM1 : rmrep st m1).
    { eapply rmrep_transport_high; [exact RM| exact MU| exact WM|]. intros l h [E1|[]]. inversion E1; subst. lia. }
    (* [comment removed for export] *)
    destruct (bk_reads m1 RM1 WF) as (R4 & R3 & BK3 & R2 & BIG & RR & RE & W).
    destruct bk_area as (Har & Hck & MSL & G0). destruct bk_guards as (G12 & G13 & G14 & G16 & G63 & G17 & G48 & GSTR).
    pose proof (rmrep_meta_chunk st m1 mm RM1 MSL) as MM. unfold meta_cells in MM. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) in MM. cbn [pw oconc] in MM.
    destruct (rmrep_group_read st m1 bm _ RM1 (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as [RG _]. cbn [g_meta pw oconc] in RG.
    pose proof (rmrep_area_check_read st m1 (area_of mm) ar RM1 Har) as RA. rewrite Hck in RA.
    pose proof (rmrep_ctx_secret_read st m1 RM1) as RC.
    pose proof (rmeta_slot_bounds st m1 mm RM1 MSL) as (GB0 & GB1 & GB2 & GB4 & _).
    assert (HBm : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
    pose proof (go_avail _ _ _ GO) as AV. pose proof (go_freed _ _ _ GO) as FRD. pose proof (go_maplen _ _ _ GO) as ML. pose proof (go_freeable _ _ _ GO) as FB.
    fold (MR st mm) in AV, FRD, ML, FB.
    pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as SCc.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rre_meta_walk ra _ gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                bk_P (conc st mm) (conc st bm) (conc st (area_of mm)) bk_b3 bk_q (m_avail (MR st mm)) (m_freed (MR st mm)) (m_last_idx (MR st mm))
                (m_freeable (MR st mm)) bk_sc (m_maplen (MR st mm)) (c_secret (ctx st)) bk_stride (pw st (m_prev (MR st mm))) (pw st (m_next (MR st mm))));
        try eassumption.
      - rewrite A0. apply unsigned_lit. rewrite EP. lia.
      - rewrite EP, SC. unfold UNIT.
        pose proof (Z.div_mod bk_stride 16 ltac:(lia)) as D1. rewrite STM in D1. pose proof (Z.div_mod (snd bm) 16 ltac:(lia)) as D2. rewrite S16 in D2.
        pose proof (Z.div_mod (r_base r) 4096 ltac:(lia)) as D3. rewrite BAL in D3.
        replace (r_base r + (snd bm + 16 + bk_stride * i) + 16 * off) with ((r_base r / 4096 * 256 + snd bm / 16 + 1 + bk_stride / 16 * i + off) * 16) by lia.
        apply Z_mod_mult.
      - rewrite EP, SC. unfold UNIT in Q16 |- *. lia.
      - rewrite EP. lia.
      - rewrite HBm, EP, SC. unfold UNIT in Q16 |- *. lia.
      - (* [comment removed for export] *)
        pose proof WF as (_ & WR & _ & WA & _). destruct MSL as (a' & ara & k & Ha' & Hkk & Eg).
        destruct (WA a' ara Ha') as (rg & Hrg & A0' & A1' & AAL & ANG & _).
        assert (HG : conc st mm = r_base rg + snd a' + (AREA_HDR + META_SIZE * k)).
        { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a' rg Hrg). reflexivity. }
        destruct (WR (fst a') rg Hrg) as (RB0 & RBAL & RL0 & RBC & _).
        pose proof (Z.div_mod (snd a') 4096 ltac:(lia)) as DA. rewrite AAL in DA. pose proof (Z.div_mod (r_base rg) 4096 ltac:(lia)) as DR. rewrite RBAL in DR.
        unfold NSLOTS in Hkk.
        assert (Hm : (r_base rg + snd a' + (AREA_HDR + META_SIZE * k)) mod 4096 = AREA_HDR + META_SIZE * k).
        { unfold AREA_HDR, META_SIZE.
          replace (r_base rg + snd a' + (24 + 40 * k)) with ((24 + 40 * k) + (snd a' / 4096 + r_base rg / 4096) * 4096) by (clear -DA DR; lia).
          rewrite Z.mod_add by (clear; lia). apply Z.mod_small. clear -Hkk. lia. }
        rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a') _ rg Hrg).
        replace ((snd a' + (AREA_HDR + META_SIZE * k)) mod 4096) with (AREA_HDR + META_SIZE * k); [clear; lia|].
        unfold AREA_HDR, META_SIZE.
        replace (snd a' + (24 + 40 * k)) with ((24 + 40 * k) + (snd a' / 4096) * 4096) by (clear -DA; lia).
        rewrite Z.mod_add by (clear; lia). symmetry. apply Z.mod_small. clear -Hkk. lia.
      - lia.
      - lia.
      - intros LT. apply rsize_classes_read; [exact MI1| unfold bk_sc in *; lia].
      - pose proof (go_li _ _ _ GO). fold (MR st mm) in H. lia.
      - rewrite FB. lia.
      - unfold bk_sc. lia.
      - lia. }
    intros ms2 (t2' & t3' & t4' & ->).
    rewrite L31.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rre_nom_walk ra _ gp tp t2' s0 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 (wz (conc st mm)) F fc m1
                bk_P (conc st bm) i (m_last_idx (MR st mm)) bk_mword bk_b3 bk_sc bk_stride bk_E bk_res); try eassumption.
      - rewrite A0. apply unsigned_lit. rewrite EP. lia.
      - rewrite HBm, EE, SC. unfold UNIT. lia.
      - rewrite HBm. lia.
      - lia.
      - lia.
      - rewrite EE, EP. clear -FIT Hn. lia.
      - rewrite EE. clear -PP BC HCEILB. lia.
      - unfold bk_mword, meta_word. fold bk_sc. pose proof (go_li _ _ _ GO). fold (MR st mm) in H. rewrite FB. unfold bk_sc in *. lia.
      - assert (RSLE : bk_res <= bk_E - bk_P) by (rewrite ERES; lia). destruct (160 <=? bk_b3); [exact RSLE|]. rewrite SH5. lia.
      - destruct (Z.leb_spec 160 bk_b3) as [GE|LT]; [exact RR|]. rewrite SH5. rewrite Z.min_l by (unfold bk_b3 in LT; lia). exact RR. }
    intros ms3 ->.
    (* [comment removed for export] *)
    assert (ERSV : (if 160 <=? bk_b3 then bk_res else Z.shiftr bk_b3 5) = bk_res).
    { destruct (Z.leb_spec 160 bk_b3) as [GE|LT]; [reflexivity|]. rewrite SH5. apply Z.min_l. unfold bk_b3 in LT. lia. }
    rewrite ERSV.
    eapply evt_mono.
    { eapply (rre_dec_walk ra _ gp tp s0 a0 a1 s3 s4 s5 s6 s7 s8 s9 s10 s11 t4' t5 t6 (wz (conc st mm)) F fc m1 n' bk_P (conc st bm) bk_mword bk_sc bk_stride bk_E bk_res);
        [exact A1| exact N| rewrite EE, EP; lia| rewrite EE; lia| unfold bk_sc in *; lia| exact MI1]. }
    intros ms4 D4. unfold rre_front_post. exists m1, t4'.
    split; [exact D4|]. split; [exact FR|]. split; [exact ST1|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI1| exact RM1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma rpres_rre_ss : forall (C : Z -> Prop) m0 m P E n' b3,
    rpres_except C m0 m -> 16 <= P -> 0 <= n' -> P + n' <= E -> E + 1 <= 2 ^ 64 -> E - P - n' < 2 ^ 32 ->
    (C (P - 3)) -> (forall x, P + n' <= x < E -> C x) ->
    rpres_except C m0 (rre_ss_mem m P E n' b3).
  Proof.
    intros C m0 m P E n' b3 HP P16 N0 PN EHI R32 C3 CE.
    assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
    unfold rre_ss_mem. cbv zeta.
    set (rsv := E - P - n').
    set (mF := if rsv =? 0 then _ else _).
    assert (HF : rpres_except C m0 mF).
    { subst mF. destruct (Z.eqb_spec rsv 0); [exact HP|]. apply rpres_write; [exact HP| lia | cbn; lia | cbn; intros; apply CE; lia]. }
    clearbody mF.
    set (mG := if 5 <=? rsv then _ else _).
    assert (HG : rpres_except C m0 (fst mG) /\ 0 <= snd mG <= 5).
    { subst mG. destruct (Z.leb_spec 5 rsv); cbn [fst snd].
      - split; [|lia]. apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply CE; lia].
        apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply CE; lia].
      - split; [exact HF| lia]. }
    clearbody mG. destruct mG as [mg r2]. cbn [fst snd] in HG |- *. destruct HG as [HG R2].
    apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros x Hx; replace x with (P - 3) by lia; exact C3].
  Qed.

  Definition rre_inplace_post' (sp gp tp a0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) (n' : Z) : machine_state -> Prop :=
    fun ms' => exists m1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None (rre_ss_mem m1 bk_P bk_E n' bk_b3) (seg_rom rsegs)
      /\ mem_inv rsegs (rre_ss_mem m1 bk_P bk_E n' bk_b3)
      /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono rsegs m m1 /\ mem_inv rsegs m1 /\ rmrep st m1 /\ stk rsegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells rsegs m1 (bv_unsigned sp + -64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Lemma rre_inplace_evt : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem) (lo n' : Z),
    rmrep st m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - 64 -> bv_unsigned sp + 8 <= 2 ^ 64 ->
    a0 = Z_to_bv 64 bk_P -> a1 = Z_to_bv 64 n' -> 1 <= n' < MMAP_THRESHOLD ->
    rinplace n' (bk_E - bk_P) bk_sc = true ->
    evt rsegs (rre_inplace_post' sp gp tp a0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 ra F fc lo m n')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x27109c) fc None m (seg_rom rsegs)).
  Proof.
    intros until n'. intros RM MI ST CLO LO SPH A0 A1 N IP.
    pose proof RM as (WF & _). pose proof (bk_region WF) as (B0 & BAL & S0 & S16 & SPAN & BC). pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & R0 & RS & B3 & L31 & SH5 & SST).
    pose proof bk_snd_c as SC. pose proof bk_span as [SK SKL]. pose proof bk_stride_facts as [ST16 STM]. hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO.
    assert (NUM : bk_P = r_base r + snd c + 16 * off /\ bk_E = r_base r + snd c + bk_stride - 4) by (unfold bk_E, bk_P, UNIT, IB; split; lia).
    destruct NUM as [EP EE].
    assert (PP : 16 <= snd c + 16 * off /\ snd c + bk_stride - 4 + 1 <= round_up_pg (r_len r)) by (rewrite SC; unfold UNIT in *; lia).
    unfold rinplace in IP. apply andb_true_iff in IP as [IP1 IP2]. apply Z.leb_le in IP1. apply Z.leb_le in IP2.
    pose proof (size_to_class_props n' ltac:(lia)) as (SCR & _ & _).
    destruct bk_guards as (_ & _ & _ & _ & G63 & _).
    assert (SC48 : bk_sc < 48) by (destruct (Z.lt_ge_cases bk_sc 48) as [LT|GE]; [exact LT| pose proof (G63 GE); lia]).
    pose proof (SST SC48) as SST'.
    eapply evt_cut; [eapply (rre_front ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n'); eassumption|].
    intros ms1 (m1 & t4' & D & FR & ST1 & MU & WM & MI1 & RM1).
    destruct D as (a2' & a4' & a5' & a7' & t1' & t2' & ->).
    replace (rinplace n' (bk_E - bk_P) bk_sc) with true by (symmetry; unfold rinplace; rewrite (proj2 (Z.leb_le _ _) IP1), (proj2 (Z.leb_le _ _) IP2); reflexivity).
    destruct (bk_reads m1 RM1 WF) as (_ & _ & BK3 & _ & _ & _ & _ & W).
    eapply evt_mono.
    { eapply (rre_inplace_walk sp gp tp t1' t2' s0 a0 a2' a4' a5' a7' s3 s4 s5 s6 s7 s8 s9 s10 s11 t4' t5 t6 (wz (conc st mm)) ra s0 s1 s2 s3 s4 s5 s6 F fc m1 lo bk_P n' bk_sc bk_E bk_res bk_b3);
        try eassumption.
      - rewrite A0. apply unsigned_lit. rewrite EP. lia.
      - rewrite EP. lia.
      - lia.
      - lia.
      - rewrite EE, EP. clear -SST' Hoff S16. lia.
      - rewrite EE, SC. clear -CLO BC SPAN SKL SK. unfold UNIT. lia. }
    intros ms2 (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & -> & MI2).
    unfold rre_inplace_post'. exists m1. do 14 eexists. split; [reflexivity|]. auto 12.
  Qed.

  (* [comment removed for export] *)
  Lemma rre_inplace_rep : forall (m1 : mem) (n' : Z),
    rmrep st m1 -> ticks_ok st -> 0 <= n' -> UNIT * off + n' <= bk_stride - IB -> bk_sc < 48 ->
    (27 <= bk_sc -> 2028 < n') ->   (* [comment removed for export] *)
    let W := ss_list c off n' bk_stride i in
    let st' := relay st W c off n' in
    rmrep st' (rre_ss_mem m1 bk_P bk_E n' bk_b3) /\ ticks_ok st' /\ relay_ok st c W off n'
    /\ strip st' = strip st /\ (forall q, conc st' q = conc st q) /\ s_regions st' = s_regions st /\ ctx st' = ctx st.
  Proof.
    intros m1 n' RM TK N0 FIT' SC48 CLS' W st'.
    pose proof RM as (WF & _). pose proof (bk_region WF) as (B0 & BAL & S0 & S16 & SPAN & BC). pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & R0 & RS & B3 & L31 & SH5 & SST).
    pose proof bk_snd_c as SC. pose proof bk_span as [SK SKL]. pose proof bk_stride_facts as [ST16 STM]. pose proof (SST SC48) as SST'.
    pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as HI.
    assert (SPANi : snd bm + 16 + get_stride (get_meta_rec st mm) * (i + 1) <= round_up_pg (r_len r)).
    { change (get_stride (get_meta_rec st mm)) with bk_stride. rewrite Z.mul_add_distr_l, Z.mul_1_r. clear -SPAN SKL. lia. }
    set (st0 := set_tick (N.succ (s_tick st)) st).
    assert (M0 : rmrep st0 m1) by (apply rmrep_set_tick; exact RM).
    assert (T0 : ticks_ok st0) by (apply ticks_ok_set_tick; [cbn; lia| exact TK]).
    assert (ER0 : s_regions st0 = s_regions st) by reflexivity.
    assert (EG0 : s_groups st0 = s_groups st) by reflexivity.
    assert (NOGRP : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst bm ->
              snd b' + 9 <= snd bm + 16 + bk_stride * i - 4 \/ snd bm + 16 + bk_stride * i + bk_stride - 4 <= snd b').
    { intros b' gh Hb' Hf. destruct (im_hdr _ _ _ IM _ _ Hb') as (m2 & Hm2 & _ & _).
      assert (H2 : hosts st b' m2) by (destruct gh as [gm gai]; cbn in Hm2; subst gm; exists gai; exact Hb').
      destruct (sep_ghdr x0 st BL LS IM IG IS mm bm i bk_hosts HI ltac:(rewrite <- bk_c; exact (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF)) m2 b' H2 Hf) as [A|A];
        unfold sstart in A; rewrite bk_gbase in A; fold bk_stride in A; unfold UNIT in A; clear -A ST16 SK; lia. }
    (* [comment removed for export] *)
    set (e := snd c + bk_stride - IB). set (po := snd c + UNIT * off). set (rs := e - po - n').
    assert (EE : bk_E = r_base r + e) by (unfold bk_E, e; lia).
    assert (EP : bk_P = r_base r + po) by (unfold bk_P, po; lia).
    assert (ERS : bk_E - bk_P - n' = rs) by (unfold rs; lia).
    assert (RSR : 0 <= rs < 2 ^ 32) by (unfold rs, e, po, UNIT, IB in *; clear -N0 FIT' SST' Hoff ST16; lia).
    assert (Tlo : snd bm + 16 + bk_stride * i - 4 <= po - 3) by (unfold po; rewrite SC; unfold UNIT; clear -Hoff; lia).
    assert (Thi : e = snd bm + 16 + bk_stride * i + bk_stride - 4) by (unfold e; rewrite SC; unfold UNIT, IB; lia).
    assert (PE : po + n' = e - rs) by (unfold rs; lia).
    assert (REP : rmrep (wrs W st0) (let m2 := if rs =? 0 then m1 else write_to_mem m1 (wa (bk_E - rs)) [b8 0] in
                              let '(m3, r') := if 5 <=? rs then (write_to_mem (write_to_mem m2 (wa (bk_E - 5)) [b8 0]) (wa (bk_E - 4)) (le4 (wz rs)), 5) else (m2, rs) in
                              write_to_mem m3 (wa (bk_P - 3)) [b8 (Z.land bk_b3 31 + Z.shiftl r' 5)])
                  /\ ticks_ok (wrs W st0)).
    { subst W. unfold ss_list. fold po e. fold rs. rewrite !wrs_app. rewrite bk_c. cbn [fst].
      assert (EW : forall stx, wr8 (fst bm, e - 1) (Z.shiftr rs 24) (wr8 (fst bm, e - 2) (Z.shiftr rs 16) (wr8 (fst bm, e - 3) (Z.shiftr rs 8) (wr8 (fst bm, e - 4) rs stx)))
                   = wr32 (fst bm, e - 4) rs stx).
      { intros stx. unfold wr32, aadd. cbn [fst snd]. replace (e - 4 + 1) with (e - 3) by lia. replace (e - 4 + 2) with (e - 2) by lia. replace (e - 4 + 3) with (e - 1) by lia. reflexivity. }
      rewrite EE, EP.
      replace (r_base r + e - rs) with (r_base r + (e - rs)) by lia. replace (r_base r + e - 5) with (r_base r + (e - 5)) by lia.
      replace (r_base r + e - 4) with (r_base r + (e - 4)) by lia. replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia.
      destruct (Z.eqb_spec rs 0) as [Z0|NZ]; destruct (Z.leb_spec 5 rs) as [LE|GT]; cbn [wrs]; try (exfalso; clear -Z0 LE; lia).
      - (* [comment removed for export] *)
        rewrite (Z.min_l rs 5) by lia. replace (Z.land bk_b3 31 + Z.shiftl rs 5) with (i + 32 * rs) by (rewrite L31, Z.shiftl_mul_pow2 by lia; lia).
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP st0 m1 (po - 3) (i + 32 * rs) M0 T0 ER0 EG0
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi N0 PE RSR; lia) ltac:(clear -Hi Z0; lia)) as [M3 T3].
        split; [exact M3| exact T3].
      - (* [comment removed for export] *)
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP st0 m1 (e - rs) 0 M0 T0 ER0 EG0
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PE N0 NZ RSR Hoff; lia) ltac:(lia)) as [MF TF].
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (e - 5) 0 MF TF ltac:(cbn; exact ER0) ltac:(cbn; exact EG0)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PE N0 LE RSR Hoff; lia) ltac:(lia)) as [M1 T1].
        destruct (rwr32_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (e - 4) rs M1 T1 ltac:(cbn; exact ER0) ltac:(cbn; exact EG0)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PE N0 LE RSR Hoff; lia)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Thi LE; lia) ltac:(exact RSR)) as [M2 T2].
        rewrite EW. rewrite (Z.min_r rs 5) by lia. replace (Z.land bk_b3 31 + Z.shiftl 5 5) with (i + 32 * 5) by (rewrite L31; reflexivity).
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (po - 3) (i + 32 * 5) M2 T2 ltac:(cbn; exact ER0) ltac:(cbn; exact EG0)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi N0 PE RSR; lia) ltac:(clear -Hi; lia)) as [M3 T3].
        split; [exact M3| exact T3].
      - (* [comment removed for export] *)
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP st0 m1 (e - rs) 0 M0 T0 ER0 EG0
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PE N0 NZ RSR Hoff; lia) ltac:(lia)) as [MF TF].
        rewrite (Z.min_l rs 5) by lia. replace (Z.land bk_b3 31 + Z.shiftl rs 5) with (i + 32 * rs) by (rewrite L31, Z.shiftl_mul_pow2 by lia; lia).
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (po - 3) (i + 32 * rs) MF TF ltac:(cbn; exact ER0) ltac:(cbn; exact EG0)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi N0 PE RSR; lia) ltac:(clear -Hi RSR GT; lia)) as [M3 T3].
        split; [exact M3| exact T3]. }
    destruct REP as [MW TW].
    destruct (rmrep_havoc (wrs W st0) _ (aadd c (UNIT * off)) n' MW TW) as [MH TH].
    split. { unfold st', relay. fold st0. unfold rre_ss_mem. rewrite ERS. exact MH. }
    split. { unfold st', relay. fold st0. exact TH. }
    split. { exact (relay_ok_set_size st L BL LS c off n n' mm bm i ai a ar ka INV BF N0 FIT' SC48 CLS'). }
    split. { apply strip_relay. }
    split. { intros q. apply conc_relay. }
    split. { exact (ce_regions _ _ (proj1 (relay_ctrl st W c off n'))). }
    exact (ce_ctx _ _ (proj1 (relay_ctrl st W c off n'))).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bk_span20 : bk_sc < 48 -> bk_stride * (i + 1) <= bk_stride * (m_last_idx (MR st mm) + 1) < 2 ^ 20.
  Proof.
    intros SC. pose proof (ig_ok _ _ _ IG _ _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as G.
    destruct (g_stride _ _ _ _ _ _ G SC) as (_ & _ & LT). unfold cnt_of in LT. fold (MR st mm) in LT. change (get_stride (MR st mm)) with bk_stride in LT.
    pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as Hi. pose proof bk_stride_facts as [S16 _].
    assert (M : bk_stride * (i + 1) <= bk_stride * (m_last_idx (MR st mm) + 1)) by (apply Z.mul_le_mono_nonneg_l; [clear -S16; lia| clear -Hi; lia]).
    clear -M LT. lia.
  Qed.

  (* [comment removed for export] *)
  Definition raa_fix_mem (m : mem) (n' al : Z) : mem :=
    let adj := aadj bk_P al in
    if adj =? 0 then rre_ss_mem m bk_P bk_E n' bk_b3
    else raa_mem m (bk_P + adj) bk_E n' (r_base r + snd c) i ((bk_P + adj - conc st bm - 16) / 16).

  Definition raa_fix_post (sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v : word) (F : bvmap 5 word) (fc : bv 32)
      (lo : Z) (m : mem) (n' al : Z) : machine_state -> Prop :=
    fun ms' => raa_tail_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v F fc (raa_fix_mem m n' al) (bk_P + aadj bk_P al) ms'.

  Lemma raa_fix_evt : forall (ra0 rav sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 s0v s1v : word) F fc (m : mem) (junk : list byte) (lo n' al k : Z),
    rmrep st m -> mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp + -32) -> hceil <= lo -> lo <= bv_unsigned sp - 32 -> bv_unsigned sp + 8 <= 2 ^ 64 ->
    rw_cells rsegs m (bv_unsigned sp + -32) [CB 8 junk; C8 s1v; C8 s0v; C8 rav] ->
    a0 = Z_to_bv 64 bk_P -> s0 = Z_to_bv 64 al -> s1 = Z_to_bv 64 n' -> al = 2 ^ k -> 4 <= k <= 6 -> 1 <= n' -> n = n' + al - 16 -> bk_sc < 48 ->
    evt rsegs (raa_fix_post sp gp tp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rav s0v s1v F fc lo m n' al)
      (MS (mkR ra0 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x270e58) fc None m (seg_rom rsegs)).
  Proof.
    intros until k. intros RM MI ST CLO LO SPH FR A0 HS0 HS1 HAL HK N1 HN SC48.
    pose proof RM as (WF & _). pose proof (bk_region WF) as (B0 & BAL & S0 & S16 & SPAN & BC). pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & R0 & RS & B3 & L31 & SH5 & SST).
    pose proof bk_span as [SK SKL]. pose proof bk_stride_facts as [ST16 STM]. pose proof bk_snd_c as SCE. pose proof bk_q16 as [Q16 QR]. pose proof (bk_span20 SC48) as [SP1 SP2].
    pose proof (SST SC48) as SST'.
    pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
    hcb; unfold Malloc.alloc_ceiling, Decode.alloc_ceiling in CLO.
    assert (NUM : bk_P = r_base r + snd c + 16 * off /\ bk_E = r_base r + snd c + bk_stride - 4 /\ bk_res = bk_E - bk_P - n /\ 16 * off + n <= bk_stride - 4)
      by (unfold bk_res, bk_E, bk_P, UNIT, IB in *; repeat split; lia).
    destruct NUM as (EP & EE & ERES & FIT).
    assert (PP : 16 <= snd c + 16 * off /\ snd c + bk_stride - 4 + 1 <= round_up_pg (r_len r)) by (rewrite SCE; unfold UNIT in *; lia).
    assert (P16 : bk_P mod 16 = 0).
    { rewrite EP, SCE. unfold UNIT.
      pose proof (Z.div_mod bk_stride 16 ltac:(lia)) as D1. rewrite STM in D1. pose proof (Z.div_mod (snd bm) 16 ltac:(lia)) as D2. rewrite S16 in D2.
      pose proof (Z.div_mod (r_base r) 4096 ltac:(lia)) as D3. rewrite BAL in D3.
      replace (r_base r + (snd bm + 16 + bk_stride * i) + 16 * off) with ((r_base r / 4096 * 256 + snd bm / 16 + 1 + bk_stride / 16 * i + off) * 16) by lia.
      apply Z_mod_mult. }
    pose proof (aadj_facts bk_P al k HAL HK P16) as (ADR & AD16 & ADAL & ALR & AL16).
    (* [comment removed for export] *)
    destruct (bk_reads m RM WF) as (R4 & R3 & BK3 & R2 & BIG & RR & RE & W).
    destruct bk_area as (Har & Hck & MSL & G0). destruct bk_guards as (G12 & G13 & G14 & G16 & G63 & G17 & G48 & GSTR).
    pose proof (rmrep_meta_chunk st m mm RM MSL) as MM. unfold meta_cells in MM. rewrite (bf_mem _ _ _ _ _ _ _ _ _ _ _ BF) in MM. cbn [pw oconc] in MM.
    destruct (rmrep_group_read st m bm _ RM (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF)) as [RG _]. cbn [g_meta pw oconc] in RG.
    pose proof (rmrep_area_check_read st m (area_of mm) ar RM Har) as RA. rewrite Hck in RA.
    pose proof (rmrep_ctx_secret_read st m RM) as RC.
    pose proof (rmeta_slot_bounds st m mm RM MSL) as (GB0 & GB1 & GB2 & GB4 & _).
    assert (HBm : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
    pose proof (go_avail _ _ _ GO) as AV. pose proof (go_freed _ _ _ GO) as FRD. pose proof (go_maplen _ _ _ GO) as ML. pose proof (go_freeable _ _ _ GO) as FB.
    fold (MR st mm) in AV, FRD, ML, FB.
    pose proof (bf_sc _ _ _ _ _ _ _ _ _ _ _ BF) as SCc.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (raa_meta_walk ra0 _ gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
                bk_P (conc st mm) (conc st bm) (conc st (area_of mm)) bk_b3 bk_q (m_avail (MR st mm)) (m_freed (MR st mm)) (m_last_idx (MR st mm))
                (m_freeable (MR st mm)) bk_sc (m_maplen (MR st mm)) (c_secret (ctx st)) bk_stride n' al k (pw st (m_prev (MR st mm))) (pw st (m_next (MR st mm))));
        try eassumption.
      - rewrite A0. apply unsigned_lit. rewrite EP. lia.
      - rewrite EP. lia.
      - rewrite EP, SCE. unfold UNIT in Q16 |- *. lia.
      - rewrite EP. lia.
      - rewrite HBm, EP, SCE. unfold UNIT in Q16 |- *. lia.
      - (* [comment removed for export] *)
        pose proof WF as (_ & WR & _ & WA & _). destruct MSL as (a' & ara & k' & Ha' & Hkk & Eg).
        destruct (WA a' ara Ha') as (rg & Hrg & A0' & A1' & AAL & ANG & _).
        assert (HG : conc st mm = r_base rg + snd a' + (AREA_HDR + META_SIZE * k')).
        { rewrite Eg, conc_aadd by (rewrite Hrg; eauto). rewrite (conc_region' st a' rg Hrg). reflexivity. }
        destruct (WR (fst a') rg Hrg) as (RB0 & RBAL & RL0 & RBC & _).
        pose proof (Z.div_mod (snd a') 4096 ltac:(lia)) as DA. rewrite AAL in DA. pose proof (Z.div_mod (r_base rg) 4096 ltac:(lia)) as DR. rewrite RBAL in DR.
        unfold NSLOTS in Hkk.
        assert (Hm : (r_base rg + snd a' + (AREA_HDR + META_SIZE * k')) mod 4096 = AREA_HDR + META_SIZE * k').
        { unfold AREA_HDR, META_SIZE.
          replace (r_base rg + snd a' + (24 + 40 * k')) with ((24 + 40 * k') + (snd a' / 4096 + r_base rg / 4096) * 4096) by (clear -DA DR; lia).
          rewrite Z.mod_add by (clear; lia). apply Z.mod_small. clear -Hkk. lia. }
        rewrite HG, Hm. unfold area_of. rewrite Eg. unfold aadd. cbn [fst snd]. rewrite (conc_region st (fst a') _ rg Hrg).
        replace ((snd a' + (AREA_HDR + META_SIZE * k')) mod 4096) with (AREA_HDR + META_SIZE * k'); [clear; lia|].
        unfold AREA_HDR, META_SIZE.
        replace (snd a' + (24 + 40 * k')) with ((24 + 40 * k') + (snd a' / 4096) * 4096) by (clear -DA; lia).
        rewrite Z.mod_add by (clear; lia). symmetry. apply Z.mod_small. clear -Hkk. lia.
      - lia.
      - lia.
      - clear -N1 HN Hfit SST' ALR Hoff. unfold UNIT, IB in Hfit. lia.
      - apply rsize_classes_read; [exact MI| unfold bk_sc in *; lia].
      - pose proof (go_li _ _ _ GO). fold (MR st mm) in H. lia.
      - rewrite FB. lia.
      - unfold bk_sc in *. lia.
      - lia.
      - exact (G16 SC48). }
    intros ms2 (t0' & t2' & t3' & ->). rewrite L31.
    replace (conc st bm + 16 + bk_stride * (i + 1) - 4) with bk_E by (rewrite EE, HBm, SCE; unfold UNIT; clear; lia).
    replace (conc st bm + 16 + bk_stride * (i + 1)) with (bk_E + 4) by (rewrite EE, HBm, SCE; unfold UNIT; clear; lia).
    fold (aadj bk_P al). set (adj := aadj bk_P al) in *.
    unfold raa_fix_post, raa_fix_mem. fold adj.
    pose proof RM as (_ & _ & _ & _ & _ & SH). destruct (SH _ _ Hr bk_Kr) as [HW _].
    destruct (Z.eq_dec adj 0) as [AZ|ANZ].
    - (* [comment removed for export] *)
      rewrite AZ, Z.add_0_r. change (0 =? 0) with true. cbv iota.
      eapply (raa_ss_walk ra0 sp gp tp t0' _ t2' _ a0 _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6 rav s0v s1v F fc m junk lo bk_P n' bk_E bk_b3);
        try eassumption.
      + rewrite A0. apply unsigned_lit. rewrite EP. lia.
      + rewrite EP. lia.
      + lia.
      + rewrite EE, EP. clear -FIT HN ALR N1. lia.
      + rewrite EE, EP. clear -SST' Hoff ST16. lia.
      + rewrite EE, SCE. clear -CLO BC SPAN SKL SK. unfold UNIT. lia.
    - (* [comment removed for export] *)
      replace (adj =? 0) with false by (symmetry; apply Z.eqb_neq; exact ANZ).
      assert (A16 : 16 <= adj <= al - 16) by (clear -ADR AD16 AL16 ANZ; Z.div_mod_to_equations; lia).
      assert (EQB : bk_P - conc st bm - 16 = 16 * bk_q) by (rewrite EP, HBm, SCE; unfold UNIT in Q16 |- *; clear -Q16; lia).
      eapply (raa_aa_walk ra0 sp gp tp t0' _ t2' _ a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4 t5 t6 rav s0v s1v F fc m junk
                lo bk_P (bk_P + adj) n' bk_E (r_base r + snd c) (conc st bm) i bk_stride adj); try eassumption.
      + rewrite A0. apply unsigned_lit. rewrite EP. lia.
      + clear -A16; lia.
      + reflexivity.
      + rewrite EP. clear -Hoff. lia.
      + rewrite SCE. clear -B0 S0 SK. unfold UNIT. lia.
      + rewrite EE, EP. clear -FIT HN A16. lia.
      + rewrite EE. clear -SST'. lia.
      + rewrite HBm, SCE. unfold UNIT. clear. lia.
      + rewrite EP, HBm, SCE. unfold UNIT in Q16 |- *. split; [clear -Q16 QR A16 SK; lia|].
        unfold UNIT, IB in Hfit. clear -Hfit HN A16 SP1 SP2 N1. lia.
      + replace (bk_P + adj - conc st bm - 16) with (adj + bk_q * 16) by (clear -EQB; lia).
        rewrite Z.mod_add by (clear; lia). exact AD16.
      + rewrite EP. replace (r_base r + snd c + 16 * off + adj - (r_base r + snd c)) with (adj + off * 16) by (clear; lia).
        rewrite Z.mod_add by (clear; lia). exact AD16.
      + rewrite HBm. clear -B0 S0. lia.
      + clear -ST16 SST'. lia.
      + pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF). fold (MR st mm) in H. clear -Hi H. lia.
      + rewrite EE, SCE. clear -CLO BC SPAN SKL SK. unfold UNIT. lia.
      + eapply wr_at_sub; [exact HW| rewrite SCE; unfold UNIT; clear -S0 SK; lia| rewrite EE, SCE; unfold UNIT; clear -SPAN SKL; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rpres_raa : forall (C : Z -> Prop) m0 m P' E n' S idx q,
    rpres_except C m0 m -> 16 <= S -> S + 16 <= P' -> 0 <= n' -> P' + n' <= E -> E + 1 <= 2 ^ 64 -> E - P' - n' < 2 ^ 32 ->
    (forall x, S - 3 <= x < S -> C x) -> (forall x, P' - 4 <= x < P' -> C x) -> (forall x, P' + n' <= x < E -> C x) ->
    rpres_except C m0 (raa_mem m P' E n' S idx q).
  Proof.
    intros C m0 m P' E n' S idx q HP S16 SP N0 PN EHI R32 CS CP CE.
    assert (L4 : forall w, length (le4 w) = 4%nat) by (intros; reflexivity).
    assert (L2 : forall w, length (le2 w) = 2%nat) by (intros; reflexivity).
    unfold raa_mem. cbv zeta.
    set (rsv := E - P' - n').
    assert (H1 : rpres_except C m0 (write_to_mem (write_to_mem (write_to_mem m (wa (P' - 4)) [b8 0]) (wa (P' - 3)) [b8 idx]) (wa (P' - 2)) (le2 (wz q)))).
    { apply rpres_write; [| lia| rewrite L2; lia| rewrite L2; intros; apply CP; lia].
      apply rpres_write; [| lia| cbn; lia| cbn; intros; apply CP; lia].
      apply rpres_write; [exact HP| lia| cbn; lia| cbn; intros; apply CP; lia]. }
    set (mA := write_to_mem (write_to_mem (write_to_mem m _ _) _ _) _ _) in *. clearbody mA.
    set (mF := if rsv =? 0 then _ else _).
    assert (HF : rpres_except C m0 mF).
    { subst mF. destruct (Z.eqb_spec rsv 0); [exact H1|]. apply rpres_write; [exact H1| lia | cbn; lia | cbn; intros; apply CE; lia]. }
    clearbody mF.
    set (mG := if 5 <=? rsv then _ else _).
    assert (HG : rpres_except C m0 mG).
    { subst mG. destruct (Z.leb_spec 5 rsv); [| exact HF].
      apply rpres_write; [| lia | rewrite L4; lia | rewrite L4; intros; apply CE; lia].
      apply rpres_write; [exact HF| lia | cbn; lia | cbn; intros; apply CE; lia]. }
    clearbody mG.
    apply rpres_write; [| lia| rewrite L2; lia| rewrite L2; intros; apply CS; lia].
    apply rpres_write; [| lia| cbn; lia| cbn; intros; apply CS; lia].
    apply rpres_write; [exact HG| lia | cbn; lia | cbn; intros x Hx; apply CP; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma raa_aa_rep : forall (m1 : mem) (n' adj : Z),
    rmrep st m1 -> ticks_ok st -> 1 <= n' -> 16 <= adj -> adj mod 16 = 0 -> UNIT * off + adj + n' <= bk_stride - IB -> off + adj / 16 <= 258 -> bk_sc < 48 ->
    (27 <= bk_sc -> 2028 < n') ->   (* [comment removed for export] *)
    let off' := off + adj / 16 in
    let W := aa_list c off' n' bk_stride i (aa_q c off' bm) in
    let st' := relay st W c off' n' in
    rmrep st' (raa_mem m1 (bk_P + adj) bk_E n' (r_base r + snd c) i ((bk_P + adj - conc st bm - 16) / 16)) /\ ticks_ok st' /\ relay_ok st c W off' n'
    /\ strip st' = strip st /\ (forall q, conc st' q = conc st q) /\ s_regions st' = s_regions st /\ ctx st' = ctx st.
  Proof.
    intros m1 n' adj RM TK N1 A16 AM FIT' O258 SC48 CLS' off' W st'.
    pose proof RM as (WF & _). pose proof (bk_region WF) as (B0 & BAL & S0 & S16 & SPAN & BC). pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & R0 & RS & B3 & L31 & SH5 & SST).
    pose proof bk_snd_c as SC. pose proof bk_span as [SK SKL]. pose proof bk_stride_facts as [ST16 STM]. pose proof (SST SC48) as SST'.
    pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) as HI.
    assert (HBm : conc st bm = r_base r + snd bm) by (apply conc_region'; exact Hr).
    set (d := adj / 16) in *. assert (ED : adj = 16 * d) by (subst d; clear -AM A16; Z.div_mod_to_equations; lia).
    assert (D1 : 1 <= d) by (clear -ED A16; lia).
    assert (OFF' : 1 <= off' <= 258) by (subst off'; clear -D1 O258 Hoff; lia).
    assert (FIT2 : UNIT * off' + n' <= get_stride (MR st mm) - IB) by (subst off'; change (get_stride (MR st mm)) with bk_stride; unfold UNIT, IB in *; clear -FIT' ED; lia).
    pose proof (aa_q_facts st L BL LS c off n off' n' mm bm i ai a ar ka INV BF OFF' ltac:(clear -N1; lia) FIT2 SC48) as [Q16' QR']. change (get_stride (MR st mm)) with bk_stride in Q16'. change (get_stride (MR st mm)) with bk_stride in FIT2.
    assert (SPANi : snd bm + 16 + get_stride (get_meta_rec st mm) * (i + 1) <= round_up_pg (r_len r)).
    { change (get_stride (get_meta_rec st mm)) with bk_stride. rewrite Z.mul_add_distr_l, Z.mul_1_r. clear -SPAN SKL. lia. }
    set (st0 := set_tick (N.succ (s_tick st)) st).
    assert (M0 : rmrep st0 m1) by (apply rmrep_set_tick; exact RM).
    assert (T0 : ticks_ok st0) by (apply ticks_ok_set_tick; [cbn; lia| exact TK]).
    assert (ER0 : s_regions st0 = s_regions st) by reflexivity.
    assert (EG0 : s_groups st0 = s_groups st) by reflexivity.
    assert (NOGRP : forall b' gh, s_groups st !! b' = Some gh -> fst b' = fst bm ->
              snd b' + 9 <= snd bm + 16 + bk_stride * i - 4 \/ snd bm + 16 + bk_stride * i + bk_stride - 4 <= snd b').
    { intros b' gh Hb' Hf. destruct (im_hdr _ _ _ IM _ _ Hb') as (m2 & Hm2 & _ & _).
      assert (H2 : hosts st b' m2) by (destruct gh as [gm gai]; cbn in Hm2; subst gm; exists gai; exact Hb').
      destruct (sep_ghdr x0 st BL LS IM IG IS mm bm i bk_hosts HI ltac:(rewrite <- bk_c; exact (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF)) m2 b' H2 Hf) as [A|A];
        unfold sstart in A; rewrite bk_gbase in A; fold bk_stride in A; unfold UNIT in A; clear -A ST16 SK; lia. }
    (* [comment removed for export] *)
    set (e := snd c + bk_stride - IB). set (po := snd c + UNIT * off'). set (rs := e - po - n').
    assert (EE : bk_E = r_base r + e) by (unfold bk_E, e; lia).
    assert (EP : bk_P + adj = r_base r + po) by (unfold bk_P, po, off'; unfold UNIT; clear -ED; lia).
    assert (EQ : (bk_P + adj - conc st bm - 16) / 16 = aa_q c off' bm) by (unfold aa_q; rewrite EP, HBm; unfold po, UNIT; f_equal; clear; lia).
    assert (ERS : bk_E - (bk_P + adj) - n' = rs) by (unfold rs; clear -EE EP; lia).
    assert (RSR : 0 <= rs < 2 ^ 32) by (unfold rs, e, po, UNIT, IB in *; clear -N1 FIT2 SST' OFF' ST16; lia).
    assert (Tlo : snd bm + 16 + bk_stride * i - 4 = snd c - 4) by (rewrite SC; unfold UNIT; clear; lia).
    assert (Thi : e = snd bm + 16 + bk_stride * i + bk_stride - 4) by (unfold e; rewrite SC; unfold UNIT, IB; clear; lia).
    assert (PO16 : snd c + 16 <= po) by (unfold po, UNIT; clear -OFF'; lia).
    assert (PE : po + n' = e - rs) by (unfold rs; clear; lia).
    assert (OD : (bk_P + adj - (r_base r + snd c)) / 16 = off') by (rewrite EP; unfold po, UNIT; replace (r_base r + (snd c + 16 * off') - (r_base r + snd c)) with (off' * 16) by (clear; lia); apply Z.div_mul; clear; lia).
    rewrite EQ. unfold raa_mem. rewrite OD, ERS. rewrite EE, EP. cbv delta [MallocRep.wz].
    assert (FC : fst c = fst bm) by (rewrite bk_c; reflexivity).
    set (q' := aa_q c off' bm) in *.
    (* [comment removed for export] *)
    set (W1 := [((fst c, po - 4), 0); ((fst c, po - 3), i); ((fst c, po - 2), q'); ((fst c, po - 1), Z.shiftr q' 8)]).
    set (m1' := write_to_mem (write_to_mem (write_to_mem m1 (wa (r_base r + po - 4)) [b8 0]) (wa (r_base r + po - 3)) [b8 i]) (wa (r_base r + po - 2)) (le2 (Z_to_bv 64 q'))) in *.
    assert (REP1 : rmrep (wrs W1 st0) m1' /\ ticks_ok (wrs W1 st0) /\ s_regions (wrs W1 st0) = s_regions st /\ s_groups (wrs W1 st0) = s_groups st).
    { subst W1 m1'. cbn [wrs]. rewrite FC.
      destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP st0 m1 (po - 4) 0 M0 T0 ER0 EG0
                 ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 PE N1 RSR; lia) ltac:(clear; lia)) as [Ma Ta].
      destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (po - 3) i Ma Ta ltac:(cbn; exact ER0) ltac:(cbn; exact EG0)
                 ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 PE N1 RSR; lia) ltac:(clear -Hi; lia)) as [Mb Tb].
      destruct (rwr16_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (po - 2) q' Mb Tb ltac:(cbn; exact ER0) ltac:(cbn; exact EG0)
                 ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 PE N1 RSR; lia)
                 ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 PE N1 RSR; lia) ltac:(exact QR')) as [Mc Tc].
      unfold wr16, aadd in Mc, Tc. cbn [fst snd] in Mc, Tc. cbv delta [KInv.wz] in Mc. replace (po - 2 + 1) with (po - 1) in Mc, Tc by (clear; lia).
      replace (r_base r + (po - 4)) with (r_base r + po - 4) in Mc by (clear; lia). replace (r_base r + (po - 3)) with (r_base r + po - 3) in Mc by (clear; lia).
      replace (r_base r + (po - 2)) with (r_base r + po - 2) in Mc by (clear; lia).
      split; [exact Mc|]. split; [exact Tc|]. split; reflexivity. }
    clearbody m1'. destruct REP1 as (M1 & T1 & ER1 & EG1).
    (* [comment removed for export] *)
    set (W2 := (if rs =? 0 then [] else [((fst c, e - rs), 0)])
               ++ (if 5 <=? rs then [((fst c, e - 5), 0); ((fst c, e - 4), rs); ((fst c, e - 3), Z.shiftr rs 8); ((fst c, e - 2), Z.shiftr rs 16); ((fst c, e - 1), Z.shiftr rs 24)] else [])
               ++ [((fst c, po - 3), i + 32 * Z.min rs 5)]).
    set (m2' := let m2 := if rs =? 0 then m1' else write_to_mem m1' (wa (r_base r + e - rs)) [b8 0] in
                let m3 := if 5 <=? rs then write_to_mem (write_to_mem m2 (wa (r_base r + e - 5)) [b8 0]) (wa (r_base r + e - 4)) (le4 (Z_to_bv 64 rs)) else m2 in
                write_to_mem m3 (wa (r_base r + po - 3)) [b8 (i + Z.shiftl (Z.min rs 5) 5)]) in *.
    assert (REP2 : rmrep (wrs W2 (wrs W1 st0)) m2' /\ ticks_ok (wrs W2 (wrs W1 st0)) /\ s_regions (wrs W2 (wrs W1 st0)) = s_regions st /\ s_groups (wrs W2 (wrs W1 st0)) = s_groups st).
    { subst W2 m2'. rewrite !wrs_app. rewrite FC.
      assert (EW : forall stx, wr8 (fst bm, e - 1) (Z.shiftr rs 24) (wr8 (fst bm, e - 2) (Z.shiftr rs 16) (wr8 (fst bm, e - 3) (Z.shiftr rs 8) (wr8 (fst bm, e - 4) rs stx)))
                   = wr32 (fst bm, e - 4) rs stx).
      { intros stx. unfold wr32, aadd. cbn [fst snd]. replace (e - 4 + 1) with (e - 3) by lia. replace (e - 4 + 2) with (e - 2) by lia. replace (e - 4 + 3) with (e - 1) by lia. reflexivity. }
      replace (r_base r + e - rs) with (r_base r + (e - rs)) by lia. replace (r_base r + e - 5) with (r_base r + (e - 5)) by lia.
      replace (r_base r + e - 4) with (r_base r + (e - 4)) by lia. replace (r_base r + po - 3) with (r_base r + (po - 3)) by lia.
      destruct (Z.eqb_spec rs 0) as [Z0|NZ]; destruct (Z.leb_spec 5 rs) as [LE|GT]; cbn [wrs app]; try (exfalso; clear -Z0 LE; lia).
      - (* [comment removed for export] *)
        rewrite !(Z.min_l rs 5) by lia. replace (i + Z.shiftl rs 5) with (i + 32 * rs) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (po - 3) (i + 32 * rs) M1 T1 ER1 EG1
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 N1 PE RSR; lia) ltac:(clear -Hi Z0; lia)) as [M3 T3].
        cbv delta [KInv.wz] in M3. split; [exact M3|]. split; [exact T3|]. split; [cbn; exact ER1| cbn; exact EG1].
      - (* [comment removed for export] *)
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (e - rs) 0 M1 T1 ER1 EG1
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PE PO16 N1 NZ RSR; lia) ltac:(lia)) as [MF TF].
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (e - 5) 0 MF TF ltac:(cbn; exact ER1) ltac:(cbn; exact EG1)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PE PO16 N1 LE RSR; lia) ltac:(lia)) as [Ma Ta].
        destruct (rwr32_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (e - 4) rs Ma Ta ltac:(cbn; exact ER1) ltac:(cbn; exact EG1)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PE PO16 N1 LE RSR; lia)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Thi LE; lia) ltac:(exact RSR)) as [Mb Tb].
        rewrite EW. rewrite !(Z.min_r rs 5) by lia. replace (i + Z.shiftl 5 5) with (i + 32 * 5) by reflexivity.
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (po - 3) (i + 32 * 5) Mb Tb ltac:(cbn; exact ER1) ltac:(cbn; exact EG1)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 N1 PE RSR; lia) ltac:(clear -Hi; lia)) as [M3 T3].
        cbv delta [KInv.wz] in M3. split; [exact M3|]. split; [exact T3|]. split; [cbn; exact ER1| cbn; exact EG1].
      - (* [comment removed for export] *)
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (e - rs) 0 M1 T1 ER1 EG1
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PE PO16 N1 NZ RSR; lia) ltac:(lia)) as [MF TF].
        rewrite !(Z.min_l rs 5) by lia. replace (i + Z.shiftl rs 5) with (i + 32 * rs) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
        destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (po - 3) (i + 32 * rs) MF TF ltac:(cbn; exact ER1) ltac:(cbn; exact EG1)
                   ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 N1 PE RSR; lia) ltac:(clear -Hi RSR GT; lia)) as [M3 T3].
        cbv delta [KInv.wz] in M3. split; [exact M3|]. split; [exact T3|]. split; [cbn; exact ER1| cbn; exact EG1]. }
    clearbody m2'. destruct REP2 as (M2 & T2 & ER2 & EG2).
    (* [comment removed for export] *)
    set (W3 := [((fst c, snd c - 3), 224); ((fst c, snd c - 2), off'); ((fst c, snd c - 1), Z.shiftr off' 8)]).
    assert (EWW : W = W1 ++ W2 ++ W3) by (subst W W1 W2 W3; unfold aa_list; rewrite <- !app_assoc; reflexivity).
    assert (REP3 : rmrep (wrs W st0) (write_to_mem (write_to_mem m2' (wa (r_base r + snd c - 3)) [b8 224]) (wa (r_base r + snd c - 2)) (le2 (Z_to_bv 64 off')))
                   /\ ticks_ok (wrs W st0)).
    { rewrite EWW. clearbody W1 W2. rewrite !wrs_app. subst W3. cbn [wrs]. rewrite FC.
      destruct (rwr8_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (snd c - 3) 224 M2 T2 ER2 EG2
                 ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 PE N1 RSR; lia) ltac:(clear; lia)) as [Ma Ta].
      destruct (rwr16_rep st mm bm r i n Hr bk_Kr S0 ltac:(lia) SPANi ST16 NOGRP _ _ (snd c - 2) off' Ma Ta ltac:(cbn; exact ER2) ltac:(cbn; exact EG2)
                 ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 PE N1 RSR; lia)
                 ltac:(change (get_stride (get_meta_rec st mm)) with bk_stride; clear -Tlo Thi PO16 PE N1 RSR ST16; lia) ltac:(clear -OFF'; lia)) as [Mb Tb].
      unfold wr16, aadd in Mb, Tb. cbn [fst snd] in Mb, Tb. cbv delta [KInv.wz] in Mb. replace (snd c - 2 + 1) with (snd c - 1) in Mb, Tb by (clear; lia).
      replace (r_base r + (snd c - 3)) with (r_base r + snd c - 3) in Mb by (clear; lia). replace (r_base r + (snd c - 2)) with (r_base r + snd c - 2) in Mb by (clear; lia).
      split; [exact Mb| exact Tb]. }
    destruct REP3 as [MW TW].
    destruct (rmrep_havoc (wrs W st0) _ (aadd c (UNIT * off')) n' MW TW) as [MH TH].
    split. { unfold st', relay. fold st0. exact MH. }
    split. { unfold st', relay. fold st0. exact TH. }
    split. { exact (relay_ok_aalign st L BL LS c off n off' n' mm bm i ai a ar ka INV BF OFF' ltac:(clear -N1; lia) FIT2 SC48 CLS'). }
    split. { apply strip_relay. }
    split. { intros q. apply conc_relay. }
    split. { exact (ce_regions _ _ (proj1 (relay_ctrl st W c off' n'))). }
    exact (ce_ctx _ _ (proj1 (relay_ctrl st W c off' n'))).
  Qed.

  (* [comment removed for export] *)
  Lemma bk_blk_sep : rregions_wf st -> forall k', In k' BL -> bslot k' <> c ->
    conc st (bslot k') + UNIT * boff k' + bsize k' <= r_base r + snd c - 4 \/ bk_E <= conc st (bslot k') + UNIT * boff k'.
  Proof.
    intros WF k' Hk' NE. pose proof WF as (_ & WR & DJ & _ & _).
    pose proof (bk_region WF) as (B0 & BAL & S0 & S16 & SPAN & BC). pose proof bk_span as [SK SKL]. pose proof bk_stride_facts as [ST16 STM]. pose proof bk_snd_c as SC.
    destruct k' as [[c' off'] n'].
    destruct (MI_WFree.block_facts x0 st L BL LS INV c' off' n' Hk') as (m' & bm' & i' & ai' & a' & ar' & ka' & BF').
    cbn [bslot boff bsize fst snd] in NE |- *.
    pose proof (bf_c _ _ _ _ _ _ _ _ _ _ _ BF') as Ec'. pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF') as Hi'. pose proof (bf_fit _ _ _ _ _ _ _ _ _ _ _ BF') as FIT'.
    pose proof (bf_off _ _ _ _ _ _ _ _ _ _ _ BF') as OFF'. pose proof (bf_n _ _ _ _ _ _ _ _ _ _ _ BF') as N'. pose proof (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF') as NH'.
    assert (H' : hosts st bm' m') by (exists ai'; exact (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF')).
    destruct (ig_region _ _ _ IG _ _ (bf_hosts _ _ _ _ _ _ _ _ _ _ _ BF')) as (r' & Hr' & Kr').
    rewrite Ec'. rewrite (conc_region' st (fst bm', sstart (MR st m') i') r' Hr'). cbn [snd].
    pose proof (sstart_succ st m' i') as SS'. 
    pose proof (stride_ge _ _ _ IG _ _ H') as [S16' _].
    destruct (N.eq_dec (fst bm') (fst bm)) as [EF|NEF].
    - (* [comment removed for export] *)
      rewrite EF in Hr'. rewrite Hr in Hr'. injection Hr' as <-.
      assert (NE2 : m' <> mm \/ i' <> i).
      { destruct (aptr_eq_dec m' mm) as [->|NEm]; [right| left; exact NEm]. intros ->.
        apply NE. rewrite Ec', bk_c, EF. reflexivity. }
      destruct (sep_ext x0 st BL LS IM IG IS mm bm i bk_hosts (bf_i _ _ _ _ _ _ _ _ _ _ _ BF) ltac:(rewrite <- bk_c; exact (bf_notH _ _ _ _ _ _ _ _ _ _ _ BF))
                  m' bm' i' H' EF Hi' NE2 ltac:(rewrite <- Ec'; exact NH')) as [A|A].
      + left. rewrite bk_c. cbn [snd]. rewrite SS' in A. unfold UNIT, IB in *. clear -A FIT' N' S16'. lia.
      + right. unfold bk_E. rewrite bk_c. cbn [snd]. rewrite sstart_succ in A. change (get_stride (MR st mm)) with bk_stride in A.
        unfold UNIT, IB in *. clear -A OFF'. lia.
    - (* [comment removed for export] *)
      destruct (WR _ _ Hr') as (B0' & _ & _ & _ & _).
      destruct (MallocFacts_inv2.group_in_region x0 st L BL LS INV bm' m' H') as (r'' & Hr'' & _ & S0' & GE'). rewrite Hr' in Hr''. injection Hr'' as <-.
      pose proof (sstart_mono x0 st LS IG _ _ 0 i' H' ltac:(lia)) as M0'. rewrite (sstart0 x0 st LS IM _ _ H') in M0'.
      pose proof (sstart_mono x0 st LS IG _ _ (i' + 1) (m_last_idx (MR st m') + 1) H' ltac:(lia)) as M1'. rewrite <- gend_eq in M1'.
      destruct (DJ _ _ _ _ Hr' Hr NEF) as [D|D]; rewrite !lr_lo_group in D by (assumption || exact bk_Kr).
      + left. rewrite SS' in M1'. unfold UNIT, IB in *. clear -D FIT' N' M1' GE' OFF' SC SK S0 B0. lia.
      + right. unfold bk_E. unfold UNIT, IB in *. clear -D M0' S0' OFF' SC SKL SPAN. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_all : rregions_wf st ->
       (0 < r_base r /\ r_base r mod 4096 = 0 /\ 0 <= snd bm /\ snd bm mod 16 = 0
        /\ snd bm + 16 + bk_stride * (m_last_idx (MR st mm) + 1) <= round_up_pg (r_len r) /\ r_base r + round_up_pg (r_len r) <= hceil)
    /\ (0 <= i <= 31 /\ 0 <= off <= 258 /\ 0 <= n /\ UNIT * off + n <= bk_stride - IB /\ 0 <= bk_res /\ bk_res <= bk_stride - IB /\ 0 <= bk_b3 < 256)
    /\ (0 <= bk_stride * i /\ bk_stride * i + bk_stride <= bk_stride * (m_last_idx (MR st mm) + 1))
    /\ snd c = snd bm + UNIT + bk_stride * i
    /\ (16 <= bk_stride /\ bk_stride mod 16 = 0)
    /\ (48 <= bk_sc -> bk_sc = 63) /\ (bk_sc < 48 -> bk_stride < 2 ^ 20)
    /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x311000 <= r_base r)
    /\ s_regions st !! (fst bm) = Some r /\ In ((c, off), n) BL.
  Proof.
    intros WF. pose proof (bk_region WF) as RG. pose proof bk_ranges as (Hi & Hoff & Hn & Hfit & R0 & RS & B3 & L31 & SH5 & SST).
    pose proof bk_guards as (_ & _ & _ & _ & G63 & _).
    split; [exact RG|]. split; [repeat split; lia|]. split; [exact bk_span|]. split; [exact bk_snd_c|]. split; [exact bk_stride_facts|].
    split; [exact G63|]. split; [exact SST|]. split; [| split; [exact Hr| exact Hk]].
    pose proof WF as (_ & WR & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RFr). destruct RG as (B0 & _ & S0 & S16 & SPAN & _). pose proof bk_span as [SK _].
    apply (rreserved_disjoint1 _ _ RFr). pose proof (round_up_pg_ge (r_len r)). pose proof bk_stride_facts as [ST16 _].
    pose proof (bf_li _ _ _ _ _ _ _ _ _ _ _ BF). pose proof (bf_i _ _ _ _ _ _ _ _ _ _ _ BF). fold (MR st mm) in *.
    assert (0 <= bk_stride * m_last_idx (MR st mm)) by (apply Z.mul_nonneg_nonneg; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN. clear -H H2 S0 SPAN ST16. lia.
  Qed.

End BLK.
