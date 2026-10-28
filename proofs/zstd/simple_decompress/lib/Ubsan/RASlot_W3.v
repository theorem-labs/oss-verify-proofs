(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import SFModel.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A MallocKit_AB MallocKit_A2 MallocKit_A3 MallocKit_B MallocKit_B3 MallocModel_B.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import ProgDeps.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Malloc Require Import Malloc_fp MallocNat MallocFacts_AS ASlot_W0 ASlot_W1 ASlot_I ASlot_W2 ASlot_W3 ASlot_W4 ASlot_W5 ASlot_W6 ASlot_W7 ASlot_W8 F_ntf_C.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RMallocRep RMallocTree RF_get_meta RMallocKit_B RMallocKit_B2 RMallocKit_B3 RF_mm_syscalls RMallocKit_A RMallocKit_A2 RMalloc_fp RF_enframe RF_malloc_entry RF_malloc_small RF_ntf_A RF_ntf_C RAllocSlot_iface RASlot_I RMallocKit_A3.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RASlot_W2 RASlot_W4.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Lemma lw_slli52_srli58_sc mq : mw_ok mq ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (sx32 (Z_to_bv 64 (meta_word mq)))) 52))) 58)
  = Z_to_bv 64 (m_sizeclass mq).
Proof.
  intros MWq. pose proof (meta_word_range _ MWq) as WR. pose proof MWq as (LI & FB & SCR & ML).
  f_equal. unfold sx32. rewrite (unsigned_lit (meta_word mq)) by lia.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite swrap32_eq'.
  unfold meta_word.
  Z.div_mod_to_equations. nia.
Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc0 : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
Hypothesis SC0 : 0 <= sc0 < 48.

(* [comment removed for export] *)
Lemma ravz_pre_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
  bv_unsigned gw = G -> mem_inv usegs m ->
  evt usegs (fun ms' =>
      ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz 0) a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2f258) fc None m (seg_rom usegs))
    (MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2f24c) fc None m (seg_rom usegs)).
Proof.
  intros until fc. intros HG MI. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0 in CH. fold G in CH. rewrite <- HG in CH.
  step. step. if_cases K0; zify_cond K0. 2:{ exfalso. apply K0. reflexivity. }
  apply evt_done. reflexivity.
Qed.

Lemma ravz_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 gw : word) F fc,
  bv_unsigned gw = G -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a2' a3' a4' a5' a6' a7' : word) m',
      ms' = MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw (wz (sxv mask)) a2' a3' a4' a5' a6' a7' s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2f2d0) fc None m' (seg_rom usegs)
      /\ munch [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep st5 m')
    (MS (rt1_regs sc0 ra sp gp tp t0 t1 t2 s1 gw a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2f258) fc None m (seg_rom usegs)).
Proof.
  intros until fc. intros HG MI. unfold rt1_regs.
  pose proof (munch_refl [(G, G + 40); (RCTX + 880, RCTX + 912)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & G4 & G24). fold G in Gpos, GC, GI, G4, G24.
  pose proof (meta_word_range _ MW) as MWR.
  assert (AMO : amo_aligned AW (Z_to_bv 64 (bv_unsigned gw + 28)) = true).
  { apply amo_aligned_intro; [atop_facts; lia|]. rewrite HG. clear -G4. Z.div_mod_to_equations. lia. }
  clear G4 G24.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
  (* [comment removed for export] *)
  step.
  destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8). unfold wa in RD8.
  pose proof (bv_unsigned_in_range _ w8) as W8R. change (bv_modulus 8) with 256 in W8R.
  step.
  (* [comment removed for export] *)
  step. step.
  assert (W8M : bv_unsigned w8 mod 32 = ai).
  { unfold ai. rewrite <- L8. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. reflexivity. }
  unfold zxb. rewrite (unsigned_lit (bv_unsigned w8)) by lia.
  rewrite (sllw2_word (bv_unsigned w8)) by lia. rewrite W8M.
  set (y := 2 ^ (ai + 1)).
  (* [comment removed for export] *)
  step. step. rewrite negw_word.
  (* [comment removed for export] *)
  pose proof (sxv_range f) as RF. pose proof (sxv_range (- y)) as RY. pose proof (sxv_range (y - 1)) as RY1.
  step. rewrite sx32_wz_sxv by lia.
  step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
  (* [comment removed for export] *)
  clear CH. rmeta_open G MUa WMa. rewrite <- HG in MUa.
  rmchunk MR MSL CH. fold mr in CH. rewrite AV0, Hmem in CH. cbn [oconc] in CH. fold G in CH. rewrite <- HG in CH. fold f in CH.
  amo_step AMO. rewrite ?sx32_wz_sxv by lia.
  step. if_false.
  amo_step AMO.
  step. if_false.
  step. rewrite ?sextw_sxv, ?sextw_sxv', ?sextw_sxv0, ?sextw_sxv1. step. if_false.
  (* [comment removed for export] *)
  step. rewrite addiw_m1_word.
  step. rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range). rewrite sxv_land.
  step.
  (* [comment removed for export] *)
  assert (AI31 : Z.land ai 31 = ai).
  { change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_small. lia. }
  assert (ACT : act = y - 1) by (unfold act, mask_upto, y; reflexivity).
  assert (E1 : Z.land f (- y) = Z.ldiff f (y - 1)) by (unfold y; apply land_neg_pow2; lia).
  assert (Ypos : 0 < y) by (unfold y; apply Z.pow_pos_nonneg; lia).
  pose proof (land_upper f (y - 1) ltac:(lia) ltac:(lia)) as R1.
  pose proof (ldiff_le f (y - 1) ltac:(lia) ltac:(lia)) as R2.
  pose proof (Z.ldiff_nonneg f (y - 1)) as R3.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR4 : rmrep st4 mX) end.
  { rewrite HG in MUa, CH. unfold st4. rewrite upd_meta_put, ACT. eapply rmrep_put_meta_frame; [exact MR | exact MSL | exact MUa | exact WMa |].
    eapply rw_cells_congr; [ | | | exact CH]; [ | reflexivity | cbn; tauto].
    unfold meta_cells, pw. cbn [cells_bytes cbytes m_prev m_next m_mem m_avail m_freed m_set_avail m_set_freed oconc].
    rewrite meta_word_upd_af. fold mr f. rewrite Hmem, E1. cbn [oconc]. rewrite !le4_sxv by lia. reflexivity. }
  clear MUa WMa.
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1.
  2:{ exfalso. apply MASK. unfold mask. rewrite ACT. apply (proj1 (sxv_zero (Z.land f (y - 1)) ltac:(lia))).
      rewrite ?wz_unsigned in K1 by (apply sxv_range). first [exact K1 | change 18446744073709551615 with (Z.ones 64) in K1; rewrite Z.land_ones in K1 by lia; rewrite Z.mod_small in K1 by apply sxv_range; exact K1]. }
  clear K1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (HRW : ov_read_bytes usegs mX (wa (bv_unsigned gw + 32)) 4 = Some (le4 (Z_to_bv 64 (meta_word mr))))
      by (destruct CH as [[_ B] _]; rewrite (bytes_at_ov_read usegs mX (bv_unsigned gw) _ 32 4 B) by (cbn; lia); reflexivity) end.
  step. step. step.
  rewrite (lw_slli52_srli58_sc mr MW).
  pose proof MW as (_ & _ & SCR & _). fold mr in SCR.
  set (sc := m_sizeclass mr) in *.
  (* [comment removed for export] *)
  step. step. step. if_cases K2; zify_cond K2; change 18446744073709551615 with (Z.ones 64) in K2; rewrite Z.land_ones in K2 by lia.
  - (* [comment removed for export] *)
    assert (NR : (7 <=? sc) && (sc <? 39) = false).
    { destruct (Z.lt_ge_cases sc 7); [apply Bool.andb_false_intro1; apply Z.leb_gt; lia|].
      apply Bool.andb_false_intro2. apply Z.ltb_ge. rewrite Z.mod_small in K2 by lia. lia. }
    apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
    split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
    unfold st5. rewrite decay_bounces_eq. fold sc. rewrite NR. cbn [andb]. exact MR4.
  - (* [comment removed for export] *)
    assert (SC7 : 7 <= sc) by (destruct (Z.le_gt_cases 7 sc); [assumption| exfalso; clear -K2 H SCR; Z.div_mod_to_equations; lia]).
    rewrite Z.mod_small in K2 by lia.
    assert (IR : (7 <=? sc) && (sc <? 39) = true) by (apply andb_true_intro; split; [apply Z.leb_le| apply Z.ltb_lt]; lia).
    (* [comment removed for export] *)
    step.
    pose proof (rmrep_bounces_read st4 _ (sc - 7) (wa (427264 + 880 + (sc - 7))) MR4 ltac:(lia) eq_refl) as RDB.
    change (bounces st4 (sc - 7)) with (bounces st (sc - 7)) in RDB.
    pose proof (BNC (sc - 7)) as BR.
    step. rewrite ?zxb_b8 by lia.
    (* [comment removed for export] *)
    step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
    + (* [comment removed for export] *)
      apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
      split; [rewrite ?HG in MU; exact MU|]. split; [exact WM|]. split; [assumption|].
      unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
      replace (bounces st (sc - 7) =? 0) with true by (symmetry; apply Z.eqb_eq; lia). cbn [andb negb]. exact MR4.
    + (* [comment removed for export] *)
      step. rewrite ?(wz_unsigned (bounces st (sc - 7))) by lia.
      pose proof MR4 as (_ & (_ & _ & _ & _ & X5 & _) & _).
      pose proof (u8arr_store_ok usegs _ _ _ (sc - 7) (Z_to_bv 64 (427256 + (sc + -7) + 888)) X5
                    ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear X5 RDB.
      st1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
        pose proof (rmrep_set_bounce st4 mX (sc - 7) (bounces st (sc - 7) - 1) MR4 ltac:(lia)) as MR5; unfold RCTX in MR5 end.
      rraw_store_finish0 (427264 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) - 1)] MU WM SOK.
      apply evt_done. cbv beta. do 7 eexists. split; [rewrite <- ACT; reflexivity|].
      split; [rewrite ?HG in MU; exact MU|].
      split; [exact WM|]. split; [assumption|].
      unfold st5. rewrite decay_bounces_eq. fold sc. rewrite IR. change (bounces st4 (sc - 7)) with (bounces st (sc - 7)).
      replace (bounces st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb negb]. exact MR5.
Qed.
End AVZ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SPANLOOP.
Variables (size : Z).
Hypothesis SZ : 16 <= size < 2^20.

Lemma rspan_loop_walk : forall (F : nat) (c span : Z)
    (ra sp gp tp t1 t2 s0 s1 a0 a1 a2 a3 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  0 <= c -> 0 <= span -> span + size * (Z.of_nat F + 2) < 2^31 -> c + 1 + Z.of_nat F < 2^31 ->
  span_exit F span size = true -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (t0' t1' a6' : word),
      ms' = MS (mkR ra sp gp tp t0' t1' t2 s0 s1 a0 a1 a2 a3 (wz (span_loop F (c + 1) span size)) (wz size) a6' (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x2f660) fc None m (seg_rom usegs))
    (MS (mkR ra sp gp tp (wz span) t1 t2 s0 s1 a0 a1 a2 a3 (wz c) (wz size) (wz (span + size - 1)) (Z_to_bv 64 4096) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x2f64c) fc None m (seg_rom usegs)).
Proof.
  induction F as [|F IH]; intros until m; intros C0 S0 SB CB EX MI; [discriminate|].
  cbn [span_exit] in EX. cbn [span_loop].
  rewrite Nat2Z.inj_succ in SB, CB.
  pose proof (lxor_range31 span (span + size - 1) ltac:(lia) ltac:(lia)) as XR.
  (* [comment removed for export] *)
  step. rewrite ?wz_unsigned by lia.
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (span + size))) with (wz (span + size)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (c + 1))) with (wz (c + 1)) by (rewrite swrap_word, sxv_small by lia; reflexivity).
  step. rewrite ?wz_unsigned by lia.
  replace (Z_to_bv 64 (bv_swrap 32 (span + size - 1 + size))) with (wz (span + size + size - 1)) by (rewrite swrap_word, sxv_small by lia; unfold wz; f_equal; lia).
  rewrite (Z.lxor_comm (span + size - 1) span).
  (* [comment removed for export] *)
  step. if_cases K.
  - (* [comment removed for export] *)
    assert (LT : Z.lxor span (span + size - 1) < 4096).
    { unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_lt in K. exact K. }
    replace (Z.lxor span (span + size - 1) <? 4096) with true in EX |- * by (symmetry; apply Z.ltb_lt; exact LT).
    replace (c + 2) with (c + 1 + 1) by lia.
    eapply (IH (c + 1) (span + size)); try assumption; try lia.
  - assert (GE : ~ Z.lxor span (span + size - 1) < 4096).
    { intros LT. unfold bv_lts, wz in K. rewrite !signed_wz_small in K by lia. apply Z.ltb_ge in K. lia. }
    replace (Z.lxor span (span + size - 1) <? 4096) with false by (symmetry; apply Z.ltb_ge; lia).
    apply evt_done. do 3 eexists. reflexivity.
Qed.
End SPANLOOP.
Lemma ai_byte_land224 w v : 0 <= w -> 0 <= v ->
  Z.land ((Z.lor (Z.land v 31) (Z.land w 224)) mod 256) 31 = Z.land v 31.
Proof.
  intros Hw Hv. apply Z.bits_inj'. intros n Hn.
  change 256 with (2^8). change 31 with (Z.ones 5).
  rewrite !Z.land_spec, Z.testbit_mod_pow2, Z.lor_spec, !Z.land_spec, !Z.testbit_ones by lia.
  replace 224 with (Z.shiftl 7 5) by reflexivity.
  destruct (Z.ltb_spec n 5).
  - rewrite Z.shiftl_spec_low by lia. replace (n <? 8) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_true_r, andb_false_r, orb_false_r. reflexivity.
  - replace (0 <=? n) with true by (symmetry; apply Z.leb_le; lia). cbn [andb]. rewrite !andb_false_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section ACT.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr) (sc mask : Z).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let ai0 := g_active_idx gh.
Hypothesis MR : rmrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis SC : 0 <= sc < 48.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI0 : 0 <= ai0 <= 31.
Hypothesis MASKR : 0 <= mask < 2^32.

(* [comment removed for export] *)
Ltac ract_prefix CH w8 :=
  rmchunk MR MSL CH; fold mr G in CH; fold G in CH; rewrite Hmem in CH; cbn [oconc] in CH;
  step;
  let RD8 := fresh "RD8" in let L8 := fresh "L8" in
  destruct (rmrep_group_read st _ b gh MR Hgh) as (_ & w8 & RD8 & L8); unfold wa in RD8;
  let W8R := fresh "W8R" in
  pose proof (bv_unsigned_in_range _ w8) as W8R; change (bv_modulus 8) with 256 in W8R;
  step;
  let W8M := fresh "W8M" in
  assert (W8M : bv_unsigned w8 mod 32 = ai0) by (unfold ai0; rewrite <- L8; change 31 with (Z.ones 5); rewrite Z.land_ones by lia; reflexivity);
  step; unfold zxb; rewrite (unsigned_lit (bv_unsigned w8)) by lia; rewrite (sllw2_word (bv_unsigned w8)) by lia; rewrite W8M;
  step; rewrite addiw_m1_word; change (2 ^ (ai0 + 1) - 1) with (mask_upto ai0);
  step; rewrite ?(wz_unsigned (sxv _)) by (apply sxv_range); rewrite sxv_land.

(* [comment removed for export] *)
Lemma ract_skip_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
  Z.land mask (mask_upto ai0) <> 0 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' a3' a4' : word),
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x2f24c) fc None m (seg_rom usegs))
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x2f224) fc None m (seg_rom usegs)).
Proof.
  intros until fc. intros NZ MI. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  pose proof (land_upper (mask_upto ai0) mask ltac:(lia) ltac:(lia)) as LR.
  step. if_cases K; zify_cond K.
  2:{ exfalso. apply NZ. rewrite Z.land_comm. apply (proj1 (sxv_zero (Z.land (mask_upto ai0) mask) ltac:(lia))).
      rewrite ?wz_unsigned in K by (apply sxv_range).
      first [exact K | change 18446744073709551615 with (Z.ones 64) in K; rewrite Z.land_ones in K by lia; rewrite Z.mod_small in K by apply sxv_range; exact K]. }
  apply evt_done. do 4 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ract_next_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (mn : aptr),
  Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some mn -> mn <> g -> meta_slot st mn -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' a3' a4' : word) m',
      ms' = MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (conc st mn)) a1' a2' a3' a4' a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x2f24c) fc None m' (seg_rom usegs)
      /\ munch [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (set_active sc (Some mn) st) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x2f224) fc None m (seg_rom usegs)).
Proof.
  intros until mn. intros ZR GN NEn MSn MI. unfold rt1_regs.
  pose proof (munch_refl [(RCTX + 80 + 8 * sc, RCTX + 80 + 8 * sc + 8)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  pose proof (rmeta_slot_bounds st m mn MR MSn) as (Npos & NC & NI & _ & _).
  pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
  assert (NEG : conc st mn <> G) by (intros E; apply NEn; eapply rconc_meta_inj; [exact MR| exact MSL| exact MSn| exact E]).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  step. if_cases K; zify_cond K.
  { exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
  clear K.
  (* [comment removed for export] *)
  rewrite GN in CH. cbn [oconc] in CH.
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. apply NEG. exact K. } clear K.
  (* [comment removed for export] *)
  clear CH.
  pose proof MR as (_ & (_ & ACTS & _) & _).
  pose proof (u64arr_store_ok usegs _ _ (actives st) sc (Z_to_bv 64 (427264 + 80 + 8 * sc)) ACTS
                ltac:(rewrite actives_length; lia) ltac:(unfold wa, RCTX; f_equal; lia)) as SOK. clear ACTS.
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (rmrep_set_active st mX sc (Some mn) MR SC) as MR2; unfold RCTX in MR2 end.
  rraw_store_finish0 (427264 + 80 + 8 * sc) (le8 (pw st (Some mn))) MU WM SOK.
  (* [comment removed for export] *)
  step.
  apply evt_done. do 5 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption| exact MR2].
Qed.
(* [comment removed for export] *)
Lemma rspan_tail_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a3 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc (cnt2 wv : Z),
  1 <= cnt2 <= 32 -> 0 <= wv < 256 ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  g_meta gh = Some g -> m_avail mr = 0 -> mem_inv usegs m ->
  evt usegs (fun ms' => exists (a1' a2' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3 a4' a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
                   (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x2f258) fc None m' (seg_rom usegs)
      /\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) (Z_to_bv 64 (conc st b)) (Z_to_bv 64 wv) a3 (Z_to_bv 64 cnt2) a5 a6 a7 s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
             (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x2f670) fc None m (seg_rom usegs)).
Proof.
  intros until wv. intros C2R WVR UNK GM AV0 MI.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
  pose proof MR as (_ & _ & _ & _ & GR & _). destruct (GR b gh Hgh) as (w8o & RWB & Hw8o). clear GR.
  unfold RCTX, RMLOCK, RSSP_GUARD in *. atop_facts.
  pose proof (munch_refl [(conc st b, conc st b + 9)]%Z m) as MUb. pose proof (wmono_refl usegs m) as WMb.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (cnt2 + -1)) by lia. step. rewrite ?(unsigned_lit wv) by lia. step.
  pose proof (land_upper (cnt2 + -1) 31 ltac:(lia) ltac:(lia)) as L2.
  pose proof (land_upper wv 224 ltac:(lia) ltac:(lia)) as L1.
  rewrite ?(unsigned_lit (Z.land (cnt2 + -1) 31)), ?(unsigned_lit (Z.land wv 224)) by lia.
  set (nbv := Z.lor _ _).
  (* [comment removed for export] *)
  step. rewrite (le1_mod nbv). mem_after_store.
  pose proof (Z.lor_nonneg (Z.land (cnt2 + -1) 31) (Z.land wv 224)) as NBpos.
  pose proof (Z.mod_pos_bound nbv 256 ltac:(lia)) as NBR.
  lazymatch goal with H : rw_cells usegs ?mX (conc st b) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR2 : rmrep (set_group_active_idx b (cnt2 - 1) st) mX);
    [ eapply (rmrep_set_group_ai st m mX b g (g_active_idx gh) (cnt2 - 1) (b8 (nbv mod 256)) MR); [ | exact UNK | exact MUb | exact WMb | | ]
    | ] end.
  { rewrite Hgh. destruct gh as [gm gai]. cbn in GM |- *. subst gm. reflexivity. }
  { lazymatch goal with H : rw_cells usegs _ (conc st b) _ |- _ => rewrite GM in H; exact H end. }
  { rewrite b8_unsigned by lia. subst nbv. replace (cnt2 - 1) with (cnt2 + -1) by lia. apply ai_byte_land224; lia. }
  (* [comment removed for export] *)
  assert (EA2 : s_areas (set_group_active_idx b (cnt2 - 1) st) = s_areas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (ER2 : s_regions (set_group_active_idx b (cnt2 - 1) st) = s_regions st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (EM2 : s_metas (set_group_active_idx b (cnt2 - 1) st) = s_metas st) by (unfold set_group_active_idx; destruct (get_group st b); reflexivity).
  assert (MS2 : meta_slot (set_group_active_idx b (cnt2 - 1) st) g) by (eapply meta_slot_same_areas; [exact EA2| exact MSL]).
  rmchunk MR2 MS2 CH.
  replace (get_meta_rec (set_group_active_idx b (cnt2 - 1) st) g) with mr in CH by (unfold mr, get_meta_rec; rewrite EM2; reflexivity).
  replace (conc (set_group_active_idx b (cnt2 - 1) st) g) with G in CH by (unfold G, conc, get_region; rewrite ER2; reflexivity).
  rewrite AV0 in CH.
  step. step. if_cases K2; zify_cond K2. { exfalso. apply K2. reflexivity. } step.
  apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact MUb|]. split; [exact WMb|]. split; [assumption| exact MR2].
Qed.

(* [comment removed for export] *)
Lemma ract_span_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc,
  Z.land mask (mask_upto ai0) = 0 -> m_next mr = Some g -> mw_ok mr -> 1 <= m_sizeclass mr < 48 ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  g_meta gh = Some g -> m_avail mr = 0 ->
  mem_inv usegs m ->
  let sc' := m_sizeclass mr in
  let cnt := ai0 + 2 in
  let size := size_class sc' * UNIT in
  let span := UNIT + size * cnt in
  let cnt1 := span_loop 300 cnt span size in
  let cnt2 := if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1 in
  evt usegs (fun ms' => exists (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 G) a1' a2' a3' a4' a5' a6' a7' s2 s3 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (RCTX + 80 + 8 * sc))
                   (Z_to_bv 64 RMLOCK) (Z_to_bv 64 (RMLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x2f258) fc None m' (seg_rom usegs)
      /\ munch [(conc st b, conc st b + 9)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ rmrep (set_group_active_idx b (cnt2 - 1) st) m')
    (MS (rt1_regs sc ra sp gp tp t0 t1 t2 s1 (Z_to_bv 64 G) a1 a2 (wz (sxv mask)) (Z_to_bv 64 2) a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x2f224) fc None m (seg_rom usegs)).
Proof.
  intros until fc. intros ZR GN MW SCR UNK GM AV0 MI sc' cnt size span cnt1 cnt2. unfold rt1_regs.
  pose proof (rmeta_slot_bounds st m g MR MSL) as (Gpos & GC & GI & _ & _). fold G in Gpos, GC, GI.
  pose proof (rgroup_bounds st m b gh MR Hgh) as (B0 & BC & BI & _).
  pose proof (sxv_range mask) as RM. pose proof (sxv_range (mask_upto ai0)) as RU.
  pose proof (meta_word_range _ MW) as MWR. pose proof MW as (LI & FB & _ & ML).
  pose proof (size_class_range sc' ltac:(lia)) as SZR.
  unfold RCTX, RMLOCK, RSSP_GUARD, RSIZE_CLASSES in *. atop_facts.
  ract_prefix CH w8.
  pose proof (MallocKit_A3.mask_upto_range ai0 AI0) as MUR.
  step. if_cases K; zify_cond K.
  { exfalso. apply K. rewrite (Z.land_comm (mask_upto ai0) mask), ZR. reflexivity. }
  clear K.
  (* [comment removed for export] *)
  rewrite GN, AV0 in CH. cbn [oconc] in CH. fold G in CH.
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit (bv_unsigned w8)) by lia. rewrite L8. fold ai0. step. step. step. step.
  (* [comment removed for export] *)
  assert (W5R : 0 <= Z.shiftr (meta_word mr) 5 < 2^64).
  { rewrite Z.shiftr_div_pow2 by lia. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. step. rewrite (unsigned_lit (Z.shiftr (meta_word mr) 5)) by lia. rewrite (meta_word_sc2 mr MW). fold sc'.
  step.
  lazymatch goal with HI : mem_inv usegs ?mc |- _ =>
    pose proof (rsize_classes_read mc sc' HI ltac:(lia)) as SCRD; unfold RSIZE_CLASSES in SCRD end.
  step. rewrite zx16_wz by lia. clear SCRD.
  fold cnt.
  assert (SZB : 16 <= size <= 131056) by (unfold size, UNIT; lia).
  assert (CNB : 2 <= cnt <= 33) by (unfold cnt; lia).
  assert (PR : 0 <= cnt * size <= 33 * 131056) by nia.
  assert (EX : span_exit 300 span size = true) by (unfold span, size, cnt, UNIT; apply span_exit_ok; lia).
  assert (SPB : span = cnt * size + 16) by (unfold span, UNIT; lia).
  assert (Esz : size = size_class sc' * 16) by reflexivity. assert (Ecnt : cnt = ai0 + 2) by reflexivity.
  pose proof (span_loop_bounds 300 cnt span size) as CB. fold cnt1 in CB. change (Z.of_nat 300) with 300 in CB.
  assert (Ec2 : cnt2 = (if m_last_idx mr + 1 <? cnt1 then m_last_idx mr + 1 else cnt1)) by reflexivity.
  assert (Ec1 : cnt1 = span_loop 300 cnt span size) by reflexivity.
  clearbody size cnt span cnt1 cnt2.
  (* [comment removed for export] *)
  step. step. rewrite (unsigned_lit ai0), Z.shiftl_mul_pow2 by lia. step.
  step. rewrite (wz_unsigned (size_class sc')), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite <- Esz.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (ai0 * 16 + 48)), ?(wz_unsigned (size_class sc')) by lia.
  replace ((ai0 * 16 + 48) * size_class sc') with (span + size - 16) by (rewrite SPB, Esz, Ecnt; lia).
  step. rewrite ?(unsigned_lit size), ?(unsigned_lit cnt) by lia. replace (size * cnt) with (cnt * size) by lia.
  step. rewrite ?(unsigned_lit (span + size - 16)) by lia. rewrite swrap_word, sxv_small by lia.
  replace (span + size - 16 + 15) with (span + size - 1) by lia.
  step. rewrite ?(unsigned_lit (cnt * size)) by lia. rewrite swrap_word, sxv_small by lia. rewrite <- SPB.
  step.
  (* [comment removed for export] *)
  eapply evt_cut.
  { change (Z_to_bv 64 (ai0 + 1)) with (wz (ai0 + 1)). change (Z_to_bv 64 size) with (wz size).
    eapply (rspan_loop_walk size ltac:(lia) 300 (ai0 + 1) span); try assumption; try (change (Z.of_nat 300) with 300; lia). }
  intros ms' (t0' & t1' & a6' & ->). replace (ai0 + 1 + 1) with cnt by lia. rewrite <- Ec1.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (meta_word mr)) by lia. rewrite (meta_word_last_idx mr MW).
  step.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned cnt1), ?unsigned_lit in K by lia.
  - replace (wz cnt1) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [lia| reflexivity]).
    assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
    eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
    cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
  - (* [comment removed for export] *)
    step.
    replace (Z_to_bv 64 (m_last_idx mr + 1)) with (Z_to_bv 64 cnt2) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); [reflexivity| f_equal; lia]).
    assert (C2R : 1 <= cnt2 <= 32) by (rewrite Ec2; destruct (Z.ltb_spec (m_last_idx mr + 1) cnt1); lia). clear K.
    eapply evt_mono. { eapply (rspan_tail_walk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fr fc cnt2 (bv_unsigned w8)); [lia| lia| exact UNK| exact GM| exact AV0| assumption]. }
    cbv beta. intros ms2 (a1'' & a2'' & a4'' & m' & -> & MU & WM & MI' & MR'). do 10 eexists. split; [reflexivity|]. eauto.
Qed.
End ACT.
End CANSEC1.
