(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA Atp_objpA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition obj_locA (j0 : list byte) (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word) : list cell :=
  [CB 24 j0; C8 w24; C8 w32; C8 w40; C8 w48; C8 w56; C8 w64; C8 w72; C8 w80; C8 w88; C8 w96; C8 w104; C8 w112; C8 w120; C8 w128].

Definition pz (z : Z) : cell := C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))).

Definition obj_sh (v4 v5 v6 : Z) (js4 : list byte) : list cell :=
  [pz (-15); pz (-15); pz (-15); pz (-15); pz v4; pz v5; pz v6; pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); CB 4 js4].

Definition obj_hdr : list cell := [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x13317); C8 (Z_to_bv 64 0xb5e4c)].

Lemma pz_0 : pz 0 = C1 (Z_to_bv 8 0).
Proof. reflexivity. Qed.

Lemma shl_mod_smallA : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> (Z.shiftl b k) mod 18446744073709551616 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.

Lemma land_shiftl_smallA : forall x y n, 0 <= n -> 0 <= x < 2^n -> Z.land (Z.shiftl y n) x = 0.
Proof.
  intros x y n Hn Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    assert (LG : Z.log2 x < i).
    { apply (Z.lt_le_trans _ n); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite (Z.bits_above_log2 x i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shiftl_smallA : forall x y n, 0 <= n -> 0 <= x < 2^n -> 0 <= y -> Z.lor (Z.shiftl y n) x = y * 2^n + x.
Proof.
  intros x y n Hn Hx Hy. rewrite <- Z.lxor_lor by (apply land_shiftl_smallA; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_smallA; lia). rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.
Lemma le32_of_lbu4A : forall b0 b1 b2 b3, 0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b2 < 256 -> 0 <= b3 < 256 ->
  Z.lor (Z.lor (Z.shiftl b3 24) (Z.shiftl b2 16)) (Z.lor (Z.shiftl b1 8) b0) = b0 + 2^8 * b1 + 2^16 * b2 + 2^24 * b3.
Proof.
  intros b0 b1 b2 b3 H0 H1 H2 H3.
  rewrite (lor_shiftl_smallA b0 b1 8) by lia.
  replace (Z.shiftl b3 24) with (Z.shiftl (Z.shiftl b3 8) 16) by (rewrite Z.shiftl_shiftl by lia; reflexivity).
  rewrite <- Z.shiftl_lor. rewrite (lor_shiftl_smallA b2 b3 8) by lia.
  rewrite (lor_shiftl_smallA (b1 * 2^8 + b0) (b3 * 2^8 + b2) 16); [lia| lia| |lia].
  change (2^16) with (2^8 * 2^8). lia.
Qed.
Lemma land64_shl_smallA : forall b k, 0 <= b < 256 -> 0 <= k <= 24 -> Z.land (Z.shiftl b k) 18446744073709551615 = Z.shiftl b k.
Proof.
  intros b k Hb Hk. rewrite land64_mod. apply Z.mod_small. rewrite Z.shiftl_mul_pow2 by lia.
  assert (0 < 2 ^ k <= 2 ^ 24) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_le_mono_r; lia]). nia.
Qed.

Lemma lor7_eqA : forall L, 0 <= L -> Z.lor L 7 = L - L mod 8 + 7.
Proof.
  intros L HL. pose proof (Z.div_mod L 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as MB.
  assert (E1 : L = Z.lor (Z.shiftl (L / 8) 3) (L mod 8)).
  { rewrite lor_shiftl_smallA; [| lia| lia| apply Z.div_pos; lia]. change (2 ^ 3) with 8. lia. }
  rewrite E1 at 1. rewrite <- Z.lor_assoc.
  assert (E2 : Z.lor (L mod 8) 7 = 7).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
    destruct (Z.lt_ge_cases i 3) as [Hi3|Hi3].
    - replace (Z.testbit 7 i) with true; [apply Bool.orb_true_r|]. symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_low. lia.
    - replace (Z.testbit 7 i) with false. 2:{ symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_high. lia. }
      rewrite Bool.orb_false_r. destruct (Z.eq_dec (L mod 8) 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 3); [| lia]. apply Z.log2_lt_pow2; lia. }
  rewrite E2. rewrite lor_shiftl_smallA; [| lia| lia| apply Z.div_pos; lia]. change (2 ^ 3) with 8. lia.
Qed.
Lemma str_sz_evenA : forall L, 0 <= L -> str_sz L mod 2 = 0.
Proof.
  intros L HL. unfold str_sz. destruct (Z.eqb_spec L 23); [reflexivity|]. rewrite lor7_eqA by lia.
  pose proof (Z.div_mod L 8 ltac:(lia)). pose proof (Z.mod_pos_bound L 8 ltac:(lia)).
  replace (L - L mod 8 + 7 + 1) with ((L / 8 + 1) * 4 * 2) by lia. apply Z_mod_mult.
Qed.

Section ObjW.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_p4 : forall (K : machine_state -> Prop) (q b P L L0 Lk f : Z)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (je jt : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 <= Lk < 2^47 ->
    rw_cells asegs m (b + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); CB 4 je; CB 4 jt] ->
    (forall (m1 : mem), Lk = 0 -> munch [(b + 160, b + 184)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (b + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
       K (MS (mkR (wz 0xb603c) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz 12) x11 x12 x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) (wz L) (wz (P + 1)) (wz f) (wz L0) (wz Lk) x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb60a0) fc None m1 (seg_rom asegs))) ->
    (forall (m1 : mem), 0 < Lk -> munch [(b + 160, b + 184)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (b + 160) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 12); CB 4 jt] ->
       K (MS (mkR (wz 0xb6058) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (P + 1)) (wz 126) (wz Lk) x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) (wz L) (wz (P + 1)) (wz f) (wz L0) (wz Lk) x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz e_memchr) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb603c) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 160)) x11 x12 x13 x14 x15 x16 x17
                       (wz f) (wz (shad f)) (wz L) (wz (P + 1)) (wz f) (wz L0) (wz Lk) x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb603c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jt. intros MI LO B0 B1 QH LK REC KNO KCHR.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_memchr in *.
    pose proof (munch_refl [(b + 160, b + 184)] m) as MU. pose proof (wmono_refl asegs m) as WM.

    astep. lstep. name_mem m1.

    step. if_cases K0; zify_cond K0.
    - eapply evt_eq; [| apply evt_done; apply (KNO m1); [lia| exact MU| exact WM| assumption| assumption]]. atp_st_eq.
    -
      astep. step. step. step.
      eapply evt_eq; [| apply evt_done; apply (KCHR m1); [rewrite ?land64_mod in K0; lia| exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_p5 : forall (K : machine_state -> Prop) (q b P L L0 Lk f r v4 v5 v6 : Z) (kbuf : list byte)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x25 x26 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 js4 jS : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 < Lk < 2^47 -> 0 < P -> P + 1 + Lk < 2^47 ->
    0x6ca000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    Z.of_nat (length kbuf) = Lk -> r = memchr_res (P + 1) 126 Lk kbuf ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128) ->
    rw_cells asegs m (shad f) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m (f + 32) [CB 24 jS] ->

    (find_byte 126 kbuf = None ->
       K (MS (mkR (wz 0xb6058) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz 0) x11 x12 x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) (wz L) (wz (P + 1)) (wz f) (wz L0) (wz Lk) x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb60a0) fc None m (seg_rom asegs))) ->

    (forall (m1 : mem) (ix : nat) (xa0 : word) (jS' : list byte), find_byte 126 kbuf = Some ix -> Lk < 23 ->
       munch [(b, b + 136); (shad f, shad f + 16); (f + 32, f + 56)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b (obj_locA j0 w24 w32 w40 w48 w56 (Z_to_bv 64 f) (Z_to_bv 64 f) w80 w88 w96 w104 w112 w120 w128) ->
       rw_cells asegs m1 (shad f) (obj_sh 0 0 0 js4) -> rw_cells asegs m1 (f + 32) [C1 (Z_to_bv 8 (2 * Lk)); CB 23 jS'] ->
       K (MS (mkR (wz 0xb6058) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) xa0 x11 x12 x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) (wz L) (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) (wz (Z.of_nat ix)) (wz (f + 33)) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb637c) fc None m1 (seg_rom asegs))) ->

    (forall (m1 : mem) (ix : nat), find_byte 126 kbuf = Some ix -> 23 <= Lk ->
       munch [(b, b + 136); (shad f, shad f + 16); (f + 32, f + 56)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b (obj_locA j0 w24 w32 w40 w48 w56 (Z_to_bv 64 f) (Z_to_bv 64 f) w80 w88 w96 w104 w112 w120 w128) ->
       rw_cells asegs m1 (shad f) (obj_sh 0 0 0 js4) -> rw_cells asegs m1 (f + 32) [CB 24 jS] ->
       K (MS (mkR (wz 0xb6368) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (str_sz Lk)) x11 x12 x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) (wz (str_sz Lk)) (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) (wz (Z.of_nat ix)) x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz OPNEW_A) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6058) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz r) x11 x12 x13 x14 x15 x16 x17
                       (wz f) (wz (shad f)) (wz L) (wz (P + 1)) (wz f) (wz L0) (wz Lk) x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb6058) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jS. intros MI LO B0 B1 QH LK P0 PH FLO FHI FSH S0 SHI LKB ER LOCA SH STR KNO KSSO KHEAP.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OPNEW_A in *.
    pose proof (munch_refl [(b, b + 136); (shad f, shad f + 16); (f + 32, f + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_locA in LOCA. unfold obj_sh, pz in SH. unfold shad, SHB in *.
    unfold memchr_res in ER. rewrite <- LKB, Nat2Z.id, firstn_all in ER.
    destruct (find_byte 126 kbuf) as [ix|] eqn:FB.
    2:{
        subst r. step. if_true. eapply evt_eq; [| apply evt_done; apply (KNO eq_refl)]. atp_st_eq. }
    pose proof (find_byte_Some _ _ _ FB) as (IXL & _). subst r.

    step. if_dead1 by P0. astep. replace (P + 1 + Z.of_nat ix - (P + 1)) with (Z.of_nat ix) by lia. astep. step. if_dead1 by IXL LKB LK.

    step. astep. lstep. lstep. lstep.

    step. if_dead1 by LK. astep. step. astep. name_mem m1.

    step. if_cases K1; zify_cond K1.
    -
      rewrite ?land64_mod in K1.
      pose proof (lor7_eqA Lk ltac:(lia)) as L7. pose proof (Z.mod_pos_bound Lk 8 ltac:(lia)) as M8.
      assert (J : forall xa0 : word, evt asegs K (MS (mkR (wz 0xb6058) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) xa0 x11 x12 x13 x14 x15 x16 x17
                         (wz f) (wz (f / 8 + 2147450880)) (wz (str_sz Lk)) (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) (wz (Z.of_nat ix)) x26 (wz 2147450880) x28 x29 x30 x31)
                         F (wz 0xb6360) fc None m1 (seg_rom asegs))).
      { intros xa0. step. step.
        eapply evt_eq; [| apply evt_done; apply (KHEAP m1 ix eq_refl); [lia| exact MU| exact WM| assumption| assumption| assumption| assumption]]. atp_st_eq. }
      astep. rewrite L7. step. if_cases KS; zify_cond KS.
      + astep. replace (Lk - Lk mod 8 + 8) with (str_sz Lk)
          by (unfold str_sz; destruct (Z.eqb_spec Lk 23) as [E23|N23]; [exfalso; subst; cbn in KS; lia| rewrite L7; lia]).
        eapply evt_eq; [| apply J]. atp_st_eq.
      + astep. step. replace (Z_to_bv 64 26) with (Z_to_bv 64 (str_sz Lk))
          by (unfold str_sz; destruct (Z.eqb_spec Lk 23) as [E23|N23]; [reflexivity| exfalso; rewrite ?land64_mod in KS; lia]).
        eapply evt_eq; [| apply J]. atp_st_eq.
    -
      rewrite ?land64_mod in K1.
      apply (rw_cells_split_CB asegs _ _ [] 24 jS [] [1; 23]%nat) in STR; [| reflexivity]. cbn [mk_CB_cells app] in STR.
      astep. nstep. rewrite (a_u64_small (2 * Lk)) in * by lia. astep. step. name_mem m2.
      eapply evt_eq; [| apply evt_done; eapply (KSSO m2 ix _ _ eq_refl); [lia| exact MU| exact WM| assumption| assumption| assumption| ]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells asegs m2 (f + 32) _ |- _ => exact H end.
  Qed.

  Lemma obj_p6a : forall (K : machine_state -> Prop) (q b P L0 Lk f A esc : Z)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jS : list byte),
    mem_inv asegs m -> 0x6ca000 <= f -> f + 120 <= ae_lo E -> 0 <= Lk < 2^47 -> 0 < A < 2^47 ->
    rw_cells asegs m (f + 32) [CB 24 jS] ->
    (forall (m1 : mem), munch [(f + 32, f + 56)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (f + 32) [C8 (Z_to_bv 64 (str_sz Lk + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 A)] ->
       K (MS (mkR (wz 0xb6368) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz A) x11 x12 x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) (wz (str_sz Lk + 1)) (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) (wz esc) (wz A) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb637c) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6368) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz A) x11 x12 x13 x14 x15 x16 x17
                       (wz f) (wz (shad f)) (wz (str_sz Lk)) (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) (wz esc) x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb6368) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jS. intros MI FLO FHI LK HA STR HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(f + 32, f + 56)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (str_sz_bound Lk ltac:(lia)) as SZB.
    apply (rw_cells_split_CB asegs _ _ [] 24 jS [] [8; 8; 8]%nat) in STR; [| reflexivity]. cbn [mk_CB_cells app] in STR.

    step. astep. step. step. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_p6b : forall (K : machine_state -> Prop) (q b P L0 Lk f D : Z)
      (gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x25 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w112 w120 w128) ->
    (forall (m1 : mem), munch [(b, b + 136)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 b (obj_locA j0 w24 w32 w40 w48 (Z_to_bv 64 L0) w64 w72 w80 w88 w96 (Z_to_bv 64 (P + 1)) w112 w120 w128) ->
       K (MS (mkR (wz 0xb6394) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz D) (wz (P + 1)) (wz Lk) x13 x14 x15 x16 x17
                  (wz f) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) x25 (wz D) (wz 2147450880) x28 x29 x30 x31)
             F (wz e_asan_memmove) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6368) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz f) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) x25 (wz D) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb637c) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH LOCA HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_asan_memmove in *.
    pose proof (munch_refl [(b, b + 136)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold obj_locA in LOCA.

    step. step. step. step. step. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_p7 : forall (K : machine_state -> Prop) (q b P L0 Lk f D esc zl zn : Z)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jn : list byte),
    mem_inv asegs m -> 0 < D -> D + Lk + 1 < 2^47 -> 0 <= Lk -> 0x6ca000 <= f -> f + 120 < 2^47 ->
    shz m zl zn -> zl <= D + Lk < zl + zn ->
    rw_cells asegs m (D + Lk) [CB 1 jn] ->
    (forall (m1 : mem), munch [(D + Lk, D + Lk + 1)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (D + Lk) [C1 (Z_to_bv 8 0)] ->
       K (MS (mkR (wz 0xb6394) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz 0x233b0) (wz 0x233b8) x12 x13 x14 x15 x16 x17
                  (wz 49) (wz (shad f)) (wz 18446744073709551615) (wz LIT_SLASH_A) (wz (f + 32)) (wz LIT_TILDE_A) (wz (f + 33)) (wz esc) (wz D) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb63c8) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR (wz 0xb6394) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz D) x11 x12 x13 x14 x15 x16 x17
                       (wz f) (wz (shad f)) x20 (wz (P + 1)) (wz (f + 32)) (wz L0) (wz Lk) (wz esc) (wz D) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb6394) fc None m (seg_rom asegs)).
  Proof.
    intros until jn. intros MI D0 DH LK FLO FHI SZ ZR DN HK. unfold LIT_SLASH_A, LIT_TILDE_A.
    pose proof (munch_refl [(D + Lk, D + Lk + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM.

    astep. chk0 SZ (D + Lk). step. if_false.

    astep.
    remember (D + Lk) as DL eqn:EDL.
    lstep. astep. astep. astep. astep. astep. astep. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.
End ObjW.
