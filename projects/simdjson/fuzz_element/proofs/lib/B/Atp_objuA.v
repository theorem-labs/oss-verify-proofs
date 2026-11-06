(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep ZBridge.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow IcptSpec.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface RT_iface2 D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit
     Atp_defsA Atp_kitA Atp_objdA Atp_objpA Atp_objkA Atp_objsA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Definition obj_loc72 (j0 : list byte) (w24 w32 : word) (f out : Z) : list cell :=
  [CB 24 j0; C8 w24; C8 w32; C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 out); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 f)].
Definition pz (z : Z) : cell := C1 (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z))).
Definition obj_sh (v4 v5 v6 : Z) (js4 : list byte) : list cell :=
  [pz (-15); pz (-15); pz (-15); pz (-15); pz v4; pz v5; pz v6; pz (-13); pz (-13); pz (-13); pz (-13); pz (-13); CB 4 js4].
Definition obj_hdr : list cell := [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x1335b); C8 (Z_to_bv 64 0xb867c)].

Lemma land_shiftl_smallB : forall x y n, 0 <= n -> 0 <= x < 2^n -> Z.land (Z.shiftl y n) x = 0.
Proof.
  intros x y n Hn Hx. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i n) as [L|G].
  - rewrite Z.shiftl_spec_low by lia. reflexivity.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; apply Bool.andb_false_r|].
    assert (LG : Z.log2 x < i).
    { apply (Z.lt_le_trans _ n); [| lia]. apply Z.log2_lt_pow2; lia. }
    rewrite (Z.bits_above_log2 x i) by lia. apply Bool.andb_false_r.
Qed.
Lemma lor_shiftl_smallB : forall x y n, 0 <= n -> 0 <= x < 2^n -> 0 <= y -> Z.lor (Z.shiftl y n) x = y * 2^n + x.
Proof.
  intros x y n Hn Hx Hy. rewrite <- Z.lxor_lor by (apply land_shiftl_smallB; lia).
  rewrite <- Z.add_nocarry_lxor by (apply land_shiftl_smallB; lia). rewrite Z.shiftl_mul_pow2 by lia. reflexivity.
Qed.

Lemma lor7_eqB : forall L, 0 <= L -> Z.lor L 7 = L - L mod 8 + 7.
Proof.
  intros L HL. pose proof (Z.div_mod L 8 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as MB.
  assert (E1 : L = Z.lor (Z.shiftl (L / 8) 3) (L mod 8)).
  { rewrite lor_shiftl_smallB; [| lia| lia| apply Z.div_pos; lia]. change (2 ^ 3) with 8. lia. }
  rewrite E1 at 1. rewrite <- Z.lor_assoc.
  assert (E2 : Z.lor (L mod 8) 7 = 7).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
    destruct (Z.lt_ge_cases i 3) as [Hi3|Hi3].
    - replace (Z.testbit 7 i) with true; [apply Bool.orb_true_r|]. symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_low. lia.
    - replace (Z.testbit 7 i) with false. 2:{ symmetry. change 7 with (Z.ones 3). apply Z.ones_spec_high. lia. }
      rewrite Bool.orb_false_r. destruct (Z.eq_dec (L mod 8) 0) as [->|NZ]; [apply Z.bits_0|].
      apply Z.bits_above_log2; [lia|]. apply (Z.lt_le_trans _ 3); [| lia]. apply Z.log2_lt_pow2; lia. }
  rewrite E2. rewrite lor_shiftl_smallB; [| lia| lia| apply Z.div_pos; lia]. change (2 ^ 3) with 8. lia.
Qed.
Lemma str_sz_evenB : forall L, 0 <= L -> str_sz L mod 2 = 0.
Proof.
  intros L HL. unfold str_sz. destruct (Z.eqb_spec L 23); [reflexivity|]. rewrite lor7_eqB by lia.
  pose proof (Z.div_mod L 8 ltac:(lia)). pose proof (Z.mod_pos_bound L 8 ltac:(lia)).
  replace (L - L mod 8 + 7 + 1) with ((L / 8 + 1) * 4 * 2) by lia. apply Z_mod_mult.
Qed.

Section ObjU.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_e0 : forall (K : machine_state -> Prop) (q b out node P L f P1 Lk sl te v4 v5 v6 : Z)
      (gp x1 t0 t1 t2 xa1 xa2 xa3 xa4 xa5 a6 a7 s7 s8 s9 s10 t3 t4 t5 t6 : word) (w24 w32 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 js4 jS : list byte),
    mem_inv bsegs m -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 < Lk < 2^47 -> 0 < P1 -> P1 + Lk < 2^47 ->
    0x6d9000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    rw_cells bsegs m b (obj_loc72 j0 w24 w32 f out) -> rw_cells bsegs m (b + 120) [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 Lk)] ->
    rw_cells bsegs m (shad f) (obj_sh v4 v5 v6 js4) -> rw_cells bsegs m (f + 32) [CB 24 jS] ->

    (forall (m1 : mem) (jS' : list byte), Lk < 23 ->
       munch [(shad f, shad f + 16); (f + 32, f + 56)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (shad f) (obj_sh 0 0 0 js4) -> rw_cells bsegs m1 (f + 32) [C1 (Z_to_bv 8 (2 * Lk)); CB 23 jS'] ->
       K (MS (mkR x1 (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz (2 * Lk)) (wz f) xa2 xa3 xa4 xa5 a6 a7
                  (wz sl) (wz (shad f)) (wz node) (wz L) (wz (f + 32)) (wz te) (wz Lk) (wz P1) (wz (f + 33)) (wz 2147450880) t3 t4 t5 t6)
             F (wz 0xb895c) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem), 23 <= Lk ->
       munch [(shad f, shad f + 16); (f + 32, f + 56)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (shad f) (obj_sh 0 0 0 js4) -> rw_cells bsegs m1 (f + 32) [CB 24 jS] ->
       K (MS (mkR (wz 0xb8948) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz (str_sz Lk)) (wz f) xa2 xa3 xa4 xa5 a6 a7
                  (wz sl) (wz (shad f)) (wz node) (wz (str_sz Lk)) (wz (f + 32)) (wz te) (wz Lk) (wz P1) s10 (wz 2147450880) t3 t4 t5 t6)
             F (wz OPNEW_A) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz te) xa1 xa2 xa3 xa4 xa5 a6 a7
                       (wz sl) (wz (shad f)) (wz node) (wz L) (wz P) s7 s8 s9 s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb8844) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jS. intros MI LO B0 B1 QH LK P10 P1H FLO FHI FSH S0 SHI LOC KSV SH STR KSSO KHEAP.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OPNEW_A in *.
    pose proof (munch_refl [(shad f, shad f + 16); (f + 32, f + 56)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold obj_loc72 in LOC. unfold obj_sh, pz in SH. unfold obj_sh, pz in KSSO, KHEAP. unfold shad, SHB in *.

    step. lstep. lstep. lstep.

    step. astep. step. if_dead1 by LK. step. astep. step. astep. name_mem m1.

    step. if_cases K1; zify_cond K1; rewrite ?land64_mod in K1.
    -
      pose proof (lor7_eqB Lk ltac:(lia)) as L7. pose proof (Z.mod_pos_bound Lk 8 ltac:(lia)) as M8.
      assert (J : evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz 23) (wz f) xa2 xa3 xa4 xa5 a6 a7
                         (wz sl) (wz (f / 8 + 2147450880)) (wz node) (wz (str_sz Lk)) (wz (f + 32)) (wz te) (wz Lk) (wz P1) s10 (wz 2147450880) t3 t4 t5 t6)
                         F (wz 0xb8940) fc None m1 (seg_rom bsegs))).
      { step. step.
        eapply evt_eq; [| apply evt_done; apply (KHEAP m1); [lia| exact MU| exact WM| assumption| assumption| assumption]]. atp_st_eq. }
      astep. rewrite L7. astep. step. if_cases KS; zify_cond KS.
      + astep. replace (Lk - Lk mod 8 + 8) with (str_sz Lk)
          by (unfold str_sz; destruct (Z.eqb_spec Lk 23) as [E23|N23]; [exfalso; subst; cbn in KS; lia| rewrite L7; lia]).
        eapply evt_eq; [| apply J]. atp_st_eq.
      + astep. step. replace (Z_to_bv 64 26) with (Z_to_bv 64 (str_sz Lk))
          by (unfold str_sz; destruct (Z.eqb_spec Lk 23) as [E23|N23]; [reflexivity| exfalso; rewrite ?land64_mod in KS; lia]).
        eapply evt_eq; [| apply J]. atp_st_eq.
    -
      apply (rw_cells_split_CB bsegs _ _ [] 24 jS [] [1; 23]%nat) in STR; [| reflexivity]. cbn [mk_CB_cells app] in STR.
      assert (LK23 : Lk < 23) by (clear - K1; lia).
      astep. nstep. rewrite (a_u64_small (2 * Lk)) in * by lia. astep. name_mem m2. step. if_dead2 by LK.
      eapply evt_eq; [| apply evt_done; eapply (KSSO m2 _ LK23 MU WM); [assumption| assumption| ]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells bsegs m2 (f + 32) _ |- _ => exact H end.
  Qed.

  Lemma obj_p6aB : forall (K : machine_state -> Prop) (q b node L f P1 Lk sl te A : Z)
      (gp t0 t1 t2 xa1 xa2 xa3 xa4 xa5 a6 a7 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (jS : list byte),
    mem_inv bsegs m -> 0x6d9000 <= f -> f + 120 <= ae_lo E -> 0 <= Lk < 2^47 -> 0 < A < 2^47 ->
    rw_cells bsegs m (f + 32) [CB 24 jS] ->
    (forall (m1 : mem), munch [(f + 32, f + 56)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (f + 32) [C8 (Z_to_bv 64 (str_sz Lk + 1)); C8 (Z_to_bv 64 Lk); C8 (Z_to_bv 64 A)] ->
       K (MS (mkR (wz 0xb8948) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz A) xa1 xa2 xa3 xa4 xa5 a6 a7
                  (wz sl) (wz (shad f)) (wz node) (wz (str_sz Lk + 1)) (wz (f + 32)) (wz te) (wz Lk) (wz P1) (wz A) (wz 2147450880) t3 t4 t5 t6)
             F (wz 0xb895c) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb8948) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz A) xa1 xa2 xa3 xa4 xa5 a6 a7
                       (wz sl) (wz (shad f)) (wz node) (wz (str_sz Lk)) (wz (f + 32)) (wz te) (wz Lk) (wz P1) s10 (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb8948) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jS. intros MI FLO FHI LK HA STR HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(f + 32, f + 56)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof (str_sz_bound Lk ltac:(lia)) as SZB.
    apply (rw_cells_split_CB bsegs _ _ [] 24 jS [] [8; 8; 8]%nat) in STR; [| reflexivity]. cbn [mk_CB_cells app] in STR.

    step. astep. step. step. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_p6bB : forall (K : machine_state -> Prop) (q b node f P1 Lk sl te D : Z)
      (gp x1 t0 t1 t2 xa0 xa1 xa2 xa3 xa4 xa5 a6 a7 s5x t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    0x6d9000 <= f -> f + 120 <= ae_lo E ->
    K (MS (mkR (wz 0xb896c) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz D) (wz P1) (wz Lk) xa3 xa4 xa5 a6 a7
               (wz sl) (wz (shad f)) (wz node) s5x (wz (f + 32)) (wz te) (wz Lk) (wz P1) (wz D) (wz 2147450880) t3 t4 t5 t6)
         F (wz e_asan_memmove) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) xa0 xa1 xa2 xa3 xa4 xa5 a6 a7
                       (wz sl) (wz (shad f)) (wz node) s5x (wz (f + 32)) (wz te) (wz Lk) (wz P1) (wz D) (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb895c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until m. intros FLO FHI HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_asan_memmove in *.

    step. step. step. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_p7B : forall (K : machine_state -> Prop) (q b out node f P1 Lk sl te D zl zn : Z)
      (gp t0 t1 t2 xa0 xa1 xa2 xa3 xa4 xa5 a6 a7 s5x t3 t4 t5 t6 : word) (w24 w32 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 jn : list byte),
    mem_inv bsegs m -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 <= sl < 2^64 -> 0 <= node < 2^64 ->
    0 < D -> D + Lk + 1 <= ae_lo E -> 0 <= Lk -> 0x6d9000 <= f -> f + 120 < 2^47 ->
    (forall m', munch [(b + 24, b + 40); (D + Lk, D + Lk + 1)] m m' -> wmono bsegs m m' -> shz m' zl zn) -> zl <= D + Lk < zl + zn ->
    rw_cells bsegs m b (obj_loc72 j0 w24 w32 f out) -> rw_cells bsegs m (D + Lk) [CB 1 jn] ->
    (forall (m1 : mem), munch [(b + 24, b + 40); (D + Lk, D + Lk + 1)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 b (obj_loc72 j0 (Z_to_bv 64 sl) (Z_to_bv 64 node) f out) -> rw_cells bsegs m1 (D + Lk) [C1 (Z_to_bv 8 0)] ->
       K (MS (mkR (wz 0xb896c) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) (wz 0x23998) (wz 0x239a0) xa2 xa3 xa4 xa5 a6 a7
                  (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz te) (wz (f + 33)) (wz P1) (wz 18446744073709551615) (wz 2147450880) t3 t4 t5 t6)
             F (wz 0xb89b0) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb896c) (wz b) gp (wz TPV) t0 t1 t2 (wz q) (wz b) xa0 xa1 xa2 xa3 xa4 xa5 a6 a7
                       (wz sl) (wz (shad f)) (wz node) s5x (wz (f + 32)) (wz te) (wz Lk) (wz P1) (wz D) (wz 2147450880) t3 t4 t5 t6)
                   F (wz 0xb896c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jn. intros MI LO B0 B1 QH SLR NDR D0 DH LK FLO FHI SZ ZR LOC DN HK. unfold LIT_SLASH_A, LIT_TILDE_A in *.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(b + 24, b + 40); (D + Lk, D + Lk + 1)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold obj_loc72 in LOC. unfold obj_loc72 in HK.

    astep. step. if_cases K1; zify_cond K1; [exfalso; rewrite ZBridge.zb_lxor_ones in K1 by lia; clear - K1 D0 DH LK HL HT; lia| clear K1].

    step. step.

    astep. chk0 SZ (D + Lk). step. if_false.
    astep.
    remember (D + Lk) as DL eqn:EDL.
    lstep.

    astep. astep. astep. astep. astep. astep. name_mem m9.
    eapply evt_eq; [| apply evt_done; apply (HK m9); [exact MU| exact WM| assumption| assumption| assumption]]. atp_st_eq.
  Qed.

  Lemma obj_u1B : forall (K : machine_state -> Prop) (q b f D cap sz esc zn : Z) (lg : bool)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    mem_inv bsegs m -> 0x6d9000 <= f -> f + 120 < 2^47 -> lstrA m (f + 32) lg D cap sz -> 0 <= esc < sz -> shz m D zn -> sz < zn ->

    (forall (c : Z) (xa2 : word), c <> 48 -> c <> 49 ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz c) (wz 48) xa2 (wz LIT_TILDE_A) x14 x15 x16 x17
                  (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz esc) (wz (f + 33)) (wz (esc + 1)) (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb8a50) fc None m (seg_rom bsegs))) ->

    (forall (lit : Z), (lit = LIT_TILDE_A \/ lit = LIT_SLASH_A) -> esc + 2 <= sz ->
       K (MS (mkR (wz 0xb8a14) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (f + 32)) (wz esc) (wz 2) (wz lit) x14 x15 x16 x17
                  (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz esc) (wz (f + 33)) (wz (esc + 1)) (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
             F (wz STR_REPLACE_A) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz esc) (wz (f + 33)) x25 (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb89b0) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until m. intros MI FLO FHI LS ESC SZ ZN KBAD KREP.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold STR_REPLACE_A, LIT_SLASH_A, LIT_TILDE_A in *.
    pose proof (munch_refl ([] : list (Z * Z)) m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof LS as (SZ0 & SZC & CAP & D0 & DC & (bs & BS & LBS & NUL) & REP).

    set (cb := nth (Z.to_nat (esc + 1)) bs (Z_to_bv 8 1)). set (c := bv_unsigned cb).
    assert (CR : 0 <= c < 256) by (subst c; pose proof (bv_unsigned_in_range 8 cb) as X; unfold bv_modulus in X; cbn in X; lia).
    assert (CNUL : esc + 1 = sz -> c = 0).
    { intros EQ. subst c cb. replace (Z.to_nat (esc + 1)) with (Z.to_nat sz) by lia. rewrite NUL. reflexivity. }
    assert (RDC : ov_read_bytes bsegs m (wa (D + (esc + 1))) 1 = Some [cb]).
    { apply (u8arr_read bsegs m D bs (esc + 1) cb _ BS); [apply nth_error_nth'; lia| lia| reflexivity]. }
    assert (EZ : zxb cb = Z_to_bv 64 c) by reflexivity.

    assert (J : evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (if lg then 1 else 0)) (wz D) x12 x13 x14 x15 x16 x17
                                  (wz 0x23a00) (wz (shad f)) (wz 0x239e0) (wz 49) (wz (f + 32)) (wz esc) (wz (f + 33)) x25 (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
                              F (wz 0xb89c4) fc None m (seg_rom bsegs))).
    2:{ destruct lg.
        - destruct REP as [HDR EV]. pose proof (rw_cells_C8_read1A _ _ _ _ HDR) as RD0.

          astep. rewrite u8_modA. astep. rewrite long_byte0A by lia. step. step. if_false. step.
          eapply evt_eq; [| exact J]. atp_st_eq.
        - destruct REP as (HDR & ED & ECAP).
          astep. astep. rewrite short_byte0A. step. step. if_true.
          eapply evt_eq; [| exact J]. atp_st_eq. }
    clear REP.

    step. if_dead1 by D0. astep. astep. step. if_dead1 by D0 ESC. step. if_dead1 by D0 ESC DC SZC.
    chk0 SZ (D + (esc + 1)). step. if_false.
    step. rewrite EZ.

    step. if_cases K1; zify_cond K1.
    -
      assert (E49 : c = 49) by (rewrite ?land64_mod in K1; lia).
      destruct (Z.eq_dec (esc + 1) sz) as [EQ|NE]; [exfalso; rewrite (CNUL EQ) in E49; lia|].
      step. astep. step. step. step.
      eapply evt_eq; [| apply evt_done; apply (KREP 0x23a00); [right; reflexivity| lia]]. atp_st_eq.
    -
      step. astep. step. if_cases K0; zify_cond K0.
      + eapply evt_eq; [| apply evt_done; apply (KBAD c x12); rewrite ?land64_mod in K0, K1; lia]. atp_st_eq.
      + assert (E48 : c = 48) by (rewrite ?land64_mod in K0; lia).
        destruct (Z.eq_dec (esc + 1) sz) as [EQ|NE]; [exfalso; rewrite (CNUL EQ) in E48; lia|].
        step. astep. step. step. step.
        eapply evt_eq; [| apply evt_done; apply (KREP 0x239e0); [left; reflexivity| lia]]. atp_st_eq.
  Qed.

  Lemma obj_u2B : forall (K : machine_state -> Prop) (q b f esc : Z)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    0 <= esc -> esc + 1 < 2^62 -> 0x6d9000 <= f -> f + 120 < 2^47 ->
    K (MS (mkR (wz 0xb8a24) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (f + 32)) (wz 126) (wz (esc + 1)) x13 x14 x15 x16 x17
               (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz esc) (wz (f + 33)) (wz (esc + 1)) (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
         F (wz STR_FIND_A) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR (wz 0xb8a14) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (f + 32)) x11 x12 x13 x14 x15 x16 x17
                       (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz esc) (wz (f + 33)) (wz (esc + 1)) (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8a14) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros E0 E62 FLO FHI HK. unfold STR_FIND_A, LIT_SLASH_A, LIT_TILDE_A in *.

    astep. step. step. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_u3B : forall (K : machine_state -> Prop) (q b f esc r : Z)
      (gp x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    (r = 18446744073709551615 \/ 0 <= r < 2^62) -> 0x6d9000 <= f -> f + 120 < 2^47 ->
    (r <> 18446744073709551615 ->
       K (MS (mkR (wz 0xb8a24) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz r) x11 x12 x13 x14 x15 x16 x17
                  (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz r) (wz (f + 33)) (wz (esc + 1)) (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb89b0) fc None m (seg_rom bsegs))) ->
    (r = 18446744073709551615 ->
       K (MS (mkR (wz 0xb8a24) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz r) x11 x12 x13 x14 x15 x16 x17
                  (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz r) (wz (f + 33)) (wz (esc + 1)) (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb8a3c) fc None m (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb8a24) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz r) x11 x12 x13 x14 x15 x16 x17
                       (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) (wz esc) (wz (f + 33)) (wz (esc + 1)) (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8a24) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros HR FLO FHI KLOOP KDONE. unfold LIT_SLASH_A, LIT_TILDE_A in *.

    step. step. if_cases K0; zify_cond K0; rewrite ?land64_mod in K0.
    - eapply evt_eq; [| apply evt_done; apply KLOOP; lia]. atp_st_eq.
    - step. eapply evt_eq; [| apply evt_done; apply KDONE; lia]. atp_st_eq.
  Qed.

  Lemma obj_v1B : forall (K : machine_state -> Prop) (q b out node f D cap sz sl : Z) (lg : bool)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x25 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv bsegs m -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 <= sl < 2^64 -> 0 <= node < 2^64 ->
    0x6d9000 <= f -> f + 120 <= ae_lo E -> lstrA m (f + 32) lg D cap sz ->
    rw_cells bsegs m b (obj_loc72 j0 (Z_to_bv 64 sl) (Z_to_bv 64 node) f out) ->
    K (MS (mkR (wz 0xb8acc) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 72)) (wz node) (wz D) (wz sz) x14 x15 x16 x17
               (wz sl) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) x23 (wz D) x25 (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
         F (wz ATP_ATKEY_A) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       (wz LIT_SLASH_A) (wz (shad f)) (wz LIT_TILDE_A) (wz 49) (wz (f + 32)) x23 (wz (f + 33)) x25 (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8a3c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH SLR NDR FLO FHI LS LOC HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold ATP_ATKEY_A, LIT_SLASH_A, LIT_TILDE_A in *.
    pose proof LS as (SZ0 & SZC & CAP & D0 & DC & (bs & BS & LBS & NUL) & REP). unfold obj_loc72 in LOC. hide BS.

    assert (J : forall xa0 : word, evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) xa0 x11 x12 (wz sz) x14 x15 x16 x17
                                  (wz 0x23a00) (wz (shad f)) (wz 0x239e0) (wz 49) (wz (f + 32)) x23 (wz D) x25 (wz 18446744073709551615) (wz 2147450880) x28 x29 x30 x31)
                              F (wz 0xb8ab8) fc None m (seg_rom bsegs))).
    { intros xa0.
      step. step. astep. step. step.
      eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq. }
    destruct lg.
    - destruct REP as [HDR EV]. pose proof (rw_cells_C8_read1A _ _ _ _ HDR) as RD0.

      astep. rewrite u8_modA. astep. rewrite long_byte0A by lia. step. if_true. step. step.
      eapply evt_eq; [| apply J]. atp_st_eq.
    - destruct REP as (HDR & ED & ECAP).

      astep. astep. rewrite short_byte0A. step. if_false. astep. rewrite ?u8_modA, ?(Z.mod_small (2 * sz) 256), short_sizeA by lia. step.
      eapply evt_eq; [| apply J]. atp_st_eq.
  Qed.

  Lemma obj_w94B : forall (K : machine_state -> Prop) (q b : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
    q + -272 <= b -> b <= q + -256 -> 272 <= q -> q < 2^47 ->
    K (MS (mkR (wz 0xb8adc) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 96)) (wz (b + 72)) (wz 16) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz e_asan_memcpy) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8acc) fc None m (seg_rom bsegs)).
  Proof.
    intros until m. intros B0 B1 QL QH HK. unfold e_asan_memcpy in *.

    astep. astep. astep. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_wa4B : forall (K : machine_state -> Prop) (q b f D cap sz code : Z) (lg : bool) (w0 w1 cw : word)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (jt cb j2 js4 : list byte),
    mem_inv bsegs m -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 <= code < 64 ->
    0x6d9000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E -> lstrA m (f + 32) lg D cap sz ->
    rw_cells bsegs m (b + 72) [C8 w0; C8 w1; C4 (Z_to_bv 64 code); CB 4 jt] -> rw_cells bsegs m (b + 96) [CB 16 cb; C4 cw; CB 4 j2] ->
    rw_cells bsegs m (shad f) (obj_sh 0 0 0 js4) ->

    (forall (m1 : mem), lg = false -> munch [(b + 112, b + 116); (shad f, shad f + 16)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (b + 96) [CB 16 cb; C4 (Z_to_bv 64 code); CB 4 j2] -> rw_cells bsegs m1 (shad f) (obj_sh (-8) (-8) (-8) js4) ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz code) (wz (-8)) x12 x13 x14 x15 x16 x17
                  x18 (wz (shad f)) x20 x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb8b38) fc None m1 (seg_rom bsegs))) ->

    (forall (m1 : mem) (xa1 : word), lg = true -> munch [(b + 112, b + 116); (shad f, shad f + 16)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (b + 96) [CB 16 cb; C4 (Z_to_bv 64 code); CB 4 j2] -> rw_cells bsegs m1 (shad f) (obj_sh 0 0 0 js4) ->
       K (MS (mkR (wz 0xb8b1c) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz D) xa1 x12 x13 x14 x15 x16 x17
                  x18 (wz (shad f)) x20 x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz OPDEL_A) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (wz (shad f)) x20 x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8adc) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until js4. intros MI LO B0 B1 QH CODE FLO FHI FSH S0 SHI LS SRET CHILD SH KS KL.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OPDEL_A in *.
    pose proof (munch_refl [(b + 112, b + 116); (shad f, shad f + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof LS as (SZ0 & SZC & CAP & D0 & DC & (bs & BS & LBS & NUL) & REP). hide BS.
    unfold obj_sh, pz in SH. unfold obj_sh, pz in KS, KL. unfold shad, SHB in *.
    destruct lg; [destruct REP as [HDR EV]| destruct REP as (HDR & ED & ECAP)].
    -
      step. astep. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?a_sx32_small, ?a_u64_small in K0 by lia; clear - K0 CODE; lia| clear K0].
      rewrite ?a_sx32_small by lia.
      step. name_mem m1.
      pose proof (rw_cells_C8_read1A _ _ _ _ ltac:(lazymatch goal with H : rw_cells bsegs m1 (f + 32) _ |- _ => exact H end)) as RD0.

      astep. rewrite u8_modA. astep. rewrite long_byte0A by lia. step. if_true. step. step. astep. step.
      eapply evt_eq; [| apply evt_done; eapply (KL m1 _ eq_refl); [exact MU| exact WM| assumption| | assumption]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells bsegs m1 (b + 96) _ |- _ => exact H end.
    -
      step. astep. step. if_cases K0; zify_cond K0; [exfalso; rewrite ?a_sx32_small, ?a_u64_small in K0 by lia; clear - K0 CODE; lia| clear K0].
      rewrite ?a_sx32_small by lia.
      step. name_mem m1.

      astep. astep. rewrite short_byte0A. step. if_false. astep. nstep. nstep. nstep. step. name_mem m2.
      eapply evt_eq; [| apply evt_done; eapply (KS m2 eq_refl); [exact MU| exact WM| assumption| | assumption]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells bsegs m2 (b + 96) _ |- _ => exact H end.
  Qed.

  Lemma obj_we4B : forall (K : machine_state -> Prop) (q b f code : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (cb j2 js4 : list byte),
    mem_inv bsegs m -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 <= code < 64 ->
    0x6d9000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    rw_cells bsegs m (b + 96) [CB 16 cb; C4 (Z_to_bv 64 code); CB 4 j2] -> rw_cells bsegs m (shad f) (obj_sh 0 0 0 js4) ->
    (forall (m1 : mem), munch [(shad f, shad f + 16)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 -> rw_cells bsegs m1 (shad f) (obj_sh (-8) (-8) (-8) js4) ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz code) (wz (-8)) (wz 64) x13 x14 x15 x16 x17
                  x18 (wz (shad f)) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb8b38) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (wz (shad f)) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8b1c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until js4. intros MI LO B0 B1 QH CODE FLO FHI FSH S0 SHI CHILD SH HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(shad f, shad f + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold obj_sh, pz in SH. unfold obj_sh, pz in HK. unfold shad, SHB in *.

    step. astep. astep. nstep. nstep. nstep. name_mem m1.
    rewrite ?a_sx32_small by lia.
    step. if_cases K0; zify_cond K0; [exfalso; rewrite ?a_sx32_small, ?a_u64_small in K0 by lia; clear - K0 CODE; lia| clear K0].
    eapply evt_eq; [| apply evt_done; apply (HK m1 MU WM ltac:(assumption) ltac:(assumption))]. atp_st_eq.
  Qed.

  Lemma obj_b1B : forall (K : machine_state -> Prop) (q b f out : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word) (w24 w32 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv bsegs m -> ae_lo E + 432 <= q -> q + -272 <= b -> b <= q + -256 -> q <= ae_hi E -> 0 < out -> out + 24 < 2^64 ->
    rw_cells bsegs m b (obj_loc72 j0 w24 w32 f out) ->
    K (MS (mkR (wz 0xb8a68) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz out) (wz 0) (wz 16) x13 x14 x15 x16 x17
               x18 (wz (shad f)) (wz (out + 16)) x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz e_asan_memset) fc None m (seg_rom bsegs)) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (wz (shad f)) x20 x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8a50) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH O0 OH LOC HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_asan_memset in *.
    unfold obj_loc72 in LOC.

    step. step. if_dead1 by O0. astep. astep. astep. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_b2B : forall (K : machine_state -> Prop) (q b f D cap sz out : Z) (lg : bool)
      (gp x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (nbs jB jC : list byte),
    mem_inv bsegs m -> ae_lo E <= out -> out + 24 <= ae_hi E -> out mod 8 = 0 -> shz m out 24 ->
    0x6d9000 <= f -> f + 120 <= ae_lo E -> lstrA m (f + 32) lg D cap sz ->
    rw_cells bsegs m out [CB 16 nbs; CB 4 jB; CB 4 jC] ->
    (forall (m1 : mem), lg = false -> munch [(out, out + 24)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 out [CB 16 nbs; C4 (Z_to_bv 64 22); CB 4 jC] ->
       K (MS (mkR (wz 0xb8a68) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz 0) x11 x12 x13 x14 x15 x16 x17
                  x18 (wz (shad f)) (wz (out + 16)) x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb8a9c) fc None m1 (seg_rom bsegs))) ->
    (forall (m1 : mem) (xa1 : word), lg = true -> munch [(out, out + 24)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 out [CB 16 nbs; C4 (Z_to_bv 64 22); CB 4 jC] ->
       K (MS (mkR (wz 0xb8a9c) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz D) xa1 x12 x13 x14 x15 x16 x17
                  x18 (wz (shad f)) (wz (out + 16)) x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz OPDEL_A) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR (wz 0xb8a68) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (wz (shad f)) (wz (out + 16)) x21 (wz (f + 32)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8a68) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until jC. intros MI OLO OHI O8 SZ FLO FHI LS OUT KS KL.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold OPDEL_A in *.
    pose proof (munch_refl [(out, out + 24)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    pose proof LS as (SZ0 & SZC & CAP & D0 & DC & (bs & BS & LBS & NUL) & REP). hide BS.
    destruct lg.
    - destruct REP as [HDR EV].

      chk0 SZ (out + 16). step. if_false. astep. lstep. name_mem m1.
      pose proof (rw_cells_C8_read1A _ _ _ _ ltac:(lazymatch goal with H : rw_cells bsegs m1 (f + 32) _ |- _ => exact H end)) as RD0.

      astep. rewrite u8_modA. astep. rewrite long_byte0A by lia. step. if_false.
      step. step. astep. step.
      eapply evt_eq; [| apply evt_done; eapply (KL m1 _ eq_refl); [exact MU| exact WM| assumption| ]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => exact H end.
    - destruct REP as (HDR & ED & ECAP).
      chk0 SZ (out + 16). step. if_false. astep. lstep. name_mem m1.
      astep. astep. rewrite short_byte0A. step. if_true.
      eapply evt_eq; [| apply evt_done; eapply (KS m1 eq_refl); [exact MU| exact WM| assumption| ]].
      + atp_st_eq.
      + lazymatch goal with H : rw_cells bsegs m1 out _ |- _ => exact H end.
  Qed.

  Lemma obj_b3B : forall (K : machine_state -> Prop) (q b f : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (js4 : list byte),
    mem_inv bsegs m -> 0x6d9000 <= f -> f + 120 <= ae_lo E -> (f + 120 <= shad f \/ shad f + 15 <= f) -> 0 <= shad f -> shad f + 15 <= ae_lo E ->
    rw_cells bsegs m (shad f) (obj_sh 0 0 0 js4) ->
    (forall (m1 : mem), munch [(shad f, shad f + 16)] m m1 -> wmono bsegs m m1 -> mem_inv bsegs m1 ->
       rw_cells bsegs m1 (shad f) (obj_sh (-8) (-8) (-8) js4) ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (-8)) x11 x12 x13 x14 x15 x16 x17
                  x18 (wz (shad f)) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb8bc0) fc None m1 (seg_rom bsegs))) ->
    evt bsegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 (wz (shad f)) x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb8a9c) fc None m (seg_rom bsegs)).
  Proof using OK.
    intros until js4. intros MI FLO FHI FSH S0 SHI SH HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(shad f, shad f + 16)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
    unfold obj_sh, pz in SH. unfold obj_sh, pz in HK. unfold shad, SHB in *.

    astep. nstep. nstep. nstep. name_mem m1. step.
    eapply evt_eq; [| apply evt_done; apply (HK m1 MU WM ltac:(assumption) ltac:(assumption))]. atp_st_eq.
  Qed.

End ObjU.
