(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import Tac ImageA SysStep.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Spec Require Import StrFun.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.P Require Import Str_tac Startup_glue.
From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import Layout. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import Shadow. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import R_small R_m2s R_thread I_consts I_qck X_atexit. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.A Require Import IcptSpec. From OssFuzzTheorems.Proofs.openssl.bndiv.lib.B Require Import I_pck D_kit I_ikit I_strncmpw I_strncmpw2 I_strncmpw3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Lemma bytes_at_firstn_a : forall m A (bs : list byte) k, bytes_at bsegs m A bs -> bytes_at bsegs m A (firstn k bs).
Proof.
  intros m A bs k H. rewrite <- (firstn_skipn k bs) in H. apply bytes_at_app in H. destruct H as [H _]. exact H.
Qed.

Lemma nth_error_firstn_lt : forall (l : list byte) j i, (i < j)%nat -> nth_error (firstn j l) i = nth_error l i.
Proof.
  induction l as [|x l IH]; intros j i Hij; [rewrite firstn_nil; destruct i; reflexivity|].
  destruct j as [|j]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

(* [comment removed for export] *)
Lemma sc_trunc : forall n b1 b2, 0 < n -> strncmp_ok n b1 b2 ->
  let j := Z.to_nat (strncmp_sz n b1 b2) in
  strncmp_idx n (firstn j b1) (firstn j b2) = strncmp_idx n b1 b2
  /\ strncmp_res n (firstn j b1) (firstn j b2) = strncmp_res n b1 b2
  /\ strncmp_sz n (firstn j b1) (firstn j b2) = strncmp_sz n b1 b2
  /\ strncmp_ok n (firstn j b1) (firstn j b2)
  /\ length (firstn j b1) = j /\ length (firstn j b2) = j.
Proof.
  intros n b1 b2 N0 (L1 & L2) j.
  pose proof (idx_aux_le (Z.to_nat n) b1 b2) as LE.
  assert (HJ : (strncmp_idx_aux b1 b2 (Z.to_nat n) < j \/ Z.to_nat n <= j)%nat).
  { unfold j, strncmp_sz, strncmp_idx. destruct (Nat.eq_dec (strncmp_idx_aux b1 b2 (Z.to_nat n)) (Z.to_nat n)) as [E|NE].
    - right. rewrite E. lia.
    - left. lia. }
  assert (EI : strncmp_idx n (firstn j b1) (firstn j b2) = strncmp_idx n b1 b2).
  { unfold strncmp_idx. rewrite (idx_aux_firstn _ b1 b2 j HJ). reflexivity. }
  assert (ES : strncmp_sz n (firstn j b1) (firstn j b2) = strncmp_sz n b1 b2) by (unfold strncmp_sz; rewrite EI; reflexivity).
  assert (LJ1 : length (firstn j b1) = j) by (rewrite firstn_length; unfold j; lia).
  assert (LJ2 : length (firstn j b2) = j) by (rewrite firstn_length; unfold j; lia).
  split; [exact EI|]. split.
  - unfold strncmp_res. rewrite EI. destruct (strncmp_idx n b1 b2 =? n) eqn:EN; [reflexivity|].
    apply Z.eqb_neq in EN. unfold strncmp_idx in EN |- *.
    rewrite !nth_error_firstn_lt by (rewrite Nat2Z.id; destruct HJ as [HJ|HJ]; [exact HJ| lia]). reflexivity.
  - split; [exact ES|]. split; [unfold strncmp_ok; rewrite ES, LJ1, LJ2; unfold j; split; lia|]. split; [exact LJ1| exact LJ2].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.

Lemma isc_tail : forall (usp p1 p2 n sz idx x1 x2 : Z)
    (ra ra' gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (s0' s4' s6' s7' s10' : word) F fc (m0 m : mem) (lo : Z) (junk : list byte),
  stk bsegs m lo (usp + -2176) -> lo <= usp - ISTRNCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> usp < 2^63 ->
  rw_cells bsegs m (usp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs m (usp + -2176) [CB 2072 junk] ->
  munch [(usp - 2256, usp)] m0 m -> wmono bsegs m0 m ->
  0 <= p1 -> 0 <= p2 -> 0 <= idx <= n -> n < 2^31 -> sz = Z.min (idx + 1) n -> 1 <= sz ->
  p1 + sz <= 2^47 -> p2 + sz <= 2^47 -> 0 <= x1 < 256 -> 0 <= x2 < 256 ->
  chk_ok m p1 sz -> chk_ok m p2 sz -> m2s_cells m -> icells_sc m -> mem_inv bsegs m ->
  evt bsegs (istrncmp_post ra (Z_to_bv 64 usp) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (cmpx x1 x2) lo m0)
    (MS (mkR ra' (Z_to_bv 64 (usp + -2176)) gp tp t0 t1 t2 s0' (Z_to_bv 64 n) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 p2) (Z_to_bv 64 p1) s4' (Z_to_bv 64 sz) s6' s7' (Z_to_bv 64 x1) (Z_to_bv 64 x2) s10' (Z_to_bv 64 idx)
             t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a823c) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until junk. intros ST LO LOLO SPH FRs FR MU WM P1 P2 IDX NH SZD SZ0 R1 R2 X1 X2 CS1 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MUl. pose proof (wmono_refl bsegs m) as WMl.
  pose proof IC as (G70 & G2 & SHC & AI & SSC).
  call (isc_chk1 RIP usp p1 sz); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| exact CS1| exact M2S| exact IC
        | assumption|].
  lazymatch goal with H : stk bsegs _ lo (usp + -2176) |- _ => rename H into ST2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (CS2' : chk_ok mm p2 sz)
      by (apply (chk_ok_agree m mm p2 sz CS2 ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MUl); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S' : m2s_cells mm)
      by (apply (m2s_cells_agree m mm M2S); [apply (agree_of_munch _ _ _ _ MUl); intros y Hy; cbn [outside]; split; [lia| exact I]
                                           | exact WMl]);
    assert (IC' : icells_sc mm) by (split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| exact SSC]]]])
  end.
  clear CS1 CS2 M2S IC.
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  assert (EUi1 : bv_unsigned (Z_to_bv 64 (idx + 1)) = idx + 1) by (apply unsigned_lit; lia).
  assert (EUp2 : bv_unsigned (Z_to_bv 64 p2) = p2) by (apply unsigned_lit; lia).
  assert (EUnp2 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p2)) = 18446744073709551615 - p2) by (apply unsigned_lit; lia).
  lstep. lstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    lstep. lstep. rewrite (lxor_ones64 p2) by lia. lstep. if_true.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 sz) by (f_equal; lia).
    eapply isc_tail2; try eassumption; lia.
  - (* [comment removed for export] *)
    lstep. rewrite (lxor_ones64 p2) by lia. lstep. if_false.
    replace (Z_to_bv 64 (idx + 1)) with (Z_to_bv 64 sz) by (f_equal; lia).
    eapply isc_tail2; try eassumption; lia.
Qed.

Theorem istrncmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (p1 p2 n : Z) (b1 b2 : list byte) (lo : Z),
  a0 = Z_to_bv 64 p1 -> a1 = Z_to_bv 64 p2 -> a2 = Z_to_bv 64 n ->
  stk bsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - ISTRNCMP_DEPTH -> kHighShadowEnd + 8 <= lo -> bv_unsigned sp < 2^63 ->
  0 < n < 2^31 -> bytes_at bsegs m p1 b1 -> bytes_at bsegs m p2 b2 -> strncmp_ok n b1 b2 ->
  p1 + strncmp_sz n b1 b2 <= 2^47 -> p2 + strncmp_sz n b1 b2 <= 2^47 ->
  (p1 + strncmp_sz n b1 b2 <= lo \/ bv_unsigned sp <= p1) -> (p2 + strncmp_sz n b1 b2 <= lo \/ bv_unsigned sp <= p2) ->
  chk_ok m p1 (strncmp_sz n b1 b2) -> chk_ok m p2 (strncmp_sz n b1 b2) -> m2s_cells m -> icells_sc m -> mem_inv bsegs m ->
  evt bsegs (istrncmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (strncmp_res n b1 b2) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a808c) fc None m (seg_rom bsegs)).
Proof using RIP.
  intros until lo. intros -> -> -> ST LO LOLO SPH N0 B1 B2 OK R1 R2 SEP1 SEP2 CS1 CS2 M2S IC MI.
  unfold kHighShadowEnd in *.
  destruct (sc_trunc n b1 b2 ltac:(lia) OK) as (EI & ER & ES & OKc & LC1 & LC2).
  rewrite <- ER.
  set (sz := strncmp_sz n b1 b2) in *.
  set (c1 := firstn (Z.to_nat sz) b1) in *. set (c2 := firstn (Z.to_nat sz) b2) in *.
  assert (BC1 : keep (bytes_at bsegs m p1 c1)) by (apply bytes_at_firstn_a; exact B1).
  assert (BC2 : keep (bytes_at bsegs m p2 c2)) by (apply bytes_at_firstn_a; exact B2).
  pose proof (bytes_at_bound _ _ _ _ B1) as BB1. pose proof (bytes_at_bound _ _ _ _ B2) as BB2.
  clear B1 B2 EI ER OK. clearbody c1 c2.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(usp - 2256, usp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (EU : bv_unsigned (Z_to_bv 64 usp) = usp) by (apply unsigned_lit; lia).
  assert (EU2176 : bv_unsigned (Z_to_bv 64 (usp + -2176)) = usp + -2176) by (apply unsigned_lit; lia).
  call (isc_prologue usp p1 p2 n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST.
  lstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (IC1 : icells_sc mm)
      by (apply (icells_sc_agree m mm IC); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]
                                          | exact WM]) end.
  pose proof IC1 as (G70 & G2 & SHC & AI & SSC). clear IC1.
  call asan_inited_spec; [exact AI| assumption|].
  xsteps_to 0x1c5b34%Z.
  call try_init_spec; [exact AI| rewrite EU2176; exact ST| lia| lia| assumption|].
  lazymatch goal with H : stk bsegs _ lo (bv_unsigned (Z_to_bv 64 _)) |- _ => rewrite EU2176 in H; rename H into ST2 end.
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  xsteps_to 0x1a80f4%Z.
  assert (SZ1 : 1 <= sz <= n).
  { rewrite <- ES. unfold strncmp_sz, strncmp_idx. lia. }
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (BM1 : bytes_at bsegs mm p1 c1)
      by (unfold keep in BC1; apply (bytes_at_agree bsegs m mm _ _ BC1); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; rewrite LC1, Z2Nat.id in Hy by lia; (split; [lia| exact I]));
    assert (BM2 : bytes_at bsegs mm p2 c2)
      by (unfold keep in BC2; apply (bytes_at_agree bsegs m mm _ _ BC2); apply (agree_of_munch _ _ _ _ MU); intros y Hy;
          cbn [outside]; rewrite LC2, Z2Nat.id in Hy by lia; (split; [lia| exact I]));
    assert (CM1 : chk_ok mm p1 sz)
      by (apply (chk_ok_agree m mm p1 sz CS1 ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (CM2 : chk_ok mm p2 sz)
      by (apply (chk_ok_agree m mm p2 sz CS2 ltac:(lia) ltac:(lia));
          apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]);
    assert (M2S' : m2s_cells mm)
      by (apply (m2s_cells_agree m mm M2S); [apply (agree_of_munch _ _ _ _ MU); intros y Hy; cbn [outside]; split; [lia| exact I]
                                           | exact WM]);
    assert (IC' : icells_sc mm) by (split; [exact G70| split; [exact G2| split; [exact SHC| split; [exact AI| exact SSC]]]])
  end.
  clear BC1 BC2 CS1 CS2 M2S IC.
  eapply evt_cut.
  { apply (isc_cmp_loop (Z.to_nat n - 1) 0 n p1 p2 c1 c2); [lia| lia| exact BM1| exact BM2| exact OKc| intros j Hj; lia| assumption]. }
  intros ms' (a0' & y1 & y2 & -> & X1R & X2R & RES).
  rewrite <- RES.
  set (idx := strncmp_idx n c1 c2) in *.
  assert (IDX : 0 <= idx <= n) by (unfold idx, strncmp_idx; pose proof (idx_aux_le (Z.to_nat n) c1 c2); lia).
  assert (SZD : sz = Z.min (idx + 1) n) by (rewrite <- ES; reflexivity).
  assert (EUi : bv_unsigned (Z_to_bv 64 idx) = idx) by (apply unsigned_lit; lia).
  assert (EUi1 : bv_unsigned (Z_to_bv 64 (idx + 1)) = idx + 1) by (apply unsigned_lit; lia).
  assert (EUp1 : bv_unsigned (Z_to_bv 64 p1) = p1) by (apply unsigned_lit; lia).
  assert (EUnp1 : bv_unsigned (Z_to_bv 64 (18446744073709551615 - p1)) = 18446744073709551615 - p1) by (apply unsigned_lit; lia).
  lstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    lstep. lstep. if_false.
    lstep. lstep. rewrite (lxor_ones64 p1) by lia. lstep. lstep. lstep. if_true.
    replace (Z_to_bv 64 n) with (Z_to_bv 64 sz) by (f_equal; lia).
    eapply isc_tail; try eassumption; lia.
  - (* [comment removed for export] *)
    do 6 lstep. if_true. lstep. lstep. if_cases K2; zify_cond K2.
    + (* [comment removed for export] *)
      lstep. lstep. rewrite (lxor_ones64 p1) by lia. lstep. lstep. lstep. if_true.
      replace (Z_to_bv 64 n) with (Z_to_bv 64 sz) by (f_equal; lia).
      eapply isc_tail; try eassumption; lia.
    + (* [comment removed for export] *)
      lstep. rewrite (lxor_ones64 p1) by lia. lstep. lstep. lstep. if_false.
      replace (Z_to_bv 64 (idx + 1)) with (Z_to_bv 64 sz) by (f_equal; lia).
      eapply isc_tail; try eassumption; lia.
Qed.

End WithRIP.
