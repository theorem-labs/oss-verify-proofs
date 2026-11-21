(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: relocated for the zlib 1.4 build, ported to the model, comments removed. *)
(* the plain 1.4 U8U2Lib moved to the UBSan image by tools/gen_u9u2lib14.py:
   U7 names, zfree in a3 at inflateEnd (x13 = 0x17dc8), image top 0x75000. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PlainU9 Require PImgRun.
(* the plain 1.4 S9U2Lib moved to the UBSan image by tools/gen_u9u2lib14.py:
   U9 names, zfree in a3 at inflateEnd (x13 = 0x17d0c), image top 0x75000. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit Require PropExec StoreOk Frame ZlibStmtBase U9LibStmt.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge Walk Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.PlainU9 Require Import PImg RMallocRep RMalloc_iface.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Common Require Import RunDraw.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.Mr Require Import MrRulesU9.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.MrP9 Require Import U9HBase U9HConv U9U2Seg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Module OZ := OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.ubsan_halts_any_exit.ZlibStmtBase.


Lemma sregs_entry_eq : forall (R : bvmap 5 word) (x21 x22 x23 x24 x25 x26 x27 : word),
  OZ.sregs R OL.S_ENTRY5 = [bv_unsigned x21; bv_unsigned x22; bv_unsigned x23; bv_unsigned x24; bv_unsigned x25; bv_unsigned x26; bv_unsigned x27] ->
  reg_get R (Z_to_bv 5 21) = x21 /\ reg_get R (Z_to_bv 5 22) = x22 /\ reg_get R (Z_to_bv 5 23) = x23 /\ reg_get R (Z_to_bv 5 24) = x24 /\
  reg_get R (Z_to_bv 5 25) = x25 /\ reg_get R (Z_to_bv 5 26) = x26 /\ reg_get R (Z_to_bv 5 27) = x27.
Proof.
  intros R x21 x22 x23 x24 x25 x26 x27 H. unfold OZ.sregs, OL.S_ENTRY5, OZ.S_ENTRY in H. cbn [map app] in H.
  injection H as H21 H22 H23 H24 H25 H26 H27. repeat split; apply bv_eq; assumption.
Qed.

Lemma sregs_entry_of : forall (R : bvmap 5 word) (x21 x22 x23 x24 x25 x26 x27 : word), reg_get R (Z_to_bv 5 21) = x21 ->
  reg_get R (Z_to_bv 5 22) = x22 -> reg_get R (Z_to_bv 5 23) = x23 -> reg_get R (Z_to_bv 5 24) = x24 ->
  reg_get R (Z_to_bv 5 25) = x25 -> reg_get R (Z_to_bv 5 26) = x26 -> reg_get R (Z_to_bv 5 27) = x27 ->
  OZ.sregs R OL.S_ENTRY5 = [bv_unsigned x21; bv_unsigned x22; bv_unsigned x23; bv_unsigned x24; bv_unsigned x25; bv_unsigned x26; bv_unsigned x27].
Proof. intros R x21 x22 x23 x24 x25 x26 x27 <- <- <- <- <- <- <-. reflexivity. Qed.

Lemma rz_end_regs {RCa1 : RunCtx}  : forall (R R' : bvmap 5 word) pc M mo T (u blk : Z) (sE : list Z) (x3 x4 x21 x22 x23 x24 x25 x26 x27 : word),
  OL.end_regs_U9 R R' u blk sE ->
  reg_get R (Z_to_bv 5 3) = x3 -> reg_get R (Z_to_bv 5 4) = x4 ->
  sE = [bv_unsigned x21; bv_unsigned x22; bv_unsigned x23; bv_unsigned x24; bv_unsigned x25; bv_unsigned x26; bv_unsigned x27] ->
  (forall y1 y5 y6 y7 y9 y12 y14 y15 y16 y17 y18 y19 y20 y28 y29 y30 y31 : word,
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 (u - 16)) x3 x4 y5 y6 y7 (Z_to_bv 64 u) y9 (Z_to_bv 64 0) (Z_to_bv 64 blk) y12
                                    (Z_to_bv 64 0x17d6c) y14 y15 y16 y17 y18 y19 y20 x21 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty pc fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' pc M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R R' pc M mo T u blk sE x3 x4 x21 x22 x23 x24 x25 x26 x27 (G13 & G11 & G10 & G8 & G2 & G3 & G4 & GS) E3 E4 -> HK.
  apply sregs_entry_eq in GS. destruct GS as (S21 & S22 & S23 & S24 & S25 & S26 & S27).
  change (reg_get R' (Z_to_bv 5 3) = reg_get R (Z_to_bv 5 3)) in G3. change (reg_get R' (Z_to_bv 5 4) = reg_get R (Z_to_bv 5 4)) in G4.
  rewrite E3 in G3. rewrite E4 in G4.
  apply rz_mkR. unfold mkR_of.
  rewrite (G13 : reg_get R' (Z_to_bv 5 13) = _), (G11 : reg_get R' (Z_to_bv 5 11) = _), (G10 : reg_get R' (Z_to_bv 5 10) = _),
          (G8 : reg_get R' (Z_to_bv 5 8) = _), (G2 : reg_get R' (Z_to_bv 5 2) = _), G3, G4, S21, S22, S23, S24, S25, S26, S27.
  apply HK.
Qed.

Lemma rz_zw_regs {RCa1 : RunCtx}  : forall (R' : bvmap 5 word) pc M mo T (v2 v3 v4 v10 v11 v12 v13 : word),
  reg_get R' (Z_to_bv 5 2) = v2 -> reg_get R' (Z_to_bv 5 3) = v3 -> reg_get R' (Z_to_bv 5 4) = v4 ->
  reg_get R' (Z_to_bv 5 10) = v10 -> reg_get R' (Z_to_bv 5 11) = v11 -> reg_get R' (Z_to_bv 5 12) = v12 ->
  reg_get R' (Z_to_bv 5 13) = v13 ->
  (let g := fun k : Z => reg_get R' (Z_to_bv 5 k) in
   realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR (g 1) v2 v3 v4 (g 5) (g 6) (g 7) (g 8) (g 9) v10 v11 v12 v13 (g 14) (g 15) (g 16) (g 17)
                                  (g 18) (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) (g 29) (g 30) (g 31))
                             bvmap_empty pc fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' pc M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R' pc M mo T v2 v3 v4 v10 v11 v12 v13 <- <- <- <- <- <- <- HK. apply rz_mkR. exact HK.
Qed.

Lemma sregs_all_kept : forall (R R' : bvmap 5 word),
  (forall k, In k kept_regs -> reg_get R' (Z_to_bv 5 k) = reg_get R (Z_to_bv 5 k)) ->
  OZ.sregs R' OZ.S_ALL = OZ.sregs R OZ.S_ALL.
Proof.
  intros R R' K. unfold OZ.sregs, OZ.S_ALL. cbn [map].
  change (OP.getr R' 8) with (reg_get R' (Z_to_bv 5 8)). change (OP.getr R 8) with (reg_get R (Z_to_bv 5 8)).
  change (OP.getr R' 9) with (reg_get R' (Z_to_bv 5 9)). change (OP.getr R 9) with (reg_get R (Z_to_bv 5 9)).
  change (OP.getr R' 18) with (reg_get R' (Z_to_bv 5 18)). change (OP.getr R 18) with (reg_get R (Z_to_bv 5 18)).
  change (OP.getr R' 19) with (reg_get R' (Z_to_bv 5 19)). change (OP.getr R 19) with (reg_get R (Z_to_bv 5 19)).
  change (OP.getr R' 20) with (reg_get R' (Z_to_bv 5 20)). change (OP.getr R 20) with (reg_get R (Z_to_bv 5 20)).
  change (OP.getr R' 21) with (reg_get R' (Z_to_bv 5 21)). change (OP.getr R 21) with (reg_get R (Z_to_bv 5 21)).
  change (OP.getr R' 22) with (reg_get R' (Z_to_bv 5 22)). change (OP.getr R 22) with (reg_get R (Z_to_bv 5 22)).
  change (OP.getr R' 23) with (reg_get R' (Z_to_bv 5 23)). change (OP.getr R 23) with (reg_get R (Z_to_bv 5 23)).
  change (OP.getr R' 24) with (reg_get R' (Z_to_bv 5 24)). change (OP.getr R 24) with (reg_get R (Z_to_bv 5 24)).
  change (OP.getr R' 25) with (reg_get R' (Z_to_bv 5 25)). change (OP.getr R 25) with (reg_get R (Z_to_bv 5 25)).
  change (OP.getr R' 26) with (reg_get R' (Z_to_bv 5 26)). change (OP.getr R 26) with (reg_get R (Z_to_bv 5 26)).
  change (OP.getr R' 27) with (reg_get R' (Z_to_bv 5 27)). change (OP.getr R 27) with (reg_get R (Z_to_bv 5 27)).
  rewrite (K 8), (K 9), (K 18), (K 19), (K 20), (K 21), (K 22), (K 23), (K 24), (K 25), (K 26), (K 27) by (cbn; tauto).
  reflexivity.
Qed.

Lemma rz_zc_regs {RCa1 : RunCtx}  : forall (R R' : bvmap 5 word) pc M mo T (sp' : Z) (v0 v1 v2 v3 v4 v5 x3 x4 x22 x23 x24 x25 x26 x27 : word),
  reg_get R' (Z_to_bv 5 2) = Z_to_bv 64 sp' ->
  reg_get R' (Z_to_bv 5 8) = v0 -> reg_get R' (Z_to_bv 5 9) = v1 -> reg_get R' (Z_to_bv 5 18) = v2 ->
  reg_get R' (Z_to_bv 5 19) = v3 -> reg_get R' (Z_to_bv 5 20) = v4 -> reg_get R' (Z_to_bv 5 21) = v5 ->
  (forall r : reg, In r ([3; 4]%bv ++ OZ.S_ENTRY) -> OP.getr R' r = OP.getr R r) ->
  reg_get R (Z_to_bv 5 3) = x3 -> reg_get R (Z_to_bv 5 4) = x4 ->
  reg_get R (Z_to_bv 5 22) = x22 -> reg_get R (Z_to_bv 5 23) = x23 -> reg_get R (Z_to_bv 5 24) = x24 ->
  reg_get R (Z_to_bv 5 25) = x25 -> reg_get R (Z_to_bv 5 26) = x26 -> reg_get R (Z_to_bv 5 27) = x27 ->
  (forall y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word,
     realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (MS (mkR y1 (Z_to_bv 64 sp') x3 x4 y5 y6 y7 v0 v1 y10 y11 y12 y13 y14 y15 y16 y17
                                    v2 v3 v4 v5 x22 x23 x24 x25 x26 x27 y28 y29 y30 y31)
                               bvmap_empty pc fc0 None M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T) ->
  realizes (run_segments psegs rc_inp rc_sp rc_mb) (mkCfg (OP.mkst (fx := OP.fx0) R' pc M (seg_rom (run_segments psegs rc_inp rc_sp rc_mb))) mo) T.
Proof.
  intros R R' pc M mo T sp' v0 v1 v2 v3 v4 v5 x3 x4 x22 x23 x24 x25 x26 x27 G2 G8 G9 G18 G19 G20 G21 K E3 E4 E22 E23 E24 E25 E26 E27 HK.
  assert (K3 : reg_get R' (Z_to_bv 5 3) = reg_get R (Z_to_bv 5 3))
    by (refine (K (Z_to_bv 5 3) _); unfold OZ.S_ENTRY; cbn [In app]; repeat (first [left; apply bv_eq; reflexivity | right])).
  assert (K4 : reg_get R' (Z_to_bv 5 4) = reg_get R (Z_to_bv 5 4))
    by (refine (K (Z_to_bv 5 4) _); unfold OZ.S_ENTRY; cbn [In app]; repeat (first [left; apply bv_eq; reflexivity | right])).
  assert (K22 : reg_get R' (Z_to_bv 5 22) = reg_get R (Z_to_bv 5 22))
    by (refine (K (Z_to_bv 5 22) _); unfold OZ.S_ENTRY; cbn [In app]; repeat (first [left; apply bv_eq; reflexivity | right])).
  assert (K23 : reg_get R' (Z_to_bv 5 23) = reg_get R (Z_to_bv 5 23))
    by (refine (K (Z_to_bv 5 23) _); unfold OZ.S_ENTRY; cbn [In app]; repeat (first [left; apply bv_eq; reflexivity | right])).
  assert (K24 : reg_get R' (Z_to_bv 5 24) = reg_get R (Z_to_bv 5 24))
    by (refine (K (Z_to_bv 5 24) _); unfold OZ.S_ENTRY; cbn [In app]; repeat (first [left; apply bv_eq; reflexivity | right])).
  assert (K25 : reg_get R' (Z_to_bv 5 25) = reg_get R (Z_to_bv 5 25))
    by (refine (K (Z_to_bv 5 25) _); unfold OZ.S_ENTRY; cbn [In app]; repeat (first [left; apply bv_eq; reflexivity | right])).
  assert (K26 : reg_get R' (Z_to_bv 5 26) = reg_get R (Z_to_bv 5 26))
    by (refine (K (Z_to_bv 5 26) _); unfold OZ.S_ENTRY; cbn [In app]; repeat (first [left; apply bv_eq; reflexivity | right])).
  assert (K27 : reg_get R' (Z_to_bv 5 27) = reg_get R (Z_to_bv 5 27))
    by (refine (K (Z_to_bv 5 27) _); unfold OZ.S_ENTRY; cbn [In app]; repeat (first [left; apply bv_eq; reflexivity | right])).
  clear K.
  rewrite E3 in K3. rewrite E4 in K4. rewrite E22 in K22. rewrite E23 in K23. rewrite E24 in K24.
  rewrite E25 in K25. rewrite E26 in K26. rewrite E27 in K27.
  apply rz_mkR. unfold mkR_of.
  rewrite G2, G8, G9, G18, G19, G20, G21, K3, K4, K22, K23, K24, K25, K26, K27.
  apply HK.
Qed.

Section FACTS.
Context {RCa1 : RunCtx}.
Context {rc : runConstT}.
Variable sp0 : Z.
Hypothesis SP0 : 0x7fff80000000 <= sp0 <= 0x800000000000.

Abbreviation UU := (sp0 - 416).   (* UU = u, the caller's sp at the inflate call; the z_stream is at UU (uncompress2_z's sp + 0) *)

Lemma u2_frames_same_on : forall (P : Z -> Prop) (M M' : word -> option byte) q payl v2 v3 v4 v5,
  u2_frames sp0 M q payl v2 v3 v4 v5 -> same_on P M M' ->
  (forall x, UU + 112 <= x < UU + 160 \/ UU + 176 <= x < UU + 192 \/ UU + 200 <= x < UU + 208 -> P x) ->
  u2_frames sp0 M' q payl v2 v3 v4 v5.
Proof.
  intros P M M' q payl v2 v3 v4 v5 [F1 F1w F2 F3 F4 F5 F6 F7 F8] SO HP.
  constructor;
    (rewrite (rdn_same_on P M M' _ _ SO); [assumption | intros x Hx; apply HP; cbn in Hx; lia | lia | cbn; lia]).
Qed.

Lemma u2_za_cells_same_on : forall (P : Z -> Prop) (M M' : word -> option byte) q,
  u2_za_cells sp0 M q -> same_on P M M' ->
  (forall x, UU - 32 <= x < UU + 88 -> P x) ->
  u2_za_cells sp0 M' q.
Proof.
  intros P M M' q [F1 F2 F3 F4 F5 F6 F7 F8 F9] SO HP.
  constructor;
    (rewrite (rdn_same_on P M M' _ _ SO); [assumption | intros x Hx; apply HP; cbn in Hx; lia | lia | cbn; lia]).
Qed.

Lemma end_cells_same_on : forall (P : Z -> Prop) (M M' : word -> option byte) p,
  OL.end_cells_U9 M UU p -> same_on P M M' ->
  (forall x, UU - 8 <= x < UU \/ UU + 56 <= x < UU + 88 -> P x) ->
  OL.end_cells_U9 M' UU p.
Proof.
  intros P M M' p (F1 & F2 & F3 & F4) SO HP. unfold OL.end_cells_U9.
  repeat split;
    (rewrite (rdn_same_on P M M' _ _ SO); [assumption | intros x Hx; apply HP; cbn in Hx; lia | lia | cbn; lia]).
Qed.

Lemma zw_inv_same_on : forall (zw : OZ.ZWINV) (P : Z -> Prop) (M M' : word -> option byte) u p q n zc sE sW,
  OL.zw_local_stmt_U9 zw -> zw u p q n zc sE sW M -> same_on P M M' ->
  (forall x, 0 <= x < 2^64 ->
     (u - OL.U9_ZWD <= x < u + 208) \/ (p <= x < p + OL.U9_INFL_N) \/ (OL.U9_BUF <= x < OL.U9_BUF + OL.U9_BUF_N) \/ (q <= x < q + n) ->
     P x) ->
  zw u p q n zc sE sW M'.
Proof.
  intros zw P M M' u p q n zc sE sW ZL ZW SO HP. eapply ZL; [|exact ZW].
  intros a IN. unfold OL.in_fpw_U9 in IN. cbv zeta in IN.
  pose proof (bv_unsigned_in_range 64 a) as RA. unfold bv_modulus in RA. change (2 ^ Z.of_N 64) with (2 ^ 64) in RA.
  assert (X : 0 <= bv_unsigned a < 2 ^ 64) by lia.
  destruct (SO (bv_unsigned a) X (HP _ X IN)) as [E _].
  unfold wa in E. rewrite Z_to_bv_bv_unsigned in E. exact E.
Qed.

Lemma agree_same_on : forall (P : Z -> Prop) (D : Z -> Prop) (M M' : word -> option byte),
  same_on P M M' -> (forall i, D i -> 0 <= i < 2^64 /\ P i) ->
  forall i, D i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof. intros P D M M' SO HD i Hi. destruct (HD i Hi) as [R Pi]. exact (proj1 (SO i R Pi)). Qed.

Hypothesis SP16 : sp0 mod 16 = 0.
Hypothesis ATOPE : ATOP = sp0 - 8388608.

Lemma lib_layout_intro : forall (M : word -> option byte) (p q n lo : Z),
  rblock_range p OL.U9_INFL_N ->
  0 <= n < 2 ^ 26 -> 1 <= q -> q + n <= ATOP ->
  (n = 0 \/ q + n <= 0x10000 \/ 0x95000 <= q) ->
  (q + n <= OL.U9_BUF \/ OL.U9_BUF + OL.U9_BUF_N <= q) ->
  (q + n <= p \/ p + OL.U9_INFL_N <= q) ->
  (forall i, 0 <= i < n -> exists b, OP.rdn (run_segments psegs rc_inp rc_sp rc_mb) M (Z_to_bv 64 (q + i)) 1 = Some [b]) ->
  mem_inv (run_segments psegs rc_inp rc_sp rc_mb) M ->
  stk (run_segments psegs rc_inp rc_sp rc_mb) M lo (sp0 - 208) -> lo <= UU - OL.U9_FRA ->
  wr_at (run_segments psegs rc_inp rc_sp rc_mb) M p OL.U9_INFL_N ->
  OL.lib_layout_U9 ATOP M UU p q n.
Proof.
  intros M p q n lo (P1 & P2 & P3 & P4 & P5) N Q1 Q2 QI QB QP RD MI ST LO WR.
  unfold OL.lib_layout_U9, OL.U9_FRA, OL.U9_IMG_TOP, OL.U9_INFL_N, OL.U9_BUF, OL.U9_BUF_N, OL.U9_RO_LO, OL.U9_RO_HI in *.
  assert (M16 : (sp0 - 416) mod 16 = 0).
  { replace (sp0 - 416) with (sp0 + (-26) * 16) by lia. rewrite Z_mod_plus_full. exact SP16. }
  repeat split; try lia; try assumption.
  - intros i Hi. destruct (M (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
    pose proof (MI _ _ E) as X.
    rewrite PImgRun.run_p_ro_addr_in, p_ro_addr, unsigned_lit in X by (rewrite ?unsigned_lit by lia; lia).
    exfalso. apply andb_false_iff in X. destruct X as [X|X]; [apply Z.leb_gt in X | apply Z.ltb_ge in X]; lia.
  - apply (store_ok_of_stk M lo (sp0 - 208)); [exact ST | lia | lia].
  - pose proof (wr_at_store_ok (run_segments psegs rc_inp rc_sp rc_mb) M p 7176 0 (Z.to_nat 7176) WR ltac:(lia) ltac:(lia)) as X.
    rewrite Z.add_0_r in X. exact X.
Qed.

End FACTS.
