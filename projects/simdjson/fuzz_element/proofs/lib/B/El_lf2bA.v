(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS SysStep StoreFast FP.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_stage1_kit.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_element.lib.B Require Import Layout RT_iface D_defs D_kit D_clx D_rlkit D_libiface Sj_akit Sj_acps Sj_hkit Atp_fzwA Atp_defsA Atp_h_defsA Pj_lftoi1A
     El_defsA El_lf1A El_lf2A.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition el_fddA (d n : Z) : Z := if 10 <=? n then d + 10 else 0.
Definition el_fdsA (n : Z) : Z := if 10 <=? n then n - 10 else 0.

Definition el_locals2 (j0 j1 j2 : list byte) (idx : word) (j4 : list byte) (act : Z) (j6 j7 j8 : list byte) (f : Z) (j10 : list byte) (sel fdd : Z)
    (j13 j15 jr : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; C8 idx; CB 8 j4; C8 (Z_to_bv 64 act); CB 8 j6; CB 8 j7; CB 24 j8; C8 (Z_to_bv 64 f); CB 4 j10; C4 (Z_to_bv 64 sel);
   C8 (Z_to_bv 64 fdd); CB 8 j13; C1 (Z_to_bv 8 0); CB 7 j15; CB 24 jr].

Definition el_W2 (sp' : Z) : list ivl := [(sp' + 24, sp' + 32); (sp' + 40, sp' + 48); (sp' + 100, sp' + 120)].

Lemma land31_range : forall x, 0 <= x -> 0 <= Z.land x 31 < 32.
Proof. intros x Hx. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. split; [apply Z.mod_pos_bound| apply Z.mod_pos_bound]; lia. Qed.

Definition el_localsH (j0 j1 j2 : list byte) (c24 : cell) (j4 : list byte) (c40 : cell) (j6 j7 j8 : list byte) (f : Z) (j10 : list byte) (c100 c104 c112 : cell)
    (j15 jr : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; c24; CB 8 j4; c40; CB 8 j6; CB 8 j7; CB 24 j8; C8 (Z_to_bv 64 f); CB 4 j10; c100; c104; c112; C1 (Z_to_bv 8 0); CB 7 j15; CB 24 jr].

Section Hdr.
Variables (usp sp' f d n : Z) (bs : list byte) (gp tp t0 t2 a5 a6 a7 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word).
Variables (j0 j1 j2 j4 j6 j7 j8 j10 j15 jr : list byte) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
Hypothesis N : n = Z.of_nat (length bs).
Hypothesis D0 : 0 <= d.
Hypothesis DH : d + n < 2^63.
Hypothesis F0 : 0 < f.
Hypothesis FD : 0 <= f / 8.
Hypothesis GLO : SEGTOP_A <= sp'.
Hypothesis LUSP : sp' + 152 <= usp - 104.
Hypothesis SPH : usp < 2^63.
Hypothesis APART : d + n <= sp' \/ usp <= d.

Definition el_hdr_post : machine_state -> Prop := fun ms =>
  exists (m1 : mem) (idx : word) (act sel s5v : Z) (t0' a1' a2' a3' a4' a5' a6' a7' : word) (j13 : list byte),
      ms = MS (mkR (Z_to_bv 64 0xb1d2c) (Z_to_bv 64 sp') gp tp t0' (Z_to_bv 64 f) t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 (el_fdsA n)) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 n) (Z_to_bv 64 s5v) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0xb1ffc) fc None m1 (seg_rom bsegs)
      /\ munch (el_W2 sp') m0 m1 /\ wmono bsegs m0 m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' (el_locals2 j0 j1 j2 idx j4 act j6 j7 j8 f j10 sel (el_fddA d n) j13 j15 jr)
      /\ 0 <= act < 32 /\ 0 <= sel < 8.

Definition hdr_st (pc : Z) (a0 a1 a2 a3 a4 : word) (s5v : Z) (m : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0xb1d2c) (Z_to_bv 64 sp') gp tp t0 (Z_to_bv 64 f) t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') a0 a1 a2 a3 a4 a5 a6 a7
          (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 n) (Z_to_bv 64 s5v) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
     F (Z_to_bv 64 pc) fc None m (seg_rom bsegs).

Local Ltac prep :=
  unfold el_hdr_post, hdr_st, lf0_st, el_W2, el_localsH, el_locals2, el_fddA, el_fdsA, shad, SHB, SEGTOP_A, EL_TRAP_A in *;
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia);
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia);
  assert (ED : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).

Lemma firstn1_skipn_nth : forall (l : list byte) (k : nat), (k < length l)%nat -> firstn 1 (skipn k l) = [nth k l z8].
Proof.
  induction l as [|x l IH]; intros k Hk; cbn [length] in Hk; [lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. lia.
Qed.
Lemma pl_read : forall (m : mem) (k : nat), bytes_at bsegs m d bs -> (k < length bs)%nat ->
  ov_read_bytes bsegs m (wa (d + Z.of_nat k)) 1 = Some [nth k bs z8].
Proof.
  intros m k BS Hk. pose proof (bytes_at_read bsegs m d bs (Z.of_nat k) 1 BS ltac:(lia) ltac:(rewrite Nat2Z.id; lia)) as R.
  rewrite Nat2Z.id in R. rewrite R. f_equal. apply firstn1_skipn_nth. exact Hk.
Qed.

Lemma el_hdr54 : forall (a1 a2 a3 a4 : word) (j3 : list byte) (act sel : Z) (w112 : word) (m : mem),
  10 <= n -> bytes_at bsegs m d bs -> 0 <= act < 32 -> 0 <= sel < 8 ->
  munch (el_W2 sp') m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  rw_cells bsegs m sp' (el_localsH j0 j1 j2 (CB 8 j3) j4 (C8 (Z_to_bv 64 act)) j6 j7 j8 f j10 (C4 (Z_to_bv 64 sel)) (C8 (Z_to_bv 64 (d + 2))) (C8 w112) j15 jr) ->
  evt bsegs el_hdr_post (hdr_st 0xb1f7c (Z_to_bv 64 (d + 2)) a1 a2 a3 a4 (d + 1) m).
Proof.
  intros until m. intros N10 BS ACT SEL MU WM MI FRl. prep.
  pose proof (pl_read m 2 BS ltac:(lia)) as R2. pose proof (pl_read m 3 BS ltac:(lia)) as R3. pose proof (pl_read m 4 BS ltac:(lia)) as R4.
  pose proof (pl_read m 5 BS ltac:(lia)) as R5. pose proof (pl_read m 6 BS ltac:(lia)) as R6. pose proof (pl_read m 7 BS ltac:(lia)) as R7.
  pose proof (pl_read m 8 BS ltac:(lia)) as R8. pose proof (pl_read m 9 BS ltac:(lia)) as R9.
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in R2, R3, R4, R5, R6, R7, R8, R9.
  assert (ED2 : bv_unsigned (Z_to_bv 64 (d + 2)) = d + 2) by (apply unsigned_lit; lia).

  do 9 zstep. ls. do 14 zstep. ls. zstep. zstep.
  replace (10 <=? n) with true by (symmetry; apply Z.leb_le; lia).
  replace (d + 2 + 8) with (d + 10) in * by lia.
  lazymatch goal with H : rw_cells _ _ sp' _ |- _ => apply (rw_cells_forget_C8 bsegs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _] _ _) in H; cbn [app] in H end.
  apply evt_done.
  lazymatch goal with H : rw_cells _ ?mx _ (_ :: _ :: _ :: C8 ?iw :: _) |- _ => exists mx, iw, act, sel, (d + 1) end.
  do 9 eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|]. split; [eassumption|]. split; [eassumption|].
  split; [eassumption|]. lia.
Qed.

Lemma acc_agreeE : forall (m m' : mem) a k, acc bsegs m a k -> agree_on (fun x => shad a <= x <= shad (a + k)) m m' -> acc bsegs m' a k.
Proof.
  intros m m' a k H AG i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [| exact Hok].
  apply (bytes_at_agree bsegs m m' _ _ Hb). intros x Hx. cbn [length] in Hx. apply AG. unfold shad in *. Z.div_mod_to_equations. lia.
Qed.

Hypothesis ACC0 : bs = [] \/ acc bsegs m0 d n.
Hypothesis SHD : shad (d + n) < sp'.

Lemma accH : forall m, munch (el_W2 sp') m0 m -> bs <> [] -> acc bsegs m d n.
Proof.
  intros m MU NE. destruct ACC0 as [E|ACC]; [exfalso; exact (NE E)|].
  apply (acc_agreeE m0 m d n ACC). apply (agree_of_munch _ _ _ _ MU). intros x Hx. cbv beta in Hx.
  unfold el_W2. unfold shad in *. cbn [outside]. lia.
Qed.

Lemma el_hdr40 : forall (a1 a2 a3 a4 : word) (j3 : list byte) (act sel : Z) (w112 : word) (m : mem),
  10 <= n -> bytes_at bsegs m d bs -> 0 <= act < 32 -> 0 <= sel < 8 ->
  munch (el_W2 sp') m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  rw_cells bsegs m sp' (el_localsH j0 j1 j2 (CB 8 j3) j4 (C8 (Z_to_bv 64 act)) j6 j7 j8 f j10 (C4 (Z_to_bv 64 sel)) (C8 (Z_to_bv 64 (d + 2))) (C8 w112) j15 jr) ->
  evt bsegs el_hdr_post (hdr_st 0xb1f68 (Z_to_bv 64 (d + 2)) a1 a2 a3 a4 (d + 1) m).
Proof.
  intros until m. intros N10 BS ACT SEL MU WM MI FRl.
  pose proof (accH m MU ltac:(intros E; subst bs; cbn [length] in N; lia)) as ACC. prep.
  assert (ED2 : bv_unsigned (Z_to_bv 64 (d + 2)) = d + 2) by (apply unsigned_lit; lia).
  destruct (acc_read1 m d n (d + 9) ACC ltac:(lia)) as (b & RD & OK).
  replace (d + 9) with (d + 2 + 7) in RD by lia.
  destruct (sh_ok_cases b (d + 9) OK) as [-> | (k & -> & K1 & K2)].
  - astep. astep. astep. step. shz_norm. step. if_false.
    eapply el_hdr54; eassumption.
  - astep. astep. astep. step. rewrite (sxb_small7 k) by lia. step. if_lia. astep. step. if_lia.
    eapply el_hdr54; eassumption.
Qed.

Lemma el_hdr24 : forall (a0 a1 a2 a3 a4 : word) (j3 : list byte) (act sel : Z) (w112 : word) (m : mem),
  10 <= n -> bytes_at bsegs m d bs -> 0 <= act < 32 -> 0 <= sel < 8 ->
  munch (el_W2 sp') m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  rw_cells bsegs m sp' (el_localsH j0 j1 j2 (CB 8 j3) j4 (C8 (Z_to_bv 64 act)) j6 j7 j8 f j10 (C4 (Z_to_bv 64 sel)) (C8 (Z_to_bv 64 (d + 2))) (C8 w112) j15 jr) ->
  evt bsegs el_hdr_post (hdr_st 0xb1f4c a0 a1 a2 a3 a4 (d + 1) m).
Proof.
  intros until m. intros N10 BS ACT SEL MU WM MI FRl.
  pose proof (accH m MU ltac:(intros E; subst bs; cbn [length] in N; lia)) as ACC. prep.
  assert (ED2 : bv_unsigned (Z_to_bv 64 (d + 2)) = d + 2) by (apply unsigned_lit; lia).

  zstep. zstep. step. if_lia.
  destruct (acc_read1 m d n (d + 2) ACC ltac:(lia)) as (b & RD & OK).
  destruct (sh_ok_cases b (d + 2) OK) as [-> | (k & -> & K1 & K2)].
  - astep. astep. step. shz_norm. step. if_false.
    eapply el_hdr40; eassumption.
  - astep. astep. step. rewrite (sxb_small7 k) by lia. step. if_lia. astep. step. if_lia.
    eapply el_hdr40; eassumption.
Qed.

Lemma el_hdr00 : forall (a1 a2 a3 a4 : word) (j3 j11 : list byte) (act : Z) (w104 w112 : word) (m : mem),
  2 <= n -> bytes_at bsegs m d bs -> 0 <= act < 32 ->
  munch (el_W2 sp') m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  rw_cells bsegs m sp' (el_localsH j0 j1 j2 (CB 8 j3) j4 (C8 (Z_to_bv 64 act)) j6 j7 j8 f j10 (CB 4 j11) (C8 w104) (C8 w112) j15 jr) ->
  evt bsegs el_hdr_post (hdr_st 0xb1f28 (Z_to_bv 64 (d + 1)) a1 a2 a3 a4 (d + 1) m).
Proof.
  intros until m. intros N2 BS ACT MU WM MI FRl. prep.
  pose proof (pl_read m 1 BS ltac:(lia)) as R1. change (Z.of_nat 1) with 1 in R1.
  assert (B1 : 0 <= bv_unsigned (nth 1%nat bs z8) < 256).
  { pose proof (bv_unsigned_in_range 8 (nth 1%nat bs z8)) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 8) with 256 in X. lia. }
  assert (ED1 : bv_unsigned (Z_to_bv 64 (d + 1)) = d + 1) by (apply unsigned_lit; lia).

  astep. zstep. zstep. astep. ls. zstep. ls. ls. step. if_cases K; zify_cond K.
  -
    zstep. ls. ls.
    replace (10 <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    lazymatch goal with H : rw_cells _ _ sp' _ |- _ => apply (rw_cells_forget_C8 bsegs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _] _ _) in H; cbn [app] in H end.
    apply evt_done.
    lazymatch goal with H : rw_cells _ ?mx _ (_ :: _ :: _ :: C8 ?iw :: _) |- _ => exists mx, iw, act, (bv_unsigned (nth 1%nat bs z8) mod 8), (d + 1) end.
    do 9 eexists. split; [atp_st_eq_goal|].
    split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. Z.div_mod_to_equations; lia.
  -
    replace (d + 1 + 1) with (d + 2) in * by lia.
    eapply el_hdr24; try eassumption; [lia| Z.div_mod_to_equations; lia].
Qed.

Lemma el_hdrc4 : forall (a0 a1 a2 a3 a4 : word) (j3 j5 j11 j12 j13 : list byte) (m : mem),
  1 <= n -> bytes_at bsegs m d bs ->
  munch (el_W2 sp') m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  rw_cells bsegs m sp' (el_localsH j0 j1 j2 (CB 8 j3) j4 (CB 8 j5) j6 j7 j8 f j10 (CB 4 j11) (CB 8 j12) (CB 8 j13) j15 jr) ->
  evt bsegs el_hdr_post (hdr_st 0xb1eec a0 a1 a2 a3 a4 d m).
Proof.
  intros until m. intros N1 BS MU WM MI FRl.
  pose proof (accH m MU ltac:(intros E; subst bs; cbn [length] in N; lia)) as ACC. prep.
  pose proof (pl_read m 0 BS ltac:(lia)) as R0. change (Z.of_nat 0) with 0 in R0. rewrite Z.add_0_r in R0.
  assert (B0 : 0 <= bv_unsigned (nth 0%nat bs z8) < 256).
  { pose proof (bv_unsigned_in_range 8 (nth 0%nat bs z8)) as X. unfold bv_modulus in X. change (2 ^ Z.of_N 8) with 256 in X. lia. }
  pose proof (land31_range (bv_unsigned (nth 0%nat bs z8)) ltac:(lia)) as A31.
  assert (ED1 : bv_unsigned (Z_to_bv 64 (d + 1)) = d + 1) by (apply unsigned_lit; lia).

  astep. zstep. zstep. astep. ls. ls. ls. step. if_cases K; zify_cond K.
  -
    ls. zstep. ls. ls.
    replace (10 <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    lazymatch goal with H : rw_cells _ _ sp' _ |- _ => apply (rw_cells_forget_C8 bsegs _ _ [_; _; _; _; _; _; _; _; _; _; _; _; _] _ _) in H; cbn [app] in H end.
    apply evt_done.
    lazymatch goal with H : rw_cells _ ?mx _ (_ :: _ :: _ :: C8 ?iw :: _) |- _ =>
      exists mx, iw, (Z.land (bv_unsigned (nth 0%nat bs z8)) 31), 0, (d + 1) end.
    do 9 eexists. split; [atp_st_eq_goal|].
    split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. lia.
  -
    zstep. zstep. step. if_lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (ACC1 : acc bsegs mx d n) by (eapply accH; [eassumption| intros E; subst bs; cbn [length] in N; lia]) end.
    destruct (acc_read1 _ d n (d + 1) ACC1 ltac:(lia)) as (b & RD & OK).
    destruct (sh_ok_cases b (d + 1) OK) as [-> | (k & -> & K1 & K2)].
    + astep. astep. step. shz_norm. step. if_false.
      eapply el_hdr00; try eassumption; lia.
    + astep. astep. step. rewrite (sxb_small7 k) by lia. step. if_lia. astep. step. if_lia.
      eapply el_hdr00; try eassumption; lia.
Qed.

Lemma el_hdr : forall (j3 j5 j11 j12 j13 : list byte) (m : mem),
  bytes_at bsegs m d bs ->
  munch (el_W2 sp') m0 m -> wmono bsegs m0 m -> mem_inv bsegs m ->
  rw_cells bsegs m sp' (el_localsH j0 j1 j2 (CB 8 j3) j4 (CB 8 j5) j6 j7 j8 f j10 (CB 4 j11) (CB 8 j12) (CB 8 j13) j15 jr) ->
  evt bsegs el_hdr_post (hdr_st 0xb1ed0 (Z_to_bv 64 (-8)) (Z_to_bv 64 (-14)) (Z_to_bv 64 (-13)) (Z_to_bv 64 0x12737) (Z_to_bv 64 0xb1cb8) d m).
Proof.
  intros until m. intros BS MU WM MI FRl. prep.

  step. if_cases K0; zify_cond K0.
  -
    ls. ls. zstep. ls. ls.
    replace (10 <=? n) with false by (symmetry; apply Z.leb_gt; lia).
    apply evt_done.
    lazymatch goal with H : rw_cells _ ?mx _ (_ :: _ :: _ :: C8 ?iw :: _) |- _ => exists mx, iw, 0, 0, d end.
    do 9 eexists. split; [atp_st_eq_goal|].
    split; [eapply munch_weaken; [| eassumption]; intros x Hx; cbn [outside] in *; lia|]. split; [eassumption|]. split; [eassumption|].
    split; [eassumption|]. lia.
  -
    zstep. step. if_lia.
    pose proof (accH m MU ltac:(intros E; subst bs; cbn [length] in N; lia)) as ACC.
    destruct (acc_read1 m d n d ACC ltac:(lia)) as (b & RD & OK).
    destruct (sh_ok_cases b d OK) as [-> | (k & -> & K1 & K2)].
    + astep. astep. step. shz_norm. step. if_false.
      eapply el_hdrc4; try eassumption; lia.
    + astep. astep. step. rewrite (sxb_small7 k) by lia. step. if_lia. astep. step. if_lia.
      eapply el_hdrc4; try eassumption; lia.
Qed.
End Hdr.

Definition el_locals3 (j0 j1 j2 : list byte) (idx : word) (act : Z) (j8 : list byte) (f : Z) (j10 : list byte) (sel fdd fds : Z) (j15 jr : list byte) : list cell :=
  [CB 8 j0; CB 8 j1; CB 8 j2; C8 idx; C8 (Z_to_bv 64 (f + 240)); C8 (Z_to_bv 64 act); C8 (Z_to_bv 64 f); C8 (Z_to_bv 64 (f + 208)); CB 24 j8; C8 (Z_to_bv 64 f);
   CB 4 j10; C4 (Z_to_bv 64 sel); C8 (Z_to_bv 64 fdd); C8 (Z_to_bv 64 fds); C1 (Z_to_bv 8 0); CB 7 j15; CB 24 jr].

Definition el_W3 (sp' f : Z) : list ivl := [(sp' + 32, sp' + 40); (sp' + 48, sp' + 64); (sp' + 112, sp' + 120); (shad f + 4, shad f + 7)].

Lemma el_walkV0 : forall (usp sp' f fdd fds n s5v : Z) (gp tp t0 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (j0 j1 j2 : list byte) (idx : word) (j4 : list byte) (act : Z) (j6 j7 j8 j10 : list byte) (sel : Z) (j13 j15 jr t : list byte) F fc (m : mem),
  0 < f -> f + 1024 < 2^63 -> 0 <= shad f -> shad f + 128 <= sp' -> SEGTOP_A <= sp' -> sp' + 152 < 2^63 -> 0 <= fdd < 2^64 -> 0 <= fds < 2^64 ->
  rw_cells bsegs m sp' (el_locals2 j0 j1 j2 idx j4 act j6 j7 j8 f j10 sel fdd j13 j15 jr) ->
  rw_cells bsegs m (shad f) (el_shadowA (-8) (-8) (-8) (-8) t) ->
  mem_inv bsegs m ->
  evt bsegs (fun ms => exists (m1 : mem),
      ms = MS (mkR (Z_to_bv 64 EL_SPLITRET_A) (Z_to_bv 64 sp') gp tp t0 (Z_to_bv 64 f) t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp')
                   (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (sp' + 104)) a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 (f + 32)) (Z_to_bv 64 (f + 96)) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 ATPA_SPLITINTO) fc None m1 (seg_rom bsegs)
      /\ munch (el_W3 sp' f) m m1 /\ wmono bsegs m m1 /\ mem_inv bsegs m1
      /\ rw_cells bsegs m1 sp' (el_locals3 j0 j1 j2 idx act j8 f j10 sel fdd fds j15 jr)
      /\ rw_cells bsegs m1 (shad f) (el_shadowA 0 (-8) (-8) (-8) t))
    (MS (mkR (Z_to_bv 64 0xb1d2c) (Z_to_bv 64 sp') gp tp t0 (Z_to_bv 64 f) t2 (Z_to_bv 64 usp) (Z_to_bv 64 sp') (Z_to_bv 64 fds) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 f) (Z_to_bv 64 (shad f)) (Z_to_bv 64 n) (Z_to_bv 64 s5v) s6 s7 s8 (Z_to_bv 64 SHB) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0xb1ffc) fc None m (seg_rom bsegs)).
Proof.
  intros until m. intros F0 FH SH0 SHH GLO SPH DD DS FRl FS MI.
  unfold el_W3, el_locals2, el_locals3, el_shadowA, el_shbytesA, EL_SPLITRET_A, ATPA_SPLITINTO, shad, SHB, SEGTOP_A in *. cbn [map app repeat] in *.
  pose proof (munch_refl [(sp' + 32, sp' + 40); (sp' + 48, sp' + 64); (sp' + 112, sp' + 120); (f / 8 + 2147450880 + 4, f / 8 + 2147450880 + 7)] m) as MU.
  pose proof (wmono_refl bsegs m) as WM.
  assert (ES : bv_unsigned (Z_to_bv 64 sp') = sp') by (apply unsigned_lit; lia).
  assert (EF : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
  assert (ESH : bv_unsigned (Z_to_bv 64 (f / 8 + 2147450880)) = f / 8 + 2147450880) by (apply unsigned_lit; lia).

  ls. zstep. zstep. zstep. ls. zstep. ls. ls. ls. ls. ls. zstep. zstep. zstep.
  apply evt_done. eexists. split; [atp_st_eq_goal|].
  split; [eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in *; lia|]. split; [exact WM|]. split; [eassumption|].
  split; [eassumption|]. eassumption.
Qed.
