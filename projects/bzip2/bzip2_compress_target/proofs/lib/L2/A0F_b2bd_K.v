(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout RT_iface D_defs D_kit I_read RT_liveprim L_libA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_hkit L_harn_defs RT_globals.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import R_unwind_chain.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt L2StmtS L2StmtD A0_sessK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import A0_b2bc_K.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzInv BzContracts CmpMem CmpCut CmpCarve CmpFsKit0 AsanKit AsanCut A0_cmp_cbV A0_b2c_hcV A0_b2c_wrV A0F_b2d_wrV A0F_b2d_wrW.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require GlueCarve BzDOut BzDState BzWalkArith3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzDOut.

(* [comment removed for export] *)
Definition dec_okL (z : list byte) (sm : bool) (cap : Z) (out : list byte) : Prop :=
  exists (junkD : BzDState.dst),
    let '(r, n, o, _) := buffToBuffDecompress junkD (map bv_unsigned z) cap (if sm then 1 else 0) in
    r = BZ_OK /\ out = map (Z_to_bv 8) o.

(* [comment removed for export] *)
Lemma strm_carveD : forall segs (m : mem) S (jb : list byte), rw_cells segs m S [CB 80 jb] ->
  rw_cells segs m S (STRMD (jw8 jb 0) (jw4 jb 8) (jw4 jb 12) (jw4 jb 16) (jseg jb 20 4) (jw8 jb 24) (jw4 jb 32) (jw4 jb 36) (jw4 jb 40) (jseg jb 44 4) (jw8 jb 48)
                           (jw8 jb 56) (jw8 jb 64) (jw8 jb 72)) /\ length (jseg jb 20 4) = 4%nat /\ length (jseg jb 44 4) = 4%nat.
Proof.
  intros segs m S jb H.
  assert (LJ : Z.of_nat (length jb) = 80) by (destruct H as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [HL _]; rewrite HL; reflexivity).
  assert (L1 : length (jseg jb 20 4) = 4%nat) by (rewrite jseg_length_nat by lia; reflexivity).
  assert (L2 : length (jseg jb 44 4) = 4%nat) by (rewrite jseg_length_nat by lia; reflexivity).
  split; [| split; [exact L1| exact L2]].
  change (STRMD _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (jcells jb 0 [8; 4; 4; 4]%nat ++ [CB 4 (jseg jb 20 4)] ++ jcells jb 24 [8; 4; 4; 4]%nat ++ [CB 4 (jseg jb 44 4)] ++ jcells jb 48 [8; 8; 8; 8]%nat).
  eapply (carve_cb segs); [exact H| | |].
  - rewrite !cells_wf_app. repeat match goal with |- _ /\ _ => split end;
      first [ apply jcells_wf; cbn [sum_nat Nat.add]; lia | cbn [cells_wf cell_wf]; split; [assumption| exact I] ].
  - rewrite !cells_bytes_app. cbn [cells_bytes cbytes]. rewrite !app_nil_r.
    rewrite !jcells_bytes by (cbn [sum_nat Nat.add]; lia). cbn [sum_nat Nat.add]. change (Z.of_nat 20) with 20. change (Z.of_nat 32) with 32.
    etransitivity; [| exact (jseg_all jb 80 LJ)].
    rewrite (jseg_cat jb 44 4 48 32 36) by lia. rewrite (jseg_cat jb 24 20 44 36 56) by lia. rewrite (jseg_cat jb 20 4 24 56 60) by lia.
    rewrite (jseg_cat jb 0 20 20 60 80) by lia. reflexivity.
  - rewrite !cells_size_app, !jcells_size. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma dblocks_virtual : forall small n tt l16 l4 S T48 T56, dblocks_ok small n tt l16 l4 ->
  exists p1 n1 p2 n2, In (p1, n1) (dblocks n tt l16 l4 ++ [(S, 64144)]) /\ In (p2, n2) (dblocks n tt l16 l4 ++ [(S, 64144)]) /\
    forall x, ~ KFrame.outside ([(S, S + 64144); (T48, T56)] ++ map (fun e => (fst e, fst e + snd e)) (dblocks n tt l16 l4)) x ->
              ~ KFrame.outside [(S, S + 64144); (T48, T56); (p1, p1 + n1); (p2, p2 + n2)] x.
Proof.
  intros small n tt l16 l4 S T48 T56 [(-> & -> & -> & ->)|(N & [(_ & T & -> & ->)|(_ & -> & L16 & L4)])]; unfold dblocks.
  - exists S, 64144, S, 64144. cbn [Z.eqb app map fst snd In]. split; [left; reflexivity|]. split; [left; reflexivity|].
    intros x H. cbn [KFrame.outside] in *. lia.
  - destruct (Z.eqb_spec tt 0) as [E|_]; [exfalso; exact (T E)|]. exists tt, (400000 * n), tt, (400000 * n). cbn [Z.eqb app map fst snd In].
    split; [left; reflexivity|]. split; [left; reflexivity|]. intros x H. cbn [KFrame.outside] in *. lia.
  - destruct (Z.eqb_spec l16 0) as [E|_]; [exfalso; exact (L16 E)|]. destruct (Z.eqb_spec l4 0) as [E|_]; [exfalso; exact (L4 E)|].
    exists l4, (50000 * n), l16, (200000 * n). cbn [Z.eqb app map fst snd In].
    split; [left; reflexivity|]. split; [right; left; reflexivity|]. intros x H. cbn [KFrame.outside] in *. lia.
Qed.

Section GlkD.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
(* [comment removed for export] *)
Lemma live_removeD : forall Σ (m : mem) small n tt l16 l4 S L,
  ART RT Σ m -> rt_live RT Σ = dblocks n tt l16 l4 ++ (S, 64144) :: L -> dblocks_ok small n tt l16 l4 -> (forall p k, In (p, k) L -> 0 < k) ->
  live_remove S (rm0 l4 (rm0 l16 (rm0 tt (dblocks n tt l16 l4 ++ (S, 64144) :: L)))) = L.
Proof.
  intros Σ m small n tt l16 l4 S L ART0 LV OK POS.
  assert (NL : forall q, (forall p k, In (p, k) L -> 0 < k -> p <> q) -> forall e, In e L -> fst e <> q).
  { intros q H [p k] He. cbn [fst]. exact (H p k He (POS p k He)). }
  destruct OK as [(-> & -> & -> & ->)|(N & [(_ & T & -> & ->)|(_ & -> & L16 & L4)])]; unfold dblocks, rm0 in *.
  - cbn [Z.eqb app] in *. rewrite live_remove_head'. apply live_remove_notin'. apply NL. intros p k H K EQ. subst p.
    pose proof (af_live_disj RT AF Σ m S 64144 S k [] _ ART0 LV H) as D. lia.
  - destruct (Z.eqb_spec tt 0) as [E|_]; [exfalso; exact (T E)|]. cbn [Z.eqb app] in *.
    assert (DS : S <> tt). { intros EQ. subst S. pose proof (af_live_disj RT AF Σ m tt (400000 * n) tt 64144 [] _ ART0 LV ltac:(left; reflexivity)) as D. lia. }
    rewrite (live_remove_head' tt). rewrite (live_remove_keep' tt (S, 64144)) by (cbn [fst]; exact DS).
    rewrite (live_remove_notin' tt L) by (apply NL; intros p k H K EQ; subst p; pose proof (af_live_disj RT AF Σ m tt (400000 * n) tt k [] _ ART0 LV ltac:(right; exact H)) as D; lia).
    rewrite live_remove_head'. apply live_remove_notin'. apply NL. intros p k H K EQ. subst p.
    pose proof (af_live_disj RT AF Σ m S 64144 S k [(tt, 400000 * n)] _ ART0 LV ltac:(right; exact H)) as D. lia.
  - destruct (Z.eqb_spec l16 0) as [E|_]; [exfalso; exact (L16 E)|]. destruct (Z.eqb_spec l4 0) as [E|_]; [exfalso; exact (L4 E)|]. cbn [Z.eqb app] in *.
    assert (D416 : l4 <> l16). { intros EQ. subst l4. pose proof (af_live_disj RT AF Σ m l16 (50000 * n) l16 (200000 * n) [] _ ART0 LV ltac:(left; reflexivity)) as D. lia. }
    assert (DS16 : S <> l16). { intros EQ. subst S. pose proof (af_live_disj RT AF Σ m l16 (200000 * n) l16 64144 [(l4, 50000 * n)] _ ART0 LV ltac:(right; left; reflexivity)) as D. lia. }
    assert (DS4 : S <> l4). { intros EQ. subst S. pose proof (af_live_disj RT AF Σ m l4 (50000 * n) l4 64144 [] _ ART0 LV ltac:(right; left; reflexivity)) as D. lia. }
    rewrite (live_remove_keep' l16 (l4, 50000 * n)) by (cbn [fst]; exact D416). rewrite (live_remove_head' l16).
    rewrite (live_remove_keep' l16 (S, 64144)) by (cbn [fst]; exact DS16).
    rewrite (live_remove_notin' l16 L) by (apply NL; intros p k H K EQ; subst p; pose proof (af_live_disj RT AF Σ m l16 (200000 * n) l16 k [(l4, 50000 * n)] _ ART0 LV ltac:(right; right; exact H)) as D; lia).
    rewrite (live_remove_head' l4). rewrite (live_remove_keep' l4 (S, 64144)) by (cbn [fst]; exact DS4).
    rewrite (live_remove_notin' l4 L) by (apply NL; intros p k H K EQ; subst p; pose proof (af_live_disj RT AF Σ m l4 (50000 * n) l4 k [] _ ART0 LV ltac:(right; right; exact H)) as D; lia).
    rewrite live_remove_head'. apply live_remove_notin'. apply NL. intros p k H K EQ. subst p.
    pose proof (af_live_disj RT AF Σ m S 64144 S k [(l4, 50000 * n); (l16, 200000 * n)] _ ART0 LV ltac:(right; right; exact H)) as D. lia.
Qed.

(* [comment removed for export] *)
Lemma dblocks_pos : forall Σ (m : mem) small n tt l16 l4 L,
  ART RT Σ m -> rt_live RT Σ = dblocks n tt l16 l4 ++ L -> dblocks_ok small n tt l16 l4 ->
  0 <= n <= 9 /\ (tt <> 0 \/ l16 <> 0 \/ l4 <> 0 -> 1 <= n) /\ 0 <= tt /\ 0 <= l16 /\ 0 <= l4.
Proof.
  intros Σ m small n tt l16 l4 L ART0 LV [(-> & -> & -> & ->)|(N & [(_ & T & -> & ->)|(_ & -> & L16 & L4)])]; unfold dblocks in LV.
  - split; [lia|]. split; [intros [H|[H|H]]; exfalso; apply H; reflexivity|]. lia.
  - destruct (Z.eqb_spec tt 0) as [E|_]; [exfalso; exact (T E)|]. cbn [Z.eqb app] in LV.
    pose proof (af_live_range RT AF Σ m tt (400000 * n) ART0 ltac:(rewrite LV; left; reflexivity)) as (R0 & _).
    split; [lia|]. split; [intros _; lia|]. lia.
  - destruct (Z.eqb_spec l16 0) as [E|_]; [exfalso; exact (L16 E)|]. destruct (Z.eqb_spec l4 0) as [E|_]; [exfalso; exact (L4 E)|]. cbn [Z.eqb app] in LV.
    pose proof (af_live_range RT AF Σ m l4 (50000 * n) ART0 ltac:(rewrite LV; left; reflexivity)) as (R0 & _).
    pose proof (af_live_range RT AF Σ m l16 (200000 * n) ART0 ltac:(rewrite LV; right; left; reflexivity)) as (R1 & _).
    split; [lia|]. split; [intros _; lia|]. lia.
Qed.

(* [comment removed for export] *)
Lemma newblk_facts : forall Σ (m : mem) l1 live0 p n f k,
  ART RT Σ m -> rt_live RT Σ = l1 ++ live0 -> In (p, n) l1 -> In (f, k) (rt_frames RT Σ) ->
  (f + fs_size k <= p \/ p + n <= f) /\ (p + n <= shad f \/ shad (f + fs_size k) <= p) /\ 0 < p /\ p + n <= rt_sp0 RT Σ - STACK_WIN /\
  (forall q j, In (q, j) live0 -> p + n <= q \/ q + j <= p).
Proof.
  intros Σ m l1 live0 p n f k ART0 LV IN1 INF.
  assert (INL : In (p, n) (rt_live RT Σ)) by (rewrite LV; apply in_or_app; left; exact IN1).
  pose proof (af_live_range RT AF Σ m p n ART0 INL) as (R0 & R1 & _).
  pose proof (af_frames_range RT AF Σ m f k ART0 INF) as (_ & _ & _ & FL).
  pose proof (af_fshadow_apart RT AF Σ m f k ART0 INF) as (SL & _).
  split; [exact (FL p n INL)|]. split; [exact (SL p n INL)|]. split; [exact R0|]. split; [exact R1|].
  intros q j INQ. destruct (in_split _ _ IN1) as (la & lb & E1). rewrite E1, <- app_assoc in LV. cbn [app] in LV.
  exact (af_live_disj RT AF Σ m p n q j la (lb ++ live0) ART0 LV ltac:(apply in_or_app; right; apply in_or_app; right; exact INQ)).
Qed.
End GlkD.

(* [comment removed for export] *)
Definition b2d_rc (ret avo : Z) : Z := if ret =? 4 then 0 else if ret =? 0 then (if avo =? 0 then -8 else -7) else ret.

(* [comment removed for export] *)
Lemma A0_b2d_D6 : forall (Q : machine_state -> Prop) (gp tp : word) (F : bvmap 5 word) (fc : bv 32) (SHD : Z) (m : mem) (ret avo : Z)
    (ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
  evt a0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (b2d_s3 SHD ret avo)) (Z_to_bv 64 (b2d_rc ret avo)) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x882d8) fc None m (seg_rom a0segs)) ->
  evt a0segs Q (MS (mkR ra spw gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (b2d_s3 SHD ret avo)) (Z_to_bv 64 ret) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (ret_pc (Z_to_bv 64 (b2d_ra ret))) fc None m (seg_rom a0segs)).
Proof.
  intros Q gp tp F fc SHD m ret avo ra spw t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.
  unfold b2d_s3, b2d_rc, b2d_ra.
  destruct (Z.eqb_spec ret 0) as [->|N0].
  - cbn [Z.eqb]. rewrite (ret_pc_even 0x884b8 ltac:(lia) eq_refl). intros K. apply (A0_b2d_D6b Q gp tp F fc m (avo =? 0)). exact K.
  - destruct (Z.eqb_spec ret 4) as [->|N4].
    + rewrite (ret_pc_even 0x884a0 ltac:(lia) eq_refl). intros K. apply (A0_b2d_D6a Q gp tp F fc m). exact K.
    + rewrite (ret_pc_even 0x884c8 ltac:(lia) eq_refl). intros K. apply (A0_b2d_D6c Q gp tp F fc m). exact K.
Qed.
