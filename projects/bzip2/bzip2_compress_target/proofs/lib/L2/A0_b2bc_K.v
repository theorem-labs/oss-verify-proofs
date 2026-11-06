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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require L_hkit L_harn_defs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.L2 Require Import L2Kit L2Act L2Stmt L2StmtS A0_sessK A0_initK.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSess2 CmpSessB CmpFsKit0 AsanKit AsanCut A0_cmp_cbV A0_b2c_hcV A0_b2c_wrV A0_b2c_wrE A0_b2c_wrI A0_b2c_wrW CmpLaws CmpLawsB BzRT1 BzRT.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCarve BzCLemmasFs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
#[local] Notation mem := (word -> option byte).


Module HD := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_harn_defs.
Module HK := OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.

(* [comment removed for export] *)
Definition wfP (w : Z) : Z := if w =? 0 then 30 else w.
(* [comment removed for export] *)
Definition enc_okL (bs : list byte) (k w : Z) (str : list byte) : Prop :=
  exists (BZP : BzParams) (a1 a2 ft inU uns mtf sel selM len code rfreq lenp : zarr) (bsB bsL nIn oP nM : Z),
    @p_bs BZP = k /\ @p_wf BZP = wfP w /\ zbok a1 /\ zbok a2 /\ bh_w32 ft
    /\ str = map (Z_to_bv 8) (@enc_stream BZP (est_init a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM) (map bv_unsigned bs)).

Lemma bs_of_rng : forall len, 1 <= HK.bs_of len <= 9.
Proof. intros len. unfold HK.bs_of. pose proof (Z.mod_pos_bound len 11 ltac:(lia)). lia. Qed.
Lemma wfP_rng : forall len, 1 <= wfP (HK.wf_of len) <= 250.
Proof. intros len. unfold wfP, HK.wf_of. pose proof (Z.mod_pos_bound len 251 ltac:(lia)). destruct (Z.eqb_spec (len mod 251) 0); lia. Qed.
Definition b2bP (len : Z) : BzParams := mkBzParams (HK.bs_of len) (wfP (HK.wf_of len)) (bs_of_rng len) (wfP_rng len).

(* [comment removed for export] *)
Definition b2bc_cps_pos (RT : rt_sig) (LIB : mem -> Prop) (enc_ok : list byte -> Z -> Z -> list byte -> Prop) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (zb dl d : Z) (bs junk : list byte) (lo : Z),
  let len := Z.of_nat (length bs) in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 zb -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 len -> a4 = Z_to_bv 64 (HK.bs_of len) -> a5 = Z_to_bv 64 0 ->
  a6 = Z_to_bv 64 (HK.wf_of len) -> tp = Z_to_bv 64 0x5fc0d8 -> ra = Z_to_bv 64 HD.RA_B2BC ->
  len < 2^26 -> 0 < d < 2^64 -> KMem.bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + len <= p + n /\ (p, n) <> (zb, HK.nZ_of len)) \/ bs = []) ->
  In (zb, HK.nZ_of len) (rt_live RT Σ) -> KStep.rw_cells asegs m zb [KCells.CB (Z.to_nat (HK.nZ_of len)) junk] ->
  (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= dl /\ dl + 4 <= f + fs_size k - 8) ->
  KStep.rw_cells asegs m dl [KCells.C4 (Z_to_bv 64 (HK.nZ_of len))] -> dl mod 8 = 0 -> KStep.ro_cells asegs m (shad dl) [KCells.C1 (Z_to_bv 8 4)] ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->
  Z.of_nat (length (rt_live RT Σ)) + HD.B2B_LIVE <= LIVE_MAX -> (length (rt_frames RT Σ) + HD.B2B_FRAMES <= FRAMES_MAX)%nat -> HD.B2BC_COST <= rt_credit RT Σ ->
  HD.harn_record m sp s0 ->
  LIB m -> ART RT Σ m -> KMem.mem_inv asegs m ->
  KFrame.stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + HD.B2B_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc HK.e_b2bc m)))
    (fun c => exists (Σ' : rts RT) (rc dlv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rc) m' ms
          /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(zb, zb + HK.nZ_of len); (dl, dl + 4)] m m'
          /\ KStep.rw_cells asegs m' dl [KCells.C4 (Z_to_bv 64 dlv)] /\ LIB m'
          /\ ((rc = 0 /\ exists str, enc_ok bs (HK.bs_of len) (HK.wf_of len) str /\ dlv = Z.of_nat (length str) /\ dlv <= HK.nZ_of len
               /\ KMem.bytes_at asegs m' zb str)
              \/ (-9 <= rc < 0))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - HD.B2BC_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Lemma hc_credit_bound : forall {BZP : BzParams} (z : zstrm), 0 <= z_avail_in z < 2^26 -> HC_CREDIT z <= 317856.
Proof.
  intros BZP z Hz. unfold HC_CREDIT, hc_fuel. bz_params. unfold BZ_MAX_UNUSED.
  assert (Q : 0 <= z_avail_in z / NBLOCKMAX <= 672).
  { split; [apply Z.div_pos; lia|]. apply Z.div_le_upper_bound; [lia|]. nia. }
  rewrite Z2Nat.id by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma n2k_C8C8 : forall (m : mem) a (w1 w2 : word), rw_cells a0segs m a [C8 w1; C8 w2] -> KStep.rw_cells asegs m a [KCells.C8 w1; KCells.C8 w2].
Proof. intros m a w1 w2 H. destruct (n_rw_cells_bytes a0segs m a _ H) as [B W]. split; [split|]; [cbn; tauto| exact B| exact W]. Qed.
Lemma n2k_C4 : forall (m : mem) a (w1 : word), rw_cells a0segs m a [C4 w1] -> KStep.rw_cells asegs m a [KCells.C4 w1].
Proof. intros m a w1 H. destruct (n_rw_cells_bytes a0segs m a _ H) as [B W]. split; [split|]; [cbn; tauto| exact B| exact W]. Qed.
Lemma k2n_C4 : forall (m : mem) a (w1 : word), KStep.rw_cells asegs m a [KCells.C4 w1] -> rw_cells a0segs m a [C4 w1].
Proof. intros m a w1 [[WF B] W]. split; [split|]; [cbn; tauto| exact B| exact W]. Qed.

(* [comment removed for export] *)
Lemma acc_dl : forall (m : mem) dl, dl mod 8 = 0 -> 0 <= dl -> KMem.bytes_at asegs m (shad dl) [Z_to_bv 8 4] -> acc asegs m dl 4.
Proof. intros m dl D8 D0 H. apply (acc_ushadow asegs m dl 4 D8 D0 ltac:(lia)). exact H. Qed.

(* [comment removed for export] *)
Lemma strm_carve : forall segs (m : mem) S (jb : list byte), rw_cells segs m S [CB 80 jb] ->
  rw_cells segs m S (STRMC (jw8 jb 0) (jw4 jb 8) (jw4 jb 12) (jw4 jb 16) (jw4 jb 20) (jw8 jb 24) (jw4 jb 32) (jw4 jb 36) (jw4 jb 40) (jw4 jb 44) (jw8 jb 48)
                           (jw8 jb 56) (jw8 jb 64) (jw8 jb 72)).
Proof.
  intros segs m S jb H.
  assert (LJ : Z.of_nat (length jb) = 80) by (destruct H as [[Hwf _] _]; cbn in Hwf; destruct Hwf as [HL _]; rewrite HL; reflexivity).
  change (STRMC _ _ _ _ _ _ _ _ _ _ _ _ _ _) with (jcells jb 0 SSHAPE).
  eapply (carve_cb segs); [exact H| | |].
  - apply jcells_wf; cbn [sum_nat SSHAPE Nat.add]; lia.
  - rewrite jcells_bytes by (cbn [sum_nat SSHAPE Nat.add]; lia). cbn [sum_nat SSHAPE Nat.add]. exact (jseg_all jb 80 LJ).
  - rewrite jcells_size. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma live_remove_notin' : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|]. unfold live_remove in *. cbn.
  assert (E : (fst e =? p) = false) by (apply Z.eqb_neq; apply H; left; reflexivity).
  rewrite E. cbn. destruct (stdpp.base.decide True) as [_|N]; [| exfalso; apply N; exact I].
  f_equal. apply IH. intros e' He'. apply H. right. exact He'.
Qed.
Lemma live_remove_head' : forall p n (l : list (Z * Z)), live_remove p ((p, n) :: l) = live_remove p l.
Proof. intros p n l. unfold live_remove. cbn. rewrite Z.eqb_refl. cbn. destruct (stdpp.base.decide False) as [N|_]; [destruct N| reflexivity]. Qed.
Lemma live_remove_keep' : forall p e (l : list (Z * Z)), fst e <> p -> live_remove p (e :: l) = e :: live_remove p l.
Proof.
  intros p e l H. unfold live_remove. cbn. rewrite (proj2 (Z.eqb_neq _ _) H). cbn.
  destruct (stdpp.base.decide True) as [_|N]; [reflexivity| exfalso; apply N; exact I].
Qed.

Section Glk.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
(* [comment removed for export] *)
Lemma live_remove4 : forall Σ (m : mem) E nE A1 n1 A2 n2 FT nF l,
  ART RT Σ m -> rt_live RT Σ = (FT, nF) :: (A2, n2) :: (A1, n1) :: (E, nE) :: l ->
  0 < nE -> 0 < n1 -> 0 < n2 -> 0 < nF -> (forall p n, In (p, n) l -> 0 < n) ->
  live_remove E (live_remove FT (live_remove A2 (live_remove A1 ((FT, nF) :: (A2, n2) :: (A1, n1) :: (E, nE) :: l)))) = l.
Proof.
  intros Σ m E nE A1 n1 A2 n2 FT nF l ART0 LV PE P1 P2 PF POS.
  assert (DF : forall p n, In (p, n) ((A2, n2) :: (A1, n1) :: (E, nE) :: l) -> 0 < n -> p <> FT).
  { intros p n H N EQ. subst p. pose proof (af_live_disj RT AF Σ m FT nF FT n [] _ ART0 LV H) as D. lia. }
  assert (D2 : forall p n, In (p, n) ((A1, n1) :: (E, nE) :: l) -> 0 < n -> p <> A2).
  { intros p n H N EQ. subst p. pose proof (af_live_disj RT AF Σ m A2 n2 A2 n [(FT, nF)] _ ART0 LV ltac:(right; exact H)) as D. lia. }
  assert (D1 : forall p n, In (p, n) ((E, nE) :: l) -> 0 < n -> p <> A1).
  { intros p n H N EQ. subst p. pose proof (af_live_disj RT AF Σ m A1 n1 A1 n [(FT, nF); (A2, n2)] _ ART0 LV ltac:(right; right; exact H)) as D. lia. }
  assert (DE : forall p n, In (p, n) l -> 0 < n -> p <> E).
  { intros p n H N EQ. subst p. pose proof (af_live_disj RT AF Σ m E nE E n [(FT, nF); (A2, n2); (A1, n1)] _ ART0 LV ltac:(right; right; right; exact H)) as D. lia. }
  assert (NL : forall q, (forall p n, In (p, n) l -> 0 < n -> p <> q) -> forall e, In e l -> fst e <> q).
  { intros q H [p n] He. cbn [fst]. exact (H p n He (POS p n He)). }
  rewrite (live_remove_keep' A1 (FT, nF)) by (cbn [fst]; intros EQ; exact (DF A1 n1 ltac:(right; left; reflexivity) P1 (eq_sym EQ))).
  rewrite (live_remove_keep' A1 (A2, n2)) by (cbn [fst]; intros EQ; exact (D2 A1 n1 ltac:(left; reflexivity) P1 (eq_sym EQ))).
  rewrite (live_remove_head' A1).
  rewrite (live_remove_keep' A1 (E, nE)) by (cbn [fst]; exact (D1 E nE ltac:(left; reflexivity) PE)).
  rewrite (live_remove_notin' A1 l) by (apply NL; intros p n H N; exact (D1 p n ltac:(right; exact H) N)).
  rewrite (live_remove_keep' A2 (FT, nF)) by (cbn [fst]; intros EQ; exact (DF A2 n2 ltac:(left; reflexivity) P2 (eq_sym EQ))).
  rewrite (live_remove_head' A2).
  rewrite (live_remove_keep' A2 (E, nE)) by (cbn [fst]; exact (D2 E nE ltac:(right; left; reflexivity) PE)).
  rewrite (live_remove_notin' A2 l) by (apply NL; intros p n H N; exact (D2 p n ltac:(right; right; exact H) N)).
  rewrite (live_remove_head' FT).
  rewrite (live_remove_keep' FT (E, nE)) by (cbn [fst]; exact (DF E nE ltac:(right; right; left; reflexivity) PE)).
  rewrite (live_remove_notin' FT l) by (apply NL; intros p n H N; exact (DF p n ltac:(right; right; right; exact H) N)).
  rewrite (live_remove_head' E).
  apply live_remove_notin'. apply NL. exact DE.
Qed.
End Glk.
