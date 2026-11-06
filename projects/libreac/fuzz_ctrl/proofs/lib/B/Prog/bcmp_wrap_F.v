(* The footprint proof of the bcmp wrapper of image B. ORIGINAL AUTHOR a Theorem Labs lane, taken BY PATH from
   a working branch dba073859bd lib/B/Prog/bcmp_wrap_F.v (that ref's own bcmp_wrap_c.v,
   blob 5704c00631d, is NOT taken: the published statement of this branch, lib/B/Prog/bcmp_wrap_c.v blob
   28990b512f7 (the blob this tree had at release c5e779efe8c) of F5 2ec9a4d28bf, stays as it is, because three B proofs depend on it).
   RE-FIT to that published statement, mechanically and in two places only: where the proof consumes the
   contract's two shadow-cover premises RSL and RSR, the published text writes the cover as
   `shadow_addr p / 8 * 8 .. shadow_addr (p + n - 1) / 8 * 8 + 8`, while this file's own sh_lo / sh_hi (and so
   the goal's bounds) write the same range as `8 * (shadow_addr p / 8) ..`. The two `exact (rng_byte ...)`
   terms below now name the published form; `lia` closes the bounds, the two forms being equal.
   IMG_LO / IMG_HI are the ones bcmp_wrap_c.v takes from lib/B/Prog/ImgBounds.v (0x10000 / 0x5fe000), not the
   wip's IMG_HI := Eval compute in B.Contract.GT. Nothing else is changed: the statement, the lemma names,
   bcmp_wrap_holds_F and every step are a Theorem Labs lane's. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes ExecF.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require Import MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import memcmp_c bcmp_wrap_c wrap_kit.
(* IMG_LO / IMG_HI by name: bcmp_wrap_c.v takes ImgBounds with Require IMPORT, which does not re-export those
   names, so this file imports ImgBounds too (the wip took them from its own bcmp_wrap_c.v, which we do not
   use). Same two Definitions, 0x10000 and 0x5fe000. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import ImgBounds.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzCallBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.I_memcmp.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.I_memcmpw.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.I_qck.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.I_tramp.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.R_m2s.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.R_thread.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.R_isPoisoned.
Import ListNotations.
Open Scope Z_scope.

Module BCB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzCallBridge.
Module BzC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.I_memcmp.
Module BzW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.I_memcmpw.
Module BzQ := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.I_qck.
Module BzT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.I_tramp.
Module BzR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.R_m2s.
Module BzH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.R_thread.
Module BzP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Bz.A.R_isPoisoned.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LFrame := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMState := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LPropExec := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.

Definition segs_in (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun s => (lo <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? hi)) segs.

Lemma find_segment_in : forall segs lo hi x n s,
  segs_in segs lo hi = true -> find_segment segs x n = Some s -> lo <= x /\ x + n <= hi.
Proof.
  induction segs as [|s0 r IH]; intros lo hi x n s Hb H; cbn in H; [discriminate H|].
  unfold segs_in in Hb. cbn [forallb] in Hb. cbv beta in Hb. apply andb_prop in Hb as [H0 Hr].
  apply andb_prop in H0 as [B0 B1]. apply Z.leb_le in B0. apply Z.leb_le in B1.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - exact (IH lo hi x n s Hr H).
Qed.

Lemma rsegs_in_img : segs_in rsegs IMG_LO IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma in_seg_img : forall a, in_seg rsegs a = true -> IMG_LO <= bv_unsigned a < IMG_HI.
Proof.
  intros a H. unfold in_seg in H.
  destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate H].
  destruct (find_segment_in rsegs IMG_LO IMG_HI (bv_unsigned a) 1 s rsegs_in_img E) as [H1 H2]. lia.
Qed.

Definition in_ivl_b (lo hi : Z) (a : word) : bool := (lo <=? bv_unsigned a) && (bv_unsigned a <? hi).

Lemma in_ivl_b_true : forall lo hi x, 0 <= x < 2^64 -> lo <= x < hi -> in_ivl_b lo hi (LMem.wa x) = true.
Proof.
  intros lo hi x Hx H. unfold in_ivl_b. rewrite wa_unsigned by lia.
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Lemma in_ivl_b_range : forall lo hi a, in_ivl_b lo hi a = true -> lo <= bv_unsigned a < hi.
Proof.
  intros lo hi a H. unfold in_ivl_b in H. apply andb_prop in H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Definition sh_lo (p : Z) : Z := 8 * (shadow_addr p / 8).
Definition sh_hi (p n : Z) : Z := 8 * (shadow_addr (p + n - 1) / 8) + 8.
Definition shad_ivl (p n : Z) : Z * Z := if n =? 0 then (0, 0) else (sh_lo p, sh_hi p n).

Definition bcmp_P (slo shi L R N : Z) (a : word) : bool :=
  existsb (fun r => in_ivl_b (fst r) (snd r) a)
          [(IMG_LO, IMG_HI); (slo, shi); (L, L + N); (R, R + N); shad_ivl L N; shad_ivl R N].

Lemma sh_bounds : forall p n, 0 <= p -> 0 < n -> p + n <= 2^47 -> 0 <= sh_lo p /\ sh_hi p n <= 2^47.
Proof.
  intros p n Hp Hn Hpn. unfold sh_lo, sh_hi, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
Qed.

Lemma P_img : forall slo shi L R N x, IMG_LO <= x < IMG_HI -> bcmp_P slo shi L R N (LMem.wa x) = true.
Proof.
  intros slo shi L R N x Hx. unfold bcmp_P. apply existsb_exists. exists (IMG_LO, IMG_HI).
  split; [cbn; tauto|]. cbn [fst snd]. apply in_ivl_b_true; unfold IMG_LO, IMG_HI in *; lia.
Qed.

Lemma P_stk : forall slo shi L R N x, 0 <= slo -> shi <= 2^64 -> slo <= x < shi ->
  bcmp_P slo shi L R N (LMem.wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 Hx. unfold bcmp_P. apply existsb_exists. exists (slo, shi).
  split; [cbn; tauto|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_buf1 : forall slo shi L R N x, 0 <= L -> L + N <= 2^64 -> L <= x < L + N ->
  bcmp_P slo shi L R N (LMem.wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 Hx. unfold bcmp_P. apply existsb_exists. exists (L, L + N).
  split; [cbn; tauto|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_buf2 : forall slo shi L R N x, 0 <= R -> R + N <= 2^64 -> R <= x < R + N ->
  bcmp_P slo shi L R N (LMem.wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 Hx. unfold bcmp_P. apply existsb_exists. exists (R, R + N).
  split; [cbn; tauto|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_sh1 : forall slo shi L R N x, 0 <= L -> 0 < N -> L + N <= 2^47 -> sh_lo L <= x < sh_hi L N ->
  bcmp_P slo shi L R N (LMem.wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 H3 Hx. destruct (sh_bounds L N H1 H2 H3) as [B1 B2].
  unfold bcmp_P. apply existsb_exists. exists (shad_ivl L N). split; [cbn; tauto|].
  unfold shad_ivl. destruct (Z.eqb_spec N 0) as [E|E]; [lia|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_sh2 : forall slo shi L R N x, 0 <= R -> 0 < N -> R + N <= 2^47 -> sh_lo R <= x < sh_hi R N ->
  bcmp_P slo shi L R N (LMem.wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 H3 Hx. destruct (sh_bounds R N H1 H2 H3) as [B1 B2].
  unfold bcmp_P. apply existsb_exists. exists (shad_ivl R N). split; [cbn; tauto|].
  unfold shad_ivl. destruct (Z.eqb_spec N 0) as [E|E]; [lia|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_lt : forall slo shi L R N a, 0 <= slo -> shi <= 2^47 -> 0 <= L -> 0 <= R -> 0 <= N ->
  L + N <= 2^47 -> R + N <= 2^47 -> bcmp_P slo shi L R N a = true -> bv_unsigned a < 2^47.
Proof.
  intros slo shi L R N a Hslo Hshi HL HR HN HLN HRN H.
  unfold bcmp_P in H. apply existsb_exists in H as (r & Hin & Hr). cbn [In] in Hin.
  destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst r.
  - cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. unfold IMG_LO, IMG_HI in Hr. lia.
  - cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. lia.
  - cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. lia.
  - cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. lia.
  - unfold shad_ivl in Hr. destruct (Z.eqb_spec N 0) as [EN|EN]; cbn [fst snd] in Hr;
      apply in_ivl_b_range in Hr; [lia|].
    destruct (sh_bounds L N HL ltac:(lia) HLN) as [B1 B2]. lia.
  - unfold shad_ivl in Hr. destruct (Z.eqb_spec N 0) as [EN|EN]; cbn [fst snd] in Hr;
      apply in_ivl_b_range in Hr; [lia|].
    destruct (sh_bounds R N HR ltac:(lia) HRN) as [B1 B2]. lia.
Qed.

Lemma rng_byte : forall (RNG : footprint) lo len x, rng RNG lo len -> lo <= x -> x + 1 <= lo + len -> RNG x 1%nat.
Proof. intros RNG lo len x (A & B & H) H1 H2. apply H; [lia|]. change (Z.of_nat 1) with 1. lia. Qed.

Lemma acc_in_P_lt : forall (Pb : word -> bool) (RNG : footprint),
  rng_bytes RNG ->
  (forall x, 0 <= x < 2^64 -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true -> x < 2^47 /\ RNG x 1%nat) ->
  forall ac, acc_in (RNG_P rsegs Pb) ac -> acc_in RNG ac.
Proof.
  intros Pb RNG RB HB [a n] H. unfold acc_in in H |- *. cbn [fst snd] in H |- *.
  assert (Ra : (0 <= bv_unsigned a < 2^64)%Z) by apply bv_unsigned_in_range.
  assert (Hend : (bv_unsigned a + Z.of_nat n <= 2^64)%Z).
  { destruct (Z_le_gt_dec (bv_unsigned a + Z.of_nat n) (2^64)) as [Le|Gt]; [exact Le|]. exfalso.
    assert (E0 : (bv_unsigned a + Z.of_nat (Z.to_nat (2^64 - 1 - bv_unsigned a)) = 2^64 - 1)%Z)
      by (rewrite Z2Nat.id; lia).
    assert (K0 : (Z.to_nat (2^64 - 1 - bv_unsigned a) < n)%nat) by lia.
    pose proof (H _ K0) as X. rewrite E0 in X.
    destruct (HB (2^64 - 1) ltac:(lia) X) as [Hlt _]. lia. }
  apply RB; [lia | exact Hend |]. intros k Hk.
  assert (Hx : (0 <= bv_unsigned a + Z.of_nat k < 2^64)%Z) by lia.
  exact (proj2 (HB _ Hx (H k Hk))).
Qed.

Lemma evtF_P_lt : forall (Pb : word -> bool) (RNG : footprint),
  rng_bytes RNG ->
  (forall x, 0 <= x < 2^64 -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true -> x < 2^47 /\ RNG x 1%nat) ->
  forall Q ms, evtF rsegs (RNG_P rsegs Pb) Q ms -> evtF rsegs RNG Q ms.
Proof.
  intros Pb RNG RB HB Q ms (ms' & Hs & HQ). exists ms'. split; [|exact HQ]. clear HQ.
  induction Hs as [x|x y z [Hsvc (accs & E & Fa)] _ IH]; [apply mstepsF_refl|].
  apply (mstepsF_cons rsegs RNG x y z); [|exact IH]. split; [exact Hsvc|].
  exists accs. split; [exact E|]. eapply Forall_impl; [|exact Fa].
  exact (acc_in_P_lt Pb RNG RB HB).
Qed.

Lemma wr_at_P_of_cj : forall (Pb : word -> bool) m A n,
  (forall i, 0 <= i < n -> Pb (LMem.wa (A + i)) = true \/ in_seg rsegs (LMem.wa (A + i)) = true) ->
  wr_at rsegs (normalize_cj rsegs m) A n -> wr_at rsegs (normalize_P rsegs Pb m) A n.
Proof.
  intros Pb m A n HP (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite (wview_normalize_P_cj rsegs Pb m _ (HP i Hi)). exact (H3 i Hi).
Qed.

Lemma ro_cells_P_of_cj : forall (Pb : word -> bool) m A cs,
  (forall i, (i < length (BzCl.cells_bytes cs))%nat ->
     Pb (LMem.wa (A + Z.of_nat i)) = true \/ in_seg rsegs (LMem.wa (A + Z.of_nat i)) = true) ->
  BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) A cs ->
  BzSt.ro_cells BzI.asegs (normalize_P rsegs Pb m) A cs.
Proof.
  intros Pb m A cs HP [Hwf Hb]. split; [exact Hwf|].
  exact (bytes_at_P_of_cj rsegs Pb m A (BzCl.cells_bytes cs) HP Hb).
Qed.

Lemma ro_cells_P_img : forall (Pb : word -> bool) m A cs,
  (forall x, IMG_LO <= x < IMG_HI -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  IMG_LO <= A -> A + Z.of_nat (BzCl.cells_size cs) <= IMG_HI ->
  BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) A cs ->
  BzSt.ro_cells BzI.asegs (normalize_P rsegs Pb m) A cs.
Proof.
  intros Pb m A cs HP H1 H2 Hro. pose proof Hro as [Hwf _].
  apply (ro_cells_P_of_cj Pb m A cs); [|exact Hro].
  intros i Hi. rewrite (BzCl.cells_bytes_length cs Hwf) in Hi. apply HP. lia.
Qed.

Lemma rw_cells_P_img : forall (Pb : word -> bool) m A cs,
  (forall x, IMG_LO <= x < IMG_HI -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  IMG_LO <= A -> A + Z.of_nat (BzCl.cells_size cs) <= IMG_HI ->
  BzSt.rw_cells BzI.asegs (normalize_cj rsegs m) A cs ->
  BzSt.rw_cells BzI.asegs (normalize_P rsegs Pb m) A cs.
Proof.
  intros Pb m A cs HP H1 H2 [Hc Hw]. split; [exact (ro_cells_P_img Pb m A cs HP H1 H2 Hc)|].
  apply (wr_at_P_of_cj Pb m A (Z.of_nat (BzCl.cells_size cs))); [|exact Hw].
  intros i Hi. apply HP. lia.
Qed.

Lemma m2s_cells_P_of_cj : forall (Pb : word -> bool) m,
  (forall x, IMG_LO <= x < IMG_HI -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  BzR.m2s_cells (normalize_cj rsegs m) -> BzR.m2s_cells (normalize_P rsegs Pb m).
Proof.
  intros Pb m HP (C1 & C2 & C3). split; [|split].
  - apply (rw_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C1].
  - apply (rw_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C2].
  - apply (rw_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C3].
Qed.

Lemma icells_mcmp_P_of_cj : forall (Pb : word -> bool) m,
  (forall x, IMG_LO <= x < IMG_HI -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  BzW.icells_mcmp (normalize_cj rsegs m) -> BzW.icells_mcmp (normalize_P rsegs Pb m).
Proof.
  intros Pb m HP (C1 & C2 & C3 & C4 & C5 & C6 & C7).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - apply (ro_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C1].
  - apply (ro_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C2].
  - apply (ro_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C3].
  - apply (ro_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C4].
  - apply (rw_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C5].
  - apply (ro_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C6].
  - apply (ro_cells_P_img Pb m _ _ HP);
      [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia | exact C7].
Qed.

Lemma chk_ok_P_of_cj : forall (Pb : word -> bool) m p n,
  0 <= p -> 0 <= n ->
  (n <> 0 -> forall x, sh_lo p <= x < sh_hi p n -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  BzQ.chk_ok (normalize_cj rsegs m) p n -> BzQ.chk_ok (normalize_P rsegs Pb m) p n.
Proof.
  intros Pb m p n Hp Hn HP (AC & QW & RO). split; [|split; [|exact RO]].
  - intros i Hi. destruct (AC i Hi) as (b & Hb & Ok). exists b. split; [|exact Ok].
    apply (bytes_at_P_of_cj rsegs Pb m (BzS.shad (p + i)) [b]); [|exact Hb].
    intros j Hj. cbn [length] in Hj. assert (Ej : j = 0%nat) by lia. subst j.
    change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
    apply (HP ltac:(lia)). unfold BzS.shad, BzS.SHB, sh_lo, sh_hi, shadow_addr, ASAN_K.
    Z.div_mod_to_equations. lia.
  - intros Hn64. destruct (QW Hn64) as (w1 & w2 & W1 & W2). exists w1, w2. split.
    + apply (ro_cells_P_of_cj Pb m _ _); [|exact W1].
      intros i Hi. cbn [BzCl.cells_bytes BzCl.cbytes] in Hi. rewrite app_nil_r, length_le8 in Hi.
      apply (HP ltac:(lia)). unfold BzQ.al8, BzS.shad, BzS.SHB, sh_lo, sh_hi, shadow_addr, ASAN_K.
      Z.div_mod_to_equations. lia.
    + apply (ro_cells_P_of_cj Pb m _ _); [|exact W2].
      intros i Hi. cbn [BzCl.cells_bytes BzCl.cbytes] in Hi. rewrite app_nil_r, length_le8 in Hi.
      apply (HP ltac:(lia)). unfold BzQ.al8, BzS.shad, BzS.SHB, sh_lo, sh_hi, shadow_addr, ASAN_K.
      Z.div_mod_to_equations. lia.
Qed.

Lemma normalize_P_some_cj : forall (Pb : word -> bool) m a b,
  normalize_P rsegs Pb m a = Some b -> normalize_cj rsegs m a = Some b.
Proof.
  intros Pb m a b H. unfold normalize_P in H. destruct (keepP rsegs Pb a) eqn:K; [|discriminate H].
  unfold normalize_cj.
  (* MemNormP states keepP_cj with the ROOT MemNorm.cj_drop; this file binds lib.B.MemNorm, whose body converts. *)
  assert (KC : cj_drop rsegs a = false) by exact (keepP_cj rsegs Pb a K). rewrite KC. exact H.
Qed.

Lemma bz_mem_inv_normalize_P : forall (Pb : word -> bool) m, BzM.mem_inv BzI.asegs (normalize_P rsegs Pb m).
Proof.
  intros Pb m. apply BzM.mem_inv_intro; [exact seg_addr_below|].
  intros a b H. pose proof (normalize_P_some_cj Pb m a b H) as H'. split.
  - exact (BzM.mem_inv_ro BzI.asegs (normalize_cj rsegs m) a b (bz_mem_inv_normalize m) H').
  - exact (BzM.mem_inv_ov_below BzI.asegs (normalize_cj rsegs m) a b (bz_mem_inv_normalize m) H').
Qed.

Lemma cj_same_of_same_P : forall (Pb : word -> bool) m m', same_P rsegs Pb m m' -> cj_same rsegs m m'.
Proof.
  intros Pb m m' H a E. apply H.
  destruct (keepP rsegs Pb a) eqn:K; [|reflexivity]. exfalso.
  (* MemNormP states keepP_cj with the ROOT MemNorm.cj_drop; E is lib.B.MemNorm's, whose body converts. *)
  assert (KC : cj_drop rsegs a = false) by exact (keepP_cj rsegs Pb a K). rewrite E in KC. discriminate KC.
Qed.

Lemma stk_rel_P : forall (Pb : word -> bool) m' m0' lo hi,
  mem_rel_P rsegs Pb m' m0' -> LFrame.stk rsegs m0' lo hi -> LFrame.stk rsegs m' lo hi.
Proof.
  intros Pb m' m0' lo hi REL (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_P rsegs Pb m' m0' _ REL (keep_of_wview_P rsegs Pb m' m0' _ REL Hw)). exact Hw.
  - exists b. exact (mrd_rel_P rsegs Pb m' m0' _ b REL Hb).
Qed.

Lemma stk_sub : forall m lo lo' hi, LFrame.stk rsegs m lo hi -> lo <= lo' -> lo' <= hi -> LFrame.stk rsegs m lo' hi.
Proof.
  intros m lo lo' hi (H0 & H1 & H) H2 H3. split; [lia|]. split; [exact H1|]. intros a Ha. apply H. lia.
Qed.

Lemma stk_join : forall m m' lo mid hi,
  LFrame.stk rsegs m lo hi -> LFrame.stk rsegs m' mid hi -> munch [(mid, hi)] m m' -> lo <= mid -> LFrame.stk rsegs m' lo hi.
Proof.
  intros m m' lo mid hi (H0 & H1 & H) (G0 & G1 & G) MU Hlm.
  split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (Z_lt_le_dec a mid) as [Hlt|Hge]; [|exact (G a ltac:(lia))].
  assert (E : m' (LMem.wa a) = m (LMem.wa a)).
  { apply MU. cbn [outside]. split; [|exact I]. rewrite wa_unsigned by lia. lia. }
  destruct (H a ltac:(lia)) as [Hw (b & Hb)]. split.
  - unfold wview. rewrite E. exact Hw.
  - exists b. unfold mrd. rewrite E. exact Hb.
Qed.

Lemma wrap_post_P : forall (Pb : word -> bool) W m m' m0' lo hi,
  mem_inv rsegs m -> asan_cells m -> shadow_rw m ->
  mem_rel_P rsegs Pb m' m0' -> same_P rsegs Pb m m' ->
  munch W (normalize_P rsegs Pb m) m0' -> wmono rsegs (normalize_P rsegs Pb m) m0' -> LFrame.stk rsegs m0' lo hi ->
  all_app W -> disjoint_from W RT_LO (RT_HI - RT_LO) ->
  munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ LFrame.stk rsegs m' lo hi /\ asan_cells m' /\ shadow_rw m'.
Proof.
  intros Pb W m m' m0' lo hi HMI HC HSR E8 SAME MU WM ST AW DJ.
  pose proof (mem_rel_P_normalize rsegs Pb m (ro_agree_of_mem_inv m HMI)) as REL0.
  assert (MU' : munch W m m') by (eapply munch_rel_P; [exact REL0 | exact E8 | exact SAME | exact MU]).
  assert (WM' : wmono rsegs m m') by (eapply wmono_rel_P; [exact REL0 | exact E8 | exact SAME | exact WM]).
  split; [exact MU'|]. split; [exact WM'|].
  split; [exact (mem_inv_of_normalized m m' HMI (cj_same_of_same_P Pb m m' SAME))|].
  split; [exact (stk_rel_P Pb m' m0' lo hi E8 ST)|].
  split; [exact (asan_cells_kept W m m' HC MU' DJ)|].
  exact (shadow_rw_kept m m' HSR (munch_meta W m m' MU' AW) WM').
Qed.

Lemma bcmp_wrap_F_core : forall (Pb : word -> bool) (RNG : footprint)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (v lo : Z),
  (forall x, IMG_LO <= x < IMG_HI -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  (forall x, bv_unsigned sp - BCMP_WRAP_K <= x < bv_unsigned sp ->
     Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  (forall x, bv_unsigned a0 <= x < bv_unsigned a0 + bv_unsigned a2 ->
     Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  (forall x, bv_unsigned a1 <= x < bv_unsigned a1 + bv_unsigned a2 ->
     Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  (bv_unsigned a2 <> 0 -> forall x, sh_lo (bv_unsigned a0) <= x < sh_hi (bv_unsigned a0) (bv_unsigned a2) ->
     Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  (bv_unsigned a2 <> 0 -> forall x, sh_lo (bv_unsigned a1) <= x < sh_hi (bv_unsigned a1) (bv_unsigned a2) ->
     Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true) ->
  (forall x, 0 <= x < 2^64 -> Pb (LMem.wa x) = true \/ in_seg rsegs (LMem.wa x) = true -> x < 2^47 /\ RNG x 1%nat) ->
  rng_bytes RNG ->
  bytes_at rsegs m (bv_unsigned a0) ls ->
  bytes_at rsegs m (bv_unsigned a1) rs ->
  memcmp_model ls rs (Z.to_nat (bv_unsigned a2)) = Some v ->
  mem_inv rsegs m ->
  (bv_unsigned a2 <= 2^40)%Z ->
  addressable m (bv_unsigned a0) (bv_unsigned a2) -> addressable m (bv_unsigned a1) (bv_unsigned a2) ->
  end_in_app (bv_unsigned a0) (bv_unsigned a2) -> end_in_app (bv_unsigned a1) (bv_unsigned a2) ->
  (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7))%Z -> (bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a1 + 7))%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned sp - BCMP_WRAP_K \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  LFrame.stk rsegs m lo (bv_unsigned sp) -> (lo + BCMP_WRAP_K <= bv_unsigned sp)%Z ->
  (HIGHMEM_BEG <= lo)%Z -> (bv_unsigned sp <= APPMEM_END)%Z ->
  asan_cells m -> shadow_rw m ->
  bytes_at rsegs m REAL_BCMP (le8 (LMem.wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (LMem.wa MEMCMP)) ->
  bytes_at rsegs m GOT_CF (le8 (LMem.wa CF)) ->
  bytes_at rsegs m (CF + 254)%Z [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255)%Z [Z_to_bv 8 1] ->
  evtF rsegs RNG (bcmp_wrap_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs v lo m)
    (LMState.MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 BCMP_WRAP) fc None m (LPropExec.seg_rom rsegs)).
Proof.
  intros Pb RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m ls rs v lo HPimg HPstk HPL HPR HPsL HPsR HB RB.
  intros BUFL BUFR HM HMI HN ADL ADR EAL EAR A7L A7R SEPL SEPR HST HK HLO HSP HC HSR HRB HRM HGCF HF4 HF5.
  unfold BCMP_WRAP_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof ADL as (L0 & N0 & LE & _). pose proof ADR as (R0 & _ & RE & _).
  unfold APPMEM_END in LE, RE, HSP. unfold HIGHMEM_BEG in HLO.
  assert (HM' : BzSF.memcmp_model (firstn (Z.to_nat (bv_unsigned a2)) ls) (firstn (Z.to_nat (bv_unsigned a2)) rs)
                  (Z.to_nat (bv_unsigned a2)) = Some v) by (rewrite memcmp_model_firstn; exact HM).
  assert (LL : (length (firstn (Z.to_nat (bv_unsigned a2)) ls) <= Z.to_nat (bv_unsigned a2))%nat)
    by (rewrite length_firstn; lia).
  assert (LR : (length (firstn (Z.to_nat (bv_unsigned a2)) rs) <= Z.to_nat (bv_unsigned a2))%nat)
    by (rewrite length_firstn; lia).
  assert (BL : bytes_at rsegs m (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)).
  { apply (bytes_at_prefix m _ _ (skipn (Z.to_nat (bv_unsigned a2)) ls)). rewrite firstn_skipn. exact BUFL. }
  assert (BR : bytes_at rsegs m (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs)).
  { apply (bytes_at_prefix m _ _ (skipn (Z.to_nat (bv_unsigned a2)) rs)). rewrite firstn_skipn. exact BUFR. }
  apply (evtF_P_lt Pb RNG RB HB).
  apply (evtF_mono rsegs (RNG_P rsegs Pb)
           (fun st => exists st0,
              BzH.frame_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc v
                [(bv_unsigned sp - 4560, bv_unsigned sp)] (bv_unsigned sp - 4560) (normalize_P rsegs Pb m) st0
              /\ ms_rel_P rsegs Pb st st0 /\ same_P rsegs Pb m (ms_mem st))).
  - apply (evtF_normalize_P rsegs Pb _ _ F _ fc None m (LPropExec.seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply BzT.tramp_bcmp.
    apply (BzC.ibcmp_spec BzP.rip_proof mcmp_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8
             s9 s10 s11 t3 t4 t5 t6 F fc (normalize_P rsegs Pb m) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)
             (firstn (Z.to_nat (bv_unsigned a2)) ls) (firstn (Z.to_nat (bv_unsigned a2)) rs) v
             (bv_unsigned sp - 4560) (bv_unsigned sp - 4560)).
    + unfold BzC.bcmp_cell.
      apply (ro_cells_P_img Pb m _ _ HPimg);
        [unfold IMG_LO; lia | cbn [BzCl.cells_size BzCl.csize Nat.add]; unfold IMG_HI; lia |].
      apply (AMC.ro_c8_norm m _ _ RO); [unfold TASK_SIZE; lia | exact HRB].
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + unfold BzW.cmp_pre.
      split; [exact LL|]. split; [exact LR|]. split; [exact HM'|].
      split; [lia|]. split; [lia|]. split; [lia|].
      split; [lia|]. split; [lia|].
      split.
      { apply (bytes_at_P_of_cj rsegs Pb m (bv_unsigned a0) (firstn (Z.to_nat (bv_unsigned a2)) ls)).
        - intros i Hi. rewrite length_firstn in Hi. apply HPL. lia.
        - apply (bytes_normalize_low m _ _ RO); [rewrite length_firstn; unfold TASK_SIZE; lia | exact BL]. }
      split.
      { apply (bytes_at_P_of_cj rsegs Pb m (bv_unsigned a1) (firstn (Z.to_nat (bv_unsigned a2)) rs)).
        - intros i Hi. rewrite length_firstn in Hi. apply HPR. lia.
        - apply (bytes_normalize_low m _ _ RO); [rewrite length_firstn; unfold TASK_SIZE; lia | exact BR]. }
      split; [lia|]. split; [lia|].
      split.
      { apply (chk_ok_P_of_cj Pb m (bv_unsigned a0) (bv_unsigned a2)); [lia | lia | exact HPsL |].
        exact (AMC.chk_ok_of_ours m _ _ HMI HSR ADL EAL A7L HN). }
      split.
      { apply (chk_ok_P_of_cj Pb m (bv_unsigned a1) (bv_unsigned a2)); [lia | lia | exact HPsR |].
        exact (AMC.chk_ok_of_ours m _ _ HMI HSR ADR EAR A7R HN). }
      split.
      { apply (m2s_cells_P_of_cj Pb m HPimg). exact (BCB.m2s_cells_normalize m HMI HC). }
      apply (icells_mcmp_P_of_cj Pb m HPimg). exact (icells_mcmp_norm m HMI HC HGCF HRM HF4 HF5).
    + lia.
    + apply (stk_P_of_cj rsegs Pb m (bv_unsigned sp - 4560) (bv_unsigned sp) HPstk).
      apply (stk_normalize m (bv_unsigned sp - 4560) (bv_unsigned sp) HMI); [|unfold TASK_SIZE; lia].
      exact (stk_sub m lo (bv_unsigned sp - 4560) (bv_unsigned sp) HST ltac:(lia) ltac:(lia)).
    + lia.
    + unfold BzR.kHighShadowEnd. lia.
    + lia.
    + exact (bz_mem_inv_normalize_P Pb m).
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    destruct (stack_W_ok (bv_unsigned sp - 4560) (bv_unsigned sp) ltac:(unfold HIGHMEM_BEG; lia) ltac:(lia)
                ltac:(unfold APPMEM_END; lia)) as [AW DJ].
    destruct (wrap_post_P Pb [(bv_unsigned sp - 4560, bv_unsigned sp)] m (ms_mem st) m0'
                (bv_unsigned sp - 4560) (bv_unsigned sp) HMI HC HSR E8 SAME MU WM ST AW DJ)
      as (MU' & WM' & MI' & ST' & HC' & HSR').
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [exact MU'|split; [exact WM'|split; [exact MI'|split; [|split; [exact HC'|split; [exact HSR'|split]]]]]]].
    + destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + exact (stk_join m (ms_mem st) lo (bv_unsigned sp - 4560) (bv_unsigned sp) HST ST' MU' ltac:(lia)).
    + apply (bytes_at_transport rsegs [(bv_unsigned sp - 4560, bv_unsigned sp)] m (ms_mem st)); [exact BL | exact MU' |].
      rewrite length_firstn. cbn [disjoint_from]. split; [lia | exact I].
    + apply (bytes_at_transport rsegs [(bv_unsigned sp - 4560, bv_unsigned sp)] m (ms_mem st)); [exact BR | exact MU' |].
      rewrite length_firstn. cbn [disjoint_from]. split; [lia | exact I].
Qed.

Theorem bcmp_wrap_holds_F : bcmp_wrap_contract_F.
Proof.
  unfold bcmp_wrap_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m ls rs v lo.
  cbv zeta. intros BUFL BUFR HM HMI HN ADL ADR EAL EAR A7L A7R SEPL SEPR HST HK HLO HSP HC HSR HRB HRM HGCF HF4 HF5
    RB RIMG RSTK RL RSL RR RSR.
  unfold BCMP_WRAP_K in *.
  pose proof ADL as (L0 & N0 & LE & _). pose proof ADR as (R0 & _ & RE & _).
  unfold APPMEM_END in LE, RE, HSP. unfold HIGHMEM_BEG in HLO.
  apply (bcmp_wrap_F_core
           (bcmp_P (bv_unsigned sp - 4560) (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)) RNG);
    try assumption.
  - intros x Hx. left. apply P_img. exact Hx.
  - intros x Hx. unfold BCMP_WRAP_K in Hx. left. apply P_stk; lia.
  - intros x Hx. left. apply P_buf1; lia.
  - intros x Hx. left. apply P_buf2; lia.
  - intros Hne x Hx. left. apply P_sh1; lia.
  - intros Hne x Hx. left. apply P_sh2; lia.
  - intros x Hx [HPx|HSx].
    + split.
      * rewrite <- (wa_unsigned x ltac:(lia)).
        refine (P_lt _ _ _ _ _ _ _ _ _ _ _ _ _ HPx); lia.
      * unfold bcmp_P in HPx. apply existsb_exists in HPx as (r & Hin & Hr). cbn [In] in Hin.
        destruct Hin as [E|[E|[E|[E|[E|[E|[]]]]]]]; subst r.
        -- cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. rewrite wa_unsigned in Hr by lia.
           unfold IMG_LO, IMG_HI in Hr.
           exact (rng_byte RNG IMG_LO (IMG_HI - IMG_LO) x RIMG ltac:(unfold IMG_LO, IMG_HI; lia)
                    ltac:(unfold IMG_LO, IMG_HI; lia)).
        -- cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. rewrite wa_unsigned in Hr by lia.
           exact (rng_byte RNG (bv_unsigned sp - 4560) 4560 x RSTK ltac:(lia) ltac:(lia)).
        -- cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. rewrite wa_unsigned in Hr by lia.
           exact (rng_byte RNG (bv_unsigned a0) (bv_unsigned a2) x RL ltac:(lia) ltac:(lia)).
        -- cbn [fst snd] in Hr. apply in_ivl_b_range in Hr. rewrite wa_unsigned in Hr by lia.
           exact (rng_byte RNG (bv_unsigned a1) (bv_unsigned a2) x RR ltac:(lia) ltac:(lia)).
        -- unfold shad_ivl in Hr. destruct (Z.eqb_spec (bv_unsigned a2) 0) as [EN|EN]; cbn [fst snd] in Hr;
             apply in_ivl_b_range in Hr; rewrite wa_unsigned in Hr by lia; [lia|].
           destruct RSL as [EZ|RSL]; [lia|]. unfold sh_lo, sh_hi in Hr.
           exact (rng_byte RNG (shadow_addr (bv_unsigned a0) / 8 * 8)
                    (shadow_addr (bv_unsigned a0 + bv_unsigned a2 - 1) / 8 * 8 + 8
                       - shadow_addr (bv_unsigned a0) / 8 * 8) x RSL ltac:(lia) ltac:(lia)).
        -- unfold shad_ivl in Hr. destruct (Z.eqb_spec (bv_unsigned a2) 0) as [EN|EN]; cbn [fst snd] in Hr;
             apply in_ivl_b_range in Hr; rewrite wa_unsigned in Hr by lia; [lia|].
           destruct RSR as [EZ|RSR]; [lia|]. unfold sh_lo, sh_hi in Hr.
           exact (rng_byte RNG (shadow_addr (bv_unsigned a1) / 8 * 8)
                    (shadow_addr (bv_unsigned a1 + bv_unsigned a2 - 1) / 8 * 8 + 8
                       - shadow_addr (bv_unsigned a1) / 8 * 8) x RSR ltac:(lia) ltac:(lia)).
    + pose proof (in_seg_img _ HSx) as Hi. rewrite wa_unsigned in Hi by lia.
      unfold IMG_LO, IMG_HI in Hi. split; [lia|].
      exact (rng_byte RNG IMG_LO (IMG_HI - IMG_LO) x RIMG ltac:(unfold IMG_LO, IMG_HI; lia)
               ltac:(unfold IMG_LO, IMG_HI; lia)).
Qed.
