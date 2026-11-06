(* lib/A/Prog/bcmp_wrap_Fk.v -- the helper lemmas of lib/A/Prog/bcmp_wrap_F.v (not in this delivery) (blob a719a50daf9, lines 1-325: segs_in ..
   stk_join) over image A's lib/A/MemNormP.v instead of the root lib/MemNormP.v, for bcmp_wrap_on.v, so its closure
   holds one normalization twin (lib.A.MemNorm) only (two Theorem Labs lanes 15:30Z). TEXT: bcmp_wrap_F.v (not in this delivery) lines 1-325 byte for
   byte except line 5 (the MemNormP Require). bcmp_wrap_F.v (not in this delivery) itself is unchanged (its users F18F / F19F keep it).
   rule 24: no function proved (helper lemmas; bcmp_wrap's run is proved in bcmp_wrap_F.v / bcmp_wrap_on.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes ExecF.
Require Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTFacts BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c wrap_kit.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.BzCallBridge.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_memcmp.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_memcmpw.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_qck.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_tramp.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_m2s.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_thread.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_isPoisoned.
Import ListNotations.
Open Scope Z_scope.

Module BCB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.BzCallBridge.
Module BzC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_memcmp.
Module BzW := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_memcmpw.
Module BzQ := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_qck.
Module BzT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.I_tramp.
Module BzR := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_m2s.
Module BzH := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_thread.
Module BzP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Bz.A.R_isPoisoned.

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

Lemma in_ivl_b_true : forall lo hi x, 0 <= x < 2^64 -> lo <= x < hi -> in_ivl_b lo hi (wa x) = true.
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

Lemma P_img : forall slo shi L R N x, IMG_LO <= x < IMG_HI -> bcmp_P slo shi L R N (wa x) = true.
Proof.
  intros slo shi L R N x Hx. unfold bcmp_P. apply existsb_exists. exists (IMG_LO, IMG_HI).
  split; [cbn; tauto|]. cbn [fst snd]. apply in_ivl_b_true; unfold IMG_LO, IMG_HI in *; lia.
Qed.

Lemma P_stk : forall slo shi L R N x, 0 <= slo -> shi <= 2^64 -> slo <= x < shi ->
  bcmp_P slo shi L R N (wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 Hx. unfold bcmp_P. apply existsb_exists. exists (slo, shi).
  split; [cbn; tauto|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_buf1 : forall slo shi L R N x, 0 <= L -> L + N <= 2^64 -> L <= x < L + N ->
  bcmp_P slo shi L R N (wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 Hx. unfold bcmp_P. apply existsb_exists. exists (L, L + N).
  split; [cbn; tauto|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_buf2 : forall slo shi L R N x, 0 <= R -> R + N <= 2^64 -> R <= x < R + N ->
  bcmp_P slo shi L R N (wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 Hx. unfold bcmp_P. apply existsb_exists. exists (R, R + N).
  split; [cbn; tauto|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_sh1 : forall slo shi L R N x, 0 <= L -> 0 < N -> L + N <= 2^47 -> sh_lo L <= x < sh_hi L N ->
  bcmp_P slo shi L R N (wa x) = true.
Proof.
  intros slo shi L R N x H1 H2 H3 Hx. destruct (sh_bounds L N H1 H2 H3) as [B1 B2].
  unfold bcmp_P. apply existsb_exists. exists (shad_ivl L N). split; [cbn; tauto|].
  unfold shad_ivl. destruct (Z.eqb_spec N 0) as [E|E]; [lia|]. cbn [fst snd]. apply in_ivl_b_true; lia.
Qed.

Lemma P_sh2 : forall slo shi L R N x, 0 <= R -> 0 < N -> R + N <= 2^47 -> sh_lo R <= x < sh_hi R N ->
  bcmp_P slo shi L R N (wa x) = true.
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
  (forall x, 0 <= x < 2^64 -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true -> x < 2^47 /\ RNG x 1%nat) ->
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
  (forall x, 0 <= x < 2^64 -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true -> x < 2^47 /\ RNG x 1%nat) ->
  forall Q ms, evtF rsegs (RNG_P rsegs Pb) Q ms -> evtF rsegs RNG Q ms.
Proof.
  intros Pb RNG RB HB Q ms (ms' & Hs & HQ). exists ms'. split; [|exact HQ]. clear HQ.
  induction Hs as [x|x y z [Hsvc (accs & E & Fa)] _ IH]; [apply mstepsF_refl|].
  apply (mstepsF_cons rsegs RNG x y z); [|exact IH]. split; [exact Hsvc|].
  exists accs. split; [exact E|]. eapply Forall_impl; [|exact Fa].
  exact (acc_in_P_lt Pb RNG RB HB).
Qed.

Lemma wr_at_P_of_cj : forall (Pb : word -> bool) m A n,
  (forall i, 0 <= i < n -> Pb (wa (A + i)) = true \/ in_seg rsegs (wa (A + i)) = true) ->
  wr_at rsegs (normalize_cj rsegs m) A n -> wr_at rsegs (normalize_P rsegs Pb m) A n.
Proof.
  intros Pb m A n HP (H1 & H2 & H3). split; [exact H1|]. split; [exact H2|].
  intros i Hi. rewrite (wview_normalize_P_cj rsegs Pb m _ (HP i Hi)). exact (H3 i Hi).
Qed.

Lemma ro_cells_P_of_cj : forall (Pb : word -> bool) m A cs,
  (forall i, (i < length (BzCl.cells_bytes cs))%nat ->
     Pb (wa (A + Z.of_nat i)) = true \/ in_seg rsegs (wa (A + Z.of_nat i)) = true) ->
  BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) A cs ->
  BzSt.ro_cells BzI.asegs (normalize_P rsegs Pb m) A cs.
Proof.
  intros Pb m A cs HP [Hwf Hb]. split; [exact Hwf|].
  exact (bytes_at_P_of_cj rsegs Pb m A (BzCl.cells_bytes cs) HP Hb).
Qed.

Lemma ro_cells_P_img : forall (Pb : word -> bool) m A cs,
  (forall x, IMG_LO <= x < IMG_HI -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
  IMG_LO <= A -> A + Z.of_nat (BzCl.cells_size cs) <= IMG_HI ->
  BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) A cs ->
  BzSt.ro_cells BzI.asegs (normalize_P rsegs Pb m) A cs.
Proof.
  intros Pb m A cs HP H1 H2 Hro. pose proof Hro as [Hwf _].
  apply (ro_cells_P_of_cj Pb m A cs); [|exact Hro].
  intros i Hi. rewrite (BzCl.cells_bytes_length cs Hwf) in Hi. apply HP. lia.
Qed.

Lemma rw_cells_P_img : forall (Pb : word -> bool) m A cs,
  (forall x, IMG_LO <= x < IMG_HI -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
  IMG_LO <= A -> A + Z.of_nat (BzCl.cells_size cs) <= IMG_HI ->
  BzSt.rw_cells BzI.asegs (normalize_cj rsegs m) A cs ->
  BzSt.rw_cells BzI.asegs (normalize_P rsegs Pb m) A cs.
Proof.
  intros Pb m A cs HP H1 H2 [Hc Hw]. split; [exact (ro_cells_P_img Pb m A cs HP H1 H2 Hc)|].
  apply (wr_at_P_of_cj Pb m A (Z.of_nat (BzCl.cells_size cs))); [|exact Hw].
  intros i Hi. apply HP. lia.
Qed.

Lemma m2s_cells_P_of_cj : forall (Pb : word -> bool) m,
  (forall x, IMG_LO <= x < IMG_HI -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
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
  (forall x, IMG_LO <= x < IMG_HI -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
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
  (n <> 0 -> forall x, sh_lo p <= x < sh_hi p n -> Pb (wa x) = true \/ in_seg rsegs (wa x) = true) ->
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
  (* MemNormP states keepP_cj with the ROOT MemNorm.cj_drop; this file binds lib.A.MemNorm, whose body converts. *)
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
  (* MemNormP states keepP_cj with the ROOT MemNorm.cj_drop; E is lib.A.MemNorm's, whose body converts. *)
  assert (KC : cj_drop rsegs a = false) by exact (keepP_cj rsegs Pb a K). rewrite E in KC. discriminate KC.
Qed.

Lemma stk_rel_P : forall (Pb : word -> bool) m' m0' lo hi,
  mem_rel_P rsegs Pb m' m0' -> stk rsegs m0' lo hi -> stk rsegs m' lo hi.
Proof.
  intros Pb m' m0' lo hi REL (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (wview_rel_P rsegs Pb m' m0' _ REL (keep_of_wview_P rsegs Pb m' m0' _ REL Hw)). exact Hw.
  - exists b. exact (mrd_rel_P rsegs Pb m' m0' _ b REL Hb).
Qed.

Lemma stk_sub : forall m lo lo' hi, stk rsegs m lo hi -> lo <= lo' -> lo' <= hi -> stk rsegs m lo' hi.
Proof.
  intros m lo lo' hi (H0 & H1 & H) H2 H3. split; [lia|]. split; [exact H1|]. intros a Ha. apply H. lia.
Qed.

Lemma stk_join : forall m m' lo mid hi,
  stk rsegs m lo hi -> stk rsegs m' mid hi -> munch [(mid, hi)] m m' -> lo <= mid -> stk rsegs m' lo hi.
Proof.
  intros m m' lo mid hi (H0 & H1 & H) (G0 & G1 & G) MU Hlm.
  split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (Z_lt_le_dec a mid) as [Hlt|Hge]; [|exact (G a ltac:(lia))].
  assert (E : m' (wa a) = m (wa a)).
  { apply MU. cbn [outside]. split; [|exact I]. rewrite wa_unsigned by lia. lia. }
  destruct (H a ltac:(lia)) as [Hw (b & Hb)]. split.
  - unfold wview. rewrite E. exact Hw.
  - exists b. unfold mrd. rewrite E. exact Hb.
Qed.
