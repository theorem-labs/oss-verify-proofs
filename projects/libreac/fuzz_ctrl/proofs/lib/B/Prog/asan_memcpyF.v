(* Build B (asan-ubsan) port of lib/A/Prog/asan_memcpyF.v (a working branch, commit 33179c325da): the
   namespace lib.A -> lib.B only; the proof script is build A's unchanged. Build B's plain proof asan_memcpy_holds
   (lib/B/Prog/asan_memcpy.v, from bf137c36c75) is lib/A/Prog/asan_memcpy.v modulo namespace, and build B's
   statement lib/B/Prog/asan_memcpy_cF.v is build A's modulo namespace (d7cbfdfafb1).

   asan_memcpy_contract_F (form (D)) by route 1 (ROUTE1.md (a working note, not in this delivery)), in the shape of lib/B/Prog/asan_memsetF.v:
   the run of asan_memcpy_holds on the restricted memory normalize_P m, where P keeps the image [IMG_LO, IMG_HI),
   the helper's frame [sp - 2224, sp), the N bytes at D and at S, and the widened shadow ranges
   [sh_lo D, sh_lo D + sh_len D N) and [sh_lo S, sh_lo S + sh_len S N). MemNormP.evtF_normalize_P turns it into a
   footprint run on m with footprint RNG_P; the rng premises weaken RNG_P to RNG (MemNormP.evtF_RNG_P_weaken_top).

   The walk is this unit's own: BzA.amemcpy_spec (lib/B/Bz/A/I_amemcpy.v, entry ASAN_MEMCPY = 0x52164), with the
   inner copy routine memcpy at 0x98a30 given by asan_memcpy.v's mc_proof. The three cases of the canonical premises are all
   inside this one run: N > 0, D <> S by memcpy_holds; D = S, N > 0 by memcpy_same_holds (route 1 lifts that plain
   run to evtF with the rest); N = 0 by empty checks (qc_words needs 1 <= n, sh_len p 0 = 0).
   The bridge sh_word_rng_sh turns the statement's `sh_word_rng RNG p N` into rng_asan's length form; the premise
   `sh_word_rng RNG (sp - ASAN_MEMCPY_K) ASAN_MEMCPY_K` is not used (P does not keep the frame's shadow).
   Every constant the script unfolds is build B's own: ASAN_MEMCPY = 0x52164 and ASAN_MEMCPY_K = 2224
   (lib/B/Prog/asan_memcpy_c.v), IMG_LO = 0x10000 and IMG_HI = 0x5fe000 (lib/B/Prog/ImgBounds.v), RT_LO, RT_HI
   and the ASan layout (lib/B/AsanRT.v), the segment list rsegs (lib/B/Img0.v). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import MemNorm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTFacts BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memcpy_c rng_asan asan_memcpy.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memcpy_cF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNormP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require RngBytes.
Require OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset.
Import ListNotations.
Open Scope Z_scope.

Module AMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.asan_memset.

(* ---- the bridge: the statement's shadow word span gives rng_asan's length form ---- *)

Lemma rng_nil : forall RNG lo, RngBytes.rng_bytes RNG -> 0 <= lo <= 2^64 -> ExecF.rng RNG lo 0.
Proof.
  intros RNG lo RB Hlo. split; [lia|]. split; [lia|].
  intros b j Hb Hj. assert (j = 0%nat) by lia. subst j.
  apply RB; [lia | lia | intros k Hk; exfalso; lia].
Qed.

Lemma sh_word_rng_sh : forall RNG p n, RngBytes.rng_bytes RNG -> 0 <= p -> 0 <= n -> p + n <= 2^64 ->
  sh_word_rng RNG p n -> ExecF.rng RNG (sh_lo p) (sh_len p n).
Proof.
  intros RNG p n RB Hp Hn Hpn H. unfold sh_word_rng in H.
  destruct (Z.eqb_spec n 0) as [E|E].
  - subst n. replace (sh_len p 0) with 0 by reflexivity. apply (rng_nil RNG _ RB).
    unfold sh_lo, shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
  - destruct H as [H|H]; [lia|].
    replace (sh_lo p) with (sh_al8_lo p) by (unfold sh_lo, sh_al8_lo; ring).
    replace (sh_len p n) with (sh_al8_hi p n - sh_al8_lo p)
      by (unfold sh_len; destruct (Z.eqb_spec n 0); [lia|]; cbv iota; unfold sh_al8_hi, sh_al8_lo, sh_lo; ring).
    exact H.
Qed.

(* The kept byte set P of the run. *)
Definition in_rngb (lo len x : Z) : bool := (lo <=? x) && (x <? lo + len).

Lemma in_rngb_true : forall lo len x, in_rngb lo len x = true <-> lo <= x < lo + len.
Proof.
  intros lo len x. unfold in_rngb. split.
  - intros H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
  - intros H. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
Qed.

Definition PM (sp D S N : Z) (a : word) : bool :=
  in_rngb IMG_LO (IMG_HI - IMG_LO) (bv_unsigned a) || in_rngb (sp - ASAN_MEMCPY_K) ASAN_MEMCPY_K (bv_unsigned a)
  || in_rngb D N (bv_unsigned a) || in_rngb S N (bv_unsigned a)
  || in_rngb (sh_lo D) (sh_len D N) (bv_unsigned a) || in_rngb (sh_lo S) (sh_len S N) (bv_unsigned a).

Lemma PM_or : forall sp D S N x, 0 <= x < 2^64 ->
  (IMG_LO <= x < IMG_HI \/ sp - ASAN_MEMCPY_K <= x < sp \/ D <= x < D + N \/ S <= x < S + N
   \/ sh_lo D <= x < sh_lo D + sh_len D N \/ sh_lo S <= x < sh_lo S + sh_len S N) ->
  PM sp D S N (wa x) = true.
Proof.
  intros sp D S N x Hx H. unfold PM. rewrite wa_unsigned by exact Hx.
  destruct H as [H|[H|[H|[H|[H|H]]]]].
  - apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; left.
    apply orb_true_iff; left. apply in_rngb_true. lia.
  - apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; left.
    apply orb_true_iff; right. apply in_rngb_true. lia.
  - apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; right.
    apply in_rngb_true. lia.
  - apply orb_true_iff; left. apply orb_true_iff; left. apply orb_true_iff; right. apply in_rngb_true. lia.
  - apply orb_true_iff; left. apply orb_true_iff; right. apply in_rngb_true. lia.
  - apply orb_true_iff; right. apply in_rngb_true. lia.
Qed.

Lemma PM_inv : forall sp D S N x, 0 <= x < 2^64 -> PM sp D S N (wa x) = true ->
  IMG_LO <= x < IMG_HI \/ sp - ASAN_MEMCPY_K <= x < sp \/ D <= x < D + N \/ S <= x < S + N
  \/ sh_lo D <= x < sh_lo D + sh_len D N \/ sh_lo S <= x < sh_lo S + sh_len S N.
Proof.
  intros sp D S N x Hx H. unfold PM in H. rewrite wa_unsigned in H by exact Hx.
  apply orb_true_iff in H as [H|H];
    [apply orb_true_iff in H as [H|H];
      [apply orb_true_iff in H as [H|H];
        [apply orb_true_iff in H as [H|H];
          [apply orb_true_iff in H as [H|H]|]|]|]|];
    apply in_rngb_true in H;
    [left | right; left | right; right; left | right; right; right; left
     | right; right; right; right; left | right; right; right; right; right]; lia.
Qed.

(* Arithmetic of the widened shadow range (rng_asan.v). *)
Lemma sh_top : forall p n, 0 <= p -> 0 <= n -> p + n <= 2^64 -> sh_lo p + sh_len p n < 2^64 - 1.
Proof.
  intros p n Hp Hn Hpn. unfold sh_len, sh_lo, shadow_addr, ASAN_K.
  destruct (Z.eqb_spec n 0); cbv iota; Z.div_mod_to_equations; lia.
Qed.

Lemma shad_in_sh : forall p n i, 0 <= p -> 0 <= i < n -> sh_lo p <= BzS.shad (p + i) < sh_lo p + sh_len p n.
Proof.
  intros p n i Hp Hi. unfold BzS.shad, BzS.SHB, sh_len, sh_lo, shadow_addr, ASAN_K.
  destruct (Z.eqb_spec n 0); [lia|]. cbv iota. Z.div_mod_to_equations. lia.
Qed.

Lemma al8_in_sh1 : forall p n i, 0 <= p -> 1 <= n -> 0 <= i < 8 ->
  sh_lo p <= BzQ.al8 (BzS.shad p) + i < sh_lo p + sh_len p n.
Proof.
  intros p n i Hp Hn Hi. unfold BzQ.al8, BzS.shad, BzS.SHB, sh_len, sh_lo, shadow_addr, ASAN_K.
  destruct (Z.eqb_spec n 0); [lia|]. cbv iota. Z.div_mod_to_equations. lia.
Qed.

Lemma al8_in_sh2 : forall p n i, 0 <= p -> 1 <= n -> 0 <= i < 8 ->
  sh_lo p <= BzQ.al8 (BzS.shad (p + n - 1)) + i < sh_lo p + sh_len p n.
Proof.
  intros p n i Hp Hn Hi. unfold BzQ.al8, BzS.shad, BzS.SHB, sh_len, sh_lo, shadow_addr, ASAN_K.
  destruct (Z.eqb_spec n 0); [lia|]. cbv iota. Z.div_mod_to_equations. lia.
Qed.

(* Every loaded segment lies in [IMG_LO, IMG_HI). *)
Definition seg_in_img (segs : list Segment) : bool :=
  forallb (fun s => (IMG_LO <=? Z.of_N (seg_base s)) && (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? IMG_HI))
    segs.

Lemma rsegs_in_img : seg_in_img rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma find_segment_img : forall segs x n s, seg_in_img segs = true -> find_segment segs x n = Some s -> 1 <= n ->
  IMG_LO <= x /\ x + n <= IMG_HI.
Proof.
  induction segs as [|s0 r IH]; intros x n s Hb H Hn; cbn in H; [discriminate H|].
  unfold seg_in_img in Hb. cbn [forallb] in Hb. apply andb_prop in Hb as [H0 Hr].
  apply andb_prop in H0 as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
  destruct (Z.leb (Z.of_N (seg_base s0)) x && Z.leb (x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))) eqn:E.
  - apply andb_prop in E as [E1 E2]. apply Z.leb_le in E1. apply Z.leb_le in E2. lia.
  - exact (IH x n s Hr H Hn).
Qed.

Lemma in_seg_img : forall x, 0 <= x < 2^64 -> MemNormP.in_seg rsegs (wa x) = true -> IMG_LO <= x < IMG_HI.
Proof.
  intros x Hx H. unfold MemNormP.in_seg in H. rewrite wa_unsigned in H by exact Hx.
  destruct (find_segment rsegs x 1) as [s|] eqn:E; [|discriminate H].
  destruct (find_segment_img rsegs x 1 s rsegs_in_img E ltac:(lia)) as [A B]. lia.
Qed.

(* Into the restricted memory: the premises of the Bz run that read memory, from their normalize_cj form. *)
Lemma normP_cj : forall (P : word -> bool) m a b,
  MemNormP.normalize_P rsegs P m a = Some b -> normalize_cj rsegs m a = Some b.
Proof.
  intros P m a b H. unfold MemNormP.normalize_P in H. destruct (MemNormP.keepP rsegs P a) eqn:K; [|discriminate H].
  unfold normalize_cj.
  (* MemNormP states keepP_cj with the ROOT MemNorm.cj_drop; this file binds lib.B.MemNorm, whose body converts. *)
  assert (KC : cj_drop rsegs a = false) by exact (MemNormP.keepP_cj rsegs P a K). rewrite KC. exact H.
Qed.

Lemma wr_at_P_of_cj : forall (P : word -> bool) m a n,
  (forall i, 0 <= i < n -> P (wa (a + i)) = true) ->
  wr_at rsegs (normalize_cj rsegs m) a n -> wr_at rsegs (MemNormP.normalize_P rsegs P m) a n.
Proof.
  intros P m a n HP (W0 & W1 & W). split; [exact W0|]. split; [exact W1|]. intros i Hi.
  rewrite (MemNormP.wview_normalize_P_cj rsegs P m _ (or_introl (HP i Hi))). exact (W i Hi).
Qed.

Lemma ro_cells_P : forall (P : word -> bool) m a cs,
  (forall i, 0 <= i < Z.of_nat (BzCl.cells_size cs) -> P (wa (a + i)) = true) ->
  BzSt.ro_cells BzI.asegs (normalize_cj rsegs m) a cs -> BzSt.ro_cells BzI.asegs (MemNormP.normalize_P rsegs P m) a cs.
Proof.
  intros P m a cs HP [Hwf Hb]. split; [exact Hwf|].
  refine (MemNormP.bytes_at_P_of_cj rsegs P m a (BzCl.cells_bytes cs) _ Hb).
  intros i Hi. left. rewrite (BzCl.cells_bytes_length cs Hwf) in Hi. apply HP. lia.
Qed.

Lemma rw_cells_P : forall (P : word -> bool) m a cs,
  (forall i, 0 <= i < Z.of_nat (BzCl.cells_size cs) -> P (wa (a + i)) = true) ->
  BzSt.rw_cells BzI.asegs (normalize_cj rsegs m) a cs -> BzSt.rw_cells BzI.asegs (MemNormP.normalize_P rsegs P m) a cs.
Proof.
  intros P m a cs HP [HC Hw]. split.
  - exact (ro_cells_P P m a cs HP HC).
  - exact (wr_at_P_of_cj P m a (Z.of_nat (BzCl.cells_size cs)) HP Hw).
Qed.

Lemma acc_P : forall (P : word -> bool) m p n,
  (forall i, 0 <= i < n -> P (wa (BzS.shad (p + i))) = true) ->
  BzS.acc BzI.asegs (normalize_cj rsegs m) p n -> BzS.acc BzI.asegs (MemNormP.normalize_P rsegs P m) p n.
Proof.
  intros P m p n HP H i Hi. destruct (H i Hi) as (b & Hb & Hok). exists b. split; [|exact Hok].
  refine (MemNormP.bytes_at_P_of_cj rsegs P m (BzS.shad (p + i)) [b] _ Hb).
  intros j Hj. cbn [length] in Hj. assert (j = 0%nat) by lia. subst j. left.
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. exact (HP i Hi).
Qed.

(* The helper's range check on the restricted memory: every byte it reads lies in the widened shadow range. *)
Lemma chk_ok_P : forall (P : word -> bool) m p n, 0 <= p ->
  (forall x, sh_lo p <= x < sh_lo p + sh_len p n -> P (wa x) = true) ->
  BzQ.chk_ok (normalize_cj rsegs m) p n -> BzQ.chk_ok (MemNormP.normalize_P rsegs P m) p n.
Proof.
  intros P m p n Hp HP (AC & QW & RO). split; [|split; [|exact RO]].
  - apply (acc_P P m); [|exact AC]. intros i Hi. apply HP. apply shad_in_sh; lia.
  - intros Hn. destruct (QW Hn) as (w1 & w2 & W1 & W2). exists w1, w2. split.
    + apply (ro_cells_P P m); [|exact W1]. intros i Hi.
      change (Z.of_nat (BzCl.cells_size [BzCl.C8 w1])) with 8 in Hi.
      apply HP. apply al8_in_sh1; lia.
    + apply (ro_cells_P P m); [|exact W2]. intros i Hi.
      change (Z.of_nat (BzCl.cells_size [BzCl.C8 w2])) with 8 in Hi.
      apply HP. apply al8_in_sh2; lia.
Qed.

(* Back to the full memory. *)
Lemma stk_rel_P : forall (P : word -> bool) m' m0' lo hi, MemNormP.mem_rel_P rsegs P m' m0' ->
  stk rsegs m0' lo hi -> stk rsegs m' lo hi.
Proof.
  intros P m' m0' lo hi REL (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hw & b & Hb). split.
  - rewrite <- (MemNormP.wview_rel_P rsegs P m' m0' _ REL (MemNormP.keep_of_wview_P rsegs P m' m0' _ REL Hw)).
    exact Hw.
  - exists b. exact (MemNormP.mrd_rel_P rsegs P m' m0' _ b REL Hb).
Qed.

Theorem asan_memcpy_holds_F : asan_memcpy_contract_F.
Proof.
  unfold asan_memcpy_contract_F.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m src junk lo.
  cbv zeta. intros SRC LEN DST OV HN AS AD ES ED H7 HRT HSD HSS HST HK HLO HSP HC HSR HMI
    RB RI RF RDD RSS RSWD RSWS _.
  pose proof AS as (S0 & N0 & SE & _). pose proof AD as (D0 & _ & DE & _).
  pose proof (sh_word_rng_sh RNG (bv_unsigned a0) (bv_unsigned a2) RB D0 N0
                ltac:(unfold APPMEM_END in DE; lia) RSWD) as RSHD.
  pose proof (sh_word_rng_sh RNG (bv_unsigned a1) (bv_unsigned a2) RB S0 N0
                ltac:(unfold APPMEM_END in SE; lia) RSWS) as RSHS.
  clear RSWD RSWS.
  pose (P := PM (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2)).
  assert (PI : forall x, IMG_LO <= x < IMG_HI -> P (wa x) = true).
  { intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x
             ltac:(unfold IMG_LO, IMG_HI in Hx; lia) (or_introl Hx)). }
  assert (PF : forall x, bv_unsigned sp - ASAN_MEMCPY_K <= x < bv_unsigned sp -> P (wa x) = true).
  { pose proof RF as (F0 & F1 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_introl Hx))). }
  assert (PD : forall x, bv_unsigned a0 <= x < bv_unsigned a0 + bv_unsigned a2 -> P (wa x) = true).
  { pose proof RDD as (D1 & D2 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_introl Hx)))). }
  assert (PS : forall x, bv_unsigned a1 <= x < bv_unsigned a1 + bv_unsigned a2 -> P (wa x) = true).
  { pose proof RSS as (S1 & S2 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_intror (or_introl Hx))))). }
  assert (PSD : forall x, sh_lo (bv_unsigned a0) <= x < sh_lo (bv_unsigned a0) + sh_len (bv_unsigned a0) (bv_unsigned a2) ->
            P (wa x) = true).
  { pose proof RSHD as (H1 & H2 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_intror (or_intror (or_introl Hx)))))). }
  assert (PSS : forall x, sh_lo (bv_unsigned a1) <= x < sh_lo (bv_unsigned a1) + sh_len (bv_unsigned a1) (bv_unsigned a2) ->
            P (wa x) = true).
  { pose proof RSHS as (H1 & H2 & _). intros x Hx.
    exact (PM_or (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x ltac:(lia)
             (or_intror (or_intror (or_intror (or_intror (or_intror Hx)))))). }
  assert (P0 : P (wa (2^64 - 1)) = false).
  { destruct (P (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
    destruct (PM_inv (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (2^64 - 1) ltac:(lia) E)
      as [X|[X|[X|[X|[X|X]]]]].
    - unfold IMG_LO, IMG_HI in X. lia.
    - unfold APPMEM_END in HSP. lia.
    - unfold APPMEM_END in DE. lia.
    - unfold APPMEM_END in SE. lia.
    - pose proof (sh_top (bv_unsigned a0) (bv_unsigned a2) D0 N0 ltac:(unfold APPMEM_END in DE; lia)). lia.
    - pose proof (sh_top (bv_unsigned a1) (bv_unsigned a2) S0 N0 ltac:(unfold APPMEM_END in SE; lia)). lia. }
  assert (G0 : MemNormP.in_seg rsegs (wa (2^64 - 1)) = false).
  { destruct (MemNormP.in_seg rsegs (wa (2^64 - 1))) eqn:E; [exfalso|reflexivity].
    pose proof (in_seg_img (2^64 - 1) ltac:(lia) E) as X. unfold IMG_LO, IMG_HI in X. lia. }
  assert (HB : forall x, 0 <= x < 2^64 -> P (wa x) = true \/ MemNormP.in_seg rsegs (wa x) = true -> RNG x 1%nat).
  { intros x Hx [Hp|Hs].
    - destruct (PM_inv (bv_unsigned sp) (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) x Hx Hp)
        as [X|[X|[X|[X|[X|X]]]]].
      + destruct RI as (_ & _ & R). apply R; lia.
      + destruct RF as (_ & _ & R). apply R; lia.
      + destruct RDD as (_ & _ & R). apply R; lia.
      + destruct RSS as (_ & _ & R). apply R; lia.
      + destruct RSHD as (_ & _ & R). apply R; lia.
      + destruct RSHS as (_ & _ & R). apply R; lia.
    - destruct RI as (_ & _ & R). pose proof (in_seg_img x Hx Hs). apply R; lia. }
  apply (MemNormP.evtF_RNG_P_weaken_top rsegs P RNG RB P0 G0 HB).
  clear HB P0 G0.
  unfold ASAN_MEMCPY_K in *.
  pose proof (ro_agree_of_mem_inv m HMI) as RO.
  pose proof (MemNormP.mem_rel_P_normalize rsegs P m RO) as REL0.
  destruct (stk_split rsegs m lo (bv_unsigned sp - 2224) (bv_unsigned sp) HST ltac:(lia)) as [STlo STw].
  assert (EN : Z.of_nat (length src) = bv_unsigned a2) by (rewrite LEN; apply Z2Nat.id; lia).
  assert (S7 : bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a1 + 7)) by (destruct H7 as [?|[? ?]]; [left|right]; assumption).
  assert (D7 : bv_unsigned a2 = 0 \/ app_mem (bv_unsigned a0 + 7)) by (destruct H7 as [?|[? ?]]; [left|right]; assumption).
  apply (ExecF.evtF_mono rsegs (MemNormP.RNG_P rsegs P) (fun st => exists st0,
            BzA.amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) (bv_unsigned a1) src
              (bv_unsigned sp - 2224) (MemNormP.normalize_P rsegs P m) st0
            /\ MemNormP.ms_rel_P rsegs P st st0 /\ MemNormP.same_P rsegs P m (ms_mem st))).
  - apply (MemNormP.evtF_normalize_P rsegs P _ _ F _ fc None m (seg_rom rsegs) wx_apart_asan RO).
    apply bz_evt.
    apply (BzA.amemcpy_spec BzP.rip_proof mc_proof ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9
             s10 s11 t3 t4 t5 t6 F fc (MemNormP.normalize_P rsegs P m) (bv_unsigned a0) (bv_unsigned a1) src junk
             (bv_unsigned sp - 2224)); rewrite ?EN.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + symmetry. apply Z_to_bv_bv_unsigned.
    + refine (MemNormP.stk_P_of_cj rsegs P m (bv_unsigned sp - 2224) (bv_unsigned sp) _
                (stk_normalize m _ _ HMI STw ltac:(unfold TASK_SIZE, APPMEM_END in *; lia))).
      intros x Hx. left. apply PF. exact Hx.
    + lia.
    + unfold BzR.kHighShadowEnd, HIGHMEM_BEG in *. lia.
    + unfold APPMEM_END in *. lia.
    + exact D0.
    + exact S0.
    + unfold APPMEM_END in *. lia.
    + unfold APPMEM_END in *. lia.
    + lia.
    + right. exact HSS.
    + right. exact HSD.
    + assert (HL : bv_unsigned a1 + Z.of_nat (length src) <= TASK_SIZE)
        by (rewrite EN; unfold TASK_SIZE, APPMEM_END in *; lia).
      refine (MemNormP.bytes_at_P_of_cj rsegs P m (bv_unsigned a1) src _ (bytes_normalize_low m (bv_unsigned a1) src RO HL SRC)).
      intros i Hi. left. apply PS. lia.
    + rewrite LEN.
      assert (HL : bv_unsigned a0 + Z.of_nat (Z.to_nat (bv_unsigned a2)) <= TASK_SIZE)
        by (rewrite Z2Nat.id by lia; unfold TASK_SIZE, APPMEM_END in *; lia).
      apply (rw_cells_P P m).
      * intros i Hi. apply PD. cbn [BzCl.cells_size BzCl.csize] in Hi. lia.
      * exact (rw_cb_normalize m (bv_unsigned a0) (Z.to_nat (bv_unsigned a2)) junk HMI HL DST).
    + apply (chk_ok_P P m); [exact S0 | exact PSS |].
      exact (chk_ok_of_ours m (bv_unsigned a1) (bv_unsigned a2) HMI HSR AS ES S7 HN).
    + apply (chk_ok_P P m); [exact D0 | exact PSD |].
      exact (chk_ok_of_ours m (bv_unsigned a0) (bv_unsigned a2) HMI HSR AD ED D7 HN).
    + destruct (BCB.m2s_cells_normalize m HMI HC) as (M1 & M2 & M3).
      unfold BzR.m2s_cells. split; [|split];
        (apply (rw_cells_P P m);
         [intros i Hi; apply PI; cbn [BzCl.cells_size BzCl.csize] in Hi; unfold IMG_LO, IMG_HI; lia | assumption]).
    + destruct (icells_normalize m HMI HC) as (I1 & I2 & I3 & I4 & I5).
      unfold BzW.icells. split; [|split; [|split; [|split]]];
        (apply (ro_cells_P P m);
         [intros i Hi; apply PI; cbn [BzCl.cells_size BzCl.csize] in Hi; unfold IMG_LO, IMG_HI; lia | assumption]).
    + apply BzM.mem_inv_intro; [exact seg_addr_below|].
      intros x b Hx. pose proof (normP_cj P m x b Hx) as Hc. pose proof (bz_mem_inv_normalize m) as BI.
      split; [exact (BzM.mem_inv_ro BzI.asegs _ x b BI Hc) | exact (BzM.mem_inv_ov_below BzI.asegs _ x b BI Hc)].
  - intros st (st0 & HQ & REL & SAME).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                    E0 & MU & WM & MI & ST & RW & B).
    subst st0.
    destruct REL as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8).
    rewrite EN in MU. rewrite LEN in RW.
    assert (MU' : munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2); (bv_unsigned sp - 2224, bv_unsigned sp)]
                    m (ms_mem st))
      by (eapply (MemNormP.munch_rel_P rsegs P); [exact REL0 | exact E8 | exact SAME | exact MU]).
    assert (WM' : wmono rsegs m (ms_mem st))
      by (eapply (MemNormP.wmono_rel_P rsegs P); [exact REL0 | exact E8 | exact SAME | exact WM]).
    assert (RW' : rw_cells rsegs (ms_mem st) (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]).
    { apply rw_cb_of_bz in RW. destruct RW as [[Hwf Hb] Hw].
      split; [split; [exact Hwf | exact (MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 Hb)]
             | exact (MemNormP.wr_at_rel_P rsegs P _ _ _ _ E8 Hw)]. }
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
    split; [|split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]].
    + rewrite Z_to_bv_bv_unsigned in E1.
      destruct st. cbn in E1, E2, E3, E4, E5, E6, E7 |- *. subst. reflexivity.
    + exact MU'.
    + exact WM'.
    + intros x b Hx. destruct (MemNormP.keepP rsegs P x) eqn:K.
      * exact (proj1 (cj_drop_false rsegs x (MemNormP.keepP_cj rsegs P x K))).
      * rewrite (SAME x K) in Hx. exact (HMI x b Hx).
    + apply (stk_merge rsegs _ lo (bv_unsigned sp - 2224) (bv_unsigned sp)); [| exact (stk_rel_P P _ _ _ _ E8 ST) | lia].
      apply (AMS.stk_kept _ m _ lo (bv_unsigned sp - 2224) STlo MU' WM').
      intros x Hx. destruct (Z_lt_le_dec x (bv_unsigned a0)) as [L|L]; [left; cbn; lia|].
      destruct (Z_lt_le_dec x (bv_unsigned a0 + bv_unsigned a2)) as [L2|L2]; [right | left; cbn; lia].
      apply (AMS.rw_cb_mrd _ _ _ _ x RW'). rewrite Z2Nat.id by lia. lia.
    + exact RW'.
    + exact (MemNormP.bytes_at_rel_P rsegs P _ _ _ _ E8 B).
    + apply (asan_cells_kept _ m _ HC MU'). cbn [disjoint_from].
      split; [|split; [|exact I]]; unfold RT_LO, RT_HI, HIGHMEM_BEG in *; lia.
    + apply (shadow_rw_kept m _ HSR); [|exact WM']. apply (munch_meta _ m _ MU'). cbn [all_app].
      split; [exact (addressable_app m _ _ AD)|]. split; [|exact I].
      intros x Hx. unfold app_mem, HIGHMEM_BEG, APPMEM_END in *. right. lia.
Qed.
