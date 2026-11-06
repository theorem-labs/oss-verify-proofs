(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import ITree Nodes Decode Image.
From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Decode NodesCfg DecodeCfg.   (* [comment removed for export] *)
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import Prelim Monad MSafe Stdio Malloc Harness Target Driver Prog KInv KStep Relim ModelInv
  MI_Inv MI_Cnt LB_Tables LB_Inv LB_Sum LB_Logic LB_StmtA LB_Raw LB_Init LB_WMalloc LB_Alloc LB_PDriver LB_PTarget.
From OSSVerify.Proofs.openssl.pem.lib.Spec Require Import UnforcedK.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).

From OSSVerify.Proofs.openssl.pem.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Notation nstep := NodesCfg.nstep_c (only parsing).
(* [comment removed for export] *)
Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition Pstat (c : Z) : Z := if c <? 12 then 8192 else 64.

Lemma Pstat_nonneg : forall c, 0 <= Pstat c.
Proof. intros; unfold Pstat; destruct (c <? 12); lia. Qed.
Lemma Pstat_ge64 : forall c, 64 <= Pstat c.
Proof. intros; unfold Pstat; destruct (c <? 12); lia. Qed.

Lemma PHI_Pstat_val : PHI Pstat = ltac:(let v := eval vm_compute in (PHI Pstat) in exact v).
Proof. vm_compute. reflexivity. Qed.

Lemma PHI_Pstat : PHI Pstat + 5 * (MAX_INPUT + 1 + IB + UNIT + 4096) <= LBUDGET.
Proof. rewrite PHI_Pstat_val. vm_compute. discriminate. Qed.
(* [comment removed for export] *)
Lemma PHI_Pstat_room : PHI Pstat + 2 * (MAX_INPUT + 1 + 8192) + BIG_ROOM <= LBUDGET.
Proof. rewrite PHI_Pstat_val. vm_compute. discriminate. Qed.

Definition mal_okQ (X : list (bptr * Z)) (n : Z) : Prop :=
  ROOMX X Pstat n /\ PHI Pstat + R63X X + bigb n <= LBUDGET.

Lemma bigb_le n : 0 <= n -> bigb n <= n + IB + UNIT + 4096.
Proof.
  intros Hn. unfold bigb. destruct (MMAP_THRESHOLD <=? n); [| unfold IB, UNIT; lia].
  pose proof (round_up_pg_spec (n + IB + UNIT)) as [[_ H] _]. lia.
Qed.

Lemma R63X_small X : smallX X -> R63X X <= zlen X * (MAX_INPUT + 1 + IB + UNIT + 4096).
Proof.
  induction X as [|[p n] X IH]; intros SX.
  - unfold R63X, zsum, zlen. cbn. lia.
  - rewrite R63X_cons. inversion SX as [|x l Hx HX]; subst. cbn [snd] in Hx. specialize (IH HX).
    pose proof (bigb_le n ltac:(lia)). unfold zlen in *. cbn [length]. rewrite Nat2Z.inj_succ. unfold IB, UNIT in *. lia.
Qed.

Lemma LRX_le_len X c : LRX X c <= zlen X.
Proof. unfold LRX. apply zcount_le_len. Qed.
Lemma n63X_le_len X : n63X X <= zlen X.
Proof. unfold n63X. apply zcount_le_len. Qed.

(* [comment removed for export] *)
Lemma OK_small : forall X n, (length X <= 4)%nat -> smallX X -> 0 <= n <= MAX_INPUT + 1 -> mal_okQ X n.
Proof.
  intros X n HL SX Hn. assert (HzL : zlen X <= 4) by (unfold zlen; lia).
  pose proof (LRX_le_len X (size_to_class n)). pose proof (n63X_le_len X).
  split.
  - split; intros _; [pose proof (Pstat_ge64 (size_to_class n))| pose proof (Pstat_ge64 63)]; lia.
  - pose proof (R63X_small X SX). pose proof (bigb_le n ltac:(lia)). pose proof PHI_Pstat.
    pose proof (R63X_nonneg X). unfold IB, UNIT, MAX_INPUT in *. nia.
Qed.

Lemma OK_first : mal_okQ [] 65536.
Proof. apply OK_small; [cbn; lia| constructor| unfold MAX_INPUT; lia]. Qed.

Lemma OK_grow : forall b k, (k <= 9)%nat -> mal_okQ [(b, 65536 * 2 ^ Z.of_nat k)] (65536 * 2 ^ Z.of_nat k * 2).
Proof.
  intros b k Hk. assert (Hp1 : 0 < 2 ^ Z.of_nat k) by (apply Z.pow_pos_nonneg; lia).
  assert (Hp2 : 2 ^ Z.of_nat k <= 2 ^ 9) by (apply Z.pow_le_mono_r; lia). change (2 ^ 9) with 512 in Hp2.
  apply OK_small; [cbn; lia| |unfold MAX_INPUT; lia].
  constructor; [cbn [snd]; unfold MAX_INPUT; lia| constructor].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition tier_f (k : Z) : bool := Bool.eqb (stc_k k <? 12) (k <? 15).
Lemma tier_b_true : forallb tier_f (zrange 0 8191) = true. Proof. vm_compute. reflexivity. Qed.
Lemma class_tier n : 0 <= n < MMAP_THRESHOLD -> (size_to_class n <? 12) = (n <=? TIER_A_MAX).
Proof.
  intros Hn. rewrite size_to_class_k. rewrite Z.shiftr_div_pow2 by lia. unfold IB, MMAP_THRESHOLD, TIER_A_MAX in *.
  set (k := (n + 4 - 1) / 2 ^ 4).
  assert (Hk : 0 <= k < 8191) by (subst k; change (2 ^ 4) with 16; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  assert (Hk2 : 16 * k <= n + 3 < 16 * k + 16) by (subst k; change (2 ^ 4) with 16; pose proof (Z.div_mod (n + 4 - 1) 16 ltac:(lia)); pose proof (Z.mod_pos_bound (n + 4 - 1) 16 ltac:(lia)); lia).
  pose proof (forallb_zrange tier_f 0 8191 k tier_b_true ltac:(lia) ltac:(lia)) as H. unfold tier_f in H.
  apply Bool.eqb_prop in H. rewrite H. destruct (Z.ltb_spec k 15), (Z.leb_spec n 236); try reflexivity; lia.
Qed.

Definition nonnegX (X : list (bptr * Z)) : Prop := Forall (fun xb => 0 <= snd xb) X.

Lemma LRX_le_cntA X c : nonnegX X -> c < 12 -> LRX X c <= cntA X.
Proof.
  induction X as [|[p n] X IH]; intros HF Hc; [unfold LRX, zcount, zlen, cntA; cbn; lia|].
  unfold LRX in *. rewrite zcount_cons. rewrite LB_PTarget.cntA_cons. cbn [snd]. inversion HF; subst. cbn [snd] in *.
  specialize (IH ltac:(assumption) Hc).
  destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hb|Hs]; cbn [negb andb]; [destruct (n <=? TIER_A_MAX); lia|].
  destruct (Z.eqb_spec (size_to_class n) c) as [E|E]; [| destruct (n <=? TIER_A_MAX); lia].
  rewrite <- (class_tier n ltac:(lia)). rewrite E. destruct (Z.ltb_spec c 12); lia.
Qed.

Lemma LRX_le_cntB X c : nonnegX X -> 12 <= c -> LRX X c <= cntB X.
Proof.
  induction X as [|[p n] X IH]; intros HF Hc; [unfold LRX, zcount, zlen, cntB; cbn; lia|].
  unfold LRX in *. rewrite zcount_cons. rewrite LB_PTarget.cntB_cons. cbn [snd]. inversion HF; subst. cbn [snd] in *.
  specialize (IH ltac:(assumption) Hc).
  destruct (Z.leb_spec MMAP_THRESHOLD n) as [Hb|Hs]; cbn [negb andb]; [destruct (TIER_A_MAX <? n); lia|].
  destruct (Z.eqb_spec (size_to_class n) c) as [E|E]; [| destruct (TIER_A_MAX <? n); lia].
  pose proof (class_tier n ltac:(lia)) as HT. rewrite E in HT.
  destruct (Z.ltb_spec c 12); [lia|]. destruct (Z.leb_spec n TIER_A_MAX); [discriminate|].
  destruct (Z.ltb_spec TIER_A_MAX n); lia.
Qed.

Lemma n63X_le_cntB X : n63X X <= cntB X.
Proof.
  induction X as [|[p n] X IH]; [unfold n63X, zcount, zlen, cntB; cbn; lia|].
  unfold n63X in *. rewrite zcount_cons, LB_PTarget.cntB_cons. cbn [snd].
  destruct (Z.leb_spec MMAP_THRESHOLD n); destruct (Z.ltb_spec TIER_A_MAX n); unfold MMAP_THRESHOLD, TIER_A_MAX in *; lia.
Qed.

Lemma R63X_le_bigsum X : nonnegX X -> R63X X <= bigsum X.
Proof.
  induction X as [|[p n] X IH]; intros HF; [unfold R63X, zsum, bigsum; cbn; lia|].
  rewrite R63X_cons, LB_PTarget.bigsum_cons. cbn [snd]. inversion HF; subst. cbn [snd] in *. specialize (IH ltac:(assumption)).
  pose proof (bigb_le n ltac:(lia)). unfold bigb in *.
  destruct (Z.leb_spec MMAP_THRESHOLD n); destruct (Z.ltb_spec TIER_A_MAX n); unfold MMAP_THRESHOLD, TIER_A_MAX, IB, UNIT in *; lia.
Qed.

Lemma cnt_app (L A : list (bptr * Z)) : cntA (L ++ A) = cntA L + cntA A /\ cntB (L ++ A) = cntB L + cntB A /\ bigsum (L ++ A) = bigsum L + bigsum A.
Proof.
  induction L as [|x L (IH1 & IH2 & IH3)]; [unfold cntA, cntB, bigsum; cbn; lia|].
  cbn [app]. rewrite !LB_PTarget.cntA_cons, !LB_PTarget.cntB_cons, !LB_PTarget.bigsum_cons. lia.
Qed.

Lemma cnt_amb (A : list (bptr * Z)) : smallX A ->
  cntA A <= zlen A /\ cntB A <= zlen A /\ bigsum A <= zlen A * (MAX_INPUT + 1 + 8192) /\ nonnegX A.
Proof.
  induction A as [|[p n] A IH]; intros SX; [unfold cntA, cntB, bigsum, zlen, nonnegX; cbn; repeat split; try lia; constructor|].
  inversion SX; subst. cbn [snd] in *. destruct (IH ltac:(assumption)) as (I1 & I2 & I3 & I4).
  rewrite LB_PTarget.cntA_cons, LB_PTarget.cntB_cons, LB_PTarget.bigsum_cons. cbn [snd]. unfold zlen in *. cbn [length]. rewrite Nat2Z.inj_succ.
  repeat split; [destruct (n <=? TIER_A_MAX); lia| destruct (TIER_A_MAX <? n); lia| destruct (TIER_A_MAX <? n); lia| constructor; [cbn [snd]; lia| exact I4]].
Qed.

(* [comment removed for export] *)
Lemma OK_gen : forall (L A : list (bptr * Z)) n, cinv L -> (length A <= 2)%nat -> smallX A -> 0 <= n ->
  (n <= TIER_A_MAX -> cntA L + zlen A < 8192) -> (TIER_A_MAX < n -> cntB L + zlen A < 64) ->
  bigsum L + (if TIER_A_MAX <? n then n + 8192 else 0) <= BIG_ROOM ->
  mal_okQ (L ++ A) n.
Proof.
  intros L A n (HA & HB & HS & HF) HlA SA Hn H1 H2 H3.
  destruct (cnt_amb A SA) as (A1 & A2 & A3 & A4). destruct (cnt_app L A) as (E1 & E2 & E3).
  assert (HzA : zlen A <= 2) by (unfold zlen; lia).
  assert (HFX : nonnegX (L ++ A)) by (apply Forall_app; split; assumption).
  split.
  - split.
    + intros Hs. destruct (Z.ltb_spec (size_to_class n) 12) as [Hc|Hc].
      * pose proof (LRX_le_cntA (L ++ A) _ HFX Hc). pose proof (class_tier n ltac:(lia)) as HT.
        destruct (Z.ltb_spec (size_to_class n) 12); [|lia]. symmetry in HT. apply Z.leb_le in HT. specialize (H1 HT).
        unfold Pstat. destruct (Z.ltb_spec (size_to_class n) 12); lia.
      * pose proof (LRX_le_cntB (L ++ A) _ HFX Hc). pose proof (class_tier n ltac:(lia)) as HT.
        destruct (Z.ltb_spec (size_to_class n) 12); [lia|]. symmetry in HT. apply Z.leb_gt in HT. specialize (H2 HT).
        unfold Pstat. destruct (Z.ltb_spec (size_to_class n) 12); lia.
    + intros Hb. pose proof (n63X_le_cntB (L ++ A)). assert (HT : TIER_A_MAX < n) by (unfold MMAP_THRESHOLD, TIER_A_MAX in *; lia).
      specialize (H2 HT). unfold Pstat. change (63 <? 12) with false. cbn iota. lia.
  - pose proof (R63X_le_bigsum (L ++ A) HFX). pose proof (bigb_le n Hn). pose proof PHI_Pstat_room.
    assert (bigb n <= (if TIER_A_MAX <? n then n + 8192 else 0)).
    { unfold bigb. destruct (Z.leb_spec MMAP_THRESHOLD n); destruct (Z.ltb_spec TIER_A_MAX n); unfold bigb, MMAP_THRESHOLD, TIER_A_MAX, IB, UNIT in *; try lia.
      pose proof (round_up_pg_spec (n + 4 + 16)) as [[_ Hr] _]. lia. }
    assert (HbA : bigsum A <= 2 * (MAX_INPUT + 1 + 8192)) by (unfold MAX_INPUT in *; nia).
    destruct (TIER_A_MAX <? n); lia.
Qed.

Lemma OK_cl : forall (L A : list (bptr * Z)) n, cinv L -> LB_PTarget.amb_ok A -> 0 <= n < SZ_MAX ->
  (n <= TIER_A_MAX -> cntA L < CAP_A) -> (TIER_A_MAX < n -> cntB L < CAP_B /\ bigsum L + n + 8192 <= BIG_ROOM) ->
  mal_okQ (L ++ A) n.
Proof.
  intros L A n HC [HlA SA] Hn H1 H2. assert (HzA : zlen A <= 2) by (unfold zlen; lia).
  apply OK_gen; try assumption; try lia.
  - intros H. specialize (H1 H). unfold CAP_A in *. lia.
  - intros H. destruct (H2 H) as [H3 _]. unfold CAP_B in *. lia.
  - destruct (Z.ltb_spec TIER_A_MAX n) as [H|H]; [pose proof (proj2 (H2 H)); lia| destruct HC as (_ & _ & HS & _); lia].
Qed.

Lemma OK_drv : forall (L A : list (bptr * Z)) n, cinv L -> (length A <= 1)%nat -> smallX A -> 0 <= n <= MAX_INPUT + 1 ->
  mal_okQ (L ++ A) n.
Proof.
  intros L A n HC HlA SA Hn. assert (HzA : zlen A <= 1) by (unfold zlen; lia).
  pose proof HC as (HA & HB & HS & HF).
  (* [comment removed for export] *)
  destruct (cnt_amb A SA) as (A1 & A2 & A3 & A4). destruct (cnt_app L A) as (E1 & E2 & E3).
  assert (HFX : nonnegX (L ++ A)) by (apply Forall_app; split; assumption).
  split.
  - split.
    + intros Hs. destruct (Z.ltb_spec (size_to_class n) 12) as [Hc|Hc].
      * pose proof (LRX_le_cntA (L ++ A) _ HFX Hc). unfold Pstat, CAP_A in *. destruct (Z.ltb_spec (size_to_class n) 12); lia.
      * pose proof (LRX_le_cntB (L ++ A) _ HFX Hc). unfold Pstat, CAP_B in *. destruct (Z.ltb_spec (size_to_class n) 12); lia.
    + intros Hb. pose proof (n63X_le_cntB (L ++ A)). unfold Pstat, CAP_B in *. change (63 <? 12) with false. cbn iota. lia.
  - pose proof (R63X_le_bigsum (L ++ A) HFX). pose proof (bigb_le n ltac:(lia)). pose proof PHI_Pstat_room.
    assert (HbA : bigsum A <= 1 * (MAX_INPUT + 1 + 8192)) by (unfold MAX_INPUT in *; nia).
    unfold IB, UNIT in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Notation QIX := (fun X => QI X Pstat).

Lemma QI_minv' : forall X s mo, QI X Pstat s mo -> minv mo /\ m_halted mo = None.
Proof. intros X s mo H. exact (QI_minv _ _ _ _ H). Qed.
Lemma QI_fds' : forall X s mo mo', QI X Pstat s mo -> m_vmmaps mo' = m_vmmaps mo -> minv mo' -> m_halted mo' = None -> QI X Pstat s mo'.
Proof. intros X s mo mo' H. exact (QI_fds _ _ _ _ _ H). Qed.
Lemma QI_live' : forall X s mo, QI X Pstat s mo -> live mo <= LBUDGET.
Proof. intros X s mo H. exact (QI_live _ _ _ _ H). Qed.

Lemma writev_LQ X fd bufs (dec : resp -> option Z) : mspecL LBUDGET (QI X Pstat) (msys (NWritev fd bufs) dec) (fun _ => QI X Pstat).
Proof. apply (writev_L LBUDGET (QI X Pstat) (QI_live' X)). Qed.
Lemma ioctl_LQ X fd req : mspecL LBUDGET (QI X Pstat) (msys (NIoctl fd req) dec_ioctl) (fun _ => QI X Pstat).
Proof. apply (ioctl_L LBUDGET (QI X Pstat) (QI_live' X)). Qed.
Lemma QI_set_so' X : forall s mo v, QI X Pstat s mo -> QI X Pstat (set_so_ps v s) mo.
Proof. intros s mo v H. apply QI_set_so. exact H. Qed.

Lemma err_LQ : forall X ps, mspecL LBUDGET (QI X Pstat) (stderr_fprintf ps) (fun _ => QI X Pstat).
Proof. intros X ps. apply (stderr_fprintf_L LBUDGET (QI X Pstat) (writev_LQ X)). Qed.
Lemma out_LQ : forall X ps, mspecL LBUDGET (QI X Pstat) (stdout_vprintf ps_so set_so_ps ps) (fun _ => QI X Pstat).
Proof. intros X ps. apply (stdout_vprintf_L ps_so set_so_ps LBUDGET (QI X Pstat) (QI_set_so' X) (writev_LQ X) (ioctl_LQ X)). Qed.
Lemma diag_LQ : forall X d, mspecL LBUDGET (QI X Pstat) (io_diag io d) (fun _ => QI X Pstat).
Proof. intros X d. unfold io, io_S. cbn [io_diag]. apply (s_diag_L LBUDGET (QI X Pstat) (writev_LQ X)). Qed.
Lemma exitio_LQ : forall X, mspecL LBUDGET (QI X Pstat) (io_exit io) (fun _ => QI X Pstat).
Proof. intros X. unfold io, io_S. cbn [io_exit]. apply (stdout_exit_flush_L ps_so set_so_ps LBUDGET (QI X Pstat) (QI_set_so' X) (writev_LQ X) (ioctl_LQ X)). Qed.

Lemma raw_malloc_LQ' : forall X n, 0 <= n ->
  mspecL LBUDGET (fun s mo => QI X Pstat s mo /\ mal_okQ X n) (raw_malloc n)
         (fun r s mo => match r with Some p => QI ((p, n) :: X) Pstat s mo /\ n < 2^63 | None => QI X Pstat s mo end).
Proof. intros X n Hn. exact (raw_malloc_LQ X Pstat n Hn). Qed.
Lemma raw_free_LQ' : forall X p n, mspecL LBUDGET (QI ((p, n) :: X) Pstat) (raw_free p) (fun _ => QI X Pstat).
Proof. intros X p n. exact (raw_free_LQ X Pstat p n). Qed.
Lemma QI_perm' : forall X Y s mo, Permutation X Y -> QI X Pstat s mo -> QI Y Pstat s mo.
Proof. intros X Y s mo HP. apply QI_perm. exact HP. Qed.

Lemma run_LQ : forall b cap cfg payload, 65536 <= cap <= MAX_INPUT -> zlength payload <= MAX_INPUT ->
  mspecL LBUDGET (QI [(b, cap)] Pstat) (run cfg payload) (fun _ s mo => exists Y, QI (Y ++ [(b, cap)]) Pstat s mo).
Proof.
  intros b cap cfg payload Hcap Hpl. unfold run.
  apply (target_run_L LBUDGET raw_malloc raw_free ps_so set_so_ps QIX mal_okQ
           raw_malloc_LQ' raw_free_LQ' QI_perm' out_LQ OK_cl OK_drv [(b, cap)] cfg payload); [cbn; lia| | exact Hpl].
  constructor; [cbn [snd]; lia| constructor].
Qed.

Lemma alloc_init_LQ : forall X bm, mspecL LBUDGET (QI X Pstat) (alloc_init bm) (fun _ => QI X Pstat).
Proof. intros X bm. unfold alloc_init. apply mspecL_ret. auto. Qed.
Lemma alloc_count_LQ : forall X, mspecL LBUDGET (QI X Pstat) alloc_count (fun _ => QI X Pstat).
Proof. intros X. unfold alloc_count. apply mspecL_ret. auto. Qed.

(* [comment removed for export] *)
Lemma prog_with_L : forall rstage argv,
  Forall (fun a => zlength a < 2^32) argv -> Forall path_okZ (tl argv) ->
  mspecL LBUDGET (QI [] Pstat) (prog_with rstage argv) (fun _ _ _ => False).
Proof.
  intros rstage argv Hargv Hpaths. unfold prog_with.
  eapply mspecL_seq; [apply (startup_L LBUDGET (QI [] Pstat)); [apply QI_minv'| apply QI_fds'| apply QI_live']|]. intros u.
  eapply mspecL_bind.
  - apply (main_model_L LBUDGET io raw_malloc raw_free rstage alloc_init run alloc_count QIX mal_okQ
             raw_malloc_LQ' raw_free_LQ' QI_perm' diag_LQ alloc_init_LQ alloc_count_LQ run_LQ QI_minv' QI_fds' QI_live'
             OK_first OK_grow argv Hargv Hpaths).
  - intros code. eapply mspecL_pre; [eapply (exit_model_L LBUDGET io QIX); apply exitio_LQ|]. intros s mo H. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
Theorem prog_noerr_gen : forall segs rstage pc ph lim en inp,
  segs_low segs -> KLIM + SMALLREQ <= lim ->
  valid_entry (mkImage segs pc ph) en inp -> TopLevel.valid_input_w inp ->
  bv_unsigned (en_sp en) - stack_max_size = alloc_ceiling ->
  tsafe nstep node_noerr (prog segs rstage (in_argv inp))
        (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).
Proof.
  intros segs rstage pc ph lim [sp brk0 mbase] inp Hsegs Hlim Hve Hvi Htop.
  destruct Hve as (_ & Hbrk & _). destruct Hvi as (Hargv & _).
  unfold prog. cbn [en_brk en_mmap_base en_sp] in *.
  apply (mspecL_program_noerr LBUDGET (QI [] Pstat) (prog_with rstage (argv_Z (in_argv inp))) (fun _ _ _ => False)).
  - apply prog_with_L; [apply argv_Z_short| apply argv_Z_paths]; exact Hargv.
  - unfold reservedZ. unfold valid_brk in Hbrk. cbn [img_segments] in Hbrk.
    apply QI_init; [exact Hbrk| exact (proj1 Hsegs)| exact (ceil_low segs Hsegs)| exact Htop| exact Pstat_nonneg| | exact (proj2 Hsegs)| exact Hlim].
    pose proof PHI_Pstat. unfold MAX_INPUT, IB, UNIT in *. lia.
  - intros [].
Qed.

End WithCeiling.

(* [comment removed for export] *)
Definition noerr_stmt (segs : list Segment) (rstage : Z) (pc : N) (ph : PhdrInfo) (lim : Z) : Prop :=
  forall en inp, valid_entry (mkImage segs pc ph) en inp -> TopLevel.valid_input_w inp ->
    tsafe nstep node_noerr (@Prog.prog (ceiling_of_sp (bv_unsigned (en_sp en))) segs rstage (in_argv inp))
          (init_model (segments_reserved segs) (en_brk en) (en_mmap_base en) (en_sp en) lim inp).

Theorem prog_noerr : forall segs rstage pc ph lim,
  segs_low segs -> KLIM + SMALLREQ <= lim ->
  noerr_stmt segs rstage pc ph lim.
Proof.
  intros segs rstage pc ph lim Hsegs Hlim en inp Hve Hvi.
  apply (@prog_noerr_gen (ceiling_of_sp (bv_unsigned (en_sp en))) segs rstage pc ph lim en inp Hsegs Hlim Hve Hvi).
  rewrite <- (TopLevel.mo0_alloc_top_ceiling segs pc ph lim en inp (TopLevel.valid_input_w_va_size _ Hvi) Hve). reflexivity.
Qed.
