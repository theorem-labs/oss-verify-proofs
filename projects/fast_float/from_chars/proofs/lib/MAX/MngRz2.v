(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec CatSim ShapeSet RealizesCfg AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PlacementCount.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require Import MallocModel MallocInv MallocLemmasBase MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngWk MngRz.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU.
Import OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngWk OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngRz OSSVerify.Proofs.fast_float.from_chars.lib.MAX.MngU.MngLedger.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngU.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kf_regions (x : kf) : list region := fst (fst x).
Definition kf_brk (x : kf) : brkst := snd (fst x).
Definition kf_areas (x : kf) : list sptr := snd x.

(* [comment removed for export] *)
Definition footprint_kf (x : kf) : list (loc * Z) :=
  (LCtx 0, CTX_SIZE)
  :: map (fun a => (LMem a, PGSZ)) (kf_areas x)
  ++ flat_map (fun k => match nth_error (kf_regions x) k with
                        | Some rg => match rg_kind rg with
                                     | RkMap => if rg_live rg then [(LMem (SP k 0), rg_len rg)] else []
                                     | _ => []
                                     end
                        | None => []
                        end) (seq 0 (length (kf_regions x))).

Lemma footprint_kf_of : forall s, footprint_kf (kf_of s) = footprint s.
Proof. intros s. reflexivity. Qed.

Definition live_kind (rs : list region) (r : nat) (k : rkind) (rg : region) : Prop :=
  nth_error rs r = Some rg /\ rg_kind rg = k /\ rg_live rg = true.

Definition covered (md : Model) (a k : Z) : Prop :=
  exists e, In e (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) /\ ecov e a k.
Definition rcovered (md : Model) (a k : Z) : Prop :=
  exists e, In e (vm_reserved (m_vmmaps md)) /\ ecov e a k.

(* [comment removed for export] *)
Definition na_byte (L : layout) (x : kf) (a : Z) : Prop :=
  ((exists r rg, nth_error (kf_regions x) r = Some rg /\ rg_kind rg = RkBrk /\ rg_live rg = true /\ ly_reg L r = ly_brk0 L) /\
     ly_brk0 L <= a < ly_brk0 L + PGSZ) \/
  (exists r rg o, nth_error (kf_regions x) r = Some rg /\ rg_kind rg = RkMetaRes /\ rg_live rg = true /\
     0 <= o /\ o + PGSZ <= rg_len rg /\ o mod PGSZ = 0 /\ ~ In o (rg_rw rg) /\ ly_reg L r + o <= a < ly_reg L r + o + PGSZ).

(* [comment removed for export] *)
Definition rtot (rs : list region) : Z :=
  fold_right (fun rg acc => match rg_kind rg with RkMetaRes => rg_len rg + acc | _ => acc end) 0 rs.
Definition ropen (rs : list region) : Z :=
  fold_right (fun rg acc => match rg_kind rg with RkMetaRes => Z.of_nat (length (rg_rw rg)) + acc | _ => acc end) 0 rs.
Definition rcnt (rs : list region) : Z :=
  fold_right (fun rg acc => match rg_kind rg with RkMetaRes => 1 + acc | _ => acc end) 0 rs.

(* [comment removed for export] *)
Record LINK (HTOP : Z) (FORB : list (Z * Z)) (L : layout) (x : kf) (md : Model) : Prop := {
  lk_halt : m_halted md = None ;
  lk_lazy : m_vm_lazy md = [] ;
  lk_top : alloc_top (m_vmmaps md) <= HTOP ;
  lk_mdisj : pairwise edisj (vm_maps (m_vmmaps md)) ;
  lk_mpos : forall e, In e (vm_maps (m_vmmaps md)) -> 0 < bv_unsigned (snd e) ;
  lk_mtop : forall e, In e (vm_maps (m_vmmaps md)) -> bv_unsigned (fst e) + bv_unsigned (snd e) <= alloc_top (m_vmmaps md) ;
  lk_forb : Forall (fun r => rcovered md (fst r) (snd r)) FORB ;
  lk_ctx : rcovered md (ly_ctx L) CTX_SIZE ;
  (* [comment removed for export] *)
  lk_rgeo : forall r rg, nth_error (kf_regions x) r = Some rg -> rg_live rg = true ->
      PGSZ <= ly_reg L r /\ ly_reg L r mod PGSZ = 0 /\ 0 < rg_len rg /\ rg_len rg mod PGSZ = 0 /\ ly_reg L r + rg_len rg <= alloc_top (m_vmmaps md) ;
  lk_rdisj : forall r1 r2 rg1 rg2, r1 <> r2 -> nth_error (kf_regions x) r1 = Some rg1 -> nth_error (kf_regions x) r2 = Some rg2 ->
      rg_live rg1 = true -> rg_live rg2 = true -> ranges_disjoint (ly_reg L r1, rg_len rg1) (ly_reg L r2, rg_len rg2) ;
  lk_rcov : forall r rg o, nth_error (kf_regions x) r = Some rg -> rg_live rg = true -> 0 <= o -> o + PGSZ <= rg_len rg ->
      o mod PGSZ = 0 -> exists e, In e (vm_maps (m_vmmaps md)) /\ ecov e (ly_reg L r + o) PGSZ ;
  (* [comment removed for export] *)
  lk_maps : forall r rg, live_kind (kf_regions x) r RkMap rg ->
      map_has (vm_maps (m_vmmaps md)) (w64 (ly_reg L r)) (w64 (rg_len rg)) = true ;
  lk_resv : forall r rg, live_kind (kf_regions x) r RkMetaRes rg ->
      forall o, 0 <= o -> o + PGSZ <= rg_len rg -> o mod PGSZ = 0 -> ~ In o (rg_rw rg) ->
         map_contains (vm_noaccess (m_vmmaps md)) (w64 (ly_reg L r + o)) (w64 PGSZ) = true ;
  (* [comment removed for export] *)
  lk_areas : forall a, In a (kf_areas x) -> exists rg, nth_error (kf_regions x) (prid a) = Some rg /\ rg_live rg = true /\
      rg_kind rg <> RkMap /\ 0 <= poff a /\ poff a + PGSZ <= rg_len rg /\ poff a mod PGSZ = 0 ;
  lk_brk :
      match kf_brk x with
      | BrkNever => bv_unsigned (vm_brk (m_vmmaps md)) = ly_brk0 L /\
                    (forall r rg, ~ live_kind (kf_regions x) r RkBrk rg)
      | BrkCur r p => nth_error (kf_regions x) r = Some (mkRegion RkBrk (PGSZ * p) [] true) /\ 2 <= p /\
                      ly_reg L r = ly_brk0 L /\ bv_unsigned (vm_brk (m_vmmaps md)) = ly_brk0 L + PGSZ * p /\
                      (Forall (fun a : sptr => prid a <> r) (kf_areas x) ->
                         p = 2 /\ region_free (vm_reserved (m_vmmaps md)) (w64 (ly_brk0 L)) (w64 PGSZ) = true)
      | BrkDead => True
      end ;
  lk_brk0 : PGSZ <= ly_brk0 L /\ ly_brk0 L mod PGSZ = 0 /\ bv_unsigned (min_brk (m_vmmaps md)) <= ly_brk0 L /\ ly_brk0 L <= HTOP ;
  (* [comment removed for export] *)
  lk_na : forall a, MngU.inC (vm_noaccess (m_vmmaps md)) a = true -> na_byte L x a ;
  (* [comment removed for export] *)
  lk_rw : forall r rg, live_kind (kf_regions x) r RkMetaRes rg ->
      List.NoDup (rg_rw rg) /\ forall o, In o (rg_rw rg) -> o mod PGSZ = 0 /\ PGSZ <= o /\ o + PGSZ <= rg_len rg ;
  lk_k0 : forall r rg, nth_error (kf_regions x) r = Some rg -> rg_kind rg = RkMetaRes -> rg_live rg = true ;
  (* [comment removed for export] *)
  lk_k1 : rtot (kf_regions x) = 2 * PGSZ * (2 ^ rcnt (kf_regions x) - 1) ;
  lk_k2 : rtot (kf_regions x) <= 2 * PGSZ * (ropen (kf_regions x) + rcnt (kf_regions x)) ;
  (* [comment removed for export] *)
  lk_atop : 2 ^ 47 - 2 ^ 32 <= alloc_top (m_vmmaps md) ;
  lk_lim : 2 ^ 31 <= vm_limit (m_vmmaps md) ;
  lk_rsz : PlacementCount.ledger_size (vm_reserved (m_vmmaps md)) <= 2 ^ 32
}.

(* [comment removed for export] *)
Lemma rtot_app : forall l1 l2, rtot (l1 ++ l2) = rtot l1 + rtot l2.
Proof. intros l1 l2. unfold rtot. induction l1 as [|y l1 IH]; cbn [app fold_right]; [lia|]. rewrite IH. destruct (rg_kind y); lia. Qed.
Lemma ropen_app : forall l1 l2, ropen (l1 ++ l2) = ropen l1 + ropen l2.
Proof. intros l1 l2. unfold ropen. induction l1 as [|y l1 IH]; cbn [app fold_right]; [lia|]. rewrite IH. destruct (rg_kind y); lia. Qed.
Lemma rcnt_app : forall l1 l2, rcnt (l1 ++ l2) = rcnt l1 + rcnt l2.
Proof. intros l1 l2. unfold rcnt. induction l1 as [|y l1 IH]; cbn [app fold_right]; [lia|]. rewrite IH. destruct (rg_kind y); lia. Qed.

Lemma rsv_lupd : forall rs r v old, nth_error rs r = Some old ->
  rtot (lupd rs r v) = rtot rs - rtot [old] + rtot [v] /\ ropen (lupd rs r v) = ropen rs - ropen [old] + ropen [v] /\
  rcnt (lupd rs r v) = rcnt rs - rcnt [old] + rcnt [v].
Proof.
  induction rs as [|y rs IH]; intros [|r] v old E; cbn in E; try discriminate E.
  - injection E as ->. unfold rtot, ropen, rcnt. cbn [lupd fold_right]. destruct (rg_kind old), (rg_kind v); lia.
  - destruct (IH r v old E) as (E1 & E2 & E3). cbn [lupd]. unfold rtot, ropen, rcnt in *. cbn [fold_right] in *.
    rewrite E1, E2, E3. destruct (rg_kind y); lia.
Qed.

Lemma rsv_other : forall rg, rg_kind rg <> RkMetaRes -> rtot [rg] = 0 /\ ropen [rg] = 0 /\ rcnt [rg] = 0.
Proof. intros rg H. revert H. unfold rtot, ropen, rcnt. cbn [fold_right]. destruct (rg_kind rg); intros H; [lia | exfalso; exact (H eq_refl) | lia]. Qed.

Lemma rsv_meta : forall len rw lv, rtot [mkRegion RkMetaRes len rw lv] = len /\ ropen [mkRegion RkMetaRes len rw lv] = Z.of_nat (length rw) /\
  rcnt [mkRegion RkMetaRes len rw lv] = 1.
Proof. intros. unfold rtot, ropen, rcnt. cbn. lia. Qed.

Lemma rsv_meta' : forall rg, rg_kind rg = RkMetaRes -> rtot [rg] = rg_len rg /\ ropen [rg] = Z.of_nat (length (rg_rw rg)) /\ rcnt [rg] = 1.
Proof. intros rg H. unfold rtot, ropen, rcnt. cbn [fold_right]. rewrite H. lia. Qed.

Lemma NoDup_snoc : forall {X} (l : list X) x, List.NoDup l -> ~ In x l -> List.NoDup (l ++ [x]).
Proof.
  intros X l. induction l as [|y l IH]; intros x H Hn; cbn [app].
  { apply NoDup_cons; [intros Hi; exact Hi | apply NoDup_nil]. }
  inversion H as [|y' l' Hy Hl]. subst. constructor.
  - intros Hi. apply in_app_iff in Hi as [Hi|[E|[]]]; [exact (Hy Hi) | apply Hn; left; symmetry; exact E].
  - apply IH; [exact Hl|]. intros Hi. apply Hn. right. exact Hi.
Qed.

Lemma msteps_isteps : forall segs a b, CatSim.msteps segs a b -> isteps segs a b.
Proof.
  intros segs a b H. induction H as [ms | ms ms1 ms2 Hsvc Hst Hrest IH].
  - apply ist_refl.
  - eapply ist_step; eassumption.
Qed.

Lemma u64_lt : forall a, 0 <= a <= 2 ^ 47 -> 0 <= a < 2 ^ 64.
Proof. intros a Ha. lia. Qed.

Lemma w64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> w64 a = w64 b -> a = b.
Proof. intros a b Ha Hb E. rewrite <- (u_w64 a Ha), <- (u_w64 b Hb), E. reflexivity. Qed.

Lemma ecov_w64 : forall a n x k, 0 <= a < 2 ^ 64 -> 0 <= n < 2 ^ 64 -> a <= x -> x + k <= a + n -> ecov (w64 a, w64 n) x k.
Proof. intros a n x k Ha Hn H1 H2. unfold ecov. cbn [fst snd]. rewrite !u_w64 by assumption. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Budget.
Variable CH : kreq -> Z.
(* [comment removed for export] *)
Fixpoint rb {A : Type} (B : Z) (t : itree astate A) {struct t} : Prop :=
  match t with
  | IAsk q _ k => CH q <= B /\ forall z, rb (B - CH q) (k z)
  | _ => True
  end.
End Budget.

Section TreeRz.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Hypothesis Hoff : sc_alloc cfg = false.
Variable FORB : list (Z * Z).
Variable HTOP : Z.
Hypothesis HTOPB : HTOP <= 2 ^ 47.
Context {fx : FPState}.
Variable rom : word -> option byte.
Variable CH : kreq -> Z.
Variable BI : kf -> Model -> Z -> Prop.

(* [comment removed for export] *)
Hypothesis ob_junk : forall x md B b, BI x md B -> CH (KJunk b) <= B -> BI x md (B - CH (KJunk b)).
Hypothesis ob_query : forall L x md B, LINK HTOP FORB L x md -> BI x md B -> CH KBrkQuery <= B ->
  BI (kstep x KBrkQuery 1) md (B - CH KBrkQuery).
Hypothesis ob_brk_refuse : forall L x md B n, LINK HTOP FORB L x md -> BI x md B -> CH (KBrkGrow n) <= B ->
  BI (kstep x (KBrkGrow n) 0) md (B - CH (KBrkGrow n)).
Hypothesis ob_brk_grant : forall L x md B n cur, LINK HTOP FORB L x md -> BI x md B -> CH (KBrkGrow n) <= B ->
  vm_brk (m_vmmaps md) = w64 cur -> PGSZ <= cur -> cur mod PGSZ = 0 -> 1 <= n -> cur + PGSZ * n + PGSZ < 2 ^ 64 ->
  BI (kstep x (KBrkGrow n) 1) (with_brk_next md (w64 (cur + PGSZ * n)) (w64 (cur + PGSZ * n))) (B - CH (KBrkGrow n)).
Hypothesis ob_guard : forall L x md B a, LINK HTOP FORB L x md -> BI x md B -> CH KGuard <= B -> 0 <= a -> a + PGSZ < 2 ^ 64 ->
  BI (kstep x KGuard 1) (fixed_na_next (w64 50) (w64 a) (w64 PGSZ) md) (B - CH KGuard).
Hypothesis ob_rw : forall L x md B len, LINK HTOP FORB L x md -> BI x md B -> CH (KMmapRW len) <= B -> 1 <= len < 2 ^ 63 ->
  exists a, fresh_rw_guard (w64 34) md (page_round len) a.
Hypothesis ob_rw' : forall L x md B len a, LINK HTOP FORB L x md -> BI x md B -> CH (KMmapRW len) <= B -> 1 <= len < 2 ^ 63 ->
  fresh_rw_guard (w64 34) md (page_round len) a ->
  BI (kstep x (KMmapRW len) 1) (fresh_rw_next (w64 34) a (w64 (page_round len)) md) (B - CH (KMmapRW len)).
Hypothesis ob_na : forall L x md B s len, LINK HTOP FORB L x md -> BI x md B -> CH (KMmapNone len) <= B ->
  kf_of s = x -> req_ok s (KMmapNone len) -> exists a, place_ok md (page_round len) a.
Hypothesis ob_na' : forall L x md B len a, LINK HTOP FORB L x md -> BI x md B -> CH (KMmapNone len) <= B -> 1 <= len < 2 ^ 63 ->
  place_ok md (page_round len) a ->
  BI (kstep x (KMmapNone len) 1) (fresh_na_next (w64 34) a (w64 (page_round len)) md) (B - CH (KMmapNone len)).
Hypothesis ob_pr : forall L x md B p, LINK HTOP FORB L x md -> BI x md B -> CH (KMprotect p) <= B ->
  0 <= loc_addr L (LMem p) -> loc_addr L (LMem p) + PGSZ < 2 ^ 64 ->
  mprotect_budget_ok md (w64 (loc_addr L (LMem p))) (w64 PGSZ) = true.
Hypothesis ob_pr' : forall L x md B p, LINK HTOP FORB L x md -> BI x md B -> CH (KMprotect p) <= B ->
  0 <= loc_addr L (LMem p) -> loc_addr L (LMem p) + PGSZ < 2 ^ 64 ->
  BI (kstep x (KMprotect p) 1) (mprotect_model_next md (w64 (loc_addr L (LMem p))) (w64 PGSZ)) (B - CH (KMprotect p)).
Hypothesis ob_munmap : forall L x md B r len rg, LINK HTOP FORB L x md -> BI x md B -> CH (KMunmap r len) <= B ->
  nth_error (kf_regions x) r = Some rg -> rg_kind rg = RkMap -> rg_live rg = true -> rg_len rg = page_round len ->
  BI (kstep x (KMunmap r len) 1) (munmap_next (w64 (ly_reg L r)) (w64 (page_round len)) md) (B - CH (KMunmap r len)).

Definition CONT (K : TSet) (L : layout) (x : kf) (md : Model) (B : Z) (regs : bvmap 5 word) (pc : word) (m : word -> option byte) : Prop :=
  LINK HTOP FORB L x md -> BI x md B -> realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.

(* [comment removed for export] *)
Definition node_ok (q : kreq) : Prop :=
  forall L x md B s regs pc m K,
    at_ecall segs L s q regs pc -> kf_of s = x -> req_ok s q -> LINK HTOP FORB L x md -> BI x md B -> CH q <= B ->
    (forall eff ans L' md', koutcome FORB HTOP L s q eff ans L' -> vm_only md md' ->
       CONT K L' (kstep x q ans) md' (B - CH q) (regupd regs 10 (eff_ret eff)) (bv_add pc (w64 4)) (mem_after m eff)) ->
    realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.

#[using="Type"] Lemma kstep_query : forall x z, kstep x KBrkQuery z = x.
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] z. reflexivity. Qed.

#[using="Type"] Lemma w64_of_u : forall (w : word) a, bv_unsigned w = a -> w = w64 a.
Proof. LiaFast.lf_pins LiaFast.u0. intros w a E. apply bv_eq. rewrite E. unfold w64. rewrite Z_to_bv_unsigned. unfold bv_wrap. subst a. symmetry. apply Z.mod_small. apply u_range. Qed.

#[using="ob_query"] Lemma case_query : node_ok KBrkQuery.
Proof. LiaFast.lf_pins (fun (ob_query : LiaFast.U) => LiaFast.u0).
  intros L x md B s regs pc m K Hec Hx Hrq HL HB Hc Hcont.
  destruct Hrq as (Hbrk & _).
  assert (HV : vm_brk (m_vmmaps md) = w64 (ly_brk0 L)).
  { pose proof (lk_brk _ _ _ _ _ HL) as Hb. subst x. unfold kf_brk in Hb. cbn [kf_of fst snd] in Hb. rewrite Hbrk in Hb.
    destruct Hb as (Hb & _). exact (w64_of_u _ _ Hb). }
  apply (rz_brk_query segs cfg rom L s regs pc m md K Hec (lk_halt _ _ _ _ _ HL) (lk_lazy _ _ _ _ _ HL)).
  rewrite HV.
  apply (Hcont (mkEffect (w64 (ly_brk0 L)) [] []) 1 L md (o_brk_query FORB HTOP L s) (vm_only_refl md)).
  - rewrite kstep_query. exact HL.
  - exact (ob_query L x md B HL HB Hc).
Qed.

(* [comment removed for export] *)

#[using="Type"] Lemma region_free_app : forall l1 l2 lo n, region_free (l1 ++ l2) lo n = true -> region_free l1 lo n = true /\ region_free l2 lo n = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction l1 as [|[a sz] t IH]; intros l2 lo n H; cbn in *; [split; [reflexivity | exact H]|].
  apply andb_true_iff in H as [H1 H2]. destruct (IH l2 lo n H2) as [A B]. split; [apply andb_true_iff; split; assumption | exact B].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma pages_disj : forall A N B len, 0 < N -> 0 < len -> B mod PGSZ = 0 -> len mod PGSZ = 0 ->
  (forall o, 0 <= o -> o + PGSZ <= len -> o mod PGSZ = 0 -> ranges_disjoint (A, N) (B + o, PGSZ)) ->
  ranges_disjoint (A, N) (B, len).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros A N B len HN Hl HB Hlen H. unfold ranges_disjoint in *. cbn [fst snd] in *.
  destruct (Z_le_gt_dec (A + N) B) as [C|C]; [left; exact C|]. destruct (Z_le_gt_dec (B + len) A) as [C'|C']; [right; exact C'|].
  exfalso.
  assert (Hy : exists y, B <= y < B + len /\ A <= y < A + N).
  { clear H. destruct (Z_le_gt_dec A B); [exists B | exists A]; split; lia. }
  destruct Hy as (y & Ey & Ey'). unfold PGSZ in *.
  set (o := (y - B) / 4096 * 4096).
  assert (Q := Z.div_mod (y - B) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (y - B) 4096 ltac:(lia)) as Q2.
  assert (Ho1 : 0 <= o) by (unfold o; apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
  assert (Ho2 : o + 4096 <= len).
  { unfold o. assert (Hlq := Z.div_mod len 4096 ltac:(lia)).
    assert ((y - B) / 4096 < len / 4096) by (apply Z.div_lt_upper_bound; clear - Ey Hlen Hlq; lia). clear - H0 Hlen Hlq; lia. }
  assert (Ho3 : o mod 4096 = 0) by (unfold o; apply Z.mod_mul; lia).
  destruct (H o Ho1 Ho2 Ho3) as [D|D]; unfold o in D; clear - D Q Q2 Ey Ey'; lia.
Qed.

#[using="Type"] Lemma rd_sym : forall a b, ranges_disjoint a b -> ranges_disjoint b a.
Proof. LiaFast.lf_pins LiaFast.u0. intros [a1 a2] [b1 b2] H. unfold ranges_disjoint in *. cbn in *. lia. Qed.

#[using="Type"] Lemma covered_rf : forall md lo n a k, region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) lo n = true ->
  covered md a k -> ranges_disjoint (bv_unsigned lo, bv_unsigned n) (a, k).
Proof. LiaFast.lf_pins LiaFast.u0. intros md lo n a k Hf (e & He & Hc). exact (rf_disj _ lo n e a k Hf He Hc). Qed.

#[using="Type"] Lemma rcovered_covered : forall md a k, rcovered md a k -> covered md a k.
Proof. LiaFast.lf_pins LiaFast.u0. intros md a k (e & He & Hc). exists e. split; [apply in_or_app; left; exact He | exact Hc]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma fp_covered : forall L x md, LINK HTOP FORB L x md -> forall rg, In rg (footprint_kf x) -> covered md (loc_addr L (fst rg)) (snd rg).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md HL rg Hin. unfold footprint_kf in Hin. destruct Hin as [<-|Hin].
  - apply rcovered_covered. cbn [fst snd loc_addr]. rewrite Z.add_0_r. exact (lk_ctx _ _ _ _ _ HL).
  - apply in_app_iff in Hin as [Hin|Hin].
    + apply in_map_iff in Hin as (a & <- & Ha). destruct (lk_areas _ _ _ _ _ HL a Ha) as (rga & H1 & H2 & _ & H4 & H5 & H6).
      destruct (lk_rcov _ _ _ _ _ HL (prid a) rga (poff a) H1 H2 H4 H5 H6) as (e & He & Hc).
      exists e. split; [apply in_or_app; right; exact He|]. destruct a as [r o]. cbn [fst snd loc_addr prid poff] in *. exact Hc.
    + apply in_flat_map in Hin as (k & Hk & Hin). destruct (nth_error (kf_regions x) k) as [rgk|] eqn:Ek; [|destruct Hin].
      destruct (rg_kind rgk) eqn:Kk; try destruct Hin. destruct (rg_live rgk) eqn:Lk; [|destruct Hin].
      destruct Hin as [<-|[]]. pose proof (lk_maps _ _ _ _ _ HL k rgk (conj Ek (conj Kk Lk))) as Hh. apply map_has_In in Hh.
      destruct (lk_rgeo _ _ _ _ _ HL k rgk Ek Lk) as (G1 & G2 & G3 & G4 & G5). pose proof (alloc_top_lt (m_vmmaps md)) as AT.
      exists (w64 (ly_reg L k), w64 (rg_len rgk)). split; [apply in_or_app; right; exact Hh|]. cbn [fst snd loc_addr].
      apply ecov_w64; clear - G1 G3 G5 AT; unfold two_pow_64, PGSZ in *; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma page_of_point : forall base len y, 0 < len -> len mod PGSZ = 0 -> base <= y < base + len ->
  exists o, 0 <= o /\ o + PGSZ <= len /\ o mod PGSZ = 0 /\ base + o <= y < base + o + PGSZ.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros base len y H1 H2 H3. exists (PGSZ * ((y - base) / PGSZ)).
  pose proof (Z.mul_div_le (y - base) PGSZ ltac:(unfold PGSZ; lia)) as Q1.
  pose proof (Z.mod_pos_bound (y - base) PGSZ ltac:(unfold PGSZ; lia)) as Q2.
  pose proof (Z.div_mod (y - base) PGSZ ltac:(unfold PGSZ; lia)) as Q3.
  apply Z.mod_divide in H2; [|unfold PGSZ; lia]. destruct H2 as (k & Ek).
  assert (Hlt : (y - base) / PGSZ < k) by (apply Z.div_lt_upper_bound; [unfold PGSZ; lia | rewrite Ek in H3; lia]).
  assert (Hq : 0 <= (y - base) / PGSZ) by (apply Z.div_pos; unfold PGSZ; lia).
  split; [apply Z.mul_nonneg_nonneg; [unfold PGSZ; lia | exact Hq]|].
  split.
  { replace (PGSZ * ((y - base) / PGSZ) + PGSZ) with (PGSZ * ((y - base) / PGSZ + 1)) by ring.
    rewrite Ek, (Z.mul_comm k PGSZ). apply Z.mul_le_mono_nonneg_l; [unfold PGSZ; lia | lia]. }
  split; [rewrite Z.mul_comm; apply Z.mod_mul; unfold PGSZ; lia|].
  lia.
Qed.

(* [comment removed for export] *)
#[using="HTOPB"] Lemma fresh_of_free : forall L x md s lo n, LINK HTOP FORB L x md -> kf_of s = x ->
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 lo) (w64 n) = true ->
  PGSZ <= lo -> lo mod PGSZ = 0 -> 0 < n -> lo + n <= alloc_top (m_vmmaps md) ->
  fresh_range FORB HTOP L s lo n.
Proof. LiaFast.lf_pins (fun (HTOPB : LiaFast.U) => LiaFast.u0).
  intros L x md s lo n HL Hx Hf H1 H2 H3 H4. pose proof (lk_top _ _ _ _ _ HL) as Ht.
  assert (R1 : bv_unsigned (w64 lo) = lo) by (apply u_w64; unfold PGSZ in *; lia).
  assert (R2 : bv_unsigned (w64 n) = n) by (apply u_w64; unfold PGSZ in *; lia).
  unfold fresh_range. split; [exact H1|]. split; [exact H2|]. split; [lia|]. split; [lia|]. split.
  - apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) (lk_forb _ _ _ _ _ HL) r Hr) as Hc.
    pose proof (covered_rf md _ _ _ _ Hf (rcovered_covered _ _ _ Hc)) as D. rewrite R1, R2 in D. destruct r; exact D.
  - split.
    + intros rg Hrg. rewrite <- footprint_kf_of, Hx in Hrg. pose proof (covered_rf md _ _ _ _ Hf (fp_covered L x md HL rg Hrg)) as D.
      rewrite R1, R2 in D. exact D.
    + intros r rg Hr Hlv. assert (Hr' : nth_error (kf_regions x) r = Some rg) by (rewrite <- Hx; exact Hr).
      destruct (lk_rgeo _ _ _ _ _ HL r rg Hr' Hlv) as (G1 & G2 & G3 & G4 & G5).
      unfold ranges_disjoint. cbn [fst snd].
      destruct (Z_le_gt_dec (lo + n) (ly_reg L r)) as [D|D]; [left; exact D|].
      destruct (Z_le_gt_dec (ly_reg L r + rg_len rg) lo) as [D'|D']; [right; exact D'|]. exfalso.
      assert (YY : exists y, lo <= y < lo + n /\ ly_reg L r <= y < ly_reg L r + rg_len rg).
      { clear - D D' G3 H3. destruct (Z_le_gt_dec lo (ly_reg L r)); [exists (ly_reg L r) | exists lo]; lia. }
      destruct YY as (y & Y1 & Y2).
      destruct (page_of_point (ly_reg L r) (rg_len rg) y G3 G4 Y2) as (o & O1 & O4 & O3 & O2).
      destruct (lk_rcov _ _ _ _ _ HL r rg o Hr' Hlv O1 O4 O3) as (e & He & Hc).
      assert (Cv : covered md (ly_reg L r + o) PGSZ) by (exists e; split; [apply in_or_app; right; exact He | exact Hc]).
      pose proof (covered_rf md _ _ _ _ Hf Cv) as D2. rewrite R1, R2 in D2. unfold ranges_disjoint in D2. cbn [fst snd] in D2.
      clear - D2 Y1 O2. lia.
Qed.

#[using="Type"] Lemma kstep_rw : forall x len, kstep x (KMmapRW len) 1 = (kf_regions x ++ [mkRegion RkMap (page_round len) [] true], kf_brk x, kf_areas x).
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] len. reflexivity. Qed.

#[using="Type"] Lemma rw_vmmaps : forall a n md, m_vmmaps (fresh_rw_next (w64 34) a n md) =
  mkVmMapsFull (vm_reserved (m_vmmaps md)) ((a, n) :: vm_maps (m_vmmaps md)) (vm_noaccess (m_vmmaps md))
    (vm_start_brk (m_vmmaps md)) (vm_brk (m_vmmaps md)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md)).
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

#[using="Type"] Lemma rw_lazy : forall a n md, m_vm_lazy (fresh_rw_next (w64 34) a n md) = m_vm_lazy md.
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

#[using="Type"] Lemma nth_app_old : forall {X} (l : list X) v k y, nth_error l k = Some y -> nth_error (l ++ [v]) k = Some y.
Proof. LiaFast.lf_pins LiaFast.u0. intros X l v k y H. rewrite nth_error_app1; [exact H|]. apply nth_error_Some. congruence. Qed.

#[using="Type"] Lemma nth_app_cases : forall {X} (l : list X) v k y, nth_error (l ++ [v]) k = Some y ->
  (nth_error l k = Some y /\ (k < length l)%nat) \/ (k = length l /\ y = v).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X l v k y H. destruct (Nat.lt_ge_cases k (length l)) as [Hk|Hk].
  - left. rewrite nth_error_app1 in H by exact Hk. split; [exact H | exact Hk].
  - right. rewrite nth_error_app2 in H by exact Hk. destruct (k - length l)%nat as [|j] eqn:E; cbn in H.
    + injection H as <-. split; [lia | reflexivity].
    + destruct j; discriminate H.
Qed.

#[using="Type"] Lemma ly_reg_set_other : forall L r a k, k <> r -> ly_reg (set_reg_addr L r a) k = ly_reg L k.
Proof. LiaFast.lf_pins LiaFast.u0. intros L r a k H. unfold set_reg_addr. cbn. rewrite (proj2 (Nat.eqb_neq k r) H). reflexivity. Qed.

#[using="Type"] Lemma ly_reg_set_same : forall L r a, ly_reg (set_reg_addr L r a) r = a.
Proof. LiaFast.lf_pins LiaFast.u0. intros L r a. unfold set_reg_addr. cbn. rewrite Nat.eqb_refl. reflexivity. Qed.

#[using="Type"] Lemma page_round_props : forall len, 1 <= len -> len <= page_round len /\ page_round len mod PGSZ = 0 /\ page_round len < len + PGSZ.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros len H. unfold page_round, PGSZ. pose proof (Z.div_mod (len + 4096 - 1) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (len + 4096 - 1) 4096 ltac:(lia)). split; [lia|]. split; [apply Z.mod_mul; lia | lia].
Qed.

(* [comment removed for export] *)
Definition brk_clause (L : layout) (rs : list region) (b : brkst) (ars : list sptr) (md : Model) : Prop :=
  match b with
  | BrkNever => bv_unsigned (vm_brk (m_vmmaps md)) = ly_brk0 L /\ (forall r rg, ~ live_kind rs r RkBrk rg)
  | BrkCur r p => nth_error rs r = Some (mkRegion RkBrk (PGSZ * p) [] true) /\ 2 <= p /\
                  ly_reg L r = ly_brk0 L /\ bv_unsigned (vm_brk (m_vmmaps md)) = ly_brk0 L + PGSZ * p /\
                  (Forall (fun a : sptr => prid a <> r) ars ->
                     p = 2 /\ region_free (vm_reserved (m_vmmaps md)) (w64 (ly_brk0 L)) (w64 PGSZ) = true)
  | BrkDead => True
  end.

#[using="Type"] Lemma lk_brk' : forall L x md, LINK HTOP FORB L x md -> brk_clause L (kf_regions x) (kf_brk x) (kf_areas x) md.
Proof. LiaFast.lf_pins LiaFast.u0. intros L x md HL. exact (lk_brk _ _ _ _ _ HL). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma link_new_region : forall L x md md' A N kk b',
  LINK HTOP FORB L x md ->
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 A) (w64 N) = true ->
  PGSZ <= A -> A mod PGSZ = 0 -> 0 < N -> N mod PGSZ = 0 -> A + N <= alloc_top (m_vmmaps md) ->
  m_halted md' = m_halted md -> m_vm_lazy md' = m_vm_lazy md ->
  vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) -> vm_maps (m_vmmaps md') = (w64 A, w64 N) :: vm_maps (m_vmmaps md) ->
  vm_start_brk (m_vmmaps md') = vm_start_brk (m_vmmaps md) -> vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md) ->
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) ->
  (forall o, 0 <= o -> o + PGSZ <= N -> o mod PGSZ = 0 -> kk = RkMetaRes ->
     map_contains (vm_noaccess (m_vmmaps md')) (w64 (A + o)) (w64 PGSZ) = true) ->
  (forall r rg, live_kind (kf_regions x) r RkMetaRes rg -> forall o, 0 <= o -> o + PGSZ <= rg_len rg -> o mod PGSZ = 0 -> ~ In o (rg_rw rg) ->
     map_contains (vm_noaccess (m_vmmaps md')) (w64 (ly_reg L r + o)) (w64 PGSZ) = true) ->
  brk_clause (set_reg_addr L (length (kf_regions x)) A) (kf_regions x ++ [mkRegion kk N [] true]) b' (kf_areas x) md' ->
  (forall a, MngU.inC (vm_noaccess (m_vmmaps md')) a = true ->
     MngU.inC (vm_noaccess (m_vmmaps md)) a = true \/ (kk = RkMetaRes /\ A <= a < A + N)) ->
  rtot (kf_regions x ++ [mkRegion kk N [] true]) = 2 * PGSZ * (2 ^ rcnt (kf_regions x ++ [mkRegion kk N [] true]) - 1) /\
  rtot (kf_regions x ++ [mkRegion kk N [] true]) <=
    2 * PGSZ * (ropen (kf_regions x ++ [mkRegion kk N [] true]) + rcnt (kf_regions x ++ [mkRegion kk N [] true])) ->
  LINK HTOP FORB (set_reg_addr L (length (kf_regions x)) A)
       (kf_regions x ++ [mkRegion kk N [] true], b', kf_areas x) md'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md md' A N kk b' HL Hf G1 G2 G3 G4 G5 E1 E2 E3 E4 E6 E7 E8 NEWNA OLDNA HBRK NAE KK.
  set (L' := set_reg_addr L (length (kf_regions x)) A) in *. set (rs := kf_regions x) in *.
  assert (RA : 0 <= A < 2 ^ 64) by (pose proof (alloc_top_lt (m_vmmaps md)); clear - G1 G3 G5 H; unfold two_pow_64, PGSZ in *; lia).
  assert (RN : 0 <= N < 2 ^ 64) by (pose proof (alloc_top_lt (m_vmmaps md)); clear - G1 G3 G5 H; unfold two_pow_64, PGSZ in *; lia).
  assert (LY : forall k y, nth_error rs k = Some y -> ly_reg L' k = ly_reg L k).
  { intros k y H. apply ly_reg_set_other. intros E. assert (Hs : nth_error rs k <> None) by congruence.
    apply nth_error_Some in Hs. unfold rs in *. clear - Hs E. lia. }
  assert (RF : forall e, In e (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) -> edisj (w64 A, w64 N) e).
  { intros [a sz] He. unfold edisj. cbn [fst snd]. exact (region_free_In _ _ _ a sz Hf He). }
  assert (FRESHP : forall k rgk o, nth_error rs k = Some rgk -> rg_live rgk = true -> 0 <= o -> o + PGSZ <= rg_len rgk -> o mod PGSZ = 0 ->
            ranges_disjoint (A, N) (ly_reg L k + o, PGSZ)).
  { intros k rgk o H1 H2 H3 H4 H5. destruct (lk_rcov _ _ _ _ _ HL k rgk o H1 H2 H3 H4 H5) as (e & He & Hc).
    pose proof (rf_disj _ _ _ e _ _ Hf ltac:(apply in_or_app; right; exact He) Hc) as D. rewrite !u_w64 in D by assumption. exact D. }
  assert (FRESHR : forall k rgk, nth_error rs k = Some rgk -> rg_live rgk = true -> ranges_disjoint (A, N) (ly_reg L k, rg_len rgk)).
  { intros k rgk H1 H2. destruct (lk_rgeo _ _ _ _ _ HL k rgk H1 H2) as (K1 & K2 & K3 & K4 & K5).
    apply pages_disj; [exact G3 | exact K3 | exact K2 | exact K4|]. intros o Ho1 Ho2 Ho3. exact (FRESHP k rgk o H1 H2 Ho1 Ho2 Ho3). }
  constructor; cbn [kf_regions kf_areas kf_brk fst snd].
  - rewrite E1. exact (lk_halt _ _ _ _ _ HL).
  - rewrite E2. exact (lk_lazy _ _ _ _ _ HL).
  - unfold alloc_top in *. rewrite E7. exact (lk_top _ _ _ _ _ HL).
  - rewrite E4. split; [|exact (lk_mdisj _ _ _ _ _ HL)]. intros y Hy. apply RF. apply in_or_app. right. exact Hy.
  - rewrite E4. intros e [<-|He]; [cbn [snd]; rewrite u_w64 by exact RN; exact G3 | exact (lk_mpos _ _ _ _ _ HL e He)].
  - rewrite E4. unfold alloc_top. rewrite E7. fold (alloc_top (m_vmmaps md)). intros e [<-|He]; [cbn [fst snd]; rewrite !u_w64 by assumption; exact G5 | exact (lk_mtop _ _ _ _ _ HL e He)].
  - unfold rcovered. rewrite E3. exact (lk_forb _ _ _ _ _ HL).
  - unfold rcovered. rewrite E3. exact (lk_ctx _ _ _ _ _ HL).
  - intros k rgk H1 H2. unfold alloc_top. rewrite E7. fold (alloc_top (m_vmmaps md)). destruct (nth_app_cases rs _ k rgk H1) as [(H1' & Hk)|(-> & ->)].
    + rewrite (LY k rgk H1'). exact (lk_rgeo _ _ _ _ _ HL k rgk H1' H2).
    + cbn [rg_len]. unfold L'. rewrite ly_reg_set_same. split; [exact G1|]. split; [exact G2|]. split; [exact G3|].
      split; [exact G4 | exact G5].
  - intros r1 r2 rg1 rg2 Hne H1 H2 L1 L2.
    destruct (nth_app_cases rs _ r1 rg1 H1) as [(H1' & Hk1)|(-> & ->)]; destruct (nth_app_cases rs _ r2 rg2 H2) as [(H2' & Hk2)|(-> & ->)].
    + rewrite (LY r1 rg1 H1'), (LY r2 rg2 H2'). exact (lk_rdisj _ _ _ _ _ HL r1 r2 rg1 rg2 Hne H1' H2' L1 L2).
    + rewrite (LY r1 rg1 H1'). unfold L'. rewrite ly_reg_set_same. cbn [rg_len]. apply rd_sym. exact (FRESHR r1 rg1 H1' L1).
    + rewrite (LY r2 rg2 H2'). unfold L'. rewrite ly_reg_set_same. cbn [rg_len]. exact (FRESHR r2 rg2 H2' L2).
    + exfalso. exact (Hne eq_refl).
  - intros k rgk o H1 H2 Ho1 Ho2 Ho3. rewrite E4. destruct (nth_app_cases rs _ k rgk H1) as [(H1' & Hk)|(-> & ->)].
    + rewrite (LY k rgk H1'). destruct (lk_rcov _ _ _ _ _ HL k rgk o H1' H2 Ho1 Ho2 Ho3) as (e & He & Hc). exists e. split; [right; exact He | exact Hc].
    + unfold L'. rewrite ly_reg_set_same. exists (w64 A, w64 N). split; [left; reflexivity|]. cbn [rg_len] in Ho2. apply ecov_w64; [exact RA | exact RN | clear - Ho1; lia | clear - Ho2; lia].
  - intros k rgk (H1 & Hk & H2). rewrite E4. destruct (nth_app_cases rs _ k rgk H1) as [(H1' & Hk')|(-> & ->)].
    + rewrite (LY k rgk H1'). apply map_has_In. right. apply map_has_In. exact (lk_maps _ _ _ _ _ HL k rgk (conj H1' (conj Hk H2))).
    + unfold L'. rewrite ly_reg_set_same. cbn [rg_len]. apply map_has_In. left. reflexivity.
  - intros k rgk (H1 & Hk & H2) o Ho1 Ho2 Ho3 Hnr. destruct (nth_app_cases rs _ k rgk H1) as [(H1' & Hk')|(-> & ->)].
    + rewrite (LY k rgk H1'). exact (OLDNA k rgk (conj H1' (conj Hk H2)) o Ho1 Ho2 Ho3 Hnr).
    + unfold L'. rewrite ly_reg_set_same. cbn [rg_len rg_kind] in *. exact (NEWNA o Ho1 Ho2 Ho3 Hk).
  - intros a Ha. destruct (lk_areas _ _ _ _ _ HL a Ha) as (rga & H1 & H2). exists rga. split; [exact (nth_app_old rs _ _ _ H1) | exact H2].
  - exact HBRK.
  - destruct (lk_brk0 _ _ _ _ _ HL) as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [|exact B4]. unfold min_brk in *. rewrite E6. exact B3.
  - intros a Ha. destruct (NAE a Ha) as [Ho|(Hkk & Ha1)].
    + destruct (lk_na _ _ _ _ _ HL a Ho) as [((r & rg & H1 & H2 & H3 & H4) & Ha')|(r & rg & o & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)].
      * left. split; [|exact Ha']. exists r, rg. split; [exact (nth_app_old rs _ _ _ H1)|]. split; [exact H2|]. split; [exact H3|].
        rewrite (LY r rg H1). exact H4.
      * right. exists r, rg, o. split; [exact (nth_app_old rs _ _ _ H1)|]. repeat (split; [assumption|]). rewrite (LY r rg H1). exact H8.
    + right. exists (length rs), (mkRegion kk N [] true), (PGSZ * ((a - A) / PGSZ)).
      cbn [kf_regions fst snd]. split; [rewrite nth_error_app2 by lia; rewrite Nat.sub_diag; reflexivity|]. cbn [rg_kind rg_live rg_len rg_rw].
      unfold L'. rewrite ly_reg_set_same. unfold PGSZ in *.
      pose proof (Z.div_mod (a - A) 4096 ltac:(lia)) as Q. pose proof (Z.mod_pos_bound (a - A) 4096 ltac:(lia)) as Q2.
      pose proof (Z.div_mod N 4096 ltac:(lia)) as QN. rewrite G4 in QN.
      assert (Hq : (a - A) / 4096 < N / 4096) by (apply Z.div_lt_upper_bound; lia).
      split; [exact Hkk|]. split; [reflexivity|]. split; [apply Z.mul_nonneg_nonneg; [lia | apply Z.div_pos; lia]|].
      split; [lia|]. split; [rewrite Z.mul_comm; apply Z_mod_mult|]. split; [intros []|]. lia.
  - intros k rgk (H1 & Hk & H2). destruct (nth_app_cases rs _ k rgk H1) as [(H1' & Hk')|(-> & ->)].
    + exact (lk_rw _ _ _ _ _ HL k rgk (conj H1' (conj Hk H2))).
    + cbn [rg_rw]. split; [constructor | intros o []].
  - intros k rgk H1 Hk. destruct (nth_app_cases rs _ k rgk H1) as [(H1' & Hk')|(-> & ->)]; [exact (lk_k0 _ _ _ _ _ HL k rgk H1' Hk) | reflexivity].
  - exact (proj1 KK).
  - exact (proj2 KK).
  - unfold alloc_top. rewrite E7. exact (lk_atop _ _ _ _ _ HL).
  - rewrite E8. exact (lk_lim _ _ _ _ _ HL).
  - rewrite E3. exact (lk_rsz _ _ _ _ _ HL).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma kk_other : forall L x md kk N rw lv, LINK HTOP FORB L x md -> kk <> RkMetaRes ->
  rtot (kf_regions x ++ [mkRegion kk N rw lv]) = 2 * PGSZ * (2 ^ rcnt (kf_regions x ++ [mkRegion kk N rw lv]) - 1) /\
  rtot (kf_regions x ++ [mkRegion kk N rw lv]) <=
    2 * PGSZ * (ropen (kf_regions x ++ [mkRegion kk N rw lv]) + rcnt (kf_regions x ++ [mkRegion kk N rw lv])).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md kk N rw lv HL Hk. destruct (rsv_other (mkRegion kk N rw lv) Hk) as (R1 & R2 & R3).
  rewrite !rtot_app, !ropen_app, !rcnt_app, R1, R2, R3, !Z.add_0_r.
  exact (conj (lk_k1 _ _ _ _ _ HL) (lk_k2 _ _ _ _ _ HL)).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma brk_clause_new : forall L x md md' A kk N,
  LINK HTOP FORB L x md -> kk <> RkBrk ->
  vm_brk (m_vmmaps md') = vm_brk (m_vmmaps md) -> vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) ->
  brk_clause (set_reg_addr L (length (kf_regions x)) A) (kf_regions x ++ [mkRegion kk N [] true]) (kf_brk x) (kf_areas x) md'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md md' A kk N HL Hkk E5 E3. pose proof (lk_brk' L x md HL) as Hb. unfold brk_clause in *.
  destruct (kf_brk x) as [| | r0 p] eqn:Eb.
  - destruct Hb as (Hb1 & Hb2). split; [rewrite E5; exact Hb1|]. intros k rgk (H1 & Hk & H2).
    destruct (nth_app_cases (kf_regions x) _ k rgk H1) as [(H1' & Hk')|(-> & ->)]; [exact (Hb2 k rgk (conj H1' (conj Hk H2))) | cbn [rg_kind] in Hk; exact (Hkk Hk)].
  - exact I.
  - destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5). split; [exact (nth_app_old _ _ _ _ Hb1)|]. split; [exact Hb2|].
    split; [rewrite ly_reg_set_other; [exact Hb3|]; intros ->; assert (Hs : nth_error (kf_regions x) (length (kf_regions x)) <> None) by congruence;
            apply nth_error_Some in Hs; clear - Hs; lia|].
    split; [rewrite E5; exact Hb4|]. intros HA. rewrite E3. exact (Hb5 HA).
Qed.

#[using="Hoff HTOPB ob_rw ob_rw'"] Lemma case_rw : forall len, node_ok (KMmapRW len).
Proof. LiaFast.lf_pins (fun (Hoff HTOPB ob_rw ob_rw' : LiaFast.U) => LiaFast.u0).
  intros len L x md B s regs pc m K Hec Hx Hrq HL HB Hc Hcont.
  apply (rz_mmap_rw segs cfg Hoff rom L s len regs pc m md K Hec (lk_halt _ _ _ _ _ HL) (lk_lazy _ _ _ _ _ HL) Hrq (ob_rw L x md B len HL HB Hc Hrq)).
  intros a Ha. pose proof Ha as (Ha1 & Ha2 & Ha3 & Ha4 & Ha5).
  assert (Hl1 : 1 <= len < 2 ^ 63) by exact Hrq.
  set (A := bv_unsigned a) in *. set (N := page_round len) in *.
  destruct (page_round_props len ltac:(clear - Hl1; lia)) as (P1 & P2 & P3).
  assert (EA : a = w64 A) by (apply w64_of_u; reflexivity). rewrite EA in Ha4 |- *.
  assert (G1 : PGSZ <= A) by (clear - Ha1 Ha2; unfold page_size, PGSZ in *; assert (Q := Z.div_mod A 4096 ltac:(lia)); lia).
  assert (Hf : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 A) (w64 N) = true) by exact Ha4.
  apply (Hcont (mkEffect (w64 A) [] [(w64 A, w64 N)]) 1 (set_reg_addr L (length (st_regions s)) A) _
           (o_mmap_rw FORB HTOP L s len A (fresh_of_free L x md s A N HL Hx Hf G1 ltac:(exact Ha1) ltac:(clear - P1 Hl1; lia) Ha3))
           (vm_only_fresh_rw_next _ _ _ _)).
  - rewrite kstep_rw. subst x. cbn [kf_of kf_regions fst snd].
    apply (link_new_region L (kf_of s) md _ A N RkMap (kf_brk (kf_of s)) HL Hf G1 Ha1 ltac:(clear - P1 Hl1; lia) P2 Ha3); try reflexivity.
    + intros o _ _ _ E. discriminate E.
    + intros r rg Hr o Ho1 Ho2 Ho3 Hnr. exact (lk_resv _ _ _ _ _ HL r rg Hr o Ho1 Ho2 Ho3 Hnr).
    + exact (brk_clause_new L (kf_of s) md _ A RkMap N HL ltac:(discriminate) eq_refl eq_refl).
    + intros a0 Ha0. left. rewrite rw_vmmaps in Ha0. exact Ha0.
    + exact (kk_other L (kf_of s) md RkMap N [] true HL ltac:(discriminate)).
  - rewrite <- EA. exact (ob_rw' L x md B len a HL HB Hc Hl1 Ha).
Qed.
#[using="Type"] Lemma kstep_na : forall x len, kstep x (KMmapNone len) 1 = (kf_regions x ++ [mkRegion RkMetaRes len [] true], kf_brk x, kf_areas x).
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] len. reflexivity. Qed.

#[using="Type"] Lemma na_vmmaps : forall a n md, m_vmmaps (fresh_na_next (w64 34) a n md) =
  mkVmMapsFull (vm_reserved (m_vmmaps md)) ((a, n) :: vm_maps (m_vmmaps md)) ((a, n) :: vm_noaccess (m_vmmaps md))
    (vm_start_brk (m_vmmaps md)) (vm_brk (m_vmmaps md)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md)).
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

#[using="Type"] Lemma page_round_mult : forall k, 0 <= k -> page_round (k * PGSZ) = k * PGSZ.
Proof. LiaFast.lf_pins LiaFast.u0. intros k Hk. unfold page_round, PGSZ. replace (k * 4096 + 4096 - 1) with (4095 + k * 4096) by ring.
  rewrite Z.div_add by lia. rewrite (Z.div_small 4095 4096) by lia. ring. Qed.

#[using="Hoff HTOPB ob_na ob_na'"] Lemma case_na : forall len, node_ok (KMmapNone len).
Proof. LiaFast.lf_pins (fun (Hoff HTOPB ob_na ob_na' : LiaFast.U) => LiaFast.u0).
  intros len L x md B s regs pc m K Hec Hx Hrq HL HB Hc Hcont.
  pose proof Hrq as (Hlen & Hcnt & Hsh & Hres).
  destruct (ob_na L x md B s len HL HB Hc Hx Hrq) as (a0 & Ha0).
  assert (K2 : 2 <= Z.shiftl 2 (st_meta_alloc_shift s)).
  { rewrite Z.shiftl_mul_pow2 by exact Hsh. pose proof (Z.pow_pos_nonneg 2 (st_meta_alloc_shift s) ltac:(lia) Hsh). clear - H. lia. }
  assert (EN : page_round len = len) by (rewrite Hlen; apply page_round_mult; clear - K2; lia).
  pose proof (alloc_top_lt (m_vmmaps md)) as AT. pose proof (lk_top _ _ _ _ _ HL) as GT.
  assert (Hl1 : 1 <= len < 2 ^ 63).
  { destruct Ha0 as (_ & A2 & A3 & _). rewrite EN in A3. pose proof (u_range a0). clear - A2 A3 AT GT HTOPB Hlen K2.
    split; [rewrite Hlen; unfold PGSZ; lia | lia]. }
  apply (rz_mmap_na segs cfg Hoff rom L s len regs pc m md K Hec (lk_halt _ _ _ _ _ HL) (lk_lazy _ _ _ _ _ HL) Hl1 (ex_intro _ a0 Ha0)).
  intros a Ha. pose proof Ha as (Ha1 & Ha2 & Ha3 & Ha4). rewrite EN in Ha3, Ha4 |- *.
  set (A := bv_unsigned a) in *.
  assert (EA : a = w64 A) by (apply w64_of_u; reflexivity). rewrite EA in Ha4 |- *.
  assert (G1 : PGSZ <= A) by (clear - Ha1 Ha2; unfold page_size, PGSZ in *; assert (Q := Z.div_mod A 4096 ltac:(lia)); lia).
  assert (Hf : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 A) (w64 len) = true) by exact Ha4.
  assert (P2 : len mod PGSZ = 0) by (rewrite Hlen; apply Z.mod_mul; unfold PGSZ; lia).
  apply (Hcont (mkEffectU (w64 A) [] [] [(w64 A, w64 len)] [] []) 1 (set_reg_addr L (length (st_regions s)) A) _
           (o_mmap_na FORB HTOP L s len A (fresh_of_free L x md s A len HL Hx Hf G1 ltac:(exact Ha1) ltac:(clear - Hl1; lia) Ha3))
           (vm_only_fresh_na_next _ _ _ _)).
  - rewrite kstep_na. subst x. cbn [kf_of kf_regions fst snd].
    apply (link_new_region L (kf_of s) md _ A len RkMetaRes (kf_brk (kf_of s)) HL Hf G1 Ha1 ltac:(clear - Hl1; lia) P2 Ha3);
      try (rewrite ?na_vmmaps; reflexivity).
    + intros o Ho1 Ho2 Ho3 _. rewrite na_vmmaps. cbn [vm_noaccess]. apply map_contains_In. exists (w64 A, w64 len). split; [left; reflexivity|].
      assert (RA : 0 <= A < 2 ^ 64) by (clear - Ha3 G1 AT Hl1; unfold two_pow_64, PGSZ in *; lia).
      rewrite !u_w64 by (clear - Ha3 G1 AT Hl1 Ho1 Ho2; unfold two_pow_64, PGSZ in *; lia). apply ecov_w64; [exact RA | clear - Ha3 G1 AT Hl1; unfold two_pow_64, PGSZ in *; lia | clear - Ho1; lia | clear - Ho2; unfold PGSZ in *; lia].
    + intros r rg Hr o Ho1 Ho2 Ho3 Hnr. rewrite na_vmmaps. cbn [vm_noaccess]. apply map_contains_In.
      pose proof (lk_resv _ _ _ _ _ HL r rg Hr o Ho1 Ho2 Ho3 Hnr) as Hna. apply map_contains_In in Hna. destruct Hna as (e & He & Hce).
      exists e. split; [right; exact He | exact Hce].
    + exact (brk_clause_new L (kf_of s) md _ A RkMetaRes len HL ltac:(discriminate) eq_refl eq_refl).
    + intros aq Haq. rewrite na_vmmaps in Haq. cbn [vm_noaccess] in Haq. unfold MngU.inC in Haq. cbn [existsb fst snd] in Haq.
      apply orb_true_iff in Haq as [Haq|Haq]; [right; split; [reflexivity|] | left; exact Haq].
      unfold MngU.inI in Haq. apply andb_true_iff in Haq as [B1 B2]. apply Z.leb_le in B1. apply Z.ltb_lt in B2.
      assert (RA : 0 <= A < 2 ^ 64) by (pose proof (u_range a) as UR; fold A in UR; exact UR).
      rewrite (u_w64 A) in B1, B2 by (clear - Hl1 RA; lia). rewrite (u_w64 len) in B2 by (clear - Hl1; lia). lia.
    + rewrite !rtot_app, !ropen_app, !rcnt_app. destruct (rsv_meta len [] true) as (R1 & R2 & R3). rewrite R1, R2, R3.
      cbn [length Z.of_nat]. destruct Hres as (F6 & F1 & F2 & _).
      change (resv_total s) with (rtot (st_regions s)) in F6, F1. change (resv_count s) with (rcnt (st_regions s)) in F1, F2.
      change (resv_opened s) with (ropen (st_regions s)) in F1. change (kf_regions (kf_of s)) with (st_regions s). rewrite F2. rewrite Hlen, Z.shiftl_mul_pow2 by exact Hsh.
      rewrite Z.pow_add_r by lia. change (2 ^ 1) with 2. set (T := 2 ^ st_meta_alloc_shift s) in *. clear - F6 F1 F2. unfold PGSZ in *. lia.
  - rewrite <- EA. replace (w64 len) with (w64 (page_round len)) by (rewrite EN; reflexivity). exact (ob_na' L x md B len a HL HB Hc Hl1 Ha).
Qed.
#[using="Type"] Lemma kstep_pr : forall x r o, kstep x (KMprotect (SP r o)) 1 =
  (lupd (kf_regions x) r (let rg := nth r (kf_regions x) rg_dflt in mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg)),
   kf_brk x, kf_areas x ++ [SP r o]).
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] r o. reflexivity. Qed.

#[using="Type"] Lemma pr_vmmaps : forall md a n, m_vmmaps (mprotect_model_next md a n) =
  mkVmMapsFull (vm_reserved (m_vmmaps md)) (vm_maps (m_vmmaps md))
    (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk (m_vmmaps md)) (vm_brk (m_vmmaps md)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md)).
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

#[using="Type"] Lemma nth_lupd_cases : forall {X} (l : list X) r v k y, nth_error (lupd l r v) k = Some y ->
  (k = r /\ y = v /\ (r < length l)%nat) \/ (k <> r /\ nth_error l k = Some y).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X l r v k y H. rewrite nth_error_lupd in H. destruct (Nat.eqb_spec k r) as [->|Hne].
  - destruct (Nat.ltb r (length l)) eqn:E; cbn in H.
    + left. injection H as <-. split; [reflexivity|]. split; [reflexivity|]. apply Nat.ltb_lt. exact E.
    + right. exfalso. apply Nat.ltb_ge in E. assert (Hs : nth_error l r <> None) by congruence. apply nth_error_Some in Hs. lia.
  - right. split; [exact Hne|]. cbn in H. exact H.
Qed.

#[using="Type"] Lemma nth_lupd_other : forall {X} (l : list X) r v k, k <> r -> nth_error (lupd l r v) k = nth_error l k.
Proof. LiaFast.lf_pins LiaFast.u0. intros X l r v k H. rewrite nth_error_lupd. rewrite (proj2 (Nat.eqb_neq k r) H). reflexivity. Qed.

#[using="Type"] Lemma nth_lupd_same : forall {X} (l : list X) r v y, nth_error l r = Some y -> nth_error (lupd l r v) r = Some v.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X l r v y H. rewrite nth_error_lupd. rewrite Nat.eqb_refl. assert (Hs : nth_error l r <> None) by congruence.
  apply nth_error_Some in Hs. rewrite (proj2 (Nat.ltb_lt _ _) Hs). reflexivity.
Qed.

#[using="Type"] Lemma nth_of_nth_error : forall {X} (l : list X) r y d, nth_error l r = Some y -> nth r l d = y.
Proof. LiaFast.lf_pins LiaFast.u0. intros X l r y d H. apply nth_error_nth. exact H. Qed.

#[using="Type"] Lemma mod_add0 : forall a b, a mod PGSZ = 0 -> b mod PGSZ = 0 -> (a + b) mod PGSZ = 0.
Proof. LiaFast.lf_pins LiaFast.u0. intros a b Ha Hb. rewrite Z.add_mod by (unfold PGSZ; lia). rewrite Ha, Hb. reflexivity. Qed.

#[using="Hoff ob_pr ob_pr'"] Lemma case_pr : forall p, node_ok (KMprotect p).
Proof. LiaFast.lf_pins (fun (Hoff ob_pr ob_pr' : LiaFast.U) => LiaFast.u0).
  intros [r o] L x md B s regs pc m K Hec Hx Hrq HL HB Hc Hcont.
  pose proof Hrq as (Hcnt & Hp & rg & Hrg & Hk & Hlv & Ho3 & Ho1 & Ho2 & Hnr). cbn [prid poff] in *.
  assert (Hrgx : nth_error (kf_regions x) r = Some rg) by (subst x; exact Hrg).
  destruct (lk_rgeo _ _ _ _ _ HL r rg Hrgx Hlv) as (G1 & G2 & G3 & G4 & G5).
  pose proof (alloc_top_lt (m_vmmaps md)) as AT. pose proof (lk_top _ _ _ _ _ HL) as GT.
  set (a := ly_reg L r + o) in *.
  assert (Ea : loc_addr L (LMem (SP r o)) = a) by reflexivity.
  assert (Ra : 0 <= a /\ a + PGSZ < 2 ^ 64) by (unfold a; clear - G1 G5 AT Ho2 Ho1; unfold two_pow_64, PGSZ in *; lia).
  assert (Hal : a mod PGSZ = 0) by (unfold a; apply mod_add0; assumption).
  assert (HNA : map_contains (vm_noaccess (m_vmmaps md)) (w64 a) (w64 PGSZ) = true).
  { exact (lk_resv _ _ _ _ _ HL r rg (conj Hrgx (conj Hk Hlv)) o ltac:(clear - Ho1; unfold PGSZ in *; lia) Ho2 Ho3 Hnr). }
  assert (HMC : map_contains (vm_maps (m_vmmaps md)) (w64 a) (w64 PGSZ) = true).
  { destruct (lk_rcov _ _ _ _ _ HL r rg o Hrgx Hlv ltac:(clear - Ho1; unfold PGSZ in *; lia) Ho2 Ho3) as (e & He & Hce).
    apply map_contains_In. exists e. split; [exact He|]. rewrite !u_w64 by (clear - Ra; unfold PGSZ in *; lia). exact Hce. }
  assert (P1 : loc_addr L (LMem (SP r o)) mod PGSZ = 0) by (rewrite Ea; exact Hal).
  assert (P2 : 0 <= loc_addr L (LMem (SP r o))) by (rewrite Ea; clear - Ra; lia).
  assert (P3 : loc_addr L (LMem (SP r o)) + PGSZ < 2 ^ 64) by (rewrite Ea; clear - Ra; lia).
  assert (P4 : map_contains (vm_noaccess (m_vmmaps md)) (w64 (loc_addr L (LMem (SP r o)))) (w64 PGSZ)
                 && map_contains (vm_maps (m_vmmaps md)) (w64 (loc_addr L (LMem (SP r o)))) (w64 PGSZ) = true) by (rewrite Ea, HNA, HMC; reflexivity).
  pose proof (ob_pr L x md B (SP r o) HL HB Hc P2 P3) as P5.
  apply (rz_mprotect segs cfg Hoff rom L s (SP r o) regs pc m md K Hec (lk_halt _ _ _ _ _ HL) (lk_lazy _ _ _ _ _ HL) P1 P2 P3 P4 P5).
  rewrite Ea.
  apply (Hcont (mkEffect (w64 0) [] [(w64 a, w64 PGSZ)]) 1 L _ ltac:(rewrite <- Ea; exact (o_mprotect FORB HTOP L s (SP r o))) (vm_only_mprotect_model_next _ _ _)).
  2: { rewrite <- Ea. exact (ob_pr' L x md B (SP r o) HL HB Hc P2 P3). }
  rewrite kstep_pr. rewrite (nth_of_nth_error _ r rg rg_dflt Hrgx).
  set (rg' := mkRegion (rg_kind rg) (rg_len rg) (rg_rw rg ++ [o]) (rg_live rg)).
  set (rs' := lupd (kf_regions x) r rg').
  assert (NTH : forall k rgk, nth_error rs' k = Some rgk -> (k = r /\ rgk = rg') \/ (k <> r /\ nth_error (kf_regions x) k = Some rgk)).
  { intros k rgk H. destruct (nth_lupd_cases _ r rg' k rgk H) as [(-> & -> & _)|H']; [left; split; reflexivity | right; exact H']. }
  assert (RSR : nth_error rs' r = Some rg') by exact (nth_lupd_same _ r rg' rg Hrgx).
  (* [comment removed for export] *)
  assert (GEO : forall k rgk, nth_error rs' k = Some rgk -> exists rgk0, nth_error (kf_regions x) k = Some rgk0 /\
                  rg_len rgk = rg_len rgk0 /\ rg_live rgk = rg_live rgk0 /\ rg_kind rgk = rg_kind rgk0).
  { intros k rgk H. destruct (NTH k rgk H) as [(-> & ->)|(_ & H')]; [exists rg; split; [exact Hrgx|]; cbn; auto | exists rgk; auto]. }
  assert (UA : bv_unsigned (w64 a) = a) by (apply u_w64; clear - Ra; unfold PGSZ in *; lia).
  constructor; cbn [kf_regions kf_areas kf_brk fst snd]; rewrite ?pr_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_brk vm_start_brk vm_init_sp].
  - exact (lk_halt _ _ _ _ _ HL).
  - exact (lk_lazy _ _ _ _ _ HL).
  - exact (lk_top _ _ _ _ _ HL).
  - exact (lk_mdisj _ _ _ _ _ HL).
  - exact (lk_mpos _ _ _ _ _ HL).
  - exact (lk_mtop _ _ _ _ _ HL).
  - exact (lk_forb _ _ _ _ _ HL).
  - exact (lk_ctx _ _ _ _ _ HL).
  - intros k rgk H1 H2. destruct (GEO k rgk H1) as (rgk0 & E1 & E2 & E3 & _). rewrite E2. rewrite E3 in H2.
    exact (lk_rgeo _ _ _ _ _ HL k rgk0 E1 H2).
  - intros r1 r2 rg1 rg2 Hne H1 H2 L1 L2. destruct (GEO r1 rg1 H1) as (rg10 & E1 & E2 & E3 & _). destruct (GEO r2 rg2 H2) as (rg20 & F1 & F2 & F3 & _).
    rewrite E2, F2. rewrite E3 in L1. rewrite F3 in L2. exact (lk_rdisj _ _ _ _ _ HL r1 r2 rg10 rg20 Hne E1 F1 L1 L2).
  - intros k rgk o' H1 H2 H3 H4 H5. destruct (GEO k rgk H1) as (rgk0 & E1 & E2 & E3 & _). rewrite E2 in H4. rewrite E3 in H2.
    exact (lk_rcov _ _ _ _ _ HL k rgk0 o' E1 H2 H3 H4 H5).
  - intros k rgk (H1 & H2 & H3). destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')]; [cbn in H2; congruence|].
    exact (lk_maps _ _ _ _ _ HL k rgk (conj H' (conj H2 H3))).
  - intros k rgk (H1 & H2 & H3) o' Ho'1 Ho'2 Ho'3 Hnr'. apply map_contains_In. rewrite UA. rewrite u_w64 by (unfold PGSZ; lia).
    destruct (NTH k rgk H1) as [(-> & ->)|(Hkr & H')].
    + unfold rg' in *. cbn [rg_len rg_rw rg_kind rg_live] in *. assert (Hne : o' <> o) by (intros ->; apply Hnr'; apply in_or_app; right; left; reflexivity).
      assert (Hnr0 : ~ In o' (rg_rw rg)) by (intros Hi; apply Hnr'; apply in_or_app; left; exact Hi).
      pose proof (lk_resv _ _ _ _ _ HL r rg (conj Hrgx (conj Hk Hlv)) o' Ho'1 Ho'2 Ho'3 Hnr0) as Hna. apply map_contains_In in Hna.
      rewrite !u_w64 in Hna |- * by (clear - G1 G5 AT Ho'1 Ho'2; unfold two_pow_64, PGSZ in *; lia).
      apply ecov_subtract; [clear; unfold PGSZ; lia | | clear - Ra; lia | clear; unfold PGSZ; lia | clear - Ra; unfold PGSZ in *; lia | exact Hna].
      unfold a. clear - Hne Ho'3 Ho3. unfold PGSZ in *.
      assert (Q1 := Z.div_mod o' 4096 ltac:(lia)). assert (Q2 := Z.div_mod o 4096 ltac:(lia)).
      assert (o' / 4096 <> o / 4096) by (intros E; apply Hne; lia). lia.
    + pose proof (lk_resv _ _ _ _ _ HL k rgk (conj H' (conj H2 H3)) o' Ho'1 Ho'2 Ho'3 Hnr') as Hna. apply map_contains_In in Hna.
      destruct (lk_rgeo _ _ _ _ _ HL k rgk H' H3) as (K1 & K2 & K3 & K4 & K5).
      rewrite !u_w64 in Hna |- * by (clear - K1 K5 AT Ho'1 Ho'2; unfold two_pow_64, PGSZ in *; lia).
      pose proof (lk_rdisj _ _ _ _ _ HL k r rgk rg Hkr H' Hrgx H3 Hlv) as D. unfold ranges_disjoint in D. cbn [fst snd] in D.
      apply ecov_subtract; [clear; unfold PGSZ; lia | | clear - Ra; lia | clear; unfold PGSZ; lia | clear - Ra; unfold PGSZ in *; lia | exact Hna].
      unfold a. clear - D Ho'1 Ho'2 Ho1 Ho2. unfold PGSZ in *. lia.
  - intros a' Ha'. apply in_app_iff in Ha' as [Ha'|[<-|[]]].
    + destruct (lk_areas _ _ _ _ _ HL a' Ha') as (rga & H1 & H2 & H3 & H4). destruct (Nat.eq_dec (prid a') r) as [E|E].
      * rewrite E in H1 |- *. rewrite Hrgx in H1. injection H1 as <-. exists rg'. split; [exact RSR|]. cbn. auto.
      * exists rga. split; [unfold rs'; rewrite nth_lupd_other by exact E; exact H1 | auto].
    + exists rg'. split; [exact RSR|]. cbn [prid poff rg'] in *. cbn. split; [exact Hlv|]. split; [rewrite Hk; discriminate|].
      split; [clear - Ho1; unfold PGSZ in *; lia|]. split; [exact Ho2 | exact Ho3].
  - pose proof (lk_brk' L x md HL) as Hb. unfold brk_clause in Hb. revert Hb. destruct (kf_brk x) as [| | r0 p0] eqn:Eb; intros Hb.
    + destruct Hb as (Hb1 & Hb2). split; [exact Hb1|]. intros k rgk (H1 & H2 & H3). destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')]; [cbn in H2; congruence|].
      exact (Hb2 k rgk (conj H' (conj H2 H3))).
    + exact I.
    + destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5). assert (Hr0 : r0 <> r) by (intros ->; rewrite Hb1 in Hrgx; injection Hrgx as <-; discriminate Hk).
      split; [unfold rs'; rewrite nth_lupd_other by exact Hr0; exact Hb1|]. split; [exact Hb2|]. split; [exact Hb3|]. split; [exact Hb4|].
      intros HA. apply Forall_app in HA as [HA _]. exact (Hb5 HA).
  - exact (lk_brk0 _ _ _ _ _ HL).
  - intros aq Haq. unfold na_byte. cbn [kf_regions fst snd]. rewrite UA, (u_w64 PGSZ) in Haq by (unfold PGSZ; lia).
    rewrite MngU.inC_subtract in Haq by (clear - Ra; unfold PGSZ in *; lia). apply andb_true_iff in Haq as [Hin Hout].
    apply negb_true_iff in Hout. unfold MngU.inI in Hout. apply andb_false_iff in Hout.
    assert (Hout' : ~ (a <= aq < a + PGSZ)) by (destruct Hout as [E|E]; [apply Z.leb_gt in E | apply Z.ltb_ge in E]; lia).
    destruct (lk_na _ _ _ _ _ HL aq Hin) as [((rb & rgb & H1 & H2 & H3 & H4) & Hg)|(rq & rgq & oq & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)].
    + left. split; [|exact Hg]. assert (Hne : rb <> r) by (intros ->; rewrite Hrgx in H1; injection H1 as <-; rewrite Hk in H2; discriminate H2).
      exists rb, rgb. split; [unfold rs'; rewrite nth_lupd_other by exact Hne; exact H1 | exact (conj H2 (conj H3 H4))].
    + right. destruct (Nat.eq_dec rq r) as [->|Hne].
      * rewrite Hrgx in H1. injection H1 as <-. exists r, rg', oq. split; [exact RSR|]. unfold rg'. cbn [rg_kind rg_live rg_len rg_rw].
        split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [|exact H8].
        intros Hin'. apply in_app_iff in Hin' as [Hin'|[E|[]]]; [exact (H7 Hin')|]. subst oq. apply Hout'. unfold a. exact H8.
      * exists rq, rgq, oq. split; [unfold rs'; rewrite nth_lupd_other by exact Hne; exact H1 | exact (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))].
  - intros k rgk (H1 & H2 & H3). destruct (NTH k rgk H1) as [(-> & ->)|(Hkr & H')].
    + unfold rg'. cbn [rg_rw rg_len]. destruct (lk_rw _ _ _ _ _ HL r rg (conj Hrgx (conj Hk Hlv))) as (ND & AL).
      split; [exact (NoDup_snoc _ _ ND Hnr)|]. intros o' Ho'. apply in_app_iff in Ho' as [Ho'|[<-|[]]]; [exact (AL o' Ho') | exact (conj Ho3 (conj Ho1 Ho2))].
    + exact (lk_rw _ _ _ _ _ HL k rgk (conj H' (conj H2 H3))).
  - intros k rgk H1 H2. destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')]; [unfold rg'; cbn [rg_live]; exact Hlv | exact (lk_k0 _ _ _ _ _ HL k rgk H' H2)].
  - unfold rs'. destruct (rsv_lupd (kf_regions x) r rg' rg Hrgx) as (R1 & R2 & R3). rewrite R1, R3.
    assert (Hk' : rg_kind rg' = RkMetaRes) by exact Hk.
    rewrite (proj1 (rsv_meta' rg Hk)), (proj1 (rsv_meta' rg' Hk')), (proj2 (proj2 (rsv_meta' rg Hk))), (proj2 (proj2 (rsv_meta' rg' Hk'))).
    cbn [rg_len rg']. rewrite !Z.sub_add. exact (lk_k1 _ _ _ _ _ HL).
  - unfold rs'. destruct (rsv_lupd (kf_regions x) r rg' rg Hrgx) as (R1 & R2 & R3). rewrite R1, R2, R3.
    assert (Hk' : rg_kind rg' = RkMetaRes) by exact Hk.
    rewrite (proj1 (rsv_meta' rg Hk)), (proj1 (rsv_meta' rg' Hk')), (proj2 (proj2 (rsv_meta' rg Hk))), (proj2 (proj2 (rsv_meta' rg' Hk'))).
    rewrite (proj1 (proj2 (rsv_meta' rg Hk))), (proj1 (proj2 (rsv_meta' rg' Hk'))). cbn [rg_len rg_rw rg']. rewrite length_app. cbn [length].
    pose proof (lk_k2 _ _ _ _ _ HL) as K2. clear - K2. unfold PGSZ in *. lia.
  - exact (lk_atop _ _ _ _ _ HL).
  - exact (lk_lim _ _ _ _ _ HL).
  - exact (lk_rsz _ _ _ _ _ HL).
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma munmap_vmmaps : forall A N md, m_vmmaps (munmap_next A N md) =
  mkVmMapsFull (vm_reserved (m_vmmaps md)) (map_remove (vm_maps (m_vmmaps md)) A)
    (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned A) (bv_unsigned A + bv_unsigned N))
    (vm_start_brk (m_vmmaps md)) (vm_brk (m_vmmaps md)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md)).
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

#[using="Type"] Lemma munmap_lazy : forall A N md, m_vm_lazy md = [] -> m_vm_lazy (munmap_next A N md) = [].
Proof. LiaFast.lf_pins LiaFast.u0. intros A N md H. unfold munmap_next, vm_forget_range, with_vm_backing, with_vmmaps, m_vm_lazy in *. cbn. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma kstep_munmap : forall x r len z,
  kstep x (KMunmap r len) z = (lupd (kf_regions x) r (mkRegion RkMap (rg_len (nth r (kf_regions x) rg_dflt)) [] false), kf_brk x, kf_areas x).
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] r len z. reflexivity. Qed.

#[using="Type"] Lemma nth_dead : forall rs r v k rg, rg_live v = false -> nth_error (lupd rs r v) k = Some rg -> rg_live rg = true ->
  k <> r /\ nth_error rs k = Some rg.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros rs r v k rg Hv H Hl. rewrite nth_error_lupd in H.
  destruct (Nat.eqb_spec k r) as [->|Hne].
  - destruct (Nat.ltb r (length rs)) eqn:E2; cbn in H.
    + injection H as <-. congruence.
    + apply Nat.ltb_ge in E2. assert (Hs : nth_error rs r <> None) by congruence. apply nth_error_Some in Hs. lia.
  - split; [exact Hne|]. cbn in H. exact H.
Qed.

#[using="HTOPB ob_munmap"] Lemma case_munmap : forall r len, node_ok (KMunmap r len).
Proof. LiaFast.lf_pins (fun (HTOPB ob_munmap : LiaFast.U) => LiaFast.u0).
  intros r len L x md B s regs pc m K Hec Hx Hrq HL HB Hc Hcont.
  destruct Hrq as (rg & Hrg & Hk & Hlv & Hlen & Hl0 & _).
  assert (Hrgx : nth_error (kf_regions x) r = Some rg) by (subst x; exact Hrg).
  destruct (lk_rgeo _ _ _ _ _ HL r rg Hrgx Hlv) as (G1 & G2 & G3 & G4 & G5). pose proof (lk_top _ _ _ _ _ HL) as GT.
  pose proof (lk_maps _ _ _ _ _ HL r rg (conj Hrgx (conj Hk Hlv))) as Hhas.
  set (a := ly_reg L r) in *. set (n := rg_len rg) in *.
  assert (Hlen1 : 1 <= len).
  { clear - Hlen G3 Hl0. destruct (Z_lt_le_dec len 1) as [Hl|Hl]; [|exact Hl]. exfalso. assert (len = 0) by lia. subst len.
    change (page_round 0) with 0 in Hlen. lia. }
  apply (rz_munmap segs cfg rom L s r len regs pc m md K Hec (lk_halt _ _ _ _ _ HL) (lk_lazy _ _ _ _ _ HL) G2 Hlen1
           ltac:(clear - G1; unfold PGSZ in *; lia) ltac:(rewrite <- Hlen; clear - G5 G1 HTOPB GT; unfold PGSZ in *; lia) ltac:(rewrite <- Hlen; exact Hhas)).
  apply (Hcont (eff_munmap (ly_reg L r) (page_round len)) 1 L _ (o_munmap FORB HTOP L s r len) (vm_only_munmap_next _ _ _)).
  2: { exact (ob_munmap L x md B r len rg HL HB Hc Hrgx Hk Hlv Hlen). }
  rewrite <- Hlen. fold a n.
  set (md' := munmap_next (w64 a) (w64 n) md).
  assert (RA : 0 <= a < 2 ^ 64) by (clear - G1 G3 G5 HTOPB GT; unfold PGSZ in *; lia). assert (RN : 0 <= n < 2 ^ 64) by (clear - G1 G3 G5 HTOPB GT; unfold PGSZ in *; lia).
  assert (Hin : In (w64 a, w64 n) (vm_maps (m_vmmaps md))) by (apply map_has_In; exact Hhas).
  (* [comment removed for export] *)
  assert (SURV : forall k rgk o e, k <> r -> nth_error (kf_regions x) k = Some rgk -> rg_live rgk = true -> 0 <= o -> o + PGSZ <= rg_len rgk ->
            In e (vm_maps (m_vmmaps md)) -> ecov e (ly_reg L k + o) PGSZ -> fst e <> w64 a).
  { intros k rgk o e Hkr Hk' Hl' Ho1 Ho2 He Hce Hfe.
    assert (E : e = (w64 a, w64 n)) by (apply (entry_same_base _ e (w64 a, w64 n) (lk_mdisj _ _ _ _ _ HL) (lk_mpos _ _ _ _ _ HL) He Hin); exact Hfe).
    subst e. unfold ecov in Hce. cbn [fst snd] in Hce. rewrite !u_w64 in Hce by assumption.
    pose proof (lk_rdisj _ _ _ _ _ HL k r rgk rg Hkr Hk' Hrgx Hl' Hlv) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. fold a n in D.
    clear - Hce D Ho1 Ho2. unfold PGSZ in *. lia. }
  rewrite kstep_munmap. set (rs' := lupd (kf_regions x) r (mkRegion RkMap (rg_len (nth r (kf_regions x) rg_dflt)) [] false)).
  assert (NTH : forall k rgk, nth_error rs' k = Some rgk -> rg_live rgk = true -> k <> r /\ nth_error (kf_regions x) k = Some rgk).
  { intros k rgk H1 H2. exact (nth_dead (kf_regions x) r (mkRegion RkMap (rg_len (nth r (kf_regions x) rg_dflt)) [] false) k rgk eq_refl H1 H2). }
  constructor; cbn [kf_regions kf_areas kf_brk fst snd]; unfold md'; rewrite ?munmap_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_brk vm_start_brk vm_init_sp].
  - rewrite (vm_only_halted _ _ (vm_only_munmap_next _ _ _)). exact (lk_halt _ _ _ _ _ HL).
  - apply munmap_lazy. exact (lk_lazy _ _ _ _ _ HL).
  - exact (lk_top _ _ _ _ _ HL).
  - apply pairwise_filter. exact (lk_mdisj _ _ _ _ _ HL).
  - intros e He. apply In_map_remove in He. exact (lk_mpos _ _ _ _ _ HL e He).
  - intros e He. apply In_map_remove in He. unfold alloc_top. cbn [vm_init_sp]. exact (lk_mtop _ _ _ _ _ HL e He).
  - exact (lk_forb _ _ _ _ _ HL).
  - exact (lk_ctx _ _ _ _ _ HL).
  - intros k rgk Hk1 Hk2. destruct (NTH k rgk Hk1 Hk2) as (_ & H). unfold alloc_top. cbn [vm_init_sp]. exact (lk_rgeo _ _ _ _ _ HL k rgk H Hk2).
  - intros r1 r2 rg1 rg2 Hne H1 H2 L1 L2. destruct (NTH r1 rg1 H1 L1) as (_ & H1'). destruct (NTH r2 rg2 H2 L2) as (_ & H2').
    exact (lk_rdisj _ _ _ _ _ HL r1 r2 rg1 rg2 Hne H1' H2' L1 L2).
  - intros k rgk o Hk1 Hk2 Ho1 Ho2 Ho3. destruct (NTH k rgk Hk1 Hk2) as (Hkr & H).
    destruct (lk_rcov _ _ _ _ _ HL k rgk o H Hk2 Ho1 Ho2 Ho3) as (e & He & Hce).
    exact (covered_remove _ (w64 a) e _ _ He Hce (SURV k rgk o e Hkr H Hk2 Ho1 Ho2 He Hce)).
  - intros k rgk (Hk1 & Hk2 & Hk3). destruct (NTH k rgk Hk1 Hk3) as (Hkr & H).
    pose proof (lk_maps _ _ _ _ _ HL k rgk (conj H (conj Hk2 Hk3))) as Hh.
    apply map_has_In in Hh. apply map_has_In. unfold map_remove. apply filter_In. split; [exact Hh|].
    apply negb_true_iff. cbn [fst]. destruct (bv_eqb (w64 (ly_reg L k)) (w64 a)) eqn:E; [|reflexivity]. exfalso. apply bv_eqb_eq in E.
    destruct (lk_rgeo _ _ _ _ _ HL k rgk H Hk3) as (K1 & K2 & K3 & K4 & K5).
    apply w64_inj in E; [| clear - K1 K3 K5 HTOPB GT; unfold PGSZ in *; lia | exact RA].
    pose proof (lk_rdisj _ _ _ _ _ HL k r rgk rg Hkr H Hrgx Hk3 Hlv) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. fold a n in D. clear - E D K3 G3. lia.
  - intros k rgk (Hk1 & Hk2 & Hk3) o Ho1 Ho2 Ho3 Hnr. destruct (NTH k rgk Hk1 Hk3) as (Hkr & H).
    pose proof (lk_resv _ _ _ _ _ HL k rgk (conj H (conj Hk2 Hk3)) o Ho1 Ho2 Ho3 Hnr) as Hna.
    destruct (lk_rgeo _ _ _ _ _ HL k rgk H Hk3) as (K1 & K2 & K3 & K4 & K5).
    apply map_contains_In in Hna. apply map_contains_In.
    pose proof (lk_rdisj _ _ _ _ _ HL k r rgk rg Hkr H Hrgx Hk3 Hlv) as D. unfold ranges_disjoint in D. cbn [fst snd] in D. fold a n in D.
    assert (U1 : bv_unsigned (w64 (ly_reg L k + o)) = ly_reg L k + o) by (apply u_w64; clear - K1 K5 HTOPB GT Ho1 Ho2; unfold PGSZ in *; lia).
    assert (U2 : bv_unsigned (w64 PGSZ) = PGSZ) by reflexivity.
    rewrite U1, U2 in Hna |- *. rewrite (u_w64 a RA), (u_w64 n RN). clear U1 U2.
    apply ecov_subtract; [clear; unfold PGSZ; lia | clear - D Ho1 Ho2; unfold PGSZ in *; lia | clear - RA; lia | clear - RN; lia | clear - RA RN G5 HTOPB GT; unfold PGSZ in *; lia | exact Hna].
  - intros a' Ha'. destruct (lk_areas _ _ _ _ _ HL a' Ha') as (rga & H1 & H2 & H3 & H4).
    exists rga. split; [|exact (conj H2 (conj H3 H4))]. unfold rs'. rewrite nth_error_lupd.
    destruct (Nat.eqb (prid a') r) eqn:E; [|exact H1]. apply Nat.eqb_eq in E. rewrite E in H1. rewrite H1 in Hrgx. injection Hrgx as ->. contradiction.
  - pose proof (lk_brk _ _ _ _ _ HL) as Hb. revert Hb. destruct (kf_brk x) as [| | r0 p] eqn:Eb; intros Hb.
    + destruct Hb as (Hb1 & Hb2). split; [exact Hb1|]. intros k rgk (Hk1 & Hk2 & Hk3). destruct (NTH k rgk Hk1 Hk3) as (_ & H).
      exact (Hb2 k rgk (conj H (conj Hk2 Hk3))).
    + exact I.
    + destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5). split; [|exact (conj Hb2 (conj Hb3 (conj Hb4 Hb5)))].
      unfold rs'. rewrite nth_error_lupd. destruct (Nat.eqb r0 r) eqn:E; [|exact Hb1]. apply Nat.eqb_eq in E. subst r0.
      rewrite Hb1 in Hrgx. injection Hrgx as <-. discriminate Hk.
  - exact (lk_brk0 _ _ _ _ _ HL).
  - intros aq Haq. unfold na_byte. cbn [kf_regions fst snd].
    rewrite (u_w64 a RA), (u_w64 n RN) in Haq. rewrite MngU.inC_subtract in Haq by (clear - RA RN G5 HTOPB GT; unfold PGSZ in *; lia).
    apply andb_true_iff in Haq as [Hinq _].
    destruct (lk_na _ _ _ _ _ HL aq Hinq) as [((rb & rgb & H1 & H2 & H3 & H4) & Hg)|(rq & rgq & oq & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)].
    + left. split; [|exact Hg]. assert (Hne : rb <> r) by (intros ->; rewrite Hrgx in H1; injection H1 as <-; rewrite Hk in H2; discriminate H2).
      exists rb, rgb. split; [unfold rs'; rewrite nth_lupd_other by exact Hne; exact H1 | exact (conj H2 (conj H3 H4))].
    + right. assert (Hne : rq <> r) by (intros ->; rewrite Hrgx in H1; injection H1 as <-; rewrite Hk in H2; discriminate H2).
      exists rq, rgq, oq. split; [unfold rs'; rewrite nth_lupd_other by exact Hne; exact H1 | exact (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))].
  - intros k rgk (H1 & H2 & H3). destruct (NTH k rgk H1 H3) as (_ & H'). exact (lk_rw _ _ _ _ _ HL k rgk (conj H' (conj H2 H3))).
  - intros k rgk H1 H2. destruct (nth_lupd_cases _ r _ k rgk H1) as [(-> & -> & _)|(_ & H')]; [cbn in H2; discriminate H2|].
    exact (lk_k0 _ _ _ _ _ HL k rgk H' H2).
  - unfold rs'. destruct (rsv_lupd (kf_regions x) r (mkRegion RkMap (rg_len (nth r (kf_regions x) rg_dflt)) [] false) rg Hrgx) as (R1 & R2 & R3).
    destruct (rsv_other rg ltac:(rewrite Hk; discriminate)) as (S1 & S2 & S3).
    destruct (rsv_other (mkRegion RkMap (rg_len (nth r (kf_regions x) rg_dflt)) [] false) ltac:(discriminate)) as (T1 & T2 & T3).
    rewrite R1, R3, S1, S3, T1, T3, !Z.sub_0_r, !Z.add_0_r. exact (lk_k1 _ _ _ _ _ HL).
  - unfold rs'. destruct (rsv_lupd (kf_regions x) r (mkRegion RkMap (rg_len (nth r (kf_regions x) rg_dflt)) [] false) rg Hrgx) as (R1 & R2 & R3).
    destruct (rsv_other rg ltac:(rewrite Hk; discriminate)) as (S1 & S2 & S3).
    destruct (rsv_other (mkRegion RkMap (rg_len (nth r (kf_regions x) rg_dflt)) [] false) ltac:(discriminate)) as (T1 & T2 & T3).
    rewrite R1, R2, R3, S1, S2, S3, T1, T2, T3, !Z.sub_0_r, !Z.add_0_r. exact (lk_k2 _ _ _ _ _ HL).
  - exact (lk_atop _ _ _ _ _ HL).
  - exact (lk_lim _ _ _ _ _ HL).
  - exact (lk_rsz _ _ _ _ _ HL).
Qed.

#[using="Type"] Lemma guard_vmmaps : forall a n md, m_vmmaps (fixed_na_next (w64 50) a n md) =
  mkVmMapsFull (vm_reserved (m_vmmaps md)) (vm_maps (m_vmmaps md))
    ((a, n) :: maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
    (vm_start_brk (m_vmmaps md)) (vm_brk (m_vmmaps md)) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md)).
Proof. LiaFast.lf_pins LiaFast.u0. intros. reflexivity. Qed.

#[using="Type"] Lemma guard_lazy : forall a n md, m_vm_lazy md = [] -> m_vm_lazy (fixed_na_next (w64 50) a n md) = [].
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a n md H. unfold fixed_na_next, with_mmap_replacement, with_mmap_backing. cbn.
  unfold vm_forget_range, with_vm_backing, with_vmmaps, m_vm_lazy in *. cbn. rewrite H. reflexivity.
Qed.

#[using="Type"] Lemma kstep_guard : forall x r p, kf_brk x = BrkCur r p -> kstep x KGuard 1 = (kf_regions x, kf_brk x, kf_areas x ++ [SP r PGSZ]).
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] r p E. cbn in E. subst b. reflexivity. Qed.

#[using="Hoff ob_guard"] Lemma case_guard : node_ok KGuard.
Proof. LiaFast.lf_pins (fun (Hoff ob_guard : LiaFast.U) => LiaFast.u0).
  intros L x md B s regs pc m K Hec Hx Hrq HL HB Hc Hcont.
  destruct Hrq as (r & rg & Hbrk & Hlen' & Hrg & Hk & Hlen & HA).
  assert (Hbx : kf_brk x = BrkCur r 2) by (subst x; exact Hbrk).
  pose proof (lk_brk' L x md HL) as Hb. unfold brk_clause in Hb. rewrite Hbx in Hb.
  destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5).
  destruct (Hb5 ltac:(subst x; exact HA)) as (_ & RFR).
  destruct (lk_rgeo _ _ _ _ _ HL r _ Hb1 eq_refl) as (G1 & G2 & G3 & G4 & G5). cbn [rg_len] in G3, G4, G5.
  pose proof (alloc_top_lt (m_vmmaps md)) as AT.
  assert (EB : brk_base L s = ly_brk0 L) by (unfold brk_base; rewrite Hbrk; exact Hb3).
  assert (MC : map_contains (vm_maps (m_vmmaps md)) (w64 (ly_brk0 L)) (w64 PGSZ) = true).
  { destruct (lk_rcov _ _ _ _ _ HL r _ 0 Hb1 eq_refl ltac:(lia) ltac:(cbn [rg_len]; unfold PGSZ; lia) eq_refl) as (e & He & Hce).
    apply map_contains_In. exists e. split; [exact He|]. rewrite Hb3, Z.add_0_r in Hce.
    rewrite !u_w64 by (clear - G1 G5 AT Hb3; rewrite Hb3 in *; unfold two_pow_64, PGSZ in *; lia). exact Hce. }
  assert (P1 : brk_base L s mod PGSZ = 0) by (rewrite EB, <- Hb3; exact G2).
  assert (P2 : 0 < brk_base L s) by (rewrite EB, <- Hb3; clear - G1; unfold PGSZ in *; lia).
  assert (P3 : brk_base L s + PGSZ <= alloc_top (m_vmmaps md)) by (rewrite EB, <- Hb3; clear - G5; unfold PGSZ in *; lia).
  assert (P4 : region_free (vm_reserved (m_vmmaps md)) (w64 (brk_base L s)) (w64 PGSZ)
                 && map_contains (vm_maps (m_vmmaps md)) (w64 (brk_base L s)) (w64 PGSZ) = true) by (rewrite EB, RFR, MC; reflexivity).
  apply (rz_guard segs cfg Hoff rom L s regs pc m md K Hec (lk_halt _ _ _ _ _ HL) (lk_lazy _ _ _ _ _ HL) P1 P2 P3 P4).
  apply (Hcont _ 1 L _ (o_guard FORB HTOP L s) (vm_only_fixed_na_next _ _ _ _)).
  2: { exact (ob_guard L x md B (brk_base L s) HL HB Hc ltac:(clear - P2; lia) ltac:(clear - P3 AT; unfold two_pow_64 in *; lia)). }
  rewrite (kstep_guard x r 2 Hbx). rewrite EB.
  set (a := ly_brk0 L) in *.
  assert (UA : bv_unsigned (w64 a) = a) by (apply u_w64; clear - G1 G5 AT Hb3; rewrite Hb3 in *; unfold two_pow_64, PGSZ in *; lia).
  constructor; cbn [kf_regions kf_areas kf_brk fst snd]; rewrite ?guard_vmmaps; cbn [vm_reserved vm_maps vm_noaccess vm_brk vm_start_brk vm_init_sp].
  - rewrite (vm_only_halted _ _ (vm_only_fixed_na_next _ _ _ _)). exact (lk_halt _ _ _ _ _ HL).
  - apply guard_lazy. exact (lk_lazy _ _ _ _ _ HL).
  - exact (lk_top _ _ _ _ _ HL).
  - exact (lk_mdisj _ _ _ _ _ HL).
  - exact (lk_mpos _ _ _ _ _ HL).
  - exact (lk_mtop _ _ _ _ _ HL).
  - exact (lk_forb _ _ _ _ _ HL).
  - exact (lk_ctx _ _ _ _ _ HL).
  - exact (lk_rgeo _ _ _ _ _ HL).
  - exact (lk_rdisj _ _ _ _ _ HL).
  - exact (lk_rcov _ _ _ _ _ HL).
  - exact (lk_maps _ _ _ _ _ HL).
  - intros k rgk (H1 & H2 & H3) o Ho1 Ho2 Ho3 Hnr. apply map_contains_In.
    pose proof (lk_resv _ _ _ _ _ HL k rgk (conj H1 (conj H2 H3)) o Ho1 Ho2 Ho3 Hnr) as Hna. apply map_contains_In in Hna.
    destruct (lk_rgeo _ _ _ _ _ HL k rgk H1 H3) as (K1 & K2 & K3 & K4 & K5).
    assert (UK : bv_unsigned (w64 (ly_reg L k + o)) = ly_reg L k + o) by (apply u_w64; clear - K1 K5 AT Ho1 Ho2; unfold two_pow_64, PGSZ in *; lia).
    assert (UP : bv_unsigned (w64 PGSZ) = PGSZ) by reflexivity.
    rewrite UK, UP in Hna |- *. rewrite UA.
    assert (Hkr : k <> r) by (intros ->; rewrite Hb1 in H1; injection H1 as <-; discriminate H2).
    pose proof (lk_rdisj _ _ _ _ _ HL k r rgk _ Hkr H1 Hb1 H3 eq_refl) as D. unfold ranges_disjoint in D. cbn [fst snd rg_len] in D. rewrite Hb3 in D.
    assert (EX : exists e', In e' (maps_subtract (vm_noaccess (m_vmmaps md)) a (a + PGSZ)) /\ ecov e' (ly_reg L k + o) PGSZ).
    { apply ecov_subtract.
      + clear. unfold PGSZ. lia.
      + clear - D Ho1 Ho2. unfold PGSZ in *. lia.
      + clear - G1 Hb3. rewrite Hb3 in G1. unfold a, PGSZ in *. lia.
      + clear. unfold PGSZ. lia.
      + clear - G5 AT Hb3. rewrite Hb3 in G5. unfold a, two_pow_64, PGSZ in *. lia.
      + exact Hna. }
    destruct EX as (e' & He' & Hce'). exists e'. split; [right; exact He' | exact Hce'].
  - intros a' Ha'. apply in_app_iff in Ha' as [Ha'|[<-|[]]]; [exact (lk_areas _ _ _ _ _ HL a' Ha')|].
    exists (mkRegion RkBrk (PGSZ * 2) [] true). split; [exact Hb1|]. cbn. split; [reflexivity|]. split; [discriminate|]. unfold PGSZ. lia.
  - rewrite Hbx. split; [exact Hb1|]. split; [exact Hb2|]. split; [exact Hb3|]. split; [exact Hb4|].
    intros HA'. apply Forall_app in HA' as [_ HA']. inversion HA' as [|y l Hy _]. cbn in Hy. exfalso. exact (Hy eq_refl).
  - exact (lk_brk0 _ _ _ _ _ HL).
  - intros aq Haq. unfold MngU.inC in Haq. cbn [existsb fst snd] in Haq. apply orb_true_iff in Haq as [Hg|Hold].
    + left. split; [exists r, (mkRegion RkBrk (PGSZ * 2) [] true); split; [exact Hb1|]; split; [reflexivity|]; split; [reflexivity | exact Hb3]|].
      fold a. rewrite UA in Hg. change (bv_unsigned (w64 PGSZ)) with PGSZ in Hg. unfold MngU.inI in Hg.
      apply andb_true_iff in Hg as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
    + fold (MngU.inC (maps_subtract (vm_noaccess (m_vmmaps md)) (bv_unsigned (w64 a)) (bv_unsigned (w64 a) + bv_unsigned (w64 PGSZ))) aq) in Hold.
      rewrite UA in Hold. change (bv_unsigned (w64 PGSZ)) with PGSZ in Hold.
      rewrite MngU.inC_subtract in Hold by (clear - G1 G5 AT Hb3; rewrite Hb3 in *; unfold a, two_pow_64, PGSZ in *; lia).
      apply andb_true_iff in Hold as [Hin _]. exact (lk_na _ _ _ _ _ HL aq Hin).
  - exact (lk_rw _ _ _ _ _ HL).
  - exact (lk_k0 _ _ _ _ _ HL).
  - exact (lk_k1 _ _ _ _ _ HL).
  - exact (lk_k2 _ _ _ _ _ HL).
  - exact (lk_atop _ _ _ _ _ HL).
  - exact (lk_lim _ _ _ _ _ HL).
  - exact (lk_rsz _ _ _ _ _ HL).
Qed.

#[using="Type"] Lemma page_round_up_aligned : forall x, x mod PGSZ = 0 -> page_round_up_Z x = x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x H. unfold page_round_up_Z, page_size. unfold PGSZ in H. assert (Q := Z.div_mod x 4096 ltac:(lia)). rewrite H, Z.add_0_r in Q.
  rewrite Q. replace (4096 * (x / 4096) + 4096 - 1) with (4095 + (x / 4096) * 4096) by ring.
  rewrite Z.div_add by lia. rewrite (Z.div_small 4095 4096) by lia. ring.
Qed.

#[using="Type"] Lemma w64_sub : forall a b, 0 <= b <= a -> a < 2 ^ 64 -> (w64 a - w64 b)%bv = w64 (a - b).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros a b H1 H2. apply bv_eq. rewrite bv_sub_unsigned. rewrite !u_w64 by lia. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Section BrkDec.
Variables (md : Model) (cur req : Z).
Hypothesis Hv : vm_brk (m_vmmaps md) = w64 cur.
Hypothesis Hc0 : PGSZ <= cur.
Hypothesis Hcr : cur < req.
Hypothesis Hr64 : req + PGSZ < 2 ^ 64.
Hypothesis Hal : cur mod PGSZ = 0.
Hypothesis Har : req mod PGSZ = 0.

#[using="Hv Hc0 Hcr Hr64 Hal Har"] Lemma brk_grow_ok_dec : brk_grow_ok md (w64 req) (w64 req) = true ->
  req <= alloc_top (m_vmmaps md) /\
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 cur) (w64 (req + PGSZ - cur)) = true.
Proof. LiaFast.lf_pins (fun (Hv Hc0 Hcr Hr64 Hal Har : LiaFast.U) => LiaFast.u0).
  intros H. unfold brk_grow_ok in H. rewrite Hv in H. rewrite !u_w64 in H by (unfold PGSZ in *; lia).
  replace (0 <? cur) with true in H by (symmetry; apply Z.ltb_lt; unfold PGSZ in *; lia).
  replace (cur <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  rewrite !page_round_up_aligned in H by assumption. cbn [andb] in H.
  replace (cur <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_true_iff in H as [H _]. apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1.
  split; [exact H1|]. unfold page_size in H2. unfold PGSZ. exact H2.
Qed.

#[using="Hv Hc0 Hcr Hr64 Hal Har"] Lemma brk_eff_dec : brk_eff (w64 req) (w64 req) (vm_brk (m_vmmaps md)) = mkEffect (w64 req) [] [(w64 cur, w64 (req - cur))].
Proof. LiaFast.lf_pins (fun (Hv Hc0 Hcr Hr64 Hal Har : LiaFast.U) => LiaFast.u0).
  rewrite Hv. unfold brk_eff, brk_zeros, brk_unmaps, brk_is_grow, brk_page_range. rewrite !u_w64 by (unfold PGSZ in *; lia).
  rewrite !page_round_up_aligned by assumption.
  replace (w_is0 (w64 req)) with false by (symmetry; apply w_is0_w64; unfold PGSZ in *; lia).
  replace (0 <? cur) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ in *; lia).
  replace (cur <? req) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (req <? cur) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

#[using="Hv Hc0 Hcr Hr64 Hal Har"] Lemma brk_next_vmmaps : m_vmmaps (with_brk_next md (w64 req) (w64 req)) =
  mkVmMapsFull (vm_reserved (m_vmmaps md)) ((w64 cur, w64 (req - cur)) :: vm_maps (m_vmmaps md)) (vm_noaccess (m_vmmaps md))
    (vm_start_brk (m_vmmaps md)) (w64 req) (vm_limit (m_vmmaps md)) (vm_mmap_base (m_vmmaps md)) (vm_init_sp (m_vmmaps md)).
Proof. LiaFast.lf_pins (fun (Hv Hc0 Hcr Hr64 Hal Har : LiaFast.U) => LiaFast.u0).
  unfold with_brk_next, brk_model_next, brk_maps_next, brk_grants, brk_is_grow, brk_unmaps, brk_page_range, maps_subtract_ranges.
  rewrite Hv. rewrite !u_w64 by (unfold PGSZ in *; lia). rewrite !page_round_up_aligned by assumption.
  replace (w_is0 (w64 req)) with false by (symmetry; apply w_is0_w64; unfold PGSZ in *; lia).
  replace (0 <? cur) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ in *; lia).
  replace (cur <? req) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (req <? cur) with false by (symmetry; apply Z.ltb_ge; lia). cbn.
  rewrite w64_sub by (unfold PGSZ in *; lia). reflexivity.
Qed.

#[using="cur Hv Hc0 Hcr Hr64 Hal Har"] Lemma brk_next_lazy : m_vm_lazy (with_brk_next md (w64 req) (w64 req)) = m_vm_lazy md.
Proof. LiaFast.lf_pins (fun (cur Hv Hc0 Hcr Hr64 Hal Har : LiaFast.U) => LiaFast.u0).
  unfold with_brk_next, brk_unmaps, brk_page_range. rewrite Hv. rewrite !u_w64 by (unfold PGSZ in *; lia). rewrite !page_round_up_aligned by assumption.
  replace (0 <? cur) with true by (symmetry; apply Z.ltb_lt; unfold PGSZ in *; lia).
  replace (req <? cur) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End BrkDec.

#[using="rom"] Lemma region_free_mono : forall l lo n n', region_free l lo n = true -> bv_unsigned n' <= bv_unsigned n -> region_free l lo n' = true.
Proof. LiaFast.lf_pins (fun (rom : LiaFast.U) => LiaFast.u0).
  induction l as [|[a sz] t IH]; intros lo n n' H Hn; cbn in *; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply andb_true_iff. split; [|exact (IH lo n n' H2 Hn)].
  apply negb_true_iff in H1. apply negb_true_iff. apply iv_overlap_false in H1. unfold iv_overlap. apply andb_false_iff.
  destruct H1 as [H1|H1]; [right | left]; apply Z.ltb_ge; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma link_dead : forall L x md, LINK HTOP FORB L x md -> LINK HTOP FORB L (kf_regions x, BrkDead, kf_areas x) md.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md HL. destruct HL as [A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16].
  constructor; cbn [kf_regions kf_areas kf_brk fst snd]; assumption || exact I.
Qed.

#[using="Type"] Lemma kstep_brk_never : forall x n z, kf_brk x = BrkNever -> z <> 0 ->
  kstep x (KBrkGrow n) z = (kf_regions x ++ [mkRegion RkBrk (2 * PGSZ) [] true], BrkCur (length (kf_regions x)) 2, kf_areas x).
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] n z E Hz. cbn in E. subst b. cbn. rewrite (proj2 (Z.eqb_neq z 0) Hz). reflexivity. Qed.

#[using="Type"] Lemma kstep_brk_cur : forall x n z r p, kf_brk x = BrkCur r p -> z <> 0 ->
  kstep x (KBrkGrow n) z = (lupd (kf_regions x) r (mkRegion RkBrk (rg_len (nth r (kf_regions x) rg_dflt) + PGSZ) [] true),
                            BrkCur r (p + 1), kf_areas x ++ [SP r (PGSZ * p)]).
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] n z r p E Hz. cbn in E. subst b. cbn. rewrite (proj2 (Z.eqb_neq z 0) Hz). reflexivity. Qed.

#[using="Type"] Lemma kstep_brk0 : forall x n, kstep x (KBrkGrow n) 0 = (kf_regions x, BrkDead, kf_areas x).
Proof. LiaFast.lf_pins LiaFast.u0. intros [[rs b] ars] n. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma link_brk_grow : forall L x md md' r p,
  LINK HTOP FORB L x md -> kf_brk x = BrkCur r p ->
  region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 (ly_brk0 L + PGSZ * p)) (w64 PGSZ) = true ->
  ly_brk0 L + PGSZ * p + PGSZ <= alloc_top (m_vmmaps md) ->
  m_halted md' = m_halted md -> m_vm_lazy md' = m_vm_lazy md ->
  vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md) ->
  vm_maps (m_vmmaps md') = (w64 (ly_brk0 L + PGSZ * p), w64 PGSZ) :: vm_maps (m_vmmaps md) ->
  vm_noaccess (m_vmmaps md') = vm_noaccess (m_vmmaps md) ->
  bv_unsigned (vm_brk (m_vmmaps md')) = ly_brk0 L + PGSZ * (p + 1) ->
  vm_start_brk (m_vmmaps md') = vm_start_brk (m_vmmaps md) -> vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md) ->
  vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md) ->
  LINK HTOP FORB L (lupd (kf_regions x) r (mkRegion RkBrk (rg_len (nth r (kf_regions x) rg_dflt) + PGSZ) [] true),
                    BrkCur r (p + 1), kf_areas x ++ [SP r (PGSZ * p)]) md'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros L x md md' r p HL Hbx Hf Htop E1 E2 E3 E4 E5 E6 E7 E8 E9.
  pose proof (lk_brk' L x md HL) as Hb. unfold brk_clause in Hb. rewrite Hbx in Hb. destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5).
  set (rs := kf_regions x) in *. set (a := ly_brk0 L) in *.
  rewrite (nth_of_nth_error _ r _ rg_dflt Hb1). cbn [rg_len].
  set (rg' := mkRegion RkBrk (PGSZ * p + PGSZ) [] true). set (rs' := lupd rs r rg').
  destruct (lk_rgeo _ _ _ _ _ HL r _ Hb1 eq_refl) as (G1 & G2 & G3 & G4 & G5). cbn [rg_len] in G3, G4, G5. rewrite Hb3 in G1, G2, G5.
  pose proof (alloc_top_lt (m_vmmaps md)) as AT.
  assert (RC : 0 <= a + PGSZ * p /\ a + PGSZ * p + PGSZ < 2 ^ 64) by (clear - G1 Htop AT Hb2; unfold two_pow_64, PGSZ in *; lia).
  assert (RSR : nth_error rs' r = Some rg') by exact (nth_lupd_same _ r rg' _ Hb1).
  assert (NTH : forall k rgk, nth_error rs' k = Some rgk -> (k = r /\ rgk = rg') \/ (k <> r /\ nth_error rs k = Some rgk)).
  { intros k rgk H. destruct (nth_lupd_cases _ r rg' k rgk H) as [(-> & -> & _)|H']; [left; split; reflexivity | right; exact H']. }
  (* [comment removed for export] *)
  assert (FRESHR : forall k rgk, k <> r -> nth_error rs k = Some rgk -> rg_live rgk = true ->
            ranges_disjoint (a + PGSZ * p, PGSZ) (ly_reg L k, rg_len rgk)).
  { intros k rgk Hkr H1 H2. destruct (lk_rgeo _ _ _ _ _ HL k rgk H1 H2) as (K1 & K2 & K3 & K4 & K5).
    apply pages_disj; [unfold PGSZ; lia | exact K3 | exact K2 | exact K4|]. intros o Ho1 Ho2 Ho3.
    destruct (lk_rcov _ _ _ _ _ HL k rgk o H1 H2 Ho1 Ho2 Ho3) as (e & He & Hc).
    pose proof (rf_disj _ _ _ e _ _ Hf ltac:(apply in_or_app; right; exact He) Hc) as D. rewrite !u_w64 in D by (clear - RC; unfold PGSZ in *; lia). exact D. }
  constructor; cbn [kf_regions kf_areas kf_brk fst snd].
  - rewrite E1. exact (lk_halt _ _ _ _ _ HL).
  - rewrite E2. exact (lk_lazy _ _ _ _ _ HL).
  - unfold alloc_top in *. rewrite E8. exact (lk_top _ _ _ _ _ HL).
  - rewrite E4. split; [|exact (lk_mdisj _ _ _ _ _ HL)]. intros [a' sz] Hy. unfold edisj. cbn [fst snd].
    exact (region_free_In _ _ _ a' sz Hf ltac:(apply in_or_app; right; exact Hy)).
  - rewrite E4. intros e [<-|He]; [reflexivity | exact (lk_mpos _ _ _ _ _ HL e He)].
  - rewrite E4. unfold alloc_top. rewrite E8. fold (alloc_top (m_vmmaps md)). intros e [<-|He]; [cbn [fst snd]; rewrite !u_w64 by (clear - RC; unfold PGSZ in *; lia); exact Htop | exact (lk_mtop _ _ _ _ _ HL e He)].
  - unfold rcovered. rewrite E3. exact (lk_forb _ _ _ _ _ HL).
  - unfold rcovered. rewrite E3. exact (lk_ctx _ _ _ _ _ HL).
  - intros k rgk H1 H2. unfold alloc_top. rewrite E8. fold (alloc_top (m_vmmaps md)). destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')].
    + unfold rg'. cbn [rg_len]. rewrite Hb3. split; [exact G1|]. split; [exact G2|]. split; [clear - Hb2; unfold PGSZ in *; lia|].
      split; [apply mod_add0; [rewrite Z.mul_comm; apply Z.mod_mul; unfold PGSZ; lia | reflexivity] | clear - Htop; lia].
    + exact (lk_rgeo _ _ _ _ _ HL k rgk H' H2).
  - intros r1 r2 rg1 rg2 Hne H1 H2 L1 L2.
    destruct (NTH r1 rg1 H1) as [(-> & ->)|(Hr1 & H1')]; destruct (NTH r2 rg2 H2) as [(-> & ->)|(Hr2 & H2')].
    + exfalso. exact (Hne eq_refl).
    + pose proof (lk_rdisj _ _ _ _ _ HL r r2 _ rg2 Hne Hb1 H2' eq_refl L2) as D. pose proof (FRESHR r2 rg2 Hr2 H2' L2) as D2.
      destruct (lk_rgeo _ _ _ _ _ HL r2 rg2 H2' L2) as (_ & _ & K3 & _ & _).
      unfold rg', ranges_disjoint in *. cbn [fst snd rg_len] in *. rewrite Hb3 in D |- *. clear - D D2 K3. unfold PGSZ in *. lia.
    + pose proof (lk_rdisj _ _ _ _ _ HL r1 r rg1 _ Hne H1' Hb1 L1 eq_refl) as D. pose proof (FRESHR r1 rg1 Hr1 H1' L1) as D2.
      destruct (lk_rgeo _ _ _ _ _ HL r1 rg1 H1' L1) as (_ & _ & K3 & _ & _).
      unfold rg', ranges_disjoint in *. cbn [fst snd rg_len] in *. rewrite Hb3 in D |- *. clear - D D2 K3. unfold PGSZ in *. lia.
    + exact (lk_rdisj _ _ _ _ _ HL r1 r2 rg1 rg2 Hne H1' H2' L1 L2).
  - intros k rgk o H1 H2 Ho1 Ho2 Ho3. rewrite E4. destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')].
    + unfold rg' in Ho2. cbn [rg_len] in Ho2. rewrite Hb3. destruct (Z_lt_le_dec o (PGSZ * p)) as [Hlt|Hge].
      * assert (Ho2' : o + PGSZ <= PGSZ * p).
        { clear - Hlt Ho3 Ho1. unfold PGSZ in *. assert (Q := Z.div_mod o 4096 ltac:(lia)). rewrite Ho3, Z.add_0_r in Q.
          assert (o / 4096 < p) by (apply Z.div_lt_upper_bound; lia). lia. }
        destruct (lk_rcov _ _ _ _ _ HL r _ o Hb1 eq_refl Ho1 ltac:(cbn [rg_len]; exact Ho2') Ho3) as (e & He & Hce).
        exists e. split; [right; exact He|]. rewrite Hb3 in Hce. exact Hce.
      * exists (w64 (a + PGSZ * p), w64 PGSZ). split; [left; reflexivity|]. apply ecov_w64; [clear - RC; unfold PGSZ in *; lia | clear; unfold PGSZ; lia | clear - Hge; unfold PGSZ in *; lia | clear - Ho2; unfold PGSZ in *; lia].
    + destruct (lk_rcov _ _ _ _ _ HL k rgk o H' H2 Ho1 Ho2 Ho3) as (e & He & Hce). exists e. split; [right; exact He | exact Hce].
  - intros k rgk (H1 & H2 & H3). rewrite E4. destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')]; [cbn in H2; discriminate|].
    apply map_has_In. right. apply map_has_In. exact (lk_maps _ _ _ _ _ HL k rgk (conj H' (conj H2 H3))).
  - intros k rgk (H1 & H2 & H3) o Ho1 Ho2 Ho3 Hnr. rewrite E5. destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')]; [cbn in H2; discriminate|].
    exact (lk_resv _ _ _ _ _ HL k rgk (conj H' (conj H2 H3)) o Ho1 Ho2 Ho3 Hnr).
  - intros a' Ha'. apply in_app_iff in Ha' as [Ha'|[<-|[]]].
    + destruct (lk_areas _ _ _ _ _ HL a' Ha') as (rga & H1 & H2 & H3 & H4). fold rs in H1. destruct (Nat.eq_dec (prid a') r) as [E|E].
      * rewrite E in H1 |- *. rewrite Hb1 in H1. injection H1 as <-. exists rg'. split; [exact RSR|]. cbn in *. split; [reflexivity|].
        split; [discriminate|]. clear - H4. unfold PGSZ in *. lia.
      * exists rga. split; [unfold rs'; rewrite nth_lupd_other by exact E; exact H1 | auto].
    + exists rg'. split; [exact RSR|]. cbn. split; [reflexivity|]. split; [discriminate|]. split; [clear - G3; unfold PGSZ in *; lia|].
      split; [lia | rewrite Z.mul_comm; apply Z.mod_mul; unfold PGSZ; lia].
  - cbn. split; [replace (PGSZ * (p + 1)) with (PGSZ * p + PGSZ) by ring; exact RSR|]. split; [clear - Hb2; lia|].
    split; [exact Hb3|]. split; [exact E6|]. intros HA. apply Forall_app in HA as [_ HA]. inversion HA as [|y l Hy _]. cbn in Hy. exfalso. exact (Hy eq_refl).
  - destruct (lk_brk0 _ _ _ _ _ HL) as (B1 & B2 & B3 & B4). split; [exact B1|]. split; [exact B2|]. split; [|exact B4]. unfold min_brk in *. rewrite E7. exact B3.
  - intros aq Haq. rewrite E5 in Haq. unfold na_byte. cbn [kf_regions fst snd].
    destruct (lk_na _ _ _ _ _ HL aq Haq) as [((rb & rgb & H1 & H2 & H3 & H4) & Hg)|(rq & rgq & oq & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8)].
    + left. split; [|exact Hg]. destruct (Nat.eq_dec rb r) as [->|Hne].
      * exists r, rg'. split; [exact RSR|]. split; [reflexivity|]. split; [reflexivity|]. exact H4.
      * exists rb, rgb. split; [unfold rs'; rewrite nth_lupd_other by exact Hne; exact H1 | exact (conj H2 (conj H3 H4))].
    + right. assert (Hne : rq <> r) by (intros ->; fold rs in H1; rewrite Hb1 in H1; injection H1 as <-; discriminate H2).
      exists rq, rgq, oq. split; [unfold rs'; rewrite nth_lupd_other by exact Hne; exact H1 | exact (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 H8))))))].
  - intros k rgk (H1 & H2 & H3). destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')]; [cbn in H2; discriminate H2|].
    exact (lk_rw _ _ _ _ _ HL k rgk (conj H' (conj H2 H3))).
  - intros k rgk H1 H2. destruct (NTH k rgk H1) as [(-> & ->)|(_ & H')]; [cbn in H2; discriminate H2|]. exact (lk_k0 _ _ _ _ _ HL k rgk H' H2).
  - unfold rs'. destruct (rsv_lupd rs r rg' _ Hb1) as (R1 & R2 & R3).
    destruct (rsv_other (mkRegion RkBrk (PGSZ * p) [] true) ltac:(discriminate)) as (S1 & S2 & S3).
    destruct (rsv_other rg' ltac:(discriminate)) as (T1 & T2 & T3).
    rewrite R1, R3, S1, S3, T1, T3, !Z.sub_0_r, !Z.add_0_r. exact (lk_k1 _ _ _ _ _ HL).
  - unfold rs'. destruct (rsv_lupd rs r rg' _ Hb1) as (R1 & R2 & R3).
    destruct (rsv_other (mkRegion RkBrk (PGSZ * p) [] true) ltac:(discriminate)) as (S1 & S2 & S3).
    destruct (rsv_other rg' ltac:(discriminate)) as (T1 & T2 & T3).
    rewrite R1, R2, R3, S1, S2, S3, T1, T2, T3, !Z.sub_0_r, !Z.add_0_r. exact (lk_k2 _ _ _ _ _ HL).
  - unfold alloc_top. rewrite E8. exact (lk_atop _ _ _ _ _ HL).
  - rewrite E9. exact (lk_lim _ _ _ _ _ HL).
  - rewrite E3. exact (lk_rsz _ _ _ _ _ HL).
Qed.

#[using="Hoff HTOPB ob_brk_refuse ob_brk_grant"] Lemma case_brk : forall n, node_ok (KBrkGrow n).
Proof. LiaFast.lf_pins (fun (Hoff HTOPB ob_brk_refuse ob_brk_grant : LiaFast.U) => LiaFast.u0).
  intros n L x md B s regs pc m K Hec Hx Hrq HL HB Hc Hcont.
  pose proof (lk_brk' L x md HL) as Hb. pose proof (lk_brk0 _ _ _ _ _ HL) as (B1 & B2 & B3 & B4).
  pose proof (alloc_top_lt (m_vmmaps md)) as AT. pose proof (lk_top _ _ _ _ _ HL) as GT.
  set (cur := brk_cur L s).
  destruct Hrq as [(Hn & Hbrk & Hbr) | (Hn & r & p & rg & Hbrk & Hrg & Hk & Hlv & Hlen)].
  - (* [comment removed for export] *)
    subst n. assert (Hbx : kf_brk x = BrkNever) by (subst x; exact Hbrk).
    unfold brk_clause in Hb. rewrite Hbx in Hb. destruct Hb as (Hb1 & Hb2).
    assert (Ec : cur = ly_brk0 L) by (unfold cur, brk_cur; rewrite Hbrk; reflexivity).
    assert (Hv : vm_brk (m_vmmaps md) = w64 cur) by (rewrite Ec; exact (w64_of_u _ _ Hb1)).
    assert (R1 : 0 < cur + PGSZ * 2 < 2 ^ 64) by (rewrite Ec; clear - B1 B4 HTOPB; unfold PGSZ in *; lia).
    assert (R2 : bv_unsigned (min_brk (m_vmmaps md)) <= cur + PGSZ * 2) by (rewrite Ec; clear - B3; unfold PGSZ in *; lia).
    assert (R3 : bv_unsigned (vm_brk (m_vmmaps md)) < cur + PGSZ * 2) by (rewrite Hb1, <- Ec; clear; unfold PGSZ; lia).
    apply (rz_brk_grow segs cfg Hoff rom L s 2 regs pc m md K Hec (lk_halt _ _ _ _ _ HL) (lk_lazy _ _ _ _ _ HL)
             ltac:(fold cur; exact R1) ltac:(fold cur; exact R2) ltac:(fold cur; exact R3)); fold cur.
    + intros Hg. rewrite Ec in Hv, Hg |- *.
      set (a := ly_brk0 L) in *.
      destruct (brk_grow_ok_dec md a (a + PGSZ * 2) Hv B1 ltac:(clear; unfold PGSZ; lia) ltac:(clear - B4 HTOPB; unfold PGSZ in *; lia) B2
                  ltac:(apply mod_add0; [exact B2 | reflexivity]) Hg) as (Htop & Hf).
      rewrite (brk_eff_dec md a (a + PGSZ * 2) Hv B1 ltac:(clear; unfold PGSZ; lia) ltac:(clear - B4 HTOPB; unfold PGSZ in *; lia) B2
                  ltac:(apply mod_add0; [exact B2 | reflexivity])).
      replace (a + PGSZ * 2 - a) with (PGSZ * 2) by ring.
      assert (Hf2 : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 a) (w64 (PGSZ * 2)) = true).
      { apply (region_free_mono _ _ _ _ Hf). rewrite !u_w64 by (clear - B4 HTOPB; unfold PGSZ in *; lia). clear. unfold PGSZ. lia. }
      assert (FR : fresh_range FORB HTOP L s (brk_cur L s) (PGSZ * 2)).
      { fold cur. rewrite Ec. apply (fresh_of_free L x md s a (PGSZ * 2) HL Hx Hf2 B1 B2 ltac:(clear; unfold PGSZ; lia) Htop). }
      assert (EK := o_brk_grant FORB HTOP L s 2 FR). rewrite Hbrk in EK. fold cur in EK. rewrite Ec in EK.
      apply (Hcont _ 1 _ _ EK (vm_only_with_brk_next _ _ _)).
      2: { exact (ob_brk_grant L x md B 2 a HL HB Hc Hv B1 B2 ltac:(lia) ltac:(clear - B4 HTOPB; unfold PGSZ in *; lia)). }
      rewrite (kstep_brk_never x 2 1 Hbx ltac:(discriminate)). subst x. cbn [kf_of kf_regions kf_areas fst snd] in *.
      assert (VM := brk_next_vmmaps md a (a + PGSZ * 2) Hv B1 ltac:(clear; unfold PGSZ; lia) ltac:(clear - B4 HTOPB; unfold PGSZ in *; lia) B2
                  ltac:(apply mod_add0; [exact B2 | reflexivity])).
      replace (a + PGSZ * 2 - a) with (PGSZ * 2) in VM by ring.
      apply (link_new_region L (kf_of s) md _ a (PGSZ * 2) RkBrk (BrkCur (length (st_regions s)) 2) HL Hf2 B1 B2
               ltac:(clear; unfold PGSZ; lia) ltac:(rewrite Z.mul_comm; apply Z.mod_mul; unfold PGSZ; lia) Htop).
      * exact (vm_only_halted _ _ (vm_only_with_brk_next _ _ _)).
      * exact (brk_next_lazy md a (a + PGSZ * 2) Hv B1 ltac:(clear; unfold PGSZ; lia) ltac:(clear - B4 HTOPB; unfold PGSZ in *; lia) B2
                  ltac:(apply mod_add0; [exact B2 | reflexivity])).
      * rewrite VM. reflexivity.
      * rewrite VM. reflexivity.
      * rewrite VM. reflexivity.
      * rewrite VM. reflexivity.
      * rewrite VM. reflexivity.
      * intros o _ _ _ E. discriminate E.
      * intros r rg Hr o Ho1 Ho2 Ho3 Hnr. rewrite VM. exact (lk_resv _ _ _ _ _ HL r rg Hr o Ho1 Ho2 Ho3 Hnr).
      * unfold brk_clause. rewrite VM. cbn [vm_brk vm_reserved].
        split; [rewrite nth_error_app2 by (apply Nat.le_refl); rewrite Nat.sub_diag; reflexivity|]. split; [clear; lia|].
        split; [apply ly_reg_set_same|]. split; [rewrite u_w64 by (clear - B1 B4 HTOPB; unfold PGSZ in *; lia); reflexivity|].
        intros _. split; [reflexivity|]. apply region_free_app in Hf2 as (Hf3 & _).
        apply (region_free_mono _ _ _ _ Hf3). rewrite !u_w64 by (clear; unfold PGSZ; lia). clear. unfold PGSZ. lia.
      * intros aq Haq. left. rewrite VM in Haq. exact Haq.
      * exact (kk_other L (kf_of s) md RkBrk (PGSZ * 2) [] true HL ltac:(discriminate)).
    + intros Hg. rewrite Hv. rewrite Ec.
      assert (EK := o_brk_refuse FORB HTOP L s 2). fold cur in EK. rewrite Ec in EK.
      apply (Hcont _ 0 _ _ EK (vm_only_refl md)).
      * rewrite kstep_brk0. exact (link_dead L x md HL).
      * exact (ob_brk_refuse L x md B 2 HL HB Hc).
  - (* [comment removed for export] *)
    subst n. assert (Hbx : kf_brk x = BrkCur r p) by (subst x; exact Hbrk).
    unfold brk_clause in Hb. rewrite Hbx in Hb. destruct Hb as (Hb1 & Hb2 & Hb3 & Hb4 & Hb5).
    destruct (lk_rgeo _ _ _ _ _ HL r _ Hb1 eq_refl) as (G1 & G2 & G3 & G4 & G5). cbn [rg_len] in G3, G4, G5.
    assert (Ec : cur = ly_brk0 L + PGSZ * p) by (unfold cur, brk_cur; rewrite Hbrk, Hb3; reflexivity).
    assert (Hv : vm_brk (m_vmmaps md) = w64 cur) by (rewrite Ec; exact (w64_of_u _ _ Hb4)).
    rewrite Hb3 in G1, G2, G5.
    assert (Ra : cur + PGSZ * 1 + PGSZ < 2 ^ 64) by (rewrite Ec; clear - G5 AT GT HTOPB Hb2; unfold two_pow_64, PGSZ in *; lia).
    assert (Rp : PGSZ <= cur) by (rewrite Ec; clear - B1 Hb2; unfold PGSZ in *; lia).
    assert (Rm : cur mod PGSZ = 0) by (rewrite Ec; apply mod_add0; [exact B2 | rewrite Z.mul_comm; apply Z.mod_mul; unfold PGSZ; lia]).
    assert (R1 : 0 < cur + PGSZ * 1 < 2 ^ 64) by (clear - Rp Ra; unfold PGSZ in *; lia).
    assert (R2 : bv_unsigned (min_brk (m_vmmaps md)) <= cur + PGSZ * 1) by (rewrite Ec; clear - B3 Hb2; unfold PGSZ in *; lia).
    assert (R3 : bv_unsigned (vm_brk (m_vmmaps md)) < cur + PGSZ * 1) by (rewrite Hb4, <- Ec; clear; unfold PGSZ; lia).
    apply (rz_brk_grow segs cfg Hoff rom L s 1 regs pc m md K Hec (lk_halt _ _ _ _ _ HL) (lk_lazy _ _ _ _ _ HL)
             ltac:(fold cur; exact R1) ltac:(fold cur; exact R2) ltac:(fold cur; exact R3)); fold cur.
    + intros Hg.
      assert (Rr : (cur + PGSZ * 1) mod PGSZ = 0) by (apply mod_add0; [exact Rm | reflexivity]).
      destruct (brk_grow_ok_dec md cur (cur + PGSZ * 1) Hv Rp ltac:(clear; unfold PGSZ; lia) ltac:(clear - Ra; lia) Rm Rr Hg) as (Htop & Hf).
      rewrite (brk_eff_dec md cur (cur + PGSZ * 1) Hv Rp ltac:(clear; unfold PGSZ; lia) ltac:(clear - Ra; lia) Rm Rr).
      replace (cur + PGSZ * 1 - cur) with (PGSZ * 1) by ring.
      assert (Hf2 : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 cur) (w64 (PGSZ * 1)) = true).
      { apply (region_free_mono _ _ _ _ Hf). rewrite !u_w64 by (clear - Ra Rp; unfold PGSZ in *; lia). clear. unfold PGSZ. lia. }
      assert (FR : fresh_range FORB HTOP L s (brk_cur L s) (PGSZ * 1)).
      { fold cur. apply (fresh_of_free L x md s cur (PGSZ * 1) HL Hx Hf2 Rp Rm ltac:(clear; unfold PGSZ; lia) ltac:(clear - Htop; unfold PGSZ in *; lia)). }
      assert (EK := o_brk_grant FORB HTOP L s 1 FR). rewrite Hbrk in EK. fold cur in EK.
      apply (Hcont _ 1 _ _ EK (vm_only_with_brk_next _ _ _)).
      2: { exact (ob_brk_grant L x md B 1 cur HL HB Hc Hv Rp Rm ltac:(lia) Ra). }
      rewrite (kstep_brk_cur x 1 1 r p Hbx ltac:(discriminate)).
      assert (VM := brk_next_vmmaps md cur (cur + PGSZ * 1) Hv Rp ltac:(clear; unfold PGSZ; lia) ltac:(clear - Ra; lia) Rm Rr).
      assert (LZ := brk_next_lazy md cur (cur + PGSZ * 1) Hv Rp ltac:(clear; unfold PGSZ; lia) ltac:(clear - Ra; lia) Rm Rr).
      set (md' := with_brk_next md (w64 (cur + PGSZ * 1)) (w64 (cur + PGSZ * 1))) in *.
      replace (cur + PGSZ * 1 - cur) with PGSZ in VM by ring.
      assert (Hf3 : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) (w64 (ly_brk0 L + PGSZ * p)) (w64 PGSZ) = true).
      { rewrite <- Ec. replace PGSZ with (PGSZ * 1) at 2 by ring. exact Hf2. }
      assert (HT : ly_brk0 L + PGSZ * p + PGSZ <= alloc_top (m_vmmaps md)) by (rewrite <- Ec; clear - Htop; lia).
      apply (link_brk_grow L x md md' r p HL Hbx Hf3 HT).
      * exact (vm_only_halted _ _ (vm_only_with_brk_next _ _ _)).
      * exact LZ.
      * rewrite VM. reflexivity.
      * rewrite VM. rewrite <- Ec. reflexivity.
      * rewrite VM. reflexivity.
      * rewrite VM. cbn [vm_brk]. rewrite u_w64 by (clear - Ra Rp; unfold PGSZ in *; lia). rewrite Ec. ring.
      * rewrite VM. reflexivity.
      * rewrite VM. reflexivity.
      * rewrite VM. reflexivity.
    + intros Hg. rewrite Hv.
      assert (EK := o_brk_refuse FORB HTOP L s 1). fold cur in EK.
      apply (Hcont _ 0 _ _ EK (vm_only_refl md)).
      * rewrite kstep_brk0. exact (link_dead L x md HL).
      * exact (ob_brk_refuse L x md B 1 HL HB Hc).
Qed.

#[using="Hoff HTOPB ob_query ob_brk_refuse ob_brk_grant ob_guard ob_rw ob_rw' ob_na ob_na' ob_pr ob_pr' ob_munmap"] Lemma case_all : forall q, is_junk q = false -> node_ok q.
Proof. LiaFast.lf_pins (fun (Hoff HTOPB ob_query ob_brk_refuse ob_brk_grant ob_guard ob_rw ob_rw' ob_na ob_na' ob_pr ob_pr' ob_munmap : LiaFast.U) => LiaFast.u0).
  intros [| n | | len | len | p | r len | b] Hj; try discriminate Hj.
  - exact case_query. - exact (case_brk n). - exact case_guard. - exact (case_rw len). - exact (case_na len).
  - exact (case_pr p). - exact (case_munmap r len).
Qed.

#[using="Hoff HTOPB ob_junk ob_query ob_brk_refuse ob_brk_grant ob_guard ob_rw ob_rw' ob_na ob_na' ob_pr ob_pr' ob_munmap"] Theorem tree_rz : forall {A} (t : itree astate A) L regs pc m x md B (Q : @wpost A) (QK : kf -> A -> Prop) K,
  wk segs FORB HTOP rom L regs pc m t Q -> rk x t QK -> reqs_ok t -> safe t -> rb CH B t ->
  LINK HTOP FORB L x md -> BI x md B ->
  (forall L' r regs' pc' m' x' md' B', Q L' r regs' pc' m' -> QK x' r -> LINK HTOP FORB L' x' md' -> BI x' md' B' ->
     vm_only md md' -> realizes_cfg segs cfg (mkCfg (@mkst fx regs' pc' m' rom) md') K) ->
  realizes_cfg segs cfg (mkCfg (@mkst fx regs pc m rom) md) K.
Proof. LiaFast.lf_pins (fun (Hoff HTOPB ob_junk ob_query ob_brk_refuse ob_brk_grant ob_guard ob_rw ob_rw' ob_na ob_na' ob_pr ob_pr' ob_munmap : LiaFast.U) => LiaFast.u0).
  intros A t. induction t as [r | q s k IH | f]; intros L regs pc m x md B Q QK K Hw Hrk Hreq Hsafe Hrb HL HB HK.
  - cbn [wk rk] in Hw, Hrk. destruct Hw as (regs' & pc' & m' & Hms & HQ).
    eapply rzc_isteps; [exact (lk_halt _ _ _ _ _ HL) | exact (lk_lazy _ _ _ _ _ HL) | apply msteps_isteps; exact Hms |].
    exact (HK L r regs' pc' m' x md B HQ Hrk HL HB (vm_only_refl md)).
  - destruct (is_junk q) eqn:Hj.
    + destruct q as [ | n | | len | len | p | r len | b]; try discriminate Hj. cbn [wk rk reqs_ok safe rb] in Hw, Hrk, Hreq, Hsafe, Hrb.
      destruct Hw as (z & Hz & Hw). destruct Hrb as (Hc & Hrb). destruct Hreq as (_ & Hreq).
      apply (IH z L regs pc m x md (B - CH (KJunk b)) Q QK K Hw (Hrk z) (Hreq z Hz) (Hsafe z Hz) (Hrb z) HL (ob_junk x md B b HB Hc)).
      intros L' r' regs' pc' m' x' md' B' H1 H2 H3 H4 H5. exact (HK L' r' regs' pc' m' x' md' B' H1 H2 H3 H4 H5).
    + assert (Hw' : exists regs1 pc1 m1, msteps segs (mkst regs pc m rom) (mkst regs1 pc1 m1 rom) /\ at_ecall segs L s q regs1 pc1 /\
          forall eff ans L', koutcome FORB HTOP L s q eff ans L' ->
            wk segs FORB HTOP rom L' (regupd regs1 10 (eff_ret eff)) (bv_add pc1 (w64 4)) (mem_after m1 eff) (k ans) Q).
      { destruct q; try discriminate Hj; exact Hw. }
      clear Hw. destruct Hw' as (regs1 & pc1 & m1 & Hms & Hec & Hkw).
      destruct (rk_ask_inv x q s k QK Hrk) as [(Hj' & _) | (_ & Hx & Hrk')]; [congruence|].
      cbn [reqs_ok safe rb] in Hreq, Hsafe, Hrb. destruct Hreq as (Hrq & Hreq). destruct Hrb as (Hc & Hrb).
      eapply rzc_isteps; [exact (lk_halt _ _ _ _ _ HL) | exact (lk_lazy _ _ _ _ _ HL) | apply msteps_isteps; exact Hms |].
      apply (case_all q Hj L x md B s regs1 pc1 m1 K Hec Hx Hrq HL HB Hc).
      intros eff ans L' md' Ho Hvm HL' HB'.
      assert (Hans : answer_ok q ans) by (destruct q; try discriminate Hj; exact I).
      apply (IH ans L' _ _ _ (kstep x q ans) md' (B - CH q) Q QK K (Hkw eff ans L' Ho) (Hrk' Hrq ans) (Hreq ans Hans) (Hsafe ans Hans) (Hrb ans) HL' HB').
      intros L'' r' regs' pc' m' x' md'' B' H1 H2 H3 H4 H5. exact (HK L'' r' regs' pc' m' x' md'' B' H1 H2 H3 H4 (vm_only_trans _ _ _ Hvm H5)).
  - exfalso. exact Hsafe.
Qed.
End TreeRz.
