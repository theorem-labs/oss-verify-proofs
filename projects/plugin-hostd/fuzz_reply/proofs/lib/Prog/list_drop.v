From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes Arr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import memmove_c ListStep ListDropRun.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YO10 YN19.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import KindB RelayFrame RelayRunT RelayRunF HarnessRep
  ListRep ListTr TrModel ListFrame HarnessGlue list_drop_c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma ld_tr_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app, !length_le8. reflexivity. Qed.

Lemma ld_cc_len : forall l, length (concat (map text_rec l)) = (16 * length l)%nat.
Proof.
  induction l as [|r l IH]; [reflexivity|].
  change (concat (map text_rec (r :: l))) with (text_rec r ++ concat (map text_rec l)).
  rewrite length_app, IH, ld_tr_len. cbn [length]. lia.
Qed.

Lemma ld_skipn_app0 : forall {X} (l1 l2 : list X), skipn (length l1) (l1 ++ l2) = l2.
Proof. intros X l1. induction l1 as [|a l1 IH]; intros l2; [reflexivity|]. cbn. apply IH. Qed.

Lemma ld_skipn_app : forall {X} (l1 l2 : list X) n, skipn (length l1 + n) (l1 ++ l2) = skipn n l2.
Proof. intros X l1. induction l1 as [|a l1 IH]; intros l2 n; [reflexivity|]. cbn. apply IH. Qed.

Lemma ld_firstn_app0 : forall {X} (l1 l2 : list X), firstn (length l1) (l1 ++ l2) = l1.
Proof. intros X l1. induction l1 as [|a l1 IH]; intros l2; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

Lemma ld_skipn_nth : forall {X} (l : list X) k d, (k < length l)%nat -> skipn k l = nth k l d :: skipn (S k) l.
Proof.
  intros X l. induction l as [|a l IH]; intros k d H; [cbn in H; lia|].
  destruct k as [|k]; [reflexivity|]. cbn [skipn nth]. apply IH. cbn in H. lia.
Qed.

Lemma ld_last_app : forall {X} (l1 l2 : list X) d, l2 <> [] -> last (l1 ++ l2) d = last l2 d.
Proof.
  intros X l1. induction l1 as [|a l1 IH]; intros l2 d H; [reflexivity|].
  cbn [app]. rewrite <- (IH l2 d H). destruct (l1 ++ l2) eqn:E.
  - apply app_eq_nil in E. destruct E as [_ E]. contradiction.
  - reflexivity.
Qed.

Lemma ld_in_rm : forall {X} (b1 b2 : list X) y x, In x (b1 ++ y :: b2) -> x <> y -> In x (b1 ++ b2).
Proof.
  intros X b1 b2 y x H N. apply in_app_or in H. apply in_or_app.
  destruct H as [H|[H|H]]; [left; exact H | congruence | right; exact H].
Qed.

Lemma ld_nodup_fst : forall {X Y} (l : list (X * Y)) x a b, List.NoDup (map fst l) -> In (x, a) l -> In (x, b) l ->
  a = b.
Proof.
  intros X Y l. induction l as [|[y c] l IH]; intros x a b ND Ha Hb; [destruct Ha|].
  cbn [map fst] in ND. apply List.NoDup_cons_iff in ND as [Hn ND].
  destruct Ha as [Ea|Ha], Hb as [Eb|Hb].
  - congruence.
  - injection Ea as E1 E2. subst. exfalso. apply Hn. exact (in_map fst _ _ Hb).
  - injection Eb as E1 E2. subst. exfalso. apply Hn. exact (in_map fst _ _ Ha).
  - exact (IH x a b ND Ha Hb).
Qed.

Lemma ld_ub_fst : forall s p a b, WF s -> In (p, a) (user_blocks s) -> In (p, b) (user_blocks s) -> a = b.
Proof.
  intros s p a b HW Ha Hb. pose proof (YO10.user_block_ptrs_NoDup s HW) as ND.
  first [ exact (ld_nodup_fst _ _ _ _ ND Ha Hb) | exact (ld_nodup_fst _ _ _ _ (proj1 (NoDup_ListNoDup _) ND) Ha Hb) ].
Qed.

Lemma ld_split : forall {X} (l : list X) k d, (k < length l)%nat ->
  l = firstn k l ++ nth k l d :: skipn (S k) l /\ length (firstn k l) = k /\
  length (skipn (S k) l) = (length l - S k)%nat.
Proof.
  intros X l k d Hk. split; [|split].
  - rewrite <- (ld_skipn_nth l k d Hk). symmetry. apply firstn_skipn.
  - rewrite length_firstn. lia.
  - apply length_skipn.
Qed.

Lemma ld_in_sub : forall {X} (l : list X) k (d y : X), (k < length l)%nat -> In y (firstn k l ++ skipn (S k) l) ->
  In y l.
Proof.
  intros X l k d y Hk H. destruct (ld_split l k d Hk) as (E & _ & _). rewrite E.
  apply in_app_or in H. apply in_or_app. destruct H as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma ld_nodup_rm : forall {X Y} (l : list (X * Y)) k d, (k < length l)%nat -> List.NoDup (map fst l) ->
  List.NoDup (map fst (firstn k l ++ skipn (S k) l)) /\
  (forall y, In y (firstn k l ++ skipn (S k) l) -> fst y <> fst (nth k l d)).
Proof.
  intros X Y l k d Hk ND. destruct (ld_split l k d Hk) as (E & _ & _).
  rewrite E in ND. rewrite map_app in ND. cbn [map] in ND. split.
  - rewrite map_app. exact (List.NoDup_remove_1 _ _ _ ND).
  - intros y Hy Ey. apply (List.NoDup_remove_2 _ _ _ ND). rewrite <- map_app, <- Ey. exact (in_map fst _ _ Hy).
Qed.

Lemma ld_skip_last : forall l junk, l <> [] ->
  skipn (16 * (length l - 1)) (concat (map text_rec l) ++ junk) = text_rec (last l (0, [])) ++ junk.
Proof.
  induction l as [|a l IH]; intros junk H; [contradiction|].
  destruct l as [|b t].
  - cbn [map concat length last]. rewrite app_nil_r. reflexivity.
  - change (concat (map text_rec (a :: b :: t))) with (text_rec a ++ concat (map text_rec (b :: t))).
    change (last (a :: b :: t) (0, [])) with (last (b :: t) (0, [])).
    rewrite <- app_assoc.
    replace (16 * (length (a :: b :: t) - 1))%nat with (length (text_rec a) + 16 * (length (b :: t) - 1))%nat
      by (rewrite ld_tr_len; cbn [length]; lia).
    rewrite ld_skipn_app. apply IH. discriminate.
Qed.

Lemma ld_mm0 : forall P r Q junk,
  mm_result (concat (map text_rec (P ++ r :: Q)) ++ junk) (16 * length P + 16) (16 * length P) (16 * length Q) =
  concat (map text_rec (P ++ Q)) ++ text_rec (last (r :: Q) (0, [])) ++ junk.
Proof.
  intros P r Q junk.
  pose proof (ld_skip_last (r :: Q) junk ltac:(discriminate)) as SL.
  change (concat (map text_rec (r :: Q))) with (text_rec r ++ concat (map text_rec Q)) in SL.
  cbn [length] in SL. replace (16 * (S (length Q) - 1))%nat with (16 * length Q)%nat in SL by lia.
  rewrite <- app_assoc in SL.
  rewrite !map_app, !concat_app.
  change (concat (map text_rec (r :: Q))) with (text_rec r ++ concat (map text_rec Q)).
  pose proof (ld_cc_len P) as LP. pose proof (ld_cc_len Q) as LQ. pose proof (ld_tr_len r) as LT.
  rewrite <- LQ in SL.
  set (cP := concat (map text_rec P)) in *. set (cQ := concat (map text_rec Q)) in *.
  set (T := text_rec r) in *.
  unfold mm_result, slice, upd_bytes.
  rewrite <- !app_assoc.
  replace (16 * length P + 16)%nat with (length cP + length T)%nat by lia.
  rewrite ld_skipn_app, ld_skipn_app0.
  replace (16 * length Q)%nat with (length cQ) by lia.
  rewrite ld_firstn_app0.
  replace (16 * length P)%nat with (length cP) by lia.
  rewrite ld_firstn_app0, ld_skipn_app, SL. reflexivity.
Qed.

Lemma ld_mm : forall recs junk (i : Z), 0 <= i < Z.of_nat (length recs) ->
  mm_result (concat (map text_rec recs) ++ junk) (Z.to_nat (16 * i + 16)) (Z.to_nat (16 * i))
    (Z.to_nat (16 * (Z.of_nat (length recs) - i - 1))) =
  concat (map text_rec (firstn (Z.to_nat i) recs ++ skipn (S (Z.to_nat i)) recs)) ++
    text_rec (last recs (0, [])) ++ junk.
Proof.
  intros recs junk i Hi.
  assert (Hk : (Z.to_nat i < length recs)%nat) by lia.
  destruct (ld_split recs (Z.to_nat i) (0, []) Hk) as (E & LP & LQ).
  revert E LP LQ.
  generalize (firstn (Z.to_nat i) recs) (nth (Z.to_nat i) recs (0, [])) (skipn (S (Z.to_nat i)) recs).
  intros P r Q E LP LQ.
  replace (Z.to_nat (16 * i + 16)) with (16 * length P + 16)%nat by lia.
  replace (Z.to_nat (16 * i)) with (16 * length P)%nat by lia.
  replace (Z.to_nat (16 * (Z.of_nat (length recs) - i - 1))) with (16 * length Q)%nat by lia.
  rewrite E.
  rewrite ld_last_app by discriminate.
  apply ld_mm0.
Qed.

Lemma ld_firstn_app8 : forall (v : word) (l : list byte), firstn 8 (le8 v ++ l) = le8 v.
Proof. intros v l. rewrite <- (length_le8 v) at 1. apply ld_firstn_app0. Qed.

Lemma ld_rec_at : forall recs junk k, (k < length recs)%nat ->
  firstn 8 (skipn (16 * k) (concat (map text_rec recs) ++ junk)) = le8 (Z_to_bv 64 (fst (nth k recs (0, [])))).
Proof.
  intros recs junk k Hk.
  destruct (ld_split recs k (0, []) Hk) as (E & LP & _).
  revert E LP.
  generalize (firstn k recs) (nth k recs (0, [])) (skipn (S k) recs).
  intros P r Q E LP.
  rewrite E.
  rewrite map_app, concat_app.
  change (concat (map text_rec (r :: Q))) with (text_rec r ++ concat (map text_rec Q)).
  replace (16 * k)%nat with (length (concat (map text_rec P))) by (rewrite ld_cc_len; lia).
  rewrite <- app_assoc, ld_skipn_app0.
  unfold text_rec at 1. rewrite <- !app_assoc.
  apply ld_firstn_app8.
Qed.

Lemma ld_rw_sub : forall segs m A (n : nat) bs (o k : nat), rw_cells segs m A [CB n bs] -> (o + k <= n)%nat ->
  rw_cells segs m (A + Z.of_nat o) [CB k (firstn k (skipn o bs))].
Proof.
  intros segs m A n bs o k H Hk.
  apply (rw_cells_split_CB segs m A [] n bs [] [o; k; (n - o - k)%nat]) in H; [|cbn; lia].
  cbn [mk_CB_cells app] in H.
  destruct (ls_cut segs m A [_] [_; _] H) as [_ H2]. cbn [cells_size csize Nat.add] in H2.
  destruct (ls_cut segs m _ [_] [_] H2) as [H3 _].
  replace (A + Z.of_nat (o + 0)) with (A + Z.of_nat o) in H3 by lia. exact H3.
Qed.

Lemma ld_cb_eq : forall segs m a (k k' : nat) bs bs', rw_cells segs m a [CB k bs] -> k = k' -> bs = bs' ->
  rw_cells segs m a [CB k' bs'].
Proof. intros segs m a k k' bs bs' H -> ->. exact H. Qed.

Lemma ld_disj : forall (P : Z -> Prop) a1 k1 a2 k2, 0 < k1 -> 0 < k2 ->
  (forall i, 0 <= i < k1 -> P (a1 + i)) -> (forall i, 0 <= i < k2 -> ~ P (a2 + i)) ->
  a1 + k1 <= a2 \/ a2 + k2 <= a1.
Proof.
  intros P a1 k1 a2 k2 K1 K2 H1 H2.
  destruct (Z_le_gt_dec (a1 + k1) a2) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (a2 + k2) a1) as [D'|D']; [right; exact D'|]. exfalso.
  apply (H2 (Z.max a1 a2 - a2) ltac:(lia)).
  replace (a2 + (Z.max a1 a2 - a2)) with (a1 + (Z.max a1 a2 - a1)) by lia. apply H1. lia.
Qed.

Lemma ld_out1 : forall lo hi x, ~ outside [(lo, hi)] x -> lo <= x < hi.
Proof.
  intros lo hi x O. assert (H1 : lo <= x < hi \/ ~ (lo <= x < hi)) by lia.
  destruct H1 as [H1|H1]; [exact H1|]. exfalso. apply O. cbn [outside]. split; [exact H1 | exact I].
Qed.

Lemma ld_out2 : forall lo1 hi1 lo2 hi2 x, ~ outside [(lo1, hi1); (lo2, hi2)] x -> lo1 <= x < hi1 \/ lo2 <= x < hi2.
Proof.
  intros lo1 hi1 lo2 hi2 x O.
  assert (H1 : lo1 <= x < hi1 \/ ~ (lo1 <= x < hi1)) by lia.
  assert (H2 : lo2 <= x < hi2 \/ ~ (lo2 <= x < hi2)) by lia.
  destruct H1 as [H1|H1]; [left; exact H1|]. destruct H2 as [H2|H2]; [right; exact H2|].
  exfalso. apply O. cbn [outside]. split; [exact H1 | split; [exact H2 | exact I]].
Qed.

Lemma ld_xr0 : forall R R' r v, Regs6ss.xregs_eqv R R' -> is_x0 r = false -> reg_get R r = v -> reg_get R' r = v.
Proof. intros R R' r v X H E. rewrite <- (X r H). exact E. Qed.

Ltac ld_xr X Hf := refine (ld_xr0 _ _ _ _ X _ Hf); reflexivity.

Ltac ld_lz := repeat match goal with
  | H : _ \/ _ |- _ => clear H
  | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
  end; lia.

Lemma ld_tr_nth : forall nm l i, (i < length (hl_recs l))%nat ->
  list_drop_tr (sh_of nm l) i =
  [RFree (Z.of_nat (length (snd (nth i (hl_recs l) (0, [])))) + 1) (nm (fst (nth i (hl_recs l) (0, []))))].
Proof.
  intros nm l i Hi. unfold list_drop_tr, sh_of, rec_drop_tr, rec_len. cbn [sh_recs].
  rewrite nth_indep with (d' := shr nm (0, [])) by (rewrite length_map; exact Hi).
  rewrite map_nth. unfold shr, bzs. cbn [fst snd]. rewrite length_map. reflexivity.
Qed.

Lemma ld_sh_real : forall L A L2 (l l2 : hlist) i,
  WF A -> NoDup (map fst (blocks L A)) -> layout_le A L L2 ->
  (hl_cap l <> 0 -> exists n, In (hl_v l, n) (blocks L A)) ->
  (forall r, In r (hl_recs l2) -> exists n, In (fst r, n) (blocks L A)) ->
  hl_cap l2 = hl_cap l -> hl_v l2 = hl_v l -> hl_recs l2 = firstn i (hl_recs l) ++ skipn (S i) (hl_recs l) ->
  sh_real L2 [] (list_drop_sh (sh_of (known_at L A) l) i) l2.
Proof.
  intros L A L2 l l2 i HW HN HL Hv Hr Ec Ev Er.
  assert (K : forall a n, In (a, n) (blocks L A) -> ptr_addr L2 (sptr_of L A a) = a).
  { intros a n Hin. destruct (sptr_of_spec L A a n HN Hin) as [Hu Ha].
    rewrite (YN19.ptr_addr_le A L L2 _ HL (lf_ub_prid_lt A _ _ HW Hu)). exact Ha. }
  rewrite Er in Hr.
  unfold sh_real, list_drop_sh, sh_of, sh_keys, known_at. cbn [sh_cap sh_v sh_recs].
  rewrite Ec, Ev, Er. split; [reflexivity|]. split.
  - intros Hc. destruct (Hv Hc) as [n Hn]. symmetry. exact (K _ _ Hn).
  - rewrite firstn_map, skipn_map, <- map_app, !map_map. split; [reflexivity|].
    apply map_ext_in. intros r Hin. destruct (Hr r Hin) as [n Hn]. cbn. symmetry. exact (K _ _ Hn).
Qed.

Lemma ld_sh_live : forall L A A2 (l : hlist) i p,
  NoDup (map fst (blocks L A)) ->
  (forall q k, In (q, k) (user_blocks A) -> q <> p -> In (q, k) (user_blocks A2)) ->
  (hl_cap l <> 0 -> exists n, In (hl_v l, n) (blocks L A) /\ hl_v l <> ptr_addr L p) ->
  (forall r, In r (firstn i (hl_recs l) ++ skipn (S i) (hl_recs l)) ->
     exists n, In (fst r, n) (blocks L A) /\ fst r <> ptr_addr L p) ->
  sh_live A2 [] (list_drop_sh (sh_of (known_at L A) l) i).
Proof.
  intros L A A2 l i p HN UBK Hv Hr.
  assert (K : forall a n, In (a, n) (blocks L A) -> a <> ptr_addr L p -> In (sptr_of L A a, n) (user_blocks A2)).
  { intros a n Hin Ha. destruct (sptr_of_spec L A a n HN Hin) as [Hu Hpa]. apply UBK; [exact Hu|].
    intros E. apply Ha. rewrite <- Hpa, E. reflexivity. }
  unfold sh_live, list_drop_sh, sh_of, known_at. cbn [sh_cap sh_v sh_recs]. split.
  - intros Hc. destruct (Hv Hc) as (n & Hn & Hne). exists n. exact (K _ _ Hn Hne).
  - intros r Hin. rewrite firstn_map, skipn_map, <- map_app in Hin. apply in_map_iff in Hin as (r0 & <- & Hr0).
    destruct (Hr r0 Hr0) as (n & Hn & Hne). exists n. exact (K _ _ Hn Hne).
Qed.

Section LDP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable F : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis FREEPC : ms_free Bm = 0x15664.
Hypothesis ERRNO_LOW : errno_addr Bm + 4 <= YM05.alloc_ceiling.
Hypothesis NDB : blocks_nodup Bm API.

Lemma ld_blk : forall L A mem md q k, aa_MR API L A mem md -> In (q, k) (blocks L A) ->
  4096 <= q /\ q + k <= YM05.alloc_ceiling.
Proof.
  intros L A mem md q k HM H. destruct (lf_blocks_in L A q k H) as (p & Hp & <-).
  exact (mr_blocks_range _ _ (aa_laws API) L A mem md p k HM Hp).
Qed.

Definition ld_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (bnd : rt_R F) (LA IX : Z) (l : hlist) (lines : bool) : config -> Prop :=
  fun c' => exists L' A' regs' mem' md' (l' : hlist),
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom (ms_segs Bm))) md' /\
    relay_post Bm API LIST_DROP_K
      (fun a => LA + 8 <= a < LA + 12 \/ hl_v l + 16 * IX <= a < hl_v l + 16 * (hl_n l - 1))
      (fun q => q = fst (nth (Z.to_nat IX) (hl_recs l) (0, [])))
      L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF (list_drop_tr (sh_of (known_at L A) l) (Z.to_nat IX)) /\
       rt_ok F A' (runF F qs bnd (list_drop_tr (sh_of (known_at L A) l) (Z.to_nat IX))) /\
       sh_real L' qs (list_drop_sh (sh_of (known_at L A) l) (Z.to_nat IX)) l' /\
       sh_live A' qs (list_drop_sh (sh_of (known_at L A) l) (Z.to_nat IX))) /\
    ro_agree (ms_segs Bm) mem' /\
    list_at Bm L' A' mem' LA l' lines /\
    hl_v l' = hl_v l /\ hl_cap l' = hl_cap l /\
    hl_recs l' = firstn (Z.to_nat IX) (hl_recs l) ++ skipn (S (Z.to_nat IX)) (hl_recs l) /\
    hl_junk l' = text_rec (last (hl_recs l) (0, [])) ++ hl_junk l /\
    (exists b1 b2, blocks L A = b1 ++ (fst (nth (Z.to_nat IX) (hl_recs l) (0, [])),
                                       text_len (nth (Z.to_nat IX) (hl_recs l) (0, []))) :: b2 /\
                   blocks L' A' = b1 ++ b2).

Lemma ld_main : free_contract_rt Bm API F -> memmove_contract ->
  forall L A regs mem md (bnd : rt_R F) (l : hlist) (lines : bool) (LA IX S0 : Z),
  getr regs 10 = Z_to_bv 64 LA -> getr regs 11 = Z_to_bv 64 IX -> S0 = spZ regs ->
  0 <= LA < 2 ^ 64 -> 0 <= IX < 2 ^ 64 ->
  ms_segs Bm = rsegs ->
  call_pre_k Bm (aa_MR API) LIST_DROP_K L A regs mem md ->
  st_init_done A = true ->
  ro_agree rsegs mem ->
  (forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr rsegs (Z_to_bv 64 a) = false) ->
  list_at Bm L A mem LA l lines ->
  IX < hl_n l ->
  rt_ok F A bnd ->
  SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_DROP) mem (seg_rom rsegs)) md)
    (ld_post L A regs mem md bnd LA IX l lines).
Proof.
  intros FRE MMV L A regs mem md bnd l lines LA IX S0 E10 E11 ES RLA RIX SEG PRE INIT RO LAI LIST HI RES.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  destruct AC as [AC _].
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HC & H63 & HWS & HTP & HERR & HAUX).
  rewrite <- ES in HAL, HC, H63, HWS.
  assert (KV : LIST_DROP_K = 8224) by reflexivity.
  rewrite KV in HC, HWS.
  destruct (mr_model _ _ LAWS _ _ _ _ HMR) as (Hh & Hl & Hmat).
  assert (ES' : bv_unsigned (getr regs 2) = S0) by (rewrite ES; reflexivity).
  destruct LIST as (LC0 & NB0 & CASE0 & ND0 & NV0 & TXF0).
  assert (N0 : 0 <= hl_n l) by (unfold hl_n; lia).
  destruct CASE0 as [(C0 & _) | (CP & INV & FV & LJ & ARR)]; [lia|].
  rewrite SEG in LC0, ARR, TXF0.
  pose proof FV as (FV1 & FV2 & FV3).
  assert (LAR : 0 <= LA /\ LA + 16 <= 2 ^ 21).
  { pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI LA ltac:(lia))))).
    pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI (LA + 15) ltac:(lia))))). lia. }
  assert (Hk : (Z.to_nat IX < length (hl_recs l))%nat) by (unfold hl_n in HI; lia).
  remember (nth (Z.to_nat IX) (hl_recs l) (0, [])) as r eqn:Er.
  assert (RIN : In r (hl_recs l)) by (rewrite Er; apply nth_In; exact Hk).
  destruct (proj1 (Forall_forall _ _) TXF0 r RIN) as (TB & TF & TRW & _ & _).
  pose proof TF as (TF1 & TF2 & TF3).
  destruct (lf_blocks_in L A _ _ TB) as (p & Hp & Ep).
  pose proof (NDB L A mem md HMR) as NDL.
  pose proof (ld_blk L A mem md _ _ HMR INV) as VB.
  assert (NVR : hl_v l <> fst r) by (intro E; apply NV0; rewrite E; exact (in_map fst _ _ RIN)).
  assert (DLV : LA + 16 <= hl_v l \/ hl_v l + 16 * hl_cap l <= LA)
    by exact (ld_disj (in_img Bm) LA 16 (hl_v l) (16 * hl_cap l) ltac:(ld_lz) ltac:(ld_lz)
                (fun j Hj => proj1 (proj1 (LAI (LA + j) ltac:(ld_lz)))) FV3).
  assert (LUS : Z.of_nat (length (concat (map text_rec (hl_recs l)) ++ hl_junk l)) = 16 * hl_cap l).
  { rewrite length_app, ld_cc_len. unfold hl_n in LJ. lia. }
  assert (US : bv_unsigned (Z_to_bv 64 S0) = S0) by (apply unsigned_lit; lia).
  assert (ULA : bv_unsigned (Z_to_bv 64 LA) = LA) by (apply unsigned_lit; lia).
  assert (UIX : bv_unsigned (Z_to_bv 64 IX) = IX) by (apply unsigned_lit; lia).
  assert (R2E : reg_get regs 2 = Z_to_bv 64 S0) by (rewrite ES; symmetry; exact (Z_to_bv_bv_unsigned (getr regs 2))).
  assert (R10 : reg_get regs 10 = Z_to_bv 64 LA) by exact E10.
  assert (R11 : reg_get regs 11 = Z_to_bv 64 IX) by exact E11.
  assert (ST : stk rsegs mem (S0 - 32) S0).
  { split; [lia|]. split; [lia|]. intros a Ha.
    assert (W : writable_at rsegs mem a) by (rewrite <- SEG; apply HWS; lia).
    split; [exact W|]. destruct (writable_hi_present mem a ltac:(lia) W) as [bb E]. exists bb.
    unfold mrd, wa. rewrite E. reflexivity. }
  pose proof (stk_normalize mem _ _ ST ltac:(lia)) as STn.
  pose proof (rw_cells_normalize rsegs mem LA _ RO LC0
                ltac:(intros j Hj; cbn in Hj; exact (proj2 (LAI (LA + j) ltac:(lia))))) as LCn.
  destruct (ls_cut rsegs _ _ [_] [_; _] LCn) as [LC8n _].
  assert (QC : rw_cells rsegs mem (hl_v l + 16 * IX) [C8 (Z_to_bv 64 (fst r))]).
  { pose proof (ld_rw_sub rsegs mem (hl_v l) _ _ (16 * Z.to_nat IX) 8 ARR ltac:(lia)) as X.
    rewrite ld_rec_at in X by exact Hk. rewrite <- Er in X.
    replace (hl_v l + Z.of_nat (16 * Z.to_nat IX)) with (hl_v l + 16 * IX) in X by lia.
    apply (rw_cells_retype rsegs _ _ _ _ X); [exact (conj I I) | reflexivity]. }
  assert (QCn : rw_cells rsegs (normalize rsegs mem) (hl_v l + 16 * IX) [C8 (Z_to_bv 64 (fst r))]).
  { apply rw_cells_normalize; [exact RO | exact QC |]. intros j Hj. cbn in Hj.
    apply (ro_addr_out Bm SEG); [ld_lz|].
    replace (hl_v l + 16 * IX + j) with (hl_v l + (16 * IX + j)) by ring. apply FV3. ld_lz. }
  eapply (lift_run regs (Z_to_bv 64 LIST_DROP) mem md [(S0 - 32, S0)]
    (fun m' => rw_cells rsegs m' (S0 - 32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)])
    (fun R pc' => pc' = Z_to_bv 64 0x15664 /\ reg_get R 1 = Z_to_bv 64 0x146b4 /\ reg_get R 2 = Z_to_bv 64 (S0 - 32) /\
       reg_get R 3 = getr regs 3 /\ reg_get R 4 = getr regs 4 /\ reg_get R 8 = Z_to_bv 64 LA /\
       reg_get R 9 = Z_to_bv 64 IX /\ reg_get R 10 = Z_to_bv 64 (fst r) /\ reg_get R 18 = Z_to_bv 64 (16 * IX) /\
       reg_get R 19 = getr regs 19 /\ reg_get R 20 = getr regs 20 /\ reg_get R 21 = getr regs 21 /\
       reg_get R 22 = getr regs 22 /\ reg_get R 23 = getr regs 23 /\ reg_get R 24 = getr regs 24 /\
       reg_get R 25 = getr regs 25 /\ reg_get R 26 = getr regs 26 /\ reg_get R 27 = getr regs 27));
    [exact Hh | exact Hl | exact RO | |].
  { unfold Regs6ss.mkR_of. rewrite R2E, R10, R11. unfold LIST_DROP.
    eapply evt_mono.
    { eapply ld_run1 with (lo := S0 - 32) (V := hl_v l) (q := fst r);
        [rewrite US; exact STn | rewrite US; lia | rewrite ULA; exact LC8n | rewrite UIX; exact QCn
        | rewrite ULA, US; ld_lz | ld_lz | rewrite UIX, US; ld_lz]. }
    intros ms' (t0 & t1 & t2 & b1 & b2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & MU & WM & FR).
    rewrite US in MU, FR. rewrite US, UIX.
    eexists _, _, m'. split; [reflexivity|].
    split; [repeat split|].
    split; [exact MU|]. split; [exact WM | exact FR]. }
  intros R R1 pc' m1 m'' (EPC & F_1 & F_2 & F_3 & F_4 & F_8 & F_9 & F_10 & F_18 & F_19 & F_20 & F_21 & F_22 & F_23
    & F_24 & F_25 & F_26 & F_27) X MU1 WM1 RO1 REL1 FRp.
  subst pc'.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL1 FRp) as FR1.
  assert (E1_1 : reg_get R1 1 = Z_to_bv 64 0x146b4) by (ld_xr X F_1).
  assert (E1_2 : reg_get R1 2 = Z_to_bv 64 (S0 - 32)) by (ld_xr X F_2).
  assert (E1_3 : reg_get R1 3 = getr regs 3) by (ld_xr X F_3).
  assert (E1_4 : reg_get R1 4 = getr regs 4) by (ld_xr X F_4).
  assert (E1_8 : reg_get R1 8 = Z_to_bv 64 LA) by (ld_xr X F_8).
  assert (E1_9 : reg_get R1 9 = Z_to_bv 64 IX) by (ld_xr X F_9).
  assert (E1_10 : reg_get R1 10 = Z_to_bv 64 (fst r)) by (ld_xr X F_10).
  assert (E1_18 : reg_get R1 18 = Z_to_bv 64 (16 * IX)) by (ld_xr X F_18).
  assert (E1_19 : reg_get R1 19 = getr regs 19) by (ld_xr X F_19).
  assert (E1_20 : reg_get R1 20 = getr regs 20) by (ld_xr X F_20).
  assert (E1_21 : reg_get R1 21 = getr regs 21) by (ld_xr X F_21).
  assert (E1_22 : reg_get R1 22 = getr regs 22) by (ld_xr X F_22).
  assert (E1_23 : reg_get R1 23 = getr regs 23) by (ld_xr X F_23).
  assert (E1_24 : reg_get R1 24 = getr regs 24) by (ld_xr X F_24).
  assert (E1_25 : reg_get R1 25 = getr regs 25) by (ld_xr X F_25).
  assert (E1_26 : reg_get R1 26 = getr regs 26) by (ld_xr X F_26).
  assert (E1_27 : reg_get R1 27 = getr regs 27) by (ld_xr X F_27).
  clear F_1 F_2 F_3 F_4 F_8 F_9 F_10 F_18 F_19 F_20 F_21 F_22 F_23 F_24 F_25 F_26 F_27 FRp.
  assert (MID1 : lmid Bm API LIST_DROP_K S0 (fun _ => False) (fun _ => False) L A mem md L A m1 md).
  { apply (lmid_A Bm API SEG AX LIST_DROP_K S0 _ L A mem md m1 [(S0 - 32, S0)]);
      [ exact HMR | exact HWF | exact HBD | rewrite KV; lia | lia
      | intros a [Ha|Ha]; [apply HWS; rewrite KV in Ha; lia | apply HERR; exact Ha]
      | exact MU1 | rewrite SEG; exact WM1 | | ].
    - intros y Hy O. left. rewrite KV. apply ld_out1 in O. lia.
    - intros y Hy _. cbn [outside]. split; [lia | exact I]. }
  pose proof MID1 as (M1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC1).
  assert (TR1 : forall a cs, rw_cells rsegs mem a cs -> a + Z.of_nat (cells_size cs) <= S0 - 32 ->
                  rw_cells rsegs m1 a cs).
  { intros a cs H HD. apply (rw_cells_transport rsegs _ mem m1 _ _ H MU1 WM1). cbn [disjoint_from].
    split; [lia | exact I]. }
  assert (LC1 : rw_cells rsegs m1 LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 (hl_cap l))]).
  { apply TR1; [exact LC0 | cbn [cells_size csize Nat.add]; ld_lz]. }
  assert (ARR1 : rw_cells rsegs m1 (hl_v l) [CB (Z.to_nat (16 * hl_cap l)) (concat (map text_rec (hl_recs l)) ++ hl_junk l)]).
  { apply TR1; [exact ARR | cbn [cells_size csize]; ld_lz]. }
  pose proof FRE as FRF. unfold free_contract_rt in FRF. rewrite SEG, FREEPC in FRF.
  assert (SP1 : spZ R1 = S0 - 32)
    by (unfold spZ; change (getr R1 2) with (reg_get R1 2); rewrite E1_2; apply unsigned_lit; lia).
  assert (PRE1 : call_pre Bm (aa_MR API) L A R1 m1 md).
  { apply (proj2 (call_pre_k_alloc Bm _ L A R1 m1 md)).
    eapply (lmid_pre Bm API _ S0 _ _ L A regs mem md L A m1 md ALLOC_STACK 32 R1 PRE ES MID1 INIT SP1);
      [ rewrite SP1; replace (S0 - 32) with (S0 + (-2) * 16) by ring; rewrite Z.mod_add by lia; exact HAL
      | exact E1_4
      | replace (getr R1 1) with (Z_to_bv 64 0x146b4) by (symmetry; exact E1_1); apply ret_ok_even; vm_compute;
        reflexivity
      | lia
      | rewrite KV; change ALLOC_STACK with 8192; lia ]. }
  eapply SR_bind.
  { apply (FRF L A R1 m1 md p (Z.of_nat (length (snd r)) + 1) bnd PRE1 RO1 Hp); [rewrite Ep; exact E1_10 | exact RES]. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & -> & POST & BLK & _ & RO2 & _ & UBK & INITI & RLEN & RES').
  apply (proj1 (call_post_k_alloc Bm _ L A R1 m1 md _ L2 A2 R2 m2 md2)) in POST.
  change ALLOC_STACK with 8192 in POST.
  pose proof POST as (M2 & W2 & BD2 & LY2 & PA2 & HPRES & HVM & HFRAME & HBLKS & HSCR).
  destruct (mr_model _ _ LAWS _ _ _ _ M2) as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (b1 & b2 & BLK1 & BLK2). rewrite Ep in BLK1.
  assert (MID2 : lmid Bm API LIST_DROP_K S0 (fun _ => False) (fun q => q = fst r) L A m1 md L2 A2 m2 md2).
  { apply (lmid_call Bm API AX CTX LIST_DROP_K S0 8192 L A R1 m1 md _ L2 A2 R2 m2 md2 (fun q => q = fst r) M1 POST).
    - intros a Ha Hb. cbv beta in Hb. rewrite Ep in Hb. destruct Ha as [Ha|Ha]; [ld_lz|].
      apply (TF3 (a - fst r) ltac:(ld_lz)). replace (fst r + (a - fst r)) with a by ring. exact Ha.
    - rewrite SP1, KV. lia.
    - rewrite SP1. lia.
    - rewrite KV. lia.
    - lia.
    - exact SC1.
    - intros p0 n0 Hp0 _ HF. apply UBK; [exact Hp0|]. intro E0. apply HF. subst p0. exact Ep.
    - intros p0 Hp0. apply UBK; [exact Hp0|]. intro E0. subst p0.
      pose proof (ld_ub_fst A p _ _ HWF Hp0 Hp). lia.
    - exact RLEN. }
  assert (NOW : forall a, YM05.alloc_ceiling <= a -> ~ owned Bm L A a /\ ~ owned Bm L2 A2 a).
  { intros a Ha. split; intro Y;
      [pose proof (owned_low Bm _ LAWS _ _ _ _ _ M1 Y) | pose proof (owned_low Bm _ LAWS _ _ _ _ _ M2 Y)]; lia. }
  assert (FR2 : rw_cells rsegs m2 (S0 - 32) [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { rewrite <- SEG. apply (rw_cp_frame Bm API 8192 L A R1 m1 md _ L2 A2 R2 m2 md2 _ _ POST); [|rewrite SEG; exact FR1].
    intros j Hj. cbn [cells_size csize Nat.add] in Hj. destruct (NOW (S0 - 32 + j) ltac:(lia)) as [Y1 Y2].
    split; [left; lia|]. split; [exact Y1|]. split; [exact Y2|].
    split; [unfold scratch_k; rewrite SP1; lia | cbv beta; rewrite Ep; lia]. }
  assert (LC2 : rw_cells rsegs m2 LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 (hl_cap l))]).
  { rewrite <- SEG. apply (rw_cp_frame Bm API 8192 L A R1 m1 md _ L2 A2 R2 m2 md2 _ _ POST); [|rewrite SEG; exact LC1].
    intros j Hj. cbn [cells_size csize Nat.add] in Hj.
    destruct (LAI (LA + j) ltac:(lia)) as [IP NR]. pose proof IP as (II & _ & _ & IE).
    split; [right; exact II|].
    split; [exact (lf_img_not_owned Bm API AX _ _ _ _ _ M1 IP)|].
    split; [exact (lf_img_not_owned Bm API AX _ _ _ _ _ M2 IP)|].
    split; [unfold scratch_k; rewrite SP1; intros [Y|Y]; [lia | exact (IE Y)]|].
    cbv beta. rewrite Ep. intro Y. apply (TF3 (LA + j - fst r) ltac:(lia)).
    replace (fst r + (LA + j - fst r)) with (LA + j) by ring. exact II. }
  destruct (lf_blocks_in L A _ _ INV) as (pv & Hpv & Epv).
  assert (Hpv2 : In (pv, 16 * hl_cap l) (user_blocks A2)).
  { apply UBK; [exact Hpv|]. intro E0. subst pv. apply NVR. congruence. }
  assert (ARR2 : rw_cells rsegs m2 (hl_v l) [CB (Z.to_nat (16 * hl_cap l)) (concat (map text_rec (hl_recs l)) ++ hl_junk l)]).
  { rewrite <- SEG.
    apply (rw_cp_block Bm API 8192 L A R1 m1 md _ L2 A2 R2 m2 md2 pv (16 * hl_cap l) (hl_v l) _ POST Hpv Hpv2);
      [rewrite Epv; lia | cbn [cells_size csize]; rewrite Epv; lia | rewrite SEG; exact ARR1]. }
  assert (INV2 : In (hl_v l, 16 * hl_cap l) (blocks L2 A2)).
  { pose proof INV as INV'. rewrite BLK1 in INV'. rewrite BLK2. apply (ld_in_rm b1 b2 _ _ INV').
    intro E0. injection E0 as E0 _. exact (NVR E0). }
  pose proof (mem_inv_normalize rsegs m2) as MI2.
  assert (FRn : rw_cells rsegs (normalize rsegs m2) (bv_unsigned (getr regs 2) - 32)
                  [C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { rewrite ES'. apply rw_cells_normalize; [exact RO2 | exact FR2 |]. intros j Hj. cbn in Hj. apply ro_addr_hi. ld_lz. }
  assert (LCn2 : rw_cells rsegs (normalize rsegs m2) LA
                   [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l)); C4 (Z_to_bv 64 (hl_cap l))]).
  { apply rw_cells_normalize; [exact RO2 | exact LC2 |]. intros j Hj. cbn in Hj. exact (proj2 (LAI (LA + j) ltac:(ld_lz))). }
  assert (ARRn2 : u8arr rsegs (normalize rsegs m2) (hl_v l) (concat (map text_rec (hl_recs l)) ++ hl_junk l)).
  { apply (u8arr_of_rw_cells rsegs _ _ (Z.to_nat (16 * hl_cap l))).
    apply rw_cells_normalize; [exact RO2 | exact ARR2 |].
    intros j Hj. cbn [cells_size csize] in Hj. apply (ro_addr_out Bm SEG); [ld_lz | apply FV3; ld_lz]. }
  assert (CS : forall k, (k = 2 \/ k = 3 \/ k = 4 \/ k = 8 \/ k = 9 \/ (18 <= k <= 27)) -> callee_saved k)
    by (intros k Hk'; unfold callee_saved; lia).
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (S0 - 32)) by exact (eq_trans (HPRES 2 (CS 2 ltac:(lia))) E1_2).
  assert (E2_3 : reg_get R2 3 = getr regs 3) by exact (eq_trans (HPRES 3 (CS 3 ltac:(lia))) E1_3).
  assert (E2_4 : reg_get R2 4 = getr regs 4) by exact (eq_trans (HPRES 4 (CS 4 ltac:(lia))) E1_4).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 LA) by exact (eq_trans (HPRES 8 (CS 8 ltac:(lia))) E1_8).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 IX) by exact (eq_trans (HPRES 9 (CS 9 ltac:(lia))) E1_9).
  assert (E2_18 : reg_get R2 18 = Z_to_bv 64 (16 * IX)) by exact (eq_trans (HPRES 18 (CS 18 ltac:(lia))) E1_18).
  assert (E2_19 : reg_get R2 19 = getr regs 19) by exact (eq_trans (HPRES 19 (CS 19 ltac:(lia))) E1_19).
  assert (E2_20 : reg_get R2 20 = getr regs 20) by exact (eq_trans (HPRES 20 (CS 20 ltac:(lia))) E1_20).
  assert (E2_21 : reg_get R2 21 = getr regs 21) by exact (eq_trans (HPRES 21 (CS 21 ltac:(lia))) E1_21).
  assert (E2_22 : reg_get R2 22 = getr regs 22) by exact (eq_trans (HPRES 22 (CS 22 ltac:(lia))) E1_22).
  assert (E2_23 : reg_get R2 23 = getr regs 23) by exact (eq_trans (HPRES 23 (CS 23 ltac:(lia))) E1_23).
  assert (E2_24 : reg_get R2 24 = getr regs 24) by exact (eq_trans (HPRES 24 (CS 24 ltac:(lia))) E1_24).
  assert (E2_25 : reg_get R2 25 = getr regs 25) by exact (eq_trans (HPRES 25 (CS 25 ltac:(lia))) E1_25).
  assert (E2_26 : reg_get R2 26 = getr regs 26) by exact (eq_trans (HPRES 26 (CS 26 ltac:(lia))) E1_26).
  assert (E2_27 : reg_get R2 27 = getr regs 27) by exact (eq_trans (HPRES 27 (CS 27 ltac:(lia))) E1_27).
  change (getr R1 1) with (reg_get R1 1). rewrite E1_1.
  set (W3 := [(hl_v l + 16 * IX, hl_v l + 16 * (hl_n l - 1)); (LA + 8, LA + 12)]).
  eapply (lift_run R2 (Z_to_bv 64 0x146b4) m2 md2 W3
    (fun m' => rw_cells rsegs m' LA [C8 (Z_to_bv 64 (hl_v l)); C4 (Z_to_bv 64 (hl_n l - 1)); C4 (Z_to_bv 64 (hl_cap l))] /\
               rw_cells rsegs m' (hl_v l)
                 [CB (Z.to_nat (16 * hl_cap l))
                     (concat (map text_rec (firstn (Z.to_nat IX) (hl_recs l) ++ skipn (S (Z.to_nat IX)) (hl_recs l))) ++
                      text_rec (last (hl_recs l) (0, [])) ++ hl_junk l)])
    (fun R pc' => pc' = getr regs 1 /\ forall R', Regs6ss.xregs_eqv R R' -> regs_preserved regs R'));
    [exact Hh2 | exact Hl2 | exact RO2 | |].
  { unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_3, E2_4, E2_8, E2_9, E2_18, E2_19, E2_20, E2_21, E2_22, E2_23, E2_24, E2_25, E2_26, E2_27.
    replace (Z_to_bv 64 (S0 - 32)) with (Z_to_bv 64 (bv_unsigned (getr regs 2) - 32)) by (rewrite ES'; reflexivity).
    replace (Z_to_bv 64 (16 * IX)) with (Z_to_bv 64 (16 * bv_unsigned (Z_to_bv 64 IX))) by (rewrite UIX; reflexivity).
    eapply evt_mono.
    { apply (ld_run2 MMV) with (sp0 := getr regs 2) (ra0 := getr regs 1) (s00 := getr regs 8) (s01 := getr regs 9)
        (s02 := getr regs 18) (V := hl_v l) (N := hl_n l) (CAP := hl_cap l)
        (us := concat (map text_rec (hl_recs l)) ++ hl_junk l);
      [ exact FRn | rewrite ULA; exact LCn2 | exact ARRn2 | exact LUS | rewrite UIX; lia | lia | lia | lia
      | rewrite ULA; exact DLV | rewrite ULA, ES'; ld_lz | rewrite ES'; ld_lz | rewrite ES'; ld_lz | exact MI2 ]. }
    intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM'
      & P1 & P2).
    rewrite ULA, UIX in MU'. rewrite ULA in P1. rewrite UIX in P2.
    eexists _, _, m'. split; [reflexivity|].
    split; [split; [apply ret_pc_of_ok; exact HRA | intros R'' X'; eapply pres_mkR; [exact X' | reflexivity ..]]|].
    split; [exact MU'|]. split; [exact WM'|].
    split; [exact P1|].
    pose proof (rw_cells_of_u8arr rsegs _ _ _ P2) as Y.
    pose proof (ld_res_len (concat (map text_rec (hl_recs l)) ++ hl_junk l) IX (hl_n l) (hl_cap l)
                  ltac:(lia) ltac:(lia) LUS) as YL.
    unfold hl_n in Y, YL.
    rewrite (ld_mm (hl_recs l) (hl_junk l) IX ltac:(unfold hl_n in HI; lia)) in Y, YL.
    apply (ld_cb_eq _ _ _ _ _ _ _ Y); [lia | reflexivity]. }
  intros Rb R' pc' m3 m'3 (EPC & HPR) X3 MU3 WM3 RO3 REL3 (P1 & P2).
  pose proof (HPR R' X3) as PRES. subst pc'.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL3 P1) as LC3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL3 P2) as ARR3.
  clear P1 P2.
  pose proof (lmid_trans Bm API LIST_DROP_K S0 _ _ _ _ L A mem md L A m1 md L2 A2 m2 md2 HWF MID1 MID2) as MID12.
  pose proof MID12 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC12).
  assert (MID3 : lmid Bm API LIST_DROP_K S0
                   (fun a => LA + 8 <= a < LA + 12 \/ hl_v l + 16 * IX <= a < hl_v l + 16 * (hl_n l - 1))
                   (fun _ => False) L2 A2 m2 md2 L2 A2 m3 md2).
  { apply (lmid_A Bm API SEG AX LIST_DROP_K S0 _ L2 A2 m2 md2 m3 W3);
      [exact M2 | exact W2 | exact BD2 | rewrite KV; ld_lz | ld_lz | exact SC12 | exact MU3 | rewrite SEG; exact WM3 | |].
    - intros a Ha O. unfold W3 in O. apply ld_out2 in O. right.
      destruct O as [O|O]; [right; exact O | left; exact O].
    - intros a Ha Ho. unfold W3. cbn [outside].
      split.
      { intro Y. apply (proj2 (proj2 (proj2 (block_facts Bm _ LAWS _ _ _ _ _ _ (a - hl_v l) M2 INV2 ltac:(ld_lz))))).
        replace (hl_v l + (a - hl_v l)) with a by ring. exact Ho. }
      split; [|exact I].
      intro Y. exact (lf_img_not_owned Bm API AX L2 A2 m2 md2 a M2 (proj1 (LAI a ltac:(ld_lz))) Ho). }
  pose proof (lmid_trans Bm API LIST_DROP_K S0 _ _ _ _ L A mem md L2 A2 m2 md2 L2 A2 m3 md2 HWF MID12 MID3) as MIDf.
  rewrite ES in MIDf.
  pose proof (rp_of_lmid Bm API _ _ _ L A regs mem md L2 A2 R' m3 md2 HWF MIDf PRES) as RP0.
  assert (ND0' : List.NoDup (map fst (hl_recs l))) by first [exact ND0 | exact (proj1 (NoDup_ListNoDup _) ND0)].
  destruct (ld_nodup_rm (hl_recs l) (Z.to_nat IX) (0, []) Hk ND0') as [NDr NEr].
  rewrite <- Er in NEr.
  set (rs' := firstn (Z.to_nat IX) (hl_recs l) ++ skipn (S (Z.to_nat IX)) (hl_recs l)) in *.
  assert (HN2 : hl_n (HL (hl_v l) (hl_cap l) rs' (text_rec (last (hl_recs l) (0, [])) ++ hl_junk l)) = hl_n l - 1).
  { unfold hl_n. cbn [hl_recs]. unfold rs'.
    destruct (ld_split (hl_recs l) (Z.to_nat IX) (0, []) Hk) as (_ & L1 & L2').
    rewrite length_app, L1, L2'. lia. }
  apply SR_ret. unfold ld_post. cbv beta. rewrite <- Er.
  exists L2, A2, R', m3, md2, (HL (hl_v l) (hl_cap l) rs' (text_rec (last (hl_recs l) (0, [])) ++ hl_junk l)).
  split; [rewrite SEG; reflexivity|].
  split.
  { eapply rp_shrink.
    - eapply rp_F_weaken; [exact RP0|]. intros q Hq. cbv beta in Hq. destruct Hq as [[[]|Hq]|[]]. exact Hq.
    - intros a Ha. cbv beta in Ha. destruct Ha as [[[]|[]]|Ha]. left. exact Ha. }
  split; [exact (INITI INIT)|].
  split.
  { exists []. split; [reflexivity|]. split.
    - rewrite (ld_tr_nth (known_at L A) l (Z.to_nat IX) Hk), <- Er. unfold known_at, runF, run_tr. cbn [run_from resolve].
      rewrite <- Ep, (sptr_of_eq L A p _ NDL Hp). exact RES'.
    - split.
      + apply (ld_sh_real L A L2 l _ (Z.to_nat IX) HWF NDL LY2);
          [intros _; exists (16 * hl_cap l); exact INV | | reflexivity | reflexivity | reflexivity].
        intros r' Ir'.
        destruct (proj1 (Forall_forall _ _) TXF0 r' (ld_in_sub (hl_recs l) (Z.to_nat IX) (0, []) r' Hk Ir')) as (T1 & _).
        eexists. exact T1.
      + apply (ld_sh_live L A A2 l (Z.to_nat IX) p NDL UBK).
        * intros _. exists (16 * hl_cap l). split; [exact INV|]. rewrite Ep. exact NVR.
        * intros r' Ir'.
          destruct (proj1 (Forall_forall _ _) TXF0 r' (ld_in_sub (hl_recs l) (Z.to_nat IX) (0, []) r' Hk Ir')) as (T1 & _).
          eexists. split; [exact T1|]. rewrite Ep. exact (NEr r' Ir'). }
  split; [rewrite SEG; exact RO3|].
  split.
  { unfold list_at. cbn [hl_v hl_cap hl_recs hl_junk]. rewrite SEG, HN2.
    split; [exact LC3|].
    split; [lia|].
    split.
    { right. split; [lia|]. split; [exact INV2|]. split; [exact FV|].
      split; [rewrite length_app, ld_tr_len; lia | exact ARR3]. }
    split; [first [exact NDr | apply NoDup_ListNoDup; exact NDr]|].
    split.
    { intro I0. apply NV0. apply in_map_iff in I0. destruct I0 as (y & Ey & Iy). rewrite <- Ey. apply in_map.
      exact (ld_in_sub (hl_recs l) (Z.to_nat IX) (0, []) y Hk Iy). }
    apply Forall_forall. intros r' Ir'.
    pose proof (ld_in_sub (hl_recs l) (Z.to_nat IX) (0, []) r' Hk Ir') as Ir0.
    pose proof (NEr r' Ir') as NE'.
    destruct (proj1 (Forall_forall _ _) TXF0 r' Ir0) as (T1 & T2 & T3 & T4 & T5).
    pose proof T2 as (T21 & T22 & T23).
    split.
    { pose proof T1 as T1'. rewrite BLK1 in T1'. rewrite BLK2. apply (ld_in_rm b1 b2 _ _ T1').
      intro E0. injection E0 as E0 _. exact (NE' E0). }
    split; [exact T2|].
    split; [|split; [exact T4 | exact T5]].
    assert (NEV : fst r' <> hl_v l) by (intro Y; apply NV0; rewrite <- Y; exact (in_map fst _ _ Ir0)).
    pose proof (blocks_disjoint Bm API L A mem md _ _ _ _ HMR T1 INV NEV) as D1.
    pose proof (ld_disj (in_img Bm) LA 16 (fst r') (Z.of_nat (length (snd r')) + 1) ltac:(ld_lz) ltac:(ld_lz)
                  (fun j Hj => proj1 (proj1 (LAI (LA + j) ltac:(ld_lz)))) T23) as D2.
    destruct (lf_blocks_in L A _ _ T1) as (p' & Hp' & Ep').
    assert (Hp2' : In (p', Z.of_nat (length (snd r')) + 1) (user_blocks A2)).
    { apply UBK; [exact Hp'|]. intro Y. subst p'. apply NE'. congruence. }
    assert (Q1 : rw_cells rsegs m1 (fst r') [CB (length (snd r') + 1) (snd r' ++ [Z_to_bv 8 0])]).
    { apply TR1; [exact T3 | cbn [cells_size csize]; ld_lz]. }
    assert (Q2 : rw_cells rsegs m2 (fst r') [CB (length (snd r') + 1) (snd r' ++ [Z_to_bv 8 0])]).
    { rewrite <- SEG.
      apply (rw_cp_block Bm API 8192 L A R1 m1 md _ L2 A2 R2 m2 md2 p' _ (fst r') _ POST Hp' Hp2');
        [rewrite Ep'; lia | cbn [cells_size csize]; rewrite Ep'; lia | rewrite SEG; exact Q1]. }
    apply (rw_cells_transport rsegs W3 m2 m3 _ _ Q2 MU3 WM3). unfold W3. cbn [disjoint_from cells_size csize].
    destruct D1 as [Y1|Y1]; destruct D2 as [Y2|Y2]; repeat split; ld_lz. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  exists b1, b2. split; [exact BLK1 | exact BLK2].
Qed.

Theorem list_drop_holds : free_contract_rt Bm API F -> memmove_contract -> list_drop_contract Bm API F.
Proof.
  intros FRE MMV. unfold list_drop_contract.
  intros L A regs mem md bnd l lines. cbv zeta.
  intros SEG PRE INIT RO LAI LIST HI RES.
  assert (GS : forall P, SR rsegs (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_DROP) mem (seg_rom rsegs)) md) P ->
                 SR (ms_segs Bm) (mkCfg (YK11.mkst regs (Z_to_bv 64 LIST_DROP) mem (seg_rom (ms_segs Bm))) md) P)
    by (rewrite SEG; intros P H; exact H).
  apply GS.
  rewrite SEG in RO, LAI.
  pose proof (bv_unsigned_in_range 64 (getr regs 10)) as Q10. change (bv_modulus 64) with (2 ^ 64) in Q10.
  pose proof (bv_unsigned_in_range 64 (getr regs 11)) as Q11. change (bv_modulus 64) with (2 ^ 64) in Q11.
  exact (ld_main FRE MMV L A regs mem md bnd l lines (bv_unsigned (getr regs 10)) (bv_unsigned (getr regs 11))
    (spZ regs) (eq_sym (Z_to_bv_bv_unsigned _)) (eq_sym (Z_to_bv_bv_unsigned _)) eq_refl Q10 Q11 SEG PRE INIT RO LAI
    LIST HI RES).
Qed.

End LDP.
