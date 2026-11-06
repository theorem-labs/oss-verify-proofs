(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_msgpack_encoder/lib/CJ/Ref/Mh_0118.v, with its module paths, module names and addresses changed; 1147 of its 1229 lines of code are new or changed and 2359 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/drain_b_seg.v, with its module paths, module names and numbers changed; 537 of its 623 lines of code are new or changed and 1143 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/relay_finish_seg.v, with its module names changed; 787 of its 829 lines of code are new or changed and 581 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/Prog/CF/list_push.v, with its module paths, module names, addresses and numbers changed; 601 of its 675 lines of code are new or changed and 755 lines of the source are left out. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import Tac Arr Bytes.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs Monad Specs.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YO0i YO0f YO0d YO05 YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Reusable Require YO10.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Contract ContractT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayFrame RelayRunT RelayRunF HarnessRep ListRep ListTr TrModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import ListStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import memcpy_c list_push_run KindB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import ListFrame list_push_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog.CF Require Import SRCF SRCF3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma lp_concat_snoc : forall recs (d : Z) (x : list byte),
  concat (map text_rec (recs ++ [(d, x)])) =
  concat (map text_rec recs) ++ le8 (Z_to_bv 64 d) ++ le8 (Z_to_bv 64 (Z.of_nat (length x))).
Proof. intros recs d x. rewrite map_app, concat_app. cbn [map concat]. rewrite app_nil_r. reflexivity. Qed.

Lemma lp_concat_len : forall recs, length (concat (map text_rec recs)) = (16 * length recs)%nat.
Proof.
  induction recs as [|r recs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
  unfold text_rec. rewrite length_app, !length_le8. cbn [length]. lia.
Qed.

Lemma lp_grow : forall N CAP, 0 <= N <= CAP -> N + 1 <= grow_cap N CAP /\
  (N < CAP -> grow_cap N CAP = CAP) /\ (N = CAP -> CAP = 0 -> grow_cap N CAP = 8) /\
  (N = CAP -> 0 < CAP -> grow_cap N CAP = 2 * CAP).
Proof.
  intros N CAP H. unfold grow_cap.
  destruct (Z.eqb_spec N CAP); destruct (Z.eqb_spec CAP 0); repeat split; intros; lia.
Qed.

Lemma lp_nodup_snoc : forall (l : list Z) a, List.NoDup l -> ~ List.In a l -> List.NoDup (l ++ [a]).
Proof.
  induction l as [|b l IH]; intros a H1 H2.
  - cbn. apply List.NoDup_cons; [intro X; exact X | apply List.NoDup_nil].
  - apply List.NoDup_cons_iff in H1. destruct H1 as [Hb Hl]. cbn [app]. apply List.NoDup_cons.
    + intro X. apply in_app_or in X. destruct X as [X|[X|[]]]; [exact (Hb X) | apply H2; left; symmetry; exact X].
    + apply IH; [exact Hl | intro X; apply H2; right; exact X].
Qed.

Lemma lp_disj : forall (P : Z -> Prop) a1 k1 a2 k2, 0 < k1 -> 0 < k2 ->
  (forall i, 0 <= i < k1 -> P (a1 + i)) -> (forall i, 0 <= i < k2 -> ~ P (a2 + i)) ->
  a1 + k1 <= a2 \/ a2 + k2 <= a1.
Proof.
  intros P a1 k1 a2 k2 K1 K2 H1 H2.
  destruct (Z_le_gt_dec (a1 + k1) a2) as [D|D]; [left; exact D|].
  destruct (Z_le_gt_dec (a2 + k2) a1) as [D'|D']; [right; exact D'|]. exfalso.
  apply (H2 (Z.max a1 a2 - a2) ltac:(lia)).
  replace (a2 + (Z.max a1 a2 - a2)) with (a1 + (Z.max a1 a2 - a1)) by lia. apply H1. lia.
Qed.

Lemma lp_cb_eq : forall segs m a (k k' : nat) bs bs', rw_cells segs m a [CB k bs] -> k = k' -> bs = bs' ->
  rw_cells segs m a [CB k' bs'].
Proof. intros segs m a k k' bs bs' H -> ->. exact H. Qed.

Ltac lpz := repeat match goal with
  | H : _ \/ _ |- _ => clear H
  | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
  end; lia.

Lemma lp_sh_n : forall nm l, sh_n (sh_of nm l) = hl_n l.
Proof. intros nm l. unfold sh_n, sh_of, hl_n. cbn [sh_recs]. rewrite length_map. reflexivity. Qed.

Lemma lp_grow_tr : forall nm l, list_grow_tr (sh_of nm l) =
  if hl_n l =? hl_cap l then
    (if hl_cap l =? 0 then [RMalloc 128] else [RRealloc (16 * hl_cap l) (32 * hl_cap l) (nm (hl_v l))])
  else [].
Proof. intros nm l. unfold list_grow_tr. rewrite lp_sh_n. reflexivity. Qed.

Lemma lp_grow_run_app : forall (F : ResFormT) L A l qs0 post b,
  length qs0 = nretF (list_grow_tr (sh_of (known_at L A) l)) ->
  runF F (qs0 ++ post) b (list_grow_tr (sh_of (known_at L A) l)) = runF F qs0 b (list_grow_tr (sh_of (known_at L A) l)).
Proof.
  intros F L A l qs0 post b H. rewrite lp_grow_tr in *.
  destruct (hl_n l =? hl_cap l); [destruct (hl_cap l =? 0)|]; [reflexivity| |reflexivity].
  destruct qs0 as [|q [|q' qs]]; cbn in H; [lia | reflexivity | lia].
Qed.

Lemma lp_push_len : forall nm l x qs0 (qd : sptr), length qs0 = nretF (list_grow_tr (sh_of nm l)) ->
  length (qs0 ++ [qd]) = nretF (list_push_tr (sh_of nm l) (bzs x)).
Proof. intros nm l x qs0 qd H. unfold list_push_tr. rewrite length_app, nret_app, H. reflexivity. Qed.

Lemma lp_push_run : forall (F : ResFormT) L A l x qs0 qd b,
  length qs0 = nretF (list_grow_tr (sh_of (known_at L A) l)) ->
  runF F (qs0 ++ [qd]) b (list_push_tr (sh_of (known_at L A) l) (bzs x)) =
  rt_malloc F (runF F qs0 b (list_grow_tr (sh_of (known_at L A) l))) (Z.of_nat (length x) + 1).
Proof.
  intros F L A l x qs0 qd b H. rewrite <- (lp_grow_run_app F L A l qs0 [qd] b H).
  unfold runF, run_tr, list_push_tr. rewrite run_from_app. unfold bzs. rewrite length_map. reflexivity.
Qed.

Lemma lp_room_tail : forall (F : ResFormT) L A l x qs0 b,
  length qs0 = nretF (list_grow_tr (sh_of (known_at L A) l)) ->
  (forall qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) ->
     roomF F qs b (list_push_tr (sh_of (known_at L A) l) (bzs x))) ->
  rt_room F (runF F qs0 b (list_grow_tr (sh_of (known_at L A) l))) (Z.of_nat (length x) + 1).
Proof.
  intros F L A l x qs0 b H R.
  specialize (R (qs0 ++ [SP 0 0]) (lp_push_len (known_at L A) l x qs0 (SP 0 0) H)).
  rewrite <- (lp_grow_run_app F L A l qs0 [SP 0 0] b H).
  unfold roomF, room_run, list_push_tr in R. apply room_from_app in R. destruct R as [_ R].
  unfold bzs in R. rewrite length_map in R. cbn [room_from] in R. exact (proj1 R).
Qed.

Lemma lp_room_grow : forall (F : ResFormT) L A l x b,
  (forall qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) ->
     roomF F qs b (list_push_tr (sh_of (known_at L A) l) (bzs x))) ->
  hl_n l = hl_cap l -> rt_room F b (if hl_cap l =? 0 then 128 else 32 * hl_cap l).
Proof.
  intros F L A l x b R E.
  assert (LQ : length [SP 0 0] = nretF (list_grow_tr (sh_of (known_at L A) l))).
  { rewrite lp_grow_tr, (proj2 (Z.eqb_eq _ _) E). destruct (hl_cap l =? 0); reflexivity. }
  specialize (R _ (lp_push_len (known_at L A) l x _ (SP 0 0) LQ)).
  unfold roomF, room_run, list_push_tr in R. apply room_from_app in R. destruct R as [R _].
  rewrite lp_grow_tr, (proj2 (Z.eqb_eq _ _) E) in R.
  destruct (hl_cap l =? 0); cbn [room_from] in R; exact (proj1 R).
Qed.

Lemma lp_real : forall L A L2 qs0 qd (l : hlist) V1 G d (x : list byte) jr,
  (forall a k, In (a, k) (blocks L A) -> In (sptr_of L A a, k) (user_blocks A) /\ ptr_addr L (sptr_of L A a) = a) ->
  WF A -> layout_le A L L2 -> hl_n l <= hl_cap l ->
  (0 < hl_cap l -> In (hl_v l, 16 * hl_cap l) (blocks L A)) ->
  Forall (fun r => exists k, 0 < k /\ In (fst r, k) (blocks L A)) (hl_recs l) ->
  G = grow_cap (hl_n l) (hl_cap l) ->
  length qs0 = nretF (list_grow_tr (sh_of (known_at L A) l)) ->
  (hl_n l < hl_cap l -> V1 = hl_v l) ->
  (hl_n l = hl_cap l -> ptr_addr L2 (nth 0 qs0 (SP 0 0)) = V1) ->
  ptr_addr L2 qd = d ->
  sh_real L2 (qs0 ++ [qd]) (list_push_sh 0 (sh_of (known_at L A) l) (bzs x)) (HL V1 G (hl_recs l ++ [(d, x)]) jr).
Proof.
  intros L A L2 qs0 qd l V1 G d x jr SPEC HW LY NC HV HR EG LQ HV1 HV2 HD.
  rewrite lp_grow_tr in LQ.
  assert (N0 : 0 <= hl_n l) by (unfold hl_n; lia).
  assert (KR : forall r, In r (hl_recs l) -> ptr_addr L2 (sptr_of L A (fst r)) = fst r).
  { intros r Ir. destruct (proj1 (Forall_forall _ _) HR r Ir) as [k [_ Hk]].
    destruct (SPEC _ _ Hk) as [Hu Ha]. rewrite (lf_addr A L L2 _ k HW LY Hu). exact Ha. }
  assert (RECS : forall j, length qs0 = j ->
    map fst (hl_recs l ++ [(d, x)]) =
    map (fun r => ptr_addr L2 (resolveF (qs0 ++ [qd]) (fst r))) (map (shr (known_at L A)) (hl_recs l) ++ [(Ret j, bzs x)])).
  { intros j Hj. rewrite !map_app, map_map. cbn [map fst]. f_equal.
    - apply map_ext_in. intros r Ir. unfold shr, known_at. cbn [fst resolve]. symmetry. exact (KR r Ir).
    - f_equal. cbn [resolve]. rewrite app_nth2 by lia. rewrite Hj, Nat.sub_diag. cbn [nth]. rewrite HD. reflexivity. }
  assert (KEYS : forall s a, sh_recs s = map (shr (known_at L A)) (hl_recs l) ++ [(a, bzs x)] ->
    map (fun r => bzs (snd r)) (hl_recs l ++ [(d, x)]) = sh_keys s).
  { intros s a Hs. unfold sh_keys. rewrite Hs, !map_app, map_map. reflexivity. }
  unfold sh_real, list_push_sh. rewrite lp_sh_n.
  change (sh_cap (sh_of (known_at L A) l)) with (hl_cap l).
  change (sh_v (sh_of (known_at L A) l)) with (known_at L A (hl_v l)).
  change (sh_recs (sh_of (known_at L A) l)) with (map (shr (known_at L A)) (hl_recs l)).
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E]; cbn [sh_cap sh_v sh_recs hl_cap hl_v hl_recs].
  - assert (LQ1 : length qs0 = 1%nat) by (rewrite LQ; destruct (hl_cap l =? 0); reflexivity).
    split; [exact EG|]. split.
    + intros _. cbn [resolve]. rewrite app_nth1 by lia. symmetry. exact (HV2 E).
    + split; [apply (KEYS _ (Ret 1%nat)); reflexivity | exact (RECS 1%nat LQ1)].
  - split; [rewrite EG; unfold grow_cap; rewrite (proj2 (Z.eqb_neq _ _) E); reflexivity|]. split.
    + intros Hc. unfold known_at. cbn [resolve]. rewrite (HV1 ltac:(lia)).
      destruct (SPEC _ _ (HV ltac:(lia))) as [Hu Ha]. rewrite (lf_addr A L L2 _ _ HW LY Hu). symmetry. exact Ha.
    + split; [apply (KEYS _ (Ret 0%nat)); reflexivity | exact (RECS 0%nat LQ)].
Qed.

Lemma lp_live : forall L A A2 qs0 qd (l : hlist) (x : list byte),
  (forall a k, In (a, k) (blocks L A) -> In (sptr_of L A a, k) (user_blocks A) /\ ptr_addr L (sptr_of L A a) = a) ->
  (forall p k, In (p, k) (user_blocks A) -> 0 < k -> ~ (hl_n l = hl_cap l /\ 0 < hl_cap l /\ ptr_addr L p = hl_v l) ->
     In (p, k) (user_blocks A2)) ->
  hl_n l <= hl_cap l ->
  (0 < hl_cap l -> In (hl_v l, 16 * hl_cap l) (blocks L A)) ->
  Forall (fun r => exists k, 0 < k /\ In (fst r, k) (blocks L A)) (hl_recs l) ->
  ~ In (hl_v l) (map fst (hl_recs l)) ->
  length qs0 = nretF (list_grow_tr (sh_of (known_at L A) l)) ->
  (hl_n l = hl_cap l -> exists k, In (nth 0 qs0 (SP 0 0), k) (user_blocks A2)) ->
  (exists k, In (qd, k) (user_blocks A2)) ->
  sh_live A2 (qs0 ++ [qd]) (list_push_sh 0 (sh_of (known_at L A) l) (bzs x)).
Proof.
  intros L A A2 qs0 qd l x SPEC KEEP NC HV HR NV LQ HQ HD.
  rewrite lp_grow_tr in LQ.
  assert (N0 : 0 <= hl_n l) by (unfold hl_n; lia).
  assert (RECS : forall j r, length qs0 = j -> In r (map (shr (known_at L A)) (hl_recs l) ++ [(Ret j, bzs x)]) ->
    exists k, In (resolveF (qs0 ++ [qd]) (fst r), k) (user_blocks A2)).
  { intros j r Hj Ir. apply in_app_or in Ir. destruct Ir as [Ir|[<-|[]]].
    - apply in_map_iff in Ir as (r0 & <- & Ir0). unfold shr, known_at. cbn [fst resolve].
      destruct (proj1 (Forall_forall _ _) HR r0 Ir0) as (k & Hk0 & Hk).
      destruct (SPEC _ _ Hk) as [Hu Ha]. exists k. apply KEEP; [exact Hu | exact Hk0 |].
      intros (_ & _ & E'). apply NV. rewrite <- E', Ha. exact (in_map fst _ _ Ir0).
    - cbn [fst resolve]. rewrite app_nth2 by lia. rewrite Hj, Nat.sub_diag. cbn [nth]. exact HD. }
  unfold sh_live, list_push_sh. rewrite lp_sh_n.
  change (sh_cap (sh_of (known_at L A) l)) with (hl_cap l).
  change (sh_v (sh_of (known_at L A) l)) with (known_at L A (hl_v l)).
  change (sh_recs (sh_of (known_at L A) l)) with (map (shr (known_at L A)) (hl_recs l)).
  destruct (Z.eqb_spec (hl_n l) (hl_cap l)) as [E|E]; cbn [sh_cap sh_v sh_recs].
  - assert (LQ1 : length qs0 = 1%nat) by (rewrite LQ; destruct (hl_cap l =? 0); reflexivity).
    split; [|intros r Ir; exact (RECS 1%nat r LQ1 Ir)].
    intros _. cbn [resolve]. rewrite app_nth1 by lia. exact (HQ E).
  - split; [|intros r Ir; exact (RECS 0%nat r LQ Ir)].
    intros Hc. unfold known_at. cbn [resolve].
    destruct (SPEC _ _ (HV ltac:(lia))) as [Hu Ha]. exists (16 * hl_cap l).
    apply KEEP; [exact Hu | lia | intros (E' & _); exact (E E')].
Qed.

Section LPP.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable Bm : malloc_syms.
Variable API : AllocAPI Bm.
Variable Fr : ResFormT.
Hypothesis AX : AllocExtra Bm (aa_MR API).
Hypothesis CTX : ctx_owned Bm API.
Hypothesis MALLOC_PC : ms_malloc Bm = 0x1608c.
Hypothesis ERRNO_LOW : errno_addr Bm + 4 <= YM05.alloc_ceiling.
Hypothesis NDB : blocks_nodup Bm API.
Hypothesis MALLOC : malloc_contract_rt Bm API Fr.
Hypothesis MEMCPY : memcpy_contract.

Lemma lpu_block_aligned : forall L A mem md q k, aa_MR API L A mem md -> In (q, k) (blocks L A) -> q mod 8 = 0.
Proof.
  intros L A mem md q k HM Hin. unfold blocks in Hin. apply in_map_iff in Hin as ([p k'] & E & Hp).
  cbn [fst snd] in E. injection E as <- <-.
  pose proof (mr_blocks_aligned Bm _ (aa_laws API) L A mem md p k' HM Hp) as H16.
  Z.div_mod_to_equations. lia.
Qed.

Definition lp_post (L : layout) (A : astate) (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
    (bnd : rt_R Fr) (LA N CAP V n : Z) (lines : bool) (x : list byte) (l : hlist) : config -> Prop :=
  fun c' => exists L' A' regs' mem' md' (l' : hlist) (d : Z),
    c' = mkCfg (YK11.mkst regs' (getr regs 1) mem' (seg_rom (ms_segs Bm))) md' /\
    relay_post Bm API LIST_PUSH_K
      (fun a => LA <= a < LA + 16 \/ (N < CAP /\ V + 16 * N <= a < V + 16 * (N + 1)))
      (fun q => N = CAP /\ 0 < CAP /\ q = V)
      L A regs mem md L' A' regs' mem' md' /\
    st_init_done A' = true /\
    (exists qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) /\
       rt_ok Fr A' (runF Fr qs bnd (list_push_tr (sh_of (known_at L A) l) (bzs x))) /\
       sh_real L' qs (list_push_sh 0 (sh_of (known_at L A) l) (bzs x)) l' /\
       sh_live A' qs (list_push_sh 0 (sh_of (known_at L A) l) (bzs x))) /\
    ro_agree (ms_segs Bm) mem' /\
    list_at Bm L' A' mem' LA l' lines /\
    hl_recs l' = hl_recs l ++ [(d, x)] /\
    hl_cap l' = grow_cap N CAP /\
    (N < CAP -> hl_v l' = V) /\
    (forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks l) -> In (q, m) (blocks L' A')) /\
    (forall q m, In (q, m) (blocks L' A') -> (In (q, m) (blocks L A) /\ (0 < m -> ~ In q (list_blocks l))) \/ In q (list_blocks l')) /\
    (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks l) -> ~ In q (list_blocks l')).

Lemma lp_spec : forall L A mem md, aa_MR API L A mem md ->
  forall a k, In (a, k) (blocks L A) -> In (sptr_of L A a, k) (user_blocks A) /\ ptr_addr L (sptr_of L A a) = a.
Proof.
  intros L A mem md HM a k Hk. apply sptr_of_spec; [|exact Hk].
  first [ exact (NDB L A mem md HM) | apply (proj2 (stdpp.base.NoDup_ListNoDup _)); exact (NDB L A mem md HM)
        | apply (proj1 (stdpp.base.NoDup_ListNoDup _)); exact (NDB L A mem md HM) ].
Qed.

Lemma lp_tail : forall L A regs mem md (bnd : rt_R Fr) (l : hlist) lines x L1 A1 R1 m1 md1 (V1 G : Z)
    (j0 junk1 : list byte) (E1 F1 : Z -> Prop) (LA SRC n S : Z) (qs0 : list sptr),
  let N := hl_n l in let CAP := hl_cap l in let V := hl_v l in
  ms_segs Bm = rsegs ->
  call_pre_k Bm (aa_MR API) LIST_PUSH_K L A regs mem md -> S = spZ regs ->
  (forall a, LA <= a < LA + 16 -> img_plain Bm a /\ ro_addr rsegs (Z_to_bv 64 a) = false) ->
  list_at Bm L A mem LA l lines ->
  (N = CAP -> CAP < 2 ^ 29) -> n < 2 ^ 64 - 1 -> Z.of_nat (length x) = n -> 0 <= SRC < 2 ^ 64 ->
  (SRC + n <= LA \/ LA + 16 <= SRC) ->
  (lines = true -> ~ In (Z_to_bv 8 0) x /\ n <= 6000) -> (lines = false -> 1 <= n) ->
  lmid Bm API LIST_PUSH_K S E1 F1 L A mem md L1 A1 m1 md1 ->
  (forall a, E1 a -> LA <= a < LA + 16) ->
  (forall q, F1 q -> N = CAP /\ 0 < CAP /\ q = V) ->
  reg_get R1 1 = Z_to_bv 64 0x148c0 -> reg_get R1 2 = Z_to_bv 64 (S - 48) -> reg_get R1 4 = getr regs 4 ->
  reg_get R1 8 = Z_to_bv 64 LA -> reg_get R1 9 = Z_to_bv 64 n -> reg_get R1 10 = Z_to_bv 64 (n + 1) ->
  reg_get R1 18 = Z_to_bv 64 SRC ->
  reg_get R1 3 = getr regs 3 -> reg_get R1 20 = getr regs 20 -> reg_get R1 21 = getr regs 21 ->
  reg_get R1 22 = getr regs 22 -> reg_get R1 23 = getr regs 23 -> reg_get R1 24 = getr regs 24 ->
  reg_get R1 25 = getr regs 25 -> reg_get R1 26 = getr regs 26 -> reg_get R1 27 = getr regs 27 ->
  rw_cells rsegs m1 (S - 48) [CB 8 j0; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8);
                              C8 (getr regs 1)] ->
  rw_cells rsegs m1 LA [C8 (Z_to_bv 64 V1); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 G)] ->
  G = grow_cap N CAP ->
  In (V1, 16 * G) (blocks L1 A1) -> fresh_block Bm V1 (16 * G) ->
  rw_cells rsegs m1 V1 [CB (Z.to_nat (16 * N)) (concat (map text_rec (hl_recs l)));
                        CB (Z.to_nat (16 * (G - N))) junk1] ->
  (N < CAP -> V1 = V) ->
  Forall (fun r => In (fst r, text_len r) (blocks L1 A1) /\
                   rw_cells rsegs m1 (fst r) [CB (length (snd r) + 1) (snd r ++ [Z_to_bv 8 0])]) (hl_recs l) ->
  ~ In V1 (map fst (hl_recs l)) ->
  bytes_at rsegs m1 SRC x ->
  ((S <= SRC /\ SRC + n <= 2 ^ 64) \/
   (exists q k, In (q, k) (blocks L1 A1) /\ (q <> V1 \/ k = 0) /\ q <= SRC /\ SRC + n <= q + k) \/
   (0 < n /\ 0 <= SRC /\ SRC + n <= 2 ^ 64 /\ forall i, 0 <= i < n -> ro_addr (ms_segs Bm) (Z_to_bv 64 (SRC + i)) = true)) ->
  (forall q m, In (q, m) (blocks L1 A1) -> (In (q, m) (blocks L A) /\ (0 < m -> ~ (N = CAP /\ 0 < CAP /\ q = V))) \/ q = V1) ->
  (forall q m, In (q, m) (blocks L A) -> ~ In q (list_blocks l) -> In (q, m) (blocks L1 A1)) ->
  (forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ In q (list_blocks l) -> q <> V1) ->
  st_init_done A1 = true -> length qs0 = nretF (list_grow_tr (sh_of (known_at L A) l)) ->
  rt_ok Fr A1 (runF Fr qs0 bnd (list_grow_tr (sh_of (known_at L A) l))) ->
  (forall qs, length qs = nretF (list_push_tr (sh_of (known_at L A) l) (bzs x)) ->
     roomF Fr qs bnd (list_push_tr (sh_of (known_at L A) l) (bzs x))) ->
  (N = CAP -> exists k, In (nth 0 qs0 (SP 0 0), k) (user_blocks A1) /\ ptr_addr L1 (nth 0 qs0 (SP 0 0)) = V1) ->
  ro_agree rsegs m1 ->
  SR rsegs (mkCfg (YK11.mkst R1 (Z_to_bv 64 0x1608c) m1 (seg_rom rsegs)) md1)
    (lp_post L A regs mem md bnd LA N CAP V n lines x l).
Proof.
  intros L A regs mem md bnd l lines x L1 A1 R1 m1 md1 V1 G j0 junk1 E1 F1 LA SRC n S qs0 N CAP V
    SEG PRE ES LAI LIST NCAP NB LX SR0 SLA LT LF MID1 HE1 HF1 E1_1 E1_2 E1_4 E1_8 E1_9 E1_10 E1_18
    E1_3 E1_20 E1_21 E1_22 E1_23 E1_24 E1_25 E1_26 E1_27 FR1 LC1 EG INV1 FV1 ARR1 NG TX1 V1T SRC1 SH1
    B1 B2 B3 INIT1 LQ0 RES1 ROOM PV RO1.
  pose proof (lp_room_tail Fr L A l x qs0 bnd LQ0 ROOM) as ROOM1. rewrite LX in ROOM1.
  pose proof (aa_laws API) as LAWS.
  pose proof (@YM05.alloc_ceiling_value rc) as AC. pose proof (@YM05.alloc_ceiling_lt rc) as ACL.
  pose proof PRE as (HMR & HWF & HBD & HRA & HAL & HC & H63 & HWS & HTP & HERR & HAUX).
  unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK in HC.
  pose proof MID1 as (M1 & W1 & BD1 & LY1 & LN1 & SV1 & Z1 & OW1 & MD1 & FRM1 & BK1 & SC1).
  destruct (mr_model _ _ LAWS _ _ _ _ M1) as (Hh1 & Hl1 & Hmat1).
  destruct LIST as (LC0 & NB0 & CASE0 & ND0 & NV0 & TXF0).
  pose proof (lp_spec L A mem md HMR) as SPEC0.
  assert (CV0 : 0 < hl_cap l -> In (hl_v l, 16 * hl_cap l) (blocks L A))
    by (intros Hc; destruct CASE0 as [(C0 & _)|(_ & IV & _)]; [lia | exact IV]).
  assert (HR0 : Forall (fun r => exists k, 0 < k /\ In (fst r, k) (blocks L A)) (hl_recs l)).
  { apply Forall_forall. intros r Ir. destruct (proj1 (Forall_forall _ _) TXF0 r Ir) as (T1 & _).
    exists (Z.of_nat (length (snd r)) + 1). split; [lia | exact T1]. }
  assert (KEEP1 : forall p k, In (p, k) (user_blocks A) -> 0 < k -> ~ (N = CAP /\ 0 < CAP /\ ptr_addr L p = V) ->
                    In (p, k) (user_blocks A1)) by (intros p k Hp Hk NF; exact (SV1 p k Hp Hk (fun Y => NF (HF1 _ Y)))).
  pose proof (bv_unsigned_in_range 64 (getr regs 2)) as RSP. unfold bv_modulus in RSP. cbn in RSP.
  rewrite <- ES in HC, H63, HAL, HWS.
  assert (ES' : bv_unsigned (getr regs 2) = S) by (rewrite ES; reflexivity).
  pose proof MALLOC as MAL. unfold malloc_contract_rt in MAL. rewrite SEG, MALLOC_PC in MAL.
  assert (SP1 : spZ R1 = S - 48) by (unfold spZ; change (getr R1 2) with (reg_get R1 2); rewrite E1_2; apply unsigned_lit; lia).
  eapply SR_bind.
  { apply (MAL L1 A1 R1 m1 md1 (n + 1) (runF Fr qs0 bnd (list_grow_tr (sh_of (known_at L A) l))));
      [ | exact RO1 | exact E1_10 | exact RES1 | exact ROOM1].
    apply (proj2 (call_pre_k_alloc Bm _ L1 A1 R1 m1 md1)).
    eapply (lmid_pre Bm API _ S _ _ L A regs mem md L1 A1 m1 md1 ALLOC_STACK 48 R1 PRE ES MID1 INIT1 SP1);
      [ rewrite SP1; replace (S - 48) with (S + (-3) * 16) by ring; rewrite Z.mod_add by lia; exact HAL
      | exact E1_4
      | replace (getr R1 1) with (Z_to_bv 64 0x148c0) by (symmetry; exact E1_1); apply ret_ok_even; vm_compute; reflexivity
      | lia
      | unfold LIST_PUSH_K, LIST_PUSH_FRAME, REALLOC_STACK, ALLOC_STACK; lia ]. }
  intros c2 RET.
  destruct RET as (L2 & A2 & R2 & m2 & md2 & d & -> & POST & A0' & NZ & AL & FRESH & BLK & KEPT & RO2 & GK & UBK
    & INIT & RLEN & RES').
  assert (KV : LIST_PUSH_K = 8304) by reflexivity.
  change ALLOC_STACK with 8192 in POST.
  rewrite SEG in RO2.
  pose proof POST as (M2 & W2 & BD2 & LY2 & PA2 & HPRES & HVM & HFRAME & HBLKS & HSCR).
  assert (PV2 : N = CAP -> ptr_addr L2 (nth 0 qs0 (SP 0 0)) = V1).
  { intros E. destruct (PV E) as (k & Hk & Ek). rewrite (lf_addr A1 L1 L2 _ k W1 LY2 Hk). exact Ek. }
  assert (HQ2 : N = CAP -> exists k, In (nth 0 qs0 (SP 0 0), k) (user_blocks A2)).
  { intros E. destruct (PV E) as (k & Hk & _). exists k. exact (UBK _ _ Hk). }
  assert (KEEP2 : forall p k, In (p, k) (user_blocks A) -> 0 < k -> ~ (N = CAP /\ 0 < CAP /\ ptr_addr L p = V) ->
                    In (p, k) (user_blocks A2)) by (intros p k Hp Hk NF; exact (UBK _ _ (KEEP1 p k Hp Hk NF))).
  destruct (mr_model _ _ LAWS _ _ _ _ M2) as (Hh2 & Hl2 & Hmat2).
  destruct BLK as (b1 & b2 & BLK1 & BLK2).
  pose proof FRESH as (FR_lo & FR_hi & FR_img).
  assert (N0 : 0 <= N) by (unfold N, hl_n; lia).
  assert (NC0 : N <= CAP) by (unfold N, CAP; lia).
  destruct (lp_grow N CAP ltac:(lia)) as (GB1 & GB2 & GB3 & GB4). rewrite <- EG in GB1, GB2, GB3, GB4.
  assert (GL : G < 2 ^ 30).
  { destruct (Z_lt_ge_dec N CAP) as [D|D]; [rewrite GB2 by exact D; lia|].
    destruct (Z.eq_dec CAP 0) as [D'|D']; [rewrite GB3 by lia; lia | rewrite GB4 by lia; specialize (NCAP ltac:(lia)); lia]. }
  pose proof FV1 as (FV_lo & FV_hi & FV_img).
  assert (INB : In (d, n + 1) (blocks L2 A2)) by (rewrite BLK1; apply in_or_app; right; left; reflexivity).
  assert (B12 : forall q m, In (q, m) (blocks L1 A1) -> In (q, m) (blocks L2 A2)).
  { intros q m H. rewrite BLK2 in H. rewrite BLK1. apply in_app_or in H. apply in_or_app.
    destruct H as [H|H]; [left; exact H | right; right; exact H]. }
  assert (DJd : forall q m, In (q, m) (blocks L1 A1) -> q + m <= d \/ d + (n + 1) <= q).
  { intros q m H. rewrite BLK2 in H. exact (blocks_mid_disjoint Bm _ LAWS _ _ _ _ _ _ _ _ _ _ M2 BLK1 H). }
  pose proof (DJd _ _ INV1) as DJV.
  pose proof (lpu_block_aligned L1 A1 m1 md1 V1 (16 * G) M1 INV1) as V8.
  assert (LAR : 0 <= LA /\ LA + 16 <= 2 ^ 21).
  { pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI LA ltac:(lia))))).
    pose proof (lf_img_low Bm SEG _ (proj1 (proj1 (LAI (LA + 15) ltac:(lia))))). lia. }
  assert (CS : forall r, (r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ (18 <= r <= 27)) -> callee_saved r)
    by (intros r Hr; unfold callee_saved; lia).
  assert (E2_2 : reg_get R2 2 = Z_to_bv 64 (S - 48)) by exact (eq_trans (HPRES 2 (CS 2 ltac:(lia))) E1_2).
  assert (E2_3 : reg_get R2 3 = getr regs 3) by exact (eq_trans (HPRES 3 (CS 3 ltac:(lia))) E1_3).
  assert (E2_4 : reg_get R2 4 = getr regs 4) by exact (eq_trans (HPRES 4 (CS 4 ltac:(lia))) E1_4).
  assert (E2_8 : reg_get R2 8 = Z_to_bv 64 LA) by exact (eq_trans (HPRES 8 (CS 8 ltac:(lia))) E1_8).
  assert (E2_9 : reg_get R2 9 = Z_to_bv 64 n) by exact (eq_trans (HPRES 9 (CS 9 ltac:(lia))) E1_9).
  assert (E2_18 : reg_get R2 18 = Z_to_bv 64 SRC) by exact (eq_trans (HPRES 18 (CS 18 ltac:(lia))) E1_18).
  assert (E2_20 : reg_get R2 20 = getr regs 20) by exact (eq_trans (HPRES 20 (CS 20 ltac:(lia))) E1_20).
  assert (E2_21 : reg_get R2 21 = getr regs 21) by exact (eq_trans (HPRES 21 (CS 21 ltac:(lia))) E1_21).
  assert (E2_22 : reg_get R2 22 = getr regs 22) by exact (eq_trans (HPRES 22 (CS 22 ltac:(lia))) E1_22).
  assert (E2_23 : reg_get R2 23 = getr regs 23) by exact (eq_trans (HPRES 23 (CS 23 ltac:(lia))) E1_23).
  assert (E2_24 : reg_get R2 24 = getr regs 24) by exact (eq_trans (HPRES 24 (CS 24 ltac:(lia))) E1_24).
  assert (E2_25 : reg_get R2 25 = getr regs 25) by exact (eq_trans (HPRES 25 (CS 25 ltac:(lia))) E1_25).
  assert (E2_26 : reg_get R2 26 = getr regs 26) by exact (eq_trans (HPRES 26 (CS 26 ltac:(lia))) E1_26).
  assert (E2_27 : reg_get R2 27 = getr regs 27) by exact (eq_trans (HPRES 27 (CS 27 ltac:(lia))) E1_27).
  assert (E2_10 : reg_get R2 10 = Z_to_bv 64 d) by exact A0'.
  assert (MID2 : lmid Bm API LIST_PUSH_K S (fun _ => False) (fun _ => False) L1 A1 m1 md1 L2 A2 m2 md2).
  { apply (lmid_call Bm API AX CTX LIST_PUSH_K S 8192 L1 A1 R1 m1 md1 (fun _ => False) L2 A2 R2 m2 md2
             (fun _ => False) M1 POST);
      [ intros; tauto | rewrite SP1; lia | rewrite SP1; lia | lia | lia | exact SC1
      | intros p n0 Hp _ _; exact (UBK p n0 Hp) | intros p Hp; exact (UBK p 0 Hp) | exact RLEN ]. }
  assert (NOW1 : forall a, YM05.alloc_ceiling <= a -> ~ owned Bm L1 A1 a /\ ~ owned Bm L2 A2 a).
  { intros a Ha. split; intro X;
      [pose proof (owned_low Bm _ LAWS _ _ _ _ _ M1 X) | pose proof (owned_low Bm _ LAWS _ _ _ _ _ M2 X)]; lia. }
  assert (FR2 : rw_cells rsegs m2 (S - 48) [CB 8 j0; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9);
                                            C8 (getr regs 8); C8 (getr regs 1)]).
  { rewrite <- SEG. apply (rw_cp_frame Bm API 8192 L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 _ _ POST); [|rewrite SEG; exact FR1].
    intros i Hi. cbn [cells_size csize Nat.add] in Hi. destruct (NOW1 (S - 48 + i) ltac:(lia)) as [X1 X2].
    split; [left; lia|]. split; [exact X1|]. split; [exact X2|].
    split; [unfold scratch_k; rewrite SP1; lia | intro X; exact X]. }
  assert (LC2 : rw_cells rsegs m2 LA [C8 (Z_to_bv 64 V1); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 G)]).
  { rewrite <- SEG. apply (rw_cp_frame Bm API 8192 L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 _ _ POST); [|rewrite SEG; exact LC1].
    intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    destruct (LAI (LA + i) ltac:(lia)) as [IP NR]. pose proof IP as (II & _ & _ & IE).
    split; [right; exact II|].
    split; [exact (lf_img_not_owned Bm API AX _ _ _ _ _ M1 IP)|].
    split; [exact (lf_img_not_owned Bm API AX _ _ _ _ _ M2 IP)|].
    split; [unfold scratch_k; rewrite SP1; intros [X|X]; [lia | exact (IE X)] | intro X; exact X]. }
  destruct (lf_blocks_in L1 A1 V1 (16 * G) INV1) as (pv & Hpv & Epv).
  assert (ARR2 : rw_cells rsegs m2 V1 [CB (Z.to_nat (16 * N)) (concat (map text_rec (hl_recs l)));
                                      CB (Z.to_nat (16 * (G - N))) junk1]).
  { rewrite <- SEG.
    apply (rw_cp_block Bm API 8192 L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 pv (16 * G) V1 _ POST Hpv (UBK _ _ Hpv));
      [rewrite Epv; lia | cbn [cells_size csize]; rewrite Epv; lia | rewrite SEG; exact ARR1]. }
  assert (TX2 : Forall (fun r => In (fst r, text_len r) (blocks L2 A2) /\
                   rw_cells rsegs m2 (fst r) [CB (length (snd r) + 1) (snd r ++ [Z_to_bv 8 0])]) (hl_recs l)).
  { eapply Forall_impl; [|exact TX1]. intros r (Hr1 & Hr2). split; [exact (B12 _ _ Hr1)|].
    destruct (lf_blocks_in L1 A1 _ _ Hr1) as (pr & Hpr & Epr).
    rewrite <- SEG.
    apply (rw_cp_block Bm API 8192 L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 pr (text_len r) (fst r) _ POST Hpr (UBK _ _ Hpr));
      [rewrite Epr; lia | cbn [cells_size csize]; rewrite Epr; unfold text_len; lia | rewrite SEG; exact Hr2]. }
  assert (SRC2 : bytes_at rsegs m2 SRC x).
  { destruct SH1 as [(H1 & H2) | [(q & kq & Hq & Hqv & H1 & H2) | (H0 & H1 & H2 & H3)]].
    - rewrite <- SEG. apply (ba_cp_frame Bm API 8192 L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 SRC x POST); [|rewrite SEG; exact SRC1].
      intros i Hi. rewrite LX in Hi. destruct (NOW1 (SRC + i) ltac:(lia)) as [X1 X2].
      split; [left; lia|]. split; [exact X1|]. split; [exact X2|].
      split; [unfold scratch_k; rewrite SP1; lia | intro X; exact X].
    - destruct (lf_blocks_in L1 A1 q kq Hq) as (pq & Hpq & Epq).
      rewrite <- SEG.
      apply (ba_cp_block Bm API 8192 L1 A1 R1 m1 md1 _ L2 A2 R2 m2 md2 pq kq SRC x POST Hpq (UBK _ _ Hpq));
        [rewrite Epq; lia | rewrite Epq, LX; lia | rewrite SEG; exact SRC1].
    - rewrite <- SEG. apply (ba_ro Bm m1 m2 SRC x); [rewrite SEG; exact RO1 | rewrite SEG; exact RO2 | | rewrite SEG; exact SRC1].
      intros i Hi. rewrite LX in Hi. exact (H3 i Hi). }
  destruct (lf_block_present_rw Bm API L2 A2 m2 md2 d (n + 1) d (length x) M2 INB ltac:(lia) ltac:(lia)) as [junk2 DST2].
  destruct (lf_block_present_rw Bm API L2 A2 m2 md2 d (n + 1) (d + n) 1 M2 INB ltac:(lia) ltac:(lia)) as [j1 DZ2].
  rewrite SEG in DST2, DZ2.
  destruct (ls_cut rsegs _ _ [_] [_] ARR2) as [ARRp ARRr]. cbn [cells_size csize Nat.add] in ARRr.
  replace (V1 + Z.of_nat (Z.to_nat (16 * N) + 0)) with (V1 + 16 * N) in ARRr by lia.
  apply (rw_cells_split_CB rsegs _ _ [] (Z.to_nat (16 * (G - N))) junk1 []
           [16%nat; (Z.to_nat (16 * (G - N)) - 16)%nat]) in ARRr; [|cbn; lia].
  cbn [mk_CB_cells app] in ARRr.
  destruct (ls_cut rsegs _ _ [_] [_] ARRr) as [SL2 RST2]. cbn [cells_size csize Nat.add] in RST2.
  replace (V1 + 16 * N + Z.of_nat (16 + 0)) with (V1 + 16 * N + 16) in RST2 by lia.
  match type of SL2 with rw_cells _ _ _ [CB _ ?j] => set (js := j) in SL2 end. clearbody js.
  match type of RST2 with rw_cells _ _ _ [CB _ ?j] => set (jr := j) in RST2 end. clearbody jr.
  pose proof RST2 as [[[LJR _] _] _].
  clear NCAP GB2 GB3 GB4 CASE0 HAL. destruct AC as [AC _].
  assert (INV2 : In (V1, 16 * G) (blocks L2 A2)) by exact (B12 _ _ INV1).
  assert (FVs : forall i, 0 <= i < 16 -> ~ in_img Bm (V1 + 16 * N + i)).
  { intros i Hi. replace (V1 + 16 * N + i) with (V1 + (16 * N + i)) by ring. apply FV_img. lpz. }
  assert (D_LB : LA + 16 <= V1 \/ V1 + 16 * G <= LA)
    by exact (lp_disj (in_img Bm) LA 16 V1 (16 * G) ltac:(lpz) ltac:(lpz)
                (fun i Hi => proj1 (proj1 (LAI (LA + i) ltac:(lpz)))) FV_img).
  assert (D_Ld : LA + 16 <= d \/ d + (n + 1) <= LA)
    by exact (lp_disj (in_img Bm) LA 16 d (n + 1) ltac:(lpz) ltac:(lpz)
                (fun i Hi => proj1 (proj1 (LAI (LA + i) ltac:(lpz)))) FR_img).
  assert (D_S : (SRC + n <= d \/ d + n <= SRC) /\ (SRC + n <= V1 + 16 * N \/ V1 + 16 * N + 16 <= SRC)).
  { destruct SH1 as [(H1 & H2) | [(q & kq & Hq & Hqv & H1 & H2) | (H0 & H1 & H2 & H3)]].
    - lpz.
    - destruct (Z.eq_dec q V1) as [EqV|NeV].
      + destruct Hqv as [Hqv|Hk0]; [contradiction|]. subst q kq. lpz.
      + pose proof (DJd q kq Hq) as X1.
        pose proof (blocks_disjoint Bm API L1 A1 m1 md1 q kq V1 (16 * G) M1 Hq INV1 NeV) as X2.
        destruct X1 as [X1|X1]; destruct X2 as [X2|X2]; lpz.
    - rewrite SEG in H3.
      pose proof (lp_disj (in_img Bm) SRC n d (n + 1) H0 ltac:(lpz)
        (fun i Hi => ro_in_img Bm SEG (SRC + i) ltac:(lpz) (H3 i Hi)) FR_img) as X1.
      pose proof (lp_disj (in_img Bm) SRC n (V1 + 16 * N) 16 H0 ltac:(lpz)
        (fun i Hi => ro_in_img Bm SEG (SRC + i) ltac:(lpz) (H3 i Hi)) FVs) as X2.
      destruct X1 as [X1|X1]; destruct X2 as [X2|X2]; lpz. }
  destruct D_S as [D_Sd D_SV].
  assert (D1 : LA + 16 <= V1 + 16 * N \/ V1 + 16 * N + 16 <= LA) by (destruct D_LB; lpz).
  assert (D2 : LA + 16 <= d \/ d + n + 1 <= LA) by (destruct D_Ld; lpz).
  assert (D3 : V1 + 16 * N + 16 <= d \/ d + n + 1 <= V1 + 16 * N) by (destruct DJV; lpz).
  pose proof (mem_inv_normalize rsegs m2) as MI2.
  assert (FRn : rw_cells rsegs (normalize rsegs m2) (bv_unsigned (getr regs 2) - 48)
                  [CB 8 j0; C8 (getr regs 19); C8 (getr regs 18); C8 (getr regs 9); C8 (getr regs 8); C8 (getr regs 1)]).
  { rewrite ES'. apply rw_cells_normalize; [exact RO2 | exact FR2 |]. intros i Hi. cbn in Hi. apply ro_addr_hi. lpz. }
  assert (LCn : rw_cells rsegs (normalize rsegs m2) LA [C8 (Z_to_bv 64 V1); C4 (Z_to_bv 64 N); C4 (Z_to_bv 64 G)]).
  { apply rw_cells_normalize; [exact RO2 | exact LC2 |]. intros i Hi. cbn in Hi. exact (proj2 (LAI (LA + i) ltac:(lpz))). }
  assert (SLn : rw_cells rsegs (normalize rsegs m2) (V1 + 16 * N) [CB 16 js]).
  { apply rw_cells_normalize; [exact RO2 | exact SL2 |]. intros i Hi. cbn in Hi.
    apply (ro_addr_out Bm SEG); [lpz | apply FVs; lpz]. }
  assert (DSTn : rw_cells rsegs (normalize rsegs m2) d [CB (length x) junk2]).
  { apply rw_cells_normalize; [exact RO2 | exact DST2 |]. intros i Hi. cbn [cells_size csize] in Hi.
    apply (ro_addr_out Bm SEG); [lpz | apply FR_img; lpz]. }
  assert (DZn : rw_cells rsegs (normalize rsegs m2) (d + n) [CB 1 j1]).
  { apply rw_cells_normalize; [exact RO2 | exact DZ2 |]. intros i Hi. cbn in Hi.
    replace (d + n + i) with (d + (n + i)) by ring. apply (ro_addr_out Bm SEG); [lpz | apply FR_img; lpz]. }
  pose proof (bytes_at_normalize rsegs m2 SRC x RO2 SRC2) as SRCn.
  change (getr R1 1) with (reg_get R1 1). rewrite E1_1. rewrite SEG.
  set (W3 := [(S - 48, S); (LA, LA + 16); (V1 + 16 * N, V1 + 16 * N + 16); (d, d + n + 1)]).
  eapply (lift_run R2 (Z_to_bv 64 0x148c0) m2 md2 W3
    (fun m' => rw_cells rsegs m' LA [C8 (Z_to_bv 64 V1); C4 (Z_to_bv 64 (N + 1)); C4 (Z_to_bv 64 G)] /\
               rw_cells rsegs m' (V1 + 16 * N) [C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n)] /\
               rw_cells rsegs m' d [CB (length x) x] /\ rw_cells rsegs m' (d + n) [C1 (Z_to_bv 8 0)])
    (fun R pc' => pc' = getr regs 1 /\ forall R', Regs6ss.xregs_eqv R R' -> regs_preserved regs R'));
    [exact Hh2 | exact Hl2 | exact RO2 | |].
  { unfold Regs6ss.mkR_of.
    rewrite E2_2, E2_3, E2_4, E2_8, E2_9, E2_10, E2_18, E2_20, E2_21, E2_22, E2_23, E2_24, E2_25, E2_26, E2_27.
    replace (Z_to_bv 64 (S - 48)) with (Z_to_bv 64 (bv_unsigned (getr regs 2) - 48)) by (rewrite ES'; reflexivity).
    eapply evt_mono.
    { apply (lpu_run3 MEMCPY) with (sp0 := getr regs 2) (V := V1) (N := N) (G := G) (x := x)
        (junk1 := js) (junk2 := junk2) (j1 := j1) (j0 := j0) (ra0 := getr regs 1) (s00 := getr regs 8)
        (s01 := getr regs 9) (s02 := getr regs 18) (s03 := getr regs 19);
      [ exact FRn | exact LCn | exact SLn | exact DSTn | exact DZn | exact SRCn | exact LX
      | lpz | lpz | exact V8 | lpz | lpz | lpz | lpz | lpz | lpz | lpz
      | exact D1 | exact D2 | exact D3 | exact D_Sd | exact SLA | exact D_SV
      | left; lpz | left; lpz | left; lpz | exact MI2 ]. }
    intros ms' (u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & m' & -> & MU' & WM'
      & P1 & P2 & P3 & P4).
    eexists _, _, m'. split; [reflexivity|].
    split; [split; [apply ret_pc_of_ok; exact HRA | intros R' X; eapply pres_mkR; [exact X | reflexivity ..]]|].
    split; [rewrite ES' in MU'; exact MU'|]. split; [exact WM'|].
    split; [exact P1|]. split; [exact P2|]. split; [exact P3 | exact P4]. }
  intros R R' pc' m3 m' (EPC & HPR) X MU3 WM3 RO3 REL3 (P1 & P2 & P3 & P4).
  pose proof (HPR R' X) as PRES. subst pc'.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL3 P1) as LC3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL3 P2) as SLOT3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL3 P3) as DST3.
  pose proof (rw_cells_of_rel rsegs _ _ _ _ REL3 P4) as DZ3.
  clear P1 P2 P3 P4.
  assert (TR : forall a cs, rw_cells rsegs m2 a cs -> disjoint_from W3 a (Z.of_nat (cells_size cs)) ->
                 rw_cells rsegs m3 a cs).
  { intros a cs H HD. exact (rw_cells_transport rsegs W3 m2 m3 a cs H MU3 WM3 HD). }
  assert (ARRp3 : rw_cells rsegs m3 V1 [CB (Z.to_nat (16 * N)) (concat (map text_rec (hl_recs l)))]).
  { apply TR; [exact ARRp|]. unfold W3. cbn [disjoint_from cells_size csize].
    destruct D_LB as [Y1|Y1]; destruct DJV as [Y2|Y2]; repeat split; lpz. }
  assert (RST3 : rw_cells rsegs m3 (V1 + 16 * N + 16) [CB (Z.to_nat (16 * (G - N)) - 16) jr]).
  { apply TR; [exact RST2|]. unfold W3. cbn [disjoint_from cells_size csize].
    destruct D_LB as [Y1|Y1]; destruct DJV as [Y2|Y2]; repeat split; lpz. }
  assert (ARR3 : rw_cells rsegs m3 V1 [CB (Z.to_nat (16 * G)) (concat (map text_rec (hl_recs l ++ [(d, x)])) ++ jr)]).
  { pose proof (ls_join rsegs m3 V1 (V1 + 16 * N) _ _ ARRp3 SLOT3 ltac:(cbn [cells_size csize]; lpz)) as J1.
    pose proof (ls_join rsegs m3 V1 (V1 + 16 * N + 16) _ _ J1 RST3 ltac:(cbn [cells_size csize app]; lpz)) as J2.
    pose proof (rw_cells_merge rsegs m3 V1 []
      [CB (Z.to_nat (16 * N)) (concat (map text_rec (hl_recs l))); C8 (Z_to_bv 64 d); C8 (Z_to_bv 64 n);
       CB (Z.to_nat (16 * (G - N)) - 16) jr] [] J2) as J3.
    apply (lp_cb_eq _ _ _ _ _ _ _ J3).
    - cbn [cells_size csize]. lpz.
    - cbn [cells_bytes cbytes]. rewrite lp_concat_snoc, LX, app_nil_r, <- !app_assoc. reflexivity. }
  assert (TXd : rw_cells rsegs m3 d [CB (length x + 1) (x ++ [Z_to_bv 8 0])]).
  { pose proof (ls_join rsegs m3 d (d + n) _ _ DST3 DZ3 ltac:(cbn [cells_size csize]; lpz)) as J1.
    pose proof (rw_cells_merge rsegs m3 d [] [CB (length x) x; C1 (Z_to_bv 8 0)] [] J1) as J2.
    apply (lp_cb_eq _ _ _ _ _ _ _ J2); cbn [cells_size csize cells_bytes cbytes app]; [lpz | reflexivity]. }
  assert (NDd : ~ In d (map fst (hl_recs l))).
  { intro I. apply in_map_iff in I. destruct I as (r & Er & Ir).
    pose proof (proj1 (proj1 (Forall_forall _ _) TX1 r Ir)) as Hb. pose proof (DJd _ _ Hb) as X1.
    unfold text_len in X1. destruct X1; lpz. }
  pose proof (lmid_trans Bm API LIST_PUSH_K S E1 F1 (fun _ => False) (fun _ => False) L A mem md L1 A1 m1 md1
                L2 A2 m2 md2 HWF MID1 MID2) as MID12.
  pose proof MID12 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SC12).
  assert (MID3 : lmid Bm API LIST_PUSH_K S
                   (fun a => LA <= a < LA + 16 \/ V1 + 16 * N <= a < V1 + 16 * N + 16 \/ d <= a < d + n + 1)
                   (fun _ => False) L2 A2 m2 md2 L2 A2 m3 md2).
  { apply (lmid_A Bm API SEG AX LIST_PUSH_K S _ L2 A2 m2 md2 m3 W3);
      [exact M2 | exact W2 | exact BD2 | rewrite KV; lpz | lpz | exact SC12 | exact MU3 | rewrite SEG; exact WM3 | |].
    - intros a Ha O. unfold W3 in O. cbn [outside] in O.
      assert (Q1 : S - 48 <= a < S \/ ~ (S - 48 <= a < S)) by (clear O; lpz).
      assert (Q2 : LA <= a < LA + 16 \/ ~ (LA <= a < LA + 16)) by (clear O; lpz).
      assert (Q3 : V1 + 16 * N <= a < V1 + 16 * N + 16 \/ ~ (V1 + 16 * N <= a < V1 + 16 * N + 16)) by (clear O; lpz).
      assert (Q4 : d <= a < d + n + 1 \/ ~ (d <= a < d + n + 1)) by (clear O; lpz).
      destruct Q1 as [Q1|Q1]; [left; rewrite KV; clear O; lpz | right].
      destruct Q2 as [Q2|Q2]; [left; exact Q2|].
      destruct Q3 as [Q3|Q3]; [right; left; exact Q3|].
      destruct Q4 as [Q4|Q4]; [right; right; exact Q4|].
      exfalso. apply O. repeat split; assumption.
    - intros a Ha Ho. unfold W3. cbn [outside].
      split; [lpz|].
      split; [intro Y; exact (lf_img_not_owned Bm API AX L2 A2 m2 md2 a M2 (proj1 (LAI a Y)) Ho)|].
      split.
      { intro Y. apply (proj2 (proj2 (proj2 (block_facts Bm _ LAWS _ _ _ _ _ _ (a - V1) M2 INV2 ltac:(lpz))))).
        replace (V1 + (a - V1)) with a by ring. exact Ho. }
      split; [|exact I].
      intro Y. apply (proj2 (proj2 (proj2 (block_facts Bm _ LAWS _ _ _ _ _ _ (a - d) M2 INB ltac:(lpz))))).
      replace (d + (a - d)) with a by ring. exact Ho. }
  pose proof (lmid_trans Bm API LIST_PUSH_K S _ _ _ _ L A mem md L2 A2 m2 md2 L2 A2 m3 md2 HWF MID12 MID3) as MIDf.
  rewrite ES in MIDf.
  pose proof (rp_of_lmid Bm API _ _ _ L A regs mem md L2 A2 R' m3 md2 HWF MIDf PRES) as RP0.
  assert (NV1 : N = CAP -> forall q m, In (q, m) (blocks L A) -> 0 < m -> ~ (0 < CAP /\ q = V) -> q <> V1).
  { intros EQ q m Hq Hm NQ Eq. subst q.
    destruct (in_dec Z.eq_dec V1 (list_blocks l)) as [I|I]; [| exact (B3 V1 m Hq Hm I eq_refl)].
    unfold list_blocks in I. apply in_app_or in I. destruct I as [I|I]; [| exact (V1T I)].
    revert I. destruct (Z.eqb_spec (hl_cap l) 0) as [C0|C0]; intros I; [destruct I | destruct I as [I|[]]].
    apply NQ. split; [lpz | symmetry; exact I]. }
  assert (INL : forall z, z = V1 \/ In z (map fst (hl_recs l)) \/ z = d ->
                  In z (list_blocks (HL V1 G (hl_recs l ++ [(d, x)]) jr))).
  { intros z Hz. unfold list_blocks. cbn [hl_cap hl_v hl_recs].
    destruct (Z.eqb_spec G 0) as [G0|G0]; [lpz|]. rewrite map_app. cbn [map fst app].
    destruct Hz as [Hz|[Hz|Hz]];
      [left; symmetry; exact Hz | right; apply in_or_app; left; exact Hz | right; apply in_or_app; right; left; symmetry; exact Hz]. }
  assert (HN' : hl_n (HL V1 G (hl_recs l ++ [(d, x)]) jr) = N + 1).
  { unfold hl_n. cbn [hl_recs]. rewrite length_app. cbn [length]. unfold N, hl_n. lpz. }
  apply SR_ret. unfold lp_post.
  exists L2, A2, R', m3, md2, (HL V1 G (hl_recs l ++ [(d, x)]) jr), d.
  split; [rewrite SEG; reflexivity|].
  split.
  { eapply rp_shrink.
    - eapply rp_F_weaken; [exact RP0|]. intros q Hq. cbv beta in Hq. destruct Hq as [[Hq|[]]|[]]. exact (HF1 q Hq).
    - intros a Ha. cbv beta in Ha. destruct Ha as [[Ha|[]]|[Ha|[Ha|Ha]]].
      + left. left. exact (HE1 a Ha).
      + left. left. exact Ha.
      + destruct (Z_lt_ge_dec N CAP) as [LT'|GE'].
        * left. right. split; [exact LT'|]. rewrite <- (NG LT'). lpz.
        * right. split; [lpz|]. split; [replace a with (V1 + (a - V1)) by ring; apply FV_img; lpz|].
          intros p n0 Hp HF Hin. cbv beta in HF.
          assert (Hn0 : 0 < n0) by lpz.
          assert (NF1 : ~ F1 (ptr_addr L p)) by (intro Y; exact (HF (HF1 _ Y))).
          pose proof (SV1 p n0 Hp Hn0 NF1) as Hp1.
          pose proof (lf_addr A L L1 p n0 HWF LY1 Hp) as EA.
          pose proof (lf_blocks_of L1 A1 p n0 Hp1) as Hb1. rewrite EA in Hb1.
          pose proof (lf_blocks_of L A p n0 Hp) as Hb0.
          assert (NE : ptr_addr L p <> V1).
          { apply (NV1 ltac:(lpz) (ptr_addr L p) n0 Hb0 Hn0). intros (Y1 & Y2). apply HF. split; [lpz | split; [exact Y1 | exact Y2]]. }
          destruct (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 Hb1 INV1 NE); lpz.
      + right. split; [lpz|]. split; [replace a with (d + (a - d)) by ring; apply FR_img; lpz|].
        intros p n0 Hp HF Hin. cbv beta in HF.
        assert (Hn0 : 0 < n0) by lpz.
        assert (NF1 : ~ F1 (ptr_addr L p)) by (intro Y; exact (HF (HF1 _ Y))).
        pose proof (SV1 p n0 Hp Hn0 NF1) as Hp1.
        pose proof (lf_addr A L L1 p n0 HWF LY1 Hp) as EA.
        pose proof (lf_blocks_of L1 A1 p n0 Hp1) as Hb1. rewrite EA in Hb1.
        destruct (DJd _ _ Hb1); lpz. }
  split; [exact INIT|].
  split.
  { destruct (lp_spec L2 A2 m2 md2 M2 d (n + 1) INB) as [Hqd Eqd].
    pose proof MIDf as (_ & _ & _ & LYf & _).
    exists (qs0 ++ [sptr_of L2 A2 d]).
    split; [exact (lp_push_len (known_at L A) l x qs0 _ LQ0)|].
    split; [rewrite (lp_push_run Fr L A l x qs0 _ bnd LQ0), LX; exact RES'|].
    split; [exact (lp_real L A L2 qs0 _ l V1 G d x jr SPEC0 HWF LYf (proj1 NB0) CV0 HR0 EG LQ0 NG PV2 Eqd)|].
    exact (lp_live L A A2 qs0 (sptr_of L2 A2 d) l x SPEC0 KEEP2 (proj1 NB0) CV0 HR0 NV0 LQ0 HQ2 (ex_intro _ (n + 1) Hqd)). }
  split; [rewrite SEG; exact RO3|].
  split.
  { unfold list_at. rewrite SEG.
    split; [rewrite HN'; exact LC3|].
    split; [rewrite HN'; cbn [hl_cap]; lpz|].
    split.
    { right. cbn [hl_cap hl_v hl_recs hl_junk]. split; [lpz|]. split; [exact INV2|]. split; [exact FV1|].
      split; [rewrite HN'; rewrite LJR; clear - GB1 N0; rewrite Nat2Z.inj_sub, Z2Nat.id by lia; lia | exact ARR3]. }
    cbn [hl_recs hl_v]. rewrite map_app. cbn [map fst].
    split; [first [ exact (lp_nodup_snoc _ _ ND0 NDd)
                  | apply NoDup_ListNoDup; exact (lp_nodup_snoc _ _ (proj1 (NoDup_ListNoDup _) ND0) NDd) ]|].
    split.
    { intro I. apply in_app_or in I. destruct I as [I|[I|[]]]; [exact (V1T I) | destruct DJV; lpz]. }
    apply Forall_app. split.
    - apply Forall_forall. intros r Ir.
      destruct (proj1 (Forall_forall _ _) TXF0 r Ir) as (T1 & T2 & T3 & T4 & T5).
      destruct (proj1 (Forall_forall _ _) TX2 r Ir) as (U1 & U2).
      destruct (proj1 (Forall_forall _ _) TX1 r Ir) as (U0 & _).
      assert (NEr : fst r <> V1) by (intro Y; apply V1T; rewrite <- Y; apply in_map; exact Ir).
      pose proof (blocks_disjoint Bm API L1 A1 m1 md1 _ _ _ _ M1 U0 INV1 NEr) as Xr1.
      pose proof (DJd _ _ U0) as Xr2.
      pose proof (block_facts Bm _ LAWS _ _ _ _ _ _ 0 M2 U1) as Xr3.
      unfold text_len in Xr1, Xr2, Xr3.
      destruct T2 as (T2a & T2b & T2c).
      pose proof (lp_disj (in_img Bm) LA 16 (fst r) (Z.of_nat (length (snd r)) + 1) ltac:(lpz) ltac:(lpz)
        (fun i Hi => proj1 (proj1 (LAI (LA + i) ltac:(lpz)))) T2c) as Xr4.
      split; [exact U1|]. split; [split; [exact T2a | split; [exact T2b | exact T2c]]|].
      split; [|split; [exact T4 | exact T5]].
      apply TR; [exact U2|]. unfold W3. cbn [disjoint_from cells_size csize].
      destruct (Xr3 ltac:(lpz)) as (_ & Xr5 & Xr6 & _).
      destruct Xr1 as [Y1|Y1]; destruct Xr2 as [Y2|Y2]; destruct Xr4 as [Y4|Y4]; repeat split; lpz.
    - constructor; [|constructor]. cbn [fst snd]. rewrite LX.
      split; [exact INB|]. split; [exact FRESH|]. split; [exact TXd|].
      split; [intro Y; destruct (LT Y) as [Y1 Y2]; split; [exact Y1 | lpz]|].
      intro Y. pose proof (LF Y). lpz. }
  split; [reflexivity|]. split; [cbn [hl_cap]; exact EG|]. split; [intro Y; exact (NG Y)|].
  split; [intros q m Hq NI; exact (B12 _ _ (B2 q m Hq NI))|].
  split.
  { intros q m Hq.
    assert (C : In (q, m) (blocks L1 A1) \/ (q, m) = (d, n + 1)).
    { rewrite BLK1 in Hq. rewrite BLK2. apply in_app_or in Hq. destruct Hq as [Hq|[Hq|Hq]];
        [left; apply in_or_app; left; exact Hq | right; symmetry; exact Hq | left; apply in_or_app; right; exact Hq]. }
    destruct C as [Hq1|Hq1]; [| injection Hq1 as -> ->; right; apply INL; right; right; reflexivity].
    destruct (B1 q m Hq1) as [(Hq0 & HnV) | EQ]; [| right; apply INL; left; exact EQ].
    destruct (Z_lt_le_dec 0 m) as [Hm|Hm]; [| left; split; [exact Hq0 | intro; lpz]].
    destruct (in_dec Z.eq_dec q (list_blocks l)) as [I|I]; [| left; split; [exact Hq0 | intros _; exact I]].
    right. apply INL. unfold list_blocks in I. apply in_app_or in I. destruct I as [I|I]; [| right; left; exact I].
    left. revert I. destruct (Z.eqb_spec (hl_cap l) 0) as [C0|C0]; intros I; [destruct I | destruct I as [I|[]]].
    destruct (Z_lt_ge_dec N CAP) as [LT'|GE'].
    - rewrite (NG LT'). symmetry. exact I.
    - exfalso. apply (HnV Hm). split; [lpz|]. split; [lpz | symmetry; exact I]. }
  intros q m Hq Hm NI I.
  unfold list_blocks in I. cbn [hl_cap hl_v hl_recs] in I. revert I.
  destruct (Z.eqb_spec G 0) as [G0|G0]; [lpz|]. intros I.
  rewrite map_app in I. cbn [map fst app] in I.
  destruct I as [I|I]; [exact (B3 q m Hq Hm NI (eq_sym I))|].
  apply in_app_or in I. destruct I as [I|[I|[]]].
  - apply NI. unfold list_blocks. apply in_or_app. right. exact I.
  - pose proof (DJd q m (B2 q m Hq NI)) as X1. destruct X1; lpz.
Qed.

End LPP.
