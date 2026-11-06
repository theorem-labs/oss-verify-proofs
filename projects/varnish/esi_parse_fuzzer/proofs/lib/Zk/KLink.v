(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import AgentLib RelSpec MmapSim AllocSim RefNodes BWorld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require PropExec MState.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Monad MSafe STree Malloc MProg KInv KNodes RzImpl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_Ccma.  (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
Ltac kl_open HK := destruct HK as [Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kmr Knc Kgna Kmat Kcpl Kbb Klim Kceil].

Section CEIL.
Context {Clg : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

(* [comment removed for export] *)
Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
  forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

(* [comment removed for export] *)
Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
  (forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

(* [comment removed for export] *)
Definition minv (mo : Model) : Prop := m_vm_lazy mo = [].

(* [comment removed for export] *)
Definition vm_only (m m' : Model) : Prop :=
  m_fd m' = m_fd m /\ m_io m' = m_io m /\ m_fsys m' = m_fsys m /\ m_proc m' = m_proc m
  /\ m_lim m' = m_lim m /\ m_time m' = m_time m.   (* [comment removed for export] *)

Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. intros mo. unfold vm_only. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof. intros a b c (?&?&?&?&?&?) (?&?&?&?&?&?). unfold vm_only. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence. Qed.
Lemma vm_only_with_vmmaps : forall h m, vm_only m (with_vmmaps h m).
Proof. intros h m. unfold vm_only, with_vmmaps. destruct m; cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma vm_only_with_vm_backing : forall l p m, vm_only m (with_vm_backing l p m).
Proof. intros l p m. unfold vm_only, with_vm_backing. destruct m; cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma vm_only_vm_forget_range : forall lo hi m, vm_only m (vm_forget_range lo hi m).
Proof. intros lo hi m. unfold vm_forget_range. apply vm_only_with_vm_backing. Qed.
Lemma vm_only_forget_vm_ranges : forall l m, vm_only m (forget_vm_ranges l m).
Proof.
  induction l as [|[a n] l IH]; intros m; cbn; [apply vm_only_refl|].
  eapply vm_only_trans; [apply vm_only_vm_forget_range| apply IH].
Qed.
(* [comment removed for export] *)

Lemma nstep_mm_vm_only : forall n mo rsp mo', nstep n mo rsp mo' -> vm_only mo mo'.
Proof.
  intros n mo rsp mo' HS. destruct n; cbn -[brk_model mmap_model noaccess_model fixed_noaccess_model
    fixed_destroyed_model munmap_model mprotect_model mremap_model_next Z.eqb] in HS; try contradiction.
  - (first [ dex1 HS as r; dand3 HS as Hr -> -> | dand4 HS as r Hr -> -> | destruct HS as (r & Hr & -> & ->) ]). unfold brk_model, with_brk_next.
    eapply vm_only_trans; [apply vm_only_with_vmmaps| apply vm_only_forget_vm_ranges].
  - destruct (flags =? NMAP_ANON)%Z; [destruct (prot =? NPROT_RW)%Z|].
    + destruct HS as [(e & _ & _ & ->)|(a & _ & _ & ->)]; [apply vm_only_refl| apply vm_only_with_vmmaps].
    + destruct HS as [(e & _ & _ & ->)|(a & _ & _ & ->)]; [apply vm_only_refl| apply vm_only_with_vmmaps].
    + destruct HS as [(e & _ & _ & ->)|[(_ & ->)|(_ & e & _ & _ & ->)]]; [apply vm_only_refl| |];
        (eapply vm_only_trans; [apply vm_only_with_vmmaps| apply vm_only_vm_forget_range]).
  - destruct HS as [-> ->]. unfold munmap_model.
    eapply vm_only_trans; [apply vm_only_with_vmmaps| apply vm_only_vm_forget_range].
  - destruct HS as [(e & _ & _ & ->)|(_ & _ & ->)]; [apply vm_only_refl| apply vm_only_with_vmmaps].
  - destruct HS as [(_ & _ & ->)|[_ [(e & _ & _ & ->)|[(_ & _ & ->)|[(_ & _ & _ & ->)|(_ & dst & _ & _ & ->)]]]]];
      try apply vm_only_refl; unfold mremap_model_next, vm_resize_backing;
      (eapply vm_only_trans; [apply vm_only_with_vmmaps| apply vm_only_with_vm_backing]).
Qed.

Lemma minv_preserved : forall n mo rsp mo', minv mo -> m_halted mo = None -> nstep n mo rsp mo' ->
  m_halted mo' = None /\ minv mo'.
Proof. intros n mo rsp mo' Hm Hh Hs. exact (nstep_KI n mo rsp mo' (conj Hh Hm) Hs). Qed.

(* [comment removed for export] *)
Definition brk_disj (L : mled) (b n : Z) : Prop :=
  forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

(* [comment removed for export] *)
Definition brk_extent (L : mled) : Z := match ld_brkreg L with Some (_, l) => l | None => 2 * PGSZ end.

(* [comment removed for export] *)
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  kl_resv : ld_resv L = map wwZ (vm_reserved (m_vmmaps mo));
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo));
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_ceiling;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end;
  (* [comment removed for export] *)
  kl_maps_resv : forall e, In e (vm_maps (m_vmmaps mo)) ->
      region_free (vm_reserved (m_vmmaps mo)) (fst e) (snd e) = true;
  kl_na_cov : forall e, In e (vm_noaccess (m_vmmaps mo)) ->
      exists e', In e' (vm_maps (m_vmmaps mo)) /\ elo e' <= elo e /\ elo e < ehi e /\ ehi e <= ehi e';
  kl_groups_na : forall b l, In (b, l) (ld_groups L) ->
      region_free (vm_noaccess (m_vmmaps mo)) (wz b) (wz (mmap_len l)) = true;
  (* [comment removed for export] *)
  kl_mat : m_vm_materialized mo = [];
  kl_complete : forall e, In e (vm_maps (m_vmmaps mo)) ->
         (exists b l, In (b, l) (ld_groups L) /\ e = went b (mmap_len l))
      \/ (exists b l k, In (b, l, k) (ld_metas L) /\ e = went b (mmap_len l))
      \/ (bv_unsigned (vm_start_brk (m_vmmaps mo)) <= elo e /\ elo e < ehi e <= bv_unsigned (vm_brk (m_vmmaps mo))
          /\ elo e mod PGSZ = 0 /\ ehi e mod PGSZ = 0);
  (* [comment removed for export] *)
  kl_brkb : bv_unsigned (vm_brk (m_vmmaps mo)) <= bv_unsigned (vm_start_brk (m_vmmaps mo)) + brk_extent L;
  (* [comment removed for export] *)
  kl_limit : bw_limit (vm_limit (m_vmmaps mo));
  (* [comment removed for export] *)
  kl_ceil : ceil_ok mo }.

(* [comment removed for export] *)
Definition gframe (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.


(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma PGSZ_eq : PGSZ = 4096. Proof. reflexivity. Qed.
Lemma page_size_eq : page_size = 4096. Proof. reflexivity. Qed.

Lemma land_4095 : forall x, Z.land x 4095 = x mod 4096.
Proof. intros x. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma round_up_pg_aligned : forall x, x mod 4096 = 0 -> round_up_pg x = x.
Proof.
  intros x Hx. unfold round_up_pg. rewrite PGSZ_eq. change (4096 - 1) with 4095. rewrite land_4095.
  assert ((- x) mod 4096 = 0). { apply Z.mod_opp_l_z; lia. } lia.
Qed.

Lemma round_up_pg_eq : forall x, round_up_pg x = page_round_up_Z x.
Proof.
  intros x. unfold round_up_pg, page_round_up_Z. rewrite PGSZ_eq, page_size_eq. change (4096 - 1) with 4095. rewrite land_4095.
  pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)) as H1.
  pose proof (Z_div_mod_eq_full (-x) 4096) as H2.
  pose proof (Z_div_mod_eq_full (x + 4095) 4096) as H3.
  pose proof (Z.mod_pos_bound (x + 4095) 4096 ltac:(lia)) as H4.
  nia.
Qed.

Lemma mmap_len_ge : forall l, 0 < l -> l <= mmap_len l < l + 4096.
Proof.
  intros l Hl. unfold mmap_len, page_round_up_Z. rewrite page_size_eq.
  pose proof (Z_div_mod_eq_full (l + 4096 - 1) 4096). pose proof (Z.mod_pos_bound (l + 4096 - 1) 4096 ltac:(lia)). lia.
Qed.

Lemma mmap_len_aligned : forall l, (mmap_len l) mod 4096 = 0.
Proof. intros. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. apply Z_mod_mult. Qed.

Lemma mmap_len_of_aligned : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof. intros l Hl Ha. unfold mmap_len, page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full l 4096). pose proof (Z_div_mod_eq_full (l + 4095) 4096). pose proof (Z.mod_pos_bound (l+4095) 4096). nia. Qed.

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.

Lemma alloc_ceiling_lt : alloc_ceiling < 2^63.
Proof. pose proof alloc_ceiling_val. lia. Qed.

Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof. intros. unfold ehi, went. cbn [fst snd]. rewrite !unsigned_wz by assumption. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pwdisj_In : forall l e1 e2, pwdisj l -> In e1 l -> In e2 l -> e1 = e2 \/ edisj e1 e2.
Proof.
  induction l as [|e l IH]; intros e1 e2 Hp H1 H2; [destruct H1|].
  inversion Hp; subst. destruct H1 as [<-|H1], H2 as [<-|H2].
  - left; reflexivity.
  - right. apply H3. exact H2.
  - right. pose proof (H3 _ H1) as D. unfold edisj in *. lia.
  - apply IH; assumption.
Qed.

Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|]. cbn in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.

Lemma region_free_disj : forall maps a n e, region_free maps a n = true -> In e maps ->
  bv_unsigned a + bv_unsigned n <= elo e \/ ehi e <= bv_unsigned a.
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.

Lemma vmwf_cons : forall maps a n, vmwf maps ->
  bv_unsigned a < bv_unsigned a + bv_unsigned n <= 2^64 ->
  region_free maps a n = true ->
  vmwf ((a, n) :: maps).
Proof.
  intros maps a n [Hb Hp] Hn Hrf. split.
  - intros e [<-|Hin]; [unfold elo, ehi; cbn; lia| apply Hb; exact Hin].
  - constructor; [|exact Hp]. intros e' Hin. pose proof (region_free_disj _ _ _ _ Hrf Hin). unfold edisj, elo, ehi in *. cbn. lia.
Qed.

Lemma pwdisj_filter : forall (f : word * word -> bool) l, pwdisj l -> pwdisj (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
  - constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply IH; assumption.
Qed.

Lemma vmwf_remove : forall maps a, vmwf maps -> vmwf (map_remove maps a).
Proof.
  intros maps a [Hb Hp]. unfold map_remove. split.
  - intros e Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply pwdisj_filter. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sub : forall a sz lo hi e, 0 < bv_unsigned sz -> bv_unsigned a + bv_unsigned sz <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz /\ elo e < ehi e.
Proof.
  intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz).
  unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) (lo)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_ends : forall a sz lo hi e, bv_unsigned a + bv_unsigned sz <= 2^64 -> 0 <= lo -> 0 <= hi < 2^64 ->
  In e (iv_subtract a sz lo hi) ->
  (elo e = bv_unsigned a \/ elo e = hi) /\ (ehi e = lo \/ ehi e = bv_unsigned a + bv_unsigned sz).
Proof.
  intros a sz lo hi e Hwf Hlo Hhi Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. split; [left; reflexivity| lia].
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. split; [lia| right; lia].
Qed.

Lemma maps_subtract_In : forall maps lo hi e, In e (maps_subtract maps lo hi) ->
  exists e0, In e0 maps /\ In e (iv_subtract (fst e0) (snd e0) lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
  cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity| exact Hin].
  - (first [ pose proof ((IH _ _ _ Hin)) as dR_2; dex1 dR_2 as e0; destruct dR_2 as [H0 H1] | pose proof ((IH _ _ _ Hin)) as dR_2; dand3 dR_2 as e0 H0 H1 | destruct (IH _ _ _ Hin) as (e0 & H0 & H1) ]). exists e0. split; [right; exact H0| exact H1].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : forall a sz lo hi,
  bv_unsigned a < bv_unsigned a + bv_unsigned sz <= 2^64 -> lo < hi ->
  (bv_unsigned a + bv_unsigned sz <= lo \/ hi <= bv_unsigned a) ->
  iv_subtract a sz lo hi = [(a, sz)].
Proof.
  intros a sz lo hi Hwf Hlh Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keep : forall maps lo hi e, vmwf maps -> lo < hi ->
  In e maps -> (ehi e <= lo \/ hi <= elo e) -> In e (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
  destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
  - left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + unfold elo, ehi in Hd. cbn in Hd. lia.
  - right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_contains : forall a sz lo hi x y,
  lo < hi -> hi < 2^64 ->
  bv_unsigned a <= x -> x < y -> y <= bv_unsigned a + bv_unsigned sz ->
  (y <= lo \/ hi <= x) ->
  exists e, In e (iv_subtract a sz lo hi) /\ elo e <= x /\ y <= ehi e.
Proof.
  intros a sz lo hi x y Hlh Hwf Hax Hxy Hy Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; left; left; reflexivity|]. unfold elo, ehi; cbn. rewrite unsigned_lit by lia. lia.
  - replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; right; left; reflexivity|]. unfold elo, ehi; cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In_intro : forall maps lo hi e e', In e maps -> In e' (iv_subtract (fst e) (snd e) lo hi) ->
  In e' (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e e' Hin H'; [destruct Hin|].
  cbn. apply in_or_app. destruct Hin as [<-|Hin]; [left; exact H'| right; eapply IH; eauto].
Qed.

Lemma pwdisj_app : forall P R, pwdisj P -> pwdisj R -> (forall p r, In p P -> In r R -> edisj p r) -> pwdisj (P ++ R).
Proof.
  induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
  - intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
  - apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.

Lemma iv_subtract_pwdisj : forall a sz lo hi, lo < hi -> bv_unsigned a + bv_unsigned sz <= 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlh Hwf. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) (lo)); destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, lo < hi -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlh Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; [exact Hlh| lia]| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
    (first [ pose proof ((maps_subtract_In _ _ _ _ He')) as dR_3; dex1 dR_3 as e0; destruct dR_3 as [H0 H0'] | pose proof ((maps_subtract_In _ _ _ _ He')) as dR_3; dand3 dR_3 as e0 H0 H0' | destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0') ]).
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma region_free_app_l : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof.
  intros l1 l2 a n H. apply region_free_intro. intros b s Hb. apply (region_free_In _ _ _ b s H). apply in_or_app. left. exact Hb.
Qed.

(* [comment removed for export] *)
Lemma region_free_sub : forall l (a n a' n' : word),
  region_free l a n = true ->
  bv_unsigned a <= bv_unsigned a' -> bv_unsigned a' + bv_unsigned n' <= bv_unsigned a + bv_unsigned n ->
  0 < bv_unsigned n' ->
  region_free l a' n' = true.
Proof.
  intros l a n a' n' H H1 H2 H3. apply region_free_intro. intros b s Hb.
  pose proof (region_free_In _ _ _ b s H Hb) as D. lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sub' : forall a sz lo hi e, bv_unsigned a + bv_unsigned sz <= 2^64 ->
  In e (iv_subtract a sz lo hi) -> bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz.
Proof.
  intros a sz lo hi e Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_sub : forall maps lo hi p,
  (forall e, In e maps -> ehi e <= 2^64) ->
  In p (maps_subtract maps lo hi) -> exists e, In e maps /\ elo e <= elo p /\ ehi p <= ehi e.
Proof.
  intros maps lo hi p Hwf Hin. (first [ pose proof ((maps_subtract_In _ _ _ _ Hin)) as dR_4; dex1 dR_4 as e0; destruct dR_4 as [H0 H1] | pose proof ((maps_subtract_In _ _ _ _ Hin)) as dR_4; dand3 dR_4 as e0 H0 H1 | destruct (maps_subtract_In _ _ _ _ Hin) as (e0 & H0 & H1) ]).
  exists e0. split; [exact H0|]. destruct e0 as [a sz].
  apply (iv_subtract_sub' a sz lo hi p); [| exact H1]. specialize (Hwf _ H0). unfold ehi in Hwf. cbn in Hwf. exact Hwf.
Qed.

Lemma region_free_mono_sub : forall l l' (x n : word),
  region_free l x n = true ->
  (forall p, In p l' -> exists e, In e l /\ elo e <= elo p /\ ehi p <= ehi e) ->
  region_free l' x n = true.
Proof.
  intros l l' x n H Hsub. apply region_free_intro. intros b s Hb.
  (first [ pose proof ((Hsub _ Hb)) as dR_5; dex1 dR_5 as e; dand3 dR_5 as He Q1 Q2 | pose proof ((Hsub _ Hb)) as dR_5; dand4 dR_5 as e He Q1 Q2 | destruct (Hsub _ Hb) as (e & He & Q1 & Q2) ]). destruct e as [b0 s0].
  pose proof (region_free_In _ _ _ b0 s0 H He) as D. unfold elo, ehi in Q1, Q2. cbn in Q1, Q2. lia.
Qed.

(* [comment removed for export] *)
Lemma na_cov_bound : forall maps noacc,
  vmwf maps ->
  (forall e, In e noacc -> exists e', In e' maps /\ elo e' <= elo e /\ elo e < ehi e /\ ehi e <= ehi e') ->
  forall e, In e noacc -> ehi e <= 2^64.
Proof.
  intros maps noacc [Hb _] Hcov e He. (first [ pose proof ((Hcov e He)) as dR_6; dex1 dR_6 as e'; dand4 dR_6 as He' Q1 Q0 Q2 | pose proof ((Hcov e He)) as dR_6; dand5 dR_6 as e' He' Q1 Q0 Q2 | destruct (Hcov e He) as (e' & He' & Q1 & Q0 & Q2) ]). specialize (Hb e' He'). lia.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_avoid : forall a sz lo hi e,
  bv_unsigned a + bv_unsigned sz <= 2^64 -> 0 <= lo -> lo < hi -> hi < 2^64 ->
  In e (iv_subtract a sz lo hi) -> ehi e <= lo \/ hi <= elo e.
Proof.
  intros a sz lo hi e Hwf H0 Hlh Hhi Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. left. unfold ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. right. unfold elo. cbn. rewrite unsigned_lit by lia. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma iv_subtract_nonempty : forall a sz lo hi e,
  bv_unsigned a + bv_unsigned sz <= 2^64 -> 0 < bv_unsigned sz -> 0 <= lo -> hi < 2^64 ->
  In e (iv_subtract a sz lo hi) -> elo e < ehi e.
Proof.
  intros a sz lo hi e Hwf Hsz H0 Hhi Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma wcov_mono : forall maps maps' lo hi, (forall e, In e maps -> In e maps') -> wcov maps lo hi -> wcov maps' lo hi.
Proof. intros maps maps' lo hi Hs Hc x Hx. (first [ pose proof ((Hc x Hx)) as dR_8; dex1 dR_8 as e; destruct dR_8 as [He Hr] | pose proof ((Hc x Hx)) as dR_8; dand3 dR_8 as e He Hr | destruct (Hc x Hx) as (e & He & Hr) ]). exists e. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nstep_brk_inv : forall req mo rsp mo',
  nstep (NBrk req) mo rsp mo' ->
  let h := m_vmmaps mo in
  exists r, brk_resolution_ok mo (Z_to_bv 64 req) r
    /\ mo' = brk_model (Z_to_bv 64 req) r mo
    /\ rsp = mkEffectU r [] (brk_zeros (Z_to_bv 64 req) r (vm_brk h)) (brk_unmaps r (vm_brk h)) [] [].
Proof. (intros req mo rsp mo'; (first [ intro dR_111; dex1 dR_111 as r; dand3 dR_111 as Hr -> -> | intro dR_111; dand4 dR_111 as r Hr -> -> | intros (r & Hr & -> & ->) ])). exists r. auto. Qed.

Lemma brk_r_ok_query : forall m r, brk_resolution_ok m (Z_to_bv 64 0) r -> r = vm_brk (m_vmmaps m).
Proof.
  intros m r H. unfold brk_resolution_ok, Mmap.brk_r_ok in H. change (w_is0 (Z_to_bv 64 0)) with true in H.
  cbn [orb] in H. apply bv_eqb_eq in H. exact H.
Qed.

(* [comment removed for export] *)
Lemma brk_model_keep' : forall m req, brk_model req (vm_brk (m_vmmaps m)) m = m.
Proof. intros. apply brk_model_keep. Qed.

Lemma nstep_dec_brk0 : forall mo rsp mo',
  nstep (NBrk 0) mo rsp mo' ->
  dec_brk0 rsp = Some (bv_unsigned (vm_brk (m_vmmaps mo))) /\ vm_only mo mo' /\ mo' = mo.
Proof.
  intros mo rsp mo' H. pose proof (nstep_mm_vm_only _ _ _ _ H) as Hv.
  (first [ pose proof ((nstep_brk_inv _ _ _ _ H)) as dR_9; dex1 dR_9 as r; dand3 dR_9 as Hr -> -> | pose proof ((nstep_brk_inv _ _ _ _ H)) as dR_9; dand4 dR_9 as r Hr -> -> | destruct (nstep_brk_inv _ _ _ _ H) as (r & Hr & -> & ->) ]). apply brk_r_ok_query in Hr. subst r.
  rewrite brk_zeros_query, brk_unmaps_keep. cbn [dec_brk0]. split; [reflexivity|]. split; [exact Hv|].
  change (Z_to_bv 64 0) with (w 0). apply brk_model_keep'.
Qed.

Lemma brk_r_ok_grow : forall m req r,
  let h := m_vmmaps m in let b := bv_unsigned (vm_brk h) in
  bv_unsigned (vm_start_brk h) <= b -> b < req < 2^64 ->
  brk_resolution_ok m (Z_to_bv 64 req) r ->
  (r = vm_brk h) \/ (r = Z_to_bv 64 req /\ Mmap.brk_grow_ok m (Z_to_bv 64 req) (Z_to_bv 64 req) = true).
Proof.
  intros m req r h b Hs Hreq H. pose proof (u64_range (vm_brk h)) as Hr0. fold b in Hr0.
  assert (A1 : 0 < bv_unsigned (Z_to_bv 64 req)) by (rewrite u64_lit; lia).
  assert (A2 : bv_unsigned (vm_start_brk h) <= bv_unsigned (Z_to_bv 64 req)) by (rewrite u64_lit; lia).
  assert (A3 : bv_unsigned (vm_brk h) <= bv_unsigned (Z_to_bv 64 req)) by (rewrite u64_lit; lia).
  apply (proj1 (brk_r_ok_grow_cases m (Z_to_bv 64 req) r A1 A2 A3)) in H. exact H.
Qed.

Lemma brk_grow_ok_facts : forall m req,
  let h := m_vmmaps m in let b := bv_unsigned (vm_brk h) in
  0 < b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  Mmap.brk_grow_ok m (Z_to_bv 64 req) (Z_to_bv 64 req) = true ->
  req <= alloc_top h /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 b) (Z_to_bv 64 (req - b)) = true.
  (* [comment removed for export] *)
Proof.
  intros m req h b Hb Hreq Hba Hra H. unfold Mmap.brk_grow_ok, Mmap.brk_budget_ok in H. fold h in H. rewrite u64_lit in H by lia. fold b in H.
  replace (0 <? b) with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. rewrite page_size_eq in H.
  replace ((b + 4096 - 1) / 4096 * 4096) with b in H.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req in H.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  assert (Hb4096 : 4096 <= b) by (pose proof (Z_div_mod_eq_full b 4096); lia).
  split; [exact H1|].
  apply (region_free_sub _ _ _ _ _ H2); rewrite ?unsigned_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk : forall req mo rsp mo',
  let h := m_vmmaps mo in let b := bv_unsigned (vm_brk h) in
  0 < b -> bv_unsigned (vm_start_brk h) <= b -> b < req < 2^64 -> b mod 4096 = 0 -> req mod 4096 = 0 ->
  nstep (NBrk req) mo rsp mo' ->
  vm_only mo mo' /\
  exists a, dec_brk b req rsp = Some a /\
  match a with
  | BrkSame => mo' = mo
  | BrkGrown => Mmap.brk_grow_ok mo (Z_to_bv 64 req) (Z_to_bv 64 req) = true /\
      mo' = with_vmmaps (mkVmMapsFull (vm_reserved h) ((vm_brk h, Z_to_bv 64 (req - b)) :: vm_maps h)
                          (vm_noaccess h) (vm_start_brk h) (Z_to_bv 64 req) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) mo
  end.
Proof.
  intros req mo rsp mo' h b Hb Hs Hreq Hba Hra H. pose proof (nstep_mm_vm_only _ _ _ _ H) as Hv. split; [exact Hv|].
  (first [ pose proof ((nstep_brk_inv _ _ _ _ H)) as dR_10; dex1 dR_10 as r; dand3 dR_10 as Hr -> -> | pose proof ((nstep_brk_inv _ _ _ _ H)) as dR_10; dand4 dR_10 as r Hr -> -> | destruct (nstep_brk_inv _ _ _ _ H) as (r & Hr & -> & ->) ]). fold h.
  destruct (brk_r_ok_grow mo req r Hs Hreq Hr) as [->|[-> Hg]].
  - exists BrkSame. rewrite brk_zeros_keep, brk_unmaps_keep. split; [| apply brk_model_keep'].
    cbn [dec_brk]. fold h b. rewrite Z.eqb_refl. reflexivity.
  - exists BrkGrown.
    assert (Hne : Z_to_bv 64 req <> Z_to_bv 64 0).
    { intros E. apply (f_equal bv_unsigned) in E. rewrite u64_lit in E by lia. change (bv_unsigned (Z_to_bv 64 0)) with 0 in E. lia. }
    assert (A1 : bv_unsigned (vm_brk h) < bv_unsigned (Z_to_bv 64 req)) by (rewrite u64_lit; lia).
    assert (A2 : bv_unsigned (vm_brk h) mod page_size = 0) by (rewrite page_size_eq; exact Hba).
    rewrite (brk_zeros_aligned_grow (Z_to_bv 64 req) (Z_to_bv 64 req) (vm_brk h) Hne Hb A1 A2).
    rewrite (brk_unmaps_grow (Z_to_bv 64 req) (vm_brk h)) by lia.
    rewrite u64_lit by lia. split.
    + cbn [dec_brk]. fold h b. rewrite u64_lit by lia.
      replace (req =? b) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
      rewrite Z.eqb_refl. cbn [andb]. unfold brk_new_pages.
      replace (page_round_up_Z b) with b.
      2:{ unfold page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
      replace (page_round_up_Z req) with req.
      2:{ unfold page_round_up_Z. rewrite page_size_eq. pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
      replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia). cbn [zeros_of]. unfold Mem.wa. fold h.
      replace (Z_to_bv 64 b) with (vm_brk h) by (symmetry; apply Z_to_bv_bv_unsigned).
      cbn [Prelude.listNN_eqb]. rewrite !bv_eqb_refl. reflexivity.
    + split; [exact Hg|].
      assert (A3 : (req - b) mod page_size = 0) by (rewrite page_size_eq, Zminus_mod, Hba, Hra; reflexivity).
      assert (A4 : 0 < req - b) by lia. assert (A5 : bv_unsigned (vm_brk (m_vmmaps mo)) + (req - b) < 2 ^ 64) by (fold h b; lia).
      pose proof (brk_model_grow_eq mo (req - b) A4 Hb A5 A2 A3) as E.
      cbv zeta in E. fold h in E. fold b in E. replace (b + (req - b)) with req in E by lia. exact E.
Qed.

Lemma m_vmmaps_vm_forget_range : forall lo hi m, m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. intros. reflexivity. Qed.

Lemma wlen_PGSZ : wlen PGSZ = Z_to_bv 64 PGSZ.
Proof. reflexivity. Qed.
Lemma rlen_PGSZ : rlen PGSZ = PGSZ.
Proof. reflexivity. Qed.

Lemma nstep_mmap_fixed_inv : forall a mo rsp mo',
  let h := m_vmmaps mo in
  let aw := Z_to_bv 64 a in let n := Z_to_bv 64 PGSZ in
  0 <= a -> a + PGSZ <= alloc_ceiling ->
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' ->
  vm_only mo mo' /\
  exists x, dec_mmap_fixed a PGSZ rsp = Some x /\
  match x with
  | FxKept e => e = ENOMEM /\ mo' = mo
  | FxDone => m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                ((aw, n) :: maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  | FxLost e => e = ENOMEM /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h)
                (maps_subtract (vm_maps h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned n))
                (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros a mo rsp mo' h aw n Ha Hc H. pose proof alloc_ceiling_lt as Hcl.
  pose proof (nstep_mm_vm_only _ _ _ _ H) as Hv. split; [exact Hv|].
  cbn -[fixed_noaccess_model fixed_destroyed_model Z.eqb w wlen] in H.
  change (MAPFX =? NMAP_ANON)%Z with false in H. cbv iota in H.
  change (w a) with aw in H. rewrite wlen_PGSZ in H. fold n in H.
  destruct H as [(e & He & -> & ->)|[(-> & ->)|(_ & e & He & -> & ->)]].
  - (* [comment removed for export] *)
    exfalso. exact (mmap_errnos_when_false e He).
  - exists FxDone. split.
    + unfold dec_mmap_fixed. subst aw n. change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl. cbn [andb].
      rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity.
    + unfold fixed_noaccess_model. rewrite m_vmmaps_vm_forget_range, with_vmmaps_vm. reflexivity.
  - (* [comment removed for export] *)
    cbn in He. destruct He as [<-|[]]. exists (FxLost ENOMEM). split; [|split; [reflexivity|]].
    + unfold dec_mmap_fixed. subst aw n. change (mmap_len PGSZ) with PGSZ. rewrite !bv_eqb_refl.
      cbn -[errno_of errno_ret]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    + unfold fixed_destroyed_model. rewrite m_vmmaps_vm_forget_range, with_vmmaps_vm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma MAPF_eq : MAPF = NMAP_ANON. Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma w_len_ne0 : forall len, 0 < len < 2^64 -> w len <> w 0.
Proof.
  intros len H E. apply (f_equal bv_unsigned) in E. unfold w in E. rewrite !u64_lit in E by lia. lia.
Qed.

Lemma rlen_eq : forall len, 0 <= len < 2^64 -> rlen len = mmap_len len.
Proof. intros len H. unfold rlen, w, mmap_len. rewrite u64_lit by lia. reflexivity. Qed.

Lemma nsafe_mmap_rw : forall len mo, 0 < len < 2^64 -> nsafe (NMmap 0 len PROT_RW MAPF) mo.
Proof. intros len mo H. cbn. left. split; [reflexivity|]. split; [left; reflexivity|]. apply w_len_ne0. exact H. Qed.

Lemma nsafe_mmap_none : forall len mo, 0 < len < 2^64 -> nsafe (NMmap 0 len PROT_NONE MAPF) mo.
Proof. intros len mo H. cbn. left. split; [reflexivity|]. split; [right; reflexivity|]. apply w_len_ne0. exact H. Qed.

Lemma grant_ok_facts : forall hint m a n,   (* [comment removed for export] *)
  grant_ok hint m a n = true ->
  bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_top (m_vmmaps m) /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok in H. rewrite !andb_true_iff in H.
  destruct H as [[[[H1 H2] H3] H4] H5].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  rewrite page_size_eq in H1. auto.
Qed.

Lemma grant_ok_na_facts : forall hint m a n,   (* [comment removed for export] *)
  grant_ok_na hint m a n = true ->
  bv_unsigned a mod 4096 = 0 /\ 0 < bv_unsigned a /\ bv_unsigned a + n <= alloc_top (m_vmmaps m) /\
  region_free (vm_reserved (m_vmmaps m) ++ vm_maps (m_vmmaps m)) a (Z_to_bv 64 n) = true.
Proof.
  intros hint m a n H. unfold grant_ok_na in H. rewrite !andb_true_iff in H.
  destruct H as [[[H1 H2] H3] H4].
  apply Z.eqb_eq in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  rewrite page_size_eq in H1. auto.
Qed.

Lemma mmap_addr_ok_intro : forall len a, 0 < len ->
  a mod 4096 = 0 -> 0 < a -> a + mmap_len len <= alloc_ceiling -> mmap_addr_ok len [] a = true.
Proof.
  intros len a Hl H1 H2 H3. unfold mmap_addr_ok. rewrite page_size_eq, H1, Z.eqb_refl.
  rewrite (proj2 (Z.ltb_lt _ _) H2). rewrite (proj2 (Z.leb_le _ _) H3). reflexivity.
Qed.

Lemma nstep_dec_mmap_gen : forall len mo rsp mo' (isnone : bool),
  let h := m_vmmaps mo in
  0 < len < 2^63 ->
  ceil_ok mo ->   (* [comment removed for export] *)
  nstep (NMmap 0 len (if isnone then PROT_NONE else PROT_RW) MAPF) mo rsp mo' ->
  vm_only mo mo' /\
  exists x, (if isnone then dec_mmap_none len [] rsp else dec_mmap len [] rsp) = Some x /\
  match x with
  | MmErr e => e = ENOMEM /\ mo' = mo
  | MmOk a => mmap_addr_ok len [] a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                        (if isnone then (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h else vm_noaccess h)
                        (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros len mo rsp mo' isnone h Hlen Hce H. pose proof (nstep_mm_vm_only _ _ _ _ H) as Hv. split; [exact Hv|].
  pose proof (mmap_len_ge len ltac:(lia)) as Hml. pose proof alloc_ceiling_lt as Hcl. unfold ceil_ok in Hce.
  cbn -[mmap_model noaccess_model Z.eqb w wlen rlen grant_ok grant_ok_na] in H.
  rewrite MAPF_eq, Z.eqb_refl in H. rewrite (rlen_eq len) in H by lia.
  assert (Ewl : wlen len = Z_to_bv 64 (mmap_len len)) by (unfold wlen; rewrite rlen_eq by lia; reflexivity).
  rewrite Ewl in H.
  destruct isnone.
  - change (PROT_NONE =? NPROT_RW)%Z with false in H. cbv iota in H.
    destruct H as [(e & He & -> & ->)|(a & Hg & -> & ->)].
    + apply mmap_errnos_when_sub in He. cbn in He. destruct He as [<-|[]]. exists (MmErr ENOMEM). split; [|split; reflexivity].
      cbn -[errno_of errno_ret]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    + (first [ pose proof ((grant_ok_na_facts _ _ _ _ Hg)) as dR_11; dand4 dR_11 as G1 G2 G3 G4 | destruct (grant_ok_na_facts _ _ _ _ Hg) as (G1 & G2 & G3 & G4) ]). rewrite Hce in G3.
      pose proof (u64_range a) as Ra.
      exists (MmOk (bv_unsigned a)). rewrite Z_to_bv_bv_unsigned. split; [|split; [|split]].
      * cbn -[errno_of mmap_addr_ok mmap_len Z.eqb bv_eqb]. rewrite !bv_eqb_refl. cbn [andb].
        rewrite (mmap_addr_ok_intro len (bv_unsigned a)) by lia. reflexivity.
      * apply mmap_addr_ok_intro; lia.
      * exact G4.
      * unfold noaccess_model. rewrite with_vmmaps_vm. reflexivity.
  - change (PROT_RW =? NPROT_RW)%Z with true in H. cbv iota in H.
    destruct H as [(e & He & -> & ->)|(a & Hg & -> & ->)].
    + apply mmap_errnos_when_sub in He. cbn in He. destruct He as [<-|[]]. exists (MmErr ENOMEM). split; [|split; reflexivity].
      cbn -[errno_of errno_ret]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    + (first [ pose proof ((grant_ok_facts _ _ _ _ Hg)) as dR_12; dand4 dR_12 as G1 G2 G3 G4 | destruct (grant_ok_facts _ _ _ _ Hg) as (G1 & G2 & G3 & G4) ]). rewrite Hce in G3.
      pose proof (u64_range a) as Ra.
      exists (MmOk (bv_unsigned a)). rewrite Z_to_bv_bv_unsigned. split; [|split; [|split]].
      * cbn -[errno_of mmap_addr_ok mmap_len Z.eqb bv_eqb]. rewrite !bv_eqb_refl. cbn [andb].
        rewrite (mmap_addr_ok_intro len (bv_unsigned a)) by lia. reflexivity.
      * apply mmap_addr_ok_intro; lia.
      * exact G4.
      * unfold mmap_model. rewrite with_vmmaps_vm. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nstep_dec_mmap_gen_nf : forall len mo rsp mo' (isnone : bool),
  let h := m_vmmaps mo in
  0 < len < 2^63 ->
  ceil_ok mo ->
  nrefusable (NMmap 0 len (if isnone then PROT_NONE else PROT_RW) MAPF) mo = false ->
  nstep (NMmap 0 len (if isnone then PROT_NONE else PROT_RW) MAPF) mo rsp mo' ->
  vm_only mo mo' /\
  exists a, (if isnone then dec_mmap_none len [] rsp else dec_mmap len [] rsp) = Some (MmOk a)
      /\ mmap_addr_ok len [] a = true
      /\ region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
      /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps h)
                        (if isnone then (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess h else vm_noaccess h)
                        (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros len mo rsp mo' isnone h Hlen Hce NR H. pose proof (nstep_mm_vm_only _ _ _ _ H) as Hv. split; [exact Hv|].
  pose proof (mmap_len_ge len ltac:(lia)) as Hml. pose proof alloc_ceiling_lt as Hcl. unfold ceil_ok in Hce.
  apply (proj1 (nstep_nf_iff _ mo rsp mo' NR)) in H.
  cbn -[mmap_model noaccess_model Z.eqb w wlen rlen grant_ok grant_ok_na] in H.
  rewrite MAPF_eq, Z.eqb_refl in H. rewrite (rlen_eq len) in H by lia.
  assert (Ewl : wlen len = Z_to_bv 64 (mmap_len len)) by (unfold wlen; rewrite rlen_eq by lia; reflexivity).
  rewrite Ewl in H.
  destruct isnone.
  - change (PROT_NONE =? NPROT_RW)%Z with false in H. cbv iota in H.
    destruct H as (a & Hg & -> & ->).
    destruct (grant_ok_na_facts _ _ _ _ Hg) as (G1 & G2 & G3 & G4). rewrite Hce in G3.
    pose proof (u64_range a) as Ra.
    exists (bv_unsigned a). rewrite Z_to_bv_bv_unsigned. split; [|split; [|split]].
    + cbn -[errno_of mmap_addr_ok mmap_len Z.eqb bv_eqb]. rewrite !bv_eqb_refl. cbn [andb].
      rewrite (mmap_addr_ok_intro len (bv_unsigned a)) by lia. reflexivity.
    + apply mmap_addr_ok_intro; lia.
    + exact G4.
    + unfold noaccess_model. rewrite with_vmmaps_vm. reflexivity.
  - change (PROT_RW =? NPROT_RW)%Z with true in H. cbv iota in H.
    destruct H as (a & Hg & -> & ->).
    destruct (grant_ok_facts _ _ _ _ Hg) as (G1 & G2 & G3 & G4). rewrite Hce in G3.
    pose proof (u64_range a) as Ra.
    exists (bv_unsigned a). rewrite Z_to_bv_bv_unsigned. split; [|split; [|split]].
    + cbn -[errno_of mmap_addr_ok mmap_len Z.eqb bv_eqb]. rewrite !bv_eqb_refl. cbn [andb].
      rewrite (mmap_addr_ok_intro len (bv_unsigned a)) by lia. reflexivity.
    + apply mmap_addr_ok_intro; lia.
    + exact G4.
    + unfold mmap_model. rewrite with_vmmaps_vm. reflexivity.
Qed.

Lemma nstep_dec_munmap : forall addr len mo rsp mo',
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  0 <= addr < 2^64 -> 0 < len < 2^64 ->
  nstep (NMunmap addr len) mo rsp mo' ->
  vm_only mo mo' /\ dec_munmap addr len rsp = Some (RgDone true) /\
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) a)
                   (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                   (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros addr len mo rsp mo' h a n Ha Hlen H. pose proof (nstep_mm_vm_only _ _ _ _ H) as Hv. split; [exact Hv|].
  cbn -[munmap_model w wlen rlen Z.eqb] in H. destruct H as [-> ->].
  assert (Ewl : wlen len = n) by (unfold wlen; rewrite rlen_eq by lia; reflexivity). rewrite Ewl.
  change (w addr) with a. split.
  - cbn -[errno_of Z.eqb bv_eqb mmap_len w]. unfold w. rewrite u64_lit by lia. rewrite Z.eqb_refl. fold n. rewrite !bv_eqb_refl. reflexivity.
  - unfold munmap_model, with_mmap_destroyed. rewrite m_vmmaps_vm_forget_range, with_vmmaps_vm. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mat_with_vmmaps h m : m_vm_materialized (with_vmmaps h m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma mat_vm_forget_range lo hi m : m_vm_materialized m = [] -> m_vm_materialized (vm_forget_range lo hi m) = [].
Proof. intros H. unfold vm_forget_range, with_vm_backing. cbn. rewrite H. reflexivity. Qed.
Lemma mat_forget_vm_ranges l m : m_vm_materialized m = [] -> m_vm_materialized (forget_vm_ranges l m) = [].
Proof. revert m. induction l as [|[a b] l IH]; intros m H; cbn; [exact H|]. apply IH. apply mat_vm_forget_range. exact H. Qed.
Lemma mat_brk_model req r m : m_vm_materialized m = [] -> m_vm_materialized (brk_model req r m) = [].
Proof. intros H. unfold brk_model, with_brk_next. apply mat_forget_vm_ranges. rewrite mat_with_vmmaps. exact H. Qed.
Lemma mat_mmap_model a n m : m_vm_materialized (mmap_model a n m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma mat_noaccess_model a n m : m_vm_materialized (noaccess_model a n m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma mat_munmap_model a n m : m_vm_materialized m = [] -> m_vm_materialized (munmap_model a n m) = [].
Proof. intros H. unfold munmap_model, with_mmap_destroyed. apply mat_vm_forget_range. rewrite mat_with_vmmaps. exact H. Qed.
Lemma mat_fixed_noaccess_model a n m : m_vm_materialized m = [] -> m_vm_materialized (fixed_noaccess_model a n m) = [].
Proof. intros H. unfold fixed_noaccess_model. apply mat_vm_forget_range. rewrite mat_with_vmmaps. exact H. Qed.
Lemma mat_fixed_destroyed_model a n m : m_vm_materialized m = [] -> m_vm_materialized (fixed_destroyed_model a n m) = [].
Proof. intros H. unfold fixed_destroyed_model. apply mat_vm_forget_range. rewrite mat_with_vmmaps. exact H. Qed.
Lemma mat_mprotect_model a n m : m_vm_materialized (mprotect_model a n m) = m_vm_materialized m.
Proof. reflexivity. Qed.
Lemma mat_mremap_model_next m old on dst nn : m_vm_materialized m = [] -> m_vm_materialized (mremap_model_next m old on dst nn) = [].
Proof.
  intros H. unfold mremap_model_next, vm_resize_backing, with_vm_backing. cbn.
  change (m_vm_materialized (with_vmmaps (mremap_maps_next (m_vmmaps m) old dst nn) m)) with (m_vm_materialized m).
  rewrite H. cbn. destruct (mremap_source_lazy_b m old on); reflexivity.
Qed.
(* [comment removed for export] *)
Lemma nstep_mat : forall n md eff md', m_vm_materialized md = [] -> nstep n md eff md' -> m_vm_materialized md' = [].
Proof.
  intros n md eff md' H Hs. destruct n; cbn in Hs; try contradiction.
  - (first [ dex1 Hs as r; dand3 Hs as _ _ -> | dand4 Hs as r _ _ -> | destruct Hs as (r & _ & _ & ->) ]). apply mat_brk_model. exact H.
  - destruct (_ =? _).
    + destruct (_ =? _).
      * destruct Hs as [(e & _ & _ & ->)|(a & _ & _ & ->)]; [exact H| rewrite mat_mmap_model; exact H].
      * destruct Hs as [(e & _ & _ & ->)|(a & _ & _ & ->)]; [exact H| rewrite mat_noaccess_model; exact H].
    + destruct Hs as [(e & _ & _ & ->)|[(_ & ->)|(_ & e & _ & _ & ->)]]; [exact H| apply mat_fixed_noaccess_model; exact H| apply mat_fixed_destroyed_model; exact H].
  - destruct Hs as [_ ->]. apply mat_munmap_model. exact H.
  - destruct Hs as [(e & _ & _ & ->)|(_ & _ & ->)]; [exact H| rewrite mat_mprotect_model; exact H].
  - destruct Hs as [(_ & _ & ->)|(_ & [(e & _ & _ & ->)|[(_ & _ & ->)|[(_ & _ & _ & ->)|(_ & dst & _ & _ & ->)]]])];
      first [exact H| apply mat_mremap_model_next; exact H].
Qed.

(* [comment removed for export] *)
Definition phase_inv (ph : brk_phase) (L : mled) (pbrk : Z) (mo : Model) : Prop :=
  match ph with
  | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
  | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
  | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
      /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
      /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
      /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
  | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
  | BPDead => True
  end.

Lemma KL_rephase : forall L ph pbrk pbrk' mo,
  KL L pbrk mo -> phase_inv ph L pbrk' mo -> KL (set_brkph ph L) pbrk' mo.
Proof. intros L ph pbrk pbrk' mo K Hph. kl_open K; constructor; cbn; auto. Qed.

Lemma KL_dead : forall L pbrk pbrk' mo, KL L pbrk mo -> KL (set_brkph BPDead L) pbrk' mo.
Proof. intros. eapply KL_rephase; [eassumption| exact I]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk0_ok : forall L G s0, gframe G -> ld_brk L = BPUntried ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (r <- msys (NBrk 0) dec_brk0 ;; mupd (set_brk_ps r) ;;; mret r)
        (ev_step_post L (EBrk 0) G s0).
Proof.
  intros L G s0 HG Hph.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ G s mo /\ brk0_answer_ok r = true /\ KL (set_brkph (BPQueried r) L) r mo)).
    (intros s mo; (first [ intro dR_112; dand3 dR_112 as -> HK HGs | intros (-> & HK & HGs) ])). split; [exact I|].
    intros rsp mo' Hst.
    (first [ pose proof ((nstep_dec_brk0 _ _ _ Hst)) as dR_14; dand3 dR_14 as Hdec Hvo -> | pose proof (nstep_dec_brk0 _ _ _ Hst) as (Hdec & Hvo & ->) ]).
    exists (bv_unsigned (vm_brk (m_vmmaps mo))). split; [exact Hdec|].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
    (first [ pose proof ((kl_start _ _ _ HK)) as dR_15; dand4 dR_15 as S1 S2 S3 S4 | pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4) ]).
    splits.
    - reflexivity.
    - exact HGs.
    - unfold brk0_answer_ok. rewrite Ebrk. pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo))) as R. unfold bv_modulus in R.
      unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - eapply KL_rephase; [exact HK|]. cbn [phase_inv]. rewrite Ebrk. splits; auto. }
  intros r. cbn beta. eapply mspec_bind.
  { apply mspec_upd. }
  intros []. apply mspec_ret. (intros s mo; (first [ intro dR_113; dex1 dR_113 as s1; dand5 dR_113 as -> -> HGs Hans HK | intro dR_113; dand6 dR_113 as s1 -> -> HGs Hans HK | intros (s1 & -> & -> & HGs & Hans & HK) ])). unfold ev_step_post. cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post Z.eqb].
  splits; auto. eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
Qed.

Lemma mspec_get_bind_eq {St A} (s0 : St) (P : assn St) (f : St -> Monad.M St A) Q :
  mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof. intros H s mo [-> HP]. unfold mbind, mget. cbn. apply H. auto. Qed.

Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

Lemma went_In_bounds : forall L pbrk mo b l, KL L pbrk mo ->
  (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) ->
  0 < b /\ 0 < mmap_len l /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))
  /\ elo (went b (mmap_len l)) = b /\ ehi (went b (mmap_len l)) = b + mmap_len l.
Proof.
  intros L pbrk mo b l K Hin. pose proof alloc_ceiling_lt.
  assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= alloc_ceiling /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))) as (Hl & Hb & Hc & Hm).
  { destruct Hin as [Hin|[k Hin]]; [pose proof (kl_groups _ _ _ K _ _ Hin)| pose proof (kl_metas _ _ _ K _ _ _ Hin)]; tauto. }
  pose proof (mmap_len_ge l ltac:(lia)). splits; auto; try lia.
  - apply elo_went. lia.
  - apply ehi_went; lia.
Qed.

Lemma In_lranges : forall L x, In x (lranges L) ->
  In x (ld_resv L)
  \/ (exists b l, In (b, l) (ld_groups L) /\ x = (b, round_up_pg l))
  \/ (exists b l k, In (b, l, k) (ld_metas L) /\ x = (b, round_up_pg l))
  \/ (exists b l, ld_brkreg L = Some (b, l) /\ x = (b + PGSZ, round_up_pg l - PGSZ)).
Proof.
  intros L x Hin. unfold lranges in Hin. rewrite !in_app_iff in Hin. destruct Hin as [H|[H|[H|H]]].
  - left; exact H.
  - right; left. apply in_map_iff in H as ([b l] & <- & H). exists b, l. auto.
  - right; right; left. apply in_map_iff in H as ([[b l] k] & <- & H). exists b, l, k. auto.
  - right; right; right. destruct (ld_brkreg L) as [[b l]|]; [|destruct H]. destruct H as [<-|[]]. exists b, l. auto.
Qed.

(* [comment removed for export] *)
Lemma KL_lbrk_pages_ok : forall L pbrk mo lo len,
  KL L pbrk mo ->
  let h := m_vmmaps mo in
  0 < lo -> 0 < len -> lo + len <= alloc_ceiling ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 lo) (Z_to_bv 64 len) = true ->
  (forall b l, ld_brkreg L = Some (b, l) -> l mod PGSZ = 0 /\ (b + l <= lo \/ lo + len <= b + PGSZ)) ->
  lbrk_pages_ok L lo len = true.
Proof.
  intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof alloc_ceiling_lt as Hcl.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ulo, Ulen in D. exact D.
  - injection E as -> ->. (first [ pose proof ((went_In_bounds _ _ _ b1 l1 HK (or_introl H))) as dR_16; dand6 dR_16 as B1 B2 B3 B4 B5 B6 | pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. (first [ pose proof ((went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H)))) as dR_17; dand6 dR_17 as B1 B2 B3 B4 B5 B6 | pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk_grow1_ok : forall L G s0 cur, gframe G -> ld_brk L = BPQueried cur ->
  let req := round_up_pg cur + 2 * PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) G s0).
Proof.
  intros L G s0 cur HG Hph req. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
                match a with
                | BrkGrown => KL (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
                | BrkSame => KL (set_brkph BPDead L) cur mo
                end)).
    (intros s mo; (first [ intro dR_114; dand3 dR_114 as -> HK HGs | intros (-> & HK & HGs) ])). split; [exact I|].
    intros rsp mo' Hst.
    pose proof (minv_preserved _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. (first [ dand4 Kph as Ecur Ebrk Epbrk Ereg | destruct Kph as (Ecur & Ebrk & Epbrk & Ereg) ]).
    (first [ pose proof ((kl_start _ _ _ HK)) as dR_19; dand4 dR_19 as S1 S2 S3 S4 | pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4) ]).
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    set (h := m_vmmaps mo) in *.
    assert (A1 : 0 < bv_unsigned (vm_brk h)) by lia.
    assert (A2 : bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h)) by lia.
    assert (A3 : bv_unsigned (vm_brk h) < req < 2^64) by (unfold PGSZ in *; lia).
    assert (A4 : bv_unsigned (vm_brk h) mod 4096 = 0) by (rewrite Ebrk, Ecur; exact S2).
    assert (A5 : req mod 4096 = 0) by (rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity).
    (first [ pose proof ((nstep_dec_brk req mo rsp mo' A1 A2 A3 A4 A5 Hst)) as dR_20; dand4 dR_20 as Hvo a Hdec Ha | pose proof (nstep_dec_brk req mo rsp mo' A1 A2 A3 A4 A5 Hst) as (Hvo & a & Hdec & Ha) ]).
    fold h in Hdec, Ha. rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    destruct a.
    - (* [comment removed for export] *)
      destruct Ha as [Hgo Emo'].
      apply brk_grow_ok_facts in Hgo; [| exact A1| exact A3| exact A4| exact A5].
      destruct Hgo as [Hceil Hrf]. fold h in Hrf.
      pose proof (kl_ceil _ _ _ HK) as Kc. unfold ceil_ok in Kc. fold h in Kc, Hceil. rewrite Kc in Hceil.   (* [comment removed for export] *)
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KL_lbrk_pages_ok L (ps_brk s0) mo cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace cur with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = 2 * PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      split; [|exact HPG].
      kl_open HK. constructor; rewrite ?Emo'; rewrite ?with_vmmaps_vm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      + intros b l Hin. specialize (Kgr b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l k Hin. specialize (Kme b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l Hb. rewrite Ereg in Hb. discriminate.
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
        * exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
        * intros b l Hin. (first [ pose proof ((went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kmr Knc Kgna Kmat Kcpl Kbb Klim Kceil) (or_introl Hin))) as dR_21; dand6 dR_21 as B1 B2 B3 B4 B5 B6 | pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kmr Knc Kgna Kmat Kcpl Kbb Klim Kceil) (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        * intros b l k Hin. (first [ pose proof ((went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kmr Knc Kgna Kmat Kcpl Kbb Klim Kceil) (or_intror (ex_intro _ k Hin)))) as dR_22; dand6 dR_22 as B1 B2 B3 B4 B5 B6 | pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kresv Krt Kstart Kgr Kme Kdis Kreg Kph Kmr Knc Kgna Kmat Kcpl Kbb Klim Kceil) (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
      + intros e [<-|He]; [cbn [fst snd]; eapply region_free_app_l; exact Hrf| apply Kmr; exact He].
      + intros e He. (first [ pose proof ((Knc e He)) as dR_23; dex1 dR_23 as e'; dand4 dR_23 as He' Q1 Q0 Q2 | pose proof ((Knc e He)) as dR_23; dand5 dR_23 as e' He' Q1 Q0 Q2 | destruct (Knc e He) as (e' & He' & Q1 & Q0 & Q2) ]). exists e'. split; [right; exact He'|]. split; [|split]; assumption.
      + intros e [<-|He].
        * right; right. rewrite elo_pair, ehi_pair, Hn, unsigned_lit by (unfold PGSZ in *; lia). unfold PGSZ in *. splits; lia.
        * destruct (Kcpl e He) as [X|[X|X]]; [left; exact X| right; left; exact X| right; right].
          rewrite unsigned_lit by (unfold PGSZ in *; lia). fold h in X. lia.
      + unfold brk_extent in *. cbn [ld_brkreg set_brkph] in *. rewrite Ereg in *. rewrite unsigned_lit by (unfold PGSZ in *; lia). fold h. unfold PGSZ in *. lia.
    - (* [comment removed for export] *)
      subst mo'. apply KL_dead with (pbrk := ps_brk s0). exact HK. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    (intros s mo; (first [ intro dR_115; dex1 dR_115 as s1; dand6 dR_115 as -> -> HGs [Hne Hpos] Ecur [HK HPG] | intro dR_115; dand7 dR_115 as s1 -> -> HGs [Hne Hpos] Ecur [HK HPG] | intros (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & [HK HPG]) ])). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. (intros s mo; (first [ intro dR_116; dand5 dR_116 as -> HGs [Hne Hpos] Ecur HK | intros (-> & HGs & [Hne Hpos] & Ecur & HK) ])). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ecur.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk_grow2_ok : forall L G s0 b l, gframe G -> ld_brk L = BPLive -> ld_brkreg L = Some (b, l) ->
  let req := b + l + PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) G s0).
Proof.
  intros L G s0 b l HG Hph Ereg req. pose proof alloc_ceiling_lt as Hcl.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
                match a with
                | BrkGrown => KL (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
                | BrkSame => KL (set_brkph BPDead L) (b + l) mo
                end)).
    (intros s mo; (first [ intro dR_117; dand3 dR_117 as -> HK HGs | intros (-> & HK & HGs) ])). split; [exact I|].
    intros rsp mo' Hst.
    pose proof (minv_preserved _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. (first [ dex2 Kph as b' l'; dand3 Kph as Ereg' Ebrk Epbrk | dand5 Kph as b' l' Ereg' Ebrk Epbrk | destruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk) ]).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    (first [ pose proof ((kl_brkreg _ _ _ HK b l Ereg)) as dR_25; dand6 dR_25 as R1 R2 R3 R4 R5 Rcov | pose proof (kl_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov) ]).
    (first [ pose proof ((kl_start _ _ _ HK)) as dR_26; dand4 dR_26 as S1 S2 S3 S4 | pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4) ]).
    set (h := m_vmmaps mo) in *.
    assert (A1 : 0 < bv_unsigned (vm_brk h)) by lia.
    assert (A2 : bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h)) by lia.
    assert (A3 : bv_unsigned (vm_brk h) < req < 2^64) by (unfold PGSZ in *; lia).
    assert (A4 : bv_unsigned (vm_brk h) mod 4096 = 0) by (rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity).
    assert (A5 : req mod 4096 = 0) by (subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity).
    (first [ pose proof ((nstep_dec_brk req mo rsp mo' A1 A2 A3 A4 A5 Hst)) as dR_27; dand4 dR_27 as Hvo a Hdec Ha | pose proof (nstep_dec_brk req mo rsp mo' A1 A2 A3 A4 A5 Hst) as (Hvo & a & Hdec & Ha) ]).
    fold h in Hdec, Ha. rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    destruct a.
    - (* [comment removed for export] *)
      destruct Ha as [Hgo Emo'].
      apply brk_grow_ok_facts in Hgo; [| exact A1| exact A3| exact A4| exact A5].
      destruct Hgo as [Hceil Hrf]. fold h in Hrf.
      pose proof (kl_ceil _ _ _ HK) as Kc. unfold ceil_ok in Kc. fold h in Kc, Hceil. rewrite Kc in Hceil.   (* [comment removed for export] *)
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KL_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [lia| unfold PGSZ; lia| subst req; lia| |].
        - replace (b + l) with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      split; [|exact HPG].
      kl_open HK. constructor; rewrite ?Emo'; rewrite ?with_vmmaps_vm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      + intros b0 l0 Hin. (first [ pose proof ((WB b0 l0 (or_introl Hin))) as dR_28; dand6 dR_28 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kgr b0 l0 Hin). (first [ dand6 Kgr as [G0 G1] G2 G3 G4 G5 G6 | destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6) ]). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
      + intros b0 l0 k Hin. (first [ pose proof ((WB b0 l0 (or_intror (ex_intro _ k Hin)))) as dR_30; dand6 dR_30 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kme b0 l0 k Hin). (first [ dand9 Kme as [G0 G1] G2 G3 G4 G5 G6 G7 G8 G9 | destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9) ]). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
      + intros b1 l1 E. injection E as <- <-. splits; auto.
        * clear -R3. unfold PGSZ in *; lia.
        * unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
        * clear -Hceil. subst req. lia.
        * intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
          -- (first [ pose proof ((Rcov x ltac:(lia))) as dR_32; dex1 dR_32 as e; destruct dR_32 as [He Hr'] | pose proof ((Rcov x ltac:(lia))) as dR_32; dand3 dR_32 as e He Hr' | destruct (Rcov x ltac:(lia)) as (e & He & Hr') ]). exists e. split; [right; exact He| exact Hr'].
          -- exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
      + rewrite Hph. exists b, (l + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; lia.
      + intros e [<-|He]; [cbn [fst snd]; eapply region_free_app_l; exact Hrf| apply Kmr; exact He].
      + intros e He. (first [ pose proof ((Knc e He)) as dR_33; dex1 dR_33 as e'; dand4 dR_33 as He' Q1 Q0 Q2 | pose proof ((Knc e He)) as dR_33; dand5 dR_33 as e' He' Q1 Q0 Q2 | destruct (Knc e He) as (e' & He' & Q1 & Q0 & Q2) ]). exists e'. split; [right; exact He'|]. split; [|split]; assumption.
      + intros e [<-|He].
        * right; right. rewrite elo_pair, ehi_pair, Hn, unsigned_lit by (unfold PGSZ in *; lia). unfold PGSZ in *. splits; lia.
        * destruct (Kcpl e He) as [X|[X|X]]; [left; exact X| right; left; exact X| right; right].
          rewrite unsigned_lit by (unfold PGSZ in *; lia). fold h in X. lia.
      + unfold brk_extent in *. cbn [ld_brkreg set_brkreg] in *. rewrite Ereg in Kbb. rewrite unsigned_lit by (unfold PGSZ in *; lia). fold h in Kbb. unfold PGSZ in *. lia.
    - (* [comment removed for export] *)
      subst mo'. apply KL_dead with (pbrk := ps_brk s0). exact HK. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    (intros s mo; (first [ intro dR_118; dex1 dR_118 as s1; dand6 dR_118 as -> -> HGs [Hne Hpos] Ecur HK | intro dR_118; dand7 dR_118 as s1 -> -> HGs [Hne Hpos] Ecur HK | intros (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & HK) ])). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    destruct HK as [HK HPG].
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. (intros s mo; (first [ intro dR_119; dand5 dR_119 as -> HGs [Hne Hpos] Ecur HK | intros (-> & HGs & [Hne Hpos] & Ecur & HK) ])). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Ecur.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wcov_rf_disj : forall maps lo hi aw nw,
  wcov maps lo hi -> region_free maps aw nw = true -> 0 < bv_unsigned nw -> lo < hi ->
  bv_unsigned aw + bv_unsigned nw <= lo \/ hi <= bv_unsigned aw.
Proof.
  intros maps lo hi aw nw Hc Hrf Hn Hlh.
  destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
  destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
  (first [ pose proof ((Hc (Z.max (bv_unsigned aw) lo) ltac:(lia))) as dR_34; dex1 dR_34 as e; destruct dR_34 as [He Hr] | pose proof ((Hc (Z.max (bv_unsigned aw) lo) ltac:(lia))) as dR_34; dand3 dR_34 as e He Hr | destruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr) ]).
  pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.


Lemma mmap_len_pos_pg : forall l, 0 < l -> PGSZ <= mmap_len l.
Proof.
  intros l Hl. pose proof (mmap_len_ge l Hl). pose proof (mmap_len_aligned l).
  pose proof (Z_div_mod_eq_full (mmap_len l) 4096). unfold PGSZ. nia.
Qed.

Lemma KL_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
  KL L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  mmap_addr_ok len [] a = true ->
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  minv mo' -> m_halted mo' = None -> m_vm_materialized mo' = [] ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
  /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false.
Proof.
  intros L pbrk mo mo' a len isnone HK Hq Hlen h n Hok Hrf Hmi' Hh' Hmat' Evm. pose proof alloc_ceiling_lt as Hcl.
  apply mmap_addr_ok_true in Hok as [(A1 & A2 & A3) _]. rewrite page_size_eq in A1. fold n in A3.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
  (* [comment removed for export] *)
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. (first [ pose proof ((WB b0 l0 H)) as dR_35; dand6 dR_35 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. (first [ pose proof ((kl_brkreg _ _ _ HK b0 l0 E)) as dR_36; dand6 dR_36 as R1 R2 R3 R4 R5 Rcov | pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov) ]).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
        pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ua, Un in D. exact D.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
      - injection E as -> ->. (first [ pose proof ((kl_brkreg _ _ _ HK b0 l0 H)) as dR_37; dand6 dR_37 as R1 R2 R3 R4 R5 _ | pose proof (kl_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _) ]).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      (first [ pose proof ((WB a l0 (or_introl Hin))) as dR_38; dand3 dR_38 as B1 B2 _ | pose proof (WB a l0 (or_introl Hin)) as (B1 & B2 & _) ]). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      (first [ pose proof ((WB a l0 (or_intror (ex_intro _ k Hin)))) as dR_39; dand3 dR_39 as B1 B2 _ | pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _) ]). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  kl_open HK.
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
            match ld_brk L' with
            | BPUntried => vm_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo') /\ ld_brkreg L' = None
            | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo')) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur /\ pbrk = cur /\ ld_brkreg L' = None
            | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo'))
                /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
                /\ ld_brkreg L' = None /\ cur + 2 * PGSZ <= alloc_ceiling
                /\ (exists e, In e (vm_maps (m_vmmaps mo')) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
                /\ (forall b l, In (b, l) (ld_groups L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
                /\ (forall b l k, In (b, l, k) (ld_metas L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
            | BPLive => exists b l, ld_brkreg L' = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = b + l /\ pbrk = b + l
            | BPDead => True
            end).
  { intros L' E1 E2. rewrite E1, E2, Evm. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  destruct isnone; constructor;
    first [ apply (Hph' (set_metas _ L)); reflexivity
          | apply (Hph' (set_groups _ L)); reflexivity
          | rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n in Hq2. lia.
    + specialize (Kme b0 l0 k Hin). (first [ dand9 Kme as [G0 G1] G2 G3 G4 G5 G6 G7 G8 G9 | destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9) ]). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. (first [ pose proof ((G9 q Hq1 Hq2)) as dR_41; dex1 dR_41 as e; destruct dR_41 as [He Hr] | pose proof ((G9 q Hq1 Hq2)) as dR_41; dand3 dR_41 as e He Hr | destruct (G9 q Hq1 Hq2) as (e & He & Hr) ]). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). (first [ dand6 Kreg as R1 R2 R3 R4 R5 Rcov | destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov) ]). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - intros e [<-|He]; [cbn [fst snd]; eapply region_free_app_l; exact Hrf| apply Kmr; exact He].
  - intros e [<-|He].
    + exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. unfold elo, ehi. cbn [fst snd]. rewrite Ua, Un. lia.
    + (first [ pose proof ((Knc e He)) as dR_43; dex1 dR_43 as e'; dand4 dR_43 as He' Q1 Q0 Q2 | pose proof ((Knc e He)) as dR_43; dand5 dR_43 as e' He' Q1 Q0 Q2 | destruct (Knc e He) as (e' & He' & Q1 & Q0 & Q2) ]). exists e'. split; [right; exact He'|]. split; [|split]; assumption.
  - intros b0 l0 Hin. apply region_free_intro. intros b1 s1 [E|Hb1].
    + injection E as <- <-. rewrite Ua, Un. pose proof (Dgm b0 l0 (or_introl Hin)) as D.
      (first [ pose proof ((WB b0 l0 (or_introl Hin))) as dR_44; dand6 dR_44 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6) ]). unfold wz. rewrite !unsigned_lit by lia. lia.
    + exact (region_free_In _ _ _ _ _ (Kgna b0 l0 Hin) Hb1).
  - intros e [<-|He].
    + right; left. exists a, len, 0. split; [left; reflexivity| reflexivity].
    + destruct (Kcpl e He) as [X|[(b0 & l0 & k & Hin & E)|X]]; [left; exact X| right; left; exists b0, l0, k; split; [right; exact Hin| exact E]| right; right; exact X].
  - (* [comment removed for export] *) unfold ceil_ok. rewrite Evm, alloc_top_mkVmMapsFull. pose proof Kceil as Kc'. unfold ceil_ok, alloc_top in Kc'. exact Kc'.
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
    + specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). (first [ dand9 Kme as [G0 G1] G2 G3 G4 G5 G6 G7 G8 G9 | destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9) ]). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). (first [ dand6 Kreg as R1 R2 R3 R4 R5 Rcov | destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov) ]). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - intros e [<-|He]; [cbn [fst snd]; eapply region_free_app_l; exact Hrf| apply Kmr; exact He].
  - intros e He. (first [ pose proof ((Knc e He)) as dR_47; dex1 dR_47 as e'; dand4 dR_47 as He' Q1 Q0 Q2 | pose proof ((Knc e He)) as dR_47; dand5 dR_47 as e' He' Q1 Q0 Q2 | destruct (Knc e He) as (e' & He' & Q1 & Q0 & Q2) ]). exists e'. split; [right; exact He'|]. split; [|split]; assumption.
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. apply region_free_intro. intros b1 s1 Hb1.
      (first [ pose proof ((Knc _ Hb1)) as dR_48; dex1 dR_48 as e'; dand4 dR_48 as He' Q1 Q0 Q2 | pose proof ((Knc _ Hb1)) as dR_48; dand5 dR_48 as e' He' Q1 Q0 Q2 | destruct (Knc _ Hb1) as (e' & He' & Q1 & Q0 & Q2) ]).
      pose proof (region_free_In _ _ _ (fst e') (snd e') Hrfm ltac:(destruct e'; exact He')) as D.
      unfold elo, ehi in Q1, Q2. cbn [fst snd] in Q1, Q2. unfold wz. rewrite !unsigned_lit by lia. rewrite Ua, Un in D. lia.
    + exact (Kgna b0 l0 Hin).
  - intros e [<-|He].
    + left. exists a, len. split; [left; reflexivity| reflexivity].
    + destruct (Kcpl e He) as [(b0 & l0 & Hin & E)|[X|X]]; [left; exists b0, l0; split; [right; exact Hin| exact E]| right; left; exact X| right; right; exact X].
  - (* [comment removed for export] *) unfold ceil_ok. rewrite Evm, alloc_top_mkVmMapsFull. pose proof Kceil as Kc'. unfold ceil_ok, alloc_top in Kc'. exact Kc'.
Qed.

Lemma is_errno_form_neg : forall e, 1 <= e <= 4095 -> is_errno_form (neg_errno e) = true.
Proof. intros e He. unfold is_errno_form, neg_errno, TWO64. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
Lemma is_err_neg : forall e, 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof. intros e He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

Lemma ev_mmap_core : forall L G s0 len (isnone : bool), gframe G -> brk_quiet L -> 0 < len < LEN_MAX ->
  let prot := if isnone then PROT_NONE else PROT_RW in
  let dec := if isnone then dec_mmap_none len [] else dec_mmap len [] in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (a <- msys (NMmap 0 len prot MAPF) dec ;; mret match a with MmErr e => neg_errno e | MmOk x => x end)
        (ev_step_post L (EMmap 0 len prot MAPF) G s0).
Proof.
  intros L G s0 len isnone HG Hq Hlen prot dec.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1.
  eapply mspec_bind.
  { apply (mspec_sys (NMmap 0 len prot MAPF) dec _
             (fun x s mo => s = s0 /\ G s mo /\
                match x with
                | MmErr e => e = ENOMEM /\ KL L (ps_brk s0) mo
                | MmOk a => KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) (ps_brk s0) mo
                            /\ mmap_answer_ok (lranges L) len a = true /\ is_err a = false
                end)).
    (intros s mo; (first [ intro dR_120; dand3 dR_120 as -> HK HGs | intros (-> & HK & HGs) ])). split.
    { subst prot. destruct isnone; [apply nsafe_mmap_none| apply nsafe_mmap_rw]; unfold LEN_MAX in Hlen; lia. }
    intros rsp mo' Hst.
    pose proof (minv_preserved _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
    assert (Hcase : vm_only mo mo' /\ exists x, dec rsp = Some x /\
              match x with
              | MmErr e => e = ENOMEM /\ mo' = mo
              | MmOk a => mmap_addr_ok len [] a = true
                  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
                  /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                       (if isnone then (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                       (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))
              end).
    { subst prot dec. destruct isnone;
        [ exact (nstep_dec_mmap_gen len mo rsp mo' true ltac:(unfold LEN_MAX in Hlen; exact Hlen) (kl_ceil _ _ _ HK) Hst)
        | exact (nstep_dec_mmap_gen len mo rsp mo' false ltac:(unfold LEN_MAX in Hlen; exact Hlen) (kl_ceil _ _ _ HK) Hst) ]. }
    (first [ dand4 Hcase as Hvo x Hd Hx | destruct Hcase as (Hvo & x & Hd & Hx) ]). exists x. split; [exact Hd|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    destruct x as [e|a].
    - destruct Hx as [-> ->]. split; [reflexivity| exact HK].
    - (first [ dand3 Hx as Hok Hrf Evm | destruct Hx as (Hok & Hrf & Evm) ]). apply (KL_mmap_new L (ps_brk s0) mo mo' a len isnone HK Hq Hlen Hok Hrf Hmi' Hh' (nstep_mat _ _ _ _ (kl_mat _ _ _ HK) Hst) Evm). }
  intros x. cbn beta. apply mspec_ret. (intros s mo; (first [ intro dR_121; dand3 dR_121 as -> HGs Hx | intros (-> & HGs & Hx) ])). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPF MAP_FIXED =? 0) with true. cbv iota.
  destruct x as [e|a].
  - destruct Hx as [-> HK]. rewrite is_err_neg by (unfold ENOMEM; lia).
    unfold mmap_answer_ok. rewrite is_errno_form_neg by (unfold ENOMEM; lia). splits; auto.
  - (first [ dand3 Hx as HK Hans Herr | destruct Hx as (HK & Hans & Herr) ]). rewrite Herr. subst prot. destruct isnone.
    + change (PROT_NONE =? PROT_NONE) with true. cbv iota. splits; auto.
    + change (PROT_RW =? PROT_NONE) with false. cbv iota. splits; auto.
Qed.

Lemma ev_mmap_ok : forall L G s0 len prot, gframe G -> brk_quiet L -> (prot = PROT_NONE \/ prot = PROT_RW) -> 0 < len < LEN_MAX ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMmap 0 len prot MAPF))
        (ev_step_post L (EMmap 0 len prot MAPF) G s0).
Proof.
  intros L G s0 len prot HG Hq Hprot Hlen. unfold ev_step.
  change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
  destruct Hprot as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota. apply (ev_mmap_core L G s0 len true HG Hq Hlen).
  - change (PROT_RW =? 0) with false. cbv iota. apply (ev_mmap_core L G s0 len false HG Hq Hlen).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_above : forall maps aw nw, (forall e, In e maps -> ehi e <= bv_unsigned aw) -> region_free maps aw nw = true.
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi in H; cbn in H.
  replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ev_mmap_fixed_ok : forall L G s0 cur, gframe G -> ld_brk L = BPGuard cur ->
  let a := round_up_pg cur in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMmap a PGSZ PROT_NONE MAPFX))
        (ev_step_post L (EMmap a PGSZ PROT_NONE MAPFX) G s0).
Proof.
  intros L G s0 cur HG Hph a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
  set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
  eapply mspec_bind.
  { apply (mspec_sys (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with FxKept e => e = ENOMEM | FxDone => True | FxLost e => e = ENOMEM end)).
    (intros s mo; (first [ intro dR_122; dand3 dR_122 as -> HK HGs | intros (-> & HK & HGs) ])).
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. (first [ dand8 Kph as Ecur Ebrk Epbrk Ereg Hceil (e0 & He0 & He0l & He0h) Dg Dm | destruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm) ]).
    (first [ pose proof ((kl_start _ _ _ HK)) as dR_53; dand4 dR_53 as S1 S2 S3 S4 | pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4) ]).
    assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
    set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 PGSZ).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + PGSZ).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus, PGSZ in *. lia. }
    assert (Hrf : region_free (vm_reserved h) aw nw = true).
    { apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kl_resv_top _ _ _ HK). exact He. }
    assert (Hmc : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    split.
    { cbn [nsafe]. right. rewrite wlen_PGSZ, rlen_PGSZ. unfold w. fold aw nw h. rewrite Ua, Un, page_size_eq.
      pose proof (kl_ceil _ _ _ HK) as Kc. unfold ceil_ok in Kc. fold h in Kc. rewrite Kc.   (* [comment removed for export] *)
      split; [reflexivity|]. split; [reflexivity|]. split; [apply (w_len_ne0 PGSZ); unfold PGSZ; lia|].
      split; [rewrite Ha, Ecur; exact S2|]. split; [lia|]. split; [unfold PGSZ; lia|]. split; [lia|].
      split; [exact Hrf| exact Hmc]. }
    intros rsp mo' Hst.
    pose proof (minv_preserved _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
    assert (HaC : a + PGSZ <= alloc_ceiling) by (unfold PGSZ in *; lia).   (* [comment removed for export] *)
    (first [ pose proof ((nstep_mmap_fixed_inv a mo rsp mo' ltac:(lia) HaC Hst)) as dR_54; dand4 dR_54 as Hvo x Hd Hx | pose proof (nstep_mmap_fixed_inv a mo rsp mo' ltac:(lia) HaC Hst) as (Hvo & x & Hd & Hx) ]).
    fold h aw nw in Hx. rewrite Ua, Un in Hx.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    (* [comment removed for export] *)
    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> (ehi e <= a \/ a + PGSZ <= elo e) -> In e maps') ->
              (forall e, In e maps' -> In e (vm_maps h) \/ In e (maps_subtract (vm_maps h) a (a + PGSZ))) ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (exists e', In e' maps' /\ elo e' <= a + PGSZ /\ a + 2 * PGSZ <= ehi e') ->
              (forall e, In e noacc' -> exists e', In e' maps' /\ elo e' <= elo e /\ elo e < ehi e /\ ehi e <= ehi e') ->
              (forall p, In p noacc' -> (elo p = a /\ ehi p = a + PGSZ) \/ exists e, In e (vm_noaccess h) /\ elo e <= elo p /\ ehi p <= ehi e) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              m_vm_materialized mo' = [] ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hback Hna Hcov' Hnacov Hnasub Evm Hmat'. subst L'.
      kl_open HK. constructor; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - intros b0 l0 Hin. (first [ pose proof ((WB b0 l0 (or_introl Hin))) as dR_55; dand6 dR_55 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6) ]). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgr b0 l0 Hin). (first [ dand6 Kgr as [G0 G1] G2 G3 G4 G5 G6 | destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6) ]). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. (first [ pose proof ((WB b0 l0 (or_intror (ex_intro _ k Hin)))) as dR_57; dand6 dR_57 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6) ]). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kme b0 l0 k Hin). (first [ dand9 Kme as [G0 G1] G2 G3 G4 G5 G6 G7 G8 G9 | destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9) ]). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. (first [ pose proof ((G9 q Hq1 Hq2)) as dR_59; dex1 dR_59 as e; dand3 dR_59 as He Hel Heh | pose proof ((G9 q Hq1 Hq2)) as dR_59; dand4 dR_59 as e He Hel Heh | destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh) ]).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + intros z Hz. (first [ dex1 Hcov' as e'; dand3 Hcov' as He' H1 H2 | dand4 Hcov' as e' He' H1 H2 | destruct Hcov' as (e' & He' & H1 & H2) ]). exists e'. split; [exact He'|]. lia.
      - exists a, (2 * PGSZ). splits; [reflexivity| lia| lia].
      - intros e He. destruct (Hback e He) as [Hem|Hem]; [apply Kmr; exact Hem|].
        (first [ pose proof ((maps_subtract_sub _ _ _ _ ltac:(intros e1 H1; exact (proj2 (proj1 Kwf e1 H1))) Hem)) as dR_61; dex1 dR_61 as ex; dand3 dR_61 as Hx0 Q1 Q2 | pose proof ((maps_subtract_sub _ _ _ _ ltac:(intros e1 H1; exact (proj2 (proj1 Kwf e1 H1))) Hem)) as dR_61; dand4 dR_61 as ex Hx0 Q1 Q2 | destruct (maps_subtract_sub _ _ _ _ ltac:(intros e1 H1; exact (proj2 (proj1 Kwf e1 H1))) Hem) as (ex & Hx0 & Q1 & Q2) ]).
        destruct e as [eb es], ex as [xb xs]. unfold elo, ehi in Q1, Q2. cbn in Q1, Q2. cbn [fst snd].
        pose proof (proj1 Hwf' _ He) as W. unfold elo, ehi in W. cbn in W.
        apply (region_free_sub _ xb xs eb es (Kmr _ Hx0)); cbn; lia.
      - intros b0 l0 Hin. pose proof (Dgm b0 l0 (or_introl Hin)) as D. (first [ pose proof ((WB b0 l0 (or_introl Hin))) as dR_62; dand6 dR_62 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6) ]).
        apply region_free_intro. intros b1 s1 Hb1. destruct (Hnasub _ Hb1) as [[E1 E2]|(e & He & Q1 & Q2)].
        + unfold elo, ehi in E1, E2. cbn in E1, E2. unfold wz. rewrite !unsigned_lit by lia. unfold PGSZ in *. lia.
        + destruct e as [eb es]. pose proof (region_free_In _ _ _ eb es (Kgna b0 l0 Hin) He). unfold elo, ehi in Q1, Q2. cbn in Q1, Q2. lia.
      - (* [comment removed for export] *)
        intros e He. destruct (Hback e He) as [Hem|Hem].
        + destruct (Kcpl e Hem) as [X|[X|X]]; [left; exact X| right; left; exact X| right; right; exact X].
        + (first [ pose proof ((maps_subtract_In _ _ _ _ Hem)) as dR_63; dex1 dR_63 as ex; destruct dR_63 as [H0 H1] | pose proof ((maps_subtract_In _ _ _ _ Hem)) as dR_63; dand3 dR_63 as ex H0 H1 | destruct (maps_subtract_In _ _ _ _ Hem) as (ex & H0 & H1) ]).
          pose proof (proj1 Kwf ex H0) as W0.
          destruct (Kcpl ex H0) as [(b0 & l0 & Hin & E0)|[(b0 & l0 & k & Hin & E0)|X]].
          * left. exists b0, l0. split; [exact Hin|].
            (first [ pose proof ((WB b0 l0 (or_introl Hin))) as dR_64; dand6 dR_64 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6) ]). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
            unfold elo, ehi in B5, B6. rewrite E0 in H1.
            rewrite iv_subtract_disjoint in H1; [destruct H1 as [<-|[]]; reflexivity| clear - B2 B3 B5 B6 Hcl; lia| unfold PGSZ; lia| clear - B5 B6 D; unfold PGSZ in *; lia].
          * right; left. exists b0, l0, k. split; [exact Hin|].
            (first [ pose proof ((WB b0 l0 (or_intror (ex_intro _ k Hin)))) as dR_65; dand6 dR_65 as B1 B2 B3 B4 B5 B6 | pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6) ]). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
            unfold elo, ehi in B5, B6. rewrite E0 in H1.
            rewrite iv_subtract_disjoint in H1; [destruct H1 as [<-|[]]; reflexivity| clear - B2 B3 B5 B6 Hcl; lia| unfold PGSZ; lia| clear - B5 B6 D; unfold PGSZ in *; lia].
          * right; right. destruct ex as [x0 s0']. cbn [fst snd] in H1. (first [ dand4 X as X1 X2 X3 X4 | destruct X as (X1 & X2 & X3 & X4) ]). unfold elo, ehi in X1, X2, X3, X4, W0. cbn [fst snd] in X1, X2, X3, X4, W0.
            assert (Ha0' : 0 <= a) by (clear - Ha Ecur S1; lia). assert (Hhi64' : a + PGSZ < 2^64) by (clear - Ha Ecur Hceil Hcl; unfold PGSZ in *; lia).
            pose proof (iv_subtract_sub' x0 s0' a (a + PGSZ) e ltac:(lia) H1) as [SB1 SB2].
            pose proof (iv_subtract_nonempty x0 s0' a (a + PGSZ) e ltac:(lia) ltac:(lia) Ha0' Hhi64' H1) as NE.
            pose proof (iv_subtract_ends x0 s0' a (a + PGSZ) e ltac:(lia) Ha0' ltac:(lia) H1) as [E1 E2].
            assert (AA : a mod PGSZ = 0) by (rewrite Ha, Ecur; exact S2). fold h in X1, X2.
            split; [clear - X1 SB1; lia|]. split; [clear - NE SB2 X2; lia|]. split.
            -- destruct E1 as [E1|E1]; rewrite E1; [exact X3| unfold PGSZ in *; rewrite Z.add_mod, AA by lia; reflexivity].
            -- destruct E2 as [E2|E2]; rewrite E2; [exact AA| exact X4].
      - (* [comment removed for export] *) unfold brk_extent in *. cbn [ld_brkreg set_brkph set_brkreg] in *. rewrite Ereg in Kbb. exact Kbb.
      - (* [comment removed for export] *) unfold ceil_ok. rewrite Evm, alloc_top_mkVmMapsFull. pose proof Kceil as Kc'. unfold ceil_ok, alloc_top in Kc'. exact Kc'. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia).
    assert (Hhi64 : a + PGSZ < 2^64) by lia.
    pose proof (na_cov_bound _ _ (kl_wf _ _ _ HK) (kl_na_cov _ _ _ HK)) as NAB. fold h in NAB.
    assert (Ha0 : 0 <= a) by lia.
    destruct x as [e| |e].
    - destruct Hx as [-> ->]. split; [|reflexivity].
      apply (KLnew (vm_maps h) (vm_noaccess h)); auto.
      + exact (kl_wf _ _ _ HK).
      + intros e x y He H1 H2 H3 H4. exists e. auto.
      + exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
      + exact (kl_na_cov _ _ _ HK).
      + intros p Hp. right. exists p. split; [exact Hp| lia].
      + subst h. destruct (m_vmmaps mo); reflexivity.
      + exact (kl_mat _ _ _ HK).
    - split; [|exact I].
      apply (KLnew (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
      + exact (kl_wf _ _ _ HK).
      + intros e x y He H1 H2 H3 H4. (first [ pose proof ((iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4)) as dR_67; dex1 dR_67 as e'; destruct dR_67 as [He' Hr] | pose proof ((iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4)) as dR_67; dand3 dR_67 as e' He' Hr | destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4) as (e' & He' & Hr) ]).
        exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
      + exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
      + intros e [<-|He].
        * exists e0. split; [exact He0|]. unfold elo, ehi in *. cbn [fst snd]. rewrite Ua, Un. unfold PGSZ in *. lia.
        * (first [ pose proof ((maps_subtract_sub _ _ _ _ NAB He)) as dR_68; dex1 dR_68 as e1; dand3 dR_68 as He1 Q1 Q2 | pose proof ((maps_subtract_sub _ _ _ _ NAB He)) as dR_68; dand4 dR_68 as e1 He1 Q1 Q2 | destruct (maps_subtract_sub _ _ _ _ NAB He) as (e1 & He1 & Q1 & Q2) ]).
          (first [ pose proof ((kl_na_cov _ _ _ HK e1 He1)) as dR_69; dex1 dR_69 as e'; dand4 dR_69 as He' R1' R0' R2' | pose proof ((kl_na_cov _ _ _ HK e1 He1)) as dR_69; dand5 dR_69 as e' He' R1' R0' R2' | destruct (kl_na_cov _ _ _ HK e1 He1) as (e' & He' & R1' & R0' & R2') ]). fold h in He'.
          (first [ pose proof ((maps_subtract_In _ _ _ _ He)) as dR_70; dand3 dR_70 as [a1 s1] Ha1 Hp1 | destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & Ha1 & Hp1) ]).
          pose proof (iv_subtract_nonempty a1 s1 a (a + PGSZ) e (NAB _ Ha1)) as NE.
          (first [ pose proof ((kl_na_cov _ _ _ HK _ Ha1)) as dR_71; dex1 dR_71 as e2; dand4 dR_71 as _ T1 T0 T2 | pose proof ((kl_na_cov _ _ _ HK _ Ha1)) as dR_71; dand5 dR_71 as e2 _ T1 T0 T2 | destruct (kl_na_cov _ _ _ HK _ Ha1) as (e2 & _ & T1 & T0 & T2) ]). unfold elo, ehi in T1, T0, T2. cbn in T1, T0, T2.
          exists e'. split; [exact He'|]. specialize (NE ltac:(lia) Ha0 Hhi64 Hp1). lia.
      + intros p [<-|Hp]; [left; unfold elo, ehi; cbn [fst snd]; rewrite Ua, Un; lia| right].
        (first [ pose proof ((maps_subtract_sub _ _ _ _ NAB Hp)) as dR_72; dex1 dR_72 as e1; dand3 dR_72 as He1 Q1 Q2 | pose proof ((maps_subtract_sub _ _ _ _ NAB Hp)) as dR_72; dand4 dR_72 as e1 He1 Q1 Q2 | destruct (maps_subtract_sub _ _ _ _ NAB Hp) as (e1 & He1 & Q1 & Q2) ]). exists e1. auto.
      + exact (nstep_mat _ _ _ _ (kl_mat _ _ _ HK) Hst).
    - destruct Hx as [-> Evm]. split; [|reflexivity].
      apply (KLnew (maps_subtract (vm_maps h) a (a + PGSZ)) (maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
      + apply vmwf_subtract; [exact Hlohi| exact (kl_wf _ _ _ HK)].
      + intros e He Hde. apply maps_subtract_keep; [exact (kl_wf _ _ _ HK)| exact Hlohi| exact He| exact Hde].
      + intros e x y He H1 H2 H3 H4. (first [ pose proof ((iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4)) as dR_73; dex1 dR_73 as e'; destruct dR_73 as [He' Hr] | pose proof ((iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4)) as dR_73; dand3 dR_73 as e' He' Hr | destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4) as (e' & He' & Hr) ]).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      + (first [ pose proof ((iv_subtract_contains (fst e0) (snd e0) a (a + PGSZ) (a + PGSZ) (a + 2 * PGSZ) Hlohi Hhi64 ltac:(unfold elo in He0l; lia) ltac:(unfold PGSZ; lia) ltac:(unfold ehi in He0h; lia) ltac:(right; lia))) as dR_74; dex1 dR_74 as e'; destruct dR_74 as [He' Hr] | pose proof ((iv_subtract_contains (fst e0) (snd e0) a (a + PGSZ) (a + PGSZ) (a + 2 * PGSZ) Hlohi Hhi64 ltac:(unfold elo in He0l; lia) ltac:(unfold PGSZ; lia) ltac:(unfold ehi in He0h; lia) ltac:(right; lia))) as dR_74; dand3 dR_74 as e' He' Hr | destruct (iv_subtract_contains (fst e0) (snd e0) a (a + PGSZ) (a + PGSZ) (a + 2 * PGSZ) Hlohi Hhi64 ltac:(unfold elo in He0l; lia) ltac:(unfold PGSZ; lia) ltac:(unfold ehi in He0h; lia) ltac:(right; lia)) as (e' & He' & Hr) ]).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      + intros e He.
        (first [ pose proof ((maps_subtract_sub _ _ _ _ NAB He)) as dR_75; dex1 dR_75 as e1; dand3 dR_75 as He1 Q1 Q2 | pose proof ((maps_subtract_sub _ _ _ _ NAB He)) as dR_75; dand4 dR_75 as e1 He1 Q1 Q2 | destruct (maps_subtract_sub _ _ _ _ NAB He) as (e1 & He1 & Q1 & Q2) ]).
        (first [ pose proof ((maps_subtract_In _ _ _ _ He)) as dR_76; dand3 dR_76 as [a1 s1] Ha1 Hp1 | destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & Ha1 & Hp1) ]).
        (first [ pose proof ((kl_na_cov _ _ _ HK _ Ha1)) as dR_77; dex1 dR_77 as e2; dand4 dR_77 as He2 T1 T0 T2 | pose proof ((kl_na_cov _ _ _ HK _ Ha1)) as dR_77; dand5 dR_77 as e2 He2 T1 T0 T2 | destruct (kl_na_cov _ _ _ HK _ Ha1) as (e2 & He2 & T1 & T0 & T2) ]). fold h in He2.
        pose proof (iv_subtract_nonempty a1 s1 a (a + PGSZ) e (NAB _ Ha1) ltac:(unfold elo, ehi in T0; cbn in T0; lia) Ha0 Hhi64 Hp1) as NE.
        pose proof (iv_subtract_avoid a1 s1 a (a + PGSZ) e (NAB _ Ha1) Ha0 Hlohi Hhi64 Hp1) as AV.
        pose proof (iv_subtract_sub' a1 s1 a (a + PGSZ) e (NAB _ Ha1) Hp1) as [SB1 SB2]. unfold elo, ehi in T1, T2. cbn in T1, T2.
        (first [ pose proof ((iv_subtract_contains (fst e2) (snd e2) a (a + PGSZ) (elo e) (ehi e) Hlohi Hhi64 ltac:(unfold elo in *; lia) NE ltac:(unfold ehi in *; lia) AV)) as dR_78; dex1 dR_78 as e'; destruct dR_78 as [He' Hr] | pose proof ((iv_subtract_contains (fst e2) (snd e2) a (a + PGSZ) (elo e) (ehi e) Hlohi Hhi64 ltac:(unfold elo in *; lia) NE ltac:(unfold ehi in *; lia) AV)) as dR_78; dand3 dR_78 as e' He' Hr | destruct (iv_subtract_contains (fst e2) (snd e2) a (a + PGSZ) (elo e) (ehi e) Hlohi Hhi64 ltac:(unfold elo in *; lia) NE ltac:(unfold ehi in *; lia) AV) as (e' & He' & Hr) ]).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| lia].
      + intros p Hp. right. (first [ pose proof ((maps_subtract_sub _ _ _ _ NAB Hp)) as dR_79; dex1 dR_79 as e1; dand3 dR_79 as He1 Q1 Q2 | pose proof ((maps_subtract_sub _ _ _ _ NAB Hp)) as dR_79; dand4 dR_79 as e1 He1 Q1 Q2 | destruct (maps_subtract_sub _ _ _ _ NAB Hp) as (e1 & He1 & Q1 & Q2) ]). exists e1. auto.
      + exact (nstep_mat _ _ _ _ (kl_mat _ _ _ HK) Hst). }
  intros x. cbn beta. apply mspec_ret. (intros s mo; (first [ intro dR_123; dand4 dR_123 as -> HGs HK Hx | intros (-> & HGs & HK & Hx) ])). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota. fold L'.
  splits; auto. unfold mmap_fixed_answer_ok. destruct x as [e| |e]; try subst e.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
  - rewrite Z.eqb_refl. apply orb_true_r.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma g_remove_split : forall a l0 (l : list (Z * Z)) (M : list Z), In (a, l0) l -> List.NoDup (map fst l ++ M) ->
  exists l1 l2, l = l1 ++ (a, l0) :: l2 /\ g_remove a l = l1 ++ l2.
Proof.
  intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; exists [], l; split; reflexivity|].
    exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. (first [ pose proof ((IH Hin Hnd')) as dR_80; dex2 dR_80 as l1 l2; destruct dR_80 as [-> E] | pose proof ((IH Hin Hnd')) as dR_80; dand4 dR_80 as l1 l2 -> E | destruct (IH Hin Hnd') as (l1 & l2 & -> & E) ]).
    exists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

Lemma phase_quiet : forall L L' pbrk mo mo',
  KL L pbrk mo -> brk_quiet L -> ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
  vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) -> vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo) ->
  phase_inv (ld_brk L') L' pbrk mo'.
Proof.
  intros L L' pbrk mo mo' HK Hq E1 E2 E3 E4. pose proof (kl_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv.
  rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

Lemma ev_munmap_ok : forall L G s0 a l0 len, gframe G -> brk_quiet L -> In (a, l0) (ld_groups L) ->
  (len = l0 \/ len = round_up_pg l0) ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMunmap a len))
        (ev_step_post L (EMunmap a len) G s0).
Proof.
  intros L G s0 a l0 len HG Hq Hin Hlen. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  set (L' := set_groups (g_remove a (ld_groups L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMunmap a len) (dec_munmap a len) _
             (fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with RgErr e => e = EINVAL | RgDone _ => True end)).
    (intros s mo; (first [ intro dR_124; dand3 dR_124 as -> HK HGs | intros (-> & HK & HGs) ])).
    (first [ pose proof ((kl_groups _ _ _ HK a l0 Hin)) as dR_81; dand6 dR_81 as A1 A2 A3 A4 A5 A6 | pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6) ]).
    (first [ pose proof ((went_In_bounds _ _ _ a l0 HK (or_introl Hin))) as dR_82; dand6 dR_82 as _ B2 _ _ B5 B6 | pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6) ]).
    set (n := mmap_len l0) in *. set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
    assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
    assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
    { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
    destruct Hlen3 as [Hlen1 Hlen2].
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + n).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus. lia. }
    assert (Hhas : map_has (vm_maps h) aw nw = true).
    { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    assert (Ewl : wlen len = nw) by (unfold wlen; rewrite rlen_eq by lia; rewrite Hlen2; reflexivity).
    split.
    { cbn [nsafe]. unfold w. fold h aw. rewrite Ua, page_size_eq, (rlen_eq len), Hlen2, Ewl by lia. unfold PGSZ in A3.
      split; [exact A3|]. split; [apply (w_len_ne0 len); lia|]. split; [pose proof alloc_ceiling_val as CV; unfold TASK_SIZE; clear -CV A4; lia| exact Hhas]. }   (* [comment removed for export] *)
    intros rsp mo' Hst.
    pose proof (minv_preserved _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
    (first [ pose proof ((nstep_dec_munmap a len mo rsp mo' ltac:(lia) ltac:(lia) Hst)) as dR_83; dand3 dR_83 as Hvo Hd Hx | pose proof (nstep_dec_munmap a len mo rsp mo' ltac:(lia) ltac:(lia) Hst) as (Hvo & Hd & Hx) ]).
    rewrite Hlen2 in Hx. fold h aw nw in Hx. rewrite Ua, Un in Hx.
    exists (RgDone true). split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    (* [comment removed for export] *)
    pose proof (kl_distinct _ _ _ HK) as Kd.
    (first [ pose proof ((g_remove_split a l0 (ld_groups L) _ Hin Kd)) as dR_84; dex2 dR_84 as g1 g2; destruct dR_84 as [Eg Ezz] | pose proof ((g_remove_split a l0 (ld_groups L) _ Hin Kd)) as dR_84; dand4 dR_84 as g1 g2 Eg Ezz | destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz) ]).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    (* [comment removed for export] *)
    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. (first [ pose proof ((went_In_bounds _ _ _ b l HK H)) as dR_85; dand6 dR_85 as C1 C2 C3 C4 C5 C6 | pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6) ]).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> fst e <> aw -> In e maps') ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + n <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (forall e, In e maps' -> In e (vm_maps h) /\ fst e <> aw) ->
              (forall e, In e noacc' -> exists e', In e' maps' /\ elo e' <= elo e /\ elo e < ehi e /\ ehi e <= ehi e') ->
              (forall p, In p noacc' -> exists e, In e (vm_noaccess h) /\ elo e <= elo p /\ ehi p <= ehi e) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              m_vm_materialized mo' = [] ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hna Hmsub' Hnacov Hnasub Evm Hmat'.
      assert (Hmsub : forall e, In e maps' -> In e (vm_maps h)) by (intros e He; exact (proj1 (Hmsub' e He))).
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
      { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
      subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). (first [ dand6 Kgr as [G0 G1] G2 G3 G4 G5 G6 | destruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6) ]). splits; try assumption.
        apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
      - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). (first [ dand9 Kme as [G0 G1] G2 G3 G4 G5 G6 G7 G8 G9 | destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9) ]). splits; try assumption.
        + apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
        + intros q Hq1 Hq2. (first [ pose proof ((G9 q Hq1 Hq2)) as dR_88; dex1 dR_88 as e; dand3 dR_88 as He Hel Heh | pose proof ((G9 q Hq1 Hq2)) as dR_88; dand4 dR_88 as e He Hel Heh | destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh) ]).
          pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kreg b0 l1 E). (first [ dand6 Kreg as R1 R2 R3 R4 R5 Rcov | destruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov) ]). splits; auto.
        intros z Hz. (first [ pose proof ((Rcov z Hz)) as dR_90; dex1 dR_90 as e; destruct dR_90 as [He Hr] | pose proof ((Rcov z Hz)) as dR_90; dand3 dR_90 as e He Hr | destruct (Rcov z Hz) as (e & He & Hr) ]). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
        intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
        destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
        + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
        + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. lia.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 _]. eapply region_free_mono_sub; [exact (Kgna b0 l1 Hin1)| exact Hnasub].
      - (* [comment removed for export] *)
        intros e He. destruct (Hmsub' e He) as [Hem Hne]. destruct (Kcpl e Hem) as [(b0 & l1 & Hin0 & E0)|[X|X]]; [| right; left; exact X| right; right; exact X].
        left. exists b0, l1. split; [| exact E0]. rewrite Eg in Hin0. rewrite Ezz. apply in_app_iff in Hin0. apply in_app_iff.
        destruct Hin0 as [Hin0|[Hin0|Hin0]]; [left; exact Hin0| | right; exact Hin0].
        exfalso. injection Hin0 as <- <-. apply Hne. rewrite E0. reflexivity.
      - (* [comment removed for export] *) unfold ceil_ok. rewrite Evm, alloc_top_mkVmMapsFull. pose proof Kceil as Kc'. unfold ceil_ok, alloc_top in Kc'. exact Kc'. }
    assert (Hlohi : a < a + n) by lia. assert (Hhi64 : a + n < 2^64) by lia. assert (Ha0 : 0 <= a) by lia.
    pose proof (na_cov_bound _ _ (kl_wf _ _ _ HK) (kl_na_cov _ _ _ HK)) as NAB. fold h in NAB.
    split; [|exact I]. apply (KLnew (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) a (a + n))).
    + apply vmwf_remove. exact (kl_wf _ _ _ HK).
    + intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
    + intros e x y He H1 H2 H3 H4. (first [ pose proof ((iv_subtract_contains (fst e) (snd e) a (a + n) x y Hlohi Hhi64 H1 H2 H3 H4)) as dR_91; dex1 dR_91 as e'; destruct dR_91 as [He' Hr] | pose proof ((iv_subtract_contains (fst e) (snd e) a (a + n) x y Hlohi Hhi64 H1 H2 H3 H4)) as dR_91; dand3 dR_91 as e' He' Hr | destruct (iv_subtract_contains (fst e) (snd e) a (a + n) x y Hlohi Hhi64 H1 H2 H3 H4) as (e' & He' & Hr) ]).
      exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
    + intros e He. unfold map_remove in He. apply filter_In in He as [He Hb]. split; [exact He|].
      intros E. rewrite E, bv_eqb_refl in Hb. discriminate.
    + intros e He.
      (first [ pose proof ((maps_subtract_In _ _ _ _ He)) as dR_92; dand3 dR_92 as [a1 s1] Ha1 Hp1 | destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & Ha1 & Hp1) ]).
      (first [ pose proof ((kl_na_cov _ _ _ HK _ Ha1)) as dR_93; dex1 dR_93 as e2; dand4 dR_93 as He2 T1 T0 T2 | pose proof ((kl_na_cov _ _ _ HK _ Ha1)) as dR_93; dand5 dR_93 as e2 He2 T1 T0 T2 | destruct (kl_na_cov _ _ _ HK _ Ha1) as (e2 & He2 & T1 & T0 & T2) ]). fold h in He2. unfold elo, ehi in T1, T0, T2. cbn in T1, T0, T2.
      pose proof (iv_subtract_nonempty a1 s1 a (a + n) e (NAB _ Ha1) ltac:(lia) Ha0 Hhi64 Hp1) as NE.
      pose proof (iv_subtract_avoid a1 s1 a (a + n) e (NAB _ Ha1) Ha0 Hlohi Hhi64 Hp1) as AV.
      pose proof (iv_subtract_sub' a1 s1 a (a + n) e (NAB _ Ha1) Hp1) as [SB1 SB2].
      (* [comment removed for export] *)
      assert (Hne2 : fst e2 <> aw).
      { intros E. destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) He2 A5) as [E2|D].
        - subst e2. pose proof B5 as B5'. pose proof B6 as B6'. unfold elo, ehi in B5', B6'. rewrite B5' in T1. rewrite B6' in T2.
          unfold elo, ehi in NE, AV, SB1, SB2. lia.
        - unfold edisj in D. rewrite B5, B6 in D. pose proof (proj1 (kl_wf _ _ _ HK) e2 He2) as W2.
          unfold elo, ehi in D, W2. rewrite E in D. rewrite Ua in D. unfold elo, ehi in NE, AV, SB1, SB2. lia. }
      exists e2. split; [| unfold elo, ehi in *; lia]. unfold map_remove. apply filter_In. split; [exact He2|].
      destruct (bv_eqb (fst e2) aw) eqn:E; [apply bv_eqb_eq in E; contradiction| reflexivity].
    + intros p Hp. (first [ pose proof ((maps_subtract_sub _ _ _ _ NAB Hp)) as dR_94; dex1 dR_94 as e1; dand3 dR_94 as He1 Q1 Q2 | pose proof ((maps_subtract_sub _ _ _ _ NAB Hp)) as dR_94; dand4 dR_94 as e1 He1 Q1 Q2 | destruct (maps_subtract_sub _ _ _ _ NAB Hp) as (e1 & He1 & Q1 & Q2) ]). exists e1. auto.
    + exact Hx.
    + exact (nstep_mat _ _ _ _ (kl_mat _ _ _ HK) Hst). }
  intros x. cbn beta. apply mspec_ret. (intros s mo; (first [ intro dR_125; dand4 dR_125 as -> HGs HK Hx | intros (-> & HGs & HK & Hx) ])). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'.
  splits; auto. unfold munmap_answer_ok. destruct x as [e|b]; try subst e.
  - rewrite is_errno_form_neg by (unfold EINVAL; lia). apply orb_true_r.
  - reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma map_base_bump : forall a ms, map (fun m : Z * Z * Z => fst (fst m)) (map (bump_meta a) ms) = map (fun m => fst (fst m)) ms.
Proof.
  intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma nstep_dec_mprotect : forall addr len mo rsp mo',
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  0 <= addr < 2^64 -> 0 < len < 2^64 -> addr + mmap_len len <= alloc_ceiling ->
  nstep (NMprotect addr len PROT_RW) mo rsp mo' ->
  vm_only mo mo' /\
  exists x, dec_mprotect addr len rsp = Some x /\
  match x with
  | RgErr e => e = ENOMEM /\ mo' = mo
  | RgDone true => m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                     (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                     (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  | RgDone false => False
  end.
Proof.
  intros addr len mo rsp mo' h a n Ha Hlen Hce H. pose proof (nstep_mm_vm_only _ _ _ _ H) as Hv. split; [exact Hv|].
  pose proof alloc_ceiling_lt as Hcl. pose proof (mmap_len_ge len ltac:(lia)) as Hml.
  cbn -[mprotect_model w wlen rlen Z.eqb mprotect_budget_ok] in H.
  assert (Ewl : wlen len = n) by (unfold wlen; rewrite rlen_eq by lia; reflexivity). rewrite Ewl in H.
  change (w addr) with a in H.
  destruct H as [(e & He & -> & ->)|(Hb & -> & ->)].
  - apply mprotect_errnos_when_sub in He. cbn in He. destruct He as [<-|[]]. exists (RgErr ENOMEM). split; [|split; reflexivity].
    cbn -[errno_of errno_ret Z.eqb]. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
  - exists (RgDone true). split.
    + cbn -[errno_of Z.eqb bv_eqb mmap_len w]. unfold w. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      rewrite Z.eqb_refl. fold a n. rewrite !bv_eqb_refl. reflexivity.
    + unfold mprotect_model. rewrite with_vmmaps_vm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_mprotect_nf : forall addr len mo rsp mo',
  let h := m_vmmaps mo in
  let a := Z_to_bv 64 addr in let n := Z_to_bv 64 (mmap_len len) in
  0 <= addr < 2^64 -> 0 < len < 2^64 -> addr + mmap_len len <= alloc_ceiling ->
  nrefusable (NMprotect addr len PROT_RW) mo = false ->
  nstep (NMprotect addr len PROT_RW) mo rsp mo' ->
  vm_only mo mo' /\ dec_mprotect addr len rsp = Some (RgDone true) /\
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h)
                     (maps_subtract (vm_noaccess h) (bv_unsigned a) (bv_unsigned a + bv_unsigned n))
                     (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h).
Proof.
  intros addr len mo rsp mo' h a n Ha Hlen Hce NR H. pose proof (nstep_mm_vm_only _ _ _ _ H) as Hv. split; [exact Hv|].
  pose proof alloc_ceiling_lt as Hcl. pose proof (mmap_len_ge len ltac:(lia)) as Hml.
  apply (proj1 (nstep_nf_iff _ mo rsp mo' NR)) in H.
  cbn -[mprotect_model w wlen rlen Z.eqb mprotect_budget_ok] in H.
  assert (Ewl : wlen len = n) by (unfold wlen; rewrite rlen_eq by lia; reflexivity). rewrite Ewl in H.
  change (w addr) with a in H.
  destruct H as (Hb & -> & ->). split.
  - cbn -[errno_of Z.eqb bv_eqb mmap_len w]. unfold w. change (bv_unsigned (Z_to_bv 64 0)) with 0.
    rewrite Z.eqb_refl. fold a n. rewrite !bv_eqb_refl. reflexivity.
  - unfold mprotect_model. rewrite with_vmmaps_vm. reflexivity.
Qed.

Lemma ev_mprotect_ok : forall L G s0 b l k, gframe G -> brk_quiet L -> In (b, l, k) (ld_metas L) ->
  (2 + k) * PGSZ <= round_up_pg l ->
  let a := b + (1 + k) * PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (ev_step (EMprotect a PGSZ PROT_RW))
        (ev_step_post L (EMprotect a PGSZ PROT_RW) G s0).
Proof.
  intros L G s0 b l k HG Hq Hin Hk2 a. pose proof alloc_ceiling_lt as Hcl. unfold ev_step.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ match x with RgErr e => (e = EINVAL \/ e = ENOMEM) /\ KL L (ps_brk s0) mo | RgDone _ => KL L' (ps_brk s0) mo end)).
    (intros s mo; (first [ intro dR_126; dand3 dR_126 as -> HK HGs | intros (-> & HK & HGs) ])).
    (first [ pose proof ((kl_metas _ _ _ HK b l k Hin)) as dR_95; dand9 dR_95 as A1 A2 A3 A4 Ak Ak1 A5 A6 Ana | pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana) ]).
    (first [ pose proof ((went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin)))) as dR_96; dand6 dR_96 as _ B2 _ _ B5 B6 | pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6) ]).
    set (nb := mmap_len l) in *. set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + PGSZ).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus, PGSZ in *. lia. }
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
    { (first [ pose proof ((Ana (1 + k) ltac:(lia) ltac:(lia))) as dR_97; dex1 dR_97 as e; dand3 dR_97 as He Hel Heh | pose proof ((Ana (1 + k) ltac:(lia) ltac:(lia))) as dR_97; dand4 dR_97 as e He Hel Heh | destruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh) ]). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    split.
    { cbn [nsafe]. unfold w. fold h aw nw. rewrite wlen_PGSZ, rlen_PGSZ. fold nw. rewrite Ua, Un, page_size_eq.
      split; [reflexivity|]. split; [exact Hamod|]. split; [unfold PGSZ; lia|]. split; [unfold two_pow_64, PGSZ in *; lia|].
      split; [exact Hcn| exact Hcm]. }
    intros rsp mo' Hst.
    pose proof (minv_preserved _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hst) as [Hh' Hmi'].
    assert (HaC : a + mmap_len PGSZ <= alloc_ceiling) by (change (mmap_len PGSZ) with PGSZ; lia).   (* [comment removed for export] *)
    (first [ pose proof ((nstep_dec_mprotect a PGSZ mo rsp mo' ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) HaC Hst)) as dR_98; dand4 dR_98 as Hvo x Hd Hx | pose proof (nstep_dec_mprotect a PGSZ mo rsp mo' ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) HaC Hst) as (Hvo & x & Hd & Hx) ]).
    change (mmap_len PGSZ) with PGSZ in Hx. fold h aw nw in Hx. rewrite Ua, Un in Hx.
    assert (HdRW : dec_mprotect_rw a PGSZ rsp = Some x).
    { destruct x as [e|[|]].
      - destruct Hx as [-> _]. unfold dec_mprotect_rw. rewrite Hd. reflexivity.
      - unfold dec_mprotect_rw. rewrite Hd. reflexivity.
      - destruct Hx. }
    exists x. split; [exact HdRW|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    pose proof (kl_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    (* [comment removed for export] *)
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. (first [ pose proof ((went_In_bounds _ _ _ b0 l0 HK H)) as dR_99; dand6 dR_99 as C1 C2 C3 C4 C5 C6 | pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6) ]).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (KLnew : forall noacc',
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (forall e, In e noacc' -> exists e', In e' (vm_maps h) /\ elo e' <= elo e /\ elo e < ehi e /\ ehi e <= ehi e') ->
              (forall p, In p noacc' -> exists e, In e (vm_noaccess h) /\ elo e <= elo p /\ ehi p <= ehi e) ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              m_vm_materialized mo' = [] ->
              KL L' (ps_brk s0) mo').
    { intros noacc' Hna Hnacov Hnasub Evm Hmat'.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live]; auto.
      - intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
        specialize (Kme b1 l1 k0 Hin1). (first [ dand9 Kme as [G0 G1] G2 G3 G4 G5 G6 G7 G8 G9 | destruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9) ]).
        unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
        + (* [comment removed for export] *)
          assert (Eb0 : b0 = b).
          { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
            pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
          subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
          splits; try assumption; try lia.
          intros q Hq1 Hq2. (first [ pose proof ((G9 q ltac:(lia) Hq2)) as dR_101; dex1 dR_101 as e; dand3 dR_101 as He Hel Heh | pose proof ((G9 q ltac:(lia) Hq2)) as dR_101; dand4 dR_101 as e He Hel Heh | destruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh) ]).
          apply (Hna e (b + q * PGSZ) (b + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). right. subst a. clear -Hq1. unfold PGSZ in *. nia.
        + splits; try assumption.
          intros q Hq1 Hq2. (first [ pose proof ((G9 q Hq1 Hq2)) as dR_102; dex1 dR_102 as e; dand3 dR_102 as He Hel Heh | pose proof ((G9 q Hq1 Hq2)) as dR_102; dand4 dR_102 as e He Hel Heh | destruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh) ]).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh).
          destruct (Z.eq_dec b0 b) as [->|Hne].
          { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite map_base_bump. exact Kd.
      - intros b0 l0 Hin0. eapply region_free_mono_sub; [exact (Kgna b0 l0 Hin0)| exact Hnasub].
      - intros e He. destruct (Kcpl e He) as [X|[(b0 & l0 & k0 & Hin0 & E0)|X]]; [left; exact X| right; left| right; right; exact X].
        exists b0, l0, (if b0 + (1 + k0) * PGSZ =? a then k0 + 1 else k0). split; [| exact E0].
        apply in_map_iff. exists (b0, l0, k0). split; [| exact Hin0]. unfold bump_meta. destruct (_ =? _); reflexivity.
      - (* [comment removed for export] *) unfold ceil_ok. rewrite Evm, alloc_top_mkVmMapsFull. pose proof Kceil as Kc'. unfold ceil_ok, alloc_top in Kc'. exact Kc'. }
    pose proof (na_cov_bound _ _ (kl_wf _ _ _ HK) (kl_na_cov _ _ _ HK)) as NAB. fold h in NAB.
    assert (Ha0 : 0 <= a) by lia.
    destruct x as [e|[|]].
    - destruct Hx as [-> ->]. split; [right; reflexivity| exact HK].
    - assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia). assert (Hhi64 : a + PGSZ < 2^64) by lia.
      apply (KLnew (maps_subtract (vm_noaccess h) a (a + PGSZ))); [| | |exact Hx|].
      + intros e x y He H1 H2 H3 H4. (first [ pose proof ((iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4)) as dR_103; dex1 dR_103 as e'; destruct dR_103 as [He' Hr] | pose proof ((iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4)) as dR_103; dand3 dR_103 as e' He' Hr | destruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi64 H1 H2 H3 H4) as (e' & He' & Hr) ]).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      + intros e He.
        (first [ pose proof ((maps_subtract_In _ _ _ _ He)) as dR_104; dand3 dR_104 as [a1 s1] Ha1 Hp1 | destruct (maps_subtract_In _ _ _ _ He) as ([a1 s1] & Ha1 & Hp1) ]).
        (first [ pose proof ((kl_na_cov _ _ _ HK _ Ha1)) as dR_105; dex1 dR_105 as e2; dand4 dR_105 as He2 T1 T0 T2 | pose proof ((kl_na_cov _ _ _ HK _ Ha1)) as dR_105; dand5 dR_105 as e2 He2 T1 T0 T2 | destruct (kl_na_cov _ _ _ HK _ Ha1) as (e2 & He2 & T1 & T0 & T2) ]). fold h in He2. unfold elo, ehi in T1, T0, T2. cbn in T1, T0, T2.
        pose proof (iv_subtract_nonempty a1 s1 a (a + PGSZ) e (NAB _ Ha1) ltac:(lia) Ha0 Hhi64 Hp1) as NE.
        pose proof (iv_subtract_sub' a1 s1 a (a + PGSZ) e (NAB _ Ha1) Hp1) as [SB1 SB2].
        exists e2. split; [exact He2|]. unfold elo, ehi in *. lia.
      + intros p Hp. (first [ pose proof ((maps_subtract_sub _ _ _ _ NAB Hp)) as dR_106; dex1 dR_106 as e1; dand3 dR_106 as He1 Q1 Q2 | pose proof ((maps_subtract_sub _ _ _ _ NAB Hp)) as dR_106; dand4 dR_106 as e1 He1 Q1 Q2 | destruct (maps_subtract_sub _ _ _ _ NAB Hp) as (e1 & He1 & Q1 & Q2) ]). exists e1. auto.
      + exact (nstep_mat _ _ _ _ (kl_mat _ _ _ HK) Hst).
    - destruct Hx. }
  intros x. cbn beta. apply mspec_ret. (intros s mo; (first [ intro dR_127; dand3 dR_127 as -> HGs Hx | intros (-> & HGs & Hx) ])). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'. unfold mprotect_answer_ok.
  destruct x as [e|bb].
  - destruct Hx as [He HK]. rewrite is_errno_form_neg by (destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    replace (neg_errno e =? 0) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno; destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    replace (neg_errno e =? TWO64 - ENOSYS) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno, TWO64, ENOSYS; destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    cbn [orb]. splits; auto.
  - cbn [Z.eqb orb]. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma round_up_pg_ge : forall x, x <= round_up_pg x.
Proof. intros x. unfold round_up_pg. pose proof (Z.land_nonneg (-x) (PGSZ - 1)). unfold PGSZ in *. lia. Qed.

Lemma ev_step_spec : forall L e (G : PState -> Model -> Prop) s0,
  gframe G -> event_pre L e ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (ev_step e) (ev_step_post L e G s0).
Proof.
  intros L e G s0 HG Hpre. destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
    + unfold ev_step. cbn [Z.eqb]. apply ev_brk0_ok; assumption.
    + destruct (Z.eqb_spec (round_up_pg cur + 2 * PGSZ) 0) as [E|NE].
      * (intros s mo; (first [ intro dR_128; dand3 dR_128 as -> HK _ | intros (-> & HK & _) ])). exfalso. pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & _).
        pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow1_ok; assumption.
    + destruct (Z.eqb_spec (b + l + PGSZ) 0) as [E|NE].
      * (intros s mo; (first [ intro dR_129; dand3 dR_129 as -> HK _ | intros (-> & HK & _) ])). exfalso. (first [ pose proof ((kl_brkreg _ _ _ HK b l Hreg)) as dR_107; dand4 dR_107 as R1 R2 R3 _ | pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _) ]). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow2_ok; assumption.
  - destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + apply ev_mmap_ok; assumption.
    + apply ev_mmap_fixed_ok; assumption.
  - (first [ dand4 Hpre as Hq l0 Hin Hlen | destruct Hpre as (Hq & l0 & Hin & Hlen) ]). apply (ev_munmap_ok L G s0 addr l0 len); assumption.
  - (first [ dand9 Hpre as Hq -> -> b l k Hin -> Hk | destruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk) ]). apply (ev_mprotect_ok L G s0 b l k); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma membed_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  gframe G -> ctree_ok L t Post ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  intros t. induction t as [r|e k IH]; intros Post G L s0 HG Hok.
  - cbn [membed]. apply mspec_ret. (intros s mo; (first [ intro dR_130; dand3 dR_130 as -> HK HGs | intros (-> & HK & HGs) ])). exists L.
    split; [constructor|]. cbn in Hok. splits; auto.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk].
    eapply mspec_bind; [apply (ev_step_spec L e G s0 HG Hpre)|].
    intros z. unfold ev_step_post. apply mspec_pointwise. (intros s1 mo1; (first [ intro dR_131; dand6 dR_131 as Hans HK1 HG1 Hm Hfa Hso | intros (Hans & HK1 & HG1 & Hm & Hfa & Hso) ])).
    eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + (intros r s mo; (first [ intro dR_132; dand8 dR_132 as L' Hp HP HK HG' Hm' Hfa' Hso' | intros (L' & Hp & HP & HK & HG' & Hm' & Hfa' & Hso') ])). exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition OWN (X : list bptr) (G : PState -> Model -> Prop) : assn PState := fun s mo =>
  (exists L, MI_Ccma.SIMREL (ps_m s) L /\ KL L (ps_brk s) mo /\ incl (map fst X) (ld_live L))
  /\ List.NoDup (map fst X) /\ G s mo.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma KL_set_live : forall L v pbrk mo, KL L pbrk mo -> KL (set_live v L) pbrk mo.
Proof. intros L v pbrk mo K. destruct K; constructor; cbn; auto. Qed.

Lemma event_post_live : forall L e z, ld_live (event_post L e z) = ld_live L.
Proof.
  intros L e z. destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

Lemma cpath_live {R} : forall L (t : stree ev Z R) L' r, cpath L t L' r -> ld_live L' = ld_live L.
Proof. intros L t L' r H. induction H; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

Lemma aptr_eqb_eq : forall a b, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma in_ap_remove : forall x c l, In x l -> x <> c -> In x (ap_remove c l).
Proof.
  intros x c l. induction l as [|y l IH]; intros Hin Hne; [destruct Hin|].
  cbn. destruct (aptr_eqb y c) eqn:E.
  - apply aptr_eqb_eq in E. subst y. destruct Hin as [->|Hin]; [congruence| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

End CEIL.
