(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac Image ZBridge SysStep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Nodes Decode Arr SFMisc.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Image OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SysStep OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Decode OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Arr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.SFMisc.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.MA Require Import F_syscalls MallocRep.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem := word -> option byte.

Definition pans_mem (o : mem) (q : aptr) (caddr hint : Z) : Z :=
  match mrd asegs o (wa caddr) with Some b => bv_unsigned b | None => 0 end.
Definition pupd_mem (o : mem) (e : ev) (z : Z) : mem := o.

Lemma pans_mem_range : forall o q c h, 0 <= pans_mem o q c h < 256.
Proof.
  intros. unfold pans_mem. destruct (mrd asegs o (wa c)) as [b|]; [|lia].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Definition mrun {R} (o : mem) (t : Malloc.M R) : Malloc.M (mem * R) := prun pans_mem pupd_mem o t.

Lemma mrun_ret {R} o (r : R) : mrun o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.
Lemma mrun_peek {R} o p c h (k : Z -> Malloc.M R) : mrun o (SVis (EPeek p c h) k) = mrun o (k (pans_mem o p c h)).
Proof. reflexivity. Qed.
Lemma mrun_vis {R} o e (k : Z -> Malloc.M R) :
  match e with EPeek _ _ _ => False | _ => True end ->
  mrun o (SVis e k) = SVis e (fun z => mrun o (k z)).
Proof. intros He. destruct e; try reflexivity. destruct He. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)


Definition implT {R} (o : mem) (t : Malloc.M R) (s : PState)
           (Q : R -> PState -> machine_state -> Prop) (ms : machine_state) : Prop :=
  implM asegs (membed (mrun o t)) s (fun r s' ms' => Q (snd r) s' ms') ms.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS1.

(* [comment removed for export] *)
Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition mmap_val (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.
Definition fixed_val (addr : Z) (a : fixed_ans) : Z :=
  match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.
Definition range_val (a : range_ans) : Z := match a with RgErr e => neg_errno e | RgDone _ => 0 end.

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition leaf_of {R} (o : mem) (t : Malloc.M R) (r : R) : Prop :=
  exists ans o', follow (mrun o t) ans = Some (o', r).

Lemma leaf_of_ret {R} o (r : R) : leaf_of o (SRet r) r.
Proof. exists [], o. reflexivity. Qed.

Lemma leaf_of_vis {R} o e (k : Z -> Malloc.M R) z r :
  match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
  leaf_of o (k z) r -> leaf_of o (SVis e k) r.
Proof.
  (intros He; cps_intros (ans & o' & H)). exists (z :: ans), o'. unfold mrun, prun. cbn [eruns].
  destruct e; cbn [psel]; try exact H; destruct He.
Qed.

Lemma leaf_of_peek {R} o p c h (k : Z -> Malloc.M R) r :
  leaf_of o (k (pans_mem o p c h)) r -> leaf_of o (SVis (EPeek p c h) k) r.
Proof. cps_intros (ans & o' & H). exists ans, o'. rewrite mrun_peek. exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition AUXV_CELL : Z := LIBC + 8.

Definition auxv_list (x3 x4 x5 x6 x11 x12 x23 rnd : Z) : list word :=
  map wz [3; x3; 4; x4; 5; x5; 6; x6; 11; x11; 12; x12; 23; x23; 25; rnd; 0; 0].

Definition auxv_ok (m : mem) (B : Z) : Prop :=
  exists av x3 x4 x5 x6 x11 x12 x23 rnd,
    rw_cells asegs m AUXV_CELL [C8 (wz av)]
    /\ bytes_at asegs m av (u64s (auxv_list x3 x4 x5 x6 x11 x12 x23 rnd))
    /\ bytes_at asegs m (rnd + 8) (zeros 8)
    /\ alloc_ceiling <= B /\ B <= av /\ av + 144 <= 2^64 /\ B <= rnd + 8 /\ rnd + 16 <= 2^64
    /\ 0 <= x3 < 2^64 /\ 0 <= x4 < 2^64 /\ 0 <= x5 < 2^64 /\ 0 <= x6 < 2^64
    /\ 0 <= x11 < 2^64 /\ 0 <= x12 < 2^64 /\ 0 <= x23 < 2^64 /\ 0 <= rnd < 2^64.

(* [comment removed for export] *)

Lemma Forall_disjoint_from : forall (P : Z * Z -> Prop) W a n,
  Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
  intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pres_except (C : Z -> Prop) (m m' : mem) : Prop :=
  forall a, 0 <= a < 2^64 -> ~ C a ->
    m' (wa a) = m (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition alloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ errno_addr (Z_to_bv 64 0x1a620) <= a < errno_addr (Z_to_bv 64 0x1a620) + 4
  \/ CTX <= a < CTX + 928
  \/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition brk_link_ps (st : mstate) (s : PState) : Prop :=
  match c_brk (ctx st) with
  | BrkLive rid off => ps_brk s = conc st (rid, off)
  | _ => True
  end.

(* [comment removed for export] *)
Definition optr_in (P : N -> Prop) (p : optr) : Prop :=
  match p with Some q => P (fst q) | None => True end.

Definition ptrs_in (P : N -> Prop) (st : mstate) : Prop :=
  let c := ctx st in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive rid _ => P rid | _ => True end
  /\ (forall g, optr_in P (m_prev (get_meta_rec st g)) /\ optr_in P (m_next (get_meta_rec st g))
             /\ optr_in P (m_mem (get_meta_rec st g)))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> P (fst b) /\ optr_in P (g_meta gh)).

Lemma ptrs_in_mono (P P' : N -> Prop) st : (forall r, P r -> P' r) -> ptrs_in P st -> ptrs_in P' st.
Proof.
  (intros HP; cps_intros (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10)).
  assert (OM : forall p, optr_in P p -> optr_in P' p) by (intros [q|]; cbn; auto).
  split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
  split; [intros sc; apply OM, H6|]. split; [destruct (c_brk (ctx st)); auto|].
  split; [intros g; cps_destruct (H8 g) as (X1 & X2 & X3); auto|].
  split; [intros a ar Ha; destruct (H9 a ar Ha); auto|].
  intros b gh Hb; destruct (H10 b gh Hb); auto.
Qed.

(* [comment removed for export] *)
Record am_rel (st st1 : mstate) (mo : optr) : Prop := mkAMR {
  amr_active : forall sc, active st1 sc = active st sc;
  amr_usage : forall sc, usage st1 sc = usage st sc;
  amr_bounces : forall i, bounces st1 i = bounces st i;
  amr_unmap_seq : forall i, unmap_seq st1 i = unmap_seq st i;
  amr_seq : c_seq (ctx st1) = c_seq (ctx st);
  amr_counter : c_mmap_counter (ctx st1) = c_mmap_counter (ctx st);
  amr_groups : s_groups st1 = s_groups st;
  amr_slots : s_slots st1 = s_slots st;
  amr_shadow : s_shadow st1 = s_shadow st;
  amr_tick : s_tick st1 = s_tick st;
  amr_reserved : s_reserved st1 = s_reserved st;
  (* [comment removed for export] *)
  amr_metas : forall g, Some g <> mo ->
      (m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
      get_meta_rec st1 g = get_meta_rec st g;
  (* [comment removed for export] *)
  amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
  (* [comment removed for export] *)
  amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
      exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
                 /\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
  amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
  amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
  amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
  (* [comment removed for export] *)
  amr_ptrs : forall P : N -> Prop,
      (forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
      ptrs_in P st -> ptrs_in P st1;
  (* [comment removed for export] *)
  amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.

Definition AM_STACK : Z := 128.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fresh_addr (st : mstate) (a : Z) : Prop :=
  a < alloc_ceiling /\ ranges_free (live_ranges st) a 1 = true.

Lemma ranges_free_In l a n b k : ranges_free l a n = true -> In (b, k) l -> a + n <= b \/ b + k <= a.
Proof.
  intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
  unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.

Lemma ranges_free_intro l a n : (forall b k, In (b, k) l -> a + n <= b \/ b + k <= a) -> ranges_free l a n = true.
Proof.
  intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
  unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.

Lemma ranges_free_sub l a n a' n' : ranges_free l a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> ranges_free l a' n' = true.
Proof.
  intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). lia.
Qed.

Lemma In_live_ranges st rid r : (s_regions st) !! rid = Some r ->
  In (region_live_range r) (live_ranges st).
Proof.
  intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
  apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.

(* [comment removed for export] *)
Lemma fresh_live_region st a rid r : fresh_addr st a -> (s_regions st) !! rid = Some r ->
  a + 1 <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= a.
Proof.
  intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fresh_addr_anti st st' a :
  s_reserved st' = s_reserved st ->
  (forall rid r, (s_regions st) !! rid = Some r ->
     exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
  fresh_addr st' a -> fresh_addr st a.
Proof.
  intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
  unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
  - apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
  - apply in_map_iff in HI. cps_destruct HI as ([rid r] & E & HI). cbn [snd] in E.
    apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
    cps_destruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
    pose proof (In_live_ranges st' rid r' Hr') as HI'.
    assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
    { unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
    unfold region_live_range in HI', E. rewrite K', B' in HI'.
    destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed.

Definition am_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (s : PState) (lo : Z) (m : mem)
    (st1 : mstate) (mo : optr) (s' : PState) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (pw st1 mo) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' (errno_addr tp) [C4 errv']
    /\ auxv_ok m' (bv_unsigned sp)
    /\ pres_except (fun a => alloc_fp (fun k => k <> RKGroup) st1 lo (bv_unsigned sp) a \/ fresh_addr st a) m m'
    /\ mrep st1 m' /\ ticks_ok st1
    /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
    /\ am_rel st st1 mo.

(* [comment removed for export] *)
Definition alloc_meta_stmt (am_pre : mstate -> Prop) : Prop :=
  forall (R : Type) (k : mstate -> optr -> Malloc.M R) (bail : Malloc.M R) (o : mem)
         (s : PState) (Q : R -> PState -> machine_state -> Prop)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : mstate) (lo : Z) (errv : word),
  am_pre st -> mrep st m -> ticks_ok st -> brk_link_ps st s ->
  auxv_ok m (bv_unsigned sp) ->
  stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - AM_STACK ->
  rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m ->
  gp = Z_to_bv 64 0x1a800 -> tp = Z_to_bv 64 0x1a620 ->
  (forall st1 mo s' ms',
     am_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s lo m st1 mo s' ms' ->
     brk_link_ps st1 s' ->
     implT o (k st1 mo) s' Q ms') ->
  implT o (alloc_meta st k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 alloc_meta_entry) fc None m (seg_rom asegs)).

End ACeilS2.
