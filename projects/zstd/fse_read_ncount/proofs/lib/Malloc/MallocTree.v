(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import Tac Image ZBridge SysStep Walk ITree Nodes Decode Arr.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import MallocRep.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Malloc Require Import ProgDeps.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Section CANSEC1. Context {rc : runConstT}.
Definition mem := word -> option byte.
Definition pans_mem (o : mem) (q : aptr) (caddr hint : Z) : Z :=
match o (wa caddr) with Some b => bv_unsigned b | None => 0 end.
Definition pupd_mem (o : mem) (e : ev) (z : Z) : mem := o.
#[using="Type"] Lemma pans_mem_range : forall o q c h, 0 <= pans_mem o q c h < 256.
Proof.
intros. unfold pans_mem. Local Ltac2 Set LiaHints.tbl := fun () => "0020=21381470951.757021565011.5000003004S1RS".
destruct (o (wa c)) as [b|]; [|lia].
pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Definition mrun {R} (o : mem) (t : Malloc.M R) : Malloc.M (mem * R) := prun pans_mem pupd_mem o t.
#[using="Type"] Lemma mrun_ret {R} o (r : R) : mrun o (SRet r) = SRet (o, r).
Proof. reflexivity. Qed.
#[using="Type"] Lemma mrun_peek {R} o p c h (k : Z -> Malloc.M R) : mrun o (SVis (EPeek p c h) k) = mrun o (k (pans_mem o p c h)).
Proof. reflexivity. Qed.
#[using="Type"] Lemma mrun_vis {R} o e (k : Z -> Malloc.M R) :
match e with EPeek _ _ _ => False | _ => True end ->
mrun o (SVis e k) = SVis e (fun z => mrun o (k z)).
Proof. intros He. destruct e; try reflexivity. destruct He. Qed.
#[using="Type"] Lemma steq_sym {E A R} (t1 t2 : stree E A R) : steq t1 t2 -> steq t2 t1.
Proof. induction 1; constructor; auto. Qed.
Definition mmap_val (a : mmap_ans) : Z := match a with MmErr e => neg_errno e | MmOk x => x end.
Definition fixed_val (addr : Z) (a : fixed_ans) : Z :=
match a with FxKept e => neg_errno e | FxDone => addr | FxLost e => neg_errno e end.
Definition range_val (a : range_ans) : Z := match a with RgErr e => neg_errno e | RgDone _ => 0 end.
Definition leaf_of {R} (o : mem) (t : Malloc.M R) (r : R) : Prop :=
exists ans o', follow (mrun o t) ans = Some (o', r).
#[using="Type"] Lemma leaf_of_ret {R} o (r : R) : leaf_of o (SRet r) r.
Proof. exists [], o. reflexivity. Qed.
#[using="Type"] Lemma leaf_of_vis {R} o e (k : Z -> Malloc.M R) z r :
match e with EPeek _ _ _ => False | EUndef _ => False | _ => True end ->
leaf_of o (k z) r -> leaf_of o (SVis e k) r.
Proof.
intros He (ans & o' & H). exists (z :: ans), o'. unfold mrun, prun. cbn [eruns].
destruct e; cbn [psel]; try exact H; destruct He.
Qed.
#[using="Type"] Lemma leaf_of_peek {R} o p c h (k : Z -> Malloc.M R) r :
leaf_of o (k (pans_mem o p c h)) r -> leaf_of o (SVis (EPeek p c h) k) r.
Proof. intros (ans & o' & H). exists ans, o'. rewrite mrun_peek. exact H. Qed.
#[using="Type"] Lemma Forall_disjoint_from : forall (P : Z * Z -> Prop) W a n,
Forall P W -> (forall lo hi, P (lo, hi) -> a + n <= lo \/ hi <= a) -> disjoint_from W a n.
Proof.
intros P W a n F HP. induction F as [|[lo hi] W Hx F IH]; cbn; [exact I|]. split; [apply (HP _ _ Hx)| exact IH].
Qed.
Definition alloc_fp (K : rkind -> Prop) (st1 : mstate) (lo sp : Z) (a : Z) : Prop :=
lo <= a < sp
\/ errno_addr (Z_to_bv 64 0x1a620) <= a < errno_addr (Z_to_bv 64 0x1a620) + 4
\/ CTX <= a < CTX + 928
\/ exists rid r, (s_regions st1) !! rid = Some r /\ K (r_kind r) /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).
Definition brk_link_ps (st : mstate) (s : PState) : Prop :=
match c_brk (ctx st) with
| BrkLive rid off => ps_brk s = conc st (rid, off)
| _ => True
end.
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
#[using="Type"] Lemma ptrs_in_mono (P P' : N -> Prop) st : (forall r, P r -> P' r) -> ptrs_in P st -> ptrs_in P' st.
Proof.
intros HP (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
assert (OM : forall p, optr_in P p -> optr_in P' p) by (intros [q|]; cbn; auto).
split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
split; [intros sc; apply OM, H6|]. split; [destruct (c_brk (ctx st)); auto|].
split; [intros g; destruct (H8 g) as (X1 & X2 & X3); auto|].
split; [intros a ar Ha; destruct (H9 a ar Ha); auto|].
intros b gh Hb; destruct (H10 b gh Hb); auto.
Qed.
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
amr_metas : forall g, Some g <> mo ->
(m_mem (get_meta_rec st g) <> None \/ m_next (get_meta_rec st g) = None) ->
get_meta_rec st1 g = get_meta_rec st g;
amr_result : forall m, mo = Some m -> get_meta_rec st1 m = meta0 /\ meta_slot st1 m;
amr_regions : forall rid r, (s_regions st) !! rid = Some r ->
exists r', (s_regions st1) !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r
/\ r_len r <= r_len r' /\ (r_kind r = RKGroup -> r' = r);
amr_new : forall rid r', (s_regions st1) !! rid = Some r' -> (s_regions st) !! rid = None -> r_kind r' <> RKGroup;
amr_next_rid : (s_next_rid st <= s_next_rid st1)%N;
amr_areas : forall a, is_Some ((s_areas st) !! a) -> is_Some ((s_areas st1) !! a);
amr_ptrs : forall P : N -> Prop,
(forall rid r, (s_regions st1) !! rid = Some r -> r_kind r <> RKGroup -> P rid) ->
ptrs_in P st -> ptrs_in P st1;
amr_fresh : forall rid, (s_next_rid st1 <= rid)%N -> (s_regions st1) !! rid = None /\ (s_shadow st1) !! rid = (s_shadow st) !! rid
}.
Definition AM_STACK : Z := 128.
Definition fresh_addr (st : mstate) (a : Z) : Prop :=
a < ATOP /\ ranges_free (live_ranges st) a 1 = true.
#[using="Type"] Lemma ranges_free_In l a n b k : ranges_free l a n = true -> In (b, k) l -> a + n <= b \/ b + k <= a.
Proof.
intros H HI. unfold ranges_free in H. apply (proj1 (forallb_forall _ _) H) in HI. cbn [fst snd] in HI.
unfold iv_disjoint in HI. apply Bool.orb_prop in HI. destruct HI as [X|X]; apply Z.leb_le in X; lia.
Qed.
#[using="Type"] Lemma ranges_free_intro l a n : (forall b k, In (b, k) l -> a + n <= b \/ b + k <= a) -> ranges_free l a n = true.
Proof.
intros H. unfold ranges_free. apply (proj2 (forallb_forall _ _)). intros [b k] HI. cbn [fst snd].
unfold iv_disjoint. destruct (H b k HI) as [X|X]; [rewrite (proj2 (Z.leb_le _ _) X); reflexivity|].
rewrite (proj2 (Z.leb_le _ _) X). apply Bool.orb_true_r.
Qed.
#[using="Type"] Lemma ranges_free_sub l a n a' n' : ranges_free l a n = true -> a <= a' -> a' + n' <= a + n -> 0 <= n' -> ranges_free l a' n' = true.
Proof.
intros H H1 H2 H3. apply ranges_free_intro. intros b k HI. pose proof (ranges_free_In l a n b k H HI). Local Ltac2 Set LiaHints.tbl := fun () => "0010<492413355.1400000:S2H12H22H0".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma In_live_ranges st rid r : (s_regions st) !! rid = Some r ->
In (region_live_range r) (live_ranges st).
Proof.
intros Hr. unfold live_ranges. apply in_or_app. right. apply in_map_iff. exists (rid, r). split; [reflexivity|].
apply (proj1 (list_elem_of_In _ _)). apply elem_of_map_to_list. exact Hr.
Qed.
#[using="Type"] Lemma fresh_live_region st a rid r : fresh_addr st a -> (s_regions st) !! rid = Some r ->
a + 1 <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= a.
Proof.
intros [_ FR] Hr. pose proof (In_live_ranges st rid r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
Local Ltac2 Set LiaHints.tbl := fun () => "0020=56556209113.957469132786.9000003006S1HS1H".
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ FR HI); lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma fresh_addr_anti st st' a :
s_reserved st' = s_reserved st ->
(forall rid r, (s_regions st) !! rid = Some r ->
exists r', (s_regions st') !! rid = Some r' /\ r_kind r' = r_kind r /\ r_base r' = r_base r /\ r_len r <= r_len r') ->
fresh_addr st' a -> fresh_addr st a.
Proof.
intros RS HR [FC FR]. split; [exact FC|]. apply ranges_free_intro. intros b k HI.
unfold live_ranges in HI. apply in_app_or in HI. destruct HI as [HI|HI].
- apply (ranges_free_In (live_ranges st') a 1 b k FR). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI.
- apply in_map_iff in HI. destruct HI as ([rid r] & E & HI). cbn [snd] in E.
apply (proj2 (list_elem_of_In _ _)) in HI. apply elem_of_map_to_list in HI.
destruct (HR rid r HI) as (r' & Hr' & K' & B' & L').
pose proof (In_live_ranges st' rid r' Hr') as HI'.
assert (RU : round_up_pg (r_len r) <= round_up_pg (r_len r')).
{ unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). Local Ltac2 Set LiaHints.tbl := fun () => "0040>17208403286.2145235811632.2150806061467.3556562515937.2100000100700F00LSS2RU1HS2L'1H2H02H42H5S2RU1H".
rewrite !Z.land_ones by lia. Z.div_mod_to_equations. lia. }
unfold region_live_range in HI', E. rewrite K', B' in HI'.
destruct (r_kind r); inversion E; subst; (pose proof (ranges_free_In _ _ _ _ _ FR HI'); lia).
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End CANSEC1.
