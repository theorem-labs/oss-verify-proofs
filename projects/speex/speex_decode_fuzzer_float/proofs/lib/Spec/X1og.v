(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (the launch's reserved ledger now also holds the vDSO/vvar pair, so KL reads the allocator's own reservations as a prefix of vm_reserved, kl_resv_top reads a reserved entry as below the brk start or one of the pair, and the new kl_vdso_in, kl_vdso_above and kl_vdso_disj carry the pair for mprotect's vDSO gate, with region_free_apart, vdso_gate_apart, kl_vdso_move and the interval lemmas a subtracted ledger needs). *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bs X1c2 X1bn.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1qx X1qs X1ra X1qu X1r3.
Import ListNotations.
Import X1bs.Exc.
Open Scope Z_scope.

Inductive brk_phase : Type :=
| BPUntried
| BPQueried (cur : Z)
| BPGuard (cur : Z)
| BPLive
| BPDead.

Record mled : Type := mkLed {
ld_ceil : Z;
ld_resv : list (Z * Z);
ld_groups : list (Z * Z);
ld_metas : list (Z * Z * Z);
ld_brkreg : option (Z * Z);
ld_brk : brk_phase;
ld_live : list cptr
}.

Definition led_init (ceil : Z) (resv : list (Z * Z)) : mled := mkLed ceil resv [] [] None BPUntried [].
Definition set_groups (v : list (Z * Z)) (L : mled) := mkLed (ld_ceil L) (ld_resv L) v (ld_metas L) (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_metas (v : list (Z * Z * Z)) (L : mled) := mkLed (ld_ceil L) (ld_resv L) (ld_groups L) v (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_brkreg (v : option (Z * Z)) (L : mled) := mkLed (ld_ceil L) (ld_resv L) (ld_groups L) (ld_metas L) v (ld_brk L) (ld_live L).
Definition set_brkph (v : brk_phase) (L : mled) := mkLed (ld_ceil L) (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) v (ld_live L).
Definition set_live (v : list cptr) (L : mled) := mkLed (ld_ceil L) (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) (ld_brk L) v.

Definition lranges (L : mled) : list (Z * Z) :=
ld_resv L
++ map (fun g => (fst g, round_up_pg (snd g))) (ld_groups L)
++ map (fun m => (fst (fst m), round_up_pg (snd (fst m)))) (ld_metas L)
++ match ld_brkreg L with Some (b, l) => [(b + PGSZ, round_up_pg l - PGSZ)] | None => [] end.

Definition lbrk_pages_ok (L : mled) (lo len : Z) : bool :=
(0 <? lo) && (lo + len <=? ld_ceil L) && ranges_free (lranges L) lo len.

Definition MAPF : Z := MAP_PRIVATE + MAP_ANON.
Definition MAPFX : Z := MAP_PRIVATE + MAP_ANON + MAP_FIXED.
Definition LEN_MAX : Z := 2^63.

Fixpoint g_remove (a : Z) (l : list (Z * Z)) : list (Z * Z) :=
match l with
| [] => []
| y :: l' => if fst y =? a then l' else y :: g_remove a l'
end.
Definition bump_meta (a : Z) (m : Z * Z * Z) : Z * Z * Z :=
let '(b, l, k) := m in if b + (1 + k) * PGSZ =? a then (b, l, k + 1) else m.
Fixpoint ap_remove (c : aptr) (l : list aptr) : list aptr :=
match l with
| [] => []
| y :: l' => if aptr_eqb y c then l' else y :: ap_remove c l'
end.

Definition brk_quiet (L : mled) : Prop :=
match ld_brk L with BPQueried _ | BPGuard _ => False | _ => True end.

Definition event_pre (L : mled) (e : ev) : Prop :=
match e with
| EBrk req =>
(req = 0 /\ ld_brk L = BPUntried)
\/ (exists cur, ld_brk L = BPQueried cur /\ req = round_up_pg cur + 2 * PGSZ)
\/ (exists b l, ld_brk L = BPLive /\ ld_brkreg L = Some (b, l) /\ req = b + l + PGSZ)
| EMmap a len prot flags =>
(brk_quiet L /\ a = 0 /\ flags = MAPF /\ (prot = PROT_NONE \/ prot = PROT_RW) /\ 0 < len < LEN_MAX)
\/ (exists cur, ld_brk L = BPGuard cur /\ a = round_up_pg cur /\ len = PGSZ /\ prot = PROT_NONE /\ flags = MAPFX)
| EMunmap a len => brk_quiet L /\ exists l, In (a, l) (ld_groups L) /\ (len = l \/ len = round_up_pg l)

| EMprotect a len prot =>
brk_quiet L /\ len = PGSZ /\ prot = PROT_RW /\
exists b l k, In (b, l, k) (ld_metas L) /\ a = b + (1 + k) * PGSZ /\ (2 + k) * PGSZ <= round_up_pg l
| EPeek _ _ _ => False
| EUndef _ => False
end.

Definition answer_ok (L : mled) (e : ev) (z : Z) : bool :=
match e with
| EBrk req =>
if req =? 0 then brk0_answer_ok z
else match ld_brk L with
| BPQueried cur => brk_answer_ok cur req z && (negb (z =? req) || lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ))
| _ => match ld_brkreg L with
| Some (b, l) => brk_answer_ok (b + l) req z && (negb (z =? req) || lbrk_pages_ok L (b + l) PGSZ)
| None => false
end
end
| EMmap a len prot flags =>
if Z.land flags MAP_FIXED =? 0 then mmap_answer_ok (ld_ceil L) (lranges L) len z
else mmap_fixed_answer_ok a z
| EMunmap _ _ => munmap_answer_ok z
| EMprotect _ _ _ => mprotect_answer_ok z
| _ => false
end.

Definition event_post (L : mled) (e : ev) (z : Z) : mled :=
match e with
| EBrk req =>
if req =? 0 then set_brkph (BPQueried z) L
else if z =? req then
match ld_brk L with
| BPQueried cur => set_brkph (BPGuard cur) L
| _ => match ld_brkreg L with
| Some (b, l) => set_brkreg (Some (b, l + PGSZ)) L
| None => L
end
end
else set_brkph BPDead L
| EMmap a len prot flags =>
if Z.land flags MAP_FIXED =? 0 then
if is_err z then L
else if prot =? PROT_NONE then set_metas ((z, len, 0) :: ld_metas L) L
else set_groups ((z, len) :: ld_groups L) L
else set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)
| EMunmap a len => set_groups (g_remove a (ld_groups L)) L
| EMprotect a len prot =>
if (z =? 0) || (z =? TWO64 - ENOSYS) then set_metas (map (bump_meta a) (ld_metas L)) L else L
| _ => L
end.

Fixpoint ctree_ok {R} (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
match t with
| SRet r => Post L r
| SVis e k => event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post
end.

Inductive cpath {R} : mled -> stree ev Z R -> mled -> R -> Prop :=
| cpath_ret L r : cpath L (SRet r) L r
| cpath_vis L e k z L' r :
answer_ok L e z = true -> cpath (event_post L e z) (k z) L' r -> cpath L (SVis e k) L' r.

Inductive creach : mstate -> mled -> Prop :=
| creach_init ceil resv : alloc_ceiling_lo <= ceil <= alloc_ceiling_hi ->
creach (strip (minit 0 ceil resv)) (led_init ceil resv)
| creach_malloc cs L n L' cs' r :
creach cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
creach cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| creach_free cs L c L' cs' :
creach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
creach cs' (set_live (ap_remove c (ld_live L')) L').

Definition wz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (wz b, wz n).
Definition wwZ (e : word * word) : Z * Z := (bv_unsigned (fst e), bv_unsigned (snd e)).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

Definition wcov (maps : list (word * word)) (lo hi : Z) : Prop :=
forall x, lo <= x < hi -> exists e, In e maps /\ elo e <= x < ehi e.

Definition edisj (e1 e2 : word * word) : Prop := ehi e1 <= elo e2 \/ ehi e2 <= elo e1.
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf (maps : list (word * word)) : Prop :=
(forall e, In e maps -> elo e < ehi e <= 2^64) /\ pwdisj maps.

Definition brk_disj (L : mled) (b n : Z) : Prop :=
forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
kl_minv : minv mo;
kl_halt : m_halted mo = None;
kl_ceil : alloc_top (m_vmmaps mo) = ld_ceil L
/\ alloc_ceiling_lo <= ld_ceil L <= alloc_ceiling_hi;
kl_wf : vmwf (vm_maps (m_vmmaps mo));
(* The allocator's ledger names the image's own reservations; [State.init_model]
   appends the launch's vDSO/vvar pair after them ([State.vm_reserved_init_model]),
   so the ledger is a PREFIX of [vm_reserved].  What the tail is, [kl_vdso_in]
   says; where it sits, [kl_resv_top]'s second disjunct says. *)
kl_resv : exists lo hi, vm_reserved (m_vmmaps mo) = lo ++ hi /\ ld_resv L = map wwZ lo;
(* A reserved entry is either one of the image's own, which ends below the brk
   start, or one of the launch's vDSO/vvar pair, which [kl_vdso_above] puts far
   above the brk guard and [kl_vdso_in] keeps in the ledger. *)
kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) ->
ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo))
\/ In e (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo)));
kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
/\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
/\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= ld_ceil L;
kl_groups : forall b l, In (b, l) (ld_groups L) ->
0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= ld_ceil L
/\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= ld_ceil L
/\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
/\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
/\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= ld_ceil L
/\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
kl_phase : match ld_brk L with
| BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
| BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
| BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
/\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
/\ ld_brkreg L = None /\ cur + 2 * PGSZ <= ld_ceil L
/\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
/\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
/\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
| BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
| BPDead => True
end;
(* The vDSO/vvar pair, which [State.init_model] reserves and which mprotect's
   answer now refuses to touch ([State.vdso_reserved] above the containment test).
   Three fields carry it, all facts the launch gives and no step disturbs:
     [kl_vdso_in]    the pair IS in the reserved ledger -- true at the launch, and no
                     step writes [vm_reserved], [m_kernel], [vm_mmap_base] or
                     [vm_init_sp];
     [kl_vdso_above] the pair sits a long way above the brk guard, because the
                     launch's placement base is above [State.mmap_base_min] while
                     the brk window stays below 2^40;
     [kl_vdso_disj]  no tracked mapping meets any reserved entry -- true at the launch
                     ([vm_maps] is empty) and kept because every grant tests
                     [region_free] over [vm_reserved ++ vm_maps].
   Together they put a range inside a tracked mapping apart from the pair. *)
kl_vdso_in : incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo)))
(vm_reserved (m_vmmaps mo));
kl_vdso_above : forall e, In e (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) ->
bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e;
kl_vdso_disj : forall r, In r (vm_reserved (m_vmmaps mo)) ->
forall e, In e (vm_maps (m_vmmaps mo)) -> edisj e r }.

(* --------------------------------------------------------------------
   Reading and moving the two vDSO facts.
   -------------------------------------------------------------------- *)

Lemma region_free_apart : forall maps aw nw,
(forall e, In e maps -> ehi e <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= elo e) ->
region_free maps aw nw = true.
Proof.
intros maps aw nw H. apply region_free_intro. intros a sz Hin.
specialize (H (a, sz) Hin). unfold elo, ehi in H. cbn [fst snd] in H. unfold iv_overlap.
destruct H as [H|H].
- replace (bv_unsigned aw <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
reflexivity.
- replace (bv_unsigned a <? bv_unsigned aw + bv_unsigned nw) with false by (symmetry; apply Z.ltb_ge; lia).
apply andb_false_r.
Qed.

Lemma region_free_apart_In : forall maps aw nw e,
region_free maps aw nw = true -> In e maps ->
ehi e <= bv_unsigned aw \/ bv_unsigned aw + bv_unsigned nw <= elo e.
Proof.
intros maps aw nw [a sz] H Hin. pose proof (region_free_In _ _ _ _ _ H Hin) as D.
unfold iv_overlap in D. apply andb_false_iff in D. unfold elo, ehi. cbn [fst snd].
destruct D as [D|D]; apply Z.ltb_ge in D; [left| right]; lia.
Qed.

(* mprotect's vDSO gate: a range apart from every reserved entry misses the pair,
   which [kl_vdso_in] puts among them. *)
Lemma vdso_gate_apart : forall mo addr n,
incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (vm_reserved (m_vmmaps mo)) ->
(forall e, In e (vm_reserved (m_vmmaps mo)) ->
ehi e <= bv_unsigned addr \/ bv_unsigned addr + bv_unsigned n <= elo e) ->
region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) addr n = true.
Proof.
intros mo addr n Hinc Hap. apply region_free_apart. intros e Hin. exact (Hap e (Hinc e Hin)).
Qed.

(* [State.vdso_top] reads [vm_mmap_base] and [alloc_top], and [alloc_top] reads
   [vm_init_sp]: a step that leaves both alone leaves the pair where it is. *)
Lemma vdso_top_eq : forall h h',
vm_mmap_base h' = vm_mmap_base h -> vm_init_sp h' = vm_init_sp h ->
vdso_top h' = vdso_top h.
Proof. intros h h' E1 E2. unfold vdso_top, mmap_top, alloc_top. rewrite E1, E2. reflexivity. Qed.

(* A grant adds one mapping, which the grant's own [region_free] over
   [vm_reserved ++ vm_maps] has already put apart from every reserved entry. *)
Lemma kl_vdso_disj_cons : forall (R M : list (word * word)) aw nw,
region_free (R ++ M) aw nw = true ->
(forall r, In r R -> forall e, In e M -> edisj e r) ->
forall r, In r R -> forall e, In e ((aw, nw) :: M) -> edisj e r.
Proof.
intros R M aw nw Hrf H r Hr e [<-|He]; [|exact (H r Hr e He)].
pose proof (region_free_apart_In _ _ _ r Hrf (in_or_app _ _ _ (or_introl Hr))) as D.
unfold edisj, elo, ehi in *. cbn [fst snd] in *. lia.
Qed.

Lemma edisj_within : forall e e0 r, elo e0 <= elo e -> ehi e <= ehi e0 -> edisj e0 r -> edisj e r.
Proof. intros e e0 r H1 H2 [D|D]; [left| right]; lia. Qed.

(* A cut of one interval lies inside it: what a step that subtracts a range from
   [vm_maps] needs in order to keep [kl_vdso_disj]. *)
Lemma iv_subtract_within : forall (a sz : word) lo hi e,
bv_unsigned a + bv_unsigned sz <= 2^64 -> 0 <= lo -> 0 <= hi ->
In e (iv_subtract a sz lo hi) ->
bv_unsigned a <= elo e /\ ehi e <= bv_unsigned a + bv_unsigned sz.
Proof.
intros a sz lo hi e Hwf Hlo Hhi Hin.
pose proof (bv_unsigned_in_range 64 a) as Ra. pose proof (bv_unsigned_in_range 64 sz) as Rs.
unfold bv_modulus in Ra, Rs. cbn in Ra, Rs.
unfold iv_subtract in Hin. apply in_app_or in Hin as [Hin|Hin].
- destruct (Z.ltb_spec (bv_unsigned a) lo) as [Hlt|Hge]; [|destruct Hin].
destruct Hin as [<-|[]]. unfold elo, ehi. cbn [fst snd]. rewrite X1by.unsigned_lit by lia. lia.
- destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Hlt|Hge]; [|destruct Hin].
destruct Hin as [<-|[]]. unfold elo, ehi. cbn [fst snd]. rewrite !X1by.unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_within : forall maps lo hi e,
(forall e0, In e0 maps -> ehi e0 <= 2^64) -> 0 <= lo -> 0 <= hi ->
In e (maps_subtract maps lo hi) ->
exists e0, In e0 maps /\ elo e0 <= elo e /\ ehi e <= ehi e0.
Proof.
induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlo Hhi Hin; [destruct Hin|].
cbn [maps_subtract] in Hin. apply in_app_or in Hin as [Hin|Hin].
- pose proof (Hwf (a, sz) (or_introl eq_refl)) as W. unfold ehi in W; cbn [fst snd] in W.
destruct (iv_subtract_within a sz lo hi e W Hlo Hhi Hin) as [H1 H2].
exists (a, sz). split; [left; reflexivity|]. unfold elo, ehi; cbn [fst snd]. split; assumption.
- destruct (IH lo hi e ltac:(intros e0 He0; apply Hwf; right; exact He0) Hlo Hhi Hin) as (e0 & He0 & H1 & H2).
exists e0. split; [right; exact He0|]. split; assumption.
Qed.

(* The ledger fact and the three vDSO facts of [KL] move across a step together: each
   reads [m_kernel], [vm_reserved], [vm_start_brk] and -- through [State.vdso_top] --
   [vm_mmap_base] and [vm_init_sp], and no step of this tree writes any of them.
   [rsv] is the ledger's reservation list, which a step does not change either. *)
Lemma kl_vdso_move : forall mo mo' (rsv : list (Z * Z)),
m_kernel mo' = m_kernel mo ->
vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) ->
vm_start_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo) ->
(exists lo hi, vm_reserved (m_vmmaps mo) = lo ++ hi /\ rsv = map wwZ lo) ->
(forall e, In e (vm_reserved (m_vmmaps mo)) ->
ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo))
\/ In e (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo)))) ->
incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (vm_reserved (m_vmmaps mo)) ->
(forall e, In e (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) ->
bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e) ->
(exists lo hi, vm_reserved (m_vmmaps mo') = lo ++ hi /\ rsv = map wwZ lo)
/\ (forall e, In e (vm_reserved (m_vmmaps mo')) ->
ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo'))
\/ In e (vdso_reserved (m_kernel mo') (vdso_top (m_vmmaps mo'))))
/\ incl (vdso_reserved (m_kernel mo') (vdso_top (m_vmmaps mo'))) (vm_reserved (m_vmmaps mo'))
/\ (forall e, In e (vdso_reserved (m_kernel mo') (vdso_top (m_vmmaps mo'))) ->
bv_unsigned (vm_start_brk (m_vmmaps mo')) + 4 * PGSZ <= elo e).
Proof.
intros mo mo' rsv Ek Er Eb Es Esb H0 H1 H2 H3.
rewrite Ek, Er, Esb, (vdso_top_eq _ _ Eb Es).
split; [exact H0|]. split; [exact H1|]. split; [exact H2| exact H3].
Qed.

Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.

Lemma vm_only_refl : forall mo, vm_only mo mo.
Proof. exact X1c7.vm_only_refl. Qed.
Lemma vm_only_trans : forall a b c, vm_only a b -> vm_only b c -> vm_only a c.
Proof. exact X1c7.vm_only_trans. Qed.

Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
: Z -> PState -> Model -> Prop :=
fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
/\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

