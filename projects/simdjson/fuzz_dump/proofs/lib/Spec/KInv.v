(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: the kernel ledger invariant covers the vDSO pair of reservations, with lemmas for its initial state and that mappings miss the pair. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

From OSSVerify.Proofs.simdjson.fuzz_dump.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section WithCeiling. Context {CE__ : Ceiling}.

Inductive brk_phase : Type :=
| BPUntried
| BPQueried (cur : Z)
| BPGuard (cur : Z)
| BPLive
| BPDead.

Record mled : Type := mkLed {
  ld_resv : list (Z * Z);
  ld_groups : list (Z * Z);
  ld_metas : list (Z * Z * Z);
  ld_brkreg : option (Z * Z);
  ld_brk : brk_phase;
  ld_live : list cptr
}.

Definition led_init (resv : list (Z * Z)) : mled := mkLed resv [] [] None BPUntried [].
Definition set_groups (v : list (Z * Z)) (L : mled) := mkLed (ld_resv L) v (ld_metas L) (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_metas (v : list (Z * Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) v (ld_brkreg L) (ld_brk L) (ld_live L).
Definition set_brkreg (v : option (Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) v (ld_brk L) (ld_live L).
Definition set_brkph (v : brk_phase) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) v (ld_live L).
Definition set_live (v : list cptr) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) (ld_brk L) v.

Definition lranges (L : mled) : list (Z * Z) :=
  ld_resv L
  ++ map (fun g => (fst g, round_up_pg (snd g))) (ld_groups L)
  ++ map (fun m => (fst (fst m), round_up_pg (snd (fst m)))) (ld_metas L)
  ++ match ld_brkreg L with Some (b, l) => [(b + PGSZ, round_up_pg l - PGSZ)] | None => [] end.

Definition lbrk_pages_ok (L : mled) (lo len : Z) : bool :=
  (0 <? lo) && (lo + len <=? MCEIL) && ranges_free (lranges L) lo len.

Lemma ceil_le_MCEIL : alloc_ceiling <= MCEIL.
Proof. ceil_bounds. unfold MCEIL. lia. Qed.

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
      if Z.land flags MAP_FIXED =? 0 then mmap_answer_ok (lranges L) len z
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
| creach_init resv : creach (strip (minit 0 resv)) (led_init resv)
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
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  (* LPS 08b1429: the ledger is the image's reservations [R0] (what the heap's
     ghost [ld_resv] knows, below [start_brk]) followed by the vDSO pair [rx]
     ([State.init_reserved]): at most two entries and 20 pages, at or above
     [start_brk + 4 pages]. See recipes/artm-vdso-ledger.md, rauxv-layout.md. *)
  kl_resv : exists R0 rx, vm_reserved (m_vmmaps mo) = R0 ++ rx /\ ld_resv L = map wwZ R0
      /\ (forall e, In e R0 -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo)))
      /\ (forall e, In e rx -> bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e)
      /\ (length rx <= 2)%nat /\ live_bytes rx <= 0x14000;
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) ->
      ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo))
      \/ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= elo e;
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

  kl_top : alloc_top (m_vmmaps mo) = alloc_ceiling;
  (* LPS 08b1429: every mapping is free of the reserved ledger (placement grants only
     [region_free (vm_reserved ++ vm_maps)] ranges), and the vDSO pair [check_mprotect]
     tests is part of that ledger. Together: a range inside a mapping misses the pair. *)
  kl_mres : forall e, In e (vm_maps (m_vmmaps mo)) -> region_free (vm_reserved (m_vmmaps mo)) (fst e) (snd e) = true;
  kl_vin : incl (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) (vm_reserved (m_vmmaps mo)) }.

Lemma KL_vin_init : forall reserved brk0 mbase sp lim inp,
  incl (vdso_reserved (m_kernel (init_model reserved brk0 mbase sp lim inp))
                      (vdso_top (m_vmmaps (init_model reserved brk0 mbase sp lim inp))))
       (vm_reserved (m_vmmaps (init_model reserved brk0 mbase sp lim inp))).
Proof.
  intros. rewrite vm_reserved_init_model.
  assert (EK : m_kernel (init_model reserved brk0 mbase sp lim inp) = in_kernel inp) by reflexivity.
  rewrite EK. intros x Hx. apply in_or_app. right. exact Hx.
Qed.

Definition frame_ok (G : PState -> Model -> Prop) : Prop :=
  forall s s' mo mo', ps_fa s' = ps_fa s -> ps_so s' = ps_so s -> vm_only mo mo' -> G s mo -> G s' mo'.

Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop :=
  fun z s mo => answer_ok L e z = true /\ KL (event_post L e z) (ps_brk s) mo /\ G s mo
                /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0.

Lemma reserved_top_ge_kl : forall l e, In e l -> ehi e <= reserved_top l.
Proof.
  induction l as [|[a sz] l IH]; intros e Hin; [destruct Hin|].
  cbn [reserved_top]. destruct Hin as [<-|Hin]; unfold ehi; cbn [fst snd]; [lia|]. specialize (IH e Hin). unfold ehi in IH. lia.
Qed.

Lemma vdso_reserved_size : forall kb top,
  (length (vdso_reserved kb top) <= 2)%nat /\ live_bytes (vdso_reserved kb top) <= 0x14000.
Proof.
  intros kb top. pose proof (vdso_text_pages_pos kb). pose proof (vdso_text_pages_le kb).
  unfold vdso_reserved. cbv zeta.
  match goal with |- context [if ?c then _ else _] => destruct c end; cbn [length live_bytes]; [lia|].
  rewrite !bv_unsigned_Z_to_bv_u64 by (unfold two_pow_64, vdso_vvar_pages, page_size in *; lia).
  unfold vdso_vvar_pages, page_size. lia.
Qed.

(* The ledger [init_model] starts from: the image's reservations, then the vDSO
   pair under [min mbase (sp - stack_max_size)], far above any brk start. *)
Lemma KL_resv_init : forall segs brk0 mbase sp lim inp,
  valid_brk segs brk0 -> reserved_top (segments_reserved segs) + brk_aslr_max <= 2 ^ 33 ->
  mmap_base_min <= bv_unsigned mbase -> bv_unsigned sp - stack_max_size = alloc_ceiling ->
  let h := m_vmmaps (init_model (segments_reserved segs) brk0 mbase sp lim inp) in
  (exists R0 rx, vm_reserved h = R0 ++ rx /\ map wwZ (segments_reserved segs) = map wwZ R0
      /\ (forall e, In e R0 -> ehi e <= bv_unsigned (vm_start_brk h))
      /\ (forall e, In e rx -> bv_unsigned (vm_start_brk h) + 4 * PGSZ <= elo e)
      /\ (length rx <= 2)%nat /\ live_bytes rx <= 0x14000)
  /\ (forall e, In e (vm_reserved h) ->
        ehi e <= bv_unsigned (vm_start_brk h) \/ bv_unsigned (vm_start_brk h) + 4 * PGSZ <= elo e).
Proof.
  intros segs brk0 mbase sp lim inp (Hlo & Hhi & Hal) Hlow Hmb Htop h.
  set (T := page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))).
  assert (ER : vm_reserved h = segments_reserved segs ++ vdso_reserved (in_kernel inp) T)
    by (subst h T; rewrite m_vmmaps_init_model; reflexivity).
  assert (ESB : vm_start_brk h = brk0) by (subst h; rewrite m_vmmaps_init_model; reflexivity).
  pose proof alloc_ceiling_ge as HCg. pose proof alloc_ceiling_le as HCl.
  pose proof (vdso_len_bounds (in_kernel inp)) as VL.
  pose proof (bv_unsigned_in_range 64 mbase) as RM. unfold bv_modulus in RM. cbn in RM.
  assert (HT : Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size) - 4096 < T
               <= Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)).
  { subst T. unfold page_round_down_Z, page_size. Z.div_mod_to_equations. lia. }
  assert (HX : forall e, In e (vdso_reserved (in_kernel inp) T) -> bv_unsigned brk0 + 4 * PGSZ <= elo e).
  { intros [a n] Hin. destruct (vdso_reserved_above (in_kernel inp) T a n ltac:(unfold two_pow_64; lia) Hin) as [A1 _].
    unfold elo. cbn [fst]. unfold mmap_base_min, PGSZ, page_size, stack_max_size in *. lia. }
  assert (HR : forall e, In e (segments_reserved segs) -> ehi e <= bv_unsigned brk0)
    by (intros e He; pose proof (reserved_top_ge_kl _ _ He); lia).
  destruct (vdso_reserved_size (in_kernel inp) T) as [LN LB].
  rewrite ER, ESB. split.
  - exists (segments_reserved segs), (vdso_reserved (in_kernel inp) T).
    split; [reflexivity|]. split; [reflexivity|]. split; [exact HR|]. split; [exact HX|]. split; assumption.
  - intros e He. apply in_app_or in He as [He|He]; [left; exact (HR e He)| right; exact (HX e He)].
Qed.

End WithCeiling.
