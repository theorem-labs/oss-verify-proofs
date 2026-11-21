(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (in the KL record the old kl_resv and kl_resv_top fields are replaced by kl_resv over the new kresv, the reserved list being the image part plus the launch's vDSO and vvar pair, and kl_apart over the new kapart, tracked mappings apart from every reserved entry; new lemmas region_free_app_l, kresv_keep, kresv_in, kresv_vdso, region_free_of_apart, kapart_free, KL_vdso_free_core and kapart_step). *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Prelim Monad MSafe STree Malloc Prog.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_KInv () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Prog.PState"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Prog.ps_fa"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.Heap.Prog.ps_so"; "OSSVerify.KrLib.Lib.Nodes.vm_only"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.bool"; "answer_ok"; "Corelib.Init.Datatypes.true"; "KL"; "event_post"; "OSSVerify.KrLib.Heap.Prog.ps_brk"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.Prog.ps_m"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive brk_phase : Type :=
| BPUntried                 (* [comment removed for export] *)
| BPQueried (cur : Z)       (* [comment removed for export] *)
| BPGuard (cur : Z)         (* [comment removed for export] *)
| BPLive                    (* [comment removed for export] *)
| BPDead.                   (* [comment removed for export] *)

Record mled : Type := mkLed {
  ld_resv : list (Z * Z);          (* [comment removed for export] *)
  ld_groups : list (Z * Z);        (* [comment removed for export] *)
  ld_metas : list (Z * Z * Z);     (* [comment removed for export] *)
  ld_brkreg : option (Z * Z);      (* [comment removed for export] *)
  ld_brk : brk_phase;
  ld_live : list cptr;             (* [comment removed for export] *)
  ld_ceil : Z                      (* [comment removed for export] *)
}.

Definition led_init (ceil : Z) (resv : list (Z * Z)) : mled := mkLed resv [] [] None BPUntried [] ceil.
Definition set_groups (v : list (Z * Z)) (L : mled) := mkLed (ld_resv L) v (ld_metas L) (ld_brkreg L) (ld_brk L) (ld_live L) (ld_ceil L).
Definition set_metas (v : list (Z * Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) v (ld_brkreg L) (ld_brk L) (ld_live L) (ld_ceil L).
Definition set_brkreg (v : option (Z * Z)) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) v (ld_brk L) (ld_live L) (ld_ceil L).
Definition set_brkph (v : brk_phase) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) v (ld_live L) (ld_ceil L).
Definition set_live (v : list cptr) (L : mled) := mkLed (ld_resv L) (ld_groups L) (ld_metas L) (ld_brkreg L) (ld_brk L) v (ld_ceil L).

(* [comment removed for export] *)
Definition lranges (L : mled) : list (Z * Z) :=
  ld_resv L
  ++ map (fun g => (fst g, round_up_pg (snd g))) (ld_groups L)
  ++ map (fun m => (fst (fst m), round_up_pg (snd (fst m)))) (ld_metas L)
  ++ match ld_brkreg L with Some (b, l) => [(b + PGSZ, round_up_pg l - PGSZ)] | None => [] end.

(* [comment removed for export] *)
Definition lbrk_pages_ok (L : mled) (lo len : Z) : bool :=
  (0 <? lo) && (lo + len <=? ld_ceil L) && ranges_free (lranges L) lo len.

Definition MAPF : Z := MAP_PRIVATE + MAP_ANON.
Definition MAPFX : Z := MAP_PRIVATE + MAP_ANON + MAP_FIXED.
Definition LEN_MAX : Z := 2^63.   (* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
        (* [comment removed for export] *)
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

(* [comment removed for export] *)
Fixpoint ctree_ok {R} (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post
  end.

(* [comment removed for export] *)
Inductive cpath {R} : mled -> stree ev Z R -> mled -> R -> Prop :=
| cpath_ret L r : cpath L (SRet r) L r
| cpath_vis L e k z L' r :
    answer_ok L e z = true -> cpath (event_post L e z) (k z) L' r -> cpath L (SVis e k) L' r.

(* [comment removed for export] *)
Inductive creach : mstate -> mled -> Prop :=
| creach_init secret canary ceil resv :
    0 <= secret < 2^64 -> 0 <= canary < 2^64 -> ceil_ok ceil ->
    creach (strip (minit secret canary ceil resv)) (led_init ceil resv)
| creach_malloc cs L n L' cs' r :
    creach cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
    creach cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| creach_free cs L c L' cs' :
    creach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
    creach cs' (set_live (ap_remove c (ld_live L')) L').

(* [comment removed for export] *)


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
Definition brk_disj (L : mled) (b n : Z) : Prop :=
  forall b0 l0, ld_brkreg L = Some (b0, l0) -> b + n <= b0 + PGSZ \/ b0 + l0 <= b.

(* At 08b1429 [init_model] ends the reserved ledger with the launch's
   vDSO/vvar pair ([State.init_reserved]); the heap ledger's own copy
   [ld_resv] is the image part.  [kresv] says so, and [kapart] keeps the
   tracked mappings apart from every reserved entry (the pair included), as
   the model's own [AsanPlanSound.co_vdso] / [co_mres] do. *)
Definition kresv (L : mled) (mo : Model) : Prop :=
  map wwZ (vm_reserved (m_vmmaps mo))
  = ld_resv L ++ map wwZ (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))).
Definition kapart (h : VmMaps) : Prop :=
  forall e r, In e (vm_maps h) -> In r (vm_reserved h) -> edisj e r.

(* [comment removed for export] *)
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  kl_ceil : ld_ceil L = alloc_top (m_vmmaps mo);
  kl_ceil_ok : ceil_ok (ld_ceil L);
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
  kl_resv : kresv L mo;
  kl_apart : kapart (m_vmmaps mo) }.

Lemma region_free_app_l : forall (l1 l2 : list (word * word)) a n,
  region_free (l1 ++ l2) a n = true -> region_free l1 a n = true.
Proof.
  induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [reflexivity|]. cbn [app region_free] in H |- *.
  apply andb_prop in H as [H1 H2]. rewrite H1. cbn [andb]. exact (IH _ _ _ H2).
Qed.

Lemma kresv_keep L L' mo mo' : kresv L mo -> ld_resv L' = ld_resv L -> m_kernel mo' = m_kernel mo ->
  vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo) ->
  vm_mmap_base (m_vmmaps mo') = vm_mmap_base (m_vmmaps mo) ->
  vm_init_sp (m_vmmaps mo') = vm_init_sp (m_vmmaps mo) -> kresv L' mo'.
Proof.
  unfold kresv. intros K E0 E1 E2 E3 E4. rewrite E0, E1, E2.
  replace (vdso_top (m_vmmaps mo')) with (vdso_top (m_vmmaps mo)); [exact K|].
  unfold vdso_top, mmap_top, alloc_top. rewrite E3, E4. reflexivity.
Qed.

Lemma kresv_in L mo x : kresv L mo -> In x (ld_resv L) ->
  exists e, In e (vm_reserved (m_vmmaps mo)) /\ wwZ e = x.
Proof.
  unfold kresv. intros K H.
  assert (H' : In x (map wwZ (vm_reserved (m_vmmaps mo)))) by (rewrite K; apply in_or_app; left; exact H).
  apply in_map_iff in H' as (e & E & He). exists e. split; assumption.
Qed.

Lemma kresv_vdso L mo r : kresv L mo -> In r (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) ->
  exists e, In e (vm_reserved (m_vmmaps mo)) /\ wwZ e = wwZ r.
Proof.
  unfold kresv. intros K H.
  assert (H' : In (wwZ r) (map wwZ (vm_reserved (m_vmmaps mo)))).
  { rewrite K. apply in_or_app; right. apply in_map. exact H. }
  apply in_map_iff in H' as (e & E & He). exists e. split; assumption.
Qed.

Lemma region_free_of_apart : forall (l : list (word * word)) (a n : word),
  (forall r, In r l -> bv_unsigned a + bv_unsigned n <= elo r \/ ehi r <= bv_unsigned a) ->
  region_free l a n = true.
Proof.
  induction l as [|[b s] l IH]; intros a n H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros r Hr; apply H; right; exact Hr).
  specialize (H (b, s) (or_introl eq_refl)). unfold elo, ehi in H. cbn [fst snd] in H.
  unfold iv_overlap.
  destruct (Z.ltb_spec (bv_unsigned a) (bv_unsigned b + bv_unsigned s));
  destruct (Z.ltb_spec (bv_unsigned b) (bv_unsigned a + bv_unsigned n)); cbn; try reflexivity; lia.
Qed.

(* a range inside a tracked mapping is free of the reserved ledger *)
Lemma kapart_free h e (a n : word) : kapart h -> In e (vm_maps h) ->
  elo e <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= ehi e ->
  region_free (vm_reserved h) a n = true.
Proof.
  intros K He H1 H2. apply region_free_of_apart. intros r Hr.
  pose proof (K e r He Hr) as D. unfold edisj in D. lia.
Qed.

(* ... and of the vDSO pair, which [kresv] puts in that ledger *)
Lemma KL_vdso_free_core L mo e (a n : word) : kresv L mo -> kapart (m_vmmaps mo) -> In e (vm_maps (m_vmmaps mo)) ->
  elo e <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= ehi e ->
  region_free (vdso_reserved (m_kernel mo) (vdso_top (m_vmmaps mo))) a n = true.
Proof.
  intros R K He H1 H2. apply region_free_of_apart. intros r Hr.
  destruct (kresv_vdso L mo r R Hr) as (r' & Hr' & E).
  pose proof (K e r' He Hr') as D. unfold edisj in D.
  unfold wwZ in E. injection E as E1 E2. unfold elo, ehi in *. rewrite <- E1, <- E2. lia.
Qed.

(* the apartness survives a step that keeps the ledger and keeps, shrinks
   or adds mappings (an added one comes free of the ledger) *)
Lemma kapart_step h h' : kapart h -> vm_reserved h' = vm_reserved h ->
  (forall e, In e (vm_maps h') ->
     (exists e0, In e0 (vm_maps h) /\ elo e0 <= elo e /\ ehi e <= ehi e0)
     \/ region_free (vm_reserved h) (fst e) (snd e) = true) ->
  kapart h'.
Proof.
  intros K Er H e r He Hr. rewrite Er in Hr. destruct (H e He) as [(e0 & He0 & L1 & L2)|F].
  - pose proof (K e0 r He0 Hr) as D. unfold edisj in *. lia.
  - destruct r as [b s]. pose proof (region_free_In _ _ _ _ _ F Hr) as D.
    unfold edisj, elo, ehi in *. cbn [fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
Definition frame_ok (G : PState -> Model -> Prop) : Prop := ltac2:(CDefT.buildp (gd_tbl_KInv ()) "Ps,$0.Ps',$0.Pmo,$1.Pmo',$1.P,(2.(3.$4.$4.)(5.R3.)(5.R4.))P,(2.$6.(7.R4.)(7.R5.))P,(8.R4.R3.)P,A2.O1.R7.R5.A2.O1.R7.R5.")
(* [comment removed for export] *).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ev_step_post (L : mled) (e : ev) (G : PState -> Model -> Prop) (s0 : PState)
  : Z -> PState -> Model -> Prop := ltac2:(CDefT.buildp (gd_tbl_KInv ()) "Lz,$4.Ls,$0.Lmo,$1.(9.(2.$:.(;.O4.O3.R3.)$<.)(9.(=.(>.O4.O3.R3.)(?.R2.)R1.)(9.A2.O2.R2.R1.(9.(2.$10.(11.R2.)(11.O1.))(9.(2.(3.$4.$4.)(5.R2.)(5.O1.))(2.$6.(7.R2.)(7.O1.)))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
