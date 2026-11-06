(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.paintcmap_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocTreeW MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_sep MallocInv_wf MallocInv_steps MallocInv_repw MallocInv_env MallocInv_vm MallocInv_coh MallocInv_ops MallocInv_ameta_iface.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Definition am_delta (h h' : VmMaps) : Prop :=
  ((exists b, vm_maps h' = (b, Z_to_bv 64 8192) :: vm_maps h) \/ vm_maps h' = vm_maps h) /\
  vm_backed_bytes h' <= vm_backed_bytes h + 4096 /\
  vm_init_sp h' = vm_init_sp h /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h.

(* [comment removed for export] *)
Definition am_grow (h h' : VmMaps) : Prop :=
  Z.of_nat (length (vm_maps h')) <= Z.of_nat (length (vm_maps h)) + 1 /\
  vm_backed_bytes h' <= vm_backed_bytes h + 8192 /\
  vm_init_sp h' = vm_init_sp h /\ vm_reserved h' = vm_reserved h /\ vm_limit h' = vm_limit h.

Lemma am_grow_refl : forall h, am_grow h h.
Proof. intros h. unfold am_grow. repeat split; auto; lia. Qed.

Definition am_room (A : astate) (s : mstate) : Prop :=
  0 < spare A \/
  (vm_backed_bytes (ms_vm s) + 4096 <= vm_limit (ms_vm s) /\
   (0 < a_ctx A KAac \/ exists a, grant_ok_na_vm (ms_vm s) a (2 ^ (a_ctx A KShift + 13)) = true)).

(* [comment removed for export] *)
Definition muse (A : astate) : Z := 101 * Z.of_nat (length (a_areas A)) - spare A.

Lemma spare_nn : forall A, WF A -> 0 <= spare A.
Proof. intros A HW. unfold spare. pose proof (wf_ctx_nonneg A HW KAmc). lia. Qed.

Lemma spare_same : forall A A', a_freelist A' = a_freelist A -> a_ctx A' KAmc = a_ctx A KAmc -> spare A' = spare A.
Proof. intros A A' E1 E2. unfold spare. rewrite E1, E2. reflexivity. Qed.

(* [comment removed for export] *)
Record sgrow (dc db da : Z) (A A' : astate) (h h' : VmMaps) : Prop := {
  sg_count : Z.of_nat (length (vm_maps h')) <= Z.of_nat (length (vm_maps h)) + dc;
  sg_backed : vm_backed_bytes h' <= vm_backed_bytes h + db;
  sg_areas : Z.of_nat (length (a_areas A')) <= Z.of_nat (length (a_areas A)) + da;
  sg_isp : vm_init_sp h' = vm_init_sp h;
  sg_res : vm_reserved h' = vm_reserved h;
  sg_lim : vm_limit h' = vm_limit h;
  (* [comment removed for export] *)
  sg_da0 : 0 <= da;
  sg_muse : muse A' <= muse A + da;
  sg_amax : 101 * (Z.of_nat (length (a_areas A')) - 1) <= Z.max (101 * (Z.of_nat (length (a_areas A)) - 1)) (muse A + da);
  (* [comment removed for export] *)
  sg_cpot : Z.of_nat (length (vm_maps h')) - Z.of_nat (length (a_areas A')) <=
            Z.of_nat (length (vm_maps h)) - Z.of_nat (length (a_areas A)) + (dc - da)
}.

Lemma sgrow_refl : forall A h, sgrow 0 0 0 A A h h.
Proof. intros A h. constructor; auto; lia. Qed.

(* [comment removed for export] *)
Lemma sgrow_same : forall A A' h h', h' = h -> a_areas A' = a_areas A -> spare A <= spare A' -> sgrow 0 0 0 A A' h h'.
Proof. intros A A' h h' -> E Hs. constructor; auto; unfold muse; rewrite ?E; lia. Qed.

Lemma sgrow_trans : forall c1 b1 a1 c2 b2 a2 A B C h1 h2 h3,
  sgrow c1 b1 a1 A B h1 h2 -> sgrow c2 b2 a2 B C h2 h3 -> sgrow (c1 + c2) (b1 + b2) (a1 + a2) A C h1 h3.
Proof.
  intros c1 b1 a1 c2 b2 a2 A B C h1 h2 h3 [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10] [Y1 Y2 Y3 Y4 Y5 Y6 Y7 Y8 Y9 Y10].
  constructor; try lia; congruence.
Qed.

Lemma sgrow_weaken : forall c b a c' b' a' A A' h h',
  sgrow c b a A A' h h' -> c <= c' -> b <= b' -> a <= a' -> c - a <= c' - a' -> sgrow c' b' a' A A' h h'.
Proof. intros c b a c' b' a' A A' h h' [X1 X2 X3 X4 X5 X6 X7 X8 X9 X10] Hc Hb Ha Hca. constructor; try lia; assumption. Qed.

(* [comment removed for export] *)
Lemma sgrow_am : forall A A' h h' pg, am_grow h h' ->
  ((0 < spare A /\ h' = h /\ a_areas A' = a_areas A /\ spare A' = spare A - 1)
   \/ (spare A = 0 /\ a_areas A' = a_areas A ++ [pg] /\ a_ctx A' KAmc = 100 /\ a_freelist A' = [])) ->
  sgrow 1 8192 1 A A' h h'.
Proof.
  intros A A' h h' pg (G1 & G2 & G3 & G4 & G5) [(Hs & Eh & E & Hs') | (Hs & E & Hc & Hf)].
  - subst h'. constructor; try reflexivity; unfold muse; rewrite ?E; lia.
  - assert (Hs' : spare A' = 100) by (unfold spare; rewrite Hc, Hf; reflexivity).
    constructor; try assumption; unfold muse; rewrite ?E, ?length_app; cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Lemma sgrow_am_fail : forall A A' h h', am_grow h h' -> spare A = 0 -> a_areas A' = a_areas A -> 0 <= spare A' ->
  sgrow 1 8192 0 A A' h h'.
Proof.
  intros A A' h h' (G1 & G2 & G3 & G4 & G5) Hs E Hs'. constructor; try assumption; unfold muse; rewrite ?E; lia.
Qed.

(* [comment removed for export] *)
Definition refusalP (M : Z) (h : VmMaps) : Prop :=
  exists len, 0 < len <= M /\ len mod 4096 = 0 /\ forall a, mmap_grant_ok MMrw h a len = false.

Lemma refusalP_weaken : forall M M' h, refusalP M h -> M <= M' -> refusalP M' h.
Proof. intros M M' h (len & H1 & H2 & H3) HM. exists len. split; [lia|]. split; assumption. Qed.

(* [comment removed for export] *)
Fixpoint lsum (l : list (Z * Z)) : Z :=
  match l with [] => 0 | (_, n) :: r => Z.max 0 n + lsum r end.

(* [comment removed for export] *)
Definition snoroom (sp0 : word) (argv envp : list (list byte)) (cb : list byte)
    (dc db da dx M : Z) (A : astate) (s : mstate) : Prop :=
  exists D1 A1 s1, II sp0 argv envp cb D1 A1 s1 /\ sgrow dc db da A A1 (ms_vm s) (ms_vm s1) /\
                   lsum (a_xmaps A1) <= lsum (a_xmaps A) + dx /\
                   (~ am_room A1 s1 \/
                    exists len, 0 < len <= M /\ len mod 4096 = 0 /\
                                vm_backed_bytes (ms_vm s1) + len <= vm_backed_bytes (ms_vm s) + db /\
                                forall a, mmap_grant_ok MMrw (ms_vm s1) a len = false).

Lemma snoroom_weaken : forall sp0 argv envp cb c b a x M c' b' a' x' M' A s,
  snoroom sp0 argv envp cb c b a x M A s -> c <= c' -> b <= b' -> a <= a' -> c - a <= c' - a' -> x <= x' -> M <= M' ->
  snoroom sp0 argv envp cb c' b' a' x' M' A s.
Proof.
  intros sp0 argv envp cb c b a x M c' b' a' x' M' A s (D1 & A1 & s1 & H1 & H2 & H3 & H4) Hc Hb Ha Hca Hx HM.
  exists D1, A1, s1. split; [exact H1|]. split; [exact (sgrow_weaken _ _ _ _ _ _ _ _ _ _ H2 Hc Hb Ha Hca)|]. split; [lia|].
  destruct H4 as [H4 | (len & L1 & L2 & L3 & L4)]; [left; exact H4 | right].
  exists len. split; [lia|]. split; [exact L2|]. split; [lia | exact L4].
Qed.

(* [comment removed for export] *)
Lemma snoroom_prefix : forall sp0 argv envp cb c0 b0 a0 x0 c b a x M A s B t,
  sgrow c0 b0 a0 A B (ms_vm s) (ms_vm t) -> lsum (a_xmaps B) <= lsum (a_xmaps A) + x0 ->
  snoroom sp0 argv envp cb c b a x M B t -> snoroom sp0 argv envp cb (c0 + c) (b0 + b) (a0 + a) (x0 + x) M A s.
Proof.
  intros sp0 argv envp cb c0 b0 a0 x0 c b a x M A s B t G0 Hx (D1 & A1 & s1 & H1 & H2 & H3 & H4).
  exists D1, A1, s1. split; [exact H1|]. split; [exact (sgrow_trans _ _ _ _ _ _ _ _ _ _ _ _ G0 H2)|]. split; [lia |].
  destruct H4 as [H4 | (len & L1 & L2 & L3 & L4)]; [left; exact H4 | right].
  exists len. split; [exact L1|]. split; [exact L2|]. split; [| exact L4].
  pose proof (sg_backed _ _ _ _ _ _ _ G0). lia.
Qed.

Definition alloc_meta_specX : Prop :=
  forall (W : wmode) (R : Type) (sp0 : word) (argv envp : list (list byte)) (cb : list byte) (D : list Z)
         (A : astate) (s : mstate) (sp : word) (K : word -> M R) (P : R -> mstate -> Prop),
    II sp0 argv envp cb D A s ->
    (* [comment removed for export] *)
    (forall s' A',
       II sp0 argv envp cb D A' s' -> FR A s A' s' -> gsame A A' -> AMvm A A' s s' ->
       a_xmaps A' = a_xmaps A -> (forall x, dom A' x <-> dom A x) ->
       spare A = 0 -> a_areas A' = a_areas A ->
       (W = WOk -> ~ am_budget A s) ->
       (* [comment removed for export] *)
       am_grow (ms_vm s) (ms_vm s') -> (W <> WFail -> ~ am_room A s) ->
       tsall W (K (Z_to_bv 64 0) s') P) ->
    (* [comment removed for export] *)
    (forall s' A' (m : Z),
       II sp0 argv envp cb (m :: D) A' s' -> FR A s A' s' -> got_meta A D A' m -> AMvm A A' s s' ->
       a_xmaps A' = a_xmaps A ->
       (W = WOk -> a_areas A = [] -> am_delta (ms_vm s) (ms_vm s')) ->
       ((0 < spare A /\ ms_vm s' = ms_vm s /\ a_areas A' = a_areas A /\ spare A' = spare A - 1)
        \/ (spare A = 0 /\ a_areas A' = a_areas A ++ [m - 24] /\ a_ctx A' KAmc = 100 /\ a_freelist A' = [])) ->
       (* [comment removed for export] *)
       am_grow (ms_vm s) (ms_vm s') ->
       tsall W (K (Z_to_bv 64 m) s') P) ->
    tsall W ((x <- m_alloc_meta sp ;; K x) s) P.

(* [comment removed for export] *)
Lemma alloc_meta_specX_spec : alloc_meta_specX -> alloc_meta_spec.
Proof.
  intros AX W R sp0 argv envp cb D A s sp K P HII HF HS.
  apply (AX W R sp0 argv envp cb D A s sp K P HII).
  - intros s' A' H1 H2 H3 H4 _ _ H5 H6 H7 _ _. exact (HF s' A' H1 H2 H3 H4 H5 H6 H7).
  - intros s' A' m H1 H2 H3 H4 _ _ H5 _. exact (HS s' A' m H1 H2 H3 H4 H5).
Qed.

End WithLayout.
