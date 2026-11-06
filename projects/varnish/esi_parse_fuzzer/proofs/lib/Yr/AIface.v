(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Frame Step Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
Definition mem := word -> option byte.

(* [comment removed for export] *)
Definition sh (a : Z) : Z := a / 8 + kShadowOffset.

(* [comment removed for export] *)
Definition shpat (n : Z) : list byte :=
  repeat (Z_to_bv 8 0) (Z.to_nat (n / 8)) ++
  (if Z.eqb (n mod 8) 0 then [] else [Z_to_bv 8 (n mod 8)]).

Lemma shpat_length : forall n, 0 <= n -> Z.of_nat (length (shpat n)) = (n + 7) / 8.
Proof.
  intros n Hn. unfold shpat. rewrite length_app, repeat_length.
  destruct (Z.eqb_spec (n mod 8) 0) as [E|E]; cbn [length]; rewrite ?Nat.add_0_r;
  rewrite ?Nat2Z.inj_add, Z2Nat.id by (apply Z.div_pos; lia);
  pose proof (Z.div_mod n 8 ltac:(lia)); pose proof (Z.mod_pos_bound n 8 ltac:(lia));
  [ rewrite <- (Z.div_unique_pos (n + 7) 8 (n / 8) 7) by lia; lia
  | cbn [Z.of_nat Pos.of_succ_nat]; rewrite <- (Z.div_unique_pos (n + 7) 8 (n / 8 + 1) (n mod 8 - 1)) by lia; lia ].
Qed.

(* [comment removed for export] *)
Definition fsize (k : Z) : Z := 64 * 2 ^ k.
Definition fslots (k : Z) : Z := 2 ^ (14 - k).

(* [comment removed for export] *)
Definition mapped (m : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> m (wz (a + i)) <> None.
Definition bytes_eq (m m' : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> m' (wz (a + i)) = m (wz (a + i)).
Definition all_zero (m : mem) (a n : Z) : Prop := forall i, 0 <= i < n -> m (wz (a + i)) = Some (Z_to_bv 8 0).

Definition blk (r n : Z) (a : Z) : Prop := r <> 0 /\ r <= a < r + n.
Definition ivl (lo hi : Z) (a : Z) : Prop := lo <= a < hi.
Definition nowhere (a : Z) : Prop := False.

(* [comment removed for export] *)
Definition ASTK : Z := 8192.
(* [comment removed for export] *)
Definition LIVE_MAX : Z := 2 ^ 31.          (* [comment removed for export] *)
Lemma LIVE_MAX_eq : LIVE_MAX = 2 ^ 31.
Proof. reflexivity. Qed.
#[global] Opaque LIVE_MAX.
Definition REQ_MAX : Z := 2 ^ 32.          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition TINYCRED0 : Z := 64.
Lemma TINYCRED0_eq : TINYCRED0 = 64.
Proof. reflexivity. Qed.
#[global] Opaque TINYCRED0.
Definition NLIVE_MAX : Z := 2 ^ 6.            (* [comment removed for export] *)
Lemma NLIVE_MAX_eq : NLIVE_MAX = 2 ^ 6.
Proof. reflexivity. Qed.
#[global] Opaque NLIVE_MAX.
(* [comment removed for export] *)
Definition NREQ_CAP : Z := 2 ^ 30.
Lemma NREQ_CAP_eq : NREQ_CAP = 2 ^ 30.
Proof. reflexivity. Qed.
#[global] Opaque NREQ_CAP.
(* [comment removed for export] *)
Definition SECCRED0 : Z := 400 * 1000.   (* [comment removed for export] *)
Lemma SECCRED0_eq : SECCRED0 = 400 * 1000.   (* [comment removed for export] *)
Proof. reflexivity. Qed.
#[global] Opaque SECCRED0.
(* [comment removed for export] *)
Definition prim_cost (n : Z) : Z := if Z.ltb kMaxPrimaryUser n then 0 else class_size (class_of n).
Lemma prim_cost_secondary : forall n, kMaxPrimaryUser < n -> prim_cost n = 0.
Proof. intros n H. unfold prim_cost. rewrite (proj2 (Z.ltb_lt _ _) H). reflexivity. Qed.
Lemma prim_cost_primary : forall n, n <= kMaxPrimaryUser -> prim_cost n = class_size (class_of n).
Proof. intros n H. unfold prim_cost. destruct (Z.ltb_spec kMaxPrimaryUser n); [lia| reflexivity]. Qed.
Lemma prim_cost_range : forall n, 0 <= n -> 0 <= prim_cost n <= 2 ^ 16 /\ (n <= kMaxPrimaryUser -> n <= prim_cost n).
Proof.
  intros n Hn. unfold prim_cost. destruct (Z.ltb_spec kMaxPrimaryUser n) as [L|L]; [lia|].
  pose proof (class_size_range (class_of n) (class_of_range n ltac:(lia))) as R. unfold kMaxSize in R.
  pose proof (class_of_fits n ltac:(lia)). pose proof (needed_size_ge n). lia.
Qed.
#[global] Opaque prim_cost.
Definition PRIMCRED0 : Z := 3225550464.
Lemma PRIMCRED0_eq : PRIMCRED0 = 3225550464.
Proof. reflexivity. Qed.
#[global] Opaque PRIMCRED0.

(* [comment removed for export] *)
Record clayout := mkCLayout {
  cl_segs : list Segment;
  cl_malloc_pc : word;            (* [comment removed for export] *)
  cl_free_pc : word;              (* [comment removed for export] *)
  cl_calloc_pc : word;            (* [comment removed for export] *)
  cl_realloc_pc : word;           (* [comment removed for export] *)
  cl_smalloc_pc : Z -> word;      (* [comment removed for export] *)
  cl_sfree_pc : Z -> word;        (* [comment removed for export] *)
  cl_tp : word;                   (* [comment removed for export] *)
  cl_errno : Z;                   (* [comment removed for export] *)
  cl_sites : list Z;              (* [comment removed for export] *)
  cl_image_lo : Z;                (* [comment removed for export] *)
  cl_rw_lo : Z;                   (* [comment removed for export] *)
  cl_image_hi : Z;
  cl_static : Z -> Prop;          (* [comment removed for export] *)
  cl_shared : Z -> Prop;          (* [comment removed for export] *)
  cl_consts : list (Z * list byte); (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition amd_frame (md md' : Model) : Prop :=
  m_fd md' = m_fd md /\ m_io md' = m_io md /\ m_fsys md' = m_fsys md /\ m_proc md' = m_proc md
  /\ m_lim md' = m_lim md /\ m_time md' = m_time md
  /\ vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)
  /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)
  /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md)
  /\ vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md)
  /\ m_halted md' = None.
(* [comment removed for export] *)

Lemma amd_frame_refl : forall md, m_halted md = None -> amd_frame md md.
Proof. intros md H. unfold amd_frame. repeat split; auto. Qed.

Lemma amd_frame_trans : forall a b c, amd_frame a b -> amd_frame b c -> amd_frame a c.
Proof.
  intros a b c H1 H2. unfold amd_frame in *.
  decompose [and] H1. decompose [and] H2.
  repeat split; congruence.
Qed.

Section WithLayout.
Context {Clg : Ceiling} (L : clayout).   (* [comment removed for export] *)

Let segs := cl_segs L.
Let rom := seg_rom (cl_segs L).

Definition in_image (a : Z) : Prop := cl_image_lo L <= a < cl_image_hi L.
Definition heap_zone (a : Z) : Prop := 0 <= a < alloc_ceiling /\ ~ in_image a.

(* [comment removed for export] *)
Definition kLowAppEnd : Z := kLowShadowMapBeg.
Definition app_lo (p n : Z) : Prop :=
  4096 <= p /\ 0 <= n /\ p + n <= kLowAppEnd /\ (p + n <= cl_image_lo L \/ cl_image_hi L <= p).
Definition app_hi (p n : Z) : Prop := kHighMemBeg <= p /\ 0 <= n /\ p + n <= alloc_ceiling.
Definition app_range (p n : Z) : Prop := app_lo p n \/ app_hi p n.
(* [comment removed for export] *)
Definition shadow_apart (p n : Z) : Prop := p + n <= sh p \/ sh p + (n + 7) / 8 <= p.
(* [comment removed for export] *)
Definition app_noshadow (p n : Z) : Prop := p + n <= kLowShadowMapBeg \/ kHighMemBeg <= p.

Lemma app_range_sub : forall p n p' n', app_range p n -> p <= p' -> 0 <= n' -> p' + n' <= p + n -> app_range p' n'.
Proof. unfold app_range, app_lo, app_hi. intros. lia. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition aview_of (H : hull) (m : mem) : mem := mrestrict (hidc H) m.

(* [comment removed for export] *)
Definition frame_ok (owned owned' : Z -> Prop) (sp win : Z) (victim newb : Z -> Prop) (v v' : mem) : Prop :=
     (forall a, 0 <= a < 2^64 -> ~ owned a -> ~ owned' a -> ~ (sp - win <= a < sp) ->
                ~ (cl_errno L <= a < cl_errno L + 4) -> ~ victim a -> ~ newb a -> v' (wz a) = v (wz a))
  /\ (forall a, 0 <= a < 2^64 -> ~ in_image a -> v (wz a) <> None -> owned a \/ victim a \/ v' (wz a) <> None)
  /\ mapped v' (sp - win) win
  /\ (forall a, 0 <= a < 2^64 -> newb a -> owned a \/ victim a \/ (v (wz a) = None /\ heap_zone a))
  /\ (forall a, 0 <= a < 2^64 -> owned' a -> owned a \/ victim a \/ (v (wz a) = None /\ heap_zone a))
  /\ (forall a, 0 <= a < 2^64 -> owned a -> ~ owned' a -> newb a \/ v' (wz a) = None)
  /\ (forall a, 0 <= a < 2^64 -> victim a -> owned' a \/ newb a \/ v' (wz a) = None).

(* [comment removed for export] *)
Definition newblk (r n : Z) (a : Z) : Prop := blk r n a \/ (r <> 0 /\ sh r <= a < sh r + (n + 7) / 8).
(* [comment removed for export] *)
Definition frm (ff k : Z) (a : Z) : Prop := (ff <= a < ff + fsize k) \/ (sh ff <= a < sh ff + fsize k / 8).

(* [comment removed for export] *)
(* [comment removed for export] *)

Class AsanAlloc := {
  (* [comment removed for export] *)
  AS : Type;
  (* [comment removed for export] *)
  a_live : AS -> Z -> option Z;
  (* [comment removed for export] *)
  a_frame : AS -> Z -> option (Z * nat);
  (* [comment removed for export] *)
  a_livebytes : AS -> Z;
  (* [comment removed for export] *)
  a_tinycred : AS -> Z;
  a_seccred : AS -> Z;     (* [comment removed for export] *)
  a_primcred : AS -> Z;    (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_nlive : AS -> Z;
  (* [comment removed for export] *)
  ahull : AS -> hull;
  alhull : AS -> hull;    (* [comment removed for export] *)
  aeager : AS -> Z;
  (* [comment removed for export] *)
  ainv : AS -> mem -> Model -> Prop;
  (* [comment removed for export] *)
  owned : AS -> Z -> Prop;

  (* [comment removed for export] *)
  as_static_owned : forall A a, cl_static L a -> owned A a;
  as_static_where : forall a, cl_static L a -> cl_rw_lo L <= a < cl_image_hi L;
  as_shared_where : forall a, cl_shared L a -> cl_rw_lo L <= a < cl_image_hi L;
  as_shared_not_static : forall a, cl_shared L a -> ~ cl_static L a;
  as_errno_where : cl_rw_lo L <= cl_errno L /\ cl_errno L + 4 <= cl_image_hi L;
  as_errno_not_static : forall i, 0 <= i < 4 -> ~ cl_static L (cl_errno L + i) /\ ~ cl_shared L (cl_errno L + i);
  as_layout_order : 4096 <= cl_image_lo L <= cl_rw_lo L /\ cl_rw_lo L <= cl_image_hi L
                    /\ cl_image_hi L <= kLowShadowMapBeg /\ kHighMemBeg + 65536 <= alloc_ceiling;
  as_ro_addr_iff : forall a : word, ro_addr segs a = true <-> cl_image_lo L <= bv_unsigned a < cl_rw_lo L;
  as_seg_rom_outside : forall a : word, ~ in_image (bv_unsigned a) -> seg_rom segs a = None;
  as_find_segment_outside : forall a : word, ~ in_image (bv_unsigned a) -> find_segment segs (bv_unsigned a) 1 = None;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_minv : forall A m md, ainv A m md -> MInv (ahull A) (alhull A) (aeager A) md /\ m_halted md = None;
  as_hull_segs : forall A m md, ainv A m md -> H_off_segments segs (hidc (ahull A));
  as_wx : wx_segs_nowrap segs;
  (* [comment removed for export] *)
  as_image_visible : forall A m md a, ainv A m md -> in_image a -> hidc (ahull A) (wz a) = false;
  (* [comment removed for export] *)
  as_shadow_visible : forall A m md a, ainv A m md ->
      (0 <= a <= kLowMemEnd \/ kHighMemBeg <= a < 2^47) ->
      ~ owned A a -> (in_image a \/ aview_of (ahull A) m (wz a) <> None) ->
      mapped (aview_of (ahull A) m) (sh a - sh a mod 8) 8;
  (* [comment removed for export] *)
  as_consts : forall A m md, ainv A m md ->
      Forall (fun c => bytes_at segs (aview_of (ahull A) m) (fst c) (snd c)) (cl_consts L);
  (* [comment removed for export] *)
  as_owned_where : forall A m md a, ainv A m md -> owned A a -> cl_static L a \/ heap_zone a;
  (* [comment removed for export] *)
  as_owned_not_stack_shadow : forall A m md a, ainv A m md ->
      sh alloc_ceiling <= a < kHighMemBeg -> ~ owned A a;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_live_ok : forall A m md p n, ainv A m md -> a_live A p = Some n ->
      0 <= n < REQ_MAX /\ p mod 16 = 0 /\ app_range p n /\ p + n <= alloc_ceiling /\
      ~ in_image p /\ mapped (aview_of (ahull A) m) p n /\
      (forall i, 0 <= i < n -> ~ owned A (p + i)) /\
      (forall i, 0 <= i < (n + 7) / 8 -> owned A (sh p + i));
  (* [comment removed for export] *)
  as_live_primary_high : forall A m md p n, ainv A m md -> a_live A p = Some n ->
      n <= kMaxPrimaryUser -> kHighMemBeg <= p;
  as_live_shadow : forall A m md p n, ainv A m md -> a_live A p = Some n ->
      bytes_at segs (aview_of (ahull A) m) (sh p) (shpat n);
  as_live_disjoint : forall A m md p n q k, ainv A m md ->
      a_live A p = Some n -> a_live A q = Some k -> p <> q -> p + n <= q \/ q + k <= p;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_frame_ok : forall A m md ff k age, ainv A m md -> a_frame A ff = Some (k, age) ->
      0 <= k <= 10 /\ ff mod Z.min (fsize k) 4096 = 0 /\ app_range ff (fsize k) /\ ff + fsize k <= alloc_ceiling /\
      ~ in_image ff /\
      wr_at segs (aview_of (ahull A) m) ff (fsize k - 8) /\ mapped (aview_of (ahull A) m) ff (fsize k) /\
      wr_at segs (aview_of (ahull A) m) (sh ff) (fsize k / 8) /\ mapped (aview_of (ahull A) m) (sh ff) (fsize k / 8) /\
      (forall i, 0 <= i < fsize k - 8 -> ~ owned A (ff + i)) /\
      (forall i, 0 <= i < fsize k / 8 -> ~ owned A (sh ff + i));
  as_frame_blk_disjoint : forall A m md ff k age p n, ainv A m md ->
      a_frame A ff = Some (k, age) -> a_live A p = Some n -> ff + fsize k <= p - 16 \/ p + n <= ff;
  as_frame_disjoint : forall A m md ff k age ff' k' age', ainv A m md ->
      a_frame A ff = Some (k, age) -> a_frame A ff' = Some (k', age') -> ff <> ff' ->
      ff + fsize k <= ff' \/ ff' + fsize k' <= ff;
  (* [comment removed for export] *)
  as_sframe_flag : forall A m md ff k age, ainv A m md -> a_frame A ff = Some (k, age) ->
      exists fa, bytes_at segs (aview_of (ahull A) m) (ff + fsize k - 8) (le8 (wz fa))
        /\ owned A fa /\ ~ in_image fa /\ wr_at segs (aview_of (ahull A) m) fa 1
        /\ (forall ff' k' age', a_frame A ff' = Some (k', age') -> ff' <> ff ->
              forall fa', bytes_at segs (aview_of (ahull A) m) (ff' + fsize k' - 8) (le8 (wz fa')) -> fa' <> fa);

  (* [comment removed for export] *)
  a_release : AS -> Z -> AS;
  as_release_spec : forall A m md ff k age, ainv A m md -> a_frame A ff = Some (k, age) ->
      a_frame (a_release A ff) ff = None
      /\ (forall g, g <> ff -> a_frame (a_release A ff) g = a_frame A g)
      /\ (forall q, a_live (a_release A ff) q = a_live A q)
      /\ a_livebytes (a_release A ff) = a_livebytes A /\ a_tinycred (a_release A ff) = a_tinycred A
      /\ a_seccred (a_release A ff) = a_seccred A
      /\ a_primcred (a_release A ff) = a_primcred A     (* [comment removed for export] *)
      /\ a_nlive (a_release A ff) = a_nlive A
      /\ ahull (a_release A ff) = ahull A /\ aeager (a_release A ff) = aeager A
      /\ (forall a, owned (a_release A ff) a <->
            (owned A a \/ ff <= a < ff + fsize k - 8 \/ sh ff <= a < sh ff + fsize k / 8));

  (* [comment removed for export] *)
  as_frame : forall A (rel : list Z) m m' md md',
      ainv A m md ->
      (forall ff, In ff rel -> exists k age, a_frame A ff = Some (k, age)) -> NoDup rel ->
      let A' := fold_left a_release rel A in
      let v := aview_of (ahull A) m in let v' := aview_of (ahull A) m' in
      (forall a : word, hidc (ahull A) a = true -> m' a = m a) ->
      (forall a, owned A a ->
          v' (wz a) = v (wz a)
          \/ (exists ff k age fa, In ff rel /\ a_frame A ff = Some (k, age) /\ a = fa /\
                bytes_at segs v (ff + fsize k - 8) (le8 (wz fa)) /\ v' (wz a) = Some (Z_to_bv 8 0))) ->
      (forall ff k age fa, In ff rel -> a_frame A ff = Some (k, age) ->
          bytes_at segs v (ff + fsize k - 8) (le8 (wz fa)) -> v' (wz fa) = Some (Z_to_bv 8 0)) ->
      (forall a, cl_shared L a -> v' (wz a) = v (wz a)) ->
      (forall a, 0 <= a < 2^64 -> ~ in_image a -> v (wz a) <> None -> v' (wz a) <> None) ->
      (forall a, 0 <= a < 2^64 -> ~ in_image a -> v' (wz a) <> None -> v (wz a) <> None) ->
      MInv (ahull A) (alhull A) (aeager A) md' -> same_but_materialized md md' ->
      ainv A' m' md';

  (* [comment removed for export] *)
  as_md_frame : forall A m md md', ainv A m md ->
      m_vm md' = m_vm md -> m_halted md' = None -> MInv (ahull A) (alhull A) (aeager A) md' -> ainv A m md';

  (* [comment removed for export] *)
  as_malloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (n : Z) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      a0 = wz n -> 1 <= n < REQ_MAX -> n <= NREQ_CAP ->
      a_livebytes A + n <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> (n < 16 -> 1 <= a_tinycred A) ->
      (kMaxPrimaryUser < n -> 1 <= a_seccred A) -> prim_cost n <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites L) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          hull_le (ahull A) (ahull A') ->
          (forall ff, a_frame A' ff = a_frame A ff) ->
          a_tinycred A' = a_tinycred A - (if Z.ltb n 16 then 1 else 0) ->
          (   (r = 0 /\ (forall q, a_live A' q = a_live A q) /\ a_livebytes A' = a_livebytes A /\
               a_nlive A' = a_nlive A /\ a_seccred A' = a_seccred A /\ a_primcred A' = a_primcred A)
           \/ (r <> 0 /\ a_live A r = None /\ a_live A' r = Some n /\
               (forall q, q <> r -> a_live A' q = a_live A q) /\
               a_livebytes A' = a_livebytes A + n /\ a_nlive A' = a_nlive A + 1 /\
               a_seccred A' = a_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               a_primcred A' = a_primcred A - prim_cost n (* [comment removed for export] *))) ->
          frame_ok (owned A) (owned A') (bv_unsigned sp) ASTK nowhere (newblk r n)
                   (aview_of (ahull A) m) v' ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_malloc_pc L) fc None m rom) md) T;

  (* [comment removed for export] *)
  as_free_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (p n0 : Z) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      a0 = wz p -> ((p = 0 /\ n0 = 0) \/ a_live A p = Some n0) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites L) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          hull_le (ahull A) (ahull A') \/ True ->     (* [comment removed for export] *)
          (forall ff, a_frame A' ff = a_frame A ff) ->
          a_live A' p = None -> (forall q, q <> p -> a_live A' q = a_live A q) ->
          a_livebytes A' = a_livebytes A - n0 -> a_tinycred A' = a_tinycred A -> a_seccred A' = a_seccred A ->
          a_primcred A' = a_primcred A (* [comment removed for export] *) ->
          a_nlive A' = a_nlive A - (if Z.eqb p 0 then 0 else 1) ->
          (forall i, 0 <= i < 4 -> mrd segs v' (wz (cl_errno L + i)) = mrd segs v (wz (cl_errno L + i))) ->
          frame_ok (owned A) (owned A') (bv_unsigned sp) ASTK (newblk p n0) nowhere
                   (aview_of (ahull A) m) v' ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_free_pc L) fc None m rom) md) T;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_calloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (cnt sz : Z) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      a0 = wz cnt -> a1 = wz sz -> 0 <= cnt < REQ_MAX -> 0 <= sz < REQ_MAX -> 1 <= cnt * sz < REQ_MAX -> cnt * sz <= NREQ_CAP ->
      a_livebytes A + cnt * sz <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> (cnt * sz < 16 -> 1 <= a_tinycred A) ->
      (kMaxPrimaryUser < cnt * sz -> 1 <= a_seccred A) -> prim_cost (cnt * sz) <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites L) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          hull_le (ahull A) (ahull A') ->
          (forall ff, a_frame A' ff = a_frame A ff) ->
          a_tinycred A' = a_tinycred A - (if Z.ltb (cnt * sz) 16 then 1 else 0) ->
          (   (r = 0 /\ (forall q, a_live A' q = a_live A q) /\ a_livebytes A' = a_livebytes A /\
               a_nlive A' = a_nlive A /\ a_seccred A' = a_seccred A /\ a_primcred A' = a_primcred A)
           \/ (r <> 0 /\ a_live A r = None /\ a_live A' r = Some (cnt * sz) /\
               (forall q, q <> r -> a_live A' q = a_live A q) /\ all_zero v' r (cnt * sz) /\
               a_livebytes A' = a_livebytes A + cnt * sz /\ a_nlive A' = a_nlive A + 1 /\
               a_seccred A' = a_seccred A - (if Z.ltb kMaxPrimaryUser (cnt * sz) then 1 else 0) /\
               a_primcred A' = a_primcred A - prim_cost (cnt * sz) (* [comment removed for export] *))) ->
          frame_ok (owned A) (owned A') (bv_unsigned sp) ASTK nowhere (newblk r (cnt * sz))
                   (aview_of (ahull A) m) v' ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_calloc_pc L) fc None m rom) md) T;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_realloc_cps :
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (p n old : Z) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      a0 = wz p -> a1 = wz n -> 1 <= n < REQ_MAX -> n <= NREQ_CAP -> p <> 0 -> a_live A p = Some old ->
      a_livebytes A + n <= LIVE_MAX -> a_nlive A + 1 <= NLIVE_MAX -> (n < 16 -> 1 <= a_tinycred A) ->
      (kMaxPrimaryUser < n -> 1 <= a_seccred A) -> prim_cost n <= a_primcred A (* [comment removed for export] *) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
      In (bv_unsigned ra) (cl_sites L) -> bv_unsigned s0 < alloc_ceiling ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          (forall ff, a_frame A' ff = a_frame A ff) ->
          a_tinycred A' = a_tinycred A - (if Z.ltb n 16 then 1 else 0) -> a_nlive A' = a_nlive A ->
          (   (* [comment removed for export] *)
              (r = 0 /\ hull_le (ahull A) (ahull A') /\ (forall q, a_live A' q = a_live A q) /\
               a_livebytes A' = a_livebytes A /\
               bytes_eq v v' p old /\
               frame_ok (owned A) (owned A') (bv_unsigned sp) ASTK nowhere nowhere (aview_of (ahull A) m) v' /\
               a_seccred A' = a_seccred A /\ a_primcred A' = a_primcred A (* [comment removed for export] *))
              (* [comment removed for export] *)
           \/ (r <> 0 /\ r <> p /\ a_live A r = None /\ a_live A' r = Some n /\ a_live A' p = None /\
               (forall q, q <> r -> q <> p -> a_live A' q = a_live A q) /\
               a_livebytes A' = a_livebytes A + n - old /\
               (forall i, 0 <= i < Z.min n old -> v' (wz (r + i)) = v (wz (p + i))) /\
               frame_ok (owned A) (owned A') (bv_unsigned sp) ASTK (newblk p old) (newblk r n)
                        (aview_of (ahull A) m) v' /\
               a_seccred A' = a_seccred A - (if Z.ltb kMaxPrimaryUser n then 1 else 0) /\
               a_primcred A' = a_primcred A - prim_cost n (* [comment removed for export] *))) ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz r) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F ra fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_realloc_pc L) fc None m rom) md) T;

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  as_smalloc_cps :
    forall (k : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (sz : Z) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      (k = 0 \/ k = 1 \/ k = 7) (* [comment removed for export] *) -> a0 = wz sz -> 0 < sz <= fsize k (* [comment removed for export] *) ->
      (7 <= k -> sz mod 8 = 0) (* [comment removed for export] *) ->
      (forall ff age, a_frame A ff = Some (k, age) -> Z.of_nat age + 2 < fslots k) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (ff : Z) (A' : AS) (m' : mem) (md' : Model),
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          ahull A' = ahull A -> aeager A' = aeager A ->
          (forall q, a_live A' q = a_live A q) -> a_livebytes A' = a_livebytes A ->
          a_tinycred A' = a_tinycred A -> a_nlive A' = a_nlive A -> a_seccred A' = a_seccred A -> a_primcred A' = a_primcred A (* [comment removed for export] *) ->
          ff <> 0 -> a_frame A ff = None -> a_frame A' ff = Some (k, 0%nat) ->
          (forall g k' age', g <> ff -> a_frame A g = Some (k', age') ->
              a_frame A' g = Some (k', if Z.eqb k' k then S age' else age')) ->
          (forall g, g <> ff -> a_frame A g = None -> a_frame A' g = None) ->
          all_zero v' (sh ff) (if Z.leb k 6 then fsize k / 8 else sz / 8) ->
          frame_ok (owned A) (owned A') (bv_unsigned sp) ASTK nowhere (frm ff k) (aview_of (ahull A) m) v' ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (wz ff) a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_smalloc_pc L k) fc None m rom) md) T;

  (* [comment removed for export] *)
  as_sfree_cps :
    forall (k : Z) (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (md : Model) (A : AS) (ff sz : Z) (age : nat) (T : TSet),
      let v := aview_of (ahull A) m in
      ainv A m md -> mem_inv segs v ->
      k = 7 (* [comment removed for export] *) -> a0 = wz ff -> a1 = wz sz -> 0 < sz <= fsize k -> (7 <= k -> sz mod 8 = 0) ->
      a_frame A ff = Some (k, age) ->
      tp = cl_tp L -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 2 = 0 ->
      alloc_ceiling <= bv_unsigned sp - ASTK ->
      mapped v (bv_unsigned sp - ASTK) ASTK ->
      (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem) (md' : Model),
          let A' := a_release A ff in
          let v' := aview_of (ahull A') m' in
          ainv A' m' md' -> mem_inv segs v' -> amd_frame md md' ->
          frame_ok (owned A) (owned A') (bv_unsigned sp) ASTK (frm ff k) nowhere (aview_of (ahull A) m) v' ->
          srealizes segs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                        s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' rom) md') T) ->
      srealizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (cl_sfree_pc L k) fc None m rom) md) T
}.

End WithLayout.

Arguments AS {Clg L AI} : rename.
Arguments a_live {Clg L AI} : rename.
Arguments a_frame {Clg L AI} : rename.
Arguments a_livebytes {Clg L AI} : rename.
Arguments a_tinycred {Clg L AI} : rename.
Arguments a_seccred {Clg L AI} : rename.
Arguments a_primcred {Clg L AI} : rename.
Arguments a_nlive {Clg L AI} : rename.
Arguments ahull {Clg L AI} : rename.
Arguments alhull {Clg L AI} : rename.
Arguments aeager {Clg L AI} : rename.
Arguments ainv {Clg L AI} : rename.
Arguments owned {Clg L AI} : rename.
Arguments a_release {Clg L AI} : rename.

(* [comment removed for export] *)
Definition aview {Clg : Ceiling} {L} {AI : AsanAlloc L} (A : AS) (m : mem) : mem := aview_of (ahull A) m.
