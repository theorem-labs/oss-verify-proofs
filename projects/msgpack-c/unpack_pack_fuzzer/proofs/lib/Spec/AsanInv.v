(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanCtrlProps.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Definition AIMG_HI : Z := 0x6a6000.
Definition RES_HI : Z := 0x7fff7000.
Definition ACEIL : Z := 0x7fff7f800000.
Definition ATOP_MAX : Z := 0x7FFFFF800000.
Definition KHIGH : Z := 0x10007fff8000.
Definition LS_LO : Z := 0x7fff7000.
Definition LS_SZ : Z := 0x10000000.
Definition GAP_LO : Z := 0x8fff7000.
Definition GAP_SZ : Z := 0x20000000000.
Definition HS_LO : Z := 0x2008fff7000.
Definition HS_SZ : Z := 0xdfff0001000.
Definition PRIM_SZ : Z := 0x2000011000.
Definition PTR_SZ : Z := 0x800000.
Definition EAGER0 : Z := 2^25.
Definition TOT0 : Z := 2^45.
Definition RTOT0 : Z := 2^30.
Definition LEN0 : Z := 32.
Definition LIMIT : Z := 0x8000000000.

Lemma ACEIL_eq : ACEIL = ALLOC_TOP_MIN. Proof. reflexivity. Qed.

Definition atop_ok (ATOP : Z) : Prop := ACEIL <= ATOP <= ATOP_MAX.
Lemma LIMIT_eq : LIMIT = target_alloc_limit. Proof. reflexivity. Qed.

Definition is_prim_of (c : Z) (ch : achunk) : bool := match ch with CPrim c' _ => c' =? c | CSec _ _ _ => false end.
Definition sec_of (ch : achunk) : list (Z * Z) := match ch with CSec mb ms _ => [(mb, ms)] | CPrim _ _ => [] end.

Definition zlen {A} (l : list A) : Z := Z.of_nat (length l).
Definition cntP (c : Z) (l : list achunk) : Z := zlen (List.filter (is_prim_of c) l).
Definition secs (l : list achunk) : list (Z * Z) := flat_map sec_of l.

Definition live_chunks (st : astate) : list achunk := map snd (map_to_list (a_live st)).
Definition qchunks (bs : list abatch) : list achunk := flat_map b_chunks bs.
Definition qbatches (pb : list abatch) (st : astate) : list abatch := pb ++ a_qloc st ++ a_qglob st.
Definition all_chunks (pc : list achunk) (pb : list abatch) (st : astate) : list achunk :=
  pc ++ live_chunks st ++ qchunks (qbatches pb st).

Definition CH (pc : list achunk) (pb : list abatch) (st : astate) : list (Z * Z) := secs (all_chunks pc pb st).

Definition nbatch (c : Z) (bs : list abatch) : Z := if c =? K_BATCH_CLASS then zlen bs else 0.

Fixpoint zsumc (l : list achunk) : Z := match l with [] => 0 | ch :: l' => chunk_size ch + zsumc l' end.
Fixpoint bsum (bs : list abatch) : Z := match bs with [] => 0 | b :: bs' => b_size b + bsum bs' end.

Definition chunk_wf (ATOP : Z) (ch : achunk) : Prop :=
  match ch with
  | CPrim c n => 0 <= n <= 64512 /\ prim_cls_ok c n
  | CSec mb ms n => 64512 < n <= 2^32 - 2^20 /\ ms = sec_map_size n /\ mb mod 4096 = 0 /\ 0 < mb
                   /\ (mb + ms <= LS_LO \/ (KHIGH <= mb /\ mb + ms <= ATOP))
  end.

Definition batch_wf (b : abatch) : Prop :=
  b_count b = zlen (b_chunks b) /\ b_count b <= Q_BATCH /\ b_size b = Q_BATCH_BYTES + zsumc (b_chunks b)
  /\ Forall (fun ch => 0 <= chunk_size ch <= Q_MAX) (b_chunks b).

Definition L24MAX : Z := 2^21.
Definition SMAX : Z := 800000.
Definition LSBYTES : Z := 3 * 2^34.
Definition EMB_MAX : Z := 2^23.

Fixpoint secbytes (l : list achunk) : Z :=
  match l with [] => 0 | CSec _ _ n :: l' => n + secbytes l' | CPrim _ _ :: l' => secbytes l' end.

Definition live_budget (st : astate) : Prop :=
  size_of_class K_BATCH_CLASS * cntP K_BATCH_CLASS (live_chunks st) <= L24MAX
  /\ zlen (secs (live_chunks st)) <= SMAX
  /\ secbytes (live_chunks st) <= LSBYTES.

Definition emb_ent (st : astate) : list (Z * Z) := let '(d, cap, _) := a_emb st in if cap =? 0 then [] else [(d, cap)].
Definition emb_ok (ATOP : Z) (st : astate) : Prop :=
  let '(d, cap, sz) := a_emb st in
  (cap = 0 /\ sz = 0) \/
  (EMB_INIT <= cap <= EMB_MAX /\ cap mod 4096 = 0 /\ d mod 4096 = 0 /\ 0 < d /\ 0 <= sz <= cap
   /\ (d + cap <= LS_LO \/ (KHIGH <= d /\ d + cap <= ATOP))).

Definition cls_inv (pc : list achunk) (pb : list abatch) (st : astate) (c : Z) : Prop :=
  let r := get_cls st c in
  0 <= c_allocated_user r /\ c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
  /\ c_mapped_user r - c_allocated_user r <= 2 * K_USER_MAP
  /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
  /\ 0 <= c_num_freed r /\ 0 <= c_count r <= max_count st c
  /\ c_allocated_user r = size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + c_count r + c_num_freed r).

Definition AINV (ATOP : Z) (pc : list achunk) (pb : list abatch) (st : astate) : Prop :=
  (forall c, 1 <= c <= 31 -> cls_inv pc pb st c)
  /\ Forall (chunk_wf ATOP) (all_chunks pc pb st)
  /\ Forall batch_wf (qbatches pb st)
  /\ a_qloc_bytes st = bsum (a_qloc st) /\ a_qglob_bytes st = bsum (a_qglob st)
  /\ a_nsec st = zlen (CH pc pb st)
  /\ (exists j, 0 <= j <= 64 /\ a_nres st = j * K_CHUNKS_BLOCK)
  /\ (forall id ch, (a_live st) !! id = Some ch -> (id < a_next st)%N)
  /\ a_space_beg st mod 65536 = 0 /\ 0 < a_space_beg st /\ a_ptr_array st mod 4096 = 0 /\ 0 < a_ptr_array st
  /\ live_budget st
  /\ emb_ok ATOP st.

Definition went (e : Z * Z) : word * word := (Z_to_bv 64 (fst e), Z_to_bv 64 (snd e)).

Definition Pm (mo : Model) (x : Z) : bool := negb (covered (vm_noaccess (m_vmmaps mo) ++ m_vm_lazy mo) x).

Definition wsep (p q : word * word) : Prop :=
  bv_unsigned (fst p) + bv_unsigned (snd p) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst p).
Inductive seps : list (word * word) -> Prop :=
| seps_nil : seps []
| seps_cons : forall p l, Forall (wsep p) l -> seps l -> seps (p :: l).

Definition entry_ok (ATOP : Z) (e : word * word) : Prop :=
  0 < bv_unsigned (snd e) /\ bv_unsigned (fst e) mod 4096 = 0 /\ bv_unsigned (snd e) mod 4096 = 0
  /\ bv_unsigned (fst e) + bv_unsigned (snd e) <= ATOP.

Definition CLASSES : list Z := map Z.of_nat (seq 1 31).
Definition csum (f : aclass -> Z) (st : astate) : Z := fold_right (fun c acc => f (get_cls st c) + acc) 0 CLASSES.
Definition cls_mapped_bytes' (r : aclass) : Z := c_mapped_user r + c_mapped_free_array r.
Definition commit_bytes (st : astate) : Z := csum cls_mapped_bytes' st + 8 * a_nres st.

Definition rcov (P : list (word * word)) (iv : Z * Z) : Prop :=
  exists e, In e P /\ bv_unsigned (fst e) <= fst iv /\ snd iv <= bv_unsigned (fst e) + bv_unsigned (snd e).

Definition START (RESV : list (Z * Z)) (ATOP : Z) (L0 R : list (word * word)) (st : astate) : Prop :=
  (exists pb0, In (went (pb0, PRIM_SZ)) L0 /\ pb0 <= a_space_beg st /\ a_space_beg st + 2^37 + 2^12 <= pb0 + PRIM_SZ
               /\ KHIGH <= pb0 /\ pb0 + PRIM_SZ <= ATOP)
  /\ In (went (a_ptr_array st, PTR_SZ)) L0 /\ a_ptr_array st + PTR_SZ <= ATOP
  /\ region_free R (Z_to_bv 64 (a_ptr_array st)) (Z_to_bv 64 PTR_SZ) = true
  /\ In (went (LS_LO, LS_SZ)) L0 /\ In (went (GAP_LO, GAP_SZ)) L0 /\ In (went (HS_LO, HS_SZ)) L0
  /\ zlen L0 <= LEN0 /\ live_bytes L0 <= TOT0
  /\ Forall (rcov (R ++ L0)) RESV.

Definition sepz (e : word * word) (lo sz : Z) : Prop :=
  bv_unsigned (fst e) + bv_unsigned (snd e) <= lo \/ lo + sz <= bv_unsigned (fst e).
Definition noacc_sep (l : list (word * word)) : Prop := Forall (fun e => sepz e LS_LO LS_SZ /\ sepz e HS_LO HS_SZ) l.

Definition rsep (l r : list (word * word)) : Prop :=
  Forall (fun e => Forall (fun q => bv_unsigned (fst e) + bv_unsigned (snd e) <= bv_unsigned (fst q) \/ bv_unsigned (fst q) + bv_unsigned (snd q) <= bv_unsigned (fst e)) r) l.

Definition committed_user (st : astate) (x : Z) : Prop :=
  exists c, 1 <= c <= 31 /\ region_beg st c <= x < region_beg st c + c_mapped_user (get_cls st c).
Definition lazy_out (L0 : list (word * word)) (st : astate) (mo : Model) : Prop :=
  forall x, covered (m_vm_lazy mo) x = true -> covered L0 x = true /\ ~ committed_user st x.

Definition mu_le (st' st : astate) : Prop :=
  a_space_beg st' = a_space_beg st /\ forall c, 1 <= c <= 31 -> c_mapped_user (get_cls st' c) <= c_mapped_user (get_cls st c).
Lemma mu_le_refl : forall st, mu_le st st. Proof. intros st. split; [reflexivity| intros; lia]. Qed.
Lemma committed_user_mu_le : forall st st' x, mu_le st' st -> committed_user st' x -> committed_user st x.
Proof.
  intros st st' x [Hsb Hmu] (c & Hc & Hx). exists c. split; [exact Hc|]. specialize (Hmu c Hc). unfold region_beg in *. rewrite Hsb in Hx. lia.
Qed.

Lemma mu_put_le : forall st c r', c_mapped_user r' <= c_mapped_user (get_cls st c) ->
  forall c0, 1 <= c0 <= 31 -> c_mapped_user (get_cls (put_cls c r' st) c0) <= c_mapped_user (get_cls st c0).
Proof.
  intros st c r' H c0 _. destruct (Z.eq_dec c c0) as [->|NE]; [rewrite get_put_eq; exact H| rewrite get_put_ne by exact NE; lia].
Qed.
Lemma committed_user_put_grow : forall st c r' x n,
  c_mapped_user r' <= c_mapped_user (get_cls st c) + n ->
  committed_user (put_cls c r' st) x ->
  committed_user st x \/ region_beg st c + c_mapped_user (get_cls st c) <= x < region_beg st c + c_mapped_user (get_cls st c) + n.
Proof.
  intros st c r' x n H (c0 & Hc0 & Hx). rewrite region_beg_put in Hx. destruct (Z.eq_dec c c0) as [<-|NE].
  - rewrite get_put_eq in Hx. destruct (Z_lt_dec x (region_beg st c + c_mapped_user (get_cls st c))) as [LT|GE].
    + left. exists c. split; [exact Hc0| lia].
    + right. lia.
  - rewrite get_put_ne in Hx by exact NE. left. exists c0. split; [exact Hc0| exact Hx].
Qed.

Definition AMI (RESV : list (Z * Z)) (ATOP : Z) (ch : list (Z * Z)) (st : astate) (mo : Model) : Prop :=
  m_vm_materialized mo = []
  /\ vm_limit (m_vmmaps mo) = LIMIT
  /\ Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (vm_reserved (m_vmmaps mo))
  /\ zlen (vm_reserved (m_vmmaps mo)) <= LEN0 /\ live_bytes (vm_reserved (m_vmmaps mo)) <= RTOT0
  /\ Forall (entry_ok ATOP) (vm_maps (m_vmmaps mo))
  /\ (ivs_wf (vm_noaccess (m_vmmaps mo)) /\ noacc_sep (vm_noaccess (m_vmmaps mo)))
  /\ ivs_wf (m_vm_lazy mo)
  /\ (seps (vm_maps (m_vmmaps mo)) /\ rsep (vm_maps (m_vmmaps mo)) (vm_reserved (m_vmmaps mo)))
  /\ (atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP)
  /\ exists L0, Permutation (vm_maps (m_vmmaps mo)) (L0 ++ map went ch)
       /\ START RESV ATOP L0 (vm_reserved (m_vmmaps mo)) st
       /\ sum_count (Pm mo) L0 <= EAGER0 + commit_bytes st
       /\ lazy_out L0 st mo.

Definition grant_model (mo : Model) (z nZ : Z) : Model :=
  with_vmmaps (mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 z, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps mo))
                 (vm_noaccess (m_vmmaps mo)) (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo))
                 (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.

Definition fixed_model (mo : Model) (flags addr nZ : Z) : Model :=
  with_mmap_replacement (Z_to_bv 64 flags) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)
     (with_vmmaps (mmap_fixed_rw_next (m_vmmaps mo) (Z_to_bv 64 addr) (Z_to_bv 64 nZ)) mo).

Definition munmap_model (mo : Model) (addr nZ : Z) : Model :=
  with_mmap_destroyed (Z_to_bv 64 addr) (Z_to_bv 64 nZ)
     (mkVmMapsFull (vm_reserved (m_vmmaps mo)) (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 addr))
        (maps_subtract (vm_noaccess (m_vmmaps mo)) addr (addr + nZ))
        (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo))
        (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))) mo.

Definition CHX (pc : list achunk) (pb : list abatch) (st : astate) : list (Z * Z) := CH pc pb st ++ emb_ent st.

Definition INV (RESV : list (Z * Z)) (ATOP : Z) (pc : list achunk) (pb : list abatch) (st : astate) (mo : Model) : Prop :=
  AINV ATOP pc pb st /\ AMI RESV ATOP (CHX pc pb st) st mo.

Lemma all_chunks_put : forall pc pb c r st, all_chunks pc pb (put_cls c r st) = all_chunks pc pb st. Proof. reflexivity. Qed.
Lemma qbatches_put : forall pb c r st, qbatches pb (put_cls c r st) = qbatches pb st. Proof. reflexivity. Qed.
Lemma CH_put : forall pc pb c r st, CH pc pb (put_cls c r st) = CH pc pb st. Proof. reflexivity. Qed.
Lemma all_chunks_init_cache : forall pc pb st, all_chunks pc pb (init_cache st) = all_chunks pc pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma qbatches_init_cache : forall pb st, qbatches pb (init_cache st) = qbatches pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma CH_init_cache : forall pc pb st, CH pc pb (init_cache st) = CH pc pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma all_chunks_set_nres : forall pc pb v st, all_chunks pc pb (set_nres v st) = all_chunks pc pb st. Proof. reflexivity. Qed.
Lemma all_chunks_set_nsec : forall pc pb v st, all_chunks pc pb (set_nsec v st) = all_chunks pc pb st. Proof. reflexivity. Qed.

Lemma In_CLASSES : forall c, In c CLASSES <-> 1 <= c <= 31.
Proof.
  intros c. unfold CLASSES. rewrite in_map_iff. split.
  - intros (n & <- & Hn). apply in_seq in Hn. lia.
  - intros Hc. exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.
Lemma NoDup_CLASSES : List.NoDup CLASSES.
Proof. unfold CLASSES. apply (List.NoDup_map_NoDup_ForallPairs Z.of_nat). intros x y Hx Hy E. lia. apply List.seq_NoDup. Qed.

Lemma fold_csum_ext : forall (f : aclass -> Z) st st' l,
  (forall c, In c l -> get_cls st' c = get_cls st c) ->
  fold_right (fun c acc => f (get_cls st' c) + acc) 0 l = fold_right (fun c acc => f (get_cls st c) + acc) 0 l.
Proof.
  induction l as [|c l IH]; intros H; cbn; [reflexivity|]. rewrite H by (left; reflexivity). rewrite IH; [reflexivity|]. intros; apply H; right; assumption.
Qed.

Lemma fold_csum_put : forall (f : aclass -> Z) st c r l,
  List.NoDup l -> In c l ->
  fold_right (fun c' acc => f (get_cls (put_cls c r st) c') + acc) 0 l
  = fold_right (fun c' acc => f (get_cls st c') + acc) 0 l - f (get_cls st c) + f r.
Proof.
  induction l as [|c0 l IH]; intros Hnd Hin; [destruct Hin|]. cbn. inversion Hnd; subst.
  destruct Hin as [->|Hin].
  - rewrite get_put_eq. rewrite (fold_csum_ext f st (put_cls c r st)); [lia|]. intros c' Hc'. apply get_put_ne. congruence.
  - rewrite get_put_ne by congruence. rewrite IH by assumption. lia.
Qed.

Lemma csum_put : forall f st c r, 1 <= c <= 31 -> csum f (put_cls c r st) = csum f st - f (get_cls st c) + f r.
Proof. intros. unfold csum. apply fold_csum_put; [apply NoDup_CLASSES| apply In_CLASSES; lia]. Qed.

Lemma csum_init_cache : forall f st, csum f (init_cache st) = csum f st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma commit_bytes_put : forall st c r, 1 <= c <= 31 ->
  commit_bytes (put_cls c r st) = commit_bytes st - cls_mapped_bytes' (get_cls st c) + cls_mapped_bytes' r.
Proof. intros. unfold commit_bytes. rewrite csum_put by assumption. cbn [a_nres put_cls set_cls]. lia. Qed.
Lemma commit_bytes_init_cache : forall st, commit_bytes (init_cache st) = commit_bytes st.
Proof. intros. unfold commit_bytes. rewrite csum_init_cache. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.

Lemma zlen_app : forall {A} (l1 l2 : list A), zlen (l1 ++ l2) = zlen l1 + zlen l2.
Proof. intros. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_cons : forall {A} (x : A) l, zlen (x :: l) = 1 + zlen l.
Proof. intros. unfold zlen. cbn [length]. lia. Qed.
Lemma zlen_nil : forall {A}, zlen (@nil A) = 0. Proof. reflexivity. Qed.
Lemma zlen_nonneg : forall {A} (l : list A), 0 <= zlen l. Proof. intros. unfold zlen. lia. Qed.

Lemma cntP_app : forall c l1 l2, cntP c (l1 ++ l2) = cntP c l1 + cntP c l2.
Proof. intros. unfold cntP. rewrite filter_app. apply zlen_app. Qed.
Lemma cntP_cons : forall c ch l, cntP c (ch :: l) = (if is_prim_of c ch then 1 else 0) + cntP c l.
Proof. intros. unfold cntP. cbn [List.filter]. destruct (is_prim_of c ch); [rewrite zlen_cons|]; lia. Qed.
Lemma cntP_nil : forall c, cntP c [] = 0. Proof. reflexivity. Qed.
Lemma cntP_nonneg : forall c l, 0 <= cntP c l. Proof. intros. unfold cntP. apply zlen_nonneg. Qed.
Lemma secs_app : forall l1 l2, secs (l1 ++ l2) = secs l1 ++ secs l2.
Proof. intros. unfold secs. apply flat_map_app. Qed.
Lemma secs_cons : forall ch l, secs (ch :: l) = sec_of ch ++ secs l. Proof. reflexivity. Qed.
Lemma qchunks_app : forall b1 b2, qchunks (b1 ++ b2) = qchunks b1 ++ qchunks b2.
Proof. intros. unfold qchunks. apply flat_map_app. Qed.
Lemma qchunks_cons : forall b bs, qchunks (b :: bs) = b_chunks b ++ qchunks bs. Proof. reflexivity. Qed.
Lemma zsumc_app : forall l1 l2, zsumc (l1 ++ l2) = zsumc l1 + zsumc l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.
Lemma bsum_app : forall l1 l2, bsum (l1 ++ l2) = bsum l1 + bsum l2.
Proof. induction l1; intros; cbn; [lia|]. rewrite IHl1. lia. Qed.
Lemma nbatch_app : forall c b1 b2, nbatch c (b1 ++ b2) = nbatch c b1 + nbatch c b2.
Proof. intros. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_app| lia]. Qed.

Lemma filter_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' HP. induction HP; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; assumption.
  - destruct (f x), (f y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.
Lemma cntP_perm : forall c l l', Permutation l l' -> cntP c l = cntP c l'.
Proof. intros. unfold cntP, zlen. rewrite (Permutation_length (filter_perm (is_prim_of c) l l' H)). reflexivity. Qed.
Lemma secs_perm : forall l l', Permutation l l' -> Permutation (secs l) (secs l').
Proof. intros. unfold secs. apply Permutation_flat_map. assumption. Qed.
Lemma zsumc_perm : forall l l', Permutation l l' -> zsumc l = zsumc l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.

Lemma live_chunks_insert : forall st id ch,
  (a_live st) !! id = None ->
  Permutation (live_chunks (set_live (<[id := ch]> (a_live st)) st)) (ch :: live_chunks st).
Proof.
  intros st id ch Hn. unfold live_chunks. cbn [a_live set_live].
  change (ch :: map snd (map_to_list (a_live st))) with (map snd ((id, ch) :: map_to_list (a_live st))).
  apply Permutation_map. apply map_to_list_insert. exact Hn.
Qed.
Lemma live_chunks_delete : forall st id ch,
  (a_live st) !! id = Some ch ->
  Permutation (live_chunks st) (ch :: live_chunks (set_live (delete id (a_live st)) st)).
Proof.
  intros st id ch Hs. unfold live_chunks. cbn [a_live set_live].
  change (ch :: map snd (map_to_list (delete id (a_live st)))) with (map snd ((id, ch) :: map_to_list (delete id (a_live st)))).
  apply Permutation_map. symmetry. apply map_to_list_delete. exact Hs.
Qed.

Lemma sum_count_cons : forall P e l, sum_count P (e :: l) = iv_count P e + sum_count P l. Proof. reflexivity. Qed.
Lemma sum_count_perm : forall P l l', Permutation l l' -> sum_count P l = sum_count P l'.
Proof. intros P l l' HP. induction HP; rewrite ?sum_count_cons; lia. Qed.
Lemma iv_count_nonneg : forall P e, 0 <= iv_count P e. Proof. intros. unfold iv_count. apply zcount_nonneg. Qed.
Lemma iv_count_le_S : forall P e, iv_count P e <= S e.
Proof. intros. unfold iv_count. pose proof (zcount_le_len P (B e) (Z.to_nat (S e))). pose proof (S_range e). lia. Qed.
Lemma sum_count_le_live : forall P l, sum_count P l <= live_bytes l.
Proof.
  intros P l. rewrite live_bytes_sum_count. induction l; rewrite ?sum_count_cons; [cbn; lia|].
  pose proof (iv_count_le_S P a). unfold iv_count at 2. unfold iv_count in H. rewrite zcount_const_true.
  pose proof (S_range a). rewrite Z2Nat.id by lia. cbn [sum_count] in *. unfold iv_count in *. rewrite ?zcount_const_true in IHl. lia.
Qed.
Lemma sum_count_ext_on : forall P Q l,
  (forall e x, In e l -> B e <= x < B e + S e -> P x = Q x) -> sum_count P l = sum_count Q l.
Proof.
  intros P Q l H. induction l as [|e l IH]; [reflexivity|]. rewrite !sum_count_cons.
  rewrite IH by (intros e' x' He' Hx'; apply (H e' x'); [right|]; assumption).
  unfold iv_count. rewrite (zcount_ext P Q); [lia|]. intros x Hx. apply (H e); [left; reflexivity|].
  pose proof (S_range e). rewrite Z2Nat.id in Hx by lia. lia.
Qed.
Lemma sum_count_sub : forall P l1 l2, sum_count P l1 <= sum_count P (l1 ++ l2).
Proof. intros. rewrite sum_count_app. pose proof (sum_count_nonneg P l2). lia. Qed.

Lemma wsep_sym : forall p q, wsep p q -> wsep q p. Proof. unfold wsep. intros; lia. Qed.
Lemma seps_perm : forall l l', Permutation l l' -> seps l -> seps l'.
Proof.
  intros l l' HP. induction HP; intros Hs.
  - constructor.
  - inversion Hs; subst. constructor; [| auto]. eapply Permutation_Forall; eauto.
  - inversion Hs; subst. inversion H2; subst. apply Forall_cons_iff in H1 as [Hxy Hl].
    constructor. { constructor; [apply wsep_sym; exact Hxy| exact H3]. } constructor; assumption.
  - auto.
Qed.
Lemma seps_cons_inv : forall p l, seps (p :: l) -> Forall (wsep p) l /\ seps l.
Proof. intros p l H. inversion H; auto. Qed.
Lemma seps_app_inv_l : forall l1 l2, seps (l1 ++ l2) -> seps l2.
Proof. induction l1; intros l2 H; [exact H|]. cbn in H. apply seps_cons_inv in H as [_ H]. auto. Qed.

Lemma region_free_wsep : forall l (a n : word),
  region_free l a n = true -> Forall (wsep (a, n)) l.
Proof.
  induction l as [|[b s] l IH]; intros a n H; [constructor|].
  cbn [region_free] in H. apply andb_true_iff in H as [H1 H2]. constructor; [|apply IH; exact H2].
  apply negb_true_iff in H1. unfold iv_overlap in H1. unfold wsep. cbn [fst snd].
  apply andb_false_iff in H1 as [H1|H1]; apply Z.ltb_ge in H1; lia.
Qed.

Lemma overlap_sum_contained : forall l e lo hi,
  seps l -> In e l -> B e <= lo -> hi <= B e + S e -> lo <= hi ->
  overlap_sum l lo hi <= hi - lo.
Proof.
  intros l e lo hi Hs Hin H1 H2 Hlh. apply in_split in Hin as (l1 & l2 & ->).
  unfold overlap_sum. rewrite sum_count_app, sum_count_cons.
  assert (Z0 : forall l', Forall (wsep e) l' -> sum_count (in_rng lo hi) l' = 0).
  { intros l' Hf. induction l' as [|q l' IH]; [reflexivity|]. rewrite sum_count_cons. apply Forall_cons_iff in Hf as [Hq Hf].
    rewrite IH by exact Hf. fold (iv_count (in_rng lo hi) q). rewrite iv_count_in_rng_disjoint; [lia|].
    unfold wsep, B, S in *. lia. }
  pose proof (seps_perm _ _ (Permutation_sym (Permutation_middle l1 l2 e)) Hs) as Hs'.
  apply seps_cons_inv in Hs' as [Hf _]. apply Forall_app in Hf as [Hf1 Hf2].
  rewrite (Z0 l1 Hf1), (Z0 l2 Hf2). pose proof (iv_count_in_rng_le e lo hi Hlh). lia.
Qed.

Lemma map_remove_perm : forall l (b s : word) l2,
  Permutation l ((b, s) :: l2) -> seps l -> 0 < bv_unsigned s -> Forall (fun e => 0 < bv_unsigned (snd e)) l2 ->
  Permutation (map_remove l b) l2.
Proof.
  intros l b s l2 HP Hs Hpos Hall.
  unfold map_remove. rewrite (filter_perm _ _ _ HP). cbn [List.filter fst]. rewrite bv_eqb_refl. cbn [negb].
  pose proof (seps_perm _ _ HP Hs) as Hs'. apply seps_cons_inv in Hs' as [Hf _].
  assert (E : List.filter (fun p : word * word => negb (bv_eqb (fst p) b)) l2 = l2).
  { clear HP Hs. induction l2 as [|[b' s'] l2 IH]; [reflexivity|]. apply Forall_cons_iff in Hf as [H1 Hf]. apply Forall_cons_iff in Hall as [H2 Hall].
    cbn [List.filter fst]. destruct (bv_eqb b' b) eqn:E.
    - exfalso. apply bv_eqb_eq in E. subst b'. unfold wsep in H1. cbn [fst snd] in H1, H2. lia.
    - cbn [negb]. rewrite IH; auto. }
  rewrite E. apply Permutation_refl.
Qed.

Lemma map_contains_In : forall l e (a n : word),
  In e l -> bv_unsigned (fst e) <= bv_unsigned a -> bv_unsigned a + bv_unsigned n <= bv_unsigned (fst e) + bv_unsigned (snd e) ->
  map_contains l a n = true.
Proof.
  intros l e a n Hin H1 H2. unfold map_contains. apply existsb_exists. exists e. split; [exact Hin|].
  apply andb_true_iff. split; apply Z.leb_le; lia.
Qed.
Lemma map_has_In : forall l (a n : word), In (a, n) l -> map_has l a n = true.
Proof. intros. unfold map_has. apply existsb_exists. exists (a, n). split; [assumption|]. cbn. rewrite !bv_eqb_refl. reflexivity. Qed.

Section AMIT.
Variable RESV : list (Z * Z).
Variable ATOP : Z.
Local Notation AMI' := (AMI RESV ATOP).

Lemma AMI_with_fds : forall ch st f mo, AMI' ch st (with_fds f mo) <-> AMI' ch st mo.
Proof. intros. unfold AMI, Pm. cbn. tauto. Qed.

Lemma AMI_atop : forall ch st mo, AMI' ch st mo -> atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP.
Proof. intros ch st mo (M1 & M2 & M3 & M4 & M5 & M6 & [M7 M7s] & M8 & M9 & MT & _). exact MT. Qed.

Lemma AMI_mono : forall ch st st' mo,
  AMI' ch st mo -> a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st ->
  commit_bytes st <= commit_bytes st' ->
  (forall c, 1 <= c <= 31 -> c_mapped_user (get_cls st' c) <= c_mapped_user (get_cls st c)) ->
  AMI' ch st' mo.
Proof.
  intros ch st st' mo H Hsb Hpa Hcb Hmu. unfold AMI in *.
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB & HLZ).
  repeat (split; [assumption|]). exists L0. split; [exact HP|]. split; [| split].
  - unfold START in *. rewrite Hsb, Hpa. exact HS.
  - lia.
  - intros x Hx. destruct (HLZ x Hx) as [X1 X2]. split; [exact X1|]. intros Hc. apply X2. exact (committed_user_mu_le st st' x (conj Hsb Hmu) Hc).
Qed.

Lemma AMI_ivs_wf : forall ch st mo, AMI' ch st mo -> model_ivs_wf mo.
Proof.
  intros ch st mo (M1 & M2 & M3 & M4 & M5 & M6 & [M7 M7s] & M8 & M9 & [[T1 T2] T3] & _).
  unfold ACEIL, ATOP_MAX in T1, T2.
  split; [|split; [|split]].
  - intros q Hq. unfold iv_wf, B, S. destruct (proj1 (Forall_forall _ _) M6 q Hq) as (_ & _ & _ & Hhi). lia.
  - exact M7.
  - exact M8.
  -   unfold AsanCeil.init_sp_ok. unfold alloc_top, stack_max_size in T3. unfold sp_window_lo. lia.
Qed.

Lemma nonlazy_sum_count : forall mo, m_vm_materialized mo = [] -> model_ivs_wf mo ->
  nonlazy_bytes mo = sum_count (Pm mo) (vm_maps (m_vmmaps mo)).
Proof.
  intros mo Hm Hwf. pose proof (vm_backing_used_sem mo Hwf) as E. rewrite vm_backing_used_split, Hm in E. cbn [length Z.of_nat] in E.
  unfold Pm. lia.
Qed.

Fixpoint zsum2 (l : list (Z * Z)) : Z := match l with [] => 0 | e :: l' => snd e + zsum2 l' end.

Lemma live_bytes_went : forall ch, Forall (fun e => 0 <= snd e < 2^64) ch -> live_bytes (map went ch) = zsum2 ch.
Proof.
  induction ch as [|[mb ms] ch IH]; intros Hf; [reflexivity|]. apply Forall_cons_iff in Hf as [H1 Hf]. cbn [map zsum2 snd fst] in *.
  change (live_bytes (went (mb, ms) :: map went ch)) with (bv_unsigned (snd (went (mb, ms))) + live_bytes (map went ch)).
  cbn [snd went fst]. rewrite unsigned_lit by lia. rewrite IH by exact Hf. reflexivity.
Qed.

Lemma AMI_nonlazy_bound : forall ch st mo,
  AMI' ch st mo -> Forall (fun e => 0 <= snd e < 2^64) ch ->
  nonlazy_bytes mo <= EAGER0 + commit_bytes st + zsum2 ch.
Proof.
  intros ch st mo H Hch. pose proof (AMI_ivs_wf _ _ _ H) as Hwf.
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & [M7 M7s] & M8 & M9 & MT & L0 & HP & HS & HB & HLZ).
  rewrite (nonlazy_sum_count mo M1 Hwf). rewrite (sum_count_perm _ _ _ HP), sum_count_app.
  pose proof (sum_count_le_live (Pm mo) (map went ch)). rewrite live_bytes_went in H by exact Hch. lia.
Qed.

Lemma region_free_app : forall l1 l2 (a n : word), region_free (l1 ++ l2) a n = region_free l1 a n && region_free l2 a n.
Proof. induction l1 as [|[b s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH. apply andb_assoc. Qed.

Lemma in_iv_subtract : forall a sz lo hi q,
  iv_wf (a, sz) -> lo <= hi -> In q (iv_subtract a sz lo hi) ->
  B (a, sz) <= B q /\ B q + S q <= B (a, sz) + S (a, sz) /\ (B q + S q <= lo \/ hi <= B q).
Proof.
  intros a sz lo hi q Hwf Hlh Hin. unfold iv_wf, B, S in *. cbn [fst snd] in *.
  pose proof (bv_unsigned_in_range 64 a) as Ha. pose proof (bv_unsigned_in_range 64 sz) as Hs. unfold bv_modulus in Ha, Hs.
  unfold iv_subtract in Hin. cbv zeta in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin]. destruct Hin as [<-|[]]. cbn [fst snd].
    rewrite !unsigned_lit by lia. lia.
Qed.
Lemma in_maps_subtract : forall l lo hi q,
  ivs_wf l -> lo <= hi -> In q (maps_subtract l lo hi) ->
  exists e, In e l /\ B e <= B q /\ B q + S q <= B e + S e /\ (B q + S q <= lo \/ hi <= B q).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hlh Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. apply in_iv_subtract; assumption.
  - destruct (IH lo hi q Hl Hlh Hin) as (e & He & H). exists e. split; [right; exact He| exact H].
Qed.
Lemma noacc_sep_subtract : forall l lo hi, ivs_wf l -> lo <= hi -> noacc_sep l -> noacc_sep (maps_subtract l lo hi).
Proof.
  intros l lo hi Hwf Hlh HS. unfold noacc_sep in *. apply Forall_forall. intros q Hq.
  destruct (in_maps_subtract l lo hi q Hwf Hlh Hq) as (e & He & E1 & E2 & _).
  pose proof (proj1 (Forall_forall _ _) HS e He) as [S1 S2]. unfold sepz, B, S in *.
  pose proof (bv_unsigned_in_range 64 (snd q)) as Rq. split; lia.
Qed.

Lemma AMI_grant : forall ch st mo z nZ,
  AMI' ch st mo ->
  z mod 4096 = 0 -> 0 < z -> z + nZ <= ATOP -> nZ mod 4096 = 0 -> 0 < nZ ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ) = true ->
  AMI' ((z, nZ) :: ch) st (grant_model mo z nZ).
Proof.
  intros ch st mo z nZ H Hal Hz Hce Hnl Hn Hrf.
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & [M7 M7s] & M8 & M9 & MT & L0 & HP & HS & HB & HLZ).
  pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
  unfold AMI, grant_model. cbn -[Z.add Z.mul Z.pow Z_to_bv bv_unsigned sum_count Pm live_bytes zlen].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  - constructor; [|exact M6]. unfold entry_ok. cbn [fst snd]. rewrite !unsigned_lit by lia. repeat split; lia.
  - constructor; [|exact (proj1 M9)]. rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf'].
    apply (region_free_wsep (vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ)). exact Hrf'.
  -
    constructor; [|exact (proj2 M9)]. rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [Hrf' _].
    pose proof (region_free_wsep (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 nZ) Hrf') as W.
    eapply Forall_impl; [| exact W]. intros q Hq. unfold wsep in Hq. cbn [fst snd] in Hq |- *. lia.
  - exact (proj1 MT).
  - exists L0. split; [|split; [exact HS| split; [exact HB| exact HLZ]]].
    change ((Z_to_bv 64 z, Z_to_bv 64 nZ) :: vm_maps (m_vmmaps mo)) with (went (z, nZ) :: vm_maps (m_vmmaps mo)).
    cbn [map]. eapply Permutation_trans; [apply perm_skip; exact HP|]. apply Permutation_middle.
Qed.

Lemma covered_cons : forall e l x, covered (e :: l) x = in_iv e x || covered l x. Proof. reflexivity. Qed.

Lemma AMI_commit : forall ch st st' mo E a n,
  AMI' ch st mo ->
  In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + n <= B E + S E -> a mod 4096 = 0 -> n mod 4096 = 0 -> 0 < n ->
  a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st -> commit_bytes st + n <= commit_bytes st' ->
  (forall x, committed_user st' x -> committed_user st x \/ a <= x < a + n) ->
  AMI' ch st' (fixed_model mo F_FIXED a n).
Proof.
  intros ch st st' mo E a n H HinE HE1 HE2 Hal Hnl Hn Hsb Hpa Hcb Hcu.
  pose proof (AMI_ivs_wf _ _ _ H) as (Wm & Wn & Wl & Wsp).
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & [M7 M7s] & M8 & M9 & MT & L0 & HP & HS & HB & HLZ).
  pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  assert (Ha : 0 <= a /\ a + n < 2^64) by (unfold B, S in *; pose proof (bv_unsigned_in_range 64 (fst E)); lia).
  unfold fixed_model, with_mmap_replacement, with_mmap_backing. change (mmap_noreserve_b (Z_to_bv 64 F_FIXED)) with false. cbv iota.
  rewrite !unsigned_lit by lia.
  unfold AMI. model_proj. unfold mmap_fixed_rw_next. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_start_brk vm_brk vm_mmap_base vm_init_sp alloc_top].
  rewrite !unsigned_lit by lia. rewrite M1. cbn [List.filter].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: try exact (proj1 MT).
  all: try exact (proj1 M9). all: try exact (proj2 M9).
  all: try (unfold alloc_top in *; cbn [vm_init_sp] in *; lia).
  - reflexivity.
  - apply maps_subtract_wf; [exact Wn| lia].
  - apply noacc_sep_subtract; [exact Wn| lia| exact M7s].
  - apply maps_subtract_wf; [exact Wl| lia].
  - exists L0. split; [exact HP|]. split. { unfold START in *. rewrite Hsb, Hpa. exact HS. }
    destruct (maps_subtract_sem _ a (a + n) Wn ltac:(lia)) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ a (a + n) Wl ltac:(lia)) as (_ & _ & Cl).
    split.
    2:{   intros x Hx. change (covered (maps_subtract (m_vm_lazy mo) a (a + n)) x = true) in Hx. rewrite Cl in Hx. apply andb_prop in Hx as [Hx1 Hx2].
        destruct (HLZ x Hx1) as [X1 X2]. split; [exact X1|]. intros Hc. destruct (Hcu x Hc) as [Hc'|Hr]; [exact (X2 Hc')|].
        apply negb_true_iff in Hx2. unfold in_rng in Hx2. apply andb_false_iff in Hx2 as [Hx2|Hx2]; [apply Z.leb_gt in Hx2| apply Z.ltb_ge in Hx2]; lia. }
    eapply Z.le_trans.
    { apply (sum_count_mono _ (fun x => Pm mo x || in_rng a (a + n) x)).
      intros x. unfold Pm. model_proj. cbn [vm_noaccess]. rewrite !covered_app, Cn, Cl.
      destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng a (a + n) x); cbn; congruence. }
    eapply Z.le_trans; [apply sum_count_or_le|].
    fold (overlap_sum L0 a (a + n)).
    assert (HO : overlap_sum L0 a (a + n) <= n); [|lia].
    eapply Z.le_trans. { unfold overlap_sum. apply (sum_count_sub _ L0 (map went ch)). }
    fold (overlap_sum (L0 ++ map went ch) a (a + n)). unfold overlap_sum. rewrite <- (sum_count_perm _ _ _ HP).
    fold (overlap_sum (vm_maps (m_vmmaps mo)) a (a + n)).
    pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + n) (proj1 M9) HinE HE1 HE2 ltac:(lia)). lia.
Qed.

Lemma seps_filter : forall f l, seps l -> seps (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hs; [constructor|]. apply seps_cons_inv in Hs as [Hf Hs]. cbn.
  destruct (f e); [|apply IH; exact Hs]. constructor; [|apply IH; exact Hs].
  apply (Forall_incl _ _ _ (incl_filter f l)) || (rewrite Forall_forall in *; intros q Hq; apply Hf; apply (incl_filter f l); exact Hq).
Qed.

Lemma AMI_munmap : forall ch1 ch2 st st' mo mb ms,
  AMI' (ch1 ++ (mb, ms) :: ch2) st mo -> 0 < mb -> 0 < ms -> mb + ms <= ATOP ->
  a_space_beg st' = a_space_beg st -> a_ptr_array st' = a_ptr_array st -> commit_bytes st <= commit_bytes st' ->
  (forall c, 1 <= c <= 31 -> c_mapped_user (get_cls st' c) <= c_mapped_user (get_cls st c)) ->
  AMI' (ch1 ++ ch2) st' (munmap_model mo mb ms).
Proof.
  intros ch1 ch2 st st' mo mb ms H Hmb Hms Hce Hsb Hpa Hcb Hmu.
  pose proof (AMI_ivs_wf _ _ _ H) as (Wm & Wn & Wl & Wsp).
  destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & [M7 M7s] & M8 & M9 & MT & L0 & HP & HS & HB & HLZ).
  pose proof MT as [[T1 T2] T3]. unfold ACEIL, ATOP_MAX in T1, T2.
  assert (HP2 : Permutation (vm_maps (m_vmmaps mo)) (went (mb, ms) :: (L0 ++ map went (ch1 ++ ch2)))).
  { eapply Permutation_trans; [exact HP|]. rewrite !map_app. cbn [map]. rewrite !app_assoc.
    apply Permutation_sym. apply Permutation_middle. }
  pose proof (seps_perm _ _ HP2 (proj1 M9)) as Hs2. apply seps_cons_inv in Hs2 as [Hfar _].
  assert (HR : Permutation (map_remove (vm_maps (m_vmmaps mo)) (Z_to_bv 64 mb)) (L0 ++ map went (ch1 ++ ch2))).
  { apply (map_remove_perm _ (Z_to_bv 64 mb) (Z_to_bv 64 ms)); [exact HP2| exact (proj1 M9)| rewrite unsigned_lit by lia; lia|].
    assert (HF : Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_maps (m_vmmaps mo))).
    { eapply Forall_impl; [|exact M6]. intros e (He & _). exact He. }
    pose proof (Permutation_Forall HP2 HF) as HF2. apply Forall_cons_iff in HF2 as [_ HF2]. exact HF2. }
  unfold munmap_model, with_mmap_destroyed. rewrite !unsigned_lit by lia.
  unfold AMI. model_proj. cbn [vm_reserved vm_maps vm_noaccess vm_limit vm_start_brk vm_brk vm_mmap_base vm_init_sp alloc_top].
  rewrite M1. cbn [List.filter].
  repeat match goal with |- _ /\ _ => split end; try assumption.
  all: try exact (proj1 MT).
  all: try (unfold alloc_top in *; cbn [vm_init_sp] in *; lia).
  - reflexivity.
  - unfold map_remove. rewrite Forall_forall in *. intros e He. apply M6. apply (incl_filter _ _ _ He).
  - apply maps_subtract_wf; [exact Wn| lia].
  - apply noacc_sep_subtract; [exact Wn| lia| exact M7s].
  - apply maps_subtract_wf; [exact Wl| lia].
  - unfold map_remove; apply seps_filter; exact (proj1 M9).
  - unfold map_remove. destruct M9 as [_ M9r]. unfold rsep in M9r |- *. rewrite Forall_forall in M9r |- *. intros q Hq. apply M9r. apply (incl_filter _ _ _ Hq).
  - exists L0. split; [exact HR|]. split. { unfold START in *. rewrite Hsb, Hpa. exact HS. }
    destruct (maps_subtract_sem _ mb (mb + ms) Wn ltac:(lia)) as (_ & _ & Cn).
    destruct (maps_subtract_sem _ mb (mb + ms) Wl ltac:(lia)) as (_ & _ & Cl).
    split.
    2:{   intros x Hx. change (covered (maps_subtract (m_vm_lazy mo) mb (mb + ms)) x = true) in Hx. rewrite Cl in Hx. apply andb_prop in Hx as [Hx1 _].
        destruct (HLZ x Hx1) as [X1 X2]. split; [exact X1|]. intros Hc. apply X2. exact (committed_user_mu_le st st' x (conj Hsb Hmu) Hc). }
    rewrite (sum_count_ext_on _ (Pm mo)); [lia|].
    intros e x He Hx. unfold Pm. model_proj. cbn [vm_noaccess]. rewrite !covered_app, Cn, Cl.
    apply Forall_app in Hfar as [HfL _]. pose proof (proj1 (Forall_forall _ _) HfL e He) as Hw.
    unfold wsep, B, S in *. cbn [fst snd went] in Hw. rewrite !unsigned_lit in Hw by lia.
    replace (in_rng mb (mb + ms) x) with false.
    2:{ symmetry. unfold in_rng. apply andb_false_iff. destruct Hw; [right; apply Z.ltb_ge| left; apply Z.leb_gt]; lia. }
    destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x); reflexivity.
Qed.

Lemma seps_app_wsep : forall l1 l2 p q, seps (l1 ++ l2) -> In p l1 -> In q l2 -> wsep p q.
Proof.
  induction l1 as [|e l1 IH]; intros l2 p q Hs Hp Hq; [destruct Hp|]. cbn [app] in Hs. apply seps_cons_inv in Hs as [Hf Hs].
  destruct Hp as [<-|Hp]; [| exact (IH l2 p q Hs Hp Hq)].
  exact (proj1 (Forall_forall _ _) Hf q (in_or_app _ _ _ (or_intror Hq))).
Qed.
Lemma covered_In : forall l x, covered l x = true -> exists e, In e l /\ B e <= x < B e + S e.
Proof.
  intros l x H. unfold covered in H. apply existsb_exists in H as (e & He & Hx). exists e. split; [exact He|].
  unfold in_iv, in_rng in Hx. apply andb_prop in Hx as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
Lemma AMI_lazy_committed : forall ch st mo x, AMI' ch st mo -> committed_user st x -> covered (m_vm_lazy mo) x = false.
Proof.
  intros ch st mo x H Hc. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & _ & _ & _ & HLZ).
  destruct (covered (m_vm_lazy mo) x) eqn:E; [| reflexivity]. exfalso. exact (proj2 (HLZ x E) Hc).
Qed.
Lemma AMI_lazy_ch : forall ch st mo mb ms x, AMI' ch st mo -> In (mb, ms) ch -> 0 <= mb -> 0 <= ms -> mb + ms < 2^64 ->
  mb <= x < mb + ms -> covered (m_vm_lazy mo) x = false.
Proof.
  intros ch st mo mb ms x H Hin Hmb Hms Hhi Hx. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & M9 & _ & L0 & HP & _ & _ & HLZ).
  destruct (covered (m_vm_lazy mo) x) eqn:E; [| reflexivity]. exfalso.
  destruct (covered_In _ _ (proj1 (HLZ x E))) as (e0 & He0 & Hx0).
  pose proof (seps_app_wsep L0 (map went ch) e0 (went (mb, ms)) (seps_perm _ _ HP (proj1 M9)) He0 (in_map went _ _ Hin)) as W.
  unfold wsep, went, B, S in *. cbn [fst snd] in *. rewrite !unsigned_lit in W by lia. lia.
Qed.

Lemma AMI_arena_entry : forall ch st mo, AMI' ch st mo ->
  exists e, In e (vm_maps (m_vmmaps mo)) /\ B e <= a_space_beg st /\ a_space_beg st + 2^37 <= B e + S e /\ KHIGH <= B e.
Proof.
  intros ch st mo H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & MT & L0 & HP & HS & _).
  destruct HS as ((pb0 & Hin & H1 & H2 & H3 & H4) & _). exists (went (pb0, PRIM_SZ)).
  split; [eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact Hin]|].
  pose proof MT as [[T1 T2] _]. unfold ACEIL, ATOP_MAX in T1, T2.
  unfold went, B, S. cbn [fst snd]. unfold PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia.
Qed.
Lemma AMI_ch_entry : forall ch st mo mb ms, AMI' ch st mo -> In (mb, ms) ch -> In (went (mb, ms)) (vm_maps (m_vmmaps mo)).
Proof.
  intros ch st mo mb ms H Hin. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & _).
  eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; right; exact (in_map went _ _ Hin)].
Qed.

Lemma AMI_resv_entry : forall ch st mo iv, AMI' ch st mo -> In iv RESV ->
  (exists e, In e (vm_reserved (m_vmmaps mo)) /\ B e <= fst iv /\ snd iv <= B e + S e)
  \/ (exists e, In e (vm_maps (m_vmmaps mo)) /\ B e <= fst iv /\ snd iv <= B e + S e).
Proof.
  intros ch st mo iv H Hin. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HR). destruct (proj1 (Forall_forall _ _) HR iv Hin) as (e & He & H1 & H2).
  apply in_app_iff in He as [He|He]; [left| right]; exists e; (split; [| split; [exact H1| exact H2]]); [exact He|].
  eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact He].
Qed.
End AMIT.
Arguments AMI_resv_entry {RESV ATOP}.
Arguments AMI_lazy_committed {RESV ATOP}.
Arguments AMI_lazy_ch {RESV ATOP}.
Arguments AMI_arena_entry {RESV ATOP}.
Arguments AMI_ch_entry {RESV ATOP}.

Arguments AMI_with_fds {RESV ATOP}.
Arguments AMI_atop {RESV ATOP}.
Arguments AMI_mono {RESV ATOP}.
Arguments AMI_ivs_wf {RESV ATOP}.
Arguments AMI_nonlazy_bound {RESV ATOP}.
Arguments AMI_grant {RESV ATOP}.
Arguments AMI_commit {RESV ATOP}.
Arguments AMI_munmap {RESV ATOP}.
