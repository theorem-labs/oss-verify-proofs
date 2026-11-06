(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg VmLedger.
From OSSVerify.Proofs.leptonica.pix1_fuzzer.lib.Common.Mallocng Require Import MallocLayout MallocTree MallocOps.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Class HeapTop := {
  alloc_ceiling : Z;
  alloc_ceiling_range : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000
}.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition LOCKA : Z := bv_unsigned A_LOCK.
Definition CTX : Z := LOCKA + 8.
Definition CTX_END : Z := LOCKA + 936.   (* [comment removed for export] *)
Definition C_SECRET : Z := LOCKA + 8.
Definition C_INIT : Z := LOCKA + 16.     (* [comment removed for export] *)
Definition C_CTR : Z := LOCKA + 20.      (* [comment removed for export] *)
Definition C_FMH : Z := LOCKA + 24.
Definition C_AM : Z := LOCKA + 32.
Definition C_AMC : Z := LOCKA + 40.
Definition C_AAC : Z := LOCKA + 48.
Definition C_SHIFT : Z := LOCKA + 56.
Definition C_AHEAD : Z := LOCKA + 64.
Definition C_ATAIL : Z := LOCKA + 72.
Definition C_AAREAS : Z := LOCKA + 80.
Definition C_ACTIVE : Z := LOCKA + 88.   (* [comment removed for export] *)
Definition C_USAGE : Z := LOCKA + 472.   (* [comment removed for export] *)
Definition C_USEQ : Z := LOCKA + 856.    (* [comment removed for export] *)
Definition C_BOUNCE : Z := LOCKA + 888.  (* [comment removed for export] *)
Definition C_SEQ : Z := LOCKA + 920.     (* [comment removed for export] *)
Definition C_BRK : Z := LOCKA + 928.
Definition ERRNO : Z := bv_unsigned A_ERRNO.

Definition T_SIZE_CLASSES : Z := bv_unsigned A_SIZE_CLASSES.
Definition T_SMALL_CNT : Z := bv_unsigned A_SMALL_CNT_TAB.
Definition T_MED_CNT : Z := bv_unsigned A_MED_CNT_TAB.
Definition T_DEBRUIJN : Z := bv_unsigned A_DEBRUIJN.

(* [comment removed for export] *)
Definition size_classes : list Z := size_classes_tab.

(* [comment removed for export] *)
Lemma alloc_ceiling_val : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
Proof. exact alloc_ceiling_range. Qed.

Lemma layout_nums :
  (LOCKA = bv_unsigned A_LOCK /\ CTX = LOCKA + 8 /\ CTX_END = LOCKA + 936 /\ ERRNO = bv_unsigned A_ERRNO /\
   bv_unsigned A_CTX = LOCKA + 8) /\
  4096 <= IMG_LO /\ IMG_LO <= RW_LO /\ RW_LO + 64 <= LOCKA /\ LOCKA + 940 <= IMG_HI /\ IMG_HI <= 2^32 /\
  0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\
  RW_LO <= ERRNO /\ ERRNO + 4 <= LOCKA.
Proof.
  unfold CTX_END, CTX. unfold LOCKA, ERRNO.
  pose proof (mlo_hull (ML:=ML)) as Hh. pose proof (mlo_ctx (ML:=ML)). pose proof (mlo_order_got (ML:=ML)).
  pose proof (mlo_order_errno (ML:=ML)). pose proof (mlo_order_tp (ML:=ML)). pose proof (mlo_order_ssp (ML:=ML)).
  pose proof (mlo_order_libc (ML:=ML)). pose proof (mlo_order_ctx (ML:=ML)). pose proof (mlo_order_replaced (ML:=ML)).
  pose proof (mlo_ctx_align (ML:=ML)). pose proof (mlo_errno (ML:=ML)) as He. pose proof (mlo_tp_align (ML:=ML)) as Ht.
  pose proof alloc_ceiling_range. unfold CTX_SIZE in *.
  assert (H4096 : 4096 <= IMG_LO).
  { destruct Hh as (Hlo0 & _ & _ & _ & Hm & _). pose proof (Z_div_mod_eq_full IMG_LO 4096). lia. }
  assert (HE4 : bv_unsigned A_ERRNO mod 4 = 0).
  { rewrite He. pose proof (Z_div_mod_eq_full (bv_unsigned A_TP) 8).
    replace (bv_unsigned A_TP - 164) with (4 * (2 * (bv_unsigned A_TP / 8) - 41)) by lia.
    rewrite Z.mul_comm. apply Z_mod_mult. }
  repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma layout_small : 4096 <= IMG_LO /\ IMG_LO <= RW_LO /\ RW_LO <= LOCKA /\ LOCKA + 940 <= IMG_HI /\ IMG_HI <= 2^32 /\
  2^33 <= alloc_ceiling <= 2^47.
Proof. pose proof layout_nums. repeat split; lia. Qed.

(* [comment removed for export] *)
Lemma layout_aligns :
  IMG_LO mod 4096 = 0 /\ RW_LO mod 4096 = 0 /\ IMG_HI mod 4096 = 0 /\ CTX mod 8 = 0 /\ LOCKA mod 8 = 0 /\ ERRNO mod 4 = 0.
Proof.
  unfold CTX, LOCKA, ERRNO.
  pose proof (mlo_hull (ML:=ML)) as Hh. pose proof (mlo_ctx (ML:=ML)) as Hc. pose proof (mlo_ctx_align (ML:=ML)) as Ha.
  pose proof (mlo_errno (ML:=ML)) as He. pose proof (mlo_tp_align (ML:=ML)) as Ht.
  assert (HE4 : bv_unsigned A_ERRNO mod 4 = 0).
  { rewrite He. pose proof (Z_div_mod_eq_full (bv_unsigned A_TP) 8).
    replace (bv_unsigned A_TP - 164) with (4 * (2 * (bv_unsigned A_TP / 8) - 41)) by lia.
    rewrite Z.mul_comm. apply Z_mod_mult. }
  assert (HC8 : (bv_unsigned A_LOCK + 8) mod 8 = 0) by (rewrite <- Hc; exact Ha).
  assert (HL8 : bv_unsigned A_LOCK mod 8 = 0).
  { pose proof (Z_div_mod_eq_full (bv_unsigned A_LOCK + 8) 8).
    replace (bv_unsigned A_LOCK) with (8 * ((bv_unsigned A_LOCK + 8) / 8 - 1)) by lia.
    rewrite Z.mul_comm. apply Z_mod_mult. }
  repeat split; try lia; tauto.
Qed.

(* [comment removed for export] *)
Lemma layout_tabs :
  T_SIZE_CLASSES = bv_unsigned A_SIZE_CLASSES /\ T_SMALL_CNT = bv_unsigned A_SMALL_CNT_TAB /\
  T_MED_CNT = bv_unsigned A_MED_CNT_TAB /\ T_DEBRUIJN = bv_unsigned A_DEBRUIJN /\
  4096 <= IMG_LO /\ (IMG_LO <= T_DEBRUIJN /\ T_DEBRUIJN + 32 <= RW_LO) /\ (IMG_LO <= T_SIZE_CLASSES /\ T_SIZE_CLASSES + 96 <= RW_LO) /\
  (IMG_LO <= T_SMALL_CNT /\ T_SMALL_CNT + 27 <= RW_LO) /\ (IMG_LO <= T_MED_CNT /\ T_MED_CNT + 4 <= RW_LO) /\ RW_LO <= IMG_HI /\ IMG_HI <= 2^32.
Proof.
  pose proof layout_nums. unfold T_DEBRUIJN, T_SIZE_CLASSES, T_SMALL_CNT, T_MED_CNT.
  pose proof (mlo_tables_ro (ML:=ML)). pose proof (mlo_size_classes_align (ML:=ML)).
  repeat split; lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition byte_of (v : Z) (k : Z) : Z := (v / 2 ^ (8 * k)) mod 256.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive slot_st := SIdle | STaken | SLive (off n : Z) | SNested (child : Z).

Inductive mrole :=
| RFree                        (* [comment removed for export] *)
| RAvail                       (* [comment removed for export] *)
| RDead                        (* [comment removed for export] *)
| RGroup (aib : Z) (slots : list slot_st).   (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive mfield := FPrev | FNext | FMem | FAvail | FFreed | FW32.

Definition mfield_eq_dec : forall a b : mfield, {a = b} + {a <> b}.
Proof. decide equality. Defined.

Definition moff (fl : mfield) : Z :=
  match fl with FPrev => 0 | FNext => 8 | FMem => 16 | FAvail => 24 | FFreed => 28 | FW32 => 32 end.
Definition mlen (fl : mfield) : Z :=
  match fl with FAvail | FFreed => 4 | _ => 8 end.

(* [comment removed for export] *)
Record meta_rec := MTR { mr_prev : Z; mr_next : Z; mr_mem : Z; mr_avail : Z; mr_freed : Z; mr_w32 : Z;
                         mt_role : mrole }.
Definition mt_f (mt : meta_rec) (fl : mfield) : Z :=
  match fl with
  | FPrev => mr_prev mt | FNext => mr_next mt | FMem => mr_mem mt
  | FAvail => mr_avail mt | FFreed => mr_freed mt | FW32 => mr_w32 mt
  end.
Definition MT (f : mfield -> Z) (r : mrole) : meta_rec :=
  MTR (f FPrev) (f FNext) (f FMem) (f FAvail) (f FFreed) (f FW32) r.
(* [comment removed for export] *)
Global Arguments mt_f : simpl never.

Lemma mt_f_MT : forall f r fl, mt_f (MT f r) fl = f fl.
Proof. intros f r fl. unfold mt_f, MT. destruct fl; reflexivity. Qed.
Lemma mt_role_MT : forall f r, mt_role (MT f r) = r.
Proof. reflexivity. Qed.
Lemma meta_ext : forall mt mt', mt_role mt = mt_role mt' -> (forall fl, mt_f mt fl = mt_f mt' fl) -> mt = mt'.
Proof.
  intros [p n m a fr w r] [p' n' m' a' fr' w' r'] Hr Hf. cbn in Hr. subst r'.
  pose proof (Hf FPrev) as E1. pose proof (Hf FNext) as E2. pose proof (Hf FMem) as E3.
  pose proof (Hf FAvail) as E4. pose proof (Hf FFreed) as E5. pose proof (Hf FW32) as E6.
  unfold mt_f in E1, E2, E3, E4, E5, E6. cbn in E1, E2, E3, E4, E5, E6. subst. reflexivity.
Qed.
Lemma MT_eta : forall mt, MT (mt_f mt) (mt_role mt) = mt.
Proof. intros [p n m a fr w r]. reflexivity. Qed.

Definition mt_prev (mt : meta_rec) : Z := mt_f mt FPrev.
Definition mt_next (mt : meta_rec) : Z := mt_f mt FNext.
Definition mt_mem (mt : meta_rec) : Z := mt_f mt FMem.
Definition mt_avail (mt : meta_rec) : Z := mt_f mt FAvail.
Definition mt_freed (mt : meta_rec) : Z := mt_f mt FFreed.
Definition mt_w32 (mt : meta_rec) : Z := mt_f mt FW32.

Definition mupd (mt : meta_rec) (fl : mfield) (v : Z) : meta_rec :=
  MT (fun fl' => if mfield_eq_dec fl' fl then v else mt_f mt fl') (mt_role mt).
Definition mrole_set (mt : meta_rec) (r : mrole) : meta_rec := MT (mt_f mt) r.

(* [comment removed for export] *)
Definition mmap_t := Z -> option meta_rec.
Definition aupd (g : mmap_t) (ma : Z) (mt : meta_rec) : mmap_t :=
  fun x => if Z.eq_dec x ma then Some mt else g x.

(* [comment removed for export] *)
Inductive cslot :=
| KSecret | KInit | KCtr | KFmh | KAm | KAmc | KAac | KShift | KAhead | KAtail | KAareas | KSeq | KBrk
| KActive (i : Z) | KUsage (i : Z) | KUseq (i : Z) | KBounce (i : Z).

Definition cslot_eq_dec : forall k k' : cslot, {k = k'} + {k <> k'}.
Proof. decide equality; apply Z.eq_dec. Defined.

Definition caddr (k : cslot) : Z :=
  match k with
  | KSecret => C_SECRET | KInit => C_INIT | KCtr => C_CTR | KFmh => C_FMH | KAm => C_AM
  | KAmc => C_AMC | KAac => C_AAC | KShift => C_SHIFT | KAhead => C_AHEAD | KAtail => C_ATAIL
  | KAareas => C_AAREAS | KSeq => C_SEQ | KBrk => C_BRK
  | KActive i => C_ACTIVE + 8 * i | KUsage i => C_USAGE + 8 * i
  | KUseq i => C_USEQ + i | KBounce i => C_BOUNCE + i
  end.

(* [comment removed for export] *)
Lemma word_eqZ : forall (w : word) z, bv_unsigned w = z -> w = Z_to_bv 64 z.
Proof. intros w z <-. symmetry. apply Z_to_bv_bv_unsigned. Qed.

Lemma A_LOCK_eq : A_LOCK = Z_to_bv 64 LOCKA.
Proof. apply word_eqZ. reflexivity. Qed.
Lemma A_CTX_eq : A_CTX = Z_to_bv 64 (caddr KSecret).
Proof. apply word_eqZ. cbn. unfold C_SECRET, LOCKA. apply mlo_ctx. Qed.
Lemma A_INIT_DONE_eq : A_INIT_DONE = Z_to_bv 64 (caddr KInit).
Proof. apply word_eqZ. cbn. unfold C_INIT, LOCKA. rewrite mlo_init_done, mlo_ctx. lia. Qed.
Lemma A_MMAP_CTR_eq : A_MMAP_CTR = Z_to_bv 64 (caddr KCtr).
Proof. apply word_eqZ. cbn. unfold C_CTR, LOCKA. rewrite mlo_mmap_ctr, mlo_ctx. lia. Qed.
Lemma A_FREE_META_HEAD_eq : A_FREE_META_HEAD = Z_to_bv 64 (caddr KFmh).
Proof. apply word_eqZ. cbn. unfold C_FMH, LOCKA. rewrite mlo_free_meta_head, mlo_ctx. lia. Qed.
Lemma A_AVAIL_META_eq : A_AVAIL_META = Z_to_bv 64 (caddr KAm).
Proof. apply word_eqZ. cbn. unfold C_AM, LOCKA. rewrite mlo_avail_meta, mlo_ctx. lia. Qed.
Lemma A_AVAIL_META_CNT_eq : A_AVAIL_META_CNT = Z_to_bv 64 (caddr KAmc).
Proof. apply word_eqZ. cbn. unfold C_AMC, LOCKA. rewrite mlo_avail_meta_cnt, mlo_ctx. lia. Qed.
Lemma A_AVAIL_AREA_CNT_eq : A_AVAIL_AREA_CNT = Z_to_bv 64 (caddr KAac).
Proof. apply word_eqZ. cbn. unfold C_AAC, LOCKA. rewrite mlo_avail_area_cnt, mlo_ctx. lia. Qed.
Lemma A_META_SHIFT_eq : A_META_SHIFT = Z_to_bv 64 (caddr KShift).
Proof. apply word_eqZ. cbn. unfold C_SHIFT, LOCKA. rewrite mlo_meta_shift, mlo_ctx. lia. Qed.
Lemma A_AREA_HEAD_eq : A_AREA_HEAD = Z_to_bv 64 (caddr KAhead).
Proof. apply word_eqZ. cbn. unfold C_AHEAD, LOCKA. rewrite mlo_area_head, mlo_ctx. lia. Qed.
Lemma A_AREA_TAIL_eq : A_AREA_TAIL = Z_to_bv 64 (caddr KAtail).
Proof. apply word_eqZ. cbn. unfold C_ATAIL, LOCKA. rewrite mlo_area_tail, mlo_ctx. lia. Qed.
Lemma A_AVAIL_AREAS_eq : A_AVAIL_AREAS = Z_to_bv 64 (caddr KAareas).
Proof. apply word_eqZ. cbn. unfold C_AAREAS, LOCKA. rewrite mlo_avail_areas, mlo_ctx. lia. Qed.
Lemma A_SEQ_eq : A_SEQ = Z_to_bv 64 (caddr KSeq).
Proof. apply word_eqZ. cbn. unfold C_SEQ, LOCKA. rewrite mlo_seq, mlo_ctx. lia. Qed.
Lemma A_BRK_eq : A_BRK = Z_to_bv 64 (caddr KBrk).
Proof. apply word_eqZ. cbn. unfold C_BRK, LOCKA. rewrite mlo_brk, mlo_ctx. lia. Qed.
Lemma Z_UNMAP_SEQ_eq : Z_UNMAP_SEQ = caddr (KUseq 0).
Proof. cbn. unfold C_USEQ, LOCKA. rewrite mlo_unmap_seq, mlo_ctx. lia. Qed.
Lemma Z_BOUNCES_eq : Z_BOUNCES = caddr (KBounce 0).
Proof. cbn. unfold C_BOUNCE, LOCKA. rewrite mlo_bounces, mlo_ctx. lia. Qed.
Lemma A_ERRNO_eq : A_ERRNO = Z_to_bv 64 ERRNO.
Proof. apply word_eqZ. reflexivity. Qed.
Lemma A_SIZE_CLASSES_eq : A_SIZE_CLASSES = Z_to_bv 64 T_SIZE_CLASSES.
Proof. apply word_eqZ. reflexivity. Qed.
Lemma A_SMALL_CNT_TAB_eq : A_SMALL_CNT_TAB = Z_to_bv 64 T_SMALL_CNT.
Proof. apply word_eqZ. reflexivity. Qed.
Lemma A_MED_CNT_TAB_eq : A_MED_CNT_TAB = Z_to_bv 64 T_MED_CNT.
Proof. apply word_eqZ. reflexivity. Qed.
Lemma A_DEBRUIJN_eq : A_DEBRUIJN = Z_to_bv 64 T_DEBRUIJN.
Proof. apply word_eqZ. reflexivity. Qed.

(* [comment removed for export] *)
Lemma at_Z0 : forall a d, at_ (Z_to_bv 64 a) d = Z_to_bv 64 (a + d).
Proof.
  intros a d. unfold at_. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite ?Zmod_mod. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma at_lock : forall d, at_ A_LOCK d = Z_to_bv 64 (LOCKA + d).
Proof. intros d. rewrite A_LOCK_eq at 1. apply at_Z0. Qed.
Lemma at_ctx : forall d, at_ A_CTX d = Z_to_bv 64 (LOCKA + (8 + d)).
Proof. intros d. rewrite A_CTX_eq. rewrite at_Z0. f_equal. cbn. unfold C_SECRET. lia. Qed.

Definition clen (k : cslot) : Z :=
  match k with
  | KInit | KCtr => 4
  | KSeq | KUseq _ | KBounce _ => 1
  | _ => 8
  end.

Definition cvalid (k : cslot) : Prop :=
  match k with
  | KActive i | KUsage i => 0 <= i < 48
  | KUseq i | KBounce i => 0 <= i < 32
  | _ => True
  end.

Definition ctx_rec := cslot -> Z.

Definition cupd (c : ctx_rec) (k : cslot) (v : Z) : ctx_rec :=
  fun k' => if cslot_eq_dec k' k then v else c k'.

Record astate := AST {
  a_ctx : ctx_rec;
  a_areas : list Z;                 (* [comment removed for export] *)
  a_meta : mmap_t;                 (* [comment removed for export] *)
  a_freelist : list Z;              (* [comment removed for export] *)
  a_active : Z -> list Z;           (* [comment removed for export] *)
  a_pages : list Z;                 (* [comment removed for export] *)
  a_brk_lo : Z;                     (* [comment removed for export] *)
  a_live : Z -> option Z;           (* [comment removed for export] *)
  (* [comment removed for export] *)
  a_mblocks : list (Z * Z);         (* [comment removed for export] *)
  a_xmaps : list (Z * Z)            (* [comment removed for export] *)
}.

Definition lupd (f : Z -> option Z) (p : Z) (v : option Z) : Z -> option Z :=
  fun x => if Z.eq_dec x p then v else f x.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition w_last (w : Z) : Z := w mod 32.
Definition w_freeable (w : Z) : Z := (w / 32) mod 2.
Definition w_sc (w : Z) : Z := (w / 64) mod 64.
Definition w_maplen (w : Z) : Z := w / 4096.

Definition mt_last (mt : meta_rec) : Z := w_last (mt_w32 mt).
Definition mt_sc (mt : meta_rec) : Z := w_sc (mt_w32 mt).
Definition mt_maplen (mt : meta_rec) : Z := w_maplen (mt_w32 mt).
Definition mt_cnt (mt : meta_rec) : Z := mt_last mt + 1.

(* [comment removed for export] *)
Definition mt_stride (mt : meta_rec) : Z :=
  if (mt_maplen mt =? 0) || negb (mt_last mt =? 0)
  then 16 * size_class (mt_sc mt)
  else mt_maplen mt * 4096 - 16.

(* [comment removed for export] *)
Definition slot_start_g (mem sd i : Z) : Z := mem + 16 + i * sd.          (* [comment removed for export] *)
Definition slot_end_g (mem sd i : Z) : Z := mem + 16 + i * sd + sd - 4.   (* [comment removed for export] *)
Definition slot_start (mt : meta_rec) (i : Z) : Z := slot_start_g (mt_mem mt) (mt_stride mt) i.
Definition slot_end (mt : meta_rec) (i : Z) : Z := slot_end_g (mt_mem mt) (mt_stride mt) i.

(* [comment removed for export] *)
Definition grp_map_len (mt : meta_rec) : Z := mt_maplen mt * 4096.

(* [comment removed for export] *)
Definition gext_lo (mt : meta_rec) : Z := mt_mem mt.
Definition gext_hi (mt : meta_rec) : Z := mt_mem mt + 12 + mt_cnt mt * mt_stride mt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record fct := FCT { f_a : Z; f_n : Z; f_v : Z }.

(* [comment removed for export] *)
Definition grp_hdr_fields (ma : Z) (mt : meta_rec) (aib : Z) : list fct :=
  [FCT (mt_mem mt) 8 ma; FCT (mt_mem mt + 8) 1 aib].

(* [comment removed for export] *)
Definition slot_fields_g (mem sd : Z) (i : Z) (st : slot_st) : list fct :=
  let p0 := slot_start_g mem sd i in
  let e := slot_end_g mem sd i in
  [FCT (p0 - 4) 1 0; FCT e 1 0] ++
  match st with
  | SIdle | STaken => []
  | SLive off n =>
      let p := p0 + 16 * off in
      let rsv := e - p - n in
      (if off =? 0 then [] else [FCT (p0 - 3) 1 224; FCT (p0 - 2) 2 off; FCT (p - 4) 1 0])
      ++ [FCT (p - 3) 1 (i + 32 * Z.min rsv 5); FCT (p - 2) 2 ((p - mem - 16) / 16)]
      ++ (if rsv <? 5 then [] else [FCT (e - 4) 4 rsv; FCT (e - 5) 1 0])
      ++ (if rsv =? 0 then [] else [FCT (e - rsv) 1 0])
  | SNested child =>
      [FCT (p0 - 3) 1 (i + 32 * 6); FCT (p0 - 2) 2 ((p0 - mem - 16) / 16)]
  end.
Definition slot_fields (mt : meta_rec) (i : Z) (st : slot_st) : list fct :=
  slot_fields_g (mt_mem mt) (mt_stride mt) i st.

Section Facts.
  Variable A : astate.

  Definition has_ctx (f : fct) : Prop := exists k, cvalid k /\ f = FCT (caddr k) (clen k) (a_ctx A k).
  Definition has_area (f : fct) : Prop := exists pg, In pg (a_areas A) /\ f = FCT pg 8 (a_ctx A KSecret).
  Definition has_meta (f : fct) : Prop :=
    exists ma mt fl, a_meta A ma = Some mt /\ f = FCT (ma + moff fl) (mlen fl) (mt_f mt fl).
  Definition has_grp (f : fct) : Prop :=
    exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\
      (In f (grp_hdr_fields ma mt aib) \/
       exists i st, nth_error slots i = Some st /\ In f (slot_fields mt (Z.of_nat i) st)).

  Definition has (f : fct) : Prop := has_ctx f \/ has_area f \/ has_meta f \/ has_grp f.

  (* [comment removed for export] *)
  Definition fbyte (f : fct) (x b : Z) : Prop :=
    f_a f <= x < f_a f + f_n f /\ b = byte_of (f_v f) (x - f_a f).

  Definition facts (x b : Z) : Prop := exists f, has f /\ fbyte f x b.

  (* [comment removed for export] *)
  Definition dom (x : Z) : Prop :=
    (exists pg, In pg (a_areas A) /\ pg <= x < pg + 4096) \/
    (exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\
       0 < mt_maplen mt /\ mt_mem mt <= x < mt_mem mt + grp_map_len mt) \/
    (exists pg, In pg (a_pages A) /\ pg <= x < pg + 4096).
End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mbyte (m : word -> option byte) (x : Z) : option Z :=
  match rdn ml_segs m (Z_to_bv 64 x) 1 with Some [b] => Some (bv_unsigned b) | _ => None end.

Record Rep (A : astate) (m : word -> option byte) : Prop := {
  rep_facts : forall x b, facts A x b -> mbyte m x = Some b;
  rep_dom   : forall x, dom A x -> m (Z_to_bv 64 x) <> None;
  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition page_aligned (x : Z) : Prop := x mod 4096 = 0.

(* [comment removed for export] *)
Definition heap_range (lo hi : Z) : Prop :=
  0x1000 <= lo /\ lo <= hi /\ hi <= alloc_ceiling /\ (hi <= IMG_LO \/ IMG_HI <= lo).

(* [comment removed for export] *)
Definition dll (A : astate) (l : list Z) : Prop :=
  forall k x, nth_error l k = Some x ->
    exists mt, a_meta A x = Some mt /\
      mt_next mt = nth (S k mod length l) l 0 /\
      mt_prev mt = nth ((k + length l - 1) mod length l)%nat l 0.

(* [comment removed for export] *)
Definition meta_addr (pg : Z) (k : Z) : Z := pg + 24 + 40 * k.

(* [comment removed for export] *)
Definition is_live (A : astate) (p n : Z) : Prop :=
  exists ma mt aib slots i off, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\ 0 <= i /\
    nth_error slots (Z.to_nat i) = Some (SLive off n) /\ p = slot_start mt i + 16 * off.

Record WF (A : astate) : Prop := {
  (* [comment removed for export] *)
  wf_areas_nodup : NoDup (a_areas A);
  wf_areas_al : forall pg, In pg (a_areas A) -> page_aligned pg /\ heap_range pg (pg + 4096);
  wf_meta_dom : forall ma, a_meta A ma <> None <->
                  exists pg k, In pg (a_areas A) /\ 0 <= k < 101 /\ ma = meta_addr pg k;
  (* [comment removed for export] *)
  wf_init : a_ctx A KInit = 0 \/ a_ctx A KInit = 1;
  wf_uninit : a_ctx A KInit = 0 -> a_areas A = [] /\ a_ctx A KFmh = 0 /\ a_ctx A KAmc = 0 /\
              a_ctx A KAac = 0 /\ a_ctx A KBrk = 0 /\ a_ctx A KAtail = 0 /\
              a_ctx A KShift = 0 /\ a_pages A = [] /\ (forall sc, a_ctx A (KActive sc) = 0);
  wf_amc : 0 <= a_ctx A KAmc <= 100;
  wf_am : a_ctx A KAmc > 0 ->
          exists pg, a_areas A <> [] /\ pg = last (a_areas A) 0 /\
          a_ctx A KAm = meta_addr pg (101 - a_ctx A KAmc) /\
          forall k, 101 - a_ctx A KAmc <= k < 101 ->
            exists mt, a_meta A (meta_addr pg k) = Some mt /\ mt_role mt = RAvail;
  wf_atail : a_ctx A KAtail = last (a_areas A) 0;
  wf_ahead : a_ctx A KAhead = hd 0 (a_areas A);
  (* [comment removed for export] *)
  wf_avail_zero : forall ma mt, a_meta A ma = Some mt -> mt_role mt = RAvail ->
     mt_prev mt = 0 /\ mt_next mt = 0 /\ mt_mem mt = 0 /\ mt_avail mt = 0 /\ mt_freed mt = 0 /\ mt_w32 mt = 0;
  wf_free_zero : forall ma mt, a_meta A ma = Some mt -> mt_role mt = RFree ->
     mt_mem mt = 0 /\ mt_avail mt = 0 /\ mt_freed mt = 0 /\ mt_w32 mt = 0;
  (* [comment removed for export] *)
  wf_fl_nodup : NoDup (a_freelist A);
  wf_fl_head : a_ctx A KFmh = hd 0 (a_freelist A);
  wf_fl_mem : forall ma, In ma (a_freelist A) <-> exists mt, a_meta A ma = Some mt /\ mt_role mt = RFree;
  wf_fl_dll : dll A (a_freelist A);
  (* [comment removed for export] *)
  wf_grp : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     (* [comment removed for export] *)
     0 <= mt_w32 mt < 2^64 /\ w_freeable (mt_w32 mt) = 1 /\
     (mt_sc mt < 48 \/ (mt_sc mt = 63 /\ mt_last mt = 0 /\ 0 < mt_maplen mt)) /\
     Z.of_nat (length slots) = mt_cnt mt /\
     0 <= mt_avail mt < 2 ^ (mt_cnt mt) /\ 0 <= mt_freed mt < 2 ^ (mt_cnt mt) /\
     Z.land (mt_avail mt) (mt_freed mt) = 0 /\
     0 <= aib < 256 /\ mt_avail mt < 2 ^ (aib mod 32 + 1) /\ aib mod 32 <= mt_last mt /\
     (forall i st, nth_error slots (Z.to_nat i) = Some st -> 0 <= i ->
        (Z.testbit (Z.lor (mt_avail mt) (mt_freed mt)) i = true <-> st = SIdle)) /\
     (* [comment removed for export] *)
     mt_mem mt mod 16 = 0 /\ 0x1000 <= mt_mem mt /\
     16 + mt_cnt mt * mt_stride mt <= (if mt_maplen mt =? 0 then 2^64 else grp_map_len mt) /\
     mt_mem mt + 16 + mt_cnt mt * mt_stride mt <= alloc_ceiling /\
     (0 < mt_maplen mt -> page_aligned (mt_mem mt) /\ heap_range (mt_mem mt) (mt_mem mt + grp_map_len mt));
  wf_live : forall ma mt aib slots i off n, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     nth_error slots (Z.to_nat i) = Some (SLive off n) -> 0 <= i ->
     0 <= off /\ 0 <= n /\ 16 * off + n <= mt_stride mt - 4 /\ off < 2^16 /\ off <= 255 /\ mt_stride mt - n < 2^20;
  wf_nested : forall ma mt aib slots i ch, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     nth_error slots (Z.to_nat i) = Some (SNested ch) -> 0 <= i ->
     exists mc aibc slc, a_meta A ch = Some mc /\ mt_role mc = RGroup aibc slc /\
       mt_maplen mc = 0 /\ mt_mem mc = slot_start mt i /\
       16 + mt_cnt mc * mt_stride mc <= mt_stride mt;   (* [comment removed for export] *)
  wf_nested_parent : forall ch mc aibc slc, a_meta A ch = Some mc -> mt_role mc = RGroup aibc slc ->
     mt_maplen mc = 0 ->
     exists ma mt aib slots i, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\
       0 <= i /\ nth_error slots (Z.to_nat i) = Some (SNested ch);
  (* [comment removed for export] *)
  wf_grp_root : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     exists mr mtr aibr slr, a_meta A mr = Some mtr /\ mt_role mtr = RGroup aibr slr /\ 0 < mt_maplen mtr /\
       mt_mem mtr <= gext_lo mt /\ gext_hi mt + 4 <= mt_mem mtr + grp_map_len mtr /\
       (0 < mt_maplen mt -> mr = ma);
  (* [comment removed for export] *)
  wf_laminar : forall ma mt aib slots ma' mt' aib' slots',
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' -> ma <> ma' ->
     gext_hi mt + 4 <= gext_lo mt' \/ gext_hi mt' + 4 <= gext_lo mt \/
     (exists j ch, 0 <= j /\ nth_error slots (Z.to_nat j) = Some (SNested ch) /\
        slot_start mt j <= gext_lo mt' /\ gext_hi mt' <= slot_end mt j) \/
     (exists j ch, 0 <= j /\ nth_error slots' (Z.to_nat j) = Some (SNested ch) /\
        slot_start mt' j <= gext_lo mt /\ gext_hi mt <= slot_end mt' j);
  (* [comment removed for export] *)
  wf_act_head : forall sc, 0 <= sc < 48 -> a_ctx A (KActive sc) = hd 0 (a_active A sc);
  wf_act_nodup : forall sc, NoDup (a_active A sc);
  wf_act_dll : forall sc, 0 <= sc < 48 -> dll A (a_active A sc);
  wf_act_mem : forall sc ma, In ma (a_active A sc) ->
     exists mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\ mt_sc mt = sc;
  wf_unlinked : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     ~ In ma (a_active A (mt_sc mt)) -> mt_prev mt = 0 /\ mt_next mt = 0;
  (* [comment removed for export] *)
  wf_act_nonhead : forall sc ma mt, In ma (a_active A sc) -> ma <> hd 0 (a_active A sc) ->
     a_meta A ma = Some mt -> mt_avail mt = 0 /\ mt_freed mt <> 0;
  wf_act63 : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_sc mt = 63 -> mt_prev mt = 0 /\ mt_next mt = 0;
  (* [comment removed for export] *)
  wf_disj_area_grp : forall pg ma mt aib slots, In pg (a_areas A) ->
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 < mt_maplen mt ->
     pg + 4096 <= mt_mem mt \/ mt_mem mt + grp_map_len mt <= pg;
  wf_disj_grp_grp : forall ma mt aib slots ma' mt' aib' slots',
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 < mt_maplen mt ->
     a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' -> 0 < mt_maplen mt' ->
     ma <> ma' -> mt_mem mt + grp_map_len mt <= mt_mem mt' \/ mt_mem mt' + grp_map_len mt' <= mt_mem mt;
  wf_grp_mem_inj : forall ma mt aib slots ma' mt' aib' slots',
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' ->
     mt_mem mt = mt_mem mt' -> ma = ma';
  (* [comment removed for export] *)
  wf_live_map : forall p n, a_live A p = Some n <-> is_live A p n;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  wf_span : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     0 < mt_last mt -> mt_cnt mt * mt_stride mt < 2^20;
  (* [comment removed for export] *)
  wf_single : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_last mt = 0 -> 0 < mt_maplen mt -> mt_sc mt < 48 ->
     256 <= size_class (mt_sc mt) \/ mt_stride mt <= 16 * size_class (mt_sc mt);
  (* [comment removed for export] *)
  wf_inactive : forall ma mt aib slots j, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     aib mod 32 < j <= mt_last mt -> Z.testbit (mt_freed mt) j = true;
  (* [comment removed for export] *)
  wf_partial : forall sc ma mt aib slots ma' mt' aib' slots',
     In ma (a_active A sc) -> In ma' (a_active A sc) ->
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     a_meta A ma' = Some mt' -> mt_role mt' = RGroup aib' slots' ->
     aib mod 32 < mt_last mt -> aib' mod 32 < mt_last mt' -> ma = ma';
  (* [comment removed for export] *)
  wf_ctx_nonneg : forall k, 0 <= a_ctx A k;
  (* [comment removed for export] *)
  wf_nested_small : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_maplen mt = 0 -> 1 <= mt_last mt /\ 16 + mt_cnt mt * mt_stride mt <= 2048;
  (* [comment removed for export] *)
  wf_reusable : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_sc mt < 48 -> Z.lor (mt_avail mt) (mt_freed mt) <> 0 -> 16 * size_class (mt_sc mt) <= mt_stride mt;
  (* [comment removed for export] *)
  wf_cover : forall pa pm paib psl j ch x mtx aibx slx,
     a_meta A pa = Some pm -> mt_role pm = RGroup paib psl -> 0 <= j -> nth_error psl (Z.to_nat j) = Some (SNested ch) ->
     a_meta A x = Some mtx -> mt_role mtx = RGroup aibx slx ->
     slot_start pm j <= gext_lo mtx -> gext_hi mtx <= slot_end pm j ->
     exists mtc aibc slc, a_meta A ch = Some mtc /\ mt_role mtc = RGroup aibc slc /\
       gext_lo mtc <= gext_lo mtx /\ gext_hi mtx <= gext_hi mtc;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  wf_shift : a_ctx A KShift < 48;
  (* [comment removed for export] *)
  wf_noarea_shift : a_areas A = [] -> a_ctx A KAac = 0 -> a_ctx A KShift = 0;
  (* [comment removed for export] *)
  wf_brk0 : a_ctx A KBrk = 0 -> a_areas A = [] /\ a_pages A = [] /\ a_ctx A KAac = 0;
  (* [comment removed for export] *)
  wf_stride20 : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     mt_sc mt < 48 -> mt_stride mt < 2^20;
  (* [comment removed for export] *)
  wf_pages_al : forall pg, In pg (a_pages A) -> page_aligned pg /\ heap_range pg (pg + 4096);
  wf_disj_page_area : forall pg pg', In pg (a_pages A) -> In pg' (a_areas A) -> pg + 4096 <= pg' \/ pg' + 4096 <= pg;
  wf_disj_page_grp : forall pg ma mt aib slots, In pg (a_pages A) ->
     a_meta A ma = Some mt -> mt_role mt = RGroup aib slots -> 0 < mt_maplen mt ->
     pg + 4096 <= mt_mem mt \/ mt_mem mt + grp_map_len mt <= pg;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  wf_partial_sc : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     aib mod 32 < mt_last mt -> 7 <= mt_sc mt;
  (* [comment removed for export] *)
  wf_mblocks_len : Z.of_nat (length (a_mblocks A)) <=
     Z.of_nat (length (a_areas A)) + (if a_ctx A KAac =? 0 then 0 else 1);
  wf_mblocks_sz : forall c l, In (c, l) (a_mblocks A) ->
     0x1000 <= c /\ 0 < l <= 2 ^ (12 + Z.of_nat (length (a_mblocks A))) /\ c + l <= alloc_ceiling;
  (* [comment removed for export] *)
  wf_shift_mblocks : a_ctx A KShift <= Z.of_nat (length (a_mblocks A));
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  wf_shift_acct : 2 ^ (a_ctx A KShift + 1) <= Z.of_nat (length (a_areas A)) + a_ctx A KAac + a_ctx A KShift + 2 /\
                  2 ^ (a_ctx A KShift) <= Z.of_nat (length (a_areas A)) + a_ctx A KShift + 2 /\
                  Z.of_nat (length (a_mblocks A)) <= a_ctx A KShift
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint maps_pw (l : list (word * word)) : Prop :=
  match l with
  | [] => True
  | (a, n) :: r => region_free r a n = true /\ maps_pw r
  end.

(* [comment removed for export] *)
Definition mcov (l : list (word * word)) (x n : Z) : Prop :=
  exists b sz, In (b, sz) l /\ bv_unsigned b <= x /\ x + n <= bv_unsigned b + bv_unsigned sz.

Record VMok (A : astate) (h : VmMaps) : Prop := {
  (* [comment removed for export] *)
  vm_grp : forall ma mt aib slots, a_meta A ma = Some mt -> mt_role mt = RGroup aib slots ->
     0 < mt_maplen mt ->
     In (Z_to_bv 64 (mt_mem mt), Z_to_bv 64 (grp_map_len mt)) (vm_maps h) /\
     region_free (vm_noaccess h) (Z_to_bv 64 (mt_mem mt)) (Z_to_bv 64 (grp_map_len mt)) = true;
  (* [comment removed for export] *)
  vm_brk_ok : a_ctx A KBrk = 0 \/ a_ctx A KBrk = 2^64 - 1 \/
              (a_ctx A KBrk = bv_unsigned (vm_brk h) /\ 0 < bv_unsigned (vm_brk h) /\
               bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h) /\ page_aligned (bv_unsigned (vm_brk h)));
  (* [comment removed for export] *)
  vm_areas_res : a_ctx A KAac > 0 ->
     page_aligned (a_ctx A KAareas) /\
     a_ctx A KAareas + 4096 * a_ctx A KAac <= alloc_ceiling /\
     map_contains (vm_maps h) (Z_to_bv 64 (a_ctx A KAareas)) (Z_to_bv 64 (4096 * a_ctx A KAac)) = true /\
     map_contains (vm_noaccess h) (Z_to_bv 64 (a_ctx A KAareas)) (Z_to_bv 64 (4096 * a_ctx A KAac)) = true;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  vm_res : vm_reserved h = segments_reserved ml_segs;
  (* [comment removed for export] *)
  vm_brk_valid : 0 < bv_unsigned (vm_brk h) /\ bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h) /\
                 page_aligned (bv_unsigned (vm_brk h)) /\ bv_unsigned (vm_brk h) <= alloc_ceiling;
  (* [comment removed for export] *)
  vm_pw : maps_pw (vm_maps h);
  (* [comment removed for export] *)
  vm_maps_wf : forall b sz, In (b, sz) (vm_maps h) -> 0 < bv_unsigned sz /\ bv_unsigned b + bv_unsigned sz <= alloc_ceiling /\
     0x1000 <= bv_unsigned b /\ (bv_unsigned b + bv_unsigned sz <= IMG_LO \/ IMG_HI <= bv_unsigned b);
  (* [comment removed for export] *)
  vm_na_in : forall b sz, In (b, sz) (vm_noaccess h) -> 0 < bv_unsigned sz /\ mcov (vm_maps h) (bv_unsigned b) (bv_unsigned sz);
  (* [comment removed for export] *)
  vm_areas_cov : forall pg, In pg (a_areas A) ->
     mcov (vm_maps h) pg 4096 /\ region_free (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) = true;
  vm_pages_cov : forall pg, In pg (a_pages A) ->
     mcov (vm_maps h) pg 4096 /\ region_free (vm_noaccess h) (Z_to_bv 64 pg) (Z_to_bv 64 4096) = true;
  (* [comment removed for export] *)
  vm_all : forall b sz, In (b, sz) (vm_maps h) ->
      (exists ma mt aib slots, a_meta A ma = Some mt /\ mt_role mt = RGroup aib slots /\ 0 < mt_maplen mt /\
          bv_unsigned b = mt_mem mt /\ bv_unsigned sz = grp_map_len mt)
      \/ (bv_unsigned (vm_start_brk h) <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= bv_unsigned (vm_brk h))
      \/ (exists c l, In (c, l) (a_mblocks A ++ a_xmaps A) /\ c <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= c + l);
  (* [comment removed for export] *)
  vm_brk_span : (a_ctx A KBrk = 0 -> vm_brk h = vm_start_brk h) /\
      bv_unsigned (vm_brk h) - bv_unsigned (vm_start_brk h) <= 4096 * (Z.of_nat (length (a_areas A)) + 1);
  (* [comment removed for export] *)
  vm_top : alloc_top h = alloc_ceiling
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition owned_of (A : astate) (x : Z) : Prop := (LOCKA <= x < CTX_END) \/ dom A x.

(* [comment removed for export] *)
Definition ctx0 : ctx_rec := fun _ => 0.
Definition A0 : astate := AST ctx0 [] (fun _ => None) [] (fun _ => []) [] 0 (fun _ => None) [] [].

(* [comment removed for export] *)
Definition set_xmaps (A : astate) (l : list (Z * Z)) : astate :=
  AST (a_ctx A) (a_areas A) (a_meta A) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A) (a_live A) (a_mblocks A) l.
Definition set_mblocks (A : astate) (l : list (Z * Z)) : astate :=
  AST (a_ctx A) (a_areas A) (a_meta A) (a_freelist A) (a_active A) (a_pages A) (a_brk_lo A) (a_live A) l (a_xmaps A).

End WithLayout.

(* [comment removed for export] *)
Ltac llia := first [lia | pose proof layout_small; lia | pose proof layout_nums; lia].
Ltac lnia := first [nia | pose proof layout_small; nia | pose proof layout_nums; nia].

(* [comment removed for export] *)
Ltac ceil := let H := fresh "HCEIL" in pose proof alloc_ceiling_val as H.
