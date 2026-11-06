(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import PropExec CatExec Hoare.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.

Class MallocLayout := {
  (* [comment removed for export] *)
  ml_segs : list Segment;          (* [comment removed for export] *)
  IMG_LO : Z;                      (* [comment removed for export] *)
  RW_LO  : Z;                      (* [comment removed for export] *)
  IMG_HI : Z;                      (* [comment removed for export] *)

  (* [comment removed for export] *)
  A_LOCK : word;                   (* [comment removed for export] *)
  A_CTX : word;                    (* [comment removed for export] *)
  A_INIT_DONE : word;              (* [comment removed for export] *)
  A_MMAP_CTR : word;               (* [comment removed for export] *)
  A_FREE_META_HEAD : word;         (* [comment removed for export] *)
  A_AVAIL_META : word;             (* [comment removed for export] *)
  A_AVAIL_META_CNT : word;         (* [comment removed for export] *)
  A_AVAIL_AREA_CNT : word;         (* [comment removed for export] *)
  A_META_SHIFT : word;             (* [comment removed for export] *)
  A_AREA_HEAD : word;              (* [comment removed for export] *)
  A_AREA_TAIL : word;              (* [comment removed for export] *)
  A_AVAIL_AREAS : word;            (* [comment removed for export] *)
                                   (* [comment removed for export] *)
                                   (* [comment removed for export] *)
  Z_UNMAP_SEQ : Z;                 (* [comment removed for export] *)
  Z_BOUNCES : Z;                   (* [comment removed for export] *)
  A_SEQ : word;                    (* [comment removed for export] *)
  A_BRK : word;                    (* [comment removed for export] *)
  A_MALLOC_REPLACED : word;        (* [comment removed for export] *)

  (* [comment removed for export] *)
  A_LIBC : word;                   (* [comment removed for export] *)
  A_NEED_LOCKS : word;             (* [comment removed for export] *)
  A_PAGE_SIZE : word;              (* [comment removed for export] *)
  A_TP : word;                     (* [comment removed for export] *)
  A_ERRNO : word;                  (* [comment removed for export] *)
  A_GOT_SSP : word;                (* [comment removed for export] *)
  A_SSP : word;                    (* [comment removed for export] *)

  (* [comment removed for export] *)
  A_SIZE_CLASSES : word;           (* [comment removed for export] *)
  A_SMALL_CNT_TAB : word;          (* [comment removed for export] *)
  A_MED_CNT_TAB : word;            (* [comment removed for export] *)
  A_DEBRUIJN : word;               (* [comment removed for export] *)

  (* [comment removed for export] *)
  PC_MALLOC : word;                   (* [comment removed for export] *)
  PC_FREE : word;                     (* [comment removed for export] *)
  PC_CALLOC : word;
  PC_LIBC_FREE : word;                (* [comment removed for export] *)
  PC_MALLOC_IMPL : word;              (* [comment removed for export] *)
  PC_GET_META : word;
  PC_NTFREE : word;                   (* [comment removed for export] *)
  PC_ALLOC_META : word;               (* [comment removed for export] *)
  PC_ALLOC_SLOT : word;
  PC_ENFRAME : word;
  PC_ALLZEROP : word;                 (* [comment removed for export] *)
  PC_MMAP : word;                     (* [comment removed for export] *)
  PC_MPROTECT : word;                 (* [comment removed for export] *)
  PC_MUNMAP : word;                   (* [comment removed for export] *)
  PC_VM_WAIT : word;                  (* [comment removed for export] *)
  PC_SYSCALL_RET : word;              (* [comment removed for export] *)
  PC_ERRNO_LOC : word;                (* [comment removed for export] *)
  PC_LOCK : word;                     (* [comment removed for export] *)
  PC_UNLOCK : word;                   (* [comment removed for export] *)
  PC_MEMCPY : word;
  PC_MEMSET : word
}.

(* [comment removed for export] *)
Definition ml_rom {ML : MallocLayout} : word -> option byte := seg_rom ml_segs.

(* [comment removed for export] *)
Definition CTX_SIZE : Z := 928.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition size_classes_tab : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 12; 15; 18; 20; 25; 31; 36; 42; 50; 63;
   72; 84; 102; 127; 146; 170; 204; 255; 292; 340; 409; 511; 584; 682; 818;
   1023; 1169; 1364; 1637; 2047; 2340; 2730; 3276; 4095; 4680; 5460; 6552; 8191].
Definition size_class (i : Z) : Z := nth (Z.to_nat i) size_classes_tab 0.

Definition debruijn32_tab : list Z :=
  [0; 1; 28; 2; 29; 14; 24; 3; 30; 22; 20; 15; 25; 17; 4; 8;
   31; 27; 13; 23; 21; 19; 16; 7; 26; 12; 18; 6; 11; 5; 10; 9].
Definition debruijn (k : Z) : Z := nth (Z.to_nat k) debruijn32_tab 0.

Definition small_cnt_tab : list Z :=
  [30; 30; 30;  31; 15; 15;  20; 10; 10;  31; 15; 7;  25; 12; 6;
   21; 10; 5;  18; 8; 4;  31; 15; 7;  28; 14; 6].
Definition small_cnt (j : Z) : Z := nth (Z.to_nat j) small_cnt_tab 0.   (* [comment removed for export] *)

Definition med_cnt_tab : list Z := [28; 24; 20; 32].
Definition med_cnt (j : Z) : Z := nth (Z.to_nat j) med_cnt_tab 0.

(* [comment removed for export] *)
Fixpoint rom_bytes (rom : word -> option byte) (a : Z) (bs : list Z) : Prop :=
  match bs with
  | [] => True
  | b :: bs' => rom (Z_to_bv 64 a) = Some (Z_to_bv 8 b) /\ rom_bytes rom (a + 1) bs'
  end.

Class MallocLayoutOk (ML : MallocLayout) := {
  (* [comment removed for export] *)
  mlo_hull : 0 < IMG_LO /\ IMG_LO <= RW_LO /\ RW_LO <= IMG_HI /\ IMG_HI <= 2^32
             /\ IMG_LO mod 4096 = 0 /\ RW_LO mod 4096 = 0 /\ IMG_HI mod 4096 = 0;
  (* [comment removed for export] *)
  mlo_rom_out : forall a : word, (bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a) -> seg_rom ml_segs a = None;
  mlo_wview_out : forall (m : word -> option byte) (a : word),
      (bv_unsigned a < IMG_LO \/ IMG_HI <= bv_unsigned a) -> wview ml_segs m a = m a;
  (* [comment removed for export] *)
  mlo_wview_ro : forall (m : word -> option byte) (a : word),
      IMG_LO <= bv_unsigned a < RW_LO -> wview ml_segs m a = m a;
  (* [comment removed for export] *)
  mlo_wview_rw : forall (m : word -> option byte) (a : word),
      RW_LO <= bv_unsigned a < IMG_HI -> wview ml_segs m a <> None;
  (* [comment removed for export] *)
  mlo_rom_in : forall a : word, IMG_LO <= bv_unsigned a < IMG_HI -> seg_rom ml_segs a <> None;

  (* [comment removed for export] *)
  mlo_reserved_in : forall b sz, In (b, sz) (segments_reserved ml_segs) ->
      IMG_LO <= bv_unsigned b /\ bv_unsigned b + bv_unsigned sz <= IMG_HI /\ 0 < bv_unsigned sz;
  mlo_reserved_cover : forall a : Z, IMG_LO <= a < IMG_HI ->
      exists b sz, In (b, sz) (segments_reserved ml_segs) /\ bv_unsigned b <= a < bv_unsigned b + bv_unsigned sz;
  mlo_reserved_top : reserved_top (segments_reserved ml_segs) = IMG_HI;

  (* [comment removed for export] *)
  mlo_ctx : bv_unsigned A_CTX = bv_unsigned A_LOCK + 8;
  mlo_init_done : bv_unsigned A_INIT_DONE = bv_unsigned A_CTX + 8;
  mlo_mmap_ctr : bv_unsigned A_MMAP_CTR = bv_unsigned A_CTX + 12;
  mlo_free_meta_head : bv_unsigned A_FREE_META_HEAD = bv_unsigned A_CTX + 16;
  mlo_avail_meta : bv_unsigned A_AVAIL_META = bv_unsigned A_CTX + 24;
  mlo_avail_meta_cnt : bv_unsigned A_AVAIL_META_CNT = bv_unsigned A_CTX + 32;
  mlo_avail_area_cnt : bv_unsigned A_AVAIL_AREA_CNT = bv_unsigned A_CTX + 40;
  mlo_meta_shift : bv_unsigned A_META_SHIFT = bv_unsigned A_CTX + 48;
  mlo_area_head : bv_unsigned A_AREA_HEAD = bv_unsigned A_CTX + 56;
  mlo_area_tail : bv_unsigned A_AREA_TAIL = bv_unsigned A_CTX + 64;
  mlo_avail_areas : bv_unsigned A_AVAIL_AREAS = bv_unsigned A_CTX + 72;
  mlo_unmap_seq : Z_UNMAP_SEQ = bv_unsigned A_CTX + 848;
  mlo_bounces : Z_BOUNCES = bv_unsigned A_CTX + 880;
  mlo_seq : bv_unsigned A_SEQ = bv_unsigned A_CTX + 912;
  mlo_brk : bv_unsigned A_BRK = bv_unsigned A_CTX + 920;
  mlo_ctx_align : bv_unsigned A_CTX mod 8 = 0;          (* [comment removed for export] *)
  (* [comment removed for export] *)
  mlo_need_locks : bv_unsigned A_NEED_LOCKS = bv_unsigned A_LIBC + 3;
  mlo_page_size : bv_unsigned A_PAGE_SIZE = bv_unsigned A_LIBC + 48;
  mlo_libc_align : bv_unsigned A_LIBC mod 8 = 0;
  (* [comment removed for export] *)
  mlo_errno : bv_unsigned A_ERRNO = bv_unsigned A_TP - 164;
  mlo_tp_align : bv_unsigned A_TP mod 8 = 0;
  mlo_ssp_align : bv_unsigned A_SSP mod 8 = 0;
  mlo_got_ssp_align : bv_unsigned A_GOT_SSP mod 8 = 0;
  (* [comment removed for export] *)
  mlo_order_got : RW_LO <= bv_unsigned A_GOT_SSP /\ bv_unsigned A_GOT_SSP + 8 <= bv_unsigned A_ERRNO;
  mlo_order_errno : bv_unsigned A_ERRNO + 4 <= bv_unsigned A_TP;
  mlo_order_tp : bv_unsigned A_TP <= bv_unsigned A_SSP;
  mlo_order_ssp : bv_unsigned A_SSP + 8 <= bv_unsigned A_LIBC;
  mlo_order_libc : bv_unsigned A_LIBC + 56 <= bv_unsigned A_LOCK;
  mlo_order_ctx : bv_unsigned A_CTX + CTX_SIZE <= bv_unsigned A_MALLOC_REPLACED;
  mlo_order_replaced : bv_unsigned A_MALLOC_REPLACED + 4 <= IMG_HI;
  (* [comment removed for export] *)
  mlo_got_ssp : rom_bytes (seg_rom ml_segs) (bv_unsigned A_GOT_SSP)
                  (map (fun i => (bv_unsigned A_SSP / 2^(8*i)) mod 256) [0;1;2;3;4;5;6;7]);
  (* [comment removed for export] *)
  mlo_ctx_zero : forall a : word, bv_unsigned A_LOCK <= bv_unsigned a < bv_unsigned A_MALLOC_REPLACED + 4 ->
                 seg_rom ml_segs a = Some (Z_to_bv 8 0);

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  mlo_tables_ro : (IMG_LO <= bv_unsigned A_DEBRUIJN /\ bv_unsigned A_DEBRUIJN + 32 <= RW_LO)
                  /\ (IMG_LO <= bv_unsigned A_SIZE_CLASSES /\ bv_unsigned A_SIZE_CLASSES + 96 <= RW_LO)
                  /\ (IMG_LO <= bv_unsigned A_SMALL_CNT_TAB /\ bv_unsigned A_SMALL_CNT_TAB + 27 <= RW_LO)
                  /\ (IMG_LO <= bv_unsigned A_MED_CNT_TAB /\ bv_unsigned A_MED_CNT_TAB + 4 <= RW_LO);
  mlo_size_classes_align : bv_unsigned A_SIZE_CLASSES mod 2 = 0;
  mlo_size_classes : rom_bytes (seg_rom ml_segs) (bv_unsigned A_SIZE_CLASSES)
                       (flat_map (fun c => [c mod 256; c / 256]) size_classes_tab);
  mlo_debruijn : rom_bytes (seg_rom ml_segs) (bv_unsigned A_DEBRUIJN) debruijn32_tab;
  mlo_small_cnt : rom_bytes (seg_rom ml_segs) (bv_unsigned A_SMALL_CNT_TAB) small_cnt_tab;
  mlo_med_cnt : rom_bytes (seg_rom ml_segs) (bv_unsigned A_MED_CNT_TAB) med_cnt_tab;

  (* [comment removed for export] *)
  mlo_pcs : Forall (fun pc : word => IMG_LO <= bv_unsigned pc < RW_LO /\ bv_unsigned pc mod 4 = 0)
              [PC_MALLOC; PC_FREE; PC_CALLOC; PC_LIBC_FREE; PC_MALLOC_IMPL; PC_GET_META; PC_NTFREE;
               PC_ALLOC_META; PC_ALLOC_SLOT; PC_ENFRAME; PC_ALLZEROP; PC_MMAP; PC_MPROTECT; PC_MUNMAP;
               PC_VM_WAIT; PC_SYSCALL_RET; PC_ERRNO_LOC; PC_LOCK; PC_UNLOCK; PC_MEMCPY; PC_MEMSET]
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma find_segment_cons : forall s rest a n,
  find_segment (s :: rest) a n
  = if (Z.of_N (seg_base s) <=? a) && (a + n <=? Z.of_N (seg_base s) + Z.of_N (seg_size s))
    then Some s else find_segment rest a n.
Proof. reflexivity. Qed.

Definition seg_misses (a n : Z) (s : Segment) : Prop :=
  a < Z.of_N (seg_base s) \/ Z.of_N (seg_base s) + Z.of_N (seg_size s) < a + n.

Lemma find_segment_none : forall segs a n,
  Forall (seg_misses a n) segs -> find_segment segs a n = None.
Proof.
  induction segs as [|s rest IH]; intros a n H; [reflexivity|].
  rewrite find_segment_cons. inversion H as [|x l Hs Hrest]; subst.
  unfold seg_misses in Hs.
  destruct (Z.leb_spec0 (Z.of_N (seg_base s)) a);
    destruct (Z.leb_spec0 (a + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s))); cbn [andb];
    try (exfalso; lia); apply IH; exact Hrest.
Qed.

Lemma find_segment_hit : forall pre s rest a n,
  Forall (seg_misses a n) pre ->
  Z.of_N (seg_base s) <= a -> a + n <= Z.of_N (seg_base s) + Z.of_N (seg_size s) ->
  find_segment (pre ++ s :: rest) a n = Some s.
Proof.
  induction pre as [|p pre IH]; intros s rest a n Hpre Hlo Hhi.
  - cbn [app]. rewrite find_segment_cons.
    rewrite (proj2 (Z.leb_le _ _) Hlo), (proj2 (Z.leb_le _ _) Hhi). reflexivity.
  - cbn [app]. rewrite find_segment_cons. inversion Hpre as [|x l Hp Hrest]; subst.
    unfold seg_misses in Hp.
    destruct (Z.leb_spec0 (Z.of_N (seg_base p)) a);
      destruct (Z.leb_spec0 (a + n) (Z.of_N (seg_base p) + Z.of_N (seg_size p))); cbn [andb];
      try (exfalso; lia); apply IH; assumption.
Qed.

(* [comment removed for export] *)
Lemma seg_rom_unfold : forall segs (a : word),
  seg_rom segs a
  = match find_segment segs (bv_unsigned a) 1 with
    | Some seg => if seg_readable seg
                  then match segment_read_bytes (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) 1 with
                       | Some (b :: _) => Some b | _ => None end
                  else None
    | None => None
    end.
Proof.
  intros segs a. unfold seg_rom, memory_read. cbn [Z.of_N N.to_nat Pos.to_nat Pos.iter_op].
  destruct (find_segment segs (bv_unsigned a) 1) as [seg|]; [|reflexivity].
  destruct (seg_readable seg); reflexivity.
Qed.

Lemma seg_rom_none_of_find : forall segs (a : word),
  find_segment segs (bv_unsigned a) 1 = None -> seg_rom segs a = None.
Proof. intros segs a H. rewrite seg_rom_unfold, H. reflexivity. Qed.

Lemma seg_rom_some_of_find : forall segs (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> seg_readable seg = true ->
  segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) <> None ->
  seg_rom segs a <> None.
Proof.
  intros segs a seg H Hr Hb. rewrite seg_rom_unfold, H, Hr. cbn [segment_read_bytes].
  destruct (segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg)))); [discriminate | exact Hb].
Qed.

Lemma wview_of_find_none : forall segs m (a : word),
  find_segment segs (bv_unsigned a) 1 = None -> wview segs m a = m a.
Proof. intros segs m a H. unfold wview. rewrite H. destruct (m a); reflexivity. Qed.

Lemma wview_of_find_ro : forall segs m (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = false -> wview segs m a = m a.
Proof. intros segs m a seg H Hw. unfold wview. rewrite H, Hw. destruct (m a); reflexivity. Qed.

Lemma wview_of_find_rw : forall segs m (a : word) seg,
  find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true ->
  segment_byte_at (seg_bytes seg) (Z.to_N (bv_unsigned a - Z.of_N (seg_base seg))) <> None ->
  wview segs m a <> None.
Proof.
  intros segs m a seg H Hw Hb. unfold wview. rewrite H, Hw. destruct (m a); [discriminate | exact Hb].
Qed.

(* [comment removed for export] *)
Fixpoint Zseq (lo : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => lo :: Zseq (lo + 1) n' end.

Lemma Zseq_In : forall n lo x, lo <= x < lo + Z.of_nat n -> In x (Zseq lo n).
Proof.
  induction n as [|n IH]; intros lo x H; [lia|]. cbn.
  destruct (Z.eq_dec lo x) as [-> | Hne]; [left; reflexivity | right]. apply IH. lia.
Qed.

(* [comment removed for export] *)
Definition chk_range (f : Z -> bool) (lo : Z) (pages : nat) : bool :=
  forallb (fun pg => forallb (fun i => f (lo + 4096 * pg + i)) (Zseq 0 4096)) (Zseq 0 pages).

Lemma chk_range_sound : forall f lo pages, chk_range f lo pages = true ->
  forall a, lo <= a < lo + 4096 * Z.of_nat pages -> f a = true.
Proof.
  intros f lo pages H a Ha. unfold chk_range in H.
  rewrite forallb_forall in H.
  set (pg := (a - lo) / 4096). set (i := (a - lo) mod 4096).
  assert (Hpg : 0 <= pg < Z.of_nat pages).
  { subst pg. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  assert (Hi : 0 <= i < 4096) by (subst i; apply Z.mod_pos_bound; lia).
  assert (Ea : a = lo + 4096 * pg + i) by (subst pg i; pose proof (Z.div_mod (a - lo) 4096 ltac:(lia)); lia).
  specialize (H pg (Zseq_In pages 0 pg ltac:(lia))). rewrite forallb_forall in H.
  specialize (H i (Zseq_In 4096 0 i ltac:(lia))). rewrite Ea. exact H.
Qed.

(* [comment removed for export] *)
Definition chk_list (f : Z -> bool) (lo : Z) (n : nat) : bool := forallb f (Zseq lo n).

Lemma chk_list_sound : forall f lo n, chk_list f lo n = true ->
  forall a, lo <= a < lo + Z.of_nat n -> f a = true.
Proof.
  intros f lo n H a Ha. unfold chk_list in H. rewrite forallb_forall in H. apply H. apply Zseq_In. exact Ha.
Qed.

(* [comment removed for export] *)
Fixpoint chk_rom_bytes (rom : word -> option byte) (a : Z) (bs : list Z) : bool :=
  match bs with
  | [] => true
  | b :: bs' => match rom (Z_to_bv 64 a) with
               | Some v => (bv_unsigned v =? b mod 256) && chk_rom_bytes rom (a + 1) bs'
               | None => false
               end
  end.

Lemma chk_rom_bytes_sound : forall rom bs a,
  Forall (fun b => 0 <= b < 256) bs ->
  chk_rom_bytes rom a bs = true -> rom_bytes rom a bs.
Proof.
  intros rom bs; induction bs as [|b bs IH]; intros a Hbs H; [exact I|]. cbn in H |- *.
  inversion Hbs as [|x l Hb Hrest]; subst.
  destruct (rom (Z_to_bv 64 a)) as [v|] eqn:Hv; [|discriminate].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. split.
  - f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 v). f_equal. rewrite H1. apply Z.mod_small. exact Hb.
  - apply IH; assumption.
Qed.
