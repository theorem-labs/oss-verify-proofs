(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg FPInv CatExec StoreOk AxSymExec3 AxSymExec3Sound AxSymRun3.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require CatSim AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac RegsEquiv Bridge.
From OSSVerify.Proofs.fast_float.from_chars.lib.H Require Import HIface U_hbase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocModel MallocInv MallocLemmasBase.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfRepr.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMeta.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfMain.
Import OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocModel OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocLemmasBase OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfInv OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfRepr.MallocWfGeom OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMeta.MallocWfSurgery OSSVerify.Proofs.fast_float.from_chars.lib.ZC.MallocWfMain.MallocWfFree.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng MngRepr MngHeap MngWb MngSurgery.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAXU Require Import AxMalloc MngOwn AXG_ffstep AXF_ff3.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require MngRz2.
From OSSVerify.Proofs.fast_float.from_chars.lib.ZC Require MallocWfKf.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Image.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Abbreviation SEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Definition FNEED : Z := 8192.
Definition MNEED : Z := 8192.
Definition ERRNO : Z := 0x778ec.

(* [comment removed for export] *)
Record HS := mkHS { hs_L : layout ; hs_s : astate ; hs_can : Z ; hs_auxv : Z ; hs_rnd : Z ; hs_typs : list Z }.

(* [comment removed for export] *)
Abbreviation hs_set hs s := (mkHS (hs_L hs) s (hs_can hs) (hs_auxv hs) (hs_rnd hs) (hs_typs hs)).

(* [comment removed for export] *)
Definition env (m : word -> option byte) (can : Z) : Prop :=
  rdn SEGS m (wa 621603) 1 = Some (word_to_le_bytes 1 (wa 0)) /\
  (forall sc, 0 <= sc < 48 -> rdn SEGS m (wa (98984 + 2 * sc)) 2 = Some (word_to_le_bytes 2 (wa (znth sc size_classes)))) /\
  (forall j, 0 <= j < 32 -> rdn SEGS m (wa (98952 + j)) 1 = Some (word_to_le_bytes 1 (wa (znth j debruijn)))) /\
  0 <= can <= 2^64 - 1 /\
  rdn SEGS m (wa 416600) 8 = Some (word_to_le_bytes 8 (wa 0x97c00)) /\
  rdn SEGS m (wa 621568) 8 = Some (word_to_le_bytes 8 (wa can)) /\
  rdn SEGS m (wa 621712) 4 = Some (word_to_le_bytes 4 (wa 0)) /\
  (forall j, 0 <= j < 4 -> exists b, mrd SEGS m (wa (ERRNO + j)) = Some b) /\
  (forall d k, 0 <= d -> d + Z.of_nat k <= 4 -> store_ok SEGS m (wa (ERRNO + d)) k = true).

(* [comment removed for export] *)
Definition page_env (m : word -> option byte) : Prop :=
  rdn SEGS m (wa 621648) 8 = Some (word_to_le_bytes 8 (wa 4096)).

(* [comment removed for export] *)
Definition init_env (L : layout) (m : word -> option byte) (AUXV RND : Z) (typs : list Z) : Prop :=
  rdn SEGS m (wa 621608) 8 = Some (word_to_le_bytes 8 (wa AUXV)) /\
  1 <= AUXV /\ AUXV mod 8 = 0 /\ AUXV + 16 * Z.of_nat (length typs) + 8 <= 2^47 /\
  (forall i, (i < length typs)%nat ->
     1 <= nth i typs 0 <= 2^64 - 1 /\
     rdn SEGS m (wa (AUXV + 16 * Z.of_nat i)) 8 = Some (word_to_le_bytes 8 (wa (nth i typs 0))) /\
     (nth i typs 0 = 25 -> rdn SEGS m (wa (AUXV + 16 * Z.of_nat i + 8)) 8 = Some (word_to_le_bytes 8 (wa RND)))) /\
  rdn SEGS m (wa (AUXV + 16 * Z.of_nat (length typs))) 8 = Some (word_to_le_bytes 8 (wa 0)) /\
  In 25 typs /\
  1 <= RND /\ RND mod 8 = 0 /\ RND + 16 <= 2^47 /\
  rdn SEGS m (wa (RND + 8)) 8 = Some (word_to_le_bytes 8 (wa (ly_sec L))).

(* [comment removed for export] *)
Definition STATIC_P : list ivl :=
  [(621603, 621604); (98984, 99111); (98952, 98984); (416600, 416608); (621568, 621576); (621712, 621716);
   (0x97c98, 0x98038); (ERRNO, ERRNO + 4); (621648, 621656); (621608, 621616)].

(* [comment removed for export] *)
Definition FORB_P : list (Z * Z) := [(0x10000, 0x12000); (0x22000, 0x40000); (0x62000, 0x4000); (0x66000, 0x33000)].

Lemma rcovered_seg : forall md (k : nat) a n, vm_reserved (m_vmmaps md) = segments_reserved SEGS -> (k < 4)%nat ->
  bv_unsigned (fst (nth k (segments_reserved SEGS) (Z_to_bv 64 0, Z_to_bv 64 0))) <= a ->
  a + n <= bv_unsigned (fst (nth k (segments_reserved SEGS) (Z_to_bv 64 0, Z_to_bv 64 0))) + bv_unsigned (snd (nth k (segments_reserved SEGS) (Z_to_bv 64 0, Z_to_bv 64 0))) ->
  MngRz2.rcovered md a n.
Proof.
  intros md k a n Hres Hk H1 H2. unfold MngRz2.rcovered. exists (nth k (segments_reserved SEGS) (Z_to_bv 64 0, Z_to_bv 64 0)).
  split; [rewrite Hres; apply nth_In; change (length (segments_reserved SEGS)) with 4%nat; exact Hk | split; assumption].
Qed.

(* [comment removed for export] *)
Definition LINKv (HTOP : Z) (L : layout) (s : astate) (md : Model) : Prop :=
  forall md0, m_vmmaps md0 = m_vmmaps md -> m_halted md0 = None -> m_vm_lazy md0 = [] ->
    MngRz2.LINK HTOP FORB_P L (MallocWfKf.kf_of s) md0.

(* [comment removed for export] *)
Definition KRO (m : word -> option byte) : Prop := Image.pristine m 0x18288 0x182a8 /\ Image.pristine m 0x182a8 0x18327.

Lemma LINK_ext : forall HTOP L x md md0, MngRz2.LINK HTOP FORB_P L x md -> m_vmmaps md0 = m_vmmaps md -> m_halted md0 = None -> m_vm_lazy md0 = [] ->
  MngRz2.LINK HTOP FORB_P L x md0.
Proof.
  intros HTOP L x md md0 HL E Hh Hl. destruct HL. constructor; unfold MngRz2.rcovered in *; rewrite ?E; assumption.
Qed.

Lemma LINKv_of : forall HTOP L s md, MngRz2.LINK HTOP FORB_P L (MallocWfKf.kf_of s) md -> LINKv HTOP L s md.
Proof. intros HTOP L s md HL md0 E Hh Hl. exact (LINK_ext HTOP L _ md md0 HL E Hh Hl). Qed.

Lemma LINK_of_v : forall HTOP L s md, LINKv HTOP L s md -> md_ok md -> MngRz2.LINK HTOP FORB_P L (MallocWfKf.kf_of s) md.
Proof. intros HTOP L s md HL (Hh & Hl). exact (HL md eq_refl Hh Hl). Qed.

(* [comment removed for export] *)
Lemma LINK_init : forall HTOP L md,
  m_halted md = None -> m_vm_lazy md = [] -> vm_maps (m_vmmaps md) = [] -> alloc_top (m_vmmaps md) <= HTOP ->
  vm_reserved (m_vmmaps md) = segments_reserved SEGS -> ly_ctx L = 0x97c98 ->
  bv_unsigned (vm_brk (m_vmmaps md)) = ly_brk0 L -> PGSZ <= ly_brk0 L -> ly_brk0 L mod PGSZ = 0 ->
  bv_unsigned (Mmap.min_brk (m_vmmaps md)) <= ly_brk0 L -> ly_brk0 L <= HTOP ->
  vm_noaccess (m_vmmaps md) = [] -> 2 ^ 47 - 2 ^ 32 <= alloc_top (m_vmmaps md) -> 2 ^ 31 <= vm_limit (m_vmmaps md) ->
  MngRz2.LINK HTOP FORB_P L (MallocWfKf.kf_of init_state) md.
Proof.
  intros HTOP L md Hh Hl Hm Ht Hf Hc Hb1 Hb2 Hb3 Hb4 Hb5 Hna Hat Hlim.
  assert (NR : forall r, nth_error (MngRz2.kf_regions (MallocWfKf.kf_of init_state)) r = None) by (intros [|r]; reflexivity).
  constructor.
  - exact Hh.
  - exact Hl.
  - exact Ht.
  - rewrite Hm. exact I.
  - intros e He. rewrite Hm in He. destruct He.
  - intros e He. rewrite Hm in He. destruct He.
  - repeat constructor.
    + apply (rcovered_seg md 0 _ _ Hf); vm_compute; first [reflexivity | lia | discriminate].
    + apply (rcovered_seg md 1 _ _ Hf); vm_compute; first [reflexivity | lia | discriminate].
    + apply (rcovered_seg md 2 _ _ Hf); vm_compute; first [reflexivity | lia | discriminate].
    + apply (rcovered_seg md 3 _ _ Hf); vm_compute; first [reflexivity | lia | discriminate].
  - rewrite Hc. apply (rcovered_seg md 3 _ _ Hf); vm_compute; first [reflexivity | lia | discriminate].
  - intros r rg E. rewrite NR in E. discriminate E.
  - intros r1 r2 rg1 rg2 _ E. rewrite NR in E. discriminate E.
  - intros r rg o E. rewrite NR in E. discriminate E.
  - intros r rg (E & _). rewrite NR in E. discriminate E.
  - intros r rg (E & _). rewrite NR in E. discriminate E.
  - intros a Ha. destruct Ha.
  - split; [exact Hb1|]. intros r rg (E & _). rewrite NR in E. discriminate E.
  - split; [exact Hb2|]. split; [exact Hb3|]. split; [exact Hb4 | exact Hb5].
  - intros a Ha. rewrite Hna in Ha. discriminate Ha.
  - intros r rg (E & _). rewrite NR in E. discriminate E.
  - intros r rg E. rewrite NR in E. discriminate E.
  - reflexivity.
  - cbn. lia.
  - exact Hat.
  - exact Hlim.
  - rewrite Hf. apply Z.leb_le. vm_compute. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pcg_ok (s : astate) : Prop :=
  forall g am, MT s g = Some (MUsed am) -> am_aidx am < am_last am -> 0 < am_maplen am /\ am_sc am <> 0.

(* [comment removed for export] *)
Record Heap (HTOP : Z) (hs : HS) (m : word -> option byte) (md : Model) : Prop := mkHeap {
  hp_h0 : Heap0 (hs_L hs) (hs_s hs) m ;
  hp_ctx : ly_ctx (hs_L hs) = 0x97c98 ;
  hp_env : env m (hs_can hs) ;
  hp_kro : KRO m ;
  hp_link : LINKv HTOP (hs_L hs) (hs_s hs) md ;
  hp_pcg : pcg_ok (hs_s hs) ;
  hp_ap : forall rg, In rg (footprint (hs_s hs)) -> fst rg <> LCtx 0 -> ranges_disjoint (crange (hs_L hs) rg) (0x10000, 0x89000) ;
  hp_top : forall rg, In rg (footprint (hs_s hs)) -> loc_addr (hs_L hs) (fst rg) + snd rg <= HTOP ;
  hp_b1 : forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b ;
  hp_T20 : 2^20 <= HTOP ;
  hp_page : page_env m ;
  hp_inited : st_init_done (hs_s hs) = true ;
  hp_rap : forall r rg, region_of (hs_s hs) r = Some rg -> rg_live rg = true -> rg_kind rg <> RkMap ->
     ranges_disjoint (ly_reg (hs_L hs) r, rg_len rg) (0x10000, 0x89000) /\ 0 <= ly_reg (hs_L hs) r /\ ly_reg (hs_L hs) r + rg_len rg <= HTOP /\
     (forall r' rg', r' <> r -> region_of (hs_s hs) r' = Some rg' -> rg_live rg' = true ->
        ranges_disjoint (ly_reg (hs_L hs) r, rg_len rg) (ly_reg (hs_L hs) r', rg_len rg')) }.

(* [comment removed for export] *)
Lemma Heap_intro : forall HTOP hs m md,
  Heap0 (hs_L hs) (hs_s hs) m /\ ly_ctx (hs_L hs) = 0x97c98 /\ env m (hs_can hs) /\ KRO m /\ LINKv HTOP (hs_L hs) (hs_s hs) md /\
  pcg_ok (hs_s hs) /\
  (forall rg, In rg (footprint (hs_s hs)) -> fst rg <> LCtx 0 -> ranges_disjoint (crange (hs_L hs) rg) (0x10000, 0x89000)) /\
  (forall rg, In rg (footprint (hs_s hs)) -> loc_addr (hs_L hs) (fst rg) + snd rg <= HTOP) /\
  (forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b) /\ 2^20 <= HTOP /\ page_env m /\ st_init_done (hs_s hs) = true /\
  (forall r rg, region_of (hs_s hs) r = Some rg -> rg_live rg = true -> rg_kind rg <> RkMap ->
     ranges_disjoint (ly_reg (hs_L hs) r, rg_len rg) (0x10000, 0x89000) /\ 0 <= ly_reg (hs_L hs) r /\ ly_reg (hs_L hs) r + rg_len rg <= HTOP /\
     (forall r' rg', r' <> r -> region_of (hs_s hs) r' = Some rg' -> rg_live rg' = true ->
        ranges_disjoint (ly_reg (hs_L hs) r, rg_len rg) (ly_reg (hs_L hs) r', rg_len rg'))) ->
  Heap HTOP hs m md.
Proof. intros HTOP hs m md (A & B & C & D & E & F & G & H & I & J & K & L & M). exact (mkHeap HTOP hs m md A B C D E F G H I J K L M). Qed.

Lemma Heap_conj : forall HTOP hs m md, Heap HTOP hs m md ->
  Heap0 (hs_L hs) (hs_s hs) m /\ ly_ctx (hs_L hs) = 0x97c98 /\ env m (hs_can hs) /\ KRO m /\ LINKv HTOP (hs_L hs) (hs_s hs) md /\
  pcg_ok (hs_s hs) /\
  (forall rg, In rg (footprint (hs_s hs)) -> fst rg <> LCtx 0 -> ranges_disjoint (crange (hs_L hs) rg) (0x10000, 0x89000)) /\
  (forall rg, In rg (footprint (hs_s hs)) -> loc_addr (hs_L hs) (fst rg) + snd rg <= HTOP) /\
  (forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b) /\ 2^20 <= HTOP /\ page_env m /\ st_init_done (hs_s hs) = true /\
  (forall r rg, region_of (hs_s hs) r = Some rg -> rg_live rg = true -> rg_kind rg <> RkMap ->
     ranges_disjoint (ly_reg (hs_L hs) r, rg_len rg) (0x10000, 0x89000) /\ 0 <= ly_reg (hs_L hs) r /\ ly_reg (hs_L hs) r + rg_len rg <= HTOP /\
     (forall r' rg', r' <> r -> region_of (hs_s hs) r' = Some rg' -> rg_live rg' = true ->
        ranges_disjoint (ly_reg (hs_L hs) r, rg_len rg) (ly_reg (hs_L hs) r', rg_len rg'))).
Proof. intros HTOP hs m md [A B C D E F G H I J K L M]. exact (conj A (conj B (conj C (conj D (conj E (conj F (conj G (conj H (conj I (conj J (conj K (conj L M)))))))))))). Qed.

Definition blocks (hs : HS) : list (Z * Z) := map (fun b => (loc_addr (hs_L hs) (LMem (fst b)), snd b)) (user_blocks (hs_s hs)).

(* [comment removed for export] *)
Definition fivl (L : layout) (rg : loc * Z) : ivl := (loc_addr L (fst rg), loc_addr L (fst rg) + snd rg).

Definition nonempty (r : ivl) : bool := fst r <? snd r.

(* [comment removed for export] *)
Definition regs_ivl (hs : HS) : list ivl :=
  List.filter nonempty (flat_map (fun k => match region_of (hs_s hs) k with
                                           | Some rg => if rg_live rg then match rg_kind rg with
                                                                           | RkMap => []
                                                                           | _ => [(ly_reg (hs_L hs) k, ly_reg (hs_L hs) k + rg_len rg)]
                                                                           end else []
                                           | None => []
                                           end) (seq 0 (length (st_regions (hs_s hs))))).

Definition owned (hs : HS) : list ivl :=
  List.filter nonempty (flat_map (fun rg => carve (blocks hs) (fivl (hs_L hs) rg)) (footprint (hs_s hs))) ++ STATIC_P ++ regs_ivl hs.

Definition HI (HTOP : Z) : heap_iface := HeapIface HS (Heap HTOP) blocks owned.

Lemma outside_app' : forall (A B : list ivl) x, outside (A ++ B) x <-> outside A x /\ outside B x.
Proof. induction A as [|[lo hi] A IH]; intros B x; cbn; [tauto|]. rewrite IH. tauto. Qed.

Lemma stk_wmono : forall m m' lo hi, stk SEGS m lo hi -> wmono SEGS m m' -> stk SEGS m' lo hi.
Proof.
  intros m m' lo hi (H1 & H2 & H) Hw. split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as [Hwa (b & Hb)]. split; [apply (wmono_wview SEGS m m' Hw); exact Hwa|].
  unfold mrd in *. change (Mem.wa a) with (wa a) in *. destruct (m' (wa a)) as [b'|] eqn:E; [exists b'; reflexivity|].
  destruct (m (wa a)) as [b0|] eqn:E0; [exfalso; apply (Hw (wa a)); [rewrite E0; discriminate | exact E] | exists b; exact Hb].
Qed.

Lemma rdn_frame : forall m m' (a : Z) n, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat n -> m' (wa x) = m (wa x)) -> rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n.
Proof.
  intros m m' a n Ha Hn H. revert a Ha Hn H. induction n as [|n IH]; intros a Ha Hn H; [reflexivity|].
  rewrite (rdn_unfold SEGS m' (wa a) (S n)), (rdn_unfold SEGS m (wa a) (S n)). unfold mrd. change (Mem.wa a) with (wa a) in *. rewrite (H a) by lia.
  replace (wa a + 1)%bv with (wa (a + 1)) by (rewrite wa_add1; reflexivity).
  rewrite (IH (a + 1)) by (try lia; intros x Hx; apply H; lia). reflexivity.
Qed.

Lemma blocks_del_split : forall {A B} (f : A -> B) (l1 l2 : list A) (b0 : A),
  (forall b, In b (l1 ++ l2) -> f b <> f b0) -> forall y, In y (map f (l1 ++ l2)) <-> In y (map f (l1 ++ b0 :: l2)) /\ y <> f b0.
Proof.
  intros A B f l1 l2 b0 Hne y. rewrite !in_map_iff. split.
  - intros (b & <- & Hb). split; [exists b; split; [reflexivity | apply in_app_iff in Hb as [Hb|Hb]; apply in_app_iff; [left|right; right]; exact Hb]|].
    exact (Hne b Hb).
  - intros ((b & <- & Hb) & Hn). exists b. split; [reflexivity|]. apply in_app_iff in Hb as [Hb|[<-|Hb]]; apply in_app_iff; [left; exact Hb | contradiction | right; exact Hb].
Qed.

Lemma pairwise_app_cons : forall {A} (R : A -> A -> Prop) l1 x l2, pairwise R (l1 ++ x :: l2) ->
  forall y, In y (l1 ++ l2) -> R x y \/ R y x.
Proof.
  intros A R l1. induction l1 as [|a t IH]; intros x l2 HP y Hy; cbn [app] in *.
  - destruct HP as [H1 _]. left. apply H1. exact Hy.
  - destruct HP as [H1 H2]. destruct Hy as [<-|Hy].
    + right. apply H1. apply in_app_iff. right. left. reflexivity.
    + exact (IH x l2 H2 y Hy).
Qed.

Lemma map_app_cons : forall {A B} (f : A -> B) l1 x l2, map f (l1 ++ x :: l2) = map f l1 ++ f x :: map f l2.
Proof. intros. rewrite map_app. reflexivity. Qed.

Lemma footprint_ctx_len : forall s rg, In rg (footprint s) -> fst rg = LCtx 0 -> snd rg = CTX_SIZE.
Proof.
  intros s rg Hrg E. unfold footprint in Hrg. destruct Hrg as [<-|Hrg]; [reflexivity|].
  apply in_app_iff in Hrg as [Hrg|Hrg].
  - apply in_map_iff in Hrg as (a & <- & _). discriminate.
  - apply in_flat_map in Hrg as (k & _ & Hk). destruct (region_of s k) as [rg'|]; [|destruct Hk].
    destruct (rg_kind rg'); try destruct Hk. destruct (rg_live rg'); [|destruct Hk]. destruct Hk as [<-|[]]. discriminate.
Qed.

Lemma static_out_image : forall L s c x, WF s -> layout_ok L s -> ly_ctx L = 0x97c98 ->
  (forall rg, In rg (footprint s) -> fst rg <> LCtx 0 -> ranges_disjoint (crange L rg) (0x10000, 0x89000)) ->
  In c (image s) -> 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> ~ in_rng (cell_range L c) x.
Proof.
  intros L s c x HW HL Hctx HAP Hc Hx Hnc Hin.
  destruct (image_in_footprint s L c HW HL Hc) as (rg & Hrg & Hincl).
  unfold range_incl, cell_range, crange, in_rng in *. cbn [fst snd] in *.
  destruct (loc_eq_dec (fst rg) (LCtx 0)) as [E|E].
  - pose proof (footprint_ctx_len s rg Hrg E) as Hlen. rewrite E in Hincl. cbn [loc_addr] in Hincl. rewrite Hctx in Hincl.
    rewrite Hlen in Hincl. unfold CTX_SIZE in Hincl. lia.
  - pose proof (HAP rg Hrg E) as D. unfold ranges_disjoint, crange in D. cbn [fst snd] in D. lia.
Qed.

Ltac getr_leaf4 :=
  match goal with
  | |- context [getr ?R ?k] => is_concrete_map R;
      let b := eval vm_compute in (bv_eqb k 0) in
      let p := eval vm_compute in (bv_key k) in
      change (getr R k) with (if b then Z_to_bv 64 0 else match tget p R with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end.

Ltac resume4 MD := apply rz_of_evt; [exact MD|]; unfold mkR_of.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma outside_filter : forall (W : list ivl) x, outside (List.filter nonempty W) x <-> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x; [cbn; tauto|].
  change (List.filter nonempty ((lo, hi) :: W)) with (if nonempty (lo, hi) then (lo, hi) :: List.filter nonempty W else List.filter nonempty W).
  unfold nonempty at 1. cbn [fst snd]. change (outside ((lo, hi) :: W) x) with (~ (lo <= x < hi) /\ outside W x).
  destruct (lo <? hi) eqn:E.
  - change (outside ((lo, hi) :: List.filter nonempty W) x) with (~ (lo <= x < hi) /\ outside (List.filter nonempty W) x). rewrite IH. tauto.
  - rewrite IH. apply Z.ltb_ge in E. split; [intros H; split; [lia | exact H] | tauto].
Qed.

Lemma carve_sub : forall bs r r', In r' (carve bs r) -> fst r <= fst r' /\ snd r' <= snd r.
Proof.
  induction bs as [|b t IH]; intros r r' H; cbn [carve] in H.
  - destruct H as [<-|[]]. lia.
  - apply in_flat_map in H as [r1 [Hr1 H]]. pose proof (IH _ _ H) as [A B]. unfold cut1 in Hr1.
    destruct Hr1 as [<-|[<-|[]]]; cbn [fst snd] in *; lia.
Qed.

Section Own.
Variable HTOP : Z.

#[using="Type"] Lemma blocks_pos : forall hs m md, Heap HTOP hs m md -> forall b, In b (blocks hs) -> 1 <= snd b.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md HP b Hb. destruct HP as [_ _ _ _ _ _ _ _ Hb1 _ _ _]. unfold blocks in Hb.
  apply in_map_iff in Hb as [b' [<- Hb']]. cbn [snd]. exact (Hb1 b' Hb').
Qed.

#[using="Type"] Lemma owned_in0 : forall hs x rg, (forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b) -> In rg (footprint (hs_s hs)) ->
  loc_addr (hs_L hs) (fst rg) <= x < loc_addr (hs_L hs) (fst rg) + snd rg ->
  (forall b, In b (blocks hs) -> ~ (fst b <= x < fst b + snd b)) -> ~ outside (owned hs) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs x rg Hb1 Hrg Hx Hnb Ho. unfold owned in Ho. apply outside_app2 in Ho as [Ho _]. rewrite outside_filter in Ho.
  rewrite outside_flat_map in Ho. specialize (Ho rg Hrg).
  apply outside_carve in Ho; [|intros b Hb; unfold blocks in Hb; apply in_map_iff in Hb as [b' [<- Hb']]; cbn [snd]; pose proof (Hb1 b' Hb'); lia].
  unfold fivl in Ho. cbn [fst snd] in Ho. destruct Ho as [Ho | (b & Hb & Hxb)]; [exact (Ho Hx) | exact (Hnb b Hb Hxb)].
Qed.

#[using="Type"] Lemma owned_in : forall hs m md x rg, Heap HTOP hs m md -> In rg (footprint (hs_s hs)) ->
  loc_addr (hs_L hs) (fst rg) <= x < loc_addr (hs_L hs) (fst rg) + snd rg ->
  (forall b, In b (blocks hs) -> ~ (fst b <= x < fst b + snd b)) -> ~ outside (owned hs) x.
Proof. LiaFast.lf_pins LiaFast.u0. intros hs m md x rg HP. apply owned_in0. exact (hp_b1 HTOP hs m md HP). Qed.

#[using="Type"] Lemma block_of : forall hs b, In b (blocks hs) -> exists b0, In b0 (user_blocks (hs_s hs)) /\ b = block_range (hs_L hs) b0.
Proof. LiaFast.lf_pins LiaFast.u0. intros hs b Hb. unfold blocks in Hb. apply in_map_iff in Hb as [b0 [<- Hb0]]. exists b0. split; [exact Hb0 | reflexivity]. Qed.

#[using="Type"] Lemma owned_image0 : forall hs c x, WF (hs_s hs) -> layout_ok (hs_L hs) (hs_s hs) -> (forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b) ->
  In c (image (hs_s hs)) -> in_rng (cell_range (hs_L hs) c) x -> ~ outside (owned hs) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs c x HW HL Hb1 Hc Hx.
  destruct (image_in_footprint (hs_s hs) (hs_L hs) c HW HL Hc) as (rg & Hrg & Hincl).
  apply (owned_in0 hs x rg Hb1 Hrg).
  - unfold range_incl, crange, in_rng, cell_range in *. cbn [fst snd] in *. lia.
  - intros b Hb Hxb. destruct (block_of hs b Hb) as (b0 & Hb0 & ->).
    pose proof (image_outside_user_blocks (hs_s hs) (hs_L hs) c b0 HW HL Hc Hb0) as D.
    unfold ranges_disjoint, in_rng, cell_range, block_range in *. cbn [fst snd] in *. lia.
Qed.

#[using="Type"] Lemma owned_image : forall hs m md c x, Heap HTOP hs m md -> In c (image (hs_s hs)) -> in_rng (cell_range (hs_L hs) c) x ->
  ~ outside (owned hs) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md c x HP. pose proof HP as [(HW & (HL & _ & _) & _) _ _ _ _ _ _ _ Hb1 _ _ _].
  exact (owned_image0 hs c x HW HL Hb1).
Qed.

#[using="Type"] Lemma owned_markers0 : forall hs c x, WF (hs_s hs) -> layout_ok (hs_L hs) (hs_s hs) -> (forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b) ->
  In c (markers (hs_s hs)) -> in_rng (cell_range (hs_L hs) c) x -> ~ outside (owned hs) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs c x HW HL Hb1 Hc Hx.
  destruct (markers_home (hs_s hs) (hs_L hs) c HW Hc) as (rg & Hrg & Hincl).
  apply (owned_in0 hs x rg Hb1 Hrg).
  - unfold range_incl, crange, in_rng, cell_range in *. cbn [fst snd] in *. lia.
  - intros b Hb Hxb. destruct (block_of hs b Hb) as (b0 & Hb0 & ->).
    pose proof (markers_outside_blocks (hs_s hs) (hs_L hs) c b0 HW HL Hc Hb0) as D.
    unfold ranges_disjoint, in_rng, cell_range, block_range in *. cbn [fst snd] in *. lia.
Qed.

#[using="Type"] Lemma owned_markers : forall hs m md c x, Heap HTOP hs m md -> In c (markers (hs_s hs)) -> in_rng (cell_range (hs_L hs) c) x ->
  ~ outside (owned hs) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md c x HP. pose proof HP as [(HW & (HL & _ & _) & _) _ _ _ _ _ _ _ Hb1 _ _ _].
  exact (owned_markers0 hs c x HW HL Hb1).
Qed.

#[using="Type"] Lemma owned_static : forall hs x, ~ outside STATIC_P x -> ~ outside (owned hs) x.
Proof. LiaFast.lf_pins LiaFast.u0. intros hs x H Ho. unfold owned in Ho. apply outside_app2 in Ho as [_ Ho]. apply outside_app2 in Ho as [Ho _]. exact (H Ho). Qed.

#[using="Type"] Lemma disjoint_from_of_outside : forall (W : list ivl) a n, 0 < n -> (forall r, In r W -> fst r < snd r) ->
  (forall x, a <= x < a + n -> outside W x) -> disjoint_from W a n.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction W as [|[lo hi] W IH]; intros a n Hn Hne H; cbn [disjoint_from]; [exact I|].
  split.
  - pose proof (Hne _ (or_introl eq_refl)) as Hlh. cbn [fst snd] in Hlh.
    destruct (Z_le_dec (a + n) lo) as [L1|L1]; [left; exact L1|]. destruct (Z_le_dec hi a) as [L2|L2]; [right; exact L2|].
    exfalso. destruct (H (Z.max a lo) ltac:(lia)) as [Hx _]. lia.
  - apply IH; [exact Hn | intros r Hr; apply Hne; right; exact Hr|]. intros x Hx. exact (proj2 (H x Hx)).
Qed.

#[using="Type"] Lemma owned_nonempty_static : forall r, In r STATIC_P -> fst r < snd r.
Proof. LiaFast.lf_pins LiaFast.u0. intros r Hr. unfold STATIC_P, ERRNO in Hr. repeat (destruct Hr as [<-|Hr]; [cbn; lia|]). destruct Hr. Qed.

#[using="Type"] Lemma owned_nonempty : forall hs r, In r (owned hs) -> fst r < snd r.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs r Hr. unfold owned in Hr. apply in_app_iff in Hr as [Hr|Hr].
  - apply List.filter_In in Hr as [_ Hr]. unfold nonempty in Hr. apply Z.ltb_lt. exact Hr.
  - apply in_app_iff in Hr as [Hr|Hr]; [exact (owned_nonempty_static r Hr)|].
    unfold regs_ivl in Hr. apply List.filter_In in Hr as [_ Hr]. unfold nonempty in Hr. apply Z.ltb_lt. exact Hr.
Qed.

#[using="Type"] Lemma static_in_image : forall x, ~ outside STATIC_P x -> 0x10000 <= x < 0x99000.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros x H. unfold STATIC_P, ERRNO in H. cbn [outside] in H.
  destruct (Z_lt_le_dec x 0x10000) as [A|A]; [exfalso; apply H; repeat split; lia|].
  destruct (Z_lt_le_dec x 0x99000) as [B|B]; [lia | exfalso; apply H; repeat split; lia].
Qed.

#[using="Type"] Lemma not_outside_flat_map : forall {X} (f : X -> list ivl) (l : list X) x, ~ outside (flat_map f l) x ->
  exists y, In y l /\ ~ outside (f y) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros X f l x. induction l as [|a t IH]; intros H; [exfalso; apply H; exact I|].
  cbn [flat_map] in H. rewrite outside_app2 in H.
  destruct (outside_dec (f a) x) as [A|A]; [|exists a; split; [left; reflexivity | exact A]].
  destruct (IH ltac:(intros B; apply H; split; [exact A | exact B])) as (y & Hy & Hny). exists y. split; [right; exact Hy | exact Hny].
Qed.

#[using="Type"] Lemma regs_ivl_in : forall hs x, ~ outside (regs_ivl hs) x ->
  exists k rg, region_of (hs_s hs) k = Some rg /\ rg_live rg = true /\ rg_kind rg <> RkMap /\
    ly_reg (hs_L hs) k <= x < ly_reg (hs_L hs) k + rg_len rg.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs x H. unfold regs_ivl in H. rewrite outside_filter in H. destruct (not_outside_flat_map _ _ _ H) as (k & Hk & Hn).
  destruct (region_of (hs_s hs) k) as [rg|] eqn:E; [|exfalso; apply Hn; exact I].
  destruct (rg_live rg) eqn:El; [|exfalso; apply Hn; exact I].
  exists k, rg. split; [exact E|]. split; [exact El|].
  destruct (rg_kind rg) eqn:Ek; [| | exfalso; apply Hn; exact I];
    (split; [discriminate|]); cbn [outside] in Hn; lia.
Qed.

#[using="Type"] Lemma owned_bounds : forall hs m md x, Heap HTOP hs m md -> ~ outside (owned hs) x ->
  0 <= x < HTOP /\ (~ outside STATIC_P x \/ x < 0x10000 \/ 0x99000 <= x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md x HP Ho. pose proof HP as [(HW & (HL & _ & _) & _) Hctx _ _ _ _ HAP HHT _ HT20].
  destruct (outside_dec STATIC_P x) as [Hs|Hs].
  2:{ pose proof (static_in_image x Hs). split; [lia | left; exact Hs]. }
  unfold owned in Ho. rewrite !outside_app2 in Ho.
  destruct (outside_dec (regs_ivl hs) x) as [Hrg0|Hrg0].
  2:{ destruct (regs_ivl_in hs x Hrg0) as (k & rg & Ek & Lk & Kk & Bx).
      destruct (hp_rap HTOP hs m md HP k rg Ek Lk Kk) as (D & P0 & T & _). unfold ranges_disjoint in D. cbn [fst snd] in D.
      split; [lia|]. right. lia. }
  assert (Ho' : ~ outside (List.filter nonempty (flat_map (fun rg => carve (blocks hs) (fivl (hs_L hs) rg)) (footprint (hs_s hs)))) x) by tauto.
  rewrite outside_filter in Ho'. destruct (not_outside_flat_map _ _ _ Ho') as (rg & Hrg & Hn).
  assert (Hx : loc_addr (hs_L hs) (fst rg) <= x < loc_addr (hs_L hs) (fst rg) + snd rg).
  { destruct (Z_le_dec (loc_addr (hs_L hs) (fst rg)) x) as [A|A];
      [destruct (Z_lt_le_dec x (loc_addr (hs_L hs) (fst rg) + snd rg)) as [B|B]; [split; assumption|] |];
      exfalso; apply Hn; apply outside_carve; [intros b Hb; pose proof (blocks_pos hs m md HP b Hb); lia | left; unfold fivl; cbn [fst snd]; lia
                                              | intros b Hb; pose proof (blocks_pos hs m md HP b Hb); lia | left; unfold fivl; cbn [fst snd]; lia]. }
  pose proof HL as (_ & _ & _ & Lrng). pose proof (Lrng rg Hrg) as (R1 & R2). unfold crange in R1, R2. cbn [fst snd] in R1, R2.
  pose proof (HHT rg Hrg) as Htop.
  split; [lia|].
  destruct (loc_eq_dec (fst rg) (LCtx 0)) as [E|E].
  - left. pose proof (footprint_ctx_len (hs_s hs) rg Hrg E) as Hlen. rewrite E in Hx. cbn [loc_addr] in Hx. rewrite Hctx, Hlen in Hx.
    unfold CTX_SIZE in Hx. intro Ho2. cbn [STATIC_P outside] in Ho2. unfold ERRNO in Ho2. lia.
  - right. pose proof (HAP rg Hrg E) as D. unfold ranges_disjoint, crange in D. cbn [fst snd] in D. lia.
Qed.
End Own.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma markers_width : forall s c, In c (markers s) -> (1 <= mc_w c)%nat.
Proof.
  intros s c Hc. destruct (In_markers_inv s c Hc) as [(g & am & i & fr & _ & _ & Hc') | (g & am & _ & ->)]; [|cbn; lia].
  unfold marker_cells in Hc'. destruct Hc' as [<-|Hc']; [cbn; lia|]. apply in_app_iff in Hc' as [Hc'|Hc'].
  - destruct (0 <? _); [destruct Hc' as [<-|[]]; cbn; lia | destruct Hc'].
  - destruct (5 <=? _); [destruct Hc' as [<-|[<-|[]]]; cbn; lia | destruct Hc'].
Qed.

Lemma bview_grow : forall m m' x, mem_grows m m' -> bview SEGS m x <> None -> bview SEGS m' x <> None.
Proof.
  intros m m' x Hg H. destruct (bview SEGS m x) as [z|] eqn:E; [|exfalso; exact (H eq_refl)]. clear H.
  destruct (bview_some SEGS m x z E) as (Hx & Hw & Hr). unfold bview.
  replace ((0 <=? x) && (x <? 2^64)) with true by (symmetry; apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
  assert (Hw' : wview SEGS m' (wa x) <> None) by (apply (wmono_wview SEGS m m'); [exact Hg | exact Hw]).
  destruct (wview SEGS m' (wa x)) as [w|]; [|exact (fun _ => Hw' eq_refl)].
  cbn [ov_read_bytes] in *. destruct (m (wa x)) as [b|] eqn:Em.
  - destruct (m' (wa x)) as [b'|] eqn:Em'; [cbn; discriminate|]. exfalso. apply (Hg (wa x)); [rewrite Em; discriminate | exact Em'].
  - destruct (m' (wa x)) as [b'|] eqn:Em'; [cbn; discriminate|].
    destruct (memory_read SEGS (wa x) 1) as [[|b0 t]|]; cbn in Hr |- *; discriminate.
Qed.

Lemma mrd_of_bview : forall m x z, bview SEGS m x = Some z -> exists b, mrd SEGS m (wa x) = Some b.
Proof.
  intros m x z E. destruct (bview_some SEGS m x z E) as (_ & _ & Hr). cbn [ov_read_bytes] in Hr. unfold mrd, seg_rom.
  destruct (m (wa x)) as [b|]; [exists b; reflexivity|].
  destruct (memory_read SEGS (wa x) 1) as [[|b0 t]|]; try discriminate. exists b0. reflexivity.
Qed.

Section Client.
Variable HTOP : Z.

(* [comment removed for export] *)
#[using="Type"] Lemma owned_kept : forall hs m m' (W : list ivl) x, munch W m m' -> (forall x : Z, ~ outside W x -> outside (owned hs) x) ->
  0 <= x < 2^64 -> ~ outside (owned hs) x -> m' (wa x) = m (wa x).
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m m' W x MU HW Hx Ho. apply MU. rewrite u_wa_small by exact Hx.
  destruct (outside_dec W x) as [A|A]; [exact A | exfalso; exact (Ho (HW x A))].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma core_kept : forall hs m m', Heap0 (hs_L hs) (hs_s hs) m -> ly_ctx (hs_L hs) = 0x97c98 -> env m (hs_can hs) -> KRO m -> page_env m ->
  (forall rg, In rg (footprint (hs_s hs)) -> fst rg <> LCtx 0 -> ranges_disjoint (crange (hs_L hs) rg) (0x10000, 0x89000)) ->
  (forall b, In b (user_blocks (hs_s hs)) -> 1 <= snd b) -> mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> ~ outside (owned hs) x -> ~ (ERRNO <= x < ERRNO + 4) -> m' (wa x) = m (wa x)) ->
  Heap0 (hs_L hs) (hs_s hs) m' /\ env m' (hs_can hs) /\ KRO m' /\ page_env m'.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m m' (HW & (HL & HC & HFM) & HM) Hctx Henv Hkro Hpg HAP Hb1 Hwm HK.
  assert (KEEP0 : forall x, ~ outside (owned hs) x -> ~ (ERRNO <= x < ERRNO + 4) -> bview SEGS m' x = bview SEGS m x).
  { intros x Ho He. destruct (Z_lt_le_dec x 0) as [Hn|Hn].
    { unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hn). reflexivity. }
    destruct (Z_lt_le_dec x (2^64)) as [Hx|Hx].
    2:{ unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; exact Hx). reflexivity. }
    apply bview_ext. exact (HK x ltac:(lia) Ho He). }
  (* [comment removed for export] *)
  assert (NOERR : forall x rg, In rg (footprint (hs_s hs)) -> loc_addr (hs_L hs) (fst rg) <= x < loc_addr (hs_L hs) (fst rg) + snd rg ->
            ~ (ERRNO <= x < ERRNO + 4)).
  { intros x rg Hrg Hx He. destruct (loc_eq_dec (fst rg) (LCtx 0)) as [E|E].
    - pose proof (footprint_ctx_len (hs_s hs) rg Hrg E) as Hlen. rewrite E in Hx. cbn [loc_addr] in Hx. rewrite Hctx, Hlen in Hx.
      unfold CTX_SIZE, ERRNO in *. lia.
    - pose proof (HAP rg Hrg E) as D. unfold ranges_disjoint, crange in D. cbn [fst snd] in D. unfold ERRNO in He. lia. }
  assert (KEEPc : forall c, (exists rg, In rg (footprint (hs_s hs)) /\ range_incl (cell_range (hs_L hs) c) (crange (hs_L hs) rg)) ->
            (forall a, in_rng (cell_range (hs_L hs) c) a -> ~ outside (owned hs) a) ->
            forall a, in_rng (cell_range (hs_L hs) c) a -> bview SEGS m' a = bview SEGS m a).
  { intros c (rg & Hrg & Hincl) Hown a Ha. apply KEEP0; [exact (Hown a Ha)|]. apply (NOERR a rg Hrg).
    unfold range_incl, crange, in_rng, cell_range in *. cbn [fst snd] in *. lia. }
  assert (STK : forall a n, (forall j, 0 <= j < Z.of_nat n -> ~ outside STATIC_P (a + j) /\ ~ (ERRNO <= a + j < ERRNO + 4)) ->
            0 <= a -> a + Z.of_nat n <= 2^64 -> rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n).
  { intros a n H Ha Hn. apply rdn_frame; [exact Ha | exact Hn|]. intros x Hx. replace x with (a + (x - a)) by ring.
    destruct (H (x - a) ltac:(lia)) as [H1 H2]. apply (HK (a + (x - a)) ltac:(lia)); [apply owned_static; exact H1 | exact H2]. }
  split; [split; [exact HW | split; [split; [exact HL | split] | ]] |].
  - apply Forall_forall. intros c Hc. apply (cell_holds_frame (hs_L hs) (bview SEGS m) (bview SEGS m') c (image_cell_width _ c Hc)).
    + exact (proj1 (Forall_forall _ _) HC c Hc).
    + apply KEEPc; [exact (image_in_footprint (hs_s hs) (hs_L hs) c HW HL Hc) |]. intros a Ha. exact (owned_image0 hs c a HW HL Hb1 Hc Ha).
  - apply Forall_forall. intros rg Hrg x Hx. pose proof (proj1 (Forall_forall _ _) HFM rg Hrg x Hx) as Hm.
    destruct (outside_dec (owned hs) x) as [Ho|Ho]; [exact (bview_grow m m' x Hwm Hm)|].
    rewrite (KEEP0 x Ho (NOERR x rg Hrg Hx)). exact Hm.
  - apply Forall_forall. intros c Hc. apply (cell_holds_frame (hs_L hs) (bview SEGS m) (bview SEGS m') c (markers_width _ c Hc)).
    + exact (proj1 (Forall_forall _ _) HM c Hc).
    + apply KEEPc; [exact (markers_home (hs_s hs) (hs_L hs) c HW Hc) |]. intros a Ha. exact (owned_markers0 hs c a HW HL Hb1 Hc Ha).
  - destruct Henv as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
    Ltac stk_side := let jj := fresh "jj" in let Hjj := fresh "Hjj" in intros jj Hjj; cbn [STATIC_P outside]; unfold ERRNO; split; lia.
    split.
    { split; [rewrite STK by (first [stk_side | cbn; lia]); exact E1|].
      split; [intros sc Hsc; rewrite STK by (first [stk_side | cbn; lia]); exact (E2 sc Hsc)|].
      split; [intros j Hj; rewrite STK by (first [stk_side | cbn; lia]); exact (E3 j Hj)|].
      split; [exact E4|].
      split; [rewrite STK by (first [stk_side | cbn; lia]); exact E5|].
      split; [rewrite STK by (first [stk_side | cbn; lia]); exact E6|].
      split; [rewrite STK by (first [stk_side | cbn; lia]); exact E7|].
      split; [intros j Hj; destruct (E8 j Hj) as (b & Hb); unfold mrd in *;
              destruct (m' (wa (ERRNO + j))) as [b'|] eqn:Em'; [exists b'; reflexivity|];
              destruct (m (wa (ERRNO + j))) as [b0|] eqn:Em; [exfalso; apply (Hwm (wa (ERRNO + j))); [rewrite Em; discriminate | exact Em'] | exists b; exact Hb]|].
      intros d k Hd Hk. apply (store_ok_mono SEGS k m m'); [exact Hwm | exact (E9 d k Hd Hk)]. }
    split.
    { destruct Hkro as ((K1 & K2 & K3) & (K4 & K5 & K6)).
      split; (split; [assumption | split; [assumption|]]); intros j Hj; change (Mem.wa j) with (wa j);
        rewrite (HK j ltac:(lia)); first [ exact (K3 j Hj) | exact (K6 j Hj) | (apply owned_static; cbn [STATIC_P outside]; lia) | (unfold ERRNO; lia) ]. }
    unfold page_env in *. rewrite STK by (first [stk_side | cbn; lia]). exact Hpg.
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem heap_kept : forall hs m m' md, Heap HTOP hs m md -> mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> ~ outside (owned hs) x -> ~ (ERRNO <= x < ERRNO + 4) -> m' (wa x) = m (wa x)) ->
  Heap HTOP hs m' md.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m m' md HP Hwm HK. pose proof HP as [H0 Hctx Henv Hkro Hled Hpcg HAP HHT Hb1 HT20 Hpg Hini Hrap].
  destruct (core_kept hs m m' H0 Hctx Henv Hkro Hpg HAP Hb1 Hwm HK) as (H0' & Henv' & Hkro' & Hpg').
  exact (mkHeap HTOP hs m' md H0' Hctx Henv' Hkro' Hled Hpcg HAP HHT Hb1 HT20 Hpg' Hini Hrap).
Qed.

#[using="Type"] Theorem heap_frame_L4 : heap_frame SEGS HS (Heap HTOP) owned.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m m' md W HP MU Hwm HWo. apply (heap_kept hs m m' md HP Hwm).
  intros x Hx Ho _. exact (owned_kept hs m m' W x MU HWo Hx Ho).
Qed.

#[using="Type"] Theorem heap_blocks_ok_L4 : heap_blocks_ok SEGS HS (Heap HTOP) blocks owned 0x10000 0x99000 HTOP STATIC_P.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m md HP. split; [|intros x Ho; exact (owned_bounds HTOP hs m md x HP Ho)].
  pose proof HP as [(HW & (HL & HC & HFM) & HM) Hctx Henv Hkro Hled Hpcg HAP HHT Hb1 HT20 Hpg Hini Hrap].
  pose proof HL as (_ & Lal & Ldisj & Lrng).
  intros p n Hpn. destruct (block_of hs (p, n) Hpn) as (b0 & Hb0 & Eb). unfold block_range in Eb. injection Eb as Ep En.
  destruct (in_user_blocks_inv (hs_s hs) b0 Hb0) as (g & am & i & fr & Hu & Hi & Hfr & Kf & ->). cbn [fst snd] in Ep, En. subst n.
  apply (used_metas_usedX _ g am HW) in Hu as Ug.
  pose proof (inv_groups HW g am Ug) as (_ & _ & Gsl & _). pose proof (Gsl i Hi) as (_ & _ & S3). rewrite Hfr in S3.
  destruct S3 as (_ & _ & (Nf & Of & Ff & _) & _).
  destruct (used_group_region [] None U0 (hs_s hs) g am HW Ug) as (rg & Hr & Hk & Hl & Ho & He & _).
  assert (FG : In (LMem (SP (prid (am_mem am)) 0), rg_len rg) (footprint (hs_s hs))) by (apply footprint_region_In; assumption).
  pose proof (slot_in_span [] None U0 (hs_s hs) HW g am i Ug Hi) as [SI1 SI2].
  assert (Ep' : p = ly_reg (hs_L hs) (prid (am_mem am)) + poff (slot_start am i) + 16 * fr_off fr).
  { rewrite Ep. unfold frame_ptr, padd. rewrite <- (prid_slot_start am i). destruct (slot_start am i) as [rr oo] eqn:Es.
    cbn [prid poff]. unfold UNIT. ring. }
  pose proof (Lrng _ FG) as (R1 & R2). unfold crange in R1, R2. cbn [fst snd loc_addr] in R1, R2.
  pose proof (HHT _ FG) as Htop. cbn [fst snd loc_addr] in Htop.
  pose proof (HAP _ FG ltac:(discriminate)) as D. unfold ranges_disjoint, crange in D. cbn [fst snd loc_addr] in D.
  assert (INB : forall x, p <= x < p + fr_n fr -> ly_reg (hs_L hs) (prid (am_mem am)) <= x < ly_reg (hs_L hs) (prid (am_mem am)) + rg_len rg).
  { intros x Hx. rewrite Ep' in Hx. unfold group_extent, UNIT, IB in *. lia. }
  assert (Hn1 : 1 <= fr_n fr) by (exact (Hb1 _ Hb0)).
  split; [exact Hn1|]. split.
  { rewrite Ep'. unfold group_extent, UNIT, IB in *. lia. }
  split.
  { split; [rewrite Ep'; unfold UNIT in SI1; clear - R1 SI1 Ho Of; lia|]. split; [pose proof (INB (p + fr_n fr - 1) ltac:(lia)); lia|].
    intros a Ha. pose proof (INB a Ha) as Ba.
    assert (Hm : bview SEGS m a <> None) by (apply (proj1 (Forall_forall _ _) HFM _ FG); cbn [fst snd loc_addr]; lia).
    destruct (bview SEGS m a) as [z|] eqn:Ez; [|exfalso; exact (Hm eq_refl)].
    destruct (bview_some SEGS m a z Ez) as (_ & Hw & _). split; [exact Hw | exact (mrd_of_bview m a z Ez)]. }
  split.
  { apply disjoint_from_of_outside; [lia | apply owned_nonempty|]. intros x Hx. unfold owned. apply outside_app2. split.
    - rewrite outside_filter, outside_flat_map. intros rg' Hrg'. apply outside_carve; [intros b Hb; pose proof (blocks_pos HTOP hs m md HP b Hb); lia|].
      right. exists (p, fr_n fr). split; [exact Hpn | cbn [fst snd]; lia].
    - pose proof (INB x Hx) as Bx. apply outside_app2. split; [unfold STATIC_P, ERRNO; cbn [outside]; repeat split; lia|].
      destruct (outside_dec (regs_ivl hs) x) as [Hro|Hro]; [exact Hro|]. exfalso.
      destruct (regs_ivl_in hs x Hro) as (k0 & rg0 & Ek0 & Lk0 & Kk0 & Bx0).
      destruct (hp_rap HTOP hs m md HP k0 rg0 Ek0 Lk0 Kk0) as (_ & _ & _ & DR).
      assert (Hne0 : prid (am_mem am) <> k0) by (intros E; rewrite E in Hr; rewrite Hr in Ek0; injection Ek0 as <-; exact (Kk0 Hk)).
      pose proof (DR (prid (am_mem am)) rg ltac:(auto) Hr Hl) as D0. unfold ranges_disjoint in D0. cbn [fst snd] in D0. lia. }
  intros q k Hqk Hne. destruct (block_of hs (q, k) Hqk) as (b1 & Hb1' & Eb1).
  pose proof (user_blocks_disjoint (hs_s hs) (hs_L hs) HW HL) as PW.
  assert (Hb0' : In (frame_ptr am i fr, fr_n fr) (user_blocks (hs_s hs))) by exact Hb0.
  assert (Hne' : (frame_ptr am i fr, fr_n fr) <> b1).
  { intro E. apply Hne. rewrite Eb1, <- E. unfold block_range. cbn [fst snd]. rewrite Ep. reflexivity. }
  pose proof (pairwise_map_In _ (block_range (hs_L hs)) _ _ _ PW Hb0' Hb1' Hne') as D2.
  unfold block_range in Eb1. injection Eb1 as Eq Ek.
  change (p = loc_addr (hs_L hs) (LMem (frame_ptr am i fr))) in Ep.
  destruct D2 as [D2|D2]; unfold ranges_disjoint, block_range in D2; cbn [fst snd] in D2; change (q = loc_addr (hs_L hs) (LMem (fst b1))) in Eq; clear - D2 Ep Eq Ek; lia.
Qed.

#[using="Type"] Theorem heap_errno_frame : forall hs m m' md, Heap HTOP hs m md -> munch [(ERRNO, ERRNO + 4)] m m' -> mem_grows m m' -> Heap HTOP hs m' md.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros hs m m' md HP MU Hwm. apply (heap_kept hs m m' md HP Hwm).
  intros x Hx _ He. apply MU. rewrite u_wa_small by exact Hx. cbn [outside]. split; [exact He | exact I].
Qed.
End Client.

(* [comment removed for export] *)
Lemma pcg_of_ceq : forall s s', (forall q a, usedX [] s' q a -> exists a0, usedX [] s q a0 /\ ceq a a0) -> pcg_ok s -> pcg_ok s'.
Proof.
  intros s s' C HP g am M Ha. destruct (C g am ltac:(unfold usedX, MTX; cbn; exact M)) as (a0 & U0' & (Em & Eml & El & Es & Ea)).
  assert (M0 : MT s g = Some (MUsed a0)) by (unfold usedX, MTX in U0'; cbn in U0'; exact U0').
  rewrite Eml, Es. apply (HP g a0 M0). rewrite <- Ea, <- El. exact Ha.
Qed.

Lemma pcg_free : forall s p n tr s', WF s -> In (p, n) (user_blocks s) -> yields (free (Some p) s) tr (tt, s') -> pcg_ok s -> pcg_ok s'.
Proof.
  intros s p n tr s' HW Hin Hy HP. destruct (user_blocks_frame s p n HW Hin) as (g & am & idx & fr & Hu & Hi & Hfr & Hk & _ & ->).
  exact (itok_yields _ (fun r => pcg_ok (snd r)) tr (tt, s')
           (free_spec U0 s g am idx fr _ HW U0_nonneg Hu Hi Hfr Hk (fun s1 _ C _ => pcg_of_ceq s s1 C HP)) Hy).
Qed.

(* [comment removed for export] *)
Lemma inited_of_areas : forall s, WF s -> st_areas s <> [] -> st_init_done s = true.
Proof.
  intros s HW Ha. destruct (st_init_done s) eqn:E; [reflexivity|].
  pose proof (inv_ctx HW) as C. unfold ctx_ok in C.
  destruct C as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hi). destruct (Hi E) as (_ & Ha' & _). exfalso. exact (Ha Ha').
Qed.

Lemma areas_of_frame : forall s g am i fr, WF s -> In (g, am, i, fr) (frames s) -> st_areas s <> [].
Proof.
  intros s g am i fr HW HF. pose proof (get_meta_ok s g am i fr HW HF) as GM. cbn zeta in GM.
  destruct GM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (a & k & Ha & _) & _). intros E. rewrite E in Ha. destruct Ha.
Qed.

Lemma areas_kf : forall s s', MallocWfKf.kf_of s' = MallocWfKf.kf_of s -> st_areas s' = st_areas s.
Proof. intros s s' E. unfold MallocWfKf.kf_of in E. injection E as Er Eb Ea. exact Ea. Qed.

Lemma regions_kf : forall s s', MallocWfKf.kf_of s' = MallocWfKf.kf_of s -> st_regions s' = st_regions s.
Proof. intros s s' E. unfold MallocWfKf.kf_of in E. injection E as Er Eb Ea. exact Er. Qed.

Section FC.
Variable cfg : SpuriousCfg.
Variable HTOP : Z.

(* [comment removed for export] *)
Definition free_k (fx : FPState) (regs : bvmap 5 word) (m : word -> option byte) (md : Model) (hs : HS) (p k : Z) (ret : word) (K : TSet) : Prop :=
  forall (fx' : FPState) regs' m'' md' hs',
    @fp_csr fx' = @fp_csr fx -> Heap HTOP hs' m'' md' -> md_ok md' -> AllocNodesCfg.vm_only md md' -> (U md' <= U md)%Z ->
    (forall a, ~ outside U_KEEP a -> m'' (wa a) = m (wa a)) ->
    blocks_del (blocks hs) (blocks hs') (p, k) ->
    callee_saved regs regs' ->
    munch (owned hs ++ owned hs' ++ [(p, p + k); (sp_of regs - FNEED, sp_of regs)]) m m'' ->
    stk SEGS m'' (sp_of regs - FNEED) (sp_of regs) ->
    realizes_cfg SEGS cfg (mkCfg (@mkst fx' regs' ret m'' (seg_rom SEGS)) md') K.

(* [comment removed for export] *)
#[using="Type"] Theorem free_finish : forall (fx : FPState) regs m md hs p k ret K R m' md' hs',
  md_ok md' -> getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z -> callee_same R regs ->
  Heap HTOP hs' m' md' -> AllocNodesCfg.vm_only md md' -> (U md' <= U md)%Z ->
  (forall a, ~ outside U_KEEP a -> m' (wa a) = m (wa a)) ->
  blocks_del (blocks hs) (blocks hs') (p, k) ->
  munch (owned hs ++ owned hs' ++ [(p, p + k); (sp_of regs - FNEED, sp_of regs)]) m m' ->
  stk SEGS m' (sp_of regs - FNEED) (sp_of regs) ->
  free_k fx regs m md hs p k ret K ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx R (wa 0x53574) m' (seg_rom SEGS)) md') K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fx regs m md hs p k ret K R m' md' hs' MD Hra Hret Hcs HP' Hvm HU HKP Hbd HMU ST CONT.
  destruct MD as [Hh Hl].
  resume4 (conj Hh Hl). change (wa 341364) with (Z_to_bv 64 341364).
  step.
  apply evt_exit_rz. intros fx' r' HR' Hfc.
  assert (C1 : getr R 1 = getr regs 1).
  { pose proof (Hcs 1%nat ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])) as C. match type of Hra with getr _ ?r = _ =>
      replace (Z_to_bv 5 (Z.of_nat 1)) with r in C by (apply bv_eq; reflexivity) end. exact C. }
  rewrite C1, Hra, (ret_pc_even_w ret Hret).
  apply (CONT fx' r' m' md' hs' Hfc HP' (conj Hh Hl) Hvm HU HKP Hbd); [|exact HMU | exact ST].
  Ltac cs1 HR' Hcs n := rewrite HR'; getr_leaf4;
    let C := fresh "C" in pose proof (Hcs n ltac:(clear; first [ AxSymRun3.memb_refl | AxSymRun3.incl_refl | cbn [In]; tauto ])) as C;
    match goal with |- getr _ ?r = _ => replace r with (Z_to_bv 5 (Z.of_nat n)) by (apply bv_eq; reflexivity) end; exact C.
  unfold callee_saved.
  split; [cs1 HR' Hcs 2%nat|]. split; [cs1 HR' Hcs 3%nat|]. split; [cs1 HR' Hcs 4%nat|]. split; [cs1 HR' Hcs 8%nat|].
  split; [cs1 HR' Hcs 9%nat|]. split; [cs1 HR' Hcs 18%nat|]. split; [cs1 HR' Hcs 19%nat|]. split; [cs1 HR' Hcs 20%nat|].
  split; [cs1 HR' Hcs 21%nat|]. split; [cs1 HR' Hcs 22%nat|]. split; [cs1 HR' Hcs 23%nat|]. split; [cs1 HR' Hcs 24%nat|].
  split; [cs1 HR' Hcs 25%nat|]. split; [cs1 HR' Hcs 26%nat|]. cs1 HR' Hcs 27%nat.
Qed.

#[using="Type"] Lemma footprint_kf_eq : forall s s', MallocWfKf.kf_of s' = MallocWfKf.kf_of s -> footprint s' = footprint s.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros s s' E. unfold MallocWfKf.kf_of in E. injection E as Er Eb Ea. unfold footprint, region_of. rewrite Er, Ea. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma keep_static : forall a, ~ outside U_KEEP a -> 0x10000 <= a < 0x99000 /\ ~ (0x97c98 <= a < 0x98038).
Proof. LiaFast.lf_pins LiaFast.u0. intros a Ha. unfold U_KEEP in Ha. cbn [outside] in Ha. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem free_contract_step : forall (fx : FPState) regs m md hs (p k : Z) (ret : word) (K : TSet) g am i fr s' R m',
  Heap HTOP hs m md -> md_ok md ->
  getr regs 1 = ret -> (bv_unsigned ret mod 2 = 0)%Z ->
  (sp_of regs mod 16 = 0)%Z -> (sp_of regs <= 2^47)%Z -> (HTOP <= sp_of regs - FNEED)%Z ->
  stk SEGS m (sp_of regs - FNEED) (sp_of regs) ->
  In (g, am, i, fr) (frames (hs_s hs)) -> fr_kind fr = FUser ->
  p = loc_addr (hs_L hs) (LMem (frame_ptr am i fr)) -> k = fr_n fr ->
  CatSim.msteps SEGS (@mkst fx regs (wa 0x52f88) m (seg_rom SEGS)) (@mkst fx R (wa 0x53574) m' (seg_rom SEGS)) ->
  callee_same R regs ->
  free (Some (frame_ptr am i fr)) (hs_s hs) = IRet (tt, s') ->
  MallocWfKf.kf_of s' = MallocWfKf.kf_of (hs_s hs) ->
  Heap0 (hs_L hs) s' m' ->
  mem_grows m m' ->
  (forall x, 0 <= x < 2^64 -> ~ (sp_of regs - FNEED <= x < sp_of regs) ->
     (forall c, In c (image (hs_s hs)) -> ~ in_rng (cell_range (hs_L hs) c) x) -> m' (wa x) = m (wa x)) ->
  free_k fx regs m md hs p k ret K ->
  realizes_cfg SEGS cfg (mkCfg (@mkst fx regs (Z_to_bv 64 0x52f88) m (seg_rom SEGS)) md) K.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros fx regs m md hs p k ret K g am i fr s' R m' HP MD Hra Hret AL Hsp47 HT ST HF Hk Ep Ek Hms Hcs Hit Hkf H0' Hwm Hfr CONT.
  pose proof MD as [Hh Hl].
  eapply rzc_isteps; [exact Hh | exact Hl | apply catsim_isteps; exact Hms|].
  pose proof HP as HP0. destruct HP as [H0 Hctx Henv Hkro Hled Hpcg HAP HHT Hb1 HT20 Hpg Hini Hrap].
  pose proof H0 as (HW & HR & HM).
  pose proof HR as (HL & HC & HFM).
  assert (Hfp : footprint s' = footprint (hs_s hs)) by exact (footprint_kf_eq _ _ Hkf).
  assert (Hb : In (frame_ptr am i fr, fr_n fr) (user_blocks (hs_s hs))).
  { destruct (in_frames_inv _ _ _ _ _ HF) as (Hu & Hi & Hfri). unfold user_blocks. apply in_flat_map. exists (g, am). split; [exact Hu|].
    cbn [snd]. apply in_flat_map. exists i. split; [apply In_zseq; lia|]. rewrite Hfri, Hk. left. reflexivity. }
  destruct (free_blocks (hs_s hs) (frame_ptr am i fr) (fr_n fr) [] s' HW Hb ltac:(rewrite Hit; reflexivity)) as (l1 & l2 & El & El').
  assert (FX : forall x, 0x10000 <= x < 0x99000 -> ~ (0x97c98 <= x < 0x98038) -> m' (wa x) = m (wa x)).
  { intros x Hx Hnc. apply Hfr; [lia | unfold FNEED in *; clear - Hx HT HT20; lia |].
    intros c Hc. apply (static_out_image (hs_L hs) (hs_s hs) c x HW HL Hctx HAP Hc); lia. }
  apply (free_finish fx regs m md hs p k ret K R m' md (hs_set hs s') MD Hra Hret Hcs).
  - (* [comment removed for export] *)
    assert (Hsub : forall b, In b (user_blocks s') -> In b (user_blocks (hs_s hs))).
    { intros b Hb'. rewrite El' in Hb'. rewrite El. apply in_app_iff in Hb' as [Hb'|Hb']; apply in_app_iff; [left|right; right]; exact Hb'. }
    assert (FR : forall a n, 0x10000 <= a -> a + Z.of_nat n <= 0x99000 -> a + Z.of_nat n <= 0x97c98 \/ 0x98038 <= a ->
                   rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n).
    { intros a n Ha Hn Hnc. apply rdn_frame; [lia | lia |]. intros x Hx. apply FX; lia. }
    destruct Henv as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
    apply Heap_intro. split; [exact H0'|]. split; [exact Hctx|]. split.
    { split; [rewrite FR by (cbn; lia); exact E1|]. split; [intros sc Hsc; rewrite FR by (cbn; lia); exact (E2 sc Hsc)|].
      split; [intros j Hj; rewrite FR by (cbn; lia); exact (E3 j Hj)|].
      split; [exact E4|]. split; [rewrite FR by (cbn; lia); exact E5|]. split; [rewrite FR by (cbn; lia); exact E6|].
      split; [rewrite FR by (cbn; lia); exact E7|].
      split; [intros j Hj; destruct (E8 j Hj) as (b0 & Hb0); exists b0; unfold mrd in *; rewrite FX by (unfold ERRNO; lia); exact Hb0|].
      intros d k0 Hd Hk0. apply (store_ok_mono SEGS k0 m m'); [exact Hwm | exact (E9 d k0 Hd Hk0)]. }
    split.
    { destruct Hkro as ((K1 & K2 & K3) & (K4 & K5 & K6)).
      split; (split; [assumption | split; [assumption|]]); intros j Hj; change (Mem.wa j) with (wa j);
        rewrite (FX j ltac:(lia) ltac:(lia)); first [ exact (K3 j Hj) | exact (K6 j Hj) ]. }
    split; [unfold LINKv in *; cbn [hs_s hs_L]; rewrite Hkf; exact Hled|].
    split; [exact (pcg_free (hs_s hs) (frame_ptr am i fr) (fr_n fr) [] s' HW Hb ltac:(rewrite Hit; reflexivity) Hpcg)|].
    split; [cbn [hs_s hs_L]; rewrite Hfp; exact HAP|]. split; [cbn [hs_s hs_L]; rewrite Hfp; exact HHT|].
    split; [intros b Hb'; apply Hb1; apply Hsub; exact Hb'|]. split; [exact HT20|].
    split; [unfold page_env in *; rewrite FR by (cbn; lia); exact Hpg|].
    split; [apply inited_of_areas; [exact (proj1 H0') | cbn [hs_s]; rewrite (areas_kf _ _ Hkf); exact (areas_of_frame _ _ _ _ _ HW HF)]|].
    cbn [hs_s hs_L]. unfold region_of. rewrite (regions_kf _ _ Hkf). exact Hrap.
  - exact (AllocNodesCfg.vm_only_refl md).
  - lia.
  - intros a Ha. destruct (keep_static a Ha) as (A1 & A2). exact (FX a A1 A2).
  - (* [comment removed for export] *)
    unfold blocks. cbn [hs_s hs_L]. rewrite El, El'. intros y. rewrite Ep, Ek.
    change (loc_addr (hs_L hs) (LMem (frame_ptr am i fr)), fr_n fr) with ((fun b : sptr * Z => (loc_addr (hs_L hs) (LMem (fst b)), snd b)) (frame_ptr am i fr, fr_n fr)).
    apply blocks_del_split. intros b Hbb E. injection E as E1' E2'.
    pose proof (user_blocks_disjoint (hs_s hs) (hs_L hs) HW HL) as PW. rewrite El, map_app_cons in PW.
    assert (Hb' : In (block_range (hs_L hs) b) (map (block_range (hs_L hs)) (l1 ++ l2))) by (apply in_map; exact Hbb).
    rewrite map_app in Hb'.
    destruct (pairwise_app_cons _ _ _ _ PW (block_range (hs_L hs) b) Hb') as [D|D];
      unfold ranges_disjoint, block_range in D; cbn [fst snd loc_addr] in D, E1'; cbn [loc_addr fst snd] in E1';
      pose proof (Hb1 b ltac:(rewrite El; apply in_app_iff in Hbb as [Hbb|Hbb]; apply in_app_iff; [left|right; right]; exact Hbb)) as Hn1;
      pose proof (Hb1 _ Hb) as Hn2; cbn [snd] in Hn1, Hn2; lia.
  - intros x Hx. apply outside_app' in Hx as (Ho1 & Ho2). apply outside_app' in Ho2 as (_ & Ho3).
    cbn [outside] in Ho3. destruct Ho3 as (_ & Ho3 & _).
    rewrite <- (wa_u x). apply Hfr; [pose proof (u64_range x); lia | lia |].
    intros c Hc Hin. exact (owned_image HTOP hs m md c (bv_unsigned x) HP0 Hc Hin Ho1).
  - exact (stk_wmono m m' _ _ ST Hwm).
  - exact CONT.
Qed.
End FC.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem heap_model_vm : forall HTOP hs m md md', Heap HTOP hs m md -> m_vmmaps md' = m_vmmaps md -> Heap HTOP hs m md'.
Proof.
  intros HTOP hs m md md' HP E. destruct HP as [H0 Hctx Henv Hkro Hled Hpcg HAP HHT Hb1 HT20 Hpg Hini Hrap].
  constructor; try assumption.
  intros md0 E0 Hh Hl. apply Hled; [rewrite E0, E; reflexivity | exact Hh | exact Hl].
Qed.

(* [comment removed for export] *)
Record HeapI (HTOP : Z) (hs : HS) (m : word -> option byte) (md : Model) : Prop := mkHeapI {
  hq_s : hs_s hs = init_state ;
  hq_h0 : Heap0 (hs_L hs) (hs_s hs) m ;
  hq_ctx : ly_ctx (hs_L hs) = 0x97c98 ;
  hq_env : env m (hs_can hs) ;
  hq_kro : KRO m ;
  hq_link : LINKv HTOP (hs_L hs) (hs_s hs) md ;
  hq_T20 : 2^20 <= HTOP ;
  hq_page : page_env m ;
  hq_init : init_env (hs_L hs) m (hs_auxv hs) (hs_rnd hs) (hs_typs hs) ;
  hq_iimg : 0x99000 <= hs_auxv hs /\ 0x99000 <= hs_rnd hs }.

(* [comment removed for export] *)
Definition INIT (hs : HS) : list ivl :=
  [(hs_auxv hs, hs_auxv hs + 16 * Z.of_nat (length (hs_typs hs)) + 8); (hs_rnd hs + 8, hs_rnd hs + 16)].

(* [comment removed for export] *)
Lemma heap0_init : forall (L : layout) m, ly_ctx L = 0x97c98 ->
  (forall x, 0x97c98 <= x < 0x98038 -> bview SEGS m x = Some 0) -> Heap0 L init_state m.
Proof.
  intros L m Hctx HZ. unfold Heap0.
  { split; [exact wf_init|]. split.
    - split.
      + split; [rewrite Hctx; reflexivity|]. split; [intros k rg Hr; destruct k; discriminate|].
        split; [rewrite footprint_init; cbn; repeat split; intros y []|].
        intros rg Hrg. rewrite footprint_init in Hrg. destruct Hrg as [<-|[]]. cbn. rewrite Hctx. unfold CTX_SIZE. lia.
      + split.
        * rewrite image_init. apply Forall_forall. intros c Hc. unfold ctx_cells in Hc. cbn [hs_L].
          assert (HV : forall c, In c (ctx_cells init_state) -> sval_num L (mc_val c) = 0 /\ (forall z, mc_val c <> VLo5 z) /\
                          0 <= loc_addr L (mc_loc c) - 0x97c98 /\ loc_addr L (mc_loc c) + Z.of_nat (mc_w c) <= 0x98038).
          { intros c0 Hc0. unfold ctx_cells in Hc0. cbn [st_init_done st_mmap_counter st_free_meta_head st_areas st_avail_meta_count
              st_avail_meta_area_count st_meta_alloc_shift st_area_head st_area_tail st_seq st_brk st_active st_usage st_unmap_seq st_bounces init_state] in Hc0.
            unfold CTX_secret, CTX_init_done, CTX_mmap_counter, CTX_free_meta_head, CTX_avail_meta, CTX_avail_meta_count,
              CTX_avail_meta_area_count, CTX_meta_alloc_shift, CTX_meta_area_head, CTX_meta_area_tail, CTX_avail_meta_areas,
              CTX_seq, CTX_brk, CTX_active, CTX_usage, CTX_unmap_seq, CTX_bounces in Hc0.
            apply in_app_iff in Hc0 as [Hc0|Hc0].
            { repeat (destruct Hc0 as [<-|Hc0]; [cbn; rewrite Hctx; split; [reflexivity|]; split; [intros z; discriminate | lia]|]). destruct Hc0. }
            repeat (apply in_app_iff in Hc0 as [Hc0|Hc0]);
              apply in_map_iff in Hc0 as [k [<- Hk]]; apply in_seq in Hk; cbn [mc_val mc_loc mc_w loc_addr];
              rewrite ?nth_repeat; cbn; rewrite Hctx; (split; [reflexivity|]); (split; [intros z; discriminate|]); lia. }
          destruct (HV c Hc) as (Hv & Hnl & Hlo & Hhi).
          unfold cell_holds. destruct (mc_val c) as [z|p|z|] eqn:Ev; [ | | exfalso; exact (Hnl z eq_refl) | ];
            intros k Hk; rewrite HZ by lia; cbn [sval_num] in Hv; rewrite ?Hv; cbn [sval_num]; rewrite ?Hv;
            unfold le_byte; try (rewrite Z.mod_0_l, Z.shiftr_0_l by (apply Z.pow_nonzero; lia); reflexivity).
          all: cbn [sval_num] in Hv |- *; rewrite Hv; rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); rewrite Z.shiftr_0_l; reflexivity.
        * rewrite footprint_init. constructor; [|constructor]. intros x Hx. cbn [fst snd loc_addr hs_L] in Hx. rewrite Hctx in Hx.
          unfold CTX_SIZE in Hx. rewrite HZ by lia. discriminate.
    - unfold markers_hold, markers. cbn. constructor. }
Qed.



(* [comment removed for export] *)
Theorem heap_need_locks : forall HTOP hs m md, Heap HTOP hs m md -> rdn SEGS m (wa 0x97c23) 1 = Some [Z_to_bv 8 0].
Proof. intros HTOP hs m md HP. destruct HP as [_ _ (E1 & _) _ _ _ _ _ _ _ _ _]. exact E1. Qed.

Lemma rdn_frame_mrd : forall m m' (a : Z) n, 0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall x, a <= x < a + Z.of_nat n -> mrd SEGS m' (wa x) = mrd SEGS m (wa x)) -> rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n.
Proof.
  intros m m' a n Ha Hn H. revert a Ha Hn H. induction n as [|n IH]; intros a Ha Hn H; [reflexivity|].
  rewrite (rdn_unfold SEGS m' (wa a) (S n)), (rdn_unfold SEGS m (wa a) (S n)). rewrite (H a) by lia.
  replace (wa a + 1)%bv with (wa (a + 1)) by (rewrite wa_add1; reflexivity).
  rewrite (IH (a + 1)) by (try lia; intros x Hx; apply H; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma core_cells : forall hs m m', Heap0 (hs_L hs) (hs_s hs) m -> ly_ctx (hs_L hs) = 0x97c98 -> env m (hs_can hs) -> KRO m -> page_env m ->
  (forall rg, In rg (footprint (hs_s hs)) -> fst rg <> LCtx 0 -> ranges_disjoint (crange (hs_L hs) rg) (0x10000, 0x89000)) ->
  munch [(0x65b58, 0x65b60); (0x97c00, 0x97c08)] m m' -> mem_grows m m' ->
  (forall a, 0x65b58 <= a < 0x65b60 \/ 0x97c00 <= a < 0x97c08 -> mrd SEGS m' (wa a) = mrd SEGS m (wa a)) ->
  Heap0 (hs_L hs) (hs_s hs) m' /\ env m' (hs_can hs) /\ KRO m' /\ page_env m'.
Proof.
  intros hs m m' (HW & (HL & HC & HFM) & HM) Hctx Henv Hkro Hpg HAP MU Hwm Hv.
  assert (KEEP : forall x, 0 <= x < 2^64 -> ~ (0x65b58 <= x < 0x65b60) -> ~ (0x97c00 <= x < 0x97c08) -> m' (wa x) = m (wa x)).
  { intros x Hx H1 H2. apply MU. rewrite u_wa_small by exact Hx. cbn [outside]. tauto. }
  (* [comment removed for export] *)
  assert (NOC : forall x rg, In rg (footprint (hs_s hs)) -> loc_addr (hs_L hs) (fst rg) <= x < loc_addr (hs_L hs) (fst rg) + snd rg ->
            ~ (0x65b58 <= x < 0x65b60) /\ ~ (0x97c00 <= x < 0x97c08)).
  { intros x rg Hrg Hx. destruct (loc_eq_dec (fst rg) (LCtx 0)) as [E|E].
    - pose proof (footprint_ctx_len (hs_s hs) rg Hrg E) as Hlen. rewrite E in Hx. cbn [loc_addr] in Hx. rewrite Hctx, Hlen in Hx.
      unfold CTX_SIZE in *. lia.
    - pose proof (HAP rg Hrg E) as D. unfold ranges_disjoint, crange in D. cbn [fst snd] in D. lia. }
  assert (KEEPb : forall x rg, In rg (footprint (hs_s hs)) -> loc_addr (hs_L hs) (fst rg) <= x < loc_addr (hs_L hs) (fst rg) + snd rg ->
            bview SEGS m' x = bview SEGS m x).
  { intros x rg Hrg Hx. destruct (NOC x rg Hrg Hx) as [N1 N2].
    destruct (Z_lt_le_dec x 0) as [Hn|Hn].
    { unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro1; apply Z.leb_gt; exact Hn). reflexivity. }
    destruct (Z_lt_le_dec x (2^64)) as [Hx2|Hx2].
    2:{ unfold bview. replace ((0 <=? x) && (x <? 2^64)) with false by (symmetry; apply andb_false_intro2; apply Z.ltb_ge; exact Hx2). reflexivity. }
    apply bview_ext. exact (KEEP x ltac:(lia) N1 N2). }
  assert (KEEPc : forall c, (exists rg, In rg (footprint (hs_s hs)) /\ range_incl (cell_range (hs_L hs) c) (crange (hs_L hs) rg)) ->
            forall a, in_rng (cell_range (hs_L hs) c) a -> bview SEGS m' a = bview SEGS m a).
  { intros c (rg & Hrg & Hincl) a Ha. apply (KEEPb a rg Hrg). unfold range_incl, crange, in_rng, cell_range in *. cbn [fst snd] in *. lia. }
  assert (RDK : forall a n, 0 <= a -> a + Z.of_nat n <= 2^64 ->
            (forall j, a <= j < a + Z.of_nat n -> (~ (0x65b58 <= j < 0x65b60) /\ ~ (0x97c00 <= j < 0x97c08)) \/
                                                  (0x65b58 <= j < 0x65b60 \/ 0x97c00 <= j < 0x97c08)) ->
            rdn SEGS m' (wa a) n = rdn SEGS m (wa a) n).
  { intros a n Ha Hn H. apply rdn_frame_mrd; [exact Ha | exact Hn|]. intros x Hx. destruct (H x Hx) as [[N1 N2] | C].
    - unfold mrd. rewrite (KEEP x ltac:(lia) N1 N2). reflexivity.
    - exact (Hv x C). }
  split; [split; [exact HW | split; [split; [exact HL | split] | ]] |].
  - apply Forall_forall. intros c Hc. apply (cell_holds_frame (hs_L hs) (bview SEGS m) (bview SEGS m') c (image_cell_width _ c Hc)).
    + exact (proj1 (Forall_forall _ _) HC c Hc).
    + apply KEEPc. exact (image_in_footprint (hs_s hs) (hs_L hs) c HW HL Hc).
  - apply Forall_forall. intros rg Hrg x Hx. rewrite (KEEPb x rg Hrg Hx). exact (proj1 (Forall_forall _ _) HFM rg Hrg x Hx).
  - apply Forall_forall. intros c Hc. apply (cell_holds_frame (hs_L hs) (bview SEGS m) (bview SEGS m') c (markers_width _ c Hc)).
    + exact (proj1 (Forall_forall _ _) HM c Hc).
    + apply KEEPc. exact (markers_home (hs_s hs) (hs_L hs) c HW Hc).
  - destruct Henv as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9).
    Ltac rdk_side := let jj := fresh "jj" in let Hjj := fresh "Hjj" in intros jj Hjj; first [left; split; lia | right; lia].
    split.
    { split; [rewrite RDK by (first [rdk_side | cbn; lia]); exact E1|].
      split; [intros sc Hsc; rewrite RDK by (first [rdk_side | cbn; lia]); exact (E2 sc Hsc)|].
      split; [intros j Hj; rewrite RDK by (first [rdk_side | cbn; lia]); exact (E3 j Hj)|].
      split; [exact E4|].
      split; [rewrite RDK by (first [rdk_side | cbn; lia]); exact E5|].
      split; [rewrite RDK by (first [rdk_side | cbn; lia]); exact E6|].
      split; [rewrite RDK by (first [rdk_side | cbn; lia]); exact E7|].
      split; [intros j Hj; destruct (E8 j Hj) as (b0 & Hb0); exists b0; unfold mrd in *; rewrite KEEP by (unfold ERRNO in *; lia); exact Hb0|].
      intros d k0 Hd Hk0. apply (store_ok_mono SEGS k0 m m'); [exact Hwm | exact (E9 d k0 Hd Hk0)]. }
    split.
    { destruct Hkro as ((K1 & K2 & K3) & (K4 & K5 & K6)).
      split; (split; [assumption | split; [assumption|]]); intros j Hj; change (Mem.wa j) with (wa j);
        rewrite (KEEP j ltac:(lia) ltac:(lia) ltac:(lia)); first [ exact (K3 j Hj) | exact (K6 j Hj) ]. }
    unfold page_env in *; rewrite RDK by (first [rdk_side | cbn; lia]); exact Hpg.
Qed.

(* [comment removed for export] *)
Theorem heap_cells_frame : forall HTOP hs m m' md, Heap HTOP hs m md ->
  munch [(0x65b58, 0x65b60); (0x97c00, 0x97c08)] m m' -> mem_grows m m' ->
  (forall a, 0x65b58 <= a < 0x65b60 \/ 0x97c00 <= a < 0x97c08 -> mrd SEGS m' (wa a) = mrd SEGS m (wa a)) -> Heap HTOP hs m' md.
Proof.
  intros HTOP hs m m' md HP MU Hwm Hv. pose proof HP as [H0 Hctx Henv Hkro Hled Hpcg HAP HHT Hb1 HT20 Hpg Hini Hrap].
  destruct (core_cells hs m m' H0 Hctx Henv Hkro Hpg HAP MU Hwm Hv) as (H0' & Henv' & Hkro' & Hpg').
  exact (mkHeap HTOP hs m' md H0' Hctx Henv' Hkro' Hled Hpcg HAP HHT Hb1 HT20 Hpg' Hini Hrap).
Qed.
