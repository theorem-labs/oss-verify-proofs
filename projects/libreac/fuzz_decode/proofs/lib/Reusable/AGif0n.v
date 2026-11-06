(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/AGif0n.v at 95e6f1d72b6 (sha256 ce897a2285b6) into lib/Reusable (shared by both images), with its module paths changed. *)
(* The primary interface between the frame-generic Allocate walk (the AG* files) and an allocator model, over the image
   classes ImgBase.AImg / ImgBaseAG.AGImg (no image: cgif_file's values are in AGif2cgif.v and AGif0cgif.v): hview,
   hit_writes, wframe, at_RETw / at_RETkw, malloc_join_t, mview, rleaf, the records AIface / AIfaceK / AIfaceM and the
   model lemmas the arms share.  It replaced AGif0.v, whose predicates over cgif's image moved to AGif0cgif.v. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YGAlloc ImgBase ImgBaseAG.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {IM : AImg} {AG : AGImg}.
Local Open Scope am_scope.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The view, the hit-g writes and the walk's frame: cgif's predicates (AGif0cgif's Section p) restated over the image
   classes (AImg, AGImg) and the copied geometry; under the cgif instances they are convertible with AGif0cgif's. *)
(* (a) The view: the cells the hit-g seed (AGhy.SSG, regions REG0G) reads, for the cached chunk at class-region
   offset [16 * v] of class [cl] with [cnt] cached entries, over the instance [inst]. *)
Record hview (B : asyms) (W : world im_segs) (ly : alayout) (inst : Z) (mem : word -> option byte) (cl cnt v : Z) : Prop := {
  hv_ly : layout_ok ly;
  hv_img : im_img_cover ly;
  hv_tsd : ly_tsd ly = im_tsd;
  hv_cnt : 1 <= cnt <= 16;
  hv_v : 0 <= v /\ v mod 2 = 0 /\ 16 * v + class_size cl <= 2 ^ 31;
  (* the image's constant cells (global literals, the thread and context objects' fixed words) *)
  hv_const : Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (as_const B ly);
  (* the instance's fields: primary.space at +0x20, and the two words at +0xe20 *)
  hv_inst : val_mem im_segs (mrestrict (w_H W) mem) (inst + 0x20) 8 (ly_space ly) /\
            val_mem im_segs (mrestrict (w_H W) mem) (inst + 0xe20) 8 0x10000000000 /\
            val_mem im_segs (mrestrict (w_H W) mem) (inst + 0xe28) 8 0x108000010;
  (* the per-thread cache cell of the class: count, class size, the last entry *)
  hv_cache : val_mem im_segs (mrestrict (w_H W) mem) (Pv ly cl) 4 cnt /\
             val_mem im_segs (mrestrict (w_H W) mem) (Pv ly cl + 8) 8 (class_size cl) /\
             val_mem im_segs (mrestrict (w_H W) mem) (PVv ly cl cnt) 4 v;
  (* the thread's unwinding flag is clear, its junk words are present *)
  hv_unw : val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0;
  hv_junk : forall a, ly_T ly + t_cache_stats <= a < ly_T ly + t_unwinding -> apresent (w_H W) mem a;
  (* the cached chunk is present, and its shadow is present and poisoned (250) *)
  hv_chunk : forall a, Kv ly cl v <= a < Kv ly cl v + class_size cl -> apresent (w_H W) mem a;
  hv_shadow : forall s, SKv ly cl v <= s < SKv ly cl v + class_size cl / 8 ->
              apresent (w_H W) mem s /\ val_mem im_segs (mrestrict (w_H W) mem) s 1 250
}.

(* (d) The allocator memory the hit-g walk writes, besides Allocate's stack window and the new block: the thread
   cache cells, the chunk header, the partial shadow byte (odd sizes), the depot zone and the block's shadow. *)
Definition hit_writes (ly : alayout) (n cl v kz : Z) (odd : bool) (a : Z) : Prop :=
WINT ly cl a \/ ((Kv ly cl v <= a < Kv ly cl v + 16) \/ (Uv ly cl v kz - 16 <= a < Uv ly cl v kz)) \/ PBW ly n cl v kz odd a \/
ag_dzone ly a \/ (SUv ly cl v kz <= a < SUv ly cl v kz + N8D n / 8).

(* The walk's frame at Allocate's entry, over the virtual register file regs0 of the walk's environment (atom 2 =
   the entry sp, 12 = the trace buffer, 13 = the stack object). *)
Definition wframe (W : world im_segs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (tr : list Z) : Prop :=
(ly_stk_lo ly + AFSTACK <= bv_unsigned (getr regs0 2) /\ ly_bot ly < bv_unsigned (getr regs0 2) /\
 bv_unsigned (getr regs0 2) <= ly_stk_hi ly /\ bv_unsigned (getr regs0 2) mod 16 = 0) /\
(1 <= length tr <= 30)%nat /\
(bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 13) /\ bv_unsigned (getr regs0 13) + 16 <= ly_stk_hi ly /\
 bv_unsigned (getr regs0 13) mod 8 = 0) /\
(bv_unsigned (getr regs0 2) <= bv_unsigned (getr regs0 12) /\ bv_unsigned (getr regs0 12) + 8 * 30 <= ly_stk_hi ly /\
 bv_unsigned (getr regs0 12) mod 8 = 0) /\
(forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem0 a).

(* (c) The machine post at Allocate's ret that the post field reads: AGis.at_RET without its last clause (the
   can_fill bytes), so that the cf = 1 post (AGis.at_RET) and the cf = 0 post (the block keeps its bytes) both give
   it.  The clauses and their order are at_RET's. *)
Definition at_RETw (W : world im_segs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
(n cl cnt v jb kz : Z) (DPOST : Z -> (word -> option byte) -> Prop) (odd : bool) (z : Z) (W' : world im_segs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 (Kv ly cl v + RZ kz) /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(exists memD, DPOST z memD /\ (forall a, ag_dzone ly a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
forall x : word, ag_dzone ly (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ WIN ly regs0 n cl v kz odd (bv_unsigned x) -> ~ ag_dzone ly (bv_unsigned x) ->
~ (Kv ly cl v + RZ kz <= bv_unsigned x < Kv ly cl v + RZ kz + n) ->
~ (SUv ly cl v kz <= bv_unsigned x < SUv ly cl v kz + N8D n / 8) -> mem' x = mem0 x) /\
(forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem' a) /\
(forall a, WINT ly cl a \/ (Kv ly cl v <= a < Kv ly cl v + RZ kz + n) \/ PBW ly n cl v kz odd a -> apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem im_segs m (Kv ly cl v) 8 0xCC6E96B9CC6E96B9 /\ val_mem im_segs m (Kv ly cl v + 8) 8 (Kv ly cl v + RZ kz - 16) /\
val_mem im_segs m (Kv ly cl v + RZ kz - 16) 1 2 /\ val_mem im_segs m (Kv ly cl v + RZ kz - 15) 1 (hdr_byte1 jb) /\
val_mem im_segs m (Kv ly cl v + RZ kz - 14) 2 0 /\ val_mem im_segs m (Kv ly cl v + RZ kz - 12) 4 n /\
val_mem im_segs m (Pv ly cl) 4 (cnt - 1) /\ val_mem im_segs m (ly_T ly + t_unwinding) 1 0 /\
(forall x : word, SUv ly cl v kz <= bv_unsigned x < SUv ly cl v kz + N8D n / 8 -> mem' x = Some (Z_to_bv 8 0)) /\
(odd = true -> val_mem im_segs m (PBv ly n cl v kz) 1 (n mod 8)).

(* The k path (0 <= n <= 48, redzone 16, header size NPv = req_size n): AGj6.at_RET without its last clause, and
   the allocator memory the k walk writes. *)
Definition at_RETkw (W : world im_segs) (ly : alayout) (regs0 : bvmap 5 word) (mem0 : word -> option byte) (md0 : Model)
(n cl cnt v jb : Z) (DPOST : Z -> (word -> option byte) -> Prop) (odd : bool) (z : Z) (W' : world im_segs) (c' : config) : Prop :=
W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0) /\
getr regs' 10 = Z_to_bv 64 (K6.Kv ly cl v + K6.RZ) /\
(forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs0 r) /\
(exists memD, DPOST z memD /\ (forall a, ag_dzone ly a -> apresent (w_H W) mem0 a -> apresent (w_H W) memD a) /\
forall x : word, ag_dzone ly (bv_unsigned x) -> mem' x = memD x) /\
(forall x : word, ~ K6.WIN ly regs0 n cl v odd (bv_unsigned x) -> ~ ag_dzone ly (bv_unsigned x) ->
~ (K6.Kv ly cl v + K6.RZ <= bv_unsigned x < K6.Kv ly cl v + K6.RZ + K6.NPv n) ->
~ (K6.SUv ly cl v <= bv_unsigned x < K6.SUv ly cl v + K6.N8D n / 8) -> mem' x = mem0 x) /\
(forall a, bv_unsigned (getr regs0 2) - AFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) mem' a) /\
(forall a, K6.WINT ly cl a \/ (K6.Kv ly cl v <= a < K6.Kv ly cl v + K6.RZ + K6.NPv n) \/ K6.PBW ly n cl v odd a ->
apresent (w_H W) mem' a) /\
let m := mrestrict (w_H W) mem' in
val_mem im_segs m (K6.Kv ly cl v + K6.RZ - 16) 1 2 /\ val_mem im_segs m (K6.Kv ly cl v + K6.RZ - 15) 1 (K6.hdr_byte1 jb) /\
val_mem im_segs m (K6.Kv ly cl v + K6.RZ - 14) 2 0 /\ val_mem im_segs m (K6.Kv ly cl v + K6.RZ - 12) 4 (K6.NPv n) /\
val_mem im_segs m (K6.Pv ly cl) 4 (cnt - 1) /\ val_mem im_segs m (ly_T ly + t_unwinding) 1 0 /\
(forall x : word, K6.SUv ly cl v <= bv_unsigned x < K6.SUv ly cl v + K6.N8D n / 8 -> mem' x = Some (Z_to_bv 8 0)) /\
(odd = true -> val_mem im_segs m (K6.PBv ly n cl v) 1 (K6.NPv n mod 8)).
Definition hit_writes_k (ly : alayout) (n cl v : Z) (odd : bool) (a : Z) : Prop :=
K6.WINT ly cl a \/ ((K6.Kv ly cl v <= a < K6.Kv ly cl v + 16) \/ (K6.Uv ly cl v - 16 <= a < K6.Uv ly cl v)) \/
K6.PBW ly n cl v odd a \/ ag_dzone ly a \/ (K6.SUv ly cl v <= a < K6.SUv ly cl v + K6.N8D n / 8).

(* The cache join with the spin tag of the dead shadow-remap branch as a parameter: [malloc_join_t 12] is
   YFi3.malloc_join (cgif_file's [spin 449860], YG00.v:425); an instance with another tag keeps the same shape. *)
Definition malloc_K_t (stag : Z) (n : Z) (trace : list Z) (ob : option sptr) : M sptr :=
match ob with
| None => ret PNull
| Some beg =>
depot_put trace ;;
let k := mkChunk beg n CAllocated in
(if needs_remap (ck_n k) then
z <- askz (KShadowRemap (ck_user k) (8 * (ck_n k / 8))) ;;
if aGranted z then ret tt else spin stag
else ret tt) ;;
modify (fun s => set_chunks (upd_chunk (st_chunks s) k) s) ;;
ret (ck_user k)
end.
Definition malloc_join_t (stag : Z) (n : Z) (trace : list Z) (c : Z) : M sptr :=
ob <- (o <- pop_part c ;; ret (match o with Some off => Some (PPrim off) | None => None end)) ;;
malloc_K_t stag n trace ob.

(* The miss view (the miss seeds AGi4.MS_1 / MK_1): hview's instance-independent cells, the class's cache count 0. *)
Record mview (B : asyms) (W : world im_segs) (ly : alayout) (inst : Z) (mem : word -> option byte) (cl : Z) : Prop := {
  mv_ly : layout_ok ly;
  mv_img : im_img_cover ly;
  mv_tsd : ly_tsd ly = im_tsd;
  mv_const : Forall (cell_holds B ly (aview im_segs (w_H W) mem)) (as_const B ly);
  mv_inst : val_mem im_segs (mrestrict (w_H W) mem) (inst + 0x20) 8 (ly_space ly) /\
            val_mem im_segs (mrestrict (w_H W) mem) (inst + 0xe20) 8 0x10000000000 /\
            val_mem im_segs (mrestrict (w_H W) mem) (inst + 0xe28) 8 0x108000010;
  mv_cnt0 : val_mem im_segs (mrestrict (w_H W) mem) (Pv ly cl) 4 0;
  mv_unw : val_mem im_segs (mrestrict (w_H W) mem) (ly_T ly + t_unwinding) 1 0
}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The interface.                                                                                                   *)
Record AIface (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z) : Prop := {
  if_inst : forall inst ly S W mem md, ARX inst ly S W mem md -> ag_inst_ok inst;
  (* (a) *)
  if_view : forall inst ly S W mem md n l off,
    ARX inst ly S W mem md -> rpre S n -> 0 <= n -> from_primary n = true ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    off mod 32 = 0 /\ hview B W ly inst mem (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16);
  (* (b) *)
  if_shape : forall n tr S l off, 0 <= n -> from_primary n = true ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    mt n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) mtag ;; malloc_join_t stag n tr (chunk_class n)) S;
  (* the depot callee: entered with the allocator's depot and constant cells as at [mem0] *)
  if_depot : forall inst ly S W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly S W mem0 md0 -> U tr S ->
    (forall x : word, ag_dzone ly (bv_unsigned x) \/ ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
    SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 ag_depot_put) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = W /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ ag_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
      dpost inst ly S W tr z mem');
  if_dpost_aok : forall inst ly S W tr z m, dpost inst ly S W tr z m -> aok S (KDepot tr) z;
  (* (c) *)
  if_post : forall inst ly S W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> n < nmax -> blocks_bytes S + n <= lmax -> U tr S ->
    49 <= n <= 64512 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    wframe W ly regs0 mem0 tr ->
    0 <= jb <= 255 ->
    val_mem im_segs (mrestrict (w_H W) mem0) (Kv ly (chunk_class n) (off / 16) + RZ (rz_log n) - 15) 1 jb ->
    at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
      (fun z m => dpost inst ly S W tr z m) odd z W
      (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
    (odd = true <-> n mod 8 <> 0) ->
    (exists trc, apath (mt n tr S) trc
      (ck_user (new_chunk (chunk_class n) off n), st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) /\
      gflag trc = true) ->
    ARX inst ly (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
    lpost (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z);
  (* (d) *)
  if_owned : forall inst ly S W mem md n l off odd a,
    ARX inst ly S W mem md -> rpre S n -> 49 <= n <= 64512 ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    0 <= a < 2 ^ 64 -> (odd = true -> n mod 8 <> 0) ->
    hit_writes ly n (chunk_class n) (off / 16) (rz_log n) odd a -> AOX ly S a;
  (* an uninited cache has no entries (the miss arms' case split) *)
  if_uninit : forall inst ly S W mem md c, ARX inst ly S W mem md -> 1 <= c <= 31 ->
    st_cache_inited S = false -> pc_chunks (cache S c) = []
}.
(* The k path's twins of (c) and (d) (0 <= n <= 48), for the k hit arm (AGil). *)
Record AIfaceK (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z) : Prop := {
  if_post_k : forall inst ly S W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
    ARX inst ly S W mem0 md0 -> rpre S n -> n < nmax -> blocks_bytes S + n <= lmax -> U tr S ->
    0 <= n <= 48 -> st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    wframe W ly regs0 mem0 tr ->
    0 <= jb <= 255 ->
    val_mem im_segs (mrestrict (w_H W) mem0) (K6.Kv ly (chunk_class n) (off / 16) + K6.RZ - 15) 1 jb ->
    at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
      (fun z m => dpost inst ly S W tr z m) odd z W
      (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
    (odd = true <-> K6.NPv n mod 8 <> 0) ->
    (exists trc, apath (mt n tr S) trc
      (ck_user (new_chunk (chunk_class n) off n), st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) /\
      gflag trc = true) ->
    ARX inst ly (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
    lpost (st_final (set_nev (st_nev S + 1) S) (chunk_class n) l off n tr z);
  if_owned_k : forall inst ly S W mem md n l off odd a,
    ARX inst ly S W mem md -> rpre S n -> 0 <= n <= 48 ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    0 <= a < 2 ^ 64 -> (odd = true -> K6.NPv n mod 8 <> 0) ->
    hit_writes_k ly n (chunk_class n) (off / 16) odd a -> AOX ly S a
}.
(* The refill callee's post (the miss arms): the call at ag_refill returns to raZ regs with a0 = 1 iff the class's
   cache is non-empty; ARX / lpost / inited hold at the post-refill state, possibly over a grown layout and world (a
   granted placement inside the refill); memory outside the callee's stack window changes only on owned addresses
   (of the pre- or the post-state).  The post-refill state carries lpost, not rpre: the refill runs after Allocate's
   tick, and rpre (cgif_file: aregime) need not survive the tick. *)
Definition rleaf (ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (lpost : astate -> Prop)
(inst : Z) (ly : alayout) (S0 : astate) (n cl : Z) (W : world im_segs) (regs : bvmap 5 word) (mem : word -> option byte)
(md : Model) (r : unit * astate) (W' : world im_segs) (c' : config) : Prop :=
exists ly' regs' mem' md',
c' = cfg_at im_segs (raZ regs) regs' mem' md' /\
ARX inst ly' (snd r) W' mem' md' /\ lpost (snd r) /\ st_cache_inited (snd r) = true /\
blocks_bytes (snd r) = blocks_bytes S0 /\ layout_le (length (st_secs S0)) ly ly' /\
wle W W' /\ aregs_preserved regs regs' /\ same_io md md' /\
(forall a, 0 <= a < 2 ^ 64 -> ~ AOX ly S0 a -> ~ AOX ly' (snd r) a -> ~ (spZ regs - RSTACK <= a < spZ regs) ->
   aview im_segs (w_H W') mem' a = aview im_segs (w_H W) mem a) /\
(* the same frame on the raw memory (ARX-style relations read raw bytes that aview hides) *)
(forall x : word, ~ AOX ly S0 (bv_unsigned x) -> ~ AOX ly' (snd r) (bv_unsigned x) ->
   ~ (spZ regs - RSTACK <= bv_unsigned x < spZ regs) -> mem' x = mem x) /\
(forall a, spZ regs - RSTACK <= a < spZ regs -> apresent (w_H W') mem' a) /\
getr regs' 10 = w64 (match pc_chunks (cache (snd r) cl) with [] => 0 | _ => 1 end).
(* The miss arms' fields (g and k miss: AGim / AGin; their seeds AGiw / AGja).  [rtree c] is the model's refill
   subtree of class c (cgif_file: YFl1.refill_tree). *)
Record AIfaceM (B : asyms) (U : list Z -> astate -> Prop) (mt : Z -> list Z -> M sptr)
(ARX : Z -> alayout -> astate -> world im_segs -> (word -> option byte) -> Model -> Prop)
(AOX : alayout -> astate -> Z -> Prop) (rpre : astate -> Z -> Prop) (nmax lmax : Z) (lpost : astate -> Prop)
(dpost : Z -> alayout -> astate -> world im_segs -> list Z -> Z -> (word -> option byte) -> Prop) (mtag stag : Z) (rtree : Z -> M unit) : Prop := {
  if_mview : forall inst ly S W mem md n,
    ARX inst ly S W mem md -> 0 <= n -> from_primary n = true ->
    pc_chunks (cache S (chunk_class n)) = [] -> mview B W ly inst mem (chunk_class n);
  if_shape_miss : forall n tr S, 0 <= n -> from_primary n = true -> pc_chunks (cache S (chunk_class n)) = [] ->
    mt n tr S = (tick ;; mcheck (n <? kMaxAllowedMalloc - kPage) mtag ;; rtree (chunk_class n) ;;
                 malloc_join_t stag n tr (chunk_class n)) S;
  (* the refill callee at the instance atom (a2 = inst), from the entry state S0 (ARX there) and the call-time
     memory, which differs from the entry memory only in Allocate's window [sp0 - AFSTACK, sp0) *)
  if_refill : forall inst ly S0 W mem0 md0 n (sp0 : Z) (regs : bvmap 5 word) (mem : word -> option byte) (mat : list word),
    ARX inst ly S0 W mem0 md0 -> rpre S0 n -> 0 <= n -> from_primary n = true ->
    pc_chunks (cache S0 (chunk_class n)) = [] ->
    ly_stk_lo ly + AFSTACK <= sp0 -> ly_bot ly < sp0 -> sp0 <= ly_stk_hi ly -> sp0 mod 16 = 0 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> aview im_segs (w_H W) mem a = aview im_segs (w_H W) mem0 a) ->
    (* the raw frame: ARX reads raw memory at hidden in-band bytes, which aview does not see; the seed writes the
       thread's unwinding byte outside the scratch window *)
    (forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> ~ (ly_T ly + t_unwinding <= bv_unsigned x < ly_T ly + t_unwinding + 1) ->
       mem x = mem0 x) ->
    (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) ->
    spZ regs = sp0 - 176 -> getr regs 1 = w64 ag_refill_ret -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 im_tp ->
    getr regs 10 = w64 (ly_T ly + t_cache) -> getr regs 11 = w64 (ly_T ly + t_cache + 80 * chunk_class n) ->
    getr regs 12 = w64 inst -> getr regs 13 = w64 (chunk_class n) ->
    amreal im_segs (rtree (chunk_class n) (set_nev (st_nev S0 + 1) S0)) W
      (cfg_at im_segs ag_refill regs mem (with_vm_backing (m_vm_lazy md0) mat md0))
      (rleaf ARX AOX lpost inst ly S0 n (chunk_class n) W regs mem (with_vm_backing (m_vm_lazy md0) mat md0));
  (* (c) for the miss join: if_post with the pop state Sp (after the refill) for the post-tick state; the model
     facts of the path come from the entry state S0 (ARX, rpre and the size budget there) *)
  if_post_miss : forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
    ARX inst ly0 S0 W0 mem00 md00 -> rpre S0 n -> blocks_bytes S0 + n <= lmax ->
    ARX inst ly Sp W mem0 md0 -> n < nmax -> blocks_bytes Sp + n <= lmax -> U tr S0 ->
    49 <= n <= 64512 -> st_cache_inited Sp = true -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
    wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
    val_mem im_segs (mrestrict (w_H W) mem0) (Kv ly (chunk_class n) (off / 16) + RZ (rz_log n) - 15) 1 jb ->
    at_RETw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb (rz_log n)
      (fun z m => dpost inst ly Sp W tr z m) odd z W
      (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
    (odd = true <-> n mod 8 <> 0) ->
    (exists trc, apath (mt n tr S0) trc (ck_user (new_chunk (chunk_class n) off n), st_final Sp (chunk_class n) l off n tr z) /\
      gflag trc = true) ->
    ARX inst ly (st_final Sp (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
    lpost (st_final Sp (chunk_class n) l off n tr z);
  (* the k twin of if_post_miss (0 <= n <= 48): if_post_k's body at the pop state Sp *)
  if_post_miss_k : forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 n tr l off (regs0 : bvmap 5 word) jb odd z (regs' : bvmap 5 word) mem' mat,
    ARX inst ly0 S0 W0 mem00 md00 -> rpre S0 n -> blocks_bytes S0 + n <= lmax ->
    ARX inst ly Sp W mem0 md0 -> n < nmax -> blocks_bytes Sp + n <= lmax -> U tr S0 ->
    0 <= n <= 48 -> st_cache_inited Sp = true -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
    wframe W ly regs0 mem0 tr -> 0 <= jb <= 255 ->
    val_mem im_segs (mrestrict (w_H W) mem0) (K6.Kv ly (chunk_class n) (off / 16) + K6.RZ - 15) 1 jb ->
    at_RETkw W ly regs0 mem0 md0 n (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16) jb
      (fun z m => dpost inst ly Sp W tr z m) odd z W
      (mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md0) mat md0)) ->
    (odd = true <-> K6.NPv n mod 8 <> 0) ->
    (exists trc, apath (mt n tr S0) trc (ck_user (new_chunk (chunk_class n) off n), st_final Sp (chunk_class n) l off n tr z) /\
      gflag trc = true) ->
    ARX inst ly (st_final Sp (chunk_class n) l off n tr z) W mem' (with_vm_backing (m_vm_lazy md0) mat md0) /\
    lpost (st_final Sp (chunk_class n) l off n tr z);
  (* the depot callee at the miss join's post-refill state Sp: the entry facts at S0 (own layout ly0), the rest of
     if_depot at Sp (U holds at the entry state; the refill ticks st_nev, so U need not hold at Sp) *)
  if_depot_miss : forall inst ly ly0 S0 Sp W0 mem00 md00 W mem0 md0 tr (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (buf : Z),
    ARX inst ly0 S0 W0 mem00 md00 -> U tr S0 ->
    ARX inst ly Sp W mem0 md0 ->
    (forall x : word, ag_dzone ly (bv_unsigned x) \/ ag_czone ly (bv_unsigned x) -> mem x = mem0 x) ->
    getr regs 10 = Z_to_bv 64 buf -> getr regs 11 = Z_to_bv 64 (Z.of_nat (length tr)) ->
    getr regs 3 = Z_to_bv 64 (as_gp B) -> getr regs 4 = Z_to_bv 64 im_tp -> YK0s.ret_ok (getr regs 1) ->
    (forall i, (i < length tr)%nat -> val_mem im_segs (mrestrict (w_H W) mem) (buf + 8 * Z.of_nat i) 8 (nth i tr 0)) ->
    buf mod 8 = 0 -> ly_stk_lo ly <= buf -> buf + 8 * 30 <= ly_stk_hi ly ->
    buf + 8 * 30 <= bv_unsigned (getr regs 2) - DEP_STK \/ bv_unsigned (getr regs 2) <= buf ->
    bv_unsigned (getr regs 2) mod 16 = 0 -> ly_stk_lo ly <= bv_unsigned (getr regs 2) - DEP_STK ->
    bv_unsigned (getr regs 2) <= ly_stk_hi ly ->
    (forall a, bv_unsigned (getr regs 2) - DEP_STK <= a < bv_unsigned (getr regs 2) -> apresent (w_H W) mem a) ->
    SRr im_segs W (mkCfg (mkst regs (Z_to_bv 64 ag_depot_put) mem (seg_rom im_segs)) md)
    (fun W' c' => W' = W /\ exists z regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs 1) mem' (seg_rom im_segs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      regs_preserved regs regs' /\
      (forall x : word, ~ (bv_unsigned (getr regs 2) - DEP_STK <= bv_unsigned x < bv_unsigned (getr regs 2)) ->
         ~ ag_dzone ly (bv_unsigned x) -> mem' x = mem x) /\
      (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem' a) /\
      dpost inst ly Sp W tr z mem');
  (* the class-full arm: the refill answered 0; Allocate sets the OOM byte (1) and returns null *)
  if_oom : forall inst ly S0 Sp W mem md n tr (sp0 : Z) mem' md',
    ARX inst ly Sp W mem md -> lpost Sp -> pc_chunks (cache Sp (chunk_class n)) = [] ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 - AFSTACK <= a < sp0) -> a <> im_oom -> ~ (im_errno <= a < im_errno + 4) ->
       aview im_segs (w_H W) mem' a = aview im_segs (w_H W) mem a) ->
    (* the raw frame: ARX reads raw memory at hidden in-band bytes, which aview does not see *)
    (forall x : word, ~ (sp0 - AFSTACK <= bv_unsigned x < sp0) -> bv_unsigned x <> im_oom -> ~ (im_errno <= bv_unsigned x < im_errno + 4) ->
       mem' x = mem x) ->
    (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem a) -> (forall a, sp0 - AFSTACK <= a < sp0 -> apresent (w_H W) mem' a) ->
    ly_stk_lo ly + AFSTACK <= sp0 -> sp0 <= ly_stk_hi ly ->
    val_mem im_segs (mrestrict (w_H W) mem') im_oom 1 1 -> same_io md md' -> m_vmmaps md' = m_vmmaps md -> m_vm_lazy md' = m_vm_lazy md ->
    (exists trc, apath (mt n tr S0) trc (PNull, Sp) /\ gflag trc = true) ->
    ARX inst ly Sp W mem' md' /\ lpost Sp /\ AOX ly Sp im_oom /\ AOX ly Sp (ly_T ly + t_unwinding)
  (* the stack is never owned by the allocator, so rleaf's frame law keeps the caller's stack object and trace
     buffer *)
  ;if_stack : forall inst ly S W mem md a, ARX inst ly S W mem md -> ly_stk_lo ly <= a < ly_stk_hi ly -> ~ AOX ly S a;
  (* AIface's (a) and (d) without rpre, for the miss arms' calls at the post-refill state Sp *)
  if_view_m : forall inst ly S W mem md n l off,
    ARX inst ly S W mem md -> 0 <= n -> from_primary n = true ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    off mod 32 = 0 /\ hview B W ly inst mem (chunk_class n) (Z.of_nat (length (l ++ [off]))) (off / 16);
  if_owned_m : forall inst ly S W mem md n l off odd a,
    ARX inst ly S W mem md -> 49 <= n <= 64512 ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    0 <= a < 2 ^ 64 -> (odd = true -> n mod 8 <> 0) ->
    hit_writes ly n (chunk_class n) (off / 16) (rz_log n) odd a -> AOX ly S a;
  (* the k twin of if_owned_m (= if_owned_k without rpre) *)
  if_owned_m_k : forall inst ly S W mem md n l off odd a,
    ARX inst ly S W mem md -> 0 <= n <= 48 ->
    st_cache_inited S = true -> pc_chunks (cache S (chunk_class n)) = l ++ [off] ->
    0 <= a < 2 ^ 64 -> (odd = true -> K6.NPv n mod 8 <> 0) ->
    hit_writes_k ly n (chunk_class n) (off / 16) odd a -> AOX ly S a;
  (* the cache join keeps the owned set at a fixed layout, outside the new block (the join allocates the popped
     chunk; its user bytes become the client's) *)
  if_mono_join : forall inst ly Sp W mem md n l off tr z a,
    ARX inst ly Sp W mem md -> pc_chunks (cache Sp (chunk_class n)) = l ++ [off] ->
    ~ (sptr_addr B ly (ck_user (new_chunk (chunk_class n) off n)) <= a <
       sptr_addr B ly (ck_user (new_chunk (chunk_class n) off n)) + req_size n) ->
    AOX ly Sp a -> AOX ly (st_final Sp (chunk_class n) l off n tr z) a
}.

End a.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Model lemmas the arms share.                                                                                     *)
Section m. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Open Scope am_scope.

(* Every result the realization delivers is the end of a path of the tree whose every answer is a granted one
   (the leaf's [apath] / [gflag] clause); the pattern of YG0d.amreal_SRr04. *)
Lemma amreal_apath_gflag (segs : list Segment) {R} : forall (t : itree astate R) W c (Q : R -> world segs -> config -> Prop),
amreal segs t W c Q ->
amreal segs t W c (fun r W' c' => Q r W' c' /\ exists trc, apath t trc r /\ gflag trc = true).
Proof.
induction t as [r | q snap k IH | pc | f]; intros W c Q H; cbn [amreal] in *.
- eapply SRr_mono; [exact H|]. intros W' c' _ HQ. split; [exact HQ|]. exists []. split; reflexivity.
- eapply SRr_mono; [exact H|]. intros W1 c1 _ Hk.
  assert (STEP : forall z, aok snap q z -> progz q z = true -> forall W2 c2, amreal segs (k z) W2 c2 Q ->
    amreal segs (k z) W2 c2 (fun r W' c' => Q r W' c' /\ exists trc, apath (IAsk q snap k) trc r /\ gflag trc = true)).
  { intros z Hz Hp W2 c2 Hc. eapply amreal_mono; [| exact (IH z W2 c2 Q Hc)].
    intros r W' c' [HQ (trc & HP & HG)]. split; [exact HQ|]. exists ((q, z) :: trc). split.
    - cbn [apath]. split; [reflexivity | split; [exact Hz | exact HP]].
    - cbn [gflag]. rewrite Hp, HG. reflexivity. }
  clear IH. destruct q;
  try (destruct Hk as (J & nx & bit & sp & i0 & Hn & Ht & Ha & Hs & Hb & Hr & Hz & Hc); exists J, nx, bit, sp, i0;
  split; [exact Hn|]; split; [exact Ht|]; split; [exact Ha|]; split; [exact Hs|]; split; [exact Hb|]; split; [exact Hr|];
  split; [exact Hz|]; intros i Hi; apply STEP; [exact (Ha i) | rewrite (Hr i Hi); reflexivity | exact (Hc i Hi)]).
  destruct Hk as (z & Hz & Hc). exists z. split; [exact Hz|]. apply STEP; [exact Hz | reflexivity | exact Hc].
- exact H.
- exact I.
Qed.

(* A pure first step of a bind. *)
Lemma bind_ret_l {A R} : forall (m : M A) (f : A -> M R) s a s', m s = IRet (a, s') -> bind m f s = f a s'.
Proof. intros m f s a s' E. unfold bind. rewrite E. reflexivity. Qed.
End m.
