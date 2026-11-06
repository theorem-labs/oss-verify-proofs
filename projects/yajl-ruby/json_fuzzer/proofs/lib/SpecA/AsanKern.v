(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition kwz (z : Z) : word := Z_to_bv 64 z.
Definition went (b n : Z) : word * word := (kwz b, kwz n).
Definition elo (e : word * word) : Z := bv_unsigned (fst e).
Definition ehi (e : word * word) : Z := bv_unsigned (fst e) + bv_unsigned (snd e).

(* [comment removed for export] *)
Definition clear_of (l : list (word * word)) (x n : Z) : Prop :=
  forall e, In e l -> x + n <= elo e \/ ehi e <= x.
(* [comment removed for export] *)
Definition clear_ofp (l : list (word * word)) (x n : Z) : Prop :=
  forall e, In e l -> 0 < bv_unsigned (snd e) -> x + n <= elo e \/ ehi e <= x.
Lemma clear_of_ofp : forall l x n, clear_of l x n -> clear_ofp l x n.
Proof. intros l x n H e He _. exact (H e He). Qed.
(* [comment removed for export] *)
Definition inside (l : list (word * word)) (x n : Z) : Prop :=
  exists e, In e l /\ elo e <= x /\ x + n <= ehi e.

Definition kResvLen : Z := 0x2000011000.   (* [comment removed for export] *)
Definition kPtrArrayLen : Z := 2^23.

Section KERN.
Variable E : aenv.
Let SB : Z := ae_space_beg E.

(* [comment removed for export] *)
Definition eager_rw (mo : Model) (x n : Z) : Prop :=
  inside (vm_maps (m_vmmaps mo)) x n /\ clear_ofp (vm_noaccess (m_vmmaps mo)) x n /\ clear_of (m_vm_lazy mo) x n.

Record AKern (s : astate) (mo : Model) : Prop := mkAKern {
  (* [comment removed for export] *)
  ak_resv : In (went (ae_resv_beg E) kResvLen) (vm_maps (m_vmmaps mo));
  ak_resv_geom : ae_resv_beg E <= SB /\ SB mod 2^16 = 0 /\ SB + kSpaceSize + kPageSize <= ae_resv_beg E + kResvLen;
  (* [comment removed for export] *)
  ak_reginfo : inside (vm_maps (m_vmmaps mo)) (SB + kSpaceSize) kPageSize /\ clear_ofp (vm_noaccess (m_vmmaps mo)) (SB + kSpaceSize) kPageSize;   (* [comment removed for export] *)
  ak_user : forall c, 1 <= c <= kLargestClassID -> 0 < rg_mapped_user (get_region s c) ->
              eager_rw mo (region_beg SB c) (rg_mapped_user (get_region s c));
  ak_fa : forall c, 1 <= c <= kLargestClassID -> 0 < rg_mapped_fa (get_region s c) ->
              eager_rw mo (free_array SB c) (rg_mapped_fa (get_region s c));
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ak_ptr : In (went (ae_ptr_array E) kPtrArrayLen) (vm_maps (m_vmmaps mo));
  ak_ptr_head : as_ptr_committed s = kChunksBlockCount -> eager_rw mo (ae_ptr_array E) kPtrArrayCommit;
  ak_ptr_tail : forall p, ae_ptr_array E + (if as_ptr_committed s =? 0 then 0 else kPtrArrayCommit) <= p ->
      p + kPageSize <= ae_ptr_array E + kPtrArrayLen -> p mod kPageSize = 0 -> inside (vm_noaccess (m_vmmaps mo)) p kPageSize;
  (* [comment removed for export] *)
  ak_sec : forall sc, In sc (as_sec s) ->
      In (went (sc_map_beg sc) (sc_map_size sc)) (vm_maps (m_vmmaps mo)) /\ eager_rw mo (sc_map_beg sc) (sc_map_size sc);
  (* [comment removed for export] *)
  ak_thread : eager_rw mo (ae_thread E) kPageSize;
  ak_depot_nodes : eager_rw mo (ae_depot_nodes E) (2^20);
  ak_store : inside (vm_maps (m_vmmaps mo)) (ae_store_blk E) (2^23) /\ clear_ofp (vm_noaccess (m_vmmaps mo)) (ae_store_blk E) (2^23);
  (* [comment removed for export] *)
  ak_node_blocks : forall b, In b (as_node_blocks s) -> In (went b kDepotNodeBlockBytes) (vm_maps (m_vmmaps mo)) /\ eager_rw mo b kDepotNodeBlockBytes;
  ak_store_blocks : forall b, In b (as_store_blocks s) ->
      inside (vm_maps (m_vmmaps mo)) b kStoreBlockBytes /\ clear_ofp (vm_noaccess (m_vmmaps mo)) b kStoreBlockBytes;
  (* [comment removed for export] *)
  ak_blocks_sep : forall b len, (In b (as_node_blocks s) /\ len = kDepotNodeBlockBytes) \/ (In b (as_store_blocks s) /\ len = kStoreBlockBytes) ->
      app_mem b len /\ b + len <= alloc_ceiling /\ b mod kPageSize = 0   (* [comment removed for export] *)
      /\ (b + len <= ae_resv_beg E \/ ae_resv_beg E + kResvLen <= b)
      /\ (forall sc, In sc (as_sec s) -> b + len <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= b)
      /\ (forall r, In r (ae_reserved E) -> b + len <= fst r \/ fst r + snd r <= b);
  (* [comment removed for export] *)
  ak_lazy : forall e, In e (m_vm_lazy mo) ->
      (0x7fff7000 <= elo e /\ ehi e <= kHighMemBeg) \/ (ae_store_blk E <= elo e /\ ehi e <= ae_store_blk E + 2^23)
      \/ (exists b, In b (as_store_blocks s) /\ b <= elo e /\ ehi e <= b + kStoreBlockBytes)
      (* [comment removed for export] *)
      \/ (ae_ptr_array E + (if as_ptr_committed s =? 0 then 0 else kPtrArrayCommit) <= elo e /\ ehi e <= ae_ptr_array E + kPtrArrayLen)
      \/ (ae_resv_beg E <= elo e /\ ehi e <= ae_resv_beg E + kResvLen
          (* [comment removed for export] *)
          /\ (forall c, 1 <= c <= kLargestClassID -> 0 < rg_mapped_user (get_region s c) ->
                 ehi e <= region_beg SB c \/ region_beg SB c + rg_mapped_user (get_region s c) <= elo e)
          /\ (forall c, 1 <= c <= kLargestClassID -> 0 < rg_mapped_fa (get_region s c) ->
                 ehi e <= free_array SB c \/ free_array SB c + rg_mapped_fa (get_region s c) <= elo e));
  (* [comment removed for export] *)
  ak_store_sep :
      (ae_store_blk E + 2^23 <= ae_resv_beg E \/ ae_resv_beg E + kResvLen <= ae_store_blk E)
      /\ (forall sc, In sc (as_sec s) -> ae_store_blk E + 2^23 <= sc_map_beg sc \/ sc_map_beg sc + sc_map_size sc <= ae_store_blk E)
      /\ (ae_store_blk E + 2^23 <= ae_thread E \/ ae_thread E + kPageSize <= ae_store_blk E)
      /\ (ae_store_blk E + 2^23 <= ae_depot_nodes E \/ ae_depot_nodes E + 2^20 <= ae_store_blk E)
      /\ (ae_store_blk E + 2^23 <= ae_ptr_array E \/ ae_ptr_array E + kPtrArrayLen <= ae_store_blk E)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ak_eager_bytes (s : astate) : Z := a_eager_bytes s + kPageSize (* [comment removed for export] *).
(* [comment removed for export] *)
Definition ak_shadow_pages_bound (s : astate) : Z :=
  (ts_mmaped (as_ts s)) / 2^15 + 2 * ts_mmaps (as_ts s) + 2.
(* [comment removed for export] *)

End KERN.
End RC__1.
