(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run LinuxProcessSemantics.EquivalenceDefinition.Equivalence OSSVerify.glaze.binary_reflection.images.Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module RefImg.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.EquivalenceDefinition.Equivalence.
Export OSSVerify.glaze.binary_reflection.images.Plain.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation PSEGS := Plain.M.loaded_segments.
Abbreviation PPC := Plain.M.init_pc.
Abbreviation PPH := Plain.M.phdrs.

(* [comment removed for export] *)
Definition PIMG : Image := mkImage Plain.M.loaded_segments Plain.M.init_pc Plain.M.phdrs.



























End RefImg.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst. Export RefImg OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Abbreviation RSEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CTX : Z := 0xa6828.                 (* [comment removed for export] *)
Definition MLOCK : Z := 0xa6820.               (* [comment removed for export] *)
Definition ctx_secret : Z := CTX.
Definition ctx_init_done : Z := CTX + 8.       (* [comment removed for export] *)
Definition ctx_mmap_counter : Z := CTX + 12.   (* [comment removed for export] *)
Definition ctx_free_meta_head : Z := CTX + 16.
Definition ctx_avail_meta : Z := CTX + 24.
Definition ctx_avail_meta_count : Z := CTX + 32.
Definition ctx_avail_meta_area_count : Z := CTX + 40.
Definition ctx_meta_alloc_shift : Z := CTX + 48.
Definition ctx_meta_area_head : Z := CTX + 56.
Definition ctx_meta_area_tail : Z := CTX + 64.
Definition ctx_avail_meta_areas : Z := CTX + 72.
Definition ctx_active (sc : Z) : Z := CTX + 80 + 8 * sc.
Definition ctx_usage (sc : Z) : Z := CTX + 464 + 8 * sc.
Definition ctx_unmap_seq (i : Z) : Z := CTX + 848 + i.      (* [comment removed for export] *)
Definition ctx_bounces (i : Z) : Z := CTX + 880 + i.        (* [comment removed for export] *)
Definition ctx_seq : Z := CTX + 912.                        (* [comment removed for export] *)
Definition ctx_brk : Z := CTX + 920.
Definition CTX_END : Z := CTX + 928.                        (* [comment removed for export] *)

Definition A_NEED_LOCKS : Z := 0xa67b3.   (* [comment removed for export] *)
Definition A_PAGESIZE : Z := 0xa67e0.     (* [comment removed for export] *)
Definition A_CANARY : Z := 0xa6790.       (* [comment removed for export] *)
Definition A_GOT_CANARY : Z := 0x746f0.   (* [comment removed for export] *)
Definition TPV : Z := 0x86520.            (* [comment removed for export] *)
Definition A_ERRNO : Z := TPV - 164.      (* [comment removed for export] *)
Definition A_TAB_CTZ : Z := 0x21810.      (* [comment removed for export] *)
Definition A_TAB_SC : Z := 0x23994.       (* [comment removed for export] *)
Definition A_TAB_SMALL : Z := 0x239f4.    (* [comment removed for export] *)
Definition A_TAB_MED : Z := 0x23a0f.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition HEAPLO : Z := 4096.
(* [comment removed for export] *)
Abbreviation IMG_LO := 65536.              (* [comment removed for export] *)
Abbreviation IMG_HI := 684032.             (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Abbreviation mh_run := run_ceil.

(* [comment removed for export] *)
Definition img_free (b e : Z) : Prop := e <= IMG_LO \/ IMG_HI <= b.


Definition MMAP_THRESHOLD : Z := 131052.
Definition NSLOTS : Z := 101.             (* [comment removed for export] *)
Definition AREA_HDR : Z := 24.
Definition META_SZ : Z := 40.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition mem := word -> option byte.

(* [comment removed for export] *)
Definition cell (M : mem) (a : Z) (n : nat) (v : Z) : Prop :=
  rdn RSEGS M (Z_to_bv 64 a) n = Some (word_to_le_bytes n (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition byte_at (M : mem) (a : Z) (b : Z) : Prop := M (Z_to_bv 64 a) = Some (Z_to_bv 8 b).

(* [comment removed for export] *)
Definition defined (M : mem) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) <> None.

(* [comment removed for export] *)
Definition img_clear (M : mem) (lo hi : Z) : Prop :=
  forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mkW (lastidx freeable sc maplen : Z) : Z := lastidx + 32 * freeable + 64 * sc + 4096 * maplen.

Lemma mkW_fields : forall li fr sc ml,
  0 <= li < 32 -> 0 <= fr < 2 -> 0 <= sc < 64 -> 0 <= ml ->
  w_lastidx (mkW li fr sc ml) = li /\ w_freeable (mkW li fr sc ml) = fr /\
  w_sizeclass (mkW li fr sc ml) = sc /\ w_maplen (mkW li fr sc ml) = ml.
Proof.
  intros li fr sc ml Hli Hfr Hsc Hml. unfold mkW, w_lastidx, w_freeable, w_sizeclass, w_maplen.
  repeat split.
  - rewrite <- Z.add_assoc, <- Z.add_assoc.
    replace (32 * fr + (64 * sc + 4096 * ml)) with ((fr + 2 * sc + 128 * ml) * 32) by lia.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (li + 32 * fr + 64 * sc + 4096 * ml) with (li + (fr + (sc + 64 * ml) * 2) * 32) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (li + 32 * fr + 64 * sc + 4096 * ml) with ((li + 32 * fr) + (sc + ml * 64) * 64) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. rewrite Z.add_0_l.
    rewrite Z.mod_add by lia. apply Z.mod_small. lia.
  - replace (li + 32 * fr + 64 * sc + 4096 * ml) with ((li + 32 * fr + 64 * sc) + ml * 4096) by lia.
    rewrite Z.div_add by lia. rewrite Z.div_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record meta_rec := MR { mr_prev : Z; mr_next : Z; mr_mem : Z; mr_avail : Z; mr_freed : Z; mr_W : Z }.
Definition meta_zero : meta_rec := MR 0 0 0 0 0 0.

(* [comment removed for export] *)
Inductive slot_st :=
| SAvail                      (* [comment removed for export] *)
| SFreed                      (* [comment removed for export] *)
| SUser (p n off res : Z)     (* [comment removed for export] *)
| SHost (m' : Z) (off : Z)    (* [comment removed for export] *)
| SJunk (off : Z).            (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive gkind :=
| GTop                        (* [comment removed for export] *)
| GNest (hm hi hoff : Z).     (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rkind :=
| RBrk                        (* [comment removed for export] *)
| RMeta (exposed : Z)         (* [comment removed for export] *)
| RGroup (m : Z).             (* [comment removed for export] *)

Record region := RG { rg_base : Z; rg_len : Z; rg_kind : rkind }.

(* [comment removed for export] *)
Inductive gkd := GPlain | GNoAcc | GGone.

Inductive brk_state :=
| BrkUntried
| BrkLive (b0 b : Z) (gk : gkd)      (* [comment removed for export] *)
| BrkDead (g : option (Z * gkd)).    (* [comment removed for export] *)

(* [comment removed for export] *)
Definition guard_of (b : brk_state) : option Z :=
  match b with BrkUntried => None | BrkLive b0 _ _ => Some b0 | BrkDead (Some (b0, _)) => Some b0 | BrkDead None => None end.

(* [comment removed for export] *)
Definition guard_kind (b : brk_state) : option (Z * gkd) :=
  match b with BrkUntried => None | BrkLive b0 _ gk => Some (b0, gk) | BrkDead g => g end.

(* [comment removed for export] *)
Definition guard_noacc (b : brk_state) : option Z :=
  match guard_kind b with Some (b0, GNoAcc) => Some b0 | _ => None end.

(* [comment removed for export] *)
Definition first_brk_region (b0 : Z) (gk : gkd) : region :=
  match gk with GGone => RG (b0 + 4096) 4096 RBrk | _ => RG b0 8192 RBrk end.

(* [comment removed for export] *)
Record ctx_rec := CX {
  c_secret : Z; c_mmap_ctr : Z; c_free_head : Z; c_avail_meta : Z; c_avail_cnt : Z;
  c_area_cnt : Z; c_shift : Z; c_area_head : Z; c_area_tail : Z; c_cursor : Z;
  c_active : Z -> Z; c_usage : Z -> Z; c_unmap_seq : Z -> Z; c_bounces : Z -> Z; c_seq : Z; c_brk : Z }.

Record mst := MST {
  s_ctx : ctx_rec;
  s_areas : list Z;                 (* [comment removed for export] *)
  s_meta : Z -> meta_rec;           (* [comment removed for export] *)
  s_flist : list Z;                 (* [comment removed for export] *)
  s_alist : Z -> list Z;            (* [comment removed for export] *)
  s_groups : list Z;                (* [comment removed for export] *)
  s_ai : Z -> Z;                    (* [comment removed for export] *)
  s_kind : Z -> gkind;              (* [comment removed for export] *)
  s_slot : Z -> Z -> slot_st;       (* [comment removed for export] *)
  s_regions : list region;
  s_brk : brk_state;
  s_canary : Z; s_errno : Z;        (* [comment removed for export] *)
  s_limbo : list Z                  (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Geom.
Variable st : mst.
Let MRc := s_meta st.

Definition g_W (m : Z) : Z := mr_W (MRc m).
Definition g_mem (m : Z) : Z := mr_mem (MRc m).
Definition g_lastidx (m : Z) : Z := w_lastidx (g_W m).
Definition g_cnt (m : Z) : Z := g_lastidx m + 1.
Definition g_sc (m : Z) : Z := w_sizeclass (g_W m).
Definition g_maplen (m : Z) : Z := w_maplen (g_W m).
Definition g_stride (m : Z) : Z := slot_stride (g_maplen m) (g_lastidx m) (g_sc m).
Definition g_slot_start (m i : Z) : Z := g_mem m + UNIT + g_stride m * i.
Definition g_slot_end (m i : Z) : Z := g_slot_start m i + g_stride m - IB.
(* [comment removed for export] *)
Definition g_span_end (m : Z) : Z := g_mem m + UNIT + g_stride m * g_cnt m - IB + 1.
(* [comment removed for export] *)
Definition g_map_end (m : Z) : Z := g_mem m + 4096 * g_maplen m.
End Geom.

(* [comment removed for export] *)
Definition meta_addr (area k : Z) : Z := area + AREA_HDR + META_SZ * k.
Definition is_meta_of (areas : list Z) (m : Z) : Prop :=
  exists a k, In a areas /\ 0 <= k < NSLOTS /\ m = meta_addr a k.

(* [comment removed for export] *)
Definition fupd {A} (f : Z -> A) (x : Z) (v : A) : Z -> A := fun y => if Z.eqb y x then v else f y.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GRPMAX : Z := 2 ^ 20.          (* [comment removed for export] *)
Definition MBLK : Z := 2 ^ 20 + 2 ^ 13.   (* [comment removed for export] *)
Definition MBASE : Z := 2 ^ 30.

Definition LMAX : Z := 144.          (* [comment removed for export] *)
Definition AREAMAX : Z := 20.

Definition MSTK : Z := 2048.
