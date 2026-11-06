(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.edge_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptRecs LeptArith LeptNuma LeptRoom LeptRoom9.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptBase.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9CL8a.
Import V9CL8a.V9LeptPixHdr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.V9 Require Import V9LeptPixCopy.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition NCR_STACK : Z := 32 + CALLOC_STACK.                      (* [comment removed for export] *)
Definition NDS_STACK : Z := 32 + ALLOC_STACK.                       (* [comment removed for export] *)
Definition RNW_STACK : Z := 48 + CALLOC_STACK.                      (* [comment removed for export] *)
Definition NEX_STACK : Z := 16 + RNW_STACK.                         (* [comment removed for export] *)
Definition NAN_STACK : Z := 32 + NEX_STACK.                         (* [comment removed for export] *)
Definition GEP_STACK : Z := 144 + 80 + NAN_STACK.                   (* [comment removed for export] *)
Definition NFE_STACK : Z := 128 + NAN_STACK.                        (* [comment removed for export] *)
Definition PMES_STACK : Z := 112 + GEP_STACK + LSF.                 (* [comment removed for export] *)

(* [comment removed for export] *)
Definition PC_numaCreate : Z := 0x61688.
Definition PC_numaDestroy : Z := 0x61794.
Definition PC_numaAddNumber : Z := 0x61848.
Definition PC_numaExtendArray : Z := 0x619bc.
Definition PC_reallocNew : Z := 0x5e334.
Definition PC_numaGetCount : Z := 0x61970.
Definition PC_numaGetFValue : Z := 0x61ad0.
Definition PC_numaGetIValue : Z := 0x61bc0.
Definition PC_numaFindExtrema : Z := 0x613c0.
Definition PC_pixGetPixel : Z := 0x6496c.
Definition PC_pixGetEdgeProfile : Z := 0x82768.
Definition PC_pixMeasureEdgeSmoothness : Z := 0x82400.
(* [comment removed for export] *)
Definition TP9 : Z := 0x10a858.

Section EdgeIface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V9Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition numaCreate_contract : Prop :=
  forall (fx : FPState) C A m md regs (s n : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NCR_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP9 ->
  getr regs 10 = Z_to_bv 64 n -> (0 <= n <= 20000)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_numa <= kR)%Z -> (RB_numa (numa_n0 n) <= bR)%Z ->
  (forall A' m' vm' regs' (na arr : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 na -> numa_new C A A' m' na (numa_n0 n) arr ->
     aroom A' vm' (kR - RK_numa) (bR - RB_numa (numa_n0 n)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_numaCreate) m al_rom) md) S.

(* [comment removed for export] *)
Definition numaDestroy_contract : Prop :=
  forall (fx : FPState) C A m md regs (s pp na nalloc n arr : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NDS_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z -> (pp mod 8 = 0)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP9 ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 na) ->
  numa_at C A m na nalloc n arr ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     live A' (Z_to_bv 64 na) = None -> live A' (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 na -> q <> Z_to_bv 64 arr -> live A' q = live A q) ->
     POSTM C A' (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_numaDestroy) m al_rom) md) S.

(* [comment removed for export] *)
Definition numaAddNumber_store_contract : Prop :=
  forall (fx : FPState) C Ar A m md regs (s na nalloc n arr : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NAN_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 na -> numa_at C A m na nalloc n arr -> (n < nalloc)%Z ->
  live Ar (Z_to_bv 64 na) = None -> live Ar (Z_to_bv 64 arr) = None ->
  (forall (fx' : FPState) m' regs', frm_zero (@fp_csr fx') -> W C A m' md -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     numa_at C A m' na nalloc (n + 1) arr ->
     ncell SEGS m' arr n (u (low32 (reg_get (@fp_regs fx) 10))) ->
     (forall a : word, ~ (s - NAN_STACK <= u a < s)%Z -> ~ (na + 4 <= u a < na + 8)%Z -> ~ (arr + 4 * n <= u a < arr + 4 * n + 4)%Z -> m' a = m a) ->
     getr regs' 10 = Z_to_bv 64 0 ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_numaAddNumber) m al_rom) md) S.

(* [comment removed for export] *)
Definition numaAddNumber_grow_contract : Prop :=
  forall (fx : FPState) C Ar A m md regs (s na nalloc arr : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NAN_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP9 ->
  getr regs 10 = Z_to_bv 64 na -> numa_at C A m na nalloc nalloc arr -> (2 * nalloc <= NUMA_NMAX)%Z ->
  live Ar (Z_to_bv 64 na) = None -> live Ar (Z_to_bv 64 arr) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (1 <= kR)%Z -> (RB_numagrow nalloc <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs' (arr' : Z), frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     POSTM C Ar s m m' ->
     numa_at C A' m' na (2 * nalloc) (nalloc + 1) arr' ->
     live A (Z_to_bv 64 arr') = None -> live A' (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 arr -> q <> Z_to_bv 64 arr' -> live A' q = live A q) ->
     getr regs' 10 = Z_to_bv 64 0 ->
     aroom A' vm' (kR - 1) (bR - RB_numagrow nalloc) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_numaAddNumber) m al_rom) md) S.

(* [comment removed for export] *)
Definition numaExtendArray_contract : Prop :=
  forall (fx : FPState) C Ar A m md regs (s na nalloc n arr : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> sub_live Ar A ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NEX_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP9 ->
  getr regs 10 = Z_to_bv 64 na -> numa_at C A m na nalloc n arr -> (2 * nalloc <= NUMA_NMAX)%Z ->
  live Ar (Z_to_bv 64 na) = None -> live Ar (Z_to_bv 64 arr) = None ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (1 <= kR)%Z -> (RB_numagrow nalloc <= bR)%Z ->
  (forall A' m' vm' regs' (arr' : Z), W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C Ar s m m' ->
     numa_at C A' m' na (2 * nalloc) n arr' ->
     live A (Z_to_bv 64 arr') = None -> live A' (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 arr -> q <> Z_to_bv 64 arr' -> live A' q = live A q) ->
     getr regs' 10 = Z_to_bv 64 0 ->
     aroom A' vm' (kR - 1) (bR - RB_numagrow nalloc) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (Z_to_bv 64 PC_numaExtendArray) m al_rom) md) S.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pixGetEdgeProfile_contract : Prop :=
  forall (fx : FPState) C A m md regs (s pixs w h cm data : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + GEP_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP9 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 0 ->
  PIXat m pixs (hdv w h 1 cm data) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w 1 * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_numa <= kR)%Z -> (RB_numa h <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs' (na arr : Z), frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 na -> numa_at C A' m' na h h arr ->
     live A (Z_to_bv 64 na) = None -> live A (Z_to_bv 64 arr) = None ->
     (forall q, q <> Z_to_bv 64 na -> q <> Z_to_bv 64 arr -> live A' q = live A q) ->
     prof_cells SEGS m' arr h 0 (w - 1) ->
     aroom A' vm' (kR - RK_numa) (bR - RB_numa h) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixGetEdgeProfile) m al_rom) md) S.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition numaFindExtrema_contract : Prop :=
  forall (fx : FPState) C A m md regs (s nas nalloc n arr : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + NFE_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP9 ->
  getr regs 10 = Z_to_bv 64 nas -> getr regs 11 = Z_to_bv 64 0 ->
  reg_get (@fp_regs fx) 10 = nan_box (Z_to_bv 32 0x3f800000) ->
  numa_at C A m nas nalloc n arr -> (2 <= n <= 20000)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_nfe <= kR)%Z -> (RB_nfe <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs' (nad nalloc' c arr' : Z), frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) ->
     cs_kept regs regs' -> POSTM C A s m m' ->
     getr regs' 10 = Z_to_bv 64 nad -> numa_at C A' m' nad nalloc' c arr' ->
     live A (Z_to_bv 64 nad) = None -> live A (Z_to_bv 64 arr') = None ->
     (forall q, q <> Z_to_bv 64 nad -> q <> Z_to_bv 64 arr' -> live A' q = live A q) ->
     aroom A' vm' (kR - RK_nfe) (bR - RB_nfe) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_numaFindExtrema) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixMeasureEdgeSmoothness_contract : Prop :=
  forall (fx : FPState) C A m md regs (s pixs w h d cm data : Z) (ret : word) (S : TSet),
  frm_zero (@fp_csr fx) -> Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PMES_STACK <= s)%Z -> (s + 16 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 TP9 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 1 -> getr regs 12 = Z_to_bv 64 1 -> getr regs 13 = Z_to_bv 64 1 ->
  getr regs 14 = Z_to_bv 64 (s + 12) -> getr regs 15 = Z_to_bv 64 (s + 8) -> getr regs 16 = Z_to_bv 64 (s + 4) -> getr regs 17 = Z_to_bv 64 0 ->
  PIXat m pixs (hdv w h d cm data) -> hdr_ok w h d -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 data) = Some (4 * (wpl_of w d * h))%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pmes <= kR)%Z -> (RB_pmes h <= bR)%Z ->
  (forall (fx' : FPState) A' m' vm' regs', frm_zero (@fp_csr fx') -> W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     POSTM C A (s + 16) m m' -> (forall q, live A' q = live A q) ->
     aroom A' vm' (kR - RK_pmes) (bR - RB_pmes h) ->
     realizes SEGS (mkCfg (@mkst fx' regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst fx regs (Z_to_bv 64 PC_pixMeasureEdgeSmoothness) m al_rom) md) S.

End EdgeIface.
