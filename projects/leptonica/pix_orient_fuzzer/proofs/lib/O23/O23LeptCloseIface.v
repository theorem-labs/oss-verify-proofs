(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.pix_orient_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk FPSteps.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptDefs LeptStructs LeptArith LeptExecB LeptRecs LeptSel.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom LeptRoomPC LeptRoom14 LeptRoomBL.
From OSSVerify.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require Import O23LeptStderr O23LeptBase O23LeptPixHdr O23LeptCmapValid O23LeptPixCopyT O23LeptDilW O23LeptCloseSpec.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition wr8 (m : word -> option byte) (p v : Z) : word -> option byte := wbytes m (Z_to_bv 64 p) (word_to_le_bytes 8 (Z_to_bv 64 v)).

(* [comment removed for export] *)
Definition CSELS_STACK : Z := 48 + 4112 + 16.
Definition SELD_STACK : Z := 48 + ALLOC_STACK + 32.
Definition RBG32_STACK : Z := 96 + 112 + LSF.
Definition PCG_STACK : Z := 48 + 96 + 16 + LSF.

(* [comment removed for export] *)
Definition csels_K (size : Z) : Z := if (size =? 30)%Z then 6 else 16.
Definition csels_shape (size dir : Z) (sv1 sv2 : selv) : Prop :=
  (size = 8 /\ dir = 2 /\ v_sy sv1 = 4 /\ v_sx sv1 = 1 /\ v_cy sv1 = 2 /\ v_cx sv1 = 0 /\
                          v_sy sv2 = 8 /\ v_sx sv2 = 1 /\ v_cy sv2 = 4 /\ v_cx sv2 = 0)%Z
  \/ (size = 30 /\ dir = 1 /\ v_sy sv1 = 1 /\ v_sx sv1 = 6 /\ v_cy sv1 = 0 /\ v_cx sv1 = 3 /\
                              v_sy sv2 = 1 /\ v_sx sv2 = 30 /\ v_cy sv2 = 0 /\ v_cx sv2 = 15)%Z.

Section CloseIface.
Context {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LL16} {P16 : O23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).

(* [comment removed for export] *)
Definition selectComposableSels_contract : Prop :=
  forall (fr : bvmap 5 word) (cs : bv 32) C A m md regs (s size dir p1 p2 : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md -> frm_zero cs ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + CSELS_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x123d20 ->
  getr regs 10 = Z_to_bv 64 size -> getr regs 11 = Z_to_bv 64 dir -> getr regs 12 = Z_to_bv 64 p1 -> getr regs 13 = Z_to_bv 64 p2 ->
  ((size = 8 /\ dir = 2) \/ (size = 30 /\ dir = 1))%Z ->
  (s <= p1)%Z -> (p1 + 8 <= c_top C)%Z -> (s <= p2)%Z -> (p2 + 8 <= c_top C)%Z -> (p1 + 8 <= p2 \/ p2 + 8 <= p1)%Z ->
  (p1 mod 8 = 0)%Z -> (p2 mod 8 = 0)%Z ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (csels_K size <= kR)%Z -> (csels_K size * 2 ^ 17 <= bR)%Z ->
  (forall (fr' : bvmap 5 word) (cs' : bv 32) A' m' vm' regs' (sel1 sel2 : Z) (sv1 sv2 : selv) (c1 c2 : Z -> Z -> Z),
     frm_zero cs' -> (forall r : reg, In (u r) fs_list -> reg_get fr' r = reg_get fr r) ->
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 0 ->
     sub_live A A' -> POSTM C A s (wr8 (wr8 m p1 sel1) p2 sel2) m' ->
     sel_at (alloc_top (c_vm C)) A' m' sel1 sv1 -> sel_at (alloc_top (c_vm C)) A' m' sel2 sv2 ->
     sel_cont m' sv1 c1 -> sel_cont m' sv2 c2 -> v_name sv1 = 0%Z -> v_name sv2 = 0%Z -> csels_shape size dir sv1 sv2 ->
     (forall p, sel_blk sel1 sv1 p \/ sel_blk sel2 sv2 p -> live A (Z_to_bv 64 p) = None /\ live (c_A0 C) (Z_to_bv 64 p) = None) ->
     (forall p q, sel_blk sel1 sv1 p -> sel_blk sel2 sv2 q -> p <> q) ->
     (forall q : word, (forall p, sel_blk sel1 sv1 p \/ sel_blk sel2 sv2 p -> q <> Z_to_bv 64 p) -> live A' q = live A q) ->
     aroom A' vm' (kR - csels_K size) (bR - csels_K size * 2 ^ 17) ->
     realizes SEGS (mkCfg (@mkst (mkFP fr' cs') regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (@mkst (mkFP fr cs) regs (0x90f1c : word) m al_rom) md) S.

Context {fx : FPState}.

(* [comment removed for export] *)
Definition selDestroy_contract : Prop :=
  forall C A m md regs (s psel sel : Z) (sv : selv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELD_STACK <= s)%Z -> (s <= psel)%Z -> (psel + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x123d20 ->
  getr regs 10 = Z_to_bv 64 psel -> rdn SEGS m (Z_to_bv 64 psel) 8 = Some (Z_to_le_bytes 8 sel) ->
  sel_at (alloc_top (c_vm C)) A m sel sv -> v_name sv = 0%Z -> (v_sy sv = 1 \/ v_sy sv = 4 \/ v_sy sv = 5 \/ v_sy sv = 8)%Z ->
  (forall p, sel_blk sel sv p -> live (c_A0 C) (Z_to_bv 64 p) = None) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (forall p, sel_blk sel sv p -> live A' (Z_to_bv 64 p) = None) ->
     (forall q : word, (forall p, sel_blk sel sv p -> q <> Z_to_bv 64 p) -> live A' q = live A q) ->
     POSTM C A' (psel + 8) m m' -> rdn SEGS m' (Z_to_bv 64 psel) 8 = Some (Z_to_le_bytes 8 0) ->
     (forall a : word, (s <= u a < psel)%Z -> m' a = m a) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x923f0 : word) m al_rom) md) S.

(* [comment removed for export] *)
Definition selDestroy_null_contract : Prop :=
  forall C A m md regs (s psel : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + SELD_STACK <= s)%Z -> (s <= psel)%Z -> (psel + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret ->
  getr regs 10 = Z_to_bv 64 psel -> rdn SEGS m (Z_to_bv 64 psel) 8 = Some (Z_to_le_bytes 8 0) ->
  (forall m' regs', W C A m' md -> cs_kept regs regs' -> POSTM C A s m m' ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) md) S) ->
  realizes SEGS (mkCfg (mkst regs (0x923f0 : word) m al_rom) md) S.

(* [comment removed for export] *)
Definition pixRemoveBorder32_contract : Prop :=
  forall C A m md regs (s pixs w h cm datas : Z) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + RBG32_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x123d20 ->
  getr regs 10 = Z_to_bv 64 pixs -> getr regs 11 = Z_to_bv 64 32 ->
  PIXat m pixs (hdv (w + 64) (h + 64) 1 cm datas) -> hdr_ok (w + 64) (h + 64) 1 -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of (w + 64) 1 * (h + 64)))%Z ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ cmap_ok cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z)) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_pixcopy <= kR)%Z -> ((RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm) <= bR)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     (exists pixd cd data, getr regs' 10 = Z_to_bv 64 pixd /\ pixt_new C A A' m' pixd w h 1 cd data cv /\ POSTM C A s m m') ->
     aroom A' vm' (kR - RK_pixcopy) (bR - (RB_pixT (4 * (wpl_of w 1 * h)) + RB_cmapT cm)) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6f3cc : word) m al_rom) md) S.

(* [comment removed for export] *)
Definition pcg_cm (C : lctx) (A : AS) (m : word -> option byte) (cm : Z) (cv : cmapv) : Prop :=
  cm = 0%Z \/ (cm <> 0%Z /\ CMAPat m cm cv /\ cmap_ok cv /\
               live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some (4 * c_nalloc cv)%Z).
Definition pixCopy_given_contract : Prop :=
  forall C A m md regs (s pixd pixs w h cms datas cmd datad : Z) (cvs cvd : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + PCG_STACK <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x123d20 ->
  getr regs 10 = Z_to_bv 64 pixd -> getr regs 11 = Z_to_bv 64 pixs -> pixd <> pixs ->
  PIXat m pixs (hdv w h 1 cms datas) -> PIXat m pixd (hdv w h 1 cmd datad) -> hdr_ok w h 1 -> (1 <= w)%Z -> (1 <= h)%Z ->
  live A (Z_to_bv 64 pixs) = Some 64%Z -> live A (Z_to_bv 64 datas) = Some (4 * (wpl_of w 1 * h))%Z ->
  live A (Z_to_bv 64 pixd) = Some 64%Z -> live A (Z_to_bv 64 datad) = Some (4 * (wpl_of w 1 * h))%Z ->
  live (c_A0 C) (Z_to_bv 64 pixd) = None -> live (c_A0 C) (Z_to_bv 64 datad) = None ->
  pcg_cm C A m cms cvs -> pcg_cm C A m cmd cvd ->
  (cmd <> 0%Z -> live (c_A0 C) (Z_to_bv 64 cmd) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cvd)) = None) ->
  forall (kR bR : Z), aroom A (m_vmmaps md) kR bR -> (RK_cmapcopy <= kR)%Z -> (RB_cmapT cms <= bR)%Z ->
  (forall A' m' vm' regs' (cmd' : Z) (cvd' : cmapv),
     W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> getr regs' 10 = Z_to_bv 64 pixd ->
     FRM C s m m' ->
     (forall (q : word) k i, live A q = Some k -> q <> Z_to_bv 64 pixd -> q <> Z_to_bv 64 datad ->
                             q <> Z_to_bv 64 cmd -> q <> Z_to_bv 64 (c_arr cvd) -> (0 <= i < k)%Z -> m' (at_ q i) = m (at_ q i)) ->
     (forall (q : word) k, live A q = Some k -> (cmd <> 0%Z -> q <> Z_to_bv 64 cmd /\ q <> Z_to_bv 64 (c_arr cvd)) -> live A' q = Some k) ->
     PIXat m' pixd (hdv w h 1 cmd' datad) ->
     ( (cms = 0%Z /\ cmd' = 0%Z /\
        (forall q : word, (cmd <> 0%Z -> q <> Z_to_bv 64 cmd /\ q <> Z_to_bv 64 (c_arr cvd)) -> live A' q = live A q) /\
        (cmd <> 0%Z -> live A' (Z_to_bv 64 cmd) = None /\ live A' (Z_to_bv 64 (c_arr cvd)) = None))
       \/ (cms <> 0%Z /\ cmd' <> 0%Z /\ CMAPat m' cmd' cvd' /\ cmap_ok cvd' /\
           c_d cvd' = c_d cvs /\ c_nalloc cvd' = c_nalloc cvs /\ c_n cvd' = c_n cvs /\
           live A' (Z_to_bv 64 cmd') = Some 24%Z /\ live A' (Z_to_bv 64 (c_arr cvd')) = Some (4 * c_nalloc cvd')%Z /\
           live (c_A0 C) (Z_to_bv 64 cmd') = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cvd')) = None /\
           (forall (q : word) k, live A q = Some k -> (cmd <> 0%Z -> q <> Z_to_bv 64 cmd /\ q <> Z_to_bv 64 (c_arr cvd)) ->
                                 q <> Z_to_bv 64 cmd' /\ q <> Z_to_bv 64 (c_arr cvd')) /\
           (forall q : word, (cmd <> 0%Z -> q <> Z_to_bv 64 cmd /\ q <> Z_to_bv 64 (c_arr cvd)) ->
                             q <> Z_to_bv 64 cmd' -> q <> Z_to_bv 64 (c_arr cvd') -> live A' q = live A q) /\
           (forall q : word, cmd <> 0%Z -> (q = Z_to_bv 64 cmd \/ q = Z_to_bv 64 (c_arr cvd)) ->
                             q <> Z_to_bv 64 cmd' -> q <> Z_to_bv 64 (c_arr cvd') -> live A' q = None)) ) ->
     aroom A' vm' (kR - RK_cmapcopy) (bR - RB_cmapT cms) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6d480 : word) m al_rom) md) S.

End CloseIface.
