(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr V2LeptCmap.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require LiaFast.   (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.VL Require LeptPixDestroy.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocVL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2RelocMusl V2LeptEnv V2LeptG.
Import ListNotations.
Open Scope bv_scope.

Section PixDestroy.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Definition pixd_post (A A' : AS) (pix data cm arr : Z) : Prop :=
  live A' (Z_to_bv 64 pix) = None /\
  (data <> 0%Z -> live A' (Z_to_bv 64 data) = None) /\
  (cm <> 0%Z -> live A' (Z_to_bv 64 cm) = None /\ live A' (Z_to_bv 64 arr) = None) /\
  (forall q, q <> Z_to_bv 64 pix -> (data <> 0%Z -> q <> Z_to_bv 64 data) -> (cm <> 0%Z -> q <> Z_to_bv 64 cm /\ q <> Z_to_bv 64 arr) ->
             live A' q = live A q).
Theorem pixDestroy_W : forall C A m md regs (s pp pix cm karr R : Z) (v : pixv) (cv : cmapv) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 64 + ALLOC_STACK <= s)%Z -> (s <= pp)%Z -> (pp + 8 <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x56270 -> (pp mod 8 = 0)%Z ->
  getr regs 10 = Z_to_bv 64 pp -> rdn SEGS m (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 pix) ->
  PIXat m pix v -> p_rc v = 1%Z -> p_text v = 0%Z -> p_cmap v = cm ->
  live A (Z_to_bv 64 pix) = Some 64%Z -> live (c_A0 C) (Z_to_bv 64 pix) = None ->
  (p_data v = 0%Z \/ (live A (Z_to_bv 64 (p_data v)) = Some R /\ live (c_A0 C) (Z_to_bv 64 (p_data v)) = None /\ (0 < R)%Z /\
                      p_data v <> pix /\ (cm <> 0%Z -> p_data v <> cm /\ p_data v <> c_arr cv))) ->
  (cm = 0%Z \/ (CMAPat m cm cv /\ live A (Z_to_bv 64 cm) = Some 24%Z /\ live A (Z_to_bv 64 (c_arr cv)) = Some karr /\
                live (c_A0 C) (Z_to_bv 64 cm) = None /\ live (c_A0 C) (Z_to_bv 64 (c_arr cv)) = None /\
                cm <> c_arr cv /\ cm <> pix /\ c_arr cv <> pix /\ (0 < karr)%Z)) ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' ->
     pixd_post A A' pix (p_data v) cm (c_arr cv) ->
     POSTM C (c_A0 C) (pp + 8) m m' -> rdn SEGS m' (Z_to_bv 64 pp) 8 = Some (Z_to_le_bytes 8 0) ->
     roomtr A (m_vmmaps md) A' vm' 0 0 ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x1982c : word) m al_rom) md) S.
Proof. rl_tail (@LeptPixDestroy.pixDestroy_W fx v2_reloc v2_sites v2_code_vl v2_sites_vl v2_lept v2_img_vl v2_data v2_rw AL CL ASR PINS (v2_pinsG P16)). Qed.

End PixDestroy.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).      (* [comment removed for export] *)
