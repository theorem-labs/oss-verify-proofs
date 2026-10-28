(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.VL Require LeptPixHdr.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocCode V23RelocSites V23RelocImg V23RelocVL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23RelocMusl V23LeptEnv V23LeptG.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixHdrT2.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixHdr.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  #[local] Definition FR6 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
       (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)).

  (* [comment removed for export] *)
  Lemma ph_A : forall regs m (s w h d : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 64)%Z -> dval d ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x6dc28 : word) m rom) (mkst regs' (0x6dc64 : word) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48) /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_A fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_Abad : forall regs m (s w h d : Z) (ret : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= d < 2 ^ 64)%Z -> ~ dval d ->
    store_ok SEGS m (Z_to_bv 64 (s - 48)) 48 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x6dc28 : word) m rom) (mkst regs' (0x6dd9c : word) (FR6 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 48)
      /\ regs_agree (fun r => In r [2; 13]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_Abad fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_B : forall regs m (s w h d : Z),
    (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> dval d ->
    getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x6dc64 : word) m rom) (mkst regs' (0x6ddec : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 (4 * (wpl_of w d * h)) /\ getr regs' 14 = Z_to_bv 64 0x4000001 /\ getr regs' 20 = Z_to_bv 64 (wpl_of w d)
      /\ getr regs' 10 = Z_to_bv 64 w /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [20; 13; 14]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_B fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_C : forall regs m (sz : Z),
    (0 <= sz <= 67108864)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    exists regs',
      msteps SEGS (mkst regs (0x6ddec : word) m rom) (mkst regs' (0x6de20 : word) m rom)
      /\ getr regs' 13 = Z_to_bv 64 20001 /\ regs_agree (fun r => In r [13]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_C fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_Cbad : forall regs m (sz : Z),
    (67108864 < sz < 2 ^ 64)%Z -> getr regs 13 = Z_to_bv 64 sz -> getr regs 14 = Z_to_bv 64 0x4000001 ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x6ddec : word) m rom) (mkst regs' (0x636a4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x11fa6 /\ getr regs' 11 = Z_to_bv 64 0x15a48 /\ getr regs' 1 = Z_to_bv 64 0x6de78
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_Cbad fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  Lemma ph_D : forall regs m (w : Z),
    (1 <= w <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    msteps SEGS (mkst regs (0x6de20 : word) m rom) (mkst regs (0x6de4c : word) m rom).
  Proof. rl_tail (@VL.LeptPixHdr.ph_D fx v23_reloc v23_code_vl rom). Qed.

  Lemma ph_Dbad : forall regs m (w : Z),
    (20000 < w < 2 ^ 64)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x6de20 : word) m rom) (mkst regs' (0x636a4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x1c850 /\ getr regs' 11 = Z_to_bv 64 0x15a48 /\ getr regs' 1 = Z_to_bv 64 0x6de78
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_Dbad fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_E : forall regs m (w h d : Z),
    (1 <= h <= 20000)%Z -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d -> getr regs 13 = Z_to_bv 64 20001 ->
    exists regs',
      msteps SEGS (mkst regs (0x6de4c : word) m rom) (mkst regs' (0x10e6e0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 11 = Z_to_bv 64 64 /\ getr regs' 1 = Z_to_bv 64 0x6deb4
      /\ getr regs' 19 = Z_to_bv 64 w /\ getr regs' 9 = Z_to_bv 64 h /\ getr regs' 8 = Z_to_bv 64 d
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 19]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_E fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  Lemma ph_Ebad : forall regs m (h : Z),
    (20000 < h < 2 ^ 64)%Z -> getr regs 11 = Z_to_bv 64 h -> getr regs 13 = Z_to_bv 64 20001 ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x6de4c : word) m rom) (mkst regs' (0x636a4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x18b8f /\ getr regs' 11 = Z_to_bv 64 0x15a48 /\ getr regs' 1 = Z_to_bv 64 0x6de78
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_Ebad fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_R0 : forall regs m (s : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) ->
    exists regs',
      msteps SEGS (mkst regs (0x6de78 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_R0 fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_H : forall regs m (s msg : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 msg -> getr regs 11 = Z_to_bv 64 0x15a48 ->
    exists regs',
      msteps SEGS (mkst regs (0x6ddc0 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x15a48
      /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_H fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_G : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x6dd9c : word) m rom) (mkst regs' (0x6ddc0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x12de8 /\ getr regs' 11 = Z_to_bv 64 0x15a48
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_G fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_Fbad : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x6deb4 : word) m rom) (mkst regs' (0x6ddc0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x15a48
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_Fbad fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma ph_F : forall regs m (s w h d pix wpl : Z) (ret s0v s1v s2v s3v s4v : word),
    (48 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> dval d -> (1 <= w <= 20000)%Z -> (1 <= h <= 20000)%Z -> (0 <= wpl < 2 ^ 31)%Z ->
    (4096 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z -> (pix + 64 <= s - 48 \/ s <= pix)%Z -> (pix mod 8 = 0)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) ->
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) ->
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v) ->
    getr regs 2 = Z_to_bv 64 (s - 48) -> getr regs 10 = Z_to_bv 64 pix ->
    getr regs 19 = Z_to_bv 64 w -> getr regs 9 = Z_to_bv 64 h -> getr regs 8 = Z_to_bv 64 d -> getr regs 20 = Z_to_bv 64 wpl ->
    exists regs',
      msteps SEGS (mkst regs (0x6deb4 : word) m rom)
        (mkst regs' ret
          (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
             (Z_to_bv 64 pix) (word_to_le_bytes 4 (Z_to_bv 64 w)))
             (Z_to_bv 64 (pix + 4)) (word_to_le_bytes 4 (Z_to_bv 64 h)))
             (Z_to_bv 64 (pix + 8)) (word_to_le_bytes 4 (Z_to_bv 64 d)))
             (Z_to_bv 64 (pix + 16)) (word_to_le_bytes 4 (Z_to_bv 64 wpl)))
             (Z_to_bv 64 (pix + 12)) (word_to_le_bytes 4 (Z_to_bv 64 (spp_of d))))
             (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 1)))
             (Z_to_bv 64 (pix + 32)) (word_to_le_bytes 4 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 1 = ret
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v /\ getr regs' 18 = s2v /\ getr regs' 19 = s3v /\ getr regs' 20 = s4v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12; 18; 19; 20]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixHdr.ph_F fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.
End Segs.

(* [comment removed for export] *)
Definition cells6 (m : word -> option byte) (s : Z) (ret s0v s1v s2v s3v s4v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) /\
  rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 s2v) /\
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 s3v) /\
  rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 s4v).

Lemma cells6_FR6 : forall m s ret regs, (48 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells6 (FR6 m s ret regs) s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20).
Proof. intros m s ret regs Hs Hs64. unfold cells6, FR6. repeat split; rdn_solve. Qed.

Lemma cells6_frm : forall C s' m m' s ret s0v s1v s2v s3v s4v, Cok C -> FRM C s' m m' ->
  (s' <= s - 48)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z ->
  cells6 m s ret s0v s1v s2v s3v s4v -> cells6 m' s ret s0v s1v s2v s3v s4v.
Proof.
  intros C s' m m' s ret s0v s1v s2v s3v s4v CK F Hs' Hlo Hs64 (R1 & R2 & R3 & R4 & R5 & R6). unfold cells6.
  rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
Qed.

Lemma str_pixCreateHeader : str16 0x15a48 15. Proof. str16_tac. Qed.
Lemma str_msg_64mb : str16 0x11fa6 47. Proof. str16_tac. Qed.
Lemma str_msg_w20k : str16 0x1c850 51. Proof. str16_tac. Qed.
Lemma str_msg_h20k : str16 0x18b8f 52. Proof. str16_tac. Qed.
Lemma str_msg_depth : str16 0x12de8 38. Proof. str16_tac. Qed.
Lemma str_msg_pixd : str16 0x126da 13. Proof. str16_tac. Qed.


(* [comment removed for export] *)
Lemma ph_lerror_W : forall C A m M md regs r (s fmt : Z) kf (ret : word) (S : TSet),
  Cok C -> W C A M md -> POSTM C A s m M ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  cells6 M s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 1 = Z_to_bv 64 0x6de78 -> getr r 10 = Z_to_bv 64 fmt -> getr r 11 = Z_to_bv 64 0x15a48 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x) ->
  In fmt (SSP.ls_fmts1 LU16) -> str16 fmt kf ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ False)) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdrT ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (0x636a4 : word) M al_rom) md) S.
Proof.
  intros C A m M md regs r s fmt kf ret S CK HW PM Hs16 Hlo Hhi Hret CE R2 R1 R10 R11 RR Hin Sf HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  apply (lept_stderr1_W C A M md r (s - 48) fmt 0x15a48 kf 15 (Z_to_bv 64 0x6de78) S CK HW R2
           ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) R1 ltac:(red; apply bv_eq; reflexivity)
           R10 R11 Hin Sf str_pixCreateHeader).
  intros m2 r2 HW2 OUT2 GR2 CS2. unfold LSF in OUT2.
  replace (Z_to_bv 64 0x6de78) with (0x6de78 : word) by (apply bv_eq; reflexivity).
  assert (PM2 : POSTM C A s m m2).
  { eapply POSTM_trans; [exact PM|]. eapply (POSTM_range C A M md m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia]. }
  destruct (cells6_frm C (s - 48) M m2 s _ _ _ _ _ _ CK ltac:(intros a _ _ _ _ H5; apply OUT2; unfold scratch in H5; lia) ltac:(lia) ltac:(lia) ltac:(lia) CE)
    as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  destruct (ph_R0 al_rom r2 m2 s ret _ _ _ _ _ ltac:(lia) ltac:(lia) Hret Q1 Q2 Q3 Q4 Q5 Q6 ltac:(csr; reflexivity))
    as (r3 & RUN3 & V2 & V10 & V1 & V8 & V9 & V18 & V19 & V230 & AG3).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW2)) | exact (mp_lazy _ (w_pure _ _ _ _ HW2)) | exact RUN3 |].
  rewrite <- (with_vmmaps_same md). apply (HK A m2 (m_vmmaps md) r3).
  - rewrite with_vmmaps_same. exact HW2.
  - apply cs_kept_of_rest; [rewrite V2, H2; reflexivity | exact V8 | exact V9 |].
    rest_solve.
  - exact PM2.
  - left. split; [exact V10 | intros q; reflexivity].
  - (pose proof RB_hdrT_eq; unfold RB_hdrT in *; rewrite ?Z.mul_1_l in *; room_tac).
Qed.

(* [comment removed for export] *)
Lemma ph_eptr_W : forall C A A1 m M md (vm0 : VmMaps) regs r (s msg : Z) km (ret : word) (S : TSet),
  Cok C -> W C A1 M md -> POSTM C A s m M -> (forall q, live A1 q = live A q) ->
  roomtr A vm0 A1 (m_vmmaps md) RK_hdr RB_hdrT ->
  (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z -> ret_ok ret ->
  cells6 M s ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ->
  getr r 2 = Z_to_bv 64 (s - 48) -> getr r 10 = Z_to_bv 64 msg -> getr r 11 = Z_to_bv 64 0x15a48 ->
  (forall x, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r x = getr regs x) -> str16 msg km ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ False)) ->
     roomtr A vm0 A' vm' RK_hdr RB_hdrT ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  getr regs 2 = Z_to_bv 64 s ->
  realizes SEGS (mkCfg (mkst r (0x6ddc0 : word) M al_rom) md) S.
Proof.
  intros C A A1 m M md vm0 regs r s msg km ret S CK HW PM LQ RT0 Hs16 Hlo Hhi Hret CE R2 R10 R11 RR Sm HK H2.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  destruct CE as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6).
  destruct (ph_H al_rom r M s msg ret _ _ _ _ _ ltac:(lia) ltac:(lia) Q1 Q2 Q3 Q4 Q5 Q6 R2 R10 R11)
    as (r1 & RUN1 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V230 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  apply (returnErrorPtr_W C A1 M md r1 s msg 0x15a48 km 15 ret (Z_to_bv 64 0) S CK HW V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
           V10 V11 V12 Sm str_pixCreateHeader).
  intros m2 r2 HW2 OUT2 GR2 CS2 A10. unfold LSF in OUT2.
  rewrite <- (with_vmmaps_same md). apply (HK A1 m2 (m_vmmaps md) r2).
  - rewrite with_vmmaps_same. exact HW2.
  - apply cs_kept_of_rest; [csr; reflexivity | csr; reflexivity | csr; reflexivity |]. rest_solve.
  - eapply POSTM_trans; [exact PM|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LQ|].
    eapply (POSTM_range C A1 M md m2); [exact CK | exact HW | exact OUT2 | lia | lia | lia].
  - left. split; [exact A10 | exact LQ].
  - exact RT0.
Qed.

Theorem pixCreateHeader_szT2_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 48 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ (O23LeptPixHdrT2.hdr_ok w h d /\ O23LeptPixHdrT2.pix_new C A A' m' pix (O23LeptPixHdrT2.pix_hdr w h d)))) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdrT ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6dc28 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 48) 48 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  
  assert (HK0 : forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q) \/ (exists pix, getr regs' 10 = Z_to_bv 64 pix /\ False)) ->
     roomtr A (m_vmmaps md) A' vm' RK_hdr RB_hdrT ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S).
  { intros A' m' vm' regs' X1 X2 X3 X4 X5. apply (HK A' m' vm' regs' X1 X2 X3); [| exact X5]. destruct X4 as [L|(pix & _ & [])]. left; exact L. }
  assert (RR0 : forall x, In x cs_rest -> getr regs x = getr regs x) by (intros; reflexivity).
  destruct (dval_dec d) as [DV|ND].
  all: cycle 1.
  - 
    destruct (ph_Abad al_rom regs m s w h d ret ltac:(lia) ltac:(lia) Hd ND SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (FR6 m s ret regs) md /\ POSTM C A s m (FR6 m s ret regs)) by (unfold FR6; wp_win CK).
    destruct WP1 as [HW1 PM1].
    destruct (ph_G al_rom r1 (FR6 m s ret regs) (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r2 & RUN2 & P10 & P11 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    apply (ph_eptr_W C A A m (FR6 m s ret regs) md (m_vmmaps md) regs r2 s 0x12de8 38 ret S CK HW1 PM1 ltac:(intros; reflexivity) ltac:((pose proof RB_hdrT_eq; unfold RB_hdrT in *; rewrite ?Z.mul_1_l in *; room_tac)) Hs16 ltac:(unfold LSF; lia) Hhi Hret
             (cells6_FR6 m s ret regs ltac:(lia) ltac:(lia)) ltac:(csr; reflexivity) P10 P11 ltac:(rest_solve)
             str_msg_depth HK0 H2).
  - 
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    destruct (ph_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) Hd DV SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q10 & Q11 & Q12 & AG1).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
    assert (WP1 : W C A (FR6 m s ret regs) md /\ POSTM C A s m (FR6 m s ret regs)) by (unfold FR6; wp_win CK).
    destruct WP1 as [HW1 PM1]. set (M1 := FR6 m s ret regs) in *.
    pose proof (cells6_FR6 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
    destruct (ph_B al_rom r1 M1 s w h d Hw Hh Hwh DV Q10 Q11 Q12) as (r2 & RUN2 & P13 & P14 & P8 & P10 & P11 & P12 & AG2).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN2 |].
    assert (RR2 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r2 x = getr regs x) by (unfold cs_rest in RR0; rest_solve).
    assert (P2 : getr r2 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (Hszhi : (4 * (wpl_of w d * h) < 2 ^ 64)%Z) by nia.
    destruct (Z_lt_ge_dec 67108864 (4 * (wpl_of w d * h))) as [BIG|SMALL].
    { 
      destruct (ph_Cbad al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r3 & RUN3 & V10 & V11 & V1 & AG3).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
      apply (ph_lerror_W C A m M1 md regs r3 s 0x11fa6 47 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) V1 V10 V11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_64mb HK0 H2). }
    destruct (ph_C al_rom r2 M1 (4 * (wpl_of w d * h)) ltac:(lia) P13 P14) as (r3 & RUN3 & V13 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN3 |].
    assert (RR3 : forall x, In x [3; 4; 18; 19; 21; 22; 23; 24; 25; 26; 27]%bv -> getr r3 x = getr regs x) by rest_solve.
    assert (V10 : getr r3 10 = Z_to_bv 64 w) by (csr; reflexivity).
    assert (V11 : getr r3 11 = Z_to_bv 64 h) by (csr; reflexivity).
    assert (V12 : getr r3 12 = Z_to_bv 64 d) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    destruct (Z_lt_ge_dec 20000 w) as [WBIG|WOK].
    { 
      destruct (ph_Dbad al_rom r3 M1 w ltac:(lia) V10 V13 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r4 & RUN4 & X10 & X11 & X1 & AG4).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
      apply (ph_lerror_W C A m M1 md regs r4 s 0x1c850 51 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) X1 X10 X11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_w20k HK0 H2). }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact (ph_D al_rom r3 M1 w ltac:(lia) V10 V13) |].
    destruct (Z_lt_ge_dec 20000 h) as [HBIG|HOK].
    { 
      destruct (ph_Ebad al_rom r3 M1 h ltac:(lia) V11 V13 (W_sev_got C A _ md HW1) (W_sev C A _ md HW1)) as (r4 & RUN4 & X10 & X11 & X1 & AG4).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
      apply (ph_lerror_W C A m M1 md regs r4 s 0x18b8f 52 ret S CK HW1 PM1 Hs16 ltac:(unfold LSF; lia) Hhi Hret CE1
               ltac:(csr; reflexivity) X1 X10 X11 ltac:(rest_solve) ltac:(cbn; repeat (first [left; reflexivity | right])) str_msg_h20k HK0 H2). }
    
    destruct (ph_E al_rom r3 M1 w h d ltac:(lia) V10 V11 V12 V13) as (r4 & RUN4 & X10 & X11 & X1 & X19 & X9 & X8 & AG4).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW1)) | exact (mp_lazy _ (w_pure _ _ _ _ HW1)) | exact RUN4 |].
    assert (X4 : getr r4 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
    assert (X20 : getr r4 20 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
    replace (0x10e6e0 : word) with (Z_to_bv 64 0x10e6e0) by (apply bv_eq; reflexivity).
    apply (W_calloc16 C A M1 md r4 1 64 (Z_to_bv 64 0x6deb4) (s - 48) S CK HW1 X10 X11 ltac:(lia) ltac:(lia) ltac:(lia) X1
             ltac:(red; apply bv_eq; reflexivity) X4 X2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
             ltac:(unfold CALLOC_STACK, ALLOC_STACK; lia) ltac:(lia)).
    intros A1 m1 vm1 r5 res HWa Hres CSa OUTa PMa HRTa.
    replace (Z_to_bv 64 0x6deb4) with (0x6deb4 : word) by (apply bv_eq; reflexivity).
    assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
    pose proof (cells6_frm C (s - 48) M1 m1 s _ _ _ _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
    destruct OUTa as [[Hres0 LIVEQ] | (Hnz & L0 & L1 & L00 & LEQ & ZERO & AL16 & TOP)].
    + 
      rewrite Hres0 in Hres.
      destruct (ph_Fbad al_rom r5 m1 (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Hres) as (r6 & RUN6 & Y10 & Y11 & AG6).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      apply (ph_eptr_W C A A1 m m1 (with_vmmaps vm1 md) (m_vmmaps md) regs r6 s 0x126da 13 ret S CK HWa PMa' LIVEQ ltac:((pose proof RB_hdrT_eq; unfold RB_hdrT in *; rewrite ?Z.mul_1_l in *; room_tac)) Hs16 ltac:(unfold LSF; lia) Hhi Hret CE2
               ltac:(csr; reflexivity) Y10 Y11 ltac:(rest_solve) str_msg_pixd).
      * intros A' m' vm' regs' HW' CS' PM' OUT' RT'. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HW'.
        exact (HK0 A' m' vm' regs' HW' CS' PM' OUT' RT').
      * exact H2.
    + 
      assert (Hpx : (4096 <= u res)%Z /\ (u res + 64 <= alloc_top (c_vm C))%Z).
      { destruct (blk_range C A1 m1 _ res (1 * 64) CK HWa L1 ltac:(lia)) as [G1 G2]. lia. }
      pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
      assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
      set (pix := u res) in *. clearbody pix.
      rewrite Eres in Hres, L0, L1, L00, LEQ, ZERO.
      assert (PX0 : PIXat m1 pix pix0).
      { apply PIXat_zero; [lia | lia |]. intros i Hi. unfold at_ in ZERO. rewrite u_Z2bv in ZERO by lia. apply ZERO. lia. }
      destruct CE2 as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6).
      assert (Y19 : getr r5 19 = Z_to_bv 64 w) by (csr; reflexivity).
      assert (Y9 : getr r5 9 = Z_to_bv 64 h) by (csr; reflexivity).
      assert (Y8 : getr r5 8 = Z_to_bv 64 d) by (csr; reflexivity).
      assert (Y20 : getr r5 20 = Z_to_bv 64 (wpl_of w d)) by (csr; reflexivity).
      assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 48)) by (csr; reflexivity).
      assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact AL16 | reflexivity]).
      destruct (ph_F al_rom r5 m1 s w h d pix (wpl_of w d) ret (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) ltac:(lia) ltac:(lia) Hret DV ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) AL8)
        as (r6 & RUN6 & V2' & V10' & V1' & V8' & V9' & V18' & V19' & V230' & AG6).
      { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
        unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m1 pix pix0 x PX0 ltac:(lia) E). }
      { exact Z1. } { exact Z2. } { exact Z3. } { exact Z4. } { exact Z5. } { exact Z6. }
      { exact Y2. } { exact Hres. } { exact Y19. } { exact Y9. } { exact Y8. } { exact Y20. }
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN6 |].
      assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M7 := MM) end.
      assert (WP7 : W C A1 M7 (with_vmmaps vm1 md) /\ POSTM C A s m M7).
      { subst M7.
        repeat (apply (WP_blk C A A1 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact L1 | exact L0 | exact L00 | exact SUBa | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia]).
        split; [exact HWa | exact PMa']. }
      destruct WP7 as [HW7 PM7].
      pose proof (spp_of_range d) as Hspp.
      assert (PX7 : PIXat M7 pix (O23LeptPixHdrT2.pix_hdr w h d)).
      { subst M7. unfold O23LeptPixHdrT2.pix_hdr.
        apply (PIX_wr_fmt _ pix (PIXV w h d (spp_of d) (wpl_of w d) 1 0 0 0 0 0 0 0) 0); [|lia].
        apply (PIX_wr_rc _ pix (PIXV w h d (spp_of d) (wpl_of w d) 0 0 0 0 0 0 0 0) 1); [|lia].
        apply (PIX_wr_spp _ pix (PIXV w h d 0 (wpl_of w d) 0 0 0 0 0 0 0 0) (spp_of d)); [|lia].
        apply (PIX_wr_wpl _ pix (PIXV w h d 0 0 0 0 0 0 0 0 0 0) (wpl_of w d)); [|lia].
        apply (PIX_wr_d _ pix (PIXV w h 0 0 0 0 0 0 0 0 0 0 0) d); [|lia].
        apply (PIX_wr_h _ pix (PIXV w 0 0 0 0 0 0 0 0 0 0 0 0) h); [|lia].
        apply (PIX_wr_w _ pix pix0 w); [exact PX0|lia]. }
      apply (HK A1 M7 vm1 r6 HW7).
      * apply cs_kept_of_rest; [csr; reflexivity | csr; reflexivity | csr; reflexivity |]. rest_solve.
      * exact PM7.
      * right. exists pix. split; [exact V10'|]. split; [unfold O23LeptPixHdrT2.hdr_ok; repeat split; try assumption; lia|].
        unfold O23LeptPixHdrT2.pix_new. do 7 (split; [first [assumption | lia] |]). exact PX7.
      * (pose proof RB_hdrT_eq; unfold RB_hdrT in *; rewrite ?Z.mul_1_l in *; room_tac).
Qed.



End PixHdr.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
