(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.pix_orient_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23LeptStderr V23LeptBase V23LeptErr V23LeptPixHdr V23LeptPixHdrT2 V23LeptPadBitsW V23Memset.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import LeptRoom14 LeptRoomBL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.Common.Leptonica.VL Require LeptPixCreate.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23Reloc V23RelocCode V23RelocSites V23RelocImg V23RelocVL.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.V23 Require Import V23RelocMusl V23LeptEnv V23LeptG.
From OssFuzzTheorems.Proofs.leptonica.pix_orient_fuzzer.lib.O23 Require O23LeptPixCreateT2 O23LeptPixHdrT2.
Import ListNotations.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok_in SOK :=
  store_ok_peel;
  first [ exact SOK
        | eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia ].

Section PixCreate.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V23Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.

  #[local] Definition FR4 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)).

  (* [comment removed for export] *)
  Lemma pn_A : forall regs m (s w h d : Z) (ret : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
    exists regs',
      msteps SEGS (mkst regs (0x6dae0 : word) m rom) (mkst regs' (0x6dc28 : word) (FR4 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x6daf8 /\ getr regs' 10 = Z_to_bv 64 w
      /\ getr regs' 11 = Z_to_bv 64 h /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 9 = Z_to_bv 64 h
      /\ regs_agree (fun r => In r [1; 2; 9]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pn_A fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pn_F1 : forall regs m (s : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x6daf8 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x13c81
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pn_F1 fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pn_B : forall regs m (s h pix : Z) (v : pixv),
    PIXat m pix v -> p_h v = h -> (1 <= h <= 20000)%Z -> (1 <= p_wpl v <= 20000)%Z -> (4096 <= pix)%Z -> (pix mod 8 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 0x127c78) 8 = Some (Z_to_le_bytes 8 0x10e958) ->
    getr regs 10 = Z_to_bv 64 pix -> getr regs 9 = Z_to_bv 64 h ->
    exists regs',
      msteps SEGS (mkst regs (0x6daf8 : word) m rom) (mkst regs' (0x10e958 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (4 * (p_wpl v * h)) /\ getr regs' 1 = Z_to_bv 64 0x6db30 /\ getr regs' 8 = Z_to_bv 64 pix
      /\ getr regs' 9 = Z_to_bv 64 0x127c78
      /\ regs_agree (fun r => In r [1; 8; 9; 10; 11; 12]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pn_B fx v23_reloc v23_sites v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pn_C : forall regs m (pix data : Z),
    (4096 <= pix)%Z -> (pix + 64 < 2 ^ 64)%Z -> (1 <= data < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 pix) 64 = true ->
    getr regs 10 = Z_to_bv 64 data -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6db30 : word) m rom)
                  (mkst regs' (0x70a54 : word) (wbytes m (Z_to_bv 64 (pix + 56)) (word_to_le_bytes 8 (Z_to_bv 64 data))) rom)
      /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x6db44 /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pn_C fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pn_D : forall regs m (s pix : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6db44 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pix
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pn_D fx v23_reloc v23_code_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pn_F2 : forall regs m (s pix : Z) (v : pixv),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> PIXat m pix v -> p_rc v = 1%Z -> p_data v = 0%Z -> p_text v = 0%Z -> p_cmap v = 0%Z ->
    (4096 <= pix)%Z -> (pix mod 16 = 0)%Z -> (pix + 64 <= s - 32 \/ s <= pix)%Z ->
    store_ok SEGS m (Z_to_bv 64 pix) 64 = true -> store_ok SEGS m (Z_to_bv 64 (s - 32)) 32 = true ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6db30 : word) m rom)
                  (mkst regs' (0x10e818 : word)
                     (wbytes (wbytes m (Z_to_bv 64 (pix + 20)) (word_to_le_bytes 4 (Z_to_bv 64 0)))
                             (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 32) /\ getr regs' 1 = Z_to_bv 64 0x6dbd4 /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 10; 11]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pn_F2 fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pn_F3 : forall regs m,
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x6dbd4 : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x1b993 /\ getr regs' 11 = Z_to_bv 64 0x13c81 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x6dc00
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pn_F3 fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  (* [comment removed for export] *)
  Lemma pn_F4 : forall regs m (s : Z) (ret s0v s1v : word),
    (32 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) ->
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v) ->
    getr regs 2 = Z_to_bv 64 (s - 32) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x6dc00 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0
      /\ getr regs' 8 = s0v /\ getr regs' 9 = s1v
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 10]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pn_F4 fx v23_reloc v23_code_vl rom). Qed.
  (* [comment removed for export] *)
  Lemma pk_A : forall regs m (s : Z) (ret : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 16)) 16 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret ->
    exists regs',
      msteps SEGS (mkst regs (0x6da3c : word) m rom)
                  (mkst regs' (0x6dae0 : word) (wbytes (wbytes m (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret)) (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 16) /\ getr regs' 1 = Z_to_bv 64 0x6da4c
      /\ getr regs' 10 = getr regs 10 /\ getr regs' 11 = getr regs 11 /\ getr regs' 12 = getr regs 12
      /\ regs_agree (fun r => In r [1; 2]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pk_A fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  Lemma pk_F : forall regs m (s : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 0x126a70) 8 = Some (Z_to_le_bytes 8 0x127c60) -> rdn SEGS m (Z_to_bv 64 0x127c60) 4 = Some (Z_to_le_bytes 4 3) ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs',
      msteps SEGS (mkst regs (0x6da4c : word) m rom) (mkst regs' (0x63740 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 0x126da /\ getr regs' 11 = Z_to_bv 64 0x1521c
      /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 12]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pk_F fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  Lemma pk_B : forall regs m (pix : Z) (v : pixv),
    PIXat m pix v -> (4096 <= pix)%Z -> (1 <= p_h v <= 20000)%Z -> (1 <= p_wpl v <= 20000)%Z -> (pix mod 8 = 0)%Z ->
    getr regs 10 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6da4c : word) m rom) (mkst regs' (0x11e6d4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 (4 * (p_wpl v * p_h v))
      /\ getr regs' 1 = Z_to_bv 64 0x6da88 /\ getr regs' 8 = Z_to_bv 64 pix
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pk_B fx v23_reloc v23_code_vl v23_sites_vl rom). Qed.

  Lemma pk_C : forall regs m (s pix : Z) (ret s0v : word),
    (16 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret ->
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) ->
    getr regs 2 = Z_to_bv 64 (s - 16) -> getr regs 8 = Z_to_bv 64 pix ->
    exists regs',
      msteps SEGS (mkst regs (0x6da88 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 10 = Z_to_bv 64 pix /\ getr regs' 8 = s0v
      /\ regs_agree (fun r => In r [1; 2; 8; 10]%list) regs regs'.
  Proof. rl_tail (@VL.LeptPixCreate.pk_C fx v23_reloc v23_code_vl rom). Qed.

End Segs.

Definition cells4 (m : word -> option byte) (s : Z) (ret s0v s1v : word) : Prop :=
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
  rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 s0v) /\
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 s1v).

Lemma cells4_FR4 : forall m s ret regs, (32 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells4 (FR4 m s ret regs) s ret (getr regs 8) (getr regs 9).
Proof. intros m s ret regs Hs Hs64. unfold cells4, FR4. repeat split; rdn_solve. Qed.

Lemma cells4_frm : forall C s' m m' s ret s0v s1v, Cok C -> FRM C s' m m' ->
  (s' <= s - 24)%Z -> (c_top C - LSTK <= s')%Z -> (s < 2 ^ 64)%Z ->
  cells4 m s ret s0v s1v -> cells4 m' s ret s0v s1v.
Proof.
  intros C s' m m' s ret s0v s1v CK F Hs' Hlo Hs64 (R1 & R2 & R3). unfold cells4.
  rewrite !(FRM_rdn16 C s' m m' _ 8 CK F) by (cbn; lia). repeat split; assumption.
Qed.

Lemma cells4_out : forall m m' (lo hi s : Z) ret s0v s1v,
  (forall x : word, ~ (lo <= u x < hi)%Z -> m' x = m x) -> (hi <= s - 24)%Z -> (24 <= s)%Z -> (s < 2 ^ 64)%Z ->
  cells4 m s ret s0v s1v -> cells4 m' s ret s0v s1v.
Proof.
  intros m m' lo hi s ret s0v s1v OUT Hhi Hs Hs64 (R1 & R2 & R3). unfold cells4.
  repeat split; (eapply (rdn_after m m' lo hi); [exact OUT | lia | cbn; lia | cbn; lia | assumption]).
Qed.

Lemma str_pixCreateNoInit : str16 0x13c81 15. Proof. str16_tac. Qed.
Lemma str_msg_pixd : str16 0x126da 13. Proof. str16_tac. Qed.
Lemma str_msg_datafail : str16 0x1b993 28. Proof. str16_tac. Qed.

(* [comment removed for export] *)

Theorem pixCreateNoInit_szT2_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 96 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix data, getr regs' 10 = Z_to_bv 64 pix /\ O23LeptPixHdrT2.hdr_ok w h d /\ O23LeptPixCreateT2.pixr_new C A A' m' pix data (set_data (O23LeptPixHdrT2.pix_hdr w h d) data))) ->
     roomtr A (m_vmmaps md) A' vm' RK_pix (RB_pixT (4 * (wpl_of w d * h))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6dae0 : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 32) 32 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pn_A al_rom regs m s w h d ret ltac:(lia) ltac:(lia) SOK H2 H1 H10 H11 H12) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & Q9 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  assert (WP1 : W C A (FR4 m s ret regs) md /\ POSTM C A s m (FR4 m s ret regs)) by (unfold FR4; wp_win CK).
  destruct WP1 as [HW1 PM1]. set (M1 := FR4 m s ret regs) in *.
  pose proof (cells4_FR4 m s ret regs ltac:(lia) ltac:(lia)) as CE1. fold M1 in CE1.
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  apply (pixCreateHeader_szT2_W C A M1 md r1 (s - 32) w h d (Z_to_bv 64 0x6daf8) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh Hwh Hd).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x6daf8) with (0x6daf8 : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  pose proof (cells4_frm C (s - 32) M1 m1 s _ _ _ CK (proj1 PMa) ltac:(lia) ltac:(lia) ltac:(lia) CE1) as CE2.
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
  assert (E9 : getr r2 9 = Z_to_bv 64 h) by (csr; reflexivity).
  assert (E4 : getr r2 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pix & Hres & HOK & PN)].
  - 
    destruct CE2 as (Z1 & Z2 & Z3).
    destruct (pn_F1 al_rom r2 m1 s ret _ _ ltac:(lia) ltac:(lia) (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) Z1 Z2 Z3 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & V9 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m1 _ r3 s 0x126da 0x13c81 13 15 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreateNoInit).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5).
    + exact HW4.
    + apply cs_kept_intro; csr; try reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m1 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + (unfold RB_pixT, RB_hdrT in *; room_tac).
  - 
    destruct HOK as (DV & Hw2 & Hh2 & Hsz). destruct PN as (Gp & TOPp & ALp & L0 & L00 & L1 & LEQ & PX1).
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
    destruct (pn_B al_rom r2 m1 s h pix (O23LeptPixHdrT2.pix_hdr w h d) PX1 eq_refl ltac:(lia) ltac:(cbn; lia) Gp AL8 (W_pmm_malloc C A1 m1 _ HWa) Hres E9)
      as (r3 & RUN3 & V10 & V1 & V8 & V9 & AG3).
    cbn [p_wpl O23LeptPixHdrT2.pix_hdr] in V10.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (V4 : getr r3 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    assert (V2 : getr r3 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    replace (0x10e958 : word) with (Z_to_bv 64 0x10e958) by (apply bv_eq; reflexivity).
    apply (W_malloc16 C A1 m1 _ r3 (4 * (wpl_of w d * h)) (Z_to_bv 64 0x6db30) (s - 32) S CK HWa V10 ltac:(lia) V1
             ltac:(red; apply bv_eq; reflexivity) V4 V2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
    intros A2 m2 vm2 r4 res HWb Hres2 CSb OUTb PMb HRTb. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWb.
    replace (Z_to_bv 64 0x6db30) with (0x6db30 : word) by (apply bv_eq; reflexivity).
    assert (SUBa : sub_live A A1) by (eapply sub_live_new; eassumption).
    assert (PMb' : POSTM C A s m m2).
    { eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1 _ _ _ SUBa). eapply POSTM_mono; [|exact PMb]. lia. }
    pose proof (cells4_frm C (s - 32) m1 m2 s _ _ _ CK (proj1 PMb) ltac:(lia) ltac:(lia) ltac:(lia) CE2) as CE3.
    assert (PX2 : PIXat m2 pix (O23LeptPixHdrT2.pix_hdr w h d)).
    { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. pose proof (proj2 PMb (Z_to_bv 64 pix) 64%Z (u x - pix)%Z L1 ltac:(lia)) as E.
      unfold at_ in E. rewrite u_Z2bv in E by lia. replace (pix + (u x - pix))%Z with (u x) in E by lia. rewrite zbv_self in E. exact E. }
    assert (X8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    assert (X2 : getr r4 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
    assert (X4 : getr r4 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
    assert (SOKp : store_ok SEGS m2 (Z_to_bv 64 pix) 64 = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx.
      unfold wview. destruct (m2 x) eqn:E; [discriminate|]. exfalso. exact (PIXat_defined m2 pix _ x PX2 ltac:(lia) E). }
    destruct OUTb as [[Hres0 LIVEQ] | (Hnz & K0 & K1 & K00 & KEQ & AL16 & TOP)].
    + 
      rewrite Hres0 in Hres2.
      destruct (pn_F2 al_rom r4 m2 s pix (O23LeptPixHdrT2.pix_hdr w h d) ltac:(lia) ltac:(lia) PX2 eq_refl eq_refl eq_refl eq_refl Gp ALp ltac:(lia) SOKp
                  (W_sok_win C A2 m2 _ (s - 32) 32 CK HWb ltac:(lia) ltac:(cbn; lia)) X2 Hres2 X8)
        as (r5 & RUN5 & Y2 & Y1 & Y10 & Y8 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M3 := MM) end.
      assert (Lp2 : live A2 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite LIVEQ; exact L1).
      assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A s m M3).
      { subst M3. apply (WP_win C A2 A m _ _ _ _ s CK); [| exact (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) | rewrite u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; cbn; lia | lia].
        apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact Lp2 | exact L0 | exact L00 | exact (sub_live_trans _ _ _ SUBa (sub_live_eq _ _ LIVEQ)) | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
        split; [exact HWb | exact PMb']. }
      destruct WP3 as [HW3 PM3].
      assert (Y4 : getr r5 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
      replace (0x10e818 : word) with (Z_to_bv 64 0x10e818) by (apply bv_eq; reflexivity).
      apply (W_free16 C A2 M3 _ r5 (Z_to_bv 64 pix) (Z_to_bv 64 0x6dbd4) 64 (s - 32) S CK HW3 Y10 Lp2 L00 Y1
               ltac:(red; apply bv_eq; reflexivity) Y4 Y2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold ALLOC_STACK; lia) ltac:(lia)).
      intros A3 m3 vm3 r6 HWc CSc Lc LEQc PMc HRTc. rewrite with_vmmaps_twice. rewrite with_vmmaps_twice in HWc.
      replace (Z_to_bv 64 0x6dbd4) with (0x6dbd4 : word) by (apply bv_eq; reflexivity).
      destruct (pn_F3 al_rom r6 m3 (W_sev_got C A3 m3 _ HWc) (W_sev C A3 m3 _ HWc)) as (r7 & RUN7 & Z10 & Z11 & Z12 & Z1' & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWc)) | exact (mp_lazy _ (w_pure _ _ _ _ HWc)) | exact RUN7 |].
      assert (Z2' : getr r7 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      apply (returnErrorPtr_W C A3 m3 _ r7 (s - 32) 0x1b993 0x13c81 28 15 (Z_to_bv 64 0x6dc00) (Z_to_bv 64 0) S CK HWc Z2'
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Z1' ltac:(red; apply bv_eq; reflexivity)
               Z10 Z11 Z12 str_msg_datafail str_pixCreateNoInit).
      intros m4 r8 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
      replace (Z_to_bv 64 0x6dc00) with (0x6dc00 : word) by (apply bv_eq; reflexivity).
      assert (LIVEQ3 : forall q, live A3 q = live A q).
      { intros q. destruct (bv_eq_dec _ q (Z_to_bv 64 pix)) as [->|NE]; [rewrite Lc, L0; reflexivity|]. rewrite (LEQc q NE), LIVEQ. apply LEQ. exact NE. }
      assert (PM4 : POSTM C A s m m4).
      { eapply POSTM_trans; [exact PM3|].
        eapply POSTM_trans; [apply (POSTM_sub C A A3); [apply sub_live_eq; exact LIVEQ3 | eapply POSTM_mono; [|exact PMc]; lia]|].
        apply (POSTM_sub C A A3); [apply sub_live_eq; exact LIVEQ3|].
        eapply (POSTM_range C A3 m3 _ m4); [exact CK | exact HWc | exact OUT4 | lia | lia | lia]. }
      assert (CE4 : cells4 m4 s ret (getr regs 8) (getr regs 9)).
      { apply (cells4_out m3 m4 (s - 32 - (16 + 3376)) (s - 32) s); [exact OUT4 | lia | lia | lia |].
        apply (cells4_frm C (s - 32) M3 m3 s); [exact CK | exact (proj1 PMc) | lia | lia | lia |].
        subst M3. destruct CE3 as (C1 & C2 & C3). unfold cells4.
        repeat split; repeat rdn_peel1; assumption. }
      destruct CE4 as (C1 & C2 & C3).
      assert (W2 : getr r8 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      destruct (pn_F4 al_rom r8 m4 s ret _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 W2 A10) as (r9 & RUN9 & U2 & U1 & U10 & U8 & U9 & AG9).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW4)) | exact (mp_lazy _ (w_pure _ _ _ _ HW4)) | exact RUN9 |].
      apply (HK A3 m4 vm3 r9 HW4).
      * apply cs_kept_intro; csr; try reflexivity.
      * exact PM4.
      * left. split; [exact U10 | exact LIVEQ3].
      * (unfold RB_pixT, RB_hdrT in *; room_tac).
    + 
      assert (Hdat : (4096 <= u res)%Z /\ (u res + 4 * (wpl_of w d * h) <= alloc_top (c_vm C))%Z).
      { destruct (blk_range C A2 m2 _ res _ CK HWb K1 ltac:(lia)) as [G1 G2]. lia. }
      assert (Eres : res = Z_to_bv 64 (u res)) by (symmetry; apply zbv_self).
      set (data := u res) in *. clearbody data.
      rewrite Eres in Hres2, K0, K1, K00, KEQ.
      assert (NEpd : Z_to_bv 64 pix <> Z_to_bv 64 data) by (intros E; rewrite E in L1; congruence).
      assert (NEpd' : pix <> data) by (intros E; apply NEpd; rewrite E; reflexivity).
      assert (Lp2 : live A2 (Z_to_bv 64 pix) = Some 64%Z) by (rewrite (KEQ _ NEpd); exact L1).
      assert (LAd : live A (Z_to_bv 64 data) = None) by (rewrite <- (LEQ _ (not_eq_sym NEpd)); exact K0).
      assert (SUBb : sub_live A A2) by (eapply sub_live_trans; [exact SUBa | eapply sub_live_new; eassumption]).
      destruct (pn_C al_rom r4 m2 pix data Gp ltac:(lia) ltac:(lia) SOKp Hres2 X8) as (r5 & RUN5 & Y10 & Y11 & Y1 & Y8 & AG5).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWb)) | exact (mp_lazy _ (w_pure _ _ _ _ HWb)) | exact RUN5 |].
      match goal with |- realizes _ (mkCfg (mkst _ _ ?MM _) _) _ => set (M3 := MM) end.
      assert (WP3 : W C A2 M3 (with_vmmaps vm2 md) /\ POSTM C A s m M3).
      { subst M3. apply (WP_blk C A A2 m _ _ (Z_to_bv 64 pix) _ 64); [exact CK | | exact Lp2 | exact L0 | exact L00 | exact SUBb | rewrite !u_Z2bv by lia; lia | rewrite length_N_to_le_bytes, !u_Z2bv by lia; cbn; lia].
        split; [exact HWb | exact PMb']. }
      destruct WP3 as [HW3 PM3].
      assert (PX3 : PIXat M3 pix (set_data (O23LeptPixHdrT2.pix_hdr w h d) data)) by (subst M3; apply PIX_wr_data; [exact PX2 | lia]).
      assert (Y2 : getr r5 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      apply (padbits_W C A A2 M3 _ r5 (s - 32) pix (set_data (O23LeptPixHdrT2.pix_hdr w h d) data) (Z_to_bv 64 0x6db44) S CK HW3 SUBb Y2
               ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity) ltac:(unfold LSF; lia) ltac:(lia) Y1 ltac:(red; apply bv_eq; reflexivity) Y10 Y11
               PX3 DV ltac:(cbn; lia) ltac:(cbn; lia) eq_refl Lp2).
      { cbn. exact K1. } { cbn. exact LAd. } { cbn. exact K00. } { cbn. exact NEpd. }
      intros m5 r6 HW5 CS5 PM5 PX5 OUT5 A10.
      replace (Z_to_bv 64 0x6db44) with (0x6db44 : word) by (apply bv_eq; reflexivity).
      assert (CE5 : cells4 m5 s ret (getr regs 8) (getr regs 9)).
      { apply (cells4_frm C (s - 32) M3 m5 s); [exact CK | exact (proj1 PM5) | lia | lia | lia |].
        subst M3. destruct CE3 as (C1 & C2 & C3). unfold cells4. repeat split; repeat rdn_peel1; assumption. }
      destruct CE5 as (C1 & C2 & C3).
      assert (W2 : getr r6 2 = Z_to_bv 64 (s - 32)) by (csr; reflexivity).
      assert (W8 : getr r6 8 = Z_to_bv 64 pix) by (csr; reflexivity).
      destruct (pn_D al_rom r6 m5 s pix ret _ _ ltac:(lia) ltac:(lia) Hret C1 C2 C3 W2 W8) as (r7 & RUN7 & U2 & U1 & U10 & U8 & U9 & AG7).
      eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN7 |].
      apply (HK A2 m5 vm2 r7 HW5).
      * apply cs_kept_intro; csr; try reflexivity.
      * eapply POSTM_trans; [exact PM3 | eapply POSTM_mono; [|exact PM5]; lia].
      * right. exists pix, data. split; [exact U10|]. split; [split; [exact DV | lia]|].
        unfold O23LeptPixCreateT2.pixr_new. cbn [p_wpl p_h p_data set_data O23LeptPixHdrT2.pix_hdr].
        do 15 (try (split; [first [assumption | lia | idtac] |])).
        all: try assumption; try lia; try reflexivity.
        all: intros q N1 N2; rewrite (KEQ q N2); apply LEQ; exact N1.
      * (unfold RB_pixT, RB_hdrT in *; room_tac).
Qed.

Lemma str_pixCreate : str16 0x1521c 9. Proof. str16_tac. Qed.

Theorem pixCreate_szT2_W : forall C A m md regs (s w h d : Z) (ret : word) (S : TSet),
  Cok C -> W C A m md ->
  getr regs 2 = Z_to_bv 64 s -> (s mod 16 = 0)%Z -> (c_top C - LSTK + 112 + LSF <= s)%Z -> (s <= c_top C)%Z ->
  getr regs 1 = ret -> ret_ok ret -> getr regs 4 = Z_to_bv 64 0x1381d0 ->
  getr regs 10 = Z_to_bv 64 w -> getr regs 11 = Z_to_bv 64 h -> getr regs 12 = Z_to_bv 64 d ->
  (1 <= w <= 1000000)%Z -> (1 <= h <= 1000000)%Z -> (w * h <= 400000000)%Z -> (0 <= d < 2 ^ 64)%Z ->
  (forall A' m' vm' regs', W C A' m' (with_vmmaps vm' md) -> cs_kept regs regs' -> POSTM C A s m m' ->
     ((getr regs' 10 = Z_to_bv 64 0 /\ forall q, live A' q = live A q)
      \/ (exists pix data, getr regs' 10 = Z_to_bv 64 pix /\ O23LeptPixHdrT2.hdr_ok w h d /\ O23LeptPixCreateT2.pixr_new C A A' m' pix data (set_data (O23LeptPixHdrT2.pix_hdr w h d) data))) ->
     roomtr A (m_vmmaps md) A' vm' RK_pix (RB_pixT (4 * (wpl_of w d * h))) ->
     realizes SEGS (mkCfg (mkst regs' ret m' al_rom) (with_vmmaps vm' md)) S) ->
  realizes SEGS (mkCfg (mkst regs (0x6da3c : word) m al_rom) md) S.
Proof.
  intros C A m md regs s w h d ret S CK HW H2 Hs16 Hlo Hhi H1 Hret H4 H10 H11 H12 Hw Hh Hwh Hd HK.
  pose proof CK as [T1 T2 T3 T4 T5]. laypins. cbn [fst snd ll_img LLU16] in *. unfold LSF in *.
  pose proof (W_sok_win C A m md (s - 16) 16 CK HW ltac:(lia) ltac:(cbn; lia)) as SOK.
  destruct (pk_A al_rom regs m s ret ltac:(lia) ltac:(lia) SOK H2 H1) as (r1 & RUN1 & Q2 & Q1 & Q10 & Q11 & Q12 & AG1).
  eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW)) | exact (mp_lazy _ (w_pure _ _ _ _ HW)) | exact RUN1 |].
  set (M1 := wbytes (wbytes m _ _) _ _).
  assert (WP1 : W C A M1 md /\ POSTM C A s m M1) by (subst M1; wp_win CK).
  destruct WP1 as [HW1 PM1].
  assert (Q4 : getr r1 4 = Z_to_bv 64 0x1381d0) by (csr; reflexivity).
  rewrite H10 in Q10. rewrite H11 in Q11. rewrite H12 in Q12.
  apply (pixCreateNoInit_szT2_W C A M1 md r1 (s - 16) w h d (Z_to_bv 64 0x6da4c) S CK HW1 Q2 ltac:(rewrite <- Zminus_mod_idemp_l, Hs16; reflexivity)
           ltac:(unfold LSF; lia) ltac:(lia) Q1 ltac:(red; apply bv_eq; reflexivity) Q4 Q10 Q11 Q12 Hw Hh Hwh Hd).
  intros A1 m1 vm1 r2 HWa CSa PMa OUTa HRTa.
  replace (Z_to_bv 64 0x6da4c) with (0x6da4c : word) by (apply bv_eq; reflexivity).
  assert (PMa' : POSTM C A s m m1) by (eapply POSTM_trans; [exact PM1 | eapply POSTM_mono; [|exact PMa]; lia]).
  assert (R8 : rdn SEGS m1 (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret)).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 8) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (R16 : rdn SEGS m1 (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (getr regs 8))).
  { rewrite (FRM_rdn16 C (s - 16) M1 m1 (s - 16) 8 CK (proj1 PMa)) by (cbn; lia). subst M1. rdn_solve. }
  assert (E2 : getr r2 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
  destruct OUTa as [[Hres0 LIVEQ] | (pix & data & Hres & HOK & PN)].
  - destruct (pk_F al_rom r2 m1 s ret (getr regs 8) ltac:(lia) ltac:(lia) (W_sev_got C A1 m1 _ HWa) (W_sev C A1 m1 _ HWa) R8 R16 E2 Hres0)
      as (r3 & RUN3 & V2 & V1 & V10 & V11 & V12 & V8 & AG3).
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    apply (returnErrorPtr_W C A1 m1 _ r3 s 0x126da 0x1521c 13 9 ret (Z_to_bv 64 0) S CK HWa V2 Hs16 ltac:(unfold LSF; lia) Hhi V1 Hret
             V10 V11 V12 str_msg_pixd str_pixCreate).
    intros m4 r5 HW4 OUT4 GR4 CS4 A10. unfold LSF in OUT4.
    apply (HK A1 m4 vm1 r5 HW4).
    + apply cs_kept_intro; csr; try reflexivity.
    + eapply POSTM_trans; [exact PMa'|]. apply (POSTM_sub C A A1); [apply sub_live_eq; exact LIVEQ|].
      eapply (POSTM_range C A1 m1 _ m4); [exact CK | exact HWa | exact OUT4 | lia | lia | lia].
    + left. split; [exact A10 | exact LIVEQ].
    + (unfold RB_pixT, RB_hdrT in *; room_tac).
  - destruct HOK as (DV & Hw2 & Hh2 & Hsz).
    destruct PN as (Gp & TOPp & ALp & Gd & TOPd & ALd & NEpd & L0 & K0 & L00 & K00 & L1 & K1 & LEQ & PX1 & Hdata).
    cbn [p_wpl p_h p_data set_data O23LeptPixHdrT2.pix_hdr] in TOPd, K1, Hdata.
    pose proof (dval_range d DV) as Hd32. pose proof (wpl_of_range w d ltac:(lia) DV) as Hwpl.
    pose proof (alloc_top_lt (c_vm C)) as ATL. unfold two_pow_64 in ATL.
    assert (AL8 : (pix mod 8 = 0)%Z) by (rewrite <- (Z.add_0_r pix); apply mod16_plus_mod8; [exact ALp | reflexivity]).
    destruct (pk_B al_rom r2 m1 pix _ PX1 Gp ltac:(cbn; lia) ltac:(cbn; lia) AL8 Hres) as (r3 & RUN3 & V10 & V11 & V12 & V1 & V8 & AG3).
    cbn [p_wpl p_h p_data set_data O23LeptPixHdrT2.pix_hdr] in V10, V12.
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HWa)) | exact (mp_lazy _ (w_pure _ _ _ _ HWa)) | exact RUN3 |].
    assert (SOKd : store_ok SEGS m1 (Z_to_bv 64 data) (Z.to_nat (4 * (wpl_of w d * h))) = true).
    { rewrite <- p16_segs. apply store_ok_of_all; rewrite u_Z2bv by lia; [lia|]. intros x Hx.
      unfold wview. destruct (m1 x) eqn:E; [discriminate|]. exfalso.
      destruct (blk_byte C A1 m1 _ (Z_to_bv 64 data) _ x CK HWa K1 ltac:(rewrite u_Z2bv by lia; lia)) as (_ & D & _). exact (D E). }
    apply (memset_at (with_vmmaps vm1 md) r3 m1 al_rom data (4 * (wpl_of w d * h)) (Z_to_bv 64 0x6da88) S
             (md_pure_with_vmmaps _ _ (w_pure _ _ _ _ HW)) ltac:(lia) ltac:(lia) ltac:(lia) SOKd ltac:(red; apply bv_eq; reflexivity) V1 V10 V11 V12).
    intros r4 A10' AG4.
    replace (Z_to_bv 64 0x6da88) with (0x6da88 : word) by (apply bv_eq; reflexivity).
    set (M5 := zf m1 data [(0, 4 * (wpl_of w d * h))%Z]).
    assert (OUT5 : forall x : word, (u x < data \/ data + 4 * (wpl_of w d * h) <= u x)%Z -> M5 x = m1 x).
    { intros x Hx. subst M5. apply zf_outside. apply inzr_falseP. cbn [inzrP]. lia. }
    assert (CH : forall a, M5 a <> m1 a -> scratch C s a \/ (exists p n, live A1 p = Some n /\ live A p = None /\ (u p <= u a < u p + n)%Z)).
    { intros a NE. right. exists (Z_to_bv 64 data), (4 * (wpl_of w d * h))%Z. rewrite u_Z2bv by lia. split; [exact K1 | split; [exact K0|]].
      destruct (Z_lt_ge_dec (u a) data); [exfalso; apply NE; apply OUT5; lia|].
      destruct (Z_lt_ge_dec (u a) (data + 4 * (wpl_of w d * h))); [lia | exfalso; apply NE; apply OUT5; lia]. }
    assert (HW5 : W C A1 M5 (with_vmmaps vm1 md)).
    { apply (W_local C A1 m1 _ M5 s CK HWa Hhi); [| subst M5; apply zf_grows].
      intros a NE. destruct (CH a NE) as [X|(p & n & L & _ & R)]; [left; exact X | right; exists p, n]. split; [exact L | split; [| exact R]].
      destruct (bv_eq_dec _ p (Z_to_bv 64 data)) as [->|NE']; [exact K00|].
      exfalso.  apply NE. apply OUT5.
      pose proof (ai_live_disjoint A1 m1 _ _ _ _ _ (w_inv _ _ _ _ HWa) L K1 NE') as D. rewrite u_Z2bv in D by lia.
      pose proof (ai_live_hull A1 m1 _ _ _ (w_inv _ _ _ _ HWa) L) as (Hn0 & _). pose proof (round16_ge n Hn0).
      pose proof (round16_ge (4 * (wpl_of w d * h)) ltac:(lia)). lia. }
    assert (PM5 : POSTM C A s m M5).
    { eapply POSTM_trans; [exact PMa'|]. exact (POSTM_local C A A1 m1 _ M5 s CK HWa (sub_live_new2 _ _ _ _ _ _ L0 K0 L1 K1 LEQ) CH). }
    assert (PX5 : PIXat M5 pix (set_data (O23LeptPixHdrT2.pix_hdr w h d) data)).
    { apply (PIXat_frame m1); [exact PX1|]. intros x Hx. apply OUT5.
      pose proof (ai_live_disjoint A1 m1 _ _ _ _ _ (w_inv _ _ _ _ HWa) L1 K1 (zneq_w pix data ltac:(lia) ltac:(lia) NEpd)) as D. rewrite !u_Z2bv in D by lia.
      unfold round16 in D at 1. change ((64 + 15) / 16)%Z with 4%Z in D. pose proof (round16_ge (4 * (wpl_of w d * h)) ltac:(lia)). lia. }
    assert (W2 : getr r4 2 = Z_to_bv 64 (s - 16)) by (csr; reflexivity).
    assert (W8 : getr r4 8 = Z_to_bv 64 pix) by (csr; reflexivity).
    destruct (pk_C al_rom r4 M5 s pix ret (getr regs 8) ltac:(lia) ltac:(lia) Hret) as (r5 & RUN5 & U2 & U1 & U10 & U8 & AG5).
    { rewrite <- R8. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT5. lia. }
    { rewrite <- R16. apply rdn_ext; rewrite u_Z2bv by lia; [cbn; lia|]. intros x Hx. cbn in Hx. apply OUT5. lia. }
    { exact W2. } { exact W8. }
    eapply rz_msteps; [exact (mp_halted _ (w_pure _ _ _ _ HW5)) | exact (mp_lazy _ (w_pure _ _ _ _ HW5)) | exact RUN5 |].
    apply (HK A1 M5 vm1 r5 HW5).
    + apply cs_kept_intro; csr; try reflexivity.
    + exact PM5.
    + right. exists pix, data. split; [exact U10|]. split; [split; [exact DV | lia]|].
      unfold O23LeptPixCreateT2.pixr_new. cbn [p_wpl p_h p_data set_data O23LeptPixHdrT2.pix_hdr]. repeat (split; [first [assumption | lia] |]); try assumption.
      all: first [exact PX5 | reflexivity | assumption].
    + (unfold RB_pixT, RB_hdrT in *; room_tac).
Qed.

End PixCreate.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
