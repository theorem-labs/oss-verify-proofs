(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.leptonica.bilateral_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare ShapeAlg AllocIface PureModel VmLedger StoreOk MemSplit RefMemcpyLib StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Mallocng Require Import AllocBase AllocCalloc AllocSure.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import SumWalkTac SumSpecs WalksLib W2Lib LibAtomic LeptDefs LeptStructs LeptArith LeptArith2.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2LeptStderr V2LeptBase V2LeptErr.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import LeptRoom.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Reloc Require Import Reloc.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica Require Import RelocLept.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.Common.Leptonica.VL Require LeptDeserA LeptDeserB.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2Reloc V2RelocCode V2RelocSites V2RelocImg V2RelocVL.
From OssFuzzTheorems.Proofs.leptonica.bilateral_fuzzer.lib.V2 Require Import V2RelocMusl V2LeptEnv V2LeptG.
Import ListNotations.
Open Scope bv_scope.

Section DeserA.
Context {fx : FPState} {AL : AllocLayout} {CL : CallocLayout} {ASR : AllocSure}.
Context {PINS : @LeptPins AL LLU16} {P16 : V2Pins}.
#[local] Notation "'u'" := bv_unsigned (only parsing).
Section Segs.
Variable rom : word -> option byte.
Definition FR9 (m : word -> option byte) (s : Z) (ret : word) (regs : bvmap 5 word) : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
       (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 ret))
       (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
       (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
       (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
       (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
       (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
       (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
       (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
       (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)).
Lemma pd_A0 : forall regs m (s dp nb : Z) (ret : word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= dp < 2 ^ 64)%Z -> (0 <= nb < 2 ^ 31)%Z ->
    store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 s -> getr regs 1 = ret -> getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb ->
    exists regs',
      msteps SEGS (mkst regs (0x3771c : word) m rom) (mkst regs' (0x37754 : word) (FR9 m s ret regs) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 dp /\ getr regs' 11 = Z_to_bv 64 nb
      /\ getr regs' 12 = Z_to_bv 64 18446744071562067995 /\ getr regs' 13 = Z_to_bv 64 (nb + 18446744071562067968)
      /\ regs_agree (fun r => In r [2; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A0 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_A1 : forall regs m (nb : Z),
    (28 <= nb < 2 ^ 31)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    exists regs', msteps SEGS (mkst regs (0x37754 : word) m rom) (mkst regs' (0x377b4 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A1 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_A2 : forall regs m (nb : Z),
    (0 <= nb < 28)%Z -> getr regs 12 = Z_to_bv 64 18446744071562067995 -> getr regs 13 = Z_to_bv 64 (nb + 18446744071562067968) ->
    getr regs 11 = Z_to_bv 64 nb ->
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs',
      msteps SEGS (mkst regs (0x37754 : word) m rom) (mkst regs' (0x17e28 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x115a1 /\ getr regs' 11 = Z_to_bv 64 0x11227 /\ getr regs' 12 = Z_to_bv 64 nb /\ getr regs' 1 = Z_to_bv 64 0x37788
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_A2 fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_B : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (dp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    u b0 = 115%Z -> u b1 = 112%Z -> u b2 = 105%Z -> u b3 = 120%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x377b4 : word) m rom) (mkst regs' (0x3784c : word) m rom)
      /\ getr regs' 12 = Z_to_bv 64 (dp + 20) /\ getr regs' 13 = Z_to_bv 64 0
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_B fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_Bbad : forall regs m (dp : Z) (b0 b1 b2 b3 : byte),
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 dp) 1 = Some [b0] -> rdn SEGS m (Z_to_bv 64 (dp + 1)) 1 = Some [b1] ->
    rdn SEGS m (Z_to_bv 64 (dp + 2)) 1 = Some [b2] -> rdn SEGS m (Z_to_bv 64 (dp + 3)) 1 = Some [b3] ->
    ~ (u b0 = 115 /\ u b1 = 112 /\ u b2 = 105 /\ u b3 = 120)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x377b4 : word) m rom) (mkst regs' (0x37888 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Bbad fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_C : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x3784c : word) m rom) (mkst regs' (0x378dc : word) m rom)
      /\ getr regs' 9 = Z_to_bv 64 wr /\ getr regs' 13 = Z_to_bv 64 18446744073708551615
      /\ regs_agree (fun r => In r [9; 13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_C fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_Cbad : forall regs m (dp wr : Z) bs4,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4)) 4 = Some bs4 -> bytes_le_to_Z bs4 = wr -> (0 <= wr < 2 ^ 32)%Z -> ~ (1 <= wr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x3784c : word) m rom) (mkst regs' (0x37860 : word) m rom)
      /\ regs_agree (fun r => In r [9; 13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Cbad fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_D : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 13 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x378dc : word) m rom) (mkst regs' (0x37910 : word) m rom)
      /\ getr regs' 18 = Z_to_bv 64 hr /\ regs_agree (fun r => In r [18; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_D fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_Dbad : forall regs m (dp hr : Z) bs8,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 8)) 4 = Some bs8 -> bytes_le_to_Z bs8 = hr -> (0 <= hr < 2 ^ 32)%Z -> ~ (1 <= hr <= 1000000)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 13 = Z_to_bv 64 18446744073708551615 ->
    exists regs', msteps SEGS (mkst regs (0x378dc : word) m rom) (mkst regs' (0x378e8 : word) m rom)
      /\ regs_agree (fun r => In r [18; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Dbad fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_E : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (wr * hr <= 400000000)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x37910 : word) m rom) (mkst regs' (0x37948 : word) m rom)
      /\ regs_agree (fun r => In r [13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_E fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_Ebad : forall regs m (wr hr : Z),
    (1 <= wr <= 1000000)%Z -> (1 <= hr <= 1000000)%Z -> (400000000 < wr * hr)%Z ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x37910 : word) m rom) (mkst regs' (0x37920 : word) m rom)
      /\ regs_agree (fun r => In r [13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_Ebad fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_F : forall regs m (dp nb ncr q dr wr hr : Z) bs20 bs12,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr <= 256)%Z -> (ncr + 7 < q)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 12)) 4 = Some bs12 -> bytes_le_to_Z bs12 = dr -> (0 <= dr < 2 ^ 32)%Z ->
    (0 <= wr < 2 ^ 64)%Z -> (0 <= hr < 2 ^ 64)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 12 = Z_to_bv 64 (dp + 20) ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x37948 : word) m rom) (mkst regs' (0x194bc : word) m rom)
      /\ getr regs' 22 = Z_to_bv 64 ncr /\ getr regs' 20 = Z_to_bv 64 nb /\ getr regs' 23 = Z_to_bv 64 dp
      /\ getr regs' 19 = Z_to_bv 64 (zx (sw32 dr))
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 (zx (sw32 dr)) /\ getr regs' 1 = Z_to_bv 64 0x3797c
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 19; 20; 22; 23]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_F fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_Fbad : forall regs m (dp nb ncr q : Z) bs20,
    (1 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z -> (28 <= nb < 2 ^ 31)%Z -> q = (nb / 4)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 20)) 4 = Some bs20 -> bytes_le_to_Z bs20 = ncr -> (0 <= ncr < 2 ^ 32)%Z -> ~ (ncr <= 256 /\ ncr + 7 < q)%Z ->
    getr regs 10 = Z_to_bv 64 dp -> getr regs 11 = Z_to_bv 64 nb -> getr regs 12 = Z_to_bv 64 (dp + 20) ->
    exists regs', msteps SEGS (mkst regs (0x37948 : word) m rom) (mkst regs' (0x37a58 : word) m rom)
      /\ regs_agree (fun r => In r [12; 13; 22]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_Fbad fx v2_reloc v2_code_vl rom). Qed.

Definition et_leaves : list (Z * Z) :=
    [(0x37888, 0x115c4); (0x37860, 0x11f8e); (0x378e8, 0x105b3); (0x37920, 0x10413); (0x37a58, 0x117ba); (0x37a80, 0x10bb4)]%Z.
Lemma pd_ET : forall pc msg regs m,
    In (pc, msg) et_leaves ->
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x378ac : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x11227
      /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_ET fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Definition ej_leaves : list (Z * Z) := [(0x37ae0, 0x119a6); (0x37b18, 0x124ff); (0x37ba4, 0x1085d)]%Z.
Lemma pd_EJ : forall pc msg regs m,
    In (pc, msg) ej_leaves ->
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    exists regs', msteps SEGS (mkst regs (Z_to_bv 64 pc) m rom) (mkst regs' (0x17ec4 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 msg /\ getr regs' 11 = Z_to_bv 64 0x11227 /\ getr regs' 12 = Z_to_bv 64 0 /\ getr regs' 1 = Z_to_bv 64 0x37bd0
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_EJ fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Definition pd_cells (m : word -> option byte) (s : Z) (ret : word) (sv : nat -> word) : Prop :=
    rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (word_to_le_bytes 8 ret) /\
    rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (word_to_le_bytes 8 (sv 8%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (word_to_le_bytes 8 (sv 9%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (word_to_le_bytes 8 (sv 18%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (word_to_le_bytes 8 (sv 19%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (word_to_le_bytes 8 (sv 20%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (word_to_le_bytes 8 (sv 21%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (word_to_le_bytes 8 (sv 22%nat)) /\
    rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (word_to_le_bytes 8 (sv 23%nat)).
Lemma pd_X50 : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x378ac : word) m rom) (mkst regs' (0x17ec4 : word) m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret /\ getr regs' 12 = Z_to_bv 64 0
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 12; 18; 19; 20; 21; 22; 23]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_X50 fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_RET : forall regs m (s : Z) (ret : word) (sv : nat -> word),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> ret_ok ret -> pd_cells m s ret sv -> getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x37bd8 : word) m rom) (mkst regs' ret m rom)
      /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = ret
      /\ getr regs' 8 = sv 8%nat /\ getr regs' 9 = sv 9%nat /\ getr regs' 18 = sv 18%nat /\ getr regs' 19 = sv 19%nat
      /\ getr regs' 20 = sv 20%nat /\ getr regs' 21 = sv 21%nat /\ getr regs' 22 = sv 22%nat /\ getr regs' 23 = sv 23%nat
      /\ regs_agree (fun r => In r [1; 2; 8; 9; 18; 19; 20; 21; 22; 23]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_RET fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_R0 : forall regs m,
    exists regs', msteps SEGS (mkst regs (0x37bd4 : word) m rom) (mkst regs' (0x37bd8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0 /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_R0 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_J34 : forall regs m, exists regs', msteps SEGS (mkst regs (0x37788 : word) m rom) (mkst regs' (0x37bd4 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J34 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_J88 : forall regs m, exists regs', msteps SEGS (mkst regs (0x37adc : word) m rom) (mkst regs' (0x37bd4 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J88 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_J7c : forall regs m, exists regs', msteps SEGS (mkst regs (0x37bd0 : word) m rom) (mkst regs' (0x37bd8 : word) m rom) /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserA.pd_J7c fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_G0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x3797c : word) m rom)
                              (mkst regs' (0x37a80 : word) (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_G0 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_G : forall regs m (s dp nb nc pix1 wpl hr ir : Z) (v1 : pixv) bsi,
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    PIXat m pix1 v1 -> (4096 <= pix1)%Z -> (pix1 + 64 <= s - 96)%Z -> (pix1 mod 8 = 0)%Z -> p_wpl v1 = wpl ->
    (1 <= hr <= 1000000)%Z -> (0 <= wpl)%Z -> (4 * (wpl * hr) <= 67108864)%Z ->
    (0 <= nc <= 256)%Z -> (28 <= nb < 2 ^ 31)%Z -> (4 * nc + 32 <= nb)%Z -> (1 <= dp)%Z -> (dp + nb <= s - 96)%Z -> (dp mod 4 = 0)%Z ->
    rdn SEGS m (Z_to_bv 64 (dp + 4 * nc + 24)) 4 = Some bsi -> bytes_le_to_Z bsi = ir -> (0 <= ir < 2 ^ 32)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pix1 -> getr regs 22 = Z_to_bv 64 nc -> getr regs 20 = Z_to_bv 64 nb ->
    getr regs 23 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 hr ->
    exists regs', msteps SEGS (mkst regs (0x3797c : word) m rom)
                              (mkst regs' (0x1982c : word) (wbytes m (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (Z_to_bv 64 pix1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 10 = Z_to_bv 64 (s - 88) /\ getr regs' 1 = Z_to_bv 64 0x379d0
      /\ getr regs' 20 = Z_to_bv 64 (zx (sw32 ir))
      /\ getr regs' 8 = Z_to_bv 64 (4 * (wpl * hr)) /\ getr regs' 21 = Z_to_bv 64 (nb - 4 * nc - 28)
      /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 13; 20; 21]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_G fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_H : forall regs m (sz wr hr d : Z),
    (0 <= sz < 2 ^ 32)%Z ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 sz -> getr regs 20 = Z_to_bv 64 sz ->
    getr regs 9 = Z_to_bv 64 wr -> getr regs 18 = Z_to_bv 64 hr -> getr regs 19 = Z_to_bv 64 d ->
    exists regs', msteps SEGS (mkst regs (0x379d0 : word) m rom) (mkst regs' (0x192d0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 wr /\ getr regs' 11 = Z_to_bv 64 hr /\ getr regs' 12 = Z_to_bv 64 d /\ getr regs' 1 = Z_to_bv 64 0x379e8
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_H fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_Hbad : forall regs m (sz msz isz : Z),
    (0 <= sz < 2 ^ 32)%Z -> (0 <= msz < 2 ^ 32)%Z -> (0 <= isz < 2 ^ 64)%Z -> (sz <> msz \/ sz <> isz) ->
    rdn SEGS m (Z_to_bv 64 0x44e98) 8 = Some (Z_to_le_bytes 8 0x45f08) -> rdn SEGS m (Z_to_bv 64 0x45f08) 4 = Some (Z_to_le_bytes 4 3) ->
    getr regs 8 = Z_to_bv 64 sz -> getr regs 21 = Z_to_bv 64 msz -> getr regs 20 = Z_to_bv 64 isz ->
    exists regs', msteps SEGS (mkst regs (0x379d0 : word) m rom) (mkst regs' (0x17e28 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 0x10e9c /\ getr regs' 11 = Z_to_bv 64 0x11227 /\ getr regs' 1 = Z_to_bv 64 0x37adc
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_Hbad fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_I0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x379e8 : word) m rom)
                              (mkst regs' (0x37ae0 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 0))) rom)
      /\ regs_agree (fun r => False) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_I0 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_I1 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> (1 <= pixd < 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x379e8 : word) m rom)
                              (mkst regs' (0x37b44 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 18 = Z_to_bv 64 0 /\ getr regs' 10 = Z_to_bv 64 pixd
      /\ regs_agree (fun r => In r [9; 18]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_I1 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_I2 : forall regs m (s pixd dp nc : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> (1 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    (0 <= dp)%Z -> (dp + 28 <= 2 ^ 64)%Z ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 pixd -> getr regs 22 = Z_to_bv 64 nc -> getr regs 23 = Z_to_bv 64 dp ->
    exists regs', msteps SEGS (mkst regs (0x379e8 : word) m rom)
                              (mkst regs' (0x1e8a4 : word) (wbytes m (Z_to_bv 64 (s - 96)) (word_to_le_bytes 8 (Z_to_bv 64 pixd))) rom)
      /\ getr regs' 10 = Z_to_bv 64 (dp + 24) /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 12 = Z_to_bv 64 nc /\ getr regs' 1 = Z_to_bv 64 0x37a10
      /\ getr regs' 18 = Z_to_bv 64 nc
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_I2 fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_J0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x37a10 : word) m rom) (mkst regs' (0x1982c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x37b18 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_J0 fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_J1 : forall regs m (s cm pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (1 <= cm < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x37a10 : word) m rom) (mkst regs' (0x19fc0 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ getr regs' 11 = Z_to_bv 64 cm /\ getr regs' 9 = Z_to_bv 64 cm /\ getr regs' 1 = Z_to_bv 64 0x37a24
      /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_J1 fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_K : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 10 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x37a24 : word) m rom) (mkst regs' (0x37b44 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_K fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_GD : forall regs m (pixd dp nc sz : Z) (v : pixv),
    PIXat m pixd v -> (4096 <= pixd)%Z -> (pixd mod 8 = 0)%Z -> (0 <= nc <= 256)%Z -> (0 <= dp)%Z -> (dp + 4 * nc + 28 < 2 ^ 64)%Z ->
    (dp mod 4 = 0)%Z -> (p_data v mod 4 = 0)%Z ->
    getr regs 10 = Z_to_bv 64 pixd -> getr regs 23 = Z_to_bv 64 dp -> getr regs 18 = Z_to_bv 64 nc -> getr regs 8 = Z_to_bv 64 sz ->
    exists regs', msteps SEGS (mkst regs (0x37b44 : word) m rom) (mkst regs' (0x4347c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (p_data v) /\ getr regs' 11 = Z_to_bv 64 (dp + 4 * nc + 28) /\ getr regs' 12 = Z_to_bv 64 sz /\ getr regs' 1 = Z_to_bv 64 0x37b78
      /\ getr regs' 18 = Z_to_bv 64 (4 * nc)
      /\ regs_agree (fun r => In r [1; 10; 11; 12; 18]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_GD fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_L0 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 22 = Z_to_bv 64 0 ->
    exists regs', msteps SEGS (mkst regs (0x37b78 : word) m rom) (mkst regs' (0x37bd8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_L0 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_L1 : forall regs m (s pixd nc cm : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z -> (1 <= nc <= 256)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) -> getr regs 22 = Z_to_bv 64 nc -> getr regs 9 = Z_to_bv 64 cm ->
    exists regs', msteps SEGS (mkst regs (0x37b78 : word) m rom) (mkst regs' (0x1d734 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 cm /\ getr regs' 11 = Z_to_bv 64 pixd /\ getr regs' 12 = Z_to_bv 64 (s - 76) /\ getr regs' 1 = Z_to_bv 64 0x37b8c
      /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_L1 fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

Lemma pd_M1 : forall regs m (s pixd : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z -> (0 <= pixd < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 1) ->
    rdn SEGS m (Z_to_bv 64 (s - 96)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 pixd)) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x37b8c : word) m rom) (mkst regs' (0x37bd8 : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 pixd /\ regs_agree (fun r => In r [10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_M1 fx v2_reloc v2_code_vl rom). Qed.

Lemma pd_M0 : forall regs m (s : Z),
    (96 <= s)%Z -> (s < 2 ^ 64)%Z ->
    rdn SEGS m (Z_to_bv 64 (s - 76)) 4 = Some (Z_to_le_bytes 4 0) ->
    getr regs 2 = Z_to_bv 64 (s - 96) ->
    exists regs', msteps SEGS (mkst regs (0x37b8c : word) m rom) (mkst regs' (0x1982c : word) m rom)
      /\ getr regs' 10 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x37ba4 /\ regs_agree (fun r => In r [1; 10]%list) regs regs'.
Proof. rl_tail (@LeptDeserB.pd_M0 fx v2_reloc v2_code_vl v2_sites_vl rom). Qed.

End Segs.

End DeserA.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).      (* [comment removed for export] *)
