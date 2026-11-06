(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.leptonica.grayquant_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptStructs LeptExec LeptExecX DitherLib DitherLoop LeptCmapArr.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.O15 Require Import O15_code_gqR_cmaparr.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Plain.M.loaded_segments.

Section Segs.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Definition PTAF (m : word -> option byte) (s q : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
    (Z_to_bv 64 (s - 8)) (word_to_le_bytes 8 (getr regs 1)))
    (Z_to_bv 64 (s - 16)) (word_to_le_bytes 8 (getr regs 8)))
    (Z_to_bv 64 (s - 24)) (word_to_le_bytes 8 (getr regs 9)))
    (Z_to_bv 64 (s - 32)) (word_to_le_bytes 8 (getr regs 18)))
    (Z_to_bv 64 (s - 40)) (word_to_le_bytes 8 (getr regs 19)))
    (Z_to_bv 64 (s - 48)) (word_to_le_bytes 8 (getr regs 20)))
    (Z_to_bv 64 (s - 56)) (word_to_le_bytes 8 (getr regs 21)))
    (Z_to_bv 64 (s - 64)) (word_to_le_bytes 8 (getr regs 22)))
    (Z_to_bv 64 (s - 72)) (word_to_le_bytes 8 (getr regs 23)))
    (Z_to_bv 64 (s - 80)) (word_to_le_bytes 8 (getr regs 24)))
    (Z_to_bv 64 (q + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (q + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (q + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 q) (word_to_le_bytes 8 (Z_to_bv 64 0)).

(* [comment removed for export] *)
Lemma pta_A : forall (fx : FPState) regs m (s q cm n : Z),
  (80 <= s)%Z -> (s <= q)%Z -> (q + 32 < 2 ^ 63)%Z -> (1 <= cm < 2 ^ 63)%Z -> (0 <= n < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 80)) 80 = true -> store_ok SEGS m (Z_to_bv 64 q) 32 = true ->
  rdn SEGS m (Z_to_bv 64 (cm + 16)) 4 = Some (Z_to_le_bytes 4 n) ->
  (cm + 24 <= s - 80 \/ q + 32 <= cm)%Z ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 (q + 24) -> getr regs 12 = Z_to_bv 64 (q + 16) ->
  getr regs 13 = Z_to_bv 64 (q + 8) -> getr regs 14 = Z_to_bv 64 q ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x189f0) m rom) (@mkst fx regs' (Z_to_bv 64 0x20ea0) (PTAF m s q regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 80) /\ getr regs' 1 = Z_to_bv 64 0x18a64 /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 4
    /\ getr regs' 8 = Z_to_bv 64 q /\ getr regs' 20 = Z_to_bv 64 n /\ getr regs' 21 = Z_to_bv 64 cm
    /\ getr regs' 22 = Z_to_bv 64 (q + 24) /\ getr regs' 23 = Z_to_bv 64 (q + 8) /\ getr regs' 24 = Z_to_bv 64 (q + 16)
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 20; 21; 22; 23; 24]%list) regs regs'.
Proof.
  intros fx regs m s q cm n Hs Hq Hq63 Hcm Hn SOK SOKq Cn AP H2 H10 H11 H12 H13 H14.
  ex_entry regs [s; q; cm; n] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; q; cm; n]) m
                 [KRange (EVar 32) 80 (2 ^ 63); KRange (EVar 33) 80 (2 ^ 63); KRange (EVar 34) 1 (2 ^ 63); KRange (EVar 35) 0 (2 ^ 31 - 1);
                  KWr (SA (EVar 32) (-80)) 80; KWr (SA (EVar 33) 0) 32; KWord (SA (EVar 34) 16) 4 (EVar 35)]).
  { ex_know regs. }
  ex_run 200%nat [0x20ea0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold PTAF; ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.


(* [comment removed for export] *)
Lemma pta_B1 : forall (fx : FPState) regs m (n rm : Z),
  (0 <= n < 2 ^ 31)%Z -> (0 <= rm < 2 ^ 63)%Z ->
  getr regs 10 = Z_to_bv 64 rm -> getr regs 20 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18a64) m rom) (@mkst fx regs' (Z_to_bv 64 0x20ea0) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x18a74 /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 9 = Z_to_bv 64 rm
    /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m n rm Hn Hrm H10 H20.
  ex_entry regs [n; rm] HR.
  assert (HK : know_ok SEGS (ex_env regs [n; rm]) m []) by (ex_know regs).
  ex_run 50%nat [0x20ea0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma pta_B2 : forall (fx : FPState) regs m (n gm : Z),
  (0 <= n < 2 ^ 31)%Z -> (0 <= gm < 2 ^ 63)%Z ->
  getr regs 10 = Z_to_bv 64 gm -> getr regs 20 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18a74) m rom) (@mkst fx regs' (Z_to_bv 64 0x20ea0) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x18a84 /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 18 = Z_to_bv 64 gm
    /\ regs_agree (fun r => In r [1; 10; 11; 18]%list) regs regs'.
Proof.
  intros fx regs m n gm Hn Hgm H10 H20.
  ex_entry regs [n; gm] HR.
  assert (HK : know_ok SEGS (ex_env regs [n; gm]) m []) by (ex_know regs).
  ex_run 50%nat [0x20ea0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Definition PTA3 (m : word -> option byte) (q rm gm bm : Z) : word -> option byte :=
  wbytes (wbytes (wbytes m
    (Z_to_bv 64 (q + 24)) (word_to_le_bytes 8 (Z_to_bv 64 rm)))
    (Z_to_bv 64 (q + 16)) (word_to_le_bytes 8 (Z_to_bv 64 gm)))
    (Z_to_bv 64 (q + 8)) (word_to_le_bytes 8 (Z_to_bv 64 bm)).

Lemma pta_B3 : forall (fx : FPState) regs m (q n rm gm bm : Z),
  (80 <= q)%Z -> (q + 32 < 2 ^ 63)%Z -> (0 <= n < 2 ^ 31)%Z -> (0 <= rm < 2 ^ 63)%Z -> (0 <= gm < 2 ^ 63)%Z -> (0 <= bm < 2 ^ 63)%Z ->
  store_ok SEGS m (Z_to_bv 64 q) 32 = true ->
  getr regs 10 = Z_to_bv 64 bm -> getr regs 9 = Z_to_bv 64 rm -> getr regs 18 = Z_to_bv 64 gm -> getr regs 20 = Z_to_bv 64 n ->
  getr regs 8 = Z_to_bv 64 q -> getr regs 22 = Z_to_bv 64 (q + 24) -> getr regs 23 = Z_to_bv 64 (q + 8) -> getr regs 24 = Z_to_bv 64 (q + 16) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18a84) m rom) (@mkst fx regs' (Z_to_bv 64 0x20ea0) (PTA3 m q rm gm bm) rom)
    /\ getr regs' 1 = Z_to_bv 64 0x18aa4 /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 19 = Z_to_bv 64 bm
    /\ regs_agree (fun r => In r [1; 10; 11; 19]%list) regs regs'.
Proof.
  intros fx regs m q n rm gm bm Hq Hq63 Hn Hrm Hgm Hbm SOKq H10 H9 H18 H20 H8 H22 H23 H24.
  ex_entry regs [q; n; rm; gm; bm] HR.
  assert (HK : know_ok SEGS (ex_env regs [q; n; rm; gm; bm]) m [KRange (EVar 32) 80 (2 ^ 63); KWr (SA (EVar 32) 0) 32]) by (ex_know regs).
  ex_run 50%nat [0x20ea0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold PTA3; ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma pta_B4 : forall (fx : FPState) regs m (q cm n arr bm am : Z),
  (80 <= q)%Z -> (q + 32 < 2 ^ 63)%Z -> (1 <= n <= 256)%Z -> (1 <= cm < 2 ^ 63)%Z -> (0 <= arr < 2 ^ 63)%Z -> (0 <= bm < 2 ^ 62)%Z -> (0 <= am < 2 ^ 63)%Z ->
  store_ok SEGS m (Z_to_bv 64 q) 8 = true ->
  rdn SEGS m (Z_to_bv 64 cm) 8 = Some (Z_to_le_bytes 8 arr) -> (cm + 8 <= q \/ q + 8 <= cm)%Z ->
  getr regs 10 = Z_to_bv 64 am -> getr regs 8 = Z_to_bv 64 q -> getr regs 20 = Z_to_bv 64 n -> getr regs 21 = Z_to_bv 64 cm -> getr regs 19 = Z_to_bv 64 bm ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18aa4) m rom)
                (@mkst fx regs' (Z_to_bv 64 0x18b64) (wbytes m (Z_to_bv 64 q) (word_to_le_bytes 8 (Z_to_bv 64 am))) rom)
    /\ getr regs' 10 = Z_to_bv 64 am /\ getr regs' 11 = Z_to_bv 64 (arr + 3) /\ getr regs' 12 = Z_to_bv 64 (bm + 4 * n)
    /\ regs_agree (fun r => In r [10; 11; 12]%list) regs regs'.
Proof.
  intros fx regs m q cm n arr bm am Hq Hq63 Hn Hcm Harr Hbm Ham SOKq Carr AP H10 H8 H20 H21 H19.
  ex_entry regs [q; cm; n; arr; bm; am] HR.
  assert (HK : know_ok SEGS (ex_env regs [q; cm; n; arr; bm; am]) m
                 [KRange (EVar 32) 80 (2 ^ 63); KRange (EVar 34) 1 256; KWr (SA (EVar 32) 0) 8; KWord (SA (EVar 33) 0) 8 (EVar 35);
                  KDisj (SA (EVar 33) 0) 8 (SA (EVar 32) 0) 8]) by (ex_know regs).
  ex_run 50%nat [0x18b64%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma pta_L : forall (last : bool) (fx : FPState) regs m (q p r1 g1 b1 a1 bend vr vg vb va : Z),
  (1 <= q < 2 ^ 63)%Z -> (0 <= p)%Z -> (p + 4 < 2 ^ 63)%Z -> (0 <= r1)%Z -> (r1 + 4 < 2 ^ 63)%Z -> (0 <= g1)%Z -> (g1 + 4 < 2 ^ 63)%Z ->
  (0 <= b1)%Z -> (b1 + 4 < 2 ^ 63)%Z -> (0 <= a1)%Z -> (a1 + 4 < 2 ^ 63)%Z -> (0 <= bend < 2 ^ 63)%Z ->
  (0 <= vr <= 255)%Z -> (0 <= vg <= 255)%Z -> (0 <= vb <= 255)%Z -> (0 <= va <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (p + 2)) 1 = Some (Z_to_le_bytes 1 vr) -> rdn SEGS m (Z_to_bv 64 (p + 1)) 1 = Some (Z_to_le_bytes 1 vg) ->
  rdn SEGS m (Z_to_bv 64 (p + 0)) 1 = Some (Z_to_le_bytes 1 vb) -> rdn SEGS m (Z_to_bv 64 (p + 3)) 1 = Some (Z_to_le_bytes 1 va) ->
  store_ok SEGS m (Z_to_bv 64 r1) 4 = true -> store_ok SEGS m (Z_to_bv 64 g1) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 b1) 4 = true -> store_ok SEGS m (Z_to_bv 64 a1) 4 = true ->
  (p + 4 <= r1 \/ r1 + 4 <= p)%Z -> (p + 4 <= g1 \/ g1 + 4 <= p)%Z -> (p + 4 <= b1 \/ b1 + 4 <= p)%Z ->
  (if last then b1 + 4 = bend else b1 + 4 <> bend)%Z ->
  getr regs 8 = Z_to_bv 64 q -> getr regs 11 = Z_to_bv 64 (p + 3) -> getr regs 9 = Z_to_bv 64 r1 -> getr regs 18 = Z_to_bv 64 g1 ->
  getr regs 19 = Z_to_bv 64 b1 -> getr regs 10 = Z_to_bv 64 a1 -> getr regs 12 = Z_to_bv 64 bend ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18b64) m rom)
                (@mkst fx regs' (Z_to_bv 64 (if last then 0x18b8c else 0x18b64)) (PTAL m r1 g1 b1 a1 vr vg vb va) rom)
    /\ getr regs' 11 = Z_to_bv 64 (p + 4 + 3) /\ getr regs' 9 = Z_to_bv 64 (r1 + 4) /\ getr regs' 18 = Z_to_bv 64 (g1 + 4)
    /\ getr regs' 19 = Z_to_bv 64 (b1 + 4) /\ getr regs' 10 = Z_to_bv 64 (a1 + 4)
    /\ regs_agree (fun r => In r [9; 10; 11; 13; 14; 15; 18; 19]%list) regs regs'.
Proof.
  intros last fx regs m q p r1 g1 b1 a1 bend vr vg vb va Hq Hp Hp63 Hr1 Hr163 Hg1 Hg163 Hb1 Hb163 Ha1 Ha163 Hbend Hvr Hvg Hvb Hva
         Cr Cg Cb Ca SOKr SOKg SOKb SOKa APr APg APb Hlast H8 H11 H9 H18 H19 H10 H12.
  ex_entry regs [q; p; r1; g1; b1; a1; bend; vr; vg; vb; va] HR.
  assert (HK : know_ok SEGS (ex_env regs [q; p; r1; g1; b1; a1; bend; vr; vg; vb; va]) m
                 [KRange (EVar 32) 1 (2 ^ 63); KRange (EVar 39) 0 255; KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255;
                  KWord (SA (EVar 33) 2) 1 (EVar 39); KWord (SA (EVar 33) 1) 1 (EVar 40); KWord (SA (EVar 33) 0) 1 (EVar 41); KWord (SA (EVar 33) 3) 1 (EVar 42);
                  KWr (SA (EVar 34) 0) 4; KWr (SA (EVar 35) 0) 4; KWr (SA (EVar 36) 0) 4; KWr (SA (EVar 37) 0) 4;
                  KDisj (SA (EVar 33) 0) 4 (SA (EVar 34) 0) 4; KDisj (SA (EVar 33) 0) 4 (SA (EVar 35) 0) 4; KDisj (SA (EVar 33) 0) 4 (SA (EVar 36) 0) 4]) by (ex_know regs).
  destruct last.
  - ex_run 50%nat [0x18b8c%Z; 0x18b64%Z] (SCR [true] [] []) HR HK R' HR' Hms.
    exists R'. split; [unfold PTAL; ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 50%nat [0x18b8c%Z; 0x18b64%Z] (SCR [false] [] []) HR HK R' HR' Hms.
    exists R'. split; [unfold PTAL; ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma pta_ret : forall (fx : FPState) regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18bbc) m rom) (@mkst fx regs ret m rom).
Proof.
  intros fx regs m ret Hret H1. replace (Z_to_bv 64 0x18bbc) with (0x18bbc : word) by (apply bv_eq; reflexivity).
  stepret F_18b64 D_18b64 ret ltac:(exact H1). apply mst_refl.
Qed.

Lemma pta_E : forall (fx : FPState) regs m (s z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 : Z),
  (80 <= s < 2 ^ 63)%Z ->
  (0 <= z1 < 2 ^ 64)%Z -> (0 <= z8 < 2 ^ 64)%Z -> (0 <= z9 < 2 ^ 64)%Z -> (0 <= z18 < 2 ^ 64)%Z -> (0 <= z19 < 2 ^ 64)%Z -> (0 <= z20 < 2 ^ 64)%Z ->
  (0 <= z21 < 2 ^ 64)%Z -> (0 <= z22 < 2 ^ 64)%Z -> (0 <= z23 < 2 ^ 64)%Z -> (0 <= z24 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (Z_to_le_bytes 8 z1) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (Z_to_le_bytes 8 z8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (Z_to_le_bytes 8 z9) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 z18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 z19) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 z20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 z21) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 z22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 z23) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 z24) ->
  getr regs 2 = Z_to_bv 64 (s - 80) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18b8c) m rom) (@mkst fx regs' (Z_to_bv 64 0x18bbc) m rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = Z_to_bv 64 z1 /\ getr regs' 8 = Z_to_bv 64 z8
    /\ getr regs' 9 = Z_to_bv 64 z9 /\ getr regs' 18 = Z_to_bv 64 z18 /\ getr regs' 19 = Z_to_bv 64 z19 /\ getr regs' 20 = Z_to_bv 64 z20
    /\ getr regs' 21 = Z_to_bv 64 z21 /\ getr regs' 22 = Z_to_bv 64 z22 /\ getr regs' 23 = Z_to_bv 64 z23 /\ getr regs' 24 = Z_to_bv 64 z24
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
Proof.
  intros fx regs m s z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 Hs R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 H2.
  ex_entry regs [s; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24]) m
                 [KRange (EVar 32) 80 (2 ^ 63);
                  KWord (SA (EVar 32) (-8)) 8 (EVar 33); KWord (SA (EVar 32) (-16)) 8 (EVar 34); KWord (SA (EVar 32) (-24)) 8 (EVar 35);
                  KWord (SA (EVar 32) (-32)) 8 (EVar 36); KWord (SA (EVar 32) (-40)) 8 (EVar 37); KWord (SA (EVar 32) (-48)) 8 (EVar 38);
                  KWord (SA (EVar 32) (-56)) 8 (EVar 39); KWord (SA (EVar 32) (-64)) 8 (EVar 40); KWord (SA (EVar 32) (-72)) 8 (EVar 41);
                  KWord (SA (EVar 32) (-80)) 8 (EVar 42)]) by (ex_know regs).
  ex_run 50%nat [0x18bbc%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma pta_loop : forall (k : nat) (fx : FPState) regs (M0 M : word -> option byte) (q arr rm gm bm am n i : Z),
  Z.of_nat k = (n - i)%Z -> (0 <= i < n)%Z -> (1 <= q < 2 ^ 63)%Z -> (0 <= arr)%Z -> (arr + 4 * n < 2 ^ 63)%Z ->
  arrs4 rm gm bm am n ->
  (arr + 4 * n <= rm \/ rm + 4 * n <= arr)%Z -> (arr + 4 * n <= gm \/ gm + 4 * n <= arr)%Z ->
  (arr + 4 * n <= bm \/ bm + 4 * n <= arr)%Z -> (arr + 4 * n <= am \/ am + 4 * n <= arr)%Z ->
  (exists bs, rdn SEGS M0 (Z_to_bv 64 arr) (Z.to_nat (4 * n)) = Some bs) ->
  regions_ok SEGS M0 (R4 rm gm bm am n) ->
  rinv (R4 rm gm bm am n) M0 M -> arr255 SEGS M rm n -> arr255 SEGS M gm n -> arr255 SEGS M bm n ->
  getr regs 8 = Z_to_bv 64 q -> getr regs 11 = Z_to_bv 64 (arr + 4 * i + 3) -> getr regs 9 = Z_to_bv 64 (rm + 4 * i) ->
  getr regs 18 = Z_to_bv 64 (gm + 4 * i) -> getr regs 19 = Z_to_bv 64 (bm + 4 * i) -> getr regs 10 = Z_to_bv 64 (am + 4 * i) ->
  getr regs 12 = Z_to_bv 64 (bm + 4 * n) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x18b64) M rom) (@mkst fx regs' (Z_to_bv 64 0x18b8c) M' rom)
    /\ rinv (R4 rm gm bm am n) M0 M' /\ arr255 SEGS M' rm n /\ arr255 SEGS M' gm n /\ arr255 SEGS M' bm n
    /\ regs_agree (fun r => In r [9; 10; 11; 13; 14; 15; 18; 19]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros fx regs M0 M q arr rm gm bm am n i Hk Hi Hq Harr Harr63 G APr APg APb APa (bs & RD) RO RI Ar Ag Ab H8 H11 H9 H18 H19 H10 H12; [lia|].
  (* [comment removed for export] *)
  assert (RG : (0 <= rm /\ rm + 4 * n < 2 ^ 63 /\ 0 <= gm /\ gm + 4 * n < 2 ^ 63 /\ 0 <= bm /\ bm + 4 * n < 2 ^ 63 /\ 0 <= am /\ am + 4 * n < 2 ^ 63)%Z)
    by (clear - G; destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _); repeat split; assumption).
  assert (APc : forall b, (arr + 4 * n <= b \/ b + 4 * n <= arr)%Z -> (arr + 4 * i + 4 <= b + 4 * i \/ b + 4 * i + 4 <= arr + 4 * i)%Z)
    by (clear - Hi; intros b H; lia).
  pose proof (APc rm APr) as APr1. pose proof (APc gm APg) as APg1. pose proof (APc bm APb) as APb1.
  (* [comment removed for export] *)
  assert (RDM : rdn SEGS M (Z_to_bv 64 arr) (Z.to_nat (4 * n)) = Some bs).
  { rewrite <- RD. apply (rinv_rdn SEGS (R4 rm gm bm am n) M0 M arr _ RI); [clear - Harr; lia | rewrite Z2Nat.id by (clear - Hi; lia); clear - Harr63; lia|].
    intros r Hr. rewrite Z2Nat.id by (clear - Hi; lia). unfold R4 in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd]; [clear - APr; lia | clear - APg; lia | clear - APb; lia | clear - APa; lia]. }
  assert (BY : forall c, (0 <= c < 4)%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M (Z_to_bv 64 (arr + 4 * i + c)) 1 = Some (Z_to_le_bytes 1 v)).
  { intros c Hc.
    destruct (rdn_byte_val SEGS M arr (Z.to_nat (4 * n)) bs (4 * i + c) ltac:(clear - Harr; lia) ltac:(rewrite Z2Nat.id by (clear - Hi; lia); clear - Harr63; lia) RDM
                ltac:(rewrite Z2Nat.id by (clear - Hi; lia); clear - Hi Hc; lia)) as (v & Hv & R).
    exists v. split; [exact Hv|]. rewrite <- R. f_equal. f_equal. clear; lia. }
  destruct (BY 2%Z ltac:(clear; lia)) as (vr & Hvr & Cr). destruct (BY 1%Z ltac:(clear; lia)) as (vg & Hvg & Cg).
  destruct (BY 0%Z ltac:(clear; lia)) as (vb & Hvb & Cb). destruct (BY 3%Z ltac:(clear; lia)) as (va & Hva & Ca).
  assert (SOK : forall z, In (z, (4 * n)%Z) (R4 rm gm bm am n) -> (0 <= z)%Z -> store_ok SEGS M (Z_to_bv 64 (z + 4 * i)) 4 = true).
  { intros z Hin Hz0. destruct (RO _ Hin) as (Q0 & Q1 & Q2 & Q3). cbn [fst snd] in Q0, Q1, Q2, Q3.
    apply (reg_sok SEGS M0 M z (Z.to_nat (4 * n)) (z + 4 * i) 4 (proj1 RI) Q3 Q0); rewrite ?Z2Nat.id by (clear - Hi; lia); cbn; clear - Hi Q1 Hz0; lia. }
  assert (SOKr : store_ok SEGS M (Z_to_bv 64 (rm + 4 * i)) 4 = true) by (apply SOK; [left; reflexivity | clear - RG; lia]).
  assert (SOKg : store_ok SEGS M (Z_to_bv 64 (gm + 4 * i)) 4 = true) by (apply SOK; [right; left; reflexivity | clear - RG; lia]).
  assert (SOKb : store_ok SEGS M (Z_to_bv 64 (bm + 4 * i)) 4 = true) by (apply SOK; [right; right; left; reflexivity | clear - RG; lia]).
  assert (SOKa : store_ok SEGS M (Z_to_bv 64 (am + 4 * i)) 4 = true) by (apply SOK; [right; right; right; left; reflexivity | clear - RG; lia]).
  destruct (PTAL_inv SEGS M0 M rm gm bm am n i vr vg vb va G Hi Hvr Hvg Hvb Hva RI Ar Ag Ab) as (RI' & Ar' & Ag' & Ab').
  assert (N1 : (0 <= arr + 4 * i)%Z /\ (arr + 4 * i + 4 < 2 ^ 63)%Z /\ (0 <= rm + 4 * i)%Z /\ (rm + 4 * i + 4 < 2 ^ 63)%Z /\ (0 <= gm + 4 * i)%Z /\ (gm + 4 * i + 4 < 2 ^ 63)%Z /\
               (0 <= bm + 4 * i)%Z /\ (bm + 4 * i + 4 < 2 ^ 63)%Z /\ (0 <= am + 4 * i)%Z /\ (am + 4 * i + 4 < 2 ^ 63)%Z /\ (0 <= bm + 4 * n < 2 ^ 63)%Z)
    by (clear - RG Hi Harr Harr63; lia).
  destruct N1 as (N1 & N2 & N3 & N4 & N5 & N6 & N7 & N8 & N9 & N10 & N11).
  destruct (Z.eq_dec (i + 1) n) as [LAST|MORE].
  - destruct (pta_L true fx regs M q (arr + 4 * i) (rm + 4 * i) (gm + 4 * i) (bm + 4 * i) (am + 4 * i) (bm + 4 * n) vr vg vb va
                Hq N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 Hvr Hvg Hvb Hva Cr Cg Cb Ca SOKr SOKg SOKb SOKa APr1 APg1 APb1
                ltac:(cbn; clear - LAST; lia) H8 H11 H9 H18 H19 H10 H12)
      as (r1 & RUN & _ & _ & _ & _ & _ & AG).
    exists r1, (PTAL M (rm + 4 * i) (gm + 4 * i) (bm + 4 * i) (am + 4 * i) vr vg vb va).
    split; [exact RUN|]. split; [exact RI'|]. split; [exact Ar'|]. split; [exact Ag'|]. split; [exact Ab' | exact AG].
  - destruct (pta_L false fx regs M q (arr + 4 * i) (rm + 4 * i) (gm + 4 * i) (bm + 4 * i) (am + 4 * i) (bm + 4 * n) vr vg vb va
                Hq N1 N2 N3 N4 N5 N6 N7 N8 N9 N10 N11 Hvr Hvg Hvb Hva Cr Cg Cb Ca SOKr SOKg SOKb SOKa APr1 APg1 APb1
                ltac:(cbn; clear - MORE; lia) H8 H11 H9 H18 H19 H10 H12)
      as (r1 & RUN & F11 & F9 & F18 & F19 & F10 & AG).
    destruct (IH fx r1 M0 (PTAL M (rm + 4 * i) (gm + 4 * i) (bm + 4 * i) (am + 4 * i) vr vg vb va) q arr rm gm bm am n (i + 1)%Z
                ltac:(clear - Hk; lia) ltac:(clear - Hi MORE; lia) Hq Harr Harr63 G APr APg APb APa (ex_intro _ bs RD) RO RI' Ar' Ag' Ab')
      as (r2 & M2 & RUN2 & RI2 & Ar2 & Ag2 & Ab2 & AG2).
    + rewrite (AG 8%bv) by notin_list. exact H8.
    + rewrite F11. f_equal. clear; lia.
    + rewrite F9. f_equal. clear; lia.
    + rewrite F18. f_equal. clear; lia.
    + rewrite F19. f_equal. clear; lia.
    + rewrite F10. f_equal. clear; lia.
    + rewrite (AG 12%bv) by notin_list. exact H12.
    + exists r2, M2. split; [exact (msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact RI2|]. split; [exact Ar2|]. split; [exact Ag2|]. split; [exact Ab2|].
      intros r Hr. rewrite (AG2 r Hr). exact (AG r Hr).
Qed.

End Segs.
