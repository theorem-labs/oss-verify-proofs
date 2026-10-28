(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac WalkTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec LeptExecX DitherLib DitherLoop LeptCmapArr.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.V15 Require Import V15_code_gqR_cmaparr.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Section Segs.
Variable rom : word -> option byte.

(* [comment removed for export] *)
Definition PTAF (m : word -> option byte) (s q : Z) (regs : bvmap 5 word) : word -> option byte :=
  wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes (wbytes m
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
    (Z_to_bv 64 (s - 88)) (word_to_le_bytes 8 (getr regs 25)))
    (Z_to_bv 64 (q + 8)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (q + 16)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 (q + 24)) (word_to_le_bytes 8 (Z_to_bv 64 0)))
    (Z_to_bv 64 q) (word_to_le_bytes 8 (Z_to_bv 64 0)).

(* [comment removed for export] *)
Lemma pta_A : forall (fx : FPState) regs m (s q cm n : Z),
  (96 <= s)%Z -> (s <= q)%Z -> (q + 32 < 2 ^ 63)%Z -> (q mod 8 = 0)%Z -> (1 <= cm < 2 ^ 63)%Z -> (cm mod 8 = 0)%Z -> (0 <= n < 2 ^ 31)%Z ->
  store_ok SEGS m (Z_to_bv 64 (s - 96)) 96 = true -> store_ok SEGS m (Z_to_bv 64 q) 32 = true ->
  rdn SEGS m (Z_to_bv 64 (cm + 16)) 4 = Some (Z_to_le_bytes 4 n) ->
  (cm + 24 <= s - 96 \/ q + 32 <= cm)%Z ->
  getr regs 2 = Z_to_bv 64 s -> getr regs 10 = Z_to_bv 64 cm -> getr regs 11 = Z_to_bv 64 (q + 24) -> getr regs 12 = Z_to_bv 64 (q + 16) ->
  getr regs 13 = Z_to_bv 64 (q + 8) -> getr regs 14 = Z_to_bv 64 q ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x193f8) m rom) (@mkst fx regs' (Z_to_bv 64 0x2891c) (PTAF m s q regs) rom)
    /\ getr regs' 2 = Z_to_bv 64 (s - 96) /\ getr regs' 1 = Z_to_bv 64 0x19498 /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 4
    /\ getr regs' 8 = Z_to_bv 64 q /\ getr regs' 21 = Z_to_bv 64 n /\ getr regs' 20 = Z_to_bv 64 cm /\ getr regs' 22 = Z_to_bv 64 0
    /\ getr regs' 25 = Z_to_bv 64 (q + 24) /\ getr regs' 24 = Z_to_bv 64 (q + 16) /\ getr regs' 23 = Z_to_bv 64 (q + 8)
    /\ regs_agree (fun r => In r [1; 2; 8; 10; 11; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof.
  intros fx regs m s q cm n Hs Hq Hq63 Hq8 Hcm Hcm8 Hn SOK SOKq Cn AP H2 H10 H11 H12 H13 H14.
  ex_entry regs [s; q; cm; n] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; q; cm; n]) m
                 [KRange (EVar 32) 96 (2 ^ 63); KRange (EVar 33) 96 (2 ^ 63); KAlign (EVar 33) 8; KRange (EVar 34) 1 (2 ^ 63); KAlign (EVar 34) 8;
                  KRange (EVar 35) 0 (2 ^ 31 - 1);
                  KWr (SA (EVar 32) (-96)) 96; KWr (SA (EVar 33) 0) 32; KWord (SA (EVar 34) 16) 4 (EVar 35)]).
  { ex_know regs. }
  ex_run 200%nat [0x2891c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold PTAF; ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.
(* [comment removed for export] *)
Lemma pta_B1 : forall (fx : FPState) regs m (n rm : Z),
  (0 <= n < 2 ^ 31)%Z -> (0 <= rm < 2 ^ 63)%Z ->
  getr regs 10 = Z_to_bv 64 rm -> getr regs 21 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19498) m rom) (@mkst fx regs' (Z_to_bv 64 0x2891c) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x194a8 /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 9 = Z_to_bv 64 rm
    /\ regs_agree (fun r => In r [1; 9; 10; 11]%list) regs regs'.
Proof.
  intros fx regs m n rm Hn Hrm H10 H21.
  ex_entry regs [n; rm] HR.
  assert (HK : know_ok SEGS (ex_env regs [n; rm]) m []) by (ex_know regs).
  ex_run 50%nat [0x2891c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

Lemma pta_B2 : forall (fx : FPState) regs m (n gm : Z),
  (0 <= n < 2 ^ 31)%Z -> (0 <= gm < 2 ^ 63)%Z ->
  getr regs 10 = Z_to_bv 64 gm -> getr regs 21 = Z_to_bv 64 n ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x194a8) m rom) (@mkst fx regs' (Z_to_bv 64 0x2891c) m rom)
    /\ getr regs' 1 = Z_to_bv 64 0x194b8 /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 18 = Z_to_bv 64 gm
    /\ regs_agree (fun r => In r [1; 10; 11; 18]%list) regs regs'.
Proof.
  intros fx regs m n gm Hn Hgm H10 H21.
  ex_entry regs [n; gm] HR.
  assert (HK : know_ok SEGS (ex_env regs [n; gm]) m []) by (ex_know regs).
  ex_run 50%nat [0x2891c%Z] (SCR [] [] []) HR HK R' HR' Hms.
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
  (96 <= q)%Z -> (q + 32 < 2 ^ 63)%Z -> (0 <= n < 2 ^ 31)%Z -> (0 <= rm < 2 ^ 63)%Z -> (0 <= gm < 2 ^ 63)%Z -> (0 <= bm < 2 ^ 63)%Z ->
  store_ok SEGS m (Z_to_bv 64 q) 32 = true ->
  getr regs 10 = Z_to_bv 64 bm -> getr regs 9 = Z_to_bv 64 rm -> getr regs 18 = Z_to_bv 64 gm -> getr regs 21 = Z_to_bv 64 n ->
  getr regs 8 = Z_to_bv 64 q -> getr regs 25 = Z_to_bv 64 (q + 24) -> getr regs 23 = Z_to_bv 64 (q + 8) -> getr regs 24 = Z_to_bv 64 (q + 16) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x194b8) m rom) (@mkst fx regs' (Z_to_bv 64 0x2891c) (PTA3 m q rm gm bm) rom)
    /\ getr regs' 1 = Z_to_bv 64 0x194d8 /\ getr regs' 10 = Z_to_bv 64 n /\ getr regs' 11 = Z_to_bv 64 4 /\ getr regs' 19 = Z_to_bv 64 bm
    /\ regs_agree (fun r => In r [1; 10; 11; 19]%list) regs regs'.
Proof.
  intros fx regs m q n rm gm bm Hq Hq63 Hn Hrm Hgm Hbm SOKq H10 H9 H18 H21 H8 H25 H23 H24.
  ex_entry regs [q; n; rm; gm; bm] HR.
  assert (HK : know_ok SEGS (ex_env regs [q; n; rm; gm; bm]) m [KRange (EVar 32) 96 (2 ^ 63); KWr (SA (EVar 32) 0) 32]) by (ex_know regs).
  ex_run 50%nat [0x2891c%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [unfold PTA3; ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma pta_B4 : forall (fx : FPState) regs m (q cm n arr rm gm bm am : Z),
  (96 <= q)%Z -> (q + 32 < 2 ^ 63)%Z -> (1 <= n <= 256)%Z -> (1 <= cm < 2 ^ 63)%Z -> (1 <= arr < 2 ^ 63)%Z ->
  (1 <= rm < 2 ^ 63)%Z -> (1 <= gm < 2 ^ 63)%Z -> (1 <= bm < 2 ^ 63)%Z -> (1 <= am < 2 ^ 63)%Z ->
  (rm mod 16 = 0)%Z -> (gm mod 16 = 0)%Z -> (bm mod 16 = 0)%Z -> (am mod 16 = 0)%Z ->
  store_ok SEGS m (Z_to_bv 64 q) 8 = true ->
  rdn SEGS m (Z_to_bv 64 cm) 8 = Some (Z_to_le_bytes 8 arr) -> (cm + 8 <= q \/ q + 8 <= cm)%Z ->
  getr regs 10 = Z_to_bv 64 am -> getr regs 8 = Z_to_bv 64 q -> getr regs 21 = Z_to_bv 64 n -> getr regs 20 = Z_to_bv 64 cm -> getr regs 22 = Z_to_bv 64 0 ->
  getr regs 9 = Z_to_bv 64 rm -> getr regs 18 = Z_to_bv 64 gm -> getr regs 19 = Z_to_bv 64 bm ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x194d8) m rom)
                (@mkst fx regs' (Z_to_bv 64 0x195d0) (wbytes m (Z_to_bv 64 q) (word_to_le_bytes 8 (Z_to_bv 64 am))) rom)
    /\ getr regs' 10 = Z_to_bv 64 am /\ getr regs' 11 = Z_to_bv 64 0 /\ getr regs' 12 = Z_to_bv 64 arr /\ getr regs' 21 = Z_to_bv 64 (4 * n)
    /\ getr regs' 13 = Z_to_bv 64 1 /\ getr regs' 14 = Z_to_bv 64 1 /\ getr regs' 15 = Z_to_bv 64 1 /\ getr regs' 16 = Z_to_bv 64 1
    /\ getr regs' 17 = Z_to_bv 64 1 /\ getr regs' 5 = Z_to_bv 64 1 /\ getr regs' 6 = Z_to_bv 64 1 /\ getr regs' 7 = Z_to_bv 64 1 /\ getr regs' 28 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 21; 28]%list) regs regs'.
Proof.
  intros fx regs m q cm n arr rm gm bm am Hq Hq63 Hn Hcm Harr Hrm Hgm Hbm Ham ALr ALg ALb ALa SOKq Carr AP H10 H8 H21 H20 H22 H9 H18 H19.
  ex_entry regs [q; cm; n; arr; rm; gm; bm; am] HR.
  assert (HK : know_ok SEGS (ex_env regs [q; cm; n; arr; rm; gm; bm; am]) m
                 [KRange (EVar 32) 96 (2 ^ 63); KRange (EVar 34) 1 256; KRange (EVar 35) 1 (2 ^ 63); KRange (EVar 36) 1 (2 ^ 63); KRange (EVar 37) 1 (2 ^ 63);
                  KRange (EVar 38) 1 (2 ^ 63); KRange (EVar 39) 1 (2 ^ 63); KAlign (EVar 36) 16; KAlign (EVar 37) 16; KAlign (EVar 38) 16; KAlign (EVar 39) 16;
                  KWr (SA (EVar 32) 0) 8; KWord (SA (EVar 33) 0) 8 (EVar 35); KDisj (SA (EVar 33) 0) 8 (SA (EVar 32) 0) 8]) by (ex_know regs).
  ex_run 80%nat [0x195d0%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext; rewrite ?zbv_snez by lia; try reflexivity; apply bv_eq; reflexivity.
Qed.

(* [comment removed for export] *)
Definition lregs (regs : bvmap 5 word) (q arr rm gm bm am n4 : Z) : Prop :=
  getr regs 8 = Z_to_bv 64 q /\ getr regs 12 = Z_to_bv 64 arr /\ getr regs 9 = Z_to_bv 64 rm /\ getr regs 18 = Z_to_bv 64 gm /\
  getr regs 19 = Z_to_bv 64 bm /\ getr regs 10 = Z_to_bv 64 am /\ getr regs 21 = Z_to_bv 64 n4 /\
  getr regs 13 = Z_to_bv 64 1 /\ getr regs 14 = Z_to_bv 64 1 /\ getr regs 15 = Z_to_bv 64 1 /\ getr regs 16 = Z_to_bv 64 1 /\
  getr regs 17 = Z_to_bv 64 1 /\ getr regs 5 = Z_to_bv 64 1 /\ getr regs 6 = Z_to_bv 64 1 /\ getr regs 7 = Z_to_bv 64 1 /\ getr regs 28 = Z_to_bv 64 1.

(* [comment removed for export] *)
Lemma pta_L : forall (last : bool) (fx : FPState) regs m (q arr rm gm bm am off n4 vr vg vb va : Z),
  (1 <= q < 2 ^ 63)%Z -> (1 <= arr)%Z -> (arr + 1024 < 2 ^ 63)%Z -> (1 <= rm)%Z -> (rm + 1024 < 2 ^ 63)%Z -> (1 <= gm)%Z -> (gm + 1024 < 2 ^ 63)%Z ->
  (1 <= bm)%Z -> (bm + 1024 < 2 ^ 63)%Z -> (1 <= am)%Z -> (am + 1024 < 2 ^ 63)%Z -> (0 <= off)%Z -> (off + 4 <= n4 <= 1024)%Z ->
  (rm mod 4 = 0)%Z -> (gm mod 4 = 0)%Z -> (bm mod 4 = 0)%Z -> (am mod 4 = 0)%Z -> (off mod 4 = 0)%Z ->
  (0 <= vr <= 255)%Z -> (0 <= vg <= 255)%Z -> (0 <= vb <= 255)%Z -> (0 <= va <= 255)%Z ->
  rdn SEGS m (Z_to_bv 64 (arr + off + 2)) 1 = Some (Z_to_le_bytes 1 vr) -> rdn SEGS m (Z_to_bv 64 (arr + off + 1)) 1 = Some (Z_to_le_bytes 1 vg) ->
  rdn SEGS m (Z_to_bv 64 (arr + off + 0)) 1 = Some (Z_to_le_bytes 1 vb) -> rdn SEGS m (Z_to_bv 64 (arr + off + 3)) 1 = Some (Z_to_le_bytes 1 va) ->
  store_ok SEGS m (Z_to_bv 64 (rm + off)) 4 = true -> store_ok SEGS m (Z_to_bv 64 (gm + off)) 4 = true ->
  store_ok SEGS m (Z_to_bv 64 (bm + off)) 4 = true -> store_ok SEGS m (Z_to_bv 64 (am + off)) 4 = true ->
  (arr + off + 4 <= rm + off \/ rm + off + 4 <= arr + off)%Z -> (arr + off + 4 <= gm + off \/ gm + off + 4 <= arr + off)%Z ->
  (arr + off + 4 <= bm + off \/ bm + off + 4 <= arr + off)%Z ->
  (if last then off + 4 = n4 else off + 4 <> n4)%Z ->
  lregs regs q arr rm gm bm am n4 -> getr regs 11 = Z_to_bv 64 off ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x195d0) m rom)
                (@mkst fx regs' (Z_to_bv 64 (if last then 0x19670 else 0x195d0)) (PTAL m (rm + off) (gm + off) (bm + off) (am + off) vr vg vb va) rom)
    /\ getr regs' 11 = Z_to_bv 64 (off + 4)
    /\ regs_agree (fun r => In r [11; 20; 29; 30; 31]%list) regs regs'.
Proof.
  intros last fx regs m q arr rm gm bm am off n4 vr vg vb va Hq Harr Harr63 Hrm Hrm63 Hgm Hgm63 Hbm Hbm63 Ham Ham63 Hoff Hn4 ALr ALg ALb ALa ALo Hvr Hvg Hvb Hva
         Cr Cg Cb Ca SOKr SOKg SOKb SOKa APr APg APb Hlast LR H11.
  destruct LR as (H8 & H12 & H9 & H18 & H19 & H10 & H21 & H13 & H14 & H15 & H16 & H17 & H5 & H6 & H7 & H28).
  ex_entry regs [q; arr; rm; gm; bm; am; off; n4; vr; vg; vb; va] HR.
  assert (HK : know_ok SEGS (ex_env regs [q; arr; rm; gm; bm; am; off; n4; vr; vg; vb; va]) m
                 [KRange (EVar 32) 1 (2 ^ 63); KRange (EVar 33) 1 (2 ^ 63 - 1024); KRange (EVar 34) 1 (2 ^ 63 - 1024); KRange (EVar 35) 1 (2 ^ 63 - 1024);
                  KRange (EVar 36) 1 (2 ^ 63 - 1024); KRange (EVar 37) 1 (2 ^ 63 - 1024); KRange (EVar 38) 0 1020; KRange (EVar 39) 4 1024;
                  KAlign (EVar 34) 4; KAlign (EVar 35) 4; KAlign (EVar 36) 4; KAlign (EVar 37) 4; KAlign (EVar 38) 4;
                  KRange (EVar 40) 0 255; KRange (EVar 41) 0 255; KRange (EVar 42) 0 255; KRange (EVar 43) 0 255;
                  KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 2) 1 (EVar 40); KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 1) 1 (EVar 41);
                  KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 0) 1 (EVar 42); KWord (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 3) 1 (EVar 43);
                  KWr (SA (EAlu ALU_ADD (EVar 34) (EVar 38)) 0) 4; KWr (SA (EAlu ALU_ADD (EVar 35) (EVar 38)) 0) 4;
                  KWr (SA (EAlu ALU_ADD (EVar 36) (EVar 38)) 0) 4; KWr (SA (EAlu ALU_ADD (EVar 37) (EVar 38)) 0) 4;
                  KDisj (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 0) 4 (SA (EAlu ALU_ADD (EVar 34) (EVar 38)) 0) 4;
                  KDisj (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 0) 4 (SA (EAlu ALU_ADD (EVar 35) (EVar 38)) 0) 4;
                  KDisj (SA (EAlu ALU_ADD (EVar 33) (EVar 38)) 0) 4 (SA (EAlu ALU_ADD (EVar 36) (EVar 38)) 0) 4]).
  { ex_know regs.
    - apply (exx_kword_sum SEGS _ m _ _ _ arr off 2 vr 1); [reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | cbn; lia | lia | exact Cr].
    - apply (exx_kword_sum SEGS _ m _ _ _ arr off 1 vg 1); [reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | cbn; lia | lia | exact Cg].
    - apply (exx_kword_sum SEGS _ m _ _ _ arr off 0 vb 1); [reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | cbn; lia | lia | exact Cb].
    - apply (exx_kword_sum SEGS _ m _ _ _ arr off 3 va 1); [reflexivity | reflexivity | reflexivity | lia | lia | lia | lia | cbn; lia | lia | exact Ca].
    - apply (exx_kwr_sum SEGS _ m _ _ rm off 0 4 (rm + off) 4); [reflexivity | reflexivity | exact SOKr | lia | cbn; lia | lia | lia | lia | cbn; lia].
    - apply (exx_kwr_sum SEGS _ m _ _ gm off 0 4 (gm + off) 4); [reflexivity | reflexivity | exact SOKg | lia | cbn; lia | lia | lia | lia | cbn; lia].
    - apply (exx_kwr_sum SEGS _ m _ _ bm off 0 4 (bm + off) 4); [reflexivity | reflexivity | exact SOKb | lia | cbn; lia | lia | lia | lia | cbn; lia].
    - apply (exx_kwr_sum SEGS _ m _ _ am off 0 4 (am + off) 4); [reflexivity | reflexivity | exact SOKa | lia | cbn; lia | lia | lia | lia | cbn; lia].
    - apply (exx_kdisj_sum SEGS _ m _ _ _ _ arr off rm off 0 4 0 4); [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | clear - APr; lia].
    - apply (exx_kdisj_sum SEGS _ m _ _ _ _ arr off gm off 0 4 0 4); [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | clear - APg; lia].
    - apply (exx_kdisj_sum SEGS _ m _ _ _ _ arr off bm off 0 4 0 4); [reflexivity | reflexivity | reflexivity | reflexivity | lia | lia | clear - APb; lia]. }
  clear APr APg APb.
  destruct last.
  - ex_run 80%nat [0x19670%Z; 0x195d0%Z] (SCR [false; false; false; false; false; true] [] []) HR HK R' HR' Hms.
    exists R'. split; [unfold PTAL; ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
  - ex_run 80%nat [0x19670%Z; 0x195d0%Z] (SCR [false; false; false; false; false; false] [] []) HR HK R' HR' Hms.
    exists R'. split; [unfold PTAL; ex_mem2 regs Hms|].
    repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma pta_E : forall (fx : FPState) regs m (s z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 z25 : Z),
  (96 <= s < 2 ^ 63)%Z ->
  (0 <= z1 < 2 ^ 64)%Z -> (0 <= z8 < 2 ^ 64)%Z -> (0 <= z9 < 2 ^ 64)%Z -> (0 <= z18 < 2 ^ 64)%Z -> (0 <= z19 < 2 ^ 64)%Z -> (0 <= z20 < 2 ^ 64)%Z ->
  (0 <= z21 < 2 ^ 64)%Z -> (0 <= z22 < 2 ^ 64)%Z -> (0 <= z23 < 2 ^ 64)%Z -> (0 <= z24 < 2 ^ 64)%Z -> (0 <= z25 < 2 ^ 64)%Z ->
  rdn SEGS m (Z_to_bv 64 (s - 8)) 8 = Some (Z_to_le_bytes 8 z1) -> rdn SEGS m (Z_to_bv 64 (s - 16)) 8 = Some (Z_to_le_bytes 8 z8) ->
  rdn SEGS m (Z_to_bv 64 (s - 24)) 8 = Some (Z_to_le_bytes 8 z9) -> rdn SEGS m (Z_to_bv 64 (s - 32)) 8 = Some (Z_to_le_bytes 8 z18) ->
  rdn SEGS m (Z_to_bv 64 (s - 40)) 8 = Some (Z_to_le_bytes 8 z19) -> rdn SEGS m (Z_to_bv 64 (s - 48)) 8 = Some (Z_to_le_bytes 8 z20) ->
  rdn SEGS m (Z_to_bv 64 (s - 56)) 8 = Some (Z_to_le_bytes 8 z21) -> rdn SEGS m (Z_to_bv 64 (s - 64)) 8 = Some (Z_to_le_bytes 8 z22) ->
  rdn SEGS m (Z_to_bv 64 (s - 72)) 8 = Some (Z_to_le_bytes 8 z23) -> rdn SEGS m (Z_to_bv 64 (s - 80)) 8 = Some (Z_to_le_bytes 8 z24) ->
  rdn SEGS m (Z_to_bv 64 (s - 88)) 8 = Some (Z_to_le_bytes 8 z25) ->
  getr regs 2 = Z_to_bv 64 (s - 96) ->
  exists regs',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x19670) m rom) (@mkst fx regs' (Z_to_bv 64 0x196a4) m rom)
    /\ getr regs' 10 = Z_to_bv 64 0 /\ getr regs' 2 = Z_to_bv 64 s /\ getr regs' 1 = Z_to_bv 64 z1 /\ getr regs' 8 = Z_to_bv 64 z8
    /\ getr regs' 9 = Z_to_bv 64 z9 /\ getr regs' 18 = Z_to_bv 64 z18 /\ getr regs' 19 = Z_to_bv 64 z19 /\ getr regs' 20 = Z_to_bv 64 z20
    /\ getr regs' 21 = Z_to_bv 64 z21 /\ getr regs' 22 = Z_to_bv 64 z22 /\ getr regs' 23 = Z_to_bv 64 z23 /\ getr regs' 24 = Z_to_bv 64 z24
    /\ getr regs' 25 = Z_to_bv 64 z25
    /\ regs_agree (fun r => In r [1; 2; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof.
  intros fx regs m s z1 z8 z9 z18 z19 z20 z21 z22 z23 z24 z25 Hs R1 R8 R9 R18 R19 R20 R21 R22 R23 R24 R25 C1 C8 C9 C18 C19 C20 C21 C22 C23 C24 C25 H2.
  ex_entry regs [s; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24; z25] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; z1; z8; z9; z18; z19; z20; z21; z22; z23; z24; z25]) m
                 [KRange (EVar 32) 96 (2 ^ 63);
                  KWord (SA (EVar 32) (-8)) 8 (EVar 33); KWord (SA (EVar 32) (-16)) 8 (EVar 34); KWord (SA (EVar 32) (-24)) 8 (EVar 35);
                  KWord (SA (EVar 32) (-32)) 8 (EVar 36); KWord (SA (EVar 32) (-40)) 8 (EVar 37); KWord (SA (EVar 32) (-48)) 8 (EVar 38);
                  KWord (SA (EVar 32) (-56)) 8 (EVar 39); KWord (SA (EVar 32) (-64)) 8 (EVar 40); KWord (SA (EVar 32) (-72)) 8 (EVar 41);
                  KWord (SA (EVar 32) (-80)) 8 (EVar 42); KWord (SA (EVar 32) (-88)) 8 (EVar 43)]) by (ex_know regs).
  ex_run 50%nat [0x196a4%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. split; [ex_mem regs Hms|].
  repeat split; [ex_reg regs HR' .. | ex_agree HR HR']; ex_ext.
Qed.

(* [comment removed for export] *)
Lemma pta_loop : forall (k : nat) (fx : FPState) regs (M0 M : word -> option byte) (q arr rm gm bm am n i : Z),
  Z.of_nat k = (n - i)%Z -> (0 <= i < n)%Z -> (n <= 256)%Z -> (1 <= q < 2 ^ 63)%Z -> (1 <= arr)%Z -> (arr + 1024 < 2 ^ 63)%Z ->
  arrs4 rm gm bm am n -> (1 <= rm)%Z -> (1 <= gm)%Z -> (1 <= bm)%Z -> (1 <= am)%Z ->
  (rm + 1024 < 2 ^ 63)%Z -> (gm + 1024 < 2 ^ 63)%Z -> (bm + 1024 < 2 ^ 63)%Z -> (am + 1024 < 2 ^ 63)%Z ->
  (rm mod 4 = 0)%Z -> (gm mod 4 = 0)%Z -> (bm mod 4 = 0)%Z -> (am mod 4 = 0)%Z ->
  (arr + 4 * n <= rm \/ rm + 4 * n <= arr)%Z -> (arr + 4 * n <= gm \/ gm + 4 * n <= arr)%Z ->
  (arr + 4 * n <= bm \/ bm + 4 * n <= arr)%Z -> (arr + 4 * n <= am \/ am + 4 * n <= arr)%Z ->
  (exists bs, rdn SEGS M0 (Z_to_bv 64 arr) (Z.to_nat (4 * n)) = Some bs) ->
  regions_ok SEGS M0 (R4 rm gm bm am n) ->
  rinv (R4 rm gm bm am n) M0 M -> arr255 SEGS M rm n -> arr255 SEGS M gm n -> arr255 SEGS M bm n ->
  lregs regs q arr rm gm bm am (4 * n) -> getr regs 11 = Z_to_bv 64 (4 * i) ->
  exists regs' M',
    msteps SEGS (@mkst fx regs (Z_to_bv 64 0x195d0) M rom) (@mkst fx regs' (Z_to_bv 64 0x19670) M' rom)
    /\ rinv (R4 rm gm bm am n) M0 M' /\ arr255 SEGS M' rm n /\ arr255 SEGS M' gm n /\ arr255 SEGS M' bm n
    /\ regs_agree (fun r => In r [11; 20; 29; 30; 31]%list) regs regs'.
Proof.
  induction k as [|k IH]; intros fx regs M0 M q arr rm gm bm am n i Hk Hi Hn256 Hq Harr Harr63 G Hrm Hgm Hbm Ham Hrm63 Hgm63 Hbm63 Ham63 ALr ALg ALb ALa
                                 APr APg APb APa (bs & RD) RO RI Ar Ag Ab LR H11; [lia|].
  assert (RG : (0 <= rm /\ rm + 4 * n < 2 ^ 63 /\ 0 <= gm /\ gm + 4 * n < 2 ^ 63 /\ 0 <= bm /\ bm + 4 * n < 2 ^ 63 /\ 0 <= am /\ am + 4 * n < 2 ^ 63)%Z)
    by (clear - G; destruct G as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & _); repeat split; assumption).
  assert (APc : forall b, (arr + 4 * n <= b \/ b + 4 * n <= arr)%Z -> (arr + 4 * i + 4 <= b + 4 * i \/ b + 4 * i + 4 <= arr + 4 * i)%Z)
    by (clear - Hi; intros b H; lia).
  pose proof (APc rm APr) as APr1. pose proof (APc gm APg) as APg1. pose proof (APc bm APb) as APb1.
  assert (RDM : rdn SEGS M (Z_to_bv 64 arr) (Z.to_nat (4 * n)) = Some bs).
  { rewrite <- RD. apply (rinv_rdn SEGS (R4 rm gm bm am n) M0 M arr _ RI); [clear - Harr; lia | rewrite Z2Nat.id by (clear - Hi; lia); clear - Harr63 Hn256; lia|].
    intros r Hr. rewrite Z2Nat.id by (clear - Hi; lia). unfold R4 in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd]; [clear - APr; lia | clear - APg; lia | clear - APb; lia | clear - APa; lia]. }
  assert (BY : forall c, (0 <= c < 4)%Z -> exists v, (0 <= v <= 255)%Z /\ rdn SEGS M (Z_to_bv 64 (arr + 4 * i + c)) 1 = Some (Z_to_le_bytes 1 v)).
  { intros c Hc.
    destruct (rdn_byte_val SEGS M arr (Z.to_nat (4 * n)) bs (4 * i + c) ltac:(clear - Harr; lia) ltac:(rewrite Z2Nat.id by (clear - Hi; lia); clear - Harr63 Hn256; lia) RDM
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
  assert (N1 : (0 <= 4 * i)%Z /\ (4 * i + 4 <= 4 * n <= 1024)%Z /\ ((4 * i) mod 4 = 0)%Z) by (clear - Hi Hn256; repeat split; try lia; rewrite Z.mul_comm; apply Z_mod_mult).
  destruct N1 as (N1 & N2 & N3).
  destruct (Z.eq_dec (i + 1) n) as [LAST|MORE].
  - destruct (pta_L true fx regs M q arr rm gm bm am (4 * i) (4 * n) vr vg vb va Hq Harr Harr63 Hrm Hrm63 Hgm Hgm63 Hbm Hbm63 Ham Ham63 N1 N2 ALr ALg ALb ALa N3
                Hvr Hvg Hvb Hva Cr Cg Cb Ca SOKr SOKg SOKb SOKa APr1 APg1 APb1 ltac:(cbn; clear - LAST; lia) LR H11)
      as (r1 & RUN & _ & AG).
    exists r1, (PTAL M (rm + 4 * i) (gm + 4 * i) (bm + 4 * i) (am + 4 * i) vr vg vb va).
    split; [exact RUN|]. split; [exact RI'|]. split; [exact Ar'|]. split; [exact Ag'|]. split; [exact Ab' | exact AG].
  - destruct (pta_L false fx regs M q arr rm gm bm am (4 * i) (4 * n) vr vg vb va Hq Harr Harr63 Hrm Hrm63 Hgm Hgm63 Hbm Hbm63 Ham Ham63 N1 N2 ALr ALg ALb ALa N3
                Hvr Hvg Hvb Hva Cr Cg Cb Ca SOKr SOKg SOKb SOKa APr1 APg1 APb1 ltac:(cbn; clear - MORE; lia) LR H11)
      as (r1 & RUN & F11 & AG).
    destruct (IH fx r1 M0 (PTAL M (rm + 4 * i) (gm + 4 * i) (bm + 4 * i) (am + 4 * i) vr vg vb va) q arr rm gm bm am n (i + 1)%Z
                ltac:(clear - Hk; lia) ltac:(clear - Hi MORE; lia) Hn256 Hq Harr Harr63 G Hrm Hgm Hbm Ham Hrm63 Hgm63 Hbm63 Ham63 ALr ALg ALb ALa
                APr APg APb APa (ex_intro _ bs RD) RO RI' Ar' Ag' Ab')
      as (r2 & M2 & RUN2 & RI2 & Ar2 & Ag2 & Ab2 & AG2).
    + destruct LR as (L8 & L12 & L9 & L18 & L19 & L10 & L21 & L13 & L14 & L15 & L16 & L17 & L5 & L6 & L7 & L28).
      unfold lregs. repeat split; (rewrite (AG _) by notin_list; assumption).
    + rewrite F11. f_equal. clear; lia.
    + exists r2, M2. split; [exact (msteps_trans _ _ _ _ RUN RUN2)|]. split; [exact RI2|]. split; [exact Ar2|]. split; [exact Ag2|]. split; [exact Ab2|].
      intros r Hr. rewrite (AG2 r Hr). exact (AG r Hr).
Qed.

Lemma pta_ret : forall (fx : FPState) regs m (ret : word), ret_ok ret -> getr regs 1 = ret ->
  msteps SEGS (@mkst fx regs (Z_to_bv 64 0x196a4) m rom) (@mkst fx regs ret m rom).
Proof.
  intros fx regs m ret Hret H1. replace (Z_to_bv 64 0x196a4) with (0x196a4 : word) by (apply bv_eq; reflexivity).
  stepret F_195a0 D_195a0 ret ltac:(exact H1). apply mst_refl.
Qed.

End Segs.
