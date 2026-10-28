(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5
  PmRefRead_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopSpecs_u5.
Import ListNotations. Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module TPSW.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.

(* [comment removed for export] *)
Definition rest_of (IS : Z) (rep : srep) (gp : Z) : list Z := skipn (Z.to_nat (gp - srep_data (IS + 80) rep)) (srep_chars rep).
Definition chunk_of (IS : Z) (rep : srep) (gp : Z) : list Z := firstn (Z.to_nat PMR.CHUNK) (rest_of IS rep gp).

(* [comment removed for export] *)
Definition xsgetn_specw : Prop :=
  forall (sp r IS dst gp rdst : Z) (rep : srep),
    cps_pure PC_XSGETN r sp TPS.XSGETN_SCR [(IS + 40, 8); (dst, 16384)]
      (fun R M => entry L R M sp r TPS.XSGETN_SCR /\ a0 R (IS + 16) /\ a1 R dst /\ a2 R 16384 /\
                  isrc_at M IS rep gp rdst /\ img_ro M /\ Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\ obj_on_stack L sp IS 272 /\
                  block_range L dst 16384 /\ L5.defined M dst 16384 /\
                  (forall b, In b (srep_blocks rep) -> block_range L (fst b) (snd b) /\ apart (fst b) (snd b) dst 16384) /\
                  Forall (fun b => 0 <= b <= 255) (srep_chars rep) (* [comment removed for export] *))
      (fun R M R' M' => exists k, a0 R' k /\ k = Z.min 16384 (srep_data (IS + 80) rep + Z.of_nat (length (srep_chars rep)) - gp) /\ isrc_at M' IS rep (gp + k) rdst /\
                  L5.bytes_at RSEGS M' dst (chunk_of IS rep gp) (* [comment removed for export] *)).

(* [comment removed for export] *)
Definition detect_json_specw : Prop :=
  forall (sp r p k : Z) (s : list Z),
    cps_pure PC_DETECT_JSON r sp TPS.DETECT_SCR []
      (fun R M => entry L R M sp r TPS.DETECT_SCR /\ a0 R p /\ a1 R k /\ 1 <= k <= 16384 /\ block_range L p k /\ L5.defined M p k /\ img_ro M /\
                  L5.bytes_at RSEGS M p s /\ Z.of_nat (length s) = k /\ Forall (fun b => 0 <= b <= 255) s (* [comment removed for export] *))
      (fun R M R' M' => exists p', a0 R' p' /\ p <= p' <= p + k /\ p' <= p + 4 /\
                  exists kind, a1 R' kind /\                                                          (* [comment removed for export] *)
                  match PMR.detect s with Some j => p' = p + Z.of_nat j /\ kind = 1 | None => 2 <= kind <= 5 end).

(* [comment removed for export] *)
Definition chunk_w (M' : mem) (IS : Z) (rep : srep) (gp : Z) (bof : bool) (ch p k gp' rdst' code : Z) (bof' : bool) : Prop :=
  let s := chunk_of IS rep gp in let '(j, cd, b') := PMRR.chunkw s bof in
  gp' = gp + Z.of_nat (length s) /\ rdst' = (if (length s <? Z.to_nat PMR.CHUNK)%nat then 2 else 0) /\ code = cd /\ bof' = b' /\
  (cd = 0 -> k = Z.of_nat (length s) - Z.of_nat j /\ (0 < k -> p = ch + Z.of_nat j /\ L5.bytes_at RSEGS M' p (skipn j s))) /\
  (cd <> 0 -> k = 0).
Definition read_chunk_specw : Prop :=
  forall (sp r Rr IS V E ch gp rdst : Z) (rep : srep) (bof : bool) (g : ls_state),
    cps_pure PC_READ_CHUNK r sp TPS.RCHUNK_SCR [(Rr, 320); (IS, 272); (E, 16); (ch, 16384); (0xdb5c0, 2); (0xfd058, 544)]
      (fun R M => entry L R M sp r TPS.RCHUNK_SCR /\ a0 R Rr /\ a1 R E /\
                  TPS.rdr_at M Rr IS V ch bof /\ isrc_at M IS rep gp rdst /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\ Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\
                  obj_on_stack L sp Rr 592 /\ obj_on_stack L sp IS 272 /\ obj_on_stack L sp E 16 /\ apart Rr 592 IS 272 /\ apart Rr 592 E 16 /\ apart IS 272 E 16 /\
                  block_range L ch 16384 /\ L5.defined M ch 16384 /\
                  (forall b, In b (srep_blocks rep) -> block_range L (fst b) (snd b) /\ apart (fst b) (snd b) ch 16384) /\
                  Forall (fun b => 0 <= b <= 255) (srep_chars rep) (* [comment removed for export] *))
      (fun R M R' M' => exists (p k gp' rdst' code : Z) (bof' : bool) (g' : ls_state),
          a0 R' p /\ a1 R' k /\ 0 <= p /\ p + k < 2 ^ 64 /\ 0 <= k <= 16384 /\ (0 < k -> ch <= p /\ p + k <= ch + 16384) /\
          TPS.rdr_at M' Rr IS V ch bof' /\ isrc_at M' IS rep gp' rdst' /\ gp <= gp' /\ k <= gp' - gp /\ (code = 0 -> k = 0 -> rdst' = 2) /\
          ec_at M' E code /\ ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0)) /\
          (* [comment removed for export] *)
          (rdst = 2 -> k = 0 /\ gp' = gp /\ rdst' = 2 /\ bof' = bof /\ code = 0) /\
          (rdst = 0 -> chunk_w M' IS rep gp bof ch p k gp' rdst' code bof')).
End Specs.
End TPSW.
