(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface LibIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5.
Import ListNotations. Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module TPS.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Definition IOSB_SCR : Z := 64.
Definition istream_dtor_spec : Prop :=
  forall (sp r : Z), cps_pure PC_ISTREAM_DTOR r sp 0 [] (fun R M => entry L R M sp r 0) (fun R M R' M' => True).
Definition iosb_dtor_spec : Prop :=
  forall (B rd rb sp r : Z),
    cps_pure PC_IOSB_DTOR r sp IOSB_SCR [(B, 8)]
      (fun R M => entry L R M sp r IOSB_SCR /\ a0 R B /\ iosb_at M B rd rb /\ obj_on_stack L sp B 152)
      (fun R M R' M' => True).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rdr_at (M : mem) (R IS V ch : Z) (bof : bool) : Prop :=
  u64 M (R + 240) IS /\ u64 M (R + 248) (IS + 16) /\ u64 M (R + 264) ch /\ u64 M (R + 272) 16384 /\
  (exists de, u64 M (R + 280) de /\ ch <= de <= ch + 16384) /\ u64 M (R + 288) 0 /\ u8 M (R + 296) (b2z bof) /\
  u64 M (R + 304) VT_DEFVIS /\ u64 M (R + 312) V /\
  (exists st0, iosb_at M (R + 88) st0 (R + 24)) /\ u64 M (R + 32) CLASSIC_IMP /\ L5.defined M R 320.
Definition RCHUNK_SCR : Z := 512.      (* [comment removed for export] *)
Definition read_chunk_spec : Prop :=
  forall (sp r Rr IS V E ch gp rdst : Z) (rep : srep) (bof : bool) (g : ls_state),
    cps_pure PC_READ_CHUNK r sp RCHUNK_SCR [(Rr, 320); (IS, 272); (E, 16); (ch, 16384); (0xdb5c0, 2); (0xfd058, 544)]
      (fun R M => entry L R M sp r RCHUNK_SCR /\ a0 R Rr /\ a1 R E /\
                  rdr_at M Rr IS V ch bof /\ isrc_at M IS rep gp rdst /\ ec_at M E 0 /\ ls_ok g M /\ g <> LS0 /\ Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\
                  obj_on_stack L sp Rr 592 /\ obj_on_stack L sp IS 272 /\ obj_on_stack L sp E 16 /\ apart Rr 592 IS 272 /\ apart Rr 592 E 16 /\ apart IS 272 E 16 /\
                  block_range L ch 16384 /\ L5.defined M ch 16384 /\
                  (forall b, In b (srep_blocks rep) -> block_range L (fst b) (snd b) /\ apart (fst b) (snd b) ch 16384))
      (fun R M R' M' => exists (p k gp' rdst' code : Z) (bof' : bool) (g' : ls_state),
          a0 R' p /\ a1 R' k /\ 0 <= p /\ p + k < 2 ^ 64 /\ 0 <= k <= 16384 /\ (0 < k -> ch <= p /\ p + k <= ch + 16384) /\
          rdr_at M' Rr IS V ch bof' /\ isrc_at M' IS rep gp' rdst' /\ gp <= gp' /\ k <= gp' - gp /\ (code = 0 -> k = 0 -> rdst' = 2) /\
          ec_at M' E code /\ ls_ok g' M' /\ (g' = g \/ (g' = LS2 /\ code <> 0))).
(* [comment removed for export] *)
Definition XSGETN_SCR : Z := 96.        (* [comment removed for export] *)
Definition xsgetn_spec : Prop :=
  forall (sp r IS dst gp rdst : Z) (rep : srep),
    cps_pure PC_XSGETN r sp XSGETN_SCR [(IS + 40, 8); (dst, 16384)]
      (fun R M => entry L R M sp r XSGETN_SCR /\ a0 R (IS + 16) /\ a1 R dst /\ a2 R 16384 /\
                  isrc_at M IS rep gp rdst /\ img_ro M /\ Z.of_nat (length (srep_chars rep)) < 2 ^ 26 /\ obj_on_stack L sp IS 272 /\
                  block_range L dst 16384 /\ L5.defined M dst 16384 /\
                  (forall b, In b (srep_blocks rep) -> block_range L (fst b) (snd b) /\ apart (fst b) (snd b) dst 16384))
      (fun R M R' M' => exists k, a0 R' k /\ k = Z.min 16384 (srep_data (IS + 80) rep + Z.of_nat (length (srep_chars rep)) - gp) /\ isrc_at M' IS rep (gp + k) rdst).
(* [comment removed for export] *)
Definition DETECT_SCR : Z := 64.        (* [comment removed for export] *)
Definition detect_json_spec : Prop :=
  forall (sp r p k : Z),
    cps_pure PC_DETECT_JSON r sp DETECT_SCR []
      (fun R M => entry L R M sp r DETECT_SCR /\ a0 R p /\ a1 R k /\ 1 <= k <= 16384 /\ block_range L p k /\ L5.defined M p k /\ img_ro M)
      (fun R M R' M' => exists p', a0 R' p' /\ p <= p' <= p + k /\ p' <= p + 4).
End Specs.
End TPS.
