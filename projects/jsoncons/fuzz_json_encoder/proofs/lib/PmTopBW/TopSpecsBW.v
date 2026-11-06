(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface HeapIfaceA L5Defs L5Core L5LazyA Pm5L5DefsA PmHeapIfaceA IcptIfaceA PmIcptIfaceA.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PmLibDefs PmLibDefsA PmLibSpecsA PmLibSpecsW PmRef PmRefRead.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib.CutGen Require Import TopSpecsXB.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module TPSAW.
(* [comment removed for export] *)
Definition rest_of (IS : Z) (rep : PML.srep) (gp : Z) : list Z := skipn (Z.to_nat (gp - PML.srep_data (IS + 80) rep)) (PML.srep_chars rep).
Definition chunk_of (IS : Z) (rep : PML.srep) (gp : Z) : list Z := firstn (Z.to_nat PMR.CHUNK) (rest_of IS rep gp).

Section SpecsAW.
Context {SCFG_P : ScfgP}.
Variable L : asan_layout.
Variable ar : asan_run.
Variable HI : asan_iface.
Variable IC : PMLA.consts.
Abbreviation segs := (hl_segs L).

(* [comment removed for export] *)
Definition xsgetn_specAW (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (IS ch gp rdst sp r : Z) (rep : PML.srep),
    PMSA.cps_asan L ar HI pc r sp TPSA.XSGETN_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R (IS + 16) /\ PMSA.a1 R ch /\ PMSA.a2 R 16384 /\
                  PMLA.isrc_at segs IC M IS rep gp rdst /\ PMLA.srep_sh M rep /\ PMLA.img_ro IC M /\ Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\
                  PMSA.fobj M FF IS 272 /\ In (ch, 16384) LB /\ shadow_blk M ch 16384 /\ L5.defined M ch 16384 /\
                  (forall b, In b (PML.srep_blocks rep) -> In b LB /\ fst b <> ch) /\ PMSA.stksh ar M sp TPSA.XSGETN_SCR /\
                  Forall (fun b => 0 <= b <= 255) (PML.srep_chars rep) (* [comment removed for export] *))
      (fun R M R' M' LB' cr' LBk W => exists k, PMSA.a0 R' k /\ k = Z.min 16384 (PML.srep_data (IS + 80) rep + Z.of_nat (length (PML.srep_chars rep)) - gp) /\
          PMLA.isrc_at segs IC M' IS rep (gp + k) rdst /\ PMLA.srep_sh M' rep /\ shadow_blk M' ch 16384 /\ L5.defined M' ch 16384 /\
          LB' = LB /\ cr' = cr /\ LBk = lb_remove ch LB /\ W = [(IS + 40, 8)] /\
          L5.bytes_at segs M' ch (chunk_of IS rep gp) (* [comment removed for export] *)).

(* [comment removed for export] *)
Definition detect_json_specAW (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (ch k sp r : Z) (s : list Z),
    PMSA.cps_asan L ar HI pc r sp TPSA.DETECT_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R ch /\ PMSA.a1 R k /\ 1 <= k <= 16384 /\ In (ch, 16384) LB /\ shadow_blk M ch 16384 /\ L5.defined M ch k /\
                  PMLA.img_ro IC M /\ PMSA.stksh ar M sp TPSA.DETECT_SCR /\
                  L5.bytes_at segs M ch s /\ Z.of_nat (length s) = k /\ Forall (fun b => 0 <= b <= 255) s (* [comment removed for export] *))
      (fun R M R' M' LB' cr' LBk W => exists p', PMSA.a0 R' p' /\ ch <= p' <= ch + k /\ p' <= ch + 4 /\ LB' = LB /\ cr' = cr /\ LBk = LB /\ W = [] /\
          exists kind, PMSA.a1 R' kind /\                                                                     (* [comment removed for export] *)
          match PMR.detect s with Some j => p' = ch + Z.of_nat j /\ kind = 1 | None => 2 <= kind <= 5 end).

(* [comment removed for export] *)
Definition chunk_w (M' : PMSA.mem) (IS : Z) (rep : PML.srep) (gp : Z) (bof : bool) (ch p k gp' rdst' code : Z) (bof' : bool) : Prop :=
  let s := chunk_of IS rep gp in let '(j, cd, b') := PMRR.chunkw s bof in
  gp' = gp + Z.of_nat (length s) /\ rdst' = (if (length s <? Z.to_nat PMR.CHUNK)%nat then 2 else 0) /\ code = cd /\ bof' = b' /\
  (cd = 0 -> k = Z.of_nat (length s) - Z.of_nat j /\ (0 < k -> p = ch + Z.of_nat j /\ L5.bytes_at segs M' p (skipn j s))) /\
  (cd <> 0 -> k = 0).
Definition read_chunk_specAW (pc : Z) : Prop :=
  forall (LB : list (Z * Z)) (FF LK : list fframe) (cr : credit) (A : list (Z * Z)) (Rr IS V E ch gp rdst sp r : Z) (rep : PML.srep) (bof : bool) (g : PML.ls_state),
    PMSA.cps_asan L ar HI pc r sp TPSA.RCHUNK_SCR LB FF LK cr A 0
      (fun R M => PMSA.a0 R Rr /\ PMSA.a1 R E /\
                  TPSA.rdr_atA L IC M Rr IS V ch bof /\ PMLA.isrc_at segs IC M IS rep gp rdst /\ PMLA.srep_sh M rep /\ PMLA.img_ro IC M /\ Z.of_nat (length (PML.srep_chars rep)) < 2 ^ 26 /\
                  PMLA.ec_at segs IC M E 0 /\ PMLA.ls_ok segs IC g M /\ g <> PML.LS0 /\
                  PMSA.fobj M FF Rr 592 /\ PMSA.fobj M FF IS 272 /\ PMSA.fobj M FF E 16 /\ PMLA.apart Rr 592 IS 272 /\ PMLA.apart Rr 592 E 16 /\ PMLA.apart IS 272 E 16 /\
                  In (ch, 16384) LB /\ shadow_blk M ch 16384 /\ L5.defined M ch 16384 /\ (forall b, In b (PML.srep_blocks rep) -> In b LB /\ fst b <> ch) /\
                  PMSA.stksh ar M sp TPSA.RCHUNK_SCR /\
                  Forall (fun b => 0 <= b <= 255) (PML.srep_chars rep) (* [comment removed for export] *))
      (fun R M R' M' LB' cr' LBk W => exists (p k gp' rdst' code : Z) (bof' : bool) (g' : PML.ls_state),
          PMSA.a0 R' p /\ PMSA.a1 R' k /\ 0 <= p /\ p + k < 2 ^ 64 /\ 0 <= k <= 16384 /\ (0 < k -> ch <= p /\ p + k <= ch + 16384) /\
          TPSA.rdr_atA L IC M' Rr IS V ch bof' /\ PMLA.isrc_at segs IC M' IS rep gp' rdst' /\ PMLA.srep_sh M' rep /\ gp <= gp' /\ k <= gp' - gp /\ (code = 0 -> k = 0 -> rdst' = 2) /\
          PMLA.ec_at segs IC M' E code /\ PMLA.ls_ok segs IC g' M' /\ (g' = g \/ (g' = PML.LS2 /\ code <> 0)) /\
          shadow_blk M' ch 16384 /\ L5.defined M' ch 16384 /\
          LB' = LB /\ cr' = cr /\ LBk = lb_remove ch LB /\ W = TPSA.WRC IC Rr IS E /\
          (* [comment removed for export] *)
          (rdst = 2 -> k = 0 /\ gp' = gp /\ rdst' = 2 /\ bof' = bof /\ code = 0) /\
          (rdst = 0 -> chunk_w M' IS rep gp bof ch p k gp' rdst' code bof')).

End SpecsAW.
End TPSAW.
