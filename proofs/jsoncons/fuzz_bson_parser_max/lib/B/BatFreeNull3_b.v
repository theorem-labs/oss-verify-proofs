(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatRzLog_b BatPoison_b BatPoisonRun_b BatPoison3_b BatAllocA_b BatAllocB_b BatAllocG_b BatAllocV_b BatInitCache_b BatPopulate1_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatCls_b BatFp_b BatClsRep_b BatClsGfa2_b BatCellEx_b BatByteCell_b BatCARSpec_b BatAlloc3Pure_b BatDepotA_b BatDepot_b BatUnwind_b BatUnwindG_b BatAllocate3_b.
     From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFxInit_b BatFxIcpt_b BatFxNull_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_free_null_fp (S : Z) (x : Z) : Prop := (S - 4096 <= x < S) \/ (0x140e40 <= x < 0x140e40 + 0x81030) \/ (0x1cf6c8 <= x < 0x1cf6c8 + 4).

Section Spec.
Context {fx : PropExec.FPState}.

#[using="Type"] Theorem art_free3_null :
  forall regs (M0 rom : word -> option byte) (raw0 : word) (S HI p tp key tsd ctx t spb ris qs top bot : Z) (ia : bool),
    getr regs 1 = raw0 -> ret_ok raw0 -> getr regs 2 = Z_to_bv 64 S -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 p -> p = 0 ->
    art_geo HI t ctx tp tsd spb ris qs -> HI + 4096 <= S - 4096 -> S < 2 ^ 47 -> S mod 16 = 0 ->
    0 <= bot -> bot < top -> 4096 <= top -> top < 2 ^ 63 -> 0x661b28 <= tp - 88 -> 0x661b28 <= tsd ->
    wrA M0 (S - 4096) 4096 -> readable8 M0 S top -> wrA M0 t 4096 -> wrA M0 0x1cf6c8 4 -> wrA M0 0x140e40 0x81030 ->
    art_layout M0 -> art_tsd M0 tp key tsd ctx t -> art_prim_consts spb ris M0 ->
    cellA M0 0x140918 1 1 -> cellA M0 0x14093c 4 30 -> cellA M0 (0x1d1768 + 34) 1 1 -> cellA M0 (t + 3168) 1 0 -> cellA M0 (t + 40) 1 0 ->
    cellA M0 (t + 8) 8 top -> cellA M0 (t + 16) 8 bot ->
    cellA M0 0x1cf6c8 4 (if ia then 1 else 0) -> (ia = true -> forall k, 0 <= k < 2 ^ 15 -> cellA M0 (0x140e48 + 8 * k) 8 0) ->
    exists regs' (M' : word -> option byte),
      msteps ASEGS (mkst regs (0x79824 : word) M0 rom) (mkst regs' raw0 M' rom)
      /\ getr regs' 2 = Z_to_bv 64 S /\ getr regs' 1 = raw0
      /\ (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
      /\ mem_grows M0 M' /\ (forall x : word, ~ art_free_null_fp S (U x) -> M' x = M0 x)
      /\ cellA M' (t + 3168) 1 0 /\ cellA M' 0x1cf6c8 4 1 /\ (forall k, 0 <= k < 2 ^ 15 -> cellA M' (0x140e48 + 8 * k) 8 0).
Proof.
  intros regs M0 rom raw0 S HI p tp key tsd ctx t spb ris qs top bot ia
         H1 Hret H2 H4 H10 Ep0
         GEO HHI HS47 HS16 Hbot Hbt Htop4 Htop Htpd Htsdd
         W RD0 Wt Wia Wtab LY TSD PC
         Ci Cctx30 Cfast Cunw C40 Ctop Cbot Cia Ctab.
  assert (Hp : 0 <= p < 2 ^ 32) by (clear - Ep0; lia).
  pose proof GEO as (G1 & G2 & Espb & G4 & Eris & G6 & G7 & G8 & G9 & G10 & G11 & (qt & Et) & G13 & G14 & G15 & G16 & G17 & G18 & G19 & G20 & G21 & G22).
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G9; lia).
  assert (At_s : apart t 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G10; lia).
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; clear - G15; lia).
  assert (Ac_s : apart ctx 4096 0x7fff7000 (0x10007fff8000 - 0x7fff7000)) by (unfold apart; clear - G16; lia).
  change (hid (t + 4096 <= 0x10000 \/ 0x696000 <= t)) in G9. change (hid (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx)) in G15.
  clear G10 G16.
  pose proof TSD as (_ & _ & _ & _ & _ & TR).
  pose proof PC as (_ & _ & _ & _ & _ & Cpg1 & Cpg2 & _).
  assert (HS8 : S mod 8 = 0). { clear - HS16. rewrite <- (Z.div_exact S 16) in HS16 by lia. rewrite HS16. replace (16 * (S / 16)) with ((2 * (S / 16)) * 8) by lia. apply Z_mod_mult. }
  (* [comment removed for export] *)
  pose proof (art_fi_a_fn regs M0 rom raw0 S p H1 H2 H10 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) HS47 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) W) as RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R _ ?X _) => set (r1 := R) in RUN1; set (M1 := X) in RUN1 end.
  assert (G01 : mem_grows M0 M1) by (unfold M1, art_fi_mem; zgrows).
  assert (A01 : art_agree [(S - 4096, 4096)] M0 M1).
  { unfold M1, art_fi_mem. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop. eapply art_agree_sub; [zagree|]. intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia. }
  assert (F8 : cellA M1 (S - 8) 8 (U raw0)) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zcell).
  assert (F16 : cellA M1 (S - 16) 8 (U (getr regs 8))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zcell).
  assert (F24 : cellA M1 (S - 24) 8 (U (getr regs 9))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zcell).
  assert (F32 : cellA M1 (S - 32) 8 (U (getr regs 18))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zcell).
  assert (F40 : cellA M1 (S - 40) 8 (U (getr regs 19))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zcell).
  assert (F48 : cellA M1 (S - 48) 8 (U (getr regs 20))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zcell).
  assert (F56 : cellA M1 (S - 56) 8 (U (getr regs 21))) by (unfold M1, art_fi_mem; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zcell).
  (* [comment removed for export] *)
  destruct (art_ia_run r1 M1 rom (0x79858 : bv 64)%bv (S - 2128) ia
              ltac:(unfold r1; gres; bveq) ltac:(unfold ret_ok; bveq) ltac:(unfold r1; gres; reflexivity)
              ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia)
              ltac:(eapply wr_grows; [exact G01|]; eapply wr_sub; [exact W|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A01); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cia]) ltac:(eapply wr_grows; [exact G01|exact Wia]) ltac:(eapply wr_grows; [exact G01|exact Wtab])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A01); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cpg1]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A01); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cpg2])
              ltac:(intros Eia k Hk; apply (art_cell_tr1 _ _ _ _ _ _ A01); [revert Hk; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; intros Hk; zarith_t|exact (Ctab Eia k Hk)]))
    as (r2 & M2 & RUN2 & P2_10 & P2_1 & P2_2 & K2 & G12 & A12 & Cia2 & Ctab2).
  replace (S - 2128 - 48) with (S - 2176) in A12 by (clear; lia).
  pose proof (art_agree_trans _ _ _ _ _ A01 A12) as A02. cbn [app] in A02.
  assert (G02 : mem_grows M0 M2) by (eapply mem_grows_trans; [exact G01|exact G12]).
  (* [comment removed for export] *)
  assert (T2 : art_tsd M2 tp key tsd ctx t). { apply (art_tsd_tr _ M0 M2 tp key tsd ctx t A02); [| | | |exact TSD]; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t. }
  destruct (art_fi_b r2 M2 rom S p (p / 2 ^ 32) tp key tsd ctx t top bot
              P2_2 ltac:(rewrite K2 by inl; unfold r1; gres; exact H4) ltac:(rewrite K2 by inl; unfold r1; gres; reflexivity) ltac:(rewrite K2 by inl; unfold r1; gres; reflexivity) P2_10
              ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) HS47 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) ltac:(apply Z.div_mod; clear; lia)
              G7 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) G9 ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) G15 G18 G19 G20 G21 G22 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) Htop
              ltac:(eapply wr_grows; [exact G02|exact W]) ltac:(eapply wr_grows; [exact G02|exact Wt]) T2
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Ci])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cctx30])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|pose proof LY as L'; unfold art_layout in L'; tauto])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cfast])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cunw])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact C40])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Ctop])
              ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A02); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cbot])
              ltac:(replace (0x140e40 + 8 + 8 * (p / 2 ^ 32)) with (0x140e48 + 8 * (p / 2 ^ 32)) by (clear; lia); apply Ctab2;
                    split; [apply Z.div_pos; [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia|clear; lia] | apply Z.div_lt_upper_bound; [clear; lia|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia]]))
    as (r3 & M3 & RUN3 & Q3_1 & Q3_2 & Q3_10 & Q3_11 & Q3_12 & Q3_13 & Q3_14 & Q3_15 & Q3_24 & Q3_4 & K3 & G23 & A23p
        & E36 & E44 & E52 & E60 & E68 & E76 & E84 & E92 & E00 & E08 & E28 & E20 & E16' & W3).
  assert (E22 : getr r2 22 = getr regs 22) by (rewrite K2 by inl; unfold r1; gres; reflexivity).
  assert (E23 : getr r2 23 = getr regs 23) by (rewrite K2 by inl; unfold r1; gres; reflexivity).
  assert (E24 : getr r2 24 = getr regs 24) by (rewrite K2 by inl; unfold r1; gres; reflexivity).
  rewrite E22 in E92. rewrite E23 in E00. rewrite E24 in E08.
  assert (A23 : art_agree [(S - 2272, 2208); (t + 3168, 1)] M2 M3).
  { intros x Hx. cbn [art_out fst snd] in Hx. apply A23p; clear - Hx; lia. }
  pose proof (art_agree_trans _ _ _ _ _ A02 A23) as A03. cbn [app] in A03.
  assert (G03 : mem_grows M0 M3) by (eapply mem_grows_trans; [exact G02|exact G23]).
  (* [comment removed for export] *)
  assert (RD3 : readable8 M3 (S - 16) top).
  { intros a Ha1 Ha2 Ha8. destruct (Z.lt_ge_cases a S) as [Lo|Hi].
    - assert (a = S - 16 \/ a = S - 8) as [->| ->].
      { clear - Ha1 Lo Ha8 HS8. rewrite <- (Z.div_exact a 8) in Ha8 by lia. rewrite <- (Z.div_exact S 8) in HS8 by lia. lia. }
      + eexists. apply (art_cell_tr1 _ M2 M3 _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ M1 M2 _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. exact F16.
      + eexists. apply (art_cell_tr1 _ M2 M3 _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ M1 M2 _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. exact F8.
    - destruct (RD0 a ltac:(lia) ltac:(lia) Ha8) as [w' Cw]. exists w'. apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [|exact Cw].
      revert Hi Ha2. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop. intros Hi Ha2. zarith_t. }
  destruct (art_unwind_fast_any r3 M3 rom (0x81f98 : bv 64)%bv (S - 2208) (S - 2128) 0x7995c S top bot
              Q3_1 ltac:(unfold ret_ok; bveq) Q3_2 Q3_10 Q3_11 Q3_12 Q3_13 Q3_14 Q3_15
              ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) ltac:(clear; lia) ltac:(clear; lia) Hbot Hbt Htop4 Htop ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) HS8 ltac:(clear; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia)
              ltac:(eapply wr_sub; [exact W3|clear; lia|clear; lia]) ltac:(eapply wr_sub; [exact W3|clear; lia|clear; lia]) (fun _ _ => RD3)
              ltac:(apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cpg1]) ltac:(apply (art_cell_tr1 _ M0 M3 _ _ _ A03); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cpg2]))
    as (r4 & M4 & RUN4 & Q4_2 & Q4_1 & K4 & G34 & A34p & (sz & Hsz & Csz & TRC)).
  assert (A34 : art_agree [(S - 2120, 4); (S - 2112, 240); (S - 2272, 64)] M3 M4).
  { intros x Hx. cbn [art_out fst snd] in Hx. apply A34p; clear - Hx; lia. }
  pose proof (art_agree_trans _ _ _ _ _ A03 A34) as A04. cbn [app] in A04.
  assert (G04 : mem_grows M0 M4) by (eapply mem_grows_trans; [exact G03|exact G34]).
  (* [comment removed for export] *)
  assert (Wt4 : wrA M4 t 4096) by (eapply wr_grows; [exact G04|exact Wt]).
  assert (F8' : cellA M4 (S - 8) 8 (U raw0)). { apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact F8]. }
  assert (F16' : cellA M4 (S - 16) 8 (U (getr regs 8))). { apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact F16]. }
  assert (F24' : cellA M4 (S - 24) 8 (U (getr regs 9))). { apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact F24]. }
  assert (F32' : cellA M4 (S - 32) 8 (U (getr regs 18))). { apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact F32]. }
  assert (F40' : cellA M4 (S - 40) 8 (U (getr regs 19))). { apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact F40]. }
  assert (F48' : cellA M4 (S - 48) 8 (U (getr regs 20))). { apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact F48]. }
  assert (F56' : cellA M4 (S - 56) 8 (U (getr regs 21))). { apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A23); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|]. apply (art_cell_tr1 _ _ _ _ _ _ A12); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact F56]. }
  rewrite Ep0 in E52.
  destruct (art_fx_null_fn r4 M4 rom raw0 S t (U (getr regs 22)) (U (getr regs 23)) (U (getr regs 24))
               (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20)) (U (getr regs 21))
               Q4_2 ltac:(rewrite K4 by inl; exact Q3_24) Hret
               ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) HS47 G7 ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) ltac:(unfold apart; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) G9
               (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _) (u64_range _)
               ltac:(eapply wr_grows; [exact G34|exact W3]) Wt4
               ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E36]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E44]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E52]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E60]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E68]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E76]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E84]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E92]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E00]) ltac:(apply (art_cell_tr1 _ _ _ _ _ _ A34); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact E08])
               F8' F16' F24' F32' F40' F48' F56')
    as (r5 & RUN5 & R5_1 & R5_2 & R5_8 & R5_9 & R5_18 & R5_19 & R5_20 & R5_21 & R5_22 & R5_23 & R5_24 & K5).
  match type of RUN5 with msteps _ _ (mkst _ _ ?X _) => set (M5 := X) in RUN5 end.
  assert (G45 : mem_grows M4 M5) by (unfold M5, art_fx_null_mem; zgrows).
  assert (A45 : art_agree [(S - 4096, 4096); (t + 3168, 1)] M4 M5).
  { unfold M5, art_fx_null_mem. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop. eapply art_agree_sub; [zagree|]. intros z Hz Hout; cbn [art_out app fst snd] in Hout |- *; repeat split; lia. }
  pose proof (art_agree_trans _ _ _ _ _ A04 A45) as A05. cbn [app] in A05.
  exists r5, M5. split.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|]. exact RUN5. }
  split; [exact R5_2|]. split; [exact R5_1|].
  split.
  { assert (KK : forall r : reg, In r [3; 4; 25; 26; 27]%bv -> getr r5 r = getr regs r).
    { intros r Hr. rewrite K5 by exact Hr. rewrite K4 by (clear - Hr; cbn [In] in *; tauto).
      assert (E3 : getr r3 r = getr r2 r).
      { cbn [In] in Hr. destruct Hr as [<-|[<-|Hr]]; [apply K3; inl| |apply K3; clear - Hr; cbn [In] in *; tauto].
        rewrite Q3_4. symmetry. rewrite K2 by inl. unfold r1; gres. exact H4. }
      rewrite E3. rewrite K2 by (clear - Hr; cbn [In] in *; tauto). clear - Hr. cbn [In] in Hr. unfold r1.
      destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; gres; reflexivity. }
    intros r Hr. cbn [In] in Hr.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]];
      first [ rewrite R5_8; apply Z_to_bv_bv_unsigned | rewrite R5_9; apply Z_to_bv_bv_unsigned | rewrite R5_18; apply Z_to_bv_bv_unsigned
            | rewrite R5_19; apply Z_to_bv_bv_unsigned | rewrite R5_20; apply Z_to_bv_bv_unsigned | rewrite R5_21; apply Z_to_bv_bv_unsigned
            | rewrite R5_22; apply Z_to_bv_bv_unsigned | rewrite R5_23; apply Z_to_bv_bv_unsigned | rewrite R5_24; apply Z_to_bv_bv_unsigned | apply KK; inl ]. }
  split; [eapply mem_grows_trans; [exact G04|exact G45]|].
  assert (Cunw5 : cellA M5 (t + 3168) 1 0). { unfold M5, art_fx_null_mem. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop. zcell. }
  split.
  { intros x N1. destruct (Z.eq_dec (U x) (t + 3168)) as [e|ne].
    + assert (Ex : x = Z_to_bv 64 (t + 3168)) by (rewrite <- e; symmetry; apply Z_to_bv_bv_unsigned). rewrite Ex.
      rewrite (art_byte_of_cell1 M0 (t + 3168) 0 ltac:(clear - At_i; unfold apart in At_i; lia) ltac:(clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia) ltac:(clear; lia) Cunw).
      apply art_byte_of_cell1; [clear - At_i; unfold apart in At_i; lia|clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; lia|clear; lia|exact Cunw5].
    + apply A05. unfold art_free_null_fp in N1. cbn [art_out fst snd]. revert N1 ne. clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop. intros N1 ne. repeat split; lia. }
  split; [exact Cunw5|].
  assert (A25 : art_agree ([(S - 2272, 2208); (t + 3168, 1)] ++ [(S - 2120, 4); (S - 2112, 240); (S - 2272, 64)] ++ [(S - 4096, 4096); (t + 3168, 1)]) M2 M5).
  { eapply art_agree_trans; [exact A23|]. eapply art_agree_trans; [exact A34|exact A45]. }
  cbn [app] in A25.
  split; [apply (art_cell_tr1 _ _ _ _ _ _ A25); [clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; zarith_t|exact Cia2]|].
  intros k Hk. apply (art_cell_tr1 _ _ _ _ _ _ A25); [revert Hk; clear - HHI HS47 HS16 HS8 G1 G2 G4 G6 G7 G8 G11 G13 G14 G17 G18 G19 G20 G21 G22 Espb Eris At_i At_s Ac_i Ac_s Htpd Htsdd Hp TR Hbot Hbt Htop4 Htop; intros Hk; zarith_t|exact (Ctab2 k Hk)].
Qed.
End Spec.
