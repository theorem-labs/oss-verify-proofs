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
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatRefill1_b BatPopulate4_b BatFp_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_agree_w4s : forall ws M dst, 0 <= dst -> dst + 4 * Z.of_nat (length ws) < 2 ^ 64 ->
  art_agree [(dst, 4 * Z.of_nat (length ws))] M (art_w4s M dst ws).
Proof. intros ws M dst Hd Hd' x Hx. cbn in Hx. destruct Hx as [Hx _]. apply art_w4s_outside; [exact Hd|exact Hd'|exact Hx]. Qed.

(* [comment removed for export] *)
Definition art_gfa_fcells (M : word -> option byte) (sp : Z) (raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 : word) : Prop :=
  cellA M (sp - 8) 8 (U raw) /\ cellA M (sp - 16) 8 (U g8) /\ cellA M (sp - 24) 8 (U g9) /\ cellA M (sp - 32) 8 (U g18) /\ cellA M (sp - 40) 8 (U g19)
  /\ cellA M (sp - 48) 8 (U g20) /\ cellA M (sp - 56) 8 (U g21) /\ cellA M (sp - 64) 8 (U g22) /\ cellA M (sp - 72) 8 (U g23) /\ cellA M (sp - 80) 8 (U g24)
  /\ cellA M (sp - 88) 8 (U g25) /\ cellA M (sp - 96) 8 (U g26) /\ cellA M (sp - 104) 8 (U g27).

Lemma art_gfa_fcells_tr : forall W M M' sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27,
  art_agree W M M' -> art_gap W (sp - 104) 104 -> 104 <= sp -> sp < 2 ^ 64 ->
  art_gfa_fcells M sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 -> art_gfa_fcells M' sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27.
Proof.
  intros W M M' sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 A G Hsp Hsp' F.
  assert (T : forall a v, sp - 104 <= a -> a + 8 <= sp -> cellA M a 8 v -> cellA M' a 8 v).
  { intros a v Ha Ha' C. apply (art_cell_tr W M M'); [exact A|eapply art_gap_sub; [exact G|lia|cbn; lia]|lia|cbn; lia|exact C]. }
  destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  unfold art_gfa_fcells. repeat split; apply T; first [lia | assumption].
Qed.

Lemma art_gfa_fcells_frame : forall M sp raw regs, 104 <= sp -> sp < 2 ^ 64 ->
  art_gfa_fcells (art_gfa_frame M sp raw regs) sp raw (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                 (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27).
Proof. intros M sp raw regs Hsp Hsp'. unfold art_gfa_fcells, art_gfa_frame. repeat split; zcell. Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_clsgfa_finish : forall (ws : list Z) regs (M rom : word -> option byte) (raw : word) (sp r ris qris c chp src na : Z)
    (g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 : word),
  getr regs 2 = Z_to_bv 64 (sp - 128) -> getr regs 8 = Z_to_bv 64 r -> getr regs 11 = Z_to_bv 64 (chp + 4 * Z.of_nat (length ws)) -> getr regs 13 = Z_to_bv 64 chp ->
  getr regs 14 = Z_to_bv 64 (Z.of_nat (length ws)) -> getr regs 19 = Z_to_bv 64 (2 ^ 61) -> getr regs 20 = Z_to_bv 64 src ->
  ret_ok raw -> (1 <= length ws <= 8)%nat ->
  0x696000 + 128 <= sp -> sp < 2 ^ 47 -> r = ris + 128 * c -> ris = 128 * qris -> 0 <= ris -> 1 <= c <= 31 -> r + 128 <= sp - 128 ->
  4096 <= chp -> chp + 64 <= sp - 128 -> 0 <= src -> src + 64 <= sp - 128 ->
  apart chp 64 src (4 * Z.of_nat (length ws)) -> apart chp 64 r 128 -> apart chp 64 0x10420 8 -> 0 <= na < 2 ^ 64 ->
  wrA M chp (4 * Z.of_nat (length ws)) -> wrA M r 128 ->
  (forall j, (j < length ws)%nat -> 0 <= nth j ws 0 < 2 ^ 31 /\ cellA M (src + 4 * Z.of_nat j) 4 (nth j ws 0)) ->
  cellA M (r + 72) 8 na -> cellA M r 8 (2 ^ 60) -> cellA M 0x10420 8 0xafffff00000fffff ->
  art_gfa_fcells M sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x57700 : word) M rom) (mkst regs' raw M' rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = Z_to_bv 64 sp /\ getr regs' 1 = raw
    /\ getr regs' 8 = g8 /\ getr regs' 9 = g9 /\ getr regs' 18 = g18 /\ getr regs' 19 = g19 /\ getr regs' 20 = g20 /\ getr regs' 21 = g21 /\ getr regs' 22 = g22
    /\ getr regs' 23 = g23 /\ getr regs' 24 = g24 /\ getr regs' 25 = g25 /\ getr regs' 26 = g26 /\ getr regs' 27 = g27
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ mem_grows M M' /\ art_agree [(chp, 4 * Z.of_nat (length ws)); (r + 72, 8); (r, 8)] M M'
    /\ (forall j, (j < length ws)%nat -> cellA M' (chp + 4 * Z.of_nat j) 4 (nth j ws 0))
    /\ cellA M' (r + 72) 8 (na + Z.of_nat (length ws)) /\ cellA M' r 8 0.
Proof.
  intros ws regs M rom raw sp r ris qris c chp src na g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27
         H2 H8 H11 H13 H14 H19 H20 Hret Hlen IMG Hsp' Er Eris Hris Hc Hr' Hchp Hchp' Hsrc Hsrc' Acs Acr Acd Hna Wch Wr Cws Cna Cmx Crd F.
  set (n := Z.of_nat (length ws)) in *. assert (Hn : 1 <= n <= 8) by (unfold n; lia).
  destruct (art_gfa_copy ws regs M rom chp src (chp + 4 * n) H13 H20 H11 ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) Hsrc ltac:(lia) Hchp
              ltac:(unfold apart in Acs |- *; lia) Wch Cws) as (r1 & RUN1 & P13 & P20 & K1).
  set (M1 := art_w4s M chp ws) in *.
  assert (A1 : art_agree [(chp, 4 * n)] M M1) by (apply art_agree_w4s; lia).
  assert (G1 : mem_grows M M1) by apply art_w4s_grows.
  assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }
  pose proof (art_gfa_fcells_tr _ M M1 sp raw g8 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 A1 ltac:(zgap) ltac:(lia) ltac:(lia) F) as F1.
  destruct F1 as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & F13).
  unfold apart in Acr, Acd.
  pose proof (art_gfa_tail_fn r1 M1 rom raw sp r n na ris qris c (U g8) (U g9) (U g18) (U g19) (U g20) (U g21) (U g22) (U g23) (U g24) (U g25) (U g26) (U g27)
                ltac:(rewrite K1 by (intros E; discriminate E); exact H2) ltac:(rewrite K1 by (intros E; discriminate E); exact H8)
                ltac:(rewrite K1 by (intros E; discriminate E); exact H14) ltac:(rewrite K1 by (intros E; discriminate E); exact H19)
                ltac:(lia) ltac:(lia) IMG Er Eris Hris Hc ltac:(lia) ltac:(unfold apart; lia) ltac:(lia) Hna Hret
                (UB g8) (UB g9) (UB g18) (UB g19) (UB g20) (UB g21) (UB g22) (UB g23) (UB g24) (UB g25) (UB g26) (UB g27)
                ltac:(eapply wr_grows; [exact G1|exact Wr]) ltac:(ztr) ltac:(ztr) ltac:(ztr)
                F1 F2 F3 F4 F5 F6 F7 F8 F9 F10 F11 F12 F13) as RUN2.
  match type of RUN2 with msteps _ _ (mkst ?R _ ?MM _) => set (r2 := R) in RUN2; set (M2 := MM) in RUN2 end.
  assert (A2 : art_agree [(r + 72, 8); (r, 8)] M1 M2). { unfold M2. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G2 : mem_grows M1 M2) by (unfold M2; zgrows).
  exists r2, M2. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
  split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|].
  do 12 (split; [unfold r2; gres; apply Z_to_bv_bv_unsigned|]).
  split; [unfold r2; gres; apply K1; intros E; discriminate E|]. split; [unfold r2; gres; apply K1; intros E; discriminate E|].
  split; [eapply mem_grows_trans; [exact G1|exact G2]|].
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A2]|]. zsub. }
  split. { intros j Hj. assert (C1 : cellA M1 (chp + 4 * Z.of_nat j) 4 (nth j ws 0)).
           { unfold M1. apply cell_w4s_nth; [lia|lia|exact Hj|]. intros jj Hjj. destruct (Cws jj Hjj) as [R _]. lia. }
           pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hj'. ztr. }
  unfold M2. split; zcell.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_clsgfa_lock : forall regs (M rom : word -> option byte) (raw : word) (sp st c chp n spb ris qris : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 1295832 -> getr regs 11 = Z_to_bv 64 st -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 13 = Z_to_bv 64 chp -> getr regs 14 = Z_to_bv 64 n ->
  0x696000 + 128 <= sp -> sp < 2 ^ 47 -> 1 <= c <= 31 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> 0 <= ris -> ris + 128 * 64 < 2 ^ 47 -> ris = 128 * qris ->
  ris + 128 * c + 128 <= sp - 128 -> 0 <= st < 2 ^ 64 -> 0 <= chp < 2 ^ 64 -> 0 <= n < 2 ^ 64 ->
  wrA M (sp - 128) 128 -> wrA M (ris + 128 * c) 128 ->
  cellA M (1295832 + 32) 8 spb -> cellA M (1295832 + 48) 8 ris -> cellA M (ris + 128 * c) 8 0 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x5758c : word) M rom) (mkst regs' (0x576dc : word) M' rom)
    /\ getr regs' 2 = Z_to_bv 64 (sp - 128) /\ getr regs' 8 = Z_to_bv 64 (ris + 128 * c) /\ getr regs' 9 = Z_to_bv 64 1295832
    /\ getr regs' 10 = Z_to_bv 64 (ris + 128 * c + 8) /\ getr regs' 11 = Z_to_bv 64 st /\ getr regs' 12 = Z_to_bv 64 c /\ getr regs' 13 = Z_to_bv 64 chp
    /\ getr regs' 14 = Z_to_bv 64 n /\ getr regs' 19 = Z_to_bv 64 (2 ^ 61) /\ getr regs' 20 = Z_to_bv 64 (spb + c * 2 ^ 32 + 3758096384)
    /\ getr regs' 3 = getr regs 3 /\ getr regs' 4 = getr regs 4
    /\ mem_grows M M' /\ art_agree [(sp - 128, 128); (ris + 128 * c, 8)] M M'
    /\ art_gfa_fcells M' sp raw (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22)
                      (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
    /\ cellA M' (ris + 128 * c) 8 (2 ^ 60).
Proof.
  intros regs M rom raw sp st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 IMG Hsp' Hc Hspb Hspb' Hris Hris' Eris Hr' Hst Hchp Hn W Wr Cspb Cris Cmx.
  pose proof (art_gfa_lock_fn regs M rom raw sp 1295832 st c chp n spb ris qris H1 H2 H10 H11 H12 H13 H14 ltac:(lia) ltac:(lia) IMG ltac:(lia) ltac:(lia) Hc Hspb Hspb' Hris Hris' Eris
                ltac:(unfold apart; lia) Hst Hchp Hn W Wr Cspb Cris Cmx) as RUN.
  match type of RUN with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN; set (M1 := MM) in RUN end.
  exists r1, M1. split; [exact RUN|].
  split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|].
  split; [unfold r1; gres; exact H11|]. split; [unfold r1; gres; exact H12|]. split; [unfold r1; gres; exact H13|]. split; [unfold r1; gres; exact H14|].
  split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|]. split; [unfold r1; gres; reflexivity|].
  split; [unfold M1, art_gfa_frame; zgrows|].
  split. { unfold M1, art_gfa_frame. eapply art_agree_sub; [zagree|]. zsub. }
  split. { pose proof (art_gfa_fcells_frame M sp raw regs ltac:(lia) ltac:(lia)) as F.
           assert (AW : art_agree [(ris + 128 * c, 8)] (art_gfa_frame M sp raw regs) M1). { unfold M1. eapply art_agree_sub; [zagree|]. zsub. }
           eapply (art_gfa_fcells_tr [(ris + 128 * c, 8)]); [exact AW|zgap|lia|lia|exact F]. }
  unfold M1. apply cell_Wn_hit; [lia|cbn; lia].
Qed.
End FPX.
