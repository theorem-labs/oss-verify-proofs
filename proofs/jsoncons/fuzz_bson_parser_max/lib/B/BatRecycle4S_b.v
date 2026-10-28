(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatFree1_b BatCellEx_b BatCls_b BatSecAllocPost_b
     BatRecycle1_b BatRecycle2C_b BatRecycle3_b BatRecycle4_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Abbreviation wokA := (wok AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
Definition art_cbr_sec_fp (sp t parr idx last mb ms : Z) : list (Z * Z) :=
  [ (sp - 80, 80); (t + 2800 + 40, 16) ] ++ art_secd_fp sp t parr idx last mb ms.

(* [comment removed for export] *)
Lemma art_sec_scan : forall HI t ctx parr bl idx mb ms m,
  art_sec_geo HI t ctx parr bl -> nth_error bl idx = Some (mb, ms) -> mb <= m < mb + ms -> art_gbb_scan m 0 (map fst bl) = mb.
Proof.
  intros HI t ctx parr bl idx mb ms m (_ & _ & _ & _ & _ & _ & GB & GD) Hnth Hm.
  pose proof (nth_error_In _ _ Hnth) as Hin.
  destruct (GB _ Hin) as (_ & _ & _ & Hmb & _). cbn [fst snd] in Hmb.
  apply art_gbb_scan_is.
  - left. apply in_map_iff. exists (mb, ms). split; [reflexivity|exact Hin].
  - lia.
  - lia.
  - intros ch Hch Hle. apply in_map_iff in Hch. destruct Hch as (b' & <- & Hin').
    destruct (In_nth_error _ _ Hin') as (j & Hj).
    destruct (Nat.eq_dec idx j) as [->|NE].
    + rewrite Hnth in Hj. injection Hj as <-. cbn. lia.
    + pose proof (GD idx j (mb, ms) b' Hnth Hj NE) as Ap. destruct (GB _ Hin') as (_ & _ & Hs & _). unfold apart in Ap. cbn [fst snd] in Ap. lia.
Qed.

(* [comment removed for export] *)
Lemma art_sec_cells_tr : forall W (M M' : word -> option byte) HI t ctx parr bl,
  art_sec_geo HI t ctx parr bl -> HI < 2 ^ 47 -> mem_grows M M' -> art_agree W M M' ->
  art_gap W 0x13c618 616 -> cellA M' (0x13c618 + 616) 4 0 -> art_gap W parr (8 * Z.of_nat (length bl)) -> (forall b, In b bl -> art_gap W (fst b) 32) ->
  art_sec_cells M parr bl -> art_sec_cells M' parr bl.
Proof.
  intros W M M' HI t ctx parr bl (Gp1 & Gp2 & Gp3 & _ & _ & _ & GB & _) HHI G A G0 CL GP GBk (C1 & C2 & C3 & _ & WP & CB).
  unfold art_sec_cells.
  split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G0|lia|cbn; lia]|lia|cbn; lia|exact C1]. }
  split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G0|lia|cbn; lia]|lia|cbn; lia|exact C2]. }
  split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact G0|lia|cbn; lia]|lia|cbn; lia|exact C3]. }
  split; [exact CL|]. split; [eapply wr_grows; [exact G|exact WP]|].
  intros j b Hj. destruct (CB j b Hj) as (B1 & B2 & B3 & B4 & B5 & B6).
  pose proof (nth_error_In _ _ Hj) as Hin. destruct (GB _ Hin) as (_ & _ & Hs & Hb0 & Hb1 & _).
  assert (Hjl : (j < length bl)%nat) by (apply nth_error_Some; rewrite Hj; discriminate).
  pose proof (proj1 (Nat2Z.inj_lt _ _) Hjl) as Hjl'.
  split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact GP|lia|cbn; lia]|lia|cbn; lia|exact B1]. }
  split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact (GBk b Hin)|lia|cbn; lia]|lia|cbn; lia|exact B2]. }
  split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact (GBk b Hin)|lia|cbn; lia]|lia|cbn; lia|exact B3]. }
  split. { apply (art_cell_tr W M M' _ _ _ A); [eapply art_gap_sub; [exact (GBk b Hin)|lia|cbn; lia]|lia|cbn; lia|exact B4]. }
  split; [eapply wr_grows; [exact G|exact B5]|eapply wr_grows; [exact G|exact B6]].
Qed.

Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

#[using="Type"] Theorem art_cbr_sec_aruns : forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
    (sp HI tp key tsd ctx t cb spb parr mb ms m b1 n f1 f2 : Z) (bl : list (Z * Z)) (idx : nat),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 cb -> getr regs 11 = Z_to_bv 64 m ->
  kHighMemBeg <= HI -> HI <= sp - 96 -> sp < 2 ^ 47 -> wrA M (sp - 96) 96 -> 0 <= cb < 2 ^ 64 ->
  0x696000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> cellA M (1295832 + 32) 8 spb ->
  nth_error bl idx = Some (mb, ms) -> art_sec_cells M parr bl -> art_sec_geo HI t ctx parr bl -> apart mb ms spb (2 ^ 37) ->
  mb + 4096 <= m -> m + 16 <= mb + ms -> 0 <= b1 < 256 -> 0 <= n < 2 ^ 32 -> cellA M m 4 (3 + 256 * b1) -> cellA M (m + 4) 4 n ->
  art_layout M -> art_tsd M tp key tsd ctx t ->
  4096 <= t -> t + 4096 <= HI -> appmem t 4096 -> (t + 4096 <= 0x10000 \/ 0x696000 <= t) -> wrA M t 4096 ->
  4096 <= ctx -> ctx + 4096 <= HI -> appmem ctx 4096 -> (ctx + 4096 <= 0x10000 \/ 0x696000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x661b28 <= tp - 88 -> tp + 8 <= 0x696000 -> 0x661b28 <= tsd -> tsd + 1024 <= 0x696000 ->
  cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 -> cellA M 0x137500 8 1 -> cellA M (0x1d1768 + 144) 8 0 ->
  cellA M (t + 2800 + 40) 8 f1 -> cellA M (t + 2800 + 48) 8 f2 ->
  art_evok_list EVOK log (art_flush_events mb ms ++ [AMunmap mb ms]) ->
  (forall regs' (M' : word -> option byte),
     getr regs' 1 = raw -> getr regs' 2 = Z_to_bv 64 sp ->
     (forall r : reg, In r [3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
     art_agree (art_cbr_sec_fp sp t parr (Z.of_nat idx) (fst (nth (length bl - 1) bl (0, 0))) mb ms) M M' ->
     (forall x : word, mb <= U x < mb + ms -> M' x = None) ->
     (forall x : word, SB + mb / 8 <= U x < SB + mb / 8 + ms / 8 -> M' x = Some (Z_to_bv 8 0)) ->
     (forall a k, 0 <= a -> a + k < 2 ^ 64 -> apart mb ms a k -> wrA M a k -> wrA M' a k) ->
     art_sec_cells M' parr (art_swap_remove (0, 0) idx bl) ->
     Q (log ++ art_flush_events mb ms ++ [AMunmap mb ms]) (mkst regs' raw M' rom)) ->
  aruns ASEGS EVOK GR Q log (mkst regs (0x548f4 : word) M rom).
Proof.
  intros Q log regs M rom raw sp HI tp key tsd ctx t cb spb parr mb ms m b1 n f1 f2 bl idx
    H1 Hret H2 H4 H10 H11 HHI0 HHI Hsp' W Hcb Hspb Hspb' Cspb Hnth SC GEO Abk Hm1 Hm2 Hb1 Hn Chw Cn LAY TSD Ht Ht' Apt Gti Wt Hctx Hctx' Apc Gci Atc
    Htp Htp' Htsd Htsd' Cpc Cpg Cgot Cmm Cf1 Cf2 EV K.
  unfold kHighMemBeg in HHI0.
  pose proof GEO as (Gp1 & Gp2 & Gp3 & Gp4 & Apt' & Apc' & GB & GD).
  pose proof (nth_error_In _ _ Hnth) as Hin.
  destruct (GB _ Hin) as (Hmb4k & Hms4k & Hmb0 & Hmb1 & Hmb2 & Hmb3 & Abp & Abt & Abc). cbn [fst snd] in Hmb4k, Hms4k, Hmb0, Hmb1, Hmb2, Hmb3, Abp, Abt, Abc.
  assert (Hmb4 : 0 <= mb) by lia.
  assert (Hlen1 : 1 <= Z.of_nat (length bl)). { assert ((idx < length bl)%nat) by (apply nth_error_Some; rewrite Hnth; discriminate). lia. }
  pose proof TSD as (_ & _ & _ & _ & _ & _ & _ & Hkey & _).
  pose proof SC as (S1 & S2 & S3 & S4 & SWP & SB_).
  destruct (SB_ idx (mb, ms) Hnth) as (B1 & B2 & B3 & B4 & B5 & B6). cbn [fst snd] in B1, B2, B3, B4, B5, B6.
  assert (At_i : apart t 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; lia). clear Gti.
  assert (Ac_i : apart ctx 4096 0x10000 (0x696000 - 0x10000)) by (unfold apart; lia). clear Gci.
  assert (Hsec : m < spb \/ spb + 2 ^ 37 <= m) by (unfold apart in Abk; lia).
  assert (Hsech : mb + 4096 < spb \/ spb + 2 ^ 37 <= mb + 4096) by (unfold apart in Abk; lia).
  (* [comment removed for export] *)
  destruct (art_cbr_sa regs M rom raw sp cb m spb H1 H2 H10 H11 ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_sub; [exact W|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]) Hcb ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hspb Hspb' Hsec Cspb)
    as (r1 & RUN1 & A1 & A2 & A8 & A9 & A19 & A20 & A10 & A11 & AK).
  destruct (art_f48_facts M sp raw regs ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (G01 & AG01).
  destruct (art_f48_cells M sp raw regs ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (E1 & E8 & E9 & E18 & E19 & E20).
  set (M1 := art_f48 M sp raw regs) in *. clearbody M1.
  assert (T1 : forall a (k : nat) v, apart a (Z.of_nat k) (sp - 48) 48 -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M1 a k v).
  { intros a k v Ap Ha Hk C. apply (art_cell_tr _ M M1 a k v AG01); [cbn [art_gap fst snd]; split; [exact Ap|exact I]|exact Ha|exact Hk|exact C]. }
  (* [comment removed for export] *)
  assert (Lchs : length (map fst bl) = length bl) by apply length_map.
  assert (Cchs : forall j, (j < length (map fst bl))%nat -> 0 <= nth j (map fst bl) 0 < 2 ^ 64 /\ cellA M1 (parr + 8 * Z.of_nat j) 8 (nth j (map fst bl) 0)).
  { intros j Hj. rewrite Lchs in Hj.
    assert (En : nth j (map fst bl) 0 = fst (nth j bl (0, 0))) by (exact (map_nth fst bl (0, 0) j)). rewrite En.
    pose proof (nth_error_nth' bl (0, 0) Hj) as Hj'. pose proof (nth_error_In _ _ Hj') as Hinj.
    destruct (GB _ Hinj) as (_ & _ & Hs & Hb0 & Hb1' & _). destruct (SB_ j _ Hj') as (X1 & _).
    pose proof (proj1 (Nat2Z.inj_lt _ _) Hj) as Hjz.
    split; [clear - Hb0 Hb1' Hs HHI Hsp'; lia|]. apply T1; [unfold apart; cbn; clear - Hjz Gp2 HHI; lia|clear - Gp1; lia|cbn; clear - Hjz Gp2 HHI Hsp'; lia|exact X1]. }
  destruct (art_gbb_run (map fst bl) r1 M1 rom (0x5496c : bv 64)%bv (sp - 48) HI m parr mb mb ms A1 ltac:(unfold ret_ok; bveq) A2 A10 A11
              ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G01|]; eapply wr_sub; [exact W|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)])
              ltac:(rewrite Lchs; clear - Hlen1; lia) ltac:(rewrite Lchs; exact Gp3) Gp1 ltac:(rewrite Lchs; exact Gp2) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))
              ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S4]) ltac:(rewrite Lchs; apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S3]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S2]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S1])
              Cchs ltac:(symmetry; apply (art_sec_scan HI t ctx parr bl idx mb ms m GEO Hnth); (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hmb4k
              ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact B2]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact B3]) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)))
    as (r2 & RUN2 & B10 & B2' & BK).
  destruct (art_gbb_mem_facts M1 (sp - 48) (0x5496c : bv 64)%bv r1 ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (G12 & AG12 & CL2).
  set (M2 := art_gbb_mem M1 (sp - 48) (0x5496c : bv 64)%bv r1) in *. clearbody M2.
  replace (sp - 48 - 32) with (sp - 80) in AG12 by (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia).
  assert (G02 : mem_grows M M2) by (eapply mem_grows_trans; [exact G01|exact G12]).
  assert (AG02 : art_agree [(sp - 48, 48); (sp - 80, 32); (0x13c618 + 616, 4)] M M2).
  { eapply art_agree_sub; [eapply art_agree_trans; [exact AG01|exact AG12]|]. intros z Hz H. exact H. }
  (* [comment removed for export] *)
  assert (T02 : forall a (k : nat) v, art_gap [(sp - 48, 48); (sp - 80, 32); (0x13c618 + 616, 4)] a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M2 a k v).
  { intros a k v Gp Ha Hk C. apply (art_cell_tr _ M M2 a k v AG02 Gp Ha Hk C). }
  destruct (art_cbr_sb r2 M2 rom spb (mb + 4096) B10 ltac:(rewrite BK by inl; exact A19) ltac:(rewrite BK by inl; exact A20) Hspb Hspb' ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hsech
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cspb]))
    as (r3 & RUN3 & C18 & CK).
  (* [comment removed for export] *)
  pose proof (art_cell_norm _ _ _ _ Cf1) as Cf1n. pose proof (art_mod64_range f1) as Hf1n.
  pose proof (art_cell_norm _ _ _ _ Cf2) as Cf2n. pose proof (art_mod64_range f2) as Hf2n.
  assert (Chi : cellA M (m + 2) 2 0).
  { destruct (cell4_split M m (3 + 256 * b1) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Chw) as (_ & _ & X). replace ((3 + 256 * b1) / 65536) with 0 in X by (symmetry; apply Z.div_small; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)). exact X. }
  assert (TSD2 : art_tsd M2 tp key tsd ctx t).
  { apply (art_tsd_tr _ M M2 tp key tsd ctx t AG02); [| | | |exact TSD]; cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ac_i; unfold apart in *; cbn in *; lia)]. }
  destruct (art_cbr_stats r3 M2 rom (sp - 48) HI tp key tsd ctx t m n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64)
              ltac:(rewrite CK by inl; exact B2')
              ltac:(rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H4)
              ltac:(rewrite CK by inl; rewrite BK by inl; exact A9)
              ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G02|]; eapply wr_sub; [exact W|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)])
              TSD2 Ht Ht' ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G02|exact Wt])
              ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hn Hf1n Hf2n
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Chi])
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cn])
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cf1n])
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cf2n]))
    as (r4 & RUN4 & DK).
  destruct (art_cbr_stats_mem_facts M2 (sp - 48) t n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (G23 & AG23).
  set (M3 := art_cbr_stats_mem M2 (sp - 48) t n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64)) in *. clearbody M3.
  replace (sp - 48 - 32) with (sp - 80) in AG23 by (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia).
  assert (G03 : mem_grows M M3) by (eapply mem_grows_trans; [exact G02|exact G23]).
  assert (AG03 : art_agree [(sp - 48, 48); (sp - 80, 32); (0x13c618 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] M M3).
  { eapply art_agree_sub; [eapply art_agree_trans; [exact AG02|exact AG23]|]. intros z Hz H. exact H. }
  assert (AG13 : art_agree [(sp - 80, 32); (0x13c618 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] M1 M3).
  { eapply art_agree_sub; [eapply art_agree_trans; [exact AG12|exact AG23]|]. intros z Hz H. exact H. }
  (* [comment removed for export] *)
  assert (TF : forall a v, sp - 48 <= a -> a + 8 <= sp -> cellA M1 a 8 v -> cellA M3 a 8 v).
  { intros a v Ha Ha' C. apply (art_cell_tr _ M1 M3 a 8 v AG13); [|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)|exact C].
    cbn [art_gap fst snd]. repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)]. }
  assert (T03 : forall a (k : nat) v, art_gap [(sp - 48, 48); (sp - 80, 32); (0x13c618 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] a (Z.of_nat k) ->
                  0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M3 a k v).
  { intros a k v Gp Ha Hk C. apply (art_cell_tr _ M M3 a k v AG03 Gp Ha Hk C). }
  pose proof (bv_unsigned_in_range 64 (getr regs 8)) as Q8r. pose proof (bv_unsigned_in_range 64 (getr regs 9)) as Q9r. pose proof (bv_unsigned_in_range 64 (getr regs 18)) as Q18r.
  pose proof (bv_unsigned_in_range 64 (getr regs 19)) as Q19r. pose proof (bv_unsigned_in_range 64 (getr regs 20)) as Q20r.
  change (bv_modulus 64) with (2 ^ 64) in Q8r, Q9r, Q18r, Q19r, Q20r.
  destruct (art_cbr_tails r4 M3 rom raw sp spb (mb + 4096) (U (getr regs 8)) (U (getr regs 9)) (U (getr regs 18)) (U (getr regs 19)) (U (getr regs 20))
              ltac:(rewrite DK by inl; rewrite CK by inl; exact B2')
              ltac:(rewrite DK by inl; exact C18)
              ltac:(rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; exact A19)
              ltac:(rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; exact A20)
              ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hspb Hspb' ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hsech
              ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cspb])
              ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E1]) ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E8]) ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E9])
              ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E18]) ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E19]) ltac:(apply TF; [(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact E20]))
    as (r5 & RUN5 & V1 & V2 & V10 & V11 & V12 & V8 & V9 & V18 & V19 & V20 & VK).
  (* [comment removed for export] *)
  eapply ar_steps.
  { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|exact RUN5]. }
  assert (SC3 : art_sec_cells M3 parr bl).
  { apply (art_sec_cells_tr _ M M3 HI t ctx parr bl GEO ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) G03 AG03); [| | | |exact SC].
    - cbn [art_gap fst snd]. repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)].
    - apply (art_cell_tr _ M2 M3 _ _ _ AG23); [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact CL2].
    - cbn [art_gap fst snd]. repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Apt'; unfold apart in *; cbn in *; lia)].
    - intros b Hb. destruct (GB _ Hb) as (_ & _ & Hs & Hb0 & Hb1' & _ & _ & Hbt & _).
      cbn [art_gap fst snd]. repeat split; first [exact I|(clear - Hs Hb0 Hb1' Hbt HHI Hsp' Ht Ht'; unfold apart in *; cbn in *; lia)]. }
  assert (LAY3 : art_layout M3).
  { apply (art_layout_tr _ M M3 AG03); [| | |exact LAY]; cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]. }
  assert (TSD3 : art_tsd M3 tp key tsd ctx t).
  { apply (art_tsd_tr _ M M3 tp key tsd ctx t AG03); [| | | |exact TSD]; cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i Ac_i Atc; unfold apart in *; cbn in *; lia)]. }
  apply (art_secd_aruns EVOK GR Q log r5 M3 rom raw sp HI tp key tsd ctx t parr mb ms bl idx V1 Hret V2
           ltac:(rewrite VK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H4) V10 V11 V12
           ltac:(unfold kHighMemBeg; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) HHI Hsp' ltac:(eapply wr_grows; [exact G03|exact W]) Hnth SC3 GEO LAY3 TSD3 Ht Ht' Apt
           ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)) ltac:(eapply wr_grows; [exact G03|exact Wt]) Hctx Hctx' Apc ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ac_i; unfold apart in *; cbn in *; lia)) Atc Htp Htp' Htsd Htsd'
           ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cpc])
           ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cpg])
           ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cgot])
           ltac:(apply T03; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cmm]) EV).
  intros r6 M6 F1 F2 FK FA FN FS FW FSC.
  apply (K r6 M6 F1 F2).
  - intros x Hx. rewrite (FK x Hx). cbn [In] in Hx.
    destruct Hx as [<-|Hx]. { rewrite VK by inl. rewrite DK by inl. rewrite CK by inl. rewrite BK by inl. apply AK. inl. }
    destruct Hx as [<-|Hx]. { rewrite VK by inl. rewrite DK by inl. rewrite CK by inl. rewrite BK by inl. apply AK. inl. }
    destruct Hx as [<-|Hx]. { rewrite V8. apply Z_to_bv_bv_unsigned. }
    destruct Hx as [<-|Hx]. { rewrite V9. apply Z_to_bv_bv_unsigned. }
    destruct Hx as [<-|Hx]. { rewrite V18. apply Z_to_bv_bv_unsigned. }
    destruct Hx as [<-|Hx]. { rewrite V19. apply Z_to_bv_bv_unsigned. }
    destruct Hx as [<-|Hx]. { rewrite V20. apply Z_to_bv_bv_unsigned. }
    repeat (destruct Hx as [<-|Hx]; [rewrite VK by inl; rewrite DK by inl; rewrite CK by inl; rewrite BK by inl; apply AK; inl|]).
    destruct Hx.
  - eapply art_agree_sub; [eapply art_agree_trans; [exact AG03|exact FA]|]. unfold art_cbr_sec_fp, art_secd_fp.
    intros z Hz H. cbn [art_out app fst snd] in H |- *. repeat split; (clear - H Hz; lia).
  - exact FN.
  - exact FS.
  - intros a k Ha Hk Ap Wa. apply (FW a k Ha Hk Ap). eapply wr_grows; [exact G03|exact Wa].
  - exact FSC.
Qed.
End Spec.
