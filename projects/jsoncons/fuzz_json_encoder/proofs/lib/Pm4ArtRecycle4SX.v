(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_json_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac Pm4ArtLeaf Pm4ArtAllocG Pm4ArtPoison ArtRuns ArtRunsMem Pm4ArtFp Pm4ArtFree1 Pm4ArtCellEx Pm4ArtCls Pm4ArtSecAllocPost
     Pm4ArtRecycle1 Pm4ArtRecycle2C Pm4ArtRecycle3 Pm4ArtRecycle4 Pm4ArtRecycle4S Pm4ArtBig Pm4_code_5c000_5d000.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation cellA := (cell Asan.M.loaded_segments).
#[local] Abbreviation wrA := (wr Asan.M.loaded_segments).
#[local] Abbreviation wokA := (wok Asan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)


Section Spec.
Variable EVOK : list aev -> aev -> Prop.
Variable GR : list aev -> (word -> option byte) -> Z -> Z -> Prop.
Context {fx : PropExec.FPState}.

Lemma art_cbr_statsX : forall regs (M rom : word -> option byte) (sp1 HI tp key tsd ctx t m nl nh n f1 f2 : Z),
  getr regs 2 = Z_to_bv 64 sp1 -> getr regs 4 = Z_to_bv 64 tp -> getr regs 9 = Z_to_bv 64 m ->
  0x6c0000 <= HI -> HI <= sp1 - 32 -> sp1 < 2 ^ 64 -> wrA M (sp1 - 32) 32 ->
  art_tsd M tp key tsd ctx t -> 4096 <= t -> t + 4096 <= HI -> tp + 8 <= HI -> tsd + 8 * key + 8 <= HI -> ctx + 160 <= HI -> wrA M t 4096 ->
  16 <= m -> m + 16 <= HI -> 0 <= nl < 2 ^ 32 -> 0 <= nh < 2 ^ 16 -> n = nl + 2 ^ 32 * nh -> 0 <= f1 < 2 ^ 64 -> 0 <= f2 < 2 ^ 64 ->
  cellA M (m + 2) 2 nh -> cellA M (m + 4) 4 nl -> cellA M (t + 2800 + 40) 8 f1 -> cellA M (t + 2800 + 48) 8 f2 ->
  exists regs', msteps ASEGS (mkst regs (0x5cca4 : word) M rom) (mkst regs' (0x5ccd0 : word) (art_cbr_stats_mem M sp1 t n f1 f2) rom)
    /\ (forall r : reg, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r).
Proof.
  intros regs M rom sp1 HI tp key tsd ctx t m nl nh n f1 f2 H2 H4 H9 HHI Hsp Hsp' W TSD Ht Ht' Htp Htsd Hctx Wt Hm Hm' Hnl Hnh En Hf1 Hf2 Chi Cn C40 C48.
  pose proof TSD as (_ & _ & _ & _ & _ & R).
  eexists. split.
  { stepn F_5cc54 D_5cc54.
    zcall (art_thread_stats_fn _ _ _ (0x5cca8 : word) sp1 tp key tsd ctx t).
    match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chi' : cellA X (m + 2) 2 nh) by zcell; assert (Cn' : cellA X (m + 4) 4 nl) by zcell;
      assert (C40' : cellA X (t + 2800 + 40) 8 f1) by zcell; assert (C48' : cellA X (t + 2800 + 48) 8 f2) by zcell; assert (Wt' : wrA X t 4096) by zwr end.
    zlhu4 F_5cc58 D_5cc58 (m + 2) Chi'.
    zlwu F_5cc5c D_5cc5c (m + 4) Cn'.
    zld F_5cc60 D_5cc60 (t + 2800 + 48) C48'.
    zld F_5cc64 D_5cc64 (t + 2800 + 40) C40'.
    stepn F_5cc68 D_5cc68. rwH. try rewrite art_zb_slli by lia.
    stepn F_5cc6c D_5cc6c. rwH. rewrite (art_zb_or4 (nh * 2 ^ 32) nl) by lia. rewrite art_lor_hi_lo by lia. replace (nh * 2 ^ 32 + nl) with n by lia.
    zstep F_5cc70 D_5cc70. zstep F_5cc74 D_5cc74.
    zsd F_5cc78 D_5cc78 (t + 2800 + 40) (f1 + 1) ltac:(zwok').
    zsd F_5cc7c D_5cc7c (t + 2800 + 48) (n + f2) ltac:(zwok').
    unfold art_cbr_stats_mem. apply mst_refl. }
  intros r Hr. cbn [In] in Hr. repeat (destruct Hr as [<-|Hr]; [gres; first [reflexivity | symmetry; exact H2]|]). destruct Hr.
Qed.

Theorem art_cbr_sec_arunsX : forall (Q : list aev -> machine_state -> Prop) (log : list aev) regs (M rom : word -> option byte) (raw : word)
    (sp HI tp key tsd ctx t cb spb parr mb ms m b1 nl nh n f1 f2 : Z) (bl : list (Z * Z)) (idx : nat),
  getr regs 1 = raw -> ret_ok raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 4 = Z_to_bv 64 tp -> getr regs 10 = Z_to_bv 64 cb -> getr regs 11 = Z_to_bv 64 m ->
  kHighMemBeg <= HI -> HI <= sp - 96 -> sp < 2 ^ 47 -> wrA M (sp - 96) 96 -> 0 <= cb < 2 ^ 64 ->
  0x6c0000 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> cellA M (1468568 + 32) 8 spb ->
  nth_error bl idx = Some (mb, ms) -> art_sec_cells M parr bl -> art_sec_geo HI t ctx parr bl -> apart mb ms spb (2 ^ 37) ->
  mb + 4096 <= m -> m + 16 <= mb + ms -> 0 <= b1 < 256 -> 0 <= nl < 2 ^ 32 -> 0 <= nh < 2 ^ 7 -> n = nl + 2 ^ 32 * nh -> 0 <= n < 2 ^ 39 ->
  cellA M m 4 (3 + 256 * b1 + 65536 * nh) -> cellA M (m + 4) 4 nl ->
  art_layout M -> art_tsd M tp key tsd ctx t ->
  4096 <= t -> t + 4096 <= HI -> appmem t 4096 -> (t + 4096 <= 0x10000 \/ 0x6c0000 <= t) -> wrA M t 4096 ->
  4096 <= ctx -> ctx + 4096 <= HI -> appmem ctx 4096 -> (ctx + 4096 <= 0x10000 \/ 0x6c0000 <= ctx) -> apart t 4096 ctx 4096 ->
  0x68bde8 <= tp - 88 -> tp + 8 <= 0x6c0000 -> 0x68bde8 <= tsd -> tsd + 1024 <= 0x6c0000 ->
  cellA M 0x160bf8 8 0x1f99a0 -> cellA M 0x1f99a0 8 4096 -> cellA M 0x160c58 8 1 -> cellA M (0x1fba28 + 144) 8 0 ->
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
  aruns ASEGS EVOK GR Q log (mkst regs (0x5cb38 : word) M rom).
Proof.
  intros Q log regs M rom raw sp HI tp key tsd ctx t cb spb parr mb ms m b1 nl nh n f1 f2 bl idx
    H1 Hret H2 H4 H10 H11 HHI0 HHI Hsp' W Hcb Hspb Hspb' Cspb Hnth SC GEO Abk Hm1 Hm2 Hb1 Hnl Hnh Enhl Hn Chw Cn LAY TSD Ht Ht' Apt Gti Wt Hctx Hctx' Apc Gci Atc
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
  assert (At_i : apart t 4096 0x10000 (0x6c0000 - 0x10000)) by (unfold apart; lia). clear Gti.
  assert (Ac_i : apart ctx 4096 0x10000 (0x6c0000 - 0x10000)) by (unfold apart; lia). clear Gci.
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
  destruct (art_gbb_run (map fst bl) r1 M1 rom (0x5cbb0 : bv 64)%bv (sp - 48) HI m parr mb mb ms A1 ltac:(unfold ret_ok; bveq) A2 A10 A11
              ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G01|]; eapply wr_sub; [exact W|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)])
              ltac:(rewrite Lchs; clear - Hlen1; lia) ltac:(rewrite Lchs; exact Gp3) Gp1 ltac:(rewrite Lchs; exact Gp2) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))
              ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S4]) ltac:(rewrite Lchs; apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S3]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S2]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact S1])
              Cchs ltac:(symmetry; apply (art_sec_scan HI t ctx parr bl idx mb ms m GEO Hnth); (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hmb4k
              ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact B2]) ltac:(apply T1; [(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact B3]) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)))
    as (r2 & RUN2 & B10 & B2' & BK).
  destruct (art_gbb_mem_facts M1 (sp - 48) (0x5cbb0 : bv 64)%bv r1 ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (G12 & AG12 & CL2).
  set (M2 := art_gbb_mem M1 (sp - 48) (0x5cbb0 : bv 64)%bv r1) in *. clearbody M2.
  replace (sp - 48 - 32) with (sp - 80) in AG12 by (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia).
  assert (G02 : mem_grows M M2) by (eapply mem_grows_trans; [exact G01|exact G12]).
  assert (AG02 : art_agree [(sp - 48, 48); (sp - 80, 32); (0x1668d8 + 616, 4)] M M2).
  { eapply art_agree_sub; [eapply art_agree_trans; [exact AG01|exact AG12]|]. intros z Hz H. exact H. }
  (* [comment removed for export] *)
  assert (T02 : forall a (k : nat) v, art_gap [(sp - 48, 48); (sp - 80, 32); (0x1668d8 + 616, 4)] a (Z.of_nat k) -> 0 <= a -> a + Z.of_nat k < 2 ^ 64 -> cellA M a k v -> cellA M2 a k v).
  { intros a k v Gp Ha Hk C. apply (art_cell_tr _ M M2 a k v AG02 Gp Ha Hk C). }
  destruct (art_cbr_sb r2 M2 rom spb (mb + 4096) B10 ltac:(rewrite BK by inl; exact A19) ltac:(rewrite BK by inl; exact A20) Hspb Hspb' ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hsech
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cspb]))
    as (r3 & RUN3 & C18 & CK).
  (* [comment removed for export] *)
  pose proof (art_cell_norm _ _ _ _ Cf1) as Cf1n. pose proof (art_mod64_range f1) as Hf1n.
  pose proof (art_cell_norm _ _ _ _ Cf2) as Cf2n. pose proof (art_mod64_range f2) as Hf2n.
  assert (Chi : cellA M (m + 2) 2 nh).
  { destruct (cell4_split M m (3 + 256 * b1 + 65536 * nh) ltac:((clear - HHI0 HHI Hsp' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hnh Hn; lia)) ltac:((clear - HHI0 HHI Hsp' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hnh Hn; lia)) ltac:((clear - HHI0 HHI Hsp' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hnh Hn; lia)) Chw) as (_ & _ & X).
    replace ((3 + 256 * b1 + 65536 * nh) / 65536) with nh in X; [exact X|]. replace (3 + 256 * b1 + 65536 * nh) with ((3 + 256 * b1) + nh * 65536) by lia. rewrite Z_div_plus_full by lia. rewrite Z.div_small by lia. lia. }
  assert (TSD2 : art_tsd M2 tp key tsd ctx t).
  { apply (art_tsd_tr _ M M2 tp key tsd ctx t AG02); [| | | |exact TSD]; cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ac_i; unfold apart in *; cbn in *; lia)]. }
  destruct (art_cbr_statsX r3 M2 rom (sp - 48) HI tp key tsd ctx t m nl nh n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64)
              ltac:(rewrite CK by inl; exact B2')
              ltac:(rewrite CK by inl; rewrite BK by inl; rewrite AK by inl; exact H4)
              ltac:(rewrite CK by inl; rewrite BK by inl; exact A9)
              ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G02|]; eapply wr_sub; [exact W|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)])
              TSD2 Ht Ht' ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:(eapply wr_grows; [exact G02|exact Wt])
              ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) Hnl ltac:(clear - Hnh; lia) Enhl Hf1n Hf2n
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Chi])
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(unfold apart; cbn; clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cn])
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cf1n])
              ltac:(apply T02; [cbn [art_gap fst snd]; repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 At_i; unfold apart in *; cbn in *; lia)]|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)|exact Cf2n]))
    as (r4 & RUN4 & DK).
  destruct (art_cbr_stats_mem_facts M2 (sp - 48) t n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia)) ltac:((clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia))) as (G23 & AG23).
  set (M3 := art_cbr_stats_mem M2 (sp - 48) t n (f1 mod 2 ^ 64) (f2 mod 2 ^ 64)) in *. clearbody M3.
  replace (sp - 48 - 32) with (sp - 80) in AG23 by (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1; lia).
  assert (G03 : mem_grows M M3) by (eapply mem_grows_trans; [exact G02|exact G23]).
  assert (AG03 : art_agree [(sp - 48, 48); (sp - 80, 32); (0x1668d8 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] M M3).
  { eapply art_agree_sub; [eapply art_agree_trans; [exact AG02|exact AG23]|]. intros z Hz H. exact H. }
  assert (AG13 : art_agree [(sp - 80, 32); (0x1668d8 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] M1 M3).
  { eapply art_agree_sub; [eapply art_agree_trans; [exact AG12|exact AG23]|]. intros z Hz H. exact H. }
  (* [comment removed for export] *)
  assert (TF : forall a v, sp - 48 <= a -> a + 8 <= sp -> cellA M1 a 8 v -> cellA M3 a 8 v).
  { intros a v Ha Ha' C. apply (art_cell_tr _ M1 M3 a 8 v AG13); [|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)|cbn; (clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)|exact C].
    cbn [art_gap fst snd]. repeat split; first [exact I|(clear - HHI0 HHI Hsp' Hcb Hspb Hspb' Hmb0 Hmb1 Hmb2 Hmb3 Hmb4 Hm1 Hm2 Hb1 Hn Ht Ht' Hctx Hctx' Htp Htp' Htsd Htsd' Gp1 Gp2 Gp3 Hkey Hlen1 Ha Ha'; unfold apart in *; cbn in *; lia)]. }
  assert (T03 : forall a (k : nat) v, art_gap [(sp - 48, 48); (sp - 80, 32); (0x1668d8 + 616, 4); (sp - 80, 32); (t + 2800 + 40, 16)] a (Z.of_nat k) ->
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
