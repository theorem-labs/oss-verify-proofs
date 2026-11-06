(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMaly5g ATransp ABudget ASecComb ASecImg ASecB1 ASecB2 ASecB3.

Module ASecB4.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict Refund EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMalmys.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AMaly5g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ATransp ABudget ASecComb ASecImg ASecB1 ASecB2 ASecB3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaly5g.AMal5j7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecImg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize in *.

(* [comment removed for export] *)
Definition INST : Z := al_instance AL_pasan.
Lemma INST_val : INST = 0xb1d58. Proof. reflexivity. Qed.
Lemma LMA_INST : ASecComb.LMA = INST + 64. Proof. reflexivity. Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition const_noinst (c : Z * list byte) : bool :=
  ((fst c + Z.of_nat (length (snd c)) <=? 0xb1d58 + 112) || (0xb1d58 + 129 <=? fst c)) &&
  ((fst c + Z.of_nat (length (snd c)) <=? 0xb1d58 + 136) || (0xb1d58 + 681 <=? fst c)) &&
  ((fst c + Z.of_nat (length (snd c)) <=? 0xb1d58 + 704) || (0xb1d58 + 720 <=? fst c)).
Lemma pa_consts_noinst : forallb const_noinst pa_consts = true.
Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition C0_ADDR : Z := 0xb2001.
(* [comment removed for export] *)
Definition const_c0 (c : Z * list byte) : bool :=
  negb (fst c =? C0_ADDR) || ((Nat.eqb (length (snd c)) 3) && forallb (fun b : byte => bv_unsigned b =? 0) (snd c)).
Lemma pa_consts_c0 : forallb const_c0 pa_consts = true.
Proof. vm_compute. reflexivity. Qed.
Lemma pa_consts_noinst2 : forallb (fun c => (fst c =? C0_ADDR) || ((fst c + Z.of_nat (length (snd c)) <=? 0xb1d58 + 681) || (0xb1d58 + 684 <=? fst c))) pa_consts = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition sec_W (slo shi thr mb ms pa nch pahi n0 f0 : Z) : list (Z * Z) :=
  [ (slo, shi); (thr + off_th_stats, thr + off_th_stats + 112);
    (INST + off_sec_n_reserved, INST + off_sec_chunks_sorted + 1); (INST + off_sec_stat_n_allocs, INST + off_sec_mutex + 4);
    (INST + off_global_stats + 16, INST + off_global_stats + 32);
    (pa + 8 * nch, pahi);
    (0x187288, 0x5d72a8); (n0, n0 + kDepotNodesBlock); (f0, f0 + kStackStoreBlockBytes);
    (mb, mb + ms); (sh mb, sh mb + ms / 8) ].

(* [comment removed for export] *)
Section BM.
Context {Clg : Ceiling}.
Lemma bm_app_range : forall A i b s, WF A -> nth_error (big_maps A) i = Some (b, s) -> (i <> 0 /\ i <> 1 /\ i <> 2 /\ i <> 3)%nat ->
  app_rangeA AL_pasan b s /\ b + s <= alloc_ceiling.
Proof.
  intros A i b s W Hn Hi.
  (first [ pose proof ((place_facts A W)) as dR_1; dand13 dR_1 as Pthr Pctx Pn0 Pf0 Pfs Pitab Pm64k Pgvec Pdvec Pm11 Pdtls Ppa _ | pose proof (place_facts A W) as (Pthr & Pctx & Pn0 & Pf0 & Pfs & Pitab & Pm64k & Pgvec & Pdvec & Pm11 & Pdtls & Ppa & _) ]).
  cbv zeta in Pthr, Pctx, Pn0, Pf0, Pfs, Pitab, Pm64k, Pgvec, Pdvec, Pm11, Pdtls, Ppa.
  destruct (Nat.lt_ge_cases i 15) as [L|GE].
  - (first [ pose proof ((bm_nth_fixed A)) as dR_2; dand15 dR_2 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    unfold a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_itab, a_m64k in *.
    Ltac pick E Hn P := rewrite Hn in E; injection E as -> ->; exact (conj (proj1 P) (proj1 (proj2 P))).
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]];
      [ lia | lia | lia | lia | pick E4 Hn Pthr | pick E5 Hn Pctx | pick E6 Hn Pfs | pick E7 Hn Pn0 | pick E8 Hn Pf0 | pick E9 Hn Pitab
      | pick E10 Hn Pm64k | pick E11 Hn Pgvec | pick E12 Hn Pdvec | pick E13 Hn Pm11 | pick E14 Hn Pdtls | lia ].
  - assert (HS : exists sc, nth_error (sr_chunks (a_sec A)) (i - 15) = Some sc /\ (b, s) = (cs_map sc, map_size (cs_n sc))).
    { unfold big_maps, big_maps_ in Hn. rewrite nth_error_app2 in Hn by (cbn; lia). cbn [length] in Hn.
      rewrite nth_error_map in Hn. destruct (nth_error (sr_chunks (a_sec A)) (i - 15)) as [sc|] eqn:E; [| discriminate].
      exists sc. split; [reflexivity|]. cbn in Hn. injection Hn as <- <-. reflexivity. }
    (first [ dex1 HS as sc; destruct HS as [Hsc E] | dand3 HS as sc Hsc E | destruct HS as (sc & Hsc & E) ]).
    injection E as -> ->. (first [ pose proof ((sec_chunk_bounds A sc W (nth_error_In _ _ Hsc))) as dR_4; dand5 dR_4 as _ _ B3 B4 _ | pose proof (sec_chunk_bounds A sc W (nth_error_In _ _ Hsc)) as (_ & _ & B3 & B4 & _) ]). exact (conj B3 B4).
Qed.
End BM.

Section ReprPost.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (n : Z) (mbw : word) (key : list Z) (slo shi : Z) (v' : mem) (pahi : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : kMaxPrimaryUser < n < 2^30 + 1.
  Hypothesis CEIL : alloc_ceiling <= slo.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Notation mb := (bv_unsigned mbw).
  Local Notation ms := (map_size n).
  Hypothesis MBA : mb mod 4096 = 0.
  Hypothesis MB0 : 0 < mb.
  Hypothesis MBC : mb + ms <= alloc_ceiling.
  Hypothesis RF : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) mbw (wz ms) = true.
  (* [comment removed for export] *)
  Local Notation nch := (Z.of_nat (length (sr_chunks (a_sec A)))).
  Local Notation pa := (p_pa (a_pl A)).
  Hypothesis PAHI : pahi = pa + 8 * nch + 8 \/ (nch = 0 /\ pahi = pa + 8 * kChunksBlockCount).

  Local Notation v := (aview_of (pa_hull A) m).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation n0 := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation D := (a_depot A).
  Local Notation AB := (sec_alloc_beg mb).
  Local Notation u := (sec_user_beg mb).
  Local Notation A' := (secA A mb n key kChunksBlockCount).
  Local Notation W := (sec_W slo shi thr mb ms pa nch pahi n0 f0).

  (* [comment removed for export] *)
  Hypothesis MU : munch W v v'.
  Hypothesis WMv : wmono rsegs v v'.
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let R : @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (ai_repr _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (conj WF0 R). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  #[using="NR"] Lemma NRu : 64512 < n < 2^30 + 1. Proof. pose proof NR as X. unfold kMaxPrimaryUser in X. exact X. Qed.
  #[using="MB0 NR mbw A"] Lemma MSP : 0 < ms < 2^40.
  Proof. pose proof NR as NR'. unfold kMaxPrimaryUser in NR'. pose proof (map_size_ge n ltac:(lia)). pose proof (map_size_le n ltac:(lia)). lia. Qed.
  Lemma MSA : ms mod 4096 = 0.
  Proof. exact (map_size_page n). Qed.

  (* [comment removed for export] *)
  #[using="RF MB0 NR AI md m Clg"] Lemma APART : forall i b s, nth_error (big_maps A) i = Some (b, s) -> b + s <= mb \/ mb + ms <= b.
  Proof. pose proof MSP. intros i b s Hi. eapply (gf_APART A m md mbw ms); eassumption. Qed.
  #[using="RF MBC MB0 MBA NR AI md m A"] Lemma AOBJ : aobj mb ms.
  Proof. pose proof MSP. pose proof MSA. eapply (gf_aobj A m md mbw ms); eassumption. Qed.
  #[using="RF MBC MB0 MBA NR AI md m A Clg"] Lemma LIN : 4096 <= mb /\ (mb + ms <= 0x10000 \/ 0x60a000 <= mb) /\ (mb + ms <= kLowShadowMapBeg \/ kHighMemBeg <= mb).
  Proof. pose proof MSP. pose proof MSA. eapply (gf_lin A m md mbw ms); eassumption. Qed.
  (* [comment removed for export] *)
  #[using="RF MBC MB0 MBA NR AI md"] Lemma VIEW_NONE : forall x, mb <= x < mb + ms -> v (wz x) = None.
  Proof. pose proof MSP. pose proof MSA. intros x. eapply (gf_view_none A m md mbw ms); eassumption. Qed.
  #[using="RF MBC MB0 MBA NR AI md m"] Lemma SHADOW : forall z, sh mb <= z < sh mb + ms / 8 -> ghost_hs_ (a_pl A) z /\ ~ heap_shadow A z.
  Proof. pose proof MSP. pose proof MSA. intros z. eapply (gf_shadow A m md mbw ms); eassumption. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="CE WF0 PAHI RF MBC MB0 MBA CEIL NR AI md m"] Lemma GEO :
    4096 <= thr /\ thr + 4096 <= alloc_ceiling /\ kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling /\
    4096 <= mb /\ (mb + ms <= 0x10000 \/ 0x60a000 <= mb) /\ (mb + ms <= kLowShadowMapBeg \/ kHighMemBeg <= mb) /\ mb + ms <= alloc_ceiling /\
    mb = 4096 * (mb / 4096) /\ ms = 4096 * (ms / 4096) /\ n + 4096 <= ms /\ ms < 2^31 /\
    AB = mb + 4096 /\ u = mb + 6144 /\ u + n <= AB + needed_size2 n /\ AB + needed_size2 n <= mb + ms /\
    4096 <= n0 /\ n0 + kDepotNodesBlock <= alloc_ceiling /\ 4096 <= f0 /\ f0 + kStackStoreBlockBytes <= alloc_ceiling /\
    4096 <= pa /\ pa + kPtrArrayReserve <= alloc_ceiling /\ 0 <= nch < kChunksBlockCount /\ pa + 8 * nch + 8 <= pahi <= pa + 8 * kChunksBlockCount /\
    alloc_ceiling <= slo /\
    0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.
  Proof.
    (first [ pose proof ((hit_place A m md AI)) as dR_5; dand6 dR_5 as Pthr PthrC _ Pctx PctxC _ | pose proof (hit_place A m md AI) as (Pthr & PthrC & _ & Pctx & PctxC & _) ]). (first [ pose proof ((hit_sep A m md AI)) as dR_6; dand13 dR_6 as _ _ _ _ _ _ _ _ _ N1 N2 F1 F2 | pose proof (hit_sep A m md AI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & F1 & F2) ]).
    (first [ pose proof ((sec_pa A m md AI)) as dR_7; dand3 dR_7 as Ppa1 Ppa2 Ppa3 | pose proof (sec_pa A m md AI) as (Ppa1 & Ppa2 & Ppa3) ]). (first [ pose proof ((sec_nch A m md AI)) as dR_8; dand4 dR_8 as NC1 NC2 NC3 NC4 | pose proof (sec_nch A m md AI) as (NC1 & NC2 & NC3 & NC4) ]).
    (first [ pose proof ((sb_facts A WF0)) as dR_9; dand5 dR_9 as _ SBA HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & SBA & HB6 & RSB & SCE) ]).
    (first [ pose proof (LIN) as dR_10; dand3 dR_10 as L1 L2 L3 | pose proof LIN as (L1 & L2 & L3) ]). pose proof MSP as MP. pose proof MSA as MA.
    pose proof (sec_user_end_fits mb n ltac:(lia)) as [U1 U2].
    pose proof NR as NR'. unfold kMaxPrimaryUser in NR'. pose proof (map_size_ge n ltac:(lia)) as MG. pose proof (map_size_le n ltac:(lia)) as ML.
    apply aobj_facts in Pthr. apply aobj_facts in N1. apply aobj_facts in F1. apply aobj_facts in Ppa1.
    pose proof (Z_div_mod_eq_full mb 4096). pose proof (Z_div_mod_eq_full ms 4096).
    unfold sec_alloc_beg, sec_user_beg, a_sb, p_sb in *. kung_all.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; lia.
  Qed.
  #[using="RF MBC MB0 MBA NR AI md m"] Lemma GEOP : aobj thr 4096 /\ aobj n0 kDepotNodesBlock /\ aobj f0 kStackStoreBlockBytes /\ aobj pa kPtrArrayReserve /\ aobj mb ms.
  Proof.
    pose proof (hit_place A m md AI) as (Pthr & _). (first [ pose proof ((hit_sep A m md AI)) as dR_11; dand13 dR_11 as _ _ _ _ _ _ _ _ _ N1 _ F1 _ | pose proof (hit_sep A m md AI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & F1 & _) ]).
    pose proof (sec_pa A m md AI) as (Ppa1 & _). exact (conj Pthr (conj N1 (conj F1 (conj Ppa1 AOBJ)))).
  Qed.
  Ltac geop := let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in let Gp := fresh "Gp" in let Gm := fresh "Gm" in
    (first [ pose proof (GEOP) as dR_12; dand5 dR_12 as Gt Gn Gf Gp Gm | pose proof GEOP as (Gt & Gn & Gf & Gp & Gm) ]); aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf; aobj_lin1 Gp; aobj_lin1 Gm.

  (* [comment removed for export] *)
  #[using="MU"] Lemma AGW : forall a, 0 <= a < 2^64 -> outside W a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha Ho. apply MU. rewrite unsigned_lit by lia. exact Ho. Qed.

  #[using="CE WF0 PAHI RF MBC MB0 MBA CEIL NR AI md m Clg"] Lemma W_shape : forall a,
    ~ (slo <= a < shi) -> ~ (thr + 2800 <= a < thr + 2912) ->
    ~ (INST + 112 <= a < INST + 129) -> ~ (INST + 136 <= a < INST + 684) -> ~ (INST + 704 <= a < INST + 720) ->
    ~ (pa + 8 * nch <= a < pahi) ->
    ~ (0x187288 <= a < 0x5d72a8) -> ~ (n0 <= a < n0 + 0x100000) -> ~ (f0 <= a < f0 + 0x800000) ->
    ~ (mb <= a < mb + ms) -> ~ (sh mb <= a < sh mb + ms / 8) ->
    outside W a.
  Proof.
    intros a X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11. pose proof GEO as G.
    unfold sec_W. rewrite INST_val in *. cbn [app outside]. unfold off_th_stats, off_th_unwinding, off_sec_n_reserved, off_sec_chunks_sorted, off_sec_stat_n_allocs, off_sec_mutex, off_global_stats.
    kung_all.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ assumption
      | match goal with X : _ |- _ => lazymatch type of X with ~ _ => idtac | _ <> _ => idtac end; clear - X G; lia end ].
  Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m A Clg"] Lemma SHG : sh mb = mb / 8 + kShadowOffset /\ mb = 8 * (mb / 8) /\ ms = 8 * (ms / 8) /\ sh AB = sh mb + 512 /\ sh u = sh mb + 768 /\
              sh (mb + ms) = sh mb + ms / 8 /\ 0x7fff8000 + 512 <= sh mb /\ (sh mb + ms / 8 <= kShadowGapBeg \/ kHighShadowMapBeg <= sh mb) /\ sh mb + ms / 8 <= kHighMemBeg.
  Proof.
    pose proof GEO as G. unfold sec_alloc_beg, sec_user_beg, sh in *. kung_all.
    pose proof (Z_div_mod_eq_full mb 8). pose proof (Z_div_mod_eq_full ms 8). pose proof (Z.mod_pos_bound mb 8 ltac:(lia)). pose proof (Z.mod_pos_bound ms 8 ltac:(lia)).
    assert (M1 : mb mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MBA]).
    assert (M2 : ms mod 8 = 0) by (apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSA]).
    replace ((mb + 4096) / 8) with (mb / 8 + 512) by lia. replace ((mb + 4096 + 2048) / 8) with (mb / 8 + 768) by lia.
    replace ((mb + ms) / 8) with (mb / 8 + ms / 8) by lia.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; lia.
  Qed.
  Ltac negs_clear := repeat match goal with X' : ~ _ |- _ => clear X' | X' : _ <> _ |- _ => clear X' end.
  Ltac wnlia := first [ assumption | negs_clear; lia
                     | match goal with X : _ |- _ => lazymatch type of X with ~ _ => idtac | _ <> _ => idtac end;
                         generalize X; negs_clear; intros ?; lia end ].
  Ltac wtac := apply W_shape; unfold kShadowOffset; wnlia.
  (* [comment removed for export] *)
  Ltac prep := pose proof GEO as G; pose proof SHG as SG; geop; kung_all.
  Ltac wsolve H H' G SG Gt Gp Gn Gf Gm := apply W_shape;
    [ clear - H H' G | clear - H H' G Gt | clear - H H' G | clear - H H' G | clear - H H' G | clear - H H' G Gp | clear - H H' G
    | clear - H H' G Gn | clear - H H' G Gf | clear - H H' G Gm SG | clear - H H' G Gm SG ]; rewrite ?INST_val; kung_all; unfold sh in *; lia.

  (* [comment removed for export] *)
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> ~ (0x187288 <= a < 0x5d72a8) ->
    ~ (INST + 112 <= a < INST + 129) -> ~ (INST + 136 <= a < INST + 684) -> ~ (INST + 704 <= a < INST + 720) ->
    v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha Hd X1 X2 X3. prep. rewrite INST_val in *. apply AGW; [lia|].
    apply W_shape; [ clear - Ha G | clear - Ha G Gt | clear - X1 | clear - X2 | clear - X3 | clear - Ha G Gp | clear - Hd
    | clear - Ha G Gn | clear - Ha G Gf | clear - Ha G Gm SG | clear - Ha G Gm SG ]; rewrite ?INST_val; kung_all; unfold sh in *; lia.
  Qed.
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGshared : forall a, cl_shared LPA a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a H. cbn [cl_shared LPA] in H. unfold pa_shared in H. apply AGimg; rewrite ?INST_val; lia. Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGconst : forall cst a, In cst (cl_consts LPA) -> fst cst <= a < fst cst + Z.of_nat (length (snd cst)) ->
    ~ (INST + 681 <= a < INST + 684) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros cst a Hin Ha NMX. cbn [cl_consts LPA] in Hin.
    pose proof pa_consts_nodepot as OK. rewrite forallb_forall in OK. specialize (OK cst Hin). unfold const_nodepot in OK.
    apply orb_true_iff in OK. rewrite !Z.leb_le in OK.
    pose proof pa_consts_noinst as OK2. rewrite forallb_forall in OK2. specialize (OK2 cst Hin). unfold const_noinst in OK2.
    rewrite !andb_true_iff, !orb_true_iff, !Z.leb_le in OK2. rewrite INST_val in *.
    destruct (pa_consts_where cst a Hin Ha) as [S|[S|S]].
    - unfold pa_shared in S. apply AGimg; rewrite ?INST_val; clear - S Ha OK OK2 NMX; lia.
    - (* [comment removed for export] *)
      unfold pa_image_shadow, sh in S. replace (0x10000 / 8) with 8192 in S by reflexivity. replace (0x60a000 / 8) with 791552 in S by reflexivity.
      prep. apply AGW; [lia|]. wsolve S S G SG Gt Gp Gn Gf Gm.
    - pose proof (pa_static_low a S). unfold pa_static in S. apply AGimg; rewrite ?INST_val; clear - S Ha OK OK2 NMX H; lia.
  Qed.
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGcstat : forall a, cfoot_stat a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. unfold cfoot_stat in Ha. cbv zeta in Ha.
    cbn [al_instance al_kHighMemEnd_var al_kMidMemBeg_var al_kMidMemEnd_var al_malloc_context_size al_can_poison_memory al_page_size_cache
         al_may_return_null al_rss_limit_exceeded al_dying_flag al_malloc_hooks AL_pasan] in Ha.
    unfold off_primary_reserved_base, off_primary_reserved_size, off_SpaceBeg, off_release_interval, off_RegionInfo_ptr, off_PremappedHeap,
      off_sec_page_size, off_sec_chunks, off_sec_ptr_array_base, off_sec_ptr_array_size, off_q_max_size, off_q_min_size, off_q_max_cache_size,
      off_max_user_malloc, off_min_redzone, off_max_redzone, off_alloc_dealloc_mismatch in Ha.
    apply AGimg; rewrite ?INST_val; lia.
  Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGmap : forall i b s a, nth_error (big_maps A) i = Some (b, s) -> (i <> 0 /\ i <> 1 /\ i <> 2 /\ i <> 3 /\ i <> 4 /\ i <> 7 /\ i <> 8)%nat ->
    b <= a < b + s -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros i b s a Hn Hi Ha. prep. (first [ pose proof ((bm_nth_fixed A)) as dR_13; dand10 dR_13 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    pose proof (APART _ _ _ Hn) as Dm.
    pose proof (bm_sep A i 1 _ _ _ _ WF0 Hn E1 ltac:(clear - Hi; lia)) as D1. pose proof (bm_sep A i 4 _ _ _ _ WF0 Hn E4 ltac:(clear - Hi; lia)) as D4.   (* [comment removed for export] *)
    pose proof (bm_sep A i 7 _ _ _ _ WF0 Hn E7 ltac:(clear - Hi; lia)) as D7. pose proof (bm_sep A i 8 _ _ _ _ WF0 Hn E8 ltac:(clear - Hi; lia)) as D8.
    pose proof (bm_sep A i 2 _ _ _ _ WF0 Hn E2 ltac:(clear - Hi; lia)) as D2. pose proof (bm_sep A i 3 _ _ _ _ WF0 Hn E3 ltac:(clear - Hi; lia)) as D3.
    unfold a_pa, a_thr, a_nodes0, a_frames0 in *.
    destruct (wfM A WF0) as [_ BND]. (first [ pose proof ((BND b s (nth_error_In _ _ Hn))) as dR_14; dand3 dR_14 as B1 B2 B3 | destruct (BND b s (nth_error_In _ _ Hn)) as (B1 & B2 & B3) ]).
    (* [comment removed for export] *)
    pose proof (bm_app_range A i b s WF0 Hn ltac:(clear - Hi; lia)) as [OFF1 OFF2]. apply app_facts in OFF1.
    apply AGW; [clear - Ha OFF1 OFF2 G; lia|].
    apply W_shape; [ clear - Ha OFF1 OFF2 G | clear - Ha D4 | clear - Ha OFF1 | clear - Ha OFF1 | clear - Ha OFF1 | clear - Ha D1 G | clear - Ha OFF1
    | clear - Ha D7 | clear - Ha D8 | clear - Ha Dm | clear - Ha OFF1 OFF2 B1 G Gm SG ]; rewrite ?INST_val; kung_all; unfold sh in *; lia.
  Qed.
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGthr : forall a, thr <= a < thr + 2800 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. prep. (first [ pose proof ((hit_sep A m md AI)) as dR_15; dand8 dR_15 as S1 _ _ _ _ N0t F0t _ | pose proof (hit_sep A m md AI) as (S1 & _ & _ & _ & _ & N0t & F0t & _) ]). unfold apart in S1, N0t, F0t.
    (first [ pose proof ((bm_nth_fixed A)) as dR_16; dand6 dR_16 as _ E1 _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _ & _ & E4 & _) ]). pose proof (bm_sep A 4 1 _ _ _ _ WF0 E4 E1 ltac:(lia)) as D. pose proof (APART _ _ _ E4) as Dm.
    unfold a_pa, a_thr, a_nodes0, a_frames0 in *. apply AGW; [lia|].
    apply W_shape; [ clear - Ha G Gt | clear - Ha | clear - Ha G Gt | clear - Ha G Gt | clear - Ha G Gt | clear - Ha D G | clear - Ha G Gt
    | clear - Ha N0t | clear - Ha F0t | clear - Ha Dm | clear - Ha G Gt Gm SG ]; rewrite ?INST_val; kung_all; unfold sh in *; lia.
  Qed.
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGthr2 : forall a, thr + 2912 <= a < thr + 4096 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. prep. (first [ pose proof ((hit_sep A m md AI)) as dR_17; dand8 dR_17 as S1 _ _ _ _ N0t F0t _ | pose proof (hit_sep A m md AI) as (S1 & _ & _ & _ & _ & N0t & F0t & _) ]). unfold apart in S1, N0t, F0t.
    (first [ pose proof ((bm_nth_fixed A)) as dR_18; dand6 dR_18 as _ E1 _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _ & _ & E4 & _) ]). pose proof (bm_sep A 4 1 _ _ _ _ WF0 E4 E1 ltac:(lia)) as D. pose proof (APART _ _ _ E4) as Dm.
    unfold a_pa, a_thr, a_nodes0, a_frames0 in *. apply AGW; [lia|].
    apply W_shape; [ clear - Ha G Gt | clear - Ha | clear - Ha G Gt | clear - Ha G Gt | clear - Ha G Gt | clear - Ha D G | clear - Ha G Gt
    | clear - Ha N0t | clear - Ha F0t | clear - Ha Dm | clear - Ha G Gt Gm SG ]; rewrite ?INST_val; kung_all; unfold sh in *; lia.
  Qed.
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGprim : forall a, sb <= a < sb + kSpaceSize + 4096 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. prep. (first [ pose proof ((bm_nth_fixed A)) as dR_19; dand10 dR_19 as E0 E1 _ _ E4 _ _ E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & _ & _ & E4 & _ & _ & E7 & E8 & _) ]).
    pose proof (bm_sep A 0 1 _ _ _ _ WF0 E0 E1 ltac:(lia)) as D1. pose proof (bm_sep A 0 4 _ _ _ _ WF0 E0 E4 ltac:(lia)) as D4.
    pose proof (bm_sep A 0 7 _ _ _ _ WF0 E0 E7 ltac:(lia)) as D7. pose proof (bm_sep A 0 8 _ _ _ _ WF0 E0 E8 ltac:(lia)) as D8.
    pose proof (APART _ _ _ E0) as Dm.
    (first [ pose proof ((sb_facts A WF0)) as dR_20; dand5 dR_20 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold a_b6, a_pa, a_sb, a_thr, a_nodes0, a_frames0 in *. apply AGW; [lia|].
    apply W_shape; [ clear - Ha G SCE | clear - Ha D4 HB6 RSB | clear - Ha G | clear - Ha G | clear - Ha G | clear - Ha D1 G HB6 RSB | clear - Ha G
    | clear - Ha D7 HB6 RSB | clear - Ha D8 HB6 RSB | clear - Ha Dm HB6 RSB | clear - Ha G SG SCE ]; rewrite ?INST_val; kung_all; unfold sh in *; lia.
  Qed.
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGpa : forall a, pa <= a < pa + 8 * nch -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. prep. (first [ pose proof ((bm_nth_fixed A)) as dR_21; dand10 dR_21 as _ E1 _ _ E4 _ _ E7 E8 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _ & _ & E4 & _ & _ & E7 & E8 & _) ]).
    pose proof (bm_sep A 1 4 _ _ _ _ WF0 E1 E4 ltac:(lia)) as D4. pose proof (bm_sep A 1 7 _ _ _ _ WF0 E1 E7 ltac:(lia)) as D7. pose proof (bm_sep A 1 8 _ _ _ _ WF0 E1 E8 ltac:(lia)) as D8.
    pose proof (APART _ _ _ E1) as Dm. unfold a_pa, a_thr, a_nodes0, a_frames0 in *. apply AGW; [lia|].
    apply W_shape; [ clear - Ha G Gp | clear - Ha D4 G | clear - Ha G Gp | clear - Ha G Gp | clear - Ha G Gp | clear - Ha | clear - Ha G Gp
    | clear - Ha D7 G | clear - Ha D8 G | clear - Ha Dm G | clear - Ha G Gp Gm SG ]; rewrite ?INST_val; kung_all; unfold sh in *; lia.
  Qed.
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGsec : forall sc a, In sc (sr_chunks (a_sec A)) -> cs_map sc <= a < cs_map sc + map_size (cs_n sc) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros sc a Hin Ha. apply In_nth_error' in Hin as [j Hj]. apply (AGmap _ _ _ a (bm_nth_sec A j sc Hj)); [lia| exact Ha].
  Qed.
  (* [comment removed for export] *)
  #[using="CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGhs : forall z, heap_shadow A z -> v' (Z_to_bv 64 z) = v (Z_to_bv 64 z).
  Proof.
    intros z Hz. pose proof (heap_shadow_range A z WF0 Hz) as ISM. unfold in_shadow_maps in ISM.
    assert (NS : ~ (sh mb <= z < sh mb + ms / 8)) by (intros X; exact (proj2 (SHADOW z X) Hz)). prep.
    apply AGW; [clear - ISM; lia|].
    apply W_shape; [ clear - ISM G | clear - ISM G Gt | clear - ISM | clear - ISM | clear - ISM | clear - ISM G Gp | clear - ISM
    | clear - ISM G Gn | clear - ISM G Gf | clear - ISM G Gm | clear - NS ]; rewrite ?INST_val; kung_all; unfold sh in *; lia.
  Qed.
  #[using="CE AR R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma AGcarved : forall ch a, carved A ch -> chunk_lo sb ch <= a < chunk_hi sb ch -> v' (wz a) = v (wz a).
  Proof.
    intros ch a C Ha. destruct ch as [[c' k']|[mb' n1]].
    - pose proof (carved_prim_where A v AR c' k' C) as X. cbn [chunk_lo chunk_hi alloc_beg] in Ha. change (a_sb A) with sb in X.
      apply AGprim. clear - X Ha. kung_all. lia.
    - unfold carved in C. cbn [chunk_lo chunk_hi] in Ha. exact (AGsec _ a C Ha).
  Qed.

  #[using="NN MB0 mbw"] Lemma mapped_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 -> mapped v a k -> mapped v' a k.
  Proof. intros a k H0 H1 H2 M i Hi. apply NN; [lia| lia| lia| exact (M i Hi)]. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Cells.
  Variables (md0 : mem) (b1' id : Z).
  Local Notation d := (n / 8).
  Local Notation e := (n mod 8).
  Local Notation dc := (n / 8 + Z.min (n mod 8) 1).
  Local Notation ru := ((ms - 4096) / 8).
  Hypothesis P_reg : rw_cells rsegs v' (ASecComb.LMA + 48) [C8 (wz kChunksBlockCount); C8 (wz (nch + 1)); C1 (Z_to_bv 8 0)].
  Hypothesis P_mtx : rw_cells rsegs v' (ASecComb.LMA + 616) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)].
  Hypothesis P_shdr : rw_cells rsegs v' mb [C8 (wz mb); C8 (wz ms); C8 (wz (needed_size2 n))].
  Hypothesis P_cidx : rw_cells rsegs v' (mb + 24) [C8 (wz nch)].
  Hypothesis P_slot : rw_cells rsegs v' (pa + 8 * nch) [C8 mbw].
  Hypothesis P_pamap : mapped v' pa (8 * kChunksBlockCount).
  Hypothesis P_mapall : mapped v' mb ms.
  Hypothesis B1R : 0 <= b1' < 256.
  Hypothesis B1M : Z.land b1' 0x7f = kHdrByte1Malloc.
  Hypothesis IDR : 0 <= id < 2^32.
  Hypothesis P_hdr : rw_cells rsegs v' (AB + 2032)
     [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1'); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
  Hypothesis P_lch : rw_cells rsegs v' AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + 2032))].
  Hypothesis P_sh512 : bytes_at rsegs v' (sh mb) (repeat (Z_to_bv 8 250) 512).
  Hypothesis P_shl : bytes_at rsegs v' (sh AB) (repeat (Z_to_bv 8 250) 256).
  Hypothesis P_shz : bytes_at rsegs v' (sh AB + 256) (repeat (Z_to_bv 8 0) (Z.to_nat d)).
  Hypothesis P_she : rw_cells rsegs v' (sh AB + 256 + d) [CB (Z.to_nat (Z.min e 1)) (repeat (Z_to_bv 8 e) (Z.to_nat (Z.min e 1)))].
  Hypothesis P_sht : bytes_at rsegs v' (sh AB + 256 + dc) (repeat (Z_to_bv 8 250) (Z.to_nat (ru - 256 - dc))).
  Hypothesis P_dr : depot_repL AL_pasan rsegs (fst (depot_putC D key)) n0 f0 md0.
  Hypothesis P_mu2 : forall a, depot_foot AL_pasan n0 f0 a -> v' (Z_to_bv 64 a) = md0 (Z_to_bv 64 a).

  (* [comment removed for export] *)
  Ltac trim := repeat match goal with H : _ /\ _ /\ _ |- _ => clear H | H : Forall _ _ |- _ => clear H | H : arepr _ _ _ _ _ |- _ => clear H
                                    | H : _ \/ _ |- _ => clear H end.
  Ltac leaf H AG :=
    lazymatch type of H with
    | u64_at _ _ _ _ => eapply u64_at_agree; [exact H|]; intros i__ Hi__; AG
    | u32_at _ _ _ _ => eapply u32_at_agree; [exact H|]; intros i__ Hi__; AG
    | u16_at _ _ _ _ => eapply u16_at_agree; [exact H|]; intros i__ Hi__; AG
    | u8_at _ _ _ _ => eapply u8_at_agree;  [exact H|]; AG
    | fill_at _ _ _ _ _ => eapply fill_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    | junk_at _ _ _ _ => eapply junk_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    end.

  (* [comment removed for export] *)
  #[using="IDR B1R id b1' CE WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md"] Lemma UNW_eq : v' (wz (thr + off_th_unwinding)) = v (wz (thr + off_th_unwinding)).
  Proof. apply AGthr2. unfold off_th_unwinding. lia. Qed.

  #[using="IDR B1R P_mtx id b1' CE AR R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma consts_P : consts_repr_ LPA AL_pasan (a_pl A) v'.
  Proof.
    pose proof GEO as G. (first [ pose proof ((hit_place A m md AI)) as dR_22; dand6 dR_22 as _ _ _ CT1 CT2 _ | pose proof (hit_place A m md AI) as (_ & _ & _ & CT1 & CT2 & _) ]). apply aobj_facts in CT1.
    (first [ pose proof ((place_facts A WF0)) as dR_23; dand12 dR_23 as _ _ _ _ _ _ _ _ _ _ Pdt _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pdt & _) ]). cbv zeta in Pdt. (first [ dand3 Pdt as Pdt PdtC _ | destruct Pdt as (Pdt & PdtC & _) ]). apply app_facts in Pdt.
    (first [ pose proof ((bm_nth_fixed A)) as dR_25; dand15 dR_25 as _ _ _ _ _ E5 _ _ _ _ _ _ _ _ E14 | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & E5 & _ & _ & _ & _ & _ & _ & _ & _ & E14) ]).
    apply (consts_P2 A v v' AR).
    - intros cst Hin. cbn [cl_consts LPA] in Hin.
      destruct (Z.eqb_spec (fst cst) C0_ADDR) as [E|NE].
      + right. (* [comment removed for export] *)
        pose proof pa_consts_c0 as OK. rewrite forallb_forall in OK. specialize (OK cst Hin). unfold const_c0 in OK.
        rewrite E, Z.eqb_refl in OK. cbn [negb orb] in OK. apply andb_true_iff in OK as [L3 Z3]. apply Nat.eqb_eq in L3.
        destruct cst as [ca bs]. cbn [fst snd] in *. subst ca. unfold C0_ADDR.
        destruct bs as [|x [|y [|z [|]]]]; cbn in L3; try lia. cbn [forallb] in Z3. rewrite !andb_true_iff in Z3. (first [ dand4 Z3 as Zx Zy Zz _ | destruct Z3 as (Zx & Zy & Zz & _) ]).
        apply Z.eqb_eq in Zx. apply Z.eqb_eq in Zy. apply Z.eqb_eq in Zz.
        destruct P_mtx as [[_ B] _]. cbn [cells_bytes cbytes] in B. change (ASecComb.LMA + 616) with (0xb2001 - 1) in B.
        change (Z_to_bv 8 0 :: Z_to_bv 8 0 :: le2 (Z_to_bv 64 0) ++ []) with ([Z_to_bv 8 0] ++ (Z_to_bv 8 0 :: le2 (Z_to_bv 64 0) ++ [])) in B.
        apply bytes_at_app in B as [_ B]. cbn [length Z.of_nat Pos.of_succ_nat] in B. replace (0xb2001 - 1 + 1) with 0xb2001 in B by lia.
        eapply bytes_at_as; [exact B|].
        cbn. repeat (first [reflexivity | apply (f_equal2 cons); [apply bv_eq; first [rewrite Zx | rewrite Zy | rewrite Zz]; vm_compute; reflexivity|]]).
      + left. intros a Ha. apply (AGconst cst a Hin Ha).
        pose proof pa_consts_noinst2 as OK. rewrite forallb_forall in OK. specialize (OK cst Hin). cbn beta in OK.
        apply orb_true_iff in OK as [OK|OK]; [exfalso; apply NE; apply Z.eqb_eq; exact OK|].
        apply orb_true_iff in OK. rewrite !Z.leb_le in OK. rewrite INST_val. clear - OK Ha. lia.
    - exact AGshared.
    - exact AGcstat.
    - intros a Ha. unfold cfoot_thr in Ha. destruct (Z.eq_dec a (thr + off_th_unwinding)) as [->|NT]; [exact UNW_eq|].
      apply AGthr. unfold off_th_context, off_th_stack_top, off_th_stack_bottom, off_th_stack_switching, off_th_unwinding in *. clear - Ha NT. lia.
    - intros a Ha. unfold cfoot_misc in Ha. pose proof TPV as TP. rewrite TP in Ha.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
      + apply (AGmap 5%nat _ _ a E5); [lia| unfold a_ctx; clear - Ha; lia].
      + apply (AGmap 5%nat _ _ a E5); [lia| unfold a_ctx; clear - Ha; lia].
      + apply AGimg; rewrite ?INST_val; clear - Ha; lia.
      + apply AGimg; rewrite ?INST_val; clear - Ha; lia.
      + apply AGimg; rewrite ?INST_val; clear - Ha; lia.
      + apply (AGmap 14%nat _ _ a E14); [lia| clear - Ha; lia].
  Qed.
  #[using="IDR B1R P_mtx id b1' CE R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma locks_P : locks_repr_ LPA AL_pasan (a_pl A) [] v'.
  Proof.
    pose proof (ar_locks _ _ _ _ _ R) as C. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    (first [ pose proof ((sb_facts A WF0)) as dR_27; dand5 dR_27 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold a_b6 in HB6, RSB.
    change (al_internal_alloc_inited AL_pasan) with 0x144e48 in *. change (al_instance AL_pasan) with INST in *.
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y]. unfold p_ri in *. change (p_sb (a_pl A)) with sb in *.
      split; [leaf X ltac:(apply AGprim; trim; unfold kRegionInfoSize, kSpaceSize in *; lia) | leaf Y ltac:(apply AGprim; trim; unfold kRegionInfoSize, kSpaceSize in *; lia)].
    - (first [ dand5 C as L1 L2 L3 L4 L5 | destruct C as (L1 & L2 & L3 & L4 & L5) ]). rewrite lockb_nil in *.
      split.
      { (* [comment removed for export] *)
        destruct P_mtx as [[_ B] _]. cbn [cells_bytes cbytes] in B.
        change (Z_to_bv 8 0 :: Z_to_bv 8 0 :: le2 (Z_to_bv 64 0) ++ []) with ([Z_to_bv 8 0] ++ (Z_to_bv 8 0 :: le2 (Z_to_bv 64 0) ++ [])) in B.
        apply bytes_at_app in B as [B _].
        unfold u8_at, off_sec_mutex. rewrite LMA_INST in B. replace (INST + 64 + 616) with (INST + 680) in B by lia. cbn [cl_segs LPA]. exact B. }
      unfold off_q_cache_mutex, off_q_recycle_mutex, off_fallback_mutex in *.
      split; [leaf L2 ltac:(apply AGimg; rewrite ?INST_val in *; lia)|].
      split; [leaf L3 ltac:(apply AGimg; rewrite ?INST_val in *; lia)|].
      split; [leaf L4 ltac:(apply AGimg; rewrite ?INST_val in *; lia)| leaf L5 ltac:(apply AGimg; rewrite ?INST_val in *; lia)].
  Qed.
  #[using="CE AR R WF0 NN MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma regions_P : forall c', 1 <= c' <= 30 -> region_repr_ LPA sb (a_reg A c') v' c'.
  Proof.
    intros c' Hc. apply (region_P A v v' AR NN c' Hc). intros a Ha. unfold rfoot in Ha.
    pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in RB. unfold region_info_addr, free_array_beg in Ha. change (p_sb (a_pl A)) with sb in *.
    apply AGprim. clear - Ha RB Hc. unfold kRegionInfoSize in *. kung_all. lia.
  Qed.
  #[using="CE AR R WF0 NN MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma cache_P : cache_repr_ LPA (a_pl A) (a_cache A) (a_cache_inited A) v'.
  Proof.
    apply (cache_P A v v' AR NN). intros c' Hc'. apply (cache_line_P A v v' AR NN (a_cache A) c' Hc' eq_refl).
    intros a Ha. offs_h Ha. cbv beta in Ha. apply AGthr. clear - Ha Hc'. unfold kPerClassSize in *. lia.
  Qed.
  #[using="CE AR R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma ia_P : ia_repr_ LPA AL_pasan (a_ia_inited A) v'.
  Proof.
    apply (ia_P A v v' AR). intros a Ha. unfold iafoot in Ha.
    cbn [al_internal_allocator_inst al_internal_alloc_inited AL_pasan] in Ha. apply AGimg; rewrite ?INST_val; clear - Ha; lia.
  Qed.
  #[using="IDR B1R id b1' CE AR R WF0 NN MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma fsbase_P : fs_base_ LPA (a_pl A) (a_fhint A) v'.
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_29; dand8 dR_29 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    apply (fsbase_P A v v' AR NN). intros a Ha. unfold a_fs in *. apply (AGmap 6%nat _ _ a E6); [lia| unfold kFakeFlagsOffset, kFakeStackBytes in *; clear - Ha; lia].
  Qed.
  #[using="IDR B1R id b1' CE AR R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma fsptrs_P : fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_30; dand8 dR_30 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    apply (fsptrs_P A v v' AR). intros a Ha. unfold a_fs in *. apply (AGmap 6%nat _ _ a E6); [lia| unfold kFakeFramesOffset, kFakeStackBytes in *; clear - Ha; lia].
  Qed.
  #[using="IDR B1R id b1' CE AR R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma fsflags_P : fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_31; dand8 dR_31 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]).
    apply (fsflags_P A v v' AR). intros a Ha. unfold a_fs in *. apply (AGmap 6%nat _ _ a E6); [lia| unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; clear - Ha; lia].
  Qed.
  #[using="AR R WF0 NN AI md m"] Lemma maps_P : maps_repr_ AL_pasan (a_pl A) v'.
  Proof. exact (maps_P A v v' AR NN). Qed.

  #[using="P_lch P_hdr IDR B1M B1R P_mapall id b1' CE AR R WF0 NN MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo md m Clg"] Lemma live_P : live_repr_ LPA sb (<[ u := LI (ChS (CS mb n)) n ]> (a_livemap A)) v'.
  Proof.
    intros u0 li Hl. pose proof GEO as G.
    destruct (decide (u0 = u)) as [->|NEu].
    - rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_chunk li_n chunk_lo chunk_hi]. pose proof NRu as NR'.
      pose proof (secondary_layout mb n ltac:(lia)) as SL. cbv zeta in SL.
      split; [|split].
      + unfold hdr_repr_. cbv zeta. cbn [user_of alloc_beg]. split.
        * exists id, b1'. split; [exact IDR|]. split; [exact B1R|]. split; [exact B1M|].
          unfold chunk_hdr_cells. cbn [ch_state ch_b1 ch_size ch_ctx]. unfold size_hi. rewrite (proj2 (proj2 (user_size_pos n ltac:(clear - NR'; lia))) ltac:(clear - NR'; lia)).
          rewrite Z.shiftr_div_pow2, Z.div_small by (clear - NR'; lia).
          replace (u - 16) with (AB + 2032) by (clear - G; lia). cbn [cl_segs LPA]. exact P_hdr.
        * intros _. destruct P_lch as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
          apply bytes_at_app in B as [B0 B1]. rewrite length_le8 in B1. unfold u64_at.
          split; [exact B0| replace (u - 16) with (AB + 2032) by (clear - G; lia); replace (AB + Z.of_nat 8) with (AB + 8) in B1 by lia; exact B1].
      + intros i Hi. replace (u + i) with (mb + (6144 + i)) by (clear - G; lia). apply P_mapall. clear - G Hi SL. lia.
      + intros i Hi. replace (mb + ms - mb) with ms in Hi by lia. exact (P_mapall i Hi).
    - rewrite lookup_insert_ne in Hl by congruence. apply (live_entry_P A v v' AR NN u0 li Hl).
      intros a Ha. exact (AGcarved _ a (known_carved A v AR _ _ (known_live A v AR u0 li Hl)) Ha).
  Qed.
  #[using="CE AR R WF0 NN MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo mbw n md m Clg"] Lemma quar_P : quarantine_repr_ LPA AL_pasan (a_pl A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    apply (quar_P A v v' AR NN).
    - intros a Ha. unfold off_th_qcache in Ha. apply AGthr. clear - Ha. lia.
    - intros a Ha. cbn [al_instance AL_pasan] in Ha. unfold off_q_cache_list_size in Ha. apply AGimg; rewrite ?INST_val; clear - Ha; lia.
    - intros b a Hb Ha. apply (AGcarved _ a (batch_carved A v AR b Hb)). cbn [chunk_lo chunk_hi alloc_beg].
      unfold batch_addr in Ha. rewrite class_size_24. exact Ha.
    - intros e a He Ha. exact (AGcarved _ a (known_carved A v AR _ _ (known_quar A v AR e He)) Ha).
  Qed.
  #[using="IDR B1R P_pamap P_slot P_cidx P_shdr P_reg id b1' CE R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo md m Clg"] Lemma sec_P : sec_repr_ LPA AL_pasan (a_pl A) (SR (sr_chunks (a_sec A) ++ [CS mb n]) kChunksBlockCount) v'.
  Proof.
    pose proof (ar_sec _ _ _ _ _ R) as C. pose proof GEO as G. unfold sec_repr_ in *. cbv zeta in *. cbn [sr_reserved sr_chunks] in *.
    change (al_instance AL_pasan) with INST in *. (first [ dand7 C as X1 X2 J1 J2 J3 CH M | destruct C as (X1 & X2 & J1 & J2 & J3 & CH & M) ]).
    destruct P_reg as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. rewrite LMA_INST in B.
    apply bytes_at_app in B as [BR B]. rewrite length_le8 in B. apply bytes_at_app in B as [BN BS]. rewrite length_le8 in BS.
    unfold off_sec_n_reserved, off_sec_n_chunks, off_sec_chunks_sorted, off_sec_stat_n_allocs, off_global_stats in *.
    split; [unfold u64_at; replace (INST + 112) with (INST + 64 + 48) by lia; exact BR|].
    split; [unfold u64_at; rewrite app_length; cbn [length]; replace (Z.of_nat (length (sr_chunks (a_sec A)) + 1)) with (nch + 1) by lia;
            replace (INST + 120) with (INST + 64 + 48 + Z.of_nat 8) by lia; exact BN|].
    split; [exists [Z_to_bv 8 0]; split; [reflexivity| replace (INST + 128) with (INST + 64 + 48 + Z.of_nat 8 + Z.of_nat 8) by lia; exact BS]|].
    (* [comment removed for export] *)
    split; [apply img_junk; rewrite ?INST_val; lia|].
    split; [apply img_junk; rewrite ?INST_val; lia|].
    split.
    - intros i sc E. destruct (nth_error_snoc_inv _ _ _ _ E) as [E'|[-> ->]].
      + (* [comment removed for export] *)
        destruct (CH i sc E') as [X Y]. pose proof (nth_error_In _ _ E') as Hin.
        assert (Z.of_nat i < nch) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E'; discriminate)); lia).
        split.
        * leaf X ltac:(apply AGpa; lia).
        * eapply rw_cells_agree; [exact Y|]. rewrite sec_hdr_size. intros j Hj. apply (AGsec sc); [exact Hin|].
          (first [ pose proof ((sec_chunk_bounds A sc WF0 Hin)) as dR_33; dand5 dR_33 as B1 _ _ _ B5 | pose proof (sec_chunk_bounds A sc WF0 Hin) as (B1 & _ & _ & _ & B5) ]). unfold kMaxPrimaryUser in B1.
          pose proof (needed_size2_secondary (cs_n sc) ltac:(unfold kMaxPrimaryUser; lia)). pose proof (rounded_size_ge (cs_n sc)). unfold kPageSize in *. lia.
      + (* [comment removed for export] *)
        cbn [cs_map cs_n]. split.
        * unfold u64_at. destruct P_slot as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
          eapply bytes_at_as; [exact B|]. rewrite Z_to_bv_bv_unsigned. reflexivity.
        * unfold sec_hdr_cells. cbn [sh_map_beg sh_map_size sh_size sh_chunk_idx].
          destruct P_shdr as [[W1 B1] WR1]. destruct P_cidx as [[W2 B2] WR2].
          split; [split; [exact (conj I (conj I (conj I (conj I I))))|]|].
          -- cbn [cells_bytes cbytes] in *. rewrite app_nil_r in *.
             replace (le8 (Z_to_bv 64 mb) ++ le8 (Z_to_bv 64 ms) ++ le8 (Z_to_bv 64 (needed_size2 n)) ++ le8 (Z_to_bv 64 nch))
               with ((le8 (Z_to_bv 64 mb) ++ le8 (Z_to_bv 64 ms) ++ le8 (Z_to_bv 64 (needed_size2 n))) ++ le8 (Z_to_bv 64 nch)) by (rewrite <- !app_assoc; reflexivity).
             apply bytes_at_app. split; [exact B1|]. rewrite !app_length, !length_le8. cbn [Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (mb + 24)%Z with (mb + 24) in B2 by lia. exact B2.
          -- cbn [cells_size csize Nat.add] in *. (first [ dand3 WR1 as W1a W1b WW1 | destruct WR1 as (W1a & W1b & WW1) ]). (first [ dand3 WR2 as W2a W2b WW2 | destruct WR2 as (W2a & W2b & WW2) ]).
             split; [exact W1a|]. split; [clear - W2b; lia|]. intros i Hi. destruct (Z_lt_le_dec i 24) as [L|GE].
             ++ apply WW1. lia.
             ++ replace (mb + i) with (mb + 24 + (i - 24)) by lia. apply WW2. lia.
    - exact P_pamap.
  Qed.
  #[using="P_mu2 P_dr md0"] Lemma depot_P : depot_repr_ LPA AL_pasan (a_pl A) (fst (depot_putC D key)) v'.
  Proof.
    unfold depot_repr_. cbn [depot_rep DepotRepL]. eapply depot_repL_agree; [exact P_dr|]. intros a Ha. exact (P_mu2 a Ha).
  Qed.
  #[using="P_sht P_she P_shz P_shl P_sh512 IDR B1R id b1' CE AR R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo md m Clg"] Lemma shadow_P : shadow_repr_ LPA sb (a_reg A) (a_cache A) (<[ u := LI (ChS (CS mb n)) n ]> (a_livemap A)) (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof ((shadow_P0 A v v' AR AGhs)) as dR_36; dand6 dR_36 as S1 S2 S3 S4 S5 S6 | pose proof (shadow_P0 A v v' AR AGhs) as (S1 & S2 & S3 & S4 & S5 & S6) ]). pose proof GEO as G. pose proof SHG as SG.
    split; [exact S1|]. split.
    { intros u0 c' k n1 Hl. destruct (decide (u0 = u)) as [->|NEu]; [rewrite lookup_insert_eq in Hl; discriminate|].
      rewrite lookup_insert_ne in Hl by congruence. exact (S2 u0 c' k n1 Hl). }
    split; [exact S3|]. split; [exact S4|]. split; [| exact S6].
    intros u0 mb' n1 Hl. destruct (decide (u0 = u)) as [->|NEu].
    - rewrite lookup_insert_eq in Hl. injection Hl as <- <-. pose proof NRu as NR'.
      (* [comment removed for export] *)
      unfold sshadow_live, fa8, shpat. rewrite (proj2 (proj2 (user_size_pos n ltac:(clear - NR'; lia))) ltac:(clear - NR'; lia)).
      (first [ dand9 SG as SG1 SG2 SG3 SG4 SG5 SG6 SG7 SG8 SG9 | destruct SG as (SG1 & SG2 & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9) ]).
      pose proof (Z_div_mod_eq_full n 8) as ND. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as NB. pose proof (div8_ceil n ltac:(clear - NR'; lia)) as DC.
      replace (Z.to_nat 768) with (512 + 256)%nat by reflexivity. rewrite repeat_app. repeat rewrite <- app_assoc.
      apply bytes_at_app. split; [exact P_sh512|]. rewrite repeat_length. replace (sh mb + Z.of_nat 512) with (sh AB) by (clear - SG4; lia).
      apply bytes_at_app. split; [exact P_shl|]. rewrite repeat_length. replace (sh AB + Z.of_nat 256) with (sh AB + 256) by lia.
      apply bytes_at_app. split; [exact P_shz|]. rewrite repeat_length, Z2Nat.id by (clear - NR' ND NB; lia).
      apply bytes_at_app. split.
      + destruct P_she as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
        destruct (Z.eqb_spec (n mod 8) 0) as [E0|NE0].
        * rewrite E0 in B. cbn [Z.min Z.to_nat repeat Z.compare Pos.compare] in B. cbn. exact B.
        * replace (Z.min (n mod 8) 1) with 1 in B by (clear - NE0 NB; lia). cbn [Z.to_nat repeat Pos.to_nat Pos.iter_op] in B. cbn. exact B.
      + assert (LEN : Z.of_nat (length (if n mod 8 =? 0 then [] else [Z_to_bv 8 (n mod 8)])) = Z.min (n mod 8) 1).
        { destruct (Z.eqb_spec (n mod 8) 0) as [E0|NE0]; [rewrite E0; reflexivity| cbn [length Z.of_nat Pos.of_succ_nat]; clear - NE0 NB; lia]. }
        rewrite LEN. replace (sh AB + 256 + d + Z.min e 1) with (sh AB + 256 + dc) by lia.
        replace (ms / 8 - 768 - (n + 7) / 8) with ((ms - 4096) / 8 - 256 - (n / 8 + Z.min (n mod 8) 1)) by (clear - DC SG3 G; lia).
        exact P_sht.
    - rewrite lookup_insert_ne in Hl by congruence. exact (S5 u0 mb' n1 Hl).
  Qed.

  #[using="P_mu2 P_dr P_sht P_she P_shz P_shl P_sh512 P_lch P_hdr IDR B1M B1R P_mapall P_pamap P_slot P_cidx P_shdr P_mtx P_reg id b1' md0 CE AR R WF0 NN MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo md m"] Theorem sec_arepr : @arepr _ DepotRepL LPA AL_pasan [] A' v'.
  Proof.
    constructor; cbn [secA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_sb a_fs].
    - exact consts_P. - exact locks_P. - exact regions_P. - exact cache_P. - exact live_P. - exact quar_P. - exact sec_P.
    - exact depot_P. - exact ia_P. - exact fsbase_P. - exact fsptrs_P. - exact fsflags_P. - exact maps_P. - exact shadow_P.
  Qed.
  End Cells.
End ReprPost.
End ASecB4.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaly5g.AMal5j7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaly5g OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecImg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB5.ASecB4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@SMz; @G; @Ha; @X; @CEIL; @Hz; @NR'; @SG4; @RSB; @Hm; @H; @AI; @NR; @MBA; @MB0; @MBC; @RF; @PAHI; @SHG_; @SG7; @RB; @L1; @R1; @Hff; @SHI; @CE'; @Rg; @Hcn; @B6; @Hp; @Hb; @SG; @D6; @LW; @NW; @NI; @G1; @L2; @G2; @L3; @G3; @L4; @G4; @Gt; @Gp; @Gn; @Gf])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
#[local] Notation WF := (WF AL_pasan).
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kHighShadowMapSize, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kLowShadowBeg, kShadowGapBeg,
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize in *.

Section Post5.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (n : Z) (mbw : word) (key : list Z) (slo shi : Z) (v' : mem) (pahi : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : kMaxPrimaryUser < n < 2^30 + 1.
  Hypothesis CEIL : alloc_ceiling <= slo.
  Local Notation mb := (bv_unsigned mbw).
  Local Notation ms := (map_size n).
  Hypothesis MBA : mb mod 4096 = 0.
  Hypothesis MB0 : 0 < mb.
  Hypothesis MBC : mb + ms <= alloc_ceiling.
  Hypothesis RF : region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) mbw (wz ms) = true.
  Local Notation nch := (Z.of_nat (length (sr_chunks (a_sec A)))).
  Local Notation pa := (p_pa (a_pl A)).
  Hypothesis PAHI : pahi = pa + 8 * nch + 8 \/ (nch = 0 /\ pahi = pa + 8 * kChunksBlockCount).

  Local Notation v := (aview_of (pa_hull A) m).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation n0 := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation D := (a_depot A).
  Local Notation AB := (sec_alloc_beg mb).
  Local Notation u := (sec_user_beg mb).
  Local Notation A' := (secA A mb n key kChunksBlockCount).
  Local Notation W := (sec_W slo shi thr mb ms pa nch pahi n0 f0).

  Hypothesis MU : munch W v v'.
  Hypothesis WMv : wmono rsegs v v'.
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let R : @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (ai_repr _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (conj WF0 R). Qed.
  Let CE : 0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000. Proof. exact alloc_ceiling_val. Qed.
  (* [comment removed for export] *)
  Let GEO_ := GEO A m md n mbw slo pahi AI NR CEIL MBA MB0 MBC RF PAHI.
  Let GEOP_ := GEOP A m md n mbw AI NR MBA MB0 MBC RF.
  Let SHG_ := SHG A m md n mbw slo pahi AI NR CEIL MBA MB0 MBC RF PAHI.
  Let AGW_ := AGW A m n mbw slo shi v' pahi MU.
  Let W_shape_ := W_shape A m md n mbw slo shi pahi AI NR CEIL MBA MB0 MBC RF PAHI.
  Let VIEW_NONE_ := VIEW_NONE A m md n mbw AI NR MBA MB0 MBC RF.
  Let SHADOW_ := SHADOW A m md n mbw AI NR MBA MB0 MBC RF.
  Let APART_ := APART A m md n mbw AI NR MB0 RF.
  Let NRu_ := NRu n NR.
  Ltac prep := pose proof GEO_ as G; pose proof SHG_ as SG;
               let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in let Gp := fresh "Gp" in let Gm := fresh "Gm" in
               pose proof GEOP_ as (Gt & Gn & Gf & Gp & Gm); aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf; aobj_lin1 Gp; aobj_lin1 Gm; kung_all.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="NRu_ SHG_ GEO_ WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo mbw n md m Clg"] Lemma rt_in_bigmap : forall b s, In (b, s) (runtime_maps A) -> exists i b' s', nth_error (big_maps A) i = Some (b', s') /\ b' <= b /\ b + s <= b' + s'.
  Proof.
    intros b s Hin. (first [ pose proof ((bm_nth_fixed A)) as dR_1; dand15 dR_1 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    (first [ pose proof ((sb_facts A WF0)) as dR_2; dand5 dR_2 as _ SBA HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & SBA & HB6 & RSB & SCE) ]).
    unfold runtime_maps, runtime_maps_ in Hin. apply in_app_iff in Hin as [Hin|Hin]; [|apply in_app_iff in Hin as [Hin|Hin]].
    - unfold a_b6, a_sb, a_pa, a_thr, a_ctx, a_ri, a_fs, a_nodes0, a_frames0, a_itab, a_m64k, p_ri in *.
      Ltac pk i E := exists i; eexists; eexists; split; [exact E| lia].
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-;
        [ pk 4%nat E4 | pk 5%nat E5 | exists 0%nat; eexists; eexists; split; [exact E0| unfold kSpaceReserve, kSpaceSize in *; lia]
        | pk 6%nat E6 | pk 7%nat E7 | pk 8%nat E8
        | exists 1%nat; eexists; eexists; split; [exact E1| unfold kChunksBlockCount, kPtrArrayReserve; lia]
        | pk 9%nat E9 | pk 10%nat E10 | pk 14%nat E14 | pk 11%nat E11 | pk 12%nat E12 | pk 13%nat E13 ].
    - apply in_flat_map in Hin as (c & Hc & Hin). apply in_map_iff in Hc as (cn & <- & Hcn). apply in_seq in Hcn.
      pose proof (region_piece_bounds A (Z.of_nat cn) WF0 ltac:(lia)) as RB. cbv zeta in RB. change (p_sb (a_pl A)) with sb in Hin.
      exists 0%nat; eexists; eexists; split; [exact E0|]. unfold a_b6, a_sb in *.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold kHighMemBeg, kFreeArrayOffset, kRegionSize, kSpaceSize, kSpaceReserve in *; lia.
    - apply in_map_iff in Hin as (sc & E & Hsc). injection E as <- <-. apply In_nth_error' in Hsc as [j Hj].
      exists (15 + j)%nat; eexists; eexists; split; [exact (bm_nth_sec A j sc Hj)| lia].
  Qed.
  #[using="NRu_ APART_ SHG_ GEO_ WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m Clg"] Lemma rt_apart_grant : forall b s a, In (b, s) (runtime_maps A) -> b <= a < b + s -> ~ (mb <= a < mb + ms).
  Proof.
    intros b s a Hin Ha Hm. (first [ pose proof ((rt_in_bigmap b s Hin)) as dR_3; dex3 dR_3 as i b' s'; dand3 dR_3 as Hi L1 R1 | pose proof ((rt_in_bigmap b s Hin)) as dR_3; dand6 dR_3 as i b' s' Hi L1 R1 | destruct (rt_in_bigmap b s Hin) as (i & b' & s' & Hi & L1 & R1) ]). pose proof (APART_ _ _ _ Hi). lia.
  Qed.
  #[using="NRu_ APART_ SHG_ GEO_ WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m Clg"] Lemma live_apart_grant : forall a, in_live_user A a -> ~ (mb <= a < mb + ms).
  Proof.
    intros a LU Hm. pose proof (bm_nth_fixed A) as (E0 & _).
    destruct (live_user_zone A a WF0 LU) as [[B6 _]|(i & s & Hi & R1)].
    - pose proof (APART_ _ _ _ E0). unfold a_b6 in *. lia.
    - pose proof (APART_ _ _ _ (bm_nth_sec A i s Hi)). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="NRu_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo mbw n md m"] Lemma thr_ownedS : forall a, thr <= a < thr + 4096 -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_4; dand6 dR_4 as _ _ _ _ E4 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & E4 & _) ]).
    apply (owned_rt A a thr 4096); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 4); [exact WF0| lia| exact E4| exact Ha]
      | eapply (fixed_bm_no_live_frame A 4); [exact WF0| lia| lia| exact E4| exact Ha]].
  Qed.
  #[using="NRu_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo mbw n md m"] Lemma n0_ownedS : forall a, n0 <= a < n0 + kDepotNodesBlock -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_5; dand9 dR_5 as _ _ _ _ _ _ _ E7 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & E7 & _) ]).
    apply (owned_rt A a n0 kDepotNodesBlock); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 7); [exact WF0| lia| exact E7| exact Ha]
      | eapply (fixed_bm_no_live_frame A 7); [exact WF0| lia| lia| exact E7| exact Ha]].
  Qed.
  #[using="NRu_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo mbw n md m"] Lemma f0_ownedS : forall a, f0 <= a < f0 + kStackStoreBlockBytes -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_6; dand10 dR_6 as _ _ _ _ _ _ _ _ E8 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & E8 & _) ]).
    apply (owned_rt A a f0 kStackStoreBlockBytes); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 8); [exact WF0| lia| exact E8| exact Ha]
      | eapply (fixed_bm_no_live_frame A 8); [exact WF0| lia| lia| exact E8| exact Ha]].
  Qed.
  #[using="NRu_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo mbw n md m"] Lemma pa_ownedS : forall a, pa <= a < pa + 8 * kChunksBlockCount -> pa_owned A a.
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_7; dand3 dR_7 as _ E1 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _) ]).
    apply (owned_rt A a pa (8 * kChunksBlockCount)); [apply rt_fixed_in; cbn; tauto| exact Ha
      | eapply (fixed_bm_no_live_user A 1); [exact WF0| lia| exact E1| unfold a_pa, kChunksBlockCount, kPtrArrayReserve in *; lia]
      | eapply (fixed_bm_no_live_frame A 1); [exact WF0| lia| lia| exact E1| unfold a_pa, kChunksBlockCount, kPtrArrayReserve in *; lia]].
  Qed.
  #[using="mbw n"] Lemma dstat_ownedS : forall a, 0x187288 <= a < 0x5d72a8 -> pa_owned A a.
  Proof. intros a Ha. apply asI_static_owned. cbn [cl_static LPA]. apply depot_static. cbn. unfold kDepotNodesL1. lia. Qed.
  #[using="mbw n"] Lemma inst_ownedS : forall a, INST <= a < INST + 3680 -> pa_owned A a.
  Proof. intros a Ha. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. rewrite INST_val in Ha. lia. Qed.
  (* [comment removed for export] *)
  #[using="SHADOW_ RF MBC MB0 MBA NR AI md m"] Lemma newsh_ownedS : forall z, sh mb <= z < sh mb + ms / 8 -> pa_owned A z.
  Proof. intros z Hz. left. right. right. exact (proj1 (SHADOW_ z Hz)). Qed.

  (* [comment removed for export] *)
  #[using="NRu_ APART_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m"] Lemma sec_owned_keep : forall a, pa_owned A a -> pa_owned A' a.
  Proof.
    intros a H. unfold pa_owned, aowned, aowned_ in *. cbn [secA a_pl a_reg a_livemap a_sec a_fframes sr_chunks].
    destruct H as [[S|[[(R1 & NU & NF)|[HS|FS]]|GH]]|I].
    - left; left; exact S.
    - left; right; left; left. split; [| split; [| exact NF]].
      + (first [ dex2 R1 as b s; destruct R1 as [Hin Hb] | dand4 R1 as b s Hin Hb | destruct R1 as (b & s & Hin & Hb) ]). exists b, s. split; [| exact Hb].
        unfold runtime_maps_ in *. cbn [sr_chunks]. rewrite map_app. rewrite !in_app_iff in Hin |- *. cbn [map]. rewrite in_app_iff. tauto.
      + ((first [ intro dR_17; dex2 dR_17 as p li; destruct dR_17 as [Hl Hp] | intro dR_17; dand4 dR_17 as p li Hl Hp | intros (p & li & Hl & Hp) ])). destruct (decide (p = u)) as [->|NEp].
        * rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_n] in Hp. (first [ dex2 R1 as b s; destruct R1 as [Hin Hb] | dand4 R1 as b s Hin Hb | destruct R1 as (b & s & Hin & Hb) ]).
          pose proof GEO_ as G. apply (rt_apart_grant b s a Hin Hb). clear - G Hp. lia.
        * rewrite lookup_insert_ne in Hl by congruence. apply NU. exists p, li. exact (conj Hl Hp).
    - left; right; left; right; left. unfold heap_shadow_ in *. cbn [sr_chunks].
      destruct HS as [X|[X|(s & Hin & Hs)]]; [left; exact X| right; left; exact X| right; right].
      exists s. split; [apply in_app_iff; left; exact Hin| exact Hs].
    - left; right; left; right; right. exact FS.
    - left; right; right. exact GH.
    - right. exact I.
  Qed.
  (* [comment removed for export] *)
  #[using="APART_ SHADOW_ VIEW_NONE_ GEO_ AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md"] Lemma sec_owned_new : forall a, pa_owned A' a -> pa_owned A a \/ (v (wz a) = None /\ heap_zone LPA a).
  Proof.
    intros a H. pose proof GEO_ as G. unfold pa_owned, aowned, aowned_ in H. cbn [secA a_pl a_reg a_livemap a_sec a_fframes sr_chunks] in H.
    destruct H as [[S|[[(R1 & NU & NF)|[HS|FS]]|GH]]|I].
    - left. left; left; exact S.
    - (first [ dex2 R1 as b s; destruct R1 as [Hin Hb] | dand4 R1 as b s Hin Hb | destruct R1 as (b & s & Hin & Hb) ]).
      assert (CASE : In (b, s) (runtime_maps A) \/ (b, s) = (mb, ms)).
      { unfold runtime_maps, runtime_maps_ in *. cbn [sr_chunks] in Hin. rewrite map_app in Hin. cbn [map cs_map cs_n] in Hin.
        rewrite !in_app_iff in Hin. rewrite !in_app_iff.
        destruct Hin as [X|[X|[X|[X|[]]]]]; [left; left; exact X| left; right; left; exact X| left; right; right; exact X| right; symmetry; exact X]. }
      destruct CASE as [OLD|E].
      + left. left; right; left; left. split; [exists b, s; exact (conj OLD Hb)|]. split; [| exact NF].
        ((first [ intro dR_18; dex2 dR_18 as p li; destruct dR_18 as [Hl Hp] | intro dR_18; dand4 dR_18 as p li Hl Hp | intros (p & li & Hl & Hp) ])). apply NU. exists p, li. split; [| exact Hp]. rewrite lookup_insert_ne; [exact Hl|].
        intros <-. rewrite (sec_u_fresh A v mb n AR NR MBA APART_) in Hl. discriminate.
      + injection E as -> ->. right. split; [apply VIEW_NONE_; exact Hb|]. unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA]. clear - G Hb. lia.
    - unfold heap_shadow_ in HS. cbn [sr_chunks] in HS. destruct HS as [X|[X|(s & Hin & Hs)]].
      + left. left; right; left; right; left. left. exact X.
      + left. left; right; left; right; left. right; left. exact X.
      + apply in_app_iff in Hin as [Hin|[<-|[]]].
        * left. left; right; left; right; left. right; right. exists s. exact (conj Hin Hs).
        * cbn [cs_map cs_n] in Hs. left. apply newsh_ownedS. exact Hs.
    - left. left; right; left; right; right. exact FS.
    - left. left; right; right. exact GH.
    - left. right. exact I.
  Qed.
  #[using="NRu_ SHADOW_ VIEW_NONE_ SHG_ GEO_ PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md"] Lemma sec_newblk : forall a, newblk u n a -> pa_owned A a \/ (v (wz a) = None /\ heap_zone LPA a).
  Proof.
    intros a NB. pose proof GEO_ as G. pose proof SHG_ as SG. pose proof NRu_ as NR'. pose proof (div8_ceil n ltac:(clear - NR'; lia)) as DC.
    unfold newblk, blk in NB. destruct NB as [[_ Ha]|[_ Ha]].
    - right. split; [apply VIEW_NONE_; clear - G Ha; lia|]. unfold heap_zone, in_image. cbn [cl_image_lo cl_image_hi LPA]. clear - G Ha. lia.
    - left. apply newsh_ownedS. pose proof (Z_div_mod_eq_full n 8). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). clear - G SG Ha DC H H0. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="NRu_ APART_ SHADOW_ W_shape_ AGW_ SHG_ GEOP_ GEO_ CE AR R WF0 MU PAHI RF MBC MB0 MBA CEIL NR AI pahi md"] Lemma sec_frame1 : forall a, 0 <= a < 2^64 -> ~ pa_owned A a -> ~ pa_owned A' a -> ~ (slo <= a < shi) -> ~ newblk u n a -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha NO NO' NW NB. prep. apply AGW_; [exact Ha|].
    apply W_shape_.
    - exact NW.
    - intros X. apply NO. apply thr_ownedS. clear - X. lia.
    - intros X. apply NO. apply inst_ownedS. clear - X. lia.
    - intros X. apply NO. apply inst_ownedS. clear - X. lia.
    - intros X. apply NO. apply inst_ownedS. clear - X. lia.
    - intros X. apply NO. apply pa_ownedS. clear - X G. kung_all. lia.
    - intros X. apply NO. apply dstat_ownedS. exact X.
    - intros X. apply NO. apply n0_ownedS. clear - X. kung_all. lia.
    - intros X. apply NO. apply f0_ownedS. clear - X. kung_all. lia.
    - intros X. destruct (decide (u <= a < u + n)) as [Y|Y].
      + apply NB. left. split; [clear - G; lia| exact Y].
      + apply NO'. (* [comment removed for export] *)
        apply (owned_rt A' a mb ms).
        * unfold runtime_maps, runtime_maps_. cbn [secA a_pl a_reg a_sec sr_chunks]. cbn [sr_chunks]. rewrite map_app. rewrite !in_app_iff. right; right. rewrite ?in_app_iff. right. cbn [map In cs_map cs_n]. left. reflexivity.
        * exact X.
        * ((first [ intro dR_19; dex2 dR_19 as p li; destruct dR_19 as [Hl Hp] | intro dR_19; dand4 dR_19 as p li Hl Hp | intros (p & li & Hl & Hp) ])). unfold in_live_user in Hl. cbn [secA a_livemap] in Hl. destruct (decide (p = u)) as [->|NEp].
          -- rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_n] in Hp. exact (Y Hp).
          -- rewrite lookup_insert_ne in Hl by congruence. exact (live_apart_grant a (ex_intro _ p (ex_intro _ li (conj Hl Hp))) X).
        * intros LF. unfold in_live_frame in LF. cbn [secA a_fframes] in LF.
          (first [ pose proof ((bm_nth_fixed A)) as dR_11; dand8 dR_11 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]). pose proof (APART_ _ _ _ E6) as D6.
          (first [ dex2 LF as ff f; destruct LF as [Hf Hff] | dand4 LF as ff f Hf Hff | destruct LF as (ff & f & Hf & Hff) ]). pose proof (live_frame_where A ff f a WF0 Hf ltac:(clear - Hff; lia)) as LW. unfold a_fs in *. clear - D6 LW X Hff. unfold kFakeFramesOffset in *. kung_all. lia.
    - intros X. apply NO. apply newsh_ownedS. exact X.
  Qed.

  (* [comment removed for export] *)
  Section Frame.
  Variable whi : Z.
  Hypothesis SHI : shi <= whi <= 2^47.
  Hypothesis SMW : mapped v slo (whi - slo).
  #[using="SMW SHI NRu_ APART_ SHADOW_ VIEW_NONE_ W_shape_ AGW_ SHG_ GEOP_ GEO_ CE AR R WF0 NN MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi md"] Theorem sec_frame_ok : frame_ok LPA (pa_owned A) (pa_owned A') whi (whi - slo) nowhere (newblk u n) v v'.
  Proof.
    pose proof CE as CE'. unfold frame_ok. replace (whi - (whi - slo)) with slo by lia.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - intros a Ha NO NO' NW NE' _ NB. apply sec_frame1; [exact Ha| exact NO| exact NO'| clear - NW SHI; lia| exact NB].
    - intros a Ha NI Hv. right. right. apply NN; [clear - Ha; lia| | clear - Ha; lia| exact Hv]. unfold in_image in NI. cbn [cl_image_lo cl_image_hi LPA] in NI. clear - NI Ha; lia.
    - apply (mapped_N A m mbw v' MB0 NN); [clear - CE' CEIL; lia | right; clear - CE' CEIL; lia | clear - SHI CE' CEIL; lia | exact SMW].
    - intros a Ha NB. destruct (sec_newblk a NB) as [O|X]; [left; exact O| right; right; exact X].
    - intros a Ha O'. destruct (sec_owned_new a O') as [O|X]; [left; exact O| right; right; exact X].
    - intros a Ha O NO'. exfalso. exact (NO' (sec_owned_keep a O)).
    - intros a Ha F. destruct F.
  Qed.
  End Frame.

  (* [comment removed for export] *)
  #[using="NRu_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m"] Lemma sec_hull_sub : forall iv, In iv (pa_hull A) -> In iv (pa_hull A').
  Proof.
    intros iv Hin. rewrite (sec_hull A mb n key kChunksBlockCount). unfold pa_hull, ahull_of, ahull_of_, aregions, aregions_ in Hin.
    change (p_sb (a_pl A)) with sb in Hin. rewrite !in_app_iff in Hin. rewrite !in_app_iff. tauto.
  Qed.
  #[using="NRu_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m"] Lemma sec_hull_cases : forall x, in_hullb (pa_hull A') x = true ->
    in_hullb (pa_hull A) x = true \/ (mb <= x < mb + ms) \/ (sh mb <= x < sh mb + ms / 8).
  Proof.
    intros x H. apply in_hullb_true in H as (lo & hi & Hin & Rg).
    rewrite (sec_hull A mb n key kChunksBlockCount) in Hin.
    assert (CASE : In (lo, hi) (pa_hull A) \/ In (lo, hi) (hull_of [(mb, ms); shadow_region mb ms])).
    { unfold pa_hull, ahull_of, ahull_of_, aregions, aregions_. change (p_sb (a_pl A)) with sb. rewrite !in_app_iff in Hin. rewrite !in_app_iff. tauto. }
    destruct CASE as [OLD|NEWi].
    - left. exact (in_hullb_intro _ _ _ _ OLD Rg).
    - right. rewrite (gf_sh mbw ms MBA (MSP A n mbw NR MB0) (MSA n)) in NEWi. cbn in NEWi.
      destruct NEWi as [E|[E|[]]]; injection E as E1 E2; subst lo hi; [left| right]; lia.
  Qed.
  #[using="NRu_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m"] Corollary sec_hidc_old : forall a, hidc (pa_hull A') a = false ->
    hidc (pa_hull A) a = false \/ (mb <= bv_unsigned a < mb + ms) \/ (sh mb <= bv_unsigned a < sh mb + ms / 8).
  Proof.
    intros a H. unfold hidc in *. apply negb_false_iff in H. destruct (sec_hull_cases _ H) as [X|X]; [left; rewrite X; reflexivity| right; exact X].
  Qed.
  #[using="NRu_ SHG_ GEOP_ GEO_ CE AR R WF0 PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m"] Corollary sec_hidc_new : forall a, hidc (pa_hull A) a = true -> hidc (pa_hull A') a = false ->
    (mb <= bv_unsigned a < mb + ms) \/ (sh mb <= bv_unsigned a < sh mb + ms / 8).
  Proof. intros a H0 H1. destruct (sec_hidc_old a H1) as [X|X]; [rewrite X in H0; discriminate| exact X]. Qed.

  (* [comment removed for export] *)
  Section Cells5.
  Local Notation d := (n / 8).
  Local Notation e := (n mod 8).
  Local Notation dc := (n / 8 + Z.min (n mod 8) 1).
  Local Notation ru := ((ms - 4096) / 8).
  Hypothesis P_sh512 : bytes_at rsegs v' (sh mb) (repeat (Z_to_bv 8 250) 512).
  Hypothesis P_shl : bytes_at rsegs v' (sh AB) (repeat (Z_to_bv 8 250) 256).
  Hypothesis P_shz : bytes_at rsegs v' (sh AB + 256) (repeat (Z_to_bv 8 0) (Z.to_nat d)).
  Hypothesis P_she : rw_cells rsegs v' (sh AB + 256 + d) [CB (Z.to_nat (Z.min e 1)) (repeat (Z_to_bv 8 e) (Z.to_nat (Z.min e 1)))].
  Hypothesis P_sht : bytes_at rsegs v' (sh AB + 256 + dc) (repeat (Z_to_bv 8 250) (Z.to_nat (ru - 256 - dc))).

  (* [comment removed for export] *)
  #[using="P_sht P_she P_shz P_shl P_sh512 NRu_ SHG_ GEO_ PAHI RF MBC MB0 MBA CEIL NR AI pahi slo md m A Clg"] Lemma newsh_present : forall z, sh mb <= z < sh mb + ms / 8 -> v' (wz z) <> None.
  Proof.
    intros z Hz. pose proof GEO_ as G. pose proof SHG_ as SG. pose proof NRu_ as NR'.
    pose proof (Z_div_mod_eq_full n 8) as ND. pose proof (Z.mod_pos_bound n 8 ltac:(lia)) as NB.
    pose proof (div8_ceil n ltac:(clear - NR'; lia)) as DC.
    (first [ dand9 SG as SG1 SG2 SG3 SG4 SG5 SG6 SG7 SG8 SG9 | destruct SG as (SG1 & SG2 & SG3 & SG4 & SG5 & SG6 & SG7 & SG8 & SG9) ]).
    (* [comment removed for export] *)
    Ltac byB B base z K2 K3 := replace z with (base + (z - base)) by lia;
      apply (bytes_at_nonnull _ _ base _ (z - base) B); [rewrite repeat_length; K2; lia | exact pa_rom_high | K3; unfold sh in *; lia].
    destruct (Z_lt_le_dec z (sh mb + 512)) as [L1|G1]; [byB P_sh512 (sh mb) z ltac:(idtac) ltac:(idtac)|].
    destruct (Z_lt_le_dec z (sh AB + 256)) as [L2|G2]; [byB P_shl (sh AB) z ltac:(idtac) ltac:(idtac)|].
    destruct (Z_lt_le_dec z (sh AB + 256 + d)) as [L3|G3]; [byB P_shz (sh AB + 256) z ltac:(clear - G2 L3) ltac:(clear - SG4 SG7)|].
    destruct (Z_lt_le_dec z (sh AB + 256 + dc)) as [L4|G4].
    - destruct P_she as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. byB B (sh AB + 256 + d) z ltac:(clear - G3 L4) ltac:(clear - SG4 SG7 NR').
    - byB P_sht (sh AB + 256 + dc) z ltac:(clear - Hz SG4 SG6 NB G1 G2 G3 G4) ltac:(clear - SG4 SG7 NR' NB).
  Qed.

  #[using="P_sht P_she P_shz P_shl P_sh512 NRu_ W_shape_ AGW_ SHG_ GEOP_ GEO_ CE AR R WF0 NN MU PAHI RF MBC MB0 MBA CEIL NR AI pahi shi slo md"] Theorem sec_hidden : forall mr : mem,
    (forall a, hidc (pa_hull A') a = true -> mr a = m a) ->
    (forall a, hidc (pa_hull A') a = false -> mr a = v' a) ->
    hidden_repr (a_pl A) (a_reg A) (a_sec A) m ->
    hidden_repr (a_pl A) (a_reg A) (SR (sr_chunks (a_sec A) ++ [CS mb n]) kChunksBlockCount) mr.
  Proof.
    intros mr HID VIS [H1 H2]. (first [ pose proof (asI_layout_order) as dR_14; dand4 dR_14 as _ _ _ LO4 | pose proof asI_layout_order as (_ & _ & _ & LO4) ]).
    (* [comment removed for export] *)
    assert (OLDVIS : forall z, in_shadow_maps z -> ~ (sh mb <= z < sh mb + ms / 8) -> hidc (pa_hull A') (wz z) = false ->
                     hidc (pa_hull A) (wz z) = false /\ v' (wz z) = v (wz z) /\ v (wz z) = m (wz z)).
    { intros z SMz NS Hv. unfold in_shadow_maps in SMz. prep.
      assert (Z64 : 0 <= z < 2^64) by (clear - SMz; lia).
      destruct (sec_hidc_old _ Hv) as [X|[X|X]]; rewrite ?unsigned_lit in X by exact Z64.
      - split; [exact X|]. split; [| unfold aview_of; rewrite (view_visible _ m z X); reflexivity].
        apply AGW_; [exact Z64|].
        apply W_shape_; [ clear - SMz G | clear - SMz G Gt | clear - SMz G | clear - SMz G | clear - SMz G | clear - SMz G Gp | clear - SMz G
                        | clear - SMz G Gn | clear - SMz G Gf | clear - SMz G Gm | exact NS ]; rewrite ?INST_val; lia.
      - exfalso. clear - SMz X G Gm. lia.
      - exfalso. exact (NS X). }
    assert (HSmono : forall z, ~ heap_shadow_ (p_sb (a_pl A)) (a_reg A) (SR (sr_chunks (a_sec A) ++ [CS mb n]) kChunksBlockCount) z ->
                     ~ heap_shadow_ (p_sb (a_pl A)) (a_reg A) (a_sec A) z /\ ~ (sh mb <= z < sh mb + ms / 8)).
    { intros z NHS. split.
      - intros HS. apply NHS. unfold heap_shadow_ in *. cbn [sr_chunks]. destruct HS as [X|[X|(s & Hin & Hs)]]; [left; exact X| right; left; exact X|].
        right; right. exists s. split; [apply in_app_iff; left; exact Hin| exact Hs].
      - intros Hz. apply NHS. unfold heap_shadow_. right; right. exists (CS mb n). cbn [sr_chunks cs_map cs_n]. split; [apply in_app_iff; right; left; reflexivity| exact Hz]. }
    split.
    - intros z GZ. destruct (H1 z GZ) as [P1 P2]. pose proof GZ as [SMz _].
      destruct (hidc (pa_hull A') (wz z)) eqn:E.
      + rewrite (HID _ E). split; [exact P1| intros NHS; exact (P2 (proj1 (HSmono z NHS)))].
      + rewrite (VIS _ E). destruct (decide (sh mb <= z < sh mb + ms / 8)) as [IN|OUT].
        * split; [exact (newsh_present z IN)|]. intros NHS. exfalso. exact (proj2 (HSmono z NHS) IN).
        * (first [ pose proof ((OLDVIS z SMz OUT E)) as dR_15; dand3 dR_15 as X0 E1 E2 | destruct (OLDVIS z SMz OUT E) as (X0 & E1 & E2) ]). split.
          -- apply NN; [| | | rewrite E2; exact P1]; unfold in_shadow_maps in SMz; clear - SMz LO4; kung_all; lia.
          -- intros NHS. rewrite E1, E2. exact (P2 (proj1 (HSmono z NHS))).
    - intros z Hz NVS. pose proof (H2 z Hz NVS) as P1.
      assert (SMz : in_shadow_maps z) by (left; exact Hz).
      destruct (hidc (pa_hull A') (wz z)) eqn:E.
      + rewrite (HID _ E). exact P1.
      + rewrite (VIS _ E). destruct (decide (sh mb <= z < sh mb + ms / 8)) as [IN|OUT]; [exact (newsh_present z IN)|].
        (first [ pose proof ((OLDVIS z SMz OUT E)) as dR_16; dand3 dR_16 as X0 E1 E2 | destruct (OLDVIS z SMz OUT E) as (X0 & E1 & E2) ]). apply NN; [| | | rewrite E2; exact P1]; unfold kLowShadowMapBeg in Hz; clear - Hz; lia.
  Qed.
  End Cells5.
End Post5.
