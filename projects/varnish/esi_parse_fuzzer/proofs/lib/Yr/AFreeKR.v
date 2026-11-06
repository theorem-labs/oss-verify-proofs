(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocI AMalmys ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeB2 AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf ABudget ASecImg AFreeB6 ANodijx APgGeo AFreeX1 AFreeX2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecImg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeX3 ATranspR AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2 AFreeRP.

Module AFreeKX.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtSrgm AMallocI AMalmys ATransp ATranspR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 ASecComb ASecB1 ANodijx.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf AFreeRS AFreeRX AFreeRI AFreeRT AFreeX1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecComb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
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
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser in *.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section BusySecKit.
Context {Clg : Ceiling}.
  Variables (A : AState) (v : mem) (p n0 kb : Z) (es : list qentry) (more : list batch).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A v.
  Hypothesis WR : WFR A.
  Hypothesis LQ : a_qlimbo A = BA kb (QE (ChS (CS (p - 6144) n0)) n0 :: es) :: more.

  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  #[warnings="-notation-for-abbreviation"] Local Notation nch := (Z.of_nat (length (sr_chunks (a_sec A)))).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation pa := (p_pa (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation sec_words := (AFreeX1.sec_words A).
  #[warnings="-notation-for-abbreviation"] Local Notation sec_last := (AFreeX1.sec_last A).

  Let W : WFT A. Proof. exact (proj1 AR). Qed.
  Let RP : @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (proj2 AR). Qed.
  Let CR : consts_repr_ LPA AL_pasan (a_pl A) v. Proof. exact (ar_consts _ _ _ _ _ RP). Qed.
  Let LK : locks_repr_ LPA AL_pasan (a_pl A) [] v. Proof. exact (ar_locks _ _ _ _ _ RP). Qed.
  Let SR : sec_repr_ LPA AL_pasan (a_pl A) (a_sec A) v. Proof. exact (ar_sec _ _ _ _ _ RP). Qed.
  Let CFA : Forall (fun c => bytes_at rsegs v (fst c) (snd c)) (cl_consts LPA).
  Proof. exact (proj1 (ar_consts _ _ _ _ _ RP)). Qed.
  (* [comment removed for export] *)
  Lemma bk_entry : kMaxPrimaryUser < n0 /\ 0 <= n0 < REQ_MAX /\ In (CS h n0) chunks.
  Proof.
    destruct (wrL A WR) as (L1 & _). rewrite LQ in L1. (first [ pose proof ((Forall_inv L1)) as dR_1; dand3 dR_1 as _ _ B3 | pose proof (Forall_inv L1) as (_ & _ & B3) ]). cbn [ba_entries] in B3.
    pose proof (Forall_inv B3) as [WE1 WE]. cbn [qe_chunk qe_n cs_n] in WE1, WE. (first [ dand3 WE as X1 X2 X3 | destruct WE as (X1 & X2 & X3) ]). split; [exact X1| split; [exact WE1| exact X3]].
  Qed.
  Let NQB : kMaxPrimaryUser < n0. Proof. exact (proj1 bk_entry). Qed.
  Ltac cell H a bs := pose proof (consts_cell _ a bs CFA eq_refl) as H.

  Lemma bk_In : In (CS h n0) chunks.
  Proof. exact (proj2 (proj2 bk_entry)). Qed.

  Lemma bk_idx : exists i, nth_error chunks i = Some (CS h n0).
  Proof. apply In_nth_error'. exact bk_In. Qed.

  Lemma bk_known : known A (ChS (CS h n0)) n0.
  Proof. cbn. split; [exact bk_In| split; [exact NQB| reflexivity]]. Qed.

  (* [comment removed for export] *)
  Lemma bk_geo : aobj h msz /\ h mod 4096 = 0 /\ 4096 + 32 <= msz /\ msz mod 4096 = 0 /\ h + msz <= alloc_ceiling /\
                 p = h + 6144 /\ p + 8 * ((n0 + 7) / 8) <= h + msz /\ n0 + 6144 <= msz /\ kMaxPrimaryUser < n0 < REQ_MAX /\
                 0x60a000 <= h /\ p mod 16 = 0.
  Proof.
    (first [ pose proof ((sec_chunk_boundsT A _ W bk_In)) as dR_3; dand5 dR_3 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_boundsT A _ W bk_In) as (B1 & B2 & B3 & B4 & B5) ]). cbn [cs_map cs_n] in *.
    (first [ pose proof ((secondary_layout h n0 NQB)) as dR_4; dand7 dR_4 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout h n0 NQB) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]).
    pose proof (map_size_page n0) as MP. pose proof (needed_size_ge n0) as NG. rewrite needed_size2_secondary in B5 by lia.
    pose proof (rounded_size_ge n0) as RG. pose proof (proj1 (proj2 bk_entry)) as NR0. assert (NR : 1 <= n0 < REQ_MAX) by (pose proof NQB as NQ; unfold kMaxPrimaryUser in NQ; lia).
    assert (US : user_size n0 = n0) by (unfold user_size; pose proof NQB as NQ; unfold kMaxPrimaryUser in NQ; destruct (Z.eqb_spec n0 0); lia). rewrite US in S4.
    pose proof (app_facts _ _ B3) as AF.
    assert (PM : p mod 16 = 0) by (clear - B2; replace p with ((p - 6144) + 16 * 384) by lia; rewrite Z.add_mod, Z.mul_mod, (mod0_down _ 4096 16 ltac:(exists 256; reflexivity) B2) by lia; reflexivity).
    unfold sec_user_beg, kPageSize in S3, S4, S7.
    assert (R8 : p + 8 * ((n0 + 7) / 8) <= h + msz).
    { apply (roundup8_le p n0 (h + msz)); [| | lia].
      - apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM].
      - rewrite Z.add_mod by lia. rewrite (mod0_down _ 4096 8 ltac:(exists 512; reflexivity) B2), (mod0_down _ kPageSize 8 ltac:(exists 512; reflexivity) MP). reflexivity. }
    split; [apply (proj1 (aobj_app_rangeA _ _)); exact B3|]. split; [exact B2|]. split; [kung_all; lia|]. split; [exact MP|].
    split; [exact B4|]. split; [lia|]. split; [exact R8|]. split; [lia|]. split; [lia|]. split; [| exact PM].
    pose proof (known_range A v [] AR (ChS (CS h n0)) n0 bk_known) as [KR _]. cbn [chunk_lo] in KR. exact KR.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_shr : sh (h + msz) = sh h + msz / 8 /\ (sh h) mod 512 = 0 /\ (msz / 8) mod 512 = 0 /\
                 ((kHighShadowMapBeg <= sh h /\ sh h + msz / 8 <= kHighMemBeg /\ kHighMemBeg <= h) \/
                  (kLowShadowBeg + 0x200 <= sh h /\ sh h + msz / 8 < kShadowGapBeg /\ h + msz <= kLowShadowMapBeg)).
  Proof.
    (first [ pose proof (bk_geo) as dR_5; dand11 dR_5 as HLO HAL MSZ MSZAL HHI _ _ _ _ H5 _ | pose proof bk_geo as (HLO & HAL & MSZ & MSZAL & HHI & _ & _ & _ & _ & H5 & _) ]). (first [ pose proof ((aobj_facts _ _ HLO)) as dR_6; dand5 dR_6 as F1 F2 F3 F4 F5 | pose proof (aobj_facts _ _ HLO) as (F1 & F2 & F3 & F4 & F5) ]).
    pose proof alloc_ceiling_val as CE.
    assert (SHA : sh (h + msz) = sh h + msz / 8).
    { apply sh_add; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL]| apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL]]. }
    pose proof (Z_div_mod_eq_full h 4096) as XH. rewrite HAL, Z.add_0_r in XH.
    pose proof (Z_div_mod_eq_full msz 4096) as XM. rewrite MSZAL, Z.add_0_r in XM.
    assert (D1 : h / 8 = 512 * (h / 4096)) by (rewrite XH at 1; replace (4096 * (h / 4096)) with ((512 * (h / 4096)) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    assert (D2 : msz / 8 = 512 * (msz / 4096)) by (rewrite XM at 1; replace (4096 * (msz / 4096)) with ((512 * (msz / 4096)) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    split; [exact SHA|]. split.
    { unfold sh, kShadowOffset. rewrite D1. replace (512 * (h / 4096) + 2147450880) with ((h / 4096 + 4194240) * 512) by lia. apply Z_mod_mult. }
    split; [rewrite D2; replace (512 * (msz / 4096)) with ((msz / 4096) * 512) by lia; apply Z_mod_mult|].
    unfold sh, kShadowOffset in *. kung_all.
    destruct F5 as [LOW|HIGH].
    - right. pose proof (Z.div_le_mono (h + msz) 0x7fff7000 8 ltac:(lia) ltac:(lia)) as U. change (0x7fff7000 / 8) with 268430848 in U.
      pose proof (Z.div_le_mono 0x60a000 h 8 ltac:(lia) ltac:(lia)) as L. change (0x60a000 / 8) with 791552 in L.
      rewrite Z.add_comm in SHA |- *. lia.
    - left. pose proof (Z.div_le_mono 0x10007fff8000 h 8 ltac:(lia) ltac:(lia)) as L. change (0x10007fff8000 / 8) with 0x2000ffff000 in L.
      pose proof (Z.div_le_mono (h + msz) 0x7fffff800000 8 ltac:(lia) ltac:(lia)) as U. change (0x7fffff800000 / 8) with 0xffffff00000 in U.
      lia.
  Qed.

  Lemma bk_sb : kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling /\ apart h msz sb (2^37) /\ (p + -16 < sb \/ sb + 2^37 <= p + -16).
  Proof.
    (first [ pose proof ((sb_factsT A W)) as dR_7; dand5 dR_7 as _ _ HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (sec_apart_b6 A v [] AR _ bk_In) as D. cbn [cs_map cs_n] in D.
    (first [ pose proof (bk_geo) as dR_8; dand10 dR_8 as HLO _ MSZ _ _ PH _ N6 NR _ | pose proof bk_geo as (HLO & _ & MSZ & _ & _ & PH & _ & N6 & NR & _) ]). unfold a_b6, a_sb in *. unfold apart. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma bkc_LMA0 : ro_cells rsegs v ASecComb.LMA [C8 (wz 4096)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_sec_page_size) 4096) by tauto. apply u64_ro. exact X.
  Qed.
  Lemma bkc_LPA8 : ro_cells rsegs v (ASecComb.LMA + 8) [C8 (wz pa)].
  Proof.
    pose proof CR as C. unfold consts_repr_ in C. cbv zeta in C. cbn [al_instance AL_pasan] in C.
    assert (X : u64_at rsegs v (728408 + off_sec_chunks) (p_pa (a_pl A))) by tauto. apply u64_ro. exact X.
  Qed.
  Lemma bkc_LREG : rw_cells rsegs v (ASecComb.LMA + 48) [C8 (wz (sr_reserved (a_sec A))); C8 (wz nch)].
  Proof.
    pose proof SR as S. unfold sec_repr_ in S. cbv zeta in S. cbn [al_instance AL_pasan] in S. (first [ dand3 S as S1 S2 _ | destruct S as (S1 & S2 & _) ]).
    unfold off_sec_n_reserved, off_sec_n_chunks in S1, S2. unfold u64_at in S1, S2.
    split; [split; [exact (conj I (conj I I))| cbn [cells_bytes cbytes]; rewrite app_nil_r; apply bytes_at_app; split;
      [exact S1| rewrite length_le8; exact S2]]|].
    apply img_wr_at0; ulma; cbn; lia.
  Qed.
  Lemma bkc_LCS : exists cs, rw_cells rsegs v (ASecComb.LMA + 64) [C1 cs].
  Proof.
    (first [ pose proof ((img_rw_bytes v (ASecComb.LMA + 64) 1 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_10; dex1 dR_10 as bs; destruct dR_10 as [LB RB] | pose proof ((img_rw_bytes v (ASecComb.LMA + 64) 1 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_10; dand3 dR_10 as bs LB RB | destruct (img_rw_bytes v (ASecComb.LMA + 64) 1 ltac:(ulma; lia) ltac:(ulma; lia)) as (bs & LB & RB) ]).
    destruct bs as [|b [|]]; cbn in LB; try lia. exists b.
    refine (rwc_rebytes _ _ _ _ _ _ RB); cbn; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact I| reflexivity].
  Qed.
  Lemma bkc_LMTX : rw_cells rsegs v (ASecComb.LMA + 616) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)].
  Proof.
    pose proof LK as LKx. unfold locks_repr_ in LKx. cbv zeta in LKx. cbn [al_instance AL_pasan] in LKx. (first [ dand3 LKx as _ L1 _ | destruct LKx as (_ & L1 & _) ]).
    unfold off_sec_mutex, lockb in L1. cbn [in_dec] in L1. unfold u8_at in L1.
    cell PB 0xb2001 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].
    split; [split; [exact (conj I (conj I (conj I I)))|]|].
    - cbn [cells_bytes cbytes]. change (ASecComb.LMA + 616) with (728408 + 680).
      apply bytes_at_app. split; [exact L1|]. cbn [length Z.of_nat Pos.of_succ_nat]. change (728408 + 680 + 1) with 0xb2001.
      apply (bytes_at_as v _ _ _ PB). byteseq.
    - apply img_wr_at0; ulma; cbn; lia.
  Qed.
  Lemma bkc_LSTA : exists (na nf ca mx : word) (bsl : list word),
    rw_cells rsegs v (ASecComb.LMA + 72) [C8 na; C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)] /\ length bsl = 64%nat.
  Proof.
    (first [ pose proof ((img_rw_words v (ASecComb.LMA + 72) 68 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_12; dex1 dR_12 as ws; destruct dR_12 as [LW RW] | pose proof ((img_rw_words v (ASecComb.LMA + 72) 68 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_12; dand3 dR_12 as ws LW RW | destruct (img_rw_words v (ASecComb.LMA + 72) 68 ltac:(ulma; lia) ltac:(ulma; lia)) as (ws & LW & RW) ]).
    destruct ws as [|na [|nf [|ca [|mx bsl]]]]; cbn in LW; try lia.
    exists na, nf, ca, mx, bsl. split; [| lia].
    refine (rwc_rebytes _ _ _ _ _ _ RW).
    - cbn -[u64s]. rewrite u64s_length. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [exact I | lia].
    - cbn [map cells_bytes cbytes]. rewrite app_nil_r, CB8_bytes. reflexivity.
  Qed.
  Lemma bkc_GST : exists (sta stm : word), rw_cells rsegs v (ASecComb.LSTAT + 16) [C8 sta; C8 stm].
  Proof.
    (first [ pose proof ((img_rw_words v (ASecComb.LSTAT + 16) 2 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_13; dex1 dR_13 as ws; destruct dR_13 as [LW RW] | pose proof ((img_rw_words v (ASecComb.LSTAT + 16) 2 ltac:(ulma; lia) ltac:(ulma; lia))) as dR_13; dand3 dR_13 as ws LW RW | destruct (img_rw_words v (ASecComb.LSTAT + 16) 2 ltac:(ulma; lia) ltac:(ulma; lia)) as (ws & LW & RW) ]).
    destruct ws as [|sta [|stm [|]]]; cbn in LW; try lia. exists sta, stm. exact RW.
  Qed.
  Lemma bkc_nch0 : 0 <= nch <= sr_reserved (a_sec A) /\ sr_reserved (a_sec A) <= kChunksBlockCount /\
                   (sr_reserved (a_sec A) = 0 \/ sr_reserved (a_sec A) = kChunksBlockCount).
  Proof. (first [ pose proof ((wtS A W)) as dR_14; dand4 dR_14 as _ LEN RES _ | destruct (wtS A W) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in *. lia. Qed.
  Lemma bkc_pa0 : aobj pa kPtrArrayReserve /\ pa + kPtrArrayReserve <= alloc_ceiling /\ pa mod 4096 = 0.
  Proof.
    pose proof (place_factsT A W) as PF. cbv zeta in PF. (first [ dand13 PF as _ _ _ _ _ _ _ _ _ _ _ (PPA & PPB & AL) _ | destruct PF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (PPA & PPB & AL) & _) ]).
    split; [apply aobj_app_rangeA; exact PPA|]. split; [exact PPB| exact AL].
  Qed.

  Lemma bk_nch : 1 <= nch < 2^20 /\ nch <= sr_reserved (a_sec A) /\ sr_reserved (a_sec A) = kChunksBlockCount /\ chunks <> [].
  Proof.
    (first [ pose proof (bkc_nch0) as dR_16; dand3 dR_16 as N1 N2 N3 | pose proof bkc_nch0 as (N1 & N2 & N3) ]).
    assert (NE : chunks <> []) by (intros E; pose proof bk_In as X; rewrite E in X; destruct X).
    assert (NZ : (0 < length chunks)%nat) by (destruct (sr_chunks (a_sec A)); [congruence| cbn; lia]).
    unfold kChunksBlockCount in *. destruct N3 as [N3|N3]; [lia|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia. exact NE.
  Qed.

  Lemma bk_pa : aobj pa (8 * nch) /\ pa + 8 * nch <= alloc_ceiling /\ pa mod 8 = 0 /\ aobj pa kPtrArrayReserve /\ 8 * nch <= kPtrArrayReserve.
  Proof.
    (first [ pose proof (bkc_pa0) as dR_17; dand3 dR_17 as A1 A2 A3 | pose proof bkc_pa0 as (A1 & A2 & A3) ]). (first [ pose proof (bk_nch) as dR_18; dand4 dR_18 as N1 N2 N3 _ | pose proof bk_nch as (N1 & N2 & N3 & _) ]). unfold kPtrArrayReserve, kChunksBlockCount in *.
    split; [apply (aobj_sub _ _ _ _ A1); lia|]. split; [lia|]. split; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact A3]|]. split; [exact A1| lia].
  Qed.


  Lemma bk_arr : u64arr rsegs v pa sec_words.
  Proof.
    pose proof SR as S. unfold sec_repr_ in S. cbv zeta in S. (first [ dand7 S as _ _ _ _ _ CH PM | destruct S as (_ & _ & _ & _ & _ & CH & PM) ]).
    (first [ pose proof (bk_pa) as dR_20; dand5 dR_20 as A1 A2 A3 A4 A5 | pose proof bk_pa as (A1 & A2 & A3 & A4 & A5) ]). pose proof (aobj_facts _ _ A1) as AF. pose proof alloc_ceiling_val as CE.
    (first [ pose proof (bk_nch) as dR_21; dand4 dR_21 as N1 N2 N3 _ | pose proof bk_nch as (N1 & N2 & N3 & _) ]).
    split.
    - apply bytes_at_u64s; [lia| rewrite sec_words_length; lia|].
      intros j w E. unfold sec_words in E. rewrite nth_error_map in E. destruct (nth_error chunks j) as [c|] eqn:Ec; [| discriminate].
      cbn in E. injection E as <-. destruct (CH j c Ec) as [U _]. exact U.
    - rewrite sec_words_length. apply mapped_wr_at; [| lia| lia]. intros k Hk. apply PM. unfold kChunksBlockCount in N3. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_hdr_at : forall j c, nth_error chunks j = Some c ->
    rw_cells rsegs v (cs_map c) [C8 (wz (cs_map c)); C8 (wz (map_size (cs_n c))); C8 (wz (needed_size2 (cs_n c))); C8 (wz (Z.of_nat j))].
  Proof.
    intros j c E. pose proof SR as S. unfold sec_repr_ in S. cbv zeta in S. (first [ dand7 S as _ _ _ _ _ CH _ | destruct S as (_ & _ & _ & _ & _ & CH & _) ]).
    destruct (CH j c E) as [_ R]. exact R.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_sep_chunks : forall j k c d, nth_error chunks j = Some c -> nth_error chunks k = Some d -> j <> k ->
    apart (cs_map c) (map_size (cs_n c)) (cs_map d) (map_size (cs_n d)).
  Proof.
    intros j k c d Ej Ek NE. unfold apart.
    exact (bm_sepT A (15 + j) (15 + k) _ _ _ _ W (bm_nth_sec A j c Ej) (bm_nth_sec A k d Ek) ltac:(lia)).
  Qed.
  Lemma bk_sep_fixed : forall j c, nth_error chunks j = Some c ->
    apart (cs_map c) (map_size (cs_n c)) pa kPtrArrayReserve /\ apart (cs_map c) (map_size (cs_n c)) thr 4096 /\
    apart (cs_map c) (map_size (cs_n c)) (p_ctx P) 0x10000 /\ apart (cs_map c) (map_size (cs_n c)) (p_nodes0 P) kDepotNodesBlock /\
    apart (cs_map c) (map_size (cs_n c)) (p_frames0 P) kStackStoreBlockBytes.
  Proof.
    intros j c E. (first [ pose proof ((bm_nth_fixed A)) as dR_23; dand10 dR_23 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]). pose proof (bm_nth_sec A j c E) as Es.
    unfold a_pa, a_thr, a_ctx, a_nodes0, a_frames0 in *. unfold apart.
    split; [exact (bm_sepT A _ _ _ _ _ _ W Es E1 ltac:(lia))|]. split; [exact (bm_sepT A _ _ _ _ _ _ W Es E4 ltac:(lia))|].
    split; [exact (bm_sepT A _ _ _ _ _ _ W Es E5 ltac:(lia))|]. split; [exact (bm_sepT A _ _ _ _ _ _ W Es E7 ltac:(lia))| exact (bm_sepT A _ _ _ _ _ _ W Es E8 ltac:(lia))].
  Qed.
  Lemma bk_sep_pa : apart pa kPtrArrayReserve thr 4096 /\ apart pa kPtrArrayReserve (p_ctx P) 0x10000 /\
                    apart pa kPtrArrayReserve (p_nodes0 P) kDepotNodesBlock /\ apart pa kPtrArrayReserve (p_frames0 P) kStackStoreBlockBytes /\
                    apart (p_ctx P) 0x10000 thr 4096.
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_24; dand10 dR_24 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    unfold a_pa, a_thr, a_ctx, a_nodes0, a_frames0 in *. unfold apart.
    split; [exact (bm_sepT A _ _ _ _ _ _ W E1 E4 ltac:(lia))|]. split; [exact (bm_sepT A _ _ _ _ _ _ W E1 E5 ltac:(lia))|].
    split; [exact (bm_sepT A _ _ _ _ _ _ W E1 E7 ltac:(lia))|]. split; [exact (bm_sepT A _ _ _ _ _ _ W E1 E8 ltac:(lia))| exact (bm_sepT A _ _ _ _ _ _ W E5 E4 ltac:(lia))].
  Qed.

  (* [comment removed for export] *)
  Lemma bk_chunk : forall c, In c chunks ->
    aobj (cs_map c) (map_size (cs_n c)) /\ cs_map c mod 4096 = 0 /\ cs_map c + map_size (cs_n c) <= alloc_ceiling /\
    4096 + 32 <= map_size (cs_n c) /\ 0x60a000 <= cs_map c /\ kMaxPrimaryUser < cs_n c < REQ_MAX /\ 0 <= needed_size2 (cs_n c) < 2^64.
  Proof.
    intros c Hc. (first [ pose proof ((sec_chunk_boundsT A _ W Hc)) as dR_25; dand5 dR_25 as B1 B2 B3 B4 B5 | pose proof (sec_chunk_boundsT A _ W Hc) as (B1 & B2 & B3 & B4 & B5) ]). pose proof alloc_ceiling_val as CE.
    pose proof (needed_size_ge (cs_n c)) as NG. rewrite needed_size2_secondary in B5 |- * by lia. pose proof (rounded_size_ge (cs_n c)) as RG.
    destruct c as [mb n1]. cbn [cs_map cs_n] in *.
    pose proof (known_range A v [] AR (ChS (CS mb n1)) n1 ltac:(cbn; split; [exact Hc| split; [lia| reflexivity]])) as [KR _]. cbn [chunk_lo] in KR.
    split; [apply (proj1 (aobj_app_rangeA _ _)); exact B3|]. split; [exact B2|]. split; [exact B4|]. split; [kung_all; lia|]. split; [exact KR|]. split; [lia|].
    unfold needed_size, REQ_MAX in *. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_nearest : nearest sec_words (p + -16) = h.
  Proof.
    (first [ pose proof (bk_geo) as dR_26; dand11 dR_26 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof bk_geo as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]). destruct bk_idx as [i NTH].
    pose proof alloc_ceiling_val as CE.
    apply nearest_spec.
    - lia.
    - exists (Z_to_bv 64 h). split; [unfold sec_words; apply in_map_iff; exists (CS h n0); split; [reflexivity| exact bk_In]|].
      apply unsigned_lit. lia.
    - intros w Hw LE. (first [ pose proof ((sec_words_In A w Hw)) as dR_27; dex1 dR_27 as c; destruct dR_27 as [Hc ->] | pose proof ((sec_words_In A w Hw)) as dR_27; dand3 dR_27 as c Hc -> | destruct (sec_words_In A w Hw) as (c & Hc & ->) ]). (first [ pose proof ((bk_chunk c Hc)) as dR_28; dand7 dR_28 as C1 C2 C3 C4 C5 C6 _ | pose proof (bk_chunk c Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & _) ]).
      rewrite unsigned_lit in LE |- * by lia.
      destruct (In_nth_error' _ _ Hc) as [j Ej].
      destruct (Nat.eq_dec j i) as [->|NE]; [rewrite NTH in Ej; injection Ej as <-; cbn [cs_map]; lia|].
      pose proof (bk_sep_chunks j i c (CS h n0) Ej NTH NE) as D. cbn [cs_map cs_n] in D. unfold apart in D. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bk_last : nth_error chunks (Z.to_nat (nch - 1)) = Some sec_last /\ In sec_last chunks /\
                  nth_error sec_words (Z.to_nat (nch - 1)) = Some (Z_to_bv 64 (cs_map sec_last)) /\
                  bv_unsigned (Z_to_bv 64 (cs_map sec_last)) = cs_map sec_last.
  Proof.
    (first [ pose proof (bk_nch) as dR_29; dand4 dR_29 as N1 _ _ NE | pose proof bk_nch as (N1 & _ & _ & NE) ]). pose proof alloc_ceiling_val as CE.
    assert (E1 : nth_error chunks (Z.to_nat (nch - 1)) = Some sec_last).
    { replace (Z.to_nat (nch - 1)) with (length chunks - 1)%nat by lia. unfold sec_last. apply nth_error_last_. exact NE. }
    assert (IN : In sec_last chunks) by (eapply nth_error_In; exact E1).
    (first [ pose proof ((bk_chunk _ IN)) as dR_30; dand6 dR_30 as C1 _ C3 C4 C5 _ | pose proof (bk_chunk _ IN) as (C1 & _ & C3 & C4 & C5 & _) ]).
    split; [exact E1|]. split; [exact IN|]. split; [apply sec_words_nth; exact E1| apply unsigned_lit; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma bk_regs : exists (srt nf ca gA gM : Z),
    0 <= srt < 256 /\ 0 <= nf < 2^64 /\ 0 <= ca < 2^64 /\ 0 <= gA < 2^64 /\ 0 <= gM < 2^64 /\
    rw_cells rsegs v 0xb1dd0 [C8 (wz nch); C1 (Z_to_bv 8 srt)] /\
    rw_cells rsegs v 0xb1de8 [C8 (wz nf); C8 (wz ca)] /\
    rw_cells rsegs v 0xb2000 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)] /\
    rw_cells rsegs v 0xb2018 [C8 (wz gA); C8 (wz gM)].
  Proof.
    pose proof bkc_LREG as LREG. destruct bkc_LCS as [cs LCS].
    (first [ dex5 bkc_LSTA as na nf ca mx bsl; destruct bkc_LSTA as [LSTA _] | dand7 bkc_LSTA as na nf ca mx bsl LSTA _ | destruct bkc_LSTA as (na & nf & ca & mx & bsl & LSTA & _) ]). (first [ dex2 bkc_GST as sta stm; rename bkc_GST into GST | dand3 bkc_GST as sta stm GST | destruct bkc_GST as (sta & stm & GST) ]).
    pose proof bkc_LMTX as LMTX. unfold ASecComb.LMA, ASecComb.LSTAT in *.
    exists (bv_unsigned cs), (bv_unsigned nf), (bv_unsigned ca), (bv_unsigned sta), (bv_unsigned stm).
    assert (Hcs : 0 <= bv_unsigned cs < 256) by (pose proof (bv_unsigned_in_range _ cs) as X; unfold bv_modulus in X; cbn in X; lia). pose proof (zr_word nf). pose proof (zr_word ca). pose proof (zr_word sta). pose proof (zr_word stm). unfold inr64 in *.
    rewrite !Z_to_bv_bv_unsigned. replace (Z_to_bv 8 (bv_unsigned cs)) with cs by (symmetry; exact (definitions.Z_to_bv_bv_unsigned _ cs)).
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split.
    { apply (rw_cells_app_split _ _ [C8 (wz (sr_reserved (a_sec A)))] [C8 (wz nch)]) in LREG as [_ LREG]. cbn [cells_size csize Nat.add] in LREG.
      change (0xb1d98 + 48 + Z.of_nat 8) with 0xb1dd0 in LREG. change (0xb1d98 + 64) with (0xb1dd0 + Z.of_nat (cells_size [C8 (wz nch)])) in LCS.
      exact (rw_cells_app_join _ _ [C8 (wz nch)] [C1 cs] LREG LCS). }
    split.
    { apply (rw_cells_app_split _ _ [C8 na] [C8 nf; C8 ca; C8 mx; CB 512 (u64s bsl)]) in LSTA as [_ LSTA]. cbn [cells_size csize Nat.add] in LSTA.
      apply (rw_cells_app_split _ _ [C8 nf; C8 ca] [C8 mx; CB 512 (u64s bsl)]) in LSTA as [LSTA _].
      change (0xb1d98 + 72 + Z.of_nat 8) with 0xb1de8 in LSTA. exact LSTA. }
    split; [exact LMTX| exact GST].
  Qed.

  (* [comment removed for export] *)
  Lemma bk_consts : ro_cells rsegs v LMA_L [C8 (wz 4096); C8 (wz pa)] /\ ro_cells rsegs v 0xa91d0 [C8 (wz 1)] /\
                    ro_cells rsegs v 0xb1d78 [C8 (wz sb)] /\ ro_cells rsegs v 0xa9180 [C8 (wz CF)].
  Proof.
    split; [| split; [| split]].
    - unfold LMA_L. pose proof bkc_LMA0 as X. pose proof bkc_LPA8 as Y. unfold ASecComb.LMA in X, Y.
      exact (ro_join2 v 0xb1d98 _ _ X Y).
    - cell Hx 0xa91d0 (le8 (Z_to_bv 64 1)). apply bytes_ro_C8. exact Hx.
    - exact (rk_SBc A v [] AR).
    - cell Hx 0xa9180 (le8 (Z_to_bv 64 0x146ee8)). unfold CF. apply bytes_ro_C8. exact Hx.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma bk_thr_stats : exists rf rfd mu mdv : Z,
    0 <= rf < 2^64 /\ 0 <= rfd < 2^64 /\ 0 <= mu < 2^64 /\ 0 <= mdv < 2^64 /\
    rw_cells rsegs v (thr + 2840) [C8 (wz rf); C8 (wz rfd)] /\ rw_cells rsegs v (thr + 2888) [C8 (wz mu); C8 (wz mdv)].
  Proof.
    (first [ pose proof ((rk_thr_words A v [] AR (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_33; dex1 dR_33 as ws1; destruct dR_33 as [L1 R1] | pose proof ((rk_thr_words A v [] AR (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_33; dand3 dR_33 as ws1 L1 R1 | destruct (rk_thr_words A v [] AR (thr + 2840) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia)) as (ws1 & L1 & R1) ]).
    (first [ pose proof ((rk_thr_words A v [] AR (thr + 2888) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_34; dex1 dR_34 as ws2; destruct dR_34 as [L2 R2] | pose proof ((rk_thr_words A v [] AR (thr + 2888) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia))) as dR_34; dand3 dR_34 as ws2 L2 R2 | destruct (rk_thr_words A v [] AR (thr + 2888) 2 ltac:(unfold off_th_stats; lia) ltac:(unfold off_th_stats; cbn; lia)) as (ws2 & L2 & R2) ]).
    destruct ws1 as [|a1 [|b1 [|]]]; cbn in L1; try lia. destruct ws2 as [|a2 [|b2 [|]]]; cbn in L2; try lia. cbn [map] in R1, R2.
    exists (bv_unsigned a1), (bv_unsigned b1), (bv_unsigned a2), (bv_unsigned b2).
    pose proof (zr_word a1). pose proof (zr_word b1). pose proof (zr_word a2). pose proof (zr_word b2). unfold inr64 in *.
    rewrite !Z_to_bv_bv_unsigned. repeat (split; [lia|]). exact (conj R1 R2).
  Qed.

  (* [comment removed for export] *)
  Section WithEntry.
    Hypothesis LE : lentry_cells sb v (QE (ChS (CS h n0)) n0).

    (* [comment removed for export] *)
    Lemma bk_cells : exists (b1 : Z) (ctxw : word),
      0 <= b1 < 256 /\ Z.land b1 0x7f = kHdrByte1Malloc /\
      rw_cells rsegs v (p + -16) [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n0)); C4 (wz n0)] /\
      rw_cells rsegs v (p + -8) [C8 ctxw] /\
      rw_cells rsegs v (h + 4096) [C8 (wz kAllocBegMagic); C8 (wz (p + -16))] /\
      mapped v h msz.
    Proof.
      (first [ pose proof (bk_geo) as dR_35; dand11 dR_35 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof bk_geo as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]). pose proof alloc_ceiling_val as CE.
      assert (US : user_size n0 = n0) by (unfold user_size; pose proof NQB as NQ; unfold kMaxPrimaryUser in NQ; destruct (Z.eqb_spec n0 0); lia).
      destruct LE as (HR & JK & MP & SHQ). cbn [qe_chunk qe_n] in HR, JK, MP, SHQ.
      cbn [chunk_lo chunk_hi cs_map cs_n] in MP. replace (h + map_size n0 - h) with msz in MP by lia.
      unfold hdr_repr_ in HR. cbv zeta in HR. cbn [user_of alloc_beg cs_map cs_n] in HR. unfold sec_user_beg, sec_alloc_beg, kPageSize in HR.
      replace (h + 4096 + 2048) with p in HR by lia. rewrite US in HR.
      destruct HR as [(id & b1 & IDR & B1R & B1M & HC) MG].
      unfold chunk_hdr_cells in HC. cbn [ch_state ch_b1 ch_size ch_ctx] in HC.
      apply (rw_cells_app_split v (p - 16) [C1 (b8 CHUNK_QUARANTINE); C1 (b8 b1); C2 (w64 (size_hi n0)); C4 (w64 n0)] [C8 (w64 id)]) in HC as [HC1 HC2].
      cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HC2.
      destruct (MG ltac:(lia)) as [M1 M2].
      exists b1, (w64 id). split; [exact B1R|]. split; [exact B1M|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
      - replace (p + -16) with (p - 16) by lia. exact HC1.
      - replace (p + -8) with (p - 16 + 8) by lia. exact HC2.
      - apply ro_rw.
        + apply (ro_join2 v (h + 4096) (C8 (wz kAllocBegMagic)) (C8 (wz (p + -16)))); [apply u64_ro; exact M1| cbn [csize]; apply u64_ro; replace (p + -16) with (p - 16) by lia; exact M2].
        + cbn. intros k Hk. replace (h + 4096 + k) with (h + (4096 + k)) by lia. apply MP. lia.
      - exact MP.
    Qed.

    (* [comment removed for export] *)
    Lemma bk_shadow : bytes_at rsegs v (sh h) (sshadow_quar n0) /\ length (sshadow_quar n0) = Z.to_nat (msz / 8) /\
                      rw_cells rsegs v (sh h) [CB (Z.to_nat (msz / 8)) (sshadow_quar n0)].
    Proof.
      (first [ pose proof (bk_geo) as dR_36; dand11 dR_36 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof bk_geo as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]). (first [ pose proof (bk_shr) as dR_37; dand4 dR_37 as SHA _ _ SIDE | pose proof bk_shr as (SHA & _ & _ & SIDE) ]).
      destruct LE as (_ & _ & _ & B). cbn [qe_chunk qe_n] in B.
      assert (US : user_size n0 = n0) by (unfold user_size; pose proof NQB as NQ; unfold kMaxPrimaryUser in NQ; destruct (Z.eqb_spec n0 0); lia).
      pose proof (Z_div_mod_eq_full msz 4096) as XM. rewrite MSZAL, Z.add_0_r in XM.
      unfold kMaxPrimaryUser, REQ_MAX in NR.
      assert (LEN : length (sshadow_quar n0) = Z.to_nat (msz / 8)).
      { unfold sshadow_quar, fa8, fd8. rewrite !length_app, !repeat_length, US.
        pose proof (Z_div_mod_eq_full (n0 + 7) 8). pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)). lia. }
      split; [exact B|]. split; [exact LEN|].
      apply (bytes_rw_CB v (sh h) (sshadow_quar n0) (Z.to_nat (msz / 8)) B LEN). unfold sh. kung_all. lia.
    Qed.
  End WithEntry.

  (* [comment removed for export] *)
  Section AtIndex.
    Variable i : nat.
    Hypothesis NTH : nth_error chunks i = Some (CS h n0).

    Lemma bk_i : 0 <= Z.of_nat i < nch /\ nth_error sec_words (Z.to_nat (Z.of_nat i)) = Some (Z_to_bv 64 h).
    Proof.
      split; [pose proof (nth_error_Some_lt _ _ _ NTH); lia|]. rewrite Nat2Z.id. exact (sec_words_nth A i _ NTH).
    Qed.

    Lemma bk_hdr : rw_cells rsegs v h [C8 (wz h); C8 (wz msz); C8 (wz (needed_size2 n0)); C8 (wz (Z.of_nat i))] /\ 0 <= needed_size2 n0 < 2^64.
    Proof.
      split; [exact (bk_hdr_at i _ NTH)|]. (first [ pose proof ((bk_chunk _ bk_In)) as dR_38; dand7 dR_38 as _ _ _ _ _ _ X | pose proof (bk_chunk _ bk_In) as (_ & _ & _ & _ & _ & _ & X) ]). exact X.
    Qed.

    (* [comment removed for export] *)
    Lemma bk_sep_h : apart h msz pa (8 * nch) /\ apart h msz thr 4096 /\ apart h msz (p_ctx P) 0x10000 /\
                     apart h msz (p_nodes0 P) kDepotNodesBlock /\ apart h msz (p_frames0 P) kStackStoreBlockBytes.
    Proof.
      (first [ pose proof ((bk_sep_fixed i _ NTH)) as dR_39; dand5 dR_39 as D1 D2 D3 D4 D5 | pose proof (bk_sep_fixed i _ NTH) as (D1 & D2 & D3 & D4 & D5) ]). cbn [cs_map cs_n] in *. (first [ pose proof (bk_pa) as dR_40; dand5 dR_40 as _ _ _ _ LE | pose proof bk_pa as (_ & _ & _ & _ & LE) ]).
      pose proof bk_nch as (N1 & _). unfold apart in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma bk_hl : let hl := Z_to_bv 64 (cs_map sec_last) in let hla := cs_map sec_last in
      aobj hla 32 /\ hla + 32 <= alloc_ceiling /\ hla mod 8 = 0 /\ bv_unsigned hl = hla /\
      (hla = h \/ apart hla 32 h msz) /\
      (hla = h \/ rw_cells rsegs v hla [C8 (wz hla); C8 (wz (map_size (cs_n sec_last))); C8 (wz (needed_size2 (cs_n sec_last))); C8 (wz (nch - 1))]) /\
      apart hla 32 pa (8 * nch) /\ apart hla 32 thr 4096 /\ apart hla 32 (p_ctx P) 0x10000 /\
      apart hla 32 (p_nodes0 P) kDepotNodesBlock /\ apart hla 32 (p_frames0 P) kStackStoreBlockBytes.
    Proof.
      cbv zeta. (first [ pose proof (bk_last) as dR_41; dand4 dR_41 as E1 IN E2 E3 | pose proof bk_last as (E1 & IN & E2 & E3) ]). (first [ pose proof ((bk_chunk _ IN)) as dR_42; dand7 dR_42 as C1 C2 C3 C4 C5 C6 _ | pose proof (bk_chunk _ IN) as (C1 & C2 & C3 & C4 & C5 & C6 & _) ]).
      (first [ pose proof ((bk_sep_fixed _ _ E1)) as dR_43; dand5 dR_43 as D1 D2 D3 D4 D5 | pose proof (bk_sep_fixed _ _ E1) as (D1 & D2 & D3 & D4 & D5) ]). (first [ pose proof (bk_pa) as dR_44; dand5 dR_44 as _ _ _ _ LE | pose proof bk_pa as (_ & _ & _ & _ & LE) ]). pose proof bk_nch as (N1 & _).
      split; [apply (aobj_sub _ _ _ _ C1); lia|]. split; [lia|]. split; [apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact C2]|]. split; [exact E3|].
      assert (CASE : cs_map sec_last = h \/ (Z.to_nat (nch - 1) <> i)).
      { destruct (Nat.eq_dec (Z.to_nat (nch - 1)) i) as [EQ|NE]; [left| right; exact NE]. rewrite EQ, NTH in E1. injection E1 as <-. reflexivity. }
      split.
      { destruct CASE as [EQ|NE]; [left; exact EQ| right]. pose proof (bk_sep_chunks _ _ _ _ E1 NTH NE) as D. cbn [cs_map cs_n] in D. unfold apart in *. lia. }
      split.
      { destruct CASE as [EQ|NE]; [left; exact EQ| right]. pose proof (bk_hdr_at _ _ E1) as R.
        replace (Z.of_nat (Z.to_nat (nch - 1))) with (nch - 1) in R by lia. exact R. }
      unfold apart in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
    Qed.
  End AtIndex.
End BusySecKit.
End AFreeKX.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeKH.

Module AFreeKM.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require SpinAlg Ledger Hull Restrict Refund Lazyiq4 Fixej5z EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Refund.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.SpinAlg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Ledger OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Hull OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Restrict OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Lazyiq4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Fixej5z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.EvtAcct OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc.Refund.Madv3tp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocI AMalmys ATransp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ABudget ACover AFreeB6 ANodijx APgGeo AFreeX1 AFreeX2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ACover OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ATranspR AFreeRS AFreeRX AFreeRI AFreeRT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeRK2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeKH.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKR.AFreeKX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
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
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser in *.

Section KChain.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 kb : Z) (es : list qentry) (more : list batch) (i : nat).
  (* [comment removed for export] *)
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A (aview_of (pa_hull A) m).
  Hypothesis WR : WFR A.
  Hypothesis LQ : a_qlimbo A = BA kb (QE (ChS (CS (p - 6144) n0)) n0 :: es) :: more.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some (CS (p - 6144) n0).
  Hypothesis LG : aledger_ AL_pasan (a_pl A) (a_reg A) (a_sec A) md.
  Hypothesis COV : acover_ LPA (a_pl A) (a_sec A) (m_vmmaps md).
  Hypothesis CEI : alloc_top (m_vmmaps md) = alloc_ceiling.
  Hypothesis HMI : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md.
  Hypothesis HLT : m_halted md = None.

  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).
  #[warnings="-notation-for-abbreviation"] Local Notation len := (a8_pend (p - 6144) (map_size n0) - a8_pbeg (p - 6144)).

  Let W : WFT A. Proof. exact (proj1 AR). Qed.
  Let S0 : In (CS h n0) chunks. Proof. eapply nth_error_In. exact NTH. Qed.
  (* [comment removed for export] *)
  Lemma bk_kgeo : kgeo p n0.
  Proof. exact (conj (bk_geo A _ p n0 kb es more AR WR LQ) (bk_shr A _ p n0 kb es more AR WR LQ)). Qed.
  Let G : kgeo p n0. Proof. exact bk_kgeo. Qed.
  Let NQ' : kMaxPrimaryUser < n0. Proof. (first [ pose proof ((proj1 G)) as dR_1; dand10 dR_1 as _ _ _ _ _ _ _ _ NR _ | destruct (proj1 G) as (_ & _ & _ & _ & _ & _ & _ & _ & NR & _) ]). exact (proj1 NR). Qed.

  (* [comment removed for export] *)
  Lemma klen_facts : 0 < len /\ pbeg + len = pend /\ 0 < pbeg /\ pend <= kHighMemBeg /\ pbeg mod 4096 = 0 /\ len mod 4096 = 0 /\
                    bv_unsigned (wz pbeg) = pbeg /\ bv_unsigned (wz len) = len /\ bv_unsigned (wz h) = h /\ bv_unsigned (wz msz) = msz /\
                    0x60a000 <= h /\ h + msz <= alloc_ceiling /\ 0 < msz /\ h mod 4096 = 0 /\ msz mod 4096 = 0 /\
                    page_round_up_Z len = len /\ page_round_up_Z msz = msz.
  Proof.
    (first [ pose proof ((ka8_geo p n0 G)) as dR_2; dand15 dR_2 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof (ka8_geo p n0 G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
    (first [ pose proof ((proj1 G)) as dR_3; dand11 dR_3 as HLO HAL MSZ MSZAL HHI _ _ _ _ H5 _ | pose proof (proj1 G) as (HLO & HAL & MSZ & MSZAL & HHI & _ & _ & _ & _ & H5 & _) ]). pose proof alloc_ceiling_val as CE.
    assert (LM : len mod 4096 = 0) by (rewrite <- Zminus_mod_idemp_l, M3, <- Zminus_mod_idemp_r, M2; reflexivity).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try (kung_all; lia); try (apply unsigned_lit; kung_all; lia); try assumption.
    - unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full len 4096) as Q. rewrite LM, Z.add_0_r in Q.
      set (q := len / 4096) in *. clearbody q. clear -Q. rewrite Q. replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by lia.
      rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
    - unfold page_round_up_Z, page_size. pose proof (Z_div_mod_eq_full msz 4096) as Q. rewrite MSZAL, Z.add_0_r in Q.
      set (q := msz / 4096) in *. clearbody q. clear -Q. rewrite Q. replace (4096 * q + 4096 - 1) with (q * 4096 + 4095) by lia.
      rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma kfsm_shadow_map : exists bS sS, In (bS, sS) (big_maps A) /\ bS <= pbeg /\ pend <= bS + sS /\ 0 <= bS /\ bS + sS <= 2^47.
  Proof.
    (first [ pose proof ((ka8_geo p n0 G)) as dR_4; dand15 dR_4 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof (ka8_geo p n0 G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
    (first [ pose proof ((bm_nth_fixed A)) as dR_5; dand5 dR_5 as _ _ E2 E3 _ | pose proof (bm_nth_fixed A) as (_ & _ & E2 & E3 & _) ]).
    destruct SIDE as [(X1 & X2 & X3)|(X1 & X2 & X3)].
    - exists kHighShadowMapBeg, kHighShadowMapSize. split; [eapply nth_error_In; exact E2|]. kung_all. unfold kHighShadowMapSize. lia.
    - exists kLowShadowMapBeg, 0x10000000. split; [eapply nth_error_In; exact E3|]. pose proof (pg_facts (sh h)) as (A1 & _). kung_all. lia.
  Qed.

  Section Models.
    Variables (md1 md2 md3 md4 md5 : Model).
    Hypothesis SB1 : same_but_materialized md md1.
    Hypothesis MD2 : md2 = madvise_model (wz pbeg) (wz len) md1.   (* [comment removed for export] *)
    Hypothesis SB3 : same_but_materialized md2 md3.
    Hypothesis MD4 : md4 = munmap_modelL (wz h) (wz msz) md3.
    Hypothesis SB5 : same_but_materialized md4 md5.
    Hypothesis HI1 : MInv (pa_hull A) (pa_lhull A) (pa_eager A) md1.
    Hypothesis HI3 : exists Hx HLx Ex, MInv Hx HLx Ex md3.   (* [comment removed for export] *)

    Lemma kvmmaps1 : m_vmmaps md1 = m_vmmaps md.  Proof. exact (same_but_materialized_vmmaps _ _ SB1). Qed.
    Lemma kvmmaps3 : m_vmmaps md3 = m_vmmaps md.
    Proof. rewrite (same_but_materialized_vmmaps _ _ SB3), MD2, madvise_model_vmmaps, kvmmaps1. reflexivity. Qed.
    Lemma kvmmaps5 : m_vmmaps md5 = munmap_vmmaps (m_vmmaps md) (wz h) (wz msz).
    Proof. rewrite (same_but_materialized_vmmaps _ _ SB5), MD4, munmap_modelL_vmmaps, kvmmaps3. reflexivity. Qed.
    Lemma kmaps3 : vm_maps (m_vmmaps md3) = vm_maps (m_vmmaps md).
    Proof. rewrite kvmmaps3. reflexivity. Qed.
    Lemma kmaps5 : vm_maps (m_vmmaps md5) = map_remove (vm_maps (m_vmmaps md)) (wz h).
    Proof. rewrite kvmmaps5. reflexivity. Qed.
    Lemma kresv5 : vm_reserved (m_vmmaps md5) = vm_reserved (m_vmmaps md) /\ vm_reserved (m_vmmaps md3) = vm_reserved (m_vmmaps md) /\ vm_reserved (m_vmmaps md1) = vm_reserved (m_vmmaps md).
    Proof. rewrite kvmmaps5, kvmmaps3, kvmmaps1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

    (* [comment removed for export] *)
    Lemma kfsm_in_maps : In (wz h, wz msz) (vm_maps (m_vmmaps md)).
    Proof. destruct LG as (L1 & _). apply L1. eapply nth_error_In. exact (bm_nth_sec A _ _ NTH). Qed.
    Lemma kfsm_has : map_has (vm_maps (m_vmmaps md3)) (wz h) (wz msz) = true.
    Proof. rewrite kmaps3. apply In_map_has. exact kfsm_in_maps. Qed.

    Lemma kfsm_eager : eager_map (wz h) (wz msz) md3.
    Proof.
      destruct LG as (_ & _ & _ & _ & _ & L6 & _). pose proof (proj1 (Forall_forall _ _) L6 _ S0) as EM. cbn [cs_map cs_n] in EM.
      apply (eager_map_sbm _ _ md2 md3 SB3). rewrite MD2. apply (eager_map_sbm _ _ md1 _ (madvise_same_but_materialized _ _ md1)).
      exact (eager_map_sbm _ _ md md1 SB1 EM).
    Qed.

    Lemma kfsm_ceil : alloc_top (m_vmmaps md5) = alloc_ceiling /\ alloc_top (m_vmmaps md3) = alloc_ceiling /\ alloc_top (m_vmmaps md1) = alloc_ceiling.
    Proof.
      pose proof CEI as TOP. unfold alloc_top in *. rewrite kvmmaps5, kvmmaps3, kvmmaps1. cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; exact TOP.
    Qed.

    Lemma kfsm_frame : amd_frame md md5.
    Proof.
      pose proof (same_but_materialized_frame _ _ SB1) as F1. pose proof (same_but_materialized_frame _ _ SB3) as F3. pose proof (same_but_materialized_frame _ _ SB5) as F5.
      pose proof (same_but_materialized_frame _ _ (madvise_same_but_materialized (wz pbeg) (wz len) md1)) as C2. rewrite <- MD2 in C2.
      pose proof (munmap_modelL_nonvm (wz h) (wz msz) md3) as C4. rewrite <- MD4 in C4.
      pose proof HLT as HH.
      unfold amd_frame. rewrite kvmmaps5. cbn [vm_limit vm_reserved vm_mmap_base vm_init_sp munmap_vmmaps commit_vmmaps].
      (first [ dand18 F1 as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 A13 A14 A15 A16 A17 _ | destruct F1 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & _) ]).
      (first [ dand18 F3 as B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16 B17 _ | destruct F3 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 & _) ]).
      (first [ dand18 F5 as D1 D2 D3 D4 D5 D6 D7 D8 D9 D10 D11 D12 D13 D14 D15 D16 D17 _ | destruct F5 as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11 & D12 & D13 & D14 & D15 & D16 & D17 & _) ]).
      (first [ dand18 C2 as C21 C22 C23 C24 C25 C26 C27 C28 C29 C210 C211 C212 C213 C214 C215 C216 C217 _ | destruct C2 as (C21 & C22 & C23 & C24 & C25 & C26 & C27 & C28 & C29 & C210 & C211 & C212 & C213 & C214 & C215 & C216 & C217 & _) ]). (first [ dand6 C4 as C41 C42 C43 C44 C45 C46 | destruct C4 as (C41 & C42 & C43 & C44 & C45 & C46) ]).
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try congruence.
      rewrite D17, MD4, <- munmap_model_modelL, munmap_model_halted. rewrite B17, MD2. rewrite madvise_model_halted. rewrite A17. exact HH.
    Qed.

    (* [comment removed for export] *)

    (* [comment removed for export] *)
    Lemma kfsm_shadow_noacc : region_free (vm_noaccess (m_vmmaps md)) (wz pbeg) (wz len) = true.
    Proof.
      (first [ pose proof (klen_facts) as dR_14; dand9 dR_14 as F1 F2 F3 F4 F5 F6 U1 U2 _ | pose proof klen_facts as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & _) ]).
      (first [ pose proof ((ka8_geo p n0 G)) as dR_15; dand15 dR_15 as G1 G2 G3 G4 G5 G6 G7 G8 M1 M2 M3 M4 SHA BIG SIDE | pose proof (ka8_geo p n0 G) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & M1 & M2 & M3 & M4 & SHA & BIG & SIDE) ]).
      destruct LG as (_ & _ & _ & _ & _ & _ & _ & (N1 & N2) & _).   (* [comment removed for export] *)
      destruct SIDE as [(X1 & X2 & X3)|(X1 & X2 & X3)].
      - apply (region_free_sub _ (wz kHighShadowMapBeg) (wz kHighShadowMapSize) _ _ N2); rewrite ?U1, ?U2, !unsigned_lit by (kung_all; unfold kHighShadowMapSize; lia);
          kung_all; unfold kHighShadowMapSize; lia.
      - pose proof (pg_facts (sh h)) as (A1 & _).
        apply (region_free_sub _ (wz kLowShadowMapBeg) (wz (kShadowGapBeg - kLowShadowMapBeg)) _ _ N1); rewrite ?U1, ?U2, !unsigned_lit by (kung_all; lia);
          kung_all; lia.
    Qed.

    (* [comment removed for export] *)
    Lemma kfsm_madvise_args : forall ms, ms_gpr ms 0 = wz pbeg -> ms_gpr ms 1 = wz len -> ms_gpr ms 2 = wz 4 -> madvise_args_ok ms md1.
    Proof.
      intros ms R0 R1 R2. (first [ pose proof (klen_facts) as dR_16; dand17 dR_16 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 H5 HHI MP _ _ PL _ | pose proof klen_facts as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & H5 & HHI & MP & _ & _ & PL & _) ]).
      apply madvise_args_ok_intro; cbv zeta; rewrite ?R0, ?R1, ?R2, ?U1, ?U2, ?PL, ?kvmmaps1; unfold page_size, two_pow_64.
      - exact F5.
      - intros E; apply (f_equal bv_unsigned) in E; rewrite U2, unsigned_lit in E by lia; clear -E F1; lia.
      - reflexivity.
      - clear -F2 F4; kung_all; lia.
      - pose proof (ka8_geo p n0 G) as (G1 & _). (first [ pose proof ((proj2 G)) as dR_17; dand4 dR_17 as _ _ _ SD | pose proof (proj2 G) as (_ & _ & _ & SD) ]).
        rewrite (proj2 (proj2 COV)). apply (pa_reserved_free pbeg len); [clear -G1 SD; kung_all; lia| exact F1| kung_all; lia].
      - (first [ dex2 kfsm_shadow_map as bS sS; dand5 kfsm_shadow_map as Hin B1 B2 B3 B4 | dand7 kfsm_shadow_map as bS sS Hin B1 B2 B3 B4 | destruct kfsm_shadow_map as (bS & sS & Hin & B1 & B2 & B3 & B4) ]). destruct LG as (L1 & _).
        unfold map_contains. apply existsb_exists. exists (wz bS, wz sS). split; [exact (L1 _ _ Hin)|].
        cbn [fst snd]. rewrite !unsigned_lit by (kung_all; lia). rewrite ?U1. apply andb_true_iff. rewrite !Z.leb_le. lia.
      - exact kfsm_shadow_noacc.
    Qed.

    (* [comment removed for export] *)
    Lemma kfsm_lazy3 : m_vm_lazy md3 = m_vm_lazy md.
    Proof. rewrite (sbm_lazy _ _ SB3), MD2, madvise_model_lazy, (sbm_lazy _ _ SB1). reflexivity. Qed.
    Lemma kfsm_lazy_free5 : forall lo hi, lazy_free (m_vm_lazy md) lo hi -> lazy_free (m_vm_lazy md5) lo hi.
    Proof.
      intros lo hi Z0. destruct HI3 as (Hx & HLx & Ex & MI3). rewrite (sbm_lazy _ _ SB5), MD4.
      apply (lazy_free_munmap_MInv Hx HLx Ex _ _ md3 lo hi MI3). rewrite kfsm_lazy3. exact Z0.
    Qed.
    (* [comment removed for export] *)
    Lemma kfsm_ledger : aledger_ AL_pasan P (a_reg A) (sec_remove (a_sec A) i) md5.
    Proof.
      pose proof LG as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9). (first [ pose proof (klen_facts) as dR_19; dand14 dR_19 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 H5 HHI MP _ | pose proof klen_facts as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & H5 & HHI & MP & _) ]).
      destruct HI3 as (Hx & HLx & Ex & MI3). pose proof alloc_ceiling_val as CE.
      unfold aledger_. cbv zeta. rewrite kmaps5. (first [ dand3 kresv5 as RV5 RV3 RV1 | destruct kresv5 as (RV5 & RV3 & RV1) ]). rewrite RV5.
      split; [| split; [exact L2| split; [exact L3| split; [exact L4| split; [| split; [| split]]]]]].
      - (* [comment removed for export] *)
        intros b s Hin. unfold map_remove. apply filter_In. split.
        + apply L1. unfold big_maps_ in Hin |- *. cbn [sec_remove sr_chunks] in Hin. apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right].
          apply in_map_iff in Hin as (c & <- & Hc). apply in_map_iff. exists c. split; [reflexivity|]. apply (rchunks'_in_iff A (CS h n0) i WR NTH) in Hc as [Hc _]. exact Hc.
        + cbn [fst]. unfold bv_eqb. rewrite U3. apply Bool.negb_true_iff. apply Z.eqb_neq.
          assert (BS : 0 <= b /\ 0 < s /\ b + s <= 2^47).
          { apply (bm_boundsT A b s W). unfold big_maps, big_maps_ in Hin |- *. cbn [sec_remove sr_chunks] in Hin. apply in_app_iff in Hin as [Hin|Hin]; apply in_or_app; [left; exact Hin| right].
            apply in_map_iff in Hin as (c & <- & Hc). apply in_map_iff. exists c. split; [reflexivity|]. apply (rchunks'_in_iff A (CS h n0) i WR NTH) in Hc as [Hc _]. exact Hc. }
          rewrite unsigned_lit by lia.
          unfold big_maps_ in Hin. cbn [sec_remove sr_chunks] in Hin. apply in_app_iff in Hin as [Hin|Hin].
          * (* [comment removed for export] *)
            destruct (In_nth_error' _ _ Hin) as [j Hj].
            assert (JL : (j < 15)%nat) by (apply nth_error_Some_lt in Hj; exact Hj).
            assert (Hj' : nth_error (big_maps A) j = Some (b, s)) by (unfold big_maps, big_maps_; rewrite nth_error_app1 by (cbn; lia); exact Hj).
            pose proof (bm_sepT A _ _ _ _ _ _ W Hj' (bm_nth_sec A _ _ NTH) ltac:(lia)) as D. cbn [cs_map cs_n] in D. lia.
          * apply in_map_iff in Hin as (c & E & Hc). injection E as <- <-. apply (rchunks'_in_iff A (CS h n0) i WR NTH) in Hc as [Hc NEc].
            destruct (In_nth_error' _ _ Hc) as [j Hj].
            pose proof (bk_sep_chunks A _ AR j i c (CS h n0) Hj NTH ltac:(intros ->; rewrite NTH in Hj; injection Hj as E; exact (NEc (eq_sym E)))) as D.
            cbn [cs_map cs_n] in D. (first [ pose proof ((bk_chunk A _ AR c Hc)) as dR_21; dand5 dR_21 as _ _ _ C4 _ | pose proof (bk_chunk A _ AR c Hc) as (_ & _ & _ & C4 & _) ]). unfold apart in D. lia.
      - rewrite kvmmaps5. cbn. exact L5.
      - apply Forall_forall. intros c Hc. cbn [sec_remove sr_chunks] in Hc. apply (rchunks'_in_iff A (CS h n0) i WR NTH) in Hc as [Hc _].
        pose proof (proj1 (Forall_forall _ _) L6 c Hc) as EM.
        apply (eager_map_sbm _ _ md4 md5 SB5). rewrite MD4. apply (eager_map_munmap_MInv Hx HLx Ex _ _ _ _ md3 MI3).
        apply (eager_map_sbm _ _ md2 md3 SB3). rewrite MD2. apply (eager_map_sbm _ _ md1 _ (madvise_same_but_materialized _ _ md1)).
        exact (eager_map_sbm _ _ md md1 SB1 EM).
      - apply (cuts_covered_sbm md4 md5 SB5). rewrite MD4. apply (cuts_covered_munmap_MInv Hx HLx Ex _ _ md3 MI3); [rewrite kmaps3; exact kfsm_in_maps| rewrite U4; lia|].
        apply (cuts_covered_sbm md2 md3 SB3). rewrite MD2. apply (cuts_covered_sbm md1 _ (madvise_same_but_materialized _ _ md1)).
        exact (cuts_covered_sbm md md1 SB1 L7).
      - (* [comment removed for export] *)
        destruct L8 as [N1 N2].
        split; [split; apply (noacc_free_sbm _ _ md4 md5 SB5); rewrite MD4; apply noacc_free_munmap; try exact (minv_noacc_nw MI3);
          apply (noacc_free_sbm _ _ md2 md3 SB3); rewrite MD2; apply noacc_free_madvise; apply (noacc_free_sbm _ _ md md1 SB1); assumption|].
        (* [comment removed for export] *)
        destruct L9 as (Z1 & Z2 & Z3). pose proof kfsm_lazy_free5 as T.
        split; [exact (T _ _ Z1)|]. split; [exact (T _ _ Z2)|]. intros c Hc. destruct (Z3 c Hc) as [ZU ZF]. split; apply T; assumption.
    Qed.

    (* [comment removed for export] *)
    Lemma kfsm_cover : acover_ LPA P (sec_remove (a_sec A) i) (m_vmmaps md5).
    Proof.
      pose proof COV as ((fog & FL & FS & COVe & F1' & F2') & C3 & RSV). (first [ pose proof (klen_facts) as dR_22; dand14 dR_22 as F1 F2 F3 F4 F5 F6 U1 U2 U3 U4 H5 HHI MP _ | pose proof klen_facts as (F1 & F2 & F3 & F4 & F5 & F6 & U1 & U2 & U3 & U4 & H5 & HHI & MP & _) ]).
      pose proof alloc_ceiling_val as CE.
      unfold acover_. rewrite kmaps5. destruct kresv5 as (RV5 & _). rewrite RV5. split; [| split; [| exact RSV]].
      - exists fog. split; [exact FL|]. split; [exact FS|]. split; [| split; [| exact F2']].
        + intros e He. apply map_remove_In in He as [He NE]. pose proof (COVe e He) as X. cbv zeta in X |- *.
          destruct X as [X|[X|X]]; [| right; left; exact X| right; right; exact X]. left.
          unfold big_maps_ in X |- *. cbn [sec_remove sr_chunks]. apply in_app_iff in X as [X|X]; apply in_or_app; [left; exact X| right].
          apply in_map_iff in X as (c & E & Hc). apply in_map_iff. exists c. split; [exact E|]. apply (rchunks'_in_iff A (CS h n0) i WR NTH). split; [exact Hc|].
          intros ->. apply NE. cbn [cs_map cs_n] in E. injection E as E1 E2. apply bv_eq. rewrite U3. symmetry. exact E1.
        + intros bs Hbs. unfold map_remove. apply filter_In. split; [exact (F1' bs Hbs)|]. cbn [fst]. unfold bv_eqb. rewrite U3. apply Bool.negb_true_iff. apply Z.eqb_neq.
          (first [ pose proof ((proj1 (Forall_forall _ _) FS bs Hbs)) as dR_23; dand3 dR_23 as S1 S2 S3 | pose proof (proj1 (Forall_forall _ _) FS bs Hbs) as (S1 & S2 & S3) ]). rewrite unsigned_lit by lia.
          (* [comment removed for export] *)
          intros E. pose proof (minv_nooverlap HMI) as NO.
          pose proof (F1' bs Hbs) as INf. pose proof kfsm_in_maps as INm.
          assert (NEQ : (wz (fst bs), wz (snd bs)) <> (wz h, wz msz)).
          { intros EE. pose proof (f_equal (fun x => bv_unsigned (snd x)) EE) as E2. cbn [snd] in E2. rewrite unsigned_lit in E2 by lia. rewrite U4 in E2.
            (first [ pose proof ((proj1 G)) as dR_24; dand9 dR_24 as _ _ _ _ _ _ _ N6 _ | pose proof (proj1 G) as (_ & _ & _ & _ & _ & _ & _ & N6 & _) ]). clear -E2 N6 NQ' S2. unfold kMaxPrimaryUser in NQ'. lia. }
          destruct (nooverlap_In_In _ _ _ NO INf INm) as [D|D]; [exact (NEQ D)|].
          unfold Ledger.hi, Ledger.lo in D. cbn [fst snd] in D. rewrite ?U3, ?U4 in D. rewrite !unsigned_lit in D by lia. rewrite ?U3, ?U4 in D.
          (first [ pose proof ((proj1 G)) as dR_25; dand4 dR_25 as _ _ MSZ _ | pose proof (proj1 G) as (_ & _ & MSZ & _) ]). lia.
      - unfold map_remove. apply filter_In. split; [exact C3|]. cbn [fst]. unfold bv_eqb. rewrite U3, unsigned_lit by (kung_all; lia). apply Bool.negb_true_iff. apply Z.eqb_neq.
        pose proof (proj1 G) as (HLO & _). (first [ pose proof ((aobj_facts _ _ HLO)) as dR_26; dand5 dR_26 as _ NN _ _ SIDE | pose proof (aobj_facts _ _ HLO) as (_ & NN & _ & _ & SIDE) ]). clear -SIDE NN. kung_all. lia.
    Qed.
  End Models.
End KChain.
End AFreeKM.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeKT.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRT OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2.AFreeRK OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRK2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeRP OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKR.AFreeKX OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKR.AFreeKM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeKT.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Ceiling.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac hot2_mid := match goal with H : context [Z.modulo _ _] |- _ => idtac | H : context [Z.div _ _] |- _ => idtac end;
  (repeat match goal with H : context [Z.modulo _ _] |- _ => clear H | H : context [Z.div _ _] |- _ => clear H end); Zify.zify; xlia zchecker.
Local Ltac lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.zt_if_trigger then first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T0 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ] else first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T1 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T2 | hot2_mid | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_T3 ].
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
                        kPtrArrayReserve, kChunksBlockCount, kFakeStackBytes, kPageSize, kSecondaryHeaderSize, kMaxPrimaryUser,
                        kQuarantineBatchBytes in *.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section KSep.
Context {Clg : Ceiling}.
  Variable A : AState.
  Hypothesis W : WFT A.
  Let P := a_pl A.
  #[using="W"] Lemma khit_sep :
    apart (p_thr P) 4096 (a_sb A) (2^37) /\ apart (p_ctx P) 0x10000 (a_sb A) (2^37) /\ apart (p_ctx P) 0x10000 (p_thr P) 4096 /\
    apart (p_nodes0 P) kDepotNodesBlock (a_sb A) (2^37) /\ apart (p_frames0 P) kStackStoreBlockBytes (a_sb A) (2^37) /\
    apart (p_nodes0 P) kDepotNodesBlock (p_thr P) 4096 /\ apart (p_frames0 P) kStackStoreBlockBytes (p_thr P) 4096 /\
    apart (p_nodes0 P) kDepotNodesBlock (p_ctx P) 0x10000 /\ apart (p_frames0 P) kStackStoreBlockBytes (p_ctx P) 0x10000 /\
    aobj (p_nodes0 P) kDepotNodesBlock /\ p_nodes0 P + kDepotNodesBlock <= alloc_ceiling /\
    aobj (p_frames0 P) kStackStoreBlockBytes /\ p_frames0 P + kStackStoreBlockBytes <= alloc_ceiling.
  Proof.
    (first [ pose proof ((bm_nth_fixed A)) as dR_1; dand10 dR_1 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    (first [ pose proof ((sb_factsT A W)) as dR_2; dand5 dR_2 as _ _ HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & _ & HB6 & RSB & SCE) ]). (first [ pose proof ((place_factsT A W)) as dR_3; dand5 dR_3 as _ _ Pn0 Pf0 _ | pose proof (place_factsT A W) as (_ & _ & Pn0 & Pf0 & _) ]). cbv zeta in Pn0, Pf0.
    pose proof alloc_ceiling_val as CE. subst P. unfold a_thr, a_ctx, a_nodes0, a_frames0, a_b6, a_sb in *.
    assert (B6 : forall i b s, i <> 0%nat -> nth_error (big_maps A) i = Some (b, s) -> apart b s (p_sb (a_pl A)) (2^37)).
    { intros i b s Hi Hn. destruct (bm_sepT A i 0 _ _ _ _ W Hn E0 Hi); unfold apart, kSpaceReserve in *; lia. }
    split; [exact (B6 4%nat _ _ ltac:(lia) E4)|]. split; [exact (B6 5%nat _ _ ltac:(lia) E5)|].
    split; [exact (bm_sepT A 5 4 _ _ _ _ W E5 E4 ltac:(lia))|].
    split; [exact (B6 7%nat _ _ ltac:(lia) E7)|]. split; [exact (B6 8%nat _ _ ltac:(lia) E8)|].
    split; [exact (bm_sepT A 7 4 _ _ _ _ W E7 E4 ltac:(lia))|]. split; [exact (bm_sepT A 8 4 _ _ _ _ W E8 E4 ltac:(lia))|].
    split; [exact (bm_sepT A 7 5 _ _ _ _ W E7 E5 ltac:(lia))|]. split; [exact (bm_sepT A 8 5 _ _ _ _ W E8 E5 ltac:(lia))|].
    (first [ dand3 Pn0 as Pn01 Pn02 _ | destruct Pn0 as (Pn01 & Pn02 & _) ]). (first [ dand3 Pf0 as Pf01 Pf02 _ | destruct Pf0 as (Pf01 & Pf02 & _) ]).
    apply (proj1 (aobj_app_rangeA _ _)) in Pn01. apply (proj1 (aobj_app_rangeA _ _)) in Pf01.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
  Qed.
End KSep.

Section KReprS.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (p n0 kb : Z) (es : list qentry) (more : list batch) (i : nat) (v' : mem) (wlo whi : Z).
  Hypothesis AR : WFT A /\ @arepr _ DepotRepL LPA AL_pasan [] A (aview_of (pa_hull A) m).
  Hypothesis WR : WFR A.
  Hypothesis LQ : a_qlimbo A = BA kb (QE (ChS (CS (p - 6144) n0)) n0 :: es) :: more.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some (CS (p - 6144) n0).
  Hypothesis WLO : alloc_ceiling <= wlo.

  #[warnings="-notation-for-abbreviation"] Local Notation v := (aview_of (pa_hull A) m).
  #[warnings="-notation-for-abbreviation"] Local Notation P := (a_pl A).
  #[warnings="-notation-for-abbreviation"] Local Notation chunks := (sr_chunks (a_sec A)).
  #[warnings="-notation-for-abbreviation"] Local Notation nch := (Z.of_nat (length (sr_chunks (a_sec A)))).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  #[warnings="-notation-for-abbreviation"] Local Notation sb := (a_sb A).
  #[warnings="-notation-for-abbreviation"] Local Notation pa := (p_pa (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation thr := (p_thr (a_pl A)).
  #[warnings="-notation-for-abbreviation"] Local Notation pbeg := (a8_pbeg (p - 6144)).
  #[warnings="-notation-for-abbreviation"] Local Notation pend := (a8_pend (p - 6144) (map_size n0)).
  #[warnings="-notation-for-abbreviation"] Local Notation hla := (cs_map (sec_last A)).

  Let W : WFT A. Proof. exact (proj1 AR). Qed.
  Let S0 : In (CS h n0) chunks. Proof. eapply nth_error_In. exact NTH. Qed.
  Let G : kgeo p n0. Proof. exact (bk_kgeo A m p n0 kb es more AR WR LQ). Qed.
  Let NQ' : kMaxPrimaryUser < n0. Proof. (first [ pose proof ((proj1 G)) as dR_6; dand10 dR_6 as _ _ _ _ _ _ _ _ NR _ | destruct (proj1 G) as (_ & _ & _ & _ & _ & _ & _ & _ & NR & _) ]). exact (proj1 NR). Qed.
  Let QTN : a_qthread A = []. Proof. exact (AFreeRP.qt_nil A WR). Qed.

  (* [comment removed for export] *)
  #[warnings="-notation-for-abbreviation"] Local Notation holeD := (AFreeX3.holeD p n0).
  #[warnings="-notation-for-abbreviation"] Local Notation EXC := (AFreeX3.EXC A p n0 i wlo whi).
  Hypothesis AG : forall a, 0 <= a < 2^64 -> ~ EXC a -> v' (wz a) = v (wz a).
  Hypothesis NNH : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> ~ holeD a -> v (wz a) <> None -> v' (wz a) <> None.

  (* [comment removed for export] *)
  #[using="AR m A Clg"] Lemma hole_eq : forall a, AFreeKT.hole (CS h n0) pbeg pend a <-> holeD a.
  Proof. intros a. unfold AFreeKT.hole, AFreeX3.holeD. cbn [cs_map cs_n]. tauto. Qed.
  Let SLO : sh (cs_map (CS h n0)) <= pbeg.
  Proof. cbn [cs_map]. pose proof (ka8_geo p n0 G) as (G1 & _). lia. Qed.
  Let SHI : pend <= sh (cs_map (CS h n0) + map_size (cs_n (CS h n0))).
  Proof. cbn [cs_map cs_n]. (first [ pose proof ((ka8_geo p n0 G)) as dR_7; dand14 dR_7 as _ _ _ _ _ G6 _ _ _ _ _ _ SHA _ | pose proof (ka8_geo p n0 G) as (_ & _ & _ & _ & _ & G6 & _ & _ & _ & _ & _ & _ & SHA & _) ]). rewrite SHA. lia. Qed.
  Let SHI8 : pend mod 8 = 0.
  Proof. (first [ pose proof ((ka8_geo p n0 G)) as dR_8; dand12 dR_8 as _ _ _ _ _ _ _ _ _ _ M3 _ | pose proof (ka8_geo p n0 G) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M3 & _) ]). apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M3]. Qed.
  Let NNH' : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> ~ AFreeKT.hole (CS h n0) pbeg pend a -> v (wz a) <> None -> v' (wz a) <> None.
  Proof. intros a H0 H1 H2 NH. apply NNH; [exact H0| exact H1| exact H2|]. intros X. apply NH. apply (proj2 (hole_eq a)). exact X. Qed.

  (* [comment removed for export] *)
  #[using="W NTH LQ WR AR more es kb m"] Lemma bnds :
    (aobj thr 4096 /\ aobj (p_ctx P) 0x10000 /\ aobj (p_nodes0 P) kDepotNodesBlock /\ aobj (p_frames0 P) kStackStoreBlockBytes /\
     aobj (p_fs P) kFakeStackBytes /\ aobj (p_dtls P) 4096 /\ aobj pa kPtrArrayReserve) /\
    (aobj h msz /\ 0x60a000 <= h /\ h + msz <= alloc_ceiling /\ 8 * nch <= kPtrArrayReserve /\ 0 <= Z.of_nat i < nch) /\
    (aobj hla (map_size (cs_n (sec_last A))) /\ 0x60a000 <= hla /\ 4096 + 32 <= map_size (cs_n (sec_last A))) /\
    (0x7fff8000 + 0x200 <= sh h /\ sh h + msz / 8 <= kHighMemBeg /\ sh (h + msz) = sh h + msz / 8).
  Proof.
    pose proof (place_factsT A W) as PF. cbv zeta in PF.
    (first [ dand13 PF as (T1 & _) (C1 & _) (N1 & _) (F1 & _) (S1 & _) _ _ _ _ _ (D1 & _) (PA1 & _) _ | destruct PF as ((T1 & _) & (C1 & _) & (N1 & _) & (F1 & _) & (S1 & _) & _ & _ & _ & _ & _ & (D1 & _) & (PA1 & _) & _) ]).
    (first [ pose proof ((bk_geo A v p n0 kb es more AR WR LQ)) as dR_10; dand11 dR_10 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof (bk_geo A v p n0 kb es more AR WR LQ) as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]).
    (first [ pose proof ((bk_pa A v p n0 kb es more AR WR LQ)) as dR_11; dand5 dR_11 as _ _ _ _ LE | pose proof (bk_pa A v p n0 kb es more AR WR LQ) as (_ & _ & _ & _ & LE) ]). pose proof (bk_i A p n0 i NTH) as [IR _].
    (first [ pose proof ((bk_last A v p n0 kb es more AR WR LQ)) as dR_12; dand3 dR_12 as _ INL _ | pose proof (bk_last A v p n0 kb es more AR WR LQ) as (_ & INL & _) ]). (first [ pose proof ((bk_chunk A v AR _ INL)) as dR_13; dand6 dR_13 as L1 L2 L3 L4 L5 _ | pose proof (bk_chunk A v AR _ INL) as (L1 & L2 & L3 & L4 & L5 & _) ]).
    (first [ pose proof ((bk_shr A v p n0 kb es more AR WR LQ)) as dR_14; dand4 dR_14 as SHA _ _ SIDE | pose proof (bk_shr A v p n0 kb es more AR WR LQ) as (SHA & _ & _ & SIDE) ]).
    split; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply (proj1 (aobj_app_rangeA _ _)); assumption|].
    split; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; lia|]. split; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption|].
    unfold kHighMemBeg, kHighShadowMapBeg, kLowShadowBeg, kShadowGapBeg in *. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac exc14 X := unfold AFreeX3.EXC, ia_blk in X;
    destruct X as [X|[X|[X|[X|[X|[X|[[Xia X]|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]]]]]].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AG W WLO NTH LQ WR AR whi wlo i more es kb n0 p"] Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> ~ (0x187288 <= a < 0x5d72a8) -> ~ ia_blk a ->
    ~ (0xb1dd0 <= a < 0xb1dd9) -> ~ (0xb1de8 <= a < 0xb1df8) -> ~ (0xb2018 <= a < 0xb2028) -> ~ (0xb2000 <= a < 0xb2004) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1 X2 X3 X4 X5 X6. (first [ pose proof (bnds) as dR_15; dand4 dR_15 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof (aobj_facts _ _ N) as N'. pose proof (aobj_facts _ _ F) as F'. pose proof (aobj_facts _ _ PA) as PA'.
    pose proof alloc_ceiling_val as CE. unfold ia_blk in X2.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO CE. lia. - clear -Ha X T'. lia. - clear -Ha X T'. lia. - clear -X X1. lia. - clear -Ha X N'. kung_all. lia. - clear -Ha X F'. kung_all. lia.
    - clear -X X2. lia. - clear -X X3. lia. - clear -X X4. lia. - clear -X X5. lia. - clear -Ha X PA' LE IR. kung_all. lia. - clear -Ha X HL5. lia.
    - clear -Ha X H5. lia. - clear -Ha X R1. lia. - clear -X X6. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W WLO NTH LQ WR AR whi wlo i more es kb n0 p"] Lemma AGthr : forall a, thr <= a < thr + 4096 -> ~ (thr + 2824 <= a < thr + 2856) -> ~ (thr + 2888 <= a < thr + 2904) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1 X2. (first [ pose proof (bnds) as dR_16; dand4 dR_16 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bk_sep_pa A v AR)) as dR_17; dand5 dR_17 as Dpt _ _ _ _ | pose proof (bk_sep_pa A v AR) as (Dpt & _ & _ & _ & _) ]). (first [ pose proof ((bk_sep_h A v p n0 kb es more AR WR LQ i NTH)) as dR_18; dand3 dR_18 as _ Dht _ | pose proof (bk_sep_h A v p n0 kb es more AR WR LQ i NTH) as (_ & Dht & _) ]).
    (first [ pose proof ((bk_hl A v p n0 kb es more AR WR LQ i NTH)) as dR_19; dand9 dR_19 as _ _ _ _ _ _ _ Dlt _ | pose proof (bk_hl A v p n0 kb es more AR WR LQ i NTH) as (_ & _ & _ & _ & _ & _ & _ & Dlt & _) ]).
    (first [ pose proof ((khit_sep A W)) as dR_20; dand8 dR_20 as _ _ _ _ _ Dn0t Df0t _ | pose proof (khit_sep A W) as (_ & _ & _ & _ & _ & Dn0t & Df0t & _) ]). unfold apart, AMallocA.apart in *.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO T'. lia. - clear -X X1. lia. - clear -X X2. lia. - clear -Ha X T'. lia. - clear -Ha X Dn0t. kung_all. lia. - clear -Ha X Df0t. kung_all. lia.
    - clear -Ha X T'. lia. - clear -Ha X T'. lia. - clear -Ha X T'. lia. - clear -Ha X T'. lia. - clear -Ha X Dpt LE IR. kung_all. lia. - clear -Ha X Dlt. lia.
    - clear -Ha X Dht. lia. - clear -Ha X T' R1 R2. kung_all. lia. - clear -Ha X T'. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W WLO NTH LQ WR AR whi wlo i more es kb"] Lemma AGapp : forall b k a, 4096 <= b -> b + k <= alloc_ceiling -> (b + k <= 0x10000 \/ 0x60a000 <= b) ->
    (b + k <= kLowShadowMapBeg \/ kHighMemBeg <= b) ->
    apart b k thr 4096 -> apart b k (p_nodes0 P) kDepotNodesBlock -> apart b k (p_frames0 P) kStackStoreBlockBytes ->
    apart b k pa kPtrArrayReserve -> apart b k (hla + 24) 8 -> apart b k h msz ->
    b <= a < b + k -> v' (wz a) = v (wz a).
  Proof.
    intros b k a B1 B2 B3 B4 D1 D2 D3 D4 D5 D6 Ha. (first [ pose proof (bnds) as dR_21; dand4 dR_21 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof alloc_ceiling_val as CE. unfold apart in *.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO B2. lia. - clear -X Ha D1. lia. - clear -X Ha D1. lia. - clear -Ha X B3. lia. - clear -Ha X D2. lia. - clear -Ha X D3. lia.
    - clear -Ha X B3. lia. - clear -Ha X B3. lia. - clear -Ha X B3. lia. - clear -Ha X B3. lia. - clear -Ha X D4 LE IR. kung_all. lia. - clear -Ha X D5. lia.
    - clear -Ha X D6. lia. - clear -Ha X B4 R1 R2. kung_all. lia. - clear -Ha X B3. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W WLO NTH LQ WR AR whi wlo i more es kb"] Lemma AGsh : forall a, kLowShadowMapBeg <= a < kHighMemBeg -> ~ (sh h <= a < sh h + msz / 8) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1. (first [ pose proof (bnds) as dR_22; dand4 dR_22 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof (aobj_facts _ _ N) as N'. pose proof (aobj_facts _ _ F) as F'. pose proof (aobj_facts _ _ PA) as PA'.
    pose proof (aobj_facts _ _ HM) as HM'. pose proof (aobj_facts _ _ HL1) as HL'. pose proof alloc_ceiling_val as CE.
    apply AG; [kung_all; lia|]. intros X. exc14 X.
    - clear -Ha X WLO CE. kung_all. lia. - clear -Ha X T'. kung_all. lia. - clear -Ha X T'. kung_all. lia. - clear -Ha X. kung_all. lia.
    - clear -Ha X N'. kung_all. lia. - clear -Ha X F'. kung_all. lia.
    - clear -Ha X. kung_all. lia. - clear -Ha X. kung_all. lia. - clear -Ha X. kung_all. lia. - clear -Ha X. kung_all. lia.
    - clear -Ha X PA' LE IR. kung_all. lia. - clear -Ha X HL' HL4. kung_all. lia.
    - clear -Ha X HM'. kung_all. lia. - clear -X X1. lia. - clear -Ha X. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG S0 W WLO NTH LQ WR AR whi wlo i more es kb"] Lemma AGchunk : forall ch a, carved A ch -> ch <> ChS (CS h n0) ->
    chunk_lo sb ch <= a < chunk_hi sb ch -> ~ (hla + 24 <= a < hla + 32) -> v' (wz a) = v (wz a).
  Proof.
    intros ch a Cc NE Ha NI. (first [ pose proof (bnds) as dR_23; dand4 dR_23 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((carved_range A v [] AR ch Cc)) as dR_24; dand3 dR_24 as CR1 CR2 CR3 | pose proof (carved_range A v [] AR ch Cc) as (CR1 & CR2 & CR3) ]). pose proof (carved_app A v [] AR ch Cc) as CA. apply app_rangeA_arith in CA. (first [ dand5 CA as _ _ _ _ CA | destruct CA as (_ & _ & _ & _ & CA) ]).
    pose proof (carved_apart_thr A v [] AR ch Cc) as Dt. pose proof (carved_apart_n0 A v [] AR ch Cc) as Dn. pose proof (carved_apart_f0 A v [] AR ch Cc) as Df.
    pose proof (carved_apart_pa A v [] AR ch Cc) as Dp. pose proof (carved_disjoint A v [] AR ch (ChS (CS h n0)) Cc S0 NE) as Dm. cbn [chunk_lo chunk_hi] in Dm.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO CR2. lia. - clear -Ha X Dt. lia. - clear -Ha X Dt. lia. - clear -Ha X CR1. lia. - clear -Ha X Dn. lia. - clear -Ha X Df. lia.
    - clear -Ha X CR1. lia. - clear -Ha X CR1. lia. - clear -Ha X CR1. lia. - clear -Ha X CR1. lia. - clear -Ha X Dp LE IR. kung_all. lia. - clear -X NI. lia.
    - clear -Ha X Dm. lia. - clear -Ha X CA R1 R2. kung_all. lia. - clear -Ha X CR1. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W WLO NTH LQ WR AR whi wlo more es kb n0 p"] Lemma AGpa : forall a, pa <= a < pa + 8 * nch -> ~ (pa + 8 * Z.of_nat i <= a < pa + 8 * Z.of_nat i + 8) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1. (first [ pose proof (bnds) as dR_26; dand4 dR_26 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ PA) as PA'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bk_sep_pa A v AR)) as dR_27; dand5 dR_27 as Dpt Dpc Dpn Dpf _ | pose proof (bk_sep_pa A v AR) as (Dpt & Dpc & Dpn & Dpf & _) ]). pose proof (bk_sep_h A v p n0 kb es more AR WR LQ i NTH) as (Dhp & _).
    (first [ pose proof ((bk_hl A v p n0 kb es more AR WR LQ i NTH)) as dR_28; dand8 dR_28 as _ _ _ _ _ _ Dlp _ | pose proof (bk_hl A v p n0 kb es more AR WR LQ i NTH) as (_ & _ & _ & _ & _ & _ & Dlp & _) ]). unfold apart in *.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO PA' LE. kung_all. lia. - clear -Ha X Dpt LE. kung_all. lia. - clear -Ha X Dpt LE. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia.
    - clear -Ha X Dpn LE. kung_all. lia. - clear -Ha X Dpf LE. kung_all. lia.
    - clear -Ha X PA' LE. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia.
    - clear -X X1. lia. - clear -Ha X Dlp. lia.
    - clear -Ha X Dhp. lia. - clear -Ha X PA' LE R1 R2. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Hypothesis PNSRT : rw_cells rsegs v' 0xb1dd0 [C8 (wz (nch - 1)); C1 (Z_to_bv 8 0)].
  Hypothesis PLCK : rw_cells rsegs v' 0xb2000 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)].
  Hypothesis PARR : u64arr rsegs v' pa (upd (sec_words A) i (Z_to_bv 64 hla)).
  Hypothesis PHLC : hla = h \/ rw_cells rsegs v' hla [C8 (wz hla); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz (Z.of_nat i))].
  Hypothesis PDR : depot_repL AL_pasan rsegs (a_depot A) (p_nodes0 P) (p_frames0 P) v'.
  (* [comment removed for export] *)
  Hypothesis IAH : forall a, iafoot a -> v' (wz a) = v (wz a).
  Hypothesis IAL : u8_at rsegs v' (al_internal_alloc_inited AL_pasan + 1) 0.
  Hypothesis IAP : bytes_at rsegs v' 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0].

  #[warnings="-notation-for-abbreviation"] Local Notation A' := (recsA A kb i es more (dead2 p n0)).

  (* [comment removed for export] *)
  #[using="IAP PLCK AG W WLO NTH LQ WR AR whi wlo i more es kb n0 p m Clg"] Lemma fs_consts : consts_repr_ LPA AL_pasan P v'.
  Proof.
    (first [ pose proof (bnds) as dR_29; dand4 dR_29 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof (aobj_facts _ _ C) as C'. pose proof (aobj_facts _ _ D) as D'f. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bk_sep_pa A v AR)) as dR_30; dand5 dR_30 as Dpt Dpc Dpn Dpf Dct | pose proof (bk_sep_pa A v AR) as (Dpt & Dpc & Dpn & Dpf & Dct) ]). (first [ pose proof ((bk_sep_h A v p n0 kb es more AR WR LQ i NTH)) as dR_31; dand5 dR_31 as Dhp Dht Dhc Dhn Dhf | pose proof (bk_sep_h A v p n0 kb es more AR WR LQ i NTH) as (Dhp & Dht & Dhc & Dhn & Dhf) ]).
    (first [ pose proof ((bk_hl A v p n0 kb es more AR WR LQ i NTH)) as dR_32; dand11 dR_32 as _ _ _ _ _ _ Dlp Dlt Dlc Dln Dlf | pose proof (bk_hl A v p n0 kb es more AR WR LQ i NTH) as (_ & _ & _ & _ & _ & _ & Dlp & Dlt & Dlc & Dln & Dlf) ]).
    (first [ pose proof ((khit_sep A W)) as dR_33; dand10 dR_33 as _ _ Dct' _ _ Dn0t Df0t Dn0c Df0c _ | pose proof (khit_sep A W) as (_ & _ & Dct' & _ & _ & Dn0t & Df0t & Dn0c & Df0c & _) ]).
    apply (consts_P2 A v v' [] AR).
    - intros cst Hin. cbn [cl_consts LPA] in Hin.
      pose proof pa_consts_okD as OK. rewrite forallb_forall in OK. specialize (OK cst Hin). cbv beta in OK.
      apply orb_true_iff in OK as [OK|OK].
      2:{ right. apply (proj1 (bool_decide_eq_true _)) in OK. subst cst. cbn [fst snd].
          destruct PLCK as [[_ B] _]. cbn [cells_bytes cbytes app] in B.
          apply (bytes_at_app _ v' 0xb2000 [Z_to_bv 8 0] _) in B as [_ B]. cbn [length Z.of_nat Pos.of_succ_nat] in B.
          apply (bytes_at_as v' _ _ _ B). byteseq. }
      apply orb_true_iff in OK as [OK|OK].
      2:{ right. apply (proj1 (bool_decide_eq_true _)) in OK. subst cst. cbn [fst snd]. exact IAP. }
      left. intros a Ha. unfold const_okD in OK. cbv zeta in OK.
      repeat (apply andb_true_iff in OK as [OK ?X]). rewrite !orb_true_iff, !Z.leb_le in *.
      destruct (pa_consts_where cst a Hin Ha) as [Sx|[Sx|Sx]].
      + apply AGimg; [unfold pa_shared in Sx; clear -Sx; lia| unfold ia_blk; clear -OK X X0 X1 X2 X3 X4 Ha; lia ..].
      + unfold pa_image_shadow, sh in Sx. apply AGsh; [clear -Sx; kung_all; lia|]. unfold sh. clear -Sx H5. kung_all. lia.
      + pose proof (pa_static_low a Sx). apply AGimg; [unfold pa_static in Sx; clear -Sx; lia| unfold ia_blk; clear -OK X X0 X1 X2 X3 X4 Ha; lia ..].
    - intros a Ha. cbn [cl_shared LPA] in Ha. unfold pa_shared in Ha. apply AGimg; unfold ia_blk; clear -Ha; lia.
    - intros a Ha. unfold cfoot_stat in Ha. offs_h Ha. alc_h Ha. apply AGimg; unfold ia_blk; clear -Ha; lia.
    - intros a Ha. unfold cfoot_thr in Ha. offs_h Ha. apply AGthr; clear -Ha T'; lia.
    - intros a Ha. unfold cfoot_misc in Ha. pose proof TPV as TP. rewrite TP in Ha.
      destruct Ha as [Ha|[Ha|[Ha|[Ha|[Ha|Ha]]]]].
      + apply (AGapp (p_ctx P) 0x10000 a); try (clear -Ha C'; lia); unfold apart; try (clear -Dct Dct' Dn0c Df0c Dpc Dlc Dhc Ha; unfold apart, AMallocA.apart in *; kung_all; lia).
      + apply (AGapp (p_ctx P) 0x10000 a); try (clear -Ha C'; lia); unfold apart; try (clear -Dct Dct' Dn0c Df0c Dpc Dlc Dhc Ha; unfold apart, AMallocA.apart in *; kung_all; lia).
      + apply AGimg; unfold ia_blk; clear -Ha; lia.
      + apply AGimg; unfold ia_blk; clear -Ha; lia.
      + apply AGimg; unfold ia_blk; clear -Ha; lia.
      + (* [comment removed for export] *)
        (first [ pose proof ((bm_nth_fixed A)) as dR_34; dand15 dR_34 as _ E1 _ _ E4 _ _ E7 E8 _ _ _ _ _ E14 | pose proof (bm_nth_fixed A) as (_ & E1 & _ & _ & E4 & _ & _ & E7 & E8 & _ & _ & _ & _ & _ & E14) ]).
        pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & _). pose proof (bm_nth_sec A _ _ EL) as ELs. pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
        pose proof (bm_sepT A _ _ _ _ _ _ W E14 E4 ltac:(lia)) as Y1. pose proof (bm_sepT A _ _ _ _ _ _ W E14 E7 ltac:(lia)) as Y2.
        pose proof (bm_sepT A _ _ _ _ _ _ W E14 E8 ltac:(lia)) as Y3. pose proof (bm_sepT A _ _ _ _ _ _ W E14 E1 ltac:(lia)) as Y4.
        pose proof (bm_sepT A _ _ _ _ _ _ W E14 ELs ltac:(lia)) as Y5. pose proof (bm_sepT A _ _ _ _ _ _ W E14 Es ltac:(lia)) as Y6.
        unfold a_thr, a_nodes0, a_frames0, a_pa in *.
        apply (AGapp (p_dtls P) 4096 a); try (clear -Ha D'f; lia); unfold apart; clear -Ha Y1 Y2 Y3 Y4 Y5 Y6 HL4; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W WLO NTH LQ WR AR whi wlo i more es kb n0 p"] Lemma AGspace : forall a, sb <= a < sb + kSpaceSize + 4096 -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha. (first [ pose proof ((sb_factsT A W)) as dR_35; dand5 dR_35 as _ _ HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_36; dand10 dR_36 as E0 E1 _ _ E4 _ _ E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & _ & _ & E4 & _ & _ & E7 & E8 & _) ]). pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & _).
    pose proof (bm_nth_sec A _ _ EL) as ELs. pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
    pose proof (bm_sepT A _ _ _ _ _ _ W E0 E4 ltac:(lia)) as Y1. pose proof (bm_sepT A _ _ _ _ _ _ W E0 E7 ltac:(lia)) as Y2.
    pose proof (bm_sepT A _ _ _ _ _ _ W E0 E8 ltac:(lia)) as Y3. pose proof (bm_sepT A _ _ _ _ _ _ W E0 E1 ltac:(lia)) as Y4.
    pose proof (bm_sepT A _ _ _ _ _ _ W E0 ELs ltac:(lia)) as Y5. pose proof (bm_sepT A _ _ _ _ _ _ W E0 Es ltac:(lia)) as Y6.
    (first [ pose proof (bnds) as dR_37; dand4 dR_37 as _ _ (_ & _ & HL4) _ | pose proof bnds as (_ & _ & (_ & _ & HL4) & _) ]).
    unfold a_b6, a_sb, a_pa, a_thr, a_nodes0, a_frames0 in *.
    unfold a_sb in Ha. apply (AGapp (p_sb P) (kSpaceSize + 4096) a); unfold apart; try (clear -Ha HB6 RSB SCE CE; kung_all; lia).
    - clear -Y1 HB6 RSB. kung_all. lia. - clear -Y2 HB6 RSB. kung_all. lia. - clear -Y3 HB6 RSB. kung_all. lia.
    - clear -Y4 HB6 RSB. kung_all. lia. - clear -Y5 HB6 RSB HL4. kung_all. lia. - clear -Y6 HB6 RSB. kung_all. lia.
  Qed.

  #[using="IAL PLCK AG W WLO NTH LQ WR AR whi wlo i more es kb n0 p m Clg"] Lemma fs_locks : locks_repr_ LPA AL_pasan P [] v'.
  Proof.
    (first [ pose proof ((sb_factsT A W)) as dR_38; dand5 dR_38 as _ _ HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & _ & HB6 & RSB & SCE) ]).
    pose proof (ar_locks _ _ _ _ _ (proj2 AR)) as LK. unfold locks_repr_ in LK |- *. cbv zeta in LK |- *. (first [ dand6 LK as C0 L1 L2 L3 L4 L5 | destruct LK as (C0 & L1 & L2 & L3 & L4 & L5) ]).
    cbn [al_instance al_internal_alloc_inited AL_pasan] in *. unfold off_sec_mutex, off_q_cache_mutex, off_q_recycle_mutex, off_fallback_mutex in *.
    rewrite lockb_nil in *. unfold p_ri in *. change (p_sb (a_pl A)) with sb in *.
    split; [| split; [| split; [| split; [| split; [| exact IAL]]]]].
    - intros c' Hc. destruct (C0 c' Hc) as [Y1 Y2].
      split; [eapply u64_at_agree; [exact Y1|]| eapply u64_at_agree; [exact Y2|]]; intros k Hk; apply AGspace; clear -Hc Hk; unfold kRegionInfoSize; kung_all; lia.
    - (* [comment removed for export] *)
      destruct PLCK as [[_ B] _]. cbn [cells_bytes cbytes app] in B. apply (bytes_at_app _ v' 0xb2000 [Z_to_bv 8 0] _) in B as [B _]. exact B.
    - eapply u8_at_agree; [exact L2|]. apply AGimg; unfold ia_blk; clear; lia.
    - eapply u8_at_agree; [exact L3|]. apply AGimg; unfold ia_blk; clear; lia.
    - eapply u8_at_agree; [exact L4|]. apply AGimg; unfold ia_blk; clear; lia.
  Qed.

  #[using="NNH' SHI8 SHI SLO NNH AG G S0 W WLO NTH LQ WR AR whi wlo i more es kb n0 p m Clg"] Lemma fs_regions : forall c', 1 <= c' <= 30 -> region_repr_ LPA sb (a_reg A c') v' c'.
  Proof.
    intros c' Hc. pose proof (region_piece_boundsT A c' W Hc) as RB. cbv zeta in RB.
    apply (region_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH' c' Hc). intros a Ha. unfold rfoot, region_info_addr, free_array_beg in Ha. change (p_sb (a_pl A)) with sb in *.
    apply AGspace. clear -Ha RB Hc. unfold kRegionInfoSize in *. kung_all. lia.
  Qed.

  #[using="NNH' SHI8 SHI SLO NNH AG G S0 W WLO NTH LQ WR AR whi wlo i more es kb n0 p m Clg"] Lemma fs_cache : cache_repr_ LPA P (a_cache A) (a_cache_inited A) v'.
  Proof.
    pose proof bnds as ((T & _) & _). pose proof (aobj_facts _ _ T) as T'.
    apply (cache_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH'). intros c' Hc'.
    apply (cache_line_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH' (a_cache A) c' Hc' eq_refl).
    intros a Ha. offs_h Ha. cbv beta in Ha. apply AGthr; clear -Ha Hc' T'; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PHLC PARR NNH' SHI8 SHI SLO NNH AG G S0 W WLO NTH LQ WR AR whi wlo i more es kb n0 p m Clg"] Lemma fs_live : live_repr_ LPA sb (a_livemap A) v'.
  Proof.
    intros u li Hl.
    assert (NE : li_chunk li <> ChS (CS h n0)) by exact (rsec_live_other A kb n0 (CS h n0) es more WR LQ u li Hl).
    (first [ pose proof ((ar_live _ _ _ _ _ (proj2 AR) u li Hl)) as dR_40; dand3 dR_40 as HR MU0 MC | destruct (ar_live _ _ _ _ _ (proj2 AR) u li Hl) as (HR & MU0 & MC) ]). pose proof alloc_ceiling_val as CE.
    pose proof (known_live A v [] AR u li Hl) as CL. pose proof (known_range A v [] AR _ _ CL) as RNG. pose proof (known_carved A v [] AR _ _ CL) as CC.
    destruct (wtV A W) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_41; dand3 dR_41 as Nn U _ | pose proof (V1 u li Hl) as (Nn & U & _) ]). pose proof (user_in A _ _ CL) as UR. rewrite <- U in UR.
    (first [ pose proof ((bk_last A v p n0 kb es more AR WR LQ)) as dR_42; dand3 dR_42 as EL INL _ | pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & INL & _) ]).
    (* [comment removed for export] *)
    assert (HF : forall a, hdr_foot sb (li_chunk li) (li_n li) a -> ~ (hla + 24 <= a < hla + 32)).
    { intros a Ha X. pose proof (hdr_foot_in A _ _ a CL ltac:(left; exact Ha)) as IN.
      destruct (chunk_eq_dec (li_chunk li) (ChS (sec_last A))) as [E|NEL].
      - rewrite E in Ha. unfold hdr_foot in Ha. destruct (sec_last A) as [mbl nl] eqn:EQL. cbn [user_of alloc_beg cs_map] in Ha, X.
        unfold sec_user_beg, sec_alloc_beg, kPageSize in Ha. clear -Ha X. lia.
      - pose proof (carved_disjoint A v [] AR _ (ChS (sec_last A)) CC INL NEL) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl.
        (first [ pose proof (bnds) as dR_43; dand4 dR_43 as _ _ (_ & _ & HL4) _ | pose proof bnds as (_ & _ & (_ & _ & HL4) & _) ]). clear -IN Dl X HL4. lia. }
    split; [|split].
    - apply (hdr_P A v v'); [| exact HR]. intros a Ha. apply (AGchunk (li_chunk li) a CC NE); [| exact (HF a Ha)]. apply (hdr_foot_in A _ (li_n li)); [exact CL| left; exact Ha].
    - apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| right; lia| lia| | exact MU0]. intros x Hx. apply (hole_free_carved A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 (li_chunk li) x CC NE). lia.
    - apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| right; lia| lia| | exact MC]. intros x Hx. apply (hole_free_carved A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 (li_chunk li) x CC NE). lia.
  Qed.

  #[using="QTN LQ WR more es kb Clg"] Lemma kquar_other : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> qe_chunk e <> ChS (CS h n0).
  Proof.
    intros e He E. apply (rsec_quar_other A kb n0 (CS h n0) es more WR LQ). rewrite <- E. rewrite quarantined_chunks_def, q_entries_nil. cbn [app].
    apply in_map. rewrite QTN in He. cbn [app] in He. rewrite AState.q_entries_app. apply in_or_app. left. exact He.
  Qed.

  #[using="PHLC PARR NNH' SHI8 SHI SLO NNH AG QTN G S0 W WLO NTH LQ WR AR whi wlo i more es kb n0 p m Clg"] Lemma fs_quar : quarantine_repr_ LPA AL_pasan P (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ (proj2 AR))) as dR_44; dand3 dR_44 as QT QG QR | pose proof (ar_quar _ _ _ _ _ (proj2 AR)) as (QT & QG & QR) ]). unfold quarantine_repr_. change (p_sb (a_pl A)) with sb in *.
    (first [ pose proof (bnds) as dR_45; dand4 dR_45 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bk_last A v p n0 kb es more AR WR LQ)) as dR_46; dand3 dR_46 as EL INL _ | pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & INL & _) ]).
    assert (AGb : forall b a, In b (a_qthread A ++ a_qglobal A) -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> v' (wz a) = v (wz a)).
    { intros b a Hb Ha. pose proof (batch_carved A v [] AR b (b_in_big A b Hb)) as Cb.
      apply (AGchunk _ a Cb ltac:(discriminate)); [cbn [chunk_lo chunk_hi alloc_beg]; rewrite class_size_24; unfold batch_addr in Ha; exact Ha|].
      pose proof (carved_disjoint A v [] AR _ (ChS (sec_last A)) Cb INL ltac:(discriminate)) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl.
      cbn [chunk_lo chunk_hi alloc_beg] in Dl. rewrite class_size_24 in Dl. unfold batch_addr in Ha. clear -Ha Dl HL4. kung_all. lia. }
    split; [|split].
    - (first [ dand5 QT as X1 X2 X3 X4 BR | destruct QT as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P A v v' (thr + off_th_qcache) (a_qthread A) ltac:(intros a Ha; unfold off_th_qcache in Ha; apply AGthr; clear -Ha T'; lia) (conj X1 (conj X2 (conj X3 X4))))) as dR_48; dand4 dR_48 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P A v v' (thr + off_th_qcache) (a_qthread A) ltac:(intros a Ha; unfold off_th_qcache in Ha; apply AGthr; clear -Ha T'; lia) (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
      apply (batches_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH'); [intros b Hb; apply in_or_app; left; exact Hb| | exact BR].
      intros b a Hb Ha. apply (AGb b a); [apply in_or_app; left; exact Hb| exact Ha].
    - (first [ dand5 QG as X1 X2 X3 X4 BR | destruct QG as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P A v v' (al_instance AL_pasan + off_q_cache_list_size) (a_qglobal A) ltac:(intros a Ha; alc_h Ha; unfold off_q_cache_list_size in Ha; apply AGimg; unfold ia_blk; clear -Ha; lia) (conj X1 (conj X2 (conj X3 X4))))) as dR_50; dand4 dR_50 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P A v v' (al_instance AL_pasan + off_q_cache_list_size) (a_qglobal A) ltac:(intros a Ha; alc_h Ha; unfold off_q_cache_list_size in Ha; apply AGimg; unfold ia_blk; clear -Ha; lia) (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
      apply (batches_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH'); [intros b Hb; apply in_or_app; right; apply in_or_app; left; exact Hb| | exact BR].
      intros b a Hb Ha. apply (AGb b a); [apply in_or_app; right; exact Hb| exact Ha].
    - intros e He. (first [ pose proof ((QR e He)) as dR_51; dand3 dR_51 as HR J MC | destruct (QR e He) as (HR & J & MC) ]).
      pose proof (known_quar A v [] AR e (q_in_big A e He)) as CL. pose proof (known_range A v [] AR _ _ CL) as RNG. pose proof (known_carved A v [] AR _ _ CL) as CC.
      pose proof (user_in A _ _ CL) as UI.
      assert (NE : qe_chunk e <> ChS (CS h n0)) by exact (kquar_other e He).
      assert (HF : forall a, hdr_foot sb (qe_chunk e) (qe_n e) a \/ (user_of sb (qe_chunk e) (qe_n e) <= a < user_of sb (qe_chunk e) (qe_n e) + 8) -> ~ (hla + 24 <= a < hla + 32)).
      { intros a Ha X. pose proof (hdr_foot_in A _ _ a CL Ha) as IN.
        destruct (chunk_eq_dec (qe_chunk e) (ChS (sec_last A))) as [E|NEL].
        - rewrite E in Ha. unfold hdr_foot in Ha. destruct (sec_last A) as [mbl nl] eqn:EQL. cbn [user_of alloc_beg cs_map] in Ha, X.
          unfold sec_user_beg, sec_alloc_beg, kPageSize in Ha. clear -Ha X. lia.
        - pose proof (carved_disjoint A v [] AR _ (ChS (sec_last A)) CC INL NEL) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl. clear -IN Dl X HL4. lia. }
      split; [|split].
      + apply (hdr_P A v v'); [| exact HR]. intros a Ha. apply (AGchunk (qe_chunk e) a CC NE); [| apply HF; left; exact Ha]. apply (hdr_foot_in A _ (qe_n e)); [exact CL| left; exact Ha].
      + eapply junk_at_agree; [exact J|]. intros k Hk. apply (AGchunk (qe_chunk e) _ CC NE); [| apply HF; right; lia]. apply (hdr_foot_in A _ (qe_n e)); [exact CL| right; lia].
      + apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| right; lia| lia| | exact MC]. intros x Hx. apply (hole_free_carved A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 (qe_chunk e) x CC NE). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PHLC PARR PNSRT NNH' SHI8 SHI SLO NNH AG G S0 W WLO NTH LQ WR AR whi wlo more es kb n0 p m Clg"] Lemma fs_sec : sec_repr_ LPA AL_pasan P (sec_remove (a_sec A) i) v'.
  Proof.
    pose proof (ar_sec _ _ _ _ _ (proj2 AR)) as SR. unfold sec_repr_ in SR |- *. cbv zeta in SR |- *. cbn [sec_remove sr_chunks sr_reserved].
    (first [ dand7 SR as X1 X2 J1 J2 J3 CH PM | destruct SR as (X1 & X2 & J1 & J2 & J3 & CH & PM) ]). cbn [al_instance AL_pasan] in *.
    (first [ pose proof (bnds) as dR_53; dand4 dR_53 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ PA) as PA'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bk_nch A v p n0 kb es more AR WR LQ)) as dR_54; dand4 dR_54 as N1 N2 N3 NEC | pose proof (bk_nch A v p n0 kb es more AR WR LQ) as (N1 & N2 & N3 & NEC) ]). (first [ pose proof ((bk_pa A v p n0 kb es more AR WR LQ)) as dR_55; dand5 dR_55 as A1 A2 A3 A4 A5 | pose proof (bk_pa A v p n0 kb es more AR WR LQ) as (A1 & A2 & A3 & A4 & A5) ]).
    (first [ pose proof ((bk_last A v p n0 kb es more AR WR LQ)) as dR_56; dand4 dR_56 as EL INL ELw HLU | pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & INL & ELw & HLU) ]).
    pose proof (rsec_nodup A WR) as ND. apply NoDup_ListNoDup in ND.
    unfold off_sec_n_reserved, off_sec_n_chunks, off_sec_chunks_sorted, off_sec_stat_n_allocs, off_global_stats in *.
    split; [| split; [| split; [| split; [| split; [| split]]]]].
    - eapply u64_at_agree; [exact X1|]. intros k Hk. apply AGimg; unfold ia_blk; clear -Hk; lia.
    - rewrite (swap_remove_length chunks i (CS 0 0) NEC). replace (Z.of_nat (length chunks - 1)) with (nch - 1) by lia.
      destruct PNSRT as [[_ B] _]. cbn [cells_bytes cbytes app] in B. apply bytes_at_app in B as [B _]. exact B.
    - destruct PNSRT as [[_ B] _]. cbn [cells_bytes cbytes app] in B. apply bytes_at_app in B as [_ B]. rewrite length_le8 in B. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in B.
      exists [Z_to_bv 8 0]. split; [reflexivity| exact B].
    - apply img_junk; lia.
    - apply img_junk; lia.
    - intros j c E. destruct (swap_remove_src chunks i (CS 0 0) j c (nth_error_Some_lt _ _ _ NTH) E) as [SRC JL]. unfold sr_src in SRC.
      destruct (Nat.eqb_spec j i) as [EJ|NJ].
      + (* [comment removed for export] *)
        subst j. rewrite EL in SRC || (replace (length chunks - 1)%nat with (Z.to_nat (nch - 1)) in SRC by lia; rewrite EL in SRC). injection SRC as <-.
        split.
        * destruct PARR as [B _]. pose proof (bk_i A p n0 i NTH) as [_ NI].
          assert (UP : nth_error (upd (sec_words A) i (Z_to_bv 64 hla)) i = Some (Z_to_bv 64 hla)).
          { apply nth_error_upd_same. rewrite sec_words_length. exact (nth_error_Some_lt _ _ _ NTH). }
          pose proof (u64s_entry v' pa _ i _ B UP) as X. unfold u64_at. exact X.
        * destruct PHLC as [EQ|CC].
          { exfalso. (* [comment removed for export] *)
            pose proof (proj1 (NoDup_nth_error (map cs_map chunks)) ltac:(destruct (wtS A W) as (S1 & _); apply NoDup_ListNoDup; exact S1) i (Z.to_nat (nch - 1))) as INJ.
            rewrite length_map in INJ. specialize (INJ (nth_error_Some_lt _ _ _ NTH)). rewrite !nth_error_map, NTH, EL in INJ. cbn in INJ. specialize (INJ ltac:(rewrite EQ; reflexivity)). lia. }
          unfold sec_hdr_cells. cbn [sh_map_beg sh_map_size sh_size sh_chunk_idx]. exact CC.
      + (* [comment removed for export] *)
        assert (NEc : c <> CS h n0).
        { intros ->. pose proof (proj1 (NoDup_nth_error chunks) ND j i ltac:(apply nth_error_Some_lt in SRC; exact SRC) ltac:(rewrite SRC, NTH; reflexivity)). lia. }
        assert (NEl : c <> sec_last A).
        { intros ->. pose proof (proj1 (NoDup_nth_error chunks) ND j (Z.to_nat (nch - 1)) ltac:(apply nth_error_Some_lt in SRC; exact SRC) ltac:(rewrite SRC, EL; reflexivity)). lia. }
        destruct (CH j c SRC) as [U R]. pose proof (nth_error_In _ _ SRC) as INc. (first [ pose proof ((bk_chunk A v AR _ INc)) as dR_57; dand7 dR_57 as C1 C2 C3 C4 C5 C6 C7 | pose proof (bk_chunk A v AR _ INc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7) ]).
        pose proof (carved_disjoint A v [] AR (ChS c) (ChS (sec_last A)) INc INL ltac:(congruence)) as Dl. rewrite !chunk_lo_S, !chunk_hi_S in Dl.
        split.
        * eapply u64_at_agree; [exact U|]. intros k Hk. apply AGpa; clear -Hk JL NJ N1; lia.
        * eapply rw_cells_agree; [exact R|]. rewrite sec_hdr_size. intros k Hk.
          apply (AGchunk (ChS c) _ INc ltac:(congruence)); [rewrite chunk_lo_S, chunk_hi_S; clear -Hk C4; lia| clear -Dl Hk HL4 C4; lia].
    - apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| clear -PA' N1 N2 N3; unfold kChunksBlockCount in N3; kung_all; lia| clear -PA' N3 CE; unfold kChunksBlockCount in N3; kung_all; lia| | exact PM].
      intros x Hx. pose proof (bk_sep_h A v p n0 kb es more AR WR LQ i NTH) as (Dhp & _).
      apply (hole_free_app A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 pa (8 * sr_reserved (a_sec A)) x); cbn [cs_map cs_n]; [clear -PA' N3; unfold kChunksBlockCount in N3; kung_all; lia| | exact Hx].
      pose proof (carved_apart_pa A v [] AR (ChS (CS h n0)) S0) as Y. cbn [chunk_lo chunk_hi cs_map cs_n] in Y. clear -Y N3. unfold kChunksBlockCount in N3. kung_all. lia.
  Qed.

  #[using="NNH' SHI8 SHI SLO NNH AG G S0 W WLO NTH LQ WR AR whi wlo i more es kb n0 p m Clg"] Lemma fs_fs : fs_base_ LPA P (a_fhint A) v' /\ fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v' /\ fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    (first [ pose proof (bnds) as dR_58; dand4 dR_58 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ S) as S'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_59; dand10 dR_59 as _ E1 _ _ E4 _ E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _ & _ & E4 & _ & E6 & E7 & E8 & _) ]). pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & _).
    pose proof (bm_nth_sec A _ _ EL) as ELs. pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
    pose proof (bm_sepT A _ _ _ _ _ _ W E6 E4 ltac:(lia)) as Y1. pose proof (bm_sepT A _ _ _ _ _ _ W E6 E7 ltac:(lia)) as Y2.
    pose proof (bm_sepT A _ _ _ _ _ _ W E6 E8 ltac:(lia)) as Y3. pose proof (bm_sepT A _ _ _ _ _ _ W E6 E1 ltac:(lia)) as Y4.
    pose proof (bm_sepT A _ _ _ _ _ _ W E6 ELs ltac:(lia)) as Y5. pose proof (bm_sepT A _ _ _ _ _ _ W E6 Es ltac:(lia)) as Y6.
    unfold a_fs, a_thr, a_nodes0, a_frames0, a_pa in *.
    assert (AGfs : forall a, p_fs P <= a < p_fs P + kFakeStackBytes -> v' (wz a) = v (wz a)).
    { intros a Ha. apply (AGapp (p_fs P) kFakeStackBytes a); try (clear -Ha S'; lia); unfold apart.
      - clear -Y1. lia. - clear -Y2. lia. - clear -Y3. lia. - clear -Y4. lia. - clear -Y5 HL4. lia. - clear -Y6. lia. }
    split; [| split].
    - apply (fsbase_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH'). intros a Ha. apply AGfs. unfold a_fs in Ha. clear -Ha. unfold kFakeFlagsOffset, kFakeStackBytes in *. lia.
    - apply (fsptrs_P A v v' [] AR). intros a Ha. apply AGfs. unfold a_fs in Ha. clear -Ha. unfold kFakeFramesOffset, kFakeStackBytes in *. lia.
    - apply (fsflags_P A v v' [] AR). intros a Ha. apply AGfs. unfold a_fs in Ha. clear -Ha. unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. lia.
  Qed.

  #[using="IAH AR m Clg"] Lemma fs_ia : ia_repr_ LPA AL_pasan (a_ia_inited A) v'.
  Proof. apply (ia_P A v v' [] AR). exact IAH. Qed.

  #[using="AG QTN S0 W WLO NTH LQ WR AR whi wlo i more es kb n0 p m Clg"] Lemma fs_shadow : shadow_repr_ LPA sb (a_reg A) (a_cache A) (a_livemap A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof (bnds) as dR_60; dand4 dR_60 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ HM) as HM'. pose proof alloc_ceiling_val as CE. (first [ pose proof ((bk_geo A v p n0 kb es more AR WR LQ)) as dR_61; dand5 dR_61 as _ HAL _ MSZAL _ | pose proof (bk_geo A v p n0 kb es more AR WR LQ) as (_ & HAL & _ & MSZAL & _) ]).
    (* [comment removed for export] *)
    assert (SHD : forall ch, carved A ch -> ch <> ChS (CS h n0) ->
              forall z, sh (chunk_lo sb ch) <= z < sh (chunk_lo sb ch) + (chunk_hi sb ch - chunk_lo sb ch) / 8 -> ~ (sh h <= z < sh h + msz / 8)).
    { intros ch Cc NE z Hz X. pose proof (carved_disjoint A v [] AR ch (ChS (CS h n0)) Cc S0 NE) as Dm. cbn [chunk_lo chunk_hi] in Dm.
      pose proof (carved_shadow A v [] AR ch Cc) as CSH.
      destruct ch as [[c' k']|[mb n1]].
      - destruct Cc as [Hc Hk]. (first [ pose proof ((carved_chunk_boundsT A c' k' W Hc Hk)) as dR_62; dand4 dR_62 as _ _ B3 _ | pose proof (carved_chunk_boundsT A c' k' W Hc Hk) as (_ & _ & B3 & _) ]). pose proof (class_size_mod32 c' Hc) as CM.
        cbn [chunk_lo chunk_hi alloc_beg] in *.
        replace (chunk_addr sb c' k' + class_size c' - chunk_addr sb c' k') with (class_size c') in Hz by lia.
        pose proof (sh_disjoint (chunk_addr sb c' k') (class_size c') h msz ltac:(apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                      ltac:(apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL]) Dm) as SD.
        clear -Hz X SD. lia.
      - unfold carved in Cc. (first [ pose proof ((bk_chunk A v AR _ Cc)) as dR_63; dand3 dR_63 as C1 C2 _ | pose proof (bk_chunk A v AR _ Cc) as (C1 & C2 & _) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
        replace (mb + map_size n1 - mb) with (map_size n1) in Hz by lia. pose proof (map_size_page n1) as MP.
        pose proof (sh_disjoint mb (map_size n1) h msz ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact C2]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                      ltac:(apply (mod0_down _ kPageSize 8); [exists 512; reflexivity| exact MP]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL]) Dm) as SD.
        clear -Hz X SD. lia. }
    assert (AGc : forall ch, carved A ch -> ch <> ChS (CS h n0) ->
              forall z, sh (chunk_lo sb ch) <= z < sh (chunk_lo sb ch) + (chunk_hi sb ch - chunk_lo sb ch) / 8 -> v' (wz z) = v (wz z)).
    { intros ch Cc NE z Hz. (first [ pose proof ((carved_shadow A v [] AR ch Cc)) as dR_64; dand3 dR_64 as CS1 CS2 CS3 | pose proof (carved_shadow A v [] AR ch Cc) as (CS1 & CS2 & CS3) ]). apply AGsh; [| exact (SHD ch Cc NE z Hz)].
      pose proof (heap_shadow_rangeT A z W (CS2 z ltac:(rewrite CS1; exact Hz))) as IM. unfold in_shadow_maps in IM. clear -IM. kung_all. lia. }
    assert (AGp : forall c' k, 1 <= c' <= 30 -> 0 <= k < carved_count A c' ->
              forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> v' (wz z) = v (wz z)).
    { intros c' k Hc Hk z Hz. apply (AGc (ChP (CP c' k)) (conj Hc Hk) ltac:(discriminate)). cbn [chunk_lo chunk_hi alloc_beg].
      replace (chunk_addr sb c' k + class_size c' - chunk_addr sb c' k) with (class_size c') by lia. exact Hz. }
    split; [|split; [|split; [|split; [|split]]]].
    - intros c' k Hc ST. apply (shadow_free_P A v v' [] AR); [exact Hc| exact ST|].
      assert (Hk : 0 <= k < carved_count A c').
      { destruct ST as [F'|[C'|[E B]]].
        - (first [ pose proof ((wtR A W)) as dR_65; dand3 dR_65 as WRg _ _ | destruct (wtR A W) as (WRg & _ & _) ]). (first [ pose proof ((WRg c' Hc)) as dR_66; dand10 dR_66 as _ _ _ _ _ _ _ _ FR _ | destruct (WRg c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F').
        - (first [ pose proof ((wtC A W)) as dR_67; dand3 dR_67 as WC _ _ | destruct (wtC A W) as (WC & _ & _) ]). (first [ pose proof ((WC c' ltac:(lia))) as dR_68; dand4 dR_68 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C').
        - subst c'. exact (batch_idx_range A v [] AR k (bi_in_big A k B)). }
      exact (AGp c' k Hc Hk).
    - intros u c' k n1 Hl. apply (shadow_live_P A v v' [] AR u); [exact Hl|].
      pose proof (known_live A v [] AR u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). exact (AGp c' k Hc Hk).
    - intros c' k n1 He. apply (shadow_quar_P A v v' [] AR); [exact He|].
      pose proof (known_quar A v [] AR _ (q_in_big A _ He)) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). exact (AGp c' k Hc Hk).
    - intros c' Hc. apply (shadow_tails_P A v v' [] AR c' Hc); intros z Hz.
      + (first [ pose proof ((region_tail_shadow A v [] AR c' Hc)) as dR_71; dand5 dR_71 as X1 _ _ X4 _ | pose proof (region_tail_shadow A v [] AR c' Hc) as (X1 & _ & _ & X4 & _) ]). apply AGsh.
        * pose proof (heap_shadow_rangeT A z W (X4 z Hz)) as IM. unfold in_shadow_maps in IM. clear -IM. kung_all. lia.
        * (* [comment removed for export] *)
          pose proof (region_piece_boundsT A c' W Hc) as RB. cbv zeta in RB. (first [ pose proof ((sb_factsT A W)) as dR_72; dand5 dR_72 as _ SBA HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & SBA & HB6 & RSB & SCE) ]).
          pose proof (sec_apart_b6 A v [] AR _ S0) as D6. cbn [cs_map cs_n] in D6. change (a_sb A) with sb in *.
          (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
          pose proof (sh_disjoint (region_beg sb c' + rg_allocated_user (a_reg A c')) (rg_mapped_user (a_reg A c') - rg_allocated_user (a_reg A c')) h msz
                        ltac:(rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) Q9), Q11; reflexivity)
                        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                        ltac:(rewrite <- Zminus_mod_idemp_l, Q10, <- Zminus_mod_idemp_r, Q11; reflexivity)
                        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL])
                        ltac:(unfold a_b6 in *; clear -D6 Q2 Q3 Q4 Q7 HB6 RSB; kung_all; lia)) as SD.
          clear -Hz SD X1. lia.
      + (first [ pose proof ((region_tail_shadow A v [] AR c' Hc)) as dR_74; dand6 dR_74 as _ _ _ _ X5 _ | pose proof (region_tail_shadow A v [] AR c' Hc) as (_ & _ & _ & _ & X5 & _) ]). apply AGsh.
        * pose proof (heap_shadow_rangeT A z W (X5 z Hz)) as IM. unfold in_shadow_maps in IM. clear -IM. kung_all. lia.
        * pose proof (region_piece_boundsT A c' W Hc) as RB. cbv zeta in RB. (first [ pose proof ((sb_factsT A W)) as dR_75; dand5 dR_75 as _ SBA HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & SBA & HB6 & RSB & SCE) ]).
          pose proof (sec_apart_b6 A v [] AR _ S0) as D6. cbn [cs_map cs_n] in D6. change (a_sb A) with sb in *.
          (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
          pose proof (sh_disjoint (region_beg sb c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c')) h msz
                        ltac:(rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) Q9); reflexivity)
                        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                        Q12
                        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL])
                        ltac:(unfold a_b6 in *; clear -D6 Q2 Q5 Q6 Q7 HB6 RSB; kung_all; lia)) as SD.
          clear -Hz SD. unfold sh in *. lia.
    - intros u mb n1 Hl. apply (shadow_seclive_P A v v' [] AR u); [exact Hl|].
      pose proof (known_live A v [] AR u _ Hl) as CL. pose proof (known_carved A v [] AR _ _ CL) as Cc. cbn [li_chunk li_n] in Cc.
      assert (NE : ChS (CS mb n1) <> ChS (CS h n0)) by exact (rsec_live_other A kb n0 (CS h n0) es more WR LQ u _ Hl).
      intros z Hz. apply (AGc _ Cc NE). cbn [chunk_lo chunk_hi]. replace (mb + map_size n1 - mb) with (map_size n1) by lia. exact Hz.
    - intros mb n2 n1 He. apply (shadow_secquar_P A v v' [] AR mb n2); [exact He|].
      pose proof (known_quar A v [] AR _ (q_in_big A _ He)) as CL. pose proof (known_carved A v [] AR _ _ CL) as Cc. cbn [qe_chunk qe_n] in Cc. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]).
      assert (NE : ChS (CS mb n1) <> ChS (CS h n0)) by exact (kquar_other (QE (ChS (CS mb n1)) n1) He).
      intros z Hz. apply (AGc _ Cc NE). cbn [chunk_lo chunk_hi]. replace (mb + map_size n1 - mb) with (map_size n1) by lia. exact Hz.
  Qed.

  #[using="IAP IAL IAH PDR PHLC PARR PLCK PNSRT NNH' SHI8 SHI SLO NNH AG QTN G S0 W WLO NTH LQ WR AR whi wlo m"] Theorem krecs_arepr : @arepr _ DepotRepL LPA AL_pasan [] A' v'.
  Proof.
    (first [ pose proof (fs_fs) as dR_78; dand3 dR_78 as F1 F2 F3 | pose proof fs_fs as (F1 & F2 & F3) ]). pose proof fs_quar as FQ. pose proof fs_shadow as FSH. rewrite QTN in FQ, FSH.
    constructor; cbn [recsA a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_sb a_fs].
    - exact fs_consts.
    - exact fs_locks.
    - exact fs_regions.
    - exact fs_cache.
    - exact fs_live.
    - exact FQ.
    - exact fs_sec.
    - exact PDR.
    - exact fs_ia.
    - exact F1.
    - exact F2.
    - exact F3.
    - exact (maps_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH').
    - exact FSH.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="S0 W NTH WR AR m Clg"] Lemma rt_maps_sub : forall b sz, In (b, sz) (runtime_maps_ P (a_reg A) (sec_remove (a_sec A) i)) ->
    In (b, sz) (runtime_maps_ P (a_reg A) (a_sec A)) /\ (b + sz <= h \/ h + msz <= b \/ sz <= 0).
  Proof.
    intros b sz Hin. (first [ pose proof ((bm_nth_fixed A)) as dR_79; dand15 dR_79 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
    (first [ pose proof ((sb_factsT A W)) as dR_80; dand5 dR_80 as _ _ HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (sec_apart_b6 A v [] AR _ S0) as D6. cbn [cs_map cs_n] in D6.
    unfold a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_pa, a_itab, a_m64k, a_b6, a_sb in *.
    unfold runtime_maps_ in Hin |- *. cbn [sec_remove sr_chunks] in Hin. rewrite !in_app_iff in Hin |- *.
    destruct Hin as [Hin|[Hin|Hin]].
    - split; [left; exact Hin|]. cbn in Hin. unfold p_ri in *.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-;
        first [ (* [comment removed for export] *) lazymatch goal with |- ?b + _ <= _ \/ _ => match goal with Ek : nth_error (big_maps A) _ = Some (b, _) |- _ => pose proof (bm_sepT A _ _ _ _ _ _ W Ek Es ltac:(lia)); lia end end
              | pose proof (bm_sepT A _ _ _ _ _ _ W E4 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E5 Es ltac:(lia)); lia
              | pose proof (bm_sepT A _ _ _ _ _ _ W E6 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E7 Es ltac:(lia)); lia
              | pose proof (bm_sepT A _ _ _ _ _ _ W E8 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E1 Es ltac:(lia)); kung_all; lia
              | pose proof (bm_sepT A _ _ _ _ _ _ W E9 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E10 Es ltac:(lia)); lia
              | pose proof (bm_sepT A _ _ _ _ _ _ W E14 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E11 Es ltac:(lia)); lia
              | pose proof (bm_sepT A _ _ _ _ _ _ W E12 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E13 Es ltac:(lia)); lia
              | kung_all; lia ].
    - split; [right; left; exact Hin|]. apply in_flat_map in Hin as (c' & Hc' & Hin). apply in_map_iff in Hc' as (k' & <- & Hk'). apply in_seq in Hk'.
      pose proof (region_piece_boundsT A (Z.of_nat k') W ltac:(lia)) as RB. cbv zeta in RB. unfold a_sb in RB.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; kung_all; lia.
    - apply in_map_iff in Hin as (c & E & Hc). injection E as <- <-. apply (rchunks'_in_iff A (CS h n0) i WR NTH) in Hc as [Hc NEc].
      split; [right; right; apply in_map_iff; exists c; split; [reflexivity| exact Hc]|].
      destruct (In_nth_error' _ _ Hc) as [j Hj].
      pose proof (bk_sep_chunks A v AR j i c (CS h n0) Hj NTH ltac:(intros ->; rewrite NTH in Hj; injection Hj as E; exact (NEc (eq_sym E)))) as D.
      cbn [cs_map cs_n] in D. unfold apart in D. lia.
  Qed.

  #[using="S0 W NTH WR AR m"] Lemma fs_owned_new : forall a, pa_owned A' a -> pa_owned A a.
  Proof.
    intros a H. unfold pa_owned, aowned, aowned_ in *. cbn [recsA a_pl a_reg a_livemap a_sec a_fframes] in H.
    destruct H as [[St|[[(R1 & NU & NF)|[HS|FS]]|GH]]|I]; [left; left; exact St| | | left; right; left; right; right; exact FS| left; right; right; exact GH| right; exact I].
    - (first [ dex2 R1 as b sz; destruct R1 as [Hin Hb] | dand4 R1 as b sz Hin Hb | destruct R1 as (b & sz & Hin & Hb) ]). destruct (rt_maps_sub b sz Hin) as [Hin0 AP].
      left. right. left. left. split; [exists b, sz; split; [exact Hin0| exact Hb]|]. split; [| exact NF].
      exact NU.
    - left. right. left. right. left. unfold heap_shadow_ in *. cbn [sec_remove sr_chunks] in HS.
      destruct HS as [HS|[HS|(c & Hc & Hz)]]; [left; exact HS| right; left; exact HS| right; right].
      exists c. split; [| exact Hz]. apply (rchunks'_in_iff A (CS h n0) i WR NTH) in Hc as [Hc _]. exact Hc.
  Qed.

  (* [comment removed for export] *)
  #[using="S0 W NTH LQ WR AR i more es kb m"] Lemma fs_shadow_ghost : forall z, sh h <= z < sh h + msz / 8 -> ghost_hs_ P z.
  Proof.
    intros z Hz. (first [ pose proof (bnds) as dR_82; dand4 dR_82 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    (first [ pose proof ((bk_shr A v p n0 kb es more AR WR LQ)) as dR_83; dand4 dR_83 as SHA _ _ SIDE | pose proof (bk_shr A v p n0 kb es more AR WR LQ) as (SHA & _ & _ & SIDE) ]). pose proof alloc_ceiling_val as CE.
    split.
    - unfold in_shadow_maps. clear -Hz SIDE. kung_all. unfold kHighShadowMapSize. lia.
    - ((first [ intro dR_111; dex2 dR_111 as b n; destruct dR_111 as [Hin Rz] | intro dR_111; dand4 dR_111 as b n Hin Rz | intros (b & n & Hin & Rz) ])). (first [ pose proof ((bm_nth_fixed A)) as dR_84; dand15 dR_84 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
      pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
      (first [ pose proof ((sb_factsT A W)) as dR_85; dand5 dR_85 as _ _ HB6 RSB SCE | pose proof (sb_factsT A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (sec_apart_b6 A v [] AR _ S0) as D6. cbn [cs_map cs_n] in D6.
      unfold a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_pa, a_itab, a_m64k, a_b6, a_sb in *.
      (* [comment removed for export] *)
      assert (DJ : b + n <= h \/ h + msz <= b).
      { unfold VIS0 in Hin. cbn in Hin. unfold stack_band_iv in Hin.
        destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]; injection E as <- <-;
          first [ (* [comment removed for export] *) lazymatch goal with |- ?b + _ <= _ \/ _ => match goal with Ek : nth_error (big_maps A) _ = Some (b, _) |- _ => pose proof (bm_sepT A _ _ _ _ _ _ W Ek Es ltac:(lia)); lia end end
                | pose proof (bm_sepT A _ _ _ _ _ _ W E11 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E12 Es ltac:(lia)); lia
                | pose proof (bm_sepT A _ _ _ _ _ _ W E8 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E7 Es ltac:(lia)); lia
                | pose proof (bm_sepT A _ _ _ _ _ _ W E6 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E4 Es ltac:(lia)); lia
                | pose proof (bm_sepT A _ _ _ _ _ _ W E13 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E5 Es ltac:(lia)); lia
                | pose proof (bm_sepT A _ _ _ _ _ _ W E14 Es ltac:(lia)); lia
                | unfold p_ri in *; kung_all; lia
                | pose proof (bm_sepT A _ _ _ _ _ _ W E9 Es ltac:(lia)); lia | pose proof (bm_sepT A _ _ _ _ _ _ W E10 Es ltac:(lia)); lia
                | lia ]. }
      (first [ pose proof ((bk_geo A v p n0 kb es more AR WR LQ)) as dR_86; dand5 dR_86 as _ HAL _ MSZAL _ | pose proof (bk_geo A v p n0 kb es more AR WR LQ) as (_ & HAL & _ & MSZAL & _) ]).
      unfold sh, kShadowOffset in Hz. unfold kShadowOffset in Rz. clear -Hz Rz DJ HAL MSZAL.
      set (q1 := (p - 6144) / 4096) in *. set (q2 := msz / 4096) in *.
      pose proof (Z_div_mod_eq_full (p - 6144) 4096) as Q1. rewrite HAL, Z.add_0_r in Q1. pose proof (Z_div_mod_eq_full msz 4096) as Q2. rewrite MSZAL, Z.add_0_r in Q2.
      fold q1 in Q1. fold q2 in Q2. clearbody q1 q2.
      assert (H8 : (p - 6144) / 8 = 512 * q1) by (rewrite Q1; replace (4096 * q1) with (512 * q1 * 8) by lia; apply Z_div_mult; lia).
      assert (M8 : msz / 8 = 512 * q2) by (rewrite Q2; replace (4096 * q2) with (512 * q2 * 8) by lia; apply Z_div_mult; lia).
      rewrite H8, M8 in Hz. destruct DJ as [DJ|DJ].
      + apply (Z.div_le_mono _ _ 8) in DJ; [|lia]. rewrite H8 in DJ. lia.
      + apply (Z.div_le_mono _ _ 8) in DJ; [|lia].
        replace ((p - 6144 + msz) / 8) with (512 * q1 + 512 * q2) in DJ by (rewrite Q1, Q2; symmetry; replace (4096 * q1 + 4096 * q2) with ((512 * q1 + 512 * q2) * 8) by lia; apply Z_div_mult; lia).
        lia.
  Qed.

  Hypothesis HNONE : forall a, h <= a < h + msz -> v' (wz a) = None.
  Hypothesis SM : mapped v wlo (whi - wlo).
  Hypothesis WHI : whi <= 2^47.

  (* [comment removed for export] *)
  #[using="S0 NTH LQ WR AR i more es kb m"] Lemma krecs_own_map : forall a, h <= a < h + msz -> pa_owned A a.
  Proof.
    intros a Ha. apply (carved_owned A v [] AR (ChS (CS h n0)) a S0); [cbn [chunk_lo chunk_hi]; exact Ha|].
    intros u li' Hl E Hu. exact (rsec_live_other A kb n0 (CS h n0) es more WR LQ u li' Hl E).
  Qed.

  (* [comment removed for export] *)
  #[using="WHI SM HNONE PHLC PARR NNH AG G S0 W WLO NTH LQ WR AR"] Theorem krecs_rstep : rstep (pa_owned A) (pa_owned A') wlo whi v v'.
  Proof.
    (first [ pose proof (bnds) as dR_87; dand4 dR_87 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof (aobj_facts _ _ PA) as PA'. pose proof (aobj_facts _ _ HM) as HM'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bk_geo A v p n0 kb es more AR WR LQ)) as dR_88; dand11 dR_88 as HLO HAL MSZ MSZAL HHI' PH PIN N6 NR _ PM | pose proof (bk_geo A v p n0 kb es more AR WR LQ) as (HLO & HAL & MSZ & MSZAL & HHI' & PH & PIN & N6 & NR & _ & PM) ]).
    (first [ pose proof ((bk_last A v p n0 kb es more AR WR LQ)) as dR_89; dand3 dR_89 as EL INL _ | pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & INL & _) ]).
    assert (OWNhla : forall a, hla + 24 <= a < hla + 32 -> pa_owned A a).
    { intros a Ha. apply (carved_owned A v [] AR (ChS (sec_last A)) a INL); [rewrite chunk_lo_S, chunk_hi_S; lia|].
      intros u li' Hl E Hu. pose proof (user_in A _ _ (known_live A v [] AR u li' Hl)) as UI. rewrite E, chunk_lo_S, chunk_hi_S in UI.
      destruct (wtV A W) as (V1 & _). (first [ pose proof ((V1 u li' Hl)) as dR_90; dand3 dR_90 as _ U _ | pose proof (V1 u li' Hl) as (_ & U & _) ]). cbv zeta in U. rewrite E in U. destruct (sec_last A) as [mbl nl] eqn:EQL. cbn [user_of cs_map] in U, Ha, UI. unfold sec_user_beg, kPageSize in U. lia. }
    assert (OWNpa : forall a, pa + 8 * Z.of_nat i <= a < pa + 8 * Z.of_nat i + 8 -> pa_owned A a).
    { intros a Ha. (first [ pose proof ((bk_nch A v p n0 kb es more AR WR LQ)) as dR_91; dand4 dR_91 as _ NR1 NR2 _ | pose proof (bk_nch A v p n0 kb es more AR WR LQ) as (_ & NR1 & NR2 & _) ]). (first [ pose proof ((bm_nth_fixed A)) as dR_92; dand3 dR_92 as _ E1 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _) ]). unfold a_pa in E1.
      apply (owned_rt A a pa (8 * kChunksBlockCount)); [unfold runtime_maps, runtime_maps_; rewrite !in_app_iff; left; cbn; clear - E1; tauto| clear -Ha IR NR1 NR2; kung_all; lia| |].
      - eapply (fixed_bm_no_live_userT A 1); [exact W| lia| exact E1| clear -Ha IR NR1 NR2; kung_all; lia].
      - eapply (fixed_bm_no_live_frameT A 1); [exact W| lia| lia| exact E1| clear -Ha IR NR1 NR2; kung_all; lia]. }
    unfold rstep. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - (* [comment removed for export] *)
      intros a Ha NO NO' NW. apply AG; [exact Ha|]. intros X. exc14 X.
      + exact (NW X).
      + apply NO. apply (thr_owned A v [] AR). clear -X. lia.
      + apply NO. apply (thr_owned A v [] AR). clear -X. lia.
      + apply NO. apply (dstat_owned A). exact X.
      + apply NO. apply (n0_owned A v [] AR). exact X.
      + apply NO. apply (f0_owned A v [] AR). exact X.
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
      + apply NO. apply OWNpa. exact X.
      + apply NO. apply OWNhla. exact X.
      + exact (NO (krecs_own_map a X)).
      + apply NO. left. right. left. right. left. unfold heap_shadow_. right. right. exists (CS h n0). split; [exact S0| cbn [cs_map cs_n]; exact X].
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
    - (* [comment removed for export] *)
      intros a Ha NI Hv. destruct (decide (h <= a < h + msz)) as [Y|Y]; [left; exact (krecs_own_map a Y)|].
      destruct (decide (pbeg <= a < pend)) as [Z1|Z1].
      + left. left. right. left. right. left. unfold heap_shadow_. right. right. exists (CS h n0). split; [exact S0| cbn [cs_map cs_n]].
        (first [ pose proof ((ka8_geo p n0 G)) as dR_93; dand7 dR_93 as G1 _ _ _ _ G6 _ | pose proof (ka8_geo p n0 G) as (G1 & _ & _ & _ & _ & G6 & _) ]). clear -Z1 G1 G6. lia.
      + right. apply NNH; [lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| lia| unfold AFreeX3.holeD; clear -Y Z1; lia| exact Hv].
    - eapply mapped_mono; [exact SM|]. intros k Hk Hvk. (first [ pose proof ((place_factsT A W)) as dR_94; dand14 dR_94 as _ _ _ _ _ _ _ _ _ _ _ _ Psp0 _ | pose proof (place_factsT A W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Psp0 & _) ]). cbv zeta in Psp0.
      (first [ pose proof ((ka8_geo p n0 G)) as dR_95; dand7 dR_95 as _ _ _ _ _ G6 _ | pose proof (ka8_geo p n0 G) as (_ & _ & _ & _ & _ & G6 & _) ]).
      apply NNH; [clear -WLO CE Hk; lia| right; clear -WLO CE Hk; lia| clear -Hk WHI Psp0; lia| unfold AFreeX3.holeD; clear -Hk WLO HHI R2 CE G6; kung_all; lia| exact Hvk].
    - intros a Ha O'. left. exact (fs_owned_new a O').
    - (* [comment removed for export] *)
      intros a Ha O NO'.
      destruct (decide (h <= a < h + msz)) as [Y|Y]; [exact (HNONE a Y)|]. exfalso. apply NO'.
      unfold pa_owned, aowned, aowned_ in O |- *. cbn [recsA a_pl a_reg a_livemap a_sec a_fframes sec_remove sr_chunks].
      destruct O as [[St|[[(R1' & NU & NF)|[HS|FS]]|GH]]|I]; [left; left; exact St| | | left; right; left; right; right; exact FS| left; right; right; exact GH| right; exact I].
      + left. right. left. left. (first [ dex2 R1' as b sz; destruct R1' as [Hin Hb] | dand4 R1' as b sz Hin Hb | destruct R1' as (b & sz & Hin & Hb) ]). split; [| split; [exact NU| exact NF]].
        exists b, sz. split; [| exact Hb]. unfold runtime_maps_ in Hin |- *. rewrite !in_app_iff in Hin |- *.
        destruct Hin as [Hin|[Hin|Hin]]; [left; exact Hin| right; left; exact Hin| right; right].
        apply in_map_iff in Hin as (c & E & Hc). apply in_map_iff. exists c. split; [exact E|]. apply (rchunks'_in_iff A (CS h n0) i WR NTH). split; [exact Hc|].
        intros ->. injection E as <- <-. exact (Y Hb).
      + destruct (decide (sh h <= a < sh h + msz / 8)) as [Z1|Z1]; [left; right; right; exact (fs_shadow_ghost a Z1)|].
        left. right. left. right. left. unfold heap_shadow_ in HS |- *. destruct HS as [HS|[HS|(c & Hc & Hz)]]; [left; exact HS| right; left; exact HS| right; right].
        exists c. split; [| exact Hz]. apply (rchunks'_in_iff A (CS h n0) i WR NTH). split; [exact Hc|]. intros ->. cbn [cs_map cs_n] in Hz. exact (Z1 Hz).
  Qed.

  (* [comment removed for export] *)
  #[using="S0 W NTH LQ WR AR i more es kb m Clg"] Lemma kSHD : forall ch, carved A ch -> ch <> ChS (CS h n0) ->
    forall z, sh (chunk_lo sb ch) <= z < sh (chunk_lo sb ch) + (chunk_hi sb ch - chunk_lo sb ch) / 8 -> ~ (sh h <= z < sh h + msz / 8).
  Proof.
    (first [ pose proof ((bk_geo A v p n0 kb es more AR WR LQ)) as dR_97; dand5 dR_97 as _ HAL _ MSZAL _ | pose proof (bk_geo A v p n0 kb es more AR WR LQ) as (_ & HAL & _ & MSZAL & _) ]).
    intros ch Cc NE z Hz X. pose proof (carved_disjoint A v [] AR ch (ChS (CS h n0)) Cc S0 NE) as Dm. cbn [chunk_lo chunk_hi] in Dm.
      pose proof (carved_shadow A v [] AR ch Cc) as CSH.
      destruct ch as [[c' k']|[mb n1]].
      - destruct Cc as [Hc Hk]. (first [ pose proof ((carved_chunk_boundsT A c' k' W Hc Hk)) as dR_98; dand4 dR_98 as _ _ B3 _ | pose proof (carved_chunk_boundsT A c' k' W Hc Hk) as (_ & _ & B3 & _) ]). pose proof (class_size_mod32 c' Hc) as CM.
        cbn [chunk_lo chunk_hi alloc_beg] in *.
        replace (chunk_addr sb c' k' + class_size c' - chunk_addr sb c' k') with (class_size c') in Hz by lia.
        pose proof (sh_disjoint (chunk_addr sb c' k') (class_size c') h msz ltac:(apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                      ltac:(apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL]) Dm) as SD.
        clear -Hz X SD. lia.
      - unfold carved in Cc. (first [ pose proof ((bk_chunk A v AR _ Cc)) as dR_99; dand3 dR_99 as C1 C2 _ | pose proof (bk_chunk A v AR _ Cc) as (C1 & C2 & _) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
        replace (mb + map_size n1 - mb) with (map_size n1) in Hz by lia. pose proof (map_size_page n1) as MP.
        pose proof (sh_disjoint mb (map_size n1) h msz ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact C2]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                      ltac:(apply (mod0_down _ kPageSize 8); [exists 512; reflexivity| exact MP]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL]) Dm) as SD.
        clear -Hz X SD. lia.
  Qed.
  #[using="AG S0 W WLO NTH LQ WR AR whi wlo i more es kb"] Lemma kAGc : forall ch, carved A ch -> ch <> ChS (CS h n0) ->
    forall z, sh (chunk_lo sb ch) <= z < sh (chunk_lo sb ch) + (chunk_hi sb ch - chunk_lo sb ch) / 8 -> v' (wz z) = v (wz z).
  Proof.
    pose proof kSHD as SHD.
    intros ch Cc NE z Hz. (first [ pose proof ((carved_shadow A v [] AR ch Cc)) as dR_100; dand3 dR_100 as CS1 CS2 CS3 | pose proof (carved_shadow A v [] AR ch Cc) as (CS1 & CS2 & CS3) ]). apply AGsh; [| exact (SHD ch Cc NE z Hz)].
      pose proof (heap_shadow_rangeT A z W (CS2 z ltac:(rewrite CS1; exact Hz))) as IM. unfold in_shadow_maps in IM. clear -IM. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="PHLC PARR W NTH LQ WR AR v' i more es kb n0 p m Clg"] Lemma kHF : forall ch n1 a, known A ch n1 -> carved A ch ->
    hdr_foot sb ch n1 a \/ (user_of sb ch n1 <= a < user_of sb ch n1 + 8) -> ~ (hla + 24 <= a < hla + 32).
  Proof.
    intros ch n1 a CL CC Ha X. (first [ pose proof (bnds) as dR_101; dand4 dR_101 as _ _ (_ & _ & HL4) _ | pose proof bnds as (_ & _ & (_ & _ & HL4) & _) ]).
    (first [ pose proof ((bk_last A v p n0 kb es more AR WR LQ)) as dR_102; dand3 dR_102 as EL INL _ | pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & INL & _) ]).
    pose proof (hdr_foot_in A _ _ a CL Ha) as IN.
    destruct (chunk_eq_dec ch (ChS (sec_last A))) as [E|NEL].
    - rewrite E in Ha. unfold hdr_foot in Ha. destruct (sec_last A) as [mbl nl] eqn:EQL. cbn [user_of alloc_beg cs_map] in Ha, X.
      unfold sec_user_beg, sec_alloc_beg, kPageSize in Ha. clear -Ha X. lia.
    - pose proof (carved_disjoint A v [] AR _ (ChS (sec_last A)) CC INL NEL) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl. clear -IN Dl X HL4. lia.
  Qed.

  #[using="PHLC PARR NNH' SHI8 SHI SLO NNH AG G S0 W WLO NTH LQ WR AR whi wlo i more es kb"] Lemma klentry_xfer : forall e', In e' (q_entries (a_qthread A ++ (a_qglobal A ++ a_qlimbo A))) -> qe_chunk e' <> ChS (CS h n0) ->
    lentry_cells sb v e' -> lentry_cells sb v' e'.
  Proof.
    (intros e' HeQ NE; (first [ intro dR_112; dand4 dR_112 as HR J MC SH | intros (HR & J & MC & SH) ])). pose proof alloc_ceiling_val as CE.
    pose proof (known_quar A v [] AR e' HeQ) as CL. pose proof (known_range A v [] AR _ _ CL) as RNG.
    pose proof (known_carved A v [] AR _ _ CL) as CV. pose proof (user_in A _ _ CL) as UI.
    split; [|split; [|split]].
    - apply (hdr_P A v v'); [| exact HR]. intros a Ha. apply (AGchunk (qe_chunk e') a CV NE); [| exact (kHF _ _ a CL CV (or_introl Ha))].
      apply (hdr_foot_in A _ (qe_n e')); [exact CL| left; exact Ha].
    - eapply junk_at_agree; [exact J|]. intros k Hk. apply (AGchunk (qe_chunk e') _ CV NE); [| apply (kHF _ _ _ CL CV); right; lia].
      apply (hdr_foot_in A _ (qe_n e')); [exact CL| right; lia].
    - apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| right; lia| lia| | exact MC]. intros x Hx.
      apply (hole_free_carved A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 (qe_chunk e') x CV NE). lia.
    - destruct (qe_chunk e') as [[c'' k'']|[mb n1]] eqn:EC.
      + eapply bytes_at_xfer; [exact SH|]. intros z Hz. apply (kAGc (ChP (CP c'' k'')) CV NE). cbn [chunk_lo chunk_hi alloc_beg].
        replace (chunk_addr sb c'' k'' + class_size c'' - chunk_addr sb c'' k'') with (class_size c'') by lia.
        unfold known in CL. (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). rewrite (pshadow_quar_length c'' (qe_n e')) in Hz by lia. exact Hz.
      + eapply bytes_at_xfer; [exact SH|]. intros z Hz. unfold known in CL. (first [ dand3 CL as Hin Hn En | destruct CL as (Hin & Hn & En) ]). subst n1.
        apply (kAGc (ChS (CS mb (qe_n e'))) CV NE). cbn [chunk_lo chunk_hi cs_map cs_n].
        replace (mb + map_size (qe_n e') - mb) with (map_size (qe_n e')) by lia.
        rewrite (sshadow_quar_length (qe_n e')) in Hz by lia. exact Hz.
  Qed.

  (* [comment removed for export] *)
  #[using="NNH' SHI8 SHI SLO NNH AG G S0 W WLO NTH LQ WR AR whi wlo i more es kb n0 p"] Lemma klbatch_xfer : forall idx es0 (j : nat) sz, carved A (ChP (CP kQuarantineBatchClass idx)) ->
    Z.of_nat (length es0) <= kQuarantineBatchCount ->
    let ba := chunk_addr sb kQuarantineBatchClass idx in
    lbatch_cells sb v ba es0 j sz ->
    lbatch_cells sb v' ba es0 j sz /\
    (bytes_at rsegs v (sh ba) (pshadow_free kQuarantineBatchClass) -> bytes_at rsegs v' (sh ba) (pshadow_free kQuarantineBatchClass)).
  Proof.
    intros idx es0 j sz CV LEN. cbv zeta. ((first [ intro dR_113; dand3 dR_113 as SL SZ MP | intros (SL & SZ & MP) ])). pose proof alloc_ceiling_val as CE.
    (first [ pose proof (bnds) as dR_105; dand4 dR_105 as _ _ (_ & _ & HL4) _ | pose proof bnds as (_ & _ & (_ & _ & HL4) & _) ]). (first [ pose proof ((bk_last A v p n0 kb es more AR WR LQ)) as dR_106; dand3 dR_106 as EL INL _ | pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & INL & _) ]).
    (first [ pose proof ((carved_range A v [] AR _ CV)) as dR_107; dand3 dR_107 as R1 R2 R3 | pose proof (carved_range A v [] AR _ CV) as (R1 & R2 & R3) ]). cbn [chunk_lo chunk_hi alloc_beg] in R1, R2, R3.
    assert (NE : ChP (CP kQuarantineBatchClass idx) <> ChS (CS h n0)) by discriminate.
    pose proof (carved_disjoint A v [] AR _ (ChS (sec_last A)) CV INL ltac:(discriminate)) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl.
    cbn [chunk_lo chunk_hi alloc_beg] in Dl. change (class_size kQuarantineBatchClass) with 8192 in Dl, R2, R3.
    assert (AGb : forall a, chunk_addr sb kQuarantineBatchClass idx <= a < chunk_addr sb kQuarantineBatchClass idx + kQuarantineBatchBytes -> v' (wz a) = v (wz a)).
    { intros a Ha. apply (AGchunk _ a CV NE); [cbn [chunk_lo chunk_hi alloc_beg]; unfold kQuarantineBatchBytes in Ha; change (class_size kQuarantineBatchClass) with 8192; exact Ha|].
      unfold kQuarantineBatchBytes in Ha. clear -Ha Dl HL4. lia. }
    split; [split; [|split]|].
    - intros i0 e Hi He. eapply u64_at_agree; [exact (SL i0 e Hi He)|]. intros q Hq. apply AGb. pose proof (nth_error_Some_lt _ _ _ He).
      unfold off_qb_batch, kQuarantineBatchBytes, kQuarantineBatchCount in *. lia.
    - eapply u64_at_agree; [exact SZ|]. intros q Hq. apply AGb. unfold off_qb_size, kQuarantineBatchBytes in *. lia.
    - unfold kQuarantineBatchBytes in *. apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| right; lia| lia| | exact MP].
      intros x Hx. apply (hole_free_carved A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 _ x CV NE). cbn [chunk_lo chunk_hi alloc_beg].
      change (class_size kQuarantineBatchClass) with 8192. lia.
    - intros SH. eapply bytes_at_xfer; [exact SH|]. intros z Hz. apply (kAGc _ CV NE). cbn [chunk_lo chunk_hi alloc_beg].
      replace (chunk_addr sb kQuarantineBatchClass idx + class_size kQuarantineBatchClass - chunk_addr sb kQuarantineBatchClass idx) with (class_size kQuarantineBatchClass) by lia.
      unfold pshadow_free, fa8 in Hz. rewrite repeat_length, Z2Nat.id in Hz by (change (class_size kQuarantineBatchClass) with 8192; lia). exact Hz.
  Qed.

  #[using="AG S0 W WLO NTH LQ WR AR whi wlo i more es kb n0 p"] Lemma ktmp_chain_xfer : forall bs, (forall b', In b' bs -> In b' (a_qthread A ++ (a_qglobal A ++ a_qlimbo A))) -> tmp_chain sb v bs -> tmp_chain sb v' bs.
  Proof.
    induction bs as [|b' bs IH]; intros SUB TC; [exact I|]. cbn [tmp_chain] in *. destruct TC as [X TC].
    (first [ pose proof (bnds) as dR_108; dand4 dR_108 as _ _ (_ & _ & HL4) _ | pose proof bnds as (_ & _ & (_ & _ & HL4) & _) ]). (first [ pose proof ((bk_last A v p n0 kb es more AR WR LQ)) as dR_109; dand3 dR_109 as EL INL _ | pose proof (bk_last A v p n0 kb es more AR WR LQ) as (EL & INL & _) ]).
    assert (Hb : In b' (a_qthread A ++ (a_qglobal A ++ a_qlimbo A))) by (apply SUB; left; reflexivity).
    pose proof (batch_carved A v [] AR b' Hb) as CV. (first [ pose proof ((batch_range A v [] AR b' Hb)) as dR_110; dand3 dR_110 as R1 R2 R3 | pose proof (batch_range A v [] AR b' Hb) as (R1 & R2 & R3) ]).
    pose proof (carved_disjoint A v [] AR _ (ChS (sec_last A)) CV INL ltac:(discriminate)) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl.
    cbn [chunk_lo chunk_hi alloc_beg] in Dl. change (class_size kQuarantineBatchClass) with 8192 in Dl.
    split; [| apply IH; [intros b'' Hb''; apply SUB; right; exact Hb''| exact TC]].
    eapply rw_cells_agree; [exact X|]. cbn [cells_size csize Nat.add]. intros i0 Hi. apply (AGchunk _ _ CV ltac:(discriminate)).
    - cbn [chunk_lo chunk_hi alloc_beg]. unfold batch_addr in *. change (class_size kQuarantineBatchClass) with 8192. lia.
    - unfold batch_addr in *. clear -Hi Dl HL4. lia.
  Qed.
End KReprS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section KHiddenS.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (p n0 : Z) (i : nat) (m' : mem).
  Hypothesis WR : WFR A.
  Hypothesis HID : hidden_repr (a_pl A) (a_reg A) (a_sec A) m.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some (CS (p - 6144) n0).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  (* [comment removed for export] *)
  Hypothesis HID1 : forall z, in_shadow_maps z -> ~ (sh h <= z < sh h + msz / 8) -> m' (wz z) = m (wz z).
  Hypothesis HID2 : forall z, sh h <= z < sh h + msz / 8 -> m' (wz z) = Some (Z_to_bv 8 0).

  #[using="HID2 HID1 NTH HID WR n0 p m"] Theorem krecs_hidden : hidden_repr (a_pl A) (a_reg A) (sec_remove (a_sec A) i) m'.
  Proof.
    pose proof HID as [H1 H2]. unfold hidden_repr.
    split.
    - intros z GZ. pose proof GZ as [IM _].
      destruct (decide (sh h <= z < sh h + msz / 8)) as [IN|OUT].
      + rewrite (HID2 z IN). split; [discriminate| intros _; reflexivity].
      + rewrite (HID1 z IM OUT). destruct (H1 z GZ) as [P1 P2]. split; [exact P1|].
        intros NHS. apply P2. intros HS. apply NHS. unfold heap_shadow_ in HS |- *. cbn [sec_remove sr_chunks].
        destruct HS as [HS|[HS|(c & Hc & Hz)]]; [left; exact HS| right; left; exact HS| right; right].
        exists c. split; [| exact Hz]. apply (rchunks'_in_iff A (CS h n0) i WR NTH). split; [exact Hc|]. intros ->. cbn [cs_map cs_n] in Hz. exact (OUT Hz).
    - intros z Hz NB. destruct (decide (sh h <= z < sh h + msz / 8)) as [IN|OUT]; [rewrite (HID2 z IN); discriminate|].
      rewrite (HID1 z ltac:(unfold in_shadow_maps; left; exact Hz) OUT). exact (H2 z Hz NB).
  Qed.
End KHiddenS.

