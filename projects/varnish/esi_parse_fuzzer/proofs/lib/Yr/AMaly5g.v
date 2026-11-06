(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMTac AMallocA AMallocH AMalmys AMal9l1.

Module AMal5j7.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocA AMallocH AMalmys AMal9l1.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.solve_load ::= first [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd.DA_Tac.solve_load_guarded | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.solve_load_image].
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize in *.

Lemma div8_ceil : forall n, 0 <= n -> (n + 7) / 8 = n / 8 + Z.min (n mod 8) 1.
Proof. intros n Hn. pose proof (Z_div_mod_eq_full n 8). pose proof (Z.mod_pos_bound n 8 ltac:(lia)). pose proof (Z_div_mod_eq_full (n + 7) 8). pose proof (Z.mod_pos_bound (n + 7) 8 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Definition const_nodepot (c : Z * list byte) : bool := (fst c + Z.of_nat (length (snd c)) <=? 0x187288) || (0x5d72a8 <=? fst c).
Lemma pa_consts_nodepot : forallb const_nodepot pa_consts = true.
Proof. vm_compute. reflexivity. Qed.

Section ReprPost.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model) (n kidx : Z) (key : list Z) (sp : word) (v' : mem).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Local Notation c := (class_of n).
  Local Notation ks' := (pk_chunks (a_cache A (class_of n))).
  Hypothesis NE : ks' <> [].
  Hypothesis KID : kidx = nth (length ks' - 1) ks' 0.
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned sp - ASTK.
  Local Notation v := (aview_of (pa_hull A) m).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation AB := (chunk_addr (a_sb A) (class_of n) kidx).
  Local Notation u := (hit_user A n kidx).
  Local Notation n0 := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation D := (a_depot A).
  Local Notation W := (malloc_hit_W sp thr (class_of n) AB n (AB / 8) (rz_size n / 8) (n / 8) (n mod 8) n0 f0).
  Local Notation W2 := (alloc_hit_W2 (Z_to_bv 64 (bv_unsigned sp + -2144)) thr (class_of n) AB n (AB / 8) (rz_size n / 8) (n / 8) (n mod 8)).
  (* [comment removed for export] *)
  Local Notation shU := (AB / 8 + rz_size n / 8 + kShadowOffset).

  (* [comment removed for export] *)
  Hypothesis MU : munch W v v'.
  Hypothesis WMv : wmono rsegs v v'.
  (* [comment removed for export] *)
  Hypothesis NN : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> v (Z_to_bv 64 a) <> None -> v' (Z_to_bv 64 a) <> None.

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let R : @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (ai_repr _ _ _ _ _ _ _ AI). Qed.

  (* [comment removed for export] *)
  #[using="KID NE NR AI md m Clg"] Lemma KIN : In kidx ks'. Proof. rewrite KID. exact (proj1 (proj2 (hit_kidx A m md n AI NR NE))). Qed.
  (* [comment removed for export] *)
  #[using="WF0 CEIL KID NE NR AI md m"] Lemma GEO :
    4096 <= thr /\ thr + 4096 <= alloc_ceiling /\ kHighMemBeg <= sb /\ sb + 2^37 <= alloc_ceiling /\
    region_beg sb c <= AB /\ AB + class_size c <= region_beg sb c + rg_allocated_user (a_reg A c) /\
    rg_allocated_user (a_reg A c) <= rg_mapped_user (a_reg A c) /\ region_beg sb c + rg_mapped_user (a_reg A c) <= region_beg sb c + kFreeArrayOffset /\
    sb <= region_beg sb c /\ region_beg sb c + kRegionSize <= sb + kSpaceSize /\
    rz_size n + n <= class_size c /\ 16 <= rz_size n /\ rz_size n = 8 * (rz_size n / 8) /\ AB = 8 * (AB / 8) /\ 32 <= class_size c /\
    class_size c = 8 * (class_size c / 8) /\ n = 8 * (n / 8) + n mod 8 /\ 0 <= n mod 8 < 8 /\
    4096 <= n0 /\ n0 + kDepotNodesBlock <= alloc_ceiling /\ 4096 <= f0 /\ f0 + kStackStoreBlockBytes <= alloc_ceiling /\
    alloc_ceiling <= bv_unsigned sp - 8192 /\ bv_unsigned sp < 2^64 /\ 1 <= c <= 30 /\ 0 <= kidx < carved_count A c /\
    0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000.   (* [comment removed for export] *)
  Proof.
    (first [ pose proof ((hit_geom A m md n kidx AI NR KIN)) as dR_1; dand15 dR_1 as _ M32 Q8 S1 S2 R8 HB HB2 R1 R2 FIT _ CR KB _ | destruct (hit_geom A m md n kidx AI NR KIN) as (_ & M32 & Q8 & S1 & S2 & R8 & HB & HB2 & R1 & R2 & FIT & _ & CR & KB & _) ]).
    (first [ pose proof ((hit_class n NR)) as dR_2; dand5 dR_2 as _ _ _ CSR CM32 | destruct (hit_class n NR) as (_ & _ & _ & CSR & CM32) ]).
    (first [ pose proof ((carved_chunk_bounds A c kidx WF0 CR KB)) as dR_3; dand3 dR_3 as B1 B2 _ | pose proof (carved_chunk_bounds A c kidx WF0 CR KB) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c WF0 CR) as RB. cbv zeta in *.
    (first [ pose proof ((hit_sep A m md AI)) as dR_4; dand13 dR_4 as _ _ _ _ _ _ _ _ _ N1 N2 F1 F2 | destruct (hit_sep A m md AI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & F1 & F2) ]). apply aobj_facts in N1. apply aobj_facts in F1.
    pose proof (place_facts A WF0) as (Pthr & _). cbv zeta in Pthr. (first [ dand3 Pthr as Pthr PthrC PthrM | destruct Pthr as (Pthr & PthrC & PthrM) ]). apply app_facts in Pthr.
    pose proof alloc_ceiling_val as CE. pose proof (rz_size_range n).
    pose proof (Z_div_mod_eq_full (class_size c) 8). pose proof (mod0_down (class_size c) 32 8 ltac:(exists 4; reflexivity) CM32).
    pose proof (Z_div_mod_eq_full n 8). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. unfold ASTK in CEIL.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try lia.
  Qed.

  #[using="AI md m"] Lemma GEOP : aobj thr 4096 /\ aobj n0 kDepotNodesBlock /\ aobj f0 kStackStoreBlockBytes.
  Proof.
    (first [ pose proof ((hit_sep A m md AI)) as dR_6; dand13 dR_6 as _ _ _ _ _ _ _ _ _ N1 _ F1 _ | destruct (hit_sep A m md AI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & F1 & _) ]).
    destruct (hit_place A m md AI) as (T1 & _). exact (conj T1 (conj N1 F1)).
  Qed.
  Ltac geop := let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in
    (first [ pose proof (GEOP) as dR_7; dand3 dR_7 as Gt Gn Gf | pose proof GEOP as (Gt & Gn & Gf) ]); aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf.

  (* [comment removed for export] *)
  #[using="MU"] Lemma AGW : forall a, 0 <= a < 2^64 -> outside W a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha Ho. apply MU. rewrite unsigned_lit by lia. exact Ho. Qed.

  (* [comment removed for export] *)
  #[using="WF0 CEIL KID NE NR AI md m Clg"] Lemma W_shape : forall a,
    ~ (bv_unsigned sp - 2352 <= a < bv_unsigned sp) -> a <> thr + 3168 ->
    ~ (bv_unsigned sp - 3168 <= a < bv_unsigned sp - 2144) ->
    ~ (thr + 208 + 80 * c <= a < thr + 208 + 80 * c + 4) -> ~ (thr + 2784 <= a < thr + 2792) ->
    ~ (AB <= a < AB + rz_size n + Z.min n 4096) ->
    ~ (0x187288 <= a < 0x5d72a8) -> ~ (n0 <= a < n0 + 0x100000) -> ~ (f0 <= a < f0 + 0x800000) ->
    ~ (shU <= a < shU + (n + 7) / 8) ->
    ~ (thr + 2800 <= a < thr + 2824) -> ~ (thr + 2912 + 8 * c <= a < thr + 2912 + 8 * c + 8) ->
    outside W a.
  Proof.
    intros a X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11 X12. pose proof GEO as G.
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CE. unfold ASTK in CEIL.
    unfold malloc_hit_W, alloc_hit_W. cbn [app outside]. rewrite !unsigned_lit by lia.
    pose proof (Z.le_min_l n 4096) as MN1. pose proof (Z.min_glb n 4096 1 ltac:(lia) ltac:(lia)) as MN2. pose proof (div8_ceil n ltac:(lia)) as DC.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ assumption
      | lazymatch goal with |- ~ (?p <= ?x < ?p + 1) => match goal with X : x <> p |- _ => clear - X; lia end end
      | lazymatch goal with |- ~ (?lo <= ?x < ?hi) =>
          let b := (let rec lb e := lazymatch e with ?u + _ => lb u | ?u - _ => lb u | _ => e end in lb lo) in
          match goal with X : ~ (?lo' <= x < ?hi') |- _ =>
            let b' := (let rec lb e := lazymatch e with ?u + _ => lb u | ?u - _ => lb u | _ => e end in lb lo') in
            constr_eq b b'; intros [L1 L2]; apply X; clear - L1 L2 G SPR CE CEIL MN1 MN2 DC; split; lia end end
      | match goal with X : _ |- _ => lazymatch type of X with ~ _ => idtac | _ <> _ => idtac end; clear - X G SPR CE CEIL MN1 MN2 DC; lia end ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac negs_clear := repeat match goal with X' : ~ _ |- _ => clear X' | X' : _ <> _ |- _ => clear X' end.
  Ltac wnlia := first [ assumption | negs_clear; lia
                     | match goal with X : _ |- _ => lazymatch type of X with ~ _ => idtac | _ <> _ => idtac end;
                         generalize X; negs_clear; intros ?; lia end ].
  Ltac wtac := apply W_shape; unfold kShadowOffset; wnlia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL KID NE NR AI sp kidx n md"] Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> ~ (0x187288 <= a < 0x5d72a8) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha Hd. pose proof GEO as G. geop. kung_all. apply AGW; [lia|]. wtac. Qed.
  #[using="WF0 MU CEIL KID NE NR AI sp kidx n md"] Lemma AGstat : forall a, rt_statics AL_pasan a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a H. unfold rt_statics in H. apply AGimg; revert H; offs; unfold kDepotNodesL1; lia. Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="WF0 NR AI kidx n md m Clg"] Lemma SEP6 : forall i b s, nth_error (big_maps A) i = Some (b, s) -> (i <> 0 /\ i <> 2 /\ i <> 3 /\ i <> 4 /\ i <> 7 /\ i <> 8)%nat ->
    apart b s (a_b6 A) kSpaceReserve /\ apart b s thr 4096 /\ apart b s n0 kDepotNodesBlock /\ apart b s f0 kStackStoreBlockBytes /\
    0 <= b /\ b + s <= 2^47.
  Proof.
    intros i b s Hn Hi. (first [ pose proof ((bm_nth_fixed A)) as dR_8; dand10 dR_8 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    unfold a_thr, a_nodes0, a_frames0 in *.
    split; [exact (bm_sep A i 0 _ _ _ _ WF0 Hn E0 ltac:(lia))|]. split; [exact (bm_sep A i 4 _ _ _ _ WF0 Hn E4 ltac:(lia))|].
    split; [exact (bm_sep A i 7 _ _ _ _ WF0 Hn E7 ltac:(lia))|]. split; [exact (bm_sep A i 8 _ _ _ _ WF0 Hn E8 ltac:(lia))|].
    destruct (wfM A WF0) as [_ BND]. (first [ pose proof ((BND b s (nth_error_In _ _ Hn))) as dR_9; dand3 dR_9 as B1 B2 B3 | destruct (BND b s (nth_error_In _ _ Hn)) as (B1 & B2 & B3) ]). lia.
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 AI kidx n md m Clg"] Lemma IN6 : a_b6 A <= sb /\ sb + kSpaceSize + 4096 <= a_b6 A + kSpaceReserve.
  Proof. (first [ pose proof ((sb_facts A WF0)) as dR_10; dand5 dR_10 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold kSpaceSize, kSpaceReserve. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL KID NE NR AI sp kidx n md"] Lemma AGmap : forall b s a, apart b s (a_b6 A) kSpaceReserve -> apart b s thr 4096 -> apart b s n0 kDepotNodesBlock ->
    apart b s f0 kStackStoreBlockBytes -> aobj b s -> b <= a < b + s ->
    v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros b s a S1 S2 S3 S4 HB Ha. pose proof GEO as G. pose proof IN6 as I6. pose proof alloc_ceiling_val as CE. aobj_lin1 HB. unfold apart in *. kung_all.
    apply AGW; [lia|]. wtac.
  Qed.
  Ltac aobj_of H := apply (proj1 (aobj_app_rangeA _ _)) in H.
  #[using="WF0 MU CEIL KID NE NR AI sp kidx n md"] Lemma AGctx : forall a, p_ctx (a_pl A) <= a < p_ctx (a_pl A) + 0x10000 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_11; dand7 dR_11 as _ _ _ _ _ E5 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & E5 & _) ]). (first [ pose proof ((SEP6 5%nat _ _ E5 ltac:(lia))) as dR_12; dand5 dR_12 as S1 S2 S3 S4 _ | destruct (SEP6 5%nat _ _ E5 ltac:(lia)) as (S1 & S2 & S3 & S4 & _) ]).
    (first [ pose proof ((place_facts A WF0)) as dR_13; dand3 dR_13 as _ Pctx _ | pose proof (place_facts A WF0) as (_ & Pctx & _) ]). cbv zeta in Pctx. destruct Pctx as (Pctx & _). aobj_of Pctx. unfold a_ctx in *.
    exact (AGmap _ _ a S1 S2 S3 S4 Pctx Ha).
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL KID NE NR AI sp md"] Lemma AGprim : forall a, sb <= a < sb + kSpaceSize + 4096 -> ~ (AB <= a < AB + class_size c) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha NC. pose proof GEO as G. pose proof IN6 as I6. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_25; dand10 dR_25 as E0 _ _ _ E4 _ _ E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & E4 & _ & _ & E7 & E8 & _) ]).
    pose proof (bm_sep A 4 0 _ _ _ _ WF0 E4 E0 ltac:(lia)) as T1. pose proof (bm_sep A 7 0 _ _ _ _ WF0 E7 E0 ltac:(lia)) as N1.
    pose proof (bm_sep A 8 0 _ _ _ _ WF0 E8 E0 ltac:(lia)) as F1. unfold a_thr, a_nodes0, a_frames0, a_b6 in *.
    pose proof (Z.le_min_l n 4096). unfold apart in *. kung_all. apply AGW; [lia|]. wtac.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL KID NE NR AI sp kidx md"] Lemma AGthr : forall a, thr <= a < thr + 4096 ->
    ~ (thr + 208 + 80 * c <= a < thr + 208 + 80 * c + 4) -> ~ (thr + 2784 <= a < thr + 2792) -> ~ (thr + 2800 <= a < thr + 2824) ->
    ~ (thr + 2912 + 8 * c <= a < thr + 2912 + 8 * c + 8) -> a <> thr + 3168 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha X1 X2 X3 X4 X5. pose proof GEO as G. geop. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((hit_sep A m md AI)) as dR_27; dand8 dR_27 as T6 _ _ _ _ TN TF _ | destruct (hit_sep A m md AI) as (T6 & _ & _ & _ & _ & TN & TF & _) ]). unfold apart in T6, TN, TF. kung_all. apply AGW; [lia|]. wtac.
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="NR"] Lemma CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Ltac trim := repeat match goal with H : _ /\ _ /\ _ |- _ => clear H | H : Forall _ _ |- _ => clear H | H : arepr _ _ _ _ _ |- _ => clear H end.
  Ltac by_stat := apply AGstat; trim; unfold rt_statics; offs; lia.
  Ltac by_thr := pose proof CR as CR__; apply AGthr; trim; unfold a_thr; offs; lia.
  Ltac by_ctx := apply AGctx; trim; unfold a_ctx; offs; lia.
  Ltac leaf H AG :=
    lazymatch type of H with
    | u64_at _ _ _ _ => eapply u64_at_agree; [exact H|]; intros i__ Hi__; AG
    | u32_at _ _ _ _ => eapply u32_at_agree; [exact H|]; intros i__ Hi__; AG
    | u16_at _ _ _ _ => eapply u16_at_agree; [exact H|]; intros i__ Hi__; AG
    | u8_at _ _ _ _ => eapply u8_at_agree;  [exact H|]; AG
    | fill_at _ _ _ _ _ => eapply fill_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    | junk_at _ _ _ _ => eapply junk_at_agree; [exact H|]; intros i__ Hi__; offs_h Hi__; AG
    end.
  Ltac walk H AG :=
    lazymatch goal with
    | |- _ /\ _ => let H1 := fresh "L" in let H2 := fresh "L" in destruct H as [H1 H2]; split; [walk H1 AG | walk H2 AG]
    | |- _ => leaf H AG
    end.


  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="NE NR AI n md m Clg"] Lemma CI : a_cache_inited A = true. Proof. exact (hit_ci A m md n AI NR NE). Qed.
  #[using="WF0 CEIL KID NE NR AI sp md m Clg"] Lemma KB : 0 <= kidx < carved_count A c. Proof. pose proof GEO; lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)


  Local Notation lm' := (<[ hit_user A n kidx := LI (ChP (CP (class_of n) kidx)) n ]> (a_livemap A)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)


  (* [comment removed for export] *)

  (* [comment removed for export] *)


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)


  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Cells.
  Variables (md0 : mem) (ks : list word) (b1' id : Z).
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis KSF : firstn (length ks') ks = map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) ks'.
  Hypothesis P_unw : rw_cells rsegs v' (thr + off_th_unwinding) [C1 (Z_to_bv 8 0)].
  Hypothesis P_pc : rw_cells rsegs v' (thr + 208 + 80 * c)
     [C4 (Z_to_bv 64 (Z.of_nat (length ks') - 1)); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  Hypothesis B1R : 0 <= b1' < 256.
  Hypothesis B1M : Z.land b1' 0x7f = kHdrByte1Malloc.
  Hypothesis IDR : 0 <= id < 2^32.
  Hypothesis P_hdr : rw_cells rsegs v' (AB + rz_size n + -16)
     [C1 (Z_to_bv 8 CHUNK_ALLOCATED); C1 (Z_to_bv 8 b1'); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
  Hypothesis P_lch : rz_size n <> 16 -> rw_cells rsegs v' AB [C8 (Z_to_bv 64 kAllocBegMagic); C8 (Z_to_bv 64 (AB + rz_size n + -16))].
  Hypothesis P_shz : bytes_at rsegs v' (AB / 8 + rz_size n / 8 + kShadowOffset) (repeat (Z_to_bv 8 0) (Z.to_nat (n / 8))).
  Hypothesis P_she : n mod 8 <> 0 -> rw_cells rsegs v' (AB / 8 + rz_size n / 8 + n / 8 + kShadowOffset) [C1 (Z_to_bv 8 (n mod 8))].
  Hypothesis P_dr : depot_repL AL_pasan rsegs (fst (depot_putC D key)) n0 f0 md0.
  Hypothesis P_mu2 : munch W2 md0 v'.


  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  End Cells.
End ReprPost.
End AMal5j7.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMal9l1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMaly5g.AMal5j7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Notation wz z := (Z_to_bv 64 z) (only parsing).
#[local] Notation WF := (WF AL_pasan).   (* [comment removed for export] *)
Ltac kung_all := unfold kHighMemBeg, kDepotNodesBlock, kStackStoreBlockBytes, kShadowOffset, kRegionSize, kSpaceSize, kFreeArrayOffset,
                        kHighShadowMapBeg, kSpaceReserve, kMaxSize, kLowShadowMapBeg, kHighShadowMapSize in *.   (* [comment removed for export] *)

Lemma pa_wx : wx_segs_nowrap rsegs.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma b1_final_ok : forall x, 0 <= x ->
  0 <= Z.lor (Z.land (b1_mid x) 243) 0 < 256 /\ Z.land (Z.lor (Z.land (b1_mid x) 243) 0) 0x7f = kHdrByte1Malloc.
Proof.
  intros x Hx. rewrite Z.lor_0_r. unfold kHdrByte1Malloc.
  assert (E : Z.land (Z.land (b1_mid x) 243) 0x7f = 0x11).
  { apply Z.bits_inj'. intros i Hi. unfold b1_mid.
    rewrite !Z.land_spec, !Z.lor_spec, !Z.land_spec, !Z.lor_spec, !Z.land_spec.
    destruct (Z_lt_dec i 8) as [L|L].
    - destruct (Z.testbit x i) eqn:Tx;
      (assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia);
      destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; reflexivity.
    - rewrite (Z.bits_above_log2 1 i) by (cbn; lia). rewrite (Z.bits_above_log2 143 i) by (cbn; lia).
      rewrite (Z.bits_above_log2 16 i) by (cbn; lia). rewrite (Z.bits_above_log2 243 i) by (cbn; lia).
      rewrite (Z.bits_above_log2 127 i) by (cbn; lia). rewrite (Z.bits_above_log2 17 i) by (cbn; lia).
      rewrite ?andb_false_r, ?orb_false_r, ?andb_false_r. reflexivity. }
  split; [| exact E].
  pose proof (b1_mid_range x Hx) as R.
  split; [apply Z.land_nonneg; right; lia|].
  destruct (Z.eq_dec (Z.land (b1_mid x) 243) 0) as [->|NZ]; [lia|].
  assert (NN : 0 <= Z.land (b1_mid x) 243) by (apply Z.land_nonneg; right; lia).
  pose proof (Z.log2_land (b1_mid x) 243 ltac:(lia) ltac:(lia)) as LG. change (Z.log2 243) with 7 in LG.
  apply (proj2 (Z.log2_lt_pow2 (Z.land (b1_mid x) 243) 8 ltac:(lia))). lia.
Qed.

(* [comment removed for export] *)
Lemma wmono_NN : forall (v v' : mem) a, wmono rsegs v v' -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> 0 <= a < 2^64 ->
  v (wz a) <> None -> v' (wz a) <> None.
Proof.
  intros v v' a WM Ha Hr Hv. specialize (WM (wz a)). unfold wview in WM.
  rewrite unsigned_lit in WM by lia. rewrite (pa_find_segment_none a 1 ltac:(lia) Ha) in WM.
  destruct (v (wz a)); [| congruence]. destruct (v' (wz a)); [congruence|]. exfalso. apply WM; [discriminate| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Post.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model) (n kidx : Z) (key : list Z) (sp : word) (v' : mem).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Local Notation c := (class_of n).
  Local Notation ks' := (pk_chunks (a_cache A (class_of n))).
  Hypothesis NE : ks' <> [].
  Hypothesis KID : kidx = nth (length ks' - 1) ks' 0.
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned sp - ASTK.
  Local Notation v := (aview_of (pa_hull A) m).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation AB := (chunk_addr (a_sb A) (class_of n) kidx).
  Local Notation u := (hit_user A n kidx).
  Local Notation n0 := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation W := (malloc_hit_W sp thr (class_of n) AB n (AB / 8) (rz_size n / 8) (n / 8) (n mod 8) n0 f0).
  Local Notation shU := (AB / 8 + rz_size n / 8 + kShadowOffset).
  Local Notation A' := (hitA A n kidx key).
  Hypothesis MU : munch W v v'.
  Hypothesis WMv : wmono rsegs v v'.
  Hypothesis SM : mapped v (bv_unsigned sp - ASTK) ASTK.

  Let WF0 : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Post.

