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
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Frame Step Arr Tac Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Ledger Hull Restrict EvtAcct.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AMalq4j AMalghy.   (* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts ARtS4t2 AMallocA AMallocH AMalmys AMal9l1 AMaldga AMalkbe.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
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

(* [comment removed for export] *)
Lemma ref_reg_mu : forall reg c k c', rg_mapped_user (ref_reg reg c k c') = rg_mapped_user (reg c').
Proof. intros. unfold ref_reg. destruct (Z.eqb_spec c' c) as [->|]; reflexivity. Qed.
Lemma ref_reg_au : forall reg c k c', rg_allocated_user (ref_reg reg c k c') = rg_allocated_user (reg c').
Proof. intros. unfold ref_reg. destruct (Z.eqb_spec c' c) as [->|]; reflexivity. Qed.
Lemma ref_reg_mfa : forall reg c k c', rg_mapped_fa (ref_reg reg c k c') = rg_mapped_fa (reg c').
Proof. intros. unfold ref_reg. destruct (Z.eqb_spec c' c) as [->|]; reflexivity. Qed.
Lemma nth_error_firstn_Some : forall {X} (l : list X) m i x, nth_error (firstn m l) i = Some x -> nth_error l i = Some x.
Proof.
  intros X l. induction l as [|y l IH]; intros [|m] [|i] x E; cbn in E; try discriminate; [exact E|]. cbn. exact (IH m i x E).
Qed.

Section ReprPost.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (A : AState) (m : mem) (md : Model) (n : Z) (key : list Z) (spa : word) (v' : mem).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis NR : 1 <= n <= kMaxPrimaryUser.
  Local Notation c := (class_of n).
  Local Notation fr := (rg_free (a_reg A (class_of n))).
  Local Notation nf := (Z.of_nat (length (rg_free (a_reg A (class_of n))))).
  Local Notation KK := (refill_count (class_of n)).
  Local Notation kidx := (refK A n).
  Local Notation fetched := (ref_fetched (rg_free (a_reg A (class_of n))) (refill_count (class_of n))).
  Local Notation ri := (a_ri A).
  (* [comment removed for export] *)
  Hypothesis CI : a_cache_inited A = true.
  Hypothesis EMP : pk_chunks (a_cache A (class_of n)) = [].
  Hypothesis ENOUGH : refill_count (class_of n) <= Z.of_nat (length (rg_free (a_reg A (class_of n)))).
  Hypothesis CEIL : alloc_ceiling <= bv_unsigned spa - 1024.
  Local Notation v := (aview_of (pa_hull A) m).
  Local Notation thr := (p_thr (a_pl A)).
  Local Notation sb := (a_sb A).
  Local Notation AB := (chunk_addr (a_sb A) (class_of n) kidx).
  Local Notation u := (hit_user A n kidx).
  Local Notation n0 := (p_nodes0 (a_pl A)).
  Local Notation f0 := (p_frames0 (a_pl A)).
  Local Notation D := (a_depot A).
  Local Notation W := (alloc_refill_W spa thr (class_of n) AB n (AB / 8) (rz_size n / 8) (n / 8) (n mod 8) n0 f0 (a_ri A)).
  Local Notation W2 := (alloc_hit_W2 spa thr (class_of n) AB n (AB / 8) (rz_size n / 8) (n / 8) (n mod 8)).
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
  #[using="ENOUGH NR AI md m Clg"] Lemma KIN : In kidx fr. Proof. unfold refK. exact (proj1 (ref_kidx A m md n AI NR ENOUGH)). Qed.
  #[using="ENOUGH NR"] Lemma RK : max_count c = 2 * KK /\ 1 <= KK <= 8 /\ KK <= nf. Proof. pose proof (ref_k A n NR). pose proof ENOUGH. lia. Qed.
  #[using="ENOUGH NR"] Lemma FETL : length fetched = Z.to_nat KK. Proof. apply ref_fetched_length. pose proof RK. lia. Qed.
  #[using="ENOUGH NR"] Lemma FET : In kidx fetched /\ kidx = nth (length fetched - 1) fetched 0 /\ fetched <> [].
  Proof. exact (rf_kidx_fetched A n NR ENOUGH). Qed.
  #[using="NR AI md m Clg"] Lemma NODUP : NoDup (ref_rest fr KK) /\ NoDup fetched /\ (forall x, In x (ref_rest fr KK) -> In x fetched -> False).
  Proof. exact (ref_nodup fr KK (rf_ND A m md n AI NR)). Qed.
  #[using="ENOUGH NR AI md m Clg"] Lemma NLAST : ~ In kidx (removelast fetched).
  Proof.
    (first [ dand3 NODUP as _ NDf _ | destruct NODUP as (_ & NDf & _) ]). (first [ dand3 FET as _ KL FNE | destruct FET as (_ & KL & FNE) ]). destruct (removelast_nodup fetched NDf) as [_ NL].
    rewrite KL at 1. exact (NL FNE).
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 CEIL ENOUGH NR AI md m"] Lemma GEO :
    4096 <= thr /\ thr + 4096 <= alloc_ceiling /\ kHighMemBeg <= sb /\ sb + 2^37 + 4096 <= alloc_ceiling /\
    region_beg sb c <= AB /\ AB + class_size c <= region_beg sb c + rg_allocated_user (a_reg A c) /\
    rg_allocated_user (a_reg A c) <= rg_mapped_user (a_reg A c) /\ region_beg sb c + rg_mapped_user (a_reg A c) <= region_beg sb c + kFreeArrayOffset /\
    sb <= region_beg sb c /\ region_beg sb c + kRegionSize <= sb + kSpaceSize /\
    rz_size n + n <= class_size c /\ 16 <= rz_size n /\ rz_size n = 8 * (rz_size n / 8) /\ AB = 8 * (AB / 8) /\ 32 <= class_size c /\
    class_size c = 8 * (class_size c / 8) /\ n = 8 * (n / 8) + n mod 8 /\ 0 <= n mod 8 < 8 /\
    4096 <= n0 /\ n0 + kDepotNodesBlock <= alloc_ceiling /\ 4096 <= f0 /\ f0 + kStackStoreBlockBytes <= alloc_ceiling /\
    alloc_ceiling <= bv_unsigned spa - 1024 /\ bv_unsigned spa < 2^64 /\ 1 <= c <= 30 /\ 0 <= kidx < carved_count A c /\
    0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000 /\
    ri = sb + kSpaceSize.   (* [comment removed for export] *)
  Proof.
    (first [ pose proof ((free_geom A m md n kidx AI NR KIN)) as dR_3; dand15 dR_3 as _ M32 Q8 S1 S2 R8 HB HB2 R1 R2 FIT _ CR KB _ | destruct (free_geom A m md n kidx AI NR KIN) as (_ & M32 & Q8 & S1 & S2 & R8 & HB & HB2 & R1 & R2 & FIT & _ & CR & KB & _) ]).
    pose proof (proj1 (ref_ri A m md n AI)) as RIE.
    (first [ pose proof ((hit_class n NR)) as dR_4; dand5 dR_4 as _ _ _ CSR CM32 | destruct (hit_class n NR) as (_ & _ & _ & CSR & CM32) ]).
    (first [ pose proof ((carved_chunk_bounds A c kidx WF0 CR KB)) as dR_5; dand3 dR_5 as B1 B2 _ | pose proof (carved_chunk_bounds A c kidx WF0 CR KB) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c WF0 CR) as RB. cbv zeta in *.
    (first [ pose proof ((hit_sep A m md AI)) as dR_6; dand13 dR_6 as _ _ _ _ _ _ _ _ _ N1 N2 F1 F2 | destruct (hit_sep A m md AI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & N2 & F1 & F2) ]). apply aobj_facts in N1. apply aobj_facts in F1.
    pose proof (place_facts A WF0) as (Pthr & _). cbv zeta in Pthr. (first [ dand3 Pthr as Pthr PthrC PthrM | destruct Pthr as (Pthr & PthrC & PthrM) ]). apply app_facts in Pthr.
    pose proof alloc_ceiling_val as CE. pose proof (rz_size_range n). (first [ pose proof ((sb_facts A WF0)) as dR_8; dand5 dR_8 as _ _ _ _ SCE | pose proof (sb_facts A WF0) as (_ & _ & _ & _ & SCE) ]). unfold kSpaceSize in SCE.
    pose proof (Z_div_mod_eq_full (class_size c) 8). pose proof (mod0_down (class_size c) 32 8 ltac:(exists 4; reflexivity) CM32).
    pose proof (Z_div_mod_eq_full n 8). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
    pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; try assumption; try lia.
  Qed.

  #[using="AI md m"] Lemma GEOP : aobj thr 4096 /\ aobj n0 kDepotNodesBlock /\ aobj f0 kStackStoreBlockBytes.
  Proof.
    (first [ pose proof ((hit_sep A m md AI)) as dR_9; dand13 dR_9 as _ _ _ _ _ _ _ _ _ N1 _ F1 _ | destruct (hit_sep A m md AI) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & N1 & _ & F1 & _) ]).
    destruct (hit_place A m md AI) as (T1 & _). exact (conj T1 (conj N1 F1)).
  Qed.
  Ltac geop := let Gt := fresh "Gt" in let Gn := fresh "Gn" in let Gf := fresh "Gf" in
    (first [ pose proof (GEOP) as dR_10; dand3 dR_10 as Gt Gn Gf | pose proof GEOP as (Gt & Gn & Gf) ]); aobj_lin1 Gt; aobj_lin1 Gn; aobj_lin1 Gf.

  (* [comment removed for export] *)
  #[using="MU"] Lemma AGW : forall a, 0 <= a < 2^64 -> outside W a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha Ho. apply MU. rewrite unsigned_lit by lia. exact Ho. Qed.

  (* [comment removed for export] *)
  #[using="WF0 CEIL ENOUGH NR AI md m Clg"] Lemma W_shape : forall a,
    ~ (bv_unsigned spa - 1024 <= a < bv_unsigned spa) ->
    ~ (thr + 208 + 80 * c <= a < thr + 208 + 80 * c + 80) -> ~ (thr + 2784 <= a < thr + 2792) ->
    ~ (AB <= a < AB + rz_size n + Z.min n 4096) ->
    ~ (0x187288 <= a < 0x5d72a8) -> ~ (n0 <= a < n0 + 0x100000) -> ~ (f0 <= a < f0 + 0x800000) ->
    ~ (shU <= a < shU + (n + 7) / 8) ->
    ~ (thr + 2800 <= a < thr + 2824) -> ~ (thr + 2912 + 8 * c <= a < thr + 2912 + 8 * c + 8) ->
    ~ (ri + 128 * c <= a < ri + 128 * c + 8) -> ~ (ri + 128 * c + 16 <= a < ri + 128 * c + 24) ->
    ~ (ri + 128 * c + 72 <= a < ri + 128 * c + 80) ->
    outside W a.
  Proof.
    intros a X1 X4 X5 X6 X7 X8 X9 X10 X11 X12 X13 X14 X15. pose proof GEO as G.
    pose proof (zr_word spa) as SPR; unfold inr64 in SPR. pose proof alloc_ceiling_val as CE.
    unfold alloc_refill_W. cbn [app outside].
    pose proof (Z.le_min_l n 4096) as MN1. pose proof (Z.min_glb n 4096 1 ltac:(lia) ltac:(lia)) as MN2. pose proof (div8_ceil n ltac:(lia)) as DC.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ assumption
      | lazymatch goal with |- ~ (?lo <= _ < _) =>
          match goal with X : ~ (?lo' <= _ < _) |- _ => tf_same_base lo lo'; clear - X G SPR CE CEIL MN1 MN2 DC; lia end end
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
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGlow : forall a, kLowShadowMapBeg <= a < kHighShadowMapBeg -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha. pose proof GEO as G. geop. unfold kLowShadowMapBeg, kHighShadowMapBeg in Ha. kung_all. apply AGW; [lia|]. wtac. Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> ~ (0x187288 <= a < 0x5d72a8) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a Ha Hd. pose proof GEO as G. geop. kung_all. apply AGW; [lia|]. wtac. Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGstat : forall a, rt_statics AL_pasan a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a H. unfold rt_statics in H. apply AGimg; revert H; offs; unfold kDepotNodesL1; lia. Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGshared : forall a, cl_shared LPA a -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof. intros a H. cbn [cl_shared LPA] in H. unfold pa_shared in H. apply AGimg; lia. Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGconst : forall cst a, In cst (cl_consts LPA) -> fst cst <= a < fst cst + Z.of_nat (length (snd cst)) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros cst a Hin Ha. cbn [cl_consts LPA] in Hin.
    pose proof pa_consts_nodepot as OK. rewrite forallb_forall in OK. specialize (OK cst Hin). unfold const_nodepot in OK.
    apply orb_true_iff in OK. rewrite !Z.leb_le in OK.
    destruct (pa_consts_where cst a Hin Ha) as [S|[S|S]].
    - apply AGimg; [unfold pa_shared in S; lia| lia].
    - unfold pa_image_shadow, sh in S. apply AGlow; unfold kLowShadowMapBeg, kHighShadowMapBeg, kShadowOffset in *.
      replace (0x10000 / 8) with 8192 in S by reflexivity. replace (0x60a000 / 8) with 791552 in S by reflexivity. lia.
    - pose proof (pa_static_low a S). apply AGimg; [unfold pa_static in S; lia| lia].
  Qed.

  (* [comment removed for export] *)
  #[using="WF0 NR AI n md m Clg"] Lemma SEP6 : forall i b s, nth_error (big_maps A) i = Some (b, s) -> (i <> 0 /\ i <> 2 /\ i <> 3 /\ i <> 4 /\ i <> 7 /\ i <> 8)%nat ->
    apart b s (a_b6 A) kSpaceReserve /\ apart b s thr 4096 /\ apart b s n0 kDepotNodesBlock /\ apart b s f0 kStackStoreBlockBytes /\
    0 <= b /\ b + s <= 2^47.
  Proof.
    intros i b s Hn Hi. (first [ pose proof ((bm_nth_fixed A)) as dR_11; dand10 dR_11 as E0 E1 E2 E3 E4 E5 E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & _) ]).
    unfold a_thr, a_nodes0, a_frames0 in *.
    split; [exact (bm_sep A i 0 _ _ _ _ WF0 Hn E0 ltac:(lia))|]. split; [exact (bm_sep A i 4 _ _ _ _ WF0 Hn E4 ltac:(lia))|].
    split; [exact (bm_sep A i 7 _ _ _ _ WF0 Hn E7 ltac:(lia))|]. split; [exact (bm_sep A i 8 _ _ _ _ WF0 Hn E8 ltac:(lia))|].
    destruct (wfM A WF0) as [_ BND]. (first [ pose proof ((BND b s (nth_error_In _ _ Hn))) as dR_12; dand3 dR_12 as B1 B2 B3 | destruct (BND b s (nth_error_In _ _ Hn)) as (B1 & B2 & B3) ]). lia.
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 AI n md m Clg"] Lemma IN6 : a_b6 A <= sb /\ sb + kSpaceSize + 4096 <= a_b6 A + kSpaceReserve.
  Proof. (first [ pose proof ((sb_facts A WF0)) as dR_13; dand5 dR_13 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold kSpaceSize, kSpaceReserve. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGmap : forall b s a, apart b s (a_b6 A) kSpaceReserve -> apart b s thr 4096 -> apart b s n0 kDepotNodesBlock ->
    apart b s f0 kStackStoreBlockBytes -> aobj b s -> b <= a < b + s ->
    v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros b s a S1 S2 S3 S4 HB Ha. pose proof GEO as G. pose proof IN6 as I6. pose proof alloc_ceiling_val as CE. aobj_lin1 HB. unfold apart in *. kung_all.
    apply AGW; [lia|]. wtac.
  Qed.
  Ltac aobj_of H := apply (proj1 (aobj_app_rangeA _ _)) in H.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGctx : forall a, p_ctx (a_pl A) <= a < p_ctx (a_pl A) + 0x10000 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_14; dand7 dR_14 as _ _ _ _ _ E5 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & E5 & _) ]). (first [ pose proof ((SEP6 5%nat _ _ E5 ltac:(lia))) as dR_15; dand5 dR_15 as S1 S2 S3 S4 _ | destruct (SEP6 5%nat _ _ E5 ltac:(lia)) as (S1 & S2 & S3 & S4 & _) ]).
    (first [ pose proof ((place_facts A WF0)) as dR_16; dand3 dR_16 as _ Pctx _ | pose proof (place_facts A WF0) as (_ & Pctx & _) ]). cbv zeta in Pctx. destruct Pctx as (Pctx & _). aobj_of Pctx. unfold a_ctx in *.
    exact (AGmap _ _ a S1 S2 S3 S4 Pctx Ha).
  Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGdtls : forall a, p_dtls (a_pl A) <= a < p_dtls (a_pl A) + 4096 -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_17; dand15 dR_17 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ E14 | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & E14) ]). (first [ pose proof ((SEP6 14%nat _ _ E14 ltac:(lia))) as dR_18; dand5 dR_18 as S1 S2 S3 S4 _ | destruct (SEP6 14%nat _ _ E14 ltac:(lia)) as (S1 & S2 & S3 & S4 & _) ]).
    (first [ pose proof ((place_facts A WF0)) as dR_19; dand12 dR_19 as _ _ _ _ _ _ _ _ _ _ Pdtls _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Pdtls & _) ]). cbv zeta in Pdtls. destruct Pdtls as (Pdtls & _). aobj_of Pdtls.
    exact (AGmap _ _ a S1 S2 S3 S4 Pdtls Ha).
  Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGfs : forall a, p_fs (a_pl A) <= a < p_fs (a_pl A) + kFakeStackBytes -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_20; dand8 dR_20 as _ _ _ _ _ _ E6 _ | pose proof (bm_nth_fixed A) as (_ & _ & _ & _ & _ & _ & E6 & _) ]). (first [ pose proof ((SEP6 6%nat _ _ E6 ltac:(lia))) as dR_21; dand5 dR_21 as S1 S2 S3 S4 _ | destruct (SEP6 6%nat _ _ E6 ltac:(lia)) as (S1 & S2 & S3 & S4 & _) ]).
    (first [ pose proof ((place_fs A WF0)) as dR_22; dand3 dR_22 as F1 F2 _ | pose proof (place_fs A WF0) as (F1 & F2 & _) ]). aobj_of F1. unfold a_fs in *.
    exact (AGmap _ _ a S1 S2 S3 S4 F1 Ha).
  Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGpa : forall a, p_pa (a_pl A) <= a < p_pa (a_pl A) + 8 * kChunksBlockCount -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha. (first [ pose proof ((bm_nth_fixed A)) as dR_23; dand3 dR_23 as _ E1 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _) ]). (first [ pose proof ((SEP6 1%nat _ _ E1 ltac:(lia))) as dR_24; dand5 dR_24 as S1 S2 S3 S4 _ | destruct (SEP6 1%nat _ _ E1 ltac:(lia)) as (S1 & S2 & S3 & S4 & _) ]).
    (first [ pose proof ((place_facts A WF0)) as dR_25; dand13 dR_25 as _ _ _ _ _ _ _ _ _ _ _ Ppa _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ppa & _) ]). cbv zeta in Ppa. destruct Ppa as (Ppa & _). aobj_of Ppa.
    unfold a_pa in *.
    apply (AGmap _ _ a S1 S2 S3 S4 Ppa). unfold kChunksBlockCount, kPtrArrayReserve in *. lia.
  Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGsec : forall sc a, In sc (sr_chunks (a_sec A)) -> cs_map sc <= a < cs_map sc + map_size (cs_n sc) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros sc a Hin Ha. destruct (In_nth_error' _ _ Hin) as [j Hj]. pose proof (bm_nth_sec A j sc Hj) as Ej.
    (first [ pose proof ((SEP6 (15 + j)%nat _ _ Ej ltac:(lia))) as dR_26; dand5 dR_26 as S1 S2 S3 S4 _ | destruct (SEP6 (15 + j)%nat _ _ Ej ltac:(lia)) as (S1 & S2 & S3 & S4 & _) ]).
    (first [ pose proof ((sec_chunk_bounds A sc WF0 Hin)) as dR_27; dand5 dR_27 as _ _ B3 B4 _ | pose proof (sec_chunk_bounds A sc WF0 Hin) as (_ & _ & B3 & B4 & _) ]). aobj_of B3.
    exact (AGmap _ _ a S1 S2 S3 S4 B3 Ha).
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL ENOUGH NR AI spa md"] Lemma AGprim : forall a, sb <= a < sb + kSpaceSize -> ~ (AB <= a < AB + class_size c) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha NC. pose proof GEO as G. pose proof IN6 as I6. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_28; dand10 dR_28 as E0 _ _ _ E4 _ _ E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & E4 & _ & _ & E7 & E8 & _) ]).
    pose proof (bm_sep A 4 0 _ _ _ _ WF0 E4 E0 ltac:(lia)) as T1. pose proof (bm_sep A 7 0 _ _ _ _ WF0 E7 E0 ltac:(lia)) as N1.
    pose proof (bm_sep A 8 0 _ _ _ _ WF0 E8 E0 ltac:(lia)) as F1. unfold a_thr, a_nodes0, a_frames0, a_b6 in *.
    pose proof (Z.le_min_l n 4096). unfold apart in *. kung_all. apply AGW; [lia|]. wtac.
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL ENOUGH NR AI spa md"] Lemma AGri : forall a, ri <= a < ri + 4096 -> ~ (ri + 128 * c <= a < ri + 128 * c + 8) ->
    ~ (ri + 128 * c + 16 <= a < ri + 128 * c + 24) -> ~ (ri + 128 * c + 72 <= a < ri + 128 * c + 80) ->
    v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha Y1 Y2 Y3. pose proof GEO as G. pose proof IN6 as I6. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_29; dand10 dR_29 as E0 _ _ _ E4 _ _ E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & _ & _ & _ & E4 & _ & _ & E7 & E8 & _) ]).
    pose proof (bm_sep A 4 0 _ _ _ _ WF0 E4 E0 ltac:(lia)) as T1. pose proof (bm_sep A 7 0 _ _ _ _ WF0 E7 E0 ltac:(lia)) as N1.
    pose proof (bm_sep A 8 0 _ _ _ _ WF0 E8 E0 ltac:(lia)) as F1. unfold a_thr, a_nodes0, a_frames0, a_b6 in *.
    pose proof (Z.le_min_l n 4096). unfold apart in *. kung_all. apply AGW; [lia|]. wtac.
  Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa n md"] Lemma AGfa : forall c' a, 1 <= c' <= 30 -> free_array_beg sb c' <= a < free_array_beg sb c' + rg_mapped_fa (a_reg A c') -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros c' a Hc Ha. pose proof GEO as G. pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in RB. unfold free_array_beg in Ha.
    apply AGprim; [kung_all; lia|].
    destruct (Z.eq_dec c' c) as [->|NEQ]; [kung_all; lia|].
    destruct (regions_disjoint sb c' c NEQ ltac:(lia) ltac:(lia)); kung_all; lia.
  Qed.
  #[using="WF0 MU CEIL ENOUGH NR AI spa md"] Lemma AGchunk : forall c' k a, 1 <= c' <= 30 -> 0 <= k < carved_count A c' -> (c' <> c \/ k <> kidx) ->
    chunk_addr sb c' k <= a < chunk_addr sb c' k + class_size c' -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros c' k a Hc Hk NEQ Ha. pose proof GEO as G. (first [ pose proof ((carved_chunk_bounds A c' k WF0 Hc Hk)) as dR_30; dand3 dR_30 as B1 B2 _ | pose proof (carved_chunk_bounds A c' k WF0 Hc Hk) as (B1 & B2 & _) ]).
    pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in *.
    apply AGprim; [kung_all; lia|].
    destruct (Z.eq_dec c' c) as [->|NC].
    - destruct NEQ as [X|NK]; [congruence|]. destruct (carved_chunks_disjoint sb c k kidx Hc ltac:(lia) ltac:(lia) NK); lia.
    - destruct (regions_disjoint sb c' c NC ltac:(lia) ltac:(lia)); kung_all; lia.
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL ENOUGH NR AI spa md"] Lemma AGthr : forall a, thr <= a < thr + 4096 ->
    ~ (thr + 208 + 80 * c <= a < thr + 208 + 80 * c + 80) -> ~ (thr + 2784 <= a < thr + 2792) -> ~ (thr + 2800 <= a < thr + 2824) ->
    ~ (thr + 2912 + 8 * c <= a < thr + 2912 + 8 * c + 8) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a Ha X1 X2 X3 X4. pose proof GEO as G. geop. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((hit_sep A m md AI)) as dR_31; dand8 dR_31 as T6 _ _ _ _ TN TF _ | destruct (hit_sep A m md AI) as (T6 & _ & _ & _ & _ & TN & TF & _) ]). destruct (ref_sep A m md n AI) as (TR & _). unfold apart in T6, TN, TF, TR. kung_all. apply AGW; [lia|]. wtac.
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 MU CEIL ENOUGH NR AI spa md"] Lemma AGhs : forall a, heap_shadow A a -> ~ (shU <= a < shU + (n + 7) / 8) -> v' (Z_to_bv 64 a) = v (Z_to_bv 64 a).
  Proof.
    intros a HS X. pose proof GEO as G. geop. pose proof alloc_ceiling_val as CE. pose proof (heap_shadow_range A a WF0 HS) as HR. unfold in_shadow_maps, kLowShadowMapBeg, kHighShadowMapSize in HR. kung_all. apply AGW; [lia|]. wtac.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="n A"] Lemma TPV : bv_unsigned (cl_tp LPA) = 0x5e83d8.
  Proof. cbn [cl_tp LPA]. rewrite unsigned_lit by lia. reflexivity. Qed.
  #[using="NR"] Lemma CR : 1 <= c <= 30. Proof. exact (proj1 (hit_class n NR)). Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="NN NR n"] Lemma mapped_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> a + k <= 2^64 -> mapped v a k -> mapped v' a k.
  Proof. intros a k H0 H1 H2 M. eapply mapped_mono; [exact M|]. intros i Hi. apply NN; lia. Qed.
  #[using="NN NR n"] Lemma junk_N : forall a k, 0 <= a -> (a + k <= 0x10000 \/ 0x60a000 <= a) -> junk_at rsegs v a k -> junk_at rsegs v' a k.
  Proof.
    (intros a k H0 H1; (first [ intro dR_123; dex1 dR_123 as bs; destruct dR_123 as [L B] | intro dR_123; dand3 dR_123 as bs L B | intros (bs & L & B) ])). pose proof (bytes_at_bound _ _ _ _ B) as BB. rewrite L in BB.
    apply junk_at_of_mapped; [lia| lia| lia|]. apply mapped_N; [lia| lia| lia|]. rewrite <- L. eapply bytes_at_mapped_gen; [exact B| lia| lia].
  Qed.

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




  #[using="R WF0 NN MU CEIL ENOUGH NR AI spa n md m Clg"] Lemma sec_P : sec_repr_ LPA AL_pasan (a_pl A) (a_sec A) v'.
  Proof.
    pose proof (ar_sec _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_facts A WF0)) as dR_32; dand13 dR_32 as _ _ _ _ _ _ _ _ _ _ _ Ppa _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Ppa & _) ]). cbv zeta in Ppa.
    (first [ dand3 Ppa as Ppa1 Ppa2 Ppa3 | destruct Ppa as (Ppa1 & Ppa2 & Ppa3) ]). apply app_facts in Ppa1.
    (first [ pose proof ((wfS A WF0)) as dR_34; dand4 dR_34 as _ LEN RES _ | destruct (wfS A WF0) as (_ & LEN & RES & _) ]). unfold kChunksBlockCount in RES. unfold sec_repr_ in *. cbv zeta in *.
    (first [ dand7 C as X1 X2 J1 J2 J3 CH M | destruct C as (X1 & X2 & J1 & J2 & J3 & CH & M) ]).
    split; [leaf X1 by_stat|]. split; [leaf X2 by_stat|]. split; [leaf J1 by_stat|]. split; [leaf J2 by_stat|]. split; [leaf J3 by_stat|]. split.
    - intros i sc E. destruct (CH i sc E) as [X Y]. pose proof (nth_error_In _ _ E) as Hin.
      assert (Z.of_nat i < Z.of_nat (length (sr_chunks (a_sec A)))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      split.
      + leaf X ltac:(apply AGpa; unfold a_pa; offs; lia).
      + eapply rw_cells_agree; [exact Y|]. rewrite sec_hdr_size. intros j Hj. apply (AGsec sc); [exact Hin|].
        (first [ pose proof ((sec_chunk_bounds A sc WF0 Hin)) as dR_36; dand5 dR_36 as B1 _ B3 B4 B5 | pose proof (sec_chunk_bounds A sc WF0 Hin) as (B1 & _ & B3 & B4 & B5) ]). pose proof (needed_size2_secondary (cs_n sc) ltac:(lia)).
        pose proof (rounded_size_ge (cs_n sc)). offs. unfold kPageSize in *. lia.
    - apply mapped_N; [clear - Ppa1; lia| clear - Ppa1 RES LEN; ALogic2.kun; lia| clear - Ppa1 Ppa2 RES LEN CE; ALogic2.kun; lia| exact M].
  Qed.

  #[using="R WF0 MU CEIL ENOUGH NR AI spa n md m Clg"] Lemma ia_P : ia_repr_ LPA AL_pasan (a_ia_inited A) v'.
  Proof.
    pose proof (ar_ia _ _ _ _ _ R) as C. unfold ia_repr_ in *. cbv zeta in *. destruct C as [C0 C]. split.
    - intros i Hi. pose proof (C0 i Hi) as L. unfold kDepotNodesL1 in Hi. leaf L by_stat.
    - destruct (a_ia_inited A); walk C by_stat.
  Qed.

  #[using="R WF0 NN MU CEIL ENOUGH NR AI spa n md m Clg"] Lemma fsbase_P : fs_base_ LPA (a_pl A) (a_fhint A) v'.
  Proof.
    pose proof (ar_fsbase _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. (first [ pose proof ((place_fs A WF0)) as dR_37; dand3 dR_37 as FS1 FS2 FSM | pose proof (place_fs A WF0) as (FS1 & FS2 & FSM) ]). unfold a_fs in FS1, FS2, FSM.
    unfold fs_base_ in *. cbv zeta in *. (first [ dand5 C as H0 H1 H2 M1 M2 | destruct C as (H0 & H1 & H2 & M1 & M2) ]).
    split; [|split; [leaf H1 ltac:(apply AGfs; unfold a_fs, kFakeStackBytes; offs; lia)| split; [leaf H2 ltac:(apply AGfs; unfold a_fs, kFakeStackBytes; offs; lia)| split]]].
    - intros k Hk. pose proof (H0 k Hk) as L. leaf L ltac:(apply AGfs; unfold a_fs, kFakeStackBytes; offs; lia).
    - apply app_facts in FS1. apply mapped_N; [lia| unfold kFakeStackBytes in *; lia| lia| exact M1].
    - pose proof (fs_shadow_strict A (sh (p_fs (a_pl A))) WF0 ltac:(unfold a_fs, kFakeStackBytes; lia)) as X1.
      pose proof (fs_shadow_strict A (sh (p_fs (a_pl A)) + (kFakeStackBytes / 8 - 1)) WF0 ltac:(unfold a_fs, kFakeStackBytes; lia)) as X2.
      unfold in_shadow_strict, kLowShadowBeg, kShadowGapBeg, kHighShadowMapBeg, kHighMemBeg in X1, X2.
      apply mapped_N; [lia| right; lia| lia| exact M2].
  Qed.

  #[using="R WF0 MU CEIL ENOUGH NR AI spa n md m Clg"] Lemma fsptrs_P : fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    intros ff f Hf. pose proof (ar_fsptrs _ _ _ _ _ R ff f Hf) as L.
    destruct (wfF A WF0) as (F1 & _). destruct (F1 ff f Hf) as (K0 & _). pose proof (fsize_pos _ K0) as FS.
    (first [ pose proof ((live_frame_where A ff f ff WF0 Hf ltac:(lia))) as dR_39; dand4 dR_39 as K _ R1 R2 | destruct (live_frame_where A ff f ff WF0 Hf ltac:(lia)) as (K & _ & R1 & R2) ]).
    leaf L ltac:(apply AGfs; unfold a_fs, saved_flag_ptr, kFakeFramesOffset in *; lia).
  Qed.

  #[using="R WF0 MU CEIL ENOUGH NR AI spa n md m Clg"] Lemma fsflags_P : fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    intros k pos Hk Hpos. (first [ pose proof ((ar_fsflags _ _ _ _ _ R k pos Hk Hpos)) as dR_40; dex1 dR_40 as b; destruct dR_40 as [U D] | pose proof ((ar_fsflags _ _ _ _ _ R k pos Hk Hpos)) as dR_40; dand3 dR_40 as b U D | destruct (ar_fsflags _ _ _ _ _ R k pos Hk Hpos) as (b & U & D) ]). exists b. split; [| exact D].
    pose proof (fflag_addr_range (a_fs A) k pos Hk Hpos).
    leaf U ltac:(apply AGfs; unfold a_fs, kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *; lia).
  Qed.

  #[using="R WF0 NN NR AI n md m"] Lemma maps_P : maps_repr_ AL_pasan (a_pl A) v'.
  Proof.
    (first [ pose proof ((ar_maps _ _ _ _ _ R)) as dR_41; dand4 dR_41 as M1 M2 M3 M4 | pose proof (ar_maps _ _ _ _ _ R) as (M1 & M2 & M3 & M4) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((place_facts A WF0)) as dR_42; dand14 dR_42 as _ _ _ _ _ _ _ _ _ _ _ _ Psp0 _ | pose proof (place_facts A WF0) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Psp0 & _) ]). cbv zeta in Psp0.
    (first [ pose proof ((sb_facts A WF0)) as dR_43; dand5 dR_43 as _ _ HB6 RSB SCE | pose proof (sb_facts A WF0) as (_ & _ & HB6 & RSB & SCE) ]). unfold maps_repr_. unfold a_sb, a_b6, p_ri in *.
    cbn [al_image_lo al_image_hi AL_pasan] in M4 |- *.
    change (shadow_region 65536 (6332416 - 65536)) with (0x7fffa000, 0xbf400) in M4 |- *. cbn [fst snd] in M4 |- *.
    (first [ pose proof (stack_shadow_iv_facts) as dR_44; dand4 dR_44 as SF1 SF2 SF3 SF4 | pose proof stack_shadow_iv_facts as (SF1 & SF2 & SF3 & SF4) ]).
    ALogic2.kun.
    split; [apply mapped_N; [lia| right; lia| lia| exact M1]|]. split; [apply mapped_N; [lia| right; lia| lia| exact M2]|].
    split; [apply mapped_N; [lia| right; lia| lia| exact M3]| apply mapped_N; [lia| right; lia| lia| exact M4]].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="WF0 CEIL ENOUGH NR AI spa md m Clg"] Lemma KB : 0 <= kidx < carved_count A c. Proof. pose proof GEO; lia. Qed.

  (* [comment removed for export] *)
  #[using="n A"] Lemma u32s_entry : forall (mm : mem) a ws i w, bytes_at rsegs mm a (u32s ws) -> nth_error ws i = Some w ->
    bytes_at rsegs mm (a + 4 * Z.of_nat i) (le4 w).
  Proof.
    intros mm a ws. revert a. induction ws as [|x ws IH]; intros a i w B E; [destruct i; discriminate|].
    cbn [u32s] in B. apply bytes_at_app in B as [B0 B1]. rewrite length_le4 in B1. destruct i as [|i].
    - injection E as ->. rewrite Z.mul_0_r, Z.add_0_r. exact B0.
    - cbn in E. replace (a + 4 * Z.of_nat (S i)) with (a + Z.of_nat 4 + 4 * Z.of_nat i) by lia. exact (IH _ i w B1 E).
  Qed.
  Lemma nth_error_removelast : forall (l : list Z) i x, nth_error (removelast l) i = Some x -> nth_error l i = Some x.
  Proof.
    intros l i x E. destruct l as [|y l'] eqn:El; [destruct i; discriminate|]. rewrite <- El in *.
    assert (NE' : l <> []) by (subst l; discriminate).
    rewrite (removelast_app_last l 0 NE'). rewrite nth_error_app1; [exact E|]. apply nth_error_Some. rewrite E. discriminate.
  Qed.


  Local Notation lm' := (<[ hit_user A n kidx := LI (ChP (CP (class_of n) kidx)) n ]> (a_livemap A)).

  (* [comment removed for export] *)
  #[using="WF0 ENOUGH NR AI md m Clg"] Lemma CL_of : forall ch n1,
    (exists u0 li, lm' !! u0 = Some li /\ li_chunk li = ch /\ li_n li = n1 /\ u0 <> u) \/ In (QE ch n1) (q_entries (a_qthread A ++ a_qglobal A)) ->
    match ch with ChP (CP c' k') => 1 <= c' <= 30 /\ 0 <= k' < carved_count A c' /\ 0 <= n1 <= kMaxPrimaryUser /\ c' = class_of n1
             | ChS (CS mb n0') => In (CS mb n0') (sr_chunks (a_sec A)) /\ kMaxPrimaryUser < n1 /\ n0' = n1 end
    /\ ch <> ChP (CP c kidx).
  Proof.
    intros ch n1 H. destruct H as [(u0 & li & Hl & <- & <- & NEu)|Hq].
    - rewrite lookup_insert_ne in Hl by congruence.
      split; [| exact (rf_not_live A m md n AI NR ENOUGH _ _ Hl)].
      destruct (wfV A WF0) as (V1 & _). (first [ pose proof ((V1 u0 li Hl)) as dR_45; dand3 dR_45 as N U C | pose proof (V1 u0 li Hl) as (N & U & C) ]). cbv zeta in C.
      destruct (li_chunk li) as [[c' k']|[mb n0']].
      + (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range (li_n li) ltac:(lia)). rewrite <- Hc in *. unfold carved_count. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; assumption.
      + (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Hin| exact N2].
    - split.
      + (first [ pose proof ((wfQ A WF0)) as dR_48; dand3 dR_48 as Q1 Q2 _ | destruct (wfQ A WF0) as (Q1 & Q2 & _) ]).
        assert (WE : wf_qentry_ (a_reg A) (a_sec A) (QE ch n1)).
        { unfold q_entries in Hq. apply in_flat_map in Hq as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb];
          [pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as WB| pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as WB];
          (first [ dand3 WB as _ _ WB | destruct WB as (_ & _ & WB) ]); exact (proj1 (Forall_forall _ _) WB _ Heb). }
        destruct WE as (N & C). cbn [qe_chunk qe_n] in *. destruct ch as [[c' k']|[mb n0']].
        * (first [ dand3 C as N2 Hc Hk | destruct C as (N2 & Hc & Hk) ]). pose proof (class_of_range n1 ltac:(lia)). rewrite <- Hc in *. unfold carved_count. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia; assumption.
        * (first [ dand3 C as N2 -> Hin | destruct C as (N2 & -> & Hin) ]). OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; [exact Hin| exact N2].
      + intros ->. apply (rf_not_quar A m md n AI NR ENOUGH). unfold quarantined_chunks_. apply in_map_iff. exists (QE (ChP (CP c kidx)) n1). split; [reflexivity| exact Hq].
  Qed.

  (* [comment removed for export] *)
  #[using="WF0 MU CEIL ENOUGH NR AI spa md"] Lemma AGch : forall ch n1 a,
    match ch with ChP (CP c' k') => 1 <= c' <= 30 /\ 0 <= k' < carved_count A c' /\ 0 <= n1 <= kMaxPrimaryUser /\ c' = class_of n1
             | ChS (CS mb n0') => In (CS mb n0') (sr_chunks (a_sec A)) /\ kMaxPrimaryUser < n1 /\ n0' = n1 end ->
    ch <> ChP (CP c kidx) -> chunk_lo sb ch <= a < chunk_hi sb ch -> v' (wz a) = v (wz a).
  Proof.
    intros ch n1 a CL NEQ Ha. destruct ch as [[c' k']|[mb n0']].
    - (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). cbn [chunk_lo chunk_hi alloc_beg] in Ha. apply (AGchunk c' k'); [exact Hc| exact Hk| | exact Ha].
      destruct (Z.eq_dec c' c) as [->|]; [| left; assumption]. right. intros ->. apply NEQ. reflexivity.
    - (first [ dand3 CL as Hin _ -> | destruct CL as (Hin & _ & ->) ]). cbn [chunk_lo chunk_hi] in Ha. apply (AGsec (CS mb n1)); [exact Hin| cbn [cs_map cs_n]; exact Ha].
  Qed.
  (* [comment removed for export] *)
  #[using="NR n"] Lemma hdr_foot_in : forall ch n1 a,
    match ch with ChP (CP c' k') => 1 <= c' <= 30 /\ 0 <= k' < carved_count A c' /\ 0 <= n1 <= kMaxPrimaryUser /\ c' = class_of n1
             | ChS (CS mb n0') => In (CS mb n0') (sr_chunks (a_sec A)) /\ kMaxPrimaryUser < n1 /\ n0' = n1 end ->
    hdr_foot sb ch n1 a \/ (user_of sb ch n1 <= a < user_of sb ch n1 + 8) -> chunk_lo sb ch <= a < chunk_hi sb ch.
  Proof.
    intros ch n1 a CL Ha. unfold hdr_foot in Ha. destruct ch as [[c' k']|[mb n0']].
    - (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((primary_layout sb c' k' n1 Hc Hn Hcl)) as dR_55; dand5 dR_55 as L1 L2 L3 L5 L4 | pose proof (primary_layout sb c' k' n1 Hc Hn Hcl) as (L1 & L2 & L3 & L5 & L4) ]). cbv zeta in *.
      cbn [chunk_lo chunk_hi alloc_beg user_of] in *. lia.
    - (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb n1 Hn)) as dR_57; dand7 dR_57 as S1 S2 S3 S4 S5 S6 S7 | pose proof (secondary_layout mb n1 Hn) as (S1 & S2 & S3 & S4 & S5 & S6 & S7) ]).
      cbn [chunk_lo chunk_hi alloc_beg user_of cs_map cs_n] in *. unfold kSecondaryHeaderSize in *. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="NR n"] Lemma hdr_P : forall ch n1 st, (forall a, hdr_foot sb ch n1 a -> v' (wz a) = v (wz a)) ->
    hdr_repr_ LPA sb v ch n1 st -> hdr_repr_ LPA sb v' ch n1 st.
  Proof.
    intros ch n1 st AG [(id0 & b1 & Hid & Hb1 & Hb1m & RC) LH]. split.
    - exists id0, b1. split; [exact Hid|]. split; [exact Hb1|]. split; [exact Hb1m|].
      eapply rw_cells_agree; [exact RC|]. rewrite chunk_hdr_size. intros i Hi. apply AG. unfold hdr_foot. left. lia.
    - intros NE16. destruct (LH NE16) as [X Y]. split; [leaf X ltac:(apply AG; unfold hdr_foot; right; lia) | leaf Y ltac:(apply AG; unfold hdr_foot; right; lia)].
  Qed.

  (* [comment removed for export] *)
  #[using="R WF0 NN CEIL ENOUGH NR AI spa md m Clg"] Lemma CMv : forall a k, region_beg sb c <= a -> a + k <= region_beg sb c + rg_mapped_user (a_reg A c) -> 0 <= k -> mapped v' a k.
  Proof.
    intros a k H1 H2 Hk. pose proof GEO as G. pose proof (ar_regions _ _ _ _ _ R c CR) as RR. unfold region_repr_ in RR. cbv zeta in RR.
    (first [ dand13 RR as _ _ _ _ _ _ _ _ _ _ _ _ RM | destruct RR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RM) ]).
    apply mapped_N; [kung_all; lia| right; kung_all; lia| kung_all; lia|]. intros i Hi. replace (a + i) with (region_beg sb c + (a - region_beg sb c + i)) by lia. apply RM. lia.
  Qed.


  #[using="WF0 NN MU CEIL ENOUGH NR AI spa n md"] Lemma batches_P : forall bs, (forall b, In b bs -> In b (a_qthread A ++ a_qglobal A)) ->
    batches_repr LPA v sb bs -> batches_repr LPA v' sb bs.
  Proof.
    induction bs as [|b bs IH]; intros SUB BR; [exact I|]. pose proof alloc_ceiling_val as CE.
    cbn [batches_repr] in *. (first [ dand6 BR as X1 X2 X3 X4 M BR | destruct BR as (X1 & X2 & X3 & X4 & M & BR) ]).
    assert (INb : In b (a_qthread A ++ a_qglobal A)) by (apply SUB; left; reflexivity).
    (first [ pose proof ((wfQ A WF0)) as dR_60; dand3 dR_60 as Q1 Q2 _ | destruct (wfQ A WF0) as (Q1 & Q2 & _) ]).
    assert (WB : wf_batch_ (a_reg A) (a_sec A) b).
    { apply in_app_iff in INb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]. }
    (first [ dand3 WB as LEN Hk _ | destruct WB as (LEN & Hk & _) ]).
    assert (C24 : 1 <= kQuarantineBatchClass <= 30) by (unfold kQuarantineBatchClass; lia).
    pose proof class_size_24 as C24E.
    assert (AGb : forall x, batch_addr sb b <= x < batch_addr sb b + kQuarantineBatchBytes -> v' (wz x) = v (wz x)).
    { intros x Hx. unfold batch_addr in Hx. apply (AGchunk kQuarantineBatchClass (ba_idx b)); [exact C24| exact Hk| | unfold kQuarantineBatchBytes in Hx; rewrite C24E; exact Hx].
      destruct (Z.eq_dec kQuarantineBatchClass c) as [E|NE24]; [| left; exact NE24]. right. intros EK.
      (first [ pose proof ((ref_partition A m md n AI NR ENOUGH)) as dR_62; dand4 dR_62 as _ _ _ NB | destruct (ref_partition A m md n AI NR ENOUGH) as (_ & _ & _ & NB) ]). apply NB. split; [symmetry; exact E|].
      rewrite <- EK. unfold batch_indices_. apply in_map. exact INb. }
    (first [ pose proof ((carved_chunk_bounds A _ _ WF0 C24 Hk)) as dR_63; dand3 dR_63 as B1 B2 _ | pose proof (carved_chunk_bounds A _ _ WF0 C24 Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A _ WF0 C24) as RB. cbv zeta in *.
    split; [leaf X1 ltac:(apply AGb; offs; lia)|]. split; [leaf X2 ltac:(apply AGb; offs; lia)|]. split; [leaf X3 ltac:(apply AGb; offs; lia)|].
    split; [|split].
    - intros i e E. pose proof (X4 i e E) as L.
      assert (Z.of_nat i < Z.of_nat (length (ba_entries b))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
      leaf L ltac:(apply AGb; unfold kQuarantineBatchCount in *; offs; lia).
    - unfold batch_addr in *. change (a_sb A) with sb in *.
      apply mapped_N; [| right | | exact M]; unfold kQuarantineBatchBytes, kHighMemBeg, kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia.
    - apply IH; [| exact BR]. intros b' Hb'. apply SUB. right. exact Hb'.
  Qed.

  #[using="R WF0 NN MU CEIL ENOUGH NR AI spa n md m Clg"] Lemma quar_P : quarantine_repr_ LPA AL_pasan (a_pl A) (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ R)) as dR_64; dand3 dR_64 as QT QG QR | pose proof (ar_quar _ _ _ _ _ R) as (QT & QG & QR) ]). unfold quarantine_repr_. change (p_sb (a_pl A)) with sb in *.
    split; [|split].
    - (first [ dand5 QT as X1 X2 X3 X4 BR | destruct QT as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      split; [leaf X1 by_thr|]. split; [leaf X2 by_thr|]. split; [leaf X3 by_thr|]. split; [leaf X4 by_thr|].
      apply batches_P; [intros b Hb; apply in_or_app; left; exact Hb| exact BR].
    - (first [ dand5 QG as X1 X2 X3 X4 BR | destruct QG as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      split; [leaf X1 by_stat|]. split; [leaf X2 by_stat|]. split; [leaf X3 by_stat|]. split; [leaf X4 by_stat|].
      apply batches_P; [intros b Hb; apply in_or_app; right; exact Hb| exact BR].
    - intros e He. (first [ pose proof ((QR e He)) as dR_67; dand3 dR_67 as HR J MC | destruct (QR e He) as (HR & J & MC) ]). pose proof alloc_ceiling_val as CE.
      pose proof (CL_of (qe_chunk e) (qe_n e) ltac:(right; destruct e; exact He)) as [CL NEQ].
      (* [comment removed for export] *)
      assert (RNG : 0x60a000 <= chunk_lo sb (qe_chunk e) /\ chunk_hi sb (qe_chunk e) <= alloc_ceiling).
      { destruct (qe_chunk e) as [[c' k']|[mb n0']].
        - (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). (first [ pose proof ((carved_chunk_bounds A c' k' WF0 Hc Hk)) as dR_69; dand3 dR_69 as B1 B2 _ | pose proof (carved_chunk_bounds A c' k' WF0 Hc Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in *.
          cbn [chunk_lo chunk_hi alloc_beg]. change (a_sb A) with sb in *. kung_all. lia.
        - (first [ dand3 CL as Hin Hn E0 | destruct CL as (Hin & Hn & E0) ]). (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_71; dand5 dR_71 as _ _ B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (_ & _ & B3 & B4 & B5) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
          apply app_facts in B3. pose proof (needed_size_ge (qe_n e)). rewrite <- E0 in *. rewrite needed_size2_secondary in B5 by lia. pose proof (rounded_size_ge n0').
          unfold kMaxPrimaryUser, kPageSize, kSecondaryHeaderSize in *. lia. }
      pose proof (hdr_foot_in (qe_chunk e) (qe_n e) (user_of sb (qe_chunk e) (qe_n e)) CL ltac:(right; lia)) as UR.
      split; [|split].
      + apply hdr_P; [| exact HR]. intros a Ha. apply (AGch (qe_chunk e) (qe_n e) a CL NEQ). apply (hdr_foot_in _ (qe_n e)); [exact CL| left; exact Ha].
      + apply junk_N; [kung_all; lia| right; kung_all; lia| exact J].
      + apply mapped_N; [kung_all; lia| right; lia| lia| exact MC].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="NR"] Lemma UEQ : u = AB + rz_size n.
  Proof. (first [ pose proof ((hit_u_range A n kidx NR)) as dR_72; dand3 dR_72 as _ _ UE | destruct (hit_u_range A n kidx NR) as (_ & _ & UE) ]). unfold hit_user in UE |- *. exact UE. Qed.
  (* [comment removed for export] *)
  #[using="WF0 CEIL ENOUGH NR AI spa md m Clg"] Lemma USH : sh u = shU /\ sh AB + rz_size n / 8 = shU /\ shU + (n + 7) / 8 <= sh (AB + class_size c) /\
              sh (AB + class_size c) = sh AB + class_size c / 8 /\ sh AB <= shU /\ kHighShadowMapBeg <= sh AB.
  Proof.
    pose proof GEO as G. pose proof UEQ as UE.
    assert (ABM : AB mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (AB / 8); lia).
    assert (RZM : rz_size n mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (rz_size n / 8); lia).
    assert (CSM : class_size c mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (class_size c / 8); lia).
    assert (UM : u mod 8 = 0) by (rewrite UE, Z.add_mod, ABM, RZM by lia; reflexivity).
    pose proof (sh_add AB (rz_size n) ABM RZM) as E1. rewrite <- UE in E1.
    pose proof (sh_add AB (class_size c) ABM CSM) as E2.
    pose proof (sh_ceil_le u n AB (class_size c) UM ABM CSM ltac:(lia) ltac:(lia)) as [_ LE].
    pose proof (sh_high_range AB ltac:(kung_all; lia)) as [HR _].
    assert (SU : sh u = shU) by (rewrite E1; unfold sh; lia).
    rewrite <- SU. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try lia.
  Qed.
  #[using="NR n A"] Lemma sh_sum_le : forall X L, 0 <= L -> sh X + L / 8 <= sh (X + L).
  Proof.
    intros X L HL. unfold sh. assert (X / 8 + L / 8 <= (X + L) / 8); [| lia].
    apply Z.div_le_lower_bound; [lia|]. pose proof (Z.mul_div_le X 8 ltac:(lia)). pose proof (Z.mul_div_le L 8 ltac:(lia)). lia.
  Qed.
  (* [comment removed for export] *)
  #[using="WF0 CEIL ENOUGH NR AI spa md m Clg"] Lemma sh_apart : forall X L z, 0 <= L -> (X + L <= AB \/ AB + class_size c <= X) -> sh X <= z < sh X + L / 8 ->
    ~ (shU <= z < shU + (n + 7) / 8).
  Proof.
    intros X L z HL D Hz. (first [ pose proof (USH) as dR_73; dand6 dR_73 as U1 U2 U3 U4 U5 U6 | pose proof USH as (U1 & U2 & U3 & U4 & U5 & U6) ]). pose proof (sh_sum_le X L HL).
    destruct D as [D|D].
    - pose proof (sh_mono (X + L) AB D). lia.
    - pose proof (sh_mono (AB + class_size c) X D). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="WF0 MU CEIL ENOUGH NR AI spa md"] Lemma CHK : forall c' k bs, 1 <= c' <= 30 -> 0 <= k < carved_count A c' -> (c' <> c \/ k <> kidx) ->
    Z.of_nat (length bs) = class_size c' / 8 ->
    bytes_at rsegs v (sh (chunk_addr sb c' k)) bs -> bytes_at rsegs v' (sh (chunk_addr sb c' k)) bs.
  Proof.
    intros c' k bs Hc Hk NEQ L B. pose proof GEO as G. eapply bytes_at_agree_gen; [exact B|]. intros i Hi.
    (first [ pose proof ((carved_chunk_bounds A c' k WF0 Hc Hk)) as dR_74; dand4 dR_74 as B1 B2 B3 B4 | pose proof (carved_chunk_bounds A c' k WF0 Hc Hk) as (B1 & B2 & B3 & B4) ]). pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in *.
    change (a_sb A) with sb in *.
    (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
    pose proof (class_size_mod32 c' Hc) as CM. pose proof (class_size_range c' Hc) as CSR'.
    apply AGhs.
    - (* [comment removed for export] *)
      pose proof (sh_ceil_le (chunk_addr sb c' k) (class_size c') (region_beg sb c') (rg_mapped_user (a_reg A c'))
        ltac:(apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact Q9]) Q10 ltac:(lia) ltac:(lia)) as [X Y].
      rewrite (div8_ceil_exact (class_size c') (mod0_down _ 32 8 (divide_wit 8 4) CM)) in Y.
      unfold heap_shadow, heap_shadow_. left. exists c'. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with sb. lia.
    - apply (sh_apart (chunk_addr sb c' k) (class_size c')); [lia| | lia].
      destruct (Z.eq_dec c' c) as [->|NC].
      + destruct NEQ as [X|NK]; [congruence|]. exact (carved_chunks_disjoint sb c k kidx Hc ltac:(lia) ltac:(lia) NK).
      + destruct (regions_disjoint sb c' c NC ltac:(lia) ltac:(lia)); kung_all; lia.
  Qed.


  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Cells.
  Variables (md0 : mem) (ks : list word) (b1' id : Z).
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis KSF : firstn (length fetched) ks = map (fun k => Z_to_bv 64 (k * class_size c / kCompactPtrScale)) fetched.
  Hypothesis P_pc : rw_cells rsegs v' (thr + 208 + 80 * c)
     [C4 (Z_to_bv 64 (Z.of_nat (length fetched) - 1)); C4 (Z_to_bv 64 (max_count c)); C8 (Z_to_bv 64 (class_size c)); CB 64 (u32s ks)].
  (* [comment removed for export] *)
  Hypothesis P_mx : rw_cells rsegs v' (ri + 128 * c) [C8 (Z_to_bv 64 0)].
  Hypothesis P_nf : rw_cells rsegs v' (ri + 128 * c + 16) [C8 (Z_to_bv 64 (nf - KK))].
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


  #[using="IDR B1R P_mx LKS id b1' ks R WF0 MU CEIL ENOUGH NR AI spa n md m Clg"] Lemma locks_P : locks_repr_ LPA AL_pasan (a_pl A) [] v'.
  Proof.
    pose proof (ar_locks _ _ _ _ _ R) as C. pose proof CR as HCR. pose proof GEO as G. unfold locks_repr_ in *. cbv zeta in *. destruct C as (C0 & C).
    split.
    - intros c' Hc. destruct (C0 c' Hc) as [X Y]. change (p_ri (a_pl A)) with ri in X, Y |- *. unfold kRegionInfoSize in *.
      destruct (Z.eq_dec c' c) as [->|NEc].
      + (* [comment removed for export] *)
        split.
        * destruct P_mx as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. unfold u64_at. rewrite Z.add_0_r. exact B.
        * leaf Y ltac:(apply AGri; offs; clear - Hi__ HCR; lia).
      + split; [leaf X ltac:(apply AGri; offs; clear - Hi__ HCR Hc NEc; lia) | leaf Y ltac:(apply AGri; offs; clear - Hi__ HCR Hc NEc; lia)].
    - walk C by_stat.
  Qed.

  #[using="IDR B1R P_nf LKS id b1' ks R WF0 NN MU CEIL ENOUGH NR AI spa md m Clg"] Lemma regions_P : forall c', 1 <= c' <= 30 -> region_repr_ LPA sb (ref_reg (a_reg A) c KK c') v' c'.
  Proof.
    intros c' Hc. pose proof (ar_regions _ _ _ _ _ R c' Hc) as C. pose proof alloc_ceiling_val as CE. pose proof CR as HCR. pose proof GEO as G.
    pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in RB. (first [ pose proof ((wfR A WF0)) as dR_76; dand3 dR_76 as WR _ _ | destruct (wfR A WF0) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_77; dand8 dR_77 as Q1 Q2 Q3 Q4 Q5 Q6 Q7 _ | pose proof (WR c' Hc) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & _) ]).
    unfold ref_reg. destruct (Z.eqb_spec c' c) as [Ec|NEc].
    - (* [comment removed for export] *)
      subst c'. unfold region_repr_ in *. cbv zeta in *. cbn [rg_free rg_mapped_fa rg_allocated_user rg_mapped_user].
      (first [ pose proof ((ref_ri A m md n AI)) as dR_78; dand7 dR_78 as _ _ _ _ _ RIA _ | pose proof (ref_ri A m md n AI) as (_ & _ & _ & _ & _ & RIA & _) ]). rewrite RIA in *. unfold free_array_beg in *.
      assert (AGR : forall x, ri + 128 * c <= x < ri + 128 * c + 128 -> ~ (ri + 128 * c <= x < ri + 128 * c + 8) ->
                ~ (ri + 128 * c + 16 <= x < ri + 128 * c + 24) -> ~ (ri + 128 * c + 72 <= x < ri + 128 * c + 80) -> v' (wz x) = v (wz x)).
      { intros x Hx Y1 Y2 Y3. apply AGri; [clear - Hx HCR; lia| exact Y1| exact Y2| exact Y3]. }
      assert (AGfa' : forall x, region_beg sb c + kFreeArrayOffset <= x < region_beg sb c + kFreeArrayOffset + rg_mapped_fa (a_reg A c) -> v' (wz x) = v (wz x)).
      { intros x Hx. apply (AGfa c); [exact Hc|]. unfold free_array_beg. exact Hx. }
      (first [ dand13 C as Hnf Hfa Hal Ham Hmu Hmm Hex J64 Jna Jrt CF M1 M2 | destruct C as (Hnf & Hfa & Hal & Ham & Hmu & Hmm & Hex & J64 & Jna & Jrt & CF & M1 & M2) ]).
      pose proof (ref_rest_length fr KK ltac:(pose proof RK; lia)) as RL.
      unfold off_ri_num_freed, off_ri_mapped_free_array, off_ri_allocated_user, off_ri_allocated_meta, off_ri_mapped_user, off_ri_mapped_meta,
             off_ri_exhausted, off_ri_n_allocated, off_ri_rtoi in *.
      split.
      { (* [comment removed for export] *)
        rewrite RL. destruct P_nf as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. unfold u64_at. exact B. }
      split; [leaf Hfa ltac:(apply AGR; clear - Hi__; lia)|]. split; [leaf Hal ltac:(apply AGR; clear - Hi__; lia)|].
      split; [leaf Ham ltac:(apply AGR; clear - Hi__; lia)|]. split; [leaf Hmu ltac:(apply AGR; clear - Hi__; lia)|].
      split; [leaf Hmm ltac:(apply AGR; clear - Hi__; lia)|]. split; [leaf Hex ltac:(apply AGR; lia)|].
      split; [apply junk_N; [kung_all; lia| right; kung_all; lia| exact J64]|].
      split; [apply junk_N; [kung_all; lia| right; kung_all; lia| exact Jna]|].
      split; [apply junk_N; [kung_all; lia| right; kung_all; lia| exact Jrt]|].
      split; [|split].
      + intros i j E. pose proof (nth_error_firstn_Some _ _ _ _ E) as E'. pose proof (CF i j E') as LF.
        assert (Z.of_nat i < nf) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E'; discriminate)); lia).
        leaf LF ltac:(apply AGfa'; offs; lia).
      + apply mapped_N; [unfold kHighMemBeg, kFreeArrayOffset in *; lia| right; unfold kHighMemBeg, kFreeArrayOffset in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| exact M1].
      + apply mapped_N; [unfold kHighMemBeg in *; lia| right; unfold kHighMemBeg in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| exact M2].
    - (* [comment removed for export] *)
      unfold region_repr_ in *. cbv zeta in *. unfold region_info_addr, free_array_beg in *.
      assert (AGri' : forall x, sb + kSpaceSize + kRegionInfoSize * c' <= x < sb + kSpaceSize + kRegionInfoSize * c' + 128 -> v' (wz x) = v (wz x)).
      { intros x Hx. apply AGri; unfold kRegionInfoSize, kSpaceSize in *; try (generalize alloc_ceiling_val); clear -Hx Hc NEc HCR G; lia. }
      assert (AGfa' : forall x, region_beg sb c' + kFreeArrayOffset <= x < region_beg sb c' + kFreeArrayOffset + rg_mapped_fa (a_reg A c') -> v' (wz x) = v (wz x)).
      { intros x Hx. apply (AGfa c'); [exact Hc|]. unfold free_array_beg. exact Hx. }
      do 10 (let L := fresh "L" in destruct C as [L C]; split; [leaf L ltac:(apply AGri'; offs; lia) |]).
      (first [ dand3 C as CF M1 M2 | destruct C as (CF & M1 & M2) ]). split; [|split].
      + intros i k E. pose proof (CF i k E) as LF. assert (Z.of_nat i < Z.of_nat (length (rg_free (a_reg A c')))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
        leaf LF ltac:(apply AGfa'; offs; lia).
      + apply mapped_N; [unfold kHighMemBeg, kFreeArrayOffset in *; lia| right; unfold kHighMemBeg, kFreeArrayOffset in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| exact M1].
      + apply mapped_N; [unfold kHighMemBeg in *; lia| right; unfold kHighMemBeg in *; lia| unfold kRegionSize, kSpaceSize, kFreeArrayOffset in *; lia| exact M2].
  Qed.

  #[using="IDR B1R LKS id b1' ks R WF0 MU CEIL ENOUGH NR AI spa n md m Clg"] Lemma consts_P : consts_repr_ LPA AL_pasan (a_pl A) v'.
  Proof.
    pose proof (ar_consts _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. pose proof TPV as TP.
    unfold consts_repr_ in *. cbv zeta in *. destruct C as (CF & C).
    split.
    { apply Forall_forall. intros cst Hc. pose proof (proj1 (Forall_forall _ _) CF cst Hc) as B.
      eapply bytes_at_agree_gen; [exact B|]. intros i Hi. apply (AGconst cst); [exact Hc| lia]. }
    do 17 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_stat |]).
    (first [ dand7 C as K1 K2 K3 KS KE1 KE2 C | destruct C as (K1 & K2 & K3 & KS & KE1 & KE2 & C) ]).
    split; [leaf K1 ltac:(apply AGshared; apply KS; lia)|]. split; [leaf K2 ltac:(apply AGshared; rewrite KE1; rewrite <- Z.add_assoc; apply KS; lia)|].
    split; [leaf K3 ltac:(apply AGshared; rewrite KE2; rewrite <- Z.add_assoc; apply KS; lia)|].
    split; [exact KS|]. split; [exact KE1|]. split; [exact KE2|].
    do 7 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_stat |]).
    do 4 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_thr |]).
    destruct C as [UNW C]. split; [leaf UNW ltac:(unfold off_th_unwinding in *; by_thr) |].   (* [comment removed for export] *)
    do 2 (let L := fresh "L" in destruct C as [L C]; split; [leaf L by_ctx |]).
    destruct C as [(tsd & T1 & T2 & T3) C]. split.
    - exists tsd. split; [|split; [exact T2|]].
      + leaf T1 ltac:(apply AGimg; rewrite TP; lia).
      + leaf T3 ltac:(apply AGshared; apply T2; lia).
    - (first [ dand5 C as C D1 D2 D3 D4 | destruct C as (C & D1 & D2 & D3 & D4) ]). split; [leaf C ltac:(apply AGimg; rewrite TP; lia)|].
      split; [leaf D1 ltac:(apply AGimg; rewrite TP; lia)|].
      split; [leaf D2 ltac:(apply AGdtls; lia)|].
      split; [leaf D3 by_thr| leaf D4 by_thr].
  Qed.

  #[using="IDR B1R P_pc KSF LKS id b1' ks R WF0 NN MU CEIL ENOUGH CI NR AI spa md m Clg"] Lemma cache_P : cache_repr_ LPA (a_pl A) (ref_cache (a_cache A) c fetched) (a_cache_inited A) v'.
  Proof.
    pose proof (ar_cache _ _ _ _ _ R) as C. pose proof alloc_ceiling_val as CE. pose proof GEO as G. pose proof CI as HCI.
    (first [ pose proof ((place_facts A WF0)) as dR_83; dand3 dR_83 as Pthr Pctx _ | pose proof (place_facts A WF0) as (Pthr & Pctx & _) ]). cbv zeta in Pthr, Pctx.
    unfold cache_repr_ in *. cbv zeta in *. (first [ dand5 C as C0 J1 J2 M1 M2 | destruct C as (C0 & J1 & J2 & M1 & M2) ]).
    (first [ dand3 Pthr as Pthr PthrC _ | destruct Pthr as (Pthr & PthrC & _) ]). apply app_facts in Pthr. (first [ dand3 Pctx as Pctx PctxC _ | destruct Pctx as (Pctx & PctxC & _) ]). apply app_facts in Pctx.
    split; [| split; [apply junk_N; [kung_all; offs; lia| offs; clear - Pthr; lia| exact J1] | split; [apply junk_N; [kung_all; offs; lia| offs; clear - Pthr; lia| exact J2]| split; (apply mapped_N; [| | | eassumption]); clear - Pthr PthrC Pctx PctxC CE; kung_all; lia]]].
    intros c' Hc'. unfold ref_cache. destruct (Z.eqb_spec c' c) as [->|NEQ].
    - (* [comment removed for export] *)
      cbn [pk_chunks]. rewrite HCI. cbn [andb]. destruct (Z.eqb_spec c 0) as [E0|_]; [lia|]. cbn [negb].
      rewrite removelast_length'. pose proof FETL as FL. (first [ pose proof (RK) as dR_87; dand3 dR_87 as MK2 KR _ | pose proof RK as (MK2 & KR & _) ]).
      destruct P_pc as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
      apply bytes_at_app in B as [Bcnt B]. apply bytes_at_app in B as [Bmax B]. apply bytes_at_app in B as [Bsz Bks].
      rewrite !length_le4, !length_le8 in *.
      assert (LNE : (1 <= length fetched)%nat) by lia.
      unfold u32_at, u64_at. offs.
      split; [lia|]. split.
      { replace (Z.of_nat (length fetched - 1)) with (Z.of_nat (length fetched) - 1) by lia. replace (thr + (208 + 80 * c) + 0) with (thr + 208 + 80 * c) by lia. exact Bcnt. }
      split.
      { split; [replace (thr + (208 + 80 * c) + 4) with (thr + 208 + 80 * c + Z.of_nat 4) by lia; exact Bmax
              | replace (thr + (208 + 80 * c) + 8) with (thr + 208 + 80 * c + Z.of_nat 4 + Z.of_nat 4) by lia; exact Bsz]. }
      split.
      { intros i k E. pose proof (nth_error_removelast _ _ _ E) as E'.
        assert (Hi : (i < length fetched)%nat) by (apply nth_error_Some; rewrite E'; discriminate).
        assert (EK : nth_error ks i = Some (Z_to_bv 64 (k * class_size c / 16))).
        { rewrite <- (firstn_skipn (length fetched) ks). rewrite nth_error_app1 by (rewrite firstn_length; lia). rewrite KSF.
          rewrite nth_error_map, E'. reflexivity. }
        pose proof (u32s_entry v' _ ks i _ Bks EK) as X.
        replace (thr + (208 + 80 * c) + (16 + 4 * Z.of_nat i)) with (thr + 208 + 80 * c + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + 4 * Z.of_nat i) by lia. exact X. }
      { (* [comment removed for export] *)
        apply junk_at_of_mapped; [kung_all; lia| lia| kung_all; lia|].
        pose proof (bytes_at_mapped_gen v' _ _ Bks ltac:(kung_all; lia) ltac:(rewrite u32s_length, LKS; pose proof CR as CR'; clear - Pthr CR'; lia)) as MK. rewrite u32s_length, LKS in MK.
        intros j Hj. replace (thr + (208 + 80 * c) + (16 + 4 * Z.of_nat (length fetched - 1)) + j)
          with (thr + 208 + 80 * c + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 8 + (4 * (Z.of_nat (length fetched) - 1) + j)) by lia. apply MK. lia. }
    - (* [comment removed for export] *)
      (first [ pose proof ((C0 c' Hc')) as dR_88; dand5 dR_88 as LEN X1 X2 X3 X4 | destruct (C0 c' Hc') as (LEN & X1 & X2 & X3 & X4) ]). split; [exact LEN|].
      assert (AGe : forall x, thr + off_th_per_class c' <= x < thr + off_th_per_class c' + 80 -> v' (wz x) = v (wz x)).
      { intros x Hx. pose proof CR as HCR. offs_h Hx. unfold kPerClassSize in Hx. apply AGthr; try (generalize alloc_ceiling_val); clear -Hx HCR Hc' NEQ; nia. }
      split; [leaf X1 ltac:(apply AGe; offs; lia)|]. split; [|split].
      + destruct (a_cache_inited A && negb (c' =? 0)); destruct X2 as [Y1 Y2]; split; first [leaf Y1 ltac:(apply AGe; offs; lia) | leaf Y2 ltac:(apply AGe; offs; lia)].
      + intros i k E. pose proof (X3 i k E) as L.
        assert (Z.of_nat i < Z.of_nat (length (pk_chunks (a_cache A c')))) by (pose proof (proj1 (nth_error_Some _ _) ltac:(rewrite E; discriminate)); lia).
        leaf L ltac:(apply AGe; offs; lia).
      + apply junk_N; [kung_all; offs; lia| offs; pose proof Hc' as Hc''; clear - Pthr Hc''; lia| exact X4].
  Qed.

  #[using="P_lch P_hdr IDR B1M B1R LKS id b1' ks R WF0 NN MU CEIL ENOUGH NR AI spa md m Clg"] Lemma live_P : live_repr_ LPA sb lm' v'.
  Proof.
    intros u0 li Hl. pose proof alloc_ceiling_val as CE.
    destruct (decide (u0 = u)) as [->|NEu].
    - rewrite lookup_insert_eq in Hl. injection Hl as <-. cbn [li_chunk li_n].
      pose proof GEO as G. (first [ pose proof ((hit_u_range A n kidx NR)) as dR_89; dand3 dR_89 as U1 U2 UE | destruct (hit_u_range A n kidx NR) as (U1 & U2 & UE) ]). unfold hit_user in UE. change (a_sb A) with sb in UE, U1, U2.
      split; [|split].
      + unfold hdr_repr_. cbv zeta. rewrite UE. cbn [alloc_beg]. split.
        * exists id, b1'. split; [exact IDR|]. split; [exact B1R|]. split; [exact B1M|].
          unfold chunk_hdr_cells. cbn [ch_state ch_b1 ch_size ch_ctx]. unfold size_hi. rewrite (proj2 (proj2 (user_size_pos n ltac:(lia))) ltac:(lia)).
          rewrite Z.shiftr_div_pow2, Z.div_small by (unfold kMaxPrimaryUser in NR; lia).
          replace (AB + rz_size n - 16) with (AB + rz_size n + -16) by lia. exact P_hdr.
        * intros NE16. destruct (P_lch ltac:(lia)) as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
          apply bytes_at_app in B as [B0 B1]. rewrite length_le8 in B1. unfold u64_at.
          split; [exact B0| replace (AB + rz_size n - 16) with (AB + rz_size n + -16) by lia; exact B1].
      + unfold hit_user. rewrite UE. apply CMv; lia.
      + cbn [chunk_lo chunk_hi alloc_beg]. replace (chunk_addr sb c kidx + class_size c - chunk_addr sb c kidx) with (class_size c) by lia. apply CMv; lia.
    - rewrite lookup_insert_ne in Hl by congruence. (first [ pose proof ((ar_live _ _ _ _ _ R u0 li Hl)) as dR_90; dand3 dR_90 as HR MU0 MC | destruct (ar_live _ _ _ _ _ R u0 li Hl) as (HR & MU0 & MC) ]).
      pose proof (CL_of (li_chunk li) (li_n li) ltac:(left; exists u0, li; rewrite lookup_insert_ne by congruence; auto)) as [CL NEQ].
      destruct (wfV A WF0) as (V1 & _). (first [ pose proof ((V1 u0 li Hl)) as dR_91; dand3 dR_91 as N U _ | pose proof (V1 u0 li Hl) as (N & U & _) ]).
      assert (RNG : 0x60a000 <= chunk_lo sb (li_chunk li) /\ chunk_hi sb (li_chunk li) <= alloc_ceiling).
      { destruct (li_chunk li) as [[c' k']|[mb n0']].
        - (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). (first [ pose proof ((carved_chunk_bounds A c' k' WF0 Hc Hk)) as dR_93; dand3 dR_93 as B1 B2 _ | pose proof (carved_chunk_bounds A c' k' WF0 Hc Hk) as (B1 & B2 & _) ]). pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in *.
          cbn [chunk_lo chunk_hi alloc_beg]. change (a_sb A) with sb in *. kung_all. lia.
        - (first [ dand3 CL as Hin Hn E0 | destruct CL as (Hin & Hn & E0) ]). (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_95; dand5 dR_95 as _ _ B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (_ & _ & B3 & B4 & B5) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
          apply app_facts in B3. pose proof (needed_size_ge (li_n li)). rewrite <- E0 in *. rewrite needed_size2_secondary in B5 by lia. pose proof (rounded_size_ge n0').
          unfold kMaxPrimaryUser, kPageSize, kSecondaryHeaderSize in *. lia. }
      pose proof (hdr_foot_in (li_chunk li) (li_n li) u0 CL) as HFu.
      split; [|split].
      + apply hdr_P; [| exact HR]. intros a Ha. apply (AGch (li_chunk li) (li_n li) a CL NEQ). apply (hdr_foot_in _ (li_n li)); [exact CL| left; exact Ha].
      + pose proof (hdr_foot_in (li_chunk li) (li_n li)) as HF.
        assert (UR : chunk_lo sb (li_chunk li) <= u0 /\ u0 + li_n li <= chunk_hi sb (li_chunk li)).
        { rewrite U. destruct (li_chunk li) as [[c' k']|[mb n0']].
          - (first [ dand4 CL as Hc Hk Hn Hcl | destruct CL as (Hc & Hk & Hn & Hcl) ]). (first [ pose proof ((primary_layout sb c' k' (li_n li) Hc Hn Hcl)) as dR_97; dand3 dR_97 as L1 L2 _ | pose proof (primary_layout sb c' k' (li_n li) Hc Hn Hcl) as (L1 & L2 & _) ]). cbv zeta in *. cbn [chunk_lo chunk_hi alloc_beg user_of] in *. lia.
          - (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]). (first [ pose proof ((secondary_layout mb (li_n li) Hn)) as dR_99; dand4 dR_99 as S1 S2 S3 _ | pose proof (secondary_layout mb (li_n li) Hn) as (S1 & S2 & S3 & _) ]). cbn [chunk_lo chunk_hi alloc_beg user_of cs_map cs_n] in *. lia. }
        apply mapped_N; [kung_all; lia| right; lia| lia| exact MU0].
      + apply mapped_N; [kung_all; lia| right; lia| lia| exact MC].
  Qed.

  Ltac side_nodisj := repeat match goal with H : _ \/ _ |- _ => clear H end.
  Ltac side_one := multimatch goal with H : _ \/ _ |- _ =>
    repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H H' then fail else clear H' end; lia end.
  (* [comment removed for export] *)
  Ltac side_lbase e := lazymatch e with ?x + _ => side_lbase x | ?x - _ => side_lbase x | _ => e end.
  Ltac side_guided := lazymatch goal with |- ~ (?lo <= ?x < _) =>
    let b := side_lbase lo in
    lazymatch b with bv_unsigned _ => fail | _ => idtac end;
    lazymatch goal with Ha : ?l <= x < _ |- _ => let ba := side_lbase l in
      multimatch goal with H : ?P \/ _ |- _ =>
        lazymatch P with context [ba] => idtac end;
        repeat match goal with H' : _ \/ _ |- _ => tryif constr_eq H H' then fail else clear H' end; lia end end end.
  #[using="P_mu2 P_dr IDR B1R LKS id b1' ks md0 WF0 CEIL ENOUGH NR AI spa n md m Clg"] Lemma depot_P : depot_repr_ LPA AL_pasan (a_pl A) (fst (depot_putC D key)) v'.
  Proof.
    unfold depot_repr_. cbn [depot_rep DepotRepL]. eapply depot_repL_agree; [exact P_dr|].
    intros a Ha. pose proof GEO as G. geop. pose proof alloc_ceiling_val as CE. pose proof (zr_word spa) as SPR; unfold inr64 in SPR.
    (first [ pose proof ((hit_sep A m md AI)) as dR_100; dand8 dR_100 as _ _ _ N1 F1 N2 F2 _ | destruct (hit_sep A m md AI) as (_ & _ & _ & N1 & F1 & N2 & F2 & _) ]). unfold apart in N1, F1, N2, F2. change (a_sb A) with sb in N1, F1.
    unfold depot_foot in Ha. unfold Yr.ACells.depot_foot in Ha. cbn [al_stackStore al_depot_nodes_map1 AL_pasan] in Ha. unfold kDepotNodesL1 in Ha.
    apply P_mu2. unfold alloc_hit_W2. cbn [outside]. rewrite !unsigned_lit by (kung_all; lia).
    pose proof (Z.le_min_l n 4096). pose proof (Z.min_glb n 4096 1 ltac:(lia) ltac:(lia)). pose proof (Z.le_min_r (n mod 8) 1).
    kung_all. destruct Ha as [Ha|[Ha|Ha]]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ side_guided | solve [side_nodisj; lia] | side_one | lia ].
  Qed.

  #[using="P_she P_shz IDR B1R LKS id b1' ks R WF0 MU CEIL ENOUGH NR AI spa md m Clg"] Lemma shadow_P : shadow_repr_ LPA sb (ref_reg (a_reg A) c KK) (ref_cache (a_cache A) c fetched) lm' (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof ((ar_shadow _ _ _ _ _ R)) as dR_101; dand6 dR_101 as S1 S2 S3 S4 S5 S6 | pose proof (ar_shadow _ _ _ _ _ R) as (S1 & S2 & S3 & S4 & S5 & S6) ]). (first [ pose proof ((sb_facts A WF0)) as dR_102; dand3 dR_102 as _ SBA _ | pose proof (sb_facts A WF0) as (_ & SBA & _) ]). pose proof GEO as G.
    (first [ pose proof ((wfR A WF0)) as dR_103; dand3 dR_103 as WR _ _ | destruct (wfR A WF0) as (WR & _ & _) ]). (first [ pose proof ((wfC A WF0)) as dR_104; dand3 dR_104 as WC _ _ | destruct (wfC A WF0) as (WC & _ & _) ]). (first [ pose proof ((wfQ A WF0)) as dR_105; dand3 dR_105 as Q1 Q2 _ | destruct (wfQ A WF0) as (Q1 & Q2 & _) ]). (first [ pose proof ((wfV A WF0)) as dR_106; dand3 dR_106 as V1 _ _ | destruct (wfV A WF0) as (V1 & _ & _) ]).
    assert (QWF : forall e, In e (q_entries (a_qthread A ++ a_qglobal A)) -> wf_qentry_ (a_reg A) (a_sec A) e).
    { intros e He. unfold q_entries in He. apply in_flat_map in He as (b & Hb & Heb). apply in_app_iff in Hb as [Hb|Hb];
      [pose proof (proj1 (Forall_forall _ _) Q1 b Hb) as WB| pose proof (proj1 (Forall_forall _ _) Q2 b Hb) as WB];
      (first [ dand3 WB as _ _ WB | destruct WB as (_ & _ & WB) ]); exact (proj1 (Forall_forall _ _) WB e Heb). }
    assert (BWF : forall k, In k (batch_indices A) -> 0 <= k < carved_count A kQuarantineBatchClass).
    { intros k Hk. unfold batch_indices, batch_indices_ in Hk. apply in_map_iff in Hk as (b & <- & Hb).
      assert (WB : wf_batch_ (a_reg A) (a_sec A) b).
      { apply in_app_iff in Hb as [Hb|Hb]; [exact (proj1 (Forall_forall _ _) Q1 b Hb)| exact (proj1 (Forall_forall _ _) Q2 b Hb)]. }
      (first [ dand3 WB as _ K _ | destruct WB as (_ & K & _) ]). exact K. }
    (first [ pose proof ((ref_partition A m md n AI NR ENOUGH)) as dR_109; dand4 dR_109 as NCa NV NQ NB | destruct (ref_partition A m md n AI NR ENOUGH) as (NCa & NV & NQ & NB) ]).
    pose proof NLAST as NC. (first [ dand3 NODUP as NDr NDf DISJ | destruct NODUP as (NDr & NDf & DISJ) ]). (first [ dand3 FET as KF KL FNE | destruct FET as (KF & KL & FNE) ]).
    (* [comment removed for export] *)
    assert (SECD : forall sc, In sc (sr_chunks (a_sec A)) -> cs_map sc + map_size (cs_n sc) <= AB \/ AB + class_size c <= cs_map sc).
    { intros sc Hin. destruct (In_nth_error' _ _ Hin) as [j Hj]. pose proof (bm_nth_sec A j sc Hj) as Ej.
      destruct (SEP6 (15 + j)%nat _ _ Ej ltac:(lia)) as (X1 & _). pose proof IN6 as I6. unfold apart in X1. kung_all. lia. }
    split; [|split; [|split; [|split; [|split]]]].
    - (* [comment removed for export] *)
      intros c' k Hc ST.
      assert (ST0 : p_free_ (a_reg A) c' k \/ p_cached_ (a_cache A) c' k \/ p_batch_ (a_qthread A) (a_qglobal A) c' k).
      { destruct ST as [F|[C|B]]; [| | right; right; exact B].
        - left. unfold p_free_, ref_reg in F |- *. destruct (Z.eqb_spec c' c) as [->|NE']; [| exact F]. cbn [rg_free] in F. exact (ref_in_rest _ _ _ F).
        - unfold p_cached_, ref_cache in C. destruct (Z.eqb_spec c' c) as [->|NE']; [| right; left; exact C]. cbn [pk_chunks] in C.
          left. unfold p_free_. apply (ref_in_fetched _ KK). apply removelast_incl. exact C. }
      apply CHK; [exact Hc| | | unfold pshadow_free, fa8; rewrite repeat_length; pose proof (class_size_range c' Hc); rewrite Z2Nat.id by (apply Z.div_pos; lia); reflexivity| exact (S1 c' k Hc ST0)].
      + destruct ST0 as [F|[C|[E B]]].
        * (first [ pose proof ((WR c' Hc)) as dR_112; dand10 dR_112 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F).
        * (first [ pose proof ((WC c' ltac:(lia))) as dR_113; dand4 dR_113 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C).
        * subst c'. apply BWF. exact B.
      + destruct (Z.eq_dec c' c) as [->|]; [right| left; assumption]. intros ->.
        destruct ST as [F|[C|B]]; [| | exact (NB B)].
        * unfold p_free_, ref_reg in F. rewrite Z.eqb_refl in F. cbn [rg_free] in F. exact (DISJ _ F KF).
        * unfold p_cached_, ref_cache in C. rewrite Z.eqb_refl in C. cbn [pk_chunks] in C. exact (NC C).
    - (* [comment removed for export] *)
      intros u0 c' k n1 Hl. destruct (decide (u0 = u)) as [->|NEu].
      + rewrite lookup_insert_eq in Hl. injection Hl as <- <- <-.
        (first [ pose proof (USH) as dR_114; dand6 dR_114 as U1 U2 U3 U4 U5 U6 | pose proof USH as (U1 & U2 & U3 & U4 & U5 & U6) ]). pose proof (free_shadow A m md n kidx AI NR KIN) as SH. change (a_sb A) with sb in SH.
        set (fa := Z_to_bv 8 kAsanHeapLeftRedzoneMagic) in *.
        assert (PIECE : forall i k, 0 <= i -> 0 <= k -> i + k <= class_size c / 8 ->
                  (sh AB + i + k <= shU \/ shU + (n + 7) / 8 <= sh AB + i) -> bytes_at rsegs v' (sh AB + i) (repeat fa (Z.to_nat k))).
        { intros i k Hi Hk Hik D.
          assert (B0 : bytes_at rsegs v (sh AB + i) (repeat fa (Z.to_nat k))).
          { replace (sh AB + i) with (sh AB + Z.of_nat (Z.to_nat i)) by lia.
            rewrite <- (repeat_mid fa (Z.to_nat (class_size c / 8)) (Z.to_nat i) (Z.to_nat k)) by lia.
            apply bytes_at_mid; [exact SH| rewrite repeat_length; lia]. }
          eapply bytes_at_agree_gen; [exact B0|]. rewrite repeat_length. intros j Hj. apply AGhs; [| lia].
            unfold heap_shadow, heap_shadow_. left. exists c. split; [exact CR|]. cbv zeta. change (p_sb (a_pl A)) with sb.
            (first [ pose proof ((region_piece_bounds A c WF0 CR)) as dR_115; dand12 dR_115 as Q1' Q2' Q3' Q4' Q5' Q6' Q7' Q8' Q9' Q10' Q11' Q12' | destruct (region_piece_bounds A c WF0 CR) as (Q1' & Q2' & Q3' & Q4' & Q5' & Q6' & Q7' & Q8' & Q9' & Q10' & Q11' & Q12') ]).
            change (a_sb A) with sb in *.
            pose proof (sh_mono (region_beg sb c) AB ltac:(lia)).
            pose proof (sh_mono (AB + class_size c) (region_beg sb c + rg_mapped_user (a_reg A c)) ltac:(lia)) as M2.
            rewrite (sh_add (region_beg sb c) (rg_mapped_user (a_reg A c)) ltac:(apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact Q9']) Q10') in M2. lia. }
        unfold pshadow_live, fa8. rewrite (proj2 (proj2 (user_size_pos n ltac:(lia))) ltac:(lia)). fold fa.
        pose proof (shpat_length n ltac:(lia)) as SPL. pose proof (div8_ceil n ltac:(lia)) as DC. pose proof (Z.le_min_r (n mod 8) 1).
        pose proof (rz_size_range n).
        apply bytes_at_app. split.
        { replace (sh AB) with (sh AB + 0) by lia. apply PIECE; lia. }
        rewrite repeat_length, Z2Nat.id by lia. rewrite U2.
        apply bytes_at_app. split.
        { (* [comment removed for export] *)
          unfold shpat. apply bytes_at_app. split; [exact P_shz|]. rewrite repeat_length, Z2Nat.id by lia.
          destruct (Z.eqb_spec (n mod 8) 0) as [E0|E0].
          - apply bytes_at_nil. pose proof (bytes_at_bound _ _ _ _ P_shz). rewrite repeat_length in *. kung_all. lia.
          - destruct (P_she E0) as [[_ B] _]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
            replace (shU + n / 8) with (AB / 8 + rz_size n / 8 + n / 8 + kShadowOffset) by (kung_all; lia). exact B. }
        replace (shU + Z.of_nat (length (shpat n))) with (sh AB + (rz_size n / 8 + (n + 7) / 8)) by lia.
        apply PIECE; lia.
      + rewrite lookup_insert_ne in Hl by congruence. (first [ pose proof ((V1 u0 _ Hl)) as dR_116; dand5 dR_116 as N U N2 Hc Hk | pose proof (V1 u0 _ Hl) as (N & U & N2 & Hc & Hk) ]). cbn [li_n li_chunk] in *.
        apply CHK; [rewrite Hc; apply class_of_range; lia| exact Hk| | apply pshadow_live_length; [lia| exact Hc]| exact (S2 u0 c' k n1 Hl)].
        destruct (Z.eq_dec c' c) as [->|]; [right| left; assumption]. intros ->.
        exact (rf_not_live A m md n AI NR ENOUGH u0 _ Hl eq_refl).
    - (* [comment removed for export] *)
      intros c' k n1 He. (first [ pose proof ((QWF _ He)) as dR_117; dand4 dR_117 as N N2 Hc Hk | pose proof (QWF _ He) as (N & N2 & Hc & Hk) ]). cbn [qe_n qe_chunk] in *.
      apply CHK; [rewrite Hc; apply class_of_range; lia| exact Hk| | apply pshadow_quar_length; [lia| exact Hc]| exact (S3 c' k n1 He)].
      destruct (Z.eq_dec c' c) as [->|]; [right| left; assumption]. intros ->.
      apply (rf_not_quar A m md n AI NR ENOUGH). unfold quarantined_chunks_. apply in_map_iff. exists (QE (ChP (CP c kidx)) n1). split; [reflexivity| exact He].
    - (* [comment removed for export] *)
      intros c' Hc. destruct (S4 c' Hc) as [X Y]. pose proof (region_piece_bounds A c' WF0 Hc) as RB. cbv zeta in *. change (a_sb A) with sb in *.
      rewrite !ref_reg_mu, !ref_reg_au, !ref_reg_mfa.
      (first [ dand12 RB as R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 | destruct RB as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12) ]).
      assert (RBM : region_beg sb c' mod 8 = 0) by (apply (mod0_down _ 0x10000 8); [exists 8192; reflexivity| exact R9]).
      assert (RD : c' <> c -> region_beg sb c' + kRegionSize <= region_beg sb c \/ region_beg sb c + kRegionSize <= region_beg sb c').
      { intros NC'. exact (regions_disjoint sb c' c NC' ltac:(lia) ltac:(lia)). }
      pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) R10) as E10. pose proof (Z_div_exact_full_2 _ 8 ltac:(lia) R11) as E11.
      assert (DQ : (rg_mapped_user (a_reg A c') - rg_allocated_user (a_reg A c')) / 8 = rg_mapped_user (a_reg A c') / 8 - rg_allocated_user (a_reg A c') / 8).
      { symmetry. apply (Z.div_unique_exact _ _ _); [lia|]. lia. }
      split.
      + eapply fill_at_agree; [exact X|]. intros i Hi. apply AGhs.
        * unfold heap_shadow, heap_shadow_. left. exists c'. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with sb.
          rewrite (sh_add _ _ RBM R11). lia.
        * apply (sh_apart (region_beg sb c' + rg_allocated_user (a_reg A c')) (rg_mapped_user (a_reg A c') - rg_allocated_user (a_reg A c'))); [lia| | lia].
          destruct (Z.eq_dec c' c) as [->|NC']; [right; lia|]. destruct (RD NC'); kung_all; lia.
      + eapply fill_at_agree; [exact Y|]. intros i Hi. apply AGhs.
        * unfold heap_shadow, heap_shadow_. right. left. exists c'. split; [exact Hc|]. cbv zeta. change (p_sb (a_pl A)) with sb. lia.
        * apply (sh_apart (region_beg sb c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c'))); [lia| | lia].
          destruct (Z.eq_dec c' c) as [->|NC']; [right; kung_all; lia|]. destruct (RD NC'); kung_all; lia.
    - (* [comment removed for export] *)
      intros u0 mb n1 Hl. destruct (decide (u0 = u)) as [->|NEu]; [rewrite lookup_insert_eq in Hl; discriminate|].
      rewrite lookup_insert_ne in Hl by congruence. (first [ pose proof ((V1 u0 _ Hl)) as dR_119; dand5 dR_119 as N U N2 _ Hin | pose proof (V1 u0 _ Hl) as (N & U & N2 & _ & Hin) ]). cbn [li_n li_chunk] in *.
      (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_120; dand5 dR_120 as _ _ B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (_ & _ & B3 & B4 & B5) ]). cbn [cs_map cs_n] in *.
      eapply bytes_at_agree_gen; [exact (S5 u0 mb n1 Hl)|]. rewrite sshadow_live_length by lia. intros i Hi. apply AGhs.
      + unfold heap_shadow, heap_shadow_. right. right. exists (CS mb n1). split; [exact Hin|]. cbn [cs_map cs_n]. lia.
      + apply (sh_apart mb (map_size n1)); [pose proof (map_size_room n1); unfold kPageSize in *; lia| exact (SECD _ Hin)| lia].
    - (* [comment removed for export] *)
      intros mb n2 n1 He. pose proof (S6 mb n2 n1 He) as B. (first [ pose proof ((QWF _ He)) as dR_121; dand4 dR_121 as N N2 E0 Hin | pose proof (QWF _ He) as (N & N2 & E0 & Hin) ]). cbn [qe_n qe_chunk] in *. subst n2.
      (first [ pose proof ((sec_chunk_bounds A _ WF0 Hin)) as dR_122; dand5 dR_122 as _ _ B3 B4 B5 | pose proof (sec_chunk_bounds A _ WF0 Hin) as (_ & _ & B3 & B4 & B5) ]). cbn [cs_map cs_n] in *.
      eapply bytes_at_agree_gen; [exact B|]. rewrite sshadow_quar_length by lia. intros i Hi. apply AGhs.
      + unfold heap_shadow, heap_shadow_. right. right. exists (CS mb n1). split; [exact Hin|]. cbn [cs_map cs_n]. lia.
      + apply (sh_apart mb (map_size n1)); [pose proof (map_size_room n1); unfold kPageSize in *; lia| exact (SECD _ Hin)| lia].
  Qed.

  #[using="P_mu2 P_dr P_she P_shz P_lch P_hdr IDR B1M B1R P_nf P_mx P_pc KSF LKS id b1' ks md0 R WF0 NN MU CEIL ENOUGH CI NR AI spa md m"] Theorem ref_arepr : @arepr _ DepotRepL LPA AL_pasan [] (refA A n key) v'.
  Proof.
    unfold refA. cbv zeta.
    constructor; cbn [a_pl a_sb a_reg a_cache a_cache_inited a_livemap a_qthread a_qglobal a_sec a_depot a_ia_inited a_fhint a_fs a_fframes].
    - exact consts_P. - exact locks_P. - exact regions_P. - exact cache_P. - exact live_P. - exact quar_P. - exact sec_P.
    - exact depot_P. - exact ia_P. - exact fsbase_P. - exact fsptrs_P. - exact fsflags_P. - exact maps_P. - exact shadow_P.
  Qed.
  End Cells.
End ReprPost.
