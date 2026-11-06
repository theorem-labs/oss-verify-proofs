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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState ADepotM LayoutPA AInv ALogic1 ALogic2 ALogic3 ALogic ARtStmts AMallocI AMalmys ATransp ATranspH.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeB1 AFreeB2 AFreeB3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AQWf ABudget ASecImg AFreeB6 ANodijx APgGeo AFreeX1 AFreeX2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ADepotM OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ALogic OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMallocI OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMalmys OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATransp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATranspH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf.AQOps OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AQWf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ABudget OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ASecImg OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeB6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.APgGeo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeX2.
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
Definition const_okD (c : Z * list byte) : bool :=
  let lo := fst c in let hi := fst c + Z.of_nat (length (snd c)) in
  ((hi <=? 0x187288) || (0x5d72a8 <=? lo)) && ((hi <=? 0xb65c0) || (0x1375f0 <=? lo)) && ((hi <=? 0x144e48) || (0x144e4c <=? lo)) &&
  ((hi <=? 0xb1dd0) || (0xb1dd9 <=? lo)) && ((hi <=? 0xb1de8) || (0xb1df8 <=? lo)) && ((hi <=? 0xb2018) || (0xb2028 <=? lo)) &&
  ((hi <=? 0xb2000) || (0xb2004 <=? lo)).
Definition sec_pad : Z * list byte := (0xb2001, [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]).
Lemma pa_consts_okD : forallb (fun c => const_okD c || bool_decide (c = ia_pad) || bool_decide (c = sec_pad)) pa_consts = true.
Proof. vm_compute. reflexivity. Qed.

Lemma u64s_entry : forall (mm : mem) a ws i w, bytes_at rsegs mm a (u64s ws) -> nth_error ws i = Some w ->
  bytes_at rsegs mm (a + 8 * Z.of_nat i) (le8 w).
Proof.
  intros mm a ws. revert a. induction ws as [|x ws IH]; intros a i w B E; [destruct i; discriminate|].
  cbn [u64s] in B. apply bytes_at_app in B as [B0 B1]. rewrite length_le8 in B1. destruct i as [|i].
  - injection E as ->. rewrite Z.mul_0_r, Z.add_0_r. exact B0.
  - cbn in E. replace (a + 8 * Z.of_nat (S i)) with (a + Z.of_nat 8 + 8 * Z.of_nat i) by lia. exact (IH _ i w B1 E).
Qed.

Section ReprS.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (i : nat) (v' : mem) (wlo whi : Z).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQB : kQuarantineMaxSize < n0.
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

  Let NQ' : kMaxPrimaryUser < n0. Proof. unfold kQuarantineMaxSize, kMaxPrimaryUser in *. lia. Qed.
  Let W : WF A. Proof. exact (ai_wf _ _ _ _ _ _ _ AI). Qed.
  Let AR : WF A /\ @arepr _ DepotRepL LPA AL_pasan [] A v. Proof. exact (conj W (ai_repr _ _ _ _ _ _ _ AI)). Qed.
  Let S0 : In (CS h n0) chunks. Proof. exact (sk_In A m md p n0 AI HL NQ'). Qed.

  (* [comment removed for export] *)
  Definition holeD (a : Z) : Prop := (h <= a < h + msz) \/ (pbeg <= a < pend).
  Definition EXC (a : Z) : Prop :=
       (wlo <= a < whi)
    \/ (thr + 2824 <= a < thr + 2856) \/ (thr + 2888 <= a < thr + 2904)
    \/ (0x187288 <= a < 0x5d72a8) \/ (p_nodes0 P <= a < p_nodes0 P + kDepotNodesBlock) \/ (p_frames0 P <= a < p_frames0 P + kStackStoreBlockBytes)
    \/ (a_ia_inited A = false /\ ia_blk a)
    \/ (0xb1dd0 <= a < 0xb1dd9) \/ (0xb1de8 <= a < 0xb1df8) \/ (0xb2018 <= a < 0xb2028)
    \/ (pa + 8 * Z.of_nat i <= a < pa + 8 * Z.of_nat i + 8) \/ (hla + 24 <= a < hla + 32)
    \/ (h <= a < h + msz) \/ (sh h <= a < sh h + msz / 8)
    \/ (0xb2000 <= a < 0xb2004).   (* [comment removed for export] *)
  Hypothesis AG : forall a, 0 <= a < 2^64 -> ~ EXC a -> v' (wz a) = v (wz a).
  Hypothesis NNH : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> ~ holeD a -> v (wz a) <> None -> v' (wz a) <> None.

  (* [comment removed for export] *)
  #[using="AR W AI md m A Clg"] Lemma hole_eq : forall a, ATranspH.hole (CS h n0) pbeg pend a <-> holeD a.
  Proof. intros a. unfold ATranspH.hole, holeD. cbn [cs_map cs_n]. tauto. Qed.
  Let SLO : sh (cs_map (CS h n0)) <= pbeg.
  Proof. cbn [cs_map]. pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & _). lia. Qed.
  Let SHI : pend <= sh (cs_map (CS h n0) + map_size (cs_n (CS h n0))).
  Proof. cbn [cs_map cs_n]. (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_1; dand14 dR_1 as _ _ _ _ _ G6 _ _ _ _ _ _ SHA _ | pose proof (a8_geo A m md p n0 AI HL NQB) as (_ & _ & _ & _ & _ & G6 & _ & _ & _ & _ & _ & _ & SHA & _) ]). rewrite SHA. lia. Qed.
  Let SHI8 : pend mod 8 = 0.
  Proof. (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_2; dand12 dR_2 as _ _ _ _ _ _ _ _ _ _ M3 _ | pose proof (a8_geo A m md p n0 AI HL NQB) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & M3 & _) ]). apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact M3]. Qed.
  Let NNH' : forall a, 0 <= a -> (a + 1 <= 0x10000 \/ 0x60a000 <= a) -> a < 2^64 -> ~ ATranspH.hole (CS h n0) pbeg pend a -> v (wz a) <> None -> v' (wz a) <> None.
  Proof. intros a H0 H1 H2 NH. apply NNH; [exact H0| exact H1| exact H2|]. intros X. apply NH. apply (proj2 (hole_eq a)). exact X. Qed.

  (* [comment removed for export] *)
  #[using="W NQ' NTH NQB HL AI md m"] Lemma bnds :
    (aobj thr 4096 /\ aobj (p_ctx P) 0x10000 /\ aobj (p_nodes0 P) kDepotNodesBlock /\ aobj (p_frames0 P) kStackStoreBlockBytes /\
     aobj (p_fs P) kFakeStackBytes /\ aobj (p_dtls P) 4096 /\ aobj pa kPtrArrayReserve) /\
    (aobj h msz /\ 0x60a000 <= h /\ h + msz <= alloc_ceiling /\ 8 * nch <= kPtrArrayReserve /\ 0 <= Z.of_nat i < nch) /\
    (aobj hla (map_size (cs_n (sec_last A))) /\ 0x60a000 <= hla /\ 4096 + 32 <= map_size (cs_n (sec_last A))) /\
    (0x7fff8000 + 0x200 <= sh h /\ sh h + msz / 8 <= kHighMemBeg /\ sh (h + msz) = sh h + msz / 8).
  Proof.
    pose proof (place_facts A W) as PF. cbv zeta in PF.
    (first [ dand13 PF as (T1 & _) (C1 & _) (N1 & _) (F1 & _) (S1 & _) _ _ _ _ _ (D1 & _) (PA1 & _) _ | destruct PF as ((T1 & _) & (C1 & _) & (N1 & _) & (F1 & _) & (S1 & _) & _ & _ & _ & _ & _ & (D1 & _) & (PA1 & _) & _) ]).
    (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_4; dand11 dR_4 as HLO HAL MSZ MSZAL HHI PH PIN N6 NR H5 PM | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & HAL & MSZ & MSZAL & HHI & PH & PIN & N6 & NR & H5 & PM) ]).
    (first [ pose proof ((sk_pa A m md p n0 AI HL NQ')) as dR_5; dand5 dR_5 as _ _ _ _ LE | pose proof (sk_pa A m md p n0 AI HL NQ') as (_ & _ & _ & _ & LE) ]). pose proof (sk_i A p n0 i NTH) as [IR _].
    (first [ pose proof ((sk_last A m md p n0 AI HL NQ')) as dR_6; dand3 dR_6 as _ INL _ | pose proof (sk_last A m md p n0 AI HL NQ') as (_ & INL & _) ]). (first [ pose proof ((sk_chunk A m md AI _ INL)) as dR_7; dand6 dR_7 as L1 L2 L3 L4 L5 _ | pose proof (sk_chunk A m md AI _ INL) as (L1 & L2 & L3 & L4 & L5 & _) ]).
    (first [ pose proof ((sk_shr A m md p n0 AI HL NQ')) as dR_8; dand4 dR_8 as SHA _ _ SIDE | pose proof (sk_shr A m md p n0 AI HL NQ') as (SHA & _ & _ & SIDE) ]).
    split; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; apply (proj1 (aobj_app_rangeA _ _)); assumption|].
    split; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption; lia|]. split; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption|].
    unfold kHighMemBeg, kHighShadowMapBeg, kLowShadowBeg, kShadowGapBeg in *. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac exc14 X := unfold EXC, ia_blk in X;
    destruct X as [X|[X|[X|[X|[X|[X|[[Xia X]|[X|[X|[X|[X|[X|[X|[X|X]]]]]]]]]]]]]].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="AG W NQ' WLO NTH NQB HL AI whi wlo i n0 p md"] Lemma AGimg : forall a, 0x10000 <= a < 0x60a000 -> ~ (0x187288 <= a < 0x5d72a8) -> ~ ia_blk a ->
    ~ (0xb1dd0 <= a < 0xb1dd9) -> ~ (0xb1de8 <= a < 0xb1df8) -> ~ (0xb2018 <= a < 0xb2028) -> ~ (0xb2000 <= a < 0xb2004) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1 X2 X3 X4 X5 X6. (first [ pose proof (bnds) as dR_9; dand4 dR_9 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof (aobj_facts _ _ N) as N'. pose proof (aobj_facts _ _ F) as F'. pose proof (aobj_facts _ _ PA) as PA'.
    pose proof alloc_ceiling_val as CE. unfold ia_blk in X2.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO CE. lia. - clear -Ha X T'. lia. - clear -Ha X T'. lia. - clear -X X1. lia. - clear -Ha X N'. kung_all. lia. - clear -Ha X F'. kung_all. lia.
    - clear -X X2. lia. - clear -X X3. lia. - clear -X X4. lia. - clear -X X5. lia. - clear -Ha X PA' LE IR. kung_all. lia. - clear -Ha X HL5. lia.
    - clear -Ha X H5. lia. - clear -Ha X R1. lia. - clear -X X6. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W NQ' WLO NTH NQB HL AI whi wlo i n0 p md"] Lemma AGthr : forall a, thr <= a < thr + 4096 -> ~ (thr + 2824 <= a < thr + 2856) -> ~ (thr + 2888 <= a < thr + 2904) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1 X2. (first [ pose proof (bnds) as dR_10; dand4 dR_10 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((sk_sep_pa A m md AI)) as dR_11; dand5 dR_11 as Dpt _ _ _ _ | pose proof (sk_sep_pa A m md AI) as (Dpt & _ & _ & _ & _) ]). (first [ pose proof ((sk_sep_h A m md p n0 AI HL NQ' i NTH)) as dR_12; dand3 dR_12 as _ Dht _ | pose proof (sk_sep_h A m md p n0 AI HL NQ' i NTH) as (_ & Dht & _) ]).
    (first [ pose proof ((sk_hl A m md p n0 AI HL NQ' i NTH)) as dR_13; dand9 dR_13 as _ _ _ _ _ _ _ Dlt _ | pose proof (sk_hl A m md p n0 AI HL NQ' i NTH) as (_ & _ & _ & _ & _ & _ & _ & Dlt & _) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_14; dand8 dR_14 as _ _ _ _ _ Dn0t Df0t _ | pose proof (hit_sep A m md AI) as (_ & _ & _ & _ & _ & Dn0t & Df0t & _) ]). unfold apart, AMallocA.apart in *.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO T'. lia. - clear -X X1. lia. - clear -X X2. lia. - clear -Ha X T'. lia. - clear -Ha X Dn0t. kung_all. lia. - clear -Ha X Df0t. kung_all. lia.
    - clear -Ha X T'. lia. - clear -Ha X T'. lia. - clear -Ha X T'. lia. - clear -Ha X T'. lia. - clear -Ha X Dpt LE IR. kung_all. lia. - clear -Ha X Dlt. lia.
    - clear -Ha X Dht. lia. - clear -Ha X T' R1 R2. kung_all. lia. - clear -Ha X T'. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W NQ' WLO NTH NQB HL AI whi wlo i md"] Lemma AGapp : forall b k a, 4096 <= b -> b + k <= alloc_ceiling -> (b + k <= 0x10000 \/ 0x60a000 <= b) ->
    (b + k <= kLowShadowMapBeg \/ kHighMemBeg <= b) ->
    apart b k thr 4096 -> apart b k (p_nodes0 P) kDepotNodesBlock -> apart b k (p_frames0 P) kStackStoreBlockBytes ->
    apart b k pa kPtrArrayReserve -> apart b k (hla + 24) 8 -> apart b k h msz ->
    b <= a < b + k -> v' (wz a) = v (wz a).
  Proof.
    intros b k a B1 B2 B3 B4 D1 D2 D3 D4 D5 D6 Ha. (first [ pose proof (bnds) as dR_15; dand4 dR_15 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof alloc_ceiling_val as CE. unfold apart in *.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO B2. lia. - clear -X Ha D1. lia. - clear -X Ha D1. lia. - clear -Ha X B3. lia. - clear -Ha X D2. lia. - clear -Ha X D3. lia.
    - clear -Ha X B3. lia. - clear -Ha X B3. lia. - clear -Ha X B3. lia. - clear -Ha X B3. lia. - clear -Ha X D4 LE IR. kung_all. lia. - clear -Ha X D5. lia.
    - clear -Ha X D6. lia. - clear -Ha X B4 R1 R2. kung_all. lia. - clear -Ha X B3. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W NQ' WLO NTH NQB HL AI whi wlo i md"] Lemma AGsh : forall a, kLowShadowMapBeg <= a < kHighMemBeg -> ~ (sh h <= a < sh h + msz / 8) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1. (first [ pose proof (bnds) as dR_16; dand4 dR_16 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
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
  #[using="AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo i md"] Lemma AGchunk : forall ch a, carved A ch -> ch <> ChS (CS h n0) ->
    chunk_lo sb ch <= a < chunk_hi sb ch -> ~ (hla + 24 <= a < hla + 32) -> v' (wz a) = v (wz a).
  Proof.
    intros ch a Cc NE Ha NI. (first [ pose proof (bnds) as dR_17; dand4 dR_17 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((carved_range A v AR ch Cc)) as dR_18; dand3 dR_18 as CR1 CR2 CR3 | pose proof (carved_range A v AR ch Cc) as (CR1 & CR2 & CR3) ]). pose proof (carved_app A v AR ch Cc) as CA. apply app_rangeA_arith in CA. (first [ dand5 CA as _ _ _ _ CA | destruct CA as (_ & _ & _ & _ & CA) ]).
    pose proof (carved_apart_thr A v AR ch Cc) as Dt. pose proof (carved_apart_n0 A v AR ch Cc) as Dn. pose proof (carved_apart_f0 A v AR ch Cc) as Df.
    pose proof (carved_apart_pa A v AR ch Cc) as Dp. pose proof (carved_disjoint A v AR ch (ChS (CS h n0)) Cc S0 NE) as Dm. cbn [chunk_lo chunk_hi] in Dm.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO CR2. lia. - clear -Ha X Dt. lia. - clear -Ha X Dt. lia. - clear -Ha X CR1. lia. - clear -Ha X Dn. lia. - clear -Ha X Df. lia.
    - clear -Ha X CR1. lia. - clear -Ha X CR1. lia. - clear -Ha X CR1. lia. - clear -Ha X CR1. lia. - clear -Ha X Dp LE IR. kung_all. lia. - clear -X NI. lia.
    - clear -Ha X Dm. lia. - clear -Ha X CA R1 R2. kung_all. lia. - clear -Ha X CR1. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W NQ' WLO NTH NQB HL AI whi wlo n0 p md"] Lemma AGpa : forall a, pa <= a < pa + 8 * nch -> ~ (pa + 8 * Z.of_nat i <= a < pa + 8 * Z.of_nat i + 8) -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha X1. (first [ pose proof (bnds) as dR_20; dand4 dR_20 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ PA) as PA'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((sk_sep_pa A m md AI)) as dR_21; dand5 dR_21 as Dpt Dpc Dpn Dpf _ | pose proof (sk_sep_pa A m md AI) as (Dpt & Dpc & Dpn & Dpf & _) ]). pose proof (sk_sep_h A m md p n0 AI HL NQ' i NTH) as (Dhp & _).
    (first [ pose proof ((sk_hl A m md p n0 AI HL NQ' i NTH)) as dR_22; dand8 dR_22 as _ _ _ _ _ _ Dlp _ | pose proof (sk_hl A m md p n0 AI HL NQ' i NTH) as (_ & _ & _ & _ & _ & _ & Dlp & _) ]). unfold apart in *.
    apply AG; [lia|]. intros X. exc14 X.
    - clear -Ha X WLO PA' LE. kung_all. lia. - clear -Ha X Dpt LE. kung_all. lia. - clear -Ha X Dpt LE. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia.
    - clear -Ha X Dpn LE. kung_all. lia. - clear -Ha X Dpf LE. kung_all. lia.
    - clear -Ha X PA' LE. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia.
    - clear -X X1. lia. - clear -Ha X Dlp. lia.
    - clear -Ha X Dhp. lia. - clear -Ha X PA' LE R1 R2. kung_all. lia. - clear -Ha X PA' LE. kung_all. lia.
  Qed.

  (* [comment removed for export] *)
  Variables (D' : list (list Z)).
  Hypothesis PNSRT : rw_cells rsegs v' 0xb1dd0 [C8 (wz (nch - 1)); C1 (Z_to_bv 8 0)].
  Hypothesis PLCK : rw_cells rsegs v' 0xb2000 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz 0)].
  Hypothesis PARR : u64arr rsegs v' pa (upd (sec_words A) i (Z_to_bv 64 hla)).
  Hypothesis PHLC : hla = h \/ rw_cells rsegs v' hla [C8 (wz hla); C8 (wz (map_size (cs_n (sec_last A)))); C8 (wz (needed_size2 (cs_n (sec_last A)))); C8 (wz (Z.of_nat i))].
  Hypothesis PDR : depot_repL AL_pasan rsegs D' (p_nodes0 P) (p_frames0 P) v'.
  (* [comment removed for export] *)
  Hypothesis IAH : (a_ia_inited A = true /\ forall a, iafoot a -> v' (wz a) = v (wz a)) \/ ia_repr_ LPA AL_pasan true v'.
  Hypothesis IAL : u8_at rsegs v' (al_internal_alloc_inited AL_pasan + 1) 0.
  Hypothesis IAP : bytes_at rsegs v' 0x144e4a [Z_to_bv 8 0; Z_to_bv 8 0].

  #[warnings="-notation-for-abbreviation"] Local Notation A' := (freeS A p i D' true (dead2 p n0)).

  (* [comment removed for export] *)
  #[using="IAP PLCK AG AR W NQ' WLO NTH NQB HL AI whi wlo i n0 p md m Clg"] Lemma fs_consts : consts_repr_ LPA AL_pasan P v'.
  Proof.
    (first [ pose proof (bnds) as dR_23; dand4 dR_23 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof (aobj_facts _ _ C) as C'. pose proof (aobj_facts _ _ D) as D'f. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((sk_sep_pa A m md AI)) as dR_24; dand5 dR_24 as Dpt Dpc Dpn Dpf Dct | pose proof (sk_sep_pa A m md AI) as (Dpt & Dpc & Dpn & Dpf & Dct) ]). (first [ pose proof ((sk_sep_h A m md p n0 AI HL NQ' i NTH)) as dR_25; dand5 dR_25 as Dhp Dht Dhc Dhn Dhf | pose proof (sk_sep_h A m md p n0 AI HL NQ' i NTH) as (Dhp & Dht & Dhc & Dhn & Dhf) ]).
    (first [ pose proof ((sk_hl A m md p n0 AI HL NQ' i NTH)) as dR_26; dand11 dR_26 as _ _ _ _ _ _ Dlp Dlt Dlc Dln Dlf | pose proof (sk_hl A m md p n0 AI HL NQ' i NTH) as (_ & _ & _ & _ & _ & _ & Dlp & Dlt & Dlc & Dln & Dlf) ]).
    (first [ pose proof ((hit_sep A m md AI)) as dR_27; dand10 dR_27 as _ _ Dct' _ _ Dn0t Df0t Dn0c Df0c _ | pose proof (hit_sep A m md AI) as (_ & _ & Dct' & _ & _ & Dn0t & Df0t & Dn0c & Df0c & _) ]).
    apply (consts_P2 A v v' AR).
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
        (first [ pose proof ((bm_nth_fixed A)) as dR_28; dand15 dR_28 as _ E1 _ _ E4 _ _ E7 E8 _ _ _ _ _ E14 | pose proof (bm_nth_fixed A) as (_ & E1 & _ & _ & E4 & _ & _ & E7 & E8 & _ & _ & _ & _ & _ & E14) ]).
        pose proof (sk_last A m md p n0 AI HL NQ') as (EL & _). pose proof (bm_nth_sec A _ _ EL) as ELs. pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
        pose proof (bm_sep A _ _ _ _ _ _ W E14 E4 ltac:(lia)) as Y1. pose proof (bm_sep A _ _ _ _ _ _ W E14 E7 ltac:(lia)) as Y2.
        pose proof (bm_sep A _ _ _ _ _ _ W E14 E8 ltac:(lia)) as Y3. pose proof (bm_sep A _ _ _ _ _ _ W E14 E1 ltac:(lia)) as Y4.
        pose proof (bm_sep A _ _ _ _ _ _ W E14 ELs ltac:(lia)) as Y5. pose proof (bm_sep A _ _ _ _ _ _ W E14 Es ltac:(lia)) as Y6.
        unfold a_thr, a_nodes0, a_frames0, a_pa in *.
        apply (AGapp (p_dtls P) 4096 a); try (clear -Ha D'f; lia); unfold apart; clear -Ha Y1 Y2 Y3 Y4 Y5 Y6 HL4; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="AG W NQ' WLO NTH NQB HL AI whi wlo i n0 p md"] Lemma AGspace : forall a, sb <= a < sb + kSpaceSize + 4096 -> v' (wz a) = v (wz a).
  Proof.
    intros a Ha. (first [ pose proof ((sb_facts A W)) as dR_29; dand5 dR_29 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_30; dand10 dR_30 as E0 E1 _ _ E4 _ _ E7 E8 _ | pose proof (bm_nth_fixed A) as (E0 & E1 & _ & _ & E4 & _ & _ & E7 & E8 & _) ]). pose proof (sk_last A m md p n0 AI HL NQ') as (EL & _).
    pose proof (bm_nth_sec A _ _ EL) as ELs. pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
    pose proof (bm_sep A _ _ _ _ _ _ W E0 E4 ltac:(lia)) as Y1. pose proof (bm_sep A _ _ _ _ _ _ W E0 E7 ltac:(lia)) as Y2.
    pose proof (bm_sep A _ _ _ _ _ _ W E0 E8 ltac:(lia)) as Y3. pose proof (bm_sep A _ _ _ _ _ _ W E0 E1 ltac:(lia)) as Y4.
    pose proof (bm_sep A _ _ _ _ _ _ W E0 ELs ltac:(lia)) as Y5. pose proof (bm_sep A _ _ _ _ _ _ W E0 Es ltac:(lia)) as Y6.
    (first [ pose proof (bnds) as dR_31; dand4 dR_31 as _ _ (_ & _ & HL4) _ | pose proof bnds as (_ & _ & (_ & _ & HL4) & _) ]).
    unfold a_b6, a_sb, a_pa, a_thr, a_nodes0, a_frames0 in *.
    unfold a_sb in Ha. apply (AGapp (p_sb P) (kSpaceSize + 4096) a); unfold apart; try (clear -Ha HB6 RSB SCE CE; kung_all; lia).
    - clear -Y1 HB6 RSB. kung_all. lia. - clear -Y2 HB6 RSB. kung_all. lia. - clear -Y3 HB6 RSB. kung_all. lia.
    - clear -Y4 HB6 RSB. kung_all. lia. - clear -Y5 HB6 RSB HL4. kung_all. lia. - clear -Y6 HB6 RSB. kung_all. lia.
  Qed.

  #[using="IAL PLCK AG AR W NQ' WLO NTH NQB HL AI whi wlo i n0 p md m Clg"] Lemma fs_locks : locks_repr_ LPA AL_pasan P [] v'.
  Proof.
    (first [ pose proof ((sb_facts A W)) as dR_32; dand5 dR_32 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]).
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

  #[using="NNH' SHI8 SHI SLO NNH AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo i n0 p md m Clg"] Lemma fs_regions : forall c', 1 <= c' <= 30 -> region_repr_ LPA sb (a_reg A c') v' c'.
  Proof.
    intros c' Hc. pose proof (region_piece_bounds A c' W Hc) as RB. cbv zeta in RB.
    apply (region_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH' c' Hc). intros a Ha. unfold rfoot, region_info_addr, free_array_beg in Ha. change (p_sb (a_pl A)) with sb in *.
    apply AGspace. clear -Ha RB Hc. unfold kRegionInfoSize in *. kung_all. lia.
  Qed.

  #[using="NNH' SHI8 SHI SLO NNH AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo i n0 p md m Clg"] Lemma fs_cache : cache_repr_ LPA P (a_cache A) (a_cache_inited A) v'.
  Proof.
    pose proof bnds as ((T & _) & _). pose proof (aobj_facts _ _ T) as T'.
    apply (cache_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH'). intros c' Hc'.
    apply (cache_line_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH' (a_cache A) c' Hc' eq_refl).
    intros a Ha. offs_h Ha. cbv beta in Ha. apply AGthr; clear -Ha Hc' T'; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PHLC PARR NNH' SHI8 SHI SLO NNH AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo i n0 md m Clg"] Lemma fs_live : live_repr_ LPA sb (free_lm A p) v'.
  Proof.
    intros u li Hl. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NEu Hl].
    (first [ pose proof ((sk_live A m md p n0 AI HL NQ')) as dR_34; dex1 dR_34 as lip; dand4 dR_34 as Hlp _ Hcp _ | pose proof ((sk_live A m md p n0 AI HL NQ')) as dR_34; dand5 dR_34 as lip Hlp _ Hcp _ | destruct (sk_live A m md p n0 AI HL NQ') as (lip & Hlp & _ & Hcp & _) ]).
    assert (NE : li_chunk li <> ChS (CS h n0)) by (rewrite <- Hcp; exact (live_live_chunk A v AR u p li lip Hl Hlp ltac:(congruence))).
    (first [ pose proof ((ar_live _ _ _ _ _ (proj2 AR) u li Hl)) as dR_35; dand3 dR_35 as HR MU0 MC | destruct (ar_live _ _ _ _ _ (proj2 AR) u li Hl) as (HR & MU0 & MC) ]). pose proof alloc_ceiling_val as CE.
    pose proof (known_live A v AR u li Hl) as CL. pose proof (known_range A v AR _ _ CL) as RNG. pose proof (known_carved A v AR _ _ CL) as CC.
    destruct (wfV A W) as (V1 & _). (first [ pose proof ((V1 u li Hl)) as dR_36; dand3 dR_36 as Nn U _ | pose proof (V1 u li Hl) as (Nn & U & _) ]). pose proof (user_in A _ _ CL) as UR. rewrite <- U in UR.
    (first [ pose proof ((sk_last A m md p n0 AI HL NQ')) as dR_37; dand3 dR_37 as EL INL _ | pose proof (sk_last A m md p n0 AI HL NQ') as (EL & INL & _) ]).
    (* [comment removed for export] *)
    assert (HF : forall a, hdr_foot sb (li_chunk li) (li_n li) a -> ~ (hla + 24 <= a < hla + 32)).
    { intros a Ha X. pose proof (hdr_foot_in A _ _ a CL ltac:(left; exact Ha)) as IN.
      destruct (chunk_eq_dec (li_chunk li) (ChS (sec_last A))) as [E|NEL].
      - rewrite E in Ha. unfold hdr_foot in Ha. destruct (sec_last A) as [mbl nl] eqn:EQL. cbn [user_of alloc_beg cs_map] in Ha, X.
        unfold sec_user_beg, sec_alloc_beg, kPageSize in Ha. clear -Ha X. lia.
      - pose proof (carved_disjoint A v AR _ (ChS (sec_last A)) CC INL NEL) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl.
        (first [ pose proof (bnds) as dR_38; dand4 dR_38 as _ _ (_ & _ & HL4) _ | pose proof bnds as (_ & _ & (_ & _ & HL4) & _) ]). clear -IN Dl X HL4. lia. }
    split; [|split].
    - apply (hdr_P A v v'); [| exact HR]. intros a Ha. apply (AGchunk (li_chunk li) a CC NE); [| exact (HF a Ha)]. apply (hdr_foot_in A _ (li_n li)); [exact CL| left; exact Ha].
    - apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| right; lia| lia| | exact MU0]. intros x Hx. apply (hole_free_carved A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 (li_chunk li) x CC NE). lia.
    - apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| right; lia| lia| | exact MC]. intros x Hx. apply (hole_free_carved A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 (li_chunk li) x CC NE). lia.
  Qed.

  #[using="PHLC PARR NNH' SHI8 SHI SLO NNH AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo i n0 p md m Clg"] Lemma fs_quar : quarantine_repr_ LPA AL_pasan P (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof ((ar_quar _ _ _ _ _ (proj2 AR))) as dR_39; dand3 dR_39 as QT QG QR | pose proof (ar_quar _ _ _ _ _ (proj2 AR)) as (QT & QG & QR) ]). unfold quarantine_repr_. change (p_sb (a_pl A)) with sb in *.
    (first [ pose proof (bnds) as dR_40; dand4 dR_40 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((sk_last A m md p n0 AI HL NQ')) as dR_41; dand3 dR_41 as EL INL _ | pose proof (sk_last A m md p n0 AI HL NQ') as (EL & INL & _) ]).
    assert (AGb : forall b a, In b (a_qthread A ++ a_qglobal A) -> batch_addr sb b <= a < batch_addr sb b + kQuarantineBatchBytes -> v' (wz a) = v (wz a)).
    { intros b a Hb Ha. pose proof (batch_carved A v AR b Hb) as Cb.
      apply (AGchunk _ a Cb ltac:(discriminate)); [cbn [chunk_lo chunk_hi alloc_beg]; rewrite class_size_24; unfold batch_addr in Ha; exact Ha|].
      pose proof (carved_disjoint A v AR _ (ChS (sec_last A)) Cb INL ltac:(discriminate)) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl.
      cbn [chunk_lo chunk_hi alloc_beg] in Dl. rewrite class_size_24 in Dl. unfold batch_addr in Ha. clear -Ha Dl HL4. kung_all. lia. }
    split; [|split].
    - (first [ dand5 QT as X1 X2 X3 X4 BR | destruct QT as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P A v v' (thr + off_th_qcache) (a_qthread A) ltac:(intros a Ha; unfold off_th_qcache in Ha; apply AGthr; clear -Ha T'; lia) (conj X1 (conj X2 (conj X3 X4))))) as dR_43; dand4 dR_43 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P A v v' (thr + off_th_qcache) (a_qthread A) ltac:(intros a Ha; unfold off_th_qcache in Ha; apply AGthr; clear -Ha T'; lia) (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
      apply (batches_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH'); [intros b Hb; apply in_or_app; left; exact Hb| | exact BR].
      intros b a Hb Ha. apply (AGb b a); [apply in_or_app; left; exact Hb| exact Ha].
    - (first [ dand5 QG as X1 X2 X3 X4 BR | destruct QG as (X1 & X2 & X3 & X4 & BR) ]). unfold qcache_repr.
      (first [ pose proof ((qcache_head_P A v v' (al_instance AL_pasan + off_q_cache_list_size) (a_qglobal A) ltac:(intros a Ha; alc_h Ha; unfold off_q_cache_list_size in Ha; apply AGimg; unfold ia_blk; clear -Ha; lia) (conj X1 (conj X2 (conj X3 X4))))) as dR_45; dand4 dR_45 as Y1 Y2 Y3 Y4 | pose proof (qcache_head_P A v v' (al_instance AL_pasan + off_q_cache_list_size) (a_qglobal A) ltac:(intros a Ha; alc_h Ha; unfold off_q_cache_list_size in Ha; apply AGimg; unfold ia_blk; clear -Ha; lia) (conj X1 (conj X2 (conj X3 X4)))) as (Y1 & Y2 & Y3 & Y4) ]).
      split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3|]. split; [exact Y4|].
      apply (batches_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH'); [intros b Hb; apply in_or_app; right; exact Hb| | exact BR].
      intros b a Hb Ha. apply (AGb b a); [apply in_or_app; right; exact Hb| exact Ha].
    - intros e He. (first [ pose proof ((QR e He)) as dR_46; dand3 dR_46 as HR J MC | destruct (QR e He) as (HR & J & MC) ]).
      pose proof (known_quar A v AR e He) as CL. pose proof (known_range A v AR _ _ CL) as RNG. pose proof (known_carved A v AR _ _ CL) as CC.
      pose proof (user_in A _ _ CL) as UI.
      assert (NE : qe_chunk e <> ChS (CS h n0)).
      { intros E. apply (freeS_quar_other A m md p _ (CS h n0) AI (sk_li A m md p n0 AI HL NQ') eq_refl).
        rewrite <- E. rewrite quarantined_chunks_def. unfold q_entries in He |- *. rewrite <- flat_map_app. apply in_map. exact He. }
      assert (HF : forall a, hdr_foot sb (qe_chunk e) (qe_n e) a \/ (user_of sb (qe_chunk e) (qe_n e) <= a < user_of sb (qe_chunk e) (qe_n e) + 8) -> ~ (hla + 24 <= a < hla + 32)).
      { intros a Ha X. pose proof (hdr_foot_in A _ _ a CL Ha) as IN.
        destruct (chunk_eq_dec (qe_chunk e) (ChS (sec_last A))) as [E|NEL].
        - rewrite E in Ha. unfold hdr_foot in Ha. destruct (sec_last A) as [mbl nl] eqn:EQL. cbn [user_of alloc_beg cs_map] in Ha, X.
          unfold sec_user_beg, sec_alloc_beg, kPageSize in Ha. clear -Ha X. lia.
        - pose proof (carved_disjoint A v AR _ (ChS (sec_last A)) CC INL NEL) as Dl. rewrite chunk_lo_S, chunk_hi_S in Dl. clear -IN Dl X HL4. lia. }
      split; [|split].
      + apply (hdr_P A v v'); [| exact HR]. intros a Ha. apply (AGchunk (qe_chunk e) a CC NE); [| apply HF; left; exact Ha]. apply (hdr_foot_in A _ (qe_n e)); [exact CL| left; exact Ha].
      + eapply junk_at_agree; [exact J|]. intros k Hk. apply (AGchunk (qe_chunk e) _ CC NE); [| apply HF; right; lia]. apply (hdr_foot_in A _ (qe_n e)); [exact CL| right; lia].
      + apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| right; lia| lia| | exact MC]. intros x Hx. apply (hole_free_carved A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 (qe_chunk e) x CC NE). lia.
  Qed.

  (* [comment removed for export] *)
  #[using="PHLC PARR PNSRT NNH' SHI8 SHI SLO NNH AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo n0 p md m Clg"] Lemma fs_sec : sec_repr_ LPA AL_pasan P (sec_remove (a_sec A) i) v'.
  Proof.
    pose proof (ar_sec _ _ _ _ _ (proj2 AR)) as SR. unfold sec_repr_ in SR |- *. cbv zeta in SR |- *. cbn [sec_remove sr_chunks sr_reserved].
    (first [ dand7 SR as X1 X2 J1 J2 J3 CH PM | destruct SR as (X1 & X2 & J1 & J2 & J3 & CH & PM) ]). cbn [al_instance AL_pasan] in *.
    (first [ pose proof (bnds) as dR_48; dand4 dR_48 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ PA) as PA'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((sk_nch A m md p n0 AI HL NQ')) as dR_49; dand4 dR_49 as N1 N2 N3 NEC | pose proof (sk_nch A m md p n0 AI HL NQ') as (N1 & N2 & N3 & NEC) ]). (first [ pose proof ((sk_pa A m md p n0 AI HL NQ')) as dR_50; dand5 dR_50 as A1 A2 A3 A4 A5 | pose proof (sk_pa A m md p n0 AI HL NQ') as (A1 & A2 & A3 & A4 & A5) ]).
    (first [ pose proof ((sk_last A m md p n0 AI HL NQ')) as dR_51; dand4 dR_51 as EL INL ELw HLU | pose proof (sk_last A m md p n0 AI HL NQ') as (EL & INL & ELw & HLU) ]).
    pose proof (sec_nodup A m md AI) as ND. apply NoDup_ListNoDup in ND.
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
        * destruct PARR as [B _]. pose proof (sk_i A p n0 i NTH) as [_ NI].
          assert (UP : nth_error (upd (sec_words A) i (Z_to_bv 64 hla)) i = Some (Z_to_bv 64 hla)).
          { apply nth_error_upd_same. rewrite sec_words_length. exact (nth_error_Some_lt _ _ _ NTH). }
          pose proof (u64s_entry v' pa _ i _ B UP) as X. unfold u64_at. exact X.
        * destruct PHLC as [EQ|CC].
          { exfalso. (* [comment removed for export] *)
            pose proof (proj1 (NoDup_nth_error (map cs_map chunks)) ltac:(destruct (wfS A W) as (S1 & _); apply NoDup_ListNoDup; exact S1) i (Z.to_nat (nch - 1))) as INJ.
            rewrite length_map in INJ. specialize (INJ (nth_error_Some_lt _ _ _ NTH)). rewrite !nth_error_map, NTH, EL in INJ. cbn in INJ. specialize (INJ ltac:(rewrite EQ; reflexivity)). lia. }
          unfold sec_hdr_cells. cbn [sh_map_beg sh_map_size sh_size sh_chunk_idx]. exact CC.
      + (* [comment removed for export] *)
        assert (NEc : c <> CS h n0).
        { intros ->. pose proof (proj1 (NoDup_nth_error chunks) ND j i ltac:(apply nth_error_Some_lt in SRC; exact SRC) ltac:(rewrite SRC, NTH; reflexivity)). lia. }
        assert (NEl : c <> sec_last A).
        { intros ->. pose proof (proj1 (NoDup_nth_error chunks) ND j (Z.to_nat (nch - 1)) ltac:(apply nth_error_Some_lt in SRC; exact SRC) ltac:(rewrite SRC, EL; reflexivity)). lia. }
        destruct (CH j c SRC) as [U R]. pose proof (nth_error_In _ _ SRC) as INc. (first [ pose proof ((sk_chunk A m md AI _ INc)) as dR_52; dand7 dR_52 as C1 C2 C3 C4 C5 C6 C7 | pose proof (sk_chunk A m md AI _ INc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7) ]).
        pose proof (carved_disjoint A v AR (ChS c) (ChS (sec_last A)) INc INL ltac:(congruence)) as Dl. rewrite !chunk_lo_S, !chunk_hi_S in Dl.
        split.
        * eapply u64_at_agree; [exact U|]. intros k Hk. apply AGpa; clear -Hk JL NJ N1; lia.
        * eapply rw_cells_agree; [exact R|]. rewrite sec_hdr_size. intros k Hk.
          apply (AGchunk (ChS c) _ INc ltac:(congruence)); [rewrite chunk_lo_S, chunk_hi_S; clear -Hk C4; lia| clear -Dl Hk HL4 C4; lia].
    - apply (mapped_NH v v' (CS h n0) pbeg pend NNH'); [lia| clear -PA' N1 N2 N3; unfold kChunksBlockCount in N3; kung_all; lia| clear -PA' N3 CE; unfold kChunksBlockCount in N3; kung_all; lia| | exact PM].
      intros x Hx. pose proof (sk_sep_h A m md p n0 AI HL NQ' i NTH) as (Dhp & _).
      apply (hole_free_app A v AR (CS h n0) pbeg pend S0 SLO SHI SHI8 pa (8 * sr_reserved (a_sec A)) x); cbn [cs_map cs_n]; [clear -PA' N3; unfold kChunksBlockCount in N3; kung_all; lia| | exact Hx].
      pose proof (carved_apart_pa A v AR (ChS (CS h n0)) S0) as Y. cbn [chunk_lo chunk_hi cs_map cs_n] in Y. clear -Y N3. unfold kChunksBlockCount in N3. kung_all. lia.
  Qed.

  #[using="NNH' SHI8 SHI SLO NNH AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo i n0 p md m Clg"] Lemma fs_fs : fs_base_ LPA P (a_fhint A) v' /\ fs_ptrs_ LPA (a_fs A) (a_fhint A) (a_fframes A) v' /\ fs_flags_ LPA (a_fs A) (a_fhint A) (a_fframes A) v'.
  Proof.
    (first [ pose proof (bnds) as dR_53; dand4 dR_53 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ S) as S'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((bm_nth_fixed A)) as dR_54; dand10 dR_54 as _ E1 _ _ E4 _ E6 E7 E8 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _ & _ & E4 & _ & E6 & E7 & E8 & _) ]). pose proof (sk_last A m md p n0 AI HL NQ') as (EL & _).
    pose proof (bm_nth_sec A _ _ EL) as ELs. pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
    pose proof (bm_sep A _ _ _ _ _ _ W E6 E4 ltac:(lia)) as Y1. pose proof (bm_sep A _ _ _ _ _ _ W E6 E7 ltac:(lia)) as Y2.
    pose proof (bm_sep A _ _ _ _ _ _ W E6 E8 ltac:(lia)) as Y3. pose proof (bm_sep A _ _ _ _ _ _ W E6 E1 ltac:(lia)) as Y4.
    pose proof (bm_sep A _ _ _ _ _ _ W E6 ELs ltac:(lia)) as Y5. pose proof (bm_sep A _ _ _ _ _ _ W E6 Es ltac:(lia)) as Y6.
    unfold a_fs, a_thr, a_nodes0, a_frames0, a_pa in *.
    assert (AGfs : forall a, p_fs P <= a < p_fs P + kFakeStackBytes -> v' (wz a) = v (wz a)).
    { intros a Ha. apply (AGapp (p_fs P) kFakeStackBytes a); try (clear -Ha S'; lia); unfold apart.
      - clear -Y1. lia. - clear -Y2. lia. - clear -Y3. lia. - clear -Y4. lia. - clear -Y5 HL4. lia. - clear -Y6. lia. }
    split; [| split].
    - apply (fsbase_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH'). intros a Ha. apply AGfs. unfold a_fs in Ha. clear -Ha. unfold kFakeFlagsOffset, kFakeStackBytes in *. lia.
    - apply (fsptrs_P A v v' AR). intros a Ha. apply AGfs. unfold a_fs in Ha. clear -Ha. unfold kFakeFramesOffset, kFakeStackBytes in *. lia.
    - apply (fsflags_P A v v' AR). intros a Ha. apply AGfs. unfold a_fs in Ha. clear -Ha. unfold kFakeFlagsOffset, kFakeFramesOffset, kFakeStackBytes in *. lia.
  Qed.

  #[using="IAH AR W AI md m A Clg"] Lemma fs_ia : ia_repr_ LPA AL_pasan true v'.
  Proof.
    destruct IAH as [[EI AGi]|R]; [| exact R]. rewrite <- EI. apply (ia_P A v v' AR). exact AGi.
  Qed.

  #[using="AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo i n0 md m Clg"] Lemma fs_shadow : shadow_repr_ LPA sb (a_reg A) (a_cache A) (free_lm A p) (a_qthread A) (a_qglobal A) v'.
  Proof.
    (first [ pose proof (bnds) as dR_55; dand4 dR_55 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ HM) as HM'. pose proof alloc_ceiling_val as CE. (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_56; dand5 dR_56 as _ HAL _ MSZAL _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (_ & HAL & _ & MSZAL & _) ]).
    (* [comment removed for export] *)
    assert (SHD : forall ch, carved A ch -> ch <> ChS (CS h n0) ->
              forall z, sh (chunk_lo sb ch) <= z < sh (chunk_lo sb ch) + (chunk_hi sb ch - chunk_lo sb ch) / 8 -> ~ (sh h <= z < sh h + msz / 8)).
    { intros ch Cc NE z Hz X. pose proof (carved_disjoint A v AR ch (ChS (CS h n0)) Cc S0 NE) as Dm. cbn [chunk_lo chunk_hi] in Dm.
      pose proof (carved_shadow A v AR ch Cc) as CSH.
      destruct ch as [[c' k']|[mb n1]].
      - destruct Cc as [Hc Hk]. (first [ pose proof ((carved_chunk_bounds A c' k' W Hc Hk)) as dR_57; dand4 dR_57 as _ _ B3 _ | pose proof (carved_chunk_bounds A c' k' W Hc Hk) as (_ & _ & B3 & _) ]). pose proof (class_size_mod32 c' Hc) as CM.
        cbn [chunk_lo chunk_hi alloc_beg] in *.
        replace (chunk_addr sb c' k' + class_size c' - chunk_addr sb c' k') with (class_size c') in Hz by lia.
        pose proof (sh_disjoint (chunk_addr sb c' k') (class_size c') h msz ltac:(apply (mod0_down _ 32 8); [exists 4; reflexivity| exact B3]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                      ltac:(apply (mod0_down _ 32 8); [exists 4; reflexivity| exact CM]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL]) Dm) as SD.
        clear -Hz X SD. lia.
      - unfold carved in Cc. (first [ pose proof ((sk_chunk A m md AI _ Cc)) as dR_58; dand3 dR_58 as C1 C2 _ | pose proof (sk_chunk A m md AI _ Cc) as (C1 & C2 & _) ]). cbn [chunk_lo chunk_hi cs_map cs_n] in *.
        replace (mb + map_size n1 - mb) with (map_size n1) in Hz by lia. pose proof (map_size_page n1) as MP.
        pose proof (sh_disjoint mb (map_size n1) h msz ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact C2]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                      ltac:(apply (mod0_down _ kPageSize 8); [exists 512; reflexivity| exact MP]) ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL]) Dm) as SD.
        clear -Hz X SD. lia. }
    assert (AGc : forall ch, carved A ch -> ch <> ChS (CS h n0) ->
              forall z, sh (chunk_lo sb ch) <= z < sh (chunk_lo sb ch) + (chunk_hi sb ch - chunk_lo sb ch) / 8 -> v' (wz z) = v (wz z)).
    { intros ch Cc NE z Hz. (first [ pose proof ((carved_shadow A v AR ch Cc)) as dR_59; dand3 dR_59 as CS1 CS2 CS3 | pose proof (carved_shadow A v AR ch Cc) as (CS1 & CS2 & CS3) ]). apply AGsh; [| exact (SHD ch Cc NE z Hz)].
      pose proof (heap_shadow_range A z W (CS2 z ltac:(rewrite CS1; exact Hz))) as IM. unfold in_shadow_maps in IM. clear -IM. kung_all. lia. }
    assert (AGp : forall c' k, 1 <= c' <= 30 -> 0 <= k < carved_count A c' ->
              forall z, sh (chunk_addr sb c' k) <= z < sh (chunk_addr sb c' k) + class_size c' / 8 -> v' (wz z) = v (wz z)).
    { intros c' k Hc Hk z Hz. apply (AGc (ChP (CP c' k)) (conj Hc Hk) ltac:(discriminate)). cbn [chunk_lo chunk_hi alloc_beg].
      replace (chunk_addr sb c' k + class_size c' - chunk_addr sb c' k) with (class_size c') by lia. exact Hz. }
    split; [|split; [|split; [|split; [|split]]]].
    - intros c' k Hc ST. apply (shadow_free_P A v v' AR); [exact Hc| exact ST|].
      assert (Hk : 0 <= k < carved_count A c').
      { destruct ST as [F'|[C'|[E B]]].
        - (first [ pose proof ((wfR A W)) as dR_60; dand3 dR_60 as WR _ _ | destruct (wfR A W) as (WR & _ & _) ]). (first [ pose proof ((WR c' Hc)) as dR_61; dand10 dR_61 as _ _ _ _ _ _ _ _ FR _ | destruct (WR c' Hc) as (_ & _ & _ & _ & _ & _ & _ & _ & FR & _) ]). exact (FR k F').
        - (first [ pose proof ((wfC A W)) as dR_62; dand3 dR_62 as WC _ _ | destruct (wfC A W) as (WC & _ & _) ]). (first [ pose proof ((WC c' ltac:(lia))) as dR_63; dand4 dR_63 as _ _ CR' _ | destruct (WC c' ltac:(lia)) as (_ & _ & CR' & _) ]). exact (CR' k C').
        - subst c'. exact (batch_idx_range A v AR k B). }
      exact (AGp c' k Hc Hk).
    - intros u c' k n1 Hl. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [_ Hl]. apply (shadow_live_P A v v' AR u); [exact Hl|].
      pose proof (known_live A v AR u _ Hl) as CL. unfold known in CL. cbn [li_chunk li_n] in CL. (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). exact (AGp c' k Hc Hk).
    - intros c' k n1 He. apply (shadow_quar_P A v v' AR); [exact He|].
      pose proof (known_quar A v AR _ He) as CL. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hc Hk _ | destruct CL as (Hc & Hk & _) ]). exact (AGp c' k Hc Hk).
    - intros c' Hc. apply (shadow_tails_P A v v' AR c' Hc); intros z Hz.
      + (first [ pose proof ((region_tail_shadow A v AR c' Hc)) as dR_66; dand5 dR_66 as X1 _ _ X4 _ | pose proof (region_tail_shadow A v AR c' Hc) as (X1 & _ & _ & X4 & _) ]). apply AGsh.
        * pose proof (heap_shadow_range A z W (X4 z Hz)) as IM. unfold in_shadow_maps in IM. clear -IM. kung_all. lia.
        * (* [comment removed for export] *)
          pose proof (region_piece_bounds A c' W Hc) as RB. cbv zeta in RB. (first [ pose proof ((sb_facts A W)) as dR_67; dand5 dR_67 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]).
          pose proof (sec_apart_b6 A v AR _ S0) as D6. cbn [cs_map cs_n] in D6. change (a_sb A) with sb in *.
          (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
          pose proof (sh_disjoint (region_beg sb c' + rg_allocated_user (a_reg A c')) (rg_mapped_user (a_reg A c') - rg_allocated_user (a_reg A c')) h msz
                        ltac:(rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) Q9), Q11; reflexivity)
                        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                        ltac:(rewrite <- Zminus_mod_idemp_l, Q10, <- Zminus_mod_idemp_r, Q11; reflexivity)
                        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL])
                        ltac:(unfold a_b6 in *; clear -D6 Q2 Q3 Q4 Q7 HB6 RSB; kung_all; lia)) as SD.
          clear -Hz SD X1. lia.
      + (first [ pose proof ((region_tail_shadow A v AR c' Hc)) as dR_69; dand6 dR_69 as _ _ _ _ X5 _ | pose proof (region_tail_shadow A v AR c' Hc) as (_ & _ & _ & _ & X5 & _) ]). apply AGsh.
        * pose proof (heap_shadow_range A z W (X5 z Hz)) as IM. unfold in_shadow_maps in IM. clear -IM. kung_all. lia.
        * pose proof (region_piece_bounds A c' W Hc) as RB. cbv zeta in RB. (first [ pose proof ((sb_facts A W)) as dR_70; dand5 dR_70 as _ SBA HB6 RSB SCE | pose proof (sb_facts A W) as (_ & SBA & HB6 & RSB & SCE) ]).
          pose proof (sec_apart_b6 A v AR _ S0) as D6. cbn [cs_map cs_n] in D6. change (a_sb A) with sb in *.
          (first [ dand12 RB as Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 Q9 Q10 Q11 Q12 | destruct RB as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12) ]).
          pose proof (sh_disjoint (region_beg sb c' + kFreeArrayOffset) (rg_mapped_fa (a_reg A c')) h msz
                        ltac:(rewrite Z.add_mod by lia; rewrite (mod0_down _ 0x10000 8 ltac:(exists 8192; reflexivity) Q9); reflexivity)
                        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL])
                        Q12
                        ltac:(apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact MSZAL])
                        ltac:(unfold a_b6 in *; clear -D6 Q2 Q5 Q6 Q7 HB6 RSB; kung_all; lia)) as SD.
          clear -Hz SD. unfold sh in *. lia.
    - intros u mb n1 Hl. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. destruct Hl as [NEu Hl]. apply (shadow_seclive_P A v v' AR u); [exact Hl|].
      pose proof (known_live A v AR u _ Hl) as CL. pose proof (known_carved A v AR _ _ CL) as Cc. cbn [li_chunk li_n] in Cc.
      assert (NE : ChS (CS mb n1) <> ChS (CS h n0)).
      { (first [ pose proof ((sk_live A m md p n0 AI HL NQ')) as dR_72; dex1 dR_72 as lip; dand4 dR_72 as Hlp _ Hcp _ | pose proof ((sk_live A m md p n0 AI HL NQ')) as dR_72; dand5 dR_72 as lip Hlp _ Hcp _ | destruct (sk_live A m md p n0 AI HL NQ') as (lip & Hlp & _ & Hcp & _) ]).
        pose proof (live_live_chunk A v AR u p _ lip Hl Hlp ltac:(congruence)) as X. cbn [li_chunk] in X. rewrite Hcp in X. exact X. }
      intros z Hz. apply (AGc _ Cc NE). cbn [chunk_lo chunk_hi]. replace (mb + map_size n1 - mb) with (map_size n1) by lia. exact Hz.
    - intros mb n2 n1 He. apply (shadow_secquar_P A v v' AR mb n2); [exact He|].
      pose proof (known_quar A v AR _ He) as CL. pose proof (known_carved A v AR _ _ CL) as Cc. cbn [qe_chunk qe_n] in Cc. unfold known in CL. cbn [qe_chunk qe_n] in CL. (first [ dand3 CL as Hin Hn -> | destruct CL as (Hin & Hn & ->) ]).
      assert (NE : ChS (CS mb n1) <> ChS (CS h n0)).
      { intros E. apply (freeS_quar_other A m md p _ (CS h n0) AI (sk_li A m md p n0 AI HL NQ') eq_refl).
        rewrite <- E. rewrite quarantined_chunks_def. unfold q_entries in He |- *. rewrite <- flat_map_app. apply (in_map qe_chunk _ (QE (ChS (CS mb n1)) n1)). exact He. }
      intros z Hz. apply (AGc _ Cc NE). cbn [chunk_lo chunk_hi]. replace (mb + map_size n1 - mb) with (map_size n1) by lia. exact Hz.
  Qed.

  #[using="IAP IAL IAH PDR PHLC PARR PLCK PNSRT NNH' SHI8 SHI SLO NNH AG S0 AR W NQ' WLO NTH NQB HL AI whi wlo md m"] Theorem freeS_arepr : @arepr _ DepotRepL LPA AL_pasan [] A' v'.
  Proof.
    (first [ pose proof (fs_fs) as dR_74; dand3 dR_74 as F1 F2 F3 | pose proof fs_fs as (F1 & F2 & F3) ]).
    constructor; cbn [freeS a_pl a_reg a_cache_inited a_cache a_livemap a_qthread a_qglobal a_sec a_depot a_fhint a_fframes a_ia_inited a_sb a_fs].
    - exact fs_consts.
    - exact fs_locks.
    - exact fs_regions.
    - exact fs_cache.
    - exact fs_live.
    - exact fs_quar.
    - exact fs_sec.
    - exact PDR.
    - exact fs_ia.
    - exact F1.
    - exact F2.
    - exact F3.
    - exact (maps_PH A v v' AR (CS h n0) pbeg pend S0 SLO SHI SHI8 NNH').
    - exact fs_shadow.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="S0 AR W NQ' NTH NQB HL AI md m Clg"] Lemma rt_maps_sub : forall b sz, In (b, sz) (runtime_maps_ P (a_reg A) (sec_remove (a_sec A) i)) ->
    In (b, sz) (runtime_maps_ P (a_reg A) (a_sec A)) /\ (b + sz <= h \/ h + msz <= b \/ sz <= 0).
  Proof.
    intros b sz Hin. (first [ pose proof ((bm_nth_fixed A)) as dR_75; dand15 dR_75 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
    pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
    (first [ pose proof ((sb_facts A W)) as dR_76; dand5 dR_76 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (sec_apart_b6 A v AR _ S0) as D6. cbn [cs_map cs_n] in D6.
    unfold a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_pa, a_itab, a_m64k, a_b6, a_sb in *.
    unfold runtime_maps_ in Hin |- *. cbn [sec_remove sr_chunks] in Hin. rewrite !in_app_iff in Hin |- *.
    destruct Hin as [Hin|[Hin|Hin]].
    - split; [left; exact Hin|]. cbn in Hin. unfold p_ri in *.
      destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]; injection E as <- <-;
        first [ (* [comment removed for export] *) lazymatch goal with |- ?b + _ <= _ \/ _ => match goal with Ek : nth_error (big_maps A) _ = Some (b, _) |- _ => pose proof (bm_sep A _ _ _ _ _ _ W Ek Es ltac:(lia)); lia end end
              | pose proof (bm_sep A _ _ _ _ _ _ W E4 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E5 Es ltac:(lia)); lia
              | pose proof (bm_sep A _ _ _ _ _ _ W E6 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E7 Es ltac:(lia)); lia
              | pose proof (bm_sep A _ _ _ _ _ _ W E8 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E1 Es ltac:(lia)); kung_all; lia
              | pose proof (bm_sep A _ _ _ _ _ _ W E9 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E10 Es ltac:(lia)); lia
              | pose proof (bm_sep A _ _ _ _ _ _ W E14 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E11 Es ltac:(lia)); lia
              | pose proof (bm_sep A _ _ _ _ _ _ W E12 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E13 Es ltac:(lia)); lia
              | kung_all; lia ].
    - split; [right; left; exact Hin|]. apply in_flat_map in Hin as (c' & Hc' & Hin). apply in_map_iff in Hc' as (k' & <- & Hk'). apply in_seq in Hk'.
      pose proof (region_piece_bounds A (Z.of_nat k') W ltac:(lia)) as RB. cbv zeta in RB. unfold a_sb in RB.
      destruct Hin as [E|[E|[]]]; injection E as <- <-; kung_all; lia.
    - apply in_map_iff in Hin as (c & E & Hc). injection E as <- <-. apply (chunks'_in_iff A m md (CS h n0) i AI NTH) in Hc as [Hc NEc].
      split; [right; right; apply in_map_iff; exists c; split; [reflexivity| exact Hc]|].
      destruct (In_nth_error' _ _ Hc) as [j Hj].
      pose proof (sk_sep_chunks A m md AI j i c (CS h n0) Hj NTH ltac:(intros ->; rewrite NTH in Hj; injection Hj as E; exact (NEc (eq_sym E)))) as D.
      cbn [cs_map cs_n] in D. unfold apart in D. lia.
  Qed.

  #[using="S0 AR W NQ' NTH NQB HL AI md m"] Lemma fs_owned_new : forall a, pa_owned A' a -> pa_owned A a.
  Proof.
    intros a H. unfold pa_owned, aowned, aowned_ in *. cbn [freeS a_pl a_reg a_livemap a_sec a_fframes] in H.
    destruct H as [[St|[[(R1 & NU & NF)|[HS|FS]]|GH]]|I]; [left; left; exact St| | | left; right; left; right; right; exact FS| left; right; right; exact GH| right; exact I].
    - (first [ dex2 R1 as b sz; destruct R1 as [Hin Hb] | dand4 R1 as b sz Hin Hb | destruct R1 as (b & sz & Hin & Hb) ]). destruct (rt_maps_sub b sz Hin) as [Hin0 AP].
      left. right. left. left. split; [exists b, sz; split; [exact Hin0| exact Hb]|]. split; [| exact NF].
      ((first [ intro dR_96; dex2 dR_96 as u li'; destruct dR_96 as [Hl Hu] | intro dR_96; dand4 dR_96 as u li' Hl Hu | intros (u & li' & Hl & Hu) ])). destruct (Z.eq_dec u p) as [->|NEu].
      + (first [ pose proof ((sk_live A m md p n0 AI HL NQ')) as dR_78; dex1 dR_78 as lip; dand4 dR_78 as Hlp Hn Hcp _ | pose proof ((sk_live A m md p n0 AI HL NQ')) as dR_78; dand5 dR_78 as lip Hlp Hn Hcp _ | destruct (sk_live A m md p n0 AI HL NQ') as (lip & Hlp & Hn & Hcp & _) ]). rewrite Hlp in Hl. injection Hl as <-. rewrite Hn in Hu.
        (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_79; dand9 dR_79 as _ _ _ _ _ PH _ N6 _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (_ & _ & _ & _ & _ & PH & _ & N6 & _) ]). clear -AP Hb Hu PH N6. lia.
      + apply NU. exists u, li'. split; [| exact Hu]. unfold free_lm. rewrite lookup_delete_Some. split; [congruence| exact Hl].
    - left. right. left. right. left. unfold heap_shadow_ in *. cbn [sec_remove sr_chunks] in HS.
      destruct HS as [HS|[HS|(c & Hc & Hz)]]; [left; exact HS| right; left; exact HS| right; right].
      exists c. split; [| exact Hz]. apply (chunks'_in_iff A m md (CS h n0) i AI NTH) in Hc as [Hc _]. exact Hc.
  Qed.

  (* [comment removed for export] *)
  #[using="S0 AR W NQ' NTH NQB HL AI i md m"] Lemma fs_shadow_ghost : forall z, sh h <= z < sh h + msz / 8 -> ghost_hs_ P z.
  Proof.
    intros z Hz. (first [ pose proof (bnds) as dR_80; dand4 dR_80 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    (first [ pose proof ((sk_shr A m md p n0 AI HL NQ')) as dR_81; dand4 dR_81 as SHA _ _ SIDE | pose proof (sk_shr A m md p n0 AI HL NQ') as (SHA & _ & _ & SIDE) ]). pose proof alloc_ceiling_val as CE.
    split.
    - unfold in_shadow_maps. clear -Hz SIDE. kung_all. unfold kHighShadowMapSize. lia.
    - ((first [ intro dR_97; dex2 dR_97 as b n; destruct dR_97 as [Hin Rz] | intro dR_97; dand4 dR_97 as b n Hin Rz | intros (b & n & Hin & Rz) ])). (first [ pose proof ((bm_nth_fixed A)) as dR_82; dand15 dR_82 as E0 E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 | pose proof (bm_nth_fixed A) as (E0 & E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14) ]).
      pose proof (bm_nth_sec A _ _ NTH) as Es. cbn [cs_map cs_n] in Es.
      (first [ pose proof ((sb_facts A W)) as dR_83; dand5 dR_83 as _ _ HB6 RSB SCE | pose proof (sb_facts A W) as (_ & _ & HB6 & RSB & SCE) ]). pose proof (sec_apart_b6 A v AR _ S0) as D6. cbn [cs_map cs_n] in D6.
      unfold a_thr, a_ctx, a_fs, a_nodes0, a_frames0, a_pa, a_itab, a_m64k, a_b6, a_sb in *.
      (* [comment removed for export] *)
      assert (DJ : b + n <= h \/ h + msz <= b).
      { unfold VIS0 in Hin. cbn in Hin. unfold stack_band_iv in Hin.
        destruct Hin as [E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[E|[]]]]]]]]]]]]]]]; injection E as <- <-;
          first [ (* [comment removed for export] *) lazymatch goal with |- ?b + _ <= _ \/ _ => match goal with Ek : nth_error (big_maps A) _ = Some (b, _) |- _ => pose proof (bm_sep A _ _ _ _ _ _ W Ek Es ltac:(lia)); lia end end
                | pose proof (bm_sep A _ _ _ _ _ _ W E11 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E12 Es ltac:(lia)); lia
                | pose proof (bm_sep A _ _ _ _ _ _ W E8 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E7 Es ltac:(lia)); lia
                | pose proof (bm_sep A _ _ _ _ _ _ W E6 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E4 Es ltac:(lia)); lia
                | pose proof (bm_sep A _ _ _ _ _ _ W E13 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E5 Es ltac:(lia)); lia
                | pose proof (bm_sep A _ _ _ _ _ _ W E14 Es ltac:(lia)); lia
                | unfold p_ri in *; kung_all; lia
                | pose proof (bm_sep A _ _ _ _ _ _ W E9 Es ltac:(lia)); lia | pose proof (bm_sep A _ _ _ _ _ _ W E10 Es ltac:(lia)); lia
                | lia ]. }
      (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_84; dand5 dR_84 as _ HAL _ MSZAL _ | pose proof (sk_geo A m md p n0 AI HL NQ') as (_ & HAL & _ & MSZAL & _) ]).
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

  #[using="WHI SM HNONE IAH PHLC PARR NNH AG S0 AR W NQ' WLO NTH NQB HL AI md"] Theorem freeS_frame : frame_ok LPA (pa_owned A) (pa_owned A') whi (whi - wlo) (newblk p n0) nowhere v v'.
  Proof.
    (first [ pose proof (bnds) as dR_85; dand4 dR_85 as (T & C & N & F & S & D & PA) (HM & H5 & HHI & LE & IR) (HL1 & HL5 & HL4) (R1 & R2 & R3) | pose proof bnds as ((T & C & N & F & S & D & PA) & (HM & H5 & HHI & LE & IR) & (HL1 & HL5 & HL4) & (R1 & R2 & R3)) ]).
    pose proof (aobj_facts _ _ T) as T'. pose proof (aobj_facts _ _ PA) as PA'. pose proof (aobj_facts _ _ HM) as HM'. pose proof alloc_ceiling_val as CE.
    (first [ pose proof ((sk_geo A m md p n0 AI HL NQ')) as dR_86; dand11 dR_86 as HLO HAL MSZ MSZAL HHI' PH PIN N6 NR _ PM | pose proof (sk_geo A m md p n0 AI HL NQ') as (HLO & HAL & MSZ & MSZAL & HHI' & PH & PIN & N6 & NR & _ & PM) ]).
    (first [ pose proof ((sk_live A m md p n0 AI HL NQ')) as dR_87; dex1 dR_87 as lip; dand4 dR_87 as Hlp Hnp Hcp _ | pose proof ((sk_live A m md p n0 AI HL NQ')) as dR_87; dand5 dR_87 as lip Hlp Hnp Hcp _ | destruct (sk_live A m md p n0 AI HL NQ') as (lip & Hlp & Hnp & Hcp & _) ]).
    (first [ pose proof ((sk_last A m md p n0 AI HL NQ')) as dR_88; dand3 dR_88 as EL INL _ | pose proof (sk_last A m md p n0 AI HL NQ') as (EL & INL & _) ]).
    (* [comment removed for export] *)
    assert (OWNmap : forall a, h <= a < h + msz -> ~ (p <= a < p + n0) -> pa_owned A a).
    { intros a Ha NU. apply (carved_owned A v AR (ChS (CS h n0)) a S0); [cbn [chunk_lo chunk_hi]; exact Ha|].
      intros u li' Hl E Hu. destruct (Z.eq_dec u p) as [->|NE]; [rewrite Hlp in Hl; injection Hl as <-; rewrite Hnp in Hu; exact (NU Hu)|].
      exact (live_live_chunk A v AR u p li' lip Hl Hlp NE ltac:(rewrite Hcp; exact E)). }
    assert (OWNhla : forall a, hla + 24 <= a < hla + 32 -> pa_owned A a).
    { intros a Ha. apply (carved_owned A v AR (ChS (sec_last A)) a INL); [rewrite chunk_lo_S, chunk_hi_S; lia|].
      intros u li' Hl E Hu. pose proof (user_in A _ _ (known_live A v AR u li' Hl)) as UI. rewrite E, chunk_lo_S, chunk_hi_S in UI.
      destruct (wfV A W) as (V1 & _). (first [ pose proof ((V1 u li' Hl)) as dR_89; dand3 dR_89 as _ U _ | pose proof (V1 u li' Hl) as (_ & U & _) ]). cbv zeta in U. rewrite E in U. destruct (sec_last A) as [mbl nl] eqn:EQL. cbn [user_of cs_map] in U, Ha, UI. unfold sec_user_beg, kPageSize in U. lia. }
    assert (OWNpa : forall a, pa + 8 * Z.of_nat i <= a < pa + 8 * Z.of_nat i + 8 -> pa_owned A a).
    { intros a Ha. (first [ pose proof ((sk_nch A m md p n0 AI HL NQ')) as dR_90; dand4 dR_90 as _ NR1 NR2 _ | pose proof (sk_nch A m md p n0 AI HL NQ') as (_ & NR1 & NR2 & _) ]). (first [ pose proof ((bm_nth_fixed A)) as dR_91; dand3 dR_91 as _ E1 _ | pose proof (bm_nth_fixed A) as (_ & E1 & _) ]). unfold a_pa in E1.
      apply (owned_rt A a pa (8 * kChunksBlockCount)); [unfold runtime_maps, runtime_maps_; rewrite !in_app_iff; left; cbn; clear - E1; tauto| clear -Ha IR NR1 NR2; kung_all; lia| |].
      - eapply (fixed_bm_no_live_user A 1); [exact W| lia| exact E1| clear -Ha IR NR1 NR2; kung_all; lia].
      - eapply (fixed_bm_no_live_frame A 1); [exact W| lia| lia| exact E1| clear -Ha IR NR1 NR2; kung_all; lia]. }
    unfold frame_ok. replace (whi - (whi - wlo)) with wlo by lia. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits.
    - (* [comment removed for export] *)
      intros a Ha NO NO' NW NE' NV _. apply AG; [exact Ha|]. intros X. exc14 X.
      + exact (NW X).
      + apply NO. apply (thr_owned A v AR). clear -X. lia.
      + apply NO. apply (thr_owned A v AR). clear -X. lia.
      + apply NO. apply (dstat_owned A). exact X.
      + apply NO. apply (n0_owned A v AR). exact X.
      + apply NO. apply (f0_owned A v AR). exact X.
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
      + apply NO. apply OWNpa. exact X.
      + apply NO. apply OWNhla. exact X.
      + destruct (decide (p <= a < p + n0)) as [Y|Y]; [apply NV; left; split; [clear -H5 PH; lia| exact Y]| exact (NO (OWNmap a X Y))].
      + apply NO. left. right. left. right. left. unfold heap_shadow_. right. right. exists (CS h n0). split; [exact S0| cbn [cs_map cs_n]; exact X].
      + apply NO. apply asI_static_owned. cbn [cl_static LPA]. unfold pa_static. clear -X. lia.
    - (* [comment removed for export] *)
      intros a Ha NI Hv. destruct (decide (h <= a < h + msz)) as [Y|Y].
      + destruct (decide (p <= a < p + n0)) as [Z1|Z1]; [right; left; left; split; [clear -H5 PH; lia| exact Z1]| left; exact (OWNmap a Y Z1)].
      + destruct (decide (pbeg <= a < pend)) as [Z1|Z1].
        * left. left. right. left. right. left. unfold heap_shadow_. right. right. exists (CS h n0). split; [exact S0| cbn [cs_map cs_n]].
          (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_92; dand7 dR_92 as G1 _ _ _ _ G6 _ | pose proof (a8_geo A m md p n0 AI HL NQB) as (G1 & _ & _ & _ & _ & G6 & _) ]). clear -Z1 G1 G6. lia.
        * right. right. apply NNH; [lia| unfold in_image in NI; cbn [cl_image_lo cl_image_hi LPA] in NI; clear -NI Ha; lia| lia| unfold holeD; clear -Y Z1; lia| exact Hv].
    - eapply mapped_mono; [exact SM|]. intros k Hk Hvk. (first [ pose proof ((place_facts A W)) as dR_93; dand14 dR_93 as _ _ _ _ _ _ _ _ _ _ _ _ Psp0 _ | pose proof (place_facts A W) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Psp0 & _) ]). cbv zeta in Psp0.
      (first [ pose proof ((a8_geo A m md p n0 AI HL NQB)) as dR_94; dand7 dR_94 as _ _ _ _ _ G6 _ | pose proof (a8_geo A m md p n0 AI HL NQB) as (_ & _ & _ & _ & _ & G6 & _) ]).
      apply NNH; [clear -WLO CE Hk; lia| right; clear -WLO CE Hk; lia| clear -Hk WHI Psp0; lia| unfold holeD; clear -Hk WLO HHI R2 CE G6; kung_all; lia| exact Hvk].
    - intros a Ha Fz. destruct Fz.
    - intros a Ha O'. left. exact (fs_owned_new a O').
    - (* [comment removed for export] *)
      intros a Ha O NO'. right.
      destruct (decide (h <= a < h + msz)) as [Y|Y]; [exact (HNONE a Y)|]. exfalso. apply NO'.
      unfold pa_owned, aowned, aowned_ in O |- *. cbn [freeS a_pl a_reg a_livemap a_sec a_fframes sec_remove sr_chunks].
      destruct O as [[St|[[(R1' & NU & NF)|[HS|FS]]|GH]]|I]; [left; left; exact St| | | left; right; left; right; right; exact FS| left; right; right; exact GH| right; exact I].
      + left. right. left. left. (first [ dex2 R1' as b sz; destruct R1' as [Hin Hb] | dand4 R1' as b sz Hin Hb | destruct R1' as (b & sz & Hin & Hb) ]). split; [| split; [| exact NF]].
        * exists b, sz. split; [| exact Hb]. unfold runtime_maps_ in Hin |- *. rewrite !in_app_iff in Hin |- *.
          destruct Hin as [Hin|[Hin|Hin]]; [left; exact Hin| right; left; exact Hin| right; right].
          apply in_map_iff in Hin as (c & E & Hc). apply in_map_iff. exists c. split; [exact E|]. apply (chunks'_in_iff A m md (CS h n0) i AI NTH). split; [exact Hc|].
          intros ->. injection E as <- <-. exact (Y Hb).
        * ((first [ intro dR_98; dex2 dR_98 as u li'; destruct dR_98 as [Hl Hu] | intro dR_98; dand4 dR_98 as u li' Hl Hu | intros (u & li' & Hl & Hu) ])). apply NU. exists u, li'. split; [| exact Hu]. unfold free_lm in Hl. rewrite lookup_delete_Some in Hl. exact (proj2 Hl).
      + destruct (decide (sh h <= a < sh h + msz / 8)) as [Z1|Z1]; [left; right; right; exact (fs_shadow_ghost a Z1)|].
        left. right. left. right. left. unfold heap_shadow_ in HS |- *. destruct HS as [HS|[HS|(c & Hc & Hz)]]; [left; exact HS| right; left; exact HS| right; right].
        exists c. split; [| exact Hz]. apply (chunks'_in_iff A m md (CS h n0) i AI NTH). split; [exact Hc|]. intros ->. cbn [cs_map cs_n] in Hz. exact (Z1 Hz).
    - (* [comment removed for export] *)
      intros a Ha NB. unfold newblk, blk in NB. destruct NB as [[_ Hb]|[_ Hb]].
      + right. right. apply HNONE. clear -Hb PH N6. lia.
      + left. left. right. right. apply fs_shadow_ghost.
        pose proof (Z_div_mod_eq_full (n0 + 7) 8) as Q. pose proof (Z.mod_pos_bound (n0 + 7) 8 ltac:(lia)).
        assert (SP : sh h + 768 = sh p).
        { symmetry. rewrite <- sh_add8; [f_equal; clear; lia| apply (mod0_down _ 4096 8); [exists 512; reflexivity| exact HAL]]. }
        pose proof (sh_mono (p + 8 * ((n0 + 7) / 8)) (h + msz) PIN) as SMx.
        rewrite (sh_add8 p ((n0 + 7) / 8)) in SMx; [| apply (mod0_down _ 16 8); [exists 2; reflexivity| exact PM]].
        rewrite R3 in SMx. clear -Hb SP SMx. lia.
  Qed.
End ReprS.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section HiddenS.
Context {Clg : Ceiling}.
  Variables (A : AState) (m : mem) (md : Model) (p n0 : Z) (i : nat) (m' : mem).
  Hypothesis AI : @pa_ainv _ DepotRepL A m md.
  Hypothesis HL : as_live A p = Some n0.
  Hypothesis NQB : kQuarantineMaxSize < n0.
  Hypothesis NTH : nth_error (sr_chunks (a_sec A)) i = Some (CS (p - 6144) n0).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (p - 6144).
  #[warnings="-notation-for-abbreviation"] Local Notation msz := (map_size n0).
  (* [comment removed for export] *)
  Hypothesis HID1 : forall z, in_shadow_maps z -> ~ (sh h <= z < sh h + msz / 8) -> m' (wz z) = m (wz z).
  Hypothesis HID2 : forall z, sh h <= z < sh h + msz / 8 -> m' (wz z) = Some (Z_to_bv 8 0).

  #[using="HID2 HID1 NTH AI n0 p md m"] Theorem freeS_hidden : hidden_repr (a_pl A) (a_reg A) (sec_remove (a_sec A) i) m'.
  Proof.
    pose proof (ai_hidden _ _ _ _ _ _ _ AI) as [H1 H2]. unfold hidden_repr.
    split.
    - intros z GZ. pose proof GZ as [IM _].
      destruct (decide (sh h <= z < sh h + msz / 8)) as [IN|OUT].
      + rewrite (HID2 z IN). split; [discriminate| intros _; reflexivity].
      + rewrite (HID1 z IM OUT). destruct (H1 z GZ) as [P1 P2]. split; [exact P1|].
        intros NHS. apply P2. intros HS. apply NHS. unfold heap_shadow_ in HS |- *. cbn [sec_remove sr_chunks].
        destruct HS as [HS|[HS|(c & Hc & Hz)]]; [left; exact HS| right; left; exact HS| right; right].
        exists c. split; [| exact Hz]. apply (chunks'_in_iff A m md (CS h n0) i AI NTH). split; [exact Hc|]. intros ->. cbn [cs_map cs_n] in Hz. exact (OUT Hz).
    - intros z Hz NB. destruct (decide (sh h <= z < sh h + msz / 8)) as [IN|OUT]; [rewrite (HID2 z IN); discriminate|].
      rewrite (HID1 z ltac:(unfold in_shadow_maps; left; exact Hz) OUT). exact (H2 z Hz NB).
  Qed.
End HiddenS.

