(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Classical_Prop.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module HW := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU RU_mkfg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRepAux Mall5lv Mallj6y Mallwlb Mallrkx Malllim Mallzvh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MTree MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallkgx Mall1es Mall79j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KInv MI_Inv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MI_WFree.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KNodes RzImpl KLink KLinkC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KLinkC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MSafe KFrame.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RzAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_Inv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MI_WFree.MI_Read OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KNodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzImpl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLink OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KLinkC.KLinkR OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MSafe OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.KFrame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.RzBridge.RzEvt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RzAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_ge3a6 W_redqm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require W_rejt8 W_retp0 RF_m8yt RF_mg1g.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_redqm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8.W_re997 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8.W_reagh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_rejt8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_retp0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mg1g.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import Mrems6x.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Instfes Inst8ld InstDefs InstFree Instjhg Instffk Instrcx Instjk7 Instqy7 Instbka Instbrv Inst41h Instr3v Instmbo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls6g Mallx0l.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import AllocSpec LayoutPU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import InstQ.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import LB_Inv LB_Sum.   (* [comment removed for export] *)
Import ListNotations.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.



(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma frame_ok_pre_agree_e (O O' : Z -> Prop) sp win (V NB : Z -> Prop) m m1 m' :
  (forall a, 0 <= a < 2^64 -> ~ (sp - win <= a < sp) -> ~ (al_errno LayoutPU <= a < al_errno LayoutPU + 4) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2^64 -> heap_zone LayoutPU a -> m (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None) ->
  (forall a, 0 <= a < 2^64 -> ~ in_image LayoutPU a -> ~ heap_zone LayoutPU a -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
  frame_ok LayoutPU O O' sp win V NB m1 m' -> frame_ok LayoutPU O O' sp win V NB m m'.
Proof.
  (intros AG MONO HIGH; (first [ intro dR_14; dand7 dR_14 as F1 F2 F3 F4 F5 F6 F7 | intros (F1 & F2 & F3 & F4 & F5 & F6 & F7) ])).
  split; [|split; [|split; [|split; [|split; [|split]]]]].
  - intros a Ha NO NO' NW NE NV NN. rewrite <- (AG a Ha NW NE). apply F1; auto.
  - intros a Ha NI Hm. destruct (classic (heap_zone LayoutPU a)) as [HZ|NHZ]; [apply F2; auto| right; right; apply HIGH; auto].
  - exact F3.
  - intros a Ha Hn. destruct (F4 a Ha Hn) as [X|[X|[X HZ]]]; [left; exact X| right; left; exact X| right; right].
    split; [| exact HZ]. destruct (m (Z_to_bv 64 a)) eqn:E; [| reflexivity]. exfalso. apply (MONO a Ha HZ); [congruence| exact X].
  - intros a Ha Ho. destruct (F5 a Ha Ho) as [X|[X|[X HZ]]]; [left; exact X| right; left; exact X| right; right].
    split; [| exact HZ]. destruct (m (Z_to_bv 64 a)) eqn:E; [| reflexivity]. exfalso. apply (MONO a Ha HZ); [congruence| exact X].
  - exact F6.
  - exact F7.
Qed.

(* [comment removed for export] *)
Lemma p0_ainv_agree_but_errno A m m' md :
  p0_ainv A m md ->
  (forall a, 0 <= a < alloc_ceiling -> ~ (PERRNO <= a < PERRNO + 4) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
  p0_ainv A m' md.
Proof.
  intros AI AG. pose proof alloc_ceiling_val as ACV. pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  eapply (p0_frame A m m' md md AI).
  - intros a Ha. apply AG.
    + destruct (p0_owned_where A m md a AI Ha) as [S|HZ]; [unfold al_static, LayoutPU, pu_static in S; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|].
      apply (proj1 (heap_zone_p0 a)) in HZ. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
    + destruct (p0_owned_where A m md a AI Ha) as [S|HZ]; [unfold al_static, LayoutPU, pu_static in S; unfold PERRNO; lia|].
      apply (proj1 (heap_zone_p0 a)) in HZ. unfold PERRNO. lia.
  - intros a Ha. apply AG; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold al_shared, LayoutPU, pu_shared, PERRNO in *; lia.
  - intros p n i Hp Hi. (first [ pose proof ((p0_live_ok A m md p n AI Hp)) as dR_1; dand7 dR_1 as N0 _ P0 PC PIMG MP _ | pose proof (p0_live_ok A m md p n AI Hp) as (N0 & _ & P0 & PC & PIMG & MP & _) ]). cbn [al_image_lo al_image_hi LayoutPU] in PIMG.
    rewrite AG; [apply MP; exact Hi| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| unfold PERRNO; lia].
  - intros a HZ Hm1. apply (proj1 (heap_zone_p0 a)) in HZ. rewrite AG in Hm1; [exact Hm1| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| unfold PERRNO; lia].
  - reflexivity.
  - exact Hh.
Qed.

(* [comment removed for export] *)
Definition img_avoid : list (Z * Z) := [(0x10000, 0x64000)].

(* [comment removed for export] *)
Lemma resv_avoid (l : list (word * word)) (dst : word) ND :
  map wwZ l = p0_reserved -> 0 < ND < 2^64 -> region_free l dst (Z_to_bv 64 ND) = true ->
  bv_unsigned dst + ND <= 0x10000 \/ 0x64000 <= bv_unsigned dst.
Proof.
  intros HM HND RF.
  destruct l as [|e1 [|e2 [|e3 [|e4 [|e5 l]]]]]; try discriminate HM.
  cbn [map] in HM. unfold p0_reserved, wwZ in HM. injection HM as E1 E2 E3 E4 E5 E6 E7 E8.
  pose proof (region_free_disj _ _ _ e1 RF ltac:(cbn; auto)) as D1.
  pose proof (region_free_disj _ _ _ e2 RF ltac:(cbn; auto)) as D2.
  pose proof (region_free_disj _ _ _ e3 RF ltac:(cbn; auto 10)) as D3.
  pose proof (region_free_disj _ _ _ e4 RF ltac:(cbn; auto 10)) as D4.
  unfold elo, ehi in D1, D2, D3, D4. rewrite unsigned_lit in D1, D2, D3, D4 by lia. lia.
Qed.

(* [comment removed for export] *)
Definition remap_leaf (md : Model) (B OL ND : Z) (z : Z) (md' : Model) : Prop :=
  same_env md md' /\
  ( (2^64 - 4095 <= z /\ md' = md)
    \/ (exists dst : word, z = bv_unsigned dst /\
         let NB := bv_unsigned dst in let h := m_vmmaps md in
         0 < NB /\ NB mod 4096 = 0 /\ NB + ND <= alloc_ceiling
         /\ m_vmmaps md' = mremap_maps_next h (Z_to_bv 64 B) dst (Z_to_bv 64 ND) /\ minv md' /\ m_halted md' = None /\ m_vm_lazy md' = [] /\ m_vm_materialized md' = []
         /\ ((dst = Z_to_bv 64 B /\ (ND < OL \/ region_free (vm_reserved h ++ map_remove (vm_maps h) (Z_to_bv 64 B)) (Z_to_bv 64 B) (Z_to_bv 64 ND) = true))
             \/ (dst <> Z_to_bv 64 B /\ OL < ND /\ region_free (vm_reserved h ++ vm_maps h) dst (Z_to_bv 64 ND) = true))
         /\ (NB + ND <= 0x10000 \/ 0x64000 <= NB)) ).

Lemma remap_node_twf md (B OL ND : Z) :
  minv md -> m_halted md = None -> m_vm_lazy md = [] -> m_vm_materialized md = [] -> ceil_ok md ->
  nsafe (NMremap B OL ND 1) md ->
  map wwZ (vm_reserved (m_vmmaps md)) = p0_reserved ->
  0 < B -> B mod 4096 = 0 -> 4096 <= OL -> OL mod 4096 = 0 -> B + OL <= alloc_ceiling -> (B + OL <= 0x10000 \/ 0x64000 <= B) ->
  4096 <= ND -> ND mod 4096 = 0 -> ND <= alloc_ceiling -> ND <> OL ->
  twf (enode (NMremap B OL ND 1) (dec_mremap img_avoid B OL ND)) md
      (fun r md' => match r with Unr => False | Ok z => remap_leaf md B OL ND z md' end).
Proof.
  intros MINV MH ML MMT CEILMD NS RESV B0 BA OL0 OLA BC BI ND0 NDA NDC NE.
  pose proof alloc_ceiling_val as ACV.
  unfold enode. cbn [twf]. split; [exact NS|].
  intros eff md' ST _.   (* [comment removed for export] *)
  pose proof (nstep_same_env _ _ _ _ ST) as SE.
  pose proof (nstep_KI _ _ _ _ (conj MH ML) ST) as [KH KL].
  pose proof (KLink.nstep_mat _ _ _ _ MMT ST) as MMT'.
  assert (MOL : mrlen OL = OL). { unfold mrlen, mw. rewrite unsigned_lit by lia. rewrite <- (KLink.mmap_len_of_aligned OL) at 2 by lia. reflexivity. }
  assert (MND : mrlen ND = ND). { unfold mrlen, mw. rewrite unsigned_lit by lia. rewrite <- (KLink.mmap_len_of_aligned ND) at 2 by lia. reflexivity. }
  destruct (nstep_mremap_cases (Clg:=Clg) B OL ND md eff md' ltac:(lia) ltac:(lia) OLA ltac:(lia) NDA
              ltac:((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); exact BC) BA MINV MH CEILMD ST)
    as [(e & He & -> & ->)|[(EQ & _)|(dst & D0 & DA & DC & NEQ & VM & MI' & MH' & CASE)]].
  - (* [comment removed for export] *) cbn in He. destruct He as [<-|[]].
    rewrite (dec_mremap_err img_avoid B OL ND (errno_ret ENOMEM) ENOMEM) by (apply errno_of_errno_ret; unfold ENOMEM; lia).
    cbn [twf]. split; [exact SE|]. left. split; [unfold neg_errno, ENOMEM; lia| reflexivity].
  - exfalso. exact (NE (eq_sym EQ)).
  - cbv zeta in *. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    pose proof (bv_unsigned_in_range _ dst) as DR. change (bv_modulus 64) with (2^64) in DR.
    assert (EN : errno_of dst = None) by (apply errno_of_small; lia).
    (* [comment removed for export] *)
    assert (NBI : bv_unsigned dst + ND <= 0x10000 \/ 0x64000 <= bv_unsigned dst).
    { destruct CASE as [(-> & [LT|[LT RF]] & _)|(NEd & LT & RF & _)].
      - rewrite unsigned_lit by lia. lia.
      - pose proof (resv_avoid (vm_reserved (m_vmmaps md)) (Z_to_bv 64 B) ND RESV ltac:(lia) (region_free_app_l _ _ _ _ RF)) as X.
        rewrite unsigned_lit in X by lia. rewrite unsigned_lit by lia. exact X.
      - exact (resv_avoid (vm_reserved (m_vmmaps md)) dst ND RESV ltac:(lia) (region_free_app_l _ _ _ _ RF)). }
    assert (EXP : eff = mremap_expected B OL ND dst /\ eff_ret eff = dst).
    { unfold mremap_expected. rewrite MOL, MND. rewrite (proj2 (Z.eqb_neq OL ND)) by lia.
      unfold mw, mwlen. rewrite MOL, MND.
      destruct CASE as [(-> & _ & ->)|(NEd & _ & _ & ->)].
      - rewrite bv_eqb_refl. split; [reflexivity|]. unfold mremap_inplace_effect. destruct (ND <? OL); reflexivity.
      - destruct (bv_eqb dst (Z_to_bv 64 B)) eqn:Q; [apply bv_eqb_true_iff in Q; contradiction|]. split; reflexivity. }
    destruct EXP as [-> RR].
    assert (DOK : mremap_dst_ok img_avoid OL ND dst = true).
    { apply mremap_dst_ok_intro; [exact DA| exact D0| |].
      - (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold mspan. rewrite MOL, MND. idtac.
        destruct CASE as [(-> & _ & _)|(NEd & LT & RF & _)]; [rewrite unsigned_lit in * by lia; lia| lia].
      - intros iv [<-|[]]. cbn [fst snd]. unfold mspan. rewrite MOL, MND.
        destruct CASE as [(-> & _ & _)|(NEd & LT & RF & _)]; [rewrite unsigned_lit in * by lia; lia| lia]. }
    rewrite (dec_mremap_of_expected img_avoid B OL ND dst EN RR DOK).
    cbn [twf]. split; [exact SE|]. right. exists dst. split; [reflexivity|].
    refine (conj D0 (conj DA (conj _ (conj VM (conj MI' (conj MH' (conj KL (conj MMT' (conj _ NBI))))))))); [idtac; exact DC|].
    destruct CASE as [(Ed & X & _)|(NEd & LT & RF & _)].
    + left. split; [exact Ed|]. destruct X as [X|[_ X]]; [left; exact X| right; exact X].
    + right. split; [exact NEd|]. split; [exact LT| exact RF].
Qed.


(* [comment removed for export] *)
Lemma zeros_cover1_iff (b n x : word) :
  zeros_cover [(b, n)] x = true <-> (bv_unsigned b <= bv_unsigned x < bv_unsigned b + bv_unsigned n)%Z.
Proof.
  unfold zeros_cover. cbn [existsb fst snd]. rewrite orb_false_r.
  split; [intros H; apply andb_prop in H as [A C]; apply Z.leb_le in A; apply Z.ltb_lt in C; lia|].
  intros H. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
(* [comment removed for export] *)

Lemma mremap_raw_facts (m2 : mem) (B OL ND : Z) (dst : word) :
  let NB := bv_unsigned dst in let mK := mremap_raw B OL ND dst m2 in
  0 < B -> B + OL <= alloc_ceiling -> 4096 <= OL -> OL mod 4096 = 0 -> 4096 <= ND -> ND mod 4096 = 0 ->
  NB + ND <= alloc_ceiling -> OL <> ND -> (dst <> Z_to_bv 64 B -> OL < ND) ->
  (forall o, 0 <= o < OL -> m2 (Z_to_bv 64 (B + o)) <> None) ->
  (forall o, 0 <= o < Z.min OL ND -> mK (Z_to_bv 64 (NB + o)) = m2 (Z_to_bv 64 (B + o)))
  /\ (forall o, 0 <= o < ND -> mK (Z_to_bv 64 (NB + o)) <> None)
  /\ (forall a, 0 <= a < 2^64 -> ~ (NB <= a < NB + ND) -> ~ (B <= a < B + OL) -> mK (Z_to_bv 64 a) = m2 (Z_to_bv 64 a))
  /\ (forall (x : word) (v : byte), mK x = Some v -> m2 x = Some v \/ (NB <= bv_unsigned x < NB + ND)).
Proof.
  intros NB mK B0 BC OL0 OLA ND0 NDA DC NE MOVE MAPPED.
  pose proof alloc_ceiling_val as ACV.
  pose proof (bv_unsigned_in_range _ dst) as DR. change (bv_modulus 64) with (2^64) in DR. fold NB in DR.
  assert (MOL : mrlen OL = OL). { unfold mrlen, mw. rewrite unsigned_lit by lia. rewrite <- (KLink.mmap_len_of_aligned OL) at 2 by lia. reflexivity. }
  assert (MND : mrlen ND = ND). { unfold mrlen, mw. rewrite unsigned_lit by lia. rewrite <- (KLink.mmap_len_of_aligned ND) at 2 by lia. reflexivity. }
  assert (Edst : dst = Z_to_bv 64 NB) by (symmetry; apply Z_to_bv_bv_unsigned).
  subst mK. unfold mremap_raw, mremap_expected. rewrite MOL, MND. rewrite (proj2 (Z.eqb_neq OL ND) NE).
  unfold mw, mwlen. rewrite MOL, MND.
  destruct (bv_eqb dst (Z_to_bv 64 B)) eqn:Q.
  - (* [comment removed for export] *) apply bv_eqb_true_iff in Q. assert (ENB : NB = B) by (subst NB; rewrite Q; apply unsigned_lit; lia).
    rewrite ENB. unfold mremap_inplace_effect, eff_mem. cbn [eff_unmaps eff_zeros eff_copies eff_writes apply_writes apply_copies].
    destruct (ND <? OL) eqn:L; [apply Z.ltb_lt in L| apply Z.ltb_ge in L].
    + (* [comment removed for export] *) cbn [eff_unmaps eff_zeros eff_copies eff_writes apply_writes apply_copies apply_zeros apply_unmaps].
      assert (CV : forall x : word, zeros_cover [((Z_to_bv 64 B + Z_to_bv 64 ND)%bv, Z_to_bv 64 (OL - ND))] x = true <-> B + ND <= bv_unsigned x < B + OL).
      { intros x. rewrite zeros_cover1_iff, lit_add_lit, !unsigned_lit by lia. lia. }
      split; [| split; [| split]].
      * intros o Ho. destruct (zeros_cover _ _) eqn:C; [| reflexivity]. apply CV in C. rewrite unsigned_lit in C by lia. lia.
      * intros o Ho. destruct (zeros_cover _ _) eqn:C; [apply CV in C; rewrite unsigned_lit in C by lia; lia|]. apply MAPPED. lia.
      * intros a Ha N1 N2. destruct (zeros_cover _ _) eqn:C; [| reflexivity]. apply CV in C. rewrite unsigned_lit in C by lia. lia.
      * intros x v Hx. destruct (zeros_cover _ _) eqn:C; [discriminate| left; exact Hx].
    + (* [comment removed for export] *) unfold mremap_tail. rewrite (proj2 (Z.ltb_lt OL ND)) by lia.
      cbn [eff_unmaps eff_zeros eff_copies eff_writes apply_writes apply_copies apply_zeros apply_unmaps].
      assert (CV : forall x : word, zeros_cover [((Z_to_bv 64 B + Z_to_bv 64 OL)%bv, Z_to_bv 64 (ND - OL))] x = true <-> B + OL <= bv_unsigned x < B + ND).
      { intros x. rewrite zeros_cover1_iff, lit_add_lit, !unsigned_lit by lia. lia. }
      split; [| split; [| split]].
      * intros o Ho. destruct (zeros_cover _ _) eqn:C; [| reflexivity]. apply CV in C. rewrite unsigned_lit in C by lia. lia.
      * intros o Ho. destruct (zeros_cover _ _) eqn:C; [discriminate|]. apply MAPPED.
        destruct (Z_lt_le_dec o OL); [lia|]. exfalso. assert (C' : zeros_cover [((Z_to_bv 64 B + Z_to_bv 64 OL)%bv, Z_to_bv 64 (ND - OL))] (Z_to_bv 64 (B + o)) = true) by (apply CV; rewrite unsigned_lit by lia; lia). congruence.
      * intros a Ha N1 N2. destruct (zeros_cover _ _) eqn:C; [| reflexivity]. apply CV in C. rewrite unsigned_lit in C by lia. lia.
      * intros x v Hx. destruct (zeros_cover _ _) eqn:C; [right; apply CV in C; lia| left; exact Hx].
  - (* [comment removed for export] *)
    assert (NEd : dst <> Z_to_bv 64 B) by (intros E; rewrite E, bv_eqb_refl in Q; discriminate).
    specialize (MOVE NEd).
    unfold mremap_move_effect, mremap_tail, eff_mem. rewrite (proj2 (Z.ltb_lt OL ND)) by lia.
    cbn [eff_unmaps eff_zeros eff_copies eff_writes apply_writes apply_copies apply_zeros apply_unmaps].
    rewrite Edst. unfold apply_copy. cbn [copy_dst copy_len copy_src]. rewrite lit_add_lit.
    assert (CVU : forall x : word, zeros_cover [(Z_to_bv 64 B : word, Z_to_bv 64 OL)] x = true <-> B <= bv_unsigned x < B + OL).
    { intros x. rewrite zeros_cover1_iff, !unsigned_lit by lia. lia. }
    assert (CVZ : forall x : word, zeros_cover [(Z_to_bv 64 (NB + OL) : word, Z_to_bv 64 (ND - OL))] x = true <-> NB + OL <= bv_unsigned x < NB + ND).
    { intros x. rewrite zeros_cover1_iff, !unsigned_lit by lia. lia. }
    rewrite !unsigned_lit by lia.
    split; [| split; [| split]].
    + intros o Ho. rewrite unsigned_lit by lia. rewrite (proj2 (Z.leb_le _ _)), (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
      f_equal. f_equal. lia.
    + intros o Ho. rewrite unsigned_lit by lia.
      destruct (Z.leb_spec0 NB (NB + o)); destruct (Z.ltb_spec0 (NB + o) (NB + OL)); cbn [andb]; try lia.
      * replace (B + (NB + o - NB)) with (B + o) by lia. apply MAPPED. lia.
      * destruct (zeros_cover _ _) eqn:C; [discriminate|]. exfalso.
        assert (C' : zeros_cover [(Z_to_bv 64 (NB + OL) : word, Z_to_bv 64 (ND - OL))] (Z_to_bv 64 (NB + o)) = true) by (apply CVZ; rewrite unsigned_lit by lia; lia). congruence.
    + intros a Ha N1 N2. rewrite unsigned_lit by lia.
      destruct (Z.leb_spec0 NB a); destruct (Z.ltb_spec0 a (NB + OL)); cbn [andb]; try lia.
      all: destruct (zeros_cover [(Z_to_bv 64 (NB + OL) : word, _)] _) eqn:C; [apply CVZ in C; rewrite unsigned_lit in C by lia; lia|].
      all: destruct (zeros_cover [(Z_to_bv 64 B : word, Z_to_bv 64 OL)] (Z_to_bv 64 a)) eqn:C2; [apply CVU in C2; rewrite unsigned_lit in C2 by lia; lia| reflexivity].
    + intros x v Hx. pose proof (bv_unsigned_in_range _ x) as XR.
      destruct (Z.leb_spec0 NB (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) (NB + OL)); cbn [andb] in Hx; try (right; lia).
      all: destruct (zeros_cover [(Z_to_bv 64 (NB + OL) : word, _)] _) eqn:C; [apply CVZ in C; right; lia|].
      all: destruct (zeros_cover [(Z_to_bv 64 B : word, Z_to_bv 64 OL)] x) eqn:C2; [discriminate| left; exact Hx].
Qed.

(* [comment removed for export] *)
Lemma bytes_at1_shift (mm mm' : word -> option byte) a a' v :
  bytes_at rsegs mm a [v] -> mm (wa a) <> None -> 0 <= a' -> a' + 1 <= 2^64 -> mm' (wa a') = mm (wa a) -> bytes_at rsegs mm' a' [v].
Proof.
  ((first [ intro dR_15; dand3 dR_15 as H0 H1 HB | intros (H0 & H1 & HB) ]); intros NN L0 L1 AG). split; [exact L0|]. split; [cbn [length Z.of_nat Pos.of_succ_nat]; lia|].
  intros k Hk. cbn [length] in Hk. assert (k = 0%nat) by lia. subst k.
  specialize (HB 0%nat ltac:(cbn; lia)). cbn [Z.of_nat nth_error] in HB |- *. rewrite Z.add_0_r in HB |- *.
  unfold mrd in HB |- *. rewrite AG. destruct (mm (wa a)); [exact HB| congruence].
Qed.

(* [comment removed for export] *)
Lemma remap_mem_outside m G NB ND base n mword b3 (x : word) :
  0 <= G -> G + 40 <= 2^64 -> 0 <= NB -> NB + ND <= 2^64 -> 0 <= base -> 0 <= n -> NB + base + 16 + n <= NB + ND - 4 ->
  ~ (G + 16 <= bv_unsigned x < G + 24) -> ~ (G + 32 <= bv_unsigned x < G + 40) ->
  bv_unsigned x <> NB + base + 16 - 3 -> ~ (NB + base + 16 + n <= bv_unsigned x <= NB + ND - 4) ->
  remap_mem m G NB ND base n mword b3 x = m x.
Proof.
  intros G0 G40 NB0 NDH B0 N0 FIT X1 X2 X3 X4. unfold remap_mem. cbv zeta.
  pose proof (length_le8 (MRep.wz NB)) as L1. pose proof (length_le8 (MRep.wz (mword mod 4096 + ND))) as L2.
  rewrite set_size_mem_outside by lia.
  rewrite !write_other by (cbn [length]; rewrite ?L1, ?L2; lia). reflexivity.
Qed.

Lemma remap_mem_mono m G NB ND base n mword b3 (x : word) :
  0 <= G -> G + 40 <= 2^64 -> 0 <= NB -> NB + ND <= 2^64 -> 0 <= base -> 0 <= n -> NB + base + 16 + n <= NB + ND - 4 ->
  m x <> None -> remap_mem m G NB ND base n mword b3 x <> None.
Proof.
  intros G0 G40 NB0 NDH B0 N0 FIT Hm. unfold remap_mem. cbv zeta.
  pose proof (length_le8 (MRep.wz NB)) as L1. pose proof (length_le8 (MRep.wz (mword mod 4096 + ND))) as L2.
  apply set_size_mem_mono; try lia.
  repeat (apply write_mono; [cbn [length]; rewrite ?L1, ?L2; lia| cbn [length]; rewrite ?L1, ?L2; lia|]). exact Hm.
Qed.

Theorem mremap_path_rz_proof {Rr : RunRandom} :   (* [comment removed for export] *)
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (m m1 : mem) (md : Model) (s : PState) (LB : list block) (b : block) (p n old : Z) (T : TSet)
         (st : mstate) (off : Z) (g bm : aptr) (i : Z) (r : region) (ar : area) (q res : Z)
         (t2y t3y t4y : word),
    let mr := get_meta_rec st g in
    let stride := get_stride mr in
    let c := blk_slot b in
    let E := r_base r + snd c + stride - 4 in
    (* [comment removed for export] *)
    p0_ainv (mkIAS s LB Rr) m md -> mem_inv rsegs m ->
    a0 = wz p -> a1 = wz n -> 0 <= n < 2^32 -> p <> 0 -> p0_live (mkIAS s LB Rr) p = Some old ->
    lb_bytes LB + n <= LIVE_MAX -> zlen LB + 1 <= NLIVE_MAX ->   (* [comment removed for export] *)
    tp = al_tp LayoutPU -> bv_unsigned sp mod 16 = 0 -> bv_unsigned ra mod 4 = 0 ->
    alloc_ceiling <= bv_unsigned sp - AllocSpec.REALLOC_STACK ->
    mapped m (bv_unsigned sp - AllocSpec.REALLOC_STACK) AllocSpec.REALLOC_STACK ->
    realloc_K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m md (mkIAS s LB Rr) p n old T ->
    (* [comment removed for export] *)
    p0_ainv (mkIAS s LB Rr) m1 md -> mem_inv rsegs m1 ->
    (forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 64 <= a < bv_unsigned sp) -> m1 (Z_to_bv 64 a) = m (Z_to_bv 64 a)) ->
    (forall a, 0 <= a < 2^64 -> m (Z_to_bv 64 a) <> None -> m1 (Z_to_bv 64 a) <> None) ->
    rw_cells rsegs m1 (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    mapped m1 (bv_unsigned sp - 64 - 8192) 8192 ->
    (* [comment removed for export] *)
    In b LB -> blk_addr b = p -> blk_size b = old ->
    heap_wit s LB m1 st -> ps_m s = strip st -> mrep st m1 -> ticks_ok st ->
    p = r_base r + snd c + UNIT * off -> rbf st m1 c off old g bm i r ar q res ->
    (* [comment removed for export] *)
    MMAP_THRESHOLD <= n -> m_sizeclass mr = 63 ->
    realizes rsegs (mkCfg (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp
                                  (wz E) (wz (conc st bm + 16 + stride * i)) t2y s0 (Z_to_bv 64 (conc st g)) a0 a1
                                  (wz (conc st bm)) (wz (m_sizeclass mr)) (Z_to_bv 64 (meta_word mr)) t3y (wz (E + 4)) (wz (E - p)) (wz (p + old))
                                  s3 s4 s5 s6 s7 s8 s9 s10 s11 t4y t4 t5 t6)
                             bvmap_empty (wz 0x24e74) (Z_to_bv 32 0) None m1 (seg_rom rsegs)) md) T.
Proof.
  intros until t4y. intros mr stride c E AI MI A0 A1 NR PNZ LV BYTES NLV TP SPA RAA CEIL MAP K AI1 MI1 AGo MONO1 FR1 MAP1 Hb Eaddr Esize HWT Hst MR TK HA RB NT SC63.
  pose proof (ainv_KI _ _ _ AI) as [Hh Hl].
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (bv_unsigned_in_range _ ra) as RAR. change (bv_modulus 64) with (2^64) in RAR.
  pose proof alloc_ceiling_val as ACV.
  unfold AllocSpec.REALLOC_STACK in *.
  assert (SP64 : 0 <= bv_unsigned sp - 64 < 2^64) by (try (generalize alloc_ceiling_val); clear - SPR CEIL ACV; lia).
  (first [ pose proof ((p0_live_ok _ m md p old AI LV)) as dR_2; dand7 dR_2 as OLD0 P16 P4096 PC PIMG PM PNO | pose proof (p0_live_ok _ m md p old AI LV) as (OLD0 & P16 & P4096 & PC & PIMG & PM & PNO) ]). cbn [al_image_lo al_image_hi LayoutPU] in PIMG.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  (* [comment removed for export] *)
  pose proof (rbf63_facts _ _ _ _ _ _ _ _ _ _ _ _ RB SC63) as RF. cbv zeta in RF. fold mr in RF.
  (first [ dand17 RF as I0 LI0 FRE BM0 EC MLR STR OLR OL4 OLA Qoff ERES MW R0 RAL RC RI | destruct RF as (I0 & LI0 & FRE & BM0 & EC & MLR & STR & OLR & OL4 & OLA & Qoff & ERES & MW & R0 & RAL & RC & RI) ]).
  idtac.
  set (B := r_base r) in *. set (OL := m_maplen mr * 4096) in *. set (G := conc st g) in *.
  fold stride in STR.
  assert (Ec2 : snd c = 16) by (rewrite EC; reflexivity).
  assert (HP : p = B + 16 + UNIT * off) by (rewrite HA, Ec2; reflexivity).
  assert (EEq : E = B + OL - 4) by (subst E; rewrite Ec2, STR; clear; lia).
  assert (CB : conc st bm = B).
  { subst B. rewrite (conc_region' st bm r); [rewrite BM0; clear; lia|].
    rewrite <- (rb_fst _ _ _ _ _ _ _ _ _ _ _ _ RB). exact (rb_reg _ _ _ _ _ _ _ _ _ _ _ _ RB). }
  pose proof (rb_off _ _ _ _ _ _ _ _ _ _ _ _ RB) as HOFF.
  pose proof (rb_fit _ _ _ _ _ _ _ _ _ _ _ _ RB) as FIT. fold mr stride in FIT. rewrite STR in FIT.
  pose proof (rb_res _ _ _ _ _ _ _ _ _ _ _ _ RB) as [_ RES0].
  rewrite CB. replace (B + 16 + stride * i) with (B + 16) by (rewrite I0; clear; lia).
  replace (meta_word mr) with (0 + 32 * 1 + 64 * 63 + 4096 * m_maplen mr) by (rewrite MW; clear; lia).
  change (Z_to_bv 64 (B + 16)) with (wz (B + 16)). change (Z_to_bv 64 B) with (wz B).
  assert (HPa0 : bv_unsigned a0 = p) by (rewrite A0; apply unsigned_lit; try (generalize alloc_ceiling_val); clear - P4096 PC ACV OLD0; lia).
  assert (HN : bv_unsigned a1 = n) by (rewrite A1; apply unsigned_lit; try (generalize alloc_ceiling_val); clear - NR; lia).
  pose proof (needed_of_props n (UNIT * off) ltac:(try (generalize alloc_ceiling_val); clear - NR; lia) ltac:(try (generalize alloc_ceiling_val); clear - HOFF; unfold UNIT; lia)) as [ND1 ND2].
  set (ND := needed_of n (UNIT * off)) in *.
  assert (HA' : blk_addr b = r_base r + snd (blk_slot b) + UNIT * off) by (rewrite Eaddr; exact HA).
  assert (RB' : rbf st m1 (blk_slot b) off (blk_size b) g bm i r ar q res) by (rewrite Esize; exact RB).
  assert (ESP : wz (bv_unsigned sp - 64 + 64) = sp) by (unfold MRep.wz; replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) by (clear; lia); apply Z_to_bv_bv_unsigned).
  assert (RET : ret_pc ra = ra).
  { rewrite <- (definitions.Z_to_bv_bv_unsigned 64 ra) at 1. rewrite ret_pc_even; [apply definitions.Z_to_bv_bv_unsigned| try (generalize alloc_ceiling_val); clear - RAR; lia| ].
    clear - RAA RAR. Z.div_mod_to_equations. lia. }
  set (b3 := i + 32 * Z.min res 5) in *.
  assert (B3R : 0 <= b3 < 256) by (subst b3; rewrite I0; try (generalize alloc_ceiling_val); clear - RES0; lia).
  pose proof (mrep_meta_chunk st m1 g MR (rb_mslot _ _ _ _ _ _ _ _ _ _ _ _ RB)) as MM. fold mr G in MM.
  pose proof (proj2 MM) as WRG. cbn [cells_size csize meta_cells Nat.add length] in WRG.
  assert (RDW : ov_read_bytes rsegs m1 (wa (G + 32)) 8 = Some (le8 (wz (meta_word mr)))).
  { eapply (rw_cells_read_at rsegs m1 G _ 32 (C8 (wz (meta_word mr))) 8); [exact MM| reflexivity| reflexivity| reflexivity]. }
  assert (WRB : wr_at rsegs m1 B OL) by (rewrite OLR; exact (rb_wr _ _ _ _ _ _ _ _ _ _ _ _ RB)).
  assert (RD3 : bytes_at rsegs m1 (p - 3) [b8 b3]).
  { replace (p - 3) with (r_base r + snd c + UNIT * off - 3) by (rewrite HA; clear; lia). exact (rb_rd3 _ _ _ _ _ _ _ _ _ _ _ _ RB). }
  (* [comment removed for export] *)
  assert (FIN : forall (RA0 T0 T1 T2 A3 A4 A5 A6 A7 S5 S6 T3 T4 T5 T6 : word) (dst : word) (mK : mem) (md' : Model),
    let NB := bv_unsigned dst in
    ( (ND = OL /\ NB = B /\ md' = md)
      \/ (ND <> OL /\ 0 < NB /\ NB mod 4096 = 0 /\ NB + ND <= alloc_ceiling
          /\ m_vmmaps md' = mremap_maps_next (m_vmmaps md) (wz B) dst (wz ND) /\ minv md' /\ m_halted md' = None /\ m_vm_lazy md' = [] /\ m_vm_materialized md' = []
          /\ ((dst = wz B /\ (ND < OL \/ region_free (vm_reserved (m_vmmaps md) ++ map_remove (vm_maps (m_vmmaps md)) (wz B)) (wz B) (wz ND) = true))
              \/ (dst <> wz B /\ region_free (vm_reserved (m_vmmaps md) ++ vm_maps (m_vmmaps md)) dst (wz ND) = true))) ) ->
    (forall o, 0 <= o < Z.min OL ND -> mK (wz (NB + o)) = m1 (wz (B + o))) ->
    (forall o, 0 <= o < ND -> mK (wz (NB + o)) <> None) ->
    (forall a, 0 <= a < alloc_ceiling -> ~ (NB <= a < NB + ND) -> ~ (B <= a < B + OL) -> mK (wz a) = m1 (wz a)) ->
    (forall a, alloc_ceiling <= a < 2^64 -> ~ (bv_unsigned sp - 64 - 112 <= a < bv_unsigned sp - 64) -> mK (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) ->
    (forall a, bv_unsigned sp - 64 - 8192 <= a < bv_unsigned sp - 64 -> mK (Z_to_bv 64 a) <> None) ->
    mem_inv rsegs mK ->
    (NB + ND <= 0x10000 \/ 0x64000 <= NB) ->
    same_env md md' -> KI md' ->
    realizes rsegs (mkCfg (MS (mkR RA0 (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp T0 T1 T2 (wz ND) (Z_to_bv 64 G) a0 a1 dst A3 A4 A5 A6 A7
                                  (Z_to_bv 64 (p + old)) (wz (UNIT * off)) (wz 4095) S5 S6 s7 s8 s9 s10 s11 T3 T4 T5 T6)
                             bvmap_empty (wz 0x24ec4) (Z_to_bv 32 0) None mK (seg_rom rsegs)) md') T).
  { intros until md'. intros NB KERN CPY NN OUT OUTHI STK MIK NBI SE [Hh' Hl'].
    cbv delta [MRep.wz KLink.wz] in KERN, CPY, NN, OUT. cbv delta [MRep.wz KLink.wz].
    pose proof (bv_unsigned_in_range _ dst) as DR. change (bv_modulus 64) with (2^64) in DR. fold NB in DR.
    (first [ pose proof ((remap_model (Clg:=Clg) s LB m1 md b st off g bm i r ar q res n dst md' mK AI1 Hb HWT HA' RB' SC63 ltac:(split; [exact NT| try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia]))) as dR_4; dex1 dR_4 as s'; dand14 dR_4 as EBR EFA ESO AI' DLT LVA LVO LVM INB' INB SEP MG1 MG2 MOWN | pose proof ((remap_model (Clg:=Clg) s LB m1 md b st off g bm i r ar q res n dst md' mK AI1 Hb HWT HA' RB' SC63 ltac:(split; [exact NT| try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia]))) as dR_4; dand15 dR_4 as s' EBR EFA ESO AI' DLT LVA LVO LVM INB' INB SEP MG1 MG2 MOWN | destruct (remap_model (Clg:=Clg) s LB m1 md b st off g bm i r ar q res n dst md' mK AI1 Hb HWT HA' RB' SC63 ltac:(split; [exact NT| try (generalize alloc_ceiling_val); clear - NR; try pose proof alloc_ceiling_val; lia]))
      as (s' & EBR & EFA & ESO & AI' & DLT & LVA & LVO & LVM & INB' & INB & SEP & MG1 & MG2 & MOWN) ]).
    { cbv zeta. fold mr. fold B OL ND NB. exact KERN. }
    { cbv zeta. fold mr. fold B OL ND NB. exact CPY. }
    { cbv zeta. fold mr. fold ND NB. exact NN. }
    { cbv zeta. fold mr. fold B OL ND NB. exact OUT. }
    cbv zeta in AI', DLT, LVA, LVO, LVM, INB', INB, SEP, MG1, MG2, MOWN. fold mr B OL ND NB G b3 in AI', DLT, LVA, LVO, LVM, INB', INB, SEP, MG1, MG2, MOWN.
    rewrite Eaddr, Esize in *.
    set (A' := NB + 16 + UNIT * off) in *. set (LB' := lb_remap b A' n LB) in *.
    set (mF := remap_mem mK G NB ND (UNIT * off) n (meta_word mr) b3).
    change (p0_ainv (mkIAS s' LB' Rr) mF md') in AI'.
    change (forall y, In y LB -> y <> b -> (blk_addr y + blk_size y <= NB \/ NB + ND <= blk_addr y) /\ (blk_addr y + blk_size y <= B \/ B + OL <= blk_addr y)
                      /\ 0 <= blk_addr y /\ blk_addr y + blk_size y <= alloc_ceiling) in SEP.
    change (G + 40 <= NB \/ NB + ND <= G) in MG1. change (G + 40 <= B \/ B + OL <= G) in MG2.
    change (NB <> B -> p0_live (mkIAS s LB Rr) A' = None /\ p0_live (mkIAS s' LB' Rr) p = None) in LVM.
    idtac.
    assert (GLO : 0 <= G /\ G + 40 <= alloc_ceiling).
    { destruct (MOWN G ltac:(clear; lia)) as [O1 _]. destruct (MOWN (G + 39) ltac:(clear; lia)) as [O2 _].
      pose proof (p0_owned_below _ _ _ _ AI1 O1) as X1. pose proof (p0_owned_below _ _ _ _ AI1 O2) as X2. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). try (generalize alloc_ceiling_val); clear - X1 X2. lia. }
    assert (NBC : 0 < NB /\ NB + ND <= alloc_ceiling).
    { destruct KERN as [(E1 & E2 & _)|(_ & X1 & _ & X2 & _)]; [rewrite E2, E1; try (generalize alloc_ceiling_val); clear - R0 RC; lia| try (generalize alloc_ceiling_val); clear - X1 X2; lia]. }
    assert (AGG : forall x : word, G <= bv_unsigned x < G + Z.of_nat (cells_size (meta_cells st mr)) -> mK x = m1 x).
    { intros x Hx. cbn [cells_size csize meta_cells Nat.add length] in Hx. rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x).
      pose proof (bv_unsigned_in_range _ x). apply OUT; [try (generalize alloc_ceiling_val); clear - Hx GLO H; lia| try (generalize alloc_ceiling_val); clear - Hx MG1; lia| try (generalize alloc_ceiling_val); clear - Hx MG2; lia]. }
    pose proof (InstDefs.rw_cells_agree' m1 mK G _ MM AGG) as MMK.
    assert (FRK : rw_cells rsegs mK (bv_unsigned sp - 64) [C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply InstDefs.rw_cells_agree'; [exact FR1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x).
      pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR. apply OUTHI; try (generalize alloc_ceiling_val); clear - Hx SPR CEIL XR; lia. }
    assert (WN : wr_at rsegs mK NB ND).
    { split; [try (generalize alloc_ceiling_val); clear - NBC; lia|]. split; [try (generalize alloc_ceiling_val); clear - NBC; lia|]. intros i0 Hi0. rewrite p0_wview_overlay by (unfold wa; rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Hi0 NBC; lia); try (generalize alloc_ceiling_val); clear - Hi0 NBI NBC; lia).
      unfold wa. apply NN. exact Hi0. }
    assert (BK : bytes_at rsegs mK (NB + UNIT * off + 16 - 3) [b8 b3]).
    { eapply (bytes_at1_shift m1 mK (p - 3)); [exact RD3| | try (generalize alloc_ceiling_val); clear - NBC HOFF; unfold UNIT; lia| try (generalize alloc_ceiling_val); clear - NBC HOFF ND1 NR; unfold UNIT in *; lia|].
      { pose proof (proj2 (proj2 WRB) (p - 3 - B) ltac:(rewrite HP; try (generalize alloc_ceiling_val); clear - HOFF FIT OLD0; unfold UNIT, IB in *; lia)) as W.
        replace (B + (p - 3 - B)) with (p - 3) in W by (clear; lia).
        rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit by (rewrite HP; try (generalize alloc_ceiling_val); clear - R0 RC HOFF OL4; unfold UNIT; lia); rewrite HP; try (generalize alloc_ceiling_val); clear - RI HOFF FIT OLD0 R0 OL4; unfold UNIT, IB in *; lia). exact W. }
      unfold wa. replace (NB + UNIT * off + 16 - 3) with (NB + (UNIT * off + 13)) by (clear; lia). rewrite HP.
      replace (B + 16 + UNIT * off - 3) with (B + (UNIT * off + 13)) by (clear; lia). apply CPY. try (generalize alloc_ceiling_val); clear - HOFF FIT OLD0 ND1 NR. unfold UNIT, IB in *. lia. }
    eapply rz_evt; [| exact Hh'| exact Hl'|].
    { eapply (realloc_remap_walk RA0 _ gp tp T0 T1 T2 _ a0 a1 dst A3 A4 A5 A6 A7 _ S5 S6 s7 s8 s9 s10 s11 T3 T4 T5 T6 _ _ mK
                ra s0 s1 s2 s3 s4 s5 s6 G NB ND (UNIT * off) n (meta_word mr) b3).
      - exact HN.
      - reflexivity.
      - try (generalize alloc_ceiling_val); clear - NBC ND1 NR HOFF. unfold UNIT in *. lia.
      - apply unsigned_lit. try (generalize alloc_ceiling_val); clear - GLO. lia.
      - try (generalize alloc_ceiling_val); clear - NR. lia.
      - try (generalize alloc_ceiling_val); clear - HOFF. unfold UNIT. lia.
      - try (generalize alloc_ceiling_val); clear - ND1. unfold UNIT in *. lia.
      - try (generalize alloc_ceiling_val); clear - ND1. unfold UNIT in *. lia.
      - try (generalize alloc_ceiling_val); clear - NBC. lia.
      - try (generalize alloc_ceiling_val); clear - NBC ND1 NR HOFF. unfold UNIT in *. lia.
      - exact ND2.
      - try (generalize alloc_ceiling_val); clear - GLO. lia.
      - try (generalize alloc_ceiling_val); clear - GLO. lia.
      - rewrite MW. try (generalize alloc_ceiling_val); clear - MLR. lia.
      - exact B3R.
      - try (generalize alloc_ceiling_val); clear - MG1. lia.
      - rewrite unsigned_lit by exact SP64. try (generalize alloc_ceiling_val); clear - NBC CEIL. lia.
      - rewrite unsigned_lit by exact SP64. try (generalize alloc_ceiling_val); clear - GLO CEIL. lia.
      - rewrite unsigned_lit by exact SP64. try (generalize alloc_ceiling_val); clear - SPR. lia.
      - exact MIK.
      - eapply (rw_cells_read_at rsegs mK G _ 32 (C8 (wz (meta_word mr))) 8); [exact MMK| reflexivity| reflexivity| reflexivity].
      - eapply wr_at_sub; [exact (proj2 MMK)| clear; lia| cbn [cells_size csize meta_cells Nat.add length]; clear; lia].
      - exact WN.
      - exact BK.
      - rewrite unsigned_lit by exact SP64. exact FRK. }
    (intros ms5; (first [ intro dR_16; dex11 dR_16 as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 m'; dand4 dR_16 as -> Em' MI' FR' | intro dR_16; dand15 dR_16 as u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 m' -> Em' MI' FR' | intros (u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & m' & -> & Em' & MI' & FR') ])).
    rewrite unsigned_lit in FR' by exact SP64. rewrite unsigned_lit by exact SP64. unfold MRep.wz. rewrite ESP, RET, <- mkst_MS'.
    replace (NB + UNIT * off + 16) with A' by (subst A'; clear; lia).
    (* [comment removed for export] *)
    assert (RMO : forall x : word, ~ (G + 16 <= bv_unsigned x < G + 24) -> ~ (G + 32 <= bv_unsigned x < G + 40) ->
                  bv_unsigned x <> A' - 3 -> ~ (A' + n <= bv_unsigned x <= NB + ND - 4) -> m' x = mK x).
    { intros x X1 X2 X3 X4. rewrite Em'. apply remap_mem_outside; subst A'; try (try (generalize alloc_ceiling_val); clear - GLO NBC HOFF NR ND1 X1 X2 X3 X4; unfold UNIT in *; lia). }
    assert (RMM : forall x : word, mK x <> None -> m' x <> None).
    { intros x Hx. rewrite Em'. apply remap_mem_mono; try (try (generalize alloc_ceiling_val); clear - GLO NBC HOFF NR ND1 Hx; unfold UNIT in *; lia). exact Hx. }
    assert (CHG : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp) -> ~ (NB <= a < NB + ND) -> ~ (B <= a < B + OL) ->
                  ~ (G + 16 <= a < G + 24) -> ~ (G + 32 <= a < G + 40) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
    { intros a Ha NW N1 N2 N3 N4. rewrite RMO by (rewrite unsigned_lit by exact Ha; subst A'; try (generalize alloc_ceiling_val); clear - N1 N3 N4 ND1 HOFF NR; unfold UNIT in *; lia).
      destruct (Z_lt_le_dec a alloc_ceiling) as [LO|HI].
      - rewrite OUT by (try (generalize alloc_ceiling_val); clear - Ha LO N1 N2; lia). apply AGo; [exact Ha| try (generalize alloc_ceiling_val); clear - NW; lia].
      - rewrite OUTHI by (try (generalize alloc_ceiling_val); clear - Ha HI NW; lia). apply AGo; [exact Ha| try (generalize alloc_ceiling_val); clear - NW; lia]. }
    assert (MONO : forall a, 0 <= a < 2^64 -> ~ (B <= a < B + OL) -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None).
    { intros a Ha N2 Hm. apply RMM.
      destruct (classic (NB <= a < NB + ND)) as [IN1|N1].
      { replace a with (NB + (a - NB)) by (clear; lia). apply NN. try (generalize alloc_ceiling_val); clear - IN1; lia. }
      destruct (Z_lt_le_dec a alloc_ceiling) as [LO|HI].
      - rewrite OUT by (try (generalize alloc_ceiling_val); clear - Ha LO N1 N2; lia). apply MONO1; [exact Ha| exact Hm].
      - destruct (classic (bv_unsigned sp - 64 - 112 <= a < bv_unsigned sp - 64)) as [W|NW].
        + apply STK. try (generalize alloc_ceiling_val); clear - W; lia.
        + rewrite OUTHI by (try (generalize alloc_ceiling_val); clear - Ha HI NW; lia). apply MONO1; [exact Ha| exact Hm]. }
    assert (OWNb : forall a, B <= a < B + OL -> ~ (p <= a < p + old) -> p0_owned (mkIAS s LB Rr) a).
    { intros a Ha Na. right. split; [apply heap_zone_p0; try (generalize alloc_ceiling_val); clear - Ha RC RI R0; lia|]. cbn [ia_LB]. rewrite INB.
      intros [X|(y & Hy & NEy & X)]; [exact (Na X)|]. (first [ pose proof ((SEP y Hy NEy)) as dR_5; dand3 dR_5 as _ Y _ | destruct (SEP y Hy NEy) as (_ & Y & _) ]). try (generalize alloc_ceiling_val); clear - Ha X Y. lia. }
    assert (OWNn : forall a, NB <= a < NB + ND -> ~ (A' <= a < A' + n) -> p0_owned (mkIAS s' LB' Rr) a).
    { intros a Ha Na. right. split; [apply heap_zone_p0; try (generalize alloc_ceiling_val); clear - Ha NBC NBI; lia|]. cbn [ia_LB]. rewrite INB'.
      intros [X|(y & Hy & NEy & X)]; [exact (Na X)|]. destruct (SEP y Hy NEy) as (Y & _). try (generalize alloc_ceiling_val); clear - Ha X Y. lia. }
    assert (PB : B + 16 <= p /\ p + old <= B + OL - 4) by (rewrite HP; try (generalize alloc_ceiling_val); clear - HOFF FIT OLD0; unfold UNIT, IB in *; lia).
    assert (PA : NB + 16 <= A' /\ A' + n <= NB + ND - 4) by (subst A'; try (generalize alloc_ceiling_val); clear - HOFF ND1 NR; unfold UNIT in *; lia).
    assert (A0' : A' <> 0) by (try (generalize alloc_ceiling_val); clear - PA NBC; lia).
    apply (K u0 u1 u2 v1 v2 v3 v4 v5 v6 v7 T3 T4 T5 T6 A' (mkIAS s' LB' Rr) m' md'); unfold AllocSpec.REALLOC_STACK.
    - rewrite Em'. exact AI'.
    - exact MI'.
    - apply md_frame_of_same_env; [exact SE| split; [exact Hh'| exact Hl']].
    - split; [exact A0'|]. split; [exact LVA|]. split.
      { destruct (Z.eq_dec NB B) as [EQB|NEB]; [left; subst A'; rewrite EQB, HP; clear; lia| right; exact (LVM NEB)]. }
      split. { intros qq Hq Hqp. apply LVO; [exact Hq| exact Hqp]. }
      split.
      { intros i0 Hi0. rewrite RMO; cycle 1.
        { rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Hi0 PA NBC; try pose proof alloc_ceiling_val; lia). try (generalize alloc_ceiling_val); clear - Hi0 PA MG1; try pose proof alloc_ceiling_val; lia. }
        { rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Hi0 PA NBC; try pose proof alloc_ceiling_val; lia). try (generalize alloc_ceiling_val); clear - Hi0 PA MG1; try pose proof alloc_ceiling_val; lia. }
        { rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Hi0 PA NBC; try pose proof alloc_ceiling_val; lia). try (generalize alloc_ceiling_val); clear - Hi0 PA; try pose proof alloc_ceiling_val; lia. }
        { rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Hi0 PA NBC; try pose proof alloc_ceiling_val; lia). try (generalize alloc_ceiling_val); clear - Hi0; try pose proof alloc_ceiling_val; lia. }
        subst A'. replace (NB + 16 + UNIT * off + i0) with (NB + (16 + UNIT * off + i0)) by (clear; lia).
        rewrite CPY by (try (generalize alloc_ceiling_val); clear - Hi0 HOFF FIT OLD0 ND1 NR; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia).
        rewrite HP. replace (B + 16 + UNIT * off + i0) with (B + (16 + UNIT * off + i0)) by (clear; lia).
        apply AGo; try (generalize alloc_ceiling_val); clear - Hi0 HOFF FIT OLD0 R0 RC CEIL; try pose proof alloc_ceiling_val; unfold UNIT, IB in *; lia. }
      (* [comment removed for export] *)
      split; [unfold p0_livebytes; cbn [ia_LB]; exact (proj1 DLT)|]. split; [unfold p0_nlive; cbn [ia_LB]; exact (proj2 DLT)|].
      (* [comment removed for export] *)
      unfold frame_ok. rewrite errno_p0. cbn [ia_LB].
      split; [|split; [|split; [|split; [|split; [|split]]]]].
      + intros a Ha NO NO' NW NE NV NN'. apply CHG; [exact Ha| exact NW| | | |].
        * intros X. destruct (classic (A' <= a < A' + n)) as [Y|Y]; [apply NN'; split; [exact A0'| exact Y]| exact (NO' (OWNn a X Y))].
        * intros X. destruct (classic (p <= a < p + old)) as [Y|Y]; [apply NV; split; [exact PNZ| exact Y]| exact (NO (OWNb a X Y))].
        * intros X. apply NO. apply (proj1 (MOWN a ltac:(try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val; lia))).
        * intros X. apply NO. apply (proj1 (MOWN a ltac:(try (generalize alloc_ceiling_val); clear - X; try pose proof alloc_ceiling_val; lia))).
      + intros a Ha NI Hm. destruct (classic (B <= a < B + OL)) as [X|X].
        * destruct (classic (p <= a < p + old)) as [Y|Y]; [right; left; split; [exact PNZ| exact Y]| left; exact (OWNb a X Y)].
        * right; right. apply MONO; [exact Ha| exact X| exact Hm].
      + intros i0 Hi0. unfold MRep.wz. destruct (Z_lt_le_dec (bv_unsigned sp - 8256 + i0) (bv_unsigned sp - 64)) as [LO|HI].
        * apply RMM. apply STK. try (generalize alloc_ceiling_val); clear - Hi0 LO; try pose proof alloc_ceiling_val; lia.
        * destruct FR' as [_ (_ & _ & W)]. cbn [cells_size csize Nat.add] in W.
          specialize (W (bv_unsigned sp - 8256 + i0 - (bv_unsigned sp - 64)) ltac:(try (generalize alloc_ceiling_val); clear - Hi0 HI; try pose proof alloc_ceiling_val; lia)).
          replace (bv_unsigned sp - 64 + (bv_unsigned sp - 8256 + i0 - (bv_unsigned sp - 64))) with (bv_unsigned sp - 8256 + i0) in W by (clear; lia).
          rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit; try (generalize alloc_ceiling_val); clear - Hi0 HI SPR CEIL; try pose proof alloc_ceiling_val; lia). exact W.
      + intros a Ha [_ Ra]. destruct (classic (p <= a < p + old)) as [Y|Y]; [right; left; split; [exact PNZ| exact Y]|].
        left. right. split; [apply heap_zone_p0; try (generalize alloc_ceiling_val); clear - Ra PA NBC NBI; try pose proof alloc_ceiling_val; lia|]. rewrite INB.
        intros [X|(y & Hy & NEy & X)]; [exact (Y X)|]. destruct (SEP y Hy NEy) as (Z1 & _). try (generalize alloc_ceiling_val); clear - Ra PA X Z1; try pose proof alloc_ceiling_val. lia.
      + intros a Ha [St|[HZ NIB']]; [left; left; exact St|].
        destruct (classic (in_block LB a)) as [IB|NIB]; [| left; right; split; [exact HZ| exact NIB]].
        rewrite INB in IB. destruct IB as [X|(y & Hy & NEy & X)]; [right; left; split; [exact PNZ| exact X]|].
        exfalso. apply NIB'. rewrite INB'. right. exists y. auto.
      + intros a Ha [St|[HZ NIB]] NO'; [exfalso; apply NO'; left; exact St|].
        destruct (classic (in_block LB' a)) as [IB'|NIB'']; [| exfalso; apply NO'; right; split; [exact HZ| exact NIB'']].
        rewrite INB' in IB'. destruct IB' as [X|(y & Hy & NEy & X)]; [left; split; [exact A0'| exact X]|].
        exfalso. apply NIB. rewrite INB. right. exists y. auto.
      + intros a Ha [_ Va]. destruct (classic (in_block LB' a)) as [IB'|NIB'].
        * rewrite INB' in IB'. destruct IB' as [X|(y & Hy & NEy & X)]; [right; left; split; [exact A0'| exact X]|].
          exfalso. (first [ pose proof ((SEP y Hy NEy)) as dR_6; dand3 dR_6 as _ Z2 _ | destruct (SEP y Hy NEy) as (_ & Z2 & _) ]). try (generalize alloc_ceiling_val); clear - Va PB X Z2. lia.
        * left. right. split; [apply heap_zone_p0; try (generalize alloc_ceiling_val); clear - Va PB RC RI R0; lia| exact NIB']. }
  (* [comment removed for export] *)
  eapply rz_evt; [| exact Hh| exact Hl|].
  { eapply (realloc_mremap_setup ra _ gp tp _ t2y s0 _ a0 a1 _ t3y _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 t4y t4 t5 t6 _ _ m1 p n (B + 16) B 0 1 63 (m_maplen mr));
      [exact HPa0| exact HN| rewrite HP; try (generalize alloc_ceiling_val); clear - HOFF R0; unfold UNIT; lia| rewrite HP; try (generalize alloc_ceiling_val); clear - NR HOFF RC R0 OL4; unfold UNIT; lia
      | try (generalize alloc_ceiling_val); clear - R0 RC OL4; lia| clear; lia| clear; lia| clear; lia| try (generalize alloc_ceiling_val); clear - MLR; lia]. }
  replace (p - (B + 16)) with (UNIT * off) by (rewrite HP; clear; lia). fold ND.
  intros ms4 [[EQ POST]|[NEQ POST]]; (first [ dand3 POST as a3' a5' -> | destruct POST as (a3' & a5' & ->) ]).
  - (* [comment removed for export] *)
    assert (EQ' : ND = OL) by (cbv delta [OL]; try (generalize alloc_ceiling_val); clear - EQ; lia).
    apply (FIN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (wz B) m1 md); cbv zeta; unfold MRep.wz; rewrite ?unsigned_lit by (try (generalize alloc_ceiling_val); clear - R0 RC OL4; lia).
    + left. split; [exact EQ'|]. split; reflexivity.
    + intros o Ho. reflexivity.
    + intros o Ho. pose proof (proj2 (proj2 WRB) o ltac:(try (generalize alloc_ceiling_val); clear - Ho EQ'; lia)) as W.
      rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Ho EQ' R0 RC OL4; lia); try (generalize alloc_ceiling_val); clear - Ho EQ' RI R0 OL4; lia). exact W.
    + intros a _ _ _. reflexivity.
    + intros a _ _. reflexivity.
    + intros a Ha. replace a with (bv_unsigned sp - 64 - 8192 + (a - (bv_unsigned sp - 64 - 8192))) by (clear; lia). apply MAP1. try (generalize alloc_ceiling_val); clear - Ha; lia.
    + exact MI1.
    + rewrite EQ'. exact RI.
    + apply same_env_refl.
    + split; [exact Hh| exact Hl].
  - (* [comment removed for export] *)
    assert (NEQ' : ND <> OL) by (cbv delta [OL]; try (generalize alloc_ceiling_val); clear - NEQ; lia).
    pose proof (p0_mremap_pre s LB m1 md b st off g bm i r ar q res AI1 Hb HWT RB' SC63) as PRE. cbv zeta in PRE. fold mr in PRE.
    (first [ dand8 PRE as MINV MH MLZ MMT RESV WENT NSAFE CEILMD | destruct PRE as (MINV & MH & MLZ & MMT & RESV & WENT & NSAFE & CEILMD) ]).
    change (forall nd, 0 < nd <= alloc_ceiling -> nd mod 4096 = 0 -> nsafe (NMremap B OL nd MREMAP_MAYMOVE) md) in NSAFE.
    destruct (errno_cell m1) as [errv ERR].
    (first [ pose proof (MR) as dR_9; dand6 dR_9 as WF CX GL ARS GR SHR | pose proof MR as (WF & CX & GL & ARS & GR & SHR) ]). (first [ dand5 GL as _ _ _ GOT GRD | destruct GL as (_ & _ & _ & GOT & GRD) ]).
    pose proof TP as TPv. cbn [al_tp LayoutPU] in TPv.
    assert (ST1 : stk rsegs m1 (bv_unsigned sp - 64 - 8192) (bv_unsigned sp - 64)).
    { apply mapped_stk_p0; [replace (bv_unsigned sp - 64 - (bv_unsigned sp - 64 - 8192)) with 8192 by (clear; lia); exact MAP1| try (generalize alloc_ceiling_val); clear - CEIL ACV; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| try (generalize alloc_ceiling_val); clear - SPR; lia]. }
    assert (MOL : mrlen OL = OL). { unfold mrlen, mw. rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - OL4 RC R0; lia). rewrite <- (KLink.mmap_len_of_aligned OL) at 2 by (try (generalize alloc_ceiling_val); clear - OL4 OLA; lia). reflexivity. }
    assert (NDC : ND <= alloc_ceiling) by (try (generalize alloc_ceiling_val); clear - ND1 NR HOFF; unfold UNIT in *; lia).
    eapply (rz_impl_epost rsegs _ _ _ md (remap_leaf md B OL ND) T); [| exact (conj Hh Hl)| |].
    { eapply (rmremap_spec (wz 151224) (Z_to_bv 64 (bv_unsigned sp - 64)) gp tp (Z_to_bv 64 E) (wz (B + 16)) t2y (wz ND) (Z_to_bv 64 G)
                (wz B) (wz (4096 * m_maplen mr)) (wz ND) (wz 1) a3' a5' (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - p)) (Z_to_bv 64 (p + old))
                (wz (UNIT * off)) (wz 4095) a0 a1 s7 s8 s9 s10 s11 t4y t4 t5 t6 bvmap_empty (Z_to_bv 32 0) m1 img_avoid B OL ND errv (wz run_guard) (bv_unsigned sp - 64 - 8192));   (* [comment removed for export] *)
        rewrite ?(errno_addr_p0 tp TPv), ?unsigned_lit by exact SP64.
      - exact ST1.
      - exact ERR.
      - exact MI1.
      - exact GOT.
      - exact GRD.
      - reflexivity.
      - unfold MRep.wz. f_equal. cbv delta [OL]. clear. lia.
      - reflexivity.
      - reflexivity.
      - try (generalize alloc_ceiling_val); clear - ND1 NR HOFF; try pose proof alloc_ceiling_val. unfold UNIT in *. lia.
      - try (generalize alloc_ceiling_val); clear - R0 RC OL4; try pose proof alloc_ceiling_val. lia.
      - try (generalize alloc_ceiling_val); clear - RC R0 OL4; try pose proof alloc_ceiling_val. lia.
      - clear. lia.
      - try (generalize alloc_ceiling_val); clear - CEIL; try pose proof alloc_ceiling_val. lia.
      - left. unfold PERRNO. try (generalize alloc_ceiling_val); clear - CEIL ACV; try pose proof alloc_ceiling_val. lia.
      - unfold PERRNO, SSP_GUARD. clear. lia.
      - rewrite TPv. rewrite unsigned_lit by (clear; lia). clear. lia.
      - rewrite MOL. exact RC.
      - rewrite MOL. unfold SSP_GUARD. try (generalize alloc_ceiling_val); clear - RI; try pose proof alloc_ceiling_val. lia.
      - exists (0x10000, 0x64000). split; [left; reflexivity|]. cbn [fst snd]. unfold SSP_GUARD. clear. lia. }
    { assert (RC' : B + OL <= alloc_ceiling) by (idtac; exact RC).
      assert (ND4 : 4096 <= ND) by (try (generalize alloc_ceiling_val); clear - ND1 NR NT HOFF; try pose proof alloc_ceiling_val; unfold UNIT, MMAP_THRESHOLD in *; lia).
      assert (NDC' : ND <= alloc_ceiling) by (idtac; exact NDC).
      exact (remap_node_twf md B OL ND MINV MH MLZ MMT CEILMD (NSAFE ND ltac:(try (generalize alloc_ceiling_val); clear - ND4 NDC'; try pose proof alloc_ceiling_val; lia) ND2) RESV R0 RAL OL4 OLA RC' RI ND4 ND2 NDC' NEQ'). }
    intros z ms' md' POST [SE LEAF] [KH' KL'].
    assert (RETc : ret_pc (Z_to_bv 64 151224) = Z_to_bv 64 151224) by (apply ret_pc_even; clear; lia).
    destruct POST as [(e & Ez & He & t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5'' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI' & ST' & ERR')
                     |(rw & Hn & Ez & DOK & t0' & t1' & t2' & a1' & a2' & a3'' & a4' & a5'' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & -> & MU & WM & MI2 & ST' & ERR2)].
    + (* [comment removed for export] *)
      destruct LEAF as [[_ EMD]|(dst & Ez' & _ & _ & DC' & _)].
      2:{ exfalso. pose proof (bv_unsigned_in_range _ dst) as DR. idtac. unfold neg_errno in Ez. try (generalize alloc_ceiling_val); clear - Ez Ez' He DR DC' ND1 NR HOFF; try pose proof alloc_ceiling_val. unfold UNIT in *. lia. }
      subst md'. rewrite RETc.
      assert (AGE : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 64 - 112 <= a < bv_unsigned sp - 64) -> ~ (PERRNO <= a < PERRNO + 4) -> m' (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
      { intros a Ha N1 N2. apply MU. cbn [outside]. rewrite (errno_addr_p0 tp TPv). rewrite (unsigned_lit a Ha), (unsigned_lit _ SP64). clear - N1 N2; try pose proof alloc_ceiling_val. tauto. }
      assert (AIE : p0_ainv (mkIAS s LB Rr) m' md).
      { apply (p0_ainv_agree_but_errno _ m1 m' md AI1). intros a Ha Ne. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). apply AGE; [try (generalize alloc_ceiling_val); clear - Ha; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ha CEIL ACV; try pose proof alloc_ceiling_val; lia| exact Ne]. }
      (* [comment removed for export] *)
      eapply rz_evt; [apply realloc_after_mremap| exact Hh| exact Hl|]. intros ms6 ->.
      eapply rz_evt; [apply realloc_remap_fail; rewrite Z_to_bv_unsigned; reflexivity| exact Hh| exact Hl|].
      (intros ms7; (first [ intro dR_17; dand8 dR_17 as u1 u2 u3 v2 v4 v5 v7 -> | intros (u1 & u2 & u3 & v2 & v4 & v5 & v7 & ->) ])). unfold MRep.wz. rewrite <- mkst_MS', A0.
      apply (realloc_fallback_cps _ _ gp tp _ _ _ _ _ a1 _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _
               ra s0 s1 s2 s3 s4 s5 s6 m' md (mkIAS s LB Rr) p n old T AIE MI' LV PNZ HN NR BYTES NLV TP); rewrite ?unsigned_lit by exact SP64.
      * clear - SPA SPR; try pose proof alloc_ceiling_val. Z.div_mod_to_equations. lia.
      * exact RAA.
      * try (generalize alloc_ceiling_val); clear - CEIL; try pose proof alloc_ceiling_val. lia.
      * try (generalize alloc_ceiling_val); clear - SPR; try pose proof alloc_ceiling_val. lia.
      * pose proof (stk_mapped_p0 (Clg:=Clg) m' _ _ ST' ltac:(try (generalize alloc_ceiling_val); clear - CEIL ACV; try pose proof alloc_ceiling_val; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia)) as X.
        rewrite ?(unsigned_lit _ SP64) in X. replace (bv_unsigned sp - 64 - (bv_unsigned sp - 64 - 8192)) with 8192 in X by (clear; lia). exact X.
      * eapply InstDefs.rw_cells_agree'; [exact FR1|]. intros x Hx. cbn [cells_size csize Nat.add] in Hx. rewrite <- (definitions.Z_to_bv_bv_unsigned 64 x).
        pose proof (bv_unsigned_in_range _ x) as XR. change (bv_modulus 64) with (2^64) in XR.
        apply AGE; [try (generalize alloc_ceiling_val); clear - XR; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Hx; try pose proof alloc_ceiling_val; lia| unfold PERRNO; try (generalize alloc_ceiling_val); clear - Hx CEIL ACV; try pose proof alloc_ceiling_val; lia].
      * intros t0'' t1'' t2'' a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x rr A' m'' md' AI' MI'' FRd' RES'.
        rewrite ESP. apply (K t0'' t1'' t2'' a1x a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x rr A' m'' md' AI' MI'' FRd').
        replace (bv_unsigned sp - 64 + 64) with (bv_unsigned sp) in RES' by (clear; lia).
        assert (AGw : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 8256 <= a < bv_unsigned sp) -> ~ (al_errno LayoutPU <= a < al_errno LayoutPU + 4) -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
        { intros a Ha NW NE. rewrite errno_p0 in NE. rewrite AGE; [| exact Ha| try (generalize alloc_ceiling_val); clear - NW; try pose proof alloc_ceiling_val; lia| exact NE]. apply AGo; [exact Ha| try (generalize alloc_ceiling_val); clear - NW; try pose proof alloc_ceiling_val; lia]. }
        assert (MONOw : forall a, 0 <= a < 2^64 -> heap_zone LayoutPU a -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None).
        { intros a Ha HZ Hm. apply (proj1 (heap_zone_p0 a)) in HZ. rewrite AGE; [exact (MONO1 a Ha Hm)| exact Ha| try (generalize alloc_ceiling_val); clear - HZ CEIL ACV; try pose proof alloc_ceiling_val; lia| unfold PERRNO; try (generalize alloc_ceiling_val); clear - HZ; try pose proof alloc_ceiling_val; lia]. }
        assert (HIGHw : forall a, 0 <= a < 2^64 -> ~ in_image LayoutPU a -> ~ heap_zone LayoutPU a -> m (Z_to_bv 64 a) <> None -> m'' (Z_to_bv 64 a) <> None).
        { intros a Ha NI NHZ Hm. pose proof (fun X => NHZ (proj2 (heap_zone_p0 a) X)) as NHZ'. unfold in_image in NI. cbn [al_image_lo al_image_hi LayoutPU] in NI.
          assert (HIa : alloc_ceiling <= a) by (try (generalize alloc_ceiling_val); clear - Ha NI NHZ'; try pose proof alloc_ceiling_val; lia).
          destruct RES' as (_ & _ & _ & _ & _ & _ & _ & FRM').
          all: (first [ dand4 FRM' as _ F2 F3 _ | destruct FRM' as (_ & F2 & F3 & _) ]).
          all: destruct (classic (bv_unsigned sp - 8256 <= a < bv_unsigned sp)) as [Wd|NWd];
            [pose proof (F3 (a - (bv_unsigned sp - 8256)) ltac:(try (generalize alloc_ceiling_val); clear - Wd; try pose proof alloc_ceiling_val; lia)) as X; unfold MRep.wz in X;
             replace (bv_unsigned sp - 8256 + (a - (bv_unsigned sp - 8256))) with a in X by (clear; lia); exact X|].
          all: destruct (F2 a Ha ltac:(unfold in_image; cbn [al_image_lo al_image_hi LayoutPU]; try (generalize alloc_ceiling_val); clear - HIa; try pose proof alloc_ceiling_val; lia)
                           ltac:(rewrite AGE; [exact (MONO1 a Ha Hm)| exact Ha| try (generalize alloc_ceiling_val); clear - NWd; try pose proof alloc_ceiling_val; lia| unfold PERRNO; try (generalize alloc_ceiling_val); clear - HIa; try pose proof alloc_ceiling_val; lia])) as [O|[V|X]];
            [exfalso; pose proof (p0_owned_below _ _ _ _ AIE O) as OB; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); try (generalize alloc_ceiling_val); clear - OB HIa; try pose proof alloc_ceiling_val; lia
            | exfalso; unfold nowhere, blk in V; try (generalize alloc_ceiling_val); clear - V HIa PC ACV OLD0; try pose proof alloc_ceiling_val; lia
            | exact X]. }
        destruct RES' as (Rnz & LVr & LD & LQ & PRE & DB' & DN' & FRM').
        split; [exact Rnz|]. split; [exact LVr|]. split; [right; exact LD|]. split; [exact LQ|]. split.
           ++ intros ii Hii. rewrite (PRE ii Hii). unfold MRep.wz. apply AGw; [try (generalize alloc_ceiling_val); clear - Hii PC P4096 ACV OLD0; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Hii PC P4096 ACV CEIL OLD0; try pose proof alloc_ceiling_val; lia| rewrite errno_p0; unfold PERRNO; try (generalize alloc_ceiling_val); clear - Hii PIMG P4096 OLD0; try pose proof alloc_ceiling_val; lia].
           ++ split; [rewrite DB'; unfold p0_livebytes; cbn [ia_LB]; reflexivity|]. split; [exact DN'|]. exact (frame_ok_pre_agree_e _ _ _ _ _ _ m m' m'' AGw MONOw HIGHw FRM').
    + (* [comment removed for export] *)
      destruct LEAF as [[GE _]|(dst & Ez' & FACTS)].
      { exfalso. unfold errno_of in Hn. destruct (Z.leb_spec0 (2^64 - 4095) (bv_unsigned rw)); [discriminate| try (generalize alloc_ceiling_val); clear - Ez GE n0; try pose proof alloc_ceiling_val; lia]. }
      assert (Edst : rw = dst) by (apply bv_eq; try (generalize alloc_ceiling_val); clear - Ez Ez'; try pose proof alloc_ceiling_val; lia). subst rw. clear Ez Ez'.
      cbv zeta in FACTS. (first [ dand10 FACTS as D0 DA DC' VM MI'' MH'' ML'' MMT'' CASE NBI | destruct FACTS as (D0 & DA & DC' & VM & MI'' & MH'' & ML'' & MMT'' & CASE & NBI) ]).
      rewrite RETc. set (NB := bv_unsigned dst) in *.
      assert (AG2 : forall a, 0 <= a < 2^64 -> ~ (bv_unsigned sp - 64 - 112 <= a < bv_unsigned sp - 64) -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
      { intros a Ha N1. apply MU. cbn [outside]. rewrite (unsigned_lit a Ha), (unsigned_lit _ SP64). clear - N1; try pose proof alloc_ceiling_val. tauto. }
      assert (MAPPED2 : forall o, 0 <= o < OL -> m2 (Z_to_bv 64 (B + o)) <> None).
      { intros o Ho. rewrite AG2; [| try (generalize alloc_ceiling_val); clear - Ho R0 RC; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ho R0 RC CEIL ACV; try pose proof alloc_ceiling_val; lia].
        pose proof (proj2 (proj2 WRB) o Ho) as W. rewrite p0_wview_overlay in W by (unfold wa; rewrite unsigned_lit by (try (generalize alloc_ceiling_val); clear - Ho R0 RC; try pose proof alloc_ceiling_val; lia); try (generalize alloc_ceiling_val); clear - Ho RI R0; try pose proof alloc_ceiling_val; lia). exact W. }
      assert (RCs : B + OL <= alloc_ceiling) by (idtac; exact RC).
      assert (ND4 : 4096 <= ND) by (try (generalize alloc_ceiling_val); clear - ND1 NR NT HOFF; try pose proof alloc_ceiling_val; unfold UNIT, MMAP_THRESHOLD in *; lia).
      assert (MOVE : dst <> Z_to_bv 64 B -> OL < ND) by (intros NEd; destruct CASE as [(Ed & _)|(_ & LT & _)]; [exact (False_ind _ (NEd Ed))| exact LT]).
      (first [ pose proof ((mremap_raw_facts m2 B OL ND dst R0 RCs OL4 OLA ND4 ND2 DC' ltac:(try (generalize alloc_ceiling_val); clear - NEQ'; try pose proof alloc_ceiling_val; lia) MOVE MAPPED2)) as dR_13; dand4 dR_13 as F1 F2 F3 F4 | destruct (mremap_raw_facts m2 B OL ND dst R0 RCs OL4 OLA ND4 ND2 DC' ltac:(try (generalize alloc_ceiling_val); clear - NEQ'; try pose proof alloc_ceiling_val; lia) MOVE MAPPED2) as (F1 & F2 & F3 & F4) ]). fold NB in F1, F2, F3, F4.
      idtac.
      (* [comment removed for export] *)
      eapply rz_evt; [apply realloc_after_mremap| exact MH''| exact ML''|]. intros ms6 ->.
      apply (FIN _ t0' t1' t2' a3'' a4' a5'' a6' a7' a0 a1 t3' t4' t5' t6' dst (mremap_raw B OL ND dst m2) md'); cbv zeta; fold NB; unfold MRep.wz.
      * right. refine (conj NEQ' (conj D0 (conj DA (conj _ (conj VM (conj MI'' (conj MH'' (conj ML'' (conj MMT'' _))))))))); [idtac; exact DC'|].
        destruct CASE as [(Ed & X)|(NEd & _ & RF)]; [left; exact (conj Ed X)| right; exact (conj NEd RF)].
      * intros o Ho. rewrite F1 by exact Ho. apply AG2; [try (generalize alloc_ceiling_val); clear - Ho R0 RC; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ho R0 RC CEIL ACV; try pose proof alloc_ceiling_val; lia].
      * exact F2.
      * intros a Ha N1 N2. idtac. rewrite F3; [| try (generalize alloc_ceiling_val); clear - Ha; try pose proof alloc_ceiling_val; lia| exact N1| exact N2]. apply AG2; [try (generalize alloc_ceiling_val); clear - Ha; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ha CEIL ACV; try pose proof alloc_ceiling_val; lia].
      * intros a Ha NW. idtac. rewrite F3; [| try (generalize alloc_ceiling_val); clear - Ha; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ha DC'; try pose proof alloc_ceiling_val; lia| try (generalize alloc_ceiling_val); clear - Ha RC; try pose proof alloc_ceiling_val; lia]. apply AG2; [try (generalize alloc_ceiling_val); clear - Ha; try pose proof alloc_ceiling_val; lia| exact NW].
      * intros a Ha. pose proof (stk_mapped_p0 (Clg:=Clg) _ _ _ ST' ltac:(try (generalize alloc_ceiling_val); clear - CEIL ACV; try pose proof alloc_ceiling_val; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia)) as Y. rewrite ?(unsigned_lit _ SP64) in Y.
        pose proof (Y (a - (bv_unsigned sp - 64 - 8192)) ltac:(try (generalize alloc_ceiling_val); clear - Ha; try pose proof alloc_ceiling_val; lia)) as X. unfold MRep.wz in X.
        replace (bv_unsigned sp - 64 - 8192 + (a - (bv_unsigned sp - 64 - 8192))) with a in X by (clear; lia). exact X.
      * intros x v Hx. destruct (F4 x v Hx) as [H2|RNG]; [exact (MI2 x v H2)|].
        unfold ro_addr. rewrite p0_find_segment_none; [reflexivity| clear; lia| try (generalize alloc_ceiling_val); clear - RNG NBI; try pose proof alloc_ceiling_val; lia].
      * exact NBI.
      * exact SE.
      * split; [exact MH''| exact ML''].
Qed.

End CEIL.

