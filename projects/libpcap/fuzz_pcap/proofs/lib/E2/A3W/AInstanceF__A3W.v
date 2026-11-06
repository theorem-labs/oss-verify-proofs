(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ACallocG__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_allC__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_kit__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module AInstanceF.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ACallocG__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_allC__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ASecStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeNull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.AFreeAll OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ART_HULLS : list (Z * Z) :=
  [(0xa4000, 0xa7000); (0xa71d8, 0xa71e0); (0xa7200, 0xa7208); (0xa7210, 0xa7218); (0xa7220, 0xa7228); (0xa7238, 0xa7248); (0xa7288, 0xa7290);
   (0xa7308, 0xa7310); (0xa7358, 0xa7368); (0xa7398, 0xa73a0); (0xaaf98, 0xab378); (0xabdb8, 0xabdc5); (0xabdf8, 0xabe0c); (0xabe24, 0xabe30);
   (0xabe4d, 0xabe4e); (0xabe58, 0xabe59); (0xade5c, 0xade5d); (0xade60, 0xade61); (0xade64, 0xade68); (0xae5f8, 0xae604); (0xaf2d8, 0xaf2da);
   (0xaf2e0, 0xaf2f8); (0xaf2fc, 0xaf300); (0xaf800, 0x130830); (0x130860, 0x130863); (0x13e088, 0x13e08c); (0x13e098, 0x13e09c);
   (0x13e0a0, 0x13e0a8); (0x1400c0, 0x1400d0); (0x140148, 0x140150); (0x140178, 0x140180); (0x1401a0, 0x1401a8); (0x1401b1, 0x1401b2);
   (0x1401b8, 0x1401c0); (0x140200, 0x140208); (0x140218, 0x140228); (0x14022c, 0x14022d); (0x1804c8, 0x5d0510); (0x5e14f0, 0x5e16f0); (0x601878, 0x601880);
   (0x602960, 0x602968)].
Definition ci_iv_okb (iv : Z * Z) : bool :=
  (0x10000 <=? fst iv) && (snd iv <=? 0x603000) && forallb (fun h => (snd iv <=? fst h) || (snd h <=? fst iv)) ART_HULLS.
(* [comment removed for export] *)
Definition ci_okb (CI : list (Z * Z)) : bool := forallb ci_iv_okb CI.
Definition hull_inb (A k : Z) : bool := existsb (fun h => (fst h <=? A) && (A + k <=? snd h)) ART_HULLS.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Gen.
Variable CI : list (Z * Z).
Hypothesis CI_B : ci_okb CI = true.

Definition aci_clear (A k : Z) : Prop := Forall (fun iv => A + k <= fst iv \/ snd iv <= A) CI.

#[using="CI_B"] Lemma ci_iv : forall iv, In iv CI -> 0x10000 <= fst iv /\ snd iv <= 0x603000 /\ forall h, In h ART_HULLS -> snd iv <= fst h \/ snd h <= fst iv.
Proof.
  intros iv Hin. pose proof (proj1 (forallb_forall _ _) CI_B iv Hin) as B. unfold ci_iv_okb in B.
  apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
  split; [exact B1|]. split; [exact B2|]. intros h Hh. pose proof (proj1 (forallb_forall _ _) B3 h Hh) as Bh. cbv beta in Bh.
  apply orb_prop in Bh as [Bh|Bh]; apply Z.leb_le in Bh; [left| right]; exact Bh.
Qed.

(* [comment removed for export] *)
#[using="CI_B"] Lemma aci_clear_hull : forall A k, hull_inb A k = true -> aci_clear A k.
Proof.
  intros A k HB. unfold hull_inb in HB. apply existsb_exists in HB as (h & Hh & B). apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
  unfold aci_clear. apply Forall_forall. intros iv Hin. (nd_pre (ci_iv iv Hin) 3%nat; intros _ _ C; nd_post). destruct (C h Hh) as [D|D]; lia.
Qed.

Ltac hull_in := cbn [In]; repeat first [left; reflexivity | right].
#[using="CI_B"] Lemma aci_okQ : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                           /\ (snd iv <= 0xab270 \/ 0xab330 <= fst iv)
                           /\ (snd iv <= 0xaf800 \/ 0x130830 <= fst iv)
                           /\ (snd iv <= 0x13e088 \/ 0x13e08c <= fst iv)) CI.
Proof.
  apply Forall_forall. intros iv Hin. (nd_pre (ci_iv iv Hin) 3%nat; intros C1 C2 C; nd_post).
  pose proof (C (0x1804c8, 0x5d0510) ltac:(unfold ART_HULLS; hull_in)) as H1. pose proof (C (0xaaf98, 0xab378) ltac:(unfold ART_HULLS; hull_in)) as H2.
  pose proof (C (0xaf800, 0x130830) ltac:(unfold ART_HULLS; hull_in)) as H3. pose proof (C (0x13e088, 0x13e08c) ltac:(unfold ART_HULLS; hull_in)) as H4.
  cbn [fst snd] in *. unfold AIMG_HI. lia.
Qed.
#[using="CI_B"] Lemma aci_ok : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Proof. eapply Forall_impl; [| exact aci_okQ]. cbv beta. intros iv (H1 & H2 & H3 & _). auto. Qed.
#[using="CI_B"] Lemma aci_ok2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Proof.
  apply Forall_forall. intros iv Hin. (nd_pre (ci_iv iv Hin) 3%nat; intros C1 C2 C; nd_post).
  pose proof (C (0xaaf98, 0xab378) ltac:(unfold ART_HULLS; hull_in)) as H2. cbn [fst snd] in *. unfold AINSTANCE. lia.
Qed.
#[using="CI_B"] Lemma aci_img : forall iv, In iv CI -> snd iv <= AIMG_HI.
Proof. intros iv Hin. (pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as ndP__; nd_pre ndP__ 3%nat; intros _ _ H; nd_post). exact H. Qed.
#[using="CI_B"] Lemma aci_ok1 : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Proof. intros iv Hin. (pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as ndP__; nd_pre ndP__ 3%nat; intros H1 _ H; nd_post). split; [clear -H1; lia| exact H]. Qed.
#[using="CI_B"] Lemma aci_lo : forall iv, In iv CI -> 0 <= fst iv.
Proof. intros iv Hin. pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as (H1 & _). lia. Qed.

Ltac aci_clear_tac := apply aci_clear_hull; try rewrite ATPv_img; vm_compute; reflexivity.

Lemma achunk_eq_dec' : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* [comment removed for export] *)
#[using="Type"] Lemma junk_any : forall m m' A n, junk_at m A n -> wmono asegs m m' -> 0x603000 <= A -> junk_at m' A n.
Proof. intros m m' A n H WM HA. exact (dc_at_any m m' A n H WM HA). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aobj_sub_sclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> sclr A k.
Proof. intros a n A k (_ & _ & _ & HS & _) H1 H2. unfold sclr in *. lia. Qed.
#[using="Type"] Lemma aobj_sub_iclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> iclr A k.
Proof. intros a n A k (_ & HG & _ & _ & HI) H1 H2. unfold iclr in *. lia. Qed.

Section ClientW.
Variables (L : alayout) (st : astate) (X : aconc) (LB : list ablock) (m m' : amem) (W Wx : list (Z * Z)).
Hypothesis ALO : alayout_ok L.
Hypothesis AR : AREP AHI L st X m.
Hypothesis BL : ablocks L st X LB.
Hypothesis HFK : AFAKE L LB m.
Hypothesis MU0 : munch (W ++ Wx) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis CW : Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                                 \/ aahm_client (fst iv) (snd iv - fst iv)) W.
(* Wx: writes to the 4-byte TLS cell at ATPv + 16; when there are any, the cell holds zero again in m'. *)
Hypothesis WX : Forall (fun iv => fst iv = ATPv + 16 /\ snd iv = ATPv + 20) Wx.
Hypothesis LS : Wx = [] \/ rw_cells asegs m' (ATPv + 16) [C4 (Z_to_bv 64 0)].
Let W' := List.filter nonempty (W ++ Wx).
Let MU : munch W' m m' := munch_filter_nonempty (W ++ Wx) m m' MU0.

(* [comment removed for export] *)
#[using="X m ALO AR BL"] Lemma hb_where : forall p B n, In (HB p B n) LB ->
  (exists c, 1 <= c < K_NUM_CLASSES /\ aregion L c <= B /\ B + n <= aregion L c + c_allocated_user (get_cls st c)
             /\ c_allocated_user (get_cls st c) <= K_FREEARR_OFF /\ 1 <= n)
  \/ (exists mb ms, B = mb + 6144 /\ 1 <= n /\ n + 6144 <= ms /\ sec_wf1 L (CSec mb ms n)).
Proof.
  intros p B n Hin.
  destruct (hb_cases L st X LB m p B n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - left. exists (xb_class b). destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). (nd_pre (PERC _ CLB) 3%nat; intros A1 A2 _; nd_post).
    pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user in *.
    split; [exact CLB|]. split; [clear -P5 RZ; lia|]. split; [clear -P4 FIT RG; lia|]. split; [unfold K_FREEARR_OFF in *; clear -A1 A2; lia| clear -NB; lia].
  - right. exists mb, ms. pose proof G as G0. cbn [sec_wf1] in G0. (nd_pre G0 7%nat; intros _ _ _ G4 G5 G6 _; nd_post).
    (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR _ NSE _ MSR _; nd_post). rewrite <- G4 in MSR.
    split; [exact EA|]. split; [clear -G5; lia|]. split; [clear -RSR NSE MSR; lia| exact G].
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI_B L st X LB m ALO AR BL HFK CW WX"] Lemma P_img : forall A k, 0 <= k -> 0x10000 <= A /\ A + k <= 0x603000 -> aci_clear A k ->
  (A + k <= ATPv + -200 \/ ATPv + 312 <= A) -> disjoint_from W' A k.      (* [comment removed for export] *)
Proof.
  intros A k Hk HA CLR HT. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi; clear -HT Hk; lia].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.   (* [comment removed for export] *)
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ _ SB; nd_post). unfold aobj in *.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; clear -KT HT NEV Hk; lia      (* [comment removed for export] *)
                              | unfold aahm_client, AAHM_SZ in KH; rewrite <- (ao_ahm_eq L ALO) in KH; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; clear -KH OAHI NEV HA Hk; lia].      (* [comment removed for export] *)
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 SB NEV HA. lia.
  - pose proof (proj1 (Forall_forall _ _) CLR iv Hiv) as D. cbn beta in D. clear -D I1 I2 NEV. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 6%nat; intros _ _ _ _ K5 _; nd_post). clear -K5 F1 F2 OFK OFKI HA NEV. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (alayout_space L ALO) as (SP1 & _). unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Q1 B1 B2 NEV HA SP1 Hc. nia.
      * cbn [sec_wf1] in Q3. (nd_pre Q3 3%nat; intros _ G2 _; nd_post). apply ablk_lin in G2. unfold AIMG_HI in G2. clear -G2 B1 B2 NEV HA. lia.   (* [comment removed for export] *)
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 6%nat; intros _ _ _ _ K5 _; nd_post). clear -K5 B1 B2 OFK OFKI HA NEV. lia.
  - clear -K5 NEV HA. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 _]. unfold ASHOFF in *. clear -I0 I1 I2 NEV HA. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 6%nat; intros _ _ _ _ K5 _; nd_post). unfold ASHOFF in *. clear -K5 F1 F2 OFK OFKI HA NEV. lia.
Qed.

(* [comment removed for export] *)
#[using="CI CI_B m ALO HFK CW WX"] Lemma P_obj : forall A k, tclr A k -> (A + k <= AAHMv \/ AAHMv + AAHM_SZ <= A) -> sclr A k -> iclr A k -> 0 <= k -> A + k <= ATOP ->      (* [comment removed for export] *)
  (A + k <= al_fake L \/ al_fake L + 11571200 <= A) ->
  (forall p B n, In (HB p B n) LB -> A + k <= B \/ B + n <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k HT HAH HS HI Hk HC HF HB. unfold sclr, KLS in HS. unfold iclr, AIMG_LO, AIMG_HI in HI. destruct HI as [HA HI].
  subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi; unfold tclr in HT; clear -HT Hk; lia].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ S47 SB; nd_post). unfold aobj in *.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; unfold tclr in HT; clear -KT HT NEV Hk; lia      (* [comment removed for export] *)
                              | unfold aahm_client in KH; clear -KH HAH NEV Hk; lia].      (* [comment removed for export] *)
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 NEV HC. lia.
  - (pose proof (proj1 (Forall_forall _ _) aci_ok iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros I0 _ I3; nd_post). unfold AIMG_HI in I3. clear -I0 I1 I2 I3 NEV HI. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 F1 F2 HF NEV Hk. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + pose proof (HB q B n' Hb) as D. clear -D B1 B2 NEV Hk. lia.
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 B1 B2 HF NEV Hk. lia.
  - clear -K5 NEV HS Hk. lia.
  - (pose proof (proj1 (Forall_forall _ _) aci_ok iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros I0 _ I3; nd_post). unfold AIMG_HI, ASHOFF in *. clear -I0 I1 I2 I3 NEV HS Hk. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). (pose proof OFK as ndP__; nd_pre ndP__ 5%nat; intros _ _ OFK3 OFKS _; nd_post). unfold sclr, KLS in OFKS.
    unfold FAKESZ, ASHOFF in *. clear -K5 K6 F1 F2 OFK3 OFKS OFKI NEV HS Hk. lia.
Qed.

(* [comment removed for export] *)
#[using="tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_sh : forall A k, 2148238848 <= A -> 0 <= k -> A + k <= shad ATOP ->
  (A + k <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k HA Hk HC HF.
  assert (HC2 : A + k <= 17594332446720 /\ 8 * (A + k) <= ATOP + 8 * ASHOFF).
  { rewrite shad_div in HC. pose proof ATOP_al16 as A16. unfold ASHOFF in *. clear -HC A16. Z.div_mod_to_equations. lia. }
  clear HC. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi; pose proof atp_lin as TLN; clear -TLN HA Hk; lia].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
  (pose proof OFK as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ OFKS _; nd_post). unfold sclr, KLS in OFKS.
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ S47 SB; nd_post). unfold aobj in *.
  assert (SF : shad (al_fake L) = al_fake L / 8 + ASHOFF /\ shad (al_fake L + 11571200) = al_fake L / 8 + 1446400 + ASHOFF).
  { rewrite !shad_div. clear -OFK. Z.div_mod_to_equations. lia. }
  destruct SF as [SF1 SF2]. unfold ASHOFF in *.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; pose proof atp_lin as TLN; clear -KT TLN NEV HA Hk HC2; lia      (* [comment removed for export] *)
                              | unfold aahm_client, AAHM_SZ in KH; rewrite <- (ao_ahm_eq L ALO) in KH; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; clear -KH OAH OAHI NEV HA Hk HC2; lia].      (* [comment removed for export] *)
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 NEV HC2. lia.
  - destruct (aci_ok1 iv Hiv) as [_ I3]. unfold AIMG_HI in I3. clear -I1 I2 I3 NEV HA. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 F1 F2 OFK OFKS NEV HC2 HA. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (alayout_space L ALO) as (SP1 & _). unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Q1 B1 B2 NEV HC2 SP1 Hc. nia.
      * cbn [sec_wf1] in Q3. (nd_pre Q3 3%nat; intros _ G2 _; nd_post). unfold ablk, KLS, AIMG_HI in G2. clear -G2 Q2 B1 B2 NEV HC2 HA. lia.   (* [comment removed for export] *)
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 B1 B2 OFK OFKS HC2 HA NEV. lia.
  - clear -K5 NEV HC2. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 I3]. unfold AIMG_HI in *. clear -I0 I1 I2 I3 NEV HA. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 F1 F2 SF1 SF2 HF NEV Hk. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI X m AR"] Lemma hb_prim_span : forall p B n c,
  In (HB p B n) LB -> 1 <= c < K_NUM_CLASSES -> aregion L c <= B -> B + n <= aregion L c + c_allocated_user (get_cls st c) ->
  al_space_beg L + K_REGION <= B /\ B + n <= al_space_beg L + K_SPACE_SIZE /\ B + n <= aregion L c + K_FREEARR_OFF.
Proof.
  intros p B n c Hin Hc Q1 Q2. destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). (nd_pre (PERC c Hc) 3%nat; intros A1 A2 _; nd_post).
  unfold aregion, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. change (2^37) with 137438953472. clear -Hc Q1 Q2 A1 A2. nia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI st X m ALO AR BL"] Lemma hb_clear_obj : forall A k,
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_space_beg L + K_SPACE_SIZE <= A /\ A + k <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA)
   \/ (al_res L <= A /\ A + k <= al_space_beg L + K_REGION)) ->
  forall p B n, In (HB p B n) LB -> A + k <= B \/ B + n <= A.
Proof.
  intros A k HR p B n Hin.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res.
  pose proof (ad_store_res L ALO) as D_s_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  unfold adisj, aobj in *.
  destruct (hb_where p B n Hin) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - (pose proof (hb_prim_span p B n c Hin Hc Q1 Q2) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post).
    unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    clear -HR S1 S2 D_t_res D_c_res D_n_res D_s_res D_p_res RSP ORS. lia.
  - cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (Ct & Cc & Cr & Cp & Cn & Cs & _); nd_post).
    unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    clear -HR Ct Cc Cr Cp Cn Cs RSP ORS Q2. lia.
Qed.

#[using="rc tlsI ALO"] Lemma hb_clear_fake_obj : forall A k,
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_res L <= A /\ A + k <= al_res L + 137439023104)) ->
  A + k <= al_fake L \/ al_fake L + 11571200 <= A.
Proof.
  intros A k HR.
  pose proof (ad_t_fake L ALO) as D1. pose proof (ad_ctx_fake L ALO) as D2. pose proof (ad_nodes_fake L ALO) as D3.
  pose proof (ad_store_fake L ALO) as D4. pose proof (ad_fake_ptr L ALO) as D5. pose proof (ad_fake_res L ALO) as D6. unfold adisj in *.
  clear -HR D1 D2 D3 D4 D5 D6. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_rt : forall A k, 0 <= k ->
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_space_beg L + K_SPACE_SIZE <= A /\ A + k <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA)
   \/ (al_res L <= A /\ A + k <= al_space_beg L + K_REGION)) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk HR.
  pose proof (ao_space L ALO) as RSP.
  (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as T1. pose proof (ad_tls_ctx L ALO) as T2. pose proof (ad_tls_nodes L ALO) as T3. pose proof (ad_tls_store L ALO) as T4.
  pose proof (ad_tls_ptr L ALO) as T5. pose proof (ad_tls_res L ALO) as T6. unfold adisj in T1, T2, T3, T4, T5, T6.
  pose proof (ad_ahm_t L ALO) as H1a. pose proof (ad_ahm_ctx L ALO) as H2a. pose proof (ad_ahm_nodes L ALO) as H3a. pose proof (ad_ahm_store L ALO) as H4a.
  pose proof (ad_ahm_ptr L ALO) as H5a. pose proof (ad_ahm_res L ALO) as H6a. unfold adisj in H1a, H2a, H3a, H4a, H5a, H6a. pose proof (ao_ahm_eq L ALO) as EAH.
  assert (SUB : exists a n, aobj a n /\ ((a + n <= ATPv + -200 \/ ATPv + 312 <= a) /\ (a + n <= AAHMv \/ AAHMv + 3727360 <= a)) /\ a <= A /\ A + k <= a + n).
  { unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION in HR. change (2^37) with 137438953472 in HR.
    destruct HR as [H|[H|[H|[H|[H|[H|H]]]]]];
      [ exists (al_t L), 4096 | exists (al_ctx L), 65536 | exists (al_nodes L), 1048576 | exists (al_store L), 8388608
      | exists (al_ptr_array L), 8388608 | exists (al_res L), 137439023104 | exists (al_res L), 137439023104 ];
      (split; [first [exact (ao_t L ALO) | exact (ao_ctx L ALO) | exact (ao_nodes L ALO) | exact (ao_store L ALO) | exact (ao_ptr L ALO) | exact (ao_res L ALO)] |]);
      rewrite <- EAH; clear -H RSP T1 T2 T3 T4 T5 T6 H1a H2a H3a H4a H5a H6a; lia. }
  (nd_pre SUB 6%nat; intros a n OA [TC TAH] S1 S2; nd_post).
  apply P_obj; [unfold tclr; clear -TC S1 S2; lia | unfold AAHM_SZ; clear -TAH S1 S2; lia | exact (aobj_sub_sclr a n A k OA S1 S2) | exact (aobj_sub_iclr a n A k OA S1 S2) | exact Hk | | |].
  - (pose proof OA as ndP__; nd_pre ndP__ 4%nat; intros _ _ O3 _; nd_post). clear -O3 S2. lia.
  - apply hb_clear_fake_obj. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION in HR. change (2^37) with 137438953472 in HR. clear -HR RSP. lia.
  - exact (hb_clear_obj A k HR).
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI CI_B X LB m ALO AR BL HFK CW WX"] Lemma P_reg_hi : forall c A k, 1 <= c < K_NUM_CLASSES -> 0 <= k ->
  aregion L c + c_allocated_user (get_cls st c) <= A -> A + k <= aregion L c + K_REGION -> disjoint_from W' A k.
Proof.
  intros c A k Hc Hk H1 H2.
  pose proof (ao_res L ALO) as ORS. pose proof (ao_space L ALO) as RSP. unfold aobj in *.
  destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). (nd_pre (PERC c Hc) 3%nat; intros A1 A2 _; nd_post).
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104).
  { unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Hc RSP. nia. }
  destruct RI as [RI1 RI2]. unfold K_REGION in *. pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  pose proof (ad_tls_res L ALO) as TR. unfold adisj in TR.
  pose proof (ad_ahm_res L ALO) as AR0. unfold adisj in AR0. rewrite (ao_ahm_eq L ALO) in AR0.
  apply P_obj; [unfold tclr; clear -TR H1 H2 RI1 RI2 A1; lia| unfold AAHM_SZ; clear -AR0 H1 H2 RI1 RI2 A1; lia| unfold sclr; right; clear -H1 RI1 RHI A1; lia| unfold iclr, AIMG_HI; split; [clear -H1 RI1 RHI A1; lia| right; clear -H1 RI1 RHI A1; lia]
               | exact Hk| atop_facts; clear -H2 RI2 ORS; lia| apply hb_clear_fake_obj; clear -H1 H2 RI1 RI2 A1; lia|].
  intros p B n Hin. destruct (hb_where p B n Hin) as [(c' & Hc' & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - destruct (Z.eq_dec c' c) as [->|NE]; [clear -Q2 H1; lia|].
    destruct (Z.lt_ge_cases c' c) as [LT|GE].
    + right. pose proof (regions_sep L c' c LT) as RS. unfold K_REGION, K_FREEARR_OFF in *. clear -RS Q2 Q3 H1 A1. lia.
    + left. pose proof (regions_sep L c c' ltac:(clear -GE NE; lia)) as RS. unfold K_REGION in *. clear -RS Q1 H2. lia.
  - cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (_ & _ & Cr & _); nd_post). clear -Cr RI1 RI2 H1 H2 Q2 A1. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI m ALO AR BL"] Lemma slot_vs_blocks : forall c k p B n, 1 <= c < K_NUM_CLASSES -> 0 <= k < ndist st c -> In (HB p B n) LB ->
  (exists b, busy_of X c k = Some b /\ xb_st b = BLive p /\ B = xb_user L b /\ n = xb_n b)
  \/ (B + n <= aslot_addr L c k \/ aslot_addr L c k + size_of_class c <= B).
Proof.
  intros c k p B n Hc Hk Hin.
  pose proof AR as (WF & _). (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  pose proof (size_of_class_facts c Hc) as [QS _]. (nd_pre (PERC c Hc) 3%nat; intros A1 A2 _; nd_post).
  (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 A1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
  destruct (hb_cases L st X LB m p B n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & Q5 & Q4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    + destruct (Z.eq_dec (xb_slot b) k) as [EK|NK].
      * left. exists b. rewrite <- EC, <- EK. split; [exact (busy_of_of_In L st X b WF Hb)|]. split; [exact Sb|]. split; [symmetry; exact Ub| symmetry; exact Nb].
      * right. pose proof (slots_disjoint L c (xb_slot b) k ltac:(clear -KB; lia) ltac:(clear -Hk; lia) NK ltac:(clear -QS; lia)) as SD.
        pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user, xb_alloc in *. rewrite EC in *.
        clear -SD FIT RG RZ. lia.
    + right. pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user, xb_alloc in *.
      (nd_pre (PERC (xb_class b) CLB) 3%nat; intros B1' B2' _; nd_post). unfold K_FREEARR_OFF in *.
      destruct (Z.lt_ge_cases (xb_class b) c) as [LT|GE].
      * left. pose proof (regions_sep L (xb_class b) c LT) as RS. unfold K_REGION in RS. clear -RS Q4 P5 FIT RG RZ B1' B2'. lia.
      * right. pose proof (regions_sep L c (xb_class b) ltac:(clear -GE NC; lia)) as RS. unfold K_REGION in RS. clear -RS Q5 P4 A1 A2 RZ. lia.
  - right. cbn [sec_wf1] in G. (nd_pre G 7%nat; intros _ _ _ G4 G5 G6 (_ & _ & Cr & _); nd_post). subst B. unfold SEC_UOFF.
    (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR _ NSE _ MSR _; nd_post). rewrite <- G4 in MSR.
    pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_NUM_CLASSES, K_REGION in *; clear -Hc RSP; nia).
    unfold K_REGION, K_FREEARR_OFF in *. clear -Cr RI P5 P4 A1 A2 G5 RSR NSE MSR. lia.
Qed.

(* [comment removed for export] *)
#[using="rc"] Lemma disjoint_from_In : forall (Wl : list (Z * Z)) A k iv, disjoint_from Wl A k -> In iv Wl -> A + k <= fst iv \/ snd iv <= A.
Proof.
  intros Wl A k iv. induction Wl as [|[lo hi] Wl IH]; intros D Hin; [destruct Hin|].
  cbn in D. destruct D as [D1 D2]. destruct Hin as [<-|Hin]; [cbn; lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_sh_res : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof.
  intros A k H1 Hk H2. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ad_fake_res L ALO) as D. pose proof (ao_res_hi L ALO) as RHI. unfold aobj, adisj in *.
  assert (SR : 2148238848 <= shad (al_res L) /\ shad (al_res L + 137439023104) <= shad ATOP   (* [comment removed for export] *)
               /\ (shad (al_res L + 137439023104) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad (al_res L))).
  { rewrite !shad_div. unfold ASHOFF. clear -ORS OFK D RHI. Z.div_mod_to_equations. lia. }
  apply P_sh; clear -SR H1 Hk H2; lia.
Qed.

#[using="rc tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_dtls : forall A k, al_dtls L <= A -> 0 <= k -> A + k <= al_dtls L + 4096 -> disjoint_from W' A k.
Proof.
  intros A k H1 Hk H2.
  pose proof (ao_dtls L ALO) as OD. pose proof (ad_fake_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  unfold aobj, adisj in *.
  pose proof (ad_tls_dtls L ALO) as TD. unfold adisj in TD.
  pose proof (ad_ahm_dtls L ALO) as AD0. unfold adisj in AD0. rewrite (ao_ahm_eq L ALO) in AD0.
  apply P_obj; [unfold tclr; clear -TD H1 H2; lia| unfold AAHM_SZ; clear -AD0 H1 H2; lia| exact (aobj_sub_sclr _ _ A k (ao_dtls L ALO) H1 H2)| exact (aobj_sub_iclr _ _ A k (ao_dtls L ALO) H1 H2)| exact Hk| clear -H2 OD; lia| clear -H1 H2 D1; lia|].   (* [comment removed for export] *)
  intros p B n Hin. destruct (hb_where p B n Hin) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - (pose proof (hb_prim_span p B n c Hin Hc Q1 Q2) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post). unfold K_REGION, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    clear -H1 H2 S1 S2 D2 RSP ORS. lia.
  - cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & Cd); nd_post). clear -H1 H2 Cd Q2. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_fakehdr : disjoint_from W' (al_fake L) 36864.
Proof.
  subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi; pose proof (ad_tls_fake L ALO) as TF; unfold adisj in TF; clear -TF; lia].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.   (* [comment removed for export] *)
  (pose proof OFK as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ OFKS _; nd_post). unfold sclr, KLS in OFKS.
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ S47 SB; nd_post). unfold aobj in *.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; pose proof (ad_tls_fake L ALO) as TF; unfold adisj in TF; clear -KT TF NEV; lia      (* [comment removed for export] *)
                              | unfold aahm_client, AAHM_SZ in KH; rewrite <- (ao_ahm_eq L ALO) in KH; pose proof (ad_ahm_fake L ALO) as AF; unfold adisj in AF; clear -KH AF NEV; lia].      (* [comment removed for export] *)
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 SB NEV OFK. lia.
  - destruct (aci_ok1 iv Hiv) as [_ I3]. unfold AIMG_HI in I3. clear -I1 I2 I3 NEV OFK OFKI. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 6%nat; intros _ _ _ _ K5 _; nd_post). clear -K5 F1 F2 NEV. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + pose proof (hb_clear_fake_obj) as _. destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * (pose proof (hb_prim_span q B n' c Hb Hc Q1 Q2) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 _; nd_post). pose proof (ad_fake_res L ALO) as D. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
        unfold adisj, aobj, K_REGION, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *. clear -S1 S2 D RSP ORS B1 B2 NEV. lia.
      * cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & Cf & _); nd_post). clear -Cf B1 B2 NEV Q2. lia.
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 6%nat; intros _ _ _ _ K5 _; nd_post). clear -K5 B1 B2 NEV. lia.
  - clear -K5 NEV OFK OFKS. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 I3]. unfold AIMG_HI in *. clear -I0 I1 I2 I3 NEV OFK OFKS OFKI. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in *.
    clear -K5 K6 F1 F2 OFK OFKS NEV. lia.
Qed.

(* [comment removed for export] *)
#[using="CI CI_B L st X LB m ALO AR BL HFK CW WX"] Lemma P_tls : forall A k, 0 <= k ->
  ((ATPv + -88 <= A /\ A + k <= ATPv + -80) \/ (ATPv + -8 <= A /\ A + k <= ATPv + 20) \/ (ATPv + 288 <= A /\ A + k <= ATPv + 312)) ->
  ((A + k <= ATPv + 16 \/ ATPv + 20 <= A) \/ Wx = []) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk HA NL. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi;
                                          destruct NL as [NL|NL]; [clear -NL Hk; lia | rewrite NL in Hin; destruct Hin]].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof atp_lin as TLN. pose proof atp_below_atop as TBA. pose proof atop_range as ATR0.
  pose proof (ad_tls_fake L ALO) as TF. pose proof (ad_tls_res L ALO) as TR. unfold adisj in TF, TR.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; clear -KT HA NEV Hk; lia
                              | unfold aahm_client, AAHM_SZ in KH; rewrite <- (ao_ahm_eq L ALO) in KH; pose proof (ad_tls_ahm L ALO) as TA; unfold adisj in TA; clear -KH TA HA NEV Hk; lia].
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 HA TBA NEV. lia.
  - destruct (ci_iv iv Hiv) as (_ & _ & CH). pose proof (CH (0x5e14f0, 0x5e16f0) ltac:(unfold ART_HULLS; cbn [In]; repeat first [left; reflexivity | right])) as HT.
    cbn [fst snd] in HT. pose proof ATPv_img as TPI. clear -HT I1 I2 NEV HA TPI. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 F1 F2 TF HA NEV. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (ao_space L ALO) as RSP. pose proof (alayout_space L ALO) as (SP1 & _). unfold aregion, K_NUM_CLASSES, K_REGION, K_FREEARR_OFF in *.
        clear -Q1 Q2 Q3 B1 B2 NEV HA TR RSP Hc. nia.
      * cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & _ & Ctls & _); nd_post). clear -Ctls Q2 B1 B2 NEV HA. lia.
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 B1 B2 TF HA NEV. lia.
  - clear -K5 NEV HA TBA ATR0 TLN. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 I3]. pose proof (proj1 (Forall_forall _ _) aci_ok iv Hiv) as (I0' & _). unfold AIMG_HI in *. clear -I0' I1 I2 I3 NEV HA TLN. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). pose proof (ao_fake L ALO) as OFK. (pose proof OFK as ndP__; nd_pre ndP__ 5%nat; intros _ _ OFK3 OFKS _; nd_post).
    pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
    unfold sclr, KLS, FAKESZ in *. clear -K5 K6 F1 F2 OFK3 OFKS OFKI NEV HA TLN ATR0. lia.
Qed.


(* [comment removed for export] *)
#[using="rc tlsI CI CI_B LB W Wx ALO AR BL HFK MU0 WM CW WX W' MU"] Lemma aslot_client : forall c k, 1 <= c < K_NUM_CLASSES -> 0 <= k < ndist st c ->
  match busy_of X c k with None => junk_at m (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m b end ->
  match busy_of X c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end.
Proof.
  intros c k Hc Hk SL.
  pose proof AR as (WF & _). pose proof (size_of_class_facts c Hc) as [QS _].
  (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC c Hc) 3%nat; intros A1 A2 _; nd_post).
  (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 A1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_NUM_CLASSES, K_REGION in *; clear -Hc RSP; nia).
  destruct RI as [RI1 RI2]. unfold K_REGION, K_FREEARR_OFF in *. pose proof (ao_res_hi L ALO) as RHI.
  (* [comment removed for export] *)
  assert (PSUB : forall A kk, aslot_addr L c k <= A -> 0 <= kk -> A + kk <= aslot_addr L c k + size_of_class c ->
      (forall b, busy_of X c k = Some b -> match xb_st b with BLive _ => A + kk <= xb_user L b \/ xb_user L b + xb_n b <= A | _ => True end) ->
      disjoint_from W' A kk).
  { intros A kk HA Hkk HB OWN.
    apply P_obj; [unfold tclr; pose proof (ad_tls_res L ALO) as TR; unfold adisj in TR; clear -TR HA HB P5 P4 A1 A2 RI1 RI2; lia
                 | pose proof (ad_ahm_res L ALO) as AR0; unfold adisj in AR0; rewrite (ao_ahm_eq L ALO) in AR0; unfold AAHM_SZ; clear -AR0 HA HB P5 P4 A1 A2 RI1 RI2; lia| unfold sclr; right; clear -HA P5 RI1 RHI; lia| unfold iclr, AIMG_HI; split; [clear -HA P5 RI1 RHI; lia| right; clear -HA P5 RI1 RHI; lia]
                 | exact Hkk| atop_facts; clear -HB P4 A1 A2 RI2 ORS; lia
                 | apply hb_clear_fake_obj; clear -HA HB P5 P4 A1 A2 RI1 RI2; lia|].   (* [comment removed for export] *)
    intros p B n Hin. destruct (slot_vs_blocks c k p B n Hc Hk Hin) as [(b & EB & Sb & -> & ->)|D]; [| clear -D HA HB; lia].
    specialize (OWN b EB). rewrite Sb in OWN. exact OWN. }
  destruct (busy_of X c k) as [b|] eqn:EB.
  - (nd_pre (busy_of_Some_facts X c k b EB) 3%nat; intros Hb Cb Kb; nd_post). pose proof (awf_fits L st X b WF Hb) as FIT.
    destruct (xb_st b) as [q| |] eqn:Sb.
    + (* [comment removed for export] *)
      unfold aslot_busy in SL |- *. cbv zeta in SL |- *. rewrite Sb in SL |- *. unfold xb_fits in FIT. rewrite Sb in FIT. (nd_pre FIT 3%nat; intros N0 RZ FIT; nd_post).
      unfold xb_user, xb_alloc in *. rewrite Cb, Kb in *. (nd_pre SL 3%nat; intros LH [stb [E HDR]] UJ; nd_post).
      assert (D : disjoint_from W' (aslot_addr L c k) (rz_size (xb_n b))).
      { apply PSUB; [clear; lia| clear -RZ; lia| clear -FIT RZ N0; pose proof (rounded_size_ge (xb_n b)); lia|].
        intros b' EB'. injection EB' as <-. rewrite Sb. unfold xb_user, xb_alloc. rewrite Cb, Kb. left. clear; lia. }
      split; [| split].
      * intros H16. destruct (LH H16) as [LC J]. split.
        -- eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | clear; lia | clear -H16; lia | clear; lia].
        -- eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | clear; lia | clear -Hp; lia | clear -Hp; lia].
      * exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
        eapply disjoint_from_sub; [exact D | clear -RZ; lia | clear; lia | clear; lia].
      * eapply junk_any; [exact UJ| exact WM| clear -P5 RI1 RHI RZ; lia].   (* [comment removed for export] *)
    + eapply (aslot_busy_frame L W' m m' MU WM); [exact SL| exact FIT|]. unfold xb_alloc. rewrite Cb, Kb.
      apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. injection EB' as <-. rewrite Sb. exact I.
    + eapply (aslot_busy_frame L W' m m' MU WM); [exact SL| exact FIT|]. unfold xb_alloc. rewrite Cb, Kb.
      apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. injection EB' as <-. rewrite Sb. exact I.
  - eapply junk_frame; [exact SL | exact MU | exact WM |]. intros _. apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. discriminate EB'.
Qed.

(* [comment removed for export] *)
#[using="CI CI_B X LB W Wx ALO AR BL HFK MU0 WM CW WX W' MU"] Lemma asec_chunk_client : forall mb ms n idx lv,
  In (CSec mb ms n) (sec_chunks_of st) -> sec_wf1 L (CSec mb ms n) ->
  (lv = true <-> sec_live st (CSec mb ms n)) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros mb ms n idx lv INC WF1 LVE CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. (nd_pre WF0 7%nat; intros G1 G2 G3 G4 G5 G6 GC; nd_post). (pose proof GC as ndP__; nd_pre ndP__ 10%nat; intros Ct Cc Cr Cp Cn Cs Cf Cd Ctls Cahm; nd_post).
  (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros NB _ RSE RSR _ NSE _ MSR MSM MSB; nd_post). rewrite <- G4 in MSR, MSM, MSB.
  (pose proof AR as ndP__; nd_pre ndP__ 8%nat; intros WF _ _ _ _ _ HS _; nd_post). cbn [AHI ah_sec] in HS. unfold ASEC_of in HS. pose proof HS as ((_ & _ & _ & _ & _ & WFA & [ND PW]) & _).
  pose proof (ao_fake L ALO) as OFK. unfold aobj in OFK. unfold K_HIGH_MEM in *.
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros G2a G2b _ _; nd_post).   (* [comment removed for export] *)
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8 /\ 2148238848 <= shad mb /\ shad mb + ms / 8 <= shad ATOP
               /\ (shad mb + ms / 8 <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad mb)).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. unfold ASHOFF, AIMG_HI in *. clear -G1 G2a G2b G3 G5 RSR NSE MSR MSM Cf OFK. Z.div_mod_to_equations. lia. }
  (nd_pre GR 6%nat; intros GR1 GR2 GR3 GR4 GR5 GR6; nd_post).
  (* [comment removed for export] *)
  assert (DLO : forall A k, mb <= A -> 0 <= k -> A + k <= mb + 6144 -> disjoint_from W' A k).
  { intros A k H1 Hk H2.
    apply P_obj; [unfold tclr; clear -Ctls H1 H2 MSR NSE RSR G5; lia| rewrite (ao_ahm_eq L ALO) in Cahm; unfold AAHM_SZ; clear -Cahm H1 H2 MSR NSE RSR G5; lia| clear -H1 H2 G2 MSR NSE RSR G5; unfold ablk, sclr, KLS, AIMG_HI in *; lia| clear -H1 H2 G2 MSR NSE RSR G5; unfold ablk, iclr, AIMG_LO, AIMG_HI, KLS in *; lia
                 | exact Hk| atop_facts; clear -H2 G3 MSR NSE RSR G5; lia| clear -H1 H2 Cf MSR NSE RSR G5; lia|].
    intros p B n' Hin. destruct (hb_cases L st X LB m p B n' ALO AR BL Hin) as [(b & _ & _ & Ub & Nb & _ & NB' & FIT & _ & _ & _ & _ & _ & R1 & R2)|(mb' & ms' & Lp & -> & G' & _ & INC')].
    - pose proof (rz_size_ge16 (xb_n b)) as RZ. pose proof (rounded_size_ge n') as RG. unfold xb_user in *. subst B n'. clear -R1 R2 Cr H1 H2 MSR NSE RSR RZ G5 FIT RG NB'. lia.
    - unfold SEC_UOFF. destruct (achunk_eq_dec' (CSec mb' ms' n') (CSec mb ms n)) as [E|NE].
      + injection E as -> -> ->. left. clear -H2; lia.
      + pose proof (PW _ _ INC' INC NE) as D. cbn [sec_mb sec_ms] in D.
        cbn [sec_wf1] in G'. (nd_pre G' 7%nat; intros _ _ _ G4' G5' G6' _; nd_post). (pose proof (sec_facts n' ltac:(clear -G5'; lia) G6') as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR' _ NSE' _ MSR' _; nd_post). rewrite <- G4' in MSR'.
        clear -D H1 H2 MSR' NSE' RSR' G5' MSR NSE RSR G5. lia. }
  assert (DSH : forall A k, shad mb <= A -> 0 <= k -> A + k <= shad mb + ms / 8 -> disjoint_from W' A k).
  { intros A k H1 Hk H2. apply P_sh; clear -H1 Hk H2 GR4 GR5 GR6; lia. }
  cbn [asec_chunk] in CH |- *. (nd_pre CH 9%nat; intros H1 H2 H3 H4 (b1 & ctx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DLO; clear; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DLO; clear; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DLO; clear; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DLO; clear; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DLO; clear; lia]. }
  split; [eapply junk_any; [exact H6| exact WM| clear -G2a; unfold AIMG_HI in *; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DSH; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DSH; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DSH; clear -GR3 GR1 POS; lia].
Qed.

(* [comment removed for export] *)
#[using="CI CI_B st X m W Wx ALO AR BL HFK MU0 WM CW WX W' MU"] Lemma afake_client : AFAKE L LB m'.
Proof.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE (h0 & h1 & h2 & hs & HS) LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11; nd_post). unfold FAKESZ in *.
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros G2a G2b G2c G2d; nd_post). unfold AIMG_HI in G2a.   (* [comment removed for export] *)
  pose proof P_fakehdr as DF.
  split; [exact G|].
  split.
  { (nd_pre CE 8%nat; intros C1 C2 C3 C4 C5 C6 C7 C8; nd_post). unfold afake_cells.
    split; [eapply cells_frame; [exact C1| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac| pose proof ATPv_img as TI; clear -TI; lia]]|].
    split; [eapply cells_frame; [exact C2| exact MU| exact WM| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply P_tls; [clear; lia| clear; lia| left; clear; lia]]|].      (* [comment removed for export] *)
    split; [eapply cells_frame; [exact C3| exact MU| exact WM| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply P_tls; [clear; lia| clear; lia| left; clear; lia]]|].      (* [comment removed for export] *)
    split; [eapply cells_frame; [exact C4| exact MU| exact WM| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply P_tls; [clear; lia| clear; lia| left; clear; lia]]|].      (* [comment removed for export] *)
    split; [eapply cells_frame; [exact C5| exact MU| exact WM| cbn; apply P_dtls; clear; lia]|].
    split; [eapply cells_frame; [exact C6| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac| pose proof ATPv_img as TI; clear -TI; lia]]|].
    split; [eapply cells_frame; [exact C7| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac| pose proof ATPv_img as TI; clear -TI; lia]]|].
    eapply dc_at_any2; [exact C8| exact WM| (nd_pre G7 3%nat; intros _ G7i _; nd_post); unfold iclr, AIMG_LO, AIMG_HI in G7i; clear -G7i; lia]. }   (* [comment removed for export] *)
  split. { exists h0, h1, h2, hs. eapply cells_frame; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]. }
  split; [eapply cells_frame; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]|].
  split; [eapply cells_frame; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| clear -G2a; lia]|].
  split. { eapply dc_at_any; [exact DC2| exact WM|]. rewrite shad_div. unfold ASHOFF. clear -G2a G2b. Z.div_mod_to_equations; lia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    rewrite (munch_outside_range W' m m' (al_fake L) 36864) in Hb; [eapply FL; eauto| exact MU| exact DF| clear -FR; lia| clear -FR G2a G2c G3; lia].
  - intros c F n Hin. (nd_pre (LV c F n Hin) 6%nat; intros Hc Hn pos Hp HF Hb; nd_post). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    rewrite (munch_outside_range W' m m' (al_fake L) 36864); [exact Hb| exact MU| exact DF| clear -FR; lia| clear -FR G2a G2c G3; lia].
Qed.

(* [comment removed for export] *)
#[using="CI CI_B LB m W Wx ALO AR BL HFK MU0 WM CW WX LS W' MU"] Theorem AREP_client : AREP AHI L st X m'.
Proof.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post). pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_ptr L ALO) as OP.
  pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  unfold aobj in ORS, OT, OC, ON, OS, OP.
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W' A k) by (intros A k H1 Hk H2; apply P_rt; [exact Hk| clear -H1 H2; lia]).
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k) by (intros A k H1 Hk H2; apply P_rt; [exact Hk| clear -H1 H2; lia]).
  Local Ltac kimg := apply P_img; [clear; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia| clear; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia| aci_clear_tac
                                   | pose proof ATPv_img as TI; clear -TI; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia].
  split; [exact WF|].
  split.
  { pose proof RT as RT0. unfold arep_rt, ATP88, ATSD in RT0 |- *.
    (nd_pre RT0 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
    (* the TLS cell at ATPv + 16: framed when nothing writes it, otherwise given by LS *)
    assert (R26' : rw_cells asegs m' (ATPv + 16) [C4 (Z_to_bv 64 0)]).
    { destruct LS as [E|LS']; [| exact LS'].
      eapply cells_frame; [exact R26 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
      apply P_tls; [clear; lia | clear; lia | right; exact E]. }
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [ exact R26'
            | lazymatch goal with |- rw_cells asegs m' ?A ?cs =>
                lazymatch goal with H : rw_cells asegs m A cs |- _ =>
                  eapply cells_frame; [exact H | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                    first [kimg | apply Kctx; clear; lia | apply P_tls; [clear; lia | clear; lia | left; clear; lia]]] end end ]. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; kimg. }
  split.
  { (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
  split.
  { intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR [SLOTS SUND] SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply P_rt; [clear; lia|]. do 5 right. left. unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; clear -Hc; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply (P_reg_hi c); [exact HcK| clear -Q5 Q6; lia| unfold afreearr, K_FREEARR_OFF in *; clear -Q1 Q2; lia| unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; clear -Q6; lia].
      + apply P_sh_res; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - split; [intros k Hk; apply (aslot_client c k HcK Hk); exact (SLOTS k Hk)|].
      eapply junk_frame; [exact SUND | exact MU | exact WM |]. intros POS. apply (P_reg_hi c); [exact HcK| clear -POS; lia| clear; lia| unfold K_FREEARR_OFF, K_REGION in *; clear -Q1 Q2; lia].
    - eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c k SAL HcK) as AL.
        split; [reflexivity|]. apply P_sh_res; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply P_sh_res; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split.
  { (* [comment removed for export] *)
    eapply (hq_frame _ AHI_laws L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched. apply Forall_forall. intros iv Hin.
      assert (D1 : disjoint_from W' (al_t L + 80) 128) by (apply Kt; clear; lia).
      assert (D2 : disjoint_from W' (AINSTANCE + 728) 256) by kimg.
      assert (D3 : disjoint_from W' 0xaf800 0x81030) by kimg.
      assert (D4 : disjoint_from W' 0x13e088 4) by kimg.
      pose proof (disjoint_from_In _ _ _ _ D1 Hin) as E1. pose proof (disjoint_from_In _ _ _ _ D2 Hin) as E2.
      pose proof (disjoint_from_In _ _ _ _ D3 Hin) as E3. pose proof (disjoint_from_In _ _ _ _ D4 Hin) as E4.
      split; [clear -E1; lia|]. split; [clear -E2; lia|]. split; [clear -E3; lia|]. split; [clear -E4; lia|].
      intros b Hb. destruct (xb_st b) as [q| |] eqn:Sb; [exact I| |].
      all: destruct (BUSY b Hb) as [CLB _]; pose proof CLB as CLBK; unfold K_NUM_CLASSES in CLB;
           (nd_pre (PERC (xb_class b) CLBK) 12%nat; intros B1' B2' _ _ _ _ _ _ _ _ _ BR; nd_post);
           pose proof (size_of_class_facts (xb_class b) CLBK) as [BS _];
           assert (KB : 0 <= xb_slot b < ndist st (xb_class b)) by
             (apply BR; apply in_app_iff; right; apply in_app_iff; right; unfold busy_slots; apply in_map_iff; exists b; split; [reflexivity|];
              apply filter_In; split; [exact Hb| apply Z.eqb_refl]);
           assert (D5 : disjoint_from W' (xb_alloc L b) (size_of_class (xb_class b)));
           [ pose proof (aslot_client) as _;
             (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -BS; lia) (proj1 B1') KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post);
             assert (RI : al_res L <= aregion L (xb_class b) /\ aregion L (xb_class b) + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_REGION in *; clear -CLB RSP; nia);
             destruct RI as [RI1 RI2]; unfold K_REGION, K_FREEARR_OFF, xb_alloc in *;
             apply P_obj; [unfold tclr; pose proof (ad_tls_res L ALO) as TR; unfold adisj in TR; clear -TR P5 P4 B1' B2' RI1 RI2; lia
                          | pose proof (ad_ahm_res L ALO) as AR0; unfold adisj in AR0; rewrite (ao_ahm_eq L ALO) in AR0; unfold AAHM_SZ; clear -AR0 P5 P4 B1' B2' RI1 RI2; lia| unfold sclr; right; clear -P5 RI1 RHI; lia| unfold iclr, AIMG_HI; split; [clear -P5 RI1 RHI; lia| right; clear -P5 RI1 RHI; lia]
                          | clear -BS; lia| atop_facts; clear -P4 B1' B2' RI2 ORS; lia| apply hb_clear_fake_obj; clear -P5 P4 B1' B2' RI1 RI2; lia|];
             intros p B n Hin'; destruct (slot_vs_blocks (xb_class b) (xb_slot b) p B n CLBK KB Hin') as [(b' & EB & Sb' & _)|D]; [| clear -D; lia];
             rewrite (busy_of_of_In L st X b WF Hb) in EB; injection EB as <-; rewrite Sb in Sb'; discriminate
           | pose proof (disjoint_from_In _ _ _ _ D5 Hin) as E5; clear -E5; lia ].
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { (* [comment removed for export] *)
    cbn [AHI ah_sec] in HS |- *. unfold ASEC_of in *. (pose proof HS as ndP__; nd_pre ndP__ 5%nat; intros WFS ARR INST2 PZ SHZ; nd_post).
    (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
    split; [exact WFS|]. split; [| split; [| split]].
    - (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). exists order. split; [exact PO|].
      assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL). destruct WR as [_ WRB].
      split; [| split].
      + destruct order as [|o0 order'].
        * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
        * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply P_rt; [clear; cbn; lia|]. do 4 right. left. cbn [length] in LEN |- *. clear -LEN WB WRB; lia.
      + eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply P_rt; [clear -POS; lia|]. do 4 right. left. clear -POS WB WRB; lia.
      + intros i ch Hi. (nd_pre (PER i ch Hi) 3%nat; intros lv LV2 CH; nd_post).
        assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        (nd_pre (asec_wf_all L st _ ch WFS Hin) 4%nat; intros mb ms n0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into W1).
        exists lv. split; [exact LV2|]. eapply asec_chunk_client; [exact Hin| exact W1| exact LV2| exact CH].
    - (nd_pre INST2 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; kimg]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; kimg]|].
      split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; kimg]|].
      split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; kimg]|].
      split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; kimg]|].
      eapply junk_frame; [exact I6| exact MU| exact WM| intros _; kimg].
    - unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
      apply P_sh_res; [apply shad_mono; clear -RSP; lia| clear -POS; lia|].
      replace (shlen K_REGION) with 536870912 by reflexivity. rewrite !shad_div. clear -RSP. Z.div_mod_to_equations. lia.
    - intros x Hx HF HC. unfold K_HIGH_MEM in Hx.
      assert (SX : 0 <= shad x < 2^64 /\ 2148238848 <= shad x /\ shad x + 1 <= shad ATOP).   (* [comment removed for export] *)
      { rewrite !shad_div. pose proof ATOP_al16 as A16. unfold ASHOFF, AIMG_HI, KLS in *. clear -Hx A16. Z.div_mod_to_equations. lia. }
      (nd_pre SX 3%nat; intros SX SX1 SX2; nd_post).
      assert (XF : x < al_fake L \/ al_fake L + 11571200 <= x).
      { unfold astartup_hulls in HF. repeat lazymatch type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF; destruct HF as [? HF] | _ => idtac end.
        cbn [fst snd] in *. clear -H3. lia. }
      rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside W' (shad x) 1); [| clear; lia]. apply P_sh; [exact SX1| clear; lia| exact SX2|].
      pose proof (ao_fake L ALO) as OFK. unfold aobj in OFK. rewrite !shad_div. clear -XF OFK. Z.div_mod_to_equations. lia. }
  split.
  { cbn [AHI ah_depot]. eapply (adi_frame adepot_iface); [exact HD | exact MU | exact WM |].
    assert (DD : disjoint_from W' 0x1804c8 (0x5d0510 - 0x1804c8)).
    { apply P_img; [clear; lia| clear; lia| aci_clear_tac| pose proof ATPv_img as TI; clear -TI; lia]. }
    assert (DN : disjoint_from W' (al_nodes L) 1048576) by (apply P_rt; [clear; lia| clear; lia]).
    assert (DS : disjoint_from W' (al_store L) 8388608) by (apply P_rt; [clear; lia| clear; lia]).
    apply Forall_forall. intros iv Hin a Ha.
    pose proof (disjoint_from_In _ _ _ _ DD Hin) as E1. pose proof (disjoint_from_In _ _ _ _ DN Hin) as E2. pose proof (disjoint_from_In _ _ _ _ DS Hin) as E3.
    clear -E1 E2 E3 Ha. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | kimg]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; kimg|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; kimg |]); apply Forall_nil].
  intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c HcK) | reflexivity | reflexivity | |].
  - intros POS. apply P_sh_res; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply P_sh_res; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End ClientW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="CI_B"] Theorem AHI_frame : forall L RNG st LB m m' (W : list ivl),
  AHEAP_I L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                    \/ aahm_client (fst iv) (snd iv - fst iv)) W ->
  AHEAP_I L RNG st LB m'.
Proof.
  intros L RNG st LB m m' W (ALO & ARNG & [X [AR BL]] & HFK) MU WM CW. cbn [AHI ah_fake] in HFK.
  assert (MU' : munch (W ++ []) m m') by (rewrite app_nil_r; exact MU).
  pose proof (Forall_nil (fun iv : Z * Z => fst iv = ATPv + 16 /\ snd iv = ATPv + 20)) as WX.
  assert (LS : ([] : list (Z * Z)) = [] \/ rw_cells asegs m' (ATPv + 16) [C4 (Z_to_bv 64 0)]) by (left; reflexivity).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [eapply AREP_client; eauto| exact BL].
  - cbn [AHI ah_fake]. eapply afake_client; eauto.
Qed.

(* The frame with the TLS cell at ATP + 16 written as well, holding zero again in m'. *)
#[using="CI_B"] Theorem AHI_frame_lsan : forall L RNG st LB m m' (W : list ivl),
  AHEAP_I L RNG st LB m -> munch (W ++ [(ATP + 16, ATP + 20)]) m m' -> wmono asegs m m' ->
  Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                    \/ aahm_client (fst iv) (snd iv - fst iv)) W ->
  rw_cells asegs m' (ATP + 16) [C4 (Z_to_bv 64 0)] ->
  AHEAP_I L RNG st LB m'.
Proof.
  intros L RNG st LB m m' W (ALO & ARNG & [X [AR BL]] & HFK) MU WM CW LS0. cbn [AHI ah_fake] in HFK. unfold ATP in MU, LS0.
  assert (WX : Forall (fun iv : Z * Z => fst iv = ATPv + 16 /\ snd iv = ATPv + 20) [(ATPv + 16, ATPv + 20)]) by (constructor; [split; reflexivity | constructor]).
  assert (LS : [(ATPv + 16, ATPv + 20)] = [] \/ rw_cells asegs m' (ATPv + 16) [C4 (Z_to_bv 64 0)]) by (right; exact LS0).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [eapply AREP_client; eauto| exact BL].
  - cbn [AHI ah_fake]. eapply afake_client; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="CI_B"] Theorem AHI_malloc : amalloc_stmt CI AHEAP_I.
Proof. exact (amalloc_all adepot_iface AQUAR AFAKE AH_laws poison_remap_proof CI aci_ok aci_ok2). Qed.

#[using="CI_B"] Theorem AHI_free : afree_stmt CI AHEAP_I.
Proof. exact (afree_total adepot_iface AFAKE AHI_laws CI aci_okQ aci_ok2 adepot_frameD afake_frameD). Qed.

#[using="CI_B"] Theorem AHI_free_null : afree_null_stmt CI AHEAP_I.
Proof. exact (afree_nullP adepot_iface ASEC_of AFAKE AHI_laws CI aci_okQ). Qed.

Definition AI_of : AMallocIface :=
  {| aci := CI;
     AHEAP := AHEAP_I;
     AI_aci_img := aci_img;
     AI_aci_lo := aci_lo;
     AI_rng_mono := AHI_rng_mono;
     AI_perm := AHI_perm;
     AI_frame := AHI_frame;
     AI_frame_lsan := AHI_frame_lsan;
     AI_block := AHI_block;
     AI_block_bounds := AHI_block_bounds;
     AI_blocks_disjoint := AHI_blocks_disjoint;
     AI_blocks_nodup := AHI_blocks_nodup;
     AI_hb_ids := AHI_hb_ids;
     AI_layout := AHI_layout;
     AI_relro := AHI_relro;
     AI_rtcells := AHI_rtcells;
     AI_malloc := AHI_malloc;
     AI_free := AHI_free;
     AI_free_null := AHI_free_null |}.

#[using="Type"] Lemma AI_of_E : AHEAP AI_of = AHEAP_P AHI.
Proof. reflexivity. Qed.
#[using="Type"] Lemma AI_of_aci : aci AI_of = CI.
Proof. reflexivity. Qed.
End Gen.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ACanary.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ASecStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeNull.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.AFreeAll.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ART_HULLS : list (Z * Z) :=
  [(0xa5000, 0xa7000); (0xa75b8, 0xa75c0); (0xa75e0, 0xa75e8); (0xa75f0, 0xa75f8); (0xa7600, 0xa7608); (0xa7618, 0xa7628); (0xa7668, 0xa7670);
   (0xa76e8, 0xa76f0); (0xa7738, 0xa7748); (0xa7778, 0xa7780); (0xab398, 0xab778); (0xac1b8, 0xac1c5); (0xac1f8, 0xac20c); (0xac224, 0xac230);
   (0xac24d, 0xac24e); (0xac258, 0xac259); (0xae25c, 0xae25d); (0xae260, 0xae261); (0xae264, 0xae268); (0xae9f8, 0xaea04); (0xaf6d8, 0xaf6da);
   (0xaf6e0, 0xaf6f8); (0xaf6fc, 0xaf700); (0xafc00, 0x130c30); (0x130c60, 0x130c63); (0x13e488, 0x13e48c); (0x13e498, 0x13e49c);
   (0x13e4a0, 0x13e4a8); (0x1404c0, 0x1404d0); (0x140548, 0x140550); (0x140578, 0x140580); (0x1405a0, 0x1405a8); (0x1405b1, 0x1405b2);
   (0x1405b8, 0x1405c0); (0x140600, 0x140608); (0x140618, 0x140628); (0x14062c, 0x14062d); (0x1808c8, 0x5d0910); (0x5e18f0, 0x5e1af0); (0x601c78, 0x601c80);
   (0x602d60, 0x602d68)].
Definition ci_iv_okb (iv : Z * Z) : bool :=
  (0x10000 <=? fst iv) && (snd iv <=? 0x604000) && forallb (fun h => (snd iv <=? fst h) || (snd h <=? fst iv)) ART_HULLS.
(* [comment removed for export] *)
Definition ci_okb (CI : list (Z * Z)) : bool := forallb ci_iv_okb CI.
Definition hull_inb (A k : Z) : bool := existsb (fun h => (fst h <=? A) && (A + k <=? snd h)) ART_HULLS.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Gen.
Variable CI : list (Z * Z).
Hypothesis CI_B : ci_okb CI = true.

Definition aci_clear (A k : Z) : Prop := Forall (fun iv => A + k <= fst iv \/ snd iv <= A) CI.

#[using="CI_B"] Lemma ci_iv : forall iv, In iv CI -> 0x10000 <= fst iv /\ snd iv <= 0x604000 /\ forall h, In h ART_HULLS -> snd iv <= fst h \/ snd h <= fst iv.
Proof.
  intros iv Hin. pose proof (proj1 (forallb_forall _ _) CI_B iv Hin) as B. unfold ci_iv_okb in B.
  apply andb_prop in B as [B B3]. apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
  split; [exact B1|]. split; [exact B2|]. intros h Hh. pose proof (proj1 (forallb_forall _ _) B3 h Hh) as Bh. cbv beta in Bh.
  apply orb_prop in Bh as [Bh|Bh]; apply Z.leb_le in Bh; [left| right]; exact Bh.
Qed.

(* [comment removed for export] *)
#[using="CI_B"] Lemma aci_clear_hull : forall A k, hull_inb A k = true -> aci_clear A k.
Proof.
  intros A k HB. unfold hull_inb in HB. apply existsb_exists in HB as (h & Hh & B). apply andb_prop in B as [B1 B2]. apply Z.leb_le in B1. apply Z.leb_le in B2.
  unfold aci_clear. apply Forall_forall. intros iv Hin. (nd_pre (ci_iv iv Hin) 3%nat; intros _ _ C; nd_post). destruct (C h Hh) as [D|D]; lia.
Qed.

Ltac hull_in := cbn [In]; repeat first [left; reflexivity | right].
#[using="CI_B"] Lemma aci_okQ : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI
                           /\ (snd iv <= 0xab670 \/ 0xab730 <= fst iv)
                           /\ (snd iv <= 0xafc00 \/ 0x130c30 <= fst iv)
                           /\ (snd iv <= 0x13e488 \/ 0x13e48c <= fst iv)) CI.
Proof.
  apply Forall_forall. intros iv Hin. (nd_pre (ci_iv iv Hin) 3%nat; intros C1 C2 C; nd_post).
  pose proof (C (0x1808c8, 0x5d0910) ltac:(unfold ART_HULLS; hull_in)) as H1. pose proof (C (0xab398, 0xab778) ltac:(unfold ART_HULLS; hull_in)) as H2.
  pose proof (C (0xafc00, 0x130c30) ltac:(unfold ART_HULLS; hull_in)) as H3. pose proof (C (0x13e488, 0x13e48c) ltac:(unfold ART_HULLS; hull_in)) as H4.
  cbn [fst snd] in *. unfold AIMG_HI. lia.
Qed.
#[using="CI_B"] Lemma aci_ok : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Proof. eapply Forall_impl; [| exact aci_okQ]. cbv beta. intros iv (H1 & H2 & H3 & _). auto. Qed.
#[using="CI_B"] Lemma aci_ok2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
Proof.
  apply Forall_forall. intros iv Hin. (nd_pre (ci_iv iv Hin) 3%nat; intros C1 C2 C; nd_post).
  pose proof (C (0xab398, 0xab778) ltac:(unfold ART_HULLS; hull_in)) as H2. cbn [fst snd] in *. unfold AINSTANCE. lia.
Qed.
#[using="CI_B"] Lemma aci_img : forall iv, In iv CI -> snd iv <= AIMG_HI.
Proof. intros iv Hin. (pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as ndP__; nd_pre ndP__ 3%nat; intros _ _ H; nd_post). exact H. Qed.
#[using="CI_B"] Lemma aci_ok1 : forall iv, In iv CI -> 0 <= fst iv /\ snd iv <= AIMG_HI.
Proof. intros iv Hin. (pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as ndP__; nd_pre ndP__ 3%nat; intros H1 _ H; nd_post). split; [clear -H1; lia| exact H]. Qed.
#[using="CI_B"] Lemma aci_lo : forall iv, In iv CI -> 0 <= fst iv.
Proof. intros iv Hin. pose proof (proj1 (Forall_forall _ _) aci_ok iv Hin) as (H1 & _). lia. Qed.

Ltac aci_clear_tac := apply aci_clear_hull; try rewrite ATPv_img; vm_compute; reflexivity.

Lemma achunk_eq_dec' : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; apply Z.eq_dec. Defined.

(* [comment removed for export] *)
#[using="Type"] Lemma junk_any : forall m m' A n, junk_at m A n -> wmono asegs m m' -> 0x604000 <= A -> junk_at m' A n.
Proof. intros m m' A n H WM HA. exact (dc_at_any m m' A n H WM HA). Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma aobj_sub_sclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> sclr A k.
Proof. intros a n A k (_ & _ & _ & HS & _) H1 H2. unfold sclr in *. lia. Qed.
#[using="Type"] Lemma aobj_sub_iclr : forall a n A k, aobj a n -> a <= A -> A + k <= a + n -> iclr A k.
Proof. intros a n A k (_ & HG & _ & _ & HI) H1 H2. unfold iclr in *. lia. Qed.

Section ClientW.
Variables (L : alayout) (st : astate) (X : aconc) (LB : list ablock) (m m' : amem) (W Wx : list (Z * Z)).
Hypothesis ALO : alayout_ok L.
Hypothesis AR : AREP AHI L st X m.
Hypothesis BL : ablocks L st X LB.
Hypothesis HFK : AFAKE L LB m.
Hypothesis MU0 : munch (W ++ Wx) m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis CW : Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                                 \/ aahm_client (fst iv) (snd iv - fst iv)) W.
(* Wx: writes to the 4-byte TLS cell at ATPv + 16; when there are any, the cell holds zero again in m'. *)
Hypothesis WX : Forall (fun iv => fst iv = ATPv + 16 /\ snd iv = ATPv + 20) Wx.
Hypothesis LS : Wx = [] \/ rw_cells asegs m' (ATPv + 16) [C4 (Z_to_bv 64 0)].
Let W' := List.filter nonempty (W ++ Wx).
Let MU : munch W' m m' := munch_filter_nonempty (W ++ Wx) m m' MU0.

(* [comment removed for export] *)
#[using="X m ALO AR BL"] Lemma hb_where : forall p B n, In (HB p B n) LB ->
  (exists c, 1 <= c < K_NUM_CLASSES /\ aregion L c <= B /\ B + n <= aregion L c + c_allocated_user (get_cls st c)
             /\ c_allocated_user (get_cls st c) <= K_FREEARR_OFF /\ 1 <= n)
  \/ (exists mb ms, B = mb + 6144 /\ 1 <= n /\ n + 6144 <= ms /\ sec_wf1 L (CSec mb ms n)).
Proof.
  intros p B n Hin.
  destruct (hb_cases L st X LB m p B n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - left. exists (xb_class b). destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). (nd_pre (PERC _ CLB) 3%nat; intros A1 A2 _; nd_post).
    pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user in *.
    split; [exact CLB|]. split; [clear -P5 RZ; lia|]. split; [clear -P4 FIT RG; lia|]. split; [unfold K_FREEARR_OFF in *; clear -A1 A2; lia| clear -NB; lia].
  - right. exists mb, ms. pose proof G as G0. cbn [sec_wf1] in G0. (nd_pre G0 7%nat; intros _ _ _ G4 G5 G6 _; nd_post).
    (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR _ NSE _ MSR _; nd_post). rewrite <- G4 in MSR.
    split; [exact EA|]. split; [clear -G5; lia|]. split; [clear -RSR NSE MSR; lia| exact G].
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI_B L st X LB m ALO AR BL HFK CW WX"] Lemma P_img : forall A k, 0 <= k -> 0x10000 <= A /\ A + k <= 0x604000 -> aci_clear A k ->
  (A + k <= ATPv + -200 \/ ATPv + 312 <= A) -> disjoint_from W' A k.      (* [comment removed for export] *)
Proof.
  intros A k Hk HA CLR HT. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi; clear -HT Hk; lia].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.   (* [comment removed for export] *)
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ _ SB; nd_post). unfold aobj in *.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; clear -KT HT NEV Hk; lia      (* [comment removed for export] *)
                              | unfold aahm_client, AAHM_SZ in KH; rewrite <- (ao_ahm_eq L ALO) in KH; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; clear -KH OAHI NEV HA Hk; lia].      (* [comment removed for export] *)
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 SB NEV HA. lia.
  - pose proof (proj1 (Forall_forall _ _) CLR iv Hiv) as D. cbn beta in D. clear -D I1 I2 NEV. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 6%nat; intros _ _ _ _ K5 _; nd_post). clear -K5 F1 F2 OFK OFKI HA NEV. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (alayout_space L ALO) as (SP1 & _). unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Q1 B1 B2 NEV HA SP1 Hc. nia.
      * cbn [sec_wf1] in Q3. (nd_pre Q3 3%nat; intros _ G2 _; nd_post). apply ablk_lin in G2. unfold AIMG_HI in G2. clear -G2 B1 B2 NEV HA. lia.   (* [comment removed for export] *)
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 6%nat; intros _ _ _ _ K5 _; nd_post). clear -K5 B1 B2 OFK OFKI HA NEV. lia.
  - clear -K5 NEV HA. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 _]. unfold ASHOFF in *. clear -I0 I1 I2 NEV HA. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 6%nat; intros _ _ _ _ K5 _; nd_post). unfold ASHOFF in *. clear -K5 F1 F2 OFK OFKI HA NEV. lia.
Qed.

(* [comment removed for export] *)
#[using="CI CI_B m ALO HFK CW WX"] Lemma P_obj : forall A k, tclr A k -> (A + k <= AAHMv \/ AAHMv + AAHM_SZ <= A) -> sclr A k -> iclr A k -> 0 <= k -> A + k <= ATOP ->      (* [comment removed for export] *)
  (A + k <= al_fake L \/ al_fake L + 11571200 <= A) ->
  (forall p B n, In (HB p B n) LB -> A + k <= B \/ B + n <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k HT HAH HS HI Hk HC HF HB. unfold sclr, KLS in HS. unfold iclr, AIMG_LO, AIMG_HI in HI. destruct HI as [HA HI].
  subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi; unfold tclr in HT; clear -HT Hk; lia].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ S47 SB; nd_post). unfold aobj in *.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; unfold tclr in HT; clear -KT HT NEV Hk; lia      (* [comment removed for export] *)
                              | unfold aahm_client in KH; clear -KH HAH NEV Hk; lia].      (* [comment removed for export] *)
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 NEV HC. lia.
  - (pose proof (proj1 (Forall_forall _ _) aci_ok iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros I0 _ I3; nd_post). unfold AIMG_HI in I3. clear -I0 I1 I2 I3 NEV HI. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 F1 F2 HF NEV Hk. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + pose proof (HB q B n' Hb) as D. clear -D B1 B2 NEV Hk. lia.
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 B1 B2 HF NEV Hk. lia.
  - clear -K5 NEV HS Hk. lia.
  - (pose proof (proj1 (Forall_forall _ _) aci_ok iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros I0 _ I3; nd_post). unfold AIMG_HI, ASHOFF in *. clear -I0 I1 I2 I3 NEV HS Hk. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). (pose proof OFK as ndP__; nd_pre ndP__ 5%nat; intros _ _ OFK3 OFKS _; nd_post). unfold sclr, KLS in OFKS.
    unfold FAKESZ, ASHOFF in *. clear -K5 K6 F1 F2 OFK3 OFKS OFKI NEV HS Hk. lia.
Qed.

(* [comment removed for export] *)
#[using="tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_sh : forall A k, 2148239360 <= A -> 0 <= k -> A + k <= shad ATOP ->
  (A + k <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k HA Hk HC HF.
  assert (HC2 : A + k <= 17594332446720 /\ 8 * (A + k) <= ATOP + 8 * ASHOFF).
  { rewrite shad_div in HC. pose proof ATOP_al16 as A16. unfold ASHOFF in *. clear -HC A16. Z.div_mod_to_equations. lia. }
  clear HC. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi; pose proof atp_lin as TLN; clear -TLN HA Hk; lia].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
  (pose proof OFK as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ OFKS _; nd_post). unfold sclr, KLS in OFKS.
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ S47 SB; nd_post). unfold aobj in *.
  assert (SF : shad (al_fake L) = al_fake L / 8 + ASHOFF /\ shad (al_fake L + 11571200) = al_fake L / 8 + 1446400 + ASHOFF).
  { rewrite !shad_div. clear -OFK. Z.div_mod_to_equations. lia. }
  destruct SF as [SF1 SF2]. unfold ASHOFF in *.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; pose proof atp_lin as TLN; clear -KT TLN NEV HA Hk HC2; lia      (* [comment removed for export] *)
                              | unfold aahm_client, AAHM_SZ in KH; rewrite <- (ao_ahm_eq L ALO) in KH; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI; unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI; clear -KH OAH OAHI NEV HA Hk HC2; lia].      (* [comment removed for export] *)
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 NEV HC2. lia.
  - destruct (aci_ok1 iv Hiv) as [_ I3]. unfold AIMG_HI in I3. clear -I1 I2 I3 NEV HA. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 F1 F2 OFK OFKS NEV HC2 HA. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (alayout_space L ALO) as (SP1 & _). unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Q1 B1 B2 NEV HC2 SP1 Hc. nia.
      * cbn [sec_wf1] in Q3. (nd_pre Q3 3%nat; intros _ G2 _; nd_post). unfold ablk, KLS, AIMG_HI in G2. clear -G2 Q2 B1 B2 NEV HC2 HA. lia.   (* [comment removed for export] *)
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 B1 B2 OFK OFKS HC2 HA NEV. lia.
  - clear -K5 NEV HC2. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 I3]. unfold AIMG_HI in *. clear -I0 I1 I2 I3 NEV HA. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 F1 F2 SF1 SF2 HF NEV Hk. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI X m AR"] Lemma hb_prim_span : forall p B n c,
  In (HB p B n) LB -> 1 <= c < K_NUM_CLASSES -> aregion L c <= B -> B + n <= aregion L c + c_allocated_user (get_cls st c) ->
  al_space_beg L + K_REGION <= B /\ B + n <= al_space_beg L + K_SPACE_SIZE /\ B + n <= aregion L c + K_FREEARR_OFF.
Proof.
  intros p B n c Hin Hc Q1 Q2. destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). (nd_pre (PERC c Hc) 3%nat; intros A1 A2 _; nd_post).
  unfold aregion, K_NUM_CLASSES, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. change (2^37) with 137438953472. clear -Hc Q1 Q2 A1 A2. nia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI st X m ALO AR BL"] Lemma hb_clear_obj : forall A k,
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_space_beg L + K_SPACE_SIZE <= A /\ A + k <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA)
   \/ (al_res L <= A /\ A + k <= al_space_beg L + K_REGION)) ->
  forall p B n, In (HB p B n) LB -> A + k <= B \/ B + n <= A.
Proof.
  intros A k HR p B n Hin.
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res.
  pose proof (ad_store_res L ALO) as D_s_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  unfold adisj, aobj in *.
  destruct (hb_where p B n Hin) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - (pose proof (hb_prim_span p B n c Hin Hc Q1 Q2) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post).
    unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    clear -HR S1 S2 D_t_res D_c_res D_n_res D_s_res D_p_res RSP ORS. lia.
  - cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (Ct & Cc & Cr & Cp & Cn & Cs & _); nd_post).
    unfold K_REGION, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    clear -HR Ct Cc Cr Cp Cn Cs RSP ORS Q2. lia.
Qed.

#[using="rc tlsI ALO"] Lemma hb_clear_fake_obj : forall A k,
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_res L <= A /\ A + k <= al_res L + 137439023104)) ->
  A + k <= al_fake L \/ al_fake L + 11571200 <= A.
Proof.
  intros A k HR.
  pose proof (ad_t_fake L ALO) as D1. pose proof (ad_ctx_fake L ALO) as D2. pose proof (ad_nodes_fake L ALO) as D3.
  pose proof (ad_store_fake L ALO) as D4. pose proof (ad_fake_ptr L ALO) as D5. pose proof (ad_fake_res L ALO) as D6. unfold adisj in *.
  clear -HR D1 D2 D3 D4 D5 D6. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_rt : forall A k, 0 <= k ->
  (   (al_t L <= A /\ A + k <= al_t L + 4096) \/ (al_ctx L <= A /\ A + k <= al_ctx L + 65536)
   \/ (al_nodes L <= A /\ A + k <= al_nodes L + 1048576) \/ (al_store L <= A /\ A + k <= al_store L + 8388608)
   \/ (al_ptr_array L <= A /\ A + k <= al_ptr_array L + 8388608)
   \/ (al_space_beg L + K_SPACE_SIZE <= A /\ A + k <= al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA)
   \/ (al_res L <= A /\ A + k <= al_space_beg L + K_REGION)) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk HR.
  pose proof (ao_space L ALO) as RSP.
  (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as T1. pose proof (ad_tls_ctx L ALO) as T2. pose proof (ad_tls_nodes L ALO) as T3. pose proof (ad_tls_store L ALO) as T4.
  pose proof (ad_tls_ptr L ALO) as T5. pose proof (ad_tls_res L ALO) as T6. unfold adisj in T1, T2, T3, T4, T5, T6.
  pose proof (ad_ahm_t L ALO) as H1a. pose proof (ad_ahm_ctx L ALO) as H2a. pose proof (ad_ahm_nodes L ALO) as H3a. pose proof (ad_ahm_store L ALO) as H4a.
  pose proof (ad_ahm_ptr L ALO) as H5a. pose proof (ad_ahm_res L ALO) as H6a. unfold adisj in H1a, H2a, H3a, H4a, H5a, H6a. pose proof (ao_ahm_eq L ALO) as EAH.
  assert (SUB : exists a n, aobj a n /\ ((a + n <= ATPv + -200 \/ ATPv + 312 <= a) /\ (a + n <= AAHMv \/ AAHMv + 3727360 <= a)) /\ a <= A /\ A + k <= a + n).
  { unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION in HR. change (2^37) with 137438953472 in HR.
    destruct HR as [H|[H|[H|[H|[H|[H|H]]]]]];
      [ exists (al_t L), 4096 | exists (al_ctx L), 65536 | exists (al_nodes L), 1048576 | exists (al_store L), 8388608
      | exists (al_ptr_array L), 8388608 | exists (al_res L), 137439023104 | exists (al_res L), 137439023104 ];
      (split; [first [exact (ao_t L ALO) | exact (ao_ctx L ALO) | exact (ao_nodes L ALO) | exact (ao_store L ALO) | exact (ao_ptr L ALO) | exact (ao_res L ALO)] |]);
      rewrite <- EAH; clear -H RSP T1 T2 T3 T4 T5 T6 H1a H2a H3a H4a H5a H6a; lia. }
  (nd_pre SUB 6%nat; intros a n OA [TC TAH] S1 S2; nd_post).
  apply P_obj; [unfold tclr; clear -TC S1 S2; lia | unfold AAHM_SZ; clear -TAH S1 S2; lia | exact (aobj_sub_sclr a n A k OA S1 S2) | exact (aobj_sub_iclr a n A k OA S1 S2) | exact Hk | | |].
  - (pose proof OA as ndP__; nd_pre ndP__ 4%nat; intros _ _ O3 _; nd_post). clear -O3 S2. lia.
  - apply hb_clear_fake_obj. unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_REGION in HR. change (2^37) with 137438953472 in HR. clear -HR RSP. lia.
  - exact (hb_clear_obj A k HR).
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI CI_B X LB m ALO AR BL HFK CW WX"] Lemma P_reg_hi : forall c A k, 1 <= c < K_NUM_CLASSES -> 0 <= k ->
  aregion L c + c_allocated_user (get_cls st c) <= A -> A + k <= aregion L c + K_REGION -> disjoint_from W' A k.
Proof.
  intros c A k Hc Hk H1 H2.
  pose proof (ao_res L ALO) as ORS. pose proof (ao_space L ALO) as RSP. unfold aobj in *.
  destruct AR as ((_ & _ & _ & _ & _ & PERC & _) & _). (nd_pre (PERC c Hc) 3%nat; intros A1 A2 _; nd_post).
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104).
  { unfold aregion, K_NUM_CLASSES, K_REGION in *. clear -Hc RSP. nia. }
  destruct RI as [RI1 RI2]. unfold K_REGION in *. pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  pose proof (ad_tls_res L ALO) as TR. unfold adisj in TR.
  pose proof (ad_ahm_res L ALO) as AR0. unfold adisj in AR0. rewrite (ao_ahm_eq L ALO) in AR0.
  apply P_obj; [unfold tclr; clear -TR H1 H2 RI1 RI2 A1; lia| unfold AAHM_SZ; clear -AR0 H1 H2 RI1 RI2 A1; lia| unfold sclr; right; clear -H1 RI1 RHI A1; lia| unfold iclr, AIMG_HI; split; [clear -H1 RI1 RHI A1; lia| right; clear -H1 RI1 RHI A1; lia]
               | exact Hk| atop_facts; clear -H2 RI2 ORS; lia| apply hb_clear_fake_obj; clear -H1 H2 RI1 RI2 A1; lia|].
  intros p B n Hin. destruct (hb_where p B n Hin) as [(c' & Hc' & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - destruct (Z.eq_dec c' c) as [->|NE]; [clear -Q2 H1; lia|].
    destruct (Z.lt_ge_cases c' c) as [LT|GE].
    + right. pose proof (regions_sep L c' c LT) as RS. unfold K_REGION, K_FREEARR_OFF in *. clear -RS Q2 Q3 H1 A1. lia.
    + left. pose proof (regions_sep L c c' ltac:(clear -GE NE; lia)) as RS. unfold K_REGION in *. clear -RS Q1 H2. lia.
  - cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (_ & _ & Cr & _); nd_post). clear -Cr RI1 RI2 H1 H2 Q2 A1. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI m ALO AR BL"] Lemma slot_vs_blocks : forall c k p B n, 1 <= c < K_NUM_CLASSES -> 0 <= k < ndist st c -> In (HB p B n) LB ->
  (exists b, busy_of X c k = Some b /\ xb_st b = BLive p /\ B = xb_user L b /\ n = xb_n b)
  \/ (B + n <= aslot_addr L c k \/ aslot_addr L c k + size_of_class c <= B).
Proof.
  intros c k p B n Hc Hk Hin.
  pose proof AR as (WF & _). (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post).
  pose proof (size_of_class_facts c Hc) as [QS _]. (nd_pre (PERC c Hc) 3%nat; intros A1 A2 _; nd_post).
  (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 A1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
  destruct (hb_cases L st X LB m p B n ALO AR BL Hin) as [(b & Hb & Sb & Ub & Nb & CLB & NB & FIT & LV & PRIM & KB & Q5 & Q4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    + destruct (Z.eq_dec (xb_slot b) k) as [EK|NK].
      * left. exists b. rewrite <- EC, <- EK. split; [exact (busy_of_of_In L st X b WF Hb)|]. split; [exact Sb|]. split; [symmetry; exact Ub| symmetry; exact Nb].
      * right. pose proof (slots_disjoint L c (xb_slot b) k ltac:(clear -KB; lia) ltac:(clear -Hk; lia) NK ltac:(clear -QS; lia)) as SD.
        pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user, xb_alloc in *. rewrite EC in *.
        clear -SD FIT RG RZ. lia.
    + right. pose proof (rounded_size_ge n) as RG. pose proof (rz_size_ge16 n) as RZ. subst B n. unfold xb_user, xb_alloc in *.
      (nd_pre (PERC (xb_class b) CLB) 3%nat; intros B1' B2' _; nd_post). unfold K_FREEARR_OFF in *.
      destruct (Z.lt_ge_cases (xb_class b) c) as [LT|GE].
      * left. pose proof (regions_sep L (xb_class b) c LT) as RS. unfold K_REGION in RS. clear -RS Q4 P5 FIT RG RZ B1' B2'. lia.
      * right. pose proof (regions_sep L c (xb_class b) ltac:(clear -GE NC; lia)) as RS. unfold K_REGION in RS. clear -RS Q5 P4 A1 A2 RZ. lia.
  - right. cbn [sec_wf1] in G. (nd_pre G 7%nat; intros _ _ _ G4 G5 G6 (_ & _ & Cr & _); nd_post). subst B. unfold SEC_UOFF.
    (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR _ NSE _ MSR _; nd_post). rewrite <- G4 in MSR.
    pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_NUM_CLASSES, K_REGION in *; clear -Hc RSP; nia).
    unfold K_REGION, K_FREEARR_OFF in *. clear -Cr RI P5 P4 A1 A2 G5 RSR NSE MSR. lia.
Qed.

(* [comment removed for export] *)
#[using="rc"] Lemma disjoint_from_In : forall (Wl : list (Z * Z)) A k iv, disjoint_from Wl A k -> In iv Wl -> A + k <= fst iv \/ snd iv <= A.
Proof.
  intros Wl A k iv. induction Wl as [|[lo hi] Wl IH]; intros D Hin; [destruct Hin|].
  cbn in D. destruct D as [D1 D2]. destruct Hin as [<-|Hin]; [cbn; lia| apply IH; assumption].
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_sh_res : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof.
  intros A k H1 Hk H2. pose proof (ao_res L ALO) as ORS. pose proof (ao_fake L ALO) as OFK. pose proof (ad_fake_res L ALO) as D. pose proof (ao_res_hi L ALO) as RHI. unfold aobj, adisj in *.
  assert (SR : 2148239360 <= shad (al_res L) /\ shad (al_res L + 137439023104) <= shad ATOP   (* [comment removed for export] *)
               /\ (shad (al_res L + 137439023104) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad (al_res L))).
  { rewrite !shad_div. unfold ASHOFF. clear -ORS OFK D RHI. Z.div_mod_to_equations. lia. }
  apply P_sh; clear -SR H1 Hk H2; lia.
Qed.

#[using="rc tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_dtls : forall A k, al_dtls L <= A -> 0 <= k -> A + k <= al_dtls L + 4096 -> disjoint_from W' A k.
Proof.
  intros A k H1 Hk H2.
  pose proof (ao_dtls L ALO) as OD. pose proof (ad_fake_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  unfold aobj, adisj in *.
  pose proof (ad_tls_dtls L ALO) as TD. unfold adisj in TD.
  pose proof (ad_ahm_dtls L ALO) as AD0. unfold adisj in AD0. rewrite (ao_ahm_eq L ALO) in AD0.
  apply P_obj; [unfold tclr; clear -TD H1 H2; lia| unfold AAHM_SZ; clear -AD0 H1 H2; lia| exact (aobj_sub_sclr _ _ A k (ao_dtls L ALO) H1 H2)| exact (aobj_sub_iclr _ _ A k (ao_dtls L ALO) H1 H2)| exact Hk| clear -H2 OD; lia| clear -H1 H2 D1; lia|].   (* [comment removed for export] *)
  intros p B n Hin. destruct (hb_where p B n Hin) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
  - (pose proof (hb_prim_span p B n c Hin Hc Q1 Q2) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 S3; nd_post). unfold K_REGION, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
    clear -H1 H2 S1 S2 D2 RSP ORS. lia.
  - cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & Cd); nd_post). clear -H1 H2 Cd Q2. lia.
Qed.

(* [comment removed for export] *)
#[using="rc tlsI CI CI_B st X LB m ALO AR BL HFK CW WX"] Lemma P_fakehdr : disjoint_from W' (al_fake L) 36864.
Proof.
  subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi; pose proof (ad_tls_fake L ALO) as TF; unfold adisj in TF; clear -TF; lia].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof (ao_fake L ALO) as OFK. pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.   (* [comment removed for export] *)
  (pose proof OFK as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ OFKS _; nd_post). unfold sclr, KLS in OFKS.
  (pose proof (ao_stack L ALO) as ndP__; nd_pre ndP__ 4%nat; intros _ _ S47 SB; nd_post). unfold aobj in *.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; pose proof (ad_tls_fake L ALO) as TF; unfold adisj in TF; clear -KT TF NEV; lia      (* [comment removed for export] *)
                              | unfold aahm_client, AAHM_SZ in KH; rewrite <- (ao_ahm_eq L ALO) in KH; pose proof (ad_ahm_fake L ALO) as AF; unfold adisj in AF; clear -KH AF NEV; lia].      (* [comment removed for export] *)
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 SB NEV OFK. lia.
  - destruct (aci_ok1 iv Hiv) as [_ I3]. unfold AIMG_HI in I3. clear -I1 I2 I3 NEV OFK OFKI. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 6%nat; intros _ _ _ _ K5 _; nd_post). clear -K5 F1 F2 NEV. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + pose proof (hb_clear_fake_obj) as _. destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * (pose proof (hb_prim_span q B n' c Hb Hc Q1 Q2) as ndP__; nd_pre ndP__ 3%nat; intros S1 S2 _; nd_post). pose proof (ad_fake_res L ALO) as D. pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
        unfold adisj, aobj, K_REGION, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *. clear -S1 S2 D RSP ORS B1 B2 NEV. lia.
      * cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & Cf & _); nd_post). clear -Cf B1 B2 NEV Q2. lia.
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 6%nat; intros _ _ _ _ K5 _; nd_post). clear -K5 B1 B2 NEV. lia.
  - clear -K5 NEV OFK OFKS. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 I3]. unfold AIMG_HI in *. clear -I0 I1 I2 I3 NEV OFK OFKS OFKI. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in *.
    clear -K5 K6 F1 F2 OFK OFKS NEV. lia.
Qed.

(* [comment removed for export] *)
#[using="CI CI_B L st X LB m ALO AR BL HFK CW WX"] Lemma P_tls : forall A k, 0 <= k ->
  ((ATPv + -88 <= A /\ A + k <= ATPv + -80) \/ (ATPv + -8 <= A /\ A + k <= ATPv + 20) \/ (ATPv + 288 <= A /\ A + k <= ATPv + 312)) ->
  ((A + k <= ATPv + 16 \/ ATPv + 20 <= A) \/ Wx = []) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk HA NL. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros [lo hi] Hin.
  apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. cbn [fst snd] in NEV |- *. apply Z.ltb_lt in NEV.
  apply in_app_or in Hin as [Hin|Hin]; [| pose proof (proj1 (Forall_forall _ _) WX _ Hin) as [KL1 KL2]; cbn [fst snd] in KL1, KL2; subst lo hi;
                                          destruct NL as [NL|NL]; [clear -NL Hk; lia | rewrite NL in Hin; destruct Hin]].
  pose proof (proj1 (Forall_forall _ _) CW _ Hin) as C. unfold aclient_range, aclient_app_range in C. cbn [fst snd] in C.
  change (2^47)%Z with 140737488355328%Z in C. unfold ASHOFF in C.
  pose proof atp_lin as TLN. pose proof atp_below_atop as TBA. pose proof atop_range as ATR0.
  pose proof (ad_tls_fake L ALO) as TF. pose proof (ad_tls_res L ALO) as TR. unfold adisj in TF, TR.
  destruct C as [C|[KT|KH]]; [| unfold atls_client in KT; clear -KT HA NEV Hk; lia
                              | unfold aahm_client, AAHM_SZ in KH; rewrite <- (ao_ahm_eq L ALO) in KH; pose proof (ad_tls_ahm L ALO) as TA; unfold adisj in TA; clear -KH TA HA NEV Hk; lia].
  destruct C as [[K1|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]] | [(b & Hb & B1 & B2) | [K5|[(iv & Hiv & I1 & I2)|(cls & FA & fn & Hf & F1 & F2)]]]].
  - clear -K1 HA TBA NEV. lia.
  - destruct (ci_iv iv Hiv) as (_ & _ & CH). pose proof (CH (0x5e18f0, 0x5e1af0) ltac:(unfold ART_HULLS; cbn [In]; repeat first [left; reflexivity | right])) as HT.
    cbn [fst snd] in HT. pose proof ATPv_img as TPI. clear -HT I1 I2 NEV HA TPI. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 F1 F2 TF HA NEV. lia.
  - destruct b as [[q|cls] B n']; cbn [ab_addr ab_size] in *.
    + destruct (hb_where q B n' Hb) as [(c & Hc & Q1 & Q2 & Q3 & Q4)|(mb & ms & -> & Q1 & Q2 & Q3)].
      * pose proof (ao_space L ALO) as RSP. pose proof (alayout_space L ALO) as (SP1 & _). unfold aregion, K_NUM_CLASSES, K_REGION, K_FREEARR_OFF in *.
        clear -Q1 Q2 Q3 B1 B2 NEV HA TR RSP Hc. nia.
      * cbn [sec_wf1] in Q3. (nd_pre Q3 7%nat; intros _ _ _ _ _ _ (_ & _ & _ & _ & _ & _ & _ & _ & Ctls & _); nd_post). clear -Ctls Q2 B1 B2 NEV HA. lia.
    + (nd_pre (afake_lb L LB m cls B n' HFK Hb) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). unfold FAKESZ in K6. clear -K5 K6 B1 B2 TF HA NEV. lia.
  - clear -K5 NEV HA TBA ATR0 TLN. lia.
  - destruct (aci_ok1 iv Hiv) as [I0 I3]. pose proof (proj1 (Forall_forall _ _) aci_ok iv Hiv) as (I0' & _). unfold AIMG_HI in *. clear -I0' I1 I2 I3 NEV HA TLN. lia.
  - (nd_pre (afake_lb L LB m cls FA fn HFK Hf) 7%nat; intros _ _ _ _ K5 K6 _; nd_post). pose proof (ao_fake L ALO) as OFK. (pose proof OFK as ndP__; nd_pre ndP__ 5%nat; intros _ _ OFK3 OFKS _; nd_post).
    pose proof (aobj_img _ _ OFK ltac:(clear; lia)) as OFKI. unfold AIMG_HI in OFKI.
    unfold sclr, KLS, FAKESZ in *. clear -K5 K6 F1 F2 OFK3 OFKS OFKI NEV HA TLN ATR0. lia.
Qed.


(* [comment removed for export] *)
#[using="rc tlsI CI CI_B LB W Wx ALO AR BL HFK MU0 WM CW WX W' MU"] Lemma aslot_client : forall c k, 1 <= c < K_NUM_CLASSES -> 0 <= k < ndist st c ->
  match busy_of X c k with None => junk_at m (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m b end ->
  match busy_of X c k with None => junk_at m' (aslot_addr L c k) (size_of_class c) | Some b => aslot_busy L m' b end.
Proof.
  intros c k Hc Hk SL.
  pose proof AR as (WF & _). pose proof (size_of_class_facts c Hc) as [QS _].
  (pose proof WF as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ PERC _; nd_post). (nd_pre (PERC c Hc) 3%nat; intros A1 A2 _; nd_post).
  (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 A1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
  pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_NUM_CLASSES, K_REGION in *; clear -Hc RSP; nia).
  destruct RI as [RI1 RI2]. unfold K_REGION, K_FREEARR_OFF in *. pose proof (ao_res_hi L ALO) as RHI.
  (* [comment removed for export] *)
  assert (PSUB : forall A kk, aslot_addr L c k <= A -> 0 <= kk -> A + kk <= aslot_addr L c k + size_of_class c ->
      (forall b, busy_of X c k = Some b -> match xb_st b with BLive _ => A + kk <= xb_user L b \/ xb_user L b + xb_n b <= A | _ => True end) ->
      disjoint_from W' A kk).
  { intros A kk HA Hkk HB OWN.
    apply P_obj; [unfold tclr; pose proof (ad_tls_res L ALO) as TR; unfold adisj in TR; clear -TR HA HB P5 P4 A1 A2 RI1 RI2; lia
                 | pose proof (ad_ahm_res L ALO) as AR0; unfold adisj in AR0; rewrite (ao_ahm_eq L ALO) in AR0; unfold AAHM_SZ; clear -AR0 HA HB P5 P4 A1 A2 RI1 RI2; lia| unfold sclr; right; clear -HA P5 RI1 RHI; lia| unfold iclr, AIMG_HI; split; [clear -HA P5 RI1 RHI; lia| right; clear -HA P5 RI1 RHI; lia]
                 | exact Hkk| atop_facts; clear -HB P4 A1 A2 RI2 ORS; lia
                 | apply hb_clear_fake_obj; clear -HA HB P5 P4 A1 A2 RI1 RI2; lia|].   (* [comment removed for export] *)
    intros p B n Hin. destruct (slot_vs_blocks c k p B n Hc Hk Hin) as [(b & EB & Sb & -> & ->)|D]; [| clear -D HA HB; lia].
    specialize (OWN b EB). rewrite Sb in OWN. exact OWN. }
  destruct (busy_of X c k) as [b|] eqn:EB.
  - (nd_pre (busy_of_Some_facts X c k b EB) 3%nat; intros Hb Cb Kb; nd_post). pose proof (awf_fits L st X b WF Hb) as FIT.
    destruct (xb_st b) as [q| |] eqn:Sb.
    + (* [comment removed for export] *)
      unfold aslot_busy in SL |- *. cbv zeta in SL |- *. rewrite Sb in SL |- *. unfold xb_fits in FIT. rewrite Sb in FIT. (nd_pre FIT 3%nat; intros N0 RZ FIT; nd_post).
      unfold xb_user, xb_alloc in *. rewrite Cb, Kb in *. (nd_pre SL 3%nat; intros LH [stb [E HDR]] UJ; nd_post).
      assert (D : disjoint_from W' (aslot_addr L c k) (rz_size (xb_n b))).
      { apply PSUB; [clear; lia| clear -RZ; lia| clear -FIT RZ N0; pose proof (rounded_size_ge (xb_n b)); lia|].
        intros b' EB'. injection EB' as <-. rewrite Sb. unfold xb_user, xb_alloc. rewrite Cb, Kb. left. clear; lia. }
      split; [| split].
      * intros H16. destruct (LH H16) as [LC J]. split.
        -- eapply cells_frame; [exact LC | exact MU | exact WM |]. cbn [cells_size csize Nat.add]. eapply disjoint_from_sub; [exact D | clear; lia | clear -H16; lia | clear; lia].
        -- eapply junk_frame; [exact J | exact MU | exact WM |]. intros Hp. eapply disjoint_from_sub; [exact D | clear; lia | clear -Hp; lia | clear -Hp; lia].
      * exists stb. split; [exact E|]. eapply cells_frame; [exact HDR | exact MU | exact WM |]. cbn [cells_size csize Nat.add].
        eapply disjoint_from_sub; [exact D | clear -RZ; lia | clear; lia | clear; lia].
      * eapply junk_any; [exact UJ| exact WM| clear -P5 RI1 RHI RZ; lia].   (* [comment removed for export] *)
    + eapply (aslot_busy_frame L W' m m' MU WM); [exact SL| exact FIT|]. unfold xb_alloc. rewrite Cb, Kb.
      apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. injection EB' as <-. rewrite Sb. exact I.
    + eapply (aslot_busy_frame L W' m m' MU WM); [exact SL| exact FIT|]. unfold xb_alloc. rewrite Cb, Kb.
      apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. injection EB' as <-. rewrite Sb. exact I.
  - eapply junk_frame; [exact SL | exact MU | exact WM |]. intros _. apply PSUB; [clear; lia| clear -QS; lia| clear; lia|]. intros b' EB'. discriminate EB'.
Qed.

(* [comment removed for export] *)
#[using="CI CI_B X LB W Wx ALO AR BL HFK MU0 WM CW WX W' MU"] Lemma asec_chunk_client : forall mb ms n idx lv,
  In (CSec mb ms n) (sec_chunks_of st) -> sec_wf1 L (CSec mb ms n) ->
  (lv = true <-> sec_live st (CSec mb ms n)) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros mb ms n idx lv INC WF1 LVE CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. (nd_pre WF0 7%nat; intros G1 G2 G3 G4 G5 G6 GC; nd_post). (pose proof GC as ndP__; nd_pre ndP__ 10%nat; intros Ct Cc Cr Cp Cn Cs Cf Cd Ctls Cahm; nd_post).
  (pose proof (sec_facts n ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros NB _ RSE RSR _ NSE _ MSR MSM MSB; nd_post). rewrite <- G4 in MSR, MSM, MSB.
  (pose proof AR as ndP__; nd_pre ndP__ 8%nat; intros WF _ _ _ _ _ HS _; nd_post). cbn [AHI ah_sec] in HS. unfold ASEC_of in HS. pose proof HS as ((_ & _ & _ & _ & _ & WFA & [ND PW]) & _).
  pose proof (ao_fake L ALO) as OFK. unfold aobj in OFK. unfold K_HIGH_MEM in *.
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros G2a G2b _ _; nd_post).   (* [comment removed for export] *)
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8 /\ 2148239360 <= shad mb /\ shad mb + ms / 8 <= shad ATOP
               /\ (shad mb + ms / 8 <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad mb)).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. unfold ASHOFF, AIMG_HI in *. clear -G1 G2a G2b G3 G5 RSR NSE MSR MSM Cf OFK. Z.div_mod_to_equations. lia. }
  (nd_pre GR 6%nat; intros GR1 GR2 GR3 GR4 GR5 GR6; nd_post).
  (* [comment removed for export] *)
  assert (DLO : forall A k, mb <= A -> 0 <= k -> A + k <= mb + 6144 -> disjoint_from W' A k).
  { intros A k H1 Hk H2.
    apply P_obj; [unfold tclr; clear -Ctls H1 H2 MSR NSE RSR G5; lia| rewrite (ao_ahm_eq L ALO) in Cahm; unfold AAHM_SZ; clear -Cahm H1 H2 MSR NSE RSR G5; lia| clear -H1 H2 G2 MSR NSE RSR G5; unfold ablk, sclr, KLS, AIMG_HI in *; lia| clear -H1 H2 G2 MSR NSE RSR G5; unfold ablk, iclr, AIMG_LO, AIMG_HI, KLS in *; lia
                 | exact Hk| atop_facts; clear -H2 G3 MSR NSE RSR G5; lia| clear -H1 H2 Cf MSR NSE RSR G5; lia|].
    intros p B n' Hin. destruct (hb_cases L st X LB m p B n' ALO AR BL Hin) as [(b & _ & _ & Ub & Nb & _ & NB' & FIT & _ & _ & _ & _ & _ & R1 & R2)|(mb' & ms' & Lp & -> & G' & _ & INC')].
    - pose proof (rz_size_ge16 (xb_n b)) as RZ. pose proof (rounded_size_ge n') as RG. unfold xb_user in *. subst B n'. clear -R1 R2 Cr H1 H2 MSR NSE RSR RZ G5 FIT RG NB'. lia.
    - unfold SEC_UOFF. destruct (achunk_eq_dec' (CSec mb' ms' n') (CSec mb ms n)) as [E|NE].
      + injection E as -> -> ->. left. clear -H2; lia.
      + pose proof (PW _ _ INC' INC NE) as D. cbn [sec_mb sec_ms] in D.
        cbn [sec_wf1] in G'. (nd_pre G' 7%nat; intros _ _ _ G4' G5' G6' _; nd_post). (pose proof (sec_facts n' ltac:(clear -G5'; lia) G6') as ndP__; nd_pre ndP__ 9%nat; intros _ _ _ RSR' _ NSE' _ MSR' _; nd_post). rewrite <- G4' in MSR'.
        clear -D H1 H2 MSR' NSE' RSR' G5' MSR NSE RSR G5. lia. }
  assert (DSH : forall A k, shad mb <= A -> 0 <= k -> A + k <= shad mb + ms / 8 -> disjoint_from W' A k).
  { intros A k H1 Hk H2. apply P_sh; clear -H1 Hk H2 GR4 GR5 GR6; lia. }
  cbn [asec_chunk] in CH |- *. (nd_pre CH 9%nat; intros H1 H2 H3 H4 (b1 & ctx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DLO; clear; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DLO; clear; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DLO; clear; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DLO; clear; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DLO; clear; lia]. }
  split; [eapply junk_any; [exact H6| exact WM| clear -G2a; unfold AIMG_HI in *; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DSH; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DSH; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DSH; clear -GR3 GR1 POS; lia].
Qed.

(* [comment removed for export] *)
#[using="CI CI_B st X m W Wx ALO AR BL HFK MU0 WM CW WX W' MU"] Lemma afake_client : AFAKE L LB m'.
Proof.
  (pose proof HFK as ndP__; nd_pre ndP__ 9%nat; intros G CE (h0 & h1 & h2 & hs & HS) LOG NGC DC1 DC2 FL LV; nd_post).
  (pose proof G as ndP__; nd_pre ndP__ 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11; nd_post). unfold FAKESZ in *.
  (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros G2a G2b G2c G2d; nd_post). unfold AIMG_HI in G2a.   (* [comment removed for export] *)
  pose proof P_fakehdr as DF.
  split; [exact G|].
  split.
  { (nd_pre CE 8%nat; intros C1 C2 C3 C4 C5 C6 C7 C8; nd_post). unfold afake_cells.
    split; [eapply cells_frame; [exact C1| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac| pose proof ATPv_img as TI; clear -TI; lia]]|].
    split; [eapply cells_frame; [exact C2| exact MU| exact WM| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply P_tls; [clear; lia| clear; lia| left; clear; lia]]|].      (* [comment removed for export] *)
    split; [eapply cells_frame; [exact C3| exact MU| exact WM| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply P_tls; [clear; lia| clear; lia| left; clear; lia]]|].      (* [comment removed for export] *)
    split; [eapply cells_frame; [exact C4| exact MU| exact WM| cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply P_tls; [clear; lia| clear; lia| left; clear; lia]]|].      (* [comment removed for export] *)
    split; [eapply cells_frame; [exact C5| exact MU| exact WM| cbn; apply P_dtls; clear; lia]|].
    split; [eapply cells_frame; [exact C6| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac| pose proof ATPv_img as TI; clear -TI; lia]]|].
    split; [eapply cells_frame; [exact C7| exact MU| exact WM| cbn; apply P_img; [clear; lia| clear; lia| aci_clear_tac| pose proof ATPv_img as TI; clear -TI; lia]]|].
    eapply dc_at_any2; [exact C8| exact WM| (nd_pre G7 3%nat; intros _ G7i _; nd_post); unfold iclr, AIMG_LO, AIMG_HI in G7i; clear -G7i; lia]. }   (* [comment removed for export] *)
  split. { exists h0, h1, h2, hs. eapply cells_frame; [exact HS| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]. }
  split; [eapply cells_frame; [exact LOG| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]|].
  split; [eapply cells_frame; [exact NGC| exact MU| exact WM| cbn; eapply disjoint_from_sub; [exact DF| clear; lia| clear; lia| clear; lia]]|].
  split; [eapply dc_at_any; [exact DC1| exact WM| clear -G2a; lia]|].
  split. { eapply dc_at_any; [exact DC2| exact WM|]. rewrite shad_div. unfold ASHOFF. clear -G2a G2b. Z.div_mod_to_equations; lia. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    rewrite (munch_outside_range W' m m' (al_fake L) 36864) in Hb; [eapply FL; eauto| exact MU| exact DF| clear -FR; lia| clear -FR G2a G2c G3; lia].
  - intros c F n Hin. (nd_pre (LV c F n Hin) 6%nat; intros Hc Hn pos Hp HF Hb; nd_post). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp) as FR.
    rewrite (munch_outside_range W' m m' (al_fake L) 36864); [exact Hb| exact MU| exact DF| clear -FR; lia| clear -FR G2a G2c G3; lia].
Qed.

(* [comment removed for export] *)
#[using="CI CI_B LB m W Wx ALO AR BL HFK MU0 WM CW WX LS W' MU"] Theorem AREP_client : AREP AHI L st X m'.
Proof.
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post). pose proof (ao_space L ALO) as RSP. pose proof (ao_res L ALO) as ORS.
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS. pose proof (ao_ptr L ALO) as OP.
  pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  unfold aobj in ORS, OT, OC, ON, OS, OP.
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  assert (Kt : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 4096 -> disjoint_from W' A k) by (intros A k H1 Hk H2; apply P_rt; [exact Hk| clear -H1 H2; lia]).
  assert (Kctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k) by (intros A k H1 Hk H2; apply P_rt; [exact Hk| clear -H1 H2; lia]).
  Local Ltac kimg := apply P_img; [clear; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia| clear; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia| aci_clear_tac
                                   | pose proof ATPv_img as TI; clear -TI; unfold AIMG_HI, AINSTANCE, ATP88, ATSD, ARELRO_LO, ARELRO_HI; lia].
  split; [exact WF|].
  split.
  { pose proof RT as RT0. unfold arep_rt, ATP88, ATSD in RT0 |- *.
    (nd_pre RT0 28%nat; intros R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23 R24 R25 R26 R27 R28; nd_post).
    (* the TLS cell at ATPv + 16: framed when nothing writes it, otherwise given by LS *)
    assert (R26' : rw_cells asegs m' (ATPv + 16) [C4 (Z_to_bv 64 0)]).
    { destruct LS as [E|LS']; [| exact LS'].
      eapply cells_frame; [exact R26 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]].
      apply P_tls; [clear; lia | clear; lia | right; exact E]. }
    repeat lazymatch goal with |- _ /\ _ => split end;
      first [ exact R26'
            | lazymatch goal with |- rw_cells asegs m' ?A ?cs =>
                lazymatch goal with H : rw_cells asegs m A cs |- _ =>
                  eapply cells_frame; [exact H | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
                    first [kimg | apply Kctx; clear; lia | apply P_tls; [clear; lia | clear; lia | left; clear; lia]]] end end ]. }
  split. { eapply ainstance_frame; [exact MU | exact WM | exact INST | reflexivity | reflexivity | | |]; kimg. }
  split.
  { (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS [sj [STATS LSJ]] UNW; nd_post). unfold athread.
    split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
    split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | reflexivity | reflexivity | reflexivity |].
             unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
    split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
    split; [exists sj; split; [eapply u64arr_frame; [exact STATS | exact MU | exact WM | replace (8 * Z.of_nat (length sj)) with 368 by (rewrite LSJ; reflexivity); apply Kt; clear; lia] | exact LSJ]|].
    eapply cells_frame; [exact UNW | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]. }
  split.
  { intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR [SLOTS SUND] SHADOW; nd_post).
    (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | reflexivity | reflexivity | reflexivity | reflexivity |].
      apply P_rt; [clear; lia|]. do 5 right. left. unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE, K_SPACE_EXTRA; change (2^37) with 137438953472; clear -Hc; lia.
    - eapply afreearray_frame; [exact MU | exact WM | exact FARR | reflexivity | reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + apply (P_reg_hi c); [exact HcK| clear -Q5 Q6; lia| unfold afreearr, K_FREEARR_OFF in *; clear -Q1 Q2; lia| unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *; clear -Q6; lia].
      + apply P_sh_res; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
        rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
        unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
    - split; [intros k Hk; apply (aslot_client c k HcK Hk); exact (SLOTS k Hk)|].
      eapply junk_frame; [exact SUND | exact MU | exact WM |]. intros POS. apply (P_reg_hi c); [exact HcK| clear -POS; lia| clear; lia| unfold K_FREEARR_OFF, K_REGION in *; clear -Q1 Q2; lia].
    - eapply (aslot_shadow_update L W' m m' MU WM st st X X c (-1)); [exact SHADOW | reflexivity | reflexivity | reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
      + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c k SAL HcK) as AL.
        split; [reflexivity|]. apply P_sh_res; [apply shad_mono; clear -P5 RI1; lia | apply shlen_nonneg; clear -QS; lia |].
        rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
      + intros POS. apply P_sh_res; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
        rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
        apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
  split.
  { (* [comment removed for export] *)
    eapply (hq_frame _ AHI_laws L st st X X m m' W'); [exact HQ | exact MU | exact WM | |].
    - unfold quar_untouched. apply Forall_forall. intros iv Hin.
      assert (D1 : disjoint_from W' (al_t L + 80) 128) by (apply Kt; clear; lia).
      assert (D2 : disjoint_from W' (AINSTANCE + 728) 256) by kimg.
      assert (D3 : disjoint_from W' 0xafc00 0x81030) by kimg.
      assert (D4 : disjoint_from W' 0x13e488 4) by kimg.
      pose proof (disjoint_from_In _ _ _ _ D1 Hin) as E1. pose proof (disjoint_from_In _ _ _ _ D2 Hin) as E2.
      pose proof (disjoint_from_In _ _ _ _ D3 Hin) as E3. pose proof (disjoint_from_In _ _ _ _ D4 Hin) as E4.
      split; [clear -E1; lia|]. split; [clear -E2; lia|]. split; [clear -E3; lia|]. split; [clear -E4; lia|].
      intros b Hb. destruct (xb_st b) as [q| |] eqn:Sb; [exact I| |].
      all: destruct (BUSY b Hb) as [CLB _]; pose proof CLB as CLBK; unfold K_NUM_CLASSES in CLB;
           (nd_pre (PERC (xb_class b) CLBK) 12%nat; intros B1' B2' _ _ _ _ _ _ _ _ _ BR; nd_post);
           pose proof (size_of_class_facts (xb_class b) CLBK) as [BS _];
           assert (KB : 0 <= xb_slot b < ndist st (xb_class b)) by
             (apply BR; apply in_app_iff; right; apply in_app_iff; right; unfold busy_slots; apply in_map_iff; exists b; split; [reflexivity|];
              apply filter_In; split; [exact Hb| apply Z.eqb_refl]);
           assert (D5 : disjoint_from W' (xb_alloc L b) (size_of_class (xb_class b)));
           [ pose proof (aslot_client) as _;
             (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -BS; lia) (proj1 B1') KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post);
             assert (RI : al_res L <= aregion L (xb_class b) /\ aregion L (xb_class b) + K_REGION <= al_res L + 137439023104) by (unfold aregion, K_REGION in *; clear -CLB RSP; nia);
             destruct RI as [RI1 RI2]; unfold K_REGION, K_FREEARR_OFF, xb_alloc in *;
             apply P_obj; [unfold tclr; pose proof (ad_tls_res L ALO) as TR; unfold adisj in TR; clear -TR P5 P4 B1' B2' RI1 RI2; lia
                          | pose proof (ad_ahm_res L ALO) as AR0; unfold adisj in AR0; rewrite (ao_ahm_eq L ALO) in AR0; unfold AAHM_SZ; clear -AR0 P5 P4 B1' B2' RI1 RI2; lia| unfold sclr; right; clear -P5 RI1 RHI; lia| unfold iclr, AIMG_HI; split; [clear -P5 RI1 RHI; lia| right; clear -P5 RI1 RHI; lia]
                          | clear -BS; lia| atop_facts; clear -P4 B1' B2' RI2 ORS; lia| apply hb_clear_fake_obj; clear -P5 P4 B1' B2' RI1 RI2; lia|];
             intros p B n Hin'; destruct (slot_vs_blocks (xb_class b) (xb_slot b) p B n CLBK KB Hin') as [(b' & EB & Sb' & _)|D]; [| clear -D; lia];
             rewrite (busy_of_of_In L st X b WF Hb) in EB; injection EB as <-; rewrite Sb in Sb'; discriminate
           | pose proof (disjoint_from_In _ _ _ _ D5 Hin) as E5; clear -E5; lia ].
    - unfold quar_same. repeat (split; [reflexivity|]). split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  split.
  { (* [comment removed for export] *)
    cbn [AHI ah_sec] in HS |- *. unfold ASEC_of in *. (pose proof HS as ndP__; nd_pre ndP__ 5%nat; intros WFS ARR INST2 PZ SHZ; nd_post).
    (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
    split; [exact WFS|]. split; [| split; [| split]].
    - (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). exists order. split; [exact PO|].
      assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL). destruct WR as [_ WRB].
      split; [| split].
      + destruct order as [|o0 order'].
        * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
        * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply P_rt; [clear; cbn; lia|]. do 4 right. left. cbn [length] in LEN |- *. clear -LEN WB WRB; lia.
      + eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply P_rt; [clear -POS; lia|]. do 4 right. left. clear -POS WB WRB; lia.
      + intros i ch Hi. (nd_pre (PER i ch Hi) 3%nat; intros lv LV2 CH; nd_post).
        assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        (nd_pre (asec_wf_all L st _ ch WFS Hin) 4%nat; intros mb ms n0 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into W1).
        exists lv. split; [exact LV2|]. eapply asec_chunk_client; [exact Hin| exact W1| exact LV2| exact CH].
    - (nd_pre INST2 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; kimg]|].
      split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; kimg]|].
      split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; kimg]|].
      split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; kimg]|].
      split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; kimg]|].
      eapply junk_frame; [exact I6| exact MU| exact WM| intros _; kimg].
    - unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
      apply P_sh_res; [apply shad_mono; clear -RSP; lia| clear -POS; lia|].
      replace (shlen K_REGION) with 536870912 by reflexivity. rewrite !shad_div. clear -RSP. Z.div_mod_to_equations. lia.
    - intros x Hx HF HC. unfold K_HIGH_MEM in Hx.
      assert (SX : 0 <= shad x < 2^64 /\ 2148239360 <= shad x /\ shad x + 1 <= shad ATOP).   (* [comment removed for export] *)
      { rewrite !shad_div. pose proof ATOP_al16 as A16. unfold ASHOFF, AIMG_HI, KLS in *. clear -Hx A16. Z.div_mod_to_equations. lia. }
      (nd_pre SX 3%nat; intros SX SX1 SX2; nd_post).
      assert (XF : x < al_fake L \/ al_fake L + 11571200 <= x).
      { unfold astartup_hulls in HF. repeat lazymatch type of HF with Forall _ (_ :: _) => apply Forall_cons_iff in HF; destruct HF as [? HF] | _ => idtac end.
        cbn [fst snd] in *. clear -H3. lia. }
      rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
      eapply (disjoint_outside W' (shad x) 1); [| clear; lia]. apply P_sh; [exact SX1| clear; lia| exact SX2|].
      pose proof (ao_fake L ALO) as OFK. unfold aobj in OFK. rewrite !shad_div. clear -XF OFK. Z.div_mod_to_equations. lia. }
  split.
  { cbn [AHI ah_depot]. eapply (adi_frame adepot_iface); [exact HD | exact MU | exact WM |].
    assert (DD : disjoint_from W' 0x1808c8 (0x5d0910 - 0x1808c8)).
    { apply P_img; [clear; lia| clear; lia| aci_clear_tac| pose proof ATPv_img as TI; clear -TI; lia]. }
    assert (DN : disjoint_from W' (al_nodes L) 1048576) by (apply P_rt; [clear; lia| clear; lia]).
    assert (DS : disjoint_from W' (al_store L) 8388608) by (apply P_rt; [clear; lia| clear; lia]).
    apply Forall_forall. intros iv Hin a Ha.
    pose proof (disjoint_from_In _ _ _ _ DD Hin) as E1. pose proof (disjoint_from_In _ _ _ _ DN Hin) as E2. pose proof (disjoint_from_In _ _ _ _ DS Hin) as E3.
    clear -E1 E2 E3 Ha. lia. }
  split; [eapply arelro_frame; [exact MU | exact HRO | kimg]|].
  split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; kimg|].
  split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
            repeat (apply Forall_cons; [cbn [fst snd]; kimg |]); apply Forall_nil].
  intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof Hc as HcK. unfold K_NUM_CLASSES in Hc.
  assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
               /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
  { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
  (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
  eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c HcK) | reflexivity | reflexivity | |].
  - intros POS. apply P_sh_res; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
  - intros POS. apply P_sh_res; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
    rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
    apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia.
Qed.
End ClientW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="CI_B"] Theorem AHI_frame : forall L RNG st LB m m' (W : list ivl),
  AHEAP_I L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                    \/ aahm_client (fst iv) (snd iv - fst iv)) W ->
  AHEAP_I L RNG st LB m'.
Proof.
  intros L RNG st LB m m' W (ALO & ARNG & [X [AR BL]] & HFK) MU WM CW. cbn [AHI ah_fake] in HFK.
  assert (MU' : munch (W ++ []) m m') by (rewrite app_nil_r; exact MU).
  pose proof (Forall_nil (fun iv : Z * Z => fst iv = ATPv + 16 /\ snd iv = ATPv + 20)) as WX.
  assert (LS : ([] : list (Z * Z)) = [] \/ rw_cells asegs m' (ATPv + 16) [C4 (Z_to_bv 64 0)]) by (left; reflexivity).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [eapply AREP_client; eauto| exact BL].
  - cbn [AHI ah_fake]. eapply afake_client; eauto.
Qed.

(* The frame with the TLS cell at ATP + 16 written as well, holding zero again in m'. *)
#[using="CI_B"] Theorem AHI_frame_lsan : forall L RNG st LB m m' (W : list ivl),
  AHEAP_I L RNG st LB m -> munch (W ++ [(ATP + 16, ATP + 20)]) m m' -> wmono asegs m m' ->
  Forall (fun iv => aclient_range CI LB (ATOP + 4096) (fst iv) (snd iv - fst iv) \/ atls_client (fst iv) (snd iv - fst iv)
                    \/ aahm_client (fst iv) (snd iv - fst iv)) W ->
  rw_cells asegs m' (ATP + 16) [C4 (Z_to_bv 64 0)] ->
  AHEAP_I L RNG st LB m'.
Proof.
  intros L RNG st LB m m' W (ALO & ARNG & [X [AR BL]] & HFK) MU WM CW LS0. cbn [AHI ah_fake] in HFK. unfold ATP in MU, LS0.
  assert (WX : Forall (fun iv : Z * Z => fst iv = ATPv + 16 /\ snd iv = ATPv + 20) [(ATPv + 16, ATPv + 20)]) by (constructor; [split; reflexivity | constructor]).
  assert (LS : [(ATPv + 16, ATPv + 20)] = [] \/ rw_cells asegs m' (ATPv + 16) [C4 (Z_to_bv 64 0)]) by (right; exact LS0).
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [eapply AREP_client; eauto| exact BL].
  - cbn [AHI ah_fake]. eapply afake_client; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="CI_B"] Theorem AHI_malloc : amalloc_stmt CI AHEAP_I.
Proof. exact (amalloc_all adepot_iface AQUAR AFAKE AH_laws poison_remap_proof CI aci_ok aci_ok2). Qed.

#[using="CI_B"] Theorem AHI_free : afree_stmt CI AHEAP_I.
Proof. exact (afree_total adepot_iface AFAKE AHI_laws CI aci_okQ aci_ok2 adepot_frameD afake_frameD). Qed.

#[using="CI_B"] Theorem AHI_free_null : afree_null_stmt CI AHEAP_I.
Proof. exact (afree_nullP adepot_iface ASEC_of AFAKE AHI_laws CI aci_okQ). Qed.

Definition AI_of : AMallocIface :=
  {| aci := CI;
     AHEAP := AHEAP_I;
     AI_aci_img := aci_img;
     AI_aci_lo := aci_lo;
     AI_rng_mono := AHI_rng_mono;
     AI_perm := AHI_perm;
     AI_frame := AHI_frame;
     AI_frame_lsan := AHI_frame_lsan;
     AI_block := AHI_block;
     AI_block_bounds := AHI_block_bounds;
     AI_blocks_disjoint := AHI_blocks_disjoint;
     AI_blocks_nodup := AHI_blocks_nodup;
     AI_hb_ids := AHI_hb_ids;
     AI_layout := AHI_layout;
     AI_relro := AHI_relro;
     AI_rtcells := AHI_rtcells;
     AI_malloc := AHI_malloc;
     AI_free := AHI_free;
     AI_free_null := AHI_free_null |}.

#[using="Type"] Lemma AI_of_E : AHEAP AI_of = AHEAP_P AHI.
Proof. reflexivity. Qed.
#[using="Type"] Lemma AI_of_aci : aci AI_of = CI.
Proof. reflexivity. Qed.
End Gen.
End CANSEC1.
End TwB.
End AInstanceF.

(* [comment removed for export] *)
Module ARealloc.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface AFake_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRead. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_front__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ACallocG__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_allC__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHolesD. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeNull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.AFreeAll OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecSlog__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ACallocG__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfnS_allC__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_kit__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADfn_arep__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AAllocFn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.ADeallocFn OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_kit__A3W.ARealloc_kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_iseg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_pre OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.ARealloc_preP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Gen.
Variable CI : list (Z * Z).
Hypothesis CI_B : ci_okb CI = true.
(* [comment removed for export] *)
#[using="CI_B"] Lemma DEALLOCFN : deallocfn_stmt CI AHEAP_I.
Proof. exact (deallocfn_total adepot_iface AFAKE AHI_laws CI (aci_okQ CI CI_B) (aci_ok2 CI CI_B) adepot_frameD afake_frameD). Qed.

(* [comment removed for export] *)
Definition CIF : list (Z * Z) := (0x13e088, 0x13e08c) :: CI.
#[using="CI_B"] Lemma cif_ok : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CIF.
Proof. apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; lia| exact (aci_ok CI CI_B)]. Qed.
#[using="CI_B"] Lemma cif_ok2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CIF.
Proof. apply Forall_cons; [cbn [fst snd]; unfold AINSTANCE; lia| exact (aci_ok2 CI CI_B)]. Qed.
#[using="CI_B"] Lemma ALLOCFN : allocfn_stmt CIF AHEAP_I.
Proof. exact (allocfn_all adepot_iface AQUAR AFAKE AH_laws poison_remap_proof CIF cif_ok cif_ok2). Qed.

#[using="Type"] Lemma aheap_pres_cif : forall LB SP m m', aheap_pres CIF LB SP m m' -> aheap_pres CI LB SP m m'.
Proof.
  intros LB SP m m' H a Ha Hc. apply H; [exact Ha|]. destruct Hc as [Hc|HT]; [left| right; exact HT].
  unfold aclient_addr, in_ranges in *. destruct Hc as [Hc|[(iv & Hiv & Hr)|[Hc|(a' & Ha' & ->)]]].
  - left; exact Hc.
  - right; left. exists iv. split; [right; exact Hiv| exact Hr].
  - right; right; left; exact Hc.
  - right; right; right. exists a'. split; [| reflexivity].
    destruct Ha' as [X|[(iv & Hiv & Hr)|X]]; [left; exact X| right; left; exists iv; split; [right; exact Hiv| exact Hr] | right; right; exact X].
Qed.


#[using="Type"] Lemma aheap_pres_u64arr : forall CIx LB SP m m' A ws,
  aheap_pres CIx LB SP m m' -> u64arr asegs m A ws -> aclient_range CIx LB SP A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
  intros CIx LB SP m m' A ws HP [Hb Hw] HR. split.
  - eapply aheap_pres_bytes_at; [exact HP | exact Hb |]. rewrite u64s_length, Nat2Z.inj_mul. exact HR.
  - eapply aheap_pres_wr_at; [exact HP | exact Hw | exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AHI_live_hdr : forall L RNG st LB m p A n,
  AHEAP_I L RNG st LB m -> In (HB p A n) LB ->
  exists b1 ctx, rw_cells asegs m (A + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
                 /\ rng RNG (A + -16) 16.
Proof.
  intros L RNG st LB m p A n AH Hin. (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  (pose proof AR as ndP__; nd_pre ndP__ 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(y & Hy & Sy & Uy & Ny & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - (nd_pre (in_split _ _ Hy) 3%nat; intros l1 l2 XB; nd_post).
    destruct y as [c k yn yst b1 ctx]. cbn [xb_class xb_slot xb_n xb_st] in *. subst yst yn.
    change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
    (nd_pre (CLS c CLB) 4%nat; intros _ _ SLOTS SHADOW; nd_post).
    pose proof (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj SLOTS SHADOW)) as (HDR & _).
    destruct (slot_rng L st X c k ALO WF CLB KB RNG ARNG) as [RSL _].
    (pose proof (chunk_geo L st X c k n ALO WF CLB KB ltac:(clear -NB; lia) FIT) as ndP__; nd_pre ndP__ 7%nat; intros _ _ ABUB ABHM _ UBS _; nd_post).
    unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy. subst A.
    exists b1, ctx. split; [replace (aslot_addr L c k + rz_size n + -16) with (aslot_addr L c k + rz_size n - 16) by (clear; lia); exact HDR|].
    eapply rng_sub'; [exact RSL|]. pose proof (rup8_facts n ltac:(clear -NB; lia)) as (RUP & _). clear -ABUB ABHM UBS RUP NB. lia.
  - cbn [AHI ah_sec] in HS.
    (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) Lp) 18%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 _; nd_post).
    cbv zeta in H5. subst A. unfold SEC_UOFF.
    exists b1, cx. split; [replace (mb + 6144 + -16) with (mb + 6128) by (clear; lia); exact H5|].
    (nd_pre (sec_wf1_facts' L mb ms n G) 13%nat; intros MAL MLO MCE MSE NBs RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
    (nd_pre ARNG 13%nat; intros _ _ _ _ _ _ _ _ _ _ _ RSECS _; nd_post).
    pose proof (proj1 (Forall_forall _ _) RSECS _ INC) as RCH. cbn in RCH.
    eapply rng_sub'; [exact (proj1 RCH)|]. clear -MSB NMS N6 NBs. lia.
Qed.

Definition AHI_realloc__stmt : Prop := arealloc_stmt CI AHEAP_I.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 39).
Variable nold : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 42).
Variable bs : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 43).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 44).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 45).
Let spA := bv_unsigned sp + -2208.
Let SO := bv_unsigned sp + -2136.
Let mn := Z.min nold n.
#[using="CI_B spA SO mn"] Lemma AHI_realloc__body : ltac:(let T := type of (fun (h : AHI_realloc__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A nold n lo bs tr RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (nold, (n, (lo, (bs, (tr, RESV)))))))))))))))))))))))))))))))))))))))))))))) as _.
  unfold arealloc_stmt. 
  intros AH HIN SRC MI ST BOT LO TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK ROK. unfold AREALLOC_STACK in LO.
  (nd_pre (AHI_block L RNG st LB m p A nold AH HIN) 8%nat; intros NOLD BRo RBo RSo SHo WRo (ch & LIVE & CSZ & _) _; nd_post).
  unfold arealloc. rewrite LIVE.
  (* [comment removed for export] *)
  (nd_pre (arealloc_preP adepot_iface ASEC_of AFAKE AHI_laws CI (aci_okQ CI CI_B) L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m st LB p A nold n lo tr AH HIN MI ST BOT LO TP Ha0 Ha1 ltac:(unfold AREQMAX in NR; clear -NR; lia) AUNW S0NE RA4 RANE SP16 RSTK) 5%nat; intros trc TRU LTRC SP47 PRE; nd_post).
  eapply implF_evtF; [exact PRE|]. clear PRE.
  intros ms1 (P1 & AH1 & PRES1). unfold realloc_pre_post in P1.
  (nd_pre P1 15%nat; intros t0a t1a t2a a7a t3a t4a t5a t6a fr0 junk0 junk2 tb sj1 m1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU1 WM1 MI1 ST1 FR48 FR16 FRP SS TB LTB TRF FRS UNW1 STATS1 LSJ1 FL1 IAS1 IAM1; nd_post).
  cbn [ms_mem] in AH1, PRES1.
  word_range sp SPR.
  pose proof (AHI_layout L RNG st LB m AH) as LAY0.
  assert (SPB : ATOP + 4096 + 8192 <= bv_unsigned sp) by (clear -BOT LO; lia).
  atop_facts.
  chg (bv_unsigned sp + -2208) spA.
  assert (EspA : bv_unsigned (Z_to_bv 64 spA) = spA) by (apply unsigned_lit; subst spA; clear -SPB SPR H; lia).
  chg (bv_unsigned sp + -2136) SO.
  (* [comment removed for export] *)
  pose proof SS as SS8. rw_split SS8 1%nat SSp SSz.
  apply rw_cells_C4C4_to_C8 in SSz. 2: { clear -LTRC; lia. }
  rw_join SSp SSz SSA.
  replace (bv_unsigned sp + -2136 + 16) with (SO + 16) in SSA, TB by (subst SO; clear; lia).
  (* [comment removed for export] *)
  eapply implS_sbind.
  { eapply (ALLOCFN L RNG (Z_to_bv 64 0x34788) (Z_to_bv 64 spA) gp tp t0a t1a t2a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 t3a t4a t5a t6a
              F fc m1 st LB n lo SO AREALLOC_PC' trc tb RESV AH1 MI1).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite EspA; exact ST1
         | |- @eq word _ _ => first [exact TP | reflexivity]
         | |- rw_cells _ _ _ _ => exact SSA
         | |- u64arr _ _ _ _ => exact TB
         | |- @eq nat _ _ => exact LTB
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- (_ <= _)%nat => exact LTRC
         | |- aresv_ok _ _ => exact ROK
         | |- rng _ _ _ => rewrite ?EspA; eapply rng_sub'; [exact RSTK|]; subst spA SO; clear -SPB LO BOT SPR; lia
         | |- _ => rewrite ?EspA; subst spA SO; unfold AMALLOC_STACK; clear -SPB LO BOT SPR SP47 NR H; lia
         end. }
  intros [st2 [q|]] RNG2 ms2 POST2; unfold amalloc_post in POST2; cbn [fst snd] in POST2.
  2: { (nd_pre POST2 22%nat; intros _ t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 _ _ _ _ []; nd_post). }
  (nd_pre POST2 18%nat; intros FPLE2 t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MI2 ST2 PRES2 NEW junk ndR3__; nd_post; destruct ndR3__ as (-> & ndR4__); nd_pre ndR4__ 6%nat; intros BRn AH2 UJ RNn RSn _; nd_post).
  rewrite EspA in ST2, PRES2.
  cbn [snd fst].
  replace (ret_pc (Z_to_bv 64 0x34788)) with (Z_to_bv 64 0x34788) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  assert (HIN2 : In (HB p A nold) (HB q NEW n :: LB)) by (right; exact HIN).
  (nd_pre (AHI_live_hdr L RNG2 st2 _ m2 p A nold AH2 HIN2) 4%nat; intros b1 hctx HDR RHD; nd_post).
  assert (SRC1 : rw_cells asegs m1 A [CB (Z.to_nat nold) bs]).
  { eapply (aheap_pres_rw_cells CI); [exact PRES1 | exact SRC |]. right. left. exists (HB p A nold). split; [exact HIN|].
    cbn [ab_addr ab_size cells_size csize]. clear -NOLD. lia. }
  assert (SRC2 : rw_cells asegs m2 A [CB (Z.to_nat nold) bs]).
  { eapply (aheap_pres_rw_cells CIF); [exact PRES2 | exact SRC1 |]. right. left. exists (HB p A nold). split; [exact HIN|].
    cbn [ab_addr ab_size cells_size csize]. clear -NOLD. lia. }
  assert (LBS : length bs = Z.to_nat nold) by (destruct SRC as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
  assert (LUJ : length junk = Z.to_nat n) by (destruct UJ as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
  (pose proof AH2 as ndP__; nd_pre ndP__ 4%nat; intros ALO2 ARNG2 [X2 [AR2 BL2]] HFK2; nd_post).
  (pose proof (AREP_poison_cells adepot_iface AQUAR ASEC_of L st2 X2 m2 ltac:(rewrite <- AHI_eq; exact AR2)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ REAL2 _; nd_post).
  pose proof (relro_word m2 0xa54d8 0xa7358 (AHI_relro L RNG2 st2 _ m2 AH2) ltac:(unfold ARELRO_LO; clear; lia) ltac:(unfold ARELRO_HI; clear; lia) ltac:(vm_compute; reflexivity)) as GOTM.
  assert (PQ : p <> q).
  { pose proof (AHI_hb_ids L RNG2 st2 _ m2 AH2) as ND. cbn [hb_ids flat_map ab_kind app] in ND. inversion ND as [|x l NI _]; subst.
    intros ->. apply NI. clear -HIN. induction LB as [|b LB' IH]; [destruct HIN|]. cbn [hb_ids flat_map]. apply in_or_app.
    destruct HIN as [->|HIN]; [left; cbn; left; reflexivity| right; apply IH; exact HIN]. }
  assert (SEP : A + nold <= NEW \/ NEW + n <= A).
  { pose proof (AHI_blocks_disjoint L RNG2 st2 _ m2 (HB p A nold) (HB q NEW n) AH2 HIN2 ltac:(left; reflexivity) ltac:(intros E; injection E; intros; apply PQ; assumption)) as D.
    cbn [ab_addr ab_size] in D. exact D. }
  (nd_pre BRn 4%nat; intros NBLK NN0 NHI N16; nd_post). (nd_pre BRo 4%nat; intros OBLK ON0 OHI O16; nd_post).
  pose proof (ablk_lin _ _ NBLK) as (NL1 & _). pose proof (ablk_lin _ _ OBLK) as (OL1 & _). unfold AIMG_HI in NL1, OL1.
  (pose proof ARNG2 as ndP__; nd_pre ndP__ 14%nat; intros RIMG2 _ _ _ _ _ _ _ _ _ _ _ _ RTLS2; nd_post).
  (* [comment removed for export] *)
  eapply implF_evtF.
  { eapply (ricptC_spec RNG2 (Z_to_bv 64 spA) gp tp t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b _ _ _ s7 s8 s9 s10 s11 t3b t4b t5b t6b
              F fc m2 A NEW n nold SO b1 hctx bs junk MI2).
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _] => exact GOTM
         | |- rw_cells _ _ _ [C8 _; C8 _] => exact REAL2
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ _ [CB _ _] => first [exact SRC2 | exact UJ]
         | |- @eq nat _ _ => first [exact LBS | exact LUJ]
         | |- _ \/ _ => exact SEP
         | |- rng_aimg _ => exact RIMG2
         | |- rng_atls _ => exact RTLS2
         | |- rng _ _ _ => first [exact RHD | exact RNn | eapply rng_fp_le; [exact FPLE2 | exact RBo]]
         | |- _ => subst SO; unfold AREQMAX in *; clear -NR NOLD NL1 OL1 NHI OHI NN0 ON0 H SPR SPB; lia
         end. }
  intros ms3 P3. unfold ricptC_post in P3. cbv zeta in P3.
  (nd_pre P3 11%nat; intros t0c t1c t2c a6c a7c t3c t4c t5c t6c m3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MU3 WM3 MI3 NEWC; nd_post).
  chg (Z.min nold n) mn.
  assert (MN : 1 <= mn /\ mn <= nold /\ mn <= n) by (subst mn; clear -NR NOLD; lia).
  (* [comment removed for export] *)
  assert (AH3 : AHEAP_I L RNG2 st2 (HB q NEW n :: LB) m3).
  { eapply (AHI_frame CI CI_B L RNG2 st2 _ m2 m3 [(NEW, NEW + mn)]%Z AH2 MU3 WM3).
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. left. right. left. exists (HB q NEW n). split; [left; reflexivity|].
    cbn [ab_addr ab_size]. clear -MN. lia. }
  (* [comment removed for export] *)
  assert (SPA : spA = bv_unsigned sp + -2208) by reflexivity. assert (SOE : SO = bv_unsigned sp + -2136) by reflexivity.
  assert (KST : forall B k, spA <= B -> aclient_range CIF LB spA B k) by (intros B k HB; left; left; exact HB).
  assert (KMU : forall B k, ATOP <= B -> 0 <= k -> disjoint_from [(NEW, NEW + mn)]%Z B k) by (intros B k HB Hk; cbn [disjoint_from]; split; [clear -HB Hk NHI MN; lia| exact I]).
  assert (XS : forall B cs, spA <= B -> rw_cells asegs m1 B cs -> rw_cells asegs m3 B cs).
  { intros B cs HB HC. eapply (rw_cells_transport asegs _ m2 m3); [| exact MU3 | exact WM3 | apply KMU; [clear -HB SPA SPB; lia| apply Nat2Z.is_nonneg]].
    eapply (aheap_pres_rw_cells CIF); [exact PRES2 | exact HC | apply KST; exact HB]. }
  pose proof (XS (bv_unsigned sp + -2208) _ ltac:(clear -SPA; lia) FR48) as FR48c. pose proof (XS (bv_unsigned sp + -2160) _ ltac:(clear -SPA; lia) FR16) as FR16c.
  pose proof (XS (bv_unsigned sp + -2144) _ ltac:(clear -SPA; lia) FRP) as FRPc. pose proof (XS (bv_unsigned sp + -2136) _ ltac:(clear -SPA; lia) SS) as SSc.
  pose proof (XS (bv_unsigned sp + -80) _ ltac:(clear -SPA; lia) FRS) as FRSc.
  assert (TBc : u64arr asegs m3 (SO + 16) tb).
  { eapply (u64arr_transport asegs _ m2 m3); [| exact MU3 | exact WM3 | apply KMU; [clear -SOE SPB; lia| clear; lia]].
    eapply (aheap_pres_u64arr CIF); [exact PRES2 | exact TB | apply KST; clear -SPA SOE; lia]. }
  assert (FLc : rw_cells asegs m3 0x13e088 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { eapply (rw_cells_transport asegs _ m2 m3); [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; split; [clear -NL1; lia| exact I]].
    eapply (aheap_pres_rw_cells CIF); [exact PRES2 | exact FL1 |]. left. right. left. exists (0x13e088, 0x13e08c). split; [left; reflexivity|].
    cbn [fst snd cells_size csize Nat.add]. clear. lia. }
  assert (ST3 : stk asegs m3 lo spA).
  { eapply stk_transport_disjoint; [exact ST2 | exact MU3 | exact WM3 |]. cbn [disjoint_from]. split; [clear -BOT NHI MN; lia| exact I]. }
  (* [comment removed for export] *)
  eapply implS_sbind.
  { eapply (DEALLOCFN L RNG2 (Z_to_bv 64 0x3481c) (Z_to_bv 64 spA) gp tp t0c t1c t2c _ _ _ _ _ _ _ _ a6c a7c _ _ _ _ _ s7 s8 s9 s10 s11 t3c t4c t5c t6c
              F fc m3 st2 _ p A nold lo SO AREALLOC_PC' trc tb AH3 HIN2 MI3).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite EspA; exact ST3
         | |- @eq word _ _ => first [exact TP | reflexivity]
         | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact FLc
         | |- 4096 <= bv_unsigned (Z_to_bv 64 _) => rewrite unsigned_lit by (clear; lia); clear; lia
         | |- rw_cells _ _ _ _ => replace (SO + 16) with (bv_unsigned sp + -2136 + 16) by (subst SO; clear; lia); exact SSc
         | |- u64arr _ _ _ _ => exact TBc
         | |- @eq nat _ _ => exact LTB
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- (_ <= _)%nat => exact LTRC
         | |- rng _ _ _ => rewrite ?EspA; eapply rng_fp_le; [exact FPLE2|]; eapply rng_sub'; [exact RSTK|]; subst spA SO; clear -SPB LO BOT SPR; lia
         | |- _ => rewrite ?EspA; subst spA SO; unfold AFREE_STACK; clear -SPB LO BOT SPR SP47 H; lia
         end. }
  intros st3 RNG3 ms4 POST4. unfold afree_post in POST4.
  (nd_pre POST4 18%nat; intros FPLE4 t0d t1d t2d a0d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MI4 ST4 PRES4 AH4; nd_post).
  rewrite EspA in ST4, PRES4. rewrite (lb_remove_cons_other p q NEW n LB ltac:(intros E; apply PQ; symmetry; exact E)) in PRES4, AH4.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x3481c)) with (Z_to_bv 64 0x3481c) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  assert (KS4 : forall B k, spA <= B -> aclient_range CI (HB q NEW n :: lb_remove p LB) spA B k) by (intros B k HB; left; left; exact HB).
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 FR48c (KS4 (bv_unsigned sp + -2208) _ ltac:(clear -SPA; lia))) as FR48d.
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 FR16c (KS4 (bv_unsigned sp + -2160) _ ltac:(clear -SPA; lia))) as FR16d.
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 FRPc (KS4 (bv_unsigned sp + -2144) _ ltac:(clear -SPA; lia))) as FRPd.
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 SSc (KS4 (bv_unsigned sp + -2136) _ ltac:(clear -SPA; lia))) as SSd.
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 FRSc (KS4 (bv_unsigned sp + -80) _ ltac:(clear -SPA; lia))) as FRSd.
  pose proof (aheap_pres_u64arr CI _ _ _ _ _ _ PRES4 TBc (KS4 (SO + 16) _ ltac:(clear -SPA SOE; lia))) as TBd.
  apply rw_cells_of_u64arr in TBd. rewrite LTB in TBd.
  assert (NEWD : rw_cells asegs m4 NEW [CB (Z.to_nat n) (firstn (Z.to_nat mn) bs ++ skipn (Z.to_nat mn) junk)]).
  { eapply (aheap_pres_rw_cells CI); [exact PRES4 | exact NEWC |]. right. left. exists (HB q NEW n). split; [left; reflexivity|].
    cbn [ab_addr ab_size cells_size csize]. clear -NR. lia. }
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (ricptD_spec RNG3 sp gp tp t0d t1d t2d _ _ a0d a1d a2d a3d a4d a5d a6d a7d _ _ _ _ s7 s8 s9 s10 s11 t3d t4d t5d t6d
              ra s0 s1 s2 s3 s4 s5 s6 _ _ _ _ _ sp F fc m4 NEW lo fr0 junk2).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST4
         | |- mem_inv _ _ => exact MI4
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] => exact FR48d
         | |- rw_cells _ _ _ [CB _ _; C8 _] => exact FR16d
         | |- rw_cells _ _ _ [C8 _; CB _ _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] => exact FRSd
         | |- exists csP, rw_cells _ _ (_ + -2144) _ /\ _ => eexists; split; [exact FRPd| reflexivity]
         | |- exists csA, rw_cells _ _ (_ + -2136) _ /\ _ => eexists; split; [exact SSd| reflexivity]
         | |- exists csT, rw_cells _ _ (_ + -2120) _ /\ _ => eexists; split; [replace (bv_unsigned sp + -2120) with (SO + 16) by (subst SO; clear; lia); exact TBd| reflexivity]
         | |- rng_aimg _ => eapply rng_fp_le; [exact FPLE4| exact RIMG2]
         | |- rng_atls _ => eapply rng_fp_le; [exact FPLE4| exact RTLS2]
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE4|]; eapply rng_fp_le; [exact FPLE2| exact RSTK]
         | |- _ => clear -SPB LO BOT NL1 NHI NN0 H; lia
         end. }
  cbv beta. intros ms5 (a0e & -> & _ & ST5).
  (* [comment removed for export] *)
  assert (INCL : forall b, In b (lb_remove p LB) -> In b LB) by (intros b Hb; exact (proj1 (proj1 (In_lb_remove p LB b) Hb))).
  assert (QFRESH : ~ In (HB q NEW n) LB).
  { pose proof (AHI_blocks_nodup L RNG2 st2 _ m2 AH2) as ND. inversion ND; assumption. }
  unfold arealloc_post. cbn [snd fst].
  split; [eapply fp_le_trans; [exact FPLE2| exact FPLE4]|].
  do 15 eexists. exists m4. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST5|].
  split.
  { eapply aheap_pres_trans; [eapply (aheap_pres_weaken CI LB); [exact PRES1 | apply Z.le_refl | exact INCL]|].
    eapply aheap_pres_trans; [eapply (aheap_pres_weaken CI LB); [exact (aheap_pres_cif _ _ _ _ PRES2) | clear -SPA; lia | exact INCL]|].
    eapply aheap_pres_trans; [| eapply (aheap_pres_weaken CI (HB q NEW n :: lb_remove p LB)); [exact PRES4 | clear -SPA; lia | intros b Hb; right; exact Hb]].
    (* [comment removed for export] *)
    eapply (aheap_pres_of_munch CI _ _ [(NEW, NEW + mn)]%Z); [exact MU3 | exact WM3 | |].
    - intros a Ha CL. cbn [outside]. split; [| exact I].
      destruct CL as [SK | [(iv & Hiv & R) | [(b & Hb & R) | (a' & Ha' & ->)]]].
      + clear -SK SPB NHI MN. lia.
      + pose proof (aci_img CI CI_B iv Hiv) as IMG. unfold AIMG_HI in IMG. clear -R IMG NL1. lia.
      + assert (Hb2 : In b (HB q NEW n :: LB)) by (right; apply INCL; exact Hb).
        assert (NEb : b <> HB q NEW n) by (intros ->; apply QFRESH; apply INCL; exact Hb).
        pose proof (AHI_blocks_disjoint L RNG2 st2 _ m2 b (HB q NEW n) AH2 Hb2 ltac:(left; reflexivity) NEb) as D. cbn [ab_addr ab_size] in D.
        clear -R D MN. lia.
      + assert (A47 : 0 <= a' < 2^47).
        { destruct Ha' as [SK | [(iv & Hiv & R) | (cls & FA & sz & Hin & R)]].
          - clear -SK H. lia.
          - pose proof (aci_img CI CI_B iv Hiv) as IMG. pose proof (aci_lo CI CI_B iv Hiv) as ILO. unfold AIMG_HI in IMG. clear -R IMG ILO. lia.
          - (pose proof (AHI_block_bounds L RNG2 st2 _ m2 (mkABlock (ABFake cls) FA sz) AH2 ltac:(right; apply INCL; exact Hin)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
            cbn [ab_addr ab_size] in K1, K2, K3. unfold AIMG_HI in K1. clear -R K1 K3 H. lia. }
        rewrite shad_div. unfold ASHOFF. unfold ablk, KLS, AIMG_HI in NBLK. clear -A47 NBLK MN. Z.div_mod_to_equations. lia.
    - intros a Ha XT. cbn [outside]. split; [| exact I].
      pose proof (AHI_block_tls L RNG2 st2 _ m2 (HB q NEW n) AH2 ltac:(left; reflexivity)) as DT. cbn [ab_addr ab_size] in DT.
      pose proof (AHI_block_ahm L RNG2 st2 _ m2 (HB q NEW n) AH2 ltac:(left; reflexivity)) as DA. cbn [ab_addr ab_size] in DA.
      destruct XT as [[T|(ta & Hta & ->)]|[IM|IM]].
      + clear -T DT MN. lia.
      + pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
        assert (SA : shad ATOP <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -H; Z.div_mod_to_equations; lia).
        unfold ablk, KLS, AIMG_HI in NBLK. clear -TS1 TS2 SA NBLK MN. lia.
      + unfold AIMSH_LO, AIMSH_LEN in IM. unfold ablk, KLS, AIMG_HI in NBLK. clear -IM NBLK MN. lia.
      + unfold AAHM_SZ in *. clear -IM DA MN. lia. }
  exists NEW, (skipn (Z.to_nat mn) junk).
  split; [reflexivity|]. split; [unfold ablock_range; repeat split; assumption|]. split; [exact AH4|].
  split; [rewrite length_skipn, LUJ; clear -MN; lia|]. split; [exact NEWD|].
  split; eapply rng_fp_le; try exact FPLE4; assumption.
Qed.
End Zd1.
#[using="CI_B"] Theorem AHI_realloc : ltac:(let t := eval cbv delta [AHI_realloc__stmt] in AHI_realloc__stmt in exact t).
Proof. exact AHI_realloc__body. Qed.
End Gen.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.AFreeGeo.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRead.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_front__A3W.F_afree_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_arep__A3W.F_afree_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.AFreeNull.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AMalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.AFreeAll.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASF_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHolesD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecSlog__A3W.AFn_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.AAllocFn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfnS_allC__A3W.ADeallocFn.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_kit__A3W.ARealloc_kit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_iseg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_arealloc_pre.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADfn_arep__A3W.ARealloc_preP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Gen.
Variable CI : list (Z * Z).
Hypothesis CI_B : ci_okb CI = true.
(* [comment removed for export] *)
#[using="CI_B"] Lemma DEALLOCFN : deallocfn_stmt CI AHEAP_I.
Proof. exact (deallocfn_total adepot_iface AFAKE AHI_laws CI (aci_okQ CI CI_B) (aci_ok2 CI CI_B) adepot_frameD afake_frameD). Qed.

(* [comment removed for export] *)
Definition CIF : list (Z * Z) := (0x13e488, 0x13e48c) :: CI.
#[using="CI_B"] Lemma cif_ok : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CIF.
Proof. apply Forall_cons; [cbn [fst snd]; unfold AIMG_HI; lia| exact (aci_ok CI CI_B)]. Qed.
#[using="CI_B"] Lemma cif_ok2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CIF.
Proof. apply Forall_cons; [cbn [fst snd]; unfold AINSTANCE; lia| exact (aci_ok2 CI CI_B)]. Qed.
#[using="CI_B"] Lemma ALLOCFN : allocfn_stmt CIF AHEAP_I.
Proof. exact (allocfn_all adepot_iface AQUAR AFAKE AH_laws poison_remap_proof CIF cif_ok cif_ok2). Qed.

#[using="Type"] Lemma aheap_pres_cif : forall LB SP m m', aheap_pres CIF LB SP m m' -> aheap_pres CI LB SP m m'.
Proof.
  intros LB SP m m' H a Ha Hc. apply H; [exact Ha|]. destruct Hc as [Hc|HT]; [left| right; exact HT].
  unfold aclient_addr, in_ranges in *. destruct Hc as [Hc|[(iv & Hiv & Hr)|[Hc|(a' & Ha' & ->)]]].
  - left; exact Hc.
  - right; left. exists iv. split; [right; exact Hiv| exact Hr].
  - right; right; left; exact Hc.
  - right; right; right. exists a'. split; [| reflexivity].
    destruct Ha' as [X|[(iv & Hiv & Hr)|X]]; [left; exact X| right; left; exists iv; split; [right; exact Hiv| exact Hr] | right; right; exact X].
Qed.


#[using="Type"] Lemma aheap_pres_u64arr : forall CIx LB SP m m' A ws,
  aheap_pres CIx LB SP m m' -> u64arr asegs m A ws -> aclient_range CIx LB SP A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
  intros CIx LB SP m m' A ws HP [Hb Hw] HR. split.
  - eapply aheap_pres_bytes_at; [exact HP | exact Hb |]. rewrite u64s_length, Nat2Z.inj_mul. exact HR.
  - eapply aheap_pres_wr_at; [exact HP | exact Hw | exact HR].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma AHI_live_hdr : forall L RNG st LB m p A n,
  AHEAP_I L RNG st LB m -> In (HB p A n) LB ->
  exists b1 ctx, rw_cells asegs m (A + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
                 /\ rng RNG (A + -16) 16.
Proof.
  intros L RNG st LB m p A n AH Hin. (pose proof AH as ndP__; nd_pre ndP__ 4%nat; intros ALO ARNG [X [AR BL]] HFK; nd_post).
  (pose proof AR as ndP__; nd_pre ndP__ 12%nat; intros WF RT INST THR CLS HQ HS HD HRO HRT2 AVL RT3; nd_post).
  destruct (hb_cases L st X LB m p A n ALO AR BL Hin) as [(y & Hy & Sy & Uy & Ny & CLB & NB & FIT & LV & PRIM & KB & P5 & P4 & R1 & R2)|(mb & ms & Lp & EA & G & PRIM & INC)].
  - (nd_pre (in_split _ _ Hy) 3%nat; intros l1 l2 XB; nd_post).
    destruct y as [c k yn yst b1 ctx]. cbn [xb_class xb_slot xb_n xb_st] in *. subst yst yn.
    change ({| xb_class := c; xb_slot := k; xb_n := n; xb_st := BLive p; xb_b1 := b1; xb_ctx := ctx |}) with (bfreed p c k n b1 ctx) in XB.
    (nd_pre (CLS c CLB) 4%nat; intros _ _ SLOTS SHADOW; nd_post).
    pose proof (read_chunk L st X m p c k n b1 ctx l1 l2 ALO WF XB (conj SLOTS SHADOW)) as (HDR & _).
    destruct (slot_rng L st X c k ALO WF CLB KB RNG ARNG) as [RSL _].
    (pose proof (chunk_geo L st X c k n ALO WF CLB KB ltac:(clear -NB; lia) FIT) as ndP__; nd_pre ndP__ 7%nat; intros _ _ ABUB ABHM _ UBS _; nd_post).
    unfold xb_user, xb_alloc in Uy. cbn [xb_class xb_slot xb_n] in Uy. subst A.
    exists b1, ctx. split; [replace (aslot_addr L c k + rz_size n + -16) with (aslot_addr L c k + rz_size n - 16) by (clear; lia); exact HDR|].
    eapply rng_sub'; [exact RSL|]. pose proof (rup8_facts n ltac:(clear -NB; lia)) as (RUP & _). clear -ABUB ABHM UBS RUP NB. lia.
  - cbn [AHI ah_sec] in HS.
    (nd_pre (read_chunk_sec _ L st X m p mb ms n HS (Permutation_refl _) Lp) 18%nat; intros order i b1 cx uw PO NTH IL LENO WF1o WDo U64 JK PER CH H1 H5 _; nd_post).
    cbv zeta in H5. subst A. unfold SEC_UOFF.
    exists b1, cx. split; [replace (mb + 6144 + -16) with (mb + 6128) by (clear; lia); exact H5|].
    (nd_pre (sec_wf1_facts' L mb ms n G) 13%nat; intros MAL MLO MCE MSE NBs RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
    (nd_pre ARNG 13%nat; intros _ _ _ _ _ _ _ _ _ _ _ RSECS _; nd_post).
    pose proof (proj1 (Forall_forall _ _) RSECS _ INC) as RCH. cbn in RCH.
    eapply rng_sub'; [exact (proj1 RCH)|]. clear -MSB NMS N6 NBs. lia.
Qed.

Definition AHI_realloc__stmt : Prop := arealloc_stmt CI AHEAP_I.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 5).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 6).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 7).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 8).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 9).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 10).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 11).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 12).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 13).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 14).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 15).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 16).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 17).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 18).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 19).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 20).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 21).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 22).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 23).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 24).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 25).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 26).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 27).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 28).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 29).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 30).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 31).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 32).
Variable F : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 33).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 34).
Variable m : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 35).
Variable st : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 36).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 37).
Variable p : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 38).
Variable A : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 39).
Variable nold : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 41).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 42).
Variable bs : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 43).
Variable tr : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 44).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'AHI_realloc__stmt 45).
Let spA := bv_unsigned sp + -2208.
Let SO := bv_unsigned sp + -2136.
Let mn := Z.min nold n.
#[using="CI_B spA SO mn"] Lemma AHI_realloc__body : ltac:(let T := type of (fun (h : AHI_realloc__stmt) => h L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A nold n lo bs tr RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (st, (LB, (p, (A, (nold, (n, (lo, (bs, (tr, RESV)))))))))))))))))))))))))))))))))))))))))))))) as _.
  unfold arealloc_stmt. 
  intros AH HIN SRC MI ST BOT LO TP Ha0 Ha1 NR AUNW S0NE RA4 RANE SP16 RSTK ROK. unfold AREALLOC_STACK in LO.
  (nd_pre (AHI_block L RNG st LB m p A nold AH HIN) 8%nat; intros NOLD BRo RBo RSo SHo WRo (ch & LIVE & CSZ & _) _; nd_post).
  unfold arealloc. rewrite LIVE.
  (* [comment removed for export] *)
  (nd_pre (arealloc_preP adepot_iface ASEC_of AFAKE AHI_laws CI (aci_okQ CI CI_B) L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
              F fc m st LB p A nold n lo tr AH HIN MI ST BOT LO TP Ha0 Ha1 ltac:(unfold AREQMAX in NR; clear -NR; lia) AUNW S0NE RA4 RANE SP16 RSTK) 5%nat; intros trc TRU LTRC SP47 PRE; nd_post).
  eapply implF_evtF; [exact PRE|]. clear PRE.
  intros ms1 (P1 & AH1 & PRES1). unfold realloc_pre_post in P1.
  (nd_pre P1 15%nat; intros t0a t1a t2a a7a t3a t4a t5a t6a fr0 junk0 junk2 tb sj1 m1 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 18%nat; intros MU1 WM1 MI1 ST1 FR48 FR16 FRP SS TB LTB TRF FRS UNW1 STATS1 LSJ1 FL1 IAS1 IAM1; nd_post).
  cbn [ms_mem] in AH1, PRES1.
  word_range sp SPR.
  pose proof (AHI_layout L RNG st LB m AH) as LAY0.
  assert (SPB : ATOP + 4096 + 8192 <= bv_unsigned sp) by (clear -BOT LO; lia).
  atop_facts.
  chg (bv_unsigned sp + -2208) spA.
  assert (EspA : bv_unsigned (Z_to_bv 64 spA) = spA) by (apply unsigned_lit; subst spA; clear -SPB SPR H; lia).
  chg (bv_unsigned sp + -2136) SO.
  (* [comment removed for export] *)
  pose proof SS as SS8. rw_split SS8 1%nat SSp SSz.
  apply rw_cells_C4C4_to_C8 in SSz. 2: { clear -LTRC; lia. }
  rw_join SSp SSz SSA.
  replace (bv_unsigned sp + -2136 + 16) with (SO + 16) in SSA, TB by (subst SO; clear; lia).
  (* [comment removed for export] *)
  eapply implS_sbind.
  { eapply (ALLOCFN L RNG (Z_to_bv 64 0x347f0) (Z_to_bv 64 spA) gp tp t0a t1a t2a _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 t3a t4a t5a t6a
              F fc m1 st LB n lo SO AREALLOC_PC' trc tb RESV AH1 MI1).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite EspA; exact ST1
         | |- @eq word _ _ => first [exact TP | reflexivity]
         | |- rw_cells _ _ _ _ => exact SSA
         | |- u64arr _ _ _ _ => exact TB
         | |- @eq nat _ _ => exact LTB
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- (_ <= _)%nat => exact LTRC
         | |- aresv_ok _ _ => exact ROK
         | |- rng _ _ _ => rewrite ?EspA; eapply rng_sub'; [exact RSTK|]; subst spA SO; clear -SPB LO BOT SPR; lia
         | |- _ => rewrite ?EspA; subst spA SO; unfold AMALLOC_STACK; clear -SPB LO BOT SPR SP47 NR H; lia
         end. }
  intros [st2 [q|]] RNG2 ms2 POST2; unfold amalloc_post in POST2; cbn [fst snd] in POST2.
  2: { (nd_pre POST2 22%nat; intros _ t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 _ _ _ _ []; nd_post). }
  (nd_pre POST2 18%nat; intros FPLE2 t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m2 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 6%nat; intros MI2 ST2 PRES2 NEW junk ndR3__; nd_post; destruct ndR3__ as (-> & ndR4__); nd_pre ndR4__ 6%nat; intros BRn AH2 UJ RNn RSn _; nd_post).
  rewrite EspA in ST2, PRES2.
  cbn [snd fst].
  replace (ret_pc (Z_to_bv 64 0x347f0)) with (Z_to_bv 64 0x347f0) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  assert (HIN2 : In (HB p A nold) (HB q NEW n :: LB)) by (right; exact HIN).
  (nd_pre (AHI_live_hdr L RNG2 st2 _ m2 p A nold AH2 HIN2) 4%nat; intros b1 hctx HDR RHD; nd_post).
  assert (SRC1 : rw_cells asegs m1 A [CB (Z.to_nat nold) bs]).
  { eapply (aheap_pres_rw_cells CI); [exact PRES1 | exact SRC |]. right. left. exists (HB p A nold). split; [exact HIN|].
    cbn [ab_addr ab_size cells_size csize]. clear -NOLD. lia. }
  assert (SRC2 : rw_cells asegs m2 A [CB (Z.to_nat nold) bs]).
  { eapply (aheap_pres_rw_cells CIF); [exact PRES2 | exact SRC1 |]. right. left. exists (HB p A nold). split; [exact HIN|].
    cbn [ab_addr ab_size cells_size csize]. clear -NOLD. lia. }
  assert (LBS : length bs = Z.to_nat nold) by (destruct SRC as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
  assert (LUJ : length junk = Z.to_nat n) by (destruct UJ as [[WFc _] _]; cbn in WFc; exact (proj1 WFc)).
  (pose proof AH2 as ndP__; nd_pre ndP__ 4%nat; intros ALO2 ARNG2 [X2 [AR2 BL2]] HFK2; nd_post).
  (pose proof (AREP_poison_cells adepot_iface AQUAR ASEC_of L st2 X2 m2 ltac:(rewrite <- AHI_eq; exact AR2)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ REAL2 _; nd_post).
  pose proof (relro_word m2 0xa58b8 0xa7738 (AHI_relro L RNG2 st2 _ m2 AH2) ltac:(unfold ARELRO_LO; clear; lia) ltac:(unfold ARELRO_HI; clear; lia) ltac:(vm_compute; reflexivity)) as GOTM.
  assert (PQ : p <> q).
  { pose proof (AHI_hb_ids L RNG2 st2 _ m2 AH2) as ND. cbn [hb_ids flat_map ab_kind app] in ND. inversion ND as [|x l NI _]; subst.
    intros ->. apply NI. clear -HIN. induction LB as [|b LB' IH]; [destruct HIN|]. cbn [hb_ids flat_map]. apply in_or_app.
    destruct HIN as [->|HIN]; [left; cbn; left; reflexivity| right; apply IH; exact HIN]. }
  assert (SEP : A + nold <= NEW \/ NEW + n <= A).
  { pose proof (AHI_blocks_disjoint L RNG2 st2 _ m2 (HB p A nold) (HB q NEW n) AH2 HIN2 ltac:(left; reflexivity) ltac:(intros E; injection E; intros; apply PQ; assumption)) as D.
    cbn [ab_addr ab_size] in D. exact D. }
  (nd_pre BRn 4%nat; intros NBLK NN0 NHI N16; nd_post). (nd_pre BRo 4%nat; intros OBLK ON0 OHI O16; nd_post).
  pose proof (ablk_lin _ _ NBLK) as (NL1 & _). pose proof (ablk_lin _ _ OBLK) as (OL1 & _). unfold AIMG_HI in NL1, OL1.
  (pose proof ARNG2 as ndP__; nd_pre ndP__ 14%nat; intros RIMG2 _ _ _ _ _ _ _ _ _ _ _ _ RTLS2; nd_post).
  (* [comment removed for export] *)
  eapply implF_evtF.
  { eapply (ricptC_spec RNG2 (Z_to_bv 64 spA) gp tp t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b _ _ _ s7 s8 s9 s10 s11 t3b t4b t5b t6b
              F fc m2 A NEW n nold SO b1 hctx bs junk MI2).
    all: try lazymatch goal with
         | |- rw_cells _ _ _ [C8 _] => exact GOTM
         | |- rw_cells _ _ _ [C8 _; C8 _] => exact REAL2
         | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact HDR
         | |- rw_cells _ _ _ [CB _ _] => first [exact SRC2 | exact UJ]
         | |- @eq nat _ _ => first [exact LBS | exact LUJ]
         | |- _ \/ _ => exact SEP
         | |- rng_aimg _ => exact RIMG2
         | |- rng_atls _ => exact RTLS2
         | |- rng _ _ _ => first [exact RHD | exact RNn | eapply rng_fp_le; [exact FPLE2 | exact RBo]]
         | |- _ => subst SO; unfold AREQMAX in *; clear -NR NOLD NL1 OL1 NHI OHI NN0 ON0 H SPR SPB; lia
         end. }
  intros ms3 P3. unfold ricptC_post in P3. cbv zeta in P3.
  (nd_pre P3 11%nat; intros t0c t1c t2c a6c a7c t3c t4c t5c t6c m3 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MU3 WM3 MI3 NEWC; nd_post).
  chg (Z.min nold n) mn.
  assert (MN : 1 <= mn /\ mn <= nold /\ mn <= n) by (subst mn; clear -NR NOLD; lia).
  (* [comment removed for export] *)
  assert (AH3 : AHEAP_I L RNG2 st2 (HB q NEW n :: LB) m3).
  { eapply (AHI_frame CI CI_B L RNG2 st2 _ m2 m3 [(NEW, NEW + mn)]%Z AH2 MU3 WM3).
    apply Forall_cons; [| apply Forall_nil]. cbn [fst snd]. left. right. left. exists (HB q NEW n). split; [left; reflexivity|].
    cbn [ab_addr ab_size]. clear -MN. lia. }
  (* [comment removed for export] *)
  assert (SPA : spA = bv_unsigned sp + -2208) by reflexivity. assert (SOE : SO = bv_unsigned sp + -2136) by reflexivity.
  assert (KST : forall B k, spA <= B -> aclient_range CIF LB spA B k) by (intros B k HB; left; left; exact HB).
  assert (KMU : forall B k, ATOP <= B -> 0 <= k -> disjoint_from [(NEW, NEW + mn)]%Z B k) by (intros B k HB Hk; cbn [disjoint_from]; split; [clear -HB Hk NHI MN; lia| exact I]).
  assert (XS : forall B cs, spA <= B -> rw_cells asegs m1 B cs -> rw_cells asegs m3 B cs).
  { intros B cs HB HC. eapply (rw_cells_transport asegs _ m2 m3); [| exact MU3 | exact WM3 | apply KMU; [clear -HB SPA SPB; lia| apply Nat2Z.is_nonneg]].
    eapply (aheap_pres_rw_cells CIF); [exact PRES2 | exact HC | apply KST; exact HB]. }
  pose proof (XS (bv_unsigned sp + -2208) _ ltac:(clear -SPA; lia) FR48) as FR48c. pose proof (XS (bv_unsigned sp + -2160) _ ltac:(clear -SPA; lia) FR16) as FR16c.
  pose proof (XS (bv_unsigned sp + -2144) _ ltac:(clear -SPA; lia) FRP) as FRPc. pose proof (XS (bv_unsigned sp + -2136) _ ltac:(clear -SPA; lia) SS) as SSc.
  pose proof (XS (bv_unsigned sp + -80) _ ltac:(clear -SPA; lia) FRS) as FRSc.
  assert (TBc : u64arr asegs m3 (SO + 16) tb).
  { eapply (u64arr_transport asegs _ m2 m3); [| exact MU3 | exact WM3 | apply KMU; [clear -SOE SPB; lia| clear; lia]].
    eapply (aheap_pres_u64arr CIF); [exact PRES2 | exact TB | apply KST; clear -SPA SOE; lia]. }
  assert (FLc : rw_cells asegs m3 0x13e488 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]).
  { eapply (rw_cells_transport asegs _ m2 m3); [| exact MU3 | exact WM3 | cbn [disjoint_from cells_size csize Nat.add]; split; [clear -NL1; lia| exact I]].
    eapply (aheap_pres_rw_cells CIF); [exact PRES2 | exact FL1 |]. left. right. left. exists (0x13e488, 0x13e48c). split; [left; reflexivity|].
    cbn [fst snd cells_size csize Nat.add]. clear. lia. }
  assert (ST3 : stk asegs m3 lo spA).
  { eapply stk_transport_disjoint; [exact ST2 | exact MU3 | exact WM3 |]. cbn [disjoint_from]. split; [clear -BOT NHI MN; lia| exact I]. }
  (* [comment removed for export] *)
  eapply implS_sbind.
  { eapply (DEALLOCFN L RNG2 (Z_to_bv 64 0x34884) (Z_to_bv 64 spA) gp tp t0c t1c t2c _ _ _ _ _ _ _ _ a6c a7c _ _ _ _ _ s7 s8 s9 s10 s11 t3c t4c t5c t6c
              F fc m3 st2 _ p A nold lo SO AREALLOC_PC' trc tb AH3 HIN2 MI3).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => rewrite EspA; exact ST3
         | |- @eq word _ _ => first [exact TP | reflexivity]
         | |- rw_cells _ _ _ [C1 _; C1 _; C1 _; C1 _] => exact FLc
         | |- 4096 <= bv_unsigned (Z_to_bv 64 _) => rewrite unsigned_lit by (clear; lia); clear; lia
         | |- rw_cells _ _ _ _ => replace (SO + 16) with (bv_unsigned sp + -2136 + 16) by (subst SO; clear; lia); exact SSc
         | |- u64arr _ _ _ _ => exact TBc
         | |- @eq nat _ _ => exact LTB
         | |- map _ _ = _ => exact TRF
         | |- In _ _ => exact TRU
         | |- (_ <= _)%nat => exact LTRC
         | |- rng _ _ _ => rewrite ?EspA; eapply rng_fp_le; [exact FPLE2|]; eapply rng_sub'; [exact RSTK|]; subst spA SO; clear -SPB LO BOT SPR; lia
         | |- _ => rewrite ?EspA; subst spA SO; unfold AFREE_STACK; clear -SPB LO BOT SPR SP47 H; lia
         end. }
  intros st3 RNG3 ms4 POST4. unfold afree_post in POST4.
  (nd_pre POST4 18%nat; intros FPLE4 t0d t1d t2d a0d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d m4 ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MI4 ST4 PRES4 AH4; nd_post).
  rewrite EspA in ST4, PRES4. rewrite (lb_remove_cons_other p q NEW n LB ltac:(intros E; apply PQ; symmetry; exact E)) in PRES4, AH4.
  apply implS_ret.
  replace (ret_pc (Z_to_bv 64 0x34884)) with (Z_to_bv 64 0x34884) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  assert (KS4 : forall B k, spA <= B -> aclient_range CI (HB q NEW n :: lb_remove p LB) spA B k) by (intros B k HB; left; left; exact HB).
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 FR48c (KS4 (bv_unsigned sp + -2208) _ ltac:(clear -SPA; lia))) as FR48d.
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 FR16c (KS4 (bv_unsigned sp + -2160) _ ltac:(clear -SPA; lia))) as FR16d.
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 FRPc (KS4 (bv_unsigned sp + -2144) _ ltac:(clear -SPA; lia))) as FRPd.
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 SSc (KS4 (bv_unsigned sp + -2136) _ ltac:(clear -SPA; lia))) as SSd.
  pose proof (aheap_pres_rw_cells CI _ _ _ _ _ _ PRES4 FRSc (KS4 (bv_unsigned sp + -80) _ ltac:(clear -SPA; lia))) as FRSd.
  pose proof (aheap_pres_u64arr CI _ _ _ _ _ _ PRES4 TBc (KS4 (SO + 16) _ ltac:(clear -SPA SOE; lia))) as TBd.
  apply rw_cells_of_u64arr in TBd. rewrite LTB in TBd.
  assert (NEWD : rw_cells asegs m4 NEW [CB (Z.to_nat n) (firstn (Z.to_nat mn) bs ++ skipn (Z.to_nat mn) junk)]).
  { eapply (aheap_pres_rw_cells CI); [exact PRES4 | exact NEWC |]. right. left. exists (HB q NEW n). split; [left; reflexivity|].
    cbn [ab_addr ab_size cells_size csize]. clear -NR. lia. }
  (* [comment removed for export] *)
  eapply evtF_mono.
  { eapply (ricptD_spec RNG3 sp gp tp t0d t1d t2d _ _ a0d a1d a2d a3d a4d a5d a6d a7d _ _ _ _ s7 s8 s9 s10 s11 t3d t4d t5d t6d
              ra s0 s1 s2 s3 s4 s5 s6 _ _ _ _ _ sp F fc m4 NEW lo fr0 junk2).
    all: try lazymatch goal with
         | |- stk _ _ _ _ => exact ST4
         | |- mem_inv _ _ => exact MI4
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] => exact FR48d
         | |- rw_cells _ _ _ [CB _ _; C8 _] => exact FR16d
         | |- rw_cells _ _ _ [C8 _; CB _ _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _; C8 _] => exact FRSd
         | |- exists csP, rw_cells _ _ (_ + -2144) _ /\ _ => eexists; split; [exact FRPd| reflexivity]
         | |- exists csA, rw_cells _ _ (_ + -2136) _ /\ _ => eexists; split; [exact SSd| reflexivity]
         | |- exists csT, rw_cells _ _ (_ + -2120) _ /\ _ => eexists; split; [replace (bv_unsigned sp + -2120) with (SO + 16) by (subst SO; clear; lia); exact TBd| reflexivity]
         | |- rng_aimg _ => eapply rng_fp_le; [exact FPLE4| exact RIMG2]
         | |- rng_atls _ => eapply rng_fp_le; [exact FPLE4| exact RTLS2]
         | |- rng _ _ _ => eapply rng_fp_le; [exact FPLE4|]; eapply rng_fp_le; [exact FPLE2| exact RSTK]
         | |- _ => clear -SPB LO BOT NL1 NHI NN0 H; lia
         end. }
  cbv beta. intros ms5 (a0e & -> & _ & ST5).
  (* [comment removed for export] *)
  assert (INCL : forall b, In b (lb_remove p LB) -> In b LB) by (intros b Hb; exact (proj1 (proj1 (In_lb_remove p LB b) Hb))).
  assert (QFRESH : ~ In (HB q NEW n) LB).
  { pose proof (AHI_blocks_nodup L RNG2 st2 _ m2 AH2) as ND. inversion ND; assumption. }
  unfold arealloc_post. cbn [snd fst].
  split; [eapply fp_le_trans; [exact FPLE2| exact FPLE4]|].
  do 15 eexists. exists m4. split; [reflexivity|]. split; [exact MI4|]. split; [exact ST5|].
  split.
  { eapply aheap_pres_trans; [eapply (aheap_pres_weaken CI LB); [exact PRES1 | apply Z.le_refl | exact INCL]|].
    eapply aheap_pres_trans; [eapply (aheap_pres_weaken CI LB); [exact (aheap_pres_cif _ _ _ _ PRES2) | clear -SPA; lia | exact INCL]|].
    eapply aheap_pres_trans; [| eapply (aheap_pres_weaken CI (HB q NEW n :: lb_remove p LB)); [exact PRES4 | clear -SPA; lia | intros b Hb; right; exact Hb]].
    (* [comment removed for export] *)
    eapply (aheap_pres_of_munch CI _ _ [(NEW, NEW + mn)]%Z); [exact MU3 | exact WM3 | |].
    - intros a Ha CL. cbn [outside]. split; [| exact I].
      destruct CL as [SK | [(iv & Hiv & R) | [(b & Hb & R) | (a' & Ha' & ->)]]].
      + clear -SK SPB NHI MN. lia.
      + pose proof (aci_img CI CI_B iv Hiv) as IMG. unfold AIMG_HI in IMG. clear -R IMG NL1. lia.
      + assert (Hb2 : In b (HB q NEW n :: LB)) by (right; apply INCL; exact Hb).
        assert (NEb : b <> HB q NEW n) by (intros ->; apply QFRESH; apply INCL; exact Hb).
        pose proof (AHI_blocks_disjoint L RNG2 st2 _ m2 b (HB q NEW n) AH2 Hb2 ltac:(left; reflexivity) NEb) as D. cbn [ab_addr ab_size] in D.
        clear -R D MN. lia.
      + assert (A47 : 0 <= a' < 2^47).
        { destruct Ha' as [SK | [(iv & Hiv & R) | (cls & FA & sz & Hin & R)]].
          - clear -SK H. lia.
          - pose proof (aci_img CI CI_B iv Hiv) as IMG. pose proof (aci_lo CI CI_B iv Hiv) as ILO. unfold AIMG_HI in IMG. clear -R IMG ILO. lia.
          - (pose proof (AHI_block_bounds L RNG2 st2 _ m2 (mkABlock (ABFake cls) FA sz) AH2 ltac:(right; apply INCL; exact Hin)) as ndP__; nd_pre ndP__ 3%nat; intros K1 K2 K3; nd_post).
            cbn [ab_addr ab_size] in K1, K2, K3. unfold AIMG_HI in K1. clear -R K1 K3 H. lia. }
        rewrite shad_div. unfold ASHOFF. unfold ablk, KLS, AIMG_HI in NBLK. clear -A47 NBLK MN. Z.div_mod_to_equations. lia.
    - intros a Ha XT. cbn [outside]. split; [| exact I].
      pose proof (AHI_block_tls L RNG2 st2 _ m2 (HB q NEW n) AH2 ltac:(left; reflexivity)) as DT. cbn [ab_addr ab_size] in DT.
      pose proof (AHI_block_ahm L RNG2 st2 _ m2 (HB q NEW n) AH2 ltac:(left; reflexivity)) as DA. cbn [ab_addr ab_size] in DA.
      destruct XT as [[T|(ta & Hta & ->)]|[IM|IM]].
      + clear -T DT MN. lia.
      + pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
        assert (SA : shad ATOP <= 17594332446720) by (rewrite shad_div; unfold ASHOFF; clear -H; Z.div_mod_to_equations; lia).
        unfold ablk, KLS, AIMG_HI in NBLK. clear -TS1 TS2 SA NBLK MN. lia.
      + unfold AIMSH_LO, AIMSH_LEN in IM. unfold ablk, KLS, AIMG_HI in NBLK. clear -IM NBLK MN. lia.
      + unfold AAHM_SZ in *. clear -IM DA MN. lia. }
  exists NEW, (skipn (Z.to_nat mn) junk).
  split; [reflexivity|]. split; [unfold ablock_range; repeat split; assumption|]. split; [exact AH4|].
  split; [rewrite length_skipn, LUJ; clear -MN; lia|]. split; [exact NEWD|].
  split; eapply rng_fp_le; try exact FPLE4; assumption.
Qed.
End Zd1.
#[using="CI_B"] Theorem AHI_realloc : ltac:(let t := eval cbv delta [AHI_realloc__stmt] in AHI_realloc__stmt in exact t).
Proof. exact AHI_realloc__body. Qed.
End Gen.
End CANSEC1.
End TwB.
End ARealloc.

(* [comment removed for export] *)
Module AInstanceC.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_tabscan__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acallocS__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ACallocG__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARealloc_iface__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.ALCallocPG OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.ARealloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section Gen.
Variable CI : list (Z * Z).
Hypothesis CI_B : ci_okb CI = true.

#[using="CI_B"] Theorem AHI_calloc : acalloc_stmt CI AHEAP_I.
Proof. exact (acalloc_all adepot_iface AQUAR ASEC_of AFAKE AH_laws CI (aci_ok CI CI_B) (aci_ok2 CI CI_B)). Qed.

#[using="CI_B"] Theorem AHI_realloc' : arealloc_stmt CI AHEAP_I.
Proof. exact (AHI_realloc CI CI_B). Qed.
End Gen.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_tabscan__A3W.F_adepot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstance.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acallocS__A3W.AInstanceM.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.AInstanceF.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ACallocG__A3W.ALCallocPG.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARealloc_iface__A3W.ARealloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AInstanceF__A3W.ARealloc.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge.flia ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_arecyc1.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section Gen.
Variable CI : list (Z * Z).
Hypothesis CI_B : ci_okb CI = true.

#[using="CI_B"] Theorem AHI_calloc : acalloc_stmt CI AHEAP_I.
Proof. exact (acalloc_all adepot_iface AQUAR ASEC_of AFAKE AH_laws CI (aci_ok CI CI_B) (aci_ok2 CI CI_B)). Qed.

#[using="CI_B"] Theorem AHI_realloc' : arealloc_stmt CI AHEAP_I.
Proof. exact (AHI_realloc CI CI_B). Qed.
End Gen.
End CANSEC1.
End TwB.
End AInstanceC.
