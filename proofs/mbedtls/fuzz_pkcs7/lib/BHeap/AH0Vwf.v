(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AxSymExec3 AxSymExec3Sound. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanCertDefs. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import AsanPlanSound AsanInit AsanMainEntryKit. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BBoot Require Import AsanMainEntryFacts AsanMainEntryLemmas.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel AModelX. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm AVst AH0Spec0 AH0Base AH0Layout AH0Pure.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AH0Vwf () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.pv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_prim"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_secv"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_thr"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_treg"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_fstk"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dtls"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dnodes"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_dstore"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_lla"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_ictx"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_tvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_gvec"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.v_divec"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.NDisj"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.AOff"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WMd"; "LinuxProcessSemantics.Riscv.Instr.M_MUL"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WLit"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.WVar"; "Stdlib.Lists.List.forallb"; "Corelib.Init.Datatypes.orb"; "pgobj_eqb"; "has_cnst"; "ndisj_pg"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "PGOBJS"; "Corelib.Init.Datatypes.andb"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryFacts.ALit"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.W_STKPG"; "Stdlib.Lists.List.existsb"; "Corelib.Init.Datatypes.negb"; "RocqVerifyHarness.AgentSubmission.BBoot.AsanMainEntryLemmas.pv_beq"; "Corelib.Init.Datatypes.app"; "TRPG_A"; "TRPG_B"; "pv_nodupb"; "Corelib.Lists.ListDef.map"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.lowhigh"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.Lists.List.In"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Base.PG"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.ex"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.lkind"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.trange"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.tr_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.node_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.store_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AVst.ri_tr"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Spec0.L0_of"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.TR"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KEager"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.kFakeBytes"; "Corelib.Init.Datatypes.false"; "RocqVerifyHarness.AgentSubmission.BHeap.AH0Layout.EXTRA"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KLazy"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.KNoacc"; "Vwf.tz"; "Vwf.pgz"; "Vwf.RIz"; "SH3"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_hi"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.t_lo"; "Corelib.Init.Logic.not"].


(* [comment removed for export] *)
Definition AL0 : asan_layout := ALazy.AL 0x7fff8000 0x0f5e50 0x1099f8 0x10000 0x65f000.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zap (x y : Z * Z) : Prop := fst x + snd x <= fst y \/ fst y + snd y <= fst x.
Inductive zseps : list (Z * Z) -> Prop :=
| zseps_nil : zseps []
| zseps_cons : forall x l, Forall (zap x) l -> zseps l -> zseps (x :: l).
Lemma zap_sym : forall x y, zap x y -> zap y x. Proof. intros x y H. unfold zap in *. lia. Qed.
Lemma zseps_app : forall a b, zseps a -> zseps b -> (forall x y, In x a -> In y b -> zap x y) -> zseps (a ++ b).
Proof.
  induction a as [|x a IH]; intros b Ha Hb X; cbn; [exact Hb|].
  inversion Ha as [|x' l F S]; subst. constructor.
  - apply Forall_app. split; [exact F|]. apply Forall_forall. intros y Hy. apply X; [now left| exact Hy].
  - apply IH; [exact S| exact Hb|]. intros u v Hu Hv. apply X; [now right| exact Hv].
Qed.
Lemma zseps_In : forall l x y, zseps l -> In x l -> In y l -> x = y \/ zap x y.
Proof.
  induction l as [|a l IH]; intros x y S Hx Hy; [destruct Hx|].
  inversion S as [|a' l' F S']; subst.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - left. reflexivity.
  - right. exact (proj1 (Forall_forall _ _) F y Hy).
  - right. apply zap_sym. exact (proj1 (Forall_forall _ _) F x Hx).
  - apply IH; assumption.
Qed.
Lemma zseps_NoDup : forall l, zseps l -> (forall x, In x l -> 0 < snd x) -> List.NoDup l.
Proof.
  induction l as [|a l IH]; intros S P; [constructor|].
  inversion S as [|a' l' F S']; subst. constructor.
  - intros Hin. pose proof (proj1 (Forall_forall _ _) F a Hin) as X. pose proof (P a ltac:(now left)). unfold zap in X. lia.
  - apply IH; [exact S'|]. intros x Hx. apply P. now right.
Qed.
Lemma NoDup_map_In_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  intros A B f l. induction l as [|a l IH]; intros x y ND Hx Hy E; [destruct Hx|].
  cbn in ND. inversion ND as [|b m Hnin ND']; subst.
  destruct Hx as [<-|Hx]; destruct Hy as [<-|Hy].
  - reflexivity.
  - exfalso. apply Hnin. rewrite E. apply in_map. exact Hy.
  - exfalso. apply Hnin. rewrite <- E. apply in_map. exact Hx.
  - apply IH; assumption.
Qed.
Lemma map_pair_eta : forall (l : list (Z * Z)), map (fun r => (fst r, snd r)) l = l.
Proof. induction l as [|[a b] l IH]; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition PGOBJS : list (pv * Z) := ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "(0.(1.$2.$3.)(4.$2.$3.$5.+2000011000.)(0.(1.$2.$3.)(4.$2.$3.$6.+800000.)(0.(1.$2.$3.)(4.$2.$3.$7.+1000.)(0.(1.$2.$3.)(4.$2.$3.$8.+10000.)(0.(1.$2.$3.)(4.$2.$3.$9.+;09000.)(0.(1.$2.$3.)(4.$2.$3.$:.+1000.)(0.(1.$2.$3.)(4.$2.$3.$;.+100000.)(0.(1.$2.$3.)(4.$2.$3.$<.+800000.)(0.(1.$2.$3.)(4.$2.$3.$=.+10000.)(0.(1.$2.$3.)(4.$2.$3.$>.+38>000.)(0.(1.$2.$3.)(4.$2.$3.$?.+1000.)(0.(1.$2.$3.)(4.$2.$3.$10.+1000.)(0.(1.$2.$3.)(4.$2.$3.$11.+1000.)(12.(1.$2.$3.)))))))))))))))")
(* [comment removed for export] *).
(* [comment removed for export] *)
Definition TRPG_A : list (pv * Z) := [(v_dnodes, 0x100000); (v_dstore, 0x800000)].
Definition TRPG_B : list (pv * Z) := ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "(0.(1.$2.$3.)(4.$2.$3.$7.+1000.)(0.(1.$2.$3.)(4.$2.$3.$8.+10000.)(0.(1.$2.$3.)(4.$2.$3.$9.+;09000.)(0.(1.$2.$3.)(4.$2.$3.$:.+1000.)(0.(1.$2.$3.)(4.$2.$3.$=.+10000.)(0.(1.$2.$3.)(4.$2.$3.$>.+38>000.)(0.(1.$2.$3.)(4.$2.$3.$?.+1000.)(0.(1.$2.$3.)(4.$2.$3.$10.+1000.)(0.(1.$2.$3.)(4.$2.$3.$11.+1000.)(12.(1.$2.$3.)))))))))))")
(* [comment removed for export] *).
Definition SH3 : list (Z * Z) := [(0x7fff7000, 0x10000000); (0x8fff7000, 0x20000000000); (0x2008fff7000, 0xdfff0001000)].

Definition pgobj_eqb (x y : pv * Z) : bool := (pv_beq (fst x) (fst y) && Z.eqb (snd x) (snd y))%bool.
Lemma pgobj_eqb_eq : forall x y, pgobj_eqb x y = true -> x = y.
Proof.
  intros [a la] [b lb] H. unfold pgobj_eqb in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2].
  apply pv_beq_eq in H1. apply Z.eqb_eq in H2. subst. reflexivity.
Qed.
Lemma pgobj_in : forall x l, existsb (pgobj_eqb x) l = true -> In x l.
Proof. intros x l H. apply existsb_exists in H as (y & Hy & E). apply pgobj_eqb_eq in E. subst y. exact Hy. Qed.
Definition ndisj_pg (a : pv) (la : Z) (b : pv) (lb : Z) : nt := ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "(13.(14.(15.$16.(17.+1000.)(18.O4.))=)(17.O3.)(14.(15.$16.(17.+1000.)(18.O2.))=)(17.O1.))")
(* [comment removed for export] *).
Definition has_cnst (c : nt) : bool := existsb (nt_eqb c) CNSTS.
(* [comment removed for export] *)
Definition pairs_okb : bool := ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "(19.(1.$2.$3.)Lx,(1.$2.$3.)(19.(1.$2.$3.)Ly,(1.$2.$3.)(1:.(1:.(1;.R2.R1.)(1<.(1=.(1>.$2.$3.R2.)(1?.$2.$3.R2.)(1>.$2.$3.R1.)(1?.$2.$3.R1.))))(1<.(1=.(1>.$2.$3.R1.)(1?.$2.$3.R1.)(1>.$2.$3.R2.)(1?.$2.$3.R2.))))$20.)$20.)")
(* [comment removed for export] *).
Definition singles_okb : bool := ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "(19.(1.$2.$3.)Lx,(1.$2.$3.)(21.(21.(1<.(13.(22.+10000.)(17.+64?000.)(14.(15.$16.(17.+1000.)(18.(1>.$2.$3.R1.)))=)(17.(1?.$2.$3.R1.))))(1<.(13.(22.+7???7000.)(17.+100000001000.)(14.(15.$16.(17.+1000.)(18.(1>.$2.$3.R1.)))=)(17.(1?.$2.$3.R1.)))))(1<.(13.(14.$23.-800000.)(17.+800000000000.)(14.(15.$16.(17.+1000.)(18.(1>.$2.$3.R1.)))=)(17.(1?.$2.$3.R1.)))))$20.)")
(* [comment removed for export] *).
(* [comment removed for export] *)
Fixpoint pv_nodupb (l : list pv) : bool :=
  match l with [] => true | v :: l' => (negb (existsb (pv_beq v) l') && pv_nodupb l')%bool end.
Definition trpg_okb : bool := ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "(21.(19.(1.$2.$3.)Lx,(1.$2.$3.)(21.(24.(1.$2.$3.)(1;.R1.)$20.)(25.(26.(1>.$2.$3.R1.)$5.)))(27.(1.$2.$3.)$28.$29.))(2:.(2;.(1.$2.$3.)$2.(1>.$2.$3.)(27.(1.$2.$3.)$28.$29.))))")
(* [comment removed for export] *).
Lemma pairs_ok : pairs_okb = true. Proof. vm_compute. reflexivity. Qed.
Lemma singles_ok : singles_okb = true. Proof. vm_compute. reflexivity. Qed.
Lemma trpg_ok : trpg_okb = true. Proof. vm_compute. reflexivity. Qed.

Lemma pv_nodupb_sound : forall l, pv_nodupb l = true -> List.NoDup l.
Proof.
  induction l as [|v l IH]; intros H; [constructor|]. cbn [pv_nodupb] in H. apply andb_prop in H as [H1 H2].
  constructor; [| exact (IH H2)]. intros Hin. enough (E : existsb (pv_beq v) l = true) by (rewrite E in H1; discriminate H1).
  apply existsb_exists. exists v. split; [exact Hin|]. destruct (pv_eq_dec v v) as [E|NE]; [| exfalso; exact (NE eq_refl)].
  exact (internal_pv_dec_lb _ _ E).
Qed.
Lemma pgobjs_pagevars : forall x, In x PGOBJS -> In (fst x) PAGEVARS /\ 0 < snd x < 2 ^ 40 /\ snd x mod 4096 = 0.
Proof.
  intros x Hx. cbn in Hx.
  repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; cbn; (split; [tauto | split; [lia | reflexivity]]).
Qed.
Lemma trpg_facts : forall x, In x (TRPG_A ++ TRPG_B) -> In x PGOBJS /\ fst x <> v_prim.
Proof.
  intros x Hx. pose proof trpg_ok as T. unfold trpg_okb in T. apply andb_prop in T as [T _].
  pose proof (proj1 (forallb_forall _ _) T x Hx) as X. cbv beta in X. apply andb_prop in X as [X1 X2].
  split; [exact (pgobj_in _ _ X1)|]. intros E. rewrite E in X2. cbn in X2. discriminate X2.
Qed.
Lemma trpg_nodup : List.NoDup (map fst (TRPG_A ++ TRPG_B)).
Proof. apply pv_nodupb_sound. pose proof trpg_ok as T. unfold trpg_okb in T. apply andb_prop in T as [_ T]. exact T. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Vwf.
  Context {hAR : arun}.
  Variable p : me_params.
  Hypothesis HCN : Forall cnst_ok (me_cnsts p).
  Variable STKHI : Z.
  Variable FOG : list (Z * Z).
  Variable TF : Z.
  Hypothesis HAC : ACEIL = STKPG p - 0x800000.
  Hypothesis STKHI_gt : SP p < STKHI.
  Hypothesis STKHI_pg : STKHI mod 4096 = 0.
  Hypothesis STKHI_47 : STKHI <= 2 ^ 47.
  Hypothesis STKHI_len : STKHI <= SP p + 2 ^ 23.
  Hypothesis FOG_ok : ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "(2<.(1.$3.$3.)Lr,(1.$3.$3.)(2=.(2>.(1>.$3.$3.R1.)(1?.$3.$3.R1.))(2=.(2?.=(1?.$3.$3.R1.))(2=.(30.(31.(1>.$3.$3.R1.)(1?.$3.$3.R1.))(32.VhAR,))(2=.(33.$3.(34.(1>.$3.$3.R1.)+1000.)=)(33.$3.(34.(1?.$3.$3.R1.)+1000.)=)))))VFOG,)")
(* [comment removed for export] *).
  Hypothesis FOG_len : (length FOG <= 2)%nat.
  Hypothesis FOG_small : Forall (fun r => snd r <= 8192) FOG.
  Hypothesis TF_ok : 1 <= TF <= 3.
  (* [comment removed for export] *)
  Definition pgz (x : pv * Z) : Z * Z := (PG p (fst x), snd x).
  Hypothesis FOG_seps : zseps FOG.
  Hypothesis FOG_apart : forall r x, In r FOG -> In x PGOBJS -> zap r (pgz x).

  Let bp := bp_of p STKHI FOG TF.
  Let h0 := h0_of bp.
  (* [comment removed for export] *)
  Definition RI : Z := SB p + 2 ^ 37.
  Definition RIz : Z * Z := (RI, 4096).

  Local Ltac pv := cbn; tauto.

  #[using="HCN"] Lemma r_s1' : 0xffff0000 <= uv p v_s1 <= 0xffffffff. Proof. exact (r_s1 p HCN). Qed.
  #[using="HCN"] Lemma r_s2' : 0 <= uv p v_s2 <= 2047. Proof. exact (r_s2 p HCN). Qed.

  (* [comment removed for export] *)
  #[using="HCN STKHI FOG HAC FOG_len"] Lemma pg_single : ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "Pv,$2.Plen,$3.P,(35.(1.$2.$3.)(4.$2.$3.R2.R1.)$20.)(2=.(30.+1000.(36.Vp,R3.))(2=.(33.$3.(34.(36.Vp,R3.)+1000.)=)(2=.(2?.=R2.)(2=.(33.$3.(34.R2.+1000.)=)(2=.(37.(30.(31.(36.Vp,R3.)R2.)+10000.)(30.+65?000.(36.Vp,R3.)))(2=.(37.(30.(31.(36.Vp,R3.)R2.)+7???7000.)(30.+10007???8000.(36.Vp,R3.)))(30.(31.(36.Vp,R3.)R2.)(32.VhAR,))))))))")
(* [comment removed for export] *).
  Proof.
    intros v len Hin. pose proof (pgobjs_pagevars _ Hin) as (Hv & Hlen & Hal). cbn [fst snd] in Hv, Hlen, Hal.
    pose proof (proj1 (forallb_forall _ _) singles_ok _ Hin) as S. cbn [fst snd] in S.
    apply andb_prop in S as [S S3]. apply andb_prop in S as [S1 S2].
    pose proof (PG_range p HCN v Hv) as [G G'].
    pose proof (page_hull_apart p HCN v len Hv ltac:(lia) (In_CNSTS _ S1)) as H1.
    pose proof (page_band_apart p HCN v len Hv ltac:(lia) (In_CNSTS _ S2)) as H2.
    pose proof (page_stack_apart p HCN (proj2 r_s1') (proj2 r_s2') v len Hv ltac:(lia) (In_CNSTS _ S3)) as H3.
    rewrite HAC. split; [lia|]. split; [exact G'|]. split; [lia|]. split; [exact Hal|]. split; [exact H1|]. split; [exact H2| exact H3].
  Qed.

  #[using="hAR HCN STKHI FOG FOG_len"] Lemma pg_pair : ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "Pa,$2.Pla,$3.Pb,$2.Plb,$3.P,(35.(1.$2.$3.)(4.$2.$3.R4.R3.)$20.)P,(35.(1.$2.$3.)(4.$2.$3.R3.R2.)$20.)(37.(33.(1.$2.$3.)(4.$2.$3.R6.R5.)(4.$2.$3.R4.R3.))(37.(30.(31.(36.Vp,R6.)R5.)(36.Vp,R4.))(30.(31.(36.Vp,R4.)R3.)(36.Vp,R6.))))")
(* [comment removed for export] *).
  Proof.
    intros a la b lb Ha Hb.
    pose proof (proj1 (forallb_forall _ _) (proj1 (forallb_forall _ _) pairs_ok _ Ha) _ Hb) as X. cbn [fst snd] in X.
    pose proof (pgobjs_pagevars _ Ha) as (Va & La & _). pose proof (pgobjs_pagevars _ Hb) as (Vb & Lb & _). cbn [fst snd] in Va, La, Vb, Lb.
    apply orb_prop in X as [X|X]; [apply orb_prop in X as [X|X]|].
    - left. exact (pgobj_eqb_eq _ _ X).
    - right. exact (pages_apart p HCN a la b lb Va Vb ltac:(lia) ltac:(lia) (In_CNSTS _ X)).
    - right. pose proof (pages_apart p HCN b lb a la Vb Va ltac:(lia) ltac:(lia) (In_CNSTS _ X)). lia.
  Qed.
  (* [comment removed for export] *)
  #[using="hAR HCN STKHI FOG FOG_len"] Lemma pg_apart : forall x y, In x PGOBJS -> In y PGOBJS -> fst x <> fst y -> zap (pgz x) (pgz y).
  Proof.
    intros [a la] [b lb] Hx Hy NE. cbn [fst snd] in NE. unfold zap, pgz. cbn [fst snd].
    destruct (pg_pair a la b lb Hx Hy) as [E|D]; [| exact D]. exfalso. injection E as E1 E2. exact (NE E1).
  Qed.

  (* [comment removed for export] *)
  #[using="hAR HCN STKHI FOG FOG_len"] Lemma ri_hull : PG p v_prim + 0x1000 <= RI /\ RI + 4096 <= PG p v_prim + 0x2000011000 /\ RI mod 4096 = 0.
  Proof.
    pose proof (r_pslack p HCN) as PS. unfold RI, SB, PG.
    split; [lia|]. split; [lia|].
    replace (4096 * uv p v_prim - 4096 * uv p v_pslack + 65536 + 2 ^ 37) with ((uv p v_prim - uv p v_pslack + 16 + 2 ^ 25) * 4096) by lia.
    apply Z_mod_mult.
  Qed.
  #[using="hAR HCN STKHI FOG TF FOG_len TF_ok"] Lemma ri_apart : forall x, In x PGOBJS -> fst x <> v_prim -> zap RIz (pgz x).
  Proof.
    intros [b lb] Hx NE. cbn [fst] in NE. dpose ri_hull as (R1 & R2 & _).
    pose proof (pg_apart (v_prim, 0x2000011000) (b, lb) ltac:(pv) Hx ltac:(cbn; congruence)) as D.
    unfold zap, pgz, RIz in *. cbn [fst snd] in *. lia.
  Qed.
  #[using="hAR HCN STKHI TF FOG_len TF_ok FOG_apart"] Lemma ri_fog : forall r, In r FOG -> zap RIz r.
  Proof.
    intros r Hr. dpose ri_hull as (R1 & R2 & _). pose proof (FOG_apart r (v_prim, 0x2000011000) Hr ltac:(pv)) as D.
    unfold zap, pgz, RIz in *. cbn [fst snd] in *. lia.
  Qed.
  #[using="hAR HCN STKHI FOG FOG_len"] Lemma ri_high : 0x10007fff8000 + 0x1000 <= RI.
  Proof. pose proof (r_prim p HCN) as PR. pose proof ri_hull as (R1 & _). unfold PG in R1. lia. Qed.

  (* [comment removed for export] *)
  Definition tz (t : trange) : Z * Z := (t_lo t, t_len t).
  #[using="Type"] Lemma tr_of_h0 : ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "(38.P,$3.$39.LK,P,$3.$39.(33.(3:.$3;.)(3<.Vh0,)(27.$3;.(0.$3;.(3=.(36.Vp,$;.))(0.$3;.(3>.(36.Vp,$<.))(0.$3;.(3?.(40.Vbp,))(12.$3;.))))(27.$3;.(0.$3;.(41.(36.Vp,$7.)+1000.$42.$43.$43.)(0.$3;.(41.(36.Vp,$8.)+10000.$42.$43.$43.)(0.$3;.(41.(36.Vp,$9.)$44.$42.$43.$43.)(0.$3;.(41.(36.Vp,$:.)+1000.$42.$43.$43.)(12.$3;.)))))(27.$3;.(2;.(1.$3.$3.)$3;.Lr,(1.$3.$3.)(41.(1>.$3.$3.R1.)(1?.$3.$3.R1.)A1.R2.(1?.$3.$3.R1.)$43.$45.)(46.Vp,VFOG,))(0.$3;.(41.+7???7000.+10000000.$47.$43.$45.)(0.$3;.(41.+8???7000.+20000000000.$48.$43.$45.)(0.$3;.(41.+2008???7000.+=???0001000.$47.$43.$45.)(12.$3;.)))))))))")
(* [comment removed for export] *).
  Proof.
    assert (E : emb_tr h0 = []) by reflexivity.   (* [comment removed for export] *)
    exists xkind. unfold tr_of. rewrite E, app_nil_r. reflexivity.   (* [comment removed for export] *)
  Qed.

  #[using="Type"] Lemma TZ : map tz (tr_of h0) = map pgz TRPG_A ++ RIz :: map pgz TRPG_B ++ FOG ++ SH3.
  Proof.
    destruct tr_of_h0 as [K ->]. unfold EXTRA. rewrite !map_app, !map_map. cbn -[PG SB Z.pow Z.add Z.mul].
    rewrite map_pair_eta. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma TZ_in : ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "Px,(1.$3.$3.)P,(35.(1.$3.$3.)R1.(2;.$3;.(1.$3.$3.)$49.(3<.Vh0,)))(37.(38.(1.$2.$3.)Lo,(1.$2.$3.)(2=.(35.(1.$2.$3.)R1.(27.(1.$2.$3.)$28.$29.))(33.(1.$3.$3.)R3.(4:.R1.))))(37.(33.(1.$3.$3.)R2.$4;.)(37.(35.(1.$3.$3.)R2.VFOG,)(35.(1.$3.$3.)R2.$4<.))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. rewrite TZ in Hx.
    apply in_app_iff in Hx as [Hx|Hx]; [left; apply in_map_iff in Hx as (o & <- & Ho); exists o; split; [apply in_app_iff; now left| reflexivity]|].
    destruct Hx as [<-|Hx]; [right; left; reflexivity|].
    apply in_app_iff in Hx as [Hx|Hx]; [left; apply in_map_iff in Hx as (o & <- & Ho); exists o; split; [apply in_app_iff; now right| reflexivity]|].
    apply in_app_iff in Hx as [Hx|Hx]; right; right; [now left| now right].
  Qed.

  (* [comment removed for export] *)
  #[using="HCN HAC FOG_ok FOG_len TF_ok"] Lemma TZ_single : ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "Px,(1.$3.$3.)P,(35.(1.$3.$3.)R1.(2;.$3;.(1.$3.$3.)$49.(3<.Vh0,)))(2=.(30.+1000.(1>.$3.$3.R2.))(2=.(2?.=(1?.$3.$3.R2.))(2=.(30.(31.(1>.$3.$3.R2.)(1?.$3.$3.R2.))(32.VhAR,))(2=.(33.$3.(34.(1>.$3.$3.R2.)+1000.)=)(2=.(33.$3.(34.(1?.$3.$3.R2.)+1000.)=)(37.(30.(31.(1>.$3.$3.R2.)(1?.$3.$3.R2.))+10000.)(30.+65?000.(1>.$3.$3.R2.))))))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. pose proof aceil_bounds as AB.
    destruct (TZ_in x Hx) as [(o & Ho & ->)|[->|[Hf|Hs]]].
    - destruct o as [v len]. pose proof (pg_single v len (proj1 (trpg_facts _ Ho))) as (A & B & C & D & E & F & G).
      unfold pgz. cbn [fst snd]. repeat split; first [assumption | lia].
    - dpose ri_hull as (R1 & R2 & R3). pose proof ri_high as R4.
      dpose (pg_single v_prim 0x2000011000 ltac:(pv)) as (_ & _ & _ & _ & _ & _ & G).
      unfold RIz. cbn [fst snd]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact R3|]. split; [reflexivity|]. lia.
    - pose proof (proj1 (Forall_forall _ _) FOG_ok x Hf) as ((L1 & L2 & L3) & P & C & M1 & M2). repeat split; assumption || lia.
    - cbn in Hs. destruct Hs as [<-|[<-|[<-|[]]]]; cbn [fst snd]; repeat split; try reflexivity; lia.
  Qed.
  #[using="HCN HAC FOG_ok FOG_len TF_ok"] Lemma tr_pos : forall x, In x (map tz (tr_of h0)) -> 0 < snd x.
  Proof. intros x Hx. dpose (TZ_single x Hx) as (_ & P & _). exact P. Qed.

  (* [comment removed for export] *)
  #[using="hAR STKHI FOG FOG_len"] Lemma sh3_facts : forall s, In s SH3 -> 0x7fff7000 <= fst s /\ 0 < snd s /\ fst s + snd s <= 0x10007fff8000.
  Proof. intros s Hs. cbn in Hs. destruct Hs as [<-|[<-|[<-|[]]]]; cbn; lia. Qed.
  #[using="hAR HCN STKHI FOG HAC FOG_len"] Lemma pg_sh : forall x s, In x PGOBJS -> In s SH3 -> zap (pgz x) s.
  Proof.
    intros [v len] s Hx Hs. dpose (pg_single v len Hx) as (_ & _ & _ & _ & _ & B & _). dpose (sh3_facts s Hs) as (S1 & S2 & S3).
    unfold zap, pgz. cbn [fst snd]. lia.
  Qed.
  #[using="hAR HCN STKHI FOG FOG_len"] Lemma ri_sh : forall s, In s SH3 -> zap RIz s.
  Proof. intros s Hs. dpose (sh3_facts s Hs) as (S1 & S2 & S3). pose proof ri_high. unfold zap, RIz. cbn [fst snd]. lia. Qed.
  #[using="hAR STKHI FOG_ok FOG_len"] Lemma fog_sh : forall r s, In r FOG -> In s SH3 -> zap r s.
  Proof.
    intros r s Hr Hs. pose proof (proj1 (Forall_forall _ _) FOG_ok r Hr) as ((L1 & L2 & L3) & P & _). dpose (sh3_facts s Hs) as (S1 & S2 & S3).
    unfold zap, kHighMemBeg in *. lia.
  Qed.
  #[using="hAR STKHI FOG FOG_len"] Lemma sh3_seps : zseps SH3.
  Proof. unfold SH3. repeat (constructor; [repeat (apply Forall_cons; [unfold zap; cbn; lia|]); apply Forall_nil|]). apply zseps_nil. Qed.

  (* [comment removed for export] *)
  #[using="hAR HCN STKHI FOG FOG_len"] Lemma zseps_pg : forall l, List.NoDup (map fst l) -> (forall x, In x l -> In x PGOBJS) -> zseps (map pgz l).
  Proof.
    induction l as [|a l IH]; intros ND INC; cbn; [apply zseps_nil|].
    cbn in ND. inversion ND as [|b m Hnin ND']; subst. constructor.
    - apply Forall_forall. intros y Hy. apply in_map_iff in Hy as (o & <- & Ho).
      apply pg_apart; [apply INC; now left| apply INC; now right|].
      intros E. apply Hnin. rewrite E. apply in_map. exact Ho.
    - apply IH; [exact ND'|]. intros x Hx. apply INC. now right.
  Qed.

  #[using="HCN HAC FOG_ok FOG_len TF_ok FOG_seps FOG_apart"] Lemma TZ_seps : zseps (map tz (tr_of h0)).
  Proof.
    rewrite TZ. pose proof trpg_nodup as ND. rewrite map_app in ND.
    assert (INA : forall x, In x TRPG_A -> In x PGOBJS /\ fst x <> v_prim) by (intros x Hx; apply trpg_facts, in_app_iff; now left).
    assert (INB : forall x, In x TRPG_B -> In x PGOBJS /\ fst x <> v_prim) by (intros x Hx; apply trpg_facts, in_app_iff; now right).
    apply zseps_app.
    - apply zseps_pg; [exact (NoDup_app_remove_r _ _ ND)| intros x Hx; exact (proj1 (INA x Hx))].
    - constructor.
      + apply Forall_forall. intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
        * apply in_map_iff in Hy as (o & <- & Ho). apply ri_apart; apply INB; exact Ho.
        * apply in_app_iff in Hy as [Hy|Hy]; [exact (ri_fog y Hy)| exact (ri_sh y Hy)].
      + apply zseps_app.
        * apply zseps_pg; [exact (NoDup_app_remove_l _ _ ND)| intros x Hx; exact (proj1 (INB x Hx))].
        * apply zseps_app; [exact FOG_seps| exact sh3_seps| exact fog_sh].
        * intros x y Hx Hy. apply in_map_iff in Hx as (o & <- & Ho). apply in_app_iff in Hy as [Hy|Hy].
          -- apply zap_sym. apply FOG_apart; [exact Hy| exact (proj1 (INB o Ho))].
          -- apply pg_sh; [exact (proj1 (INB o Ho))| exact Hy].
    - intros x y Hx Hy. apply in_map_iff in Hx as (o & <- & Ho). destruct Hy as [<-|Hy].
      + apply zap_sym. apply ri_apart; apply INA; exact Ho.
      + apply in_app_iff in Hy as [Hy|Hy].
        * apply in_map_iff in Hy as (o' & <- & Ho'). apply pg_apart; [exact (proj1 (INA o Ho))| exact (proj1 (INB o' Ho'))|].
          (* [comment removed for export] *)
          intros E. clear - Ho Ho' E. destruct o as [a la], o' as [b lb]. cbn [fst] in E. subst b. cbn in Ho, Ho'. intuition congruence.
        * apply in_app_iff in Hy as [Hy|Hy].
          -- apply zap_sym. apply FOG_apart; [exact Hy| exact (proj1 (INA o Ho))].
          -- apply pg_sh; [exact (proj1 (INA o Ho))| exact Hy].
  Qed.

  #[using="HCN HAC FOG_ok FOG_len TF_ok FOG_seps FOG_apart"] Lemma tr_nodup : List.NoDup (tr_of h0).
  Proof. apply (NoDup_map_inv tz). apply zseps_NoDup; [exact TZ_seps| exact tr_pos]. Qed.

  #[using="HCN HAC FOG_ok FOG_len TF_ok FOG_seps FOG_apart"] Lemma tr_pair : ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "Pt1,$3;.Pt2,$3;.P,(35.$3;.R2.(3<.Vh0,))P,(35.$3;.R2.(3<.Vh0,))(37.(33.$3;.R4.R3.)(37.(30.(4=.R4.)(4>.R3.))(30.(4=.R3.)(4>.R4.))))")
(* [comment removed for export] *).
  Proof.
    intros t1 t2 H1 H2.
    destruct (zseps_In _ (tz t1) (tz t2) TZ_seps (in_map _ _ _ H1) (in_map _ _ _ H2)) as [E|D].
    - left. apply (NoDup_map_In_inj tz (tr_of h0)); [| exact H1| exact H2| exact E]. apply zseps_NoDup; [exact TZ_seps| exact tr_pos].
    - right. unfold zap, tz, t_hi in *. cbn [fst snd] in D. exact D.
  Qed.

  (* [comment removed for export] *)
  Local Ltac trA v len := left; exists (v, len); eexists; split; [cbn; tauto| split; [reflexivity| discriminate]].
  Local Ltac trB v len := right; right; left; exists (v, len); eexists; split; [cbn; tauto| reflexivity].
  Local Ltac trS lo len := right; right; right; right; exists (lo, len); eexists; split; [cbn; tauto| reflexivity].
  #[using="TF_ok"] Lemma tr_cases : ltac2:(CDefT.buildp (gd_tbl_AH0Vwf ()) "Pt,$3;.P,(35.$3;.R1.(3<.Vh0,))(37.(38.(1.$2.$3.)Lo,(1.$2.$3.)(38.$39.Lk,$39.(2=.(35.(1.$2.$3.)R2.(27.(1.$2.$3.)$28.$29.))(2=.(33.$3;.R4.(41.(36.Vp,(1>.$2.$3.R2.))(1?.$2.$3.R2.)R1.$43.$43.))(4?.(33.$39.R1.$48.))))))(37.(33.$3;.R2.(3?.(40.Vbp,)))(37.(38.(1.$2.$3.)Lo,(1.$2.$3.)(38.$39.Lk,$39.(2=.(35.(1.$2.$3.)R2.(27.(1.$2.$3.)$28.$29.))(33.$3;.R4.(41.(36.Vp,(1>.$2.$3.R2.))(1?.$2.$3.R2.)R1.$43.$45.)))))(37.(38.(1.$3.$3.)Lr,(1.$3.$3.)(38.$39.Lk,$39.(2=.(35.(1.$3.$3.)R2.VFOG,)(33.$3;.R4.(41.(1>.$3.$3.R2.)(1?.$3.$3.R2.)R1.$43.$45.)))))(38.(1.$3.$3.)Ls,(1.$3.$3.)(38.$39.Lk,$39.(2=.(35.(1.$3.$3.)R2.$4<.)(33.$3;.R4.(41.(1>.$3.$3.R2.)(1?.$3.$3.R2.)R1.$43.$45.)))))))))")
(* [comment removed for export] *).
  Proof.
    intros t Ht. destruct tr_of_h0 as [K E]. rewrite E in Ht. clear E. unfold EXTRA in Ht. rewrite map_app in Ht. cbn [map] in Ht.
    apply in_app_iff in Ht as [Ht|Ht].
    { destruct Ht as [<-|[<-|[<-|[]]]]; [trA v_dnodes 0x100000| trA v_dstore 0x800000| right; left; reflexivity]. }
    apply in_app_iff in Ht as [Ht|Ht].
    { destruct Ht as [<-|[<-|[<-|[<-|[]]]]]; [trA v_thr 0x1000| trA v_treg 0x10000| trA v_fstk 0xb09000| trA v_dtls 0x1000]. }
    apply in_app_iff in Ht as [Ht|Ht].
    { apply in_app_iff in Ht as [Ht|Ht].
      - destruct Ht as [<-|[<-|[<-|[<-|[<-|[]]]]]]; [trB v_lla 0x10000| trB v_ictx 0x38e000| trB v_tvec 0x1000| trB v_gvec 0x1000| trB v_divec 0x1000].
      - apply in_map_iff in Ht as (r & <- & Hr). right; right; right; left. dexists r, (K (snd r)). auto. }
    destruct Ht as [<-|[<-|[<-|[]]]]; [trS 0x7fff7000 0x10000000| trS 0x8fff7000 0x20000000000| trS 0x2008fff7000 0xdfff0001000].
  Qed.

  (* [comment removed for export] *)
  #[using="HCN HAC STKHI_gt FOG_len"] Lemma stk64_facts : ACEIL <= stk64 (L0_of bp) /\ stk64 (L0_of bp) <= STKHI.
  Proof.
    pose proof r_s1' as S1. pose proof r_s2' as S2.
    unfold stk64. cbn [L0_of l_stk_lo bp bp_of bp_sp0]. fold (SP p). rewrite HAC. unfold STKPG.
    pose proof (Z.div_mod (uv p v_s2) 256 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound (uv p v_s2) 256 ltac:(lia)) as M1.
    set (q := uv p v_s2 / 256) in *. set (r := uv p v_s2 mod 256) in *.
    pose proof (Z.div_mod r 4 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound r 4 ltac:(lia)) as M2.
    set (q' := r / 4) in *. set (r' := r mod 4) in *.
    assert (E : (SP p - 2 ^ 23) mod 64 = 16 * r').
    { unfold SP. replace (32768 * uv p v_s1 + 16 * uv p v_s2 - 2 ^ 23) with (16 * r' + (512 * uv p v_s1 + 64 * q + q' - 2 ^ 17) * 64) by lia.
      rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
    rewrite E. unfold SP in *. clear E. clearbody q r q' r'. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HCN HAC STKHI_gt STKHI_pg STKHI_47 STKHI_len FOG_ok FOG_len TF_ok FOG_seps FOG_apart"] Theorem h0_vwf : vwf AL0 (vst_of h0).
  Proof.
    pose proof aceil_bounds as AB. dpose ri_hull as (R1 & R2 & R3). pose proof ri_high as R4.
    dpose (pg_single v_prim 0x2000011000 ltac:(pv)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7).
    dpose (pg_single v_secv 0x800000 ltac:(pv)) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7).
    unfold vwf. cbn [v_tr v_hulls v_ghost v_stk v_img v_eb vst_of hulls_of al_img_lo al_img_hi AL0 fst snd].
    change (h_L h0) with (L0_of bp). unfold hulls_of.
    change (l_b6 (L0_of bp)) with (PG p v_prim). change (l_pa (L0_of bp)) with (PG p v_secv). change (l_stk_hi (L0_of bp)) with STKHI.
    change (a_sech (h_acct h0)) with (@nil (Z * Z)).
    split. { (* [comment removed for export] *)
      apply Forall_forall. intros t Ht. pose proof (TZ_single (tz t) (in_map _ _ _ Ht)) as (A1 & A2 & A3 & A4 & A5 & A6). unfold tz, t_hi in *. cbn [fst snd] in A1, A2, A3, A4, A5, A6.
      repeat match goal with |- _ /\ _ => split end; try assumption.
      destruct (tr_cases t Ht) as [(o & k & Ho & -> & Hk)|[->|[(o & k & Ho & ->)|[(r & k & Hr & ->)|(s & k & Hs & ->)]]]]; cbn [t_cs t_kind ri_tr]; intros C;
        first [exact Hk | discriminate | discriminate C]. }
    split. { exact tr_pair. }
    split. { (* [comment removed for export] *)
      unfold kPrimHullLen, kPaHullLen. constructor; [cbn [fst snd]; repeat split; first [assumption | reflexivity | lia]|].
      constructor; [cbn [fst snd]; repeat split; first [assumption | reflexivity | lia]| apply Forall_nil]. }
    split. { (* [comment removed for export] *)
      intros H1 H2 HH1 HH2. unfold kPrimHullLen, kPaHullLen in *.
      pose proof (pg_apart (v_prim, 0x2000011000) (v_secv, 0x800000) ltac:(pv) ltac:(pv) ltac:(cbn; discriminate)) as D. unfold zap, pgz in D. cbn [fst snd] in D.
      destruct HH1 as [<-|[<-|[]]]; destruct HH2 as [<-|[<-|[]]]; cbn [fst snd]; first [left; reflexivity | right; lia]. }
    split. { (* [comment removed for export] *)
      intros t H Ht HH. unfold kPrimHullLen, kPaHullLen in HH.
      assert (CASE : forall x, In x (map tz (tr_of h0)) -> x = RIz \/ (zap x (pgz (v_prim, 0x2000011000)) /\ zap x (pgz (v_secv, 0x800000)))).
      { intros x Hx. destruct (TZ_in x Hx) as [(o & Ho & ->)|[->|[Hf|Hs]]].
        - right. pose proof (trpg_facts o Ho) as [Io NP]. split; (apply pg_apart; [exact Io| pv|]); cbn [fst]; [exact NP|].
          intros E. clear - Ho E. destruct o as [v len]. cbn [fst] in E. subst v. cbn in Ho. intuition discriminate.
        - left. reflexivity.
        - right. split; (apply FOG_apart; [exact Hf| pv]).
        - right. split; (apply zap_sym; apply pg_sh; [pv| exact Hs]). }
      destruct (CASE (tz t) (in_map _ _ _ Ht)) as [E|[D1 D2]].
      - (* [comment removed for export] *)
        assert (Et : t = ri_tr (L0_of bp)).
        { destruct (tr_cases t Ht) as [(o & k & Ho & -> & Hk)|[->|[(o & k & Ho & ->)|[(r & k & Hr & ->)|(s & k & Hs & ->)]]]]; try reflexivity; exfalso;
            unfold tz, RIz in E; cbn [t_lo t_len fst snd] in E; injection E as E1 E2.
          + pose proof (ri_apart o (proj1 (trpg_facts o Ho)) (proj2 (trpg_facts o Ho))) as D. unfold zap, RIz, pgz in D. cbn [fst snd] in D.
            destruct o as [v len]. cbn [fst snd] in E1, E2, D. pose proof (pg_single v len (proj1 (trpg_facts _ Ho))) as (_ & _ & Lp & _). lia.
          + pose proof (ri_apart o (proj1 (trpg_facts o Ho)) (proj2 (trpg_facts o Ho))) as D. unfold zap, RIz, pgz in D. cbn [fst snd] in D.
            destruct o as [v len]. cbn [fst snd] in E1, E2, D. pose proof (pg_single v len (proj1 (trpg_facts _ Ho))) as (_ & _ & Lp & _). lia.
          + pose proof (ri_fog r Hr) as D. pose proof (proj1 (Forall_forall _ _) FOG_ok r Hr) as (_ & P & _). unfold zap, RIz in D. cbn [fst snd] in D. lia.
          + pose proof (ri_sh s Hs) as D. dpose (sh3_facts s Hs) as (S1 & S2 & S3). unfold zap, RIz in D. cbn [fst snd] in D. lia. }
        subst t. unfold t_hi. destruct HH as [<-|[<-|[]]]; cbn [fst snd t_lo t_len t_lit t_kind ri_tr].
        + left. unfold ri_base, space_end, kSpaceSize. cbn [L0_of l_sb bp bp_of bp_sb]. fold (SB p). fold RI. repeat split; lia || reflexivity.
        + right. pose proof (ri_apart (v_secv, 0x800000) ltac:(pv) ltac:(cbn; discriminate)) as D. unfold zap, RIz, pgz in D. cbn [fst snd] in D.
          unfold ri_base, space_end, kSpaceSize. cbn [L0_of l_sb bp bp_of bp_sb]. fold (SB p). fold RI. lia.
      - right. unfold zap, tz, pgz, t_hi in *. cbn [fst snd] in D1, D2. destruct HH as [<-|[<-|[]]]; cbn [fst snd]; lia. }
    split. { exact (proj1 stk64_facts). } split. { exact (proj2 stk64_facts). } split. { exact STKHI_47. }
    split. { reflexivity. } split. { reflexivity. } split. { lia. } split. { lia. } split. { lia. }
    split. { (* [comment removed for export] *) cbn [app]. exact (proj1 (gsh_ok p HCN STKHI FOG TF)). }
    split. { (* [comment removed for export] *)
      intros t Ht C.
      destruct (tr_cases t Ht) as [(o & k & Ho & -> & Hk)|[->|[(o & k & Ho & E)|[(r & k & Hr & E)|(s & k & Hs & E)]]]];
        [| | subst t; discriminate C| subst t; discriminate C| subst t; discriminate C].
      - destruct o as [v len]. unfold t_hi. cbn [fst snd t_lo t_len]. pose proof (pg_single v len (proj1 (trpg_facts _ Ho))) as (_ & _ & _ & _ & _ & B & _). exact B.
      - right. unfold t_hi, ri_tr, ri_base, space_end, kSpaceSize. cbn [t_lo t_len L0_of l_sb bp bp_of bp_sb]. fold (SB p). fold RI. lia. }
    split. { (* [comment removed for export] *)
      unfold eb_of, E0, kDepotBlockBytes, h0, bp. cbn.
      match goal with |- context [AFreeSlot.zsum ?f ?l] => pose proof (AFreeSlot.zsum_nonneg f l ltac:(intros; lia)) end. lia. }
    split. { exact tr_nodup. }
    (* [comment removed for export] *)
    pose proof (proj1 (L0_wf p HCN STKHI FOG TF HAC STKHI_gt STKHI_pg STKHI_47 STKHI_len FOG_ok)) as WL0. fold bp in WL0.
    change (units_of_L (L0_of bp)) with (units_of_L (L0_of bp)).
    assert (HAP0 : l_b6 (L0_of bp) + kPrimHullLen <= l_pa (L0_of bp) \/ l_pa (L0_of bp) + kPaHullLen <= l_b6 (L0_of bp)).
    { change (l_b6 (L0_of bp)) with (PG p v_prim). change (l_pa (L0_of bp)) with (PG p v_secv). unfold kPrimHullLen, kPaHullLen.
      pose proof (pg_apart (v_prim, 0x2000011000) (v_secv, 0x800000) ltac:(pv) ltac:(pv) ltac:(cbn; discriminate)) as D. unfold zap, pgz in D. cbn [fst snd] in D. lia. }
    split. { intros U n HU. exact (units_of_L_wf (L0_of bp) U n WL0 HU). }
    split. { intros U n U' n' HU HU'. exact (units_of_L_sep (L0_of bp) WL0 HAP0 U n U' n' HU HU'). }
    split. { intros H HH x Hx. apply (units_of_L_cover (L0_of bp) H x WL0); [| exact Hx].
             unfold hulls_of. change (l_b6 (L0_of bp)) with (PG p v_prim). change (l_pa (L0_of bp)) with (PG p v_secv). exact HH. }
    (* [comment removed for export] *)
    intros t U n Ht TL HU.
    pose proof (units_of_L_inside (L0_of bp) U n WL0 HU) as INS. pose proof (proj1 (units_of_L_wf (L0_of bp) U n WL0 HU)) as NP.
    change (l_b6 (L0_of bp)) with (PG p v_prim) in INS. change (l_pa (L0_of bp)) with (PG p v_secv) in INS. unfold kPrimHullLen, kPaHullLen in INS.
    assert (CASE : forall x, In x (map tz (tr_of h0)) -> x = RIz \/ (zap x (pgz (v_prim, 0x2000011000)) /\ zap x (pgz (v_secv, 0x800000)))).
    { intros x Hx. destruct (TZ_in x Hx) as [(o & Ho & ->)|[->|[Hf|Hs]]].
      - right. pose proof (trpg_facts o Ho) as [Io NPo]. split; (apply pg_apart; [exact Io| pv|]); cbn [fst]; [exact NPo|].
        intros E. clear - Ho E. destruct o as [v len]. cbn [fst] in E. subst v. cbn in Ho. intuition discriminate.
      - left. reflexivity.
      - right. split; (apply FOG_apart; [exact Hf| pv]).
      - right. split; (apply zap_sym; apply pg_sh; [pv| exact Hs]). }
    destruct (CASE (tz t) (in_map _ _ _ Ht)) as [E|[D1 D2]].
    - (* [comment removed for export] *)
      exfalso. destruct (tr_cases t Ht) as [(o & k & Ho & -> & Hk)|[->|[(o & k & Ho & ->)|[(r & k & Hr & ->)|(s' & k & Hs & ->)]]]];
        unfold tz, RIz in E; cbn [t_lo t_len fst snd t_lit ri_tr] in E, TL; try discriminate TL.
      + injection E as E1 E2. pose proof (ri_apart o (proj1 (trpg_facts o Ho)) (proj2 (trpg_facts o Ho))) as D. unfold zap, RIz, pgz in D. cbn [fst snd] in D.
        destruct o as [v len]. cbn [fst snd] in E1, E2, D. pose proof (pg_single v len (proj1 (trpg_facts _ Ho))) as (_ & _ & Lp & _). lia.
      + injection E as E1 E2. pose proof (ri_apart o (proj1 (trpg_facts o Ho)) (proj2 (trpg_facts o Ho))) as D. unfold zap, RIz, pgz in D. cbn [fst snd] in D.
        destruct o as [v len]. cbn [fst snd] in E1, E2, D. pose proof (pg_single v len (proj1 (trpg_facts _ Ho))) as (_ & _ & Lp & _). lia.
      + injection E as E1 E2. pose proof (ri_fog r Hr) as D. pose proof (proj1 (Forall_forall _ _) FOG_ok r Hr) as (_ & P & _). unfold zap, RIz in D. cbn [fst snd] in D. lia.
      + injection E as E1 E2. pose proof (ri_sh s' Hs) as D. dpose (sh3_facts s' Hs) as (S1 & S2 & S3). unfold zap, RIz in D. cbn [fst snd] in D. lia.
    - unfold zap, tz, pgz, t_hi in *. cbn [fst snd] in D1, D2. clear - D1 D2 INS NP. lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HCN HAC STKHI_gt FOG_ok FOG_len TF_ok"] Theorem h0_vranges : vranges_ok AL0 (vst_of h0).
  Proof.
    unfold vranges_ok, csranges, lazyranges. cbn [al_sb AL0 v_stk v_img v_tr v_ghost vst_of fst snd].
    change (h_L h0) with (L0_of bp). change (l_stk_hi (L0_of bp)) with STKHI. change (a_sech (h_acct h0)) with (@nil (Z * Z)).
    pose proof stk64_facts as [K1 K2]. pose proof aceil_bounds as AB.
    split; [lia|]. split.
    - constructor; [cbn [fst snd]; lia|]. constructor; [cbn [fst snd]; lia|]. apply Forall_app. split.
      + apply Forall_forall. intros r Hr.
        apply in_map_iff in Hr as (t & <- & Ht). apply filter_In in Ht as [Ht _]. cbn [fst snd].
        pose proof (TZ_single (tz t) (in_map _ _ _ Ht)) as (A1 & A2 & _). unfold tz in *. cbn [fst snd] in A1, A2. lia.
      + (* [comment removed for export] *) cbn [app]. pose proof (proj1 (gsh_ok p HCN STKHI FOG TF)) as G. apply Forall_forall. intros r Hr.
        pose proof (proj1 (Forall_forall _ _) G r Hr) as (G1 & G2 & _). split; [exact G1| exact G2].
    - apply Forall_forall. intros r Hr. apply in_map_iff in Hr as (t & <- & Ht). apply filter_In in Ht as [Ht _]. cbn [fst snd].
      pose proof (TZ_single (tz t) (in_map _ _ _ Ht)) as (A1 & A2 & _). unfold tz in *. cbn [fst snd] in A2. lia.
  Qed.
End Vwf.
