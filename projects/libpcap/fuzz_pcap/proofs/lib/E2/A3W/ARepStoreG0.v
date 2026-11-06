(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3g0__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepStore__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_tailg. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_acalloc_iseg__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_tailg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wn sp t c AB UB PGE n nodes store :=
  ([(sp - 4096, sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + n); (AB, AB + 16); (shad UB, PGE);
    (ADEPOT_LO, ADEPOT_HI); (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := solve [fu_focus; lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->      (* [comment removed for export] *)
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6303744 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6303744 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
Section KindsG.
Variables (sp t c AB S UB PGE n nodes store res ctx lo grz ssz : Z).
(* [comment removed for export] *)
Definition kfactsG : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (1 <= c <= 30)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ UB - 16 >= AB /\ 1 <= n /\ UB + n <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ shad UB + 1 <= PGE /\ PGE <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6303744 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6303744 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6303744 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfactsG.

(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with UB => constr:(res) | AB => constr:(res) | _ => X end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.
Ltac kind1 := lazymatch goal with
  | |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in first [ solve [ kkeep2 X Y; klia ] | lia_rel | lia ]
  | |- _ => first [ lia_rel | lia ] end.
Ltac kind := pose proof KF as KF'; unfold kfactsG, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  (nd_pre KF' 8%nat; intros F_lo F_t F_c F_res F_slot F_sh F_ns F_ctx; nd_post);
  cbn [disjoint_from]; repeat (split; [kind1|]); first [ kind1 | exact I ].   (* [comment removed for export] *)

#[using="rc S res ctx lo grz ssz KF"] Lemma KG_img : forall A k, 0x10000 <= A -> 0 <= k -> (A + k <= ADEPOT_LO \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI)) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S res ctx lo grz ssz KF"] Lemma KG_low : forall A k, 2147450880 <= A -> A + k <= 2148238848 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S res ctx lo grz ssz KF"] Lemma KG_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S res ctx lo grz ssz KF"] Lemma KG_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ PGE <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S lo grz ssz KF"] Lemma KG_ctx : 
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S ctx lo grz ssz KF"] Lemma KG_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 208 + c * 80 \/ t + 208 + c * 80 + 4 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S ctx lo grz ssz KF"] Lemma KG_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= AB \/ (AB + 16 <= A /\ A + k <= UB - 16) \/ UB + n <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="S ctx lo grz ssz KF"] Lemma KG_obj : forall A k, ((6303744 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="S ctx lo grz ssz KF"] Lemma KG_objL : forall A k, ((A + k <= 65536 \/ 6303744 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.
End KindsG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_prim : forall (CI : list (Z * Z)) sp t c AB S UB PGE n nodes store res ctx lo grz ssz (LB : list ablock) m m',
  kfactsG sp t c AB S UB PGE n nodes store res ctx lo grz ssz ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI ->
  munch (Wn sp t c AB UB PGE n nodes store) m m' -> wmono asegs m m' ->
  (forall b, In b LB -> disjoint_from (Wn sp t c AB UB PGE n nodes store) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (Wn sp t c AB UB PGE n nodes store) (shad a') 1) ->
  PGE <= shad ATOP ->
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from (Wn sp t c AB UB PGE n nodes store) A k) ->      (* [comment removed for export] *)
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from (Wn sp t c AB UB PGE n nodes store) (shad a') 1) ->                  (* [comment removed for export] *)
  disjoint_from (Wn sp t c AB UB PGE n nodes store) AIMSH_LO AIMSH_LEN ->                                                          (* [comment removed for export] *)
  disjoint_from (Wn sp t c AB UB PGE n nodes store) AAHMv AAHM_SZ ->                                                          (* [comment removed for export] *)
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t c AB S UB PGE n nodes store res ctx lo grz ssz LB m m' KF CIOK MU WM HBK HFK PSP TLSK TLSS IMSH AHMK a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  destruct CL as [CL|TL]; [| exact (aextra_outside _ a TLSK TLSS IMSH AHMK TL)].
  pose proof KF as KF'. (nd_pre KF' 8%nat; intros F_lo F_t F_c F_res F_slot F_sh F_ns F_ctx; nd_post).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - eapply disjoint_outside; [eapply (KG_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (KG_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
  - (nd_pre BLK 3%nat; intros b Hb R; nd_post). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (KG_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: clear -ST SD SDs F_sh PSP; Z.div_mod_to_equations; lia.
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (KG_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; Z.div_mod_to_equations; lia.
    + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed.

#[using="Type"] Lemma b1'_range : forall b1, 0 <= b1 -> 0 <= Z.lor (Z.land (hdr_b1_mid b1) 243) 0 < 256.
Proof.
  intros b1 Hb. rewrite Z.lor_0_r. pose proof (hdr_b1_mid_range b1 Hb) as [R0 R1].
  assert (A0 : 0 <= Z.land (hdr_b1_mid b1) 243) by (apply Z.land_nonneg; right; lia).
  split; [exact A0|].
  destruct (Z.eq_dec (Z.land (hdr_b1_mid b1) 243) 0) as [->|NZ]; [lia|].
  change 256 with (2^8). apply lt_pow2_of_log2; [lia|].
  pose proof (Z.log2_land (hdr_b1_mid b1) 243 R0 ltac:(lia)) as L1.
  replace (Z.log2 243) with 7 in L1 by reflexivity. lia.
Qed.

#[using="Type"] Lemma b1'_at1 : forall b1, 0 <= b1 < 256 -> Z.land (Z.lor (Z.land (hdr_b1_mid b1) 243) 0) 3 = 1.
Proof.
  intros b1 Hb.
  assert (C : forallb (fun i => Z.land (Z.lor (Z.land (hdr_b1_mid (Z.of_nat i)) 243) 0) 3 =? 1) (seq 0 256) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C (Z.to_nat b1) ltac:(apply in_seq; lia)) as C1. cbn beta in C1.
  rewrite Z2Nat.id in C1 by lia. apply Z.eqb_eq. exact C1.
Qed.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition store_primU_stmt (DI : ADepotIface) (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop)
    (CI : list (Z * Z)) : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (n lo c cnt k b1 : Z) (maxc csz : word) (ub : list byte),
  let S := size_of_class c in let AB := aslot_addr L c k in let UB := AB + rz_size n in let PG := shad UB + shlen (n - n mod 8) in
  alayout_ok L -> arng L RNG st -> AREP (AH DI AQ ASEC AFK) L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n -> is_primary n = true -> class_id (needed_size n) = c -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None -> 0 <= k < ndist st c ->
  maxc = Z_to_bv 64 (max_count st c) -> csz = Z_to_bv 64 S -> 0 <= b1 < 256 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  (16 < rz_size n -> junk_at m (AB + 16) (rz_size n - 32)) ->
  junk_at m (UB + n) (S - rz_size n - n) ->
  fill_at m (shad AB + 1) (shlen (rz_size n) - 1) 0xfa ->
  fill_at m (PG + (if n mod 8 =? 0 then 0 else 1)) (shlen S - shlen (rz_size n) - shlen (n - n mod 8) - (if n mod 8 =? 0 then 0 else 1)) 0xfa ->
  junk_at m (al_t L + 2768) 16 -> junk_at m (al_t L + 2792) 8 ->
  forall ms',
    malloc_post_genU DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG (if n mod 8 =? 0 then 0 else 1) lo b1 maxc csz ub m ms' ->
    amalloc_postU CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m ub
      (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
         (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)), Some (a_next st)) RNG ms'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Definition store_primU__stmt : Prop := store_primU_stmt DI AQ ASEC AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 23).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 24).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 25).
Variable c : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 26).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 27).
Variable k : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 28).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 29).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 30).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 31).
Variable ub : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 32).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let grz := shlen (rz_size n).
Let g := shlen (n - n mod 8).
Let room := if n mod 8 =? 0 then 0 else 1.
Let PG := shad UB + g.
Let b1' := Z.lor (Z.land (hdr_b1_mid b1) 243) 0.
#[using="HL CI_OK S AB UB grz g room PG b1'"] Lemma store_primU__body : ltac:(let T := type of (fun (h : store_primU__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X n lo c cnt k b1 maxc csz ub) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (n, (lo, (c, (cnt, (k, (b1, (maxc, (csz, ub))))))))))))))))))))))))))))))))) as _.
  unfold store_primU_stmt.  cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM HC0 HCNT POS NK NB KR HMX HCSZ B1 CEIL LO LHJ TL SHpre SHsuf CSa CSc ms' PM.
  clear SHpre SHsuf. unfold AMALLOC_STACK in LO.
  (* [comment removed for export] *)
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N PRIM HC0) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ SZM16 SMALL MCB; nd_post).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post). clear CL5.
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post). clear DL9 DL10.
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post). (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros _ _ [kC CBND]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros _ _ [kN NBND]; nd_post). (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros _ _ [kS SBND]; nd_post). unfold AIMG_HI in DL3, DL6, CL3.
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t.
  word_range sp SPR.
  assert (CIN : a_cinit st = true).
  { unfold max_count in CNTB. destruct (a_cinit st); [reflexivity| exfalso]. rewrite HCNT in CNTB. clear -CNTB POS. lia. }
  assert (MC16 : max_cached c <= 16) by (clear -MCB; lia).
  assert (CNT16 : 0 < cnt <= 16) by (unfold max_count in CNTB; rewrite CIN, HCNT in CNTB; clear -CNTB POS MC16; lia).
  (* [comment removed for export] *)
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB SZM _ _; nd_post).
  chg (size_of_class c) S.
  (pose proof (slot_in_region L st c k ltac:(clear -SZB; subst S; lia) (proj1 A1) KR) as ndP__; nd_pre ndP__ 3%nat; intros G5 G4 KS0; nd_post). fold S in G5, G4, KS0.
  chg (aslot_addr L c k) AB.
  assert (G1 : al_space_beg L <= AB) by (unfold aregion, K_REGION in G5; clear -G5 C16; lia).
  assert (G2 : AB + S <= al_space_beg L + K_SPACE_SIZE).
  { unfold aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. generalize G4 A1 A2 C16; clear; intros. change (2^37) with 137438953472. lia. }
  assert (G3 : AB mod 16 = 0) by (subst AB; apply slot_aligned; [exact SAL| exact HCK]).
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  chg (AB + rz_size n) UB. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  chg (shlen (rz_size n)) grz. chg (shlen (n - n mod 8)) g. chg (if n mod 8 =? 0 then 0 else 1) room.
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8) by (subst grz g; rewrite !shlen_div; split; reflexivity).
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (RMQ : room = (if n mod 8 =? 0 then 0 else 1)) by reflexivity. clearbody room.
  assert (GR5 : 0 <= room <= 1) by (rewrite RMQ; clear; destruct (n mod 8 =? 0); lia).
  assert (SS8 : shlen S = S / 8) by (rewrite shlen_div; reflexivity).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2, SS8, RMQ. generalize NSZ NS RSR RSM SZM RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. rewrite !shad_div. generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations; lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000 /\ shad AB + shlen S = shad (AB + S)).   (* [comment removed for export] *)
  { rewrite SS8, !shad_div. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 G3 SP1 SP2 SZB SZM ES. clear. intros. Z.div_mod_to_equations. lia. }
  (nd_pre GR89 3%nat; intros GR8 GR9 GR10; nd_post).
  chg (shad UB + g) PG.
  assert (PGE_ : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (ROOM : granules n = g + room) by (subst g; rewrite RMQ; apply granules_eq; clear -N; lia).
  assert (GR11 : 1 <= g + room).
  { subst g. rewrite RMQ, shlen_div. generalize N; clear; intros. destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104
      /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ UB + n <= xb_alloc L b)
      /\ xb_alloc L b mod 16 = 0 /\ 16 <= size_of_class (xb_class b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc. split; [| split; [| split; [| split; [apply slot_aligned; [exact SAL| exact CLB] | clear -QS; lia]]]].
    - unfold aregion, K_REGION in P5. clear -P5 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    - unfold aregion, K_REGION, K_FREEARR_OFF in *. clear -P4 Q1 Q2 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
      + rewrite EC in *. assert (NKb : xb_slot b <> k).
        { intros EK. enough (busy_of X c k <> None) by congruence. unfold busy_of.
          destruct (List.find _ _) eqn:FE; [discriminate|]. exfalso.
          apply (find_none _ _ FE) in Hb. rewrite EC, EK, !Z.eqb_refl in Hb. discriminate. }
        destruct (slots_disjoint L c (xb_slot b) k ltac:(clear -KB; lia) ltac:(clear -KR; lia) NKb ltac:(clear -SZB; lia)) as [D|D];
          rewrite <- EAB in D; fold S in D; [left; exact D| right].
        clear -D EUB RZR N NSZ NS RSR ES. subst S. lia.
      + assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
        unfold K_REGION, K_FREEARR_OFF in *.
        destruct (proj1 (Z.lt_gt_cases (xb_class b) c) NC) as [LT|GT]; [left | right].
        * specialize (RC _ _ LT). clear -RC P4 Q1 Q2 G5. lia.
        * specialize (RC _ _ GT). clear -RC P5 G4 A1 A2 EUB N NSZ NS RSR RZR ES. subst S. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 19%nat; intros id t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' stj' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 16%nat; intros MU WM MI' ST' IDR CR' STS' STATS' LSJ' UW' HDR' UF' LH' SHU' SHP' DEP'; nd_post).
  (* [comment removed for export] *)
  assert (MUn : munch (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. subst PG. generalize GR3 GR4 GR5 GR7. clear. intros. lia. }
  clear MU.
  assert (KF : kfactsG (bv_unsigned sp) (al_t L) c AB S UB (PG + room) n (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo grz (shlen S)).
  { unfold kfactsG. subst PG. unfold AMALLOC_STACK, K_SPACE_SIZE in *. change (2^37) with 137438953472 in G2.
    generalize CEIL LO TL1 TL2 TL4 C16 RES RHI RSP G1 G2 EUB RZR N NSZ NS RSR ES GR8 GR7 GR3 GR4 GR5 GR6 GR9 GR11 DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.
    repeat split; first [lia | assumption | match goal with |- ?G => idtac "KF-LEFT" G end]. }   (* [comment removed for export] *)
  pose proof (KG_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KG_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KG_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KG_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KG_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_c_t) (unbx D_c_res) (unbx D_c_n) (unbx D_c_s)) as Kctx.
  pose proof (KG_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx DL7) (unbx DL8)) as Kt.
  pose proof (KG_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx D_n_res) (unbx D_s_res)) as Kres.
  pose proof (KG_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KG_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  change (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st)) (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)))
    with (st_fast st c n cnt).
  chg (Z.lor (Z.land (hdr_b1_mid b1) 243) 0) b1'.
  pose proof (b1'_range b1 ltac:(clear -B1; lia)) as B1R. fold b1' in B1R.
  set (X' := xfast X c k n (a_next st) b1' id).
  (pose proof (st_fast_fields st c n cnt) as ndP__; nd_pre ndP__ 11%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11; nd_post).
  (* [comment removed for export] *)
  assert (WF' : awf L (st_fast st c n cnt) X').
  { apply awf_fast; [exact WF | exact HCK | exact HCNT | exact POS | exact NK | exact NB | clear -N NS NSR RSR RZR; unfold AREQMAX; lia | | exact B1R | apply b1'_at1; clear -B1; lia | clear -IDR; lia].
    fold S. clear -NS NSZ. lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L (st_fast st c n cnt) m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact E3 | exact E4 | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (THR' : athread L (st_fast st c n cnt) X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      + destruct (CACHES c HCK) as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        (pose proof (st_fast_counters st c n cnt c) as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ _ EC5; nd_post). rewrite Z.eqb_refl in EC5.
        rewrite EC5, st_fast_max_count, E5, CIN. unfold X'. rewrite xfast_cls, Z.eqb_refl. cbn [xc_cache].
        exists (Z_to_bv 64 (acompact c k) :: tail).
        assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
        { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC HCNT. lia. }
        split; [| split].
        * unfold acache_addr. rewrite HMX, HCSZ in CR'. fold S. exact CR'.
        * eapply u32arr_frame; [| exact MUn | exact WM |].
          -- rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
          -- rewrite length_app, length_map. cbn [length]. unfold acache_addr.
             assert (LRL : (length (removelast (xc_cache (x_cls X c))) + Datatypes.S (length tail) = 16)%nat).
             { rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia. }
             rewrite LRL. apply Kt; clear -C16; lia.
        * cbn [length]. rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | | exact E5 | |].
        * (pose proof (st_fast_counters st c n cnt c') as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ _ EC5; nd_post). rewrite EC5. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold acache_addr. unfold K_NUM_CLASSES in Hc'. apply Kt; clear -C16 Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact CSa | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [exact CSc | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (UBN : AB + 16 <= UB /\ UB + n <= AB + S) by (clear -EUB RZR N NSZ NS RSR; lia).
  assert (PGB : PG + room <= shad (AB + S)) by (subst PG; rewrite GR7, <- GR10; clear -GR6; lia).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L (st_fast st c n cnt) m' c'' /\ afreearray L (st_fast st c n cnt) X' m' c''
      /\ aslots L (st_fast st c n cnt) X' m' c'' /\ aslot_shadow L (st_fast st c n cnt) X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    (pose proof (st_fast_counters st c n cnt c'') as ndP__; nd_pre ndP__ 5%nat; intros EC1 EC2 EC3 EC4 EC5; nd_post).
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    (* [comment removed for export] *)
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC3 | exact EC4 | exact EC2 | exact EC1 |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; clear -Hc'' RSP G2 EUB NSZ NS RSR RZR N; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC3 | exact EC4 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c'' c) as [->|_]; reflexivity.
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *.
        * clear -RI1. lia.
        * clear -RI2 RI3 Q6. lia.
        * clear -Q5 Q6; lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right; right. clear -G4 A1 A2 UBN. lia.
          -- destruct (SIDE NE) as [D|D]; [left; clear -D Q6; lia | right; right; clear -D UBN; lia].
      + apply Kshad.
        * rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF in *. clear -RI1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -RI2 RI3 Q6 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2. lia.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia].
                unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q6 UBN. lia.
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslots_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SLOTS | apply st_fast_ndist | exact EC2 | exact EC1 | | |].
      + intros k'' Hk'' NEk. (pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [| split].
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kres; [clear -P5 RI1; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -QS; lia |].
          destruct (Z.eqb_spec c'' c) as [->|NE].
          -- destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D;
               [left; exact D | right; right; clear -D EUB RZR N NSZ NS RSR ES; subst S; lia].
          -- destruct (SIDE NE) as [D|D]; [left; clear -D P4 Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D P5 UBN; lia].
        * intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|].
          exact (awf_fits L st X b WF IB).
      + intros POS''. apply Kres; [clear -Q1 RI1; unfold aregion in *; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -POS''; lia |].
        destruct (Z.eqb_spec c'' c) as [->|NE]; [right; right; clear -G4 UBN; lia|].
        destruct (SIDE NE) as [D|D]; [left; clear -D Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D Q1 UBN; lia].
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb].
        unfold aslot_busy, bnew. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot xb_alloc xb_user xb_hdr].
        unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n]. rewrite <- EAB. fold S. rewrite <- EUB.
        split; [| split].
        * intros R16. split.
          -- replace (UB - 16) with (UB + -16) by (clear; lia). unfold AMAGIC. exact (LH' R16).
          -- eapply junk_frame; [exact (LHJ R16) | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; clear -Hp R16 RZR G1 RSP G2 EUB RI3 N NSZ NS RSR; lia.
        * exists 2. split; [reflexivity|]. replace (UB - 16) with (UB + -16) by (clear; lia). exact HDR'.
        * replace (S - rz_size n) with (n + (S - rz_size n - n)) by (clear; lia).
          apply (junk_merge m' UB n (S - rz_size n - n)); [| | clear -N; lia | clear -NSZ NS RSR N; lia].
          -- pose proof (junk_of_cells m' _ _ UF') as J. cbn [cells_size csize] in J. rewrite Nat.add_0_r, Z2Nat.id in J by (clear -N; lia). exact J.
          -- eapply junk_frame; [exact TL | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; [| | clear -Hp; lia | right; right; clear; lia].
             ++ clear -G1 RSP EUB RZR N. lia.
             ++ clear -G2 RI3 EUB NSZ NS RSR N RZR. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SHADOW | apply st_fast_ndist | exact EC2 | exact EC1 | | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk'' NEk. (pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
        split.
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P5 RI1 RES RHI. Z.div_mod_to_equations. lia.
          -- rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -P4 Q1 Q2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
          -- apply shlen_nonneg. clear -QS; lia.
          -- destruct (Z.eqb_spec c'' c) as [->|NE].
             ++ destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D.
                ** left. apply shad_sep; [clear -D UBN; lia| clear -AL''; Z.div_mod_to_equations; lia].
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact D.
             ++ destruct (SIDE NE) as [D|D].
                ** left. apply shad_sep; [| clear -AL''; Z.div_mod_to_equations; lia]. unfold K_FREEARR_OFF, K_REGION in *. clear -D P4 Q1 Q2 UBN. lia.
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D P5. lia.
      + intros POS''. apply Kshad.
        * rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * destruct (Z.eqb_spec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact G4.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep.
                ** unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
                ** pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM. clear -AM RM''. Z.div_mod_to_equations. lia.
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb]. rewrite <- EAB. fold S.
        unfold slot_shadow_bytes, bnew. cbn [xb_n xb_st]. unfold block_shadow_bytes.
        change (shlen (rz_size n)) with grz. rewrite <- (shlen_floor n). change (shlen (n - n mod 8)) with g. rewrite ROOM.
        (* [comment removed for export] *)
        destruct SHADOW as [SHK _]. specialize (SHK k KR). rewrite NB in SHK. rewrite <- EAB in SHK. fold S in SHK. cbn [slot_shadow_bytes] in SHK.
        change (rw_cells asegs m (shad AB) [CB (Z.to_nat (shlen S)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S)))]) with (fill_at m (shad AB) (shlen S) 250) in SHK.
        destruct (fill_split m (shad AB) grz (shlen S - grz) 250 ltac:(replace (grz + (shlen S - grz)) with (shlen S) by (clear; lia); exact SHK)
                    ltac:(clear -GR3; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [F1 R1].
        destruct (fill_split m (shad AB + grz) (g + room) (shlen S - grz - (g + room)) 250
                    ltac:(replace (g + room + (shlen S - grz - (g + room))) with (shlen S - grz) by (clear; lia); exact R1)
                    ltac:(clear -GR4 GR5; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [_ F2].
        eapply fill_frame in F1; [| exact MUn | exact WM | intros _; apply Kshad; [clear -GR8; lia | clear -GR9 GR6 GR4 GR5 GR3; lia | clear -GR3; lia | left; clear -GR7; lia]].
        replace (shad AB + grz + (g + room)) with (PG + room) in F2 by (subst PG; clear -GR7; lia).
        eapply fill_frame in F2; [| exact MUn | exact WM | intros Hp; apply Kshad; [subst PG; clear -GR8 GR7 GR3 GR4 GR5; lia | clear -GR9 GR6 GR7 GR3 GR4 GR5 Hp; subst PG; lia | clear -Hp; lia | right; clear; lia]].
        unfold fill_at in F1, F2. change (shlen (n - n mod 8)) with g in SHU'.
        replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat grz)) in SHU' by (clear -GR7 GR3; lia).
        destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
        * assert (R0 : room = 0) by (rewrite RMQ; reflexivity). clearbody PG. subst room. rewrite app_nil_r.
          replace (PG + 0) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' F2)) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + Z.to_nat (shlen S - grz - (g + 0))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          exact FIN.
        * assert (RM1 : room = 1) by (rewrite RMQ; reflexivity). clearbody PG. subst room. specialize (SHP' M0). apply cb_of_C1 in SHP'.
          replace PG with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in SHP' by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          replace (PG + 1) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g) + Z.of_nat 1) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' (cb_app m' _ _ _ _ _ SHP' F2))) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + (1 + Z.to_nat (shlen S - grz - (g + 1)))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          rewrite <- app_assoc. cbn [app] in FIN. exact FIN. }
  (* [comment removed for export] *)
  assert (HQ' : AQ L (st_fast st c n cnt) X' m').
  { eapply (hq_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HQ | exact MUn | exact WM | |].
    - unfold quar_untouched. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      do 10 (apply Forall_cons; [cbn [fst snd];
        split; [clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N UBN GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 D_t_res DL7 DL8 TBND TIMG NBND DL3 SBND DL6 RHI; unbox D_t_res; unbox DL7; unbox DL8; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        intros b Hb; (nd_pre (BB b Hb) 5%nat; intros Bb1 Bb2 Bb3 Bb4 Bb5; nd_post); destruct (xb_st b); [exact I| |];
        clear -Bb1 Bb2 Bb3 CEIL LO RES C16 EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 G2 DL1 DL2 DL4 DL5 D_t_res D_n_res D_s_res UBN NBND DL3 SBND DL6 RHI;
        unbox D_t_res; unbox D_n_res; unbox D_s_res; lia |]).
      apply Forall_nil.
    - unfold quar_same. rewrite E1, E8, E9, E10, E11. repeat (split; [reflexivity|]). split.
      + intros b Hb. destruct (xb_st b); [exact I| right; exact Hb | right; exact Hb].
      + intros b [<-|Hb]; [exact I|]. destruct (xb_st b); [exact I| exact Hb | exact Hb]. }
  assert (HS' : ASEC L (st_fast st c n cnt) X' m').
  { eapply (hs_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad AB).
      { rewrite !shad_div. unfold aregion, K_REGION in G5. change (2^32) with 4294967296 in G5. clear -G5 C16. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (AB + S) <= shad (al_space_beg L) + 17179869184).
      { rewrite !shad_div. clear -G2. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL2 C16 TBND TIMG; lia |]).
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G1 G2 UBN N RSP; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha GR7 GR3 PGB SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; unfold AIMG_HI; clear -Ha; lia |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - unfold sec_same. rewrite E2, E3, E4, E6. repeat (split; [reflexivity|]).
      assert (NONE : (a_live st) !! (a_next st) = None).
      { destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as FF. clear -FF. lia. }
      split.
      + intros p mb ms n'. destruct (N.eq_dec p (a_next st)) as [->|NE].
        * rewrite lookup_insert_eq. split; [intros HH; discriminate| intros HH]. exfalso. rewrite NONE in HH. discriminate.
        * rewrite lookup_insert_ne by congruence. first [ solve [ clear; tauto ] | tauto ].   (* [comment removed for export] *)
      + eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [exact NONE| exact E6| exact E8| exact E10]. }
  assert (AR' : AREP (AH DI AQ ASEC AFK) L (st_fast st c n cnt) X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|].
    split; [eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUn | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
    split; [| eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
    intros c'' Hc''. (pose proof (st_fast_counters st c n cnt c'') as ndP__; nd_pre ndP__ 5%nat; intros EC1 EC2 EC3 EC4 EC5; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof (aregion_mod L c'' SAL) as RM''. unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    eapply (ashadow_avail_frame L _ m m' MUn WM st); [exact (AVL c'' ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) | exact EC1 | exact EC4 | |].
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_FREEARR_OFF in *. clear -G4 A1. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| clear -RM'' Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia]. unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, aregion in *. clear -Q5 Q6 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2 Q5 Q6. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM'' Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia].
             unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q5 Q6 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D Q1 Q5 Q6. lia. }
  (* [comment removed for export] *)
  pose proof (ablocks_fast L st X LB c k n cnt b1' id WF BL) as BL'. rewrite <- EAB, <- EUB in BL'. fold X' in BL'.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi _ [kF FKs]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HBK : forall b, In b LB -> disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (ab_addr b) (ab_size b)).
  { intros [[p|cls] A n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL p A n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EUA & Gs)].
      + (nd_pre (BB b Hb) 5%nat; intros Bb1 Bb2 Bb3 Bb4 Bb5; nd_post).
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
        apply Kres; clear -Bb1 Bb2 Bb3 FIT; lia.
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
        destruct (ablk_int _ _ Gs2) as [kB GB].   (* [comment removed for export] *)
        apply Kobj; clear -GB Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      apply Kobj; [clear -K1 K3 FKO FKi FKs; lia | clear -K3 FKO FKi FKs; lia | exact K2 | clear -K1 K3 D_t_f; unbox D_t_f; lia
                  | clear -K1 K3 D_f_res; unbox D_f_res; lia | clear -K1 K3 D_n_f; unbox D_n_f; lia | clear -K1 K3 D_s_f; unbox D_s_f; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO Ha' FKi FKs; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO Ha' FKi FKs; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
    - left. rewrite GR7, (shad_div a'), (shad_div AB). clear -D Ha' K3 RSP G1 GR3. Z.div_mod_to_equations. lia.
    - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G2. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (HFK' : AFK L (HB (a_next st) UB n :: LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. unfold aobj in DTO. (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DTs] [jD DTi]; nd_post).   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ PG + room <= shad (al_fake L))
                    /\ 2148238848 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; clear -FKO FKi FKs; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
        - left. rewrite GR7, shlen_div, (shad_div (al_fake L)), (shad_div AB). clear -D RSP G1 GR3. Z.div_mod_to_equations. lia.
        - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D RSP G2. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      do 10 (apply Forall_cons; [cbn [fst snd];
        clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 FKO DTO D1 D2 D3 D4 D_t_f D_f_res D_n_f D_s_f SHF1 SHF2 SHF3 UBN TBND TIMG NBND DL3 SBND DL6 RHI FKi FKs DTs DTi D_l_t D_l_r D_l_n D_l_s TLN ATR0;      (* [comment removed for export] *)
       
        (* [comment removed for export] *)
        first [ lazymatch goal with
                | |- context [al_t _] => unbox D_t_f; clear D_f_res D_n_f D_s_f
                | |- context [al_nodes _] => unbox D_n_f; clear D_t_f D_f_res D_s_f
                | |- context [al_store _] => unbox D_s_f; clear D_t_f D_f_res D_n_f
                | |- _ => unbox D_f_res; clear D_t_f D_n_f D_s_f
                end; unfold AIMG_HI in *; repeat (split; [fu_lia|]); fu_lia
              | unbox D_t_f; unbox D_f_res; unbox D_n_f; unbox D_s_f; unfold AIMG_HI in *; repeat (split; [lia|]); lia ] |]).
      apply Forall_nil.
    - intros cls FA sz. cbn. split; [intros [E|Hin]; [discriminate| exact Hin] | intros Hin; right; exact Hin]. }
  (* [comment removed for export] *)
  assert (PSP : PG + room <= shad ATOP).
  { eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -G2 SP2. lia. }
  split; [apply fp_le_refl|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_prim CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia]. }
  cbn [fst snd]. exists UB.
  split; [reflexivity|]. split.
  { unfold ablock_range. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    split; [unfold ablk; right; clear -G1 SP1 EUB RZR UBN G2 SP2 N; lia|]. split; [clear -N; lia|]. split; [clear -UBN G2 SP2; lia|].   (* [comment removed for export] *)
    rewrite EUB. clear -G3 RZM RZR. Z.div_mod_to_equations; lia. }
  split.
  { split; [exact ALO|]. split; [eapply arng_fast; [exact WF| exact ARNG]|]. split; [| exact HFK']. exists X'. split; [exact AR' | exact BL']. }
  split; [exact UF'|].
  (nd_pre ARNG 11%nat; intros _ _ _ _ _ _ _ _ _ RCLS _; nd_post). (nd_pre (RCLS c HCK) 4%nat; intros RREG RSREG _ _; nd_post).
  split; [| split].
  - eapply rng_sub'; [exact RREG|]. clear -G5 G4 A1 UBN. lia.
  - eapply rng_sub'; [exact RSREG|]. pose proof (aregion_mod L c SAL) as RM.
    split; [apply shad_mono; clear -G5 UBN; lia|].
    rewrite <- (shad_add_shlen (aregion L c) (c_mapped_user (get_cls st c))) by (clear -RM; Z.div_mod_to_equations; lia).
    rewrite (shad_div UB), shlen_div, (shad_div (aregion L c + c_mapped_user (get_cls st c))).
    pose proof (size_of_class_facts c HCK) as [_ S16]. fold S in S16.
    clear -UBN G4 A1 G3 S16. Z.div_mod_to_equations. lia.
  - intros NP. exfalso. rewrite PRIM in NP. discriminate.
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_primU : ltac:(let t := eval cbv delta [store_primU__stmt] in store_primU__stmt in exact t).
Proof. exact store_primU__body. Qed.

End S.

End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.StepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3g0__A3W.F_amalloc_tailg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.ARepStore.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_tailg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_acalloc_iseg__A3W.ACalloc_iface.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Notation Wn sp t c AB UB PGE n nodes store :=
  ([(sp - 4096, sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792); (t + 2800, t + 3169);
    (UB - 16, UB + n); (AB, AB + 16); (shad UB, PGE);
    (ADEPOT_LO, ADEPOT_HI); (nodes, nodes + 1048576); (store, store + 8388608)]%Z) (only parsing).

(* [comment removed for export] *)
Ltac fu_drop_fake := repeat match goal with H : context [al_fake _] |- _ => clear H end.
Ltac fu_drop_dtls := repeat match goal with H : context [al_dtls _] |- _ => clear H end.
Ltac fu_drop_tls := repeat match goal with H : context [ATPv] |- _ => clear H | H : context [kt_img] |- _ => clear H end.
Ltac fu_focus :=
  lazymatch goal with
  | |- context [al_fake _] => fu_drop_dtls; fu_drop_tls
  | |- context [al_dtls _] => fu_drop_fake; fu_drop_tls
  | |- context [ATPv] => fu_drop_fake; fu_drop_dtls
  | |- _ => fu_drop_fake; fu_drop_dtls; fu_drop_tls
  end.
Ltac fu_lia := solve [fu_focus; lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
(* [comment removed for export] *)
#[using="Type"] Local Lemma ablk_int : forall lo hi, ablk lo hi ->      (* [comment removed for export] *)
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
  6307840 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
  intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed.
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
  4096 <= a /\ a + 4096 <= ATOP
  /\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
  /\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6307840 * j <= a).
Proof.
  intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. (nd_pre H 5%nat; intros H1 H2 H3 H4 H5; nd_post).
  split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed.
Section KindsG.
Variables (sp t c AB S UB PGE n nodes store res ctx lo grz ssz : Z).
(* [comment removed for export] *)
Definition kfactsG : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (1 <= c <= 30)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ UB - 16 >= AB /\ 1 <= n /\ UB + n <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ shad UB + 1 <= PGE /\ PGE <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6307840 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6307840 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6307840 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfactsG.

(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
Local Ltac2 rlx_prune (x : ident) : unit :=
  let hs := Control.hyps () in
  let cs := zt_plain_consts () in
  let ids := List.map_filter (fun h => let (id, body, ty) := h in
                match body with
                | Some _ => None
                | None => if Ident.equal id x then None else if zt_plain_arith_s cs ty then None
                          else if zt_is_local id then zt_is_prop_some ty id else None
                end) hs in
  match ids with [] => () | _ :: _ => Std.clear ids end.
Local Ltac2 rlx_id (v : Ltac1.t) : ident :=
  match Ltac1.to_ident v with
  | Some id => id
  | None => match Constr.Unsafe.kind (Option.get (Ltac1.to_constr v)) with Constr.Unsafe.Var id => id | _ => Control.throw (Tactic_failure None) end
  end.
Set Default Proof Mode "Classic".
Local Ltac rlx_prune X := let f := ltac2:(x |- rlx_prune (rlx_id x)) in f X.
Local Ltac rlx_lia X := rlx_prune X; first [ zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | Zify.zify; xlia zchecker ].
Local Ltac lia_rel ::= first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; rlx_lia X ] end ].
(* [comment removed for export] *)
Ltac kbase L := lazymatch L with Z.add ?X _ => kbase X | Z.sub ?X _ => kbase X | Z.mul _ ?X => kbase X | _ => L end.
Ltac kalias X := lazymatch X with UB => constr:(res) | AB => constr:(res) | _ => X end.
Ltac kkeep2 X Y := repeat match goal with H : _ \/ _ |- _ => lazymatch type of H with context [X] => fail | context [Y] => fail | _ => clear H end end.
Ltac klia := Zify.zify; xlia zchecker.
Ltac kind1 := lazymatch goal with
  | |- (_ <= ?L \/ _)%Z => let X := kbase L in let Y := kalias X in first [ solve [ kkeep2 X Y; klia ] | lia_rel | lia ]
  | |- _ => first [ lia_rel | lia ] end.
Ltac kind := pose proof KF as KF'; unfold kfactsG, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  (nd_pre KF' 8%nat; intros F_lo F_t F_c F_res F_slot F_sh F_ns F_ctx; nd_post);
  cbn [disjoint_from]; repeat (split; [kind1|]); first [ kind1 | exact I ].   (* [comment removed for export] *)

#[using="rc S res ctx lo grz ssz KF"] Lemma KG_img : forall A k, 0x10000 <= A -> 0 <= k -> (A + k <= ADEPOT_LO \/ (ADEPOT_HI <= A /\ A + k <= AIMG_HI)) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S res ctx lo grz ssz KF"] Lemma KG_low : forall A k, 2147450880 <= A -> A + k <= 2148239360 -> 0 <= k ->      (* [comment removed for export] *)
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S res ctx lo grz ssz KF"] Lemma KG_hi : forall A k, sp <= A -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S res ctx lo grz ssz KF"] Lemma KG_shad : forall A k, 2147446784 <= A -> A + k <= 17594333495296 -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= shad UB \/ PGE <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S lo grz ssz KF"] Lemma KG_ctx : 
  (ctx + 65536 <= t \/ t + 4096 <= ctx) -> (ctx + 65536 <= res \/ res + 137439023104 <= ctx) ->
  (ctx + 65536 <= nodes \/ nodes + 1048576 <= ctx) -> (ctx + 65536 <= store \/ store + 8388608 <= ctx) ->
  forall A k, ctx <= A -> A + k <= ctx + 65536 -> 0 <= k ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S ctx lo grz ssz KF"] Lemma KG_t :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (t + 4096 <= nodes \/ nodes + 1048576 <= t) -> (t + 4096 <= store \/ store + 8388608 <= t) ->
  forall A k, t <= A -> A + k <= t + 4096 -> 0 <= k ->
  (A + k <= t + 208 + c * 80 \/ t + 208 + c * 80 + 4 <= A) -> (A + k <= t + 2784 \/ t + 2792 <= A) -> (A + k <= t + 2800 \/ t + 3169 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="rc S ctx lo grz ssz KF"] Lemma KG_res :
  (t + 4096 <= res \/ res + 137439023104 <= t) -> (nodes + 1048576 <= res \/ res + 137439023104 <= nodes) ->
  (store + 8388608 <= res \/ res + 137439023104 <= store) ->
  forall A k, res <= A -> A + k <= res + 137439023104 -> 0 <= k ->
  (A + k <= AB \/ (AB + 16 <= A /\ A + k <= UB - 16) \/ UB + n <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.

#[using="S ctx lo grz ssz KF"] Lemma KG_obj : forall A k, ((6307840 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->      (* [comment removed for export] *)
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.
(* [comment removed for export] *)
#[using="S ctx lo grz ssz KF"] Lemma KG_objL : forall A k, ((A + k <= 65536 \/ 6307840 <= A) /\ (A + k <= 2147446784 \/ 17594333495296 <= A)) -> A + k <= ATOP -> 0 <= k ->      
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= res \/ res + 137439023104 <= A) ->
  (A + k <= nodes \/ nodes + 1048576 <= A) -> (A + k <= store \/ store + 8388608 <= A) ->
  disjoint_from (Wn sp t c AB UB PGE n nodes store) A k.
Proof. intros. kind. Qed.
End KindsG.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma aheap_pres_prim : forall (CI : list (Z * Z)) sp t c AB S UB PGE n nodes store res ctx lo grz ssz (LB : list ablock) m m',
  kfactsG sp t c AB S UB PGE n nodes store res ctx lo grz ssz ->
  Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI ->
  munch (Wn sp t c AB UB PGE n nodes store) m m' -> wmono asegs m m' ->
  (forall b, In b LB -> disjoint_from (Wn sp t c AB UB PGE n nodes store) (ab_addr b) (ab_size b)) ->
  (forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
       disjoint_from (Wn sp t c AB UB PGE n nodes store) (shad a') 1) ->
  PGE <= shad ATOP ->
  (forall A k, ATPv + -200 <= A -> A + k <= ATPv + 312 -> 0 <= k -> disjoint_from (Wn sp t c AB UB PGE n nodes store) A k) ->      (* [comment removed for export] *)
  (forall a', ATPv + -200 <= a' < ATPv + 312 -> disjoint_from (Wn sp t c AB UB PGE n nodes store) (shad a') 1) ->                  (* [comment removed for export] *)
  disjoint_from (Wn sp t c AB UB PGE n nodes store) AIMSH_LO AIMSH_LEN ->                                                          (* [comment removed for export] *)
  disjoint_from (Wn sp t c AB UB PGE n nodes store) AAHMv AAHM_SZ ->                                                          (* [comment removed for export] *)
  aheap_pres CI LB sp m m'.
Proof.
  intros CI sp t c AB S UB PGE n nodes store res ctx lo grz ssz LB m m' KF CIOK MU WM HBK HFK PSP TLSK TLSS IMSH AHMK a Ha CL.
  split; [| intros Hw; apply WM; exact Hw].
  apply MU. rewrite wa_unsigned by exact Ha.
  destruct CL as [CL|TL]; [| exact (aextra_outside _ a TLSK TLSS IMSH AHMK TL)].
  pose proof KF as KF'. (nd_pre KF' 8%nat; intros F_lo F_t F_c F_res F_slot F_sh F_ns F_ctx; nd_post).
  destruct CL as [ST | [CIa | [BLK | SH]]].
  - eapply disjoint_outside; [eapply (KG_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); lia | lia].
  - (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
    eapply disjoint_outside; [eapply (KG_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF a 1); unfold AIMG_HI in *; lia | lia].
  - (nd_pre BLK 3%nat; intros b Hb R; nd_post). eapply disjoint_outside; [exact (HBK b Hb) | lia].
  - (nd_pre SH 3%nat; intros a' Ha' ndR1__; nd_post; revert ndR1__; intros ->).
    pose proof (shad_div a') as SD. pose proof (shad_div ATOP) as SDs. unfold ASHOFF in *.
    destruct Ha' as [ST | [CIa | FK]].
    + eapply disjoint_outside; [eapply (KG_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: clear -ST SD SDs F_sh PSP; Z.div_mod_to_equations; lia.
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CIOK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (KG_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (shad a') 1) | lia].
      all: unfold AIMG_HI in *; clear -R SD Q1 Q3; Z.div_mod_to_equations; lia.
    + (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). eapply disjoint_outside; [exact (HFK cls FA sz Hin a' R) | lia].
Qed.

#[using="Type"] Lemma b1'_range : forall b1, 0 <= b1 -> 0 <= Z.lor (Z.land (hdr_b1_mid b1) 243) 0 < 256.
Proof.
  intros b1 Hb. rewrite Z.lor_0_r. pose proof (hdr_b1_mid_range b1 Hb) as [R0 R1].
  assert (A0 : 0 <= Z.land (hdr_b1_mid b1) 243) by (apply Z.land_nonneg; right; lia).
  split; [exact A0|].
  destruct (Z.eq_dec (Z.land (hdr_b1_mid b1) 243) 0) as [->|NZ]; [lia|].
  change 256 with (2^8). apply lt_pow2_of_log2; [lia|].
  pose proof (Z.log2_land (hdr_b1_mid b1) 243 R0 ltac:(lia)) as L1.
  replace (Z.log2 243) with 7 in L1 by reflexivity. lia.
Qed.

#[using="Type"] Lemma b1'_at1 : forall b1, 0 <= b1 < 256 -> Z.land (Z.lor (Z.land (hdr_b1_mid b1) 243) 0) 3 = 1.
Proof.
  intros b1 Hb.
  assert (C : forallb (fun i => Z.land (Z.lor (Z.land (hdr_b1_mid (Z.of_nat i)) 243) 0) 3 =? 1) (seq 0 256) = true) by (vm_compute; reflexivity).
  pose proof (proj1 (forallb_forall _ _) C (Z.to_nat b1) ltac:(apply in_seq; lia)) as C1. cbn beta in C1.
  rewrite Z2Nat.id in C1 by lia. apply Z.eqb_eq. exact C1.
Qed.



(* [comment removed for export] *)

(* [comment removed for export] *)
Definition store_primU_stmt (DI : ADepotIface) (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop)
    (CI : list (Z * Z)) : Prop :=
  forall (L : alayout) (RNG : footprint) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m : amem) (st : astate) (LB : list ablock) (X : aconc) (n lo c cnt k b1 : Z) (maxc csz : word) (ub : list byte),
  let S := size_of_class c in let AB := aslot_addr L c k in let UB := AB + rz_size n in let PG := shad UB + shlen (n - n mod 8) in
  alayout_ok L -> arng L RNG st -> AREP (AH DI AQ ASEC AFK) L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n -> is_primary n = true -> class_id (needed_size n) = c -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None -> 0 <= k < ndist st c ->
  maxc = Z_to_bv 64 (max_count st c) -> csz = Z_to_bv 64 S -> 0 <= b1 < 256 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
  (16 < rz_size n -> junk_at m (AB + 16) (rz_size n - 32)) ->
  junk_at m (UB + n) (S - rz_size n - n) ->
  fill_at m (shad AB + 1) (shlen (rz_size n) - 1) 0xfa ->
  fill_at m (PG + (if n mod 8 =? 0 then 0 else 1)) (shlen S - shlen (rz_size n) - shlen (n - n mod 8) - (if n mod 8 =? 0 then 0 else 1)) 0xfa ->
  junk_at m (al_t L + 2768) 16 -> junk_at m (al_t L + 2792) 8 ->
  forall ms',
    malloc_post_genU DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG (if n mod 8 =? 0 then 0 else 1) lo b1 maxc csz ub m ms' ->
    amalloc_postU CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m ub
      (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st))
         (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)), Some (a_next st)) RNG ms'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.

Definition store_primU__stmt : Prop := store_primU_stmt DI AQ ASEC AFK CI.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 1).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 3).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 4).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 5).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 6).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 7).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 8).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 9).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 10).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 11).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 12).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 13).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 14).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 15).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 16).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 17).
Variable F : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 18).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 19).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 20).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 21).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 22).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 23).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 24).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 25).
Variable c : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 26).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 27).
Variable k : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 28).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 29).
Variable maxc : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 30).
Variable csz : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 31).
Variable ub : ltac2:(SecDietF.SzSecF.ty 'store_primU__stmt 32).
Let S := size_of_class c.
Let AB := aslot_addr L c k.
Let UB := AB + rz_size n.
Let grz := shlen (rz_size n).
Let g := shlen (n - n mod 8).
Let room := if n mod 8 =? 0 then 0 else 1.
Let PG := shad UB + g.
Let b1' := Z.lor (Z.land (hdr_b1_mid b1) 243) 0.
#[using="HL CI_OK S AB UB grz g room PG b1'"] Lemma store_primU__body : ltac:(let T := type of (fun (h : store_primU__stmt) => h L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st LB X n lo c cnt k b1 maxc csz ub) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (ra, (sp, (gp, (tp, (s0, (s1, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (F, (fc, (m, (st, (LB, (X, (n, (lo, (c, (cnt, (k, (b1, (maxc, (csz, ub))))))))))))))))))))))))))))))))) as _.
  unfold store_primU_stmt.  cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM HC0 HCNT POS NK NB KR HMX HCSZ B1 CEIL LO LHJ TL SHpre SHsuf CSa CSc ms' PM.
  clear SHpre SHsuf. unfold AMALLOC_STACK in LO.
  (* [comment removed for export] *)
  (pose proof (prim_facts n N PRIM) as ndP__; nd_pre ndP__ 8%nat; intros NS RZR RZE RZM RLR RSR RSM NSR; nd_post).
  (pose proof (prim_class_facts n c N PRIM HC0) as ndP__; nd_pre ndP__ 5%nat; intros C16 NSZ SZM16 SMALL MCB; nd_post).
  assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS STATS0 UNW; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HCK) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  (pose proof (alayout_t L ALO) as ndP__; nd_pre ndP__ 4%nat; intros TL1 TL2 TL3 TL4; nd_post).
  (pose proof (alayout_ctx L ALO) as ndP__; nd_pre ndP__ 5%nat; intros CL1 CL2 CL3 CL4 CL5; nd_post). clear CL5.
  (pose proof (alayout_depot L ALO) as ndP__; nd_pre ndP__ 10%nat; intros DL1 DL2 DL3 DL4 DL5 DL6 DL7 DL8 DL9 DL10; nd_post). clear DL9 DL10.
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT TBND] [jT TIMG]; nd_post). (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros _ _ [kC CBND]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros _ _ [kN NBND]; nd_post). (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros _ _ [kS SBND]; nd_post). unfold AIMG_HI in DL3, DL6, CL3.
  (pose proof (alayout_stack L ALO) as ndP__; nd_pre ndP__ 3%nat; intros STK1 STK2 STK3; nd_post).
  pose proof (ao_res L ALO) as RES. unfold aobj in RES. pose proof (ao_space L ALO) as RSP. pose proof (ao_res_hi L ALO) as RHI.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s.
  unfold adisj in D_t_res, D_n_res, D_s_res, D_c_res, D_c_n, D_c_s.
  assert (D_c_t : al_ctx L + 65536 <= al_t L \/ al_t L + 4096 <= al_ctx L) by (pose proof (ad_t_ctx L ALO) as X1; unfold adisj in X1; clear -X1; lia).
  box DL7. box DL8. box D_t_res. box D_n_res. box D_s_res. box D_c_res. box D_c_n. box D_c_s. box D_c_t.
  word_range sp SPR.
  assert (CIN : a_cinit st = true).
  { unfold max_count in CNTB. destruct (a_cinit st); [reflexivity| exfalso]. rewrite HCNT in CNTB. clear -CNTB POS. lia. }
  assert (MC16 : max_cached c <= 16) by (clear -MCB; lia).
  assert (CNT16 : 0 < cnt <= 16) by (unfold max_count in CNTB; rewrite CIN, HCNT in CNTB; clear -CNTB POS MC16; lia).
  (* [comment removed for export] *)
  (pose proof (cls_facts c C16) as ndP__; nd_pre ndP__ 4%nat; intros SZB SZM _ _; nd_post).
  chg (size_of_class c) S.
  (pose proof (slot_in_region L st c k ltac:(clear -SZB; subst S; lia) (proj1 A1) KR) as ndP__; nd_pre ndP__ 3%nat; intros G5 G4 KS0; nd_post). fold S in G5, G4, KS0.
  chg (aslot_addr L c k) AB.
  assert (G1 : al_space_beg L <= AB) by (unfold aregion, K_REGION in G5; clear -G5 C16; lia).
  assert (G2 : AB + S <= al_space_beg L + K_SPACE_SIZE).
  { unfold aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF in *. generalize G4 A1 A2 C16; clear; intros. change (2^37) with 137438953472. lia. }
  assert (G3 : AB mod 16 = 0) by (subst AB; apply slot_aligned; [exact SAL| exact HCK]).
  assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
  assert (ES : S = size_of_class c) by reflexivity.
  chg (AB + rz_size n) UB. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
  chg (shlen (rz_size n)) grz. chg (shlen (n - n mod 8)) g. chg (if n mod 8 =? 0 then 0 else 1) room.
  assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8) by (subst grz g; rewrite !shlen_div; split; reflexivity).
  destruct GR12 as [GR1 GR2].
  assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
  assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
  assert (RMQ : room = (if n mod 8 =? 0 then 0 else 1)) by reflexivity. clearbody room.
  assert (GR5 : 0 <= room <= 1) by (rewrite RMQ; clear; destruct (n mod 8 =? 0); lia).
  assert (SS8 : shlen S = S / 8) by (rewrite shlen_div; reflexivity).
  assert (GR6 : grz + g + room <= shlen S).
  { rewrite GR1, GR2, SS8, RMQ. generalize NSZ NS RSR RSM SZM RZM RZR N. clear. intros.
    destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
  assert (GR7 : shad UB = shad AB + grz).
  { rewrite GR1, EUB. rewrite !shad_div. generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations; lia. }
  assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000 /\ shad AB + shlen S = shad (AB + S)).   (* [comment removed for export] *)
  { rewrite SS8, !shad_div. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 G3 SP1 SP2 SZB SZM ES. clear. intros. Z.div_mod_to_equations. lia. }
  (nd_pre GR89 3%nat; intros GR8 GR9 GR10; nd_post).
  chg (shad UB + g) PG.
  assert (PGE_ : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
  assert (ROOM : granules n = g + room) by (subst g; rewrite RMQ; apply granules_eq; clear -N; lia).
  assert (GR11 : 1 <= g + room).
  { subst g. rewrite RMQ, shlen_div. generalize N; clear; intros. destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) ->
      al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104
      /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ UB + n <= xb_alloc L b)
      /\ xb_alloc L b mod 16 = 0 /\ 16 <= size_of_class (xb_class b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc. split; [| split; [| split; [| split; [apply slot_aligned; [exact SAL| exact CLB] | clear -QS; lia]]]].
    - unfold aregion, K_REGION in P5. clear -P5 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    - unfold aregion, K_REGION, K_FREEARR_OFF in *. clear -P4 Q1 Q2 CLB RSP. unfold K_NUM_CLASSES in CLB. lia.
    - (* [comment removed for export] *)
      destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
      + rewrite EC in *. assert (NKb : xb_slot b <> k).
        { intros EK. enough (busy_of X c k <> None) by congruence. unfold busy_of.
          destruct (List.find _ _) eqn:FE; [discriminate|]. exfalso.
          apply (find_none _ _ FE) in Hb. rewrite EC, EK, !Z.eqb_refl in Hb. discriminate. }
        destruct (slots_disjoint L c (xb_slot b) k ltac:(clear -KB; lia) ltac:(clear -KR; lia) NKb ltac:(clear -SZB; lia)) as [D|D];
          rewrite <- EAB in D; fold S in D; [left; exact D| right].
        clear -D EUB RZR N NSZ NS RSR ES. subst S. lia.
      + assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
        unfold K_REGION, K_FREEARR_OFF in *.
        destruct (proj1 (Z.lt_gt_cases (xb_class b) c) NC) as [LT|GT]; [left | right].
        * specialize (RC _ _ LT). clear -RC P4 Q1 Q2 G5. lia.
        * specialize (RC _ _ GT). clear -RC P5 G4 A1 A2 EUB N NSZ NS RSR RZR ES. subst S. lia. }
  (* [comment removed for export] *)
  (nd_pre PM 19%nat; intros id t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' sj' stj' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 16%nat; intros MU WM MI' ST' IDR CR' STS' STATS' LSJ' UW' HDR' UF' LH' SHU' SHP' DEP'; nd_post).
  (* [comment removed for export] *)
  assert (MUn : munch (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) m m').
  { eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. subst PG. generalize GR3 GR4 GR5 GR7. clear. intros. lia. }
  clear MU.
  assert (KF : kfactsG (bv_unsigned sp) (al_t L) c AB S UB (PG + room) n (al_nodes L) (al_store L) (al_res L) (al_ctx L) lo grz (shlen S)).
  { unfold kfactsG. subst PG. unfold AMALLOC_STACK, K_SPACE_SIZE in *. change (2^37) with 137438953472 in G2.
    generalize CEIL LO TL1 TL2 TL4 C16 RES RHI RSP G1 G2 EUB RZR N NSZ NS RSR ES GR8 GR7 GR3 GR4 GR5 GR6 GR9 GR11 DL1 DL2 DL3 DL4 DL5 DL6 CL1 CL2 CL3. clear. intros.
    unfold iclr, AIMG_LO, AIMG_HI in *.
    repeat split; first [lia | assumption | match goal with |- ?G => idtac "KF-LEFT" G end]. }   (* [comment removed for export] *)
  pose proof (KG_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kimg.
  pose proof (KG_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Klow.
  pose proof (KG_hi _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Khi.
  pose proof (KG_shad _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kshad.
  pose proof (KG_ctx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_c_t) (unbx D_c_res) (unbx D_c_n) (unbx D_c_s)) as Kctx.
  pose proof (KG_t _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx DL7) (unbx DL8)) as Kt.
  pose proof (KG_res _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF (unbx D_t_res) (unbx D_n_res) (unbx D_s_res)) as Kres.
  pose proof (KG_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as Kobj.
  pose proof (KG_objL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF) as KobjL.      (* [comment removed for export] *)
  pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_res L ALO) as D_l_r. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
  unfold adisj in D_l_t, D_l_r, D_l_n, D_l_s. pose proof atp_lin as TLN. pose proof atop_range as ATR0.
  (* [comment removed for export] *)
  change (set_next (N.succ (a_next st)) (set_live (<[ a_next st := CPrim c n ]> (a_live st)) (put_cls c (cls_set_count (cnt - 1) (get_cls st c)) st)))
    with (st_fast st c n cnt).
  chg (Z.lor (Z.land (hdr_b1_mid b1) 243) 0) b1'.
  pose proof (b1'_range b1 ltac:(clear -B1; lia)) as B1R. fold b1' in B1R.
  set (X' := xfast X c k n (a_next st) b1' id).
  (pose proof (st_fast_fields st c n cnt) as ndP__; nd_pre ndP__ 11%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11; nd_post).
  (* [comment removed for export] *)
  assert (WF' : awf L (st_fast st c n cnt) X').
  { apply awf_fast; [exact WF | exact HCK | exact HCNT | exact POS | exact NK | exact NB | clear -N NS NSR RSR RZR; unfold AREQMAX; lia | | exact B1R | apply b1'_at1; clear -B1; lia | clear -IDR; lia].
    fold S. clear -NS NSZ. lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUn | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI; lia | apply Kctx; clear; lia | apply KobjL; clear -D_l_t D_l_r D_l_n D_l_s TLN ATR0; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L (st_fast st c n cnt) m').
  { eapply ainstance_frame; [exact MUn | exact WM | exact INST | exact E3 | exact E4 | | |]; apply Kimg; clear; unfold AINSTANCE, AIMG_HI; lia. }
  assert (THR' : athread L (st_fast st c n cnt) X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - eapply cells_frame; [exact T40 | exact MUn | exact WM |]. cbn [cells_size csize Nat.add]. apply Kt; clear -C16; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      + destruct (CACHES c HCK) as [tail (CR & CH & LCH)]. unfold acache_cells. cbv zeta.
        (pose proof (st_fast_counters st c n cnt c) as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ _ EC5; nd_post). rewrite Z.eqb_refl in EC5.
        rewrite EC5, st_fast_max_count, E5, CIN. unfold X'. rewrite xfast_cls, Z.eqb_refl. cbn [xc_cache].
        exists (Z_to_bv 64 (acompact c k) :: tail).
        assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
        { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC HCNT. lia. }
        split; [| split].
        * unfold acache_addr. rewrite HMX, HCSZ in CR'. fold S. exact CR'.
        * eapply u32arr_frame; [| exact MUn | exact WM |].
          -- rewrite CACHE, map_app in CH. cbn [map] in CH. rewrite <- app_assoc in CH. cbn [app] in CH. exact CH.
          -- rewrite length_app, length_map. cbn [length]. unfold acache_addr.
             assert (LRL : (length (removelast (xc_cache (x_cls X c))) + Datatypes.S (length tail) = 16)%nat).
             { rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia. }
             rewrite LRL. apply Kt; clear -C16; lia.
        * cbn [length]. rewrite length_removelast; [clear -LCH LENC HCNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC HCNT POS. lia.
      + eapply acache_cells_frame; [exact MUn | exact WM | exact (CACHES c' Hc') | | exact E5 | |].
        * (pose proof (st_fast_counters st c n cnt c') as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ _ EC5; nd_post). rewrite EC5. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c' c) as [EQ'|_]; [exfalso; clear -EQ' NE; lia| reflexivity].
        * unfold acache_addr. unfold K_NUM_CLASSES in Hc'. apply Kt; clear -C16 Hc' NE; lia.
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + eapply junk_frame; [exact CSa | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STS') as J. cbn in J. exact J.
        * replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) by (clear; lia).
          eapply junk_frame; [exact CSc | exact MUn | exact WM | intros _; apply Kt; clear -C16; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - exact UW'. }
  (* [comment removed for export] *)
  assert (RC : forall c1 c2, c1 < c2 -> aregion L c1 + K_REGION <= aregion L c2) by (intros; apply regions_sep; assumption).
  assert (UBN : AB + 16 <= UB /\ UB + n <= AB + S) by (clear -EUB RZR N NSZ NS RSR; lia).
  assert (PGB : PG + room <= shad (AB + S)) by (subst PG; rewrite GR7, <- GR10; clear -GR6; lia).
  assert (CLS' : forall c'', 1 <= c'' < K_NUM_CLASSES ->
      aregion_cells L (st_fast st c n cnt) m' c'' /\ afreearray L (st_fast st c n cnt) X' m' c''
      /\ aslots L (st_fast st c n cnt) X' m' c'' /\ aslot_shadow L (st_fast st c n cnt) X' m' c'').
  { intros c'' Hc''. (nd_pre (CLS c'' Hc'') 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
    (nd_pre (PERC c'' Hc'') 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
    pose proof (size_of_class_facts c'' Hc'') as [QS QS16].
    (pose proof (st_fast_counters st c n cnt c'') as ndP__; nd_pre ndP__ 5%nat; intros EC1 EC2 EC3 EC4 EC5; nd_post).
    pose proof (aregion_mod L c'' SAL) as RM''.
    unfold K_NUM_CLASSES in Hc''.
    (* [comment removed for export] *)
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post).
    split; [| split; [| split]].
    - eapply aregion_cells_frame; [exact MUn | exact WM | exact REG | exact EC3 | exact EC4 | exact EC2 | exact EC1 |].
      apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE in *; change (2^37) with 137438953472 in *; clear -Hc'' RSP G2 EUB NSZ NS RSR RZR N; lia.
    - eapply afreearray_frame; [exact MUn | exact WM | exact FARR | exact EC3 | exact EC4 | | exact QLENF | exact Q5 | | clear -Q6; lia |].
      + unfold X'. rewrite xfast_cls. destruct (Z.eqb_spec c'' c) as [->|_]; reflexivity.
      + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *.
        * clear -RI1. lia.
        * clear -RI2 RI3 Q6. lia.
        * clear -Q5 Q6; lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right; right. clear -G4 A1 A2 UBN. lia.
          -- destruct (SIDE NE) as [D|D]; [left; clear -D Q6; lia | right; right; clear -D UBN; lia].
      + apply Kshad.
        * rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF in *. clear -RI1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -RI2 RI3 Q6 RES RHI. Z.div_mod_to_equations. lia.
        * apply shlen_nonneg. clear -Q5 Q6. lia.
        * destruct (Z.eq_dec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2. lia.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM''; Z.div_mod_to_equations; lia].
                unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q6 UBN. lia.
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D. lia.
    - (* [comment removed for export] *)
      eapply (aslots_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SLOTS | apply st_fast_ndist | exact EC2 | exact EC1 | | |].
      + intros k'' Hk'' NEk. (pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        split; [| split].
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kres; [clear -P5 RI1; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -QS; lia |].
          destruct (Z.eqb_spec c'' c) as [->|NE].
          -- destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D;
               [left; exact D | right; right; clear -D EUB RZR N NSZ NS RSR ES; subst S; lia].
          -- destruct (SIDE NE) as [D|D]; [left; clear -D P4 Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D P5 UBN; lia].
        * intros b Hb. (nd_pre (busy_of_Some_facts X c'' k'' b Hb) 3%nat; intros IB CB' KB'; nd_post). split; [exact CB'|]. split; [exact KB'|].
          exact (awf_fits L st X b WF IB).
      + intros POS''. apply Kres; [clear -Q1 RI1; unfold aregion in *; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF, K_REGION in *; lia | clear -POS''; lia |].
        destruct (Z.eqb_spec c'' c) as [->|NE]; [right; right; clear -G4 UBN; lia|].
        destruct (SIDE NE) as [D|D]; [left; clear -D Q1 Q2; unfold K_FREEARR_OFF, K_REGION in *; lia | right; right; clear -D Q1 UBN; lia].
      + (* [comment removed for export] *)
        destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb].
        unfold aslot_busy, bnew. cbn [xb_st xb_class xb_n xb_b1 xb_ctx xb_slot xb_alloc xb_user xb_hdr].
        unfold xb_user, xb_hdr, xb_alloc. cbn [xb_class xb_slot xb_n]. rewrite <- EAB. fold S. rewrite <- EUB.
        split; [| split].
        * intros R16. split.
          -- replace (UB - 16) with (UB + -16) by (clear; lia). unfold AMAGIC. exact (LH' R16).
          -- eapply junk_frame; [exact (LHJ R16) | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; clear -Hp R16 RZR G1 RSP G2 EUB RI3 N NSZ NS RSR; lia.
        * exists 2. split; [reflexivity|]. replace (UB - 16) with (UB + -16) by (clear; lia). exact HDR'.
        * replace (S - rz_size n) with (n + (S - rz_size n - n)) by (clear; lia).
          apply (junk_merge m' UB n (S - rz_size n - n)); [| | clear -N; lia | clear -NSZ NS RSR N; lia].
          -- pose proof (junk_of_cells m' _ _ UF') as J. cbn [cells_size csize] in J. rewrite Nat.add_0_r, Z2Nat.id in J by (clear -N; lia). exact J.
          -- eapply junk_frame; [exact TL | exact MUn | exact WM |]. intros Hp.
             unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
             apply Kres; [| | clear -Hp; lia | right; right; clear; lia].
             ++ clear -G1 RSP EUB RZR N. lia.
             ++ clear -G2 RI3 EUB NSZ NS RSR N RZR. lia.
    - (* [comment removed for export] *)
      eapply (aslot_shadow_update L _ m m' MUn WM st _ X X' c'' (if c'' =? c then k else -1));
        [exact SHADOW | apply st_fast_ndist | exact EC2 | exact EC1 | | | | apply shlen_nonneg; clear -QS; lia].
      + intros k'' Hk'' NEk. (pose proof (slot_in_region L st c'' k'' ltac:(clear -QS; lia) (proj1 Q1) Hk'') as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
        pose proof (slot_aligned L c'' k'' SAL ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) as AL''.
        split.
        * unfold X'. rewrite xfast_busy_of. destruct (Z.eqb_spec c c'') as [<-|NE]; [| reflexivity].
          rewrite Z.eqb_refl in NEk. destruct (Z.eqb_spec k k'') as [<-|NK']; [exfalso; exact (NEk eq_refl)| reflexivity].
        * apply Kshad.
          -- rewrite shad_div. unfold ASHOFF. clear -P5 RI1 RES RHI. Z.div_mod_to_equations. lia.
          -- rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -P4 Q1 Q2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
          -- apply shlen_nonneg. clear -QS; lia.
          -- destruct (Z.eqb_spec c'' c) as [->|NE].
             ++ destruct (slots_disjoint L c k'' k ltac:(clear -Hk''; lia) ltac:(clear -KR; lia) NEk ltac:(clear -QS; lia)) as [D|D]; rewrite <- EAB in D; fold S in D.
                ** left. apply shad_sep; [clear -D UBN; lia| clear -AL''; Z.div_mod_to_equations; lia].
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact D.
             ++ destruct (SIDE NE) as [D|D].
                ** left. apply shad_sep; [| clear -AL''; Z.div_mod_to_equations; lia]. unfold K_FREEARR_OFF, K_REGION in *. clear -D P4 Q1 Q2 UBN. lia.
                ** right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D P5. lia.
      + intros POS''. apply Kshad.
        * rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. Z.div_mod_to_equations. lia.
        * rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
        * clear -POS''; lia.
        * destruct (Z.eqb_spec c'' c) as [->|NE].
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. exact G4.
          -- destruct (SIDE NE) as [D|D].
             ++ left. apply shad_sep.
                ** unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
                ** pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM. clear -AM RM''. Z.div_mod_to_equations. lia.
             ++ right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE]; [| intros Hk0; exfalso; clear -Hk0; lia]. intros _.
        unfold X'. rewrite xfast_busy_of, !Z.eqb_refl. cbn [andb]. rewrite <- EAB. fold S.
        unfold slot_shadow_bytes, bnew. cbn [xb_n xb_st]. unfold block_shadow_bytes.
        change (shlen (rz_size n)) with grz. rewrite <- (shlen_floor n). change (shlen (n - n mod 8)) with g. rewrite ROOM.
        (* [comment removed for export] *)
        destruct SHADOW as [SHK _]. specialize (SHK k KR). rewrite NB in SHK. rewrite <- EAB in SHK. fold S in SHK. cbn [slot_shadow_bytes] in SHK.
        change (rw_cells asegs m (shad AB) [CB (Z.to_nat (shlen S)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S)))]) with (fill_at m (shad AB) (shlen S) 250) in SHK.
        destruct (fill_split m (shad AB) grz (shlen S - grz) 250 ltac:(replace (grz + (shlen S - grz)) with (shlen S) by (clear; lia); exact SHK)
                    ltac:(clear -GR3; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [F1 R1].
        destruct (fill_split m (shad AB + grz) (g + room) (shlen S - grz - (g + room)) 250
                    ltac:(replace (g + room + (shlen S - grz - (g + room))) with (shlen S - grz) by (clear; lia); exact R1)
                    ltac:(clear -GR4 GR5; lia) ltac:(clear -GR6 GR4 GR5; lia)) as [_ F2].
        eapply fill_frame in F1; [| exact MUn | exact WM | intros _; apply Kshad; [clear -GR8; lia | clear -GR9 GR6 GR4 GR5 GR3; lia | clear -GR3; lia | left; clear -GR7; lia]].
        replace (shad AB + grz + (g + room)) with (PG + room) in F2 by (subst PG; clear -GR7; lia).
        eapply fill_frame in F2; [| exact MUn | exact WM | intros Hp; apply Kshad; [subst PG; clear -GR8 GR7 GR3 GR4 GR5; lia | clear -GR9 GR6 GR7 GR3 GR4 GR5 Hp; subst PG; lia | clear -Hp; lia | right; clear; lia]].
        unfold fill_at in F1, F2. change (shlen (n - n mod 8)) with g in SHU'.
        replace (shad UB) with (shad AB + Z.of_nat (Z.to_nat grz)) in SHU' by (clear -GR7 GR3; lia).
        destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0].
        * assert (R0 : room = 0) by (rewrite RMQ; reflexivity). clearbody PG. subst room. rewrite app_nil_r.
          replace (PG + 0) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' F2)) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + Z.to_nat (shlen S - grz - (g + 0))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          exact FIN.
        * assert (RM1 : room = 1) by (rewrite RMQ; reflexivity). clearbody PG. subst room. specialize (SHP' M0). apply cb_of_C1 in SHP'.
          replace PG with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g)) in SHP' by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          replace (PG + 1) with (shad AB + Z.of_nat (Z.to_nat grz) + Z.of_nat (Z.to_nat g) + Z.of_nat 1) in F2 by (clear -GR7 GR3 GR4 PGE_; subst g; lia).
          pose proof (cb_app m' _ _ _ _ _ F1 (cb_app m' _ _ _ _ _ SHU' (cb_app m' _ _ _ _ _ SHP' F2))) as FIN.
          replace (Z.to_nat grz + (Z.to_nat g + (1 + Z.to_nat (shlen S - grz - (g + 1)))))%nat with (Z.to_nat (shlen S)) in FIN by (clear -GR3 GR4 GR6; lia).
          rewrite <- app_assoc. cbn [app] in FIN. exact FIN. }
  (* [comment removed for export] *)
  assert (HQ' : AQ L (st_fast st c n cnt) X' m').
  { eapply (hq_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HQ | exact MUn | exact WM | |].
    - unfold quar_untouched. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      do 10 (apply Forall_cons; [cbn [fst snd];
        split; [clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N UBN GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 D_t_res DL7 DL8 TBND TIMG NBND DL3 SBND DL6 RHI; unbox D_t_res; unbox DL7; unbox DL8; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        split; [clear -CEIL LO TL1 C16 N G1 RSP RES EUB RZR GR8 GR7 GR3 DL1 DL4 TBND TIMG NBND DL3 SBND DL6 RHI; lia|];
        intros b Hb; (nd_pre (BB b Hb) 5%nat; intros Bb1 Bb2 Bb3 Bb4 Bb5; nd_post); destruct (xb_st b); [exact I| |];
        clear -Bb1 Bb2 Bb3 CEIL LO RES C16 EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 G2 DL1 DL2 DL4 DL5 D_t_res D_n_res D_s_res UBN NBND DL3 SBND DL6 RHI;
        unbox D_t_res; unbox D_n_res; unbox D_s_res; lia |]).
      apply Forall_nil.
    - unfold quar_same. rewrite E1, E8, E9, E10, E11. repeat (split; [reflexivity|]). split.
      + intros b Hb. destruct (xb_st b); [exact I| right; exact Hb | right; exact Hb].
      + intros b [<-|Hb]; [exact I|]. destruct (xb_st b); [exact I| exact Hb | exact Hb]. }
  assert (HS' : ASEC L (st_fast st c n cnt) X' m').
  { eapply (hs_frame _ HL L st (st_fast st c n cnt) X X' m m'); [exact HS | exact MUn | exact WM | |].
    - unfold sec_untouched, aknown. unfold AINSTANCE, K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHB1 : shad (al_space_beg L) + 536870912 <= shad AB).
      { rewrite !shad_div. unfold aregion, K_REGION in G5. change (2^32) with 4294967296 in G5. clear -G5 C16. Z.div_mod_to_equations. lia. }
      assert (SHB2 : shad (AB + S) <= shad (al_space_beg L) + 17179869184).
      { rewrite !shad_div. clear -G2. Z.div_mod_to_equations. lia. }
      (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      do 3 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL2 C16 TBND TIMG; lia |]).
      do 2 (apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha G1 G2 UBN N RSP; lia |]).
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha GR7 GR3 PGB SHB1 SHB2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; left; left; unfold AIMG_HI; clear -Ha; lia |].   (* [comment removed for export] *)
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 8 right; left; clear -Ha; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 9 right; left; clear -Ha; lia |].
      apply Forall_nil.
    - unfold sec_same. rewrite E2, E3, E4, E6. repeat (split; [reflexivity|]).
      assert (NONE : (a_live st) !! (a_next st) = None).
      { destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as FF. clear -FF. lia. }
      split.
      + intros p mb ms n'. destruct (N.eq_dec p (a_next st)) as [->|NE].
        * rewrite lookup_insert_eq. split; [intros HH; discriminate| intros HH]. exfalso. rewrite NONE in HH. discriminate.
        * rewrite lookup_insert_ne by congruence. first [ solve [ clear; tauto ] | tauto ].   (* [comment removed for export] *)
      + eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [exact NONE| exact E6| exact E8| exact E10]. }
  assert (AR' : AREP (AH DI AQ ASEC AFK) L (st_fast st c n cnt) X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split; [exact CLS'|].
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact DEP'|].
    split; [eapply arelro_frame; [exact MUn | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUn | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI; lia|].
    split; [| eapply arep_rt3_frame; [exact MUn | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI; lia |]); apply Forall_nil].
    intros c'' Hc''. (pose proof (st_fast_counters st c n cnt c'') as ndP__; nd_pre ndP__ 5%nat; intros EC1 EC2 EC3 EC4 EC5; nd_post).
    (nd_pre (PERC c'' Hc'') 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). pose proof (aregion_mod L c'' SAL) as RM''. unfold K_NUM_CLASSES in Hc''.
    assert (RI : al_res L <= aregion L c'' /\ aregion L c'' + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc'' RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    assert (SIDE : c'' <> c -> aregion L c'' + K_REGION <= AB \/ AB + S <= aregion L c'').
    { intros NE. destruct (proj1 (Z.lt_gt_cases c'' c) NE) as [LT|GT].
      - left. specialize (RC _ _ LT). clear -RC G5. lia.
      - right. specialize (RC _ _ GT). unfold K_REGION, K_FREEARR_OFF in *. clear -RC G4 A1 A2. lia. }
    eapply (ashadow_avail_frame L _ m m' MUn WM st); [exact (AVL c'' ltac:(unfold K_NUM_CLASSES; clear -Hc''; lia)) | exact EC1 | exact EC4 | |].
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, aregion in *. clear -Q1 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_FREEARR_OFF in *. clear -G4 A1. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| clear -RM'' Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia]. unfold K_FREEARR_OFF, K_REGION in *. clear -D Q1 Q2 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D Q1. lia.
    - intros POS''. apply Kshad.
      + rewrite shad_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, aregion in *. clear -Q5 Q6 RI1 RES RHI. Z.div_mod_to_equations. lia.
      + rewrite shad_div, shlen_div. unfold ASHOFF, afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3 RES RHI. Z.div_mod_to_equations. lia.
      + clear -POS''; lia.
      + destruct (Z.eqb_spec c'' c) as [->|NE].
        * right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -G4 A1 A2 Q5 Q6. lia.
        * destruct (SIDE NE) as [D|D].
          -- left. apply shad_sep; [| unfold afreearr, K_FREEARR_OFF; clear -RM'' Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia].
             unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -D Q5 Q6 UBN. lia.
          -- right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold afreearr, K_FREEARR_OFF in *. clear -D Q1 Q5 Q6. lia. }
  (* [comment removed for export] *)
  pose proof (ablocks_fast L st X LB c k n cnt b1' id WF BL) as BL'. rewrite <- EAB, <- EUB in BL'. fold X' in BL'.
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  pose proof (ao_fake L ALO) as FKO. (pose proof (aobj_int _ _ FKO ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros FKi _ [kF FKs]; nd_post). unfold aobj in FKO.   (* [comment removed for export] *)
  pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_store_fake L ALO) as D_s_f.
  unfold adisj in D_t_f, D_f_res, D_n_f, D_s_f. box D_t_f. box D_f_res. box D_n_f. box D_s_f.
  assert (HBK : forall b, In b LB -> disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (ab_addr b) (ab_size b)).
  { intros [[p|cls] A n'] Hin; cbn [ab_addr ab_size].
    - destruct (proj1 BL p A n' Hin) as [(b & Hb & Sb & Ub & Nb)|(mb & ms & Lp & EUA & Gs)].
      + (nd_pre (BB b Hb) 5%nat; intros Bb1 Bb2 Bb3 Bb4 Bb5; nd_post).
        pose proof (awf_fits L st X b WF Hb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
        apply Kres; clear -Bb1 Bb2 Bb3 FIT; lia.
      + (* [comment removed for export] *)
        cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
        destruct (ablk_int _ _ Gs2) as [kB GB].   (* [comment removed for export] *)
        apply Kobj; clear -GB Gs3 Gs4 Gs5 SF Ct Cr Cn Cs; lia.
    - (nd_pre (FKD cls A n' Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
      apply Kobj; [clear -K1 K3 FKO FKi FKs; lia | clear -K3 FKO FKi FKs; lia | exact K2 | clear -K1 K3 D_t_f; unbox D_t_f; lia
                  | clear -K1 K3 D_f_res; unbox D_f_res; lia | clear -K1 K3 D_n_f; unbox D_n_f; lia | clear -K1 K3 D_s_f; unbox D_s_f; lia]. }
  assert (HFS : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> forall a', FA <= a' < FA + sz ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (shad a') 1).
  { intros cls FA sz Hin a' Ha'. (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
    apply Kshad; [rewrite shad_div; unfold ASHOFF; clear -K1 FKO Ha' FKi FKs; Z.div_mod_to_equations; lia
                 | rewrite shad_div; unfold ASHOFF; clear -K3 FKO Ha' FKi FKs; Z.div_mod_to_equations; lia | clear; lia |].
    pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
    - left. rewrite GR7, (shad_div a'), (shad_div AB). clear -D Ha' K3 RSP G1 GR3. Z.div_mod_to_equations. lia.
    - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      clear -D Ha' K1 RSP G2. lia. }
  (* [comment removed for export] *)
  assert (TLSK : forall TA tk, ATPv + -200 <= TA -> TA + tk <= ATPv + 312 -> 0 <= tk ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) TA tk).
  { intros TA tk TH1 TH2 TH3. pose proof ATPv_img as TI. apply Kimg; clear -TH1 TH2 TH3 TI; unfold AIMG_HI; lia. }
  assert (TLSS : forall a', ATPv + -200 <= a' < ATPv + 312 ->
      disjoint_from (Wn (bv_unsigned sp) (al_t L) c AB UB (PG + room) n (al_nodes L) (al_store L)) (shad a') 1).
  { intros a' Ha'. pose proof ATPv_img as TI. apply Klow; clear -Ha' TI; try (rewrite shad_div; unfold ASHOFF); try Z.div_mod_to_equations; lia. }
  assert (HFK' : AFK L (HB (a_next st) UB n :: LB) m').
  { eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MUn | exact WM |] |].
    - pose proof (ao_dtls L ALO) as DTO. unfold aobj in DTO. (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD DTs] [jD DTi]; nd_post).   (* [comment removed for export] *)
      pose proof (ad_t_dtls L ALO) as D1. pose proof (ad_dtls_res L ALO) as D2. pose proof (ad_nodes_dtls L ALO) as D3. pose proof (ad_store_dtls L ALO) as D4.
      unfold adisj in D1, D2, D3, D4.
      unfold fake_untouched. unfold K_SPACE_SIZE in *. change (2^37) with 137438953472 in *.
      assert (SHF : (shad (al_fake L) + shlen 11571200 <= shad UB \/ PG + room <= shad (al_fake L))
                    /\ 2148239360 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594333495296).   (* [comment removed for export] *)
      { split; [| rewrite shad_div, shlen_div; unfold ASHOFF; clear -FKO FKi FKs; Z.div_mod_to_equations; lia].
        pose proof D_f_res as DF. unbox DF. destruct DF as [D|D].
        - left. rewrite GR7, shlen_div, (shad_div (al_fake L)), (shad_div AB). clear -D RSP G1 GR3. Z.div_mod_to_equations. lia.
        - right. eapply Z.le_trans; [exact PGB|]. apply shad_mono. clear -D RSP G2. lia. }
      (nd_pre SHF 3%nat; intros SHF1 SHF2 SHF3; nd_post).
      do 10 (apply Forall_cons; [cbn [fst snd];
        clear -CEIL LO TL1 TL2 C16 G1 G2 RSP RES EUB RZR N GR8 GR7 GR3 GR11 PGB GR10 GR9 DL1 DL2 DL4 DL5 FKO DTO D1 D2 D3 D4 D_t_f D_f_res D_n_f D_s_f SHF1 SHF2 SHF3 UBN TBND TIMG NBND DL3 SBND DL6 RHI FKi FKs DTs DTi D_l_t D_l_r D_l_n D_l_s TLN ATR0;      (* [comment removed for export] *)
       
        (* [comment removed for export] *)
        first [ lazymatch goal with
                | |- context [al_t _] => unbox D_t_f; clear D_f_res D_n_f D_s_f
                | |- context [al_nodes _] => unbox D_n_f; clear D_t_f D_f_res D_s_f
                | |- context [al_store _] => unbox D_s_f; clear D_t_f D_f_res D_n_f
                | |- _ => unbox D_f_res; clear D_t_f D_n_f D_s_f
                end; unfold AIMG_HI in *; repeat (split; [fu_lia|]); fu_lia
              | unbox D_t_f; unbox D_f_res; unbox D_n_f; unbox D_s_f; unfold AIMG_HI in *; repeat (split; [lia|]); lia ] |]).
      apply Forall_nil.
    - intros cls FA sz. cbn. split; [intros [E|Hin]; [discriminate| exact Hin] | intros Hin; right; exact Hin]. }
  (* [comment removed for export] *)
  assert (PSP : PG + room <= shad ATOP).
  { eapply Z.le_trans; [exact PGB|]. apply shad_mono. unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *. clear -G2 SP2. lia. }
  split; [apply fp_le_refl|].
  do 15 eexists. exists m'. split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|]. split.
  { eapply (aheap_pres_prim CI); [exact KF | exact CI_OK | exact MUn | exact WM | exact HBK | exact HFS | exact PSP | exact TLSK | exact TLSS | apply Klow; unfold AIMSH_LO, AIMSH_LEN; clear; lia
      | rewrite <- (ao_ahm_eq L ALO); unfold AAHM_SZ; pose proof (ao_ahm L ALO) as OAH; pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI;
      pose proof (ad_ahm_t L ALO) as DA1; pose proof (ad_ahm_res L ALO) as DA2; pose proof (ad_ahm_nodes L ALO) as DA3; pose proof (ad_ahm_store L ALO) as DA4;
      unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI, adisj in OAH, OAHI, DA1, DA2, DA3, DA4; apply Kobj; clear -OAH OAHI DA1 DA2 DA3 DA4; lia]. }
  cbn [fst snd]. exists UB.
  split; [reflexivity|]. split.
  { unfold ablock_range. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    split; [unfold ablk; right; clear -G1 SP1 EUB RZR UBN G2 SP2 N; lia|]. split; [clear -N; lia|]. split; [clear -UBN G2 SP2; lia|].   (* [comment removed for export] *)
    rewrite EUB. clear -G3 RZM RZR. Z.div_mod_to_equations; lia. }
  split.
  { split; [exact ALO|]. split; [eapply arng_fast; [exact WF| exact ARNG]|]. split; [| exact HFK']. exists X'. split; [exact AR' | exact BL']. }
  split; [exact UF'|].
  (nd_pre ARNG 11%nat; intros _ _ _ _ _ _ _ _ _ RCLS _; nd_post). (nd_pre (RCLS c HCK) 4%nat; intros RREG RSREG _ _; nd_post).
  split; [| split].
  - eapply rng_sub'; [exact RREG|]. clear -G5 G4 A1 UBN. lia.
  - eapply rng_sub'; [exact RSREG|]. pose proof (aregion_mod L c SAL) as RM.
    split; [apply shad_mono; clear -G5 UBN; lia|].
    rewrite <- (shad_add_shlen (aregion L c) (c_mapped_user (get_cls st c))) by (clear -RM; Z.div_mod_to_equations; lia).
    rewrite (shad_div UB), shlen_div, (shad_div (aregion L c + c_mapped_user (get_cls st c))).
    pose proof (size_of_class_facts c HCK) as [_ S16]. fold S in S16.
    clear -UBN G4 A1 G3 S16. Z.div_mod_to_equations. lia.
  - intros NP. exfalso. rewrite PRIM in NP. discriminate.
Qed.
End Zd1.
#[using="HL CI_OK"] Theorem store_primU : ltac:(let t := eval cbv delta [store_primU__stmt] in store_primU__stmt in exact t).
Proof. exact store_primU__body. Qed.

End S.

End CANSEC1.
End TwB.
