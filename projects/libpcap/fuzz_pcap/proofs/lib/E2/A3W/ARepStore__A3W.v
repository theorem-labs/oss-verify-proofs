(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA StepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W.
From LinuxProcessSemantics.LinuxProcessSem Require Specs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ARepStore.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.
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



Section Kinds.
Variables (sp t c AB S UB PGE n nodes store res ctx lo grz ssz : Z).
(* [comment removed for export] *)
Definition kfacts : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (1 <= c <= 16)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ UB - 16 >= AB /\ 1 <= n /\ UB + n <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ shad UB + 1 <= PGE /\ PGE <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6303744 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6303744 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6303744 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfacts.

(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Ltac kind := pose proof KF as KF'; unfold kfacts, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  (nd_pre KF' 8%nat; intros F_lo F_t F_c F_res F_slot F_sh F_ns F_ctx; nd_post);
  cbn [disjoint_from]; repeat (split; [first [ lia_rel | lia ]|]); first [ lia_rel | lia | exact I ].   (* [comment removed for export] *)
















(* [comment removed for export] *)

End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bnew (c k n : Z) (p : aptr) (b1 ctx : Z) : xbusy := mkXBusy c k n (BLive p) b1 ctx.
Definition xfast (X : aconc) (c k n : Z) (p : aptr) (b1 ctx : Z) : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c')
          (bnew c k n p b1 ctx :: x_busy X).

#[using="Type"] Lemma xfast_busy_of : forall X c k n p b1 ctx c' k',
  busy_of (xfast X c k n p b1 ctx) c' k' = if (c =? c') && (k =? k') then Some (bnew c k n p b1 ctx) else busy_of X c' k'.
Proof. intros. unfold xfast, busy_of. cbn. destruct ((c =? c') && (k =? k')); reflexivity. Qed.
#[using="Type"] Lemma xfast_busy_slots : forall X c k n p b1 ctx c',
  busy_slots (xfast X c k n p b1 ctx) c' = (if c =? c' then [k] else []) ++ busy_slots X c'.
Proof. intros. unfold xfast, busy_slots. cbn. destruct (c =? c'); reflexivity. Qed.
#[using="Type"] Lemma xfast_cls : forall X c k n p b1 ctx c',
  x_cls (xfast X c k n p b1 ctx) c' = if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c'.
Proof. reflexivity. Qed.




Definition awf_fast__stmt : Prop := forall L st X c k n cnt b1 ctx,
  awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None ->
  1 <= n <= AREQMAX -> rounded_size n + rz_size n <= size_of_class c -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  awf L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 2).
Variable c : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 3).
Variable k : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 4).
Variable n : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 5).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 6).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 7).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 8).
#[using="Type"] Lemma awf_fast__body : ltac:(let T := type of (fun (h : awf_fast__stmt) => h L st X c k n cnt b1 ctx) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (c, (k, (n, (cnt, (b1, ctx))))))))) as _.
  intros WF HC CNT POS NK NB N FIT B1 AT1 CTX.
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (st_fast_fields st c n cnt) as ndP__; nd_pre ndP__ 11%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11; nd_post).
  assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
  { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC CNT. lia. }
  assert (LRL : Z.of_nat (length (removelast (xc_cache (x_cls X c)))) = cnt - 1).
  { rewrite length_removelast; [clear -LENC CNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC CNT POS. lia. }
  assert (PNE : forall p ch, a_live st !! p = Some ch -> p <> a_next st).
  { intros p ch Hp E. pose proof (FRESH p ch Hp) as F. subst p. clear -F. lia. }
  unfold awf. rewrite E1, E2, E6, E7.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { (* [comment removed for export] *)
    intros c' HC'. rewrite st_fast_cls, st_fast_max_count, st_fast_ndist, xfast_cls, xfast_busy_slots.
    destruct (Z.eqb_spec c' c) as [->|NE].
    - rewrite Z.eqb_refl. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count cls_set_count app].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
      split; [exact LENF|]. split; [exact LRL|]. split; [clear -CNTB CNT POS; lia|].
      rewrite CACHE in ND, RANGE. rewrite <- !app_assoc in ND, RANGE. cbn [app] in ND, RANGE.
      split; [exact ND | exact RANGE].
    - destruct (Z.eqb_spec c c') as [EQ|_]; [exfalso; clear -EQ NE; lia|]. cbn [app].
      (nd_pre (PERC c' HC') 12%nat; intros B1' B2 B3 B4 B5 B6 B7 BLENF BLENC BCNTB BND BRANGE; nd_post).
      cbv zeta. repeat lazymatch goal with |- _ /\ _ => split end.
      all: first [exact B1' | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7 | exact BLENF | exact BLENC | exact BCNTB | exact BND | exact BRANGE
                 | exact (proj1 B1') | exact (proj2 B1') | exact (proj1 B6) | exact (proj2 B6) | exact (proj1 BCNTB) | exact (proj2 BCNTB)
                 | match goal with |- ?G => idtac "PERC-LEFT" G end]. }
  split.
  { intros c' HC'. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; [exfalso; exact (HC' HC)| exact (OUTC c' HC')]. }
  split.
  { (* [comment removed for export] *)
    intros b [<-|Hb].
    - cbn. split; [exact HC|]. split; [exact N|]. split; [exact FIT|]. split; [exact B1|]. split; [exact AT1|]. split; [exact CTX|]. apply lookup_insert_eq.
    - destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [p| |]; [| exact M | exact M].
      (nd_pre M 6%nat; intros M1 M2 M3 M3' M4 M5; nd_post). split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M3'|]. split; [exact M4|].
      rewrite lookup_insert_ne by (symmetry; eapply PNE; exact M5). exact M5. }
  split.
  { (* [comment removed for export] *)
    intros p c0 n0 Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
    - rewrite lookup_insert_eq in Hp. injection Hp as <- <-. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. auto.
    - rewrite lookup_insert_ne in Hp by congruence. (nd_pre (LIVE p c0 n0 Hp) 3%nat; intros b Hb R; nd_post). exists b. split; [right; exact Hb| exact R]. }
  split.
  { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [clear; lia|].
    rewrite lookup_insert_ne in Hp by congruence. pose proof (FRESH p ch Hp) as F. clear -F. lia. }
  (* [comment removed for export] *)
  intros b0 b2 [<-|H0] [<-|H2] EQ [p Hp]; [reflexivity| exfalso | exfalso | exact (UNIQ b0 b2 H0 H2 EQ (ex_intro _ p Hp))].
  - cbn in EQ. destruct (BUSY b2 H2) as [_ M]. rewrite <- EQ in M. (nd_pre M 6%nat; intros _ _ _ _ _ M5; nd_post). exact (PNE _ _ M5 eq_refl).
  - cbn in EQ. destruct (BUSY b0 H0) as [_ M]. rewrite EQ in M. (nd_pre M 6%nat; intros _ _ _ _ _ M5; nd_post). exact (PNE _ _ M5 eq_refl).
Qed.
End Zd1.
#[using="Type"] Lemma awf_fast : ltac:(let t := eval cbv delta [awf_fast__stmt] in awf_fast__stmt in exact t).
Proof. exact awf_fast__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ablocks_fast : forall L st X LB c k n cnt b1 ctx,
  awf L st X -> ablocks L st X LB ->
  ablocks L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx) (HB (a_next st) (aslot_addr L c k + rz_size n) n :: LB).
Proof.
  intros L st X LB c k n cnt b1 ctx WF (BH & BF & NDI & NDL).
  (nd_pre WF 11%nat; intros _ _ _ _ _ _ _ BUSY _ FRESH _; nd_post).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. (nd_pre M 6%nat; intros _ _ _ _ _ M5; nd_post). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. left. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. unfold xb_user, xb_alloc. cbn. auto.
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms & Lp & R)].
      * left. exists b. split; [right; exact Hb| exact R].
      * right. exists mb, ms. split; [| exact R]. (pose proof (st_fast_fields st c n cnt) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ E6 _; nd_post). rewrite E6.
        rewrite lookup_insert_ne; [exact Lp|]. intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. (nd_pre Hin 3%nat; intros b Hb Hp; nd_post).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unbx {P : Prop} (b : boxed P) : P := match b with Box _ p => p end.









#[using="Type"] Lemma arng_fast : forall L RNG st X c n cnt, awf L st X -> arng L RNG st -> arng L RNG (st_fast st c n cnt).
Proof.
  intros L RNG st X c n cnt WF (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RC & RPA & RSC & RPSH & RTLS).
  (nd_pre WF 11%nat; intros _ _ _ _ _ _ _ _ _ FRESH _; nd_post).
  (pose proof (st_fast_fields st c n cnt) as ndP__; nd_pre ndP__ 11%nat; intros _ _ E3 _ _ E6 _ E8 _ E10 _; nd_post).
  unfold arng. repeat (split; [assumption|]). split; [| split].
  - intros c' Hc'. (pose proof (st_fast_counters st c n cnt c') as ndP__; nd_pre ndP__ 5%nat; intros E1 E2 _ E4 E5; nd_post). cbv zeta. rewrite E1, E4. exact (RC c' Hc').
  - rewrite E3. exact RPA.
  - split; [| split; [exact RPSH | exact RTLS]]. eapply RSEC_perm; [apply Permutation_sym; eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [| exact E6| exact E8| exact E10]| exact RSC].
    destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aalloc2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_aalloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc__A3W.F_amalloc_icpt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB.
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



Section Kinds.
Variables (sp t c AB S UB PGE n nodes store res ctx lo grz ssz : Z).
(* [comment removed for export] *)
Definition kfacts : Prop :=
     (ATOP <= lo /\ lo <= sp - 4096)
  /\ (sclr t 4096 /\ iclr t 4096 /\ 4096 <= t /\ t + 4096 <= ATOP)      (* [comment removed for export] *)
  /\ (1 <= c <= 16)
  /\ (17594333495296 <= res /\ res + 137439023104 <= ATOP)
  /\ (res + 4096 <= AB /\ AB + S <= res + 137439023104 /\ UB - 16 >= AB /\ 1 <= n /\ UB + n <= AB + S)
  /\ (2201439137792 <= shad AB /\ shad UB = shad AB + grz /\ 2 <= grz /\ shad UB + 1 <= PGE /\ PGE <= shad AB + ssz
      /\ shad AB + ssz <= 17594333495296)
  /\ (sclr nodes 1048576 /\ 6307840 <= nodes /\ nodes + 1048576 <= ATOP /\ sclr store 8388608 /\ 6307840 <= store /\ store + 8388608 <= ATOP)
  /\ (sclr ctx 65536 /\ 6307840 <= ctx /\ ctx + 65536 <= ATOP).
Hypothesis KF : kfacts.

(* [comment removed for export] *)
Local Ltac hide_disj_all := repeat match goal with H : (_ \/ _) |- _ => change (?P) with (sf_hide P) in H end.
Local Ltac hide_disj_but X :=
  repeat match goal with H : (_ \/ _) |- _ => tryif constr_eq H X then fail else change (?P) with (sf_hide P) in H end.
Local Ltac lia_rel := first [ solve [ hide_disj_all; lia ] | match goal with X : (_ \/ _) |- _ => solve [ hide_disj_but X; lia ] end ].
Ltac kind := pose proof KF as KF'; unfold kfacts, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  (nd_pre KF' 8%nat; intros F_lo F_t F_c F_res F_slot F_sh F_ns F_ctx; nd_post);
  cbn [disjoint_from]; repeat (split; [first [ lia_rel | lia ]|]); first [ lia_rel | lia | exact I ].   (* [comment removed for export] *)
















(* [comment removed for export] *)

End Kinds.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bnew (c k n : Z) (p : aptr) (b1 ctx : Z) : xbusy := mkXBusy c k n (BLive p) b1 ctx.
Definition xfast (X : aconc) (c k n : Z) (p : aptr) (b1 ctx : Z) : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c')
          (bnew c k n p b1 ctx :: x_busy X).

#[using="Type"] Lemma xfast_busy_of : forall X c k n p b1 ctx c' k',
  busy_of (xfast X c k n p b1 ctx) c' k' = if (c =? c') && (k =? k') then Some (bnew c k n p b1 ctx) else busy_of X c' k'.
Proof. intros. unfold xfast, busy_of. cbn. destruct ((c =? c') && (k =? k')); reflexivity. Qed.
#[using="Type"] Lemma xfast_busy_slots : forall X c k n p b1 ctx c',
  busy_slots (xfast X c k n p b1 ctx) c' = (if c =? c' then [k] else []) ++ busy_slots X c'.
Proof. intros. unfold xfast, busy_slots. cbn. destruct (c =? c'); reflexivity. Qed.
#[using="Type"] Lemma xfast_cls : forall X c k n p b1 ctx c',
  x_cls (xfast X c k n p b1 ctx) c' = if c' =? c then mkXClass (xc_free (x_cls X c)) (removelast (xc_cache (x_cls X c))) else x_cls X c'.
Proof. reflexivity. Qed.




Definition awf_fast__stmt : Prop := forall L st X c k n cnt b1 ctx,
  awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k -> busy_of X c k = None ->
  1 <= n <= AREQMAX -> rounded_size n + rz_size n <= size_of_class c -> 0 <= b1 < 256 -> Z.land b1 3 = 1 -> 0 <= ctx < 2^31 ->
  awf L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx).
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 2).
Variable c : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 3).
Variable k : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 4).
Variable n : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 5).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 6).
Variable b1 : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 7).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'awf_fast__stmt 8).
#[using="Type"] Lemma awf_fast__body : ltac:(let T := type of (fun (h : awf_fast__stmt) => h L st X c k n cnt b1 ctx) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (c, (k, (n, (cnt, (b1, ctx))))))))) as _.
  intros WF HC CNT POS NK NB N FIT B1 AT1 CTX.
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (nd_pre (PERC c HC) 12%nat; intros A1 A2 A3 A4 A5 A6 A7 LENF LENC CNTB ND RANGE; nd_post).
  (pose proof (st_fast_fields st c n cnt) as ndP__; nd_pre ndP__ 11%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11; nd_post).
  assert (CACHE : xc_cache (x_cls X c) = removelast (xc_cache (x_cls X c)) ++ [k]).
  { apply cache_split_last. rewrite <- NK. f_equal. clear -LENC CNT. lia. }
  assert (LRL : Z.of_nat (length (removelast (xc_cache (x_cls X c)))) = cnt - 1).
  { rewrite length_removelast; [clear -LENC CNT POS; lia|]. intros E. rewrite E in LENC. cbn in LENC. clear -LENC CNT POS. lia. }
  assert (PNE : forall p ch, a_live st !! p = Some ch -> p <> a_next st).
  { intros p ch Hp E. pose proof (FRESH p ch Hp) as F. subst p. clear -F. lia. }
  unfold awf. rewrite E1, E2, E6, E7.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  { (* [comment removed for export] *)
    intros c' HC'. rewrite st_fast_cls, st_fast_max_count, st_fast_ndist, xfast_cls, xfast_busy_slots.
    destruct (Z.eqb_spec c' c) as [->|NE].
    - rewrite Z.eqb_refl. cbn [xc_free xc_cache c_allocated_user c_mapped_user c_num_freed c_mapped_free_array c_count cls_set_count app].
      split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|]. split; [exact A6|]. split; [exact A7|].
      split; [exact LENF|]. split; [exact LRL|]. split; [clear -CNTB CNT POS; lia|].
      rewrite CACHE in ND, RANGE. rewrite <- !app_assoc in ND, RANGE. cbn [app] in ND, RANGE.
      split; [exact ND | exact RANGE].
    - destruct (Z.eqb_spec c c') as [EQ|_]; [exfalso; clear -EQ NE; lia|]. cbn [app].
      (nd_pre (PERC c' HC') 12%nat; intros B1' B2 B3 B4 B5 B6 B7 BLENF BLENC BCNTB BND BRANGE; nd_post).
      cbv zeta. repeat lazymatch goal with |- _ /\ _ => split end.
      all: first [exact B1' | exact B2 | exact B3 | exact B4 | exact B5 | exact B6 | exact B7 | exact BLENF | exact BLENC | exact BCNTB | exact BND | exact BRANGE
                 | exact (proj1 B1') | exact (proj2 B1') | exact (proj1 B6) | exact (proj2 B6) | exact (proj1 BCNTB) | exact (proj2 BCNTB)
                 | match goal with |- ?G => idtac "PERC-LEFT" G end]. }
  split.
  { intros c' HC'. rewrite st_fast_cls. destruct (Z.eqb_spec c' c) as [->|NE]; [exfalso; exact (HC' HC)| exact (OUTC c' HC')]. }
  split.
  { (* [comment removed for export] *)
    intros b [<-|Hb].
    - cbn. split; [exact HC|]. split; [exact N|]. split; [exact FIT|]. split; [exact B1|]. split; [exact AT1|]. split; [exact CTX|]. apply lookup_insert_eq.
    - destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [p| |]; [| exact M | exact M].
      (nd_pre M 6%nat; intros M1 M2 M3 M3' M4 M5; nd_post). split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M3'|]. split; [exact M4|].
      rewrite lookup_insert_ne by (symmetry; eapply PNE; exact M5). exact M5. }
  split.
  { (* [comment removed for export] *)
    intros p c0 n0 Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
    - rewrite lookup_insert_eq in Hp. injection Hp as <- <-. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. auto.
    - rewrite lookup_insert_ne in Hp by congruence. (nd_pre (LIVE p c0 n0 Hp) 3%nat; intros b Hb R; nd_post). exists b. split; [right; exact Hb| exact R]. }
  split.
  { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [clear; lia|].
    rewrite lookup_insert_ne in Hp by congruence. pose proof (FRESH p ch Hp) as F. clear -F. lia. }
  (* [comment removed for export] *)
  intros b0 b2 [<-|H0] [<-|H2] EQ [p Hp]; [reflexivity| exfalso | exfalso | exact (UNIQ b0 b2 H0 H2 EQ (ex_intro _ p Hp))].
  - cbn in EQ. destruct (BUSY b2 H2) as [_ M]. rewrite <- EQ in M. (nd_pre M 6%nat; intros _ _ _ _ _ M5; nd_post). exact (PNE _ _ M5 eq_refl).
  - cbn in EQ. destruct (BUSY b0 H0) as [_ M]. rewrite EQ in M. (nd_pre M 6%nat; intros _ _ _ _ _ M5; nd_post). exact (PNE _ _ M5 eq_refl).
Qed.
End Zd1.
#[using="Type"] Lemma awf_fast : ltac:(let t := eval cbv delta [awf_fast__stmt] in awf_fast__stmt in exact t).
Proof. exact awf_fast__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ablocks_fast : forall L st X LB c k n cnt b1 ctx,
  awf L st X -> ablocks L st X LB ->
  ablocks L (st_fast st c n cnt) (xfast X c k n (a_next st) b1 ctx) (HB (a_next st) (aslot_addr L c k + rz_size n) n :: LB).
Proof.
  intros L st X LB c k n cnt b1 ctx WF (BH & BF & NDI & NDL).
  (nd_pre WF 11%nat; intros _ _ _ _ _ _ _ BUSY _ FRESH _; nd_post).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. (nd_pre M 6%nat; intros _ _ _ _ _ M5; nd_post). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. left. exists (bnew c k n (a_next st) b1 ctx). split; [left; reflexivity|]. cbn. unfold xb_user, xb_alloc. cbn. auto.
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms & Lp & R)].
      * left. exists b. split; [right; exact Hb| exact R].
      * right. exists mb, ms. split; [| exact R]. (pose proof (st_fast_fields st c n cnt) as ndP__; nd_pre ndP__ 7%nat; intros _ _ _ _ _ E6 _; nd_post). rewrite E6.
        rewrite lookup_insert_ne; [exact Lp|]. intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. (nd_pre Hin 3%nat; intros b Hb Hp; nd_post).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition unbx {P : Prop} (b : boxed P) : P := match b with Box _ p => p end.









#[using="Type"] Lemma arng_fast : forall L RNG st X c n cnt, awf L st X -> arng L RNG st -> arng L RNG (st_fast st c n cnt).
Proof.
  intros L RNG st X c n cnt WF (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & RC & RPA & RSC & RPSH & RTLS).
  (nd_pre WF 11%nat; intros _ _ _ _ _ _ _ _ _ FRESH _; nd_post).
  (pose proof (st_fast_fields st c n cnt) as ndP__; nd_pre ndP__ 11%nat; intros _ _ E3 _ _ E6 _ E8 _ E10 _; nd_post).
  unfold arng. repeat (split; [assumption|]). split; [| split].
  - intros c' Hc'. (pose proof (st_fast_counters st c n cnt c') as ndP__; nd_pre ndP__ 5%nat; intros E1 E2 _ E4 E5; nd_post). cbv zeta. rewrite E1, E4. exact (RC c' Hc').
  - rewrite E3. exact RPA.
  - split; [| split; [exact RPSH | exact RTLS]]. eapply RSEC_perm; [apply Permutation_sym; eapply (sec_chunks_of_insert_prim st _ (a_next st) c n); [| exact E6| exact E8| exact E10]| exact RSC].
    destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


End CANSEC1.
End TwB.
End ARepStore.

(* [comment removed for export] *)
Module ASecStore.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AMalloc_iface. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASec__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_amalloc_arep. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ASecModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.
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
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma sec_chunk_in_ranges : forall st mb ms n, In (CSec mb ms n) (sec_chunks_of st) -> In (mb, mb + ms) (asec_ranges st).
Proof.
  intros st mb ms n H. unfold sec_chunks_of in H. apply List.filter_In in H. destruct H as [H _].
  unfold asec_ranges. apply in_flat_map. exists (CSec mb ms n). split; [exact H| left; reflexivity].
Qed.

#[using="Type"] Lemma avoids_all_In : forall a n l iv, avoids_all a n l = true -> In iv l -> a + n <= fst iv \/ snd iv <= a.
Proof.
  intros a n l iv H Hin. unfold avoids_all in H. rewrite forallb_forall in H. specialize (H iv Hin).
  unfold iv_clear in H. apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma asec_wf_all : forall L st cs ch, asec_wf L st cs -> In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st cs ch (_ & _ & _ & _ & _ & WF1 & _) Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1.
  destruct ch as [c n|mb ms n]; [destruct W1|]. exists mb, ms, n. split; [reflexivity| exact W1].
Qed.

Section Valid.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (n a : Z).
Let ms := sec_map_size n.
Hypothesis ALO : alayout_ok L.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis FR : sfresh RESV st n a = true.
Hypothesis ROK : aresv_ok L RESV.

#[using="tlsI L RESV st N PRIM FR ROK"] Lemma valid_geo : a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP /\ 0 < ms /\ ms = sec_map_size n.
Proof.
  (nd_pre (sfresh_true_facts RESV st n a FR) 8%nat; intros _ _ AV _ POS AL TOPB _; nd_post).   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSB; nd_post).
  destruct ROK as (R1 & R2 & _).
  pose proof (pcov_clear _ _ _ _ _ R1 AV ltac:(unfold AIMG_HI; clear; lia) ltac:(clear -MSB; lia)) as C1.   (* [comment removed for export] *)
  pose proof (pcov_clear _ _ _ _ _ R2 AV ltac:(clear; lia) ltac:(clear -MSB; lia)) as C2.                    (* [comment removed for export] *)
  subst ms. split; [exact AL|]. split; [| split; [exact TOPB| split; [clear -MSB; lia| reflexivity]]].
  unfold ablk, KLS. unfold AIMG_HI in *. clear -C1 C2 POS TOPB MSB. lia.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
#[using="RESV st N PRIM FR ROK"] Lemma valid_hulls : Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L).
Proof.
  (nd_pre (sfresh_true_facts RESV st n a FR) 8%nat; intros _ _ AV _ _ _ _ _; nd_post).   (* [comment removed for export] *)
  (pose proof valid_geo as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ MSP _; nd_post).
  destruct ROK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16).      (* [comment removed for export] *)
  unfold astartup_hulls. fold (al_res L) in R3. change (4096 * al_V L 323%nat) with (al_dtls L) in R10.
  repeat (apply Forall_cons; [cbn [fst snd]; eapply pcov_clear; [first [ match goal with H : pcov _ ?l ?h |- pcov _ ?l' ?h' => constr_eq l l'; constr_eq h h'; exact H end | eassumption ]| exact AV| clear; lia| exact MSP] |]). apply Forall_nil.
Qed.

#[using="RESV st N PRIM FR ROK"] Lemma valid_clear : sec_clear L a ms.
Proof.
  pose proof valid_hulls as H. unfold astartup_hulls in H.
  repeat lazymatch type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] | _ => idtac end.
  cbn [fst snd] in *. unfold sec_clear, al_ahm. repeat split; lia.
Qed.

#[using="rc tlsI L RESV N PRIM FR ROK"] Lemma valid_chunks : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) (sec_chunks_of st).
Proof.
  (nd_pre (sfresh_true_facts RESV st n a FR) 8%nat; intros _ _ _ AV _ _ _ _; nd_post).   (* [comment removed for export] *)
  apply Forall_forall. intros ch Hin. destruct ch as [c k|mb ms' k]; cbn [sec_mb sec_ms].
  - (pose proof valid_geo as ndP__; nd_pre ndP__ 3%nat; intros _ G _; nd_post). (pose proof (ablk_lin _ _ G) as ndP__; nd_pre ndP__ 3%nat; intros _ G0 _; nd_post). right. clear -G0. lia.   (* [comment removed for export] *)
  - pose proof (avoids_all_In _ _ _ _ AV (sec_chunk_in_ranges st mb ms' k Hin)) as D. cbn [fst snd] in D. exact D.
Qed.

#[using="RESV st N PRIM FR ROK"] Lemma valid_wf1 : sec_wf1 L (CSec a ms n).
Proof.
  (pose proof valid_geo as ndP__; nd_pre ndP__ 5%nat; intros G1 G2 G3 G4 G5; nd_post). pose proof (sec_facts n N PRIM) as (NB & _).
  cbn [sec_wf1]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G5|].
  split; [lia|]. split; [exact PRIM| exact valid_clear].
Qed.
End Valid.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma wview_some : forall m (x : word) b, m x = Some b -> wview asegs m x = Some b.
Proof. intros m x b H. unfold wview. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma ashz_azero : forall L cs m a ms,
  ashz L cs m ->
  a mod 8 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= ms ->
  Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L) ->
  Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs ->
  azero m (shad a) (ms / 8).
Proof.
  intros L cs m a ms SHZ A8 ALO AHI MS0 HH HC.
  assert (PT : forall i, 0 <= i < ms / 8 -> m (wa (shad a + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. replace (shad a + i) with (shad (a + 8 * i)) by (rewrite !shad_div; clear -A8; Z.div_mod_to_equations; lia).
    apply SHZ.
    - unfold ablk, KLS, K_HIGH_MEM in *. unfold AIMG_HI in *. clear -Hi ALO AHI A8. Z.div_mod_to_equations. lia.   (* [comment removed for export] *)
    - eapply Forall_impl; [| exact HH]. cbn beta. intros iv Hiv. clear -Hi Hiv A8. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact HC]. cbn beta. intros ch Hch. clear -Hi Hch A8. Z.div_mod_to_equations. lia. }
  assert (SR : 0 <= shad a /\ shad a + ms / 8 <= 2^64).
  { (pose proof (ablk_lin _ _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 AL3 AL4; nd_post). rewrite shad_div. unfold ASHOFF in *. clear -AL2 AL4 AHI MS0. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  split; [exact PT|]. split; [lia|]. split; [lia|]. intros i Hi. rewrite (wview_some _ _ _ (PT i Hi)). discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_insert_sec : forall st st' p mb ms n,
  (a_live st) !! p = None ->
  a_live st' = <[p := CSec mb ms n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  Permutation (sec_chunks_of st') (CSec mb ms n :: sec_chunks_of st).
Proof.
  intros st st' p mb ms n NONE E1 E2 E3. unfold sec_chunks_of, achunks. rewrite E1, E2, E3, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
  apply Permutation_app_tail.
  pose proof (map_to_list_insert (a_live st) p (CSec mb ms n) NONE) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_trans; [apply filter_is_sec_perm; exact P|]. cbn. apply Permutation_refl.
Qed.

#[using="Type"] Lemma awf_fresh_none : forall L st X, awf L st X -> (a_live st) !! (a_next st) = None.
Proof.
  intros L st X WF. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. lia.
Qed.

#[using="Type"] Lemma awf_sec : forall L st X nres' a ms n, awf L st X -> awf L (st_sec st nres' a ms n) X.
Proof.
  intros L st X nres' a ms n WF.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 12%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12; nd_post).
  unfold awf. rewrite E1, E2, E7, E8.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. rewrite get_cls_st_sec, max_count_st_sec. unfold ndist. rewrite get_cls_st_sec. exact (PERC c Hc). }
  split. { intros c Hc. rewrite get_cls_st_sec. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CLB M]. split; [exact CLB|]. destruct (xb_st b) as [p| |]; try exact M.
           (nd_pre M 6%nat; intros M1 M2 M3 M4 M5 M6; nd_post). repeat (split; [assumption|]).
           rewrite lookup_insert_ne; [exact M6|]. intros E. assert (X0 : a_live st !! p = None) by (rewrite <- E; exact NONE). rewrite X0 in M6. discriminate. }
  split. { intros p c k Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
           - rewrite lookup_insert_eq in Hp. discriminate.
           - rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact (LIVE p c k Hp). }
  split. { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [lia|].
           rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). pose proof (FRESH p ch Hp). lia. }
  exact UNIQ.
Qed.

#[using="Type"] Lemma ablocks_sec : forall L st X LB nres' a ms n,
  awf L st X -> ablocks L st X LB -> sec_wf1 L (CSec a ms n) ->
  ablocks L (st_sec st nres' a ms n) X (HB (a_next st) (a + SEC_UOFF) n :: LB).
Proof.
  intros L st X LB nres' a ms n WF (BH & BF & NDI & NDL) W1.
  pose proof (awf_fresh_none L st X WF) as NONE.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ _ E7 _; nd_post).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms' & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. (nd_pre M 6%nat; intros _ _ _ _ _ M5; nd_post). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. right. exists a, ms. rewrite E7, lookup_insert_eq. split; [reflexivity|]. split; [reflexivity| exact W1].
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms' & Lp & R)].
      * left. exists b. split; [exact Hb| exact R].
      * right. exists mb, ms'. split; [| exact R]. rewrite E7, lookup_insert_ne; [exact Lp|].
        intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. (nd_pre Hin 3%nat; intros b Hb Hp; nd_post).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed.

#[using="Type"] Lemma arng_sec : forall L RNG RNG' st X nres' a ms n,
  awf L st X -> arng L RNG st -> fp_le RNG RNG' ->
  rng RNG' a ms -> rng RNG' (shad a) (ms / 8) -> rng RNG' (al_ptr_array L) (8 * nres') ->
  arng L RNG' (st_sec st nres' a ms n).
Proof.
  intros L RNG RNG' st X nres' a ms n WF AR LE R1 R2 R3.
  (pose proof (arng_mono L RNG RNG' st LE AR) as ndP__; nd_pre ndP__ 13%nat; intros A1 A2 A3 A4 A5 A6 A6a A6b A6c A7 A8 A9 A10; nd_post).
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 12%nat; intros _ _ E3 _ _ _ E7 _ E9 _ E11 _; nd_post).
  unfold arng. rewrite E3. repeat (split; [assumption|]). split; [| exact A10].
  eapply RSEC_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [eapply awf_fresh_none; exact WF| exact E7| exact E9| exact E11]|].
  constructor; [| exact A9]. cbn [sec_mb sec_ms]. split; [exact R1| exact R2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Proof.
  intros cs cs' L st X m P (WFS & ARR & INST & PZ & SHZ).
  split; [| split; [| split; [exact INST| split; [exact PZ|]]]].
  - (nd_pre WFS 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post). unfold asec_wf.
    split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [rewrite <- (Permutation_length P); exact WL|]. split; [exact WB|].
    split; [| eapply sec_disjoint_perm; [exact P| exact WD]].
    rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
  - (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). exists order. split; [eapply Permutation_trans; [exact PO| exact P]|].
    split; [exact U64| split; [exact JK| exact PER]].
  - intros x Hx HF HC. apply (SHZ x Hx HF). rewrite Forall_forall in HC |- *. intros ch Hin. apply HC.
    eapply Permutation_in; [exact P| exact Hin].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma asec_chunk_frameW : forall L W m m' mb ms n idx lv,
  munch W m m' -> wmono asegs m m' ->
  sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WM WF1 DC DS CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. (nd_pre WF0 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post).
  (pose proof (sec_facts n ltac:(lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ RSE RSR _ NSE _ MSR MSM _; nd_post). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  (nd_pre GR 3%nat; intros GR1 GR2 GR3; nd_post).
  cbn [asec_chunk] in CH |- *. (nd_pre CH 9%nat; intros H1 H2 H3 H4 (b1 & ctx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

#[using="Type"] Lemma junk_zero_len : forall m A n, junk_at m A n -> n <= 0 -> forall m', junk_at m' A n.
Proof.
  intros m A n [bs H] Hn m'. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
  split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section Append.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Variables (st : astate) (X : aconc) (nres' a n id : Z).
Let ms := sec_map_size n.
Let cs := sec_chunks_of st.
Let nsec := a_nsec st.
Let nres := a_nres st.
Let PA := al_ptr_array L.
Let UB := a + 6144.
Hypothesis WF : awf L st X.
Hypothesis SEC : ASECc cs L st X m.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis W1 : sec_wf1 L (CSec a ms n).
Hypothesis DJ : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs.
Hypothesis NR' : (nsec <> nres /\ nres' = nres)
              \/ (nsec = nres /\ nres' = nres + 16384
                  /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]).
Hypothesis NRB : nres' <= 1048576.
(* [comment removed for export] *)
Hypothesis Wch : forall ch, In ch cs ->
     (forall A k, sec_mb ch <= A -> A + k <= sec_mb ch + sec_ms ch -> 0 < k -> disjoint_from W A k)
  /\ (forall A k, shad (sec_mb ch) <= A -> A + k <= shad (sec_mb ch) + sec_ms ch / 8 -> 0 < k -> disjoint_from W A k).
Hypothesis Wpa : 0 < nsec -> disjoint_from W PA (8 * nsec).
Hypothesis Wpj : nsec + 1 < nres -> disjoint_from W (PA + 8 * nsec + 8) (8 * (nres - nsec - 1)).
Hypothesis Wbase : disjoint_from W (AINSTANCE + 80) 8.
Hypothesis Wp0 : disjoint_from W (shad (al_space_beg L)) (shlen K_REGION).
Hypothesis Wshz : forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) -> (x < a \/ a + ms <= x) -> disjoint_from W (shad x) 1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis C_srt : rw_cells asegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)].
Hypothesis C_jst : junk_at m' (AINSTANCE + 136) 32.
Hypothesis C_jbs : junk_at m' (AINSTANCE + 168) 512.
Hypothesis C_mtx : rw_cells asegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Hypothesis C_jgl : junk_at m' (AINSTANCE + 704) 16.
Hypothesis C_slot : rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].
Hypothesis C_hdr : rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)].
Hypothesis C_pgj : junk_at m' (a + 32) (4096 - 32).
Hypothesis C_mag : rw_cells asegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))].
Hypothesis C_lcj : junk_at m' (a + 4096 + 16) (2048 - 32).
Hypothesis C_ahd : rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
Hypothesis IDR : 0 < id < 2^31.
Hypothesis C_usr : junk_at m' UB (ms - 6144).
Hypothesis C_shf : fill_at m' (shad a) 768 0xfa.
Hypothesis C_shu : rw_cells asegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Hypothesis C_sht : fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa.

#[using="rc L id nres PA UB C_hdr C_pgj C_mag C_lcj C_ahd IDR C_usr C_shf C_shu C_sht"] Lemma asec_chunk_new : asec_chunk m' (CSec a ms n) nsec true.
Proof.
  cbn [asec_chunk]. unfold SEC_UOFF, SEC_MAGIC. fold UB.
  replace (UB - 16) with (UB + -16) by (subst UB; lia).
  split; [exact C_hdr|]. split; [exact C_pgj|]. split; [exact C_mag|]. split; [exact C_lcj|].
  split. { exists 17, id. split; [exact C_ahd|]. split; [lia|]. split; [reflexivity| lia]. }
  split; [unfold SEC_UOFF; exact C_usr|]. split; [exact C_shf|]. split; [| exact C_sht].
  unfold sec_user_shadow. exact C_shu.
Qed.

#[using="W m MU WM id cs nsec nres PA UB WF SEC N PRIM W1 DJ NR' NRB Wch Wpa Wpj Wbase Wp0 Wshz C_srt C_jst C_jbs C_mtx C_jgl C_slot C_hdr C_pgj C_mag C_lcj C_ahd IDR C_usr C_shf C_shu C_sht"] Theorem asec_append : ASEC_of L (st_sec st nres' a ms n) X m'.
Proof.
  pose proof (awf_fresh_none L st X WF) as NONE.
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 12%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12; nd_post).
  destruct SEC as (WFS & ARR & INST & PZ & SHZ).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post).
  pose proof W1 as W0. cbn [sec_wf1] in W0. (nd_pre W0 7%nat; intros G1 G2 G3 G4 G5 G6 GC; nd_post).
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB _ RSE RSR _ NSE _ MSR MSM MSB; nd_post). fold ms in MSR, MSM, MSB.
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. fold PA in OP.
  assert (NEWNOT : ~ In (CSec a ms n) cs).
  { intros Hin. pose proof (proj1 (Forall_forall _ _) DJ _ Hin) as D. cbn [sec_mb sec_ms] in D. clear -D MSB. lia. }
  assert (NSR : 0 <= nsec /\ nsec + 1 <= nres' /\ (nres' = nres \/ nres' = nres + 16384)).
  { subst nsec nres. destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia. }
  (nd_pre NSR 3%nat; intros NS0 NS1 NS2; nd_post).
  unfold ASEC_of. eapply ASECc_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [exact NONE| exact E7| exact E9| exact E11]|].
  fold cs. split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    unfold asec_wf. rewrite E2, E3, E4. split; [exact ALO|]. split; [exact WP|].
    split. { split; [| clear -NRB NS0 NS1; lia]. destruct WR as [WRM _]. destruct NS2 as [-> | ->]; [exact WRM|].
             subst nres. clear -WRM. Z.div_mod_to_equations. lia. }
    split; [cbn [length]; subst nsec; clear -WL; lia|]. split; [clear -NS0 NS1; subst nsec; lia|].
    split; [constructor; [exact W1| exact WF1]|].
    destruct WD as [ND PW]. split; [constructor; [exact NEWNOT| exact ND]|].
    intros ci cj [<-|Hi] [<-|Hj] NE; [exfalso; exact (NE eq_refl)| | |].
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hj) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hi) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + exact (PW ci cj Hi Hj NE).
  - (* [comment removed for export] *)
    (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). unfold asec_arr. rewrite E3, E4. fold PA. fold nsec.
    assert (LEN : Z.of_nat (length order) = nsec) by (rewrite (Permutation_length PO); exact WL).
    exists (order ++ [CSec a ms n]).
    split. { eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact PO. }
    split; [| split].
    + rewrite map_app. cbn [map sec_mb]. apply u64arr_snoc.
      * destruct order as [|o0 order'].
        { destruct U64 as [[B0 [B1 _]] _]. apply u64arr_nil; [clear -OP; lia| clear -OP; atop_facts; lia]. }
        eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. cbn [length] in LEN |- *.
        replace (8 * Z.of_nat (S (length order'))) with (8 * nsec) by (clear -LEN; lia). apply Wpa. clear -LEN; lia.
      * rewrite length_map. replace (PA + 8 * Z.of_nat (length order)) with (PA + 8 * nsec) by (clear -LEN; lia). exact C_slot.
    + destruct NR' as [(A1 & A2)|(A1 & A2 & ZC)].
      * rewrite A2. destruct (junk_split m (PA + 8 * nsec) 8 (8 * (nres - nsec - 1))
                      ltac:(replace (8 + 8 * (nres - nsec - 1)) with (8 * (nres - nsec)) by (clear; lia); exact JK) ltac:(clear; lia) ltac:(clear -A1 WB; subst nsec nres; lia))
          as [_ JR].
        replace (PA + 8 * (nsec + 1)) with (PA + 8 * nsec + 8) by (clear; lia).
        replace (8 * (nres - (nsec + 1))) with (8 * (nres - nsec - 1)) by (clear; lia).
        destruct (Z_lt_le_dec (nsec + 1) nres) as [LT|GE].
        { eapply junk_frame; [exact JR| exact MU| exact WM| intros _; apply Wpj; exact LT]. }
        eapply junk_zero_len; [exact JR| clear -GE; lia].
      * rewrite A2, A1. subst nres. replace (PA + 8 * (a_nres st + 1)) with (PA + 8 * a_nres st + 8) by (clear; lia).
        replace (8 * (a_nres st + 16384 - (a_nres st + 1))) with (131072 - 8) by (clear; lia). eexists. exact ZC.
    + intros i ch Hi.
      destruct (Nat.lt_ge_cases i (length order)) as [LT|GE].
      * rewrite nth_error_app1 in Hi by exact LT. (nd_pre (PER i ch Hi) 3%nat; intros lv LV CH; nd_post).
        assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        (nd_pre (asec_wf_all L st cs ch WFS Hin) 4%nat; intros mb ms' n' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into WF1c).
        exists lv. split.
        { rewrite LV. unfold sec_live. rewrite E7. split; intros [p Hp].
          - exists p. rewrite lookup_insert_ne; [exact Hp|]. intros E. subst p. rewrite NONE in Hp. discriminate.
          - destruct (N.eq_dec p (a_next st)) as [->|NE].
            + rewrite lookup_insert_eq in Hp. injection Hp as Ea Em En. exfalso. apply NEWNOT. rewrite <- Ea, <- Em, <- En in Hin. exact Hin.
            + exists p. rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact Hp. }
        destruct (Wch _ Hin) as [DC DS]. cbn [sec_mb sec_ms] in DC, DS.
        eapply asec_chunk_frameW; [exact MU| exact WM| exact WF1c| exact DC| exact DS| exact CH].
      * rewrite nth_error_app2 in Hi by exact GE.
        assert (EI : i = length order) by (destruct (i - length order)%nat as [|k] eqn:EK; [clear -GE EK; lia| cbn in Hi; destruct k; discriminate]).
        subst i. rewrite Nat.sub_diag in Hi. cbn in Hi. injection Hi as <-.
        exists true. split.
        { split; [intros _| reflexivity]. exists (a_next st). rewrite E7, lookup_insert_eq. reflexivity. }
        rewrite LEN. exact asec_chunk_new.
  - (* [comment removed for export] *)
    (nd_pre INST 6%nat; intros I1 _ _ _ _ _; nd_post). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; exact Wbase]|].
    split; [exists (Z_to_bv 8 0); exact C_srt|]. split; [exact C_jst|]. split; [exact C_jbs|]. split; [| exact C_jgl].
    pose proof C_mtx as M4. rw_split M4 1%nat M0 M3. exact M3.
  - (* [comment removed for export] *)
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM| intros _; exact Wp0].
  - (* [comment removed for export] *)
    intros x Hx HF HC. apply Forall_cons_iff in HC. destruct HC as [HCn HC]. cbn [sec_mb sec_ms] in HCn.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia]. apply Wshz; [exact Hx| clear -HCn Hx; lia].
Qed.
End Append.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WT (L : alayout) (sp a ms nsec nres nres' : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (al_t L + 2800, al_t L + 3169); (AINSTANCE + 112, AINSTANCE + 720);
   (al_ptr_array L + 8 * nsec, al_ptr_array L + 8 * nsec + 8); (al_ptr_array L + 8 * nres, al_ptr_array L + 8 * nres');
   (a, a + ms); (shad a, shad a + ms / 8);
   (0x1804c8, 0x5d0510); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z.

(* [comment removed for export] *)
Definition wt_facts (L : alayout) (sp lo a ms nsec nres nres' : Z) : Prop :=
     alayout_ok L /\ ATOP <= lo /\ lo <= sp - 4096
  /\ ablk a (a + ms) /\ a + ms <= ATOP /\ a mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 < ms /\ sec_clear L a ms
  /\ 0 <= nsec /\ nsec + 1 <= nres' /\ 8 * nres' <= 8388608 /\ 0 <= nres <= nres'.

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

Section KW.
Variables (L : alayout) (sp lo a ms nsec nres nres' : Z).
Hypothesis WTF : wt_facts L sp lo a ms nsec nres nres'.
Let W' := List.filter nonempty (WT L sp a ms nsec nres nres').

Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
  destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
Local Ltac facts :=
  lazymatch goal with |- _ =>
  (pose proof WTF as ndP__; nd_pre ndP__ 13%nat; intros ALO CEIL LO AHI0 ACE AAL MSM MSP (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d) NS0 NS1 NS8 NS9; nd_post);
  pose proof (ao_t L ALO) as OT; pose proof (ao_ctx L ALO) as OC; pose proof (ao_res L ALO) as ORS; pose proof (ao_nodes L ALO) as ON;
  pose proof (ao_store L ALO) as OS; pose proof (ao_ptr L ALO) as OP; unfold aobj in OT, OC, ORS, ON, OS, OP;
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT OTs] [jT OTi]; nd_post); (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OCi _ [kC OCs]; nd_post);   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros ONi _ [kN ONs]; nd_post); (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OSi _ [kS OSs]; nd_post);
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi _ [kP OPs]; nd_post); pose proof (ao_res_hi L ALO) as RHI;
  destruct (ablk_int _ _ AHI0) as [kA ABND]; (pose proof (ablk_lin _ _ AHI0) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 _ _; nd_post); unfold AIMG_HI in AL1;   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res; pose proof (ad_nodes_res L ALO) as D_n_res; pose proof (ad_store_res L ALO) as D_s_res;
  pose proof (ad_ptr_res L ALO) as D_p_res; pose proof (ad_t_ctx L ALO) as D_t_c; pose proof (ad_t_nodes L ALO) as D_t_n;
  pose proof (ad_t_store L ALO) as D_t_s; pose proof (ad_t_ptr L ALO) as D_t_p; pose proof (ad_ctx_nodes L ALO) as D_c_n;
  pose proof (ad_ctx_store L ALO) as D_c_s; pose proof (ad_ctx_ptr L ALO) as D_c_p;
  unfold adisj in D_t_res, D_n_res, D_s_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_p, D_c_n, D_c_s, D_c_p
  end.

#[using="rc tlsI L sp lo nsec nres nres' WTF"] Lemma WT_shad : 0x800b8600 <= shad a /\ shad a + ms / 8 = shad (a + ms) /\ shad (a + ms) <= 0x10007fef8000      (* [comment removed for export] *)
                /\ (forall x, x < a -> shad x + 1 <= shad a) /\ (forall x, a + ms <= x -> shad (a + ms) <= shad x).
Proof.
  facts. rewrite !shad_div. unfold ASHOFF in *. split; [clear -AL1; Z.div_mod_to_equations; lia|].
  split; [clear -AAL MSM; Z.div_mod_to_equations; lia|]. split; [clear -ACE; Z.div_mod_to_equations; lia|].
  split; intros x Hx; rewrite shad_div; unfold ASHOFF; [clear -Hx AAL| clear -Hx]; Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma KT_X : forall A k, 0 <= k ->
  (forall iv, In iv (WT L sp a ms nsec nres nres') -> fst iv < snd iv -> A + k <= fst iv \/ snd iv <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk H. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros iv Hiv.
  apply List.filter_In in Hiv. destruct Hiv as [Hiv NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV. exact (H iv Hiv NEV).
Qed.

#[using="rc tlsI lo WTF"] Lemma KT_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
  (A + k <= AINSTANCE + 112 \/ AINSTANCE + 720 <= A) -> (A + k <= 0x1804c8 \/ 0x5d0510 <= A) -> disjoint_from W' A k.
Proof.
  facts. (pose proof WT_shad as ndP__; nd_pre ndP__ 4%nat; intros SA1 SA2 SA3 _; nd_post).
  intros A k H1 H2 H3 H4 H5. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 H5 NEV CEIL LO OT OP AL1 SA1 ON OS NS0 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

#[using="tlsI lo WTF"] Lemma KT_obj : forall A k, (A + k <= 65536 \/ 6303744 <= A) -> (A + k <= 2147446784 \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ATOP ->      (* [comment removed for export] *)
  (A + k <= al_t L + 2800 \/ al_t L + 3169 <= A) -> (A + k <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
  (A + k <= a \/ a + ms <= A) -> (A + k <= al_nodes L \/ al_nodes L + 1048576 <= A) -> (A + k <= al_store L \/ al_store L + 8388608 <= A) ->
  disjoint_from W' A k.
Proof.
  facts. (pose proof WT_shad as ndP__; nd_pre ndP__ 4%nat; intros SA1 SA2 SA3 _; nd_post).
  intros A k H0 H1 H2 H3 H4 H5 H6 H7 H8. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H0 H1 H2 H3 H4 H5 H6 H7 H8 NEV CEIL LO NS0 NS1 NS8 NS9 SA1 SA2 SA3; lia.
Qed.

#[using="rc tlsI lo WTF"] Lemma KT_shad : forall A k, 2147446784 <= A -> 0 <= k -> A + k <= 17594333495296 ->      (* [comment removed for export] *)
  (A + k <= shad a \/ shad (a + ms) <= A) -> disjoint_from W' A k.
Proof.
  facts. (pose proof WT_shad as ndP__; nd_pre ndP__ 4%nat; intros SA1 SA2 SA3 _; nd_post).
  intros A k H1 H2 H3 H4. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 NEV CEIL LO OT OP ABND ON OS SA2 NS0 NS1 NS8 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

(* [comment removed for export] *)

#[using="rc tlsI lo WTF"] Lemma KT_t : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 2800 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OT D_t_p C_t D_t_n D_t_s OTs OTi; lia. Qed.   (* [comment removed for export] *)

#[using="rc tlsI lo WTF"] Lemma KT_ctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OC OT D_t_c D_c_p C_c D_c_n D_c_s OTs OTi OCs OCi; lia. Qed.

#[using="rc tlsI lo WTF"] Lemma KT_res : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 ORS RHI OT D_t_res D_p_res C_r D_n_res D_s_res OTs OTi; lia. Qed.   (* [comment removed for export] *)

#[using="rc tlsI sp lo nsec nres nres' WTF"] Lemma KT_res_geo : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                   /\ shad (al_res L + 137439023104) <= 0x10007fef8000      (* [comment removed for export] *)
                   /\ (shad (al_res L + 137439023104) <= shad a \/ shad (a + ms) <= shad (al_res L)).
Proof. facts. rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI C_r AAL. Z.div_mod_to_equations. lia. Qed.

#[using="rc tlsI lo WTF"] Lemma KT_res_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof. (pose proof KT_res_geo as ndP__; nd_pre ndP__ 4%nat; intros SR1 SR2 SR3 SR4; nd_post). intros A k H1 H2 H3. apply KT_shad; clear -H1 H2 H3 SR1 SR3 SR4; lia. Qed.

(* [comment removed for export] *)
#[using="lo WTF"] Lemma KT_tls : forall A k, ATPv + -200 <= A -> 0 <= k -> A + k <= ATPv + 312 -> disjoint_from W' A k.
Proof.
  intros A k H1 H2 H3. pose proof ATPv_img as TI. apply KT_img; unfold AIMG_HI, AINSTANCE; lia.
Qed.

(* [comment removed for export] *)
#[using="lo WTF"] Lemma KT_rt : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt L m -> arep_rt L m'.
Proof.
  intros m m' MU WM RT. eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
  repeat (apply Forall_cons; [cbn [fst snd]; first [apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia | apply KT_ctx; clear; lia | apply KT_tls; clear; lia] |]). apply Forall_nil.
Qed.
#[using="rc tlsI lo WTF"] Lemma KT_rt2 : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt2 m -> arep_rt2 m'.
Proof. intros m m' MU WM RT2. eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia. Qed.
#[using="rc tlsI lo WTF"] Lemma KT_rt3 : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt3 m -> arep_rt3 m'.
Proof.
  intros m m' MU WM RT3. eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]. unfold rt3_hulls.
  repeat (apply Forall_cons; [cbn [fst snd]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia |]). apply Forall_nil.
Qed.
#[using="rc tlsI lo WTF"] Lemma KT_relro : forall m m', munch W' m m' -> arelro m -> arelro m'.
Proof. intros m m' MU HRO. eapply arelro_frame; [exact MU | exact HRO | apply KT_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]. Qed.
End KW.

Section Store.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Let AHS : aholes := AH DI AQ ASEC_of AFK.
Hypothesis HL : ahole_laws AHS.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition store_sec__stmt : Prop := forall (L : alayout) (RNG RNG' : footprint) (sp lo : Z) (m m' : amem) (st : astate) (X : aconc) (LB : list ablock)
    (n a nres' id : Z) (sj' : list word) (RESV : list (Z * Z)),
  let nsec := a_nsec st in let nres := a_nres st in let PA := al_ptr_array L in let ms := sec_map_size n in
  let UB := a + 6144 in let t := al_t L in
  alayout_ok L -> arng L RNG st -> AREP AHS L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  sfresh RESV st n a = true -> aresv_ok L RESV ->
  ATOP <= lo -> lo <= sp - 4096 -> sp <= 2^47 ->
  fp_le RNG RNG' -> rng RNG' a ms -> rng RNG' (shad a) (ms / 8) ->
  ((nsec <> nres /\ nres' = nres)
   \/ (nsec = nres /\ nres' = nres + 16384
       /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])) ->
  nres' <= 1048576 -> rng RNG' PA (8 * nres') ->
  munch (WT L sp a ms nsec nres nres') m m' -> wmono asegs m m' ->
  (* [comment removed for export] *)
  u64arr asegs m' (t + 2800) sj' -> length sj' = 46%nat -> rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m' (AINSTANCE + 112) [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))] ->
  rw_cells asegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)] -> junk_at m' (AINSTANCE + 136) 32 -> junk_at m' (AINSTANCE + 168) 512 ->
  rw_cells asegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m' (AINSTANCE + 704) 16 ->
  rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)] ->
  rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)] ->
  junk_at m' (a + 32) (4096 - 32) ->
  rw_cells asegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))] ->
  junk_at m' (a + 4096 + 16) (2048 - 32) ->
  rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 < id < 2^31 ->
  junk_at m' UB (ms - 6144) ->
  fill_at m' (shad a) 768 0xfa ->
  rw_cells asegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa ->
  ADEPOT DI L m' ->
     aheap_pres CI LB sp m m'
  /\ AHEAP_P AHS L RNG' (st_sec st nres' a ms n) (HB (a_next st) UB n :: LB) m'.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 1).
Variable RNG' : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 3).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 4).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 5).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 6).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 7).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 8).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 9).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 10).
Variable a : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 11).
Variable nres' : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 12).
Variable id : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 13).
Variable sj' : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 14).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 15).
Let ms := sec_map_size n.
Let W' := List.filter nonempty (WT L sp a ms (a_nsec st) (a_nres st) nres').
Let st2 := st_sec st nres' a ms n.
#[using="HL CI_OK CI_OK2 ms W' st2"] Lemma store_sec__body : ltac:(let T := type of (fun (h : store_sec__stmt) => h L RNG RNG' sp lo m m' st X LB n a nres' id sj' RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (RNG', (sp, (lo, (m, (m', (st, (X, (LB, (n, (a, (nres', (id, (sj', RESV)))))))))))))))) as _.
 cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM FRSH ROK CEIL LO SP47 FPLE RA RSA NR' NRB RPA' MU0 WM
         STATS LSJ UNW I112 I128 J136 J168 I680 J704 SLOT HDR PGJ MAG LCJ AHD IDR USR SHF SHU SHT DEP.
  chg (sec_map_size n) ms.
  (* [comment removed for export] *)
  (pose proof (valid_geo L RESV st n a N PRIM FRSH ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
  pose proof (valid_clear L RESV st n a N PRIM FRSH ROK) as VC. fold ms in VC.
  pose proof (valid_hulls L RESV st n a N PRIM FRSH ROK) as VH. fold ms in VH.
  pose proof (valid_chunks L RESV st n a N PRIM FRSH ROK) as VK. fold ms in VK.
  pose proof (valid_wf1 L RESV st n a N PRIM FRSH ROK) as VW. fold ms in VW.
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB _ RSE RSR _ NSE _ MSR MSM MSB; nd_post). fold ms in MSR, MSM, MSB.
  (nd_pre VC 10%nat; intros C_t C_c C_r C_p C_n C_s C_f C_d C_l C_ahm; nd_post).      (* [comment removed for export] *)
  unfold K_HIGH_MEM in AHI0.
  pose proof (munch_filter_nonempty _ m m' MU0) as MU. clear MU0. chg (List.filter nonempty (WT L sp a ms (a_nsec st) (a_nres st) nres')) W'.
  assert (NE : Forall (fun iv => fst iv < snd iv) W') by (apply nonempty_filter).
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_fake L ALO) as OFK. pose proof (ao_ptr L ALO) as OP. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, OP, OD. pose proof (ao_space L ALO) as RSP.
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT OTs] [jT OTi]; nd_post). (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OCi _ [kC OCs]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros ONi _ [kN ONs]; nd_post). (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OSi _ [kS OSs]; nd_post).
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi _ [kP OPs]; nd_post). (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ [kF OFKs]; nd_post).
  (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD ODs] [jD ODi]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ AHI0) as [kA ABND]. (pose proof (ablk_lin _ _ AHI0) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 _ _; nd_post). unfold AIMG_HI in AL1.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ad_t_ctx L ALO) as D_t_c.
  pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_ptr L ALO) as D_t_p.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_ctx_ptr L ALO) as D_c_p.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_fake L ALO) as D_s_f. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d. pose proof (ad_fake_dtls L ALO) as D_f_d.
  unfold adisj in D_t_res, D_c_res, D_n_res, D_s_res, D_f_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_p, D_c_n, D_c_s, D_c_f, D_c_p,
                   D_n_f, D_n_p, D_s_f, D_s_p, D_f_p, D_d_res, D_t_d, D_d_p, D_n_d, D_s_d, D_f_d.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  pose proof HS as HS0. unfold AHS, AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  (pose proof HS0 as ndP__; nd_pre ndP__ 5%nat; intros WFS ARR INST2 PZ SHZ; nd_post). (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  assert (NSR : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ 8 * nres' <= 8388608 /\ a_nres st <= nres').
  { destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB NRB WR; lia. }
  (nd_pre NSR 4%nat; intros NS0 NS1 NS8 NS9; nd_post).
  (* [comment removed for export] *)
  assert (WTF : wt_facts L sp lo a ms (a_nsec st) (a_nres st) nres').
  { unfold wt_facts. repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    - unfold sec_clear. repeat (split; [assumption|]). assumption.
    - clear -WB; lia. }
  (pose proof (WT_shad L sp lo a ms _ _ _ WTF) as ndP__; nd_pre ndP__ 5%nat; intros SA1 SA2 SA3 SAlt SAge; nd_post).
  pose proof (KT_X L sp a ms (a_nsec st) (a_nres st) nres') as KX. pose proof (KT_img L sp lo a ms _ _ _ WTF) as Kimg.
  pose proof (KT_obj L sp lo a ms _ _ _ WTF) as Kobj. pose proof (KT_shad L sp lo a ms _ _ _ WTF) as Kshad.
pose proof (KT_t L sp lo a ms _ _ _ WTF) as Kt.   (* [comment removed for export] *)
  pose proof (KT_ctx L sp lo a ms _ _ _ WTF) as Kctx. pose proof (KT_res L sp lo a ms _ _ _ WTF) as Kres.
  pose proof (KT_tls L sp lo a ms _ _ _ WTF) as Ktls. fold W' in Ktls.      (* [comment removed for export] *)
  pose proof (KT_res_sh L sp lo a ms _ _ _ WTF) as Kres_sh. (pose proof (KT_res_geo L sp lo a ms _ _ _ WTF) as ndP__; nd_pre ndP__ 4%nat; intros SR1 SR2 SR3 SR4; nd_post).
  fold W' in KX, Kimg, Kobj, Kshad, Kt, Kctx, Kres, Kres_sh.
  Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 12%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12; nd_post).
  chg (st_sec st nres' a ms n) st2.
  (* [comment removed for export] *)
  assert (AR' : AREP AHS L st2 X m').
  { split; [apply awf_sec; exact WF|].
    split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
             repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia | apply Kctx; clear; lia | apply Ktls; clear; lia] |]). apply Forall_nil. }
    split. { (* [comment removed for export] *)
      (nd_pre INST 9%nat; intros I1 I2 I3 I4 I5 I6 I7 I8 I9; nd_post). unfold ainstance. subst st2. rewrite E3, E4.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I3| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I4| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [exact I112|].
      split; [pose proof I680 as M4; rw_split M4 1%nat M0 M3; exact M0|].
      split; [eapply cells_frame; [exact I7| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I8| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      eapply cells_frame; [exact I9| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]. }
    split. { (* [comment removed for export] *)
      (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS _ _; nd_post). unfold athread.
      split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | subst st2; reflexivity | subst st2; reflexivity | reflexivity |].
               unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
      split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
      split; [exists sj'; split; [exact STATS| exact LSJ]| exact UNW]. }
    split. { (* [comment removed for export] *)
      intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
      (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
      pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
      assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                   /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
      { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
      (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
      split; [| split; [| split]].
      - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity |].
        apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
      - eapply afreearray_frame; [exact MU | exact WM | exact FARR | subst st2; reflexivity | subst st2; reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
        + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
        + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
          rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
          unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
      - eapply (aslots_update L W' m m' MU WM st st2 X X c (-1)); [exact SLOTS | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
        + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
          split; [reflexivity|]. split.
          * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
          * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
            apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
            split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
        + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
      - eapply (aslot_shadow_update L W' m m' MU WM st st2 X X c (-1)); [exact SHADOW | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
        + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
          pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
          split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | rewrite shlen_div; clear -QS QS16; Z.div_mod_to_equations; lia |].
          rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
        + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
          rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
          apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
    split. { (* [comment removed for export] *)
      eapply (hq_frame _ HL L st st2 X X m m' W'); [exact HQ | exact MU | exact WM | |].
      - unfold quar_untouched. apply Forall_forall. intros iv Hin.
        unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
        inWT Hin. all: unfold AINSTANCE in *.
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS C_t D_t_p D_t_n D_t_s NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |];
          clear -NEV B1 B2 CEIL LO OT OP ORS AHI0 SA1 SA2 SA3 SR1 ON OS D_t_res D_p_res C_r D_n_res D_s_res NS0 NS1 NS8 NS9 WB ABND AL1 RHI OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - unfold quar_same. subst st2. rewrite E9, E10, E11, E12, E1. repeat (split; [reflexivity|]).
        split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
    split. { (* [comment removed for export] *)
      unfold AHS, AH. cbn [ah_sec]. subst st2.
      eapply (asec_append L W' m m' MU WM st X nres' a n id WF HS0 N PRIM VW VK NR' NRB).
      - intros ch Hin. (nd_pre (asec_wf_all L st _ ch WFS Hin) 4%nat; intros mb ms' n' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into W1c). cbn [sec_mb sec_ms].
        pose proof W1c as W0. cbn [sec_wf1] in W0. (nd_pre W0 7%nat; intros G1 G2 G3 G4 G5 G6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
        (pose proof (sec_facts n' ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ MSM' MSB'; nd_post). rewrite <- G4 in MSM', MSB'.
        destruct (ablk_int _ _ G2) as [kB GB].   (* [comment removed for export] *)
        assert (SHc : 0x800b8600 <= shad mb /\ shad mb + ms' / 8 = shad (mb + ms') /\ shad (mb + ms') <= 0x10007fef8000
                      /\ (shad (mb + ms') <= shad a \/ shad (a + ms) <= shad mb)).
        { rewrite !shad_div. unfold ASHOFF, K_HIGH_MEM in *. clear -G1 GB G3 MSM' D AAL MSM. Z.div_mod_to_equations. lia. }
        (nd_pre SHc 4%nat; intros SC1 SC2 SC3 SC4; nd_post). unfold K_HIGH_MEM in *.
        split; intros A k H1 H2 H3.
        + apply Kobj; clear -H1 H2 H3 GB G3 Ct Cp Cn Cs D; lia.
        + apply Kshad; clear -H1 H2 H3 SC1 SC2 SC3 SC4; lia.
      - intros POS. apply KX; [clear -POS; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -POS NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - intros LT. apply KX; [clear -LT NS0; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -LT NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia.
      - replace (shlen K_REGION) with 536870912 by reflexivity.
        apply Kres_sh; [apply shad_mono; clear -RSP; lia| clear; lia|].
        rewrite !shad_div. clear -RSP. Z.div_mod_to_equations. lia.
      - intros x Hx Hxa. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
        assert (SX : 2147446784 <= shad x /\ shad x + 1 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
        apply Kshad; [clear -SX; lia| clear; lia| clear -SX; lia|].
        destruct Hxa as [Hxa|Hxa]; [left; apply SAlt; exact Hxa| right; apply SAge; exact Hxa].
      - exact I128. - exact J136. - exact J168. - exact I680. - exact J704. - exact SLOT. - exact HDR. - exact PGJ. - exact MAG. - exact LCJ.
      - exact AHD. - exact IDR. - exact USR. - exact SHF. - exact SHU. - exact SHT. }
    split; [exact DEP|].
    split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]|].
    split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia|].
    split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia |]); apply Forall_nil].
    intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | subst st2; reflexivity | subst st2; reflexivity | |].
    - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
    - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  (* [comment removed for export] *)
  assert (SHFK : 0x800b8600 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 = shad (al_fake L + 11571200)      (* [comment removed for export] *)
                 /\ shad (al_fake L + 11571200) <= 0x10007fef8000
                 /\ (shad (a + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad a)).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK C_f AAL OFKs OFKi. Z.div_mod_to_equations. lia. }
  (nd_pre SHFK 4%nat; intros SF1 SF2 SF3 SF4; nd_post).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  split.
  - (* [comment removed for export] *)
    intros x Hx CL. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Hx.
    destruct CL as [CL|TL].
    2:{ (* [comment removed for export] *)
        destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_ptr L ALO) as DA2. pose proof (ad_ahm_nodes L ALO) as DA3. pose proof (ad_ahm_store L ALO) as DA4.
            unfold adisj in DA1, DA2, DA3, DA4.
            eapply (disjoint_outside W' x 1); [apply Kobj; clear -IM OAH OAHI DA1 DA2 DA3 DA4 C_ahm; lia | clear; lia]. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. eapply (disjoint_outside W' x 1); [apply Kshad; clear -IM SA1; lia | clear; lia]. }
        - eapply (disjoint_outside W' x 1); [apply Ktls; clear -T; lia | clear; lia].
        - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
          assert (SATOP : shad ATOP <= 17594332446720) by (pose proof atop_range as ATR0; rewrite shad_div; unfold ASHOFF; clear -ATR0; Z.div_mod_to_equations; lia).
          eapply (disjoint_outside W' (shad ta) 1); [| clear; lia].
          apply Kshad; [clear -TS1; lia | clear; lia | clear -TS2 SATOP; lia |].
          destruct C_l as [D|D]; [right; apply SAge; clear -D Hta; lia | left; apply SAlt; clear -D Hta; lia]. }
    destruct CL as [STa | [CIa | [BLK | SH]]].
    + eapply (disjoint_outside W' x 1); [| clear; lia]. apply KX; [clear; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
        clear -STa NEV CEIL LO OT OP AHI0 ACE ON OS SA2 SA3 NS0 NS1 NS8 NS9 WB SP47 ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Kimg x 1); unfold AIMG_HI, AINSTANCE in *; clear -R Q1 Q2 Q3 Q4; lia | clear; lia].
    + (nd_pre BLK 3%nat; intros b Hb R; nd_post). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      * destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        -- destruct (BB xb Hxb) as [Bb1 Bb2].
           pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
           eapply disjoint_outside; [eapply (Kres x 1) | clear; lia]; clear -R Bb1 Bb2 FIT; lia.
        -- (* [comment removed for export] *)
           assert (Hin : In (CSec mb0 ms0 n') (sec_chunks_of st)).
           { unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
             apply in_map_iff. exists (p, CSec mb0 ms0 n'). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp. }
           pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
           cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
           pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SFc. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
           destruct (ablk_int _ _ Gs2) as [kB GB].   (* [comment removed for export] *)
           eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R GB Gs3 Gs4 Gs5 SFc Ct Cp Cn Cs D; lia.
      * (nd_pre (FKD cls A n' Hb) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R K1 K3 OFK D_t_f D_f_p C_f D_n_f D_s_f OFKs OFKi; lia.
    + (nd_pre SH 3%nat; intros x' Hx' ndR1__; nd_post; revert ndR1__; intros ->).
      destruct Hx' as [STa | [CIa | FK]].
      * assert (SX : shad (a + ms) <= shad x' /\ shad x' + 1 <= 17594333495296).
        { split; [apply SAge; atop_facts; clear -STa ACE; lia|]. rewrite shad_div. unfold ASHOFF. clear -STa. Z.div_mod_to_equations. lia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1 SA2 MSB; lia | clear; lia].
      * (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
        assert (SX : 2147446784 <= shad x' /\ shad x' + 1 <= 0x800b8600) by (rewrite shad_div; unfold ASHOFF, AIMG_HI in *; clear -R Q1 Q3; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1; lia | clear; lia].
      * (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post).
        assert (SX : shad (al_fake L) <= shad x' /\ shad x' + 1 <= shad (al_fake L + 11571200)).
        { rewrite !shad_div. clear -R K1 K3 OFK OFKs OFKi. Z.div_mod_to_equations. lia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1) | clear; lia]; clear -SX SF1 SF3 SF4; lia.
  - (* [comment removed for export] *)
    split; [exact ALO|].
    split; [eapply (arng_sec L RNG RNG' st X); [exact WF| exact ARNG| exact FPLE| exact RA| exact RSA| exact RPA']|].
    split; [exists X; split; [exact AR'| replace (a + 6144) with (a + SEC_UOFF) by reflexivity; apply ablocks_sec; [exact WF| exact BL| exact VW]]|].
    unfold AHS, AH. cbn [ah_fake].
    eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |] |].
    + unfold fake_untouched. apply Forall_forall. intros iv Hin.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
      (* [comment removed for export] *)
      pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_ptr L ALO) as D_l_p. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
      unfold adisj in D_l_t, D_l_p, D_l_n, D_l_s. pose proof atp_lin as TLN.
      inWT Hin. all: unfold AINSTANCE in *.
      all: clear -NEV CEIL LO OT OP OFK OD AHI0 ACE SA1 SA2 SA3 SF1 SF2 SF3 SF4 ON OS D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi OFKs OFKi ODs ODi D_l_t D_l_p D_l_n D_l_s C_l TLN.
      (* [comment removed for export] *)
      all: first [ lazymatch goal with
                   | |- context [al_t _] => clear D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_ptr_array _] => clear D_t_f D_t_d C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_nodes _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_s_f D_s_d
                   | |- context [al_store _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_n_d
                   | |- _ => clear D_t_f D_t_d D_f_p D_d_p D_n_f D_s_f D_n_d D_s_d
                   end; repeat (split; [fu_lia|]); fu_lia
                 | repeat (split; [fu_lia|]); fu_lia ].
    + intros c F n'. split; [intros H; cbn [In] in H; destruct H as [H|H]; [discriminate H| exact H]| intros H; cbn [In]; right; exact H].
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2"] Theorem store_sec : ltac:(let t := eval cbv delta [store_sec__stmt] in store_sec__stmt in exact t).
Proof. exact store_sec__body. Qed.
End Store.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.ADepot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.ASecModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AModelFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.APrimFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_amalloc_arep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB.
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
Ltac fu_lia := first [solve [fu_focus; lia] | lia].
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma sec_chunk_in_ranges : forall st mb ms n, In (CSec mb ms n) (sec_chunks_of st) -> In (mb, mb + ms) (asec_ranges st).
Proof.
  intros st mb ms n H. unfold sec_chunks_of in H. apply List.filter_In in H. destruct H as [H _].
  unfold asec_ranges. apply in_flat_map. exists (CSec mb ms n). split; [exact H| left; reflexivity].
Qed.

#[using="Type"] Lemma avoids_all_In : forall a n l iv, avoids_all a n l = true -> In iv l -> a + n <= fst iv \/ snd iv <= a.
Proof.
  intros a n l iv H Hin. unfold avoids_all in H. rewrite forallb_forall in H. specialize (H iv Hin).
  unfold iv_clear in H. apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma asec_wf_all : forall L st cs ch, asec_wf L st cs -> In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st cs ch (_ & _ & _ & _ & _ & WF1 & _) Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1.
  destruct ch as [c n|mb ms n]; [destruct W1|]. exists mb, ms, n. split; [reflexivity| exact W1].
Qed.

Section Valid.
Variables (L : alayout) (RESV : list (Z * Z)) (st : astate) (n a : Z).
Let ms := sec_map_size n.
Hypothesis ALO : alayout_ok L.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis FR : sfresh RESV st n a = true.
Hypothesis ROK : aresv_ok L RESV.

#[using="tlsI L RESV st N PRIM FR ROK"] Lemma valid_geo : a mod 4096 = 0 /\ ablk a (a + ms) /\ a + ms <= ATOP /\ 0 < ms /\ ms = sec_map_size n.
Proof.
  (nd_pre (sfresh_true_facts RESV st n a FR) 8%nat; intros _ _ AV _ POS AL TOPB _; nd_post).   (* [comment removed for export] *)
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ _ MSB; nd_post).
  destruct ROK as (R1 & R2 & _).
  pose proof (pcov_clear _ _ _ _ _ R1 AV ltac:(unfold AIMG_HI; clear; lia) ltac:(clear -MSB; lia)) as C1.   (* [comment removed for export] *)
  pose proof (pcov_clear _ _ _ _ _ R2 AV ltac:(clear; lia) ltac:(clear -MSB; lia)) as C2.                    (* [comment removed for export] *)
  subst ms. split; [exact AL|]. split; [| split; [exact TOPB| split; [clear -MSB; lia| reflexivity]]].
  unfold ablk, KLS. unfold AIMG_HI in *. clear -C1 C2 POS TOPB MSB. lia.   (* [comment removed for export] *)
Qed.

(* [comment removed for export] *)
#[using="RESV st N PRIM FR ROK"] Lemma valid_hulls : Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L).
Proof.
  (nd_pre (sfresh_true_facts RESV st n a FR) 8%nat; intros _ _ AV _ _ _ _ _; nd_post).   (* [comment removed for export] *)
  (pose proof valid_geo as ndP__; nd_pre ndP__ 5%nat; intros _ _ _ MSP _; nd_post).
  destruct ROK as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16).      (* [comment removed for export] *)
  unfold astartup_hulls. fold (al_res L) in R3. change (4096 * al_V L 323%nat) with (al_dtls L) in R10.
  repeat (apply Forall_cons; [cbn [fst snd]; eapply pcov_clear; [first [ match goal with H : pcov _ ?l ?h |- pcov _ ?l' ?h' => constr_eq l l'; constr_eq h h'; exact H end | eassumption ]| exact AV| clear; lia| exact MSP] |]). apply Forall_nil.
Qed.

#[using="RESV st N PRIM FR ROK"] Lemma valid_clear : sec_clear L a ms.
Proof.
  pose proof valid_hulls as H. unfold astartup_hulls in H.
  repeat lazymatch type of H with Forall _ (_ :: _) => apply Forall_cons_iff in H; destruct H as [? H] | _ => idtac end.
  cbn [fst snd] in *. unfold sec_clear, al_ahm. repeat split; lia.
Qed.

#[using="rc tlsI L RESV N PRIM FR ROK"] Lemma valid_chunks : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) (sec_chunks_of st).
Proof.
  (nd_pre (sfresh_true_facts RESV st n a FR) 8%nat; intros _ _ _ AV _ _ _ _; nd_post).   (* [comment removed for export] *)
  apply Forall_forall. intros ch Hin. destruct ch as [c k|mb ms' k]; cbn [sec_mb sec_ms].
  - (pose proof valid_geo as ndP__; nd_pre ndP__ 3%nat; intros _ G _; nd_post). (pose proof (ablk_lin _ _ G) as ndP__; nd_pre ndP__ 3%nat; intros _ G0 _; nd_post). right. clear -G0. lia.   (* [comment removed for export] *)
  - pose proof (avoids_all_In _ _ _ _ AV (sec_chunk_in_ranges st mb ms' k Hin)) as D. cbn [fst snd] in D. exact D.
Qed.

#[using="RESV st N PRIM FR ROK"] Lemma valid_wf1 : sec_wf1 L (CSec a ms n).
Proof.
  (pose proof valid_geo as ndP__; nd_pre ndP__ 5%nat; intros G1 G2 G3 G4 G5; nd_post). pose proof (sec_facts n N PRIM) as (NB & _).
  cbn [sec_wf1]. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G5|].
  split; [lia|]. split; [exact PRIM| exact valid_clear].
Qed.
End Valid.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma wview_some : forall m (x : word) b, m x = Some b -> wview asegs m x = Some b.
Proof. intros m x b H. unfold wview. rewrite H. reflexivity. Qed.

#[using="Type"] Lemma ashz_azero : forall L cs m a ms,
  ashz L cs m ->
  a mod 8 = 0 -> ablk a (a + ms) -> a + ms <= ATOP -> 0 <= ms ->
  Forall (fun iv => a + ms <= fst iv \/ snd iv <= a) (astartup_hulls L) ->
  Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs ->
  azero m (shad a) (ms / 8).
Proof.
  intros L cs m a ms SHZ A8 ALO AHI MS0 HH HC.
  assert (PT : forall i, 0 <= i < ms / 8 -> m (wa (shad a + i)) = Some (Z_to_bv 8 0)).
  { intros i Hi. replace (shad a + i) with (shad (a + 8 * i)) by (rewrite !shad_div; clear -A8; Z.div_mod_to_equations; lia).
    apply SHZ.
    - unfold ablk, KLS, K_HIGH_MEM in *. unfold AIMG_HI in *. clear -Hi ALO AHI A8. Z.div_mod_to_equations. lia.   (* [comment removed for export] *)
    - eapply Forall_impl; [| exact HH]. cbn beta. intros iv Hiv. clear -Hi Hiv A8. Z.div_mod_to_equations. lia.
    - eapply Forall_impl; [| exact HC]. cbn beta. intros ch Hch. clear -Hi Hch A8. Z.div_mod_to_equations. lia. }
  assert (SR : 0 <= shad a /\ shad a + ms / 8 <= 2^64).
  { (pose proof (ablk_lin _ _ ALO) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 AL3 AL4; nd_post). rewrite shad_div. unfold ASHOFF in *. clear -AL2 AL4 AHI MS0. Z.div_mod_to_equations. lia. }   (* [comment removed for export] *)
  split; [exact PT|]. split; [lia|]. split; [lia|]. intros i Hi. rewrite (wview_some _ _ _ (PT i Hi)). discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_insert_sec : forall st st' p mb ms n,
  (a_live st) !! p = None ->
  a_live st' = <[p := CSec mb ms n]> (a_live st) -> a_qloc st' = a_qloc st -> a_qglob st' = a_qglob st ->
  Permutation (sec_chunks_of st') (CSec mb ms n :: sec_chunks_of st).
Proof.
  intros st st' p mb ms n NONE E1 E2 E3. unfold sec_chunks_of, achunks. rewrite E1, E2, E3, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
  apply Permutation_app_tail.
  pose proof (map_to_list_insert (a_live st) p (CSec mb ms n) NONE) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P.
  eapply Permutation_trans; [apply filter_is_sec_perm; exact P|]. cbn. apply Permutation_refl.
Qed.

#[using="Type"] Lemma awf_fresh_none : forall L st X, awf L st X -> (a_live st) !! (a_next st) = None.
Proof.
  intros L st X WF. destruct WF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FRESH & _).
  destruct ((a_live st) !! (a_next st)) as [ch|] eqn:E; [| reflexivity]. exfalso. pose proof (FRESH _ _ E) as F. clear -F. lia.
Qed.

#[using="Type"] Lemma awf_sec : forall L st X nres' a ms n, awf L st X -> awf L (st_sec st nres' a ms n) X.
Proof.
  intros L st X nres' a ms n WF.
  pose proof (awf_fresh_none L st X WF) as NONE.
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 12%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12; nd_post).
  unfold awf. rewrite E1, E2, E7, E8.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. rewrite get_cls_st_sec, max_count_st_sec. unfold ndist. rewrite get_cls_st_sec. exact (PERC c Hc). }
  split. { intros c Hc. rewrite get_cls_st_sec. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CLB M]. split; [exact CLB|]. destruct (xb_st b) as [p| |]; try exact M.
           (nd_pre M 6%nat; intros M1 M2 M3 M4 M5 M6; nd_post). repeat (split; [assumption|]).
           rewrite lookup_insert_ne; [exact M6|]. intros E. assert (X0 : a_live st !! p = None) by (rewrite <- E; exact NONE). rewrite X0 in M6. discriminate. }
  split. { intros p c k Hp. destruct (N.eq_dec p (a_next st)) as [->|NE].
           - rewrite lookup_insert_eq in Hp. discriminate.
           - rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact (LIVE p c k Hp). }
  split. { intros p ch Hp. destruct (N.eq_dec p (a_next st)) as [->|NE]; [lia|].
           rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). pose proof (FRESH p ch Hp). lia. }
  exact UNIQ.
Qed.

#[using="Type"] Lemma ablocks_sec : forall L st X LB nres' a ms n,
  awf L st X -> ablocks L st X LB -> sec_wf1 L (CSec a ms n) ->
  ablocks L (st_sec st nres' a ms n) X (HB (a_next st) (a + SEC_UOFF) n :: LB).
Proof.
  intros L st X LB nres' a ms n WF (BH & BF & NDI & NDL) W1.
  pose proof (awf_fresh_none L st X WF) as NONE.
  destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _ & FRESH & _).
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 8%nat; intros _ _ _ _ _ _ E7 _; nd_post).
  assert (OLD : forall p A n', In (HB p A n') LB -> (p < a_next st)%N).
  { intros p A n' Hin. destruct (BH p A n' Hin) as [(b & Hb & Sb & _)|(mb & ms' & Lp & _)].
    - destruct (BUSY b Hb) as [_ M]. rewrite Sb in M. (nd_pre M 6%nat; intros _ _ _ _ _ M5; nd_post). exact (FRESH _ _ M5).
    - exact (FRESH _ _ Lp). }
  split; [| split; [| split]].
  - intros p A n' [E|Hin].
    + injection E as <- <- <-. right. exists a, ms. rewrite E7, lookup_insert_eq. split; [reflexivity|]. split; [reflexivity| exact W1].
    + destruct (BH p A n' Hin) as [(b & Hb & R)|(mb & ms' & Lp & R)].
      * left. exists b. split; [exact Hb| exact R].
      * right. exists mb, ms'. split; [| exact R]. rewrite E7, lookup_insert_ne; [exact Lp|].
        intros E. pose proof (OLD _ _ _ Hin) as F. rewrite E in F. clear -F. lia.
  - intros cls A n' [E|Hin]; [discriminate| exact (BF cls A n' Hin)].
  - cbn. constructor; [| exact NDI]. intros Hin. unfold hb_ids in Hin. apply in_flat_map in Hin. (nd_pre Hin 3%nat; intros b Hb Hp; nd_post).
    destruct b as [[p|cls] A n']; cbn in Hp; [| destruct Hp]. destruct Hp as [E|[]]. subst p. pose proof (OLD _ _ _ Hb) as F. clear -F. lia.
  - constructor; [| exact NDL]. intros Hin. pose proof (OLD _ _ _ Hin) as F. clear -F. lia.
Qed.

#[using="Type"] Lemma arng_sec : forall L RNG RNG' st X nres' a ms n,
  awf L st X -> arng L RNG st -> fp_le RNG RNG' ->
  rng RNG' a ms -> rng RNG' (shad a) (ms / 8) -> rng RNG' (al_ptr_array L) (8 * nres') ->
  arng L RNG' (st_sec st nres' a ms n).
Proof.
  intros L RNG RNG' st X nres' a ms n WF AR LE R1 R2 R3.
  (pose proof (arng_mono L RNG RNG' st LE AR) as ndP__; nd_pre ndP__ 13%nat; intros A1 A2 A3 A4 A5 A6 A6a A6b A6c A7 A8 A9 A10; nd_post).
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 12%nat; intros _ _ E3 _ _ _ E7 _ E9 _ E11 _; nd_post).
  unfold arng. rewrite E3. repeat (split; [assumption|]). split; [| exact A10].
  eapply RSEC_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [eapply awf_fresh_none; exact WF| exact E7| exact E9| exact E11]|].
  constructor; [| exact A9]. cbn [sec_mb sec_ms]. split; [exact R1| exact R2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma ASECc_perm : forall cs cs' L st X m, Permutation cs cs' -> ASECc cs L st X m -> ASECc cs' L st X m.
Proof.
  intros cs cs' L st X m P (WFS & ARR & INST & PZ & SHZ).
  split; [| split; [| split; [exact INST| split; [exact PZ|]]]].
  - (nd_pre WFS 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post). unfold asec_wf.
    split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [rewrite <- (Permutation_length P); exact WL|]. split; [exact WB|].
    split; [| eapply sec_disjoint_perm; [exact P| exact WD]].
    rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
  - (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). exists order. split; [eapply Permutation_trans; [exact PO| exact P]|].
    split; [exact U64| split; [exact JK| exact PER]].
  - intros x Hx HF HC. apply (SHZ x Hx HF). rewrite Forall_forall in HC |- *. intros ch Hin. apply HC.
    eapply Permutation_in; [exact P| exact Hin].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma asec_chunk_frameW : forall L W m m' mb ms n idx lv,
  munch W m m' -> wmono asegs m m' ->
  sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k) ->
  asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros L W m m' mb ms n idx lv MU WM WF1 DC DS CH.
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. (nd_pre WF0 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post).
  (pose proof (sec_facts n ltac:(lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ RSE RSR _ NSE _ MSR MSM _; nd_post). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  (nd_pre GR 3%nat; intros GR1 GR2 GR3; nd_post).
  cbn [asec_chunk] in CH |- *. (nd_pre CH 9%nat; intros H1 H2 H3 H4 (b1 & ctx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.

#[using="Type"] Lemma junk_zero_len : forall m A n, junk_at m A n -> n <= 0 -> forall m', junk_at m' A n.
Proof.
  intros m A n [bs H] Hn m'. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
  split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
  - split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

Section Append.
Variables (L : alayout) (W : list (Z * Z)) (m m' : amem).
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono asegs m m'.
Variables (st : astate) (X : aconc) (nres' a n id : Z).
Let ms := sec_map_size n.
Let cs := sec_chunks_of st.
Let nsec := a_nsec st.
Let nres := a_nres st.
Let PA := al_ptr_array L.
Let UB := a + 6144.
Hypothesis WF : awf L st X.
Hypothesis SEC : ASECc cs L st X m.
Hypothesis N : 1 <= n <= AREQMAX.
Hypothesis PRIM : is_primary n = false.
Hypothesis W1 : sec_wf1 L (CSec a ms n).
Hypothesis DJ : Forall (fun ch => a + ms <= sec_mb ch \/ sec_mb ch + sec_ms ch <= a) cs.
Hypothesis NR' : (nsec <> nres /\ nres' = nres)
              \/ (nsec = nres /\ nres' = nres + 16384
                  /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))]).
Hypothesis NRB : nres' <= 1048576.
(* [comment removed for export] *)
Hypothesis Wch : forall ch, In ch cs ->
     (forall A k, sec_mb ch <= A -> A + k <= sec_mb ch + sec_ms ch -> 0 < k -> disjoint_from W A k)
  /\ (forall A k, shad (sec_mb ch) <= A -> A + k <= shad (sec_mb ch) + sec_ms ch / 8 -> 0 < k -> disjoint_from W A k).
Hypothesis Wpa : 0 < nsec -> disjoint_from W PA (8 * nsec).
Hypothesis Wpj : nsec + 1 < nres -> disjoint_from W (PA + 8 * nsec + 8) (8 * (nres - nsec - 1)).
Hypothesis Wbase : disjoint_from W (AINSTANCE + 80) 8.
Hypothesis Wp0 : disjoint_from W (shad (al_space_beg L)) (shlen K_REGION).
Hypothesis Wshz : forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) -> (x < a \/ a + ms <= x) -> disjoint_from W (shad x) 1.   (* [comment removed for export] *)
(* [comment removed for export] *)
Hypothesis C_srt : rw_cells asegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)].
Hypothesis C_jst : junk_at m' (AINSTANCE + 136) 32.
Hypothesis C_jbs : junk_at m' (AINSTANCE + 168) 512.
Hypothesis C_mtx : rw_cells asegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].
Hypothesis C_jgl : junk_at m' (AINSTANCE + 704) 16.
Hypothesis C_slot : rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)].
Hypothesis C_hdr : rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)].
Hypothesis C_pgj : junk_at m' (a + 32) (4096 - 32).
Hypothesis C_mag : rw_cells asegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))].
Hypothesis C_lcj : junk_at m' (a + 4096 + 16) (2048 - 32).
Hypothesis C_ahd : rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)].
Hypothesis IDR : 0 < id < 2^31.
Hypothesis C_usr : junk_at m' UB (ms - 6144).
Hypothesis C_shf : fill_at m' (shad a) 768 0xfa.
Hypothesis C_shu : rw_cells asegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)].
Hypothesis C_sht : fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa.

#[using="rc L id nres PA UB C_hdr C_pgj C_mag C_lcj C_ahd IDR C_usr C_shf C_shu C_sht"] Lemma asec_chunk_new : asec_chunk m' (CSec a ms n) nsec true.
Proof.
  cbn [asec_chunk]. unfold SEC_UOFF, SEC_MAGIC. fold UB.
  replace (UB - 16) with (UB + -16) by (subst UB; lia).
  split; [exact C_hdr|]. split; [exact C_pgj|]. split; [exact C_mag|]. split; [exact C_lcj|].
  split. { exists 17, id. split; [exact C_ahd|]. split; [lia|]. split; [reflexivity| lia]. }
  split; [unfold SEC_UOFF; exact C_usr|]. split; [exact C_shf|]. split; [| exact C_sht].
  unfold sec_user_shadow. exact C_shu.
Qed.

#[using="W m MU WM id cs nsec nres PA UB WF SEC N PRIM W1 DJ NR' NRB Wch Wpa Wpj Wbase Wp0 Wshz C_srt C_jst C_jbs C_mtx C_jgl C_slot C_hdr C_pgj C_mag C_lcj C_ahd IDR C_usr C_shf C_shu C_sht"] Theorem asec_append : ASEC_of L (st_sec st nres' a ms n) X m'.
Proof.
  pose proof (awf_fresh_none L st X WF) as NONE.
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 12%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12; nd_post).
  destruct SEC as (WFS & ARR & INST & PZ & SHZ).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post).
  pose proof W1 as W0. cbn [sec_wf1] in W0. (nd_pre W0 7%nat; intros G1 G2 G3 G4 G5 G6 GC; nd_post).
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB _ RSE RSR _ NSE _ MSR MSM MSB; nd_post). fold ms in MSR, MSM, MSB.
  pose proof (ao_ptr L ALO) as OP. unfold aobj in OP. fold PA in OP.
  assert (NEWNOT : ~ In (CSec a ms n) cs).
  { intros Hin. pose proof (proj1 (Forall_forall _ _) DJ _ Hin) as D. cbn [sec_mb sec_ms] in D. clear -D MSB. lia. }
  assert (NSR : 0 <= nsec /\ nsec + 1 <= nres' /\ (nres' = nres \/ nres' = nres + 16384)).
  { subst nsec nres. destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB; lia. }
  (nd_pre NSR 3%nat; intros NS0 NS1 NS2; nd_post).
  unfold ASEC_of. eapply ASECc_perm; [apply Permutation_sym; eapply sec_chunks_of_insert_sec; [exact NONE| exact E7| exact E9| exact E11]|].
  fold cs. split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    unfold asec_wf. rewrite E2, E3, E4. split; [exact ALO|]. split; [exact WP|].
    split. { split; [| clear -NRB NS0 NS1; lia]. destruct WR as [WRM _]. destruct NS2 as [-> | ->]; [exact WRM|].
             subst nres. clear -WRM. Z.div_mod_to_equations. lia. }
    split; [cbn [length]; subst nsec; clear -WL; lia|]. split; [clear -NS0 NS1; subst nsec; lia|].
    split; [constructor; [exact W1| exact WF1]|].
    destruct WD as [ND PW]. split; [constructor; [exact NEWNOT| exact ND]|].
    intros ci cj [<-|Hi] [<-|Hj] NE; [exfalso; exact (NE eq_refl)| | |].
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hj) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + pose proof (proj1 (Forall_forall _ _) DJ _ Hi) as D. cbn [sec_mb sec_ms] in D |- *. clear -D. lia.
    + exact (PW ci cj Hi Hj NE).
  - (* [comment removed for export] *)
    (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). unfold asec_arr. rewrite E3, E4. fold PA. fold nsec.
    assert (LEN : Z.of_nat (length order) = nsec) by (rewrite (Permutation_length PO); exact WL).
    exists (order ++ [CSec a ms n]).
    split. { eapply Permutation_trans; [apply Permutation_app_comm|]. cbn [app]. apply perm_skip. exact PO. }
    split; [| split].
    + rewrite map_app. cbn [map sec_mb]. apply u64arr_snoc.
      * destruct order as [|o0 order'].
        { destruct U64 as [[B0 [B1 _]] _]. apply u64arr_nil; [clear -OP; lia| clear -OP; atop_facts; lia]. }
        eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. cbn [length] in LEN |- *.
        replace (8 * Z.of_nat (S (length order'))) with (8 * nsec) by (clear -LEN; lia). apply Wpa. clear -LEN; lia.
      * rewrite length_map. replace (PA + 8 * Z.of_nat (length order)) with (PA + 8 * nsec) by (clear -LEN; lia). exact C_slot.
    + destruct NR' as [(A1 & A2)|(A1 & A2 & ZC)].
      * rewrite A2. destruct (junk_split m (PA + 8 * nsec) 8 (8 * (nres - nsec - 1))
                      ltac:(replace (8 + 8 * (nres - nsec - 1)) with (8 * (nres - nsec)) by (clear; lia); exact JK) ltac:(clear; lia) ltac:(clear -A1 WB; subst nsec nres; lia))
          as [_ JR].
        replace (PA + 8 * (nsec + 1)) with (PA + 8 * nsec + 8) by (clear; lia).
        replace (8 * (nres - (nsec + 1))) with (8 * (nres - nsec - 1)) by (clear; lia).
        destruct (Z_lt_le_dec (nsec + 1) nres) as [LT|GE].
        { eapply junk_frame; [exact JR| exact MU| exact WM| intros _; apply Wpj; exact LT]. }
        eapply junk_zero_len; [exact JR| clear -GE; lia].
      * rewrite A2, A1. subst nres. replace (PA + 8 * (a_nres st + 1)) with (PA + 8 * a_nres st + 8) by (clear; lia).
        replace (8 * (a_nres st + 16384 - (a_nres st + 1))) with (131072 - 8) by (clear; lia). eexists. exact ZC.
    + intros i ch Hi.
      destruct (Nat.lt_ge_cases i (length order)) as [LT|GE].
      * rewrite nth_error_app1 in Hi by exact LT. (nd_pre (PER i ch Hi) 3%nat; intros lv LV CH; nd_post).
        assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
        (nd_pre (asec_wf_all L st cs ch WFS Hin) 4%nat; intros mb ms' n' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into WF1c).
        exists lv. split.
        { rewrite LV. unfold sec_live. rewrite E7. split; intros [p Hp].
          - exists p. rewrite lookup_insert_ne; [exact Hp|]. intros E. subst p. rewrite NONE in Hp. discriminate.
          - destruct (N.eq_dec p (a_next st)) as [->|NE].
            + rewrite lookup_insert_eq in Hp. injection Hp as Ea Em En. exfalso. apply NEWNOT. rewrite <- Ea, <- Em, <- En in Hin. exact Hin.
            + exists p. rewrite lookup_insert_ne in Hp by (intros E; apply NE; symmetry; exact E). exact Hp. }
        destruct (Wch _ Hin) as [DC DS]. cbn [sec_mb sec_ms] in DC, DS.
        eapply asec_chunk_frameW; [exact MU| exact WM| exact WF1c| exact DC| exact DS| exact CH].
      * rewrite nth_error_app2 in Hi by exact GE.
        assert (EI : i = length order) by (destruct (i - length order)%nat as [|k] eqn:EK; [clear -GE EK; lia| cbn in Hi; destruct k; discriminate]).
        subst i. rewrite Nat.sub_diag in Hi. cbn in Hi. injection Hi as <-.
        exists true. split.
        { split; [intros _| reflexivity]. exists (a_next st). rewrite E7, lookup_insert_eq. reflexivity. }
        rewrite LEN. exact asec_chunk_new.
  - (* [comment removed for export] *)
    (nd_pre INST 6%nat; intros I1 _ _ _ _ _; nd_post). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; exact Wbase]|].
    split; [exists (Z_to_bv 8 0); exact C_srt|]. split; [exact C_jst|]. split; [exact C_jbs|]. split; [| exact C_jgl].
    pose proof C_mtx as M4. rw_split M4 1%nat M0 M3. exact M3.
  - (* [comment removed for export] *)
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM| intros _; exact Wp0].
  - (* [comment removed for export] *)
    intros x Hx HF HC. apply Forall_cons_iff in HC. destruct HC as [HCn HC]. cbn [sec_mb sec_ms] in HCn.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM in *; unfold AIMG_HI, KLS in Hx; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia]. apply Wshz; [exact Hx| clear -HCn Hx; lia].
Qed.
End Append.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition WT (L : alayout) (sp a ms nsec nres nres' : Z) : list (Z * Z) :=
  [(sp - 4096, sp); (al_t L + 2800, al_t L + 3169); (AINSTANCE + 112, AINSTANCE + 720);
   (al_ptr_array L + 8 * nsec, al_ptr_array L + 8 * nsec + 8); (al_ptr_array L + 8 * nres, al_ptr_array L + 8 * nres');
   (a, a + ms); (shad a, shad a + ms / 8);
   (0x1808c8, 0x5d0910); (al_nodes L, al_nodes L + 1048576); (al_store L, al_store L + 8388608)]%Z.

(* [comment removed for export] *)
Definition wt_facts (L : alayout) (sp lo a ms nsec nres nres' : Z) : Prop :=
     alayout_ok L /\ ATOP <= lo /\ lo <= sp - 4096
  /\ ablk a (a + ms) /\ a + ms <= ATOP /\ a mod 4096 = 0 /\ ms mod 4096 = 0 /\ 0 < ms /\ sec_clear L a ms
  /\ 0 <= nsec /\ nsec + 1 <= nres' /\ 8 * nres' <= 8388608 /\ 0 <= nres <= nres'.

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

Section KW.
Variables (L : alayout) (sp lo a ms nsec nres nres' : Z).
Hypothesis WTF : wt_facts L sp lo a ms nsec nres nres'.
Let W' := List.filter nonempty (WT L sp a ms nsec nres nres').

Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
  destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
Local Ltac facts :=
  lazymatch goal with |- _ =>
  (pose proof WTF as ndP__; nd_pre ndP__ 13%nat; intros ALO CEIL LO AHI0 ACE AAL MSM MSP (C_t & C_c & C_r & C_p & C_n & C_s & C_f & C_d) NS0 NS1 NS8 NS9; nd_post);
  pose proof (ao_t L ALO) as OT; pose proof (ao_ctx L ALO) as OC; pose proof (ao_res L ALO) as ORS; pose proof (ao_nodes L ALO) as ON;
  pose proof (ao_store L ALO) as OS; pose proof (ao_ptr L ALO) as OP; unfold aobj in OT, OC, ORS, ON, OS, OP;
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT OTs] [jT OTi]; nd_post); (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OCi _ [kC OCs]; nd_post);   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros ONi _ [kN ONs]; nd_post); (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OSi _ [kS OSs]; nd_post);
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi _ [kP OPs]; nd_post); pose proof (ao_res_hi L ALO) as RHI;
  destruct (ablk_int _ _ AHI0) as [kA ABND]; (pose proof (ablk_lin _ _ AHI0) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 _ _; nd_post); unfold AIMG_HI in AL1;   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res; pose proof (ad_nodes_res L ALO) as D_n_res; pose proof (ad_store_res L ALO) as D_s_res;
  pose proof (ad_ptr_res L ALO) as D_p_res; pose proof (ad_t_ctx L ALO) as D_t_c; pose proof (ad_t_nodes L ALO) as D_t_n;
  pose proof (ad_t_store L ALO) as D_t_s; pose proof (ad_t_ptr L ALO) as D_t_p; pose proof (ad_ctx_nodes L ALO) as D_c_n;
  pose proof (ad_ctx_store L ALO) as D_c_s; pose proof (ad_ctx_ptr L ALO) as D_c_p;
  unfold adisj in D_t_res, D_n_res, D_s_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_p, D_c_n, D_c_s, D_c_p
  end.

#[using="rc tlsI L sp lo nsec nres nres' WTF"] Lemma WT_shad : 0x800b8800 <= shad a /\ shad a + ms / 8 = shad (a + ms) /\ shad (a + ms) <= 0x10007fef8000      (* [comment removed for export] *)
                /\ (forall x, x < a -> shad x + 1 <= shad a) /\ (forall x, a + ms <= x -> shad (a + ms) <= shad x).
Proof.
  facts. rewrite !shad_div. unfold ASHOFF in *. split; [clear -AL1; Z.div_mod_to_equations; lia|].
  split; [clear -AAL MSM; Z.div_mod_to_equations; lia|]. split; [clear -ACE; Z.div_mod_to_equations; lia|].
  split; intros x Hx; rewrite shad_div; unfold ASHOFF; [clear -Hx AAL| clear -Hx]; Z.div_mod_to_equations; lia.
Qed.

#[using="Type"] Lemma KT_X : forall A k, 0 <= k ->
  (forall iv, In iv (WT L sp a ms nsec nres nres') -> fst iv < snd iv -> A + k <= fst iv \/ snd iv <= A) ->
  disjoint_from W' A k.
Proof.
  intros A k Hk H. subst W'. apply disjoint_from_Forall. apply Forall_forall. intros iv Hiv.
  apply List.filter_In in Hiv. destruct Hiv as [Hiv NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV. exact (H iv Hiv NEV).
Qed.

#[using="rc tlsI lo WTF"] Lemma KT_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= AIMG_HI ->      (* [comment removed for export] *)
  (A + k <= AINSTANCE + 112 \/ AINSTANCE + 720 <= A) -> (A + k <= 0x1808c8 \/ 0x5d0910 <= A) -> disjoint_from W' A k.
Proof.
  facts. (pose proof WT_shad as ndP__; nd_pre ndP__ 4%nat; intros SA1 SA2 SA3 _; nd_post).
  intros A k H1 H2 H3 H4 H5. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 H5 NEV CEIL LO OT OP AL1 SA1 ON OS NS0 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

#[using="tlsI lo WTF"] Lemma KT_obj : forall A k, (A + k <= 65536 \/ 6307840 <= A) -> (A + k <= 2147446784 \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ATOP ->      (* [comment removed for export] *)
  (A + k <= al_t L + 2800 \/ al_t L + 3169 <= A) -> (A + k <= al_ptr_array L \/ al_ptr_array L + 8388608 <= A) ->
  (A + k <= a \/ a + ms <= A) -> (A + k <= al_nodes L \/ al_nodes L + 1048576 <= A) -> (A + k <= al_store L \/ al_store L + 8388608 <= A) ->
  disjoint_from W' A k.
Proof.
  facts. (pose proof WT_shad as ndP__; nd_pre ndP__ 4%nat; intros SA1 SA2 SA3 _; nd_post).
  intros A k H0 H1 H2 H3 H4 H5 H6 H7 H8. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H0 H1 H2 H3 H4 H5 H6 H7 H8 NEV CEIL LO NS0 NS1 NS8 NS9 SA1 SA2 SA3; lia.
Qed.

#[using="rc tlsI lo WTF"] Lemma KT_shad : forall A k, 2147446784 <= A -> 0 <= k -> A + k <= 17594333495296 ->      (* [comment removed for export] *)
  (A + k <= shad a \/ shad (a + ms) <= A) -> disjoint_from W' A k.
Proof.
  facts. (pose proof WT_shad as ndP__; nd_pre ndP__ 4%nat; intros SA1 SA2 SA3 _; nd_post).
  intros A k H1 H2 H3 H4. apply KT_X; [exact H2|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
    clear -H1 H2 H3 H4 NEV CEIL LO OT OP ABND ON OS SA2 NS0 NS1 NS8 NS9 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
Qed.

(* [comment removed for export] *)

#[using="rc tlsI lo WTF"] Lemma KT_t : forall A k, al_t L <= A -> 0 <= k -> A + k <= al_t L + 2800 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OT D_t_p C_t D_t_n D_t_s OTs OTi; lia. Qed.   (* [comment removed for export] *)

#[using="rc tlsI lo WTF"] Lemma KT_ctx : forall A k, al_ctx L <= A -> 0 <= k -> A + k <= al_ctx L + 65536 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 OC OT D_t_c D_c_p C_c D_c_n D_c_s OTs OTi OCs OCi; lia. Qed.

#[using="rc tlsI lo WTF"] Lemma KT_res : forall A k, al_res L <= A -> 0 <= k -> A + k <= al_res L + 137439023104 -> disjoint_from W' A k.
Proof. facts. intros A k H1 H2 H3. apply KT_obj; atop_facts; clear -H1 H2 H3 ORS RHI OT D_t_res D_p_res C_r D_n_res D_s_res OTs OTi; lia. Qed.   (* [comment removed for export] *)

#[using="rc tlsI sp lo nsec nres nres' WTF"] Lemma KT_res_geo : 2201439137792 <= shad (al_res L) /\ shad (al_res L) + shlen 137439023104 = shad (al_res L + 137439023104)
                   /\ shad (al_res L + 137439023104) <= 0x10007fef8000      (* [comment removed for export] *)
                   /\ (shad (al_res L + 137439023104) <= shad a \/ shad (a + ms) <= shad (al_res L)).
Proof. facts. rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -ORS RHI C_r AAL. Z.div_mod_to_equations. lia. Qed.

#[using="rc tlsI lo WTF"] Lemma KT_res_sh : forall A k, shad (al_res L) <= A -> 0 <= k -> A + k <= shad (al_res L + 137439023104) -> disjoint_from W' A k.
Proof. (pose proof KT_res_geo as ndP__; nd_pre ndP__ 4%nat; intros SR1 SR2 SR3 SR4; nd_post). intros A k H1 H2 H3. apply KT_shad; clear -H1 H2 H3 SR1 SR3 SR4; lia. Qed.

(* [comment removed for export] *)
#[using="lo WTF"] Lemma KT_tls : forall A k, ATPv + -200 <= A -> 0 <= k -> A + k <= ATPv + 312 -> disjoint_from W' A k.
Proof.
  intros A k H1 H2 H3. pose proof ATPv_img as TI. apply KT_img; unfold AIMG_HI, AINSTANCE; lia.
Qed.

(* [comment removed for export] *)
#[using="lo WTF"] Lemma KT_rt : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt L m -> arep_rt L m'.
Proof.
  intros m m' MU WM RT. eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
  repeat (apply Forall_cons; [cbn [fst snd]; first [apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia | apply KT_ctx; clear; lia | apply KT_tls; clear; lia] |]). apply Forall_nil.
Qed.
#[using="rc tlsI lo WTF"] Lemma KT_rt2 : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt2 m -> arep_rt2 m'.
Proof. intros m m' MU WM RT2. eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia. Qed.
#[using="rc tlsI lo WTF"] Lemma KT_rt3 : forall m m', munch W' m m' -> wmono asegs m m' -> arep_rt3 m -> arep_rt3 m'.
Proof.
  intros m m' MU WM RT3. eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]. unfold rt3_hulls.
  repeat (apply Forall_cons; [cbn [fst snd]; apply KT_img; clear; unfold AIMG_HI, AINSTANCE; lia |]). apply Forall_nil.
Qed.
#[using="rc tlsI lo WTF"] Lemma KT_relro : forall m m', munch W' m m' -> arelro m -> arelro m'.
Proof. intros m m' MU HRO. eapply arelro_frame; [exact MU | exact HRO | apply KT_img; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]. Qed.
End KW.

Section Store.
Variable DI : ADepotIface.
Variables (AQ : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Let AHS : aholes := AH DI AQ ASEC_of AFK.
Hypothesis HL : ahole_laws AHS.
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.

Definition store_sec__stmt : Prop := forall (L : alayout) (RNG RNG' : footprint) (sp lo : Z) (m m' : amem) (st : astate) (X : aconc) (LB : list ablock)
    (n a nres' id : Z) (sj' : list word) (RESV : list (Z * Z)),
  let nsec := a_nsec st in let nres := a_nres st in let PA := al_ptr_array L in let ms := sec_map_size n in
  let UB := a + 6144 in let t := al_t L in
  alayout_ok L -> arng L RNG st -> AREP AHS L st X m -> ablocks L st X LB -> AFK L LB m ->
  1 <= n <= AREQMAX -> is_primary n = false ->
  sfresh RESV st n a = true -> aresv_ok L RESV ->
  ATOP <= lo -> lo <= sp - 4096 -> sp <= 2^47 ->
  fp_le RNG RNG' -> rng RNG' a ms -> rng RNG' (shad a) (ms / 8) ->
  ((nsec <> nres /\ nres' = nres)
   \/ (nsec = nres /\ nres' = nres + 16384
       /\ rw_cells asegs m' (PA + 8 * nres + 8) [CB (Z.to_nat (131072 - 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (131072 - 8)))])) ->
  nres' <= 1048576 -> rng RNG' PA (8 * nres') ->
  munch (WT L sp a ms nsec nres nres') m m' -> wmono asegs m m' ->
  (* [comment removed for export] *)
  u64arr asegs m' (t + 2800) sj' -> length sj' = 46%nat -> rw_cells asegs m' (t + 3168) [C1 (Z_to_bv 8 0)] ->
  rw_cells asegs m' (AINSTANCE + 112) [C8 (Z_to_bv 64 nres'); C8 (Z_to_bv 64 (nsec + 1))] ->
  rw_cells asegs m' (AINSTANCE + 128) [C1 (Z_to_bv 8 0)] -> junk_at m' (AINSTANCE + 136) 32 -> junk_at m' (AINSTANCE + 168) 512 ->
  rw_cells asegs m' (AINSTANCE + 680) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m' (AINSTANCE + 704) 16 ->
  rw_cells asegs m' (PA + 8 * nsec) [C8 (Z_to_bv 64 a)] ->
  rw_cells asegs m' a [C8 (Z_to_bv 64 a); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 nsec)] ->
  junk_at m' (a + 32) (4096 - 32) ->
  rw_cells asegs m' (a + 4096) [C8 (Z_to_bv 64 0xCC6E96B9CC6E96B9); C8 (Z_to_bv 64 (UB + -16))] ->
  junk_at m' (a + 4096 + 16) (2048 - 32) ->
  rw_cells asegs m' (UB + -16) [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 17); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 id)] ->
  0 < id < 2^31 ->
  junk_at m' UB (ms - 6144) ->
  fill_at m' (shad a) 768 0xfa ->
  rw_cells asegs m' (shad UB) [CB (Z.to_nat (granules n)) (block_shadow_bytes n)] ->
  fill_at m' (shad UB + granules n) (ms / 8 - 768 - granules n) 0xfa ->
  ADEPOT DI L m' ->
     aheap_pres CI LB sp m m'
  /\ AHEAP_P AHS L RNG' (st_sec st nres' a ms n) (HB (a_next st) UB n :: LB) m'.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 0).
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 1).
Variable RNG' : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 2).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 3).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 4).
Variable m : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 5).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 6).
Variable st : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 7).
Variable X : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 8).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 9).
Variable n : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 10).
Variable a : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 11).
Variable nres' : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 12).
Variable id : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 13).
Variable sj' : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 14).
Variable RESV : ltac2:(SecDietF.SzSecF.ty 'store_sec__stmt 15).
Let ms := sec_map_size n.
Let W' := List.filter nonempty (WT L sp a ms (a_nsec st) (a_nres st) nres').
Let st2 := st_sec st nres' a ms n.
#[using="HL CI_OK CI_OK2 ms W' st2"] Lemma store_sec__body : ltac:(let T := type of (fun (h : store_sec__stmt) => h L RNG RNG' sp lo m m' st X LB n a nres' id sj' RESV) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (RNG, (RNG', (sp, (lo, (m, (m', (st, (X, (LB, (n, (a, (nres', (id, (sj', RESV)))))))))))))))) as _.
 cbv zeta.
  intros ALO ARNG AR BL HFK N PRIM FRSH ROK CEIL LO SP47 FPLE RA RSA NR' NRB RPA' MU0 WM
         STATS LSJ UNW I112 I128 J136 J168 I680 J704 SLOT HDR PGJ MAG LCJ AHD IDR USR SHF SHU SHT DEP.
  chg (sec_map_size n) ms.
  (* [comment removed for export] *)
  (pose proof (valid_geo L RESV st n a N PRIM FRSH ROK) as ndP__; nd_pre ndP__ 5%nat; intros AAL AHI0 ACE MSP _; nd_post). fold ms in ACE, MSP.
  pose proof (valid_clear L RESV st n a N PRIM FRSH ROK) as VC. fold ms in VC.
  pose proof (valid_hulls L RESV st n a N PRIM FRSH ROK) as VH. fold ms in VH.
  pose proof (valid_chunks L RESV st n a N PRIM FRSH ROK) as VK. fold ms in VK.
  pose proof (valid_wf1 L RESV st n a N PRIM FRSH ROK) as VW. fold ms in VW.
  (pose proof (sec_facts n N PRIM) as ndP__; nd_pre ndP__ 10%nat; intros NB _ RSE RSR _ NSE _ MSR MSM MSB; nd_post). fold ms in MSR, MSM, MSB.
  (nd_pre VC 10%nat; intros C_t C_c C_r C_p C_n C_s C_f C_d C_l C_ahm; nd_post).      (* [comment removed for export] *)
  unfold K_HIGH_MEM in AHI0.
  pose proof (munch_filter_nonempty _ m m' MU0) as MU. clear MU0. chg (List.filter nonempty (WT L sp a ms (a_nsec st) (a_nres st) nres')) W'.
  assert (NE : Forall (fun iv => fst iv < snd iv) W') by (apply nonempty_filter).
  (* [comment removed for export] *)
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 SP4; nd_post).
  pose proof (ao_t L ALO) as OT. pose proof (ao_ctx L ALO) as OC. pose proof (ao_res L ALO) as ORS. pose proof (ao_nodes L ALO) as ON. pose proof (ao_store L ALO) as OS.
  pose proof (ao_fake L ALO) as OFK. pose proof (ao_ptr L ALO) as OP. pose proof (ao_dtls L ALO) as OD.
  unfold aobj in OT, OC, ORS, ON, OS, OFK, OP, OD. pose proof (ao_space L ALO) as RSP.
  (pose proof (aobj4_int _ (ao_t L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kT OTs] [jT OTi]; nd_post). (pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OCi _ [kC OCs]; nd_post).   (* [comment removed for export] *)
  (pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros ONi _ [kN ONs]; nd_post). (pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OSi _ [kS OSs]; nd_post).
  (pose proof (aobj_int _ _ (ao_ptr L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OPi _ [kP OPs]; nd_post). (pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as ndP__; nd_pre ndP__ 3%nat; intros OFKi _ [kF OFKs]; nd_post).
  (pose proof (aobj4_int _ (ao_dtls L ALO)) as ndP__; nd_pre ndP__ 4%nat; intros _ _ [kD ODs] [jD ODi]; nd_post). pose proof (ao_res_hi L ALO) as RHI.
  destruct (ablk_int _ _ AHI0) as [kA ABND]. (pose proof (ablk_lin _ _ AHI0) as ndP__; nd_pre ndP__ 4%nat; intros AL1 AL2 _ _; nd_post). unfold AIMG_HI in AL1.   (* [comment removed for export] *)
  pose proof (ad_t_res L ALO) as D_t_res. pose proof (ad_ctx_res L ALO) as D_c_res. pose proof (ad_nodes_res L ALO) as D_n_res. pose proof (ad_store_res L ALO) as D_s_res.
  pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_ptr_res L ALO) as D_p_res. pose proof (ad_t_ctx L ALO) as D_t_c.
  pose proof (ad_t_nodes L ALO) as D_t_n. pose proof (ad_t_store L ALO) as D_t_s. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_t_ptr L ALO) as D_t_p.
  pose proof (ad_ctx_nodes L ALO) as D_c_n. pose proof (ad_ctx_store L ALO) as D_c_s. pose proof (ad_ctx_fake L ALO) as D_c_f. pose proof (ad_ctx_ptr L ALO) as D_c_p.
  pose proof (ad_nodes_fake L ALO) as D_n_f. pose proof (ad_nodes_ptr L ALO) as D_n_p. pose proof (ad_store_fake L ALO) as D_s_f. pose proof (ad_store_ptr L ALO) as D_s_p.
  pose proof (ad_fake_ptr L ALO) as D_f_p. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d. pose proof (ad_dtls_ptr L ALO) as D_d_p.
  pose proof (ad_nodes_dtls L ALO) as D_n_d. pose proof (ad_store_dtls L ALO) as D_s_d. pose proof (ad_fake_dtls L ALO) as D_f_d.
  unfold adisj in D_t_res, D_c_res, D_n_res, D_s_res, D_f_res, D_p_res, D_t_c, D_t_n, D_t_s, D_t_f, D_t_p, D_c_n, D_c_s, D_c_f, D_c_p,
                   D_n_f, D_n_p, D_s_f, D_s_p, D_f_p, D_d_res, D_t_d, D_d_p, D_n_d, D_s_d, D_f_d.
  (* [comment removed for export] *)
  pose proof AR as AR0. (nd_pre AR0 12%nat; intros WF RT INST THR CLS HQ HS HD HRO RT2 AVL RT3; nd_post).
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVE FRESH UNIQ; nd_post).
  pose proof HS as HS0. unfold AHS, AH in HS0. cbn [ah_sec] in HS0. unfold ASEC_of in HS0.
  (pose proof HS0 as ndP__; nd_pre ndP__ 5%nat; intros WFS ARR INST2 PZ SHZ; nd_post). (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros _ WP WR WL WB WF1 WD; nd_post).
  assert (NSR : 0 <= a_nsec st /\ a_nsec st + 1 <= nres' /\ 8 * nres' <= 8388608 /\ a_nres st <= nres').
  { destruct NR' as [(A1 & A2)|(A1 & A2 & _)]; clear -A1 A2 WB NRB WR; lia. }
  (nd_pre NSR 4%nat; intros NS0 NS1 NS8 NS9; nd_post).
  (* [comment removed for export] *)
  assert (WTF : wt_facts L sp lo a ms (a_nsec st) (a_nres st) nres').
  { unfold wt_facts. repeat lazymatch goal with |- _ /\ _ => split end; try assumption.
    - unfold sec_clear. repeat (split; [assumption|]). assumption.
    - clear -WB; lia. }
  (pose proof (WT_shad L sp lo a ms _ _ _ WTF) as ndP__; nd_pre ndP__ 5%nat; intros SA1 SA2 SA3 SAlt SAge; nd_post).
  pose proof (KT_X L sp a ms (a_nsec st) (a_nres st) nres') as KX. pose proof (KT_img L sp lo a ms _ _ _ WTF) as Kimg.
  pose proof (KT_obj L sp lo a ms _ _ _ WTF) as Kobj. pose proof (KT_shad L sp lo a ms _ _ _ WTF) as Kshad.
pose proof (KT_t L sp lo a ms _ _ _ WTF) as Kt.   (* [comment removed for export] *)
  pose proof (KT_ctx L sp lo a ms _ _ _ WTF) as Kctx. pose proof (KT_res L sp lo a ms _ _ _ WTF) as Kres.
  pose proof (KT_tls L sp lo a ms _ _ _ WTF) as Ktls. fold W' in Ktls.      (* [comment removed for export] *)
  pose proof (KT_res_sh L sp lo a ms _ _ _ WTF) as Kres_sh. (pose proof (KT_res_geo L sp lo a ms _ _ _ WTF) as ndP__; nd_pre ndP__ 4%nat; intros SR1 SR2 SR3 SR4; nd_post).
  fold W' in KX, Kimg, Kobj, Kshad, Kt, Kctx, Kres, Kres_sh.
  Local Ltac inWT Hiv := unfold WT in Hiv; cbn [In] in Hiv;
    destruct Hiv as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]; cbn [fst snd] in *.
  (* [comment removed for export] *)
  assert (BB : forall b, In b (x_busy X) -> al_res L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_res L + 137439023104).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    (nd_pre (PERC (xb_class b) CLB) 12%nat; intros Q1 Q2 _ _ _ _ _ _ _ _ _ QR; nd_post).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    (pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
    unfold xb_alloc, aregion, K_REGION, K_FREEARR_OFF, K_NUM_CLASSES in *. clear -P5 P4 Q1 Q2 CLB RSP. lia. }
  (pose proof (st_sec_fields st nres' a ms n) as ndP__; nd_pre ndP__ 12%nat; intros E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12; nd_post).
  chg (st_sec st nres' a ms n) st2.
  (* [comment removed for export] *)
  assert (AR' : AREP AHS L st2 X m').
  { split; [apply awf_sec; exact WF|].
    split. { eapply arep_rt_frame; [exact MU | exact WM | exact RT |]. unfold rt_hulls, ATP88, ATSD.
             repeat (apply Forall_cons; [cbn [fst snd]; first [apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia | apply Kctx; clear; lia | apply Ktls; clear; lia] |]). apply Forall_nil. }
    split. { (* [comment removed for export] *)
      (nd_pre INST 9%nat; intros I1 I2 I3 I4 I5 I6 I7 I8 I9; nd_post). unfold ainstance. subst st2. rewrite E3, E4.
      split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I3| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I4| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [exact I112|].
      split; [pose proof I680 as M4; rw_split M4 1%nat M0 M3; exact M0|].
      split; [eapply cells_frame; [exact I7| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      split; [eapply cells_frame; [exact I8| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]|].
      eapply cells_frame; [exact I9| exact MU| exact WM| cbn; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia]. }
    split. { (* [comment removed for export] *)
      (nd_pre THR 6%nat; intros T0 T40 CACHES CSTATS _ _; nd_post). unfold athread.
      split; [eapply cells_frame; [exact T0 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split; [eapply cells_frame; [exact T40 | exact MU | exact WM | cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]; apply Kt; clear; lia]|].
      split. { intros c Hc. eapply acache_cells_frame; [exact MU | exact WM | exact (CACHES c Hc) | subst st2; reflexivity | subst st2; reflexivity | reflexivity |].
               unfold acache_addr. unfold K_NUM_CLASSES in Hc. apply Kt; clear -Hc; lia. }
      split; [eapply junk_frame; [exact CSTATS | exact MU | exact WM | intros _; apply Kt; clear; lia]|].
      split; [exists sj'; split; [exact STATS| exact LSJ]| exact UNW]. }
    split. { (* [comment removed for export] *)
      intros c Hc. (nd_pre (CLS c Hc) 4%nat; intros REG FARR SLOTS SHADOW; nd_post).
      (nd_pre (PERC c Hc) 12%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 QLENF QLENC QCNTB QND QRANGE; nd_post).
      pose proof (size_of_class_facts c Hc) as [QS QS16]. pose proof (aregion_mod L c SAL) as RM. unfold K_NUM_CLASSES in Hc.
      assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                   /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
      { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
      (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
      split; [| split; [| split]].
      - eapply aregion_cells_frame; [exact MU | exact WM | exact REG | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity |].
        apply Kres; unfold aregion_info, ARI_STRIDE, K_SPACE_SIZE; change (2^37) with 137438953472; clear -Hc RSP; lia.
      - eapply afreearray_frame; [exact MU | exact WM | exact FARR | subst st2; reflexivity | subst st2; reflexivity | reflexivity | exact QLENF | exact Q5 | | clear -Q6; lia |].
        + apply Kres; unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *; [clear -RI1; lia | clear -Q5 Q6; lia | clear -RI2 RI3 Q6; lia].
        + apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF; clear -RI1; lia | apply shlen_nonneg; clear -Q5 Q6; lia |].
          rewrite <- shad_add_shlen by (unfold afreearr, K_FREEARR_OFF; clear -RM; Z.div_mod_to_equations; lia). apply shad_mono.
          unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX in *. clear -RI2 RI3 Q6. lia.
      - eapply (aslots_update L W' m m' MU WM st st2 X X c (-1)); [exact SLOTS | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia].
        + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
          split; [reflexivity|]. split.
          * apply Kres; [clear -P5 RI1; lia | clear -QS; lia | clear -P4 Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
          * intros b Hb. pose proof Hb as Hb'. unfold busy_of in Hb'. apply find_some in Hb'. destruct Hb' as [HIn HP].
            apply andb_true_iff in HP. destruct HP as [HP1 HP2]. apply Z.eqb_eq in HP1. apply Z.eqb_eq in HP2.
            split; [exact HP1|]. split; [exact HP2|]. exact (awf_fits L st X b WF HIn).
        + intros POS. apply Kres; [clear -Q1 RI1; lia | clear -POS; lia | clear -Q1 Q2 RI2 RI3; unfold K_FREEARR_OFF in *; lia].
      - eapply (aslot_shadow_update L W' m m' MU WM st st2 X X c (-1)); [exact SHADOW | subst st2; reflexivity | subst st2; reflexivity | subst st2; reflexivity | | | intros Hk; exfalso; clear -Hk; lia | apply shlen_nonneg; clear -QS; lia].
        + intros k Hk _. (pose proof (slot_in_region L st c k ltac:(clear -QS; lia) (proj1 Q1) Hk) as ndP__; nd_pre ndP__ 3%nat; intros P5 P4 P0; nd_post).
          pose proof (slot_aligned L c k SAL ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) as AL.
          split; [reflexivity|]. apply Kres_sh; [apply shad_mono; clear -P5 RI1; lia | rewrite shlen_div; clear -QS QS16; Z.div_mod_to_equations; lia |].
          rewrite <- shad_add_shlen by (clear -AL; Z.div_mod_to_equations; lia). apply shad_mono. clear -P4 Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia.
        + intros POS. apply Kres_sh; [apply shad_mono; clear -Q1 RI1; lia | clear -POS; lia |].
          rewrite <- shad_add_shlen by (pose proof (mod16_of_class _ _ Q3 QS16 ltac:(clear -QS; lia)) as AM; clear -AM RM; Z.div_mod_to_equations; lia).
          apply shad_mono. clear -Q1 Q2 RI2 RI3. unfold K_FREEARR_OFF in *. lia. }
    split. { (* [comment removed for export] *)
      eapply (hq_frame _ HL L st st2 X X m m' W'); [exact HQ | exact MU | exact WM | |].
      - unfold quar_untouched. apply Forall_forall. intros iv Hin.
        unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
        inWT Hin. all: unfold AINSTANCE in *.
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS C_t D_t_p D_t_n D_t_s NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: split; [clear -NEV CEIL LO OT OP AHI0 SA1 SA2 SA3 ON OS NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi; lia|].
        all: intros b Hb; destruct (BB b Hb) as [B1 B2]; destruct (xb_st b); [exact I| |];
          clear -NEV B1 B2 CEIL LO OT OP ORS AHI0 SA1 SA2 SA3 SR1 ON OS D_t_res D_p_res C_r D_n_res D_s_res NS0 NS1 NS8 NS9 WB ABND AL1 RHI OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - unfold quar_same. subst st2. rewrite E9, E10, E11, E12, E1. repeat (split; [reflexivity|]).
        split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
    split. { (* [comment removed for export] *)
      unfold AHS, AH. cbn [ah_sec]. subst st2.
      eapply (asec_append L W' m m' MU WM st X nres' a n id WF HS0 N PRIM VW VK NR' NRB).
      - intros ch Hin. (nd_pre (asec_wf_all L st _ ch WFS Hin) 4%nat; intros mb ms' n' ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into W1c). cbn [sec_mb sec_ms].
        pose proof W1c as W0. cbn [sec_wf1] in W0. (nd_pre W0 7%nat; intros G1 G2 G3 G4 G5 G6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
        pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
        (pose proof (sec_facts n' ltac:(clear -G5; lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ MSM' MSB'; nd_post). rewrite <- G4 in MSM', MSB'.
        destruct (ablk_int _ _ G2) as [kB GB].   (* [comment removed for export] *)
        assert (SHc : 0x800b8800 <= shad mb /\ shad mb + ms' / 8 = shad (mb + ms') /\ shad (mb + ms') <= 0x10007fef8000
                      /\ (shad (mb + ms') <= shad a \/ shad (a + ms) <= shad mb)).
        { rewrite !shad_div. unfold ASHOFF, K_HIGH_MEM in *. clear -G1 GB G3 MSM' D AAL MSM. Z.div_mod_to_equations. lia. }
        (nd_pre SHc 4%nat; intros SC1 SC2 SC3 SC4; nd_post). unfold K_HIGH_MEM in *.
        split; intros A k H1 H2 H3.
        + apply Kobj; clear -H1 H2 H3 GB G3 Ct Cp Cn Cs D; lia.
        + apply Kshad; clear -H1 H2 H3 SC1 SC2 SC3 SC4; lia.
      - intros POS. apply KX; [clear -POS; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -POS NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - intros LT. apply KX; [clear -LT NS0; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
          clear -LT NEV CEIL LO OT OP AHI0 ON OS SA2 SA3 D_t_p C_p D_n_p D_s_p NS0 NS1 NS8 NS9 WB ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
      - apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia.
      - replace (shlen K_REGION) with 536870912 by reflexivity.
        apply Kres_sh; [apply shad_mono; clear -RSP; lia| clear; lia|].
        rewrite !shad_div. clear -RSP. Z.div_mod_to_equations. lia.
      - intros x Hx Hxa. unfold K_HIGH_MEM, KLS in Hx. unfold AIMG_HI in Hx.
        assert (SX : 2147446784 <= shad x /\ shad x + 1 <= 17594333495296) by (rewrite shad_div; unfold ASHOFF; clear -Hx; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
        apply Kshad; [clear -SX; lia| clear; lia| clear -SX; lia|].
        destruct Hxa as [Hxa|Hxa]; [left; apply SAlt; exact Hxa| right; apply SAge; exact Hxa].
      - exact I128. - exact J136. - exact J168. - exact I680. - exact J704. - exact SLOT. - exact HDR. - exact PGJ. - exact MAG. - exact LCJ.
      - exact AHD. - exact IDR. - exact USR. - exact SHF. - exact SHU. - exact SHT. }
    split; [exact DEP|].
    split; [eapply arelro_frame; [exact MU | exact HRO | apply Kimg; clear; unfold ARELRO_LO, ARELRO_HI, AIMG_HI, AINSTANCE; lia]|].
    split; [eapply arep_rt2_frame; [exact MU | exact WM | exact RT2 | | |]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia|].
    split; [| eapply arep_rt3_frame; [exact MU | exact WM | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply Kimg; clear; unfold AIMG_HI, AINSTANCE; lia |]); apply Forall_nil].
    intros c Hc. (nd_pre (PERC c Hc) 8%nat; intros Q1 Q2 Q3 Q4 Q5 Q6 Q7 _; nd_post). unfold K_NUM_CLASSES in Hc.
    assert (RI : al_res L <= aregion L c /\ aregion L c + K_REGION <= al_space_beg L + K_SPACE_SIZE
                 /\ al_space_beg L + K_SPACE_SIZE + 4096 <= al_res L + 137439023104).
    { unfold aregion, K_REGION, K_SPACE_SIZE. change (2^37) with 137438953472. clear -Hc RSP. lia. }
    (nd_pre RI 3%nat; intros RI1 RI2 RI3; nd_post). unfold K_REGION, K_SPACE_SIZE in RI2, RI3. change (2^37) with 137438953472 in RI2, RI3.
    eapply (ashadow_avail_frame L W' m m' MU WM st); [exact (AVL c ltac:(unfold K_NUM_CLASSES; clear -Hc; lia)) | subst st2; reflexivity | subst st2; reflexivity | |].
    - intros POS. apply Kres_sh; [apply shad_mono; unfold aregion in *; clear -Q1 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; clear -RM Q4; unfold K_USER_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold K_FREEARR_OFF, K_REGION in *. clear -Q1 Q2 RI2 RI3. lia.
    - intros POS. apply Kres_sh; [apply shad_mono; unfold afreearr, K_FREEARR_OFF, aregion in *; clear -Q5 Q6 RI1; lia | clear -POS; lia |].
      rewrite <- shad_add_shlen by (pose proof (aregion_mod L c SAL) as RM; unfold afreearr, K_FREEARR_OFF; clear -RM Q7; unfold K_FREEARR_MAP in *; Z.div_mod_to_equations; lia).
      apply shad_mono. unfold afreearr, K_FREEARR_OFF, K_FREEARR_MAX, K_REGION in *. clear -Q5 Q6 RI2 RI3. lia. }
  (* [comment removed for export] *)
  assert (SHFK : 0x800b8800 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 = shad (al_fake L + 11571200)      (* [comment removed for export] *)
                 /\ shad (al_fake L + 11571200) <= 0x10007fef8000
                 /\ (shad (a + ms) <= shad (al_fake L) \/ shad (al_fake L + 11571200) <= shad a)).
  { rewrite !shad_div, shlen_div. unfold ASHOFF in *. clear -OFK C_f AAL OFKs OFKi. Z.div_mod_to_equations. lia. }
  (nd_pre SHFK 4%nat; intros SF1 SF2 SF3 SF4; nd_post).
  assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
    by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
  split.
  - (* [comment removed for export] *)
    intros x Hx CL. split; [| intros Hw; apply WM; exact Hw]. apply MU. rewrite wa_unsigned by exact Hx.
    destruct CL as [CL|TL].
    2:{ (* [comment removed for export] *)
        destruct TL as [[T|(ta & Hta & ->)]|[IM|IM]].
        4:{ pose proof (ao_ahm L ALO) as OAH. pose proof (aobj_img _ _ OAH ltac:(clear; lia)) as OAHI. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OAH, OAHI.
          rewrite <- (ao_ahm_eq L ALO) in IM. unfold AAHM_SZ in IM. pose proof (ad_ahm_t L ALO) as DA1. pose proof (ad_ahm_ptr L ALO) as DA2. pose proof (ad_ahm_nodes L ALO) as DA3. pose proof (ad_ahm_store L ALO) as DA4.
            unfold adisj in DA1, DA2, DA3, DA4.
            eapply (disjoint_outside W' x 1); [apply Kobj; clear -IM OAH OAHI DA1 DA2 DA3 DA4 C_ahm; lia | clear; lia]. }
        3:{ unfold AIMSH_LO, AIMSH_LEN in IM. eapply (disjoint_outside W' x 1); [apply Kshad; clear -IM SA1; lia | clear; lia]. }
        - eapply (disjoint_outside W' x 1); [apply Ktls; clear -T; lia | clear; lia].
        - pose proof (tls_shadow_band ta Hta) as (TS1 & TS2).
          assert (SATOP : shad ATOP <= 17594332446720) by (pose proof atop_range as ATR0; rewrite shad_div; unfold ASHOFF; clear -ATR0; Z.div_mod_to_equations; lia).
          eapply (disjoint_outside W' (shad ta) 1); [| clear; lia].
          apply Kshad; [clear -TS1; lia | clear; lia | clear -TS2 SATOP; lia |].
          destruct C_l as [D|D]; [right; apply SAge; clear -D Hta; lia | left; apply SAlt; clear -D Hta; lia]. }
    destruct CL as [STa | [CIa | [BLK | SH]]].
    + eapply (disjoint_outside W' x 1); [| clear; lia]. apply KX; [clear; lia|]. intros iv Hiv NEV. inWT Hiv; unfold AIMG_HI, AINSTANCE in *;
        clear -STa NEV CEIL LO OT OP AHI0 ACE ON OS SA2 SA3 NS0 NS1 NS8 NS9 WB SP47 ABND AL1 SA1 OTs OTi ONs ONi OSs OSi OPs OPi; lia.
    + (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post).
      pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
      eapply disjoint_outside; [eapply (Kimg x 1); unfold AIMG_HI, AINSTANCE in *; clear -R Q1 Q2 Q3 Q4; lia | clear; lia].
    + (nd_pre BLK 3%nat; intros b Hb R; nd_post). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
      * destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
        -- destruct (BB xb Hxb) as [Bb1 Bb2].
           pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
           eapply disjoint_outside; [eapply (Kres x 1) | clear; lia]; clear -R Bb1 Bb2 FIT; lia.
        -- (* [comment removed for export] *)
           assert (Hin : In (CSec mb0 ms0 n') (sec_chunks_of st)).
           { unfold sec_chunks_of, achunks. apply List.filter_In. split; [| reflexivity]. apply in_app_iff. left.
             apply in_map_iff. exists (p, CSec mb0 ms0 n'). split; [reflexivity|]. apply list_elem_of_In. apply elem_of_map_to_list. exact Lp. }
           pose proof (proj1 (Forall_forall _ _) VK _ Hin) as D. cbn [sec_mb sec_ms] in D.
           cbn [sec_wf1] in Gs. (nd_pre Gs 7%nat; intros Gs1 Gs2 Gs3 Gs4 Gs5 Gs6 (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd); nd_post).
           pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SFc. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
           destruct (ablk_int _ _ Gs2) as [kB GB].   (* [comment removed for export] *)
           eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R GB Gs3 Gs4 Gs5 SFc Ct Cp Cn Cs D; lia.
      * (nd_pre (FKD cls A n' Hb) 3%nat; intros K1 K2 K3; nd_post). atop_facts.
        eapply disjoint_outside; [eapply (Kobj x 1) | clear; lia]; clear -R K1 K3 OFK D_t_f D_f_p C_f D_n_f D_s_f OFKs OFKi; lia.
    + (nd_pre SH 3%nat; intros x' Hx' ndR1__; nd_post; revert ndR1__; intros ->).
      destruct Hx' as [STa | [CIa | FK]].
      * assert (SX : shad (a + ms) <= shad x' /\ shad x' + 1 <= 17594333495296).
        { split; [apply SAge; atop_facts; clear -STa ACE; lia|]. rewrite shad_div. unfold ASHOFF. clear -STa. Z.div_mod_to_equations. lia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1 SA2 MSB; lia | clear; lia].
      * (nd_pre CIa 3%nat; intros iv Hiv R; nd_post). (pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as ndP__; nd_pre ndP__ 3%nat; intros Q1 Q2 Q3; nd_post). cbn [fst snd] in *.
        assert (SX : 2147446784 <= shad x' /\ shad x' + 1 <= 0x800b8800) by (rewrite shad_div; unfold ASHOFF, AIMG_HI in *; clear -R Q1 Q3; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
        eapply disjoint_outside; [eapply (Kshad (shad x') 1); clear -SX SA1; lia | clear; lia].
      * (nd_pre FK 5%nat; intros cls FA sz Hin R; nd_post). (nd_pre (FKD cls FA sz Hin) 3%nat; intros K1 K2 K3; nd_post).
        assert (SX : shad (al_fake L) <= shad x' /\ shad x' + 1 <= shad (al_fake L + 11571200)).
        { rewrite !shad_div. clear -R K1 K3 OFK OFKs OFKi. Z.div_mod_to_equations. lia. }
        eapply disjoint_outside; [eapply (Kshad (shad x') 1) | clear; lia]; clear -SX SF1 SF3 SF4; lia.
  - (* [comment removed for export] *)
    split; [exact ALO|].
    split; [eapply (arng_sec L RNG RNG' st X); [exact WF| exact ARNG| exact FPLE| exact RA| exact RSA| exact RPA']|].
    split; [exists X; split; [exact AR'| replace (a + 6144) with (a + SEC_UOFF) by reflexivity; apply ablocks_sec; [exact WF| exact BL| exact VW]]|].
    unfold AHS, AH. cbn [ah_fake].
    eapply (hf_blocks _ HL L LB); [eapply (hf_frame _ HL L LB m m'); [exact HFK | exact MU | exact WM |] |].
    + unfold fake_untouched. apply Forall_forall. intros iv Hin.
      unfold W' in Hin. apply List.filter_In in Hin. destruct Hin as [Hin NEV]. unfold nonempty in NEV. apply Z.ltb_lt in NEV.
      (* [comment removed for export] *)
      pose proof (ad_tls_t L ALO) as D_l_t. pose proof (ad_tls_ptr L ALO) as D_l_p. pose proof (ad_tls_nodes L ALO) as D_l_n. pose proof (ad_tls_store L ALO) as D_l_s.
      unfold adisj in D_l_t, D_l_p, D_l_n, D_l_s. pose proof atp_lin as TLN.
      inWT Hin. all: unfold AINSTANCE in *.
      all: clear -NEV CEIL LO OT OP OFK OD AHI0 ACE SA1 SA2 SA3 SF1 SF2 SF3 SF4 ON OS D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d NS0 NS1 NS8 NS9 WB ABND AL1 OTs OTi ONs ONi OSs OSi OPs OPi OFKs OFKi ODs ODi D_l_t D_l_p D_l_n D_l_s C_l TLN.
      (* [comment removed for export] *)
      all: first [ lazymatch goal with
                   | |- context [al_t _] => clear D_f_p D_d_p C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_ptr_array _] => clear D_t_f D_t_d C_f C_d D_n_f D_s_f D_n_d D_s_d
                   | |- context [al_nodes _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_s_f D_s_d
                   | |- context [al_store _] => clear D_t_f D_t_d D_f_p D_d_p C_f C_d D_n_f D_n_d
                   | |- _ => clear D_t_f D_t_d D_f_p D_d_p D_n_f D_s_f D_n_d D_s_d
                   end; repeat (split; [fu_lia|]); fu_lia
                 | repeat (split; [fu_lia|]); fu_lia ].
    + intros c F n'. split; [intros H; cbn [In] in H; destruct H as [H|H]; [discriminate H| exact H]| intros H; cbn [In]; right; exact H].
Qed.
End Zd1.
#[using="HL CI_OK CI_OK2"] Theorem store_sec : ltac:(let t := eval cbv delta [store_sec__stmt] in store_sec__stmt in exact t).
Proof. exact store_sec__body. Qed.
End Store.
End CANSEC1.
End TwB.
End ASecStore.

(* [comment removed for export] *)
Module F_asecdealloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF ITreeA.   (* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_agbb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aflush OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aunmap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac footprint_after_store_with segs m a bs n Hn Ha Hl ::= footprint_after_store_with_d0 segs m a bs n Hn Ha Hl.   (* [comment removed for export] *)
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?AD (le8 ?v)) _) =>
      let E := lazymatch AD with wa ?E => E | Z_to_bv 64 ?E => E end in
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma rw_cells_hd1 : forall m A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app asegs m A [c] cs)) in H as [H _]. exact H. Qed.

Definition sdealloc_entry := 0x3650c.
(* [comment removed for export] *)
End CANSEC1.
Abbreviation SDEALLOC_STACK := 624.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition sdealloc_k {R} (k : astate -> AM R) (st : astate) : Z -> AM R :=
  fun r => let st1 := set_nsec (a_nsec st - 1) st in
           if r =? 0 then k st1 else if is_err r then aundef_ USpin (k st1) else aundef_ UBadAnswer (k st1).

#[using="Type"] Lemma large_dealloc_unfold : forall {R} (st : astate) mb ms (k : astate -> AM R),
  large_dealloc st mb ms k = poison0 mb ms (ev (AMunmap mb ms) (sdealloc_k k st)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sdealloc_tail_W (sp0 t mb ms : Z) : list (Z * Z) :=
  [(sp0 - 96, sp0); (t + 2800, t + 3168); (mb, mb + ms)]%Z.

Definition sdealloc_tail_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    (sp ra0 s0v s1v s2v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms ctx t lo : Z) (hsz hix : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 hix] ->
  ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) (zeros (shlen ms))] ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra0 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG mb 32 ->
  (* [comment removed for export] *)
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap mb ms) rsp RNG RNG' ->
      munch (sdealloc_tail_W (bv_unsigned sp) t mb ms) m m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
      (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat) ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra0 sp gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ev (AMunmap mb ms) (sdealloc_k k st))) (epostF Q)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 mb) (Z_to_bv 64 mb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ms) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x36600) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 2).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 5).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 6).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 7).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 8).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 9).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 10).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 11).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 12).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 13).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 14).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 15).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 16).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 17).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 18).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 19).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 20).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 21).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 22).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 39).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 40).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 41).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 42).
Variable t : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 44).
Variable hsz : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 45).
Variable hix : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 46).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 47).
#[using="Type"] Lemma sdealloc_tail_spec__body : ltac:(let T := type of (fun (h : sdealloc_tail_spec__stmt) => h RNG R k st Q sp ra0 s0v s1v s2v ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms ctx t lo hsz hix sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (st, (Q, (sp, (ra0, (s0v, (s1v, (s2v, (ra, (gp, (tp, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, (ctx, (t, (lo, (hsz, (hix, sj)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SPHI MI TP FR HDR MLO MPOS MAL MCE TI TK T88 TSD CT CX0 CX1 T0 T1 DMT DMC STATS LSJ
         PC PRM RR SHZ0 RA RIMG RTLS RSTK RCTX RT RMB KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post).   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  assert (MS4 : 4096 <= ms) by (clear -MPOS MAL; Z.div_mod_to_equations; lia).
  pose proof (munch_refl (sdealloc_tail_W (bv_unsigned sp) t mb ms) m) as MU. unfold sdealloc_tail_W in MU.
  box HDR. box STATS. box CT. box TSD.
  iprefix.
  step. step.                                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. eapply implF_evtS.
  { eapply (flush_spec RNG) with (mb := mb) (ms := ms) (lo := lo).
    all: lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- rw_cells _ _ (shad _) _ => exact SHZ0
         | |- _ mod 4096 = 0 => exact MAL
         | |- poison_cells _ => exact PC
         | |- premap_cells _ => exact PRM
         | |- arelro0 _ => exact RR
         | |- ablk _ _ => exact MLO   (* [comment removed for export] *)
         | |- @eq word _ _ => reflexivity
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -SPHI CEIL LO LO0 SPR; lia
         | |- _ => atop_facts; rewrite ?unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MPOS MCE RA; lia
         end. }
  cbv beta. intros ms' PO. unfold flush_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU1 WM1 MI1 ST1; nd_post).
  clear SHZ0. iprefix.
  rewrite !unsigned_lit in MU1, ST1 by (clear -SPHI CEIL LO LO0 SPR; lia).
  replace (ret_pc (Z_to_bv 64 222732)) with (Z_to_bv 64 222732 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport FR MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  xport TI MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). xport TK MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). xport T88 MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  carry TSD MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). carry CT MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR CX0 CX1; lia).
  carry STATS MU1 WM1 ltac:(rewrite LSJ; clear -SPHI CEIL LO LO0 SPR T0 T1; lia).
  carry HDR MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MCE MS4; lia).
  pose proof (poison_cells_frame _ _ _ PC MU1 WM1 ltac:(apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPHI CEIL LO LO0 SPR; lia | apply Forall_nil])) as PC1.
  pose proof (arelro0_munch _ _ _ RR MU1 ltac:(apply Forall_cons; [cbn; unfold ARELRO_LO, ARELRO_HI; clear -SPHI CEIL LO LO0 SPR; lia | apply Forall_nil])) as RR1.
  lazymatch type of MU1 with munch _ _ ?mm =>
    assert (MU1' : munch [(bv_unsigned sp - 96, bv_unsigned sp); (t + 2800, t + 3168); (mb, mb + ms)]%Z m mm) end.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia. }
  clear MU MU1 WM1 MI RR. rename MI1 into MI. rename MU1' into MU.
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  box HDR. box STATS. box CT. box TSD.
  eapply evtF_cut.
  { eapply (thread_stats_spec RNG ctx t lo).
    all: lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); exact ST1
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- rw_cells _ _ (_ + 152) _ => unboxed CT
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 _)] => first [eassumption | unboxed TSD]
         | |- rw_cells _ _ _ _ => eassumption
         | |- iclr _ _ => exact T0   (* [comment removed for export] *)
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ 4096 => exact RCTX
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -SPHI CEIL LO LO0 SPR; lia
         | |- _ => unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); clear -SPHI CEIL LO LO0 SPR CX0 CX1 T0 T1; lia
         end. }
  cbv beta. intros ms' PO. (nd_pre PO 3%nat; intros a1q mq ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MU0 WM0 MI0 ST0; nd_post).
  rewrite !unsigned_lit in MU0, ST0 by (clear -SPHI CEIL LO LO0 SPR; lia).
  replace (ret_pc (Z_to_bv 64 222736)) with (Z_to_bv 64 222736 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  clear ST1. try clear ST. rename ST0 into ST.
  carry STATS MU0 WM0 ltac:(rewrite LSJ; clear -SPHI CEIL LO LO0 SPR T0 T1; lia).
  carry HDR MU0 WM0 ltac:(clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MCE MS4; lia).
  xport FR MU0 WM0 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  lazymatch type of MU0 with munch _ _ ?mm =>
    assert (MU2 : munch [(bv_unsigned sp - 96, bv_unsigned sp); (t + 2800, t + 3168); (mb, mb + ms)]%Z m mm) end.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU0]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia. }
  clear MU MU0 WM0 MI. rename MI0 into MI. rename MU2 into MU.
  pose proof (rng_sub _ _ _ (t + 2800) 368 RT ltac:(clear; lia) ltac:(clear; lia)) as RSJ.
  aload STATS 12 (t + 2800 + 96).                              (* [comment removed for export] *)
  aload STATS 11 (t + 2800 + 88).                              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  astore STATS 11.                                             (* [comment removed for export] *)
  astore STATS 12.                                             (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 5 step.                                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. rewrite aembed_vis. cbn [aev_tree].
  eapply (unmap_or_die_spec RNG (fun z => aembed ATOP (sdealloc_k k st z)) Q) with (addr := mb) (size := ms) (lo := lo).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- @eq word _ _ => reflexivity
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ _ => exact RSTK
       | |- unmap_cells _ =>
           (* [comment removed for export] *)
           destruct PC as (G6 & _); (nd_pre PRM 4%nat; intros _ _ ML _; nd_post); apply rw_cells_hd1 in G6;
           split; (eapply cells_frameD; [eassumption | exact MU | cbn; unfold AIMG_HI in *; clear -SPHI CEIL LO LO0 SPR T0 MLO ML1 ML2 ML3; lia])
       | |- forall _, _ => idtac
       | |- _ => unfold AIMG_HI; clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MPOS MAL MCE RA; lia
       end.
  (* [comment removed for export] *)
  intros rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MUu MIu STu UCu.
  unfold sdealloc_k. rewrite Z.eqb_refl.
  eapply KONT; [exact HF | | exact MIu | exact STu |].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUu]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
  - eexists. split; [eapply u64arr_frameD; [exact STATS | exact MUu |] | rewrite !upd_length; exact LSJ].
    rewrite !upd_length, LSJ. cbn. clear -SPHI CEIL LO LO0 SPR T0 T1 DMT. lia.
Qed.
End Zd1.
#[using="Type"] Lemma sdealloc_tail_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    (sp ra0 s0v s1v s2v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms ctx t lo : Z) (hsz hix : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 hix] ->
  ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) (zeros (shlen ms))] ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra0 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG mb 32 ->
  (* [comment removed for export] *)
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap mb ms) rsp RNG RNG' ->
      munch (sdealloc_tail_W (bv_unsigned sp) t mb ms) m m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
      (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat) ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra0 sp gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ev (AMunmap mb ms) (sdealloc_k k st))) (epostF Q)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 mb) (Z_to_bv 64 mb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ms) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x36600) fc None m (seg_rom asegs)).
Proof. exact sdealloc_tail_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma nth_map_lit : forall (l : list Z) i x, nth_error l i = Some x -> nth i (map (Z_to_bv 64) l) (Z_to_bv 64 0) = Z_to_bv 64 x.
Proof.
  intros l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

#[using="Type"] Lemma c8x4_of_junk32 : forall m A, junk_at m A 32 -> exists w1 w2 w3 w4 : word, rw_cells asegs m A [C8 w1; C8 w2; C8 w3; C8 w4].
Proof.
  intros m A J. destruct (junk_split m A 16 16 J ltac:(lia) ltac:(lia)) as [J1 J2].
  (nd_pre (c8c8_of_junk m A J1) 3%nat; intros w1 w2 H1; nd_post). (nd_pre (c8c8_of_junk m (A + 16) J2) 3%nat; intros w3 w4 H2; nd_post).
  exists w1, w2, w3, w4. apply (proj2 (rw_cells_app asegs m A [C8 w1; C8 w2] [C8 w3; C8 w4])). split; [exact H1| exact H2].
Qed.

#[using="Type"] Lemma junk_of_cells' : forall m A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof. intros m A cs n H <-. apply junk_of_cells. exact H. Qed.

(* [comment removed for export] *)
Definition sdealloc_W (sp t mb ms PA idx last : Z) : list (Z * Z) :=
  [(sp - SDEALLOC_STACK, sp); (t + 2800, t + 3168);
   (0xab010, 0xab019); (0xab028, 0xab038); (0xab240, 0xab244); (0xab258, 0xab268);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)]%Z.

(* [comment removed for export] *)
Definition sdealloc_post (sp : word) (t mb ms PA nres nsec idx last lo : Z) (bases : list Z) (lw1 lw2 : word)
    (m m' : amem) : Prop :=
     munch (sdealloc_W (bv_unsigned sp) t mb ms PA idx last) m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nsec - 1))]
  /\ rw_cells asegs m' 0xab018 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab020 32
  /\ rw_cells asegs m' 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab258 16
  /\ u64arr asegs m' PA (upd (map (Z_to_bv 64) bases) (Z.to_nat idx) (Z_to_bv 64 last))
  /\ (idx <> nsec - 1 -> rw_cells asegs m' last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 idx)])
  /\ (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells asegs m' (shad mb) [CB (Z.to_nat (shlen ms)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen ms)))].

Definition sdealloc_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms idx PA nres nsec last ctx t lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt : byte) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SDEALLOC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xaafd8 -> a1 = Z_to_bv 64 0xab248 -> a2 = Z_to_bv 64 (mb + 4096) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xaafe0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 srt] -> junk_at m 0xab020 32 ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab258 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 sdealloc_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 2).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 38).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 39).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 40).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 41).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 42).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 43).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 44).
Variable last : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 45).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 46).
Variable t : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 47).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 48).
Variable bases : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 49).
Variable hsz : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 50).
Variable lw1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 51).
Variable lw2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 52).
Variable srt : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 53).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 54).
Variable shj : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 55).
#[using="Type"] Lemma sdealloc_spec__body : ltac:(let T := type of (fun (h : sdealloc_spec__stmt) => h RNG R k st Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms idx PA nres nsec last ctx t lo bases hsz lw1 lw2 srt sj shj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (st, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, (idx, (PA, (nres, (nsec, (last, (ctx, (t, (lo, (bases, (hsz, (lw1, (lw2, (srt, (sj, shj)))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO SPHI MI TP -> -> -> I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR MAL MLO MPOS MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT DML DPL RA
         RIMG RTLS RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ PA0) as ndP__; nd_pre ndP__ 4%nat; intros PL1 PL2 PL3 PL4; nd_post). (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post).   (* [comment removed for export] *) unfold AIMG_HI in PL1, ML1.
  pose proof PA0 as PBND; pose proof MLO as MBND; unfold ablk, AIMG_HI, KLS in PBND, MBND. unfold AIMG_HI in CXI.   (* [comment removed for export] *)
  pose proof CX0 as CBND; pose proof T0 as TBND; unfold sclr, KLS in CBND, TBND.   (* [comment removed for export] *)
  assert (ASD : mb + ms <= shad mb \/ shad mb + shlen ms + 8 <= mb) by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND MAL MSAL MCE MPOS; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold ATP88, ATSD, sdealloc_entry in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  assert (MS4 : 4096 <= ms) by (clear -MPOS MSAL; Z.div_mod_to_equations; lia).
  assert (LENm : length (map (Z_to_bv 64) bases) = Z.to_nat nsec) by (rewrite length_map; clear -LEN; lia).
  rewrite large_dealloc_unfold.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - SDEALLOC_STACK, bv_unsigned sp); (0xab010, 0xab019); (0xab028, 0xab038);
                          (0xab240, 0xab244); (0xab258, 0xab268); (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - SDEALLOC_STACK, bv_unsigned sp); (0xab010, 0xab019); (0xab028, 0xab038);
                          (0xab240, 0xab244); (PA + 8 * idx, PA + 8 * idx + 8)]%Z m) as MUb.
  (* [comment removed for export] *)
  box TI. box TK. box T88. box TSD. box CT. box STATS. box SH. box LHDR. box DMT. box DMC. box DMP. box DPT. box DPC. box DCT.
  (nd_pre (c8x4_of_junk32 _ _ JST) 5%nat; intros j0 j1 j2 j3 JS4; nd_post). clear JST.
  (nd_pre (c8c8_of_junk _ _ JGL) 3%nat; intros g0 g1 GL2; nd_post). clear JGL.
  iprefix.
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 0) ltac:(f_equal; change 4095 with (2^12 - 1); rewrite zb_land_mask_l by (clear; lia); change (2^12) with 4096; clear -MAL; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep. step.                                    (* [comment removed for export] *)
  apply (gbb_mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 700992) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 mb) ltac:(f_equal; clear; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (PA + 8 * idx)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -IDX; lia).
  pose proof (rng_sub _ _ _ (PA + 8 * idx) 8 RPA ltac:(clear -IDX NSR; lia) ltac:(clear -IDX NSR; lia)) as RDi.
  aload ARR idx (PA + 8 * idx).                                (* [comment removed for export] *)
  first [rewrite (nth_map_lit _ _ _ NTHI) | unfold w0; rewrite (nth_map_lit _ _ _ NTHI)].
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 IDX NSR PA0 PL1 PL2 PL3 PA1 NRB PBND. rewrite ?unsigned_lit in K2 by lia. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep.                                          (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -IDX; lia).
  step. step.                                                  (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  pose proof (rng_sub _ _ _ (PA + 8 * (nsec - 1)) 8 RPA ltac:(clear -IDX NSR; lia) ltac:(clear -IDX NSR; lia)) as RDl.
  aload ARR (nsec - 1) (PA + 8 * nsec + -8).                   (* [comment removed for export] *)
  first [rewrite (nth_map_lit _ _ _ NTHL) | unfold w0; rewrite (nth_map_lit _ _ _ NTHL)].
  zstep. zstep.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  box HDR. snapshot [(PA + 8 * idx, PA + 8 * idx + 8)]%Z MUa WMa.
  astore ARR idx.                                              (* [comment removed for export] *)
  carry HDR MUa WMa ltac:(ub DMP; clear -Y IDX NSR MS4; lia). clear MUa WMa.
  (* [comment removed for export] *)
  destruct (Z.eq_dec idx (nsec - 1)) as [EQI | NEI];
  [ (* [comment removed for export] *)
    clear MUb;
    assert (last = mb) as ELM by (rewrite <- EQI in NTHL; rewrite NTHI in NTHL; injection NTHL as E; symmetry; exact E);
    subst last;
    pose proof MLO as LLO; pose proof ML1 as LL1; pose proof MBND as LBND; assert (LCE : mb + 32 <= ATOP) by (clear -MCE MS4; lia);
    assert (LDL : tclr mb 32) by (eapply tclr_sub; [exact DML | clear; lia | clear -MS4; lia]);      (* [comment removed for export] *)   (* [comment removed for export] *)
    box ARR; snapshot [(mb + 24, mb + 32)]%Z MUl WMl;
    step;
    carry ARR MUl WMl ltac:(ub DMP; rewrite ?upd_length, LENm; clear -Y IDX NSR MS4; lia); clear MUl WMl
  | (* [comment removed for export] *)
    unbox LHDR; (nd_pre (LHDR NEI) 8%nat; intros LH LLO LCE LDM LDT LDC LDP LDL; nd_post); clear LHDR;
    (pose proof (ablk_lin _ _ LLO) as ndP__; nd_pre ndP__ 4%nat; intros LL1 _ _ _; nd_post); unfold AIMG_HI in LL1; pose proof LLO as LBND; unfold ablk, AIMG_HI, KLS in LBND;   (* [comment removed for export] *)
    pose proof (RLH NEI) as RLH';
    xport LH MUb WM ltac:(clear -LDP LLO LCE CEIL LO SPR IDX NSR LL1; lia); clear MUb;
    box ARR; box HDR; box LDM; box LDT; box LDC; box LDP;
    snapshot [(last + 24, last + 32)]%Z MUl WMl;
    step;
    carry ARR MUl WMl ltac:(ub LDP; rewrite ?upd_length, LENm; clear -Y IDX NSR; lia);
    carry HDR MUl WMl ltac:(ub LDM; clear -Y MS4; lia); clear MUl WMl ].
  (* [comment removed for export] *)
  all: assert (AMO1 : amo_aligned AD (Z_to_bv 64 0xab258) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO1.                                         (* [comment removed for export] *)
  all: step; zstep; zstep.                                     (* [comment removed for export] *)
  all: assert (AMO2 : amo_aligned AD (Z_to_bv 64 0xab260) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO2.                                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply (gbb_mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; step; step.                           (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  all: assert (SHR : 0x800b8600 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND ML1 ML2 ML3 MCE MS4; Z.div_mod_to_equations; lia).
  all: assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  all: assert (MSAL8 : ms mod 8 = 0) by (clear -MSAL; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport asegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR PA0 PL1 PL2 PL3 IDX MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB NSR; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia|]); apply Forall_nil)).
  (* [comment removed for export] *)
  all: eapply (poison0_spec R (ev (AMunmap mb ms) (sdealloc_k k st)) Q RNG) with (addr := mb) (size := ms) (lo := lo).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ _ => exact SH
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
       | |- forall _, _ => idtac
       | |- ablk _ _ => exact MLO   (* [comment removed for export] *)
       | |- _ => unfold PZR_STACK; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 MPOS MAL8 MSAL8 MCE; lia
       end.
  all: intros RNG1 mP t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PP.
  all: (nd_pre PP 9%nat; intros LE1 MUp WMp MI1 ST1 SHZ PC1 PRM1 RR1; nd_post); unfold PZR_STACK in MUp.
  all: rewrite !unsigned_lit in MUp, ST1 by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 222720)) with (Z_to_bv 64 222720 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: xport FR MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport HDR MUp WMp ltac:(clear -CEIL LO SPR SHR MLO ML1 ML2 ML3 MS4 MCE MBND ASD; lia).
  all: xport ARR MUp WMp ltac:(rewrite ?length_map; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 PA1 IDX NSR LEN PBND NRB; lia).
  all: xport NSC MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport SRT MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport JS4 MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport MTX MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport GL2 MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: try (xport LH MUp WMp ltac:(clear -CEIL LO SPR SHR LLO LCE LL1 LBND; lia)).
  (* [comment removed for export] *)
  all: lazymatch type of MU with munch ?Wc ?me ?mk => lazymatch type of MUp with munch ?Wp _ ?m1' =>
         assert (MU01 : munch (Wc ++ Wp) me m1') by (eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUp]];
            let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans asegs _ _ _ WM WMp) as WM01; cbn [app] in MU01 end end.
  all: carry TI MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry TK MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry T88 MU01 WM01 ltac:((nd_pre (tclr_int_lem _ _ LDL ltac:(clear -LL1; lia) ltac:(clear -LCE; atop_facts; lia)) 4%nat; intros kL KL1 KL2 KL3; nd_post);      (* [comment removed for export] *)
                                 (nd_pre (tclr_int_lem _ _ DPL ltac:(clear -PL1; lia) ltac:(clear -PA1; atop_facts; lia)) 4%nat; intros kP KP1 KP2 KP3; nd_post);
                                 clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB KL1 KL2 KL3 KP1 KP2 KP3; lia).
  all: carry TSD MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry CT MU01 WM01 ltac:(first [ub LDC | pose proof I as Y]; ub DPC; ub DMC; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO CX0 CX1 MS4 Y Y0 Y1 LL1 CXI PBND MBND ASD LBND NRB CBND; lia).
  all: carry STATS MU01 WM01 ltac:(rewrite LSJ; first [ub LDT | pose proof I as Y]; ub DPT; ub DMT; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO T0 T1 MS4 Y Y0 Y1 LL1 TIC PBND MBND ASD LBND NRB TBND; lia).
  (* [comment removed for export] *)
  all: pose proof (rng_fp_le _ _ _ _ LE1 RSTK) as RSTK1; pose proof (rng_fp_le _ _ _ _ LE1 RCTX) as RCTX1;
       pose proof (rng_fp_le _ _ _ _ LE1 RT) as RT1; pose proof (rng_fp_le _ _ _ _ LE1 RMB) as RMB1; pose proof (rng_fp_le _ _ _ _ LE1 RIMG) as RIMG1; pose proof (rng_fp_le _ _ _ _ LE1 RTLS) as RTLS1.
  (* [comment removed for export] *)
  all: eapply (sdealloc_tail_spec RNG1 k st Q sp ra s0 s1 s2) with (lo := lo) (ctx := ctx) (t := t) (sj := sj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST1
       | |- mem_inv _ _ => exact MI1
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact RR1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => first [exact FR | exact HDR]
       | |- rw_cells _ _ _ _ => assumption
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- rng_aimg _ => exact RIMG1
       | |- rng_atls _ => exact RTLS1
       | |- rng _ _ 4096 => first [exact RCTX1 | exact RT1]
       | |- rng _ _ 32 => eapply rng_sub'; [exact RMB1|]; clear -MS4; lia
       | |- rng _ _ _ => exact RSTK1
       | |- _ \/ _ => first [unboxed DMT | unboxed DMC]
       | |- forall _, _ => idtac
       | |- ablk _ _ => exact MLO | |- iclr _ _ => assumption   (* [comment removed for export] *)
       | |- _ => unfold AIMG_HI; clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 MPOS MSAL MCE CX0 CX1 T0 T1 RA CXI TIC CBND TBND; lia
       end.
  (* [comment removed for export] *)
  all: intros rsp RNG' m' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 HF MUu MIu STu SJu.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF |].
  all: unfold sdealloc_post, sdealloc_W, sdealloc_tail_W in *.
  all: split; [ eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_weaken; [| exact MUu]];
                let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia |].
  all: split; [exact MIu|]. all: split; [exact STu|].
  all: split; [eapply cells_frameD; [exact NSC | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply cells_frameD; [exact SRT | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply junk_frameD; [eapply junk_of_cells'; [exact JS4| reflexivity] | exact MUu | intros _; cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply cells_frameD; [exact MTX | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply junk_frameD; [eapply junk_of_cells'; [exact GL2| reflexivity] | exact MUu | intros _; cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply u64arr_frameD; [exact ARR | exact MUu | rewrite ?upd_length, ?length_map; cbn; ub DMP; ub DPT; clear -CEIL LO SPR PA0 PL1 PL2 PL3 PA1 IDX NSR LEN Y Y0 NRB PBND; lia]|].
  all: split; [first [ intros NE; exfalso; exact (NE EQI)
                     | intros _; eapply cells_frameD; [exact LH | exact MUu | cbn; ub LDM; ub LDT; clear -CEIL LO SPR LCE Y Y0; lia] ]|].
  all: split; [exact SJu|].
  all: eapply cells_frameD; [exact SHZ | exact MUu | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -CEIL LO SPR SHR MLO ML1 ML2 ML3 T0 TIC MBND ASD MS4 TBND; lia].
Qed.
End Zd2.
#[using="Type"] Lemma sdealloc_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms idx PA nres nsec last ctx t lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt : byte) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SDEALLOC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xaafd8 -> a1 = Z_to_bv 64 0xab248 -> a2 = Z_to_bv 64 (mb + 4096) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xaafe0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 srt] -> junk_at m 0xab020 32 ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab258 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 sdealloc_entry) fc None m (seg_rom asegs)).
Proof. exact sdealloc_spec__body. Qed.

End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ITreeA.   (* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_agbb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.F_memset.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoison_remap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aflush.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_aunmap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac footprint_after_store_with segs m a bs n Hn Ha Hl ::= footprint_after_store_with_d0 segs m a bs n Hn Ha Hl.   (* [comment removed for export] *)
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
(* [comment removed for export] *)
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?AD (le8 ?v)) _) =>
      let E := lazymatch AD with wa ?E => E | Z_to_bv 64 ?E => E end in
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma rw_cells_hd1 : forall m A c cs, rw_cells asegs m A (c :: cs) -> rw_cells asegs m A [c].
Proof. intros m A c cs H. apply (proj1 (rw_cells_app asegs m A [c] cs)) in H as [H _]. exact H. Qed.

Definition sdealloc_entry := 0x36574.
(* [comment removed for export] *)
End CANSEC1.
Abbreviation SDEALLOC_STACK := 624.

(* [comment removed for export] *)
Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition sdealloc_k {R} (k : astate -> AM R) (st : astate) : Z -> AM R :=
  fun r => let st1 := set_nsec (a_nsec st - 1) st in
           if r =? 0 then k st1 else if is_err r then aundef_ USpin (k st1) else aundef_ UBadAnswer (k st1).

#[using="Type"] Lemma large_dealloc_unfold : forall {R} (st : astate) mb ms (k : astate -> AM R),
  large_dealloc st mb ms k = poison0 mb ms (ev (AMunmap mb ms) (sdealloc_k k st)).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sdealloc_tail_W (sp0 t mb ms : Z) : list (Z * Z) :=
  [(sp0 - 96, sp0); (t + 2800, t + 3168); (mb, mb + ms)]%Z.

Definition sdealloc_tail_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    (sp ra0 s0v s1v s2v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms ctx t lo : Z) (hsz hix : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 hix] ->
  ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) (zeros (shlen ms))] ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra0 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG mb 32 ->
  (* [comment removed for export] *)
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap mb ms) rsp RNG RNG' ->
      munch (sdealloc_tail_W (bv_unsigned sp) t mb ms) m m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
      (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat) ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra0 sp gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ev (AMunmap mb ms) (sdealloc_k k st))) (epostF Q)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 mb) (Z_to_bv 64 mb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ms) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x36668) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 2).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 4).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 5).
Variable ra0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 6).
Variable s0v : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 7).
Variable s1v : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 8).
Variable s2v : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 9).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 10).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 11).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 12).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 13).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 14).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 15).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 16).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 17).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 18).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 19).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 20).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 21).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 22).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 23).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 24).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 25).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 26).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 27).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 28).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 29).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 30).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 31).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 32).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 33).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 34).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 35).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 36).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 37).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 38).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 39).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 40).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 41).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 42).
Variable t : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 43).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 44).
Variable hsz : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 45).
Variable hix : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 46).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'sdealloc_tail_spec__stmt 47).
#[using="Type"] Lemma sdealloc_tail_spec__body : ltac:(let T := type of (fun (h : sdealloc_tail_spec__stmt) => h RNG R k st Q sp ra0 s0v s1v s2v ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms ctx t lo hsz hix sj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (st, (Q, (sp, (ra0, (s0v, (s1v, (s2v, (ra, (gp, (tp, (t0, (t1, (t2, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, (ctx, (t, (lo, (hsz, (hix, sj)))))))))))))))))))))))))))))))))))))))))))))))) as _.
 intros ST CEIL LO SPHI MI TP FR HDR MLO MPOS MAL MCE TI TK T88 TSD CT CX0 CX1 T0 T1 DMT DMC STATS LSJ
         PC PRM RR SHZ0 RA RIMG RTLS RSTK RCTX RT RMB KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post).   (* [comment removed for export] *)
  unfold AIMG_HI, ATP88, ATSD in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  assert (MS4 : 4096 <= ms) by (clear -MPOS MAL; Z.div_mod_to_equations; lia).
  pose proof (munch_refl (sdealloc_tail_W (bv_unsigned sp) t mb ms) m) as MU. unfold sdealloc_tail_W in MU.
  box HDR. box STATS. box CT. box TSD.
  iprefix.
  step. step.                                                  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. eapply implF_evtS.
  { eapply (flush_spec RNG) with (mb := mb) (ms := ms) (lo := lo).
    all: lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- rw_cells _ _ (shad _) _ => exact SHZ0
         | |- _ mod 4096 = 0 => exact MAL
         | |- poison_cells _ => exact PC
         | |- premap_cells _ => exact PRM
         | |- arelro0 _ => exact RR
         | |- ablk _ _ => exact MLO   (* [comment removed for export] *)
         | |- @eq word _ _ => reflexivity
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -SPHI CEIL LO LO0 SPR; lia
         | |- _ => atop_facts; rewrite ?unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MPOS MCE RA; lia
         end. }
  cbv beta. intros ms' PO. unfold flush_post in PO. destruct_exs PO. (destruct PO as (-> & ndR1__); nd_pre ndR1__ 4%nat; intros MU1 WM1 MI1 ST1; nd_post).
  clear SHZ0. iprefix.
  rewrite !unsigned_lit in MU1, ST1 by (clear -SPHI CEIL LO LO0 SPR; lia).
  replace (ret_pc (Z_to_bv 64 222836)) with (Z_to_bv 64 222836 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  (* [comment removed for export] *)
  xport FR MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  xport TI MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). xport TK MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). xport T88 MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  carry TSD MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR; lia). carry CT MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR CX0 CX1; lia).
  carry STATS MU1 WM1 ltac:(rewrite LSJ; clear -SPHI CEIL LO LO0 SPR T0 T1; lia).
  carry HDR MU1 WM1 ltac:(clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MCE MS4; lia).
  pose proof (poison_cells_frame _ _ _ PC MU1 WM1 ltac:(apply Forall_cons; [cbn; unfold AIMG_HI; clear -SPHI CEIL LO LO0 SPR; lia | apply Forall_nil])) as PC1.
  pose proof (arelro0_munch _ _ _ RR MU1 ltac:(apply Forall_cons; [cbn; unfold ARELRO_LO, ARELRO_HI; clear -SPHI CEIL LO LO0 SPR; lia | apply Forall_nil])) as RR1.
  lazymatch type of MU1 with munch _ _ ?mm =>
    assert (MU1' : munch [(bv_unsigned sp - 96, bv_unsigned sp); (t + 2800, t + 3168); (mb, mb + ms)]%Z m mm) end.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU1]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia. }
  clear MU MU1 WM1 MI RR. rename MI1 into MI. rename MU1' into MU.
  (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  box HDR. box STATS. box CT. box TSD.
  eapply evtF_cut.
  { eapply (thread_stats_spec RNG ctx t lo).
    all: lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); exact ST1
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- rw_cells _ _ (_ + 152) _ => unboxed CT
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 _)] => first [eassumption | unboxed TSD]
         | |- rw_cells _ _ _ _ => eassumption
         | |- iclr _ _ => exact T0   (* [comment removed for export] *)
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ 4096 => exact RCTX
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -SPHI CEIL LO LO0 SPR; lia
         | |- _ => unfold AIMG_HI; rewrite ?unsigned_lit by (clear -SPHI CEIL LO LO0 SPR; lia); clear -SPHI CEIL LO LO0 SPR CX0 CX1 T0 T1; lia
         end. }
  cbv beta. intros ms' PO. (nd_pre PO 3%nat; intros a1q mq ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MU0 WM0 MI0 ST0; nd_post).
  rewrite !unsigned_lit in MU0, ST0 by (clear -SPHI CEIL LO LO0 SPR; lia).
  replace (ret_pc (Z_to_bv 64 222840)) with (Z_to_bv 64 222840 : word) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
  clear ST1. try clear ST. rename ST0 into ST.
  carry STATS MU0 WM0 ltac:(rewrite LSJ; clear -SPHI CEIL LO LO0 SPR T0 T1; lia).
  carry HDR MU0 WM0 ltac:(clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MCE MS4; lia).
  xport FR MU0 WM0 ltac:(clear -SPHI CEIL LO LO0 SPR; lia).
  lazymatch type of MU0 with munch _ _ ?mm =>
    assert (MU2 : munch [(bv_unsigned sp - 96, bv_unsigned sp); (t + 2800, t + 3168); (mb, mb + ms)]%Z m mm) end.
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU0]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia. }
  clear MU MU0 WM0 MI. rename MI0 into MI. rename MU2 into MU.
  pose proof (rng_sub _ _ _ (t + 2800) 368 RT ltac:(clear; lia) ltac:(clear; lia)) as RSJ.
  aload STATS 12 (t + 2800 + 96).                              (* [comment removed for export] *)
  aload STATS 11 (t + 2800 + 88).                              (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  astore STATS 11.                                             (* [comment removed for export] *)
  astore STATS 12.                                             (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  do 5 step.                                                   (* [comment removed for export] *)
  release_frame FR ST (bv_unsigned sp).
  step.                                                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply evtF_done. rewrite aembed_vis. cbn [aev_tree].
  eapply (unmap_or_die_spec RNG (fun z => aembed ATOP (sdealloc_k k st z)) Q) with (addr := mb) (size := ms) (lo := lo).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- @eq word _ _ => reflexivity
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ _ => exact RSTK
       | |- unmap_cells _ =>
           (* [comment removed for export] *)
           destruct PC as (G6 & _); (nd_pre PRM 4%nat; intros _ _ ML _; nd_post); apply rw_cells_hd1 in G6;
           split; (eapply cells_frameD; [eassumption | exact MU | cbn; unfold AIMG_HI in *; clear -SPHI CEIL LO LO0 SPR T0 MLO ML1 ML2 ML3; lia])
       | |- forall _, _ => idtac
       | |- _ => unfold AIMG_HI; clear -SPHI CEIL LO LO0 SPR MLO ML1 ML2 ML3 MPOS MAL MCE RA; lia
       end.
  (* [comment removed for export] *)
  intros rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' HF MUu MIu STu UCu.
  unfold sdealloc_k. rewrite Z.eqb_refl.
  eapply KONT; [exact HF | | exact MIu | exact STu |].
  - eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MUu]. let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
  - eexists. split; [eapply u64arr_frameD; [exact STATS | exact MUu |] | rewrite !upd_length; exact LSJ].
    rewrite !upd_length, LSJ. cbn. clear -SPHI CEIL LO LO0 SPR T0 T1 DMT. lia.
Qed.
End Zd1.
#[using="Type"] Lemma sdealloc_tail_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    (sp ra0 s0v s1v s2v : word)
    ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms ctx t lo : Z) (hsz hix : word) (sj : list word),
  stk asegs m lo (bv_unsigned sp + -32) -> ATOP <= lo -> lo <= bv_unsigned sp - 96 -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  (* [comment removed for export] *)
  rw_cells asegs m (bv_unsigned sp + -32) [C8 s2v; C8 s1v; C8 s0v; C8 ra0] ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 hix] ->
  ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  0 < ctx -> ctx + 4096 <= ATOP -> iclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) (zeros (shlen ms))] ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra0 ->
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG mb 32 ->
  (* [comment removed for export] *)
  (forall rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fstepS (NMunmap mb ms) rsp RNG RNG' ->
      munch (sdealloc_tail_W (bv_unsigned sp) t mb ms) m m' -> mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) ->
      (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat) ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra0 sp gp tp t0' t1' t2' s0v s1v a0' a1' a2' a3' a4' a5' a6' a7' s2v s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra0) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (ev (AMunmap mb ms) (sdealloc_k k st))) (epostF Q)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 mb) (Z_to_bv 64 mb) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 ms) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x36668) fc None m (seg_rom asegs)).
Proof. exact sdealloc_tail_spec__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma nth_map_lit : forall (l : list Z) i x, nth_error l i = Some x -> nth i (map (Z_to_bv 64) l) (Z_to_bv 64 0) = Z_to_bv 64 x.
Proof.
  intros l. induction l as [|y l IH]; intros [|i] x H; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

#[using="Type"] Lemma c8x4_of_junk32 : forall m A, junk_at m A 32 -> exists w1 w2 w3 w4 : word, rw_cells asegs m A [C8 w1; C8 w2; C8 w3; C8 w4].
Proof.
  intros m A J. destruct (junk_split m A 16 16 J ltac:(lia) ltac:(lia)) as [J1 J2].
  (nd_pre (c8c8_of_junk m A J1) 3%nat; intros w1 w2 H1; nd_post). (nd_pre (c8c8_of_junk m (A + 16) J2) 3%nat; intros w3 w4 H2; nd_post).
  exists w1, w2, w3, w4. apply (proj2 (rw_cells_app asegs m A [C8 w1; C8 w2] [C8 w3; C8 w4])). split; [exact H1| exact H2].
Qed.

#[using="Type"] Lemma junk_of_cells' : forall m A cs n, rw_cells asegs m A cs -> Z.of_nat (cells_size cs) = n -> junk_at m A n.
Proof. intros m A cs n H <-. apply junk_of_cells. exact H. Qed.

(* [comment removed for export] *)
Definition sdealloc_W (sp t mb ms PA idx last : Z) : list (Z * Z) :=
  [(sp - SDEALLOC_STACK, sp); (t + 2800, t + 3168);
   (0xab410, 0xab419); (0xab428, 0xab438); (0xab640, 0xab644); (0xab658, 0xab668);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)]%Z.

(* [comment removed for export] *)
Definition sdealloc_post (sp : word) (t mb ms PA nres nsec idx last lo : Z) (bases : list Z) (lw1 lw2 : word)
    (m m' : amem) : Prop :=
     munch (sdealloc_W (bv_unsigned sp) t mb ms PA idx last) m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nsec - 1))]
  /\ rw_cells asegs m' 0xab418 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab420 32
  /\ rw_cells asegs m' 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab658 16
  /\ u64arr asegs m' PA (upd (map (Z_to_bv 64) bases) (Z.to_nat idx) (Z_to_bv 64 last))
  /\ (idx <> nsec - 1 -> rw_cells asegs m' last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 idx)])
  /\ (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells asegs m' (shad mb) [CB (Z.to_nat (shlen ms)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen ms)))].

Definition sdealloc_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms idx PA nres nsec last ctx t lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt : byte) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SDEALLOC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xab3d8 -> a1 = Z_to_bv 64 0xab648 -> a2 = Z_to_bv 64 (mb + 4096) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xab3e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 srt] -> junk_at m 0xab420 32 ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab658 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 sdealloc_entry) fc None m (seg_rom asegs)).
Section Zd2.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 2).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 38).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 39).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 40).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 41).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 42).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 43).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 44).
Variable last : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 45).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 46).
Variable t : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 47).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 48).
Variable bases : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 49).
Variable hsz : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 50).
Variable lw1 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 51).
Variable lw2 : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 52).
Variable srt : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 53).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 54).
Variable shj : ltac2:(SecDietF.SzSecF.ty 'sdealloc_spec__stmt 55).
#[using="Type"] Lemma sdealloc_spec__body : ltac:(let T := type of (fun (h : sdealloc_spec__stmt) => h RNG R k st Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms idx PA nres nsec last ctx t lo bases hsz lw1 lw2 srt sj shj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (st, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, (idx, (PA, (nres, (nsec, (last, (ctx, (t, (lo, (bases, (hsz, (lw1, (lw2, (srt, (sj, shj)))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO SPHI MI TP -> -> -> I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR MAL MLO MPOS MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT DML DPL RA
         RIMG RTLS RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ PA0) as ndP__; nd_pre ndP__ 4%nat; intros PL1 PL2 PL3 PL4; nd_post). (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post).   (* [comment removed for export] *) unfold AIMG_HI in PL1, ML1.
  pose proof PA0 as PBND; pose proof MLO as MBND; unfold ablk, AIMG_HI, KLS in PBND, MBND. unfold AIMG_HI in CXI.   (* [comment removed for export] *)
  pose proof CX0 as CBND; pose proof T0 as TBND; unfold sclr, KLS in CBND, TBND.   (* [comment removed for export] *)
  assert (ASD : mb + ms <= shad mb \/ shad mb + shlen ms + 8 <= mb) by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND MAL MSAL MCE MPOS; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
  unfold ATP88, ATSD, sdealloc_entry in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  assert (MS4 : 4096 <= ms) by (clear -MPOS MSAL; Z.div_mod_to_equations; lia).
  assert (LENm : length (map (Z_to_bv 64) bases) = Z.to_nat nsec) by (rewrite length_map; clear -LEN; lia).
  rewrite large_dealloc_unfold.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - SDEALLOC_STACK, bv_unsigned sp); (0xab410, 0xab419); (0xab428, 0xab438);
                          (0xab640, 0xab644); (0xab658, 0xab668); (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  pose proof (munch_refl [(bv_unsigned sp - SDEALLOC_STACK, bv_unsigned sp); (0xab410, 0xab419); (0xab428, 0xab438);
                          (0xab640, 0xab644); (PA + 8 * idx, PA + 8 * idx + 8)]%Z m) as MUb.
  (* [comment removed for export] *)
  box TI. box TK. box T88. box TSD. box CT. box STATS. box SH. box LHDR. box DMT. box DMC. box DMP. box DPT. box DPC. box DCT.
  (nd_pre (c8x4_of_junk32 _ _ JST) 5%nat; intros j0 j1 j2 j3 JS4; nd_post). clear JST.
  (nd_pre (c8c8_of_junk _ _ JGL) 3%nat; intros g0 g1 GL2; nd_post). clear JGL.
  iprefix.
  carve_frame 32%nat ST.
  do 5 step.                                                   (* [comment removed for export] *)
  step. zstep. zstep.                                          (* [comment removed for export] *)
  setreg 13 (Z_to_bv 64 0) ltac:(f_equal; change 4095 with (2^12 - 1); rewrite zb_land_mask_l by (clear; lia); change (2^12) with 4096; clear -MAL; Z.div_mod_to_equations; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep. step.                                    (* [comment removed for export] *)
  apply (gbb_mtx_to_C4 _ 0 ltac:(clear; lia)) in MTX.
  assert (AMO : amo_aligned AW (Z_to_bv 64 702016) = true) by (apply amo_alignedW_intro; [clear; lia| reflexivity]).
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. zstep. zstep. zstep.                                   (* [comment removed for export] *)
  amo_stepA AMO.                                               (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 8 (Z_to_bv 64 mb) ltac:(f_equal; clear; lia).
  step. if_lit.                                                (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  setreg 12 (Z_to_bv 64 (PA + 8 * idx)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -IDX; lia).
  pose proof (rng_sub _ _ _ (PA + 8 * idx) 8 RPA ltac:(clear -IDX NSR; lia) ltac:(clear -IDX NSR; lia)) as RDi.
  aload ARR idx (PA + 8 * idx).                                (* [comment removed for export] *)
  first [rewrite (nth_map_lit _ _ _ NTHI) | unfold w0; rewrite (nth_map_lit _ _ _ NTHI)].
  step. if_cases K1; zify_cond K1. { exfalso. clear -K1. rewrite ?unsigned_lit in K1 by lia. lia. }   (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. if_cases K2; zify_cond K2. { exfalso. clear -K2 IDX NSR PA0 PL1 PL2 PL3 PA1 NRB PBND. rewrite ?unsigned_lit in K2 by lia. lia. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  zstep. step. zstep.                                          (* [comment removed for export] *)
  setreg 15 (Z_to_bv 64 (PA + 8 * nsec)) ltac:(f_equal; rewrite ?Z.shiftl_mul_pow2 by (clear; lia); clear -IDX; lia).
  step. step.                                                  (* [comment removed for export] *)
  zstep.                                                       (* [comment removed for export] *)
  pose proof (rng_sub _ _ _ (PA + 8 * (nsec - 1)) 8 RPA ltac:(clear -IDX NSR; lia) ltac:(clear -IDX NSR; lia)) as RDl.
  aload ARR (nsec - 1) (PA + 8 * nsec + -8).                   (* [comment removed for export] *)
  first [rewrite (nth_map_lit _ _ _ NTHL) | unfold w0; rewrite (nth_map_lit _ _ _ NTHL)].
  zstep. zstep.                                                (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  zstep. zstep.                                                (* [comment removed for export] *)
  box HDR. snapshot [(PA + 8 * idx, PA + 8 * idx + 8)]%Z MUa WMa.
  astore ARR idx.                                              (* [comment removed for export] *)
  carry HDR MUa WMa ltac:(ub DMP; clear -Y IDX NSR MS4; lia). clear MUa WMa.
  (* [comment removed for export] *)
  destruct (Z.eq_dec idx (nsec - 1)) as [EQI | NEI];
  [ (* [comment removed for export] *)
    clear MUb;
    assert (last = mb) as ELM by (rewrite <- EQI in NTHL; rewrite NTHI in NTHL; injection NTHL as E; symmetry; exact E);
    subst last;
    pose proof MLO as LLO; pose proof ML1 as LL1; pose proof MBND as LBND; assert (LCE : mb + 32 <= ATOP) by (clear -MCE MS4; lia);
    assert (LDL : tclr mb 32) by (eapply tclr_sub; [exact DML | clear; lia | clear -MS4; lia]);      (* [comment removed for export] *)   (* [comment removed for export] *)
    box ARR; snapshot [(mb + 24, mb + 32)]%Z MUl WMl;
    step;
    carry ARR MUl WMl ltac:(ub DMP; rewrite ?upd_length, LENm; clear -Y IDX NSR MS4; lia); clear MUl WMl
  | (* [comment removed for export] *)
    unbox LHDR; (nd_pre (LHDR NEI) 8%nat; intros LH LLO LCE LDM LDT LDC LDP LDL; nd_post); clear LHDR;
    (pose proof (ablk_lin _ _ LLO) as ndP__; nd_pre ndP__ 4%nat; intros LL1 _ _ _; nd_post); unfold AIMG_HI in LL1; pose proof LLO as LBND; unfold ablk, AIMG_HI, KLS in LBND;   (* [comment removed for export] *)
    pose proof (RLH NEI) as RLH';
    xport LH MUb WM ltac:(clear -LDP LLO LCE CEIL LO SPR IDX NSR LL1; lia); clear MUb;
    box ARR; box HDR; box LDM; box LDT; box LDC; box LDP;
    snapshot [(last + 24, last + 32)]%Z MUl WMl;
    step;
    carry ARR MUl WMl ltac:(ub LDP; rewrite ?upd_length, LENm; clear -Y IDX NSR; lia);
    carry HDR MUl WMl ltac:(ub LDM; clear -Y MS4; lia); clear MUl WMl ].
  (* [comment removed for export] *)
  all: assert (AMO1 : amo_aligned AD (Z_to_bv 64 0xab658) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO1.                                         (* [comment removed for export] *)
  all: step; zstep; zstep.                                     (* [comment removed for export] *)
  all: assert (AMO2 : amo_aligned AD (Z_to_bv 64 0xab660) = true) by (apply amo_alignedD_intro; [clear; lia| reflexivity]).
  all: amo_stepA AMO2.                                         (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply (gbb_mtx_of_C4 _ 1 ltac:(clear; lia)) in MTX.
  all: step.                                                   (* [comment removed for export] *)
  all: step; step; step; step; step.                           (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  all: assert (SHR : 0x800b8800 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND ML1 ML2 ML3 MCE MS4; Z.div_mod_to_equations; lia).
  all: assert (MAL8 : mb mod 8 = 0) by (clear -MAL; Z.div_mod_to_equations; lia).
  all: assert (MSAL8 : ms mod 8 = 0) by (clear -MSAL; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport asegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR PA0 PL1 PL2 PL3 IDX MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB NSR; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 NRB PBND; lia|]); apply Forall_nil)).
  (* [comment removed for export] *)
  all: eapply (poison0_spec R (ev (AMunmap mb ms) (sdealloc_k k st)) Q RNG) with (addr := mb) (size := ms) (lo := lo).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => reflexivity
       | |- rw_cells _ _ _ _ => exact SH
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
       | |- forall _, _ => idtac
       | |- ablk _ _ => exact MLO   (* [comment removed for export] *)
       | |- _ => unfold PZR_STACK; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 MPOS MAL8 MSAL8 MCE; lia
       end.
  all: intros RNG1 mP t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' PP.
  all: (nd_pre PP 9%nat; intros LE1 MUp WMp MI1 ST1 SHZ PC1 PRM1 RR1; nd_post); unfold PZR_STACK in MUp.
  all: rewrite !unsigned_lit in MUp, ST1 by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 222824)) with (Z_to_bv 64 222824 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: xport FR MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport HDR MUp WMp ltac:(clear -CEIL LO SPR SHR MLO ML1 ML2 ML3 MS4 MCE MBND ASD; lia).
  all: xport ARR MUp WMp ltac:(rewrite ?length_map; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 PA1 IDX NSR LEN PBND NRB; lia).
  all: xport NSC MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport SRT MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport JS4 MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport MTX MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: xport GL2 MUp WMp ltac:(clear -CEIL LO SPR SHR; lia).
  all: try (xport LH MUp WMp ltac:(clear -CEIL LO SPR SHR LLO LCE LL1 LBND; lia)).
  (* [comment removed for export] *)
  all: lazymatch type of MU with munch ?Wc ?me ?mk => lazymatch type of MUp with munch ?Wp _ ?m1' =>
         assert (MU01 : munch (Wc ++ Wp) me m1') by (eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUp]];
            let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans asegs _ _ _ WM WMp) as WM01; cbn [app] in MU01 end end.
  all: carry TI MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry TK MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry T88 MU01 WM01 ltac:((nd_pre (tclr_int_lem _ _ LDL ltac:(clear -LL1; lia) ltac:(clear -LCE; atop_facts; lia)) 4%nat; intros kL KL1 KL2 KL3; nd_post);      (* [comment removed for export] *)
                                 (nd_pre (tclr_int_lem _ _ DPL ltac:(clear -PL1; lia) ltac:(clear -PA1; atop_facts; lia)) 4%nat; intros kP KP1 KP2 KP3; nd_post);
                                 clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB KL1 KL2 KL3 KP1 KP2 KP3; lia).
  all: carry TSD MU01 WM01 ltac:(clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO LL1 PBND MBND ASD LBND MS4 NRB; lia).
  all: carry CT MU01 WM01 ltac:(first [ub LDC | pose proof I as Y]; ub DPC; ub DMC; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO CX0 CX1 MS4 Y Y0 Y1 LL1 CXI PBND MBND ASD LBND NRB CBND; lia).
  all: carry STATS MU01 WM01 ltac:(rewrite LSJ; first [ub LDT | pose proof I as Y]; ub DPT; ub DMT; clear -CEIL LO SPR SHR PA0 PL1 PL2 PL3 IDX NSR MLO ML1 ML2 ML3 LLO T0 T1 MS4 Y Y0 Y1 LL1 TIC PBND MBND ASD LBND NRB TBND; lia).
  (* [comment removed for export] *)
  all: pose proof (rng_fp_le _ _ _ _ LE1 RSTK) as RSTK1; pose proof (rng_fp_le _ _ _ _ LE1 RCTX) as RCTX1;
       pose proof (rng_fp_le _ _ _ _ LE1 RT) as RT1; pose proof (rng_fp_le _ _ _ _ LE1 RMB) as RMB1; pose proof (rng_fp_le _ _ _ _ LE1 RIMG) as RIMG1; pose proof (rng_fp_le _ _ _ _ LE1 RTLS) as RTLS1.
  (* [comment removed for export] *)
  all: eapply (sdealloc_tail_spec RNG1 k st Q sp ra s0 s1 s2) with (lo := lo) (ctx := ctx) (t := t) (sj := sj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST1
       | |- mem_inv _ _ => exact MI1
       | |- poison_cells _ => exact PC1
       | |- premap_cells _ => exact PRM1
       | |- arelro0 _ => exact RR1
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => first [exact FR | exact HDR]
       | |- rw_cells _ _ _ _ => assumption
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- rng_aimg _ => exact RIMG1
       | |- rng_atls _ => exact RTLS1
       | |- rng _ _ 4096 => first [exact RCTX1 | exact RT1]
       | |- rng _ _ 32 => eapply rng_sub'; [exact RMB1|]; clear -MS4; lia
       | |- rng _ _ _ => exact RSTK1
       | |- _ \/ _ => first [unboxed DMT | unboxed DMC]
       | |- forall _, _ => idtac
       | |- ablk _ _ => exact MLO | |- iclr _ _ => assumption   (* [comment removed for export] *)
       | |- _ => unfold AIMG_HI; clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 MPOS MSAL MCE CX0 CX1 T0 T1 RA CXI TIC CBND TBND; lia
       end.
  (* [comment removed for export] *)
  all: intros rsp RNG' m' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 HF MUu MIu STu SJu.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF |].
  all: unfold sdealloc_post, sdealloc_W, sdealloc_tail_W in *.
  all: split; [ eapply munch_trans; [eapply munch_weaken; [| exact MU01] | eapply munch_weaken; [| exact MUu]];
                let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia |].
  all: split; [exact MIu|]. all: split; [exact STu|].
  all: split; [eapply cells_frameD; [exact NSC | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply cells_frameD; [exact SRT | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply junk_frameD; [eapply junk_of_cells'; [exact JS4| reflexivity] | exact MUu | intros _; cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply cells_frameD; [exact MTX | exact MUu | cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply junk_frameD; [eapply junk_of_cells'; [exact GL2| reflexivity] | exact MUu | intros _; cbn; clear -CEIL LO SPR MLO ML1 ML2 ML3 T0 TIC TBND; lia]|].
  all: split; [eapply u64arr_frameD; [exact ARR | exact MUu | rewrite ?upd_length, ?length_map; cbn; ub DMP; ub DPT; clear -CEIL LO SPR PA0 PL1 PL2 PL3 PA1 IDX NSR LEN Y Y0 NRB PBND; lia]|].
  all: split; [first [ intros NE; exfalso; exact (NE EQI)
                     | intros _; eapply cells_frameD; [exact LH | exact MUu | cbn; ub LDM; ub LDT; clear -CEIL LO SPR LCE Y Y0; lia] ]|].
  all: split; [exact SJu|].
  all: eapply cells_frameD; [exact SHZ | exact MUu | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -CEIL LO SPR SHR MLO ML1 ML2 ML3 T0 TIC MBND ASD MS4 TBND; lia].
Qed.
End Zd2.
#[using="Type"] Lemma sdealloc_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms idx PA nres nsec last ctx t lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt : byte) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SDEALLOC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xab3d8 -> a1 = Z_to_bv 64 0xab648 -> a2 = Z_to_bv 64 (mb + 4096) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xab3e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 srt] -> junk_at m 0xab420 32 ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab658 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 0 < ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 sdealloc_entry) fc None m (seg_rom asegs)).
Proof. exact sdealloc_spec__body. Qed.

End CANSEC2.
End TwB.
End F_asecdealloc.

(* [comment removed for export] *)
Module F_arecsec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_agbb OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_asecdealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?AD (le8 ?v)) _) =>
      let E := lazymatch AD with wa ?E => E | Z_to_bv 64 ?E => E end in
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Abbreviation SREC2_STACK := 624.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition recycle_sec_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB CBA lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC2_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + 6128) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xaafe0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 srt] -> junk_at m 0xab020 32 ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab258 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x35f40) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 2).
Variable st : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 38).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 39).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 41).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 43).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 45).
Variable last : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 46).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 47).
Variable t : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 48).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 49).
Variable CBA : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 50).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 51).
Variable bases : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 52).
Variable hsz : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 53).
Variable lw1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 54).
Variable lw2 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 55).
Variable srt : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 56).
Variable hst : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 57).
Variable hb1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 58).
Variable hctx : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 59).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 60).
Variable shj : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 61).
#[using="Type"] Lemma recycle_sec_spec__body : ltac:(let T := type of (fun (h : recycle_sec_spec__stmt) => h RNG R k st Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms n idx PA nres nsec last ctx t SB CBA lo bases hsz lw1 lw2 srt hst hb1 hctx sj shj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (st, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, (n, (idx, (PA, (nres, (nsec, (last, (ctx, (t, (SB, (CBA, (lo, (bases, (hsz, (lw1, (lw2, (srt, (hst, (hb1, (hctx, (sj, shj)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO SPHI MI TP -> -> ISB DSP SB0 I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR ACH NR BR MAL MLO MS8K MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT DML DPL RA
         RIMG RTLS RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ PA0) as ndP__; nd_pre ndP__ 4%nat; intros PL1 PL2 PL3 PL4; nd_post). (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in PL1, ML1, CXI.   (* [comment removed for export] *)
  pose proof MLO as MBND; unfold ablk, AIMG_HI, KLS in MBND. pose proof T0 as TBND; unfold sclr, KLS in TBND.   (* [comment removed for export] *)
  unfold ATP88, ATSD, K_SPACE_SIZE, K_SPACE_EXTRA in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xab240, 0xab244); (t + 2800, t + 3168)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xab240, 0xab244)]%Z m) as MUs.   (* [comment removed for export] *)
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box I64. box I72. box NSC. box SRT. box JST. box JGL. box TI. box TK. box T88. box TSD. box CT. box STATS. box ARR. box HDR. box SH. box LHDR. box ACH.
  box DMT. box DMC. box DMP. box DPT. box DPC. box DCT.
  rewrite large_dealloc_unfold. iprefix.
  carve_frame 48%nat ST.
  do 7 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct DSP as [DLO | DHI];
  [ step; if_cases K1; zify_cond K1; [ | exfalso; clear -K1 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K1 by lia; lia ]
  | step; if_cases K1; zify_cond K1;
    [ exfalso; clear -K1 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K1 by lia; lia
    | zstep; step; if_cases K2; zify_cond K2; [ | exfalso; clear -K2 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K2 by lia; lia ] ] ].
  all: zstep; step.                                            (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: pose proof I64 as I64o; pose proof I72 as I72o; pose proof NSC as NSCo; pose proof ARR as ARRo; pose proof HDR as HDRo.
  all: carry I64 MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry I72 MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry NSC MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry ARR MU WM ltac:(rewrite ?length_map; ub DPT; clear -CEIL LO SPR T0 PA0 PA1 LEN NSR Y PL1 PL2 PL3 TIC; lia).
  all: carry HDR MU WM ltac:(ub DMT; clear -CEIL LO SPR T0 MLO MCE MS8K Y ML1 ML2 ML3 TIC; lia).
  all: eapply evtF_cut;
       [ eapply (sec_gbb_spec RNG) with (p := mb + 6128) (PA := PA) (nres := nres) (nsec := nsec) (mb := mb) (ms := ms) (lo := lo) (bases := bases);
         lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR
         | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSC
         | |- rw_cells _ _ _ _ => assumption
         | |- u64arr _ _ _ _ => exact ARR
         | |- Forall _ _ => exact BR
         | |- In _ _ => eapply nth_error_In; exact NTHI
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ (8 * _) => eapply rng_sub'; [exact RPA|]; clear -IDX NSR; lia
         | |- rng _ _ 32 => eapply rng_sub'; [exact RMB|]; clear -MS8K; lia
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
         | |- ablk _ _ => first [exact MLO | eapply ablk_sub; [exact PA0 | clear; lia | clear -IDX NSR NRB; lia]]   (* [comment removed for export] *)
         | |- _ => atop_facts; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI LEN IDX NSR PA0 PA1 MAL MLO MS8K MCE RA ML1 ML2 ML3 PL1 PL2 PL3; lia
         end
       | ].
  all: cbv beta; intros ms' PO; unfold gbb_post in PO; destruct_exs PO; (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUg WMg MIg STg MTXg; nd_post).
  all: rewrite !unsigned_lit in MUg, STg by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 221112)) with (Z_to_bv 64 221112 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: xport FR MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport ISB MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport I64 MUg WMg ltac:(clear -CEIL LO SPR; lia). all: xport I72 MUg WMg ltac:(clear -CEIL LO SPR; lia). all: xport NSC MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport ARR MUg WMg ltac:(rewrite ?length_map; clear -CEIL LO SPR PA0 PA1 LEN NSR PL1 PL2 PL3; lia).
  all: xport HDR MUg WMg ltac:(clear -CEIL LO SPR MLO MCE MS8K ML1 ML2 ML3; lia).
  all: clear MTX; rename MTXg into MTX.
  all: lazymatch type of MU with munch ?W0 ?me ?ma => lazymatch type of MUg with munch _ _ ?mb' =>
         assert (MU2 : munch W0 me mb') by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUg];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans asegs _ _ _ WM WMg) as WM2 end end.
  all: lazymatch type of MUs with munch ?W0 ?me ?ma => lazymatch type of MUg with munch _ _ ?mb' =>
         assert (MUs2 : munch W0 me mb') by (eapply munch_trans; [exact MUs|]; eapply munch_weaken; [| exact MUg];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia) end end.
  all: clear MU MUs WM MUg WMg MI ST; rename MU2 into MU; rename MUs2 into MUs; rename WM2 into WM; rename MIg into MI; rename STg into ST.
  (* [comment removed for export] *)
  all: step; step; zstep.                                      (* [comment removed for export] *)
  1: step; if_cases K3; zify_cond K3; [ exfalso; clear -K3 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K3 by lia; lia | step ].
  2: step; if_cases K3; zify_cond K3; [ | exfalso; clear -K3 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K3 by lia; lia ];
     step; if_cases K4; zify_cond K4; [ | exfalso; clear -K4 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K4 by lia; lia ].
  (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: clear I64 I72 NSC ARR HDR.
  all: eapply evtF_cut;
       [ eapply (thread_stats_spec RNG ctx t lo);
         lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- rw_cells _ _ (_ + 152) _ => carry CT MU WM ltac:(ub DCT; clear -CEIL LO SPR CX0 CX1 Y CXI; lia); exact CT
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 _)] => first [carry T88 MU WM ltac:(clear -CEIL LO SPR T0 TIC T1; lia); exact T88 | carry TSD MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TSD]
         | |- rw_cells _ _ _ [C1 _] => carry TI MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TI
         | |- rw_cells _ _ _ [C4 _] => carry TK MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TK
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ 4096 => exact RCTX
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
         | |- iclr _ _ => assumption   (* [comment removed for export] *)
         | |- _ => unfold AIMG_HI; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR CX0 CX1 T0 T1 TIC CXI; lia
         end
       | ].
  all: cbv beta; intros ms' PO; (nd_pre PO 3%nat; intros a1q mq ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MUt WMt MIt STt; nd_post).
  all: rewrite !unsigned_lit in MUt, STt by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 221360)) with (Z_to_bv 64 221360 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: lazymatch type of MU with munch ?W0 ?me ?ma => lazymatch type of MUt with munch _ _ ?mb' =>
         assert (MU2 : munch W0 me mb') by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUt];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans asegs _ _ _ WM WMt) as WM2 end end.
  all: lazymatch type of MUs with munch ?W0 ?me ?ma => lazymatch type of MUt with munch _ _ ?mb' =>
         assert (MUs2 : munch W0 me mb') by (eapply munch_trans; [exact MUs|]; eapply munch_weaken; [| exact MUt];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia) end end.
  all: xport FR MUt WMt ltac:(clear -CEIL LO SPR; lia). all: xport MTX MUt WMt ltac:(clear -CEIL LO SPR; lia). all: xport ISB MUt WMt ltac:(clear -CEIL LO SPR; lia).
  all: clear MU MUs WM MUt WMt MI ST; rename MU2 into MU; rename MUs2 into MUs; rename WM2 into WM; rename MIt into MI; rename STt into ST.
  all: carry STATS MUs WM ltac:(rewrite LSJ; clear -CEIL LO SPR T0 T1 TIC; lia). all: clear MUs.
  all: carry ACH MU WM ltac:(ub DMT; clear -CEIL LO SPR MLO MCE MS8K T0 Y ML1 ML2 ML3 TIC; lia).
  all: pose proof (rng_sub _ _ _ (t + 2800) 368 RT ltac:(clear; lia) ltac:(clear; lia)) as RSJ.
  all: step; step; clear ACH.                                  (* [comment removed for export] *)
  all: aload STATS 6 (t + 2800 + 48).                          (* [comment removed for export] *)
  all: aload STATS 5 (t + 2800 + 40).                          (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep.                             (* [comment removed for export] *)
  all: astore STATS 5.                                         (* [comment removed for export] *)
  all: astore STATS 6.                                         (* [comment removed for export] *)
  all: step; if_cases K5; zify_cond K5; [ exfalso; clear -K5 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K5 by lia; lia | ].   (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  1: step; if_cases K6; zify_cond K6; [ | exfalso; clear -K6 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K6 by lia; lia ].
  2: step; if_cases K6; zify_cond K6; [ exfalso; clear -K6 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K6 by lia; lia | ];
     zstep; step; if_cases K7; zify_cond K7; [ | exfalso; clear -K7 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K7 by lia; lia ].
  (* [comment removed for export] *)
  all: zstep; zstep; step.                                     (* [comment removed for export] *)
  all: do 7 step.                                              (* [comment removed for export] *)
  all: release_frame FR ST (bv_unsigned sp).
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  (* [comment removed for export] *)
  all: carry I64o MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry I72o MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry NSCo MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry SRT MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: unbox JST; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JST; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR T0 TIC; lia] end.
  all: unbox JGL; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JGL; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR T0 TIC; lia] end.
  all: carry TI MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry TK MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry T88 MU WM ltac:(clear -CEIL LO SPR T0 TIC T1; lia); carry TSD MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry CT MU WM ltac:(ub DCT; clear -CEIL LO SPR CX0 CX1 T0 Y TIC CXI; lia).
  all: carry ARRo MU WM ltac:(rewrite ?length_map; ub DPT; clear -CEIL LO SPR T0 PA0 PA1 LEN NSR Y PL1 PL2 PL3 TIC; lia).
  all: carry HDRo MU WM ltac:(ub DMT; clear -CEIL LO SPR T0 MLO MCE MS8K Y ML1 ML2 ML3 TIC; lia).
  all: assert (SHR : 0x800b8600 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND MCE MS8K ML1 ML2 ML3; Z.div_mod_to_equations; lia).
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport asegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR T0 TIC TBND; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR T0 TIC; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR T0 TIC; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR T0 TIC; lia|]); apply Forall_nil)).
  all: unbox LHDR.
  all: lazymatch goal with |- implF _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mk _) =>
         assert (LHDRk : idx <> nsec - 1 ->
            rw_cells asegs mk last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
            /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
            /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
            /\ tclr last 32)
         by (intros NE; (nd_pre (LHDR NE) 8%nat; intros LH L1 L2 L3 L4 L5 L6 L7; nd_post); (pose proof (ablk_lin _ _ L1) as ndP__; nd_pre ndP__ 4%nat; intros LL1 LL2 LL3 LL4; nd_post); unfold AIMG_HI in LL1;   (* [comment removed for export] *)
             split; [| split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| split; [exact L6| exact L7]]]]]]];
             eapply cells_frame; [exact LH | exact MU | exact WM | cbn; clear -CEIL LO SPR T0 L1 L2 L4 TIC LL1; lia]) end.
  all: clear LHDR.
  all: eapply (sdealloc_spec RNG k st Q) with (mb := mb) (ms := ms) (idx := idx) (PA := PA) (nres := nres) (nsec := nsec) (last := last)
         (ctx := ctx) (t := t) (lo := lo) (bases := bases) (lw1 := lw1) (lw2 := lw2).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDRo
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSCo
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ _ _ => first [eassumption | exact SRT]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- u64arr _ _ _ (map _ _) => exact ARRo
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => rewrite !upd_length; exact LSJ
       | |- @eq (option Z) _ _ => assumption
       | |- @eq Z _ _ => assumption
       | |- tclr _ _ => assumption      (* [comment removed for export] *)
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ 4096 => assumption
       | |- rng _ _ (8 * _) => exact RPA
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ (_ - _) => exact RSTK
       | |- rng _ _ _ => exact RMB
       | |- _ -> rng _ _ _ => exact RLH
       | |- _ -> _ /\ _ => exact LHDRk
       | |- _ \/ _ => first [unboxed DMT | unboxed DMC | unboxed DMP | unboxed DPT | unboxed DPC | unboxed DCT]
       | |- forall _, _ => idtac
       | |- ablk _ _ => assumption | |- iclr _ _ => assumption   (* [comment removed for export] *)
       | |- _ => try assumption; atop_facts; clear -CEIL LO LO0 SPR SPHI MLO MS8K MSAL MCE CX0 CX1 T0 T1 PA0 PA1 IDX NSR LEN RA MAL NR CXI TIC NRB ML1 ML2 ML3 PL1 PL2 PL3; lia
       end.
  (* [comment removed for export] *)
  all: intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF |].
  all: destruct PP as (MUd & REST); split; [| exact REST].
  all: eapply munch_trans; [eapply munch_weaken; [| exact MU] | exact MUd].
  all: unfold sdealloc_W; let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
Qed.
End Zd1.
#[using="Type"] Lemma recycle_sec_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB CBA lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC2_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + 6128) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xaafe0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 srt] -> junk_at m 0xab020 32 ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab258 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x35f40) fc None m (seg_rom asegs)).
Proof. exact recycle_sec_spec__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_agbb.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_asecdealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mem_after_store ::= mem_after_store_fast.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.
Local Ltac aload ST8 i AEXPR :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let RD := fresh "RD" in
    pose proof (u64arr_read asegs mm A ws i (nth (Z.to_nat i) ws w0) (wa AEXPR) ST8
                  ltac:(apply nth_error_nth'; rewrite ?upd_length; lia) ltac:(lia) ltac:(f_equal; lia)) as RD;
    step; clear RD
  end.
Local Ltac astore ST8 i :=
  lazymatch type of ST8 with u64arr _ ?mm ?A ?ws =>
    let SOK := fresh "SOK" in
    pose proof (u64arr_store_ok asegs mm A ws i (wa (A + 8 * i)) ST8 ltac:(rewrite ?upd_length; lia) eq_refl) as SOK;
    step;
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ (write_to_mem _ ?AD (le8 ?v)) _) =>
      let E := lazymatch AD with wa ?E => E | Z_to_bv 64 ?E => E end in
      let S2 := fresh "STATS" in
      pose proof (u64arr_write asegs mm A ws i v ST8 ltac:(rewrite ?upd_length; lia)) as S2;
      replace (A + 8 * i)%Z with E in S2 by lia;
      clear ST8; store_done; try clear SOK; rename S2 into ST8
    end
  end.

(* [comment removed for export] *)
Abbreviation SREC2_STACK := 624.

(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition recycle_sec_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB CBA lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC2_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + 6128) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xab3e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 srt] -> junk_at m 0xab420 32 ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab658 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x35fa8) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 2).
Variable st : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 38).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 39).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 41).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 43).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 45).
Variable last : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 46).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 47).
Variable t : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 48).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 49).
Variable CBA : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 50).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 51).
Variable bases : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 52).
Variable hsz : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 53).
Variable lw1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 54).
Variable lw2 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 55).
Variable srt : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 56).
Variable hst : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 57).
Variable hb1 : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 58).
Variable hctx : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 59).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 60).
Variable shj : ltac2:(SecDietF.SzSecF.ty 'recycle_sec_spec__stmt 61).
#[using="Type"] Lemma recycle_sec_spec__body : ltac:(let T := type of (fun (h : recycle_sec_spec__stmt) => h RNG R k st Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms n idx PA nres nsec last ctx t SB CBA lo bases hsz lw1 lw2 srt hst hb1 hctx sj shj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (st, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, (n, (idx, (PA, (nres, (nsec, (last, (ctx, (t, (SB, (CBA, (lo, (bases, (hsz, (lw1, (lw2, (srt, (hst, (hb1, (hctx, (sj, shj)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO SPHI MI TP -> -> ISB DSP SB0 I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR ACH NR BR MAL MLO MS8K MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT DML DPL RA
         RIMG RTLS RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ PA0) as ndP__; nd_pre ndP__ 4%nat; intros PL1 PL2 PL3 PL4; nd_post). (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in PL1, ML1, CXI.   (* [comment removed for export] *)
  pose proof MLO as MBND; unfold ablk, AIMG_HI, KLS in MBND. pose proof T0 as TBND; unfold sclr, KLS in TBND.   (* [comment removed for export] *)
  unfold ATP88, ATSD, K_SPACE_SIZE, K_SPACE_EXTRA in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xab640, 0xab644); (t + 2800, t + 3168)]%Z m) as MU.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp); (0xab640, 0xab644)]%Z m) as MUs.   (* [comment removed for export] *)
  pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box I64. box I72. box NSC. box SRT. box JST. box JGL. box TI. box TK. box T88. box TSD. box CT. box STATS. box ARR. box HDR. box SH. box LHDR. box ACH.
  box DMT. box DMC. box DMP. box DPT. box DPC. box DCT.
  rewrite large_dealloc_unfold. iprefix.
  carve_frame 48%nat ST.
  do 7 step.                                                   (* [comment removed for export] *)
  step. step.                                                  (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  step.                                                        (* [comment removed for export] *)
  step. zstep.                                                 (* [comment removed for export] *)
  (* [comment removed for export] *)
  destruct DSP as [DLO | DHI];
  [ step; if_cases K1; zify_cond K1; [ | exfalso; clear -K1 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K1 by lia; lia ]
  | step; if_cases K1; zify_cond K1;
    [ exfalso; clear -K1 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K1 by lia; lia
    | zstep; step; if_cases K2; zify_cond K2; [ | exfalso; clear -K2 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K2 by lia; lia ] ] ].
  all: zstep; step.                                            (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: pose proof I64 as I64o; pose proof I72 as I72o; pose proof NSC as NSCo; pose proof ARR as ARRo; pose proof HDR as HDRo.
  all: carry I64 MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry I72 MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry NSC MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry ARR MU WM ltac:(rewrite ?length_map; ub DPT; clear -CEIL LO SPR T0 PA0 PA1 LEN NSR Y PL1 PL2 PL3 TIC; lia).
  all: carry HDR MU WM ltac:(ub DMT; clear -CEIL LO SPR T0 MLO MCE MS8K Y ML1 ML2 ML3 TIC; lia).
  all: eapply evtF_cut;
       [ eapply (sec_gbb_spec RNG) with (p := mb + 6128) (PA := PA) (nres := nres) (nsec := nsec) (mb := mb) (ms := ms) (lo := lo) (bases := bases);
         lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => reflexivity
         | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR
         | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSC
         | |- rw_cells _ _ _ _ => assumption
         | |- u64arr _ _ _ _ => exact ARR
         | |- Forall _ _ => exact BR
         | |- In _ _ => eapply nth_error_In; exact NTHI
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ (8 * _) => eapply rng_sub'; [exact RPA|]; clear -IDX NSR; lia
         | |- rng _ _ 32 => eapply rng_sub'; [exact RMB|]; clear -MS8K; lia
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
         | |- ablk _ _ => first [exact MLO | eapply ablk_sub; [exact PA0 | clear; lia | clear -IDX NSR NRB; lia]]   (* [comment removed for export] *)
         | |- _ => atop_facts; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI LEN IDX NSR PA0 PA1 MAL MLO MS8K MCE RA ML1 ML2 ML3 PL1 PL2 PL3; lia
         end
       | ].
  all: cbv beta; intros ms' PO; unfold gbb_post in PO; destruct_exs PO; (destruct PO as (-> & ndR1__); nd_pre ndR1__ 5%nat; intros MUg WMg MIg STg MTXg; nd_post).
  all: rewrite !unsigned_lit in MUg, STg by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 221216)) with (Z_to_bv 64 221216 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: xport FR MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport ISB MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport I64 MUg WMg ltac:(clear -CEIL LO SPR; lia). all: xport I72 MUg WMg ltac:(clear -CEIL LO SPR; lia). all: xport NSC MUg WMg ltac:(clear -CEIL LO SPR; lia).
  all: xport ARR MUg WMg ltac:(rewrite ?length_map; clear -CEIL LO SPR PA0 PA1 LEN NSR PL1 PL2 PL3; lia).
  all: xport HDR MUg WMg ltac:(clear -CEIL LO SPR MLO MCE MS8K ML1 ML2 ML3; lia).
  all: clear MTX; rename MTXg into MTX.
  all: lazymatch type of MU with munch ?W0 ?me ?ma => lazymatch type of MUg with munch _ _ ?mb' =>
         assert (MU2 : munch W0 me mb') by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUg];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans asegs _ _ _ WM WMg) as WM2 end end.
  all: lazymatch type of MUs with munch ?W0 ?me ?ma => lazymatch type of MUg with munch _ _ ?mb' =>
         assert (MUs2 : munch W0 me mb') by (eapply munch_trans; [exact MUs|]; eapply munch_weaken; [| exact MUg];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia) end end.
  all: clear MU MUs WM MUg WMg MI ST; rename MU2 into MU; rename MUs2 into MUs; rename WM2 into WM; rename MIg into MI; rename STg into ST.
  (* [comment removed for export] *)
  all: step; step; zstep.                                      (* [comment removed for export] *)
  1: step; if_cases K3; zify_cond K3; [ exfalso; clear -K3 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K3 by lia; lia | step ].
  2: step; if_cases K3; zify_cond K3; [ | exfalso; clear -K3 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K3 by lia; lia ];
     step; if_cases K4; zify_cond K4; [ | exfalso; clear -K4 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K4 by lia; lia ].
  (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: clear I64 I72 NSC ARR HDR.
  all: eapply evtF_cut;
       [ eapply (thread_stats_spec RNG ctx t lo);
         lazymatch goal with
         | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
         | |- mem_inv _ _ => exact MI
         | |- @eq word _ _ => first [reflexivity | exact TP]
         | |- rw_cells _ _ (_ + 152) _ => carry CT MU WM ltac:(ub DCT; clear -CEIL LO SPR CX0 CX1 Y CXI; lia); exact CT
         | |- rw_cells _ _ _ [C8 (Z_to_bv 64 _)] => first [carry T88 MU WM ltac:(clear -CEIL LO SPR T0 TIC T1; lia); exact T88 | carry TSD MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TSD]
         | |- rw_cells _ _ _ [C1 _] => carry TI MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TI
         | |- rw_cells _ _ _ [C4 _] => carry TK MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); exact TK
         | |- rng_aimg _ => exact RIMG
         | |- rng_atls _ => exact RTLS
         | |- rng _ _ 4096 => exact RCTX
         | |- rng _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
         | |- iclr _ _ => assumption   (* [comment removed for export] *)
         | |- _ => unfold AIMG_HI; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR CX0 CX1 T0 T1 TIC CXI; lia
         end
       | ].
  all: cbv beta; intros ms' PO; (nd_pre PO 3%nat; intros a1q mq ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); nd_pre ndR2__ 4%nat; intros MUt WMt MIt STt; nd_post).
  all: rewrite !unsigned_lit in MUt, STt by (clear -CEIL LO LO0 SPR; lia).
  all: replace (ret_pc (Z_to_bv 64 221464)) with (Z_to_bv 64 221464 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  all: lazymatch type of MU with munch ?W0 ?me ?ma => lazymatch type of MUt with munch _ _ ?mb' =>
         assert (MU2 : munch W0 me mb') by (eapply munch_trans; [exact MU|]; eapply munch_weaken; [| exact MUt];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia);
         pose proof (wmono_trans asegs _ _ _ WM WMt) as WM2 end end.
  all: lazymatch type of MUs with munch ?W0 ?me ?ma => lazymatch type of MUt with munch _ _ ?mb' =>
         assert (MUs2 : munch W0 me mb') by (eapply munch_trans; [exact MUs|]; eapply munch_weaken; [| exact MUt];
           let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia) end end.
  all: xport FR MUt WMt ltac:(clear -CEIL LO SPR; lia). all: xport MTX MUt WMt ltac:(clear -CEIL LO SPR; lia). all: xport ISB MUt WMt ltac:(clear -CEIL LO SPR; lia).
  all: clear MU MUs WM MUt WMt MI ST; rename MU2 into MU; rename MUs2 into MUs; rename WM2 into WM; rename MIt into MI; rename STt into ST.
  all: carry STATS MUs WM ltac:(rewrite LSJ; clear -CEIL LO SPR T0 T1 TIC; lia). all: clear MUs.
  all: carry ACH MU WM ltac:(ub DMT; clear -CEIL LO SPR MLO MCE MS8K T0 Y ML1 ML2 ML3 TIC; lia).
  all: pose proof (rng_sub _ _ _ (t + 2800) 368 RT ltac:(clear; lia) ltac:(clear; lia)) as RSJ.
  all: step; step; clear ACH.                                  (* [comment removed for export] *)
  all: aload STATS 6 (t + 2800 + 48).                          (* [comment removed for export] *)
  all: aload STATS 5 (t + 2800 + 40).                          (* [comment removed for export] *)
  all: zstep; zstep; zstep; zstep.                             (* [comment removed for export] *)
  all: astore STATS 5.                                         (* [comment removed for export] *)
  all: astore STATS 6.                                         (* [comment removed for export] *)
  all: step; if_cases K5; zify_cond K5; [ exfalso; clear -K5 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K5 by lia; lia | ].   (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  1: step; if_cases K6; zify_cond K6; [ | exfalso; clear -K6 DLO MS8K SB0 MLO ML1 ML2 ML3; rewrite ?Z.mod_small in K6 by lia; lia ].
  2: step; if_cases K6; zify_cond K6; [ exfalso; clear -K6 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K6 by lia; lia | ];
     zstep; step; if_cases K7; zify_cond K7; [ | exfalso; clear -K7 DHI SB0 MLO MCE ML1 ML2 ML3; rewrite ?Z.mod_small in K7 by lia; lia ].
  (* [comment removed for export] *)
  all: zstep; zstep; step.                                     (* [comment removed for export] *)
  all: do 7 step.                                              (* [comment removed for export] *)
  all: release_frame FR ST (bv_unsigned sp).
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  (* [comment removed for export] *)
  all: carry I64o MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry I72o MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry NSCo MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry SRT MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: unbox JST; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JST; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR T0 TIC; lia] end.
  all: unbox JGL; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JGL; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR T0 TIC; lia] end.
  all: carry TI MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry TK MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia); carry T88 MU WM ltac:(clear -CEIL LO SPR T0 TIC T1; lia); carry TSD MU WM ltac:(clear -CEIL LO SPR T0 TIC; lia).
  all: carry CT MU WM ltac:(ub DCT; clear -CEIL LO SPR CX0 CX1 T0 Y TIC CXI; lia).
  all: carry ARRo MU WM ltac:(rewrite ?length_map; ub DPT; clear -CEIL LO SPR T0 PA0 PA1 LEN NSR Y PL1 PL2 PL3 TIC; lia).
  all: carry HDRo MU WM ltac:(ub DMT; clear -CEIL LO SPR T0 MLO MCE MS8K Y ML1 ML2 ML3 TIC; lia).
  all: assert (SHR : 0x800b8800 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MBND MCE MS8K ML1 ML2 ML3; Z.div_mod_to_equations; lia).
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport asegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR T0 TIC TBND; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR T0 TIC; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR T0 TIC; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR T0 TIC; lia|]); apply Forall_nil)).
  all: unbox LHDR.
  all: lazymatch goal with |- implF _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mk _) =>
         assert (LHDRk : idx <> nsec - 1 ->
            rw_cells asegs mk last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
            /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
            /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
            /\ tclr last 32)
         by (intros NE; (nd_pre (LHDR NE) 8%nat; intros LH L1 L2 L3 L4 L5 L6 L7; nd_post); (pose proof (ablk_lin _ _ L1) as ndP__; nd_pre ndP__ 4%nat; intros LL1 LL2 LL3 LL4; nd_post); unfold AIMG_HI in LL1;   (* [comment removed for export] *)
             split; [| split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| split; [exact L6| exact L7]]]]]]];
             eapply cells_frame; [exact LH | exact MU | exact WM | cbn; clear -CEIL LO SPR T0 L1 L2 L4 TIC LL1; lia]) end.
  all: clear LHDR.
  all: eapply (sdealloc_spec RNG k st Q) with (mb := mb) (ms := ms) (idx := idx) (PA := PA) (nres := nres) (nsec := nsec) (last := last)
         (ctx := ctx) (t := t) (lo := lo) (bases := bases) (lw1 := lw1) (lw2 := lw2).
  all: lazymatch goal with
       | |- stk _ _ _ _ => exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDRo
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSCo
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ _ _ => first [eassumption | exact SRT]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- u64arr _ _ _ (map _ _) => exact ARRo
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => rewrite !upd_length; exact LSJ
       | |- @eq (option Z) _ _ => assumption
       | |- @eq Z _ _ => assumption
       | |- tclr _ _ => assumption      (* [comment removed for export] *)
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ 4096 => assumption
       | |- rng _ _ (8 * _) => exact RPA
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ (_ - _) => exact RSTK
       | |- rng _ _ _ => exact RMB
       | |- _ -> rng _ _ _ => exact RLH
       | |- _ -> _ /\ _ => exact LHDRk
       | |- _ \/ _ => first [unboxed DMT | unboxed DMC | unboxed DMP | unboxed DPT | unboxed DPC | unboxed DCT]
       | |- forall _, _ => idtac
       | |- ablk _ _ => assumption | |- iclr _ _ => assumption   (* [comment removed for export] *)
       | |- _ => try assumption; atop_facts; clear -CEIL LO LO0 SPR SPHI MLO MS8K MSAL MCE CX0 CX1 T0 T1 PA0 PA1 IDX NSR LEN RA MAL NR CXI TIC NRB ML1 ML2 ML3 PL1 PL2 PL3; lia
       end.
  (* [comment removed for export] *)
  all: intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1 b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF |].
  all: destruct PP as (MUd & REST); split; [| exact REST].
  all: eapply munch_trans; [eapply munch_weaken; [| exact MU] | exact MUd].
  all: unfold sdealloc_W; let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
Qed.
End Zd1.
#[using="Type"] Lemma recycle_sec_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB CBA lo : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - SREC2_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (mb + 6128) ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xab3e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 srt] -> junk_at m 0xab420 32 ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab658 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      sdealloc_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x35fa8) fc None m (seg_rom asegs)).
Proof. exact recycle_sec_spec__body. Qed.
End CANSEC1.
End TwB.
End F_arecsec.

(* [comment removed for export] *)
Module F_aputrec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require Import InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import MM_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import SysStepF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ADepot_iface__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKit2. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_agbb__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_aalloc3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_asecdealloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_arecsec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6303744 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : ABase.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6303744 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Abbreviation PUTREC_STACK := 704.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition putrec_W (sp t mb ms PA idx last : Z) : list (Z * Z) :=
  [(sp - PUTREC_STACK, sp); (t + 2800, t + 3168);
   (0xab010, 0xab019); (0xab028, 0xab038); (0xab240, 0xab244); (0xab258, 0xab268);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)]%Z.

Definition putrec_post (sp : word) (t mb ms PA nres nsec idx last lo : Z) (bases : list Z) (lw1 lw2 : word)
    (m m' : amem) : Prop :=
     munch (putrec_W (bv_unsigned sp) t mb ms PA idx last) m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nsec - 1))]
  /\ rw_cells asegs m' 0xab018 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab020 32
  /\ rw_cells asegs m' 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab258 16
  /\ u64arr asegs m' PA (upd (map (Z_to_bv 64) bases) (Z.to_nat idx) (Z_to_bv 64 last))
  /\ (idx <> nsec - 1 -> rw_cells asegs m' last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 idx)])
  /\ (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells asegs m' (shad mb) [CB (Z.to_nat (shlen ms)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen ms)))].

Definition put_passthru_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB lo nb fst0 lst qb : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PUTREC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xab270 -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 (mb + 6128) -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] -> Q_MAX < n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] -> 0 <= qb <= Q_CACHE ->
  (last + 32 <= t \/ t + 4096 <= last) -> last + 32 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xaafe0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 srt] -> junk_at m 0xab020 32 ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab258 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      putrec_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37ff4) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 2).
Variable st : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 38).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 39).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 41).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 43).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 45).
Variable last : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 46).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 47).
Variable t : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 48).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 49).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 50).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 51).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 52).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 53).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 54).
Variable bases : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 55).
Variable hsz : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 56).
Variable lw1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 57).
Variable lw2 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 58).
Variable srt : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 59).
Variable hst : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 60).
Variable hb1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 61).
Variable hctx : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 62).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 63).
Variable shj : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 64).
#[using="Type"] Lemma put_passthru_spec__body : ltac:(let T := type of (fun (h : put_passthru_spec__stmt) => h RNG R k st Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms n idx PA nres nsec last ctx t SB lo nb fst0 lst qb bases hsz lw1 lw2 srt hst hb1 hctx sj shj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (st, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, (n, (idx, (PA, (nres, (nsec, (last, (ctx, (t, (SB, (lo, (nb, (fst0, (lst, (qb, (bases, (hsz, (lw1, (lw2, (srt, (hst, (hb1, (hctx, (sj, shj))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO SPHI MI TP -> -> -> -> QCELL NBIG TC QBLE LDT0 LCE0 ISB DSP SB0 I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR ACH NR BR MAL MLO MS8K MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT DML DPL RA
         RIMG RTLS RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. band_int T0. band_int CX0. band_int MLO.   (* [comment removed for export] *)
  unfold ATP88, ATSD, K_SPACE_SIZE, K_SPACE_EXTRA in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box ISB. box I64. box I72. box NSC. box SRT. box JST. box MTX. box JGL. box TI. box TK. box T88. box TSD. box CT. box STATS. box ARR. box HDR. box ACH. box SH.
  box LHDR. box TC. box QCELL. box DMT. box DMC. box DMP. box DPT. box DPC. box DCT. box LDT0.
  rewrite large_dealloc_unfold at 1 || idtac.
  iprefix.
  carve_frame 80%nat ST.
  do 9 step.                                                   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  carry QCELL MU WM ltac:(clear -CEIL LO SPR; lia).
  step. step.                                                  (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1.                       (* [comment removed for export] *)
  { exfalso. unfold Q_MAX in *. clear -K1 NBIG NR. rewrite ?Z.mod_small in K1 by lia. lia. }
  carry ISB MU WM ltac:(clear -CEIL LO SPR; lia).
  step. step.                                                  (* [comment removed for export] *)
  destruct DSP as [DLO | DHI];
  [ step; if_cases K2; zify_cond K2; [ | exfalso; clear -K2 DLO MS8K SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO; rewrite ?Z.mod_small in K2 by lia; lia ]
  | step; if_cases K2; zify_cond K2;
    [ exfalso; clear -K2 DHI SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE; rewrite ?Z.mod_small in K2 by lia; lia
    | step; zstep; zstep; step; if_cases K3; zify_cond K3; [ | exfalso; clear -K3 DHI SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE; rewrite ?Z.mod_small in K3 by lia; lia ] ] ].
  all: step; step.                                             (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  (* [comment removed for export] *)
  all: carry I64 MU WM ltac:(clear -CEIL LO SPR; lia); carry I72 MU WM ltac:(clear -CEIL LO SPR; lia); carry NSC MU WM ltac:(clear -CEIL LO SPR; lia).
  all: carry SRT MU WM ltac:(clear -CEIL LO SPR; lia); carry MTX MU WM ltac:(clear -CEIL LO SPR; lia).
  all: unbox JST; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JST; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR; lia] end.
  all: unbox JGL; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JGL; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR; lia] end.
  all: carry TI MU WM ltac:(clear -CEIL LO SPR; lia); carry TK MU WM ltac:(clear -CEIL LO SPR; lia); carry T88 MU WM ltac:(clear -CEIL LO SPR; lia); carry TSD MU WM ltac:(clear -CEIL LO SPR; lia).
  all: carry CT MU WM ltac:(clear -CEIL LO SPR CX1; lia).
  all: carry STATS MU WM ltac:(rewrite LSJ; clear -CEIL LO SPR T1; lia).
  all: carry ARR MU WM ltac:(rewrite ?length_map; clear -CEIL LO SPR PA1 LEN NSR; lia).
  all: carry HDR MU WM ltac:(clear -CEIL LO SPR MCE MS8K; lia).
  all: carry ACH MU WM ltac:(clear -CEIL LO SPR MCE MS8K; lia).
  all: assert (SHR : 2148238848 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE MS8K; Z.div_mod_to_equations; lia).
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport asegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR; lia|]); apply Forall_nil)).
  all: unbox LHDR.
  all: lazymatch goal with |- implF _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mk _) =>
         assert (LHDRk : idx <> nsec - 1 ->
            rw_cells asegs mk last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
            /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
            /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32)
         by (intros NE; (nd_pre (LHDR NE) 8%nat; intros LH L1 L2 L3 L4 L5 L6 L7; nd_post); split; [| split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| split; [exact L6| exact L7]]]]]]];
             eapply cells_frame; [exact LH | exact MU | exact WM | cbn; clear -CEIL LO SPR L1 L2; lia]) end.
  all: clear LHDR.
  all: eapply (recycle_sec_spec RNG k st Q) with (mb := mb) (ms := ms) (n := n) (idx := idx) (PA := PA) (nres := nres) (nsec := nsec) (last := last)
         (ctx := ctx) (t := t) (SB := SB) (CBA := bv_unsigned sp + -80) (lo := lo) (bases := bases) (lw1 := lw1) (lw2 := lw2) (sj := sj) (hsz := hsz) (srt := srt)
         (hst := hst) (hb1 := hb1) (hctx := hctx) (shj := shj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSC
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact ACH
       | |- rw_cells _ _ _ _ => first [eassumption | exact SRT | exact ISB]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- u64arr _ _ _ (map _ _) => exact ARR
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- @eq (option Z) _ _ => assumption
       | |- @eq Z _ _ => assumption
       | |- Forall _ _ => exact BR
       | |- tclr _ _ => assumption      (* [comment removed for export] *)
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ 4096 => assumption
       | |- rng _ _ (8 * _) => exact RPA
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
       | |- rng _ _ _ => exact RMB
       | |- _ -> rng _ _ _ => exact RLH
       | |- _ -> _ /\ _ => exact LHDRk
       | |- _ \/ _ => first [left; exact DLO | right; exact DHI | unboxed DMT | unboxed DMC | unboxed DMP | unboxed DPT | unboxed DPC | unboxed DCT]
       | |- forall _, _ => idtac
       | |- _ => try assumption; atop_facts; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MS8K MSAL MCE CX0 KACX0 KBCX0 KCCX0 CX1 T0 KAT0 KBT0 KCT0 TIC T1 PA0 PA1 IDX NSR LEN RA MAL NR SB0; lia
       end.
  (* [comment removed for export] *)
  all: intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1' b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  all: (pose proof PP as ndP__; nd_pre ndP__ 12%nat; intros MUd MId STd NSCd SRTd JSTd MTXd JGLd ARRd LHDRd STATSd SHZd; nd_post).
  all: rewrite ?unsigned_lit in MUd, STd by (clear -CEIL LO LO0 SPR; lia).
  all: unfold sdealloc_W in MUd.
  all: replace (ret_pc (Z_to_bv 64 229556)) with (Z_to_bv 64 229556 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: carry TC MU WM ltac:(clear -CEIL LO SPR T1; lia).
  all: pose proof (cells_frameD _ _ _ _ _ TC MUd ltac:(cbn; ub DMT; ub DPT; ub LDT0; clear -CEIL LO SPR T0 KAT0 KBT0 KCT0 TIC T1 MS8K IDX NSR PA0 SHR Y Y0 Y1; lia)) as TCd.
  (* [comment removed for export] *)
  all: lazymatch goal with FRq : rw_cells asegs _ (bv_unsigned _ + -80) _ |- _ =>
         pose proof (cells_frameD _ _ _ _ _ FRq MUd ltac:(cbn; clear -CEIL LO SPR T1 MCE MS8K PA1 IDX NSR SHR LCE0; lia)) as FRd; clear FRq end.
  all: pose proof (fp_le_trans _ _ _ LE1 (fstepS_le _ _ _ _ HF)) as LE.
  all: pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'; pose proof (rng_fp_le _ _ _ _ LE RT) as RT'; pose proof (rng_fp_le _ _ _ _ LE RIMG) as RIMG'.
  all: clear RSTK RT RIMG RCTX RPA RMB RSH RLH.
  all: iprefix.
  all: step.                                                   (* [comment removed for export] *)
  all: step; if_cases K5; zify_cond K5; [ | exfalso; unfold Q_CACHE in *; clear -K5 QBLE; rewrite ?Z.mod_small in K5 by lia; lia ].   (* [comment removed for export] *)
  all: do 9 step.                                              (* [comment removed for export] *)
  all: release_frame FRd STd (bv_unsigned sp).
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF | | exact TCd].
  all: unfold putrec_post, putrec_W.
  all: split; [| split; [exact MId| split; [exact STd| exact (proj2 (proj2 (proj2 PP)))]]].
  all: eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUd]];
       let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
Qed.
End Zd1.
#[using="Type"] Lemma put_passthru_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB lo nb fst0 lst qb : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PUTREC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xab270 -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 (mb + 6128) -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab2b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] -> Q_MAX < n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] -> 0 <= qb <= Q_CACHE ->
  (last + 32 <= t \/ t + 4096 <= last) -> last + 32 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xaafb8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells asegs m 0xaafd8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xaafe0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab008 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab018 [C1 srt] -> junk_at m 0xab020 32 ->
  rw_cells asegs m 0xab240 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab258 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      putrec_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x37ff4) fc None m (seg_rom asegs)).
Proof. exact put_passthru_spec__body. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.MM_syscalls.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.SysStepF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ADepot_iface__A3W.AKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.APoisonR_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_rsrvshadow.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_agbb__A3W.F_apoisonz.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_aalloc3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_asecdealloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepStore__A3W.F_arecsec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw.
(* [comment removed for export] *) Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac d_is_natlit n ::= sl_is_natlit n.
Local Ltac is_natlit n ::= sl_is_natlit n.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Local Ltac band_lin :=      (* [comment removed for export] *)
  repeat match goal with H : iclr ?a ?n |- _ => unfold iclr, AIMG_LO, AIMG_HI in H end.
Local Ltac with_band H tac :=
  let H' := fresh H in pose proof H as H'; unfold sclr, iclr, ablk, KLS, AIMG_LO, AIMG_HI in H'; tac; try clear H'.
(* [comment removed for export] *)
Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6307840 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6307840 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (sclr_int a n H G1 G2) 4%nat; intros k A B C; nd_post); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>      (* [comment removed for export] *)
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      (nd_pre (iclr_int a n H G2) 5%nat; intros k A B C D; nd_post); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Local Ltac ub H := let X := fresh "Y" in pose proof H as X; unbox X.

(* [comment removed for export] *)
Abbreviation PUTREC_STACK := 704.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition putrec_W (sp t mb ms PA idx last : Z) : list (Z * Z) :=
  [(sp - PUTREC_STACK, sp); (t + 2800, t + 3168);
   (0xab410, 0xab419); (0xab428, 0xab438); (0xab640, 0xab644); (0xab658, 0xab668);
   (PA + 8 * idx, PA + 8 * idx + 8); (last + 24, last + 32); (mb, mb + ms); (shad mb, shad mb + shlen ms)]%Z.

Definition putrec_post (sp : word) (t mb ms PA nres nsec idx last lo : Z) (bases : list Z) (lw1 lw2 : word)
    (m m' : amem) : Prop :=
     munch (putrec_W (bv_unsigned sp) t mb ms PA idx last) m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
  /\ rw_cells asegs m' 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 (nsec - 1))]
  /\ rw_cells asegs m' 0xab418 [C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab420 32
  /\ rw_cells asegs m' 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m' 0xab658 16
  /\ u64arr asegs m' PA (upd (map (Z_to_bv 64) bases) (Z.to_nat idx) (Z_to_bv 64 last))
  /\ (idx <> nsec - 1 -> rw_cells asegs m' last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 idx)])
  /\ (exists sj', u64arr asegs m' (t + 2800) sj' /\ length sj' = 46%nat)
  /\ rw_cells asegs m' (shad mb) [CB (Z.to_nat (shlen ms)) (repeat (Z_to_bv 8 0) (Z.to_nat (shlen ms)))].

Definition put_passthru_spec__stmt : Prop := forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB lo nb fst0 lst qb : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PUTREC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xab670 -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 (mb + 6128) -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] -> Q_MAX < n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] -> 0 <= qb <= Q_CACHE ->
  (last + 32 <= t \/ t + 4096 <= last) -> last + 32 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xab3e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 srt] -> junk_at m 0xab420 32 ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab658 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      putrec_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3805c) fc None m (seg_rom asegs)).
Section Zd1.   (* [comment removed for export] *)
Variable RNG : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 0).
Variable R : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 1).
Variable k : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 2).
Variable st : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 3).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 4).
Variable ra : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 5).
Variable sp : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 6).
Variable gp : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 7).
Variable tp : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 8).
Variable t0 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 9).
Variable t1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 10).
Variable t2 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 11).
Variable s0 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 12).
Variable s1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 13).
Variable a0 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 14).
Variable a1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 15).
Variable a2 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 16).
Variable a3 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 17).
Variable a4 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 18).
Variable a5 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 19).
Variable a6 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 20).
Variable a7 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 21).
Variable s2 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 22).
Variable s3 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 23).
Variable s4 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 24).
Variable s5 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 25).
Variable s6 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 26).
Variable s7 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 27).
Variable s8 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 28).
Variable s9 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 29).
Variable s10 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 30).
Variable s11 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 31).
Variable t3 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 32).
Variable t4 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 33).
Variable t5 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 34).
Variable t6 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 35).
Variable F : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 36).
Variable fc : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 37).
Variable m : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 38).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 39).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 40).
Variable n : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 41).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 42).
Variable PA : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 43).
Variable nres : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 44).
Variable nsec : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 45).
Variable last : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 46).
Variable ctx : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 47).
Variable t : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 48).
Variable SB : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 49).
Variable lo : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 50).
Variable nb : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 51).
Variable fst0 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 52).
Variable lst : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 53).
Variable qb : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 54).
Variable bases : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 55).
Variable hsz : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 56).
Variable lw1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 57).
Variable lw2 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 58).
Variable srt : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 59).
Variable hst : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 60).
Variable hb1 : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 61).
Variable hctx : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 62).
Variable sj : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 63).
Variable shj : ltac2:(SecDietF.SzSecF.ty 'put_passthru_spec__stmt 64).
#[using="Type"] Lemma put_passthru_spec__body : ltac:(let T := type of (fun (h : put_passthru_spec__stmt) => h RNG R k st Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m mb ms n idx PA nres nsec last ctx t SB lo nb fst0 lst qb bases hsz lw1 lw2 srt hst hb1 hctx sj shj) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (RNG, (R, (k, (st, (Q, (ra, (sp, (gp, (tp, (t0, (t1, (t2, (s0, (s1, (a0, (a1, (a2, (a3, (a4, (a5, (a6, (a7, (s2, (s3, (s4, (s5, (s6, (s7, (s8, (s9, (s10, (s11, (t3, (t4, (t5, (t6, (F, (fc, (m, (mb, (ms, (n, (idx, (PA, (nres, (nsec, (last, (ctx, (t, (SB, (lo, (nb, (fst0, (lst, (qb, (bases, (hsz, (lw1, (lw2, (srt, (hst, (hb1, (hctx, (sj, shj))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))) as _.

  intros ST CEIL LO SPHI MI TP -> -> -> -> QCELL NBIG TC QBLE LDT0 LCE0 ISB DSP SB0 I64 I72 NSC SRT JST MTX JGL TI TK T88 TSD CT CX0 CX1 T0 T1 STATS LSJ PC PRM RR
         ARR LEN IDX NSR NTHI NTHL PA0 PA1 HDR ACH NR BR MAL MLO MS8K MSAL MCE SH LHDR DMT DMC DMP DPT DPC DCT DML DPL RA
         RIMG RTLS RSTK RCTX RT RPA RMB RSH RLH CXI TIC NRB KONT. band_lin.   (* [comment removed for export] *)
  (pose proof (ablk_lin _ _ MLO) as ndP__; nd_pre ndP__ 4%nat; intros ML1 ML2 ML3 ML4; nd_post). unfold AIMG_HI in ML1. band_int T0. band_int CX0. band_int MLO.   (* [comment removed for export] *)
  unfold ATP88, ATSD, K_SPACE_SIZE, K_SPACE_EXTRA in *.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption). word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  (* [comment removed for export] *)
  box ISB. box I64. box I72. box NSC. box SRT. box JST. box MTX. box JGL. box TI. box TK. box T88. box TSD. box CT. box STATS. box ARR. box HDR. box ACH. box SH.
  box LHDR. box TC. box QCELL. box DMT. box DMC. box DMP. box DPT. box DPC. box DCT. box LDT0.
  rewrite large_dealloc_unfold at 1 || idtac.
  iprefix.
  carve_frame 80%nat ST.
  do 9 step.                                                   (* [comment removed for export] *)
  step. step. step.                                            (* [comment removed for export] *)
  carry QCELL MU WM ltac:(clear -CEIL LO SPR; lia).
  step. step.                                                  (* [comment removed for export] *)
  step. if_lit.                                                (* [comment removed for export] *)
  step. step. if_cases K1; zify_cond K1.                       (* [comment removed for export] *)
  { exfalso. unfold Q_MAX in *. clear -K1 NBIG NR. rewrite ?Z.mod_small in K1 by lia. lia. }
  carry ISB MU WM ltac:(clear -CEIL LO SPR; lia).
  step. step.                                                  (* [comment removed for export] *)
  destruct DSP as [DLO | DHI];
  [ step; if_cases K2; zify_cond K2; [ | exfalso; clear -K2 DLO MS8K SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO; rewrite ?Z.mod_small in K2 by lia; lia ]
  | step; if_cases K2; zify_cond K2;
    [ exfalso; clear -K2 DHI SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE; rewrite ?Z.mod_small in K2 by lia; lia
    | step; zstep; zstep; step; if_cases K3; zify_cond K3; [ | exfalso; clear -K3 DHI SB0 MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE; rewrite ?Z.mod_small in K3 by lia; lia ] ] ].
  all: step; step.                                             (* [comment removed for export] *)
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  (* [comment removed for export] *)
  all: carry I64 MU WM ltac:(clear -CEIL LO SPR; lia); carry I72 MU WM ltac:(clear -CEIL LO SPR; lia); carry NSC MU WM ltac:(clear -CEIL LO SPR; lia).
  all: carry SRT MU WM ltac:(clear -CEIL LO SPR; lia); carry MTX MU WM ltac:(clear -CEIL LO SPR; lia).
  all: unbox JST; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JST; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR; lia] end.
  all: unbox JGL; lazymatch type of MU with munch ?W0 ?me ?mm => eapply (junk_frame W0 me mm) in JGL; [| exact MU | exact WM | intros _; cbn; clear -CEIL LO SPR; lia] end.
  all: carry TI MU WM ltac:(clear -CEIL LO SPR; lia); carry TK MU WM ltac:(clear -CEIL LO SPR; lia); carry T88 MU WM ltac:(clear -CEIL LO SPR; lia); carry TSD MU WM ltac:(clear -CEIL LO SPR; lia).
  all: carry CT MU WM ltac:(clear -CEIL LO SPR CX1; lia).
  all: carry STATS MU WM ltac:(rewrite LSJ; clear -CEIL LO SPR T1; lia).
  all: carry ARR MU WM ltac:(rewrite ?length_map; clear -CEIL LO SPR PA1 LEN NSR; lia).
  all: carry HDR MU WM ltac:(clear -CEIL LO SPR MCE MS8K; lia).
  all: carry ACH MU WM ltac:(clear -CEIL LO SPR MCE MS8K; lia).
  all: assert (SHR : 2148239360 <= shad mb /\ shad mb + shlen ms <= 0x10007fff8000 /\ 512 <= shlen ms)   (* [comment removed for export] *)
         by (unfold shad, shlen, ASHOFF; rewrite !Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MCE MS8K; Z.div_mod_to_equations; lia).
  all: unbox SH; lazymatch type of MU with munch ?Wc ?me ?mk =>
         apply (rw_cells_transport asegs Wc me mk) in SH;
         [| exact MU | exact WM | cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by (clear -SHR; lia); clear -SHR CEIL LO SPR; lia] end.
  all: lazymatch type of MU with munch ?Wc ?me ?mk =>
         pose proof (poison_cells_frameD Wc me mk PC MU) as PCk; pose proof (premap_cells_frameD Wc me mk PRM MU) as PRMk;
         pose proof (arelro0_munch Wc me mk RR MU) as RRk end.
  all: cbn [disjoint_from] in PCk, PRMk.
  all: do 7 (specialize (PCk ltac:(clear -CEIL LO SPR; lia))).
  all: do 7 (specialize (PRMk ltac:(clear -CEIL LO SPR; lia))).
  all: specialize (RRk ltac:(unfold ARELRO_LO, ARELRO_HI; repeat (apply Forall_cons; [cbn; clear -CEIL LO SPR; lia|]); apply Forall_nil)).
  all: unbox LHDR.
  all: lazymatch goal with |- implF _ _ _ _ _ _ _ _ (MS _ _ _ _ _ ?mk _) =>
         assert (LHDRk : idx <> nsec - 1 ->
            rw_cells asegs mk last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
            /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
            /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32)
         by (intros NE; (nd_pre (LHDR NE) 8%nat; intros LH L1 L2 L3 L4 L5 L6 L7; nd_post); split; [| split; [exact L1| split; [exact L2| split; [exact L3| split; [exact L4| split; [exact L5| split; [exact L6| exact L7]]]]]]];
             eapply cells_frame; [exact LH | exact MU | exact WM | cbn; clear -CEIL LO SPR L1 L2; lia]) end.
  all: clear LHDR.
  all: eapply (recycle_sec_spec RNG k st Q) with (mb := mb) (ms := ms) (n := n) (idx := idx) (PA := PA) (nres := nres) (nsec := nsec) (last := last)
         (ctx := ctx) (t := t) (SB := SB) (CBA := bv_unsigned sp + -80) (lo := lo) (bases := bases) (lw1 := lw1) (lw2 := lw2) (sj := sj) (hsz := hsz) (srt := srt)
         (hst := hst) (hb1 := hb1) (hctx := hctx) (shj := shj).
  all: lazymatch goal with
       | |- stk _ _ _ _ => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); exact ST
       | |- mem_inv _ _ => exact MI
       | |- poison_cells _ => exact PCk
       | |- premap_cells _ => exact PRMk
       | |- arelro0 _ => exact RRk
       | |- @eq word _ _ => first [reflexivity | exact TP]
       | |- rw_cells _ _ (_ + 152) _ => exact CT
       | |- rw_cells _ _ ATSD _ => exact TSD
       | |- rw_cells _ _ _ [C8 _; C8 _; C8 _; C8 _] => exact HDR
       | |- rw_cells _ _ _ [C8 _; C8 _] => exact NSC
       | |- rw_cells _ _ _ [CB _ _] => exact SH
       | |- rw_cells _ _ _ [C1 _; C1 _; C2 _; C4 _; C8 _] => exact ACH
       | |- rw_cells _ _ _ _ => first [eassumption | exact SRT | exact ISB]
       | |- junk_at _ _ 32 => exact JST
       | |- junk_at _ _ 16 => exact JGL
       | |- u64arr _ _ _ (map _ _) => exact ARR
       | |- u64arr _ _ _ _ => exact STATS
       | |- length _ = _ => exact LSJ
       | |- @eq (option Z) _ _ => assumption
       | |- @eq Z _ _ => assumption
       | |- Forall _ _ => exact BR
       | |- tclr _ _ => assumption      (* [comment removed for export] *)
       | |- rng_aimg _ => exact RIMG
       | |- rng_atls _ => exact RTLS
       | |- rng _ _ 4096 => assumption
       | |- rng _ _ (8 * _) => exact RPA
       | |- rng _ (shad _) _ => exact RSH
       | |- rng _ _ (_ - _) => rewrite unsigned_lit by (clear -CEIL LO LO0 SPR; lia); eapply rng_sub'; [exact RSTK|]; clear -CEIL LO LO0 SPR; lia
       | |- rng _ _ _ => exact RMB
       | |- _ -> rng _ _ _ => exact RLH
       | |- _ -> _ /\ _ => exact LHDRk
       | |- _ \/ _ => first [left; exact DLO | right; exact DHI | unboxed DMT | unboxed DMC | unboxed DMP | unboxed DPT | unboxed DPC | unboxed DCT]
       | |- forall _, _ => idtac
       | |- _ => try assumption; atop_facts; rewrite ?unsigned_lit by (clear -CEIL LO LO0 SPR; lia); clear -CEIL LO LO0 SPR SPHI MLO ML1 ML2 ML3 KAMLO KBMLO KEMLO KCMLO KDMLO MS8K MSAL MCE CX0 KACX0 KBCX0 KCCX0 CX1 T0 KAT0 KBT0 KCT0 TIC T1 PA0 PA1 IDX NSR LEN RA MAL NR SB0; lia
       end.
  (* [comment removed for export] *)
  all: intros RNG1 rsp RNG' m' u0 u1 u2 b0 b1' b2 b3 b4 b5 b6 b7 u3 u4 u5 u6 LE1 HF PP.
  all: (pose proof PP as ndP__; nd_pre ndP__ 12%nat; intros MUd MId STd NSCd SRTd JSTd MTXd JGLd ARRd LHDRd STATSd SHZd; nd_post).
  all: rewrite ?unsigned_lit in MUd, STd by (clear -CEIL LO LO0 SPR; lia).
  all: unfold sdealloc_W in MUd.
  all: replace (ret_pc (Z_to_bv 64 229660)) with (Z_to_bv 64 229660 : word) by (symmetry; apply ret_pc_even; [clear; lia|reflexivity]).
  (* [comment removed for export] *)
  all: carry TC MU WM ltac:(clear -CEIL LO SPR T1; lia).
  all: pose proof (cells_frameD _ _ _ _ _ TC MUd ltac:(cbn; ub DMT; ub DPT; ub LDT0; clear -CEIL LO SPR T0 KAT0 KBT0 KCT0 TIC T1 MS8K IDX NSR PA0 SHR Y Y0 Y1; lia)) as TCd.
  (* [comment removed for export] *)
  all: lazymatch goal with FRq : rw_cells asegs _ (bv_unsigned _ + -80) _ |- _ =>
         pose proof (cells_frameD _ _ _ _ _ FRq MUd ltac:(cbn; clear -CEIL LO SPR T1 MCE MS8K PA1 IDX NSR SHR LCE0; lia)) as FRd; clear FRq end.
  all: pose proof (fp_le_trans _ _ _ LE1 (fstepS_le _ _ _ _ HF)) as LE.
  all: pose proof (rng_fp_le _ _ _ _ LE RSTK) as RSTK'; pose proof (rng_fp_le _ _ _ _ LE RT) as RT'; pose proof (rng_fp_le _ _ _ _ LE RIMG) as RIMG'.
  all: clear RSTK RT RIMG RCTX RPA RMB RSH RLH.
  all: iprefix.
  all: step.                                                   (* [comment removed for export] *)
  all: step; if_cases K5; zify_cond K5; [ | exfalso; unfold Q_CACHE in *; clear -K5 QBLE; rewrite ?Z.mod_small in K5 by lia; lia ].   (* [comment removed for export] *)
  all: do 9 step.                                              (* [comment removed for export] *)
  all: release_frame FRd STd (bv_unsigned sp).
  all: step.                                                   (* [comment removed for export] *)
  all: apply evtF_done.
  all: eapply (KONT RNG1 rsp RNG' m'); [exact LE1 | exact HF | | exact TCd].
  all: unfold putrec_post, putrec_W.
  all: split; [| split; [exact MId| split; [exact STd| exact (proj2 (proj2 (proj2 PP)))]]].
  all: eapply munch_trans; [eapply munch_weaken; [| exact MU] | eapply munch_weaken; [| exact MUd]];
       let xq := fresh "xq" in let Hq := fresh "Hq" in intros xq Hq; cbn in Hq |- *; clear -Hq; lia.
Qed.
End Zd1.
#[using="Type"] Lemma put_passthru_spec : forall RNG {R} (k : astate -> AM R) (st : astate) (Q : R -> footprint -> machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (mb ms n idx PA nres nsec last ctx t SB lo nb fst0 lst qb : Z) (bases : list Z)
    (hsz lw1 lw2 : word) (srt hst hb1 : byte) (hctx : word) (sj : list word) (shj : list byte),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - PUTREC_STACK -> bv_unsigned sp <= 2^47 ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 0xab670 -> a1 = Z_to_bv 64 (t + 80) -> a4 = Z_to_bv 64 (mb + 6128) -> a5 = Z_to_bv 64 n ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab6b0 [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)] -> Q_MAX < n ->
  rw_cells asegs m (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] -> 0 <= qb <= Q_CACHE ->
  (last + 32 <= t \/ t + 4096 <= last) -> last + 32 <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xab3b8 [C8 (Z_to_bv 64 SB)] -> (mb + ms <= SB \/ SB + K_SPACE_SIZE + K_SPACE_EXTRA <= mb) -> 0 <= SB < 2^47 ->
  rw_cells asegs m 0xab3d8 [C8 (Z_to_bv 64 4096)] -> rw_cells asegs m 0xab3e0 [C8 (Z_to_bv 64 PA)] ->
  rw_cells asegs m 0xab408 [C8 (Z_to_bv 64 nres); C8 (Z_to_bv 64 nsec)] ->
  rw_cells asegs m 0xab418 [C1 srt] -> junk_at m 0xab420 32 ->
  rw_cells asegs m 0xab640 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)] ->
  junk_at m 0xab658 16 ->
  (* [comment removed for export] *)
  rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] -> rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)] ->
  rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] -> rw_cells asegs m ATSD [C8 (Z_to_bv 64 ctx)] ->
  rw_cells asegs m (ctx + 152) [C8 (Z_to_bv 64 t)] ->
  sclr ctx 65536 -> ctx + 4096 <= ATOP -> sclr t 4096 -> (t + 4096 <= ATOP /\ tlsfarb kt_t t 4096 = true) ->
  u64arr asegs m (t + 2800) sj -> length sj = 46%nat ->
  (* [comment removed for export] *)
  poison_cells m -> premap_cells m -> arelro0 m ->
  (* [comment removed for export] *)
  u64arr asegs m PA (map (Z_to_bv 64) bases) -> Z.of_nat (length bases) = nsec ->
  0 <= idx < nsec -> nsec <= nres -> nth_error bases (Z.to_nat idx) = Some mb -> nth_error bases (Z.to_nat (nsec - 1)) = Some last ->
  ablk PA (PA + 8388608) -> PA + 8 * nres <= ATOP ->
  (* [comment removed for export] *)
  rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 hsz; C8 (Z_to_bv 64 idx)] ->
  rw_cells asegs m (mb + 6128) [C1 hst; C1 hb1; C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 hctx] -> 0 <= n < 2^32 ->
  Forall (fun ch => 0 <= ch < 2^64 /\ (ch <= mb + 6128 -> ch <= mb)) bases ->
  mb mod 4096 = 0 -> ablk mb (mb + ms) -> 8192 <= ms -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  rw_cells asegs m (shad mb) [CB (Z.to_nat (shlen ms)) shj] ->
  (idx <> nsec - 1 ->
      rw_cells asegs m last [C8 (Z_to_bv 64 last); C8 lw1; C8 lw2; C8 (Z_to_bv 64 (nsec - 1))]
   /\ ablk last (last + 32) /\ last + 32 <= ATOP /\ (last + 32 <= mb \/ mb + ms <= last)
   /\ (last + 32 <= t \/ t + 4096 <= last) /\ (last + 32 <= ctx \/ ctx + 4096 <= last) /\ (last + 32 <= PA \/ PA + 8 * nres <= last)
   /\ tclr last 32) ->
  (* [comment removed for export] *)
  (mb + ms <= t \/ t + 4096 <= mb) -> (mb + ms <= ctx \/ ctx + 4096 <= mb) -> (mb + ms <= PA \/ PA + 8 * nres <= mb) ->
  (PA + 8 * nres <= t \/ t + 4096 <= PA) -> (PA + 8 * nres <= ctx \/ ctx + 4096 <= PA) -> (ctx + 4096 <= t \/ t + 4096 <= ctx) ->
  tclr mb ms -> tclr PA (8 * nres) ->      (* [comment removed for export] *)
  4096 <= bv_unsigned ra ->
  (* [comment removed for export] *)
  rng_aimg RNG -> rng_atls RNG -> rng RNG lo (bv_unsigned sp - lo) -> rng RNG ctx 4096 -> rng RNG t 4096 -> rng RNG PA (8 * nres) ->
  rng RNG mb ms -> rng RNG (shad mb) (shlen ms) -> (idx <> nsec - 1 -> rng RNG last 32) ->
  AIMG_HI <= ctx -> iclr t 4096 -> nres <= 1048576 ->      (* [comment removed for export] *)
  (* [comment removed for export] *)
  (forall RNG1 rsp RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      fp_le RNG RNG1 -> fstepS (NMunmap mb ms) rsp RNG1 RNG' ->
      putrec_post sp t mb ms PA nres nsec idx last lo bases lw1 lw2 m m' ->
      rw_cells asegs m' (t + 80) [C8 (Z_to_bv 64 nb); C8 (Z_to_bv 64 fst0); C8 (Z_to_bv 64 lst); C8 (Z_to_bv 64 qb)] ->
      implS asegs RNG' (aembed ATOP (k (set_nsec (a_nsec st - 1) st))) (epostF Q)
            (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                F (ret_pc ra) fc None m' (seg_rom asegs))) ->
  implS asegs RNG (aembed ATOP (large_dealloc st mb ms k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x3805c) fc None m (seg_rom asegs)).
Proof. exact put_passthru_spec__body. Qed.
End CANSEC1.
End TwB.
End F_aputrec.
