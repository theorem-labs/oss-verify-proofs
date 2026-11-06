(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From Stdlib Require NArith.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics MemImageType Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AQConst.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ALayout.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition al_res (L : alayout) : Z := 4096 * al_V L 221%nat.
(* [comment removed for export] *)
Definition al_dtls (L : alayout) : Z := 4096 * al_V L 323%nat.
(* [comment removed for export] *)
Definition al_ahm (L : alayout) : Z := 4096 * al_V L 220%nat.
End CANSEC1.
Notation AAHM_LEN := 3727360 (only parsing).
Notation ARES_LEN := 137439023104 (only parsing).   (* [comment removed for export] *)
Notation AOBJ_LO := 17594333499392 (only parsing).  (* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition adisj (a1 n1 a2 n2 : Z) : Prop := a1 + n1 <= a2 \/ a2 + n2 <= a1.
(* [comment removed for export] *)
Definition aobj (a n : Z) : Prop := a mod 4096 = 0 /\ 4096 <= a /\ a + n <= ATOP /\ sclr a n /\ iclr a n.
#[using="Type"] Lemma aobj_img : forall a n, aobj a n -> 0x10000 <= n -> AIMG_HI <= a.
Proof. intros a n (_ & H1 & _ & _ & H4) Hn. unfold iclr, AIMG_LO, AIMG_HI in *. lia. Qed.

Record alayout_ok (L : alayout) : Prop := mkALO {
  ao_t : aobj (al_t L) 4096;  ao_ctx : aobj (al_ctx L) 65536;  ao_nodes : aobj (al_nodes L) 1048576;
  ao_store : aobj (al_store L) 8388608;  ao_fake : aobj (al_fake L) 11571200;  ao_res : aobj (al_res L) 137439023104;
  ao_ptr : aobj (al_ptr_array L) 8388608;  ao_dtls : aobj (al_dtls L) 4096;
  ao_res_hi : 0x10007fff8000 <= al_res L;     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ao_space : al_res L + 4096 <= al_space_beg L <= al_res L + 65536;  ao_space_al : al_space_beg L mod 65536 = 0;
  (* [comment removed for export] *)
  ad_t_res : adisj (al_t L) 4096 (al_res L) 137439023104;  ad_ctx_res : adisj (al_ctx L) 65536 (al_res L) 137439023104;
  ad_nodes_res : adisj (al_nodes L) 1048576 (al_res L) 137439023104;  ad_store_res : adisj (al_store L) 8388608 (al_res L) 137439023104;
  ad_fake_res : adisj (al_fake L) 11571200 (al_res L) 137439023104;  ad_ptr_res : adisj (al_ptr_array L) 8388608 (al_res L) 137439023104;
  ad_t_ctx : adisj (al_t L) 4096 (al_ctx L) 65536;  ad_t_nodes : adisj (al_t L) 4096 (al_nodes L) 1048576;
  ad_t_store : adisj (al_t L) 4096 (al_store L) 8388608;  ad_t_fake : adisj (al_t L) 4096 (al_fake L) 11571200;
  ad_t_ptr : adisj (al_t L) 4096 (al_ptr_array L) 8388608;
  ad_ctx_nodes : adisj (al_ctx L) 65536 (al_nodes L) 1048576;  ad_ctx_store : adisj (al_ctx L) 65536 (al_store L) 8388608;
  ad_ctx_fake : adisj (al_ctx L) 65536 (al_fake L) 11571200;  ad_ctx_ptr : adisj (al_ctx L) 65536 (al_ptr_array L) 8388608;
  ad_nodes_store : adisj (al_nodes L) 1048576 (al_store L) 8388608;  ad_nodes_fake : adisj (al_nodes L) 1048576 (al_fake L) 11571200;
  ad_nodes_ptr : adisj (al_nodes L) 1048576 (al_ptr_array L) 8388608;
  ad_store_fake : adisj (al_store L) 8388608 (al_fake L) 11571200;  ad_store_ptr : adisj (al_store L) 8388608 (al_ptr_array L) 8388608;
  ad_fake_ptr : adisj (al_fake L) 11571200 (al_ptr_array L) 8388608;
  ad_dtls_res : adisj (al_dtls L) 4096 (al_res L) 137439023104;  ad_t_dtls : adisj (al_t L) 4096 (al_dtls L) 4096;
  ad_ctx_dtls : adisj (al_ctx L) 65536 (al_dtls L) 4096;  ad_nodes_dtls : adisj (al_nodes L) 1048576 (al_dtls L) 4096;
  ad_store_dtls : adisj (al_store L) 8388608 (al_dtls L) 4096;  ad_fake_dtls : adisj (al_fake L) 11571200 (al_dtls L) 4096;
  ad_dtls_ptr : adisj (al_dtls L) 4096 (al_ptr_array L) 8388608;
  (* [comment removed for export] *)
  ao_stack : al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP <= al_bot L <= ATOP + 4096);
  ao_U : (length (al_U L) <= Z.to_nat AUMAX)%nat;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ai_tls_res : al_res L + 137439023104 <= ATPv + -200 + kt_res * 18446744073709551616 /\ ATPv + 312 <= al_res L + (1 - kt_res) * 18446744073709551616;
  ai_tls_t : al_t L + 4096 <= ATPv + -200 + kt_t * 18446744073709551616 /\ ATPv + 312 <= al_t L + (1 - kt_t) * 18446744073709551616;
  ad_tls_ctx : adisj (ATPv + -200) 512 (al_ctx L) 65536;
  ad_tls_nodes : adisj (ATPv + -200) 512 (al_nodes L) 1048576;  ad_tls_store : adisj (ATPv + -200) 512 (al_store L) 8388608;
  ad_tls_fake : adisj (ATPv + -200) 512 (al_fake L) 11571200;
  ad_tls_ptr : adisj (ATPv + -200) 512 (al_ptr_array L) 8388608;  ad_tls_dtls : adisj (ATPv + -200) 512 (al_dtls L) 4096;
  (* [comment removed for export] *)
  ao_ahm_eq : al_ahm L = AAHMv;  ao_ahm : aobj (al_ahm L) 3727360;
  ad_ahm_t : adisj (al_ahm L) 3727360 (al_t L) 4096;  ad_ahm_ctx : adisj (al_ahm L) 3727360 (al_ctx L) 65536;
  ad_ahm_nodes : adisj (al_ahm L) 3727360 (al_nodes L) 1048576;  ad_ahm_store : adisj (al_ahm L) 3727360 (al_store L) 8388608;
  ad_ahm_fake : adisj (al_ahm L) 3727360 (al_fake L) 11571200;  ad_ahm_res : adisj (al_ahm L) 3727360 (al_res L) 137439023104;
  ad_ahm_ptr : adisj (al_ahm L) 3727360 (al_ptr_array L) 8388608;  ad_ahm_dtls : adisj (al_ahm L) 3727360 (al_dtls L) 4096;
  ad_tls_ahm : adisj (ATPv + -200) 512 (al_ahm L) 3727360
}.

(* [comment removed for export] *)
#[using="Type"] Lemma ad_tls_res : forall L, alayout_ok L -> adisj (ATPv + -200) 512 (al_res L) 137439023104.
Proof. intros L H. pose proof (ai_tls_res L H) as (A & B). pose proof atp_lin as ((_ & _ & (K & _)) & _). unfold adisj. assert (E : kt_res = 0 \/ kt_res = 1) by lia. destruct E as [E|E]; rewrite E in *; lia. Qed.
#[using="Type"] Lemma ad_tls_t : forall L, alayout_ok L -> adisj (ATPv + -200) 512 (al_t L) 4096.
Proof. intros L H. pose proof (ai_tls_t L H) as (A & B). pose proof atp_lin as ((_ & _ & (_ & K)) & _). unfold adisj. assert (E : kt_t = 0 \/ kt_t = 1) by lia. destruct E as [E|E]; rewrite E in *; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma alayout_space : forall L, alayout_ok L ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true)
  /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
  /\ 0 <= al_space_beg L < 2^47.
Proof.
  intros L H. pose proof (ai_tls_res L H) as (TR1 & TR2). pose proof atp_lin as ((_ & _ & (KR & _)) & _). pose proof (ao_res L H) as R. pose proof (ao_res_hi L H) as RH. pose proof (ao_space L H) as SB. pose proof (ao_space_al L H) as SAL.
  unfold aobj, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472.
  split; [split; [lia | apply tlsfarb_intro; lia] | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma alayout_slot_disj : forall L A sz, alayout_ok L ->
  al_space_beg L <= A -> A + sz <= al_space_beg L + K_SPACE_SIZE -> 0 <= sz ->
     (al_t L + 4096 <= A \/ A + sz <= al_t L)
  /\ (al_ctx L + 65536 <= A \/ A + sz <= al_ctx L)
  /\ (al_nodes L + 1048576 <= A \/ A + sz <= al_nodes L)
  /\ (al_store L + 8388608 <= A \/ A + sz <= al_store L)
  /\ (al_fake L + 11571200 <= A \/ A + sz <= al_fake L).
Proof.
  intros L A sz H LO HI SZ. pose proof (ao_space L H) as SB. unfold K_SPACE_SIZE in HI. change (2^37) with 137438953472 in HI.
  unfold adisj in *.
  split; [pose proof (ad_t_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_ctx_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_nodes_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_store_res L H) as D; unfold adisj in D; lia|].
  pose proof (ad_fake_res L H) as D; unfold adisj in D; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma alayout_t : forall L, alayout_ok L ->
  sclr (al_t L) 4096 /\ (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) /\ al_t L mod 4096 = 0 /\ iclr (al_t L) 4096.
Proof. intros L H. pose proof (ao_t L H) as T. pose proof (ai_tls_t L H) as (TT1 & TT2). pose proof (tlsfarb_intro kt_t (al_t L) 4096 TT1 TT2) as TF. unfold aobj in *. tauto. Qed.
#[using="Type"] Lemma alayout_t_lin : forall L, alayout_ok L -> 4096 <= al_t L /\ (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true).
Proof. intros L H. pose proof (ao_t L H) as T. pose proof (ai_tls_t L H) as (TT1 & TT2). pose proof (tlsfarb_intro kt_t (al_t L) 4096 TT1 TT2) as TF. unfold aobj in *. tauto. Qed.
#[using="Type"] Lemma alayout_ctx : forall L, alayout_ok L ->
  sclr (al_ctx L) 65536 /\ al_ctx L + 65536 <= ATOP /\ AIMG_HI <= al_ctx L /\ 0 < al_ctx L
  /\ (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L).
Proof.
  intros L H. pose proof (ao_ctx L H) as C. pose proof (aobj_img _ _ C ltac:(lia)) as CI. pose proof (ad_t_ctx L H) as D.
  unfold aobj, adisj, AIMG_HI in *. repeat split; try tauto; lia.
Qed.
#[using="Type"] Lemma alayout_depot : forall L, alayout_ok L ->
  sclr (al_nodes L) 1048576 /\ al_nodes L + 1048576 <= ATOP /\ AIMG_HI <= al_nodes L
  /\ sclr (al_store L) 8388608 /\ al_store L + 8388608 <= ATOP /\ AIMG_HI <= al_store L
  /\ (al_t L + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= al_t L) /\ (al_t L + 4096 <= al_store L \/ al_store L + 8388608 <= al_t L)
  /\ (al_ctx L + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= al_ctx L) /\ (al_ctx L + 4096 <= al_store L \/ al_store L + 8388608 <= al_ctx L).
Proof.
  intros L H. pose proof (ao_nodes L H) as N. pose proof (ao_store L H) as S.
  pose proof (aobj_img _ _ N ltac:(lia)) as NI. pose proof (aobj_img _ _ S ltac:(lia)) as SI. unfold aobj, AIMG_HI in *.
  split; [tauto|]. split; [lia|]. split; [lia|]. split; [tauto|]. split; [lia|]. split; [lia|].
  split; [pose proof (ad_t_nodes L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_t_store L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_ctx_nodes L H) as D; unfold adisj in D; lia|].
  pose proof (ad_ctx_store L H) as D; unfold adisj in D; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma alayout_stack : forall L, alayout_ok L ->
  al_bot L + 0x800000 = al_top L /\ al_top L <= 2^47 /\ (ATOP <= al_bot L <= ATOP + 4096).
Proof. intros L H. pose proof (ao_stack L H). lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma alayout_page_bot : forall L, alayout_ok L -> forall e, e mod 4096 = 0 -> e <= ATOP -> e <= al_bot L.
Proof. intros L H e He Hle. (pose proof (ao_stack L H) as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). Z.div_mod_to_equations. nia. Qed.
End CANSEC2.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition al_res (L : alayout) : Z := 4096 * al_V L 221%nat.
(* [comment removed for export] *)
Definition al_dtls (L : alayout) : Z := 4096 * al_V L 323%nat.
(* [comment removed for export] *)
Definition al_ahm (L : alayout) : Z := 4096 * al_V L 220%nat.
End CANSEC1.
Notation AAHM_LEN := 3727360 (only parsing).
Notation ARES_LEN := 137439023104 (only parsing).   (* [comment removed for export] *)
Notation AOBJ_LO := 17594333499392 (only parsing).  (* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition adisj (a1 n1 a2 n2 : Z) : Prop := a1 + n1 <= a2 \/ a2 + n2 <= a1.
(* [comment removed for export] *)
Definition aobj (a n : Z) : Prop := a mod 4096 = 0 /\ 4096 <= a /\ a + n <= ATOP /\ sclr a n /\ iclr a n.
#[using="Type"] Lemma aobj_img : forall a n, aobj a n -> 0x10000 <= n -> AIMG_HI <= a.
Proof. intros a n (_ & H1 & _ & _ & H4) Hn. unfold iclr, AIMG_LO, AIMG_HI in *. lia. Qed.

Record alayout_ok (L : alayout) : Prop := mkALO {
  ao_t : aobj (al_t L) 4096;  ao_ctx : aobj (al_ctx L) 65536;  ao_nodes : aobj (al_nodes L) 1048576;
  ao_store : aobj (al_store L) 8388608;  ao_fake : aobj (al_fake L) 11571200;  ao_res : aobj (al_res L) 137439023104;
  ao_ptr : aobj (al_ptr_array L) 8388608;  ao_dtls : aobj (al_dtls L) 4096;
  ao_res_hi : 0x10007fff8000 <= al_res L;     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ao_space : al_res L + 4096 <= al_space_beg L <= al_res L + 65536;  ao_space_al : al_space_beg L mod 65536 = 0;
  (* [comment removed for export] *)
  ad_t_res : adisj (al_t L) 4096 (al_res L) 137439023104;  ad_ctx_res : adisj (al_ctx L) 65536 (al_res L) 137439023104;
  ad_nodes_res : adisj (al_nodes L) 1048576 (al_res L) 137439023104;  ad_store_res : adisj (al_store L) 8388608 (al_res L) 137439023104;
  ad_fake_res : adisj (al_fake L) 11571200 (al_res L) 137439023104;  ad_ptr_res : adisj (al_ptr_array L) 8388608 (al_res L) 137439023104;
  ad_t_ctx : adisj (al_t L) 4096 (al_ctx L) 65536;  ad_t_nodes : adisj (al_t L) 4096 (al_nodes L) 1048576;
  ad_t_store : adisj (al_t L) 4096 (al_store L) 8388608;  ad_t_fake : adisj (al_t L) 4096 (al_fake L) 11571200;
  ad_t_ptr : adisj (al_t L) 4096 (al_ptr_array L) 8388608;
  ad_ctx_nodes : adisj (al_ctx L) 65536 (al_nodes L) 1048576;  ad_ctx_store : adisj (al_ctx L) 65536 (al_store L) 8388608;
  ad_ctx_fake : adisj (al_ctx L) 65536 (al_fake L) 11571200;  ad_ctx_ptr : adisj (al_ctx L) 65536 (al_ptr_array L) 8388608;
  ad_nodes_store : adisj (al_nodes L) 1048576 (al_store L) 8388608;  ad_nodes_fake : adisj (al_nodes L) 1048576 (al_fake L) 11571200;
  ad_nodes_ptr : adisj (al_nodes L) 1048576 (al_ptr_array L) 8388608;
  ad_store_fake : adisj (al_store L) 8388608 (al_fake L) 11571200;  ad_store_ptr : adisj (al_store L) 8388608 (al_ptr_array L) 8388608;
  ad_fake_ptr : adisj (al_fake L) 11571200 (al_ptr_array L) 8388608;
  ad_dtls_res : adisj (al_dtls L) 4096 (al_res L) 137439023104;  ad_t_dtls : adisj (al_t L) 4096 (al_dtls L) 4096;
  ad_ctx_dtls : adisj (al_ctx L) 65536 (al_dtls L) 4096;  ad_nodes_dtls : adisj (al_nodes L) 1048576 (al_dtls L) 4096;
  ad_store_dtls : adisj (al_store L) 8388608 (al_dtls L) 4096;  ad_fake_dtls : adisj (al_fake L) 11571200 (al_dtls L) 4096;
  ad_dtls_ptr : adisj (al_dtls L) 4096 (al_ptr_array L) 8388608;
  (* [comment removed for export] *)
  ao_stack : al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP <= al_bot L <= ATOP + 4096);
  ao_U : (length (al_U L) <= Z.to_nat AUMAX)%nat;
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  ai_tls_res : al_res L + 137439023104 <= ATPv + -200 + kt_res * 18446744073709551616 /\ ATPv + 312 <= al_res L + (1 - kt_res) * 18446744073709551616;
  ai_tls_t : al_t L + 4096 <= ATPv + -200 + kt_t * 18446744073709551616 /\ ATPv + 312 <= al_t L + (1 - kt_t) * 18446744073709551616;
  ad_tls_ctx : adisj (ATPv + -200) 512 (al_ctx L) 65536;
  ad_tls_nodes : adisj (ATPv + -200) 512 (al_nodes L) 1048576;  ad_tls_store : adisj (ATPv + -200) 512 (al_store L) 8388608;
  ad_tls_fake : adisj (ATPv + -200) 512 (al_fake L) 11571200;
  ad_tls_ptr : adisj (ATPv + -200) 512 (al_ptr_array L) 8388608;  ad_tls_dtls : adisj (ATPv + -200) 512 (al_dtls L) 4096;
  (* [comment removed for export] *)
  ao_ahm_eq : al_ahm L = AAHMv;  ao_ahm : aobj (al_ahm L) 3727360;
  ad_ahm_t : adisj (al_ahm L) 3727360 (al_t L) 4096;  ad_ahm_ctx : adisj (al_ahm L) 3727360 (al_ctx L) 65536;
  ad_ahm_nodes : adisj (al_ahm L) 3727360 (al_nodes L) 1048576;  ad_ahm_store : adisj (al_ahm L) 3727360 (al_store L) 8388608;
  ad_ahm_fake : adisj (al_ahm L) 3727360 (al_fake L) 11571200;  ad_ahm_res : adisj (al_ahm L) 3727360 (al_res L) 137439023104;
  ad_ahm_ptr : adisj (al_ahm L) 3727360 (al_ptr_array L) 8388608;  ad_ahm_dtls : adisj (al_ahm L) 3727360 (al_dtls L) 4096;
  ad_tls_ahm : adisj (ATPv + -200) 512 (al_ahm L) 3727360
}.

(* [comment removed for export] *)
#[using="Type"] Lemma ad_tls_res : forall L, alayout_ok L -> adisj (ATPv + -200) 512 (al_res L) 137439023104.
Proof. intros L H. pose proof (ai_tls_res L H) as (A & B). pose proof atp_lin as ((_ & _ & (K & _)) & _). unfold adisj. assert (E : kt_res = 0 \/ kt_res = 1) by lia. destruct E as [E|E]; rewrite E in *; lia. Qed.
#[using="Type"] Lemma ad_tls_t : forall L, alayout_ok L -> adisj (ATPv + -200) 512 (al_t L) 4096.
Proof. intros L H. pose proof (ai_tls_t L H) as (A & B). pose proof atp_lin as ((_ & _ & (_ & K)) & _). unfold adisj. assert (E : kt_t = 0 \/ kt_t = 1) by lia. destruct E as [E|E]; rewrite E in *; lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma alayout_space : forall L, alayout_ok L ->
  (0x10007fff8000 <= al_space_beg L /\ tlsfarb kt_res (al_space_beg L) 137438957568 = true)
  /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
  /\ 0 <= al_space_beg L < 2^47.
Proof.
  intros L H. pose proof (ai_tls_res L H) as (TR1 & TR2). pose proof atp_lin as ((_ & _ & (KR & _)) & _). pose proof (ao_res L H) as R. pose proof (ao_res_hi L H) as RH. pose proof (ao_space L H) as SB. pose proof (ao_space_al L H) as SAL.
  unfold aobj, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472.
  split; [split; [lia | apply tlsfarb_intro; lia] | lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma alayout_slot_disj : forall L A sz, alayout_ok L ->
  al_space_beg L <= A -> A + sz <= al_space_beg L + K_SPACE_SIZE -> 0 <= sz ->
     (al_t L + 4096 <= A \/ A + sz <= al_t L)
  /\ (al_ctx L + 65536 <= A \/ A + sz <= al_ctx L)
  /\ (al_nodes L + 1048576 <= A \/ A + sz <= al_nodes L)
  /\ (al_store L + 8388608 <= A \/ A + sz <= al_store L)
  /\ (al_fake L + 11571200 <= A \/ A + sz <= al_fake L).
Proof.
  intros L A sz H LO HI SZ. pose proof (ao_space L H) as SB. unfold K_SPACE_SIZE in HI. change (2^37) with 137438953472 in HI.
  unfold adisj in *.
  split; [pose proof (ad_t_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_ctx_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_nodes_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_store_res L H) as D; unfold adisj in D; lia|].
  pose proof (ad_fake_res L H) as D; unfold adisj in D; lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma alayout_t : forall L, alayout_ok L ->
  sclr (al_t L) 4096 /\ (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true) /\ al_t L mod 4096 = 0 /\ iclr (al_t L) 4096.
Proof. intros L H. pose proof (ao_t L H) as T. pose proof (ai_tls_t L H) as (TT1 & TT2). pose proof (tlsfarb_intro kt_t (al_t L) 4096 TT1 TT2) as TF. unfold aobj in *. tauto. Qed.
#[using="Type"] Lemma alayout_t_lin : forall L, alayout_ok L -> 4096 <= al_t L /\ (al_t L + 4096 <= ATOP /\ tlsfarb kt_t (al_t L) 4096 = true).
Proof. intros L H. pose proof (ao_t L H) as T. pose proof (ai_tls_t L H) as (TT1 & TT2). pose proof (tlsfarb_intro kt_t (al_t L) 4096 TT1 TT2) as TF. unfold aobj in *. tauto. Qed.
#[using="Type"] Lemma alayout_ctx : forall L, alayout_ok L ->
  sclr (al_ctx L) 65536 /\ al_ctx L + 65536 <= ATOP /\ AIMG_HI <= al_ctx L /\ 0 < al_ctx L
  /\ (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L).
Proof.
  intros L H. pose proof (ao_ctx L H) as C. pose proof (aobj_img _ _ C ltac:(lia)) as CI. pose proof (ad_t_ctx L H) as D.
  unfold aobj, adisj, AIMG_HI in *. repeat split; try tauto; lia.
Qed.
#[using="Type"] Lemma alayout_depot : forall L, alayout_ok L ->
  sclr (al_nodes L) 1048576 /\ al_nodes L + 1048576 <= ATOP /\ AIMG_HI <= al_nodes L
  /\ sclr (al_store L) 8388608 /\ al_store L + 8388608 <= ATOP /\ AIMG_HI <= al_store L
  /\ (al_t L + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= al_t L) /\ (al_t L + 4096 <= al_store L \/ al_store L + 8388608 <= al_t L)
  /\ (al_ctx L + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= al_ctx L) /\ (al_ctx L + 4096 <= al_store L \/ al_store L + 8388608 <= al_ctx L).
Proof.
  intros L H. pose proof (ao_nodes L H) as N. pose proof (ao_store L H) as S.
  pose proof (aobj_img _ _ N ltac:(lia)) as NI. pose proof (aobj_img _ _ S ltac:(lia)) as SI. unfold aobj, AIMG_HI in *.
  split; [tauto|]. split; [lia|]. split; [lia|]. split; [tauto|]. split; [lia|]. split; [lia|].
  split; [pose proof (ad_t_nodes L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_t_store L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_ctx_nodes L H) as D; unfold adisj in D; lia|].
  pose proof (ad_ctx_store L H) as D; unfold adisj in D; lia.
Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma alayout_stack : forall L, alayout_ok L ->
  al_bot L + 0x800000 = al_top L /\ al_top L <= 2^47 /\ (ATOP <= al_bot L <= ATOP + 4096).
Proof. intros L H. pose proof (ao_stack L H). lia. Qed.
(* [comment removed for export] *)
#[using="Type"] Lemma alayout_page_bot : forall L, alayout_ok L -> forall e, e mod 4096 = 0 -> e <= ATOP -> e <= al_bot L.
Proof. intros L H e He Hle. (pose proof (ao_stack L H) as ndP__; nd_pre ndP__ 4%nat; intros S1 S2 S3 S4; nd_post). Z.div_mod_to_equations. nia. Qed.
End CANSEC2.
End TwB.
End ALayout.

(* [comment removed for export] *)
Module ARep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Import AImg ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition AMAGIC : Z := 0xCC6E96B9CC6E96B9.  (* [comment removed for export] *)
Definition ARI_STRIDE : Z := 128.         (* [comment removed for export] *)
Definition ASTATS_WORDS : nat := 46%nat.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive bstate :=
| BLive (p : aptr)       (* [comment removed for export] *)
| BQuar                  (* [comment removed for export] *)
| BBatch.                (* [comment removed for export] *)

Record xbusy := mkXBusy {
  xb_class : Z;          (* [comment removed for export] *)
  xb_slot : Z;           (* [comment removed for export] *)
  xb_n : Z;              (* [comment removed for export] *)
  xb_st : bstate;
  xb_b1 : Z;             (* [comment removed for export] *)
  xb_ctx : Z             (* [comment removed for export] *)
}.

Record xclass := mkXClass {
  xc_free : list Z;      (* [comment removed for export] *)
  xc_cache : list Z      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record aconc := mkAConc {
  x_cls : Z -> xclass;
  x_busy : list xbusy
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aregion (L : alayout) (c : Z) : Z := al_space_beg L + c * K_REGION.
Definition aslot_addr (L : alayout) (c k : Z) : Z := aregion L c + k * size_of_class c.
Definition afreearr (L : alayout) (c : Z) : Z := aregion L c + K_FREEARR_OFF.
Definition aregion_info (L : alayout) (c : Z) : Z := al_space_beg L + K_SPACE_SIZE + c * ARI_STRIDE.
Definition acompact (c k : Z) : Z := k * (size_of_class c / 16).
(* [comment removed for export] *)
Definition xb_alloc (L : alayout) (b : xbusy) : Z := aslot_addr L (xb_class b) (xb_slot b).
Definition xb_user (L : alayout) (b : xbusy) : Z := xb_alloc L b + rz_size (xb_n b).
Definition xb_hdr (L : alayout) (b : xbusy) : Z := xb_user L b - 16.
(* [comment removed for export] *)
Definition ndist (st : astate) (c : Z) : Z := c_allocated_user (get_cls st c) / size_of_class c.

(* [comment removed for export] *)
Definition busy_of (X : aconc) (c k : Z) : option xbusy :=
  List.find (fun b => (xb_class b =? c) && (xb_slot b =? k)) (x_busy X).
Definition busy_slots (X : aconc) (c : Z) : list Z :=
  List.map xb_slot (List.filter (fun b => xb_class b =? c) (x_busy X)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition junk_at (m : amem) (A len : Z) : Prop :=
  exists bs, rw_cells asegs m A [CB (Z.to_nat len) bs].
(* [comment removed for export] *)
Definition fill_at (m : amem) (A len v : Z) : Prop :=
  rw_cells asegs m A [CB (Z.to_nat len) (repeat (Z_to_bv 8 v) (Z.to_nat len))].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition arep_rt (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa54a0 [C8 (Z_to_bv 64 0x140128); C8 (Z_to_bv 64 0xabdf8); C8 (Z_to_bv 64 0xae5f8);
                                C8 (Z_to_bv 64 0xaf2e8); C8 (Z_to_bv 64 0xaf2f0); C8 (Z_to_bv 64 0xaf2e0)]
  /\ rw_cells asegs m 0xa54d0 [C8 (Z_to_bv 64 0xa7360)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6018 [C8 (Z_to_bv 64 0xaf2d9)]
  /\ rw_cells asegs m 0xa6108 [C8 (Z_to_bv 64 0x10)]                                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7358 [C8 (Z_to_bv 64 0x9e6a0); C8 (Z_to_bv 64 0x9ead4)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xabdb8 [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048); C1 (Z_to_bv 8 1)]
                                                                                            (* [comment removed for export] *)
  /\ rw_cells asegs m 0xabdf8 [C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 1024); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 2048)]
                                                                                            (* [comment removed for export] *)
  /\ rw_cells asegs m 0xabe24 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xabe4d [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae5f8 [C8 (Z_to_bv 64 0x7fff8000)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0xade5c [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xade60 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xade64 [C4 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf2d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf2e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf2fc [C4 (Z_to_bv 64 30)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x130860 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)]        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)]                                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1400c0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140148 [C8 (Z_to_bv 64 0x1e00010000)]                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0x14014a [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1401a0 [C8 (Z_to_bv 64 18446744073709551615)]                                    (* [comment removed for export] *)
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)]                                    (* [comment removed for export] *)
  /\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))].                          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ainstance (L : alayout) (st : astate) (m : amem) : Prop :=
     rw_cells asegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 (al_space_beg L))]                  (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 48) [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 64) [C8 (Z_to_bv 64 4096)]                              (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 72) [C8 (Z_to_bv 64 (al_ptr_array L))]                  (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 112) [C8 (Z_to_bv 64 (a_nres st)); C8 (Z_to_bv 64 (a_nsec st))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)]                                (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 984) [C1 (Z_to_bv 8 0)]                                (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 40) [C4 (Z_to_bv 64 4294967295)]                        (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 56) [C1 (Z_to_bv 8 0)].                                (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition acache_addr (L : alayout) (c : Z) : Z := al_t L + 208 + c * 80.
Definition acache_cells (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let xc := x_cls X c in
  exists tail : list word,
     rw_cells asegs m (acache_addr L c)
       [C4 (Z_to_bv 64 (c_count (get_cls st c))); C4 (Z_to_bv 64 (max_count st c));
        C8 (Z_to_bv 64 (if a_cinit st then size_of_class c else 0))]
  /\ u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache xc) ++ tail)
  /\ (length (xc_cache xc) + length tail = 16)%nat.

(* [comment removed for export] *)
Definition athread (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     rw_cells asegs m (al_t L) [C8 (Z_to_bv 64 (al_ctx L)); C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))]
  /\ rw_cells asegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]                 (* [comment removed for export] *)
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> acache_cells L st X m c)
  /\ junk_at m (al_t L + 2768) 32                                       (* [comment removed for export] *)
  /\ (exists sj, u64arr asegs m (al_t L + 2800) sj /\ length sj = ASTATS_WORDS)   (* [comment removed for export] *)
  /\ rw_cells asegs m (al_t L + 3168) [C1 (Z_to_bv 8 0)].              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition aregion_cells (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in
     rw_cells asegs m (aregion_info L c) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ rw_cells asegs m (aregion_info L c + 16)
       [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 (c_mapped_free_array r));
        C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0) (* [comment removed for export] *);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0) (* [comment removed for export] *)]
  /\ junk_at m (aregion_info L c + 64) 4                                                    (* [comment removed for export] *)
  /\ rw_cells asegs m (aregion_info L c + 68) [C1 (Z_to_bv 8 0)]                            (* [comment removed for export] *)
  /\ junk_at m (aregion_info L c + 72) 56.                                                  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition afreearray (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let xc := x_cls X c in
     u32arr asegs m (afreearr L c) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free xc))
  /\ junk_at m (afreearr L c + 4 * c_num_freed r) (c_mapped_free_array r - 4 * c_num_freed r)
  /\ junk_at m (shad (afreearr L c)) (shlen (c_mapped_free_array r)).        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bstate_byte (s : bstate) : option Z :=
  match s with BLive _ => Some 2 | BQuar => Some 3 | BBatch => None end.

Definition aslot_busy (L : alayout) (m : amem) (b : xbusy) : Prop :=
  let c := xb_class b in let S := size_of_class c in
  let AB := xb_alloc L b in let n := xb_n b in let rz := rz_size n in let UB := AB + rz in let HB := UB - 16 in
  match xb_st b with
  | BBatch => junk_at m AB S    (* [comment removed for export] *)
  | s =>
       (16 < rz -> rw_cells asegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 HB)] /\ junk_at m (AB + 16) (rz - 32))
    /\ (exists stb, bstate_byte s = Some stb /\
           rw_cells asegs m HB [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 (xb_b1 b)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 (xb_ctx b))])
    /\ junk_at m UB (S - rz)
  end.

Definition aslots (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
     (forall k, 0 <= k < ndist st c ->
        match busy_of X c k with
        | None => junk_at m (aslot_addr L c k) S
        | Some b => aslot_busy L m b
        end)
  /\ junk_at m (aregion L c + c_allocated_user r) (c_mapped_user r - c_allocated_user r).

(* [comment removed for export] *)
Definition granules (n : Z) : Z := shlen (n + 7).      (* [comment removed for export] *)
Definition block_shadow_bytes (n : Z) : list byte :=
  repeat (Z_to_bv 8 0) (Z.to_nat (shlen n)) ++
  (if n mod 8 =? 0 then [] else [Z_to_bv 8 (n mod 8)]).
Definition slot_shadow_bytes (S : Z) (b : option xbusy) : list byte :=
  match b with
  | None => repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S))
  | Some b =>
      let n := xb_n b in let rz := rz_size n in
      let mid := match xb_st b with
                 | BLive _ => block_shadow_bytes n
                 | BQuar => repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))
                 | BBatch => repeat (Z_to_bv 8 0xfa) (Z.to_nat (granules n))
                 end in
      repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)) ++ mid
      ++ repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n))
  end.
Definition aslot_shadow (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
     (forall k, 0 <= k < ndist st c ->
        rw_cells asegs m (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen S)) (slot_shadow_bytes S (busy_of X c k))])
  /\ fill_at m (shad (aregion L c + c_allocated_user r)) (shlen (c_mapped_user r - c_allocated_user r)) 0xfa.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition awf (L : alayout) (st : astate) (X : aconc) : Prop :=
     a_space_beg st = al_space_beg L /\ a_ptr_array st = al_ptr_array L
  /\ al_space_beg L mod K_ALIGN = 0 /\ 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP
  (* [comment removed for export] *)
  /\ (forall c, 1 <= c < K_NUM_CLASSES ->
        let r := get_cls st c in let xc := x_cls X c in let S := size_of_class c in
           0 <= c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
        /\ c_allocated_user r mod S = 0 /\ c_mapped_user r mod K_USER_MAP = 0
        /\ 0 <= c_num_freed r /\ 4 * c_num_freed r <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
        /\ Z.of_nat (length (xc_free xc)) = c_num_freed r
        /\ Z.of_nat (length (xc_cache xc)) = c_count r /\ 0 <= c_count r <= max_count st c
        /\ List.NoDup (xc_free xc ++ xc_cache xc ++ busy_slots X c)
        /\ (forall k, In k (xc_free xc ++ xc_cache xc ++ busy_slots X c) -> 0 <= k < ndist st c))
  (* [comment removed for export] *)
  /\ (forall c, ~ (1 <= c < K_NUM_CLASSES) -> get_cls st c = aclass0)
  (* [comment removed for export] *)
  /\ (forall b, In b (x_busy X) ->
        1 <= xb_class b < K_NUM_CLASSES
        /\ match xb_st b with
           | BLive p => 1 <= xb_n b <= AREQMAX /\ rounded_size (xb_n b) + rz_size (xb_n b) <= size_of_class (xb_class b)
                        /\ 0 <= xb_b1 b < 256 /\ Z.land (xb_b1 b) 3 = 1 (* [comment removed for export] *)
                        /\ 0 <= xb_ctx b < 2^31
                        /\ (a_live st) !! p = Some (CPrim (xb_class b) (xb_n b))
           | BQuar => 1 <= xb_n b <= AREQMAX /\ rounded_size (xb_n b) + rz_size (xb_n b) <= size_of_class (xb_class b)
                        /\ 0 <= xb_b1 b < 256 /\ Z.land (xb_b1 b) 3 = 1 /\ 0 <= xb_ctx b < 2^31      (* [comment removed for export] *)
           | BBatch => xb_class b = K_BATCH_CLASS                           (* [comment removed for export] *)
           end)
  /\ (forall p c n, (a_live st) !! p = Some (CPrim c n) -> exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_class b = c /\ xb_n b = n)
  /\ (forall p ch, (a_live st) !! p = Some ch -> (p < a_next st)%N)           (* [comment removed for export] *)
  /\ (forall b1 b2, In b1 (x_busy X) -> In b2 (x_busy X) -> xb_st b1 = xb_st b2 -> (exists p, xb_st b1 = BLive p) -> b1 = b2).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record aholes := mkAHoles {
  ah_quar : alayout -> astate -> aconc -> amem -> Prop;
  ah_sec : alayout -> astate -> aconc -> amem -> Prop;
  ah_depot : alayout -> amem -> Prop;
  ah_fake : alayout -> list ablock -> amem -> Prop     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition arelro (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

(* [comment removed for export] *)
Definition azero (m : amem) (A n : Z) : Prop :=
  (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) /\ wr_at asegs m A n.
Definition ashadow_avail (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in
     azero m (shad (aregion L c + c_mapped_user r)) (shlen (K_FREEARR_OFF - c_mapped_user r))
  /\ azero m (shad (afreearr L c + c_mapped_free_array r)) (shlen (K_FREEARR_MAX - c_mapped_free_array r)).

(* [comment removed for export] *)
Definition arep_rt2 (m : amem) : Prop :=
     rw_cells asegs m 0x14022c [C1 (Z_to_bv 8 0)]          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1401b8 [C8 (Z_to_bv 64 0)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa71d8 [C8 (Z_to_bv 64 0x9edb8)]. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition arep_rt3 (m : amem) : Prop :=
     rw_cells asegs m 0xa7238 [C8 (Z_to_bv 64 0x9dff0); C8 (Z_to_bv 64 0x9aee0)]
  /\ rw_cells asegs m 0xa7210 [C8 (Z_to_bv 64 0xa3ea8)]
  /\ rw_cells asegs m 0xa7220 [C8 (Z_to_bv 64 0x9abc8)]
  /\ rw_cells asegs m 0xa7308 [C8 (Z_to_bv 64 0x9eff4)]
  /\ rw_cells asegs m 0xa7200 [C8 (Z_to_bv 64 0x9e5a4)]
  /\ rw_cells asegs m 0x140178 [C8 (Z_to_bv 64 4294967296)]
  /\ rw_cells asegs m 0x140220 [C8 (Z_to_bv 64 0x101010101010101)]
  /\ rw_cells asegs m 0xae600 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xabe58 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x13e098 [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5490 [C8 (Z_to_bv 64 0x13e0a0); C8 (Z_to_bv 64 0xa7398)]
  /\ rw_cells asegs m 0xa7398 [C8 (Z_to_bv 64 0x19361)]
  /\ rw_cells asegs m 0x13e0a0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0x140200 [C8 (Z_to_bv 64 0x10101000100)]
  /\ rw_cells asegs m 0x140218 [C8 (Z_to_bv 64 0x101000100000000)]
  /\ (exists cb : list byte, rw_cells asegs m 0x6015f8 [CB 8 cb])   (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601878 [C8 (Z_to_bv 64 4096)].

Definition AREP (H : aholes) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     awf L st X
  /\ arep_rt L m
  /\ ainstance L st m
  /\ athread L st X m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L st m c /\ afreearray L st X m c /\ aslots L st X m c /\ aslot_shadow L st X m c)
  /\ ah_quar H L st X m /\ ah_sec H L st X m /\ ah_depot H L m
  /\ arelro m
  /\ arep_rt2 m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L st m c)
  /\ arep_rt3 m.                                       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section KitStatements.
Variable H : aholes.

(* [comment removed for export] *)
Definition kit_cache_pop_stmt : Prop :=
  forall L st X m c cnt, AREP H L st X m -> 1 <= c < K_NUM_CLASSES ->
  c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k
    /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells asegs m (acache_addr L c)
         [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr asegs m (acache_addr L c + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k))
    /\ junk_at m (aslot_addr L c k) (size_of_class c)
    /\ fill_at m (shad (aslot_addr L c k)) (shlen (size_of_class c)) 0xfa.

(* [comment removed for export] *)
Definition kit_malloc_fast_stmt : Prop :=
  forall L st X m m' c k n (p : aptr) b1 ctx,
  AREP H L st X m -> 1 <= c < K_NUM_CLASSES -> is_primary n = true -> class_id (needed_size n) = c ->
  0 < c_count (get_cls st c) ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (c_count (get_cls st c) - 1)) = Some k ->
  (a_live st) !! p = None -> 0 <= b1 < 0x80 -> 0 <= ctx < 2^31 ->
  let b := mkXBusy c k n (BLive p) b1 ctx in
  let st' := set_next (N.succ (a_next st)) (set_live (<[p := CPrim c n]> (a_live st))
               (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)) in
  (* [comment removed for export] *)
  (m' = m -> False) ->
  AREP H L st' (mkAConc (x_cls X) (b :: x_busy X)) m'.

(* [comment removed for export] *)
Definition hole_frame_stmt (P : alayout -> amem -> Prop) (FP : alayout -> Z -> Prop) : Prop :=
  forall L m m' (W : list (Z * Z)),
    P L m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv -> ~ FP L a) W -> P L m'.
End KitStatements.
End CANSEC1.
(* [comment removed for export] *)

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition AMAGIC : Z := 0xCC6E96B9CC6E96B9.  (* [comment removed for export] *)
Definition ARI_STRIDE : Z := 128.         (* [comment removed for export] *)
Definition ASTATS_WORDS : nat := 46%nat.  (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive bstate :=
| BLive (p : aptr)       (* [comment removed for export] *)
| BQuar                  (* [comment removed for export] *)
| BBatch.                (* [comment removed for export] *)

Record xbusy := mkXBusy {
  xb_class : Z;          (* [comment removed for export] *)
  xb_slot : Z;           (* [comment removed for export] *)
  xb_n : Z;              (* [comment removed for export] *)
  xb_st : bstate;
  xb_b1 : Z;             (* [comment removed for export] *)
  xb_ctx : Z             (* [comment removed for export] *)
}.

Record xclass := mkXClass {
  xc_free : list Z;      (* [comment removed for export] *)
  xc_cache : list Z      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record aconc := mkAConc {
  x_cls : Z -> xclass;
  x_busy : list xbusy
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition aregion (L : alayout) (c : Z) : Z := al_space_beg L + c * K_REGION.
Definition aslot_addr (L : alayout) (c k : Z) : Z := aregion L c + k * size_of_class c.
Definition afreearr (L : alayout) (c : Z) : Z := aregion L c + K_FREEARR_OFF.
Definition aregion_info (L : alayout) (c : Z) : Z := al_space_beg L + K_SPACE_SIZE + c * ARI_STRIDE.
Definition acompact (c k : Z) : Z := k * (size_of_class c / 16).
(* [comment removed for export] *)
Definition xb_alloc (L : alayout) (b : xbusy) : Z := aslot_addr L (xb_class b) (xb_slot b).
Definition xb_user (L : alayout) (b : xbusy) : Z := xb_alloc L b + rz_size (xb_n b).
Definition xb_hdr (L : alayout) (b : xbusy) : Z := xb_user L b - 16.
(* [comment removed for export] *)
Definition ndist (st : astate) (c : Z) : Z := c_allocated_user (get_cls st c) / size_of_class c.

(* [comment removed for export] *)
Definition busy_of (X : aconc) (c k : Z) : option xbusy :=
  List.find (fun b => (xb_class b =? c) && (xb_slot b =? k)) (x_busy X).
Definition busy_slots (X : aconc) (c : Z) : list Z :=
  List.map xb_slot (List.filter (fun b => xb_class b =? c) (x_busy X)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition junk_at (m : amem) (A len : Z) : Prop :=
  exists bs, rw_cells asegs m A [CB (Z.to_nat len) bs].
(* [comment removed for export] *)
Definition fill_at (m : amem) (A len v : Z) : Prop :=
  rw_cells asegs m A [CB (Z.to_nat len) (repeat (Z_to_bv 8 v) (Z.to_nat len))].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition arep_rt (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5880 [C8 (Z_to_bv 64 0x140528); C8 (Z_to_bv 64 0xac1f8); C8 (Z_to_bv 64 0xae9f8);
                                C8 (Z_to_bv 64 0xaf6e8); C8 (Z_to_bv 64 0xaf6f0); C8 (Z_to_bv 64 0xaf6e0)]
  /\ rw_cells asegs m 0xa58b0 [C8 (Z_to_bv 64 0xa7740)]                                   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa63f8 [C8 (Z_to_bv 64 0xaf6d9)]
  /\ rw_cells asegs m 0xa64e8 [C8 (Z_to_bv 64 0x10)]                                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7738 [C8 (Z_to_bv 64 0x9ea84); C8 (Z_to_bv 64 0x9eeb8)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac1b8 [C8 (Z_to_bv 64 (2^40)); C2 (Z_to_bv 64 16); C2 (Z_to_bv 64 2048); C1 (Z_to_bv 8 1)]
                                                                                            (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac1f8 [C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 256); C4 (Z_to_bv 64 1024); C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 2048)]
                                                                                            (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac224 [C4 (Z_to_bv 64 0x1000); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0xbe)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xac24d [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae9f8 [C8 (Z_to_bv 64 0x7fff8000)]                                 (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae25c [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0xae260 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs m 0xae264 [C4 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf6d8 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)]                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf6e0 [C8 (Z_to_bv 64 0x7fffffffffff); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]   (* [comment removed for export] *)
  /\ rw_cells asegs m 0xaf6fc [C4 (Z_to_bv 64 30)]                                         (* [comment removed for export] *)
  /\ rw_cells asegs m 0x130c60 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0)]        (* [comment removed for export] *)
  /\ rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)]                                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1404c0 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]                       (* [comment removed for export] *)
  /\ rw_cells asegs m 0x140548 [C8 (Z_to_bv 64 0x1e00010000)]                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0x14054a [C1 (Z_to_bv 8 1)]                                           (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1405a0 [C8 (Z_to_bv 64 18446744073709551615)]                                    (* [comment removed for export] *)
  /\ rw_cells asegs m ATP88 [C8 (Z_to_bv 64 ATSD)] /\ rw_cells asegs m ATSD [C8 (Z_to_bv 64 (al_ctx L))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (ATPv + 16) [C4 (Z_to_bv 64 0)]                                          (* [comment removed for export] *)
  /\ rw_cells asegs m (al_ctx L + 8) [C4 (Z_to_bv 64 0)]                                    (* [comment removed for export] *)
  /\ rw_cells asegs m (al_ctx L + 152) [C8 (Z_to_bv 64 (al_t L))].                          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ainstance (L : alayout) (st : astate) (m : amem) : Prop :=
     rw_cells asegs m (AINSTANCE + 32) [C8 (Z_to_bv 64 (al_space_beg L))]                  (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 48) [C8 (Z_to_bv 64 (al_space_beg L + K_SPACE_SIZE))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 64) [C8 (Z_to_bv 64 4096)]                              (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 72) [C8 (Z_to_bv 64 (al_ptr_array L))]                  (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 112) [C8 (Z_to_bv 64 (a_nres st)); C8 (Z_to_bv 64 (a_nsec st))]   (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 680) [C1 (Z_to_bv 8 0)]                                (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 984) [C1 (Z_to_bv 8 0)]                                (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 40) [C4 (Z_to_bv 64 4294967295)]                        (* [comment removed for export] *)
  /\ rw_cells asegs m (AINSTANCE + 56) [C1 (Z_to_bv 8 0)].                                (* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition acache_addr (L : alayout) (c : Z) : Z := al_t L + 208 + c * 80.
Definition acache_cells (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let xc := x_cls X c in
  exists tail : list word,
     rw_cells asegs m (acache_addr L c)
       [C4 (Z_to_bv 64 (c_count (get_cls st c))); C4 (Z_to_bv 64 (max_count st c));
        C8 (Z_to_bv 64 (if a_cinit st then size_of_class c else 0))]
  /\ u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache xc) ++ tail)
  /\ (length (xc_cache xc) + length tail = 16)%nat.

(* [comment removed for export] *)
Definition athread (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     rw_cells asegs m (al_t L) [C8 (Z_to_bv 64 (al_ctx L)); C8 (Z_to_bv 64 (al_top L)); C8 (Z_to_bv 64 (al_bot L))]
  /\ rw_cells asegs m (al_t L + 40) [C1 (Z_to_bv 8 0)]                 (* [comment removed for export] *)
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> acache_cells L st X m c)
  /\ junk_at m (al_t L + 2768) 32                                       (* [comment removed for export] *)
  /\ (exists sj, u64arr asegs m (al_t L + 2800) sj /\ length sj = ASTATS_WORDS)   (* [comment removed for export] *)
  /\ rw_cells asegs m (al_t L + 3168) [C1 (Z_to_bv 8 0)].              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition aregion_cells (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in
     rw_cells asegs m (aregion_info L c) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]            (* [comment removed for export] *)
  /\ rw_cells asegs m (aregion_info L c + 16)
       [C8 (Z_to_bv 64 (c_num_freed r)); C8 (Z_to_bv 64 (c_mapped_free_array r));
        C8 (Z_to_bv 64 (c_allocated_user r)); C8 (Z_to_bv 64 0) (* [comment removed for export] *);
        C8 (Z_to_bv 64 (c_mapped_user r)); C8 (Z_to_bv 64 0) (* [comment removed for export] *)]
  /\ junk_at m (aregion_info L c + 64) 4                                                    (* [comment removed for export] *)
  /\ rw_cells asegs m (aregion_info L c + 68) [C1 (Z_to_bv 8 0)]                            (* [comment removed for export] *)
  /\ junk_at m (aregion_info L c + 72) 56.                                                  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition afreearray (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let xc := x_cls X c in
     u32arr asegs m (afreearr L c) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free xc))
  /\ junk_at m (afreearr L c + 4 * c_num_freed r) (c_mapped_free_array r - 4 * c_num_freed r)
  /\ junk_at m (shad (afreearr L c)) (shlen (c_mapped_free_array r)).        (* [comment removed for export] *)

(* [comment removed for export] *)
Definition bstate_byte (s : bstate) : option Z :=
  match s with BLive _ => Some 2 | BQuar => Some 3 | BBatch => None end.

Definition aslot_busy (L : alayout) (m : amem) (b : xbusy) : Prop :=
  let c := xb_class b in let S := size_of_class c in
  let AB := xb_alloc L b in let n := xb_n b in let rz := rz_size n in let UB := AB + rz in let HB := UB - 16 in
  match xb_st b with
  | BBatch => junk_at m AB S    (* [comment removed for export] *)
  | s =>
       (16 < rz -> rw_cells asegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 HB)] /\ junk_at m (AB + 16) (rz - 32))
    /\ (exists stb, bstate_byte s = Some stb /\
           rw_cells asegs m HB [C1 (Z_to_bv 8 stb); C1 (Z_to_bv 8 (xb_b1 b)); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 (xb_ctx b))])
    /\ junk_at m UB (S - rz)
  end.

Definition aslots (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
     (forall k, 0 <= k < ndist st c ->
        match busy_of X c k with
        | None => junk_at m (aslot_addr L c k) S
        | Some b => aslot_busy L m b
        end)
  /\ junk_at m (aregion L c + c_allocated_user r) (c_mapped_user r - c_allocated_user r).

(* [comment removed for export] *)
Definition granules (n : Z) : Z := shlen (n + 7).      (* [comment removed for export] *)
Definition block_shadow_bytes (n : Z) : list byte :=
  repeat (Z_to_bv 8 0) (Z.to_nat (shlen n)) ++
  (if n mod 8 =? 0 then [] else [Z_to_bv 8 (n mod 8)]).
Definition slot_shadow_bytes (S : Z) (b : option xbusy) : list byte :=
  match b with
  | None => repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S))
  | Some b =>
      let n := xb_n b in let rz := rz_size n in
      let mid := match xb_st b with
                 | BLive _ => block_shadow_bytes n
                 | BQuar => repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))
                 | BBatch => repeat (Z_to_bv 8 0xfa) (Z.to_nat (granules n))
                 end in
      repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)) ++ mid
      ++ repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n))
  end.
Definition aslot_shadow (L : alayout) (st : astate) (X : aconc) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in let S := size_of_class c in
     (forall k, 0 <= k < ndist st c ->
        rw_cells asegs m (shad (aslot_addr L c k)) [CB (Z.to_nat (shlen S)) (slot_shadow_bytes S (busy_of X c k))])
  /\ fill_at m (shad (aregion L c + c_allocated_user r)) (shlen (c_mapped_user r - c_allocated_user r)) 0xfa.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition awf (L : alayout) (st : astate) (X : aconc) : Prop :=
     a_space_beg st = al_space_beg L /\ a_ptr_array st = al_ptr_array L
  /\ al_space_beg L mod K_ALIGN = 0 /\ 0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP
  (* [comment removed for export] *)
  /\ (forall c, 1 <= c < K_NUM_CLASSES ->
        let r := get_cls st c in let xc := x_cls X c in let S := size_of_class c in
           0 <= c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
        /\ c_allocated_user r mod S = 0 /\ c_mapped_user r mod K_USER_MAP = 0
        /\ 0 <= c_num_freed r /\ 4 * c_num_freed r <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
        /\ Z.of_nat (length (xc_free xc)) = c_num_freed r
        /\ Z.of_nat (length (xc_cache xc)) = c_count r /\ 0 <= c_count r <= max_count st c
        /\ List.NoDup (xc_free xc ++ xc_cache xc ++ busy_slots X c)
        /\ (forall k, In k (xc_free xc ++ xc_cache xc ++ busy_slots X c) -> 0 <= k < ndist st c))
  (* [comment removed for export] *)
  /\ (forall c, ~ (1 <= c < K_NUM_CLASSES) -> get_cls st c = aclass0)
  (* [comment removed for export] *)
  /\ (forall b, In b (x_busy X) ->
        1 <= xb_class b < K_NUM_CLASSES
        /\ match xb_st b with
           | BLive p => 1 <= xb_n b <= AREQMAX /\ rounded_size (xb_n b) + rz_size (xb_n b) <= size_of_class (xb_class b)
                        /\ 0 <= xb_b1 b < 256 /\ Z.land (xb_b1 b) 3 = 1 (* [comment removed for export] *)
                        /\ 0 <= xb_ctx b < 2^31
                        /\ (a_live st) !! p = Some (CPrim (xb_class b) (xb_n b))
           | BQuar => 1 <= xb_n b <= AREQMAX /\ rounded_size (xb_n b) + rz_size (xb_n b) <= size_of_class (xb_class b)
                        /\ 0 <= xb_b1 b < 256 /\ Z.land (xb_b1 b) 3 = 1 /\ 0 <= xb_ctx b < 2^31      (* [comment removed for export] *)
           | BBatch => xb_class b = K_BATCH_CLASS                           (* [comment removed for export] *)
           end)
  /\ (forall p c n, (a_live st) !! p = Some (CPrim c n) -> exists b, In b (x_busy X) /\ xb_st b = BLive p /\ xb_class b = c /\ xb_n b = n)
  /\ (forall p ch, (a_live st) !! p = Some ch -> (p < a_next st)%N)           (* [comment removed for export] *)
  /\ (forall b1 b2, In b1 (x_busy X) -> In b2 (x_busy X) -> xb_st b1 = xb_st b2 -> (exists p, xb_st b1 = BLive p) -> b1 = b2).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record aholes := mkAHoles {
  ah_quar : alayout -> astate -> aconc -> amem -> Prop;
  ah_sec : alayout -> astate -> aconc -> amem -> Prop;
  ah_depot : alayout -> amem -> Prop;
  ah_fake : alayout -> list ablock -> amem -> Prop     (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition arelro (m : amem) : Prop := forall i, ARELRO_LO <= i < ARELRO_HI -> m (wa i) = None.

(* [comment removed for export] *)
Definition azero (m : amem) (A n : Z) : Prop :=
  (forall i, 0 <= i < n -> m (wa (A + i)) = Some (Z_to_bv 8 0)) /\ wr_at asegs m A n.
Definition ashadow_avail (L : alayout) (st : astate) (m : amem) (c : Z) : Prop :=
  let r := get_cls st c in
     azero m (shad (aregion L c + c_mapped_user r)) (shlen (K_FREEARR_OFF - c_mapped_user r))
  /\ azero m (shad (afreearr L c + c_mapped_free_array r)) (shlen (K_FREEARR_MAX - c_mapped_free_array r)).

(* [comment removed for export] *)
Definition arep_rt2 (m : amem) : Prop :=
     rw_cells asegs m 0x14062c [C1 (Z_to_bv 8 0)]          (* [comment removed for export] *)
  /\ rw_cells asegs m 0x1405b8 [C8 (Z_to_bv 64 0)]         (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa75b8 [C8 (Z_to_bv 64 0x9f19c)]. (* [comment removed for export] *)

(* [comment removed for export] *)
Definition arep_rt3 (m : amem) : Prop :=
     rw_cells asegs m 0xa7618 [C8 (Z_to_bv 64 0x9e3d4); C8 (Z_to_bv 64 0x9b2c4)]
  /\ rw_cells asegs m 0xa75f0 [C8 (Z_to_bv 64 0xa428c)]
  /\ rw_cells asegs m 0xa7600 [C8 (Z_to_bv 64 0x9afac)]
  /\ rw_cells asegs m 0xa76e8 [C8 (Z_to_bv 64 0x9f3d8)]
  /\ rw_cells asegs m 0xa75e0 [C8 (Z_to_bv 64 0x9e988)]
  /\ rw_cells asegs m 0x140578 [C8 (Z_to_bv 64 4294967296)]
  /\ rw_cells asegs m 0x140620 [C8 (Z_to_bv 64 0x101010101010101)]
  /\ rw_cells asegs m 0xaea00 [C4 (Z_to_bv 64 1)]
  /\ rw_cells asegs m 0xac258 [C1 (Z_to_bv 8 1)]
  /\ rw_cells asegs m 0x13e498 [C4 (Z_to_bv 64 0)]
  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa5870 [C8 (Z_to_bv 64 0x13e4a0); C8 (Z_to_bv 64 0xa7778)]
  /\ rw_cells asegs m 0xa7778 [C8 (Z_to_bv 64 0x19361)]
  /\ rw_cells asegs m 0x13e4a0 [C8 (Z_to_bv 64 4096)]
  /\ rw_cells asegs m 0x140600 [C8 (Z_to_bv 64 0x10101000100)]
  /\ rw_cells asegs m 0x140618 [C8 (Z_to_bv 64 0x101000100000000)]
  /\ (exists cb : list byte, rw_cells asegs m 0x6019f8 [CB 8 cb])   (* [comment removed for export] *)
  /\ rw_cells asegs m 0x601c78 [C8 (Z_to_bv 64 4096)].

Definition AREP (H : aholes) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
     awf L st X
  /\ arep_rt L m
  /\ ainstance L st m
  /\ athread L st X m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> aregion_cells L st m c /\ afreearray L st X m c /\ aslots L st X m c /\ aslot_shadow L st X m c)
  /\ ah_quar H L st X m /\ ah_sec H L st X m /\ ah_depot H L m
  /\ arelro m
  /\ arep_rt2 m
  /\ (forall c, 1 <= c < K_NUM_CLASSES -> ashadow_avail L st m c)
  /\ arep_rt3 m.                                       (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section KitStatements.
Variable H : aholes.

(* [comment removed for export] *)
Definition kit_cache_pop_stmt : Prop :=
  forall L st X m c cnt, AREP H L st X m -> 1 <= c < K_NUM_CLASSES ->
  c_count (get_cls st c) = cnt -> 0 < cnt ->
  exists k chunks,
       nth_error (xc_cache (x_cls X c)) (Z.to_nat (cnt - 1)) = Some k
    /\ busy_of X c k = None /\ 0 <= k < ndist st c
    /\ rw_cells asegs m (acache_addr L c)
         [C4 (Z_to_bv 64 cnt); C4 (Z_to_bv 64 (max_count st c)); C8 (Z_to_bv 64 (size_of_class c))]
    /\ u32arr asegs m (acache_addr L c + 16) chunks /\ length chunks = 16%nat
    /\ nth_error chunks (Z.to_nat (cnt - 1)) = Some (Z_to_bv 64 (acompact c k))
    /\ junk_at m (aslot_addr L c k) (size_of_class c)
    /\ fill_at m (shad (aslot_addr L c k)) (shlen (size_of_class c)) 0xfa.

(* [comment removed for export] *)
Definition kit_malloc_fast_stmt : Prop :=
  forall L st X m m' c k n (p : aptr) b1 ctx,
  AREP H L st X m -> 1 <= c < K_NUM_CLASSES -> is_primary n = true -> class_id (needed_size n) = c ->
  0 < c_count (get_cls st c) ->
  nth_error (xc_cache (x_cls X c)) (Z.to_nat (c_count (get_cls st c) - 1)) = Some k ->
  (a_live st) !! p = None -> 0 <= b1 < 0x80 -> 0 <= ctx < 2^31 ->
  let b := mkXBusy c k n (BLive p) b1 ctx in
  let st' := set_next (N.succ (a_next st)) (set_live (<[p := CPrim c n]> (a_live st))
               (put_cls c (cls_set_count (c_count (get_cls st c) - 1) (get_cls st c)) st)) in
  (* [comment removed for export] *)
  (m' = m -> False) ->
  AREP H L st' (mkAConc (x_cls X) (b :: x_busy X)) m'.

(* [comment removed for export] *)
Definition hole_frame_stmt (P : alayout -> amem -> Prop) (FP : alayout -> Z -> Prop) : Prop :=
  forall L m m' (W : list (Z * Z)),
    P L m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv -> ~ FP L a) W -> P L m'.
End KitStatements.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End ARep.

(* [comment removed for export] *)
Module AFrameD.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import NDestr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma wview_agree : forall m m' (x : word), m' x = m x -> wview segs m' x = wview segs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_agree : forall m m' A n,
  wr_at segs m A n -> (forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))) -> wr_at segs m' A n.
Proof.
  intros m m' A n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_agree m m' _ (E i Hi)). apply H. exact Hi.
Qed.

#[using="Type"] Lemma wr_at_transportD : forall W m m' A n,
  wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
  intros W m m' A n WR MU D. (pose proof WR as ndP__; nd_pre ndP__ 3%nat; intros H0 H1 _; nd_post).
  eapply wr_at_agree; [exact WR|]. intros i Hi. apply MU.
  rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia].
Qed.

#[using="Type"] Lemma rw_cells_transportD : forall W m m' A cs,
  rw_cells segs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] MU D. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

#[using="Type"] Lemma u8arr_transportD : forall W m m' A bs,
  u8arr segs m A bs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transportD; eauto.
Qed.

#[using="Type"] Lemma u32arr_transportD : forall W m m' A ws,
  u32arr segs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

#[using="Type"] Lemma u64arr_transportD : forall W m m' A ws,
  u64arr segs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_transportD : forall W m m' lo hi,
  stk segs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk segs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) MU D. split; [exact H0|]. split; [exact H1|].
  intros a Ha.
  assert (E : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  destruct (H a Ha) as [WV [b RD]]. split.
  - rewrite (wview_agree m m' _ E). exact WV.
  - exists b. unfold mrd in *. rewrite E. exact RD.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munch_agree_range : forall W m m' A n i,
  munch W m m' -> disjoint_from W A n -> 0 <= A -> A + n <= 2^64 -> 0 <= i < n ->
  m' (wa (A + i)) = m (wa (A + i)).
Proof.
  intros W m m' A n i MU D H0 H1 Hi. apply MU. rewrite wa_unsigned by lia.
  eapply disjoint_outside; [exact D | lia].
Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma junk_frameD : forall W m m' A n, junk_at m A n -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma fill_frameD : forall W m m' A n v, fill_at m A n v -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma cells_frameD : forall W m m' A cs, rw_cells asegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof. intros. eapply rw_cells_transportD; eauto. Qed.

#[using="Type"] Lemma u64arr_frameD : forall W m m' A ws, u64arr asegs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof. intros. eapply u64arr_transportD; eauto. Qed.
#[using="Type"] Lemma u32arr_frameD : forall W m m' A ws, u32arr asegs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof. intros. eapply u32arr_transportD; eauto. Qed.

#[using="Type"] Lemma azero_frameD : forall W m m' A n, azero m A n -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros W m m' A n [Z0 WR] MU D. (pose proof WR as ndP__; nd_pre ndP__ 3%nat; intros W0 W1 _; nd_post).
  assert (E : forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))).
  { intros i Hi. eapply munch_agree_range; [exact MU | apply D; lia | lia | lia | lia]. }
  split.
  - intros i Hi. rewrite (E i Hi). apply Z0. exact Hi.
  - eapply wr_at_agree; [exact WR | exact E].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ro_cells_frameD : forall W m m' A cs, ro_cells asegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> ro_cells asegs m' A cs.
Proof. intros. eapply ro_cells_transport; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wmono_but (W : list ivl) (m m' : amem) : Prop :=
  forall x : word, outside W (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None.

#[using="Type"] Lemma munch_wmono_but : forall W m m', munch W m m' -> wmono_but W m m'.
Proof. intros W m m' MU x Hx. rewrite (wview_agree asegs m m' x (MU x Hx)). exact (fun H => H). Qed.
#[using="Type"] Lemma wmono_wmono_but : forall W m m', wmono asegs m m' -> wmono_but W m m'.
Proof. intros W m m' WM x _. apply WM. Qed.
#[using="Type"] Lemma wmono_but_refl : forall W m, wmono_but W m m.
Proof. intros W m x _ H; exact H. Qed.
#[using="Type"] Lemma wmono_but_trans : forall W m1 m2 m3, wmono_but W m1 m2 -> wmono_but W m2 m3 -> wmono_but W m1 m3.
Proof. intros W m1 m2 m3 A B x Hx H. apply B; [exact Hx|]. apply A; assumption. Qed.
#[using="Type"] Lemma wmono_but_weaken : forall W W' m m', sub_fp W W' -> wmono_but W m m' -> wmono_but W' m m'.
Proof. intros W W' m m' S H x Hx. apply H. apply S. exact Hx. Qed.
#[using="Type"] Lemma wmono_but_write : forall W m0 m a bs, wmono_but W m0 m -> wmono_but W m0 (write_to_mem m a bs).
Proof. intros W m0 m a bs H x Hx Hw. apply wview_write_mono. apply H; assumption. Qed.
End CANSEC1.

(* [comment removed for export] *)

Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Section WithSegs.
Variable segs : list Segment.

#[using="Type"] Lemma wview_agree : forall m m' (x : word), m' x = m x -> wview segs m' x = wview segs m x.
Proof. intros m m' x E. unfold wview. rewrite E. reflexivity. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wr_at_agree : forall m m' A n,
  wr_at segs m A n -> (forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))) -> wr_at segs m' A n.
Proof.
  intros m m' A n (H0 & H1 & H) E. split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite (wview_agree m m' _ (E i Hi)). apply H. exact Hi.
Qed.

#[using="Type"] Lemma wr_at_transportD : forall W m m' A n,
  wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
  intros W m m' A n WR MU D. (pose proof WR as ndP__; nd_pre ndP__ 3%nat; intros H0 H1 _; nd_post).
  eapply wr_at_agree; [exact WR|]. intros i Hi. apply MU.
  rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia].
Qed.

#[using="Type"] Lemma rw_cells_transportD : forall W m m' A cs,
  rw_cells segs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) ->
  rw_cells segs m' A cs.
Proof.
  intros W m m' A cs [[Hwf Hb] Hw] MU D. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

#[using="Type"] Lemma u8arr_transportD : forall W m m' A bs,
  u8arr segs m A bs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof.
  intros W m m' A bs [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto.
  - eapply wr_at_transportD; eauto.
Qed.

#[using="Type"] Lemma u32arr_transportD : forall W m m' A ws,
  u32arr segs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u32s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

#[using="Type"] Lemma u64arr_transportD : forall W m m' A ws,
  u64arr segs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr segs m' A ws.
Proof.
  intros W m m' A ws [Hb Hw] MU D. split.
  - eapply bytes_at_transport; eauto. rewrite u64s_length, Nat2Z.inj_mul. exact D.
  - eapply wr_at_transportD; eauto.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stk_transportD : forall W m m' lo hi,
  stk segs m lo hi -> munch W m m' -> disjoint_from W lo (hi - lo) -> stk segs m' lo hi.
Proof.
  intros W m m' lo hi (H0 & H1 & H) MU D. split; [exact H0|]. split; [exact H1|].
  intros a Ha.
  assert (E : m' (wa a) = m (wa a)).
  { apply MU. rewrite wa_unsigned by lia. eapply disjoint_outside; [exact D | lia]. }
  destruct (H a Ha) as [WV [b RD]]. split.
  - rewrite (wview_agree m m' _ E). exact WV.
  - exists b. unfold mrd in *. rewrite E. exact RD.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma munch_agree_range : forall W m m' A n i,
  munch W m m' -> disjoint_from W A n -> 0 <= A -> A + n <= 2^64 -> 0 <= i < n ->
  m' (wa (A + i)) = m (wa (A + i)).
Proof.
  intros W m m' A n i MU D H0 H1 Hi. apply MU. rewrite wa_unsigned by lia.
  eapply disjoint_outside; [exact D | lia].
Qed.
End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma junk_frameD : forall W m m' A n, junk_at m A n -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> junk_at m' A n.
Proof.
  intros W m m' A n [bs H] MU D. exists bs.
  pose proof H as H0. destruct H0 as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - assert (bs = []) as -> by (destruct bs; [reflexivity| cbn in L; lia]).
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma fill_frameD : forall W m m' A n v, fill_at m A n v -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> fill_at m' A n v.
Proof.
  intros W m m' A n v H MU D. unfold fill_at in *.
  destruct (Z.lt_ge_cases 0 n).
  - eapply rw_cells_transportD; [exact H | exact MU |]. cbn [cells_size csize]. rewrite Nat.add_0_r.
    rewrite Z2Nat.id by lia. exact (D ltac:(lia)).
  - pose proof H as HH. destruct HH as [[[L _] [B0 [B1 B]]] [W0 [W1 WR]]]. cbn in L, B1, W1.
    replace (Z.to_nat n) with 0%nat in * by lia. cbn [repeat] in *.
    split; [split; [cbn; lia|]|]; unfold bytes_at, wr_at; cbn.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
    + split; [lia|]. split; [lia|]. intros i Hi. lia.
Qed.

#[using="Type"] Lemma cells_frameD : forall W m m' A cs, rw_cells asegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof. intros. eapply rw_cells_transportD; eauto. Qed.

#[using="Type"] Lemma u64arr_frameD : forall W m m' A ws, u64arr asegs m A ws -> munch W m m' ->
  disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof. intros. eapply u64arr_transportD; eauto. Qed.
#[using="Type"] Lemma u32arr_frameD : forall W m m' A ws, u32arr asegs m A ws -> munch W m m' ->
  disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof. intros. eapply u32arr_transportD; eauto. Qed.

#[using="Type"] Lemma azero_frameD : forall W m m' A n, azero m A n -> munch W m m' ->
  (0 < n -> disjoint_from W A n) -> azero m' A n.
Proof.
  intros W m m' A n [Z0 WR] MU D. (pose proof WR as ndP__; nd_pre ndP__ 3%nat; intros W0 W1 _; nd_post).
  assert (E : forall i, 0 <= i < n -> m' (wa (A + i)) = m (wa (A + i))).
  { intros i Hi. eapply munch_agree_range; [exact MU | apply D; lia | lia | lia | lia]. }
  split.
  - intros i Hi. rewrite (E i Hi). apply Z0. exact Hi.
  - eapply wr_at_agree; [exact WR | exact E].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ro_cells_frameD : forall W m m' A cs, ro_cells asegs m A cs -> munch W m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> ro_cells asegs m' A cs.
Proof. intros. eapply ro_cells_transport; eauto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition wmono_but (W : list ivl) (m m' : amem) : Prop :=
  forall x : word, outside W (bv_unsigned x) -> wview asegs m x <> None -> wview asegs m' x <> None.

#[using="Type"] Lemma munch_wmono_but : forall W m m', munch W m m' -> wmono_but W m m'.
Proof. intros W m m' MU x Hx. rewrite (wview_agree asegs m m' x (MU x Hx)). exact (fun H => H). Qed.
#[using="Type"] Lemma wmono_wmono_but : forall W m m', wmono asegs m m' -> wmono_but W m m'.
Proof. intros W m m' WM x _. apply WM. Qed.
#[using="Type"] Lemma wmono_but_refl : forall W m, wmono_but W m m.
Proof. intros W m x _ H; exact H. Qed.
#[using="Type"] Lemma wmono_but_trans : forall W m1 m2 m3, wmono_but W m1 m2 -> wmono_but W m2 m3 -> wmono_but W m1 m3.
Proof. intros W m1 m2 m3 A B x Hx H. apply B; [exact Hx|]. apply A; assumption. Qed.
#[using="Type"] Lemma wmono_but_weaken : forall W W' m m', sub_fp W W' -> wmono_but W m m' -> wmono_but W' m m'.
Proof. intros W W' m m' S H x Hx. apply H. apply S. exact Hx. Qed.
#[using="Type"] Lemma wmono_but_write : forall W m0 m a bs, wmono_but W m0 m -> wmono_but W m0 (write_to_mem m a bs).
Proof. intros W m0 m a bs H x Hx Hw. apply wview_write_mono. apply H; assumption. Qed.
End CANSEC1.
End TwB.
End AFrameD.

(* [comment removed for export] *)
Module ARepQ.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import ExecF.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require Import AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg ABase. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require Export AQConst.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition abatch_addr (L : alayout) (k : Z) : Z := aslot_addr L K_BATCH_CLASS k.

(* [comment removed for export] *)
Definition qhdr (L : alayout) (ch : achunk) (k : Z) : Z :=
  match ch with
  | CPrim c n => aslot_addr L c k + rz_size n - 16
  | CSec mb ms n => mb + PG + rz_size n - 16
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record qbatchc := mkQB {
  qb_slot : Z;         (* [comment removed for export] *)
  qb_ks : list Z       (* [comment removed for export] *)
}.
Record qconc := mkQConc {
  q_loc : list qbatchc;    (* [comment removed for export] *)
  q_glob : list qbatchc;   (* [comment removed for export] *)
  q_ia : bool;             (* [comment removed for export] *)
  q_pend : list (Z * Z)    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Fixpoint qhdrs (L : alayout) (chs : list achunk) (ks : list Z) : list Z :=
  match chs, ks with
  | ch :: chs', k :: ks' => qhdrs L chs' ks' ++ [qhdr L ch k]
  | _, _ => []
  end.

Definition qaddrs (L : alayout) (qs : list qbatchc) : list Z := map (fun q => abatch_addr L (qb_slot q)) qs.
Definition qfirst (L : alayout) (qs : list qbatchc) : Z := hd 0 (qaddrs L qs).
Definition qlast (L : alayout) (qs : list qbatchc) : Z := List.last (qaddrs L qs) 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition abatch_cells (L : alayout) (m : amem) (b : abatch) (q : qbatchc) (nx : Z) : Prop :=
  let B := abatch_addr L (qb_slot q) in
     rw_cells asegs m B [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]
  /\ u64arr asegs m (B + 24) (map (Z_to_bv 64) (qhdrs L (b_chunks b) (qb_ks q)))
  /\ junk_at m (B + 24 + 8 * b_count b) (Q_BATCH_BYTES - 24 - 8 * b_count b)
  /\ b_count b = Z.of_nat (length (b_chunks b)) /\ length (qb_ks q) = length (b_chunks b)
  /\ 0 <= b_count b <= Q_BATCH.

(* [comment removed for export] *)
Fixpoint abatches_to (L : alayout) (m : amem) (bs : list abatch) (qs : list qbatchc) (nxt : Z) : Prop :=
  match bs, qs with
  | [], [] => True
  | b :: bs', q :: qs' => abatch_cells L m b q (hd nxt (qaddrs L qs')) /\ abatches_to L m bs' qs' nxt
  | _, _ => False
  end.
Definition abatches (L : alayout) (m : amem) (bs : list abatch) (qs : list qbatchc) : Prop := abatches_to L m bs qs 0.

(* [comment removed for export] *)
Definition aqcache (L : alayout) (m : amem) (C : Z) (bs : list abatch) (qs : list qbatchc) (bytes : Z) : Prop :=
     rw_cells asegs m C [C8 (Z_to_bv 64 (Z.of_nat (length bs))); C8 (Z_to_bv 64 (qfirst L qs));
                        C8 (Z_to_bv 64 (qlast L qs)); C8 (Z_to_bv 64 bytes)]
  /\ abatches L m bs qs.

(* [comment removed for export] *)
Definition aquar_glob_const (m : amem) : Prop :=
     rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)]
  /\ rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition aintal (ia : bool) (m : amem) : Prop :=
     rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE)
  /\ (ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint qentries (bs : list abatch) (qs : list qbatchc) : list (achunk * Z) :=
  match bs, qs with
  | b :: bs', q :: qs' => combine (b_chunks b) (qb_ks q) ++ qentries bs' qs'
  | _, _ => []
  end.

Definition qentry_ok (X : aconc) (e : achunk * Z) : Prop :=
  match fst e with
  | CPrim c n => exists b1 ctx, In (mkXBusy c (snd e) n BQuar b1 ctx) (x_busy X)
  | CSec _ _ _ => True          (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition qprim_ids (es : list (achunk * Z)) : list (Z * Z) :=
  flat_map (fun e => match fst e with CPrim c _ => [(c, snd e)] | CSec _ _ _ => [] end) es.

Definition qcoupled (L : alayout) (st : astate) (X : aconc) (Q : qconc) : Prop :=
  let es := qentries (a_qloc st) (q_loc Q) ++ qentries (a_qglob st) (q_glob Q) in
  let bslots := map qb_slot (q_loc Q ++ q_glob Q) in
     length (q_loc Q) = length (a_qloc st) /\ length (q_glob Q) = length (a_qglob st)
  /\ Forall (qentry_ok X) es
  /\ List.NoDup (qprim_ids es ++ q_pend Q) /\ List.NoDup bslots
  (* [comment removed for export] *)
  /\ (forall k, In k bslots <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k)
  /\ (forall c k, In (c, k) (qprim_ids es ++ q_pend Q) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c /\ xb_slot b = k)
  /\ Forall (fun k => 0 <= k) bslots.

(* [comment removed for export] *)
Definition qnum (st : astate) : Prop :=
     a_qloc_bytes st = batches_bytes (a_qloc st) /\ a_qglob_bytes st = batches_bytes (a_qglob st)
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st ++ a_qglob st)
  /\ a_qloc_bytes st <= Q_CACHE /\ a_qglob_bytes st <= Q_MAX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AQUAR_at (L : alayout) (st : astate) (X : aconc) (Q : qconc) (m : amem) : Prop :=
     aquar_glob_const m
  /\ aqcache L m (aq_tcache L) (a_qloc st) (q_loc Q) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (q_glob Q) (a_qglob_bytes st)
  /\ aintal (q_ia Q) m
  /\ qcoupled L st X Q
  /\ qnum st.

Definition AQUAR (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
  exists Q, AQUAR_at L st X Q m.

(* [comment removed for export] *)
Definition aquar_fp (L : alayout) (st : astate) (X : aconc) (a : Z) : Prop :=
     (aq_tcache L <= a < aq_tcache L + 32)
  \/ (AQ_MAX <= a < AQ_MAX + 24) \/ (AQ_MUTEX <= a < AQ_MUTEX + 4) \/ (AQ_GCACHE <= a < AQ_GCACHE + 32)
  \/ (AIA_BASE <= a < AIA_BASE + AIA_SIZE) \/ (AIA_FLAG <= a < AIA_FLAG + 4)
  \/ (exists b, In b (x_busy X) /\ xb_st b = BBatch /\ abatch_addr L (xb_slot b) <= a < abatch_addr L (xb_slot b) + Q_BATCH_BYTES).

(* [comment removed for export] *)
Definition qconc0 : qconc := mkQConc [] [] false [].
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.MState OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Mem OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Cells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Exec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Frame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.ExecF.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA.AsanEmbed.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AQConst.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition abatch_addr (L : alayout) (k : Z) : Z := aslot_addr L K_BATCH_CLASS k.

(* [comment removed for export] *)
Definition qhdr (L : alayout) (ch : achunk) (k : Z) : Z :=
  match ch with
  | CPrim c n => aslot_addr L c k + rz_size n - 16
  | CSec mb ms n => mb + PG + rz_size n - 16
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Record qbatchc := mkQB {
  qb_slot : Z;         (* [comment removed for export] *)
  qb_ks : list Z       (* [comment removed for export] *)
}.
Record qconc := mkQConc {
  q_loc : list qbatchc;    (* [comment removed for export] *)
  q_glob : list qbatchc;   (* [comment removed for export] *)
  q_ia : bool;             (* [comment removed for export] *)
  q_pend : list (Z * Z)    (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Fixpoint qhdrs (L : alayout) (chs : list achunk) (ks : list Z) : list Z :=
  match chs, ks with
  | ch :: chs', k :: ks' => qhdrs L chs' ks' ++ [qhdr L ch k]
  | _, _ => []
  end.

Definition qaddrs (L : alayout) (qs : list qbatchc) : list Z := map (fun q => abatch_addr L (qb_slot q)) qs.
Definition qfirst (L : alayout) (qs : list qbatchc) : Z := hd 0 (qaddrs L qs).
Definition qlast (L : alayout) (qs : list qbatchc) : Z := List.last (qaddrs L qs) 0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition abatch_cells (L : alayout) (m : amem) (b : abatch) (q : qbatchc) (nx : Z) : Prop :=
  let B := abatch_addr L (qb_slot q) in
     rw_cells asegs m B [C8 (Z_to_bv 64 nx); C8 (Z_to_bv 64 (b_size b)); C8 (Z_to_bv 64 (b_count b))]
  /\ u64arr asegs m (B + 24) (map (Z_to_bv 64) (qhdrs L (b_chunks b) (qb_ks q)))
  /\ junk_at m (B + 24 + 8 * b_count b) (Q_BATCH_BYTES - 24 - 8 * b_count b)
  /\ b_count b = Z.of_nat (length (b_chunks b)) /\ length (qb_ks q) = length (b_chunks b)
  /\ 0 <= b_count b <= Q_BATCH.

(* [comment removed for export] *)
Fixpoint abatches_to (L : alayout) (m : amem) (bs : list abatch) (qs : list qbatchc) (nxt : Z) : Prop :=
  match bs, qs with
  | [], [] => True
  | b :: bs', q :: qs' => abatch_cells L m b q (hd nxt (qaddrs L qs')) /\ abatches_to L m bs' qs' nxt
  | _, _ => False
  end.
Definition abatches (L : alayout) (m : amem) (bs : list abatch) (qs : list qbatchc) : Prop := abatches_to L m bs qs 0.

(* [comment removed for export] *)
Definition aqcache (L : alayout) (m : amem) (C : Z) (bs : list abatch) (qs : list qbatchc) (bytes : Z) : Prop :=
     rw_cells asegs m C [C8 (Z_to_bv 64 (Z.of_nat (length bs))); C8 (Z_to_bv 64 (qfirst L qs));
                        C8 (Z_to_bv 64 (qlast L qs)); C8 (Z_to_bv 64 bytes)]
  /\ abatches L m bs qs.

(* [comment removed for export] *)
Definition aquar_glob_const (m : amem) : Prop :=
     rw_cells asegs m AQ_MAX [C8 (Z_to_bv 64 Q_MAX); C8 (Z_to_bv 64 Q_MIN); C8 (Z_to_bv 64 Q_CACHE)]
  /\ rw_cells asegs m AQ_MUTEX [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)].

(* [comment removed for export] *)
Definition aintal (ia : bool) (m : amem) : Prop :=
     rw_cells asegs m AIA_FLAG [C1 (Z_to_bv 8 (if ia then 1 else 0)); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ stk asegs m AIA_BASE (AIA_BASE + AIA_SIZE)
  /\ (ia = true -> forall j, 0 <= j < AIA_MAP1_LEN / 8 -> bytes_at asegs m (AIA_MAP1 + 8 * j) (le8 (Z_to_bv 64 0))).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint qentries (bs : list abatch) (qs : list qbatchc) : list (achunk * Z) :=
  match bs, qs with
  | b :: bs', q :: qs' => combine (b_chunks b) (qb_ks q) ++ qentries bs' qs'
  | _, _ => []
  end.

Definition qentry_ok (X : aconc) (e : achunk * Z) : Prop :=
  match fst e with
  | CPrim c n => exists b1 ctx, In (mkXBusy c (snd e) n BQuar b1 ctx) (x_busy X)
  | CSec _ _ _ => True          (* [comment removed for export] *)
  end.

(* [comment removed for export] *)
Definition qprim_ids (es : list (achunk * Z)) : list (Z * Z) :=
  flat_map (fun e => match fst e with CPrim c _ => [(c, snd e)] | CSec _ _ _ => [] end) es.

Definition qcoupled (L : alayout) (st : astate) (X : aconc) (Q : qconc) : Prop :=
  let es := qentries (a_qloc st) (q_loc Q) ++ qentries (a_qglob st) (q_glob Q) in
  let bslots := map qb_slot (q_loc Q ++ q_glob Q) in
     length (q_loc Q) = length (a_qloc st) /\ length (q_glob Q) = length (a_qglob st)
  /\ Forall (qentry_ok X) es
  /\ List.NoDup (qprim_ids es ++ q_pend Q) /\ List.NoDup bslots
  (* [comment removed for export] *)
  /\ (forall k, In k bslots <-> exists b, In b (x_busy X) /\ xb_st b = BBatch /\ xb_class b = K_BATCH_CLASS /\ xb_slot b = k)
  /\ (forall c k, In (c, k) (qprim_ids es ++ q_pend Q) <-> exists b, In b (x_busy X) /\ xb_st b = BQuar /\ xb_class b = c /\ xb_slot b = k)
  /\ Forall (fun k => 0 <= k) bslots.

(* [comment removed for export] *)
Definition qnum (st : astate) : Prop :=
     a_qloc_bytes st = batches_bytes (a_qloc st) /\ a_qglob_bytes st = batches_bytes (a_qglob st)
  /\ Forall (fun b => Q_BATCH_BYTES <= b_size b) (a_qloc st ++ a_qglob st)
  /\ a_qloc_bytes st <= Q_CACHE /\ a_qglob_bytes st <= Q_MAX.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AQUAR_at (L : alayout) (st : astate) (X : aconc) (Q : qconc) (m : amem) : Prop :=
     aquar_glob_const m
  /\ aqcache L m (aq_tcache L) (a_qloc st) (q_loc Q) (a_qloc_bytes st)
  /\ aqcache L m AQ_GCACHE (a_qglob st) (q_glob Q) (a_qglob_bytes st)
  /\ aintal (q_ia Q) m
  /\ qcoupled L st X Q
  /\ qnum st.

Definition AQUAR (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
  exists Q, AQUAR_at L st X Q m.

(* [comment removed for export] *)
Definition aquar_fp (L : alayout) (st : astate) (X : aconc) (a : Z) : Prop :=
     (aq_tcache L <= a < aq_tcache L + 32)
  \/ (AQ_MAX <= a < AQ_MAX + 24) \/ (AQ_MUTEX <= a < AQ_MUTEX + 4) \/ (AQ_GCACHE <= a < AQ_GCACHE + 32)
  \/ (AIA_BASE <= a < AIA_BASE + AIA_SIZE) \/ (AIA_FLAG <= a < AIA_FLAG + 4)
  \/ (exists b, In b (x_busy X) /\ xb_st b = BBatch /\ abatch_addr L (xb_slot b) <= a < abatch_addr L (xb_slot b) + Q_BATCH_BYTES).

(* [comment removed for export] *)
Definition qconc0 : qconc := mkQConc [] [] false [].
End CANSEC1.
End TwB.
End ARepQ.
