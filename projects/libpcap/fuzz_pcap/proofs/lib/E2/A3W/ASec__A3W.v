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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require ExecF ITreeA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.SpecA Require AsanCtrl AsanEmbed.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require RunDraw.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require NDestr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDietF.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module ASec.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_afree_s__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_apoison__A3W. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
Definition sec_live (st : astate) (ch : achunk) : Prop := exists p, (a_live st) !! p = Some ch.
Definition SEC_MAGIC : Z := 0xCC6E96B9CC6E96B9.  (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_disjoint (cs : list achunk) : Prop :=
  List.NoDup cs /\
  forall ci cj, In ci cs -> In cj cs -> ci <> cj ->
    sec_mb ci + sec_ms ci <= sec_mb cj \/ sec_mb cj + sec_ms cj <= sec_mb ci.
#[using="Type"] Lemma sec_disjoint_nil : sec_disjoint [].
Proof. split; [constructor| intros ci cj [] ]. Qed.
#[using="Type"] Lemma sec_disjoint_perm : forall cs cs', Permutation cs cs' -> sec_disjoint cs -> sec_disjoint cs'.
Proof.
  intros cs cs' P [ND D]. split; [eapply Permutation_NoDup; [exact P| exact ND]|].
  intros ci cj Hi Hj NE. apply D; [| | exact NE]; (eapply Permutation_in; [apply Permutation_sym; exact P| assumption]).
Qed.

Definition asec_wf (L : alayout) (st : astate) (cs : list achunk) : Prop :=
     alayout_ok L                                                          (* [comment removed for export] *)
  /\ a_ptr_array st = al_ptr_array L
  /\ (a_nres st mod 16384 = 0 /\ 0 <= a_nres st <= 1048576) /\ Z.of_nat (length cs) = a_nsec st /\ 0 <= a_nsec st <= a_nres st
      (* [comment removed for export] *)
  /\ Forall (sec_wf1 L) cs /\ sec_disjoint cs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_user_shadow (lv : bool) (n : Z) : list byte :=
  if lv then block_shadow_bytes n else repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)).

#[using="Type"] Lemma granules_eq : forall n, 0 <= n -> granules n = shlen n + (if n mod 8 =? 0 then 0 else 1).
Proof.
  intros n N. unfold granules, shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma sec_user_shadow_length : forall lv n, 0 <= n -> length (sec_user_shadow lv n) = Z.to_nat (granules n).
Proof.
  intros lv n N. unfold sec_user_shadow. destruct lv; [| apply repeat_length].
  unfold block_shadow_bytes. rewrite length_app, repeat_length, granules_eq by lia.
  pose proof (proj2 (Z.shiftr_nonneg n 3) N) as S. unfold shlen in *. destruct (n mod 8 =? 0); cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Definition asec_chunk (m : amem) (ch : achunk) (idx : Z) (lv : bool) : Prop :=
  match ch with
  | CSec mb ms n =>
      let res := mb + 4096 in let ub := mb + SEC_UOFF in
         rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)]
      /\ junk_at m (mb + 32) (4096 - 32)
      /\ rw_cells asegs m res [C8 (Z_to_bv 64 SEC_MAGIC); C8 (Z_to_bv 64 (ub - 16))]
      /\ junk_at m (res + 16) (2048 - 32)
      /\ (exists b1 ctx, rw_cells asegs m (ub - 16) [C1 (Z_to_bv 8 (if lv then 2 else 3)); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0);
                                                 C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
                        /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31)
      /\ junk_at m ub (ms - SEC_UOFF)
      /\ fill_at m (shad mb) 768 0xfa
      /\ rw_cells asegs m (shad ub) [CB (Z.to_nat (granules n)) (sec_user_shadow lv n)]
      /\ fill_at m (shad ub + granules n) (ms / 8 - 768 - granules n) 0xfa
  | CPrim _ _ => False
  end.

(* [comment removed for export] *)
Definition asec_arr (L : alayout) (st : astate) (cs : list achunk) (m : amem) : Prop :=
  exists order : list achunk,
       Permutation order cs
    /\ u64arr asegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
    /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
    /\ (forall i ch, nth_error order i = Some ch ->
          exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat i) lv).

(* [comment removed for export] *)
Definition asec_inst (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xaafe8 [C8 (Z_to_bv 64 (al_ptr_array L))]        (* [comment removed for export] *)
  /\ (exists srt : byte, rw_cells asegs m 0xab018 [C1 srt])              (* [comment removed for export] *)
  /\ junk_at m 0xab020 32                                                (* [comment removed for export] *)
  /\ junk_at m 0xab040 512                                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab241 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ junk_at m 0xab258 16.                                               (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition astartup_hulls (L : alayout) : list (Z * Z) :=
  let V := al_V L in
  [(4096 * V 584%nat, 4096 * V 584%nat + 4096); (4096 * V 503%nat, 4096 * V 503%nat + 4096);
   (al_store L, al_store L + 8388608); (al_nodes L, al_nodes L + 1048576); (al_fake L, al_fake L + 11571200);
   (al_dtls L, al_dtls L + 4096); (4096 * V 258%nat, 4096 * V 258%nat + 4096); (al_ctx L, al_ctx L + 65536);
   (al_t L, al_t L + 4096); (al_res L, al_res L + 137439023104);
   (4096 * V 220%nat, 4096 * V 220%nat + 0x38e000); (4096 * V 91%nat, 4096 * V 91%nat + 0x10000);
   (al_ptr_array L, al_ptr_array L + 8388608);
   (ATPv + -200, ATPv + 312)].      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ashz (L : alayout) (cs : list achunk) (m : amem) : Prop :=
  forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
    Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
    Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) cs ->
    m (wa (shad x)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition aprim0 (L : alayout) (m : amem) : Prop := azero m (shad (al_space_beg L)) (shlen K_REGION).

Definition ASECc (cs : list achunk) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
  asec_wf L st cs /\ asec_arr L st cs m /\ asec_inst L m /\ aprim0 L m /\ ashz L cs m.

(* [comment removed for export] *)
Definition ASEC_of (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop := ASECc (sec_chunks_of st) L st X m.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_afree_s__A3W.F_ammap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_apoison__A3W.F_apoison.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
Definition sec_live (st : astate) (ch : achunk) : Prop := exists p, (a_live st) !! p = Some ch.
Definition SEC_MAGIC : Z := 0xCC6E96B9CC6E96B9.  (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_disjoint (cs : list achunk) : Prop :=
  List.NoDup cs /\
  forall ci cj, In ci cs -> In cj cs -> ci <> cj ->
    sec_mb ci + sec_ms ci <= sec_mb cj \/ sec_mb cj + sec_ms cj <= sec_mb ci.
#[using="Type"] Lemma sec_disjoint_nil : sec_disjoint [].
Proof. split; [constructor| intros ci cj [] ]. Qed.
#[using="Type"] Lemma sec_disjoint_perm : forall cs cs', Permutation cs cs' -> sec_disjoint cs -> sec_disjoint cs'.
Proof.
  intros cs cs' P [ND D]. split; [eapply Permutation_NoDup; [exact P| exact ND]|].
  intros ci cj Hi Hj NE. apply D; [| | exact NE]; (eapply Permutation_in; [apply Permutation_sym; exact P| assumption]).
Qed.

Definition asec_wf (L : alayout) (st : astate) (cs : list achunk) : Prop :=
     alayout_ok L                                                          (* [comment removed for export] *)
  /\ a_ptr_array st = al_ptr_array L
  /\ (a_nres st mod 16384 = 0 /\ 0 <= a_nres st <= 1048576) /\ Z.of_nat (length cs) = a_nsec st /\ 0 <= a_nsec st <= a_nres st
      (* [comment removed for export] *)
  /\ Forall (sec_wf1 L) cs /\ sec_disjoint cs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_user_shadow (lv : bool) (n : Z) : list byte :=
  if lv then block_shadow_bytes n else repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)).

#[using="Type"] Lemma granules_eq : forall n, 0 <= n -> granules n = shlen n + (if n mod 8 =? 0 then 0 else 1).
Proof.
  intros n N. unfold granules, shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia.
Qed.
#[using="Type"] Lemma sec_user_shadow_length : forall lv n, 0 <= n -> length (sec_user_shadow lv n) = Z.to_nat (granules n).
Proof.
  intros lv n N. unfold sec_user_shadow. destruct lv; [| apply repeat_length].
  unfold block_shadow_bytes. rewrite length_app, repeat_length, granules_eq by lia.
  pose proof (proj2 (Z.shiftr_nonneg n 3) N) as S. unfold shlen in *. destruct (n mod 8 =? 0); cbn [length]; lia.
Qed.

(* [comment removed for export] *)
Definition asec_chunk (m : amem) (ch : achunk) (idx : Z) (lv : bool) : Prop :=
  match ch with
  | CSec mb ms n =>
      let res := mb + 4096 in let ub := mb + SEC_UOFF in
         rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)]
      /\ junk_at m (mb + 32) (4096 - 32)
      /\ rw_cells asegs m res [C8 (Z_to_bv 64 SEC_MAGIC); C8 (Z_to_bv 64 (ub - 16))]
      /\ junk_at m (res + 16) (2048 - 32)
      /\ (exists b1 ctx, rw_cells asegs m (ub - 16) [C1 (Z_to_bv 8 (if lv then 2 else 3)); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0);
                                                 C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
                        /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31)
      /\ junk_at m ub (ms - SEC_UOFF)
      /\ fill_at m (shad mb) 768 0xfa
      /\ rw_cells asegs m (shad ub) [CB (Z.to_nat (granules n)) (sec_user_shadow lv n)]
      /\ fill_at m (shad ub + granules n) (ms / 8 - 768 - granules n) 0xfa
  | CPrim _ _ => False
  end.

(* [comment removed for export] *)
Definition asec_arr (L : alayout) (st : astate) (cs : list achunk) (m : amem) : Prop :=
  exists order : list achunk,
       Permutation order cs
    /\ u64arr asegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
    /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
    /\ (forall i ch, nth_error order i = Some ch ->
          exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat i) lv).

(* [comment removed for export] *)
Definition asec_inst (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xab3e8 [C8 (Z_to_bv 64 (al_ptr_array L))]        (* [comment removed for export] *)
  /\ (exists srt : byte, rw_cells asegs m 0xab418 [C1 srt])              (* [comment removed for export] *)
  /\ junk_at m 0xab420 32                                                (* [comment removed for export] *)
  /\ junk_at m 0xab440 512                                               (* [comment removed for export] *)
  /\ rw_cells asegs m 0xab641 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ junk_at m 0xab658 16.                                               (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition astartup_hulls (L : alayout) : list (Z * Z) :=
  let V := al_V L in
  [(4096 * V 584%nat, 4096 * V 584%nat + 4096); (4096 * V 503%nat, 4096 * V 503%nat + 4096);
   (al_store L, al_store L + 8388608); (al_nodes L, al_nodes L + 1048576); (al_fake L, al_fake L + 11571200);
   (al_dtls L, al_dtls L + 4096); (4096 * V 258%nat, 4096 * V 258%nat + 4096); (al_ctx L, al_ctx L + 65536);
   (al_t L, al_t L + 4096); (al_res L, al_res L + 137439023104);
   (4096 * V 220%nat, 4096 * V 220%nat + 0x38e000); (4096 * V 91%nat, 4096 * V 91%nat + 0x10000);
   (al_ptr_array L, al_ptr_array L + 8388608);
   (ATPv + -200, ATPv + 312)].      (* [comment removed for export] *)
(* [comment removed for export] *)
Definition ashz (L : alayout) (cs : list achunk) (m : amem) : Prop :=
  forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
    Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
    Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) cs ->
    m (wa (shad x)) = Some (Z_to_bv 8 0).

(* [comment removed for export] *)
Definition aprim0 (L : alayout) (m : amem) : Prop := azero m (shad (al_space_beg L)) (shlen K_REGION).

Definition ASECc (cs : list achunk) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
  asec_wf L st cs /\ asec_arr L st cs m /\ asec_inst L m /\ aprim0 L m /\ ashz L cs m.

(* [comment removed for export] *)
Definition ASEC_of (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop := ASECc (sec_chunks_of st) L st X m.

End CANSEC1.
End TwB.
End ASec.

(* [comment removed for export] *)
Module ASecFrame.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.
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
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma su_disjoint : forall L W A k,
  sec_untouched L W -> Forall (fun iv => fst iv < snd iv) W -> 0 < k ->
  (forall a, A <= a < A + k -> aknown L a -> False) ->
  disjoint_from W A k.
Proof.
  intros L W A k SU NE Hk CL. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion SU as [|x l Hx Hl]; subst. inversion NE as [|x' l' Hn Hnl]; subst. split; [| apply IH; [exact Hl| exact Hnl]].
  cbn [fst snd] in Hx, Hn.
  destruct (Z_lt_le_dec lo (A + k)) as [L1|L1]; [| left; lia].
  destruct (Z_lt_le_dec A hi) as [L2|L2]; [| right; lia].
  exfalso. apply (CL (Z.max A lo)); [lia|]. apply Hx. lia.
Qed.

#[using="Type"] Lemma sec_untouched_filter : forall L W, sec_untouched L W -> sec_untouched L (List.filter nonempty W).
Proof. intros L W SU. unfold sec_untouched in *. rewrite Forall_forall in SU |- *. intros iv Hin. apply SU. apply List.filter_In in Hin. tauto. Qed.
#[using="Type"] Lemma nonempty_filter : forall W, Forall (fun iv : Z * Z => fst iv < snd iv) (List.filter nonempty W).
Proof. intros W. rewrite Forall_forall. intros [lo hi] Hin. apply List.filter_In in Hin. destruct Hin as [_ NE]. unfold nonempty in NE. cbn [fst snd] in *. apply Z.ltb_lt. exact NE. Qed.

Section Geo.
Variable L : alayout.
Hypothesis ALO : alayout_ok L.

(* [comment removed for export] *)
Local Ltac layout :=
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 _; nd_post); pose proof (ao_space L ALO) as RSP; pose proof (ao_res_hi L ALO) as ORH;
  (pose proof (ao_t L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OT1 OT2 OTs OTi; nd_post);
  let OC := fresh in pose proof (ao_ctx L ALO) as OC; pose proof (aobj_img _ _ OC ltac:(lia)) as OCI; (nd_pre OC 5%nat; intros _ OC1 OC2 OCs _; nd_post);
  (pose proof (ao_res L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OR1 OR2 _ _; nd_post);
  let ON := fresh in pose proof (ao_nodes L ALO) as ON; pose proof (aobj_img _ _ ON ltac:(lia)) as ONI; (nd_pre ON 5%nat; intros _ ON1 ON2 ONs _; nd_post);
  let OS := fresh in pose proof (ao_store L ALO) as OS; pose proof (aobj_img _ _ OS ltac:(lia)) as OSI; (nd_pre OS 5%nat; intros _ OS1 OS2 OSs _; nd_post);
  let OFK := fresh in pose proof (ao_fake L ALO) as OFK; pose proof (aobj_img _ _ OFK ltac:(lia)) as OFI; (nd_pre OFK 5%nat; intros OF0 OF1 OF2 OFs _; nd_post);
  (pose proof (ao_dtls L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OD1 OD2 ODs ODi; nd_post);
  let OP := fresh in pose proof (ao_ptr L ALO) as OP; pose proof (aobj_img _ _ OP ltac:(lia)) as OPI; (nd_pre OP 5%nat; intros _ OP1 OP2 OPs _; nd_post);
  pose proof atop_range as ATR; pose proof ATOP_al16 as ATA;
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in SP2, SP3; change (2^37) with 137438953472 in SP2;
  unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *.

(* [comment removed for export] *)
#[using="tlsI ALO"] Lemma clear_inst : forall a, AINSTANCE + 72 <= a < AINSTANCE + 728 -> aknown L a -> False.
Proof.
  intros a Ha K. layout.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha OF1 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OTi OCI OR1 ORH ONI OSI OFI ODi ATR ATA SP1 SP2. lia.
Qed.

(* [comment removed for export] *)
#[using="tlsI ALO"] Lemma clear_ptr : forall a, al_ptr_array L <= a < al_ptr_array L + 8388608 -> aknown L a -> False.
Proof.
  intros a Ha K. layout.
  pose proof (ad_t_ptr L ALO) as X1. pose proof (ad_ctx_ptr L ALO) as X2. pose proof (ad_ptr_res L ALO) as X3. pose proof (ad_nodes_ptr L ALO) as X4.
  pose proof (ad_store_ptr L ALO) as X5. pose proof (ad_fake_ptr L ALO) as X6. pose proof (ad_dtls_ptr L ALO) as X7.
  unfold adisj, aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha OPI OPs SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 OPs OP2 ATR SP2. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha OF1 OF2 OPs ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OPs OP2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OP2 X1 X2 X3 X4 X5 X6 X7 RSP SP1 SP2 ATR ATA. lia.
Qed.

(* [comment removed for export] *)
#[using="ALO"] Lemma clear_chunk : forall mb ms n a, sec_wf1 L (CSec mb ms n) -> mb <= a < mb + ms -> aknown L a -> False.
Proof.
  intros mb ms n a WF1 Ha K. cbn [sec_wf1] in WF1. (nd_pre WF1 7%nat; intros G1 G2 G3 G4 G5 G6 (Qt & Qc & Qr & Qp & Qn & Qs & Qf & Qd); nd_post).
  layout. unfold ablk in G2.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha G2 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 G2 G3 ATR SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OF1 OF2 G2 G3 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha G2 G3 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha G3 Qt Qc Qr Qn Qs Qf Qd RSP SP1 SP2 ATR ATA. lia.
Qed.

(* [comment removed for export] *)
#[using="ALO"] Lemma clear_chunk_shadow : forall mb ms n a, sec_wf1 L (CSec mb ms n) -> shad mb <= a < shad mb + ms / 8 -> aknown L a -> False.
Proof.
  intros mb ms n a WF1 Ha K. cbn [sec_wf1] in WF1. (nd_pre WF1 7%nat; intros G1 G2 G3 G4 G5 G6 (Qt & Qc & Qr & Qp & Qn & Qs & Qf & Qd); nd_post).
  (pose proof (sec_facts n ltac:(lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ MSM MSB; nd_post). rewrite <- G4 in MSM, MSB.
  layout. unfold ablk in G2.
  assert (MB8 : mb mod 8 = 0) by (clear -G1; Z.div_mod_to_equations; lia).
  assert (MS8 : ms mod 8 = 0) by (clear -MSM; Z.div_mod_to_equations; lia).
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. rewrite !shad_div in K. rewrite !shad_div in Ha. unfold ASHOFF in K, Ha.
  destruct K as [K|[K|[K|[K|K]]]].
  - (* [comment removed for export] *)
    clear -K Ha G2 G3 MSB ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha MB8 MS8 MSB Qr RSP SP3 OR1 ORH G2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha MB8 MS8 MSB Qf OF0 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha MB8 MS8 MSB G3 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha G2 G3 MSB MB8 MS8 ATR OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 SP1 SP2. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
#[using="tlsI ALO"] Lemma clear_prim0 : forall a, shad (al_space_beg L) <= a < shad (al_space_beg L) + shlen K_REGION -> aknown L a -> False.
Proof.
  intros a Ha K. layout. pose proof (ad_fake_res L ALO) as DFR.
  unfold adisj, aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_REGION in *. change (2^32) with 4294967296 in Ha.
  rewrite !shad_div, shlen_div in Ha. rewrite !shad_div in K. unfold ASHOFF in K, Ha.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha DFR RSP OF0 SP3 OR1 ORH SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP2 SP1 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 ATR ATA. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
#[using="ALO"] Lemma clear_free_shadow : forall x,
  (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
  Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
  aknown L (shad x) -> False.
Proof.
  intros x Hx HF K. unfold astartup_hulls in HF.
  repeat (apply Forall_cons_iff in HF; destruct HF as [?H HF]). cbn [fst snd] in *.
  layout. unfold K_HIGH_MEM in Hx.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Hx ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx H8 RSP SP3 OR1 ORH ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx H3 OF0 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Hx ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
Qed.
End Geo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
Variables (L : alayout) (W0 : list (Z * Z)) (m m' : amem).
Hypothesis MU0 : munch W0 m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis SU0 : sec_untouched L W0.
Let W := List.filter nonempty W0.
Let MU : munch W m m' := munch_filter_nonempty W0 m m' MU0.
Let SU : sec_untouched L W := sec_untouched_filter L W0 SU0.
Let NE : Forall (fun iv => fst iv < snd iv) W := nonempty_filter W0.

Section WithLayout.
Hypothesis ALO : alayout_ok L.
#[using="rc tlsI L SU0 SU NE ALO"] Lemma D_inst : forall A k, AINSTANCE + 72 <= A -> A + k <= AINSTANCE + 728 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_inst L ALO). lia. Qed.
#[using="rc tlsI SU0 SU NE ALO"] Lemma D_ptr : forall A k, al_ptr_array L <= A -> A + k <= al_ptr_array L + 8388608 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_ptr L ALO). lia. Qed.
#[using="SU0 SU NE ALO"] Lemma D_chunk : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k.
Proof. intros mb ms n A k WF1 H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_chunk L ALO mb ms n); [exact WF1| lia]. Qed.
#[using="SU0 SU NE ALO"] Lemma D_shadow : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k.
Proof. intros mb ms n A k WF1 H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_chunk_shadow L ALO mb ms n); [exact WF1| lia]. Qed.

(* [comment removed for export] *)
#[using="W0 MU0 WM SU0 W MU SU NE ALO"] Lemma asec_chunk_frame : forall mb ms n idx lv,
  sec_wf1 L (CSec mb ms n) -> asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros mb ms n idx lv WF1 CH. pose proof WF1 as WF0. cbn [sec_wf1] in WF0. (nd_pre WF0 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post).
  (pose proof (sec_facts n ltac:(lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ RSE RSR _ NSE _ MSR MSM _; nd_post). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  (nd_pre GR 3%nat; intros GR1 GR2 GR3; nd_post).
  cbn [asec_chunk] in CH |- *. (nd_pre CH 9%nat; intros H1 H2 H3 H4 (b1 & ctx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1 POS; lia].
Qed.
End WithLayout.

#[using="W0 MU0 WM SU0 W MU SU NE"] Theorem asec_frame : forall st st' X X',
  ASEC_of L st X m -> sec_same st st' -> ASEC_of L st' X' m'.
Proof.
  intros st st' X X' (WFS & ARR & INST & PZ & SHZ) (EN & ER & EP & EL & PERM).
  unfold ASEC_of, ASECc.
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post).
  assert (ALLSEC : forall ch, In ch (sec_chunks_of st) -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    unfold asec_wf. rewrite EP, ER, EN. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [| split; [exact WB| split]].
    + rewrite (Permutation_length PERM). exact WL.
    + rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [exact PERM| exact Hin].
    + eapply sec_disjoint_perm; [apply Permutation_sym; exact PERM| exact WD].
  - (* [comment removed for export] *)
    (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PERM]|].
    split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply (D_ptr ALO); cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply (D_ptr ALO); clear -POS WB WR; lia.
    + intros i ch Hi. (nd_pre (PER i ch Hi) 3%nat; intros lv LV CH; nd_post).
      assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      (nd_pre (ALLSEC ch Hin) 4%nat; intros mb ms n ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into W1).
      exists lv. split; [| eapply asec_chunk_frame; [exact ALO| exact W1| exact CH]].
      rewrite LV. unfold sec_live. split; intros [p Hp]; exists p; [apply (proj2 (EL p mb ms n)); exact Hp| apply (proj1 (EL p mb ms n)); exact Hp].
  - (* [comment removed for export] *)
    (nd_pre INST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    eapply junk_frame; [exact I6| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia].
  - (* [comment removed for export] *)
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
    apply (su_disjoint L); [exact SU| exact NE| exact POS|]. intros a Ha. apply (clear_prim0 L ALO). exact Ha.
  - (* [comment removed for export] *)
    intros x Hx HF HC.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; pose proof atop_range as ATR; clear -Hx ATR; Z.div_mod_to_equations; lia).
    assert (HC0 : Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) (sec_chunks_of st)).
    { rewrite Forall_forall in HC |- *. intros ch Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]. }
    rewrite <- (SHZ x Hx HF HC0). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.
End Frame.

(* [comment removed for export] *)
#[using="Type"] Theorem asec_hs_frame : forall L st st' X X' m m' W,
  ASEC_of L st X m -> munch W m m' -> wmono asegs m m' -> sec_untouched L W -> sec_same st st' -> ASEC_of L st' X' m'.
Proof. intros L st st' X X' m m' W HS MU WM SU SS. eapply (asec_frame L W m m' MU WM SU); [exact HS| exact SS]. Qed.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.LibA.RunDraw. Local Ltac Zify.zify_pre_hook ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB.twm_hook_1. Local Ltac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Step.addr_diff E A ::= OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKit2.TwB.twm_hook_1 E A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma su_disjoint : forall L W A k,
  sec_untouched L W -> Forall (fun iv => fst iv < snd iv) W -> 0 < k ->
  (forall a, A <= a < A + k -> aknown L a -> False) ->
  disjoint_from W A k.
Proof.
  intros L W A k SU NE Hk CL. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  inversion SU as [|x l Hx Hl]; subst. inversion NE as [|x' l' Hn Hnl]; subst. split; [| apply IH; [exact Hl| exact Hnl]].
  cbn [fst snd] in Hx, Hn.
  destruct (Z_lt_le_dec lo (A + k)) as [L1|L1]; [| left; lia].
  destruct (Z_lt_le_dec A hi) as [L2|L2]; [| right; lia].
  exfalso. apply (CL (Z.max A lo)); [lia|]. apply Hx. lia.
Qed.

#[using="Type"] Lemma sec_untouched_filter : forall L W, sec_untouched L W -> sec_untouched L (List.filter nonempty W).
Proof. intros L W SU. unfold sec_untouched in *. rewrite Forall_forall in SU |- *. intros iv Hin. apply SU. apply List.filter_In in Hin. tauto. Qed.
#[using="Type"] Lemma nonempty_filter : forall W, Forall (fun iv : Z * Z => fst iv < snd iv) (List.filter nonempty W).
Proof. intros W. rewrite Forall_forall. intros [lo hi] Hin. apply List.filter_In in Hin. destruct Hin as [_ NE]. unfold nonempty in NE. cbn [fst snd] in *. apply Z.ltb_lt. exact NE. Qed.

Section Geo.
Variable L : alayout.
Hypothesis ALO : alayout_ok L.

(* [comment removed for export] *)
Local Ltac layout :=
  (pose proof (alayout_space L ALO) as ndP__; nd_pre ndP__ 4%nat; intros SP1 SP2 SP3 _; nd_post); pose proof (ao_space L ALO) as RSP; pose proof (ao_res_hi L ALO) as ORH;
  (pose proof (ao_t L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OT1 OT2 OTs OTi; nd_post);
  let OC := fresh in pose proof (ao_ctx L ALO) as OC; pose proof (aobj_img _ _ OC ltac:(lia)) as OCI; (nd_pre OC 5%nat; intros _ OC1 OC2 OCs _; nd_post);
  (pose proof (ao_res L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OR1 OR2 _ _; nd_post);
  let ON := fresh in pose proof (ao_nodes L ALO) as ON; pose proof (aobj_img _ _ ON ltac:(lia)) as ONI; (nd_pre ON 5%nat; intros _ ON1 ON2 ONs _; nd_post);
  let OS := fresh in pose proof (ao_store L ALO) as OS; pose proof (aobj_img _ _ OS ltac:(lia)) as OSI; (nd_pre OS 5%nat; intros _ OS1 OS2 OSs _; nd_post);
  let OFK := fresh in pose proof (ao_fake L ALO) as OFK; pose proof (aobj_img _ _ OFK ltac:(lia)) as OFI; (nd_pre OFK 5%nat; intros OF0 OF1 OF2 OFs _; nd_post);
  (pose proof (ao_dtls L ALO) as ndP__; nd_pre ndP__ 5%nat; intros _ OD1 OD2 ODs ODi; nd_post);
  let OP := fresh in pose proof (ao_ptr L ALO) as OP; pose proof (aobj_img _ _ OP ltac:(lia)) as OPI; (nd_pre OP 5%nat; intros _ OP1 OP2 OPs _; nd_post);
  pose proof atop_range as ATR; pose proof ATOP_al16 as ATA;
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in SP2, SP3; change (2^37) with 137438953472 in SP2;
  unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in *.

(* [comment removed for export] *)
#[using="tlsI ALO"] Lemma clear_inst : forall a, AINSTANCE + 72 <= a < AINSTANCE + 728 -> aknown L a -> False.
Proof.
  intros a Ha K. layout.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha OF1 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OTi OCI OR1 ORH ONI OSI OFI ODi ATR ATA SP1 SP2. lia.
Qed.

(* [comment removed for export] *)
#[using="tlsI ALO"] Lemma clear_ptr : forall a, al_ptr_array L <= a < al_ptr_array L + 8388608 -> aknown L a -> False.
Proof.
  intros a Ha K. layout.
  pose proof (ad_t_ptr L ALO) as X1. pose proof (ad_ctx_ptr L ALO) as X2. pose proof (ad_ptr_res L ALO) as X3. pose proof (ad_nodes_ptr L ALO) as X4.
  pose proof (ad_store_ptr L ALO) as X5. pose proof (ad_fake_ptr L ALO) as X6. pose proof (ad_dtls_ptr L ALO) as X7.
  unfold adisj, aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha OPI OPs SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 OPs OP2 ATR SP2. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha OF1 OF2 OPs ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OPs OP2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OP2 X1 X2 X3 X4 X5 X6 X7 RSP SP1 SP2 ATR ATA. lia.
Qed.

(* [comment removed for export] *)
#[using="ALO"] Lemma clear_chunk : forall mb ms n a, sec_wf1 L (CSec mb ms n) -> mb <= a < mb + ms -> aknown L a -> False.
Proof.
  intros mb ms n a WF1 Ha K. cbn [sec_wf1] in WF1. (nd_pre WF1 7%nat; intros G1 G2 G3 G4 G5 G6 (Qt & Qc & Qr & Qp & Qn & Qs & Qf & Qd); nd_post).
  layout. unfold ablk in G2.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha G2 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 G2 G3 ATR SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha OF1 OF2 G2 G3 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha G2 G3 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha G3 Qt Qc Qr Qn Qs Qf Qd RSP SP1 SP2 ATR ATA. lia.
Qed.

(* [comment removed for export] *)
#[using="ALO"] Lemma clear_chunk_shadow : forall mb ms n a, sec_wf1 L (CSec mb ms n) -> shad mb <= a < shad mb + ms / 8 -> aknown L a -> False.
Proof.
  intros mb ms n a WF1 Ha K. cbn [sec_wf1] in WF1. (nd_pre WF1 7%nat; intros G1 G2 G3 G4 G5 G6 (Qt & Qc & Qr & Qp & Qn & Qs & Qf & Qd); nd_post).
  (pose proof (sec_facts n ltac:(lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ _ _ _ _ _ _ MSM MSB; nd_post). rewrite <- G4 in MSM, MSB.
  layout. unfold ablk in G2.
  assert (MB8 : mb mod 8 = 0) by (clear -G1; Z.div_mod_to_equations; lia).
  assert (MS8 : ms mod 8 = 0) by (clear -MSM; Z.div_mod_to_equations; lia).
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. rewrite !shad_div in K. rewrite !shad_div in Ha. unfold ASHOFF in K, Ha.
  destruct K as [K|[K|[K|[K|K]]]].
  - (* [comment removed for export] *)
    clear -K Ha G2 G3 MSB ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha MB8 MS8 MSB Qr RSP SP3 OR1 ORH G2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Ha MB8 MS8 MSB Qf OF0 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha MB8 MS8 MSB G3 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - (* [comment removed for export] *)
    clear -K Ha G2 G3 MSB MB8 MS8 ATR OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 SP1 SP2. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
#[using="tlsI ALO"] Lemma clear_prim0 : forall a, shad (al_space_beg L) <= a < shad (al_space_beg L) + shlen K_REGION -> aknown L a -> False.
Proof.
  intros a Ha K. layout. pose proof (ad_fake_res L ALO) as DFR.
  unfold adisj, aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_REGION in *. change (2^32) with 4294967296 in Ha.
  rewrite !shad_div, shlen_div in Ha. rewrite !shad_div in K. unfold ASHOFF in K, Ha.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha DFR RSP OF0 SP3 OR1 ORH SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP2 SP1 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Ha SP1 SP2 OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 ATR ATA. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
#[using="ALO"] Lemma clear_free_shadow : forall x,
  (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
  Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
  aknown L (shad x) -> False.
Proof.
  intros x Hx HF K. unfold astartup_hulls in HF.
  repeat (apply Forall_cons_iff in HF; destruct HF as [?H HF]). cbn [fst snd] in *.
  layout. unfold K_HIGH_MEM in Hx.
  unfold aknown, KLS, AIMG_HI, AIMG_LO, AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. rewrite !shad_div in K. unfold ASHOFF in K.
  destruct K as [K|[K|[K|[K|K]]]].
  - clear -K Hx ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx H8 RSP SP3 OR1 ORH ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx H3 OF0 SP1 SP2 ATR ATA. Z.div_mod_to_equations. lia.
  - clear -K Hx ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
  - clear -K Hx OTs OT2 OCs OC2 OR1 ORH ONs ON2 OSs OS2 OFs OF2 ODs OD2 ATR ATA SP1 SP2. Z.div_mod_to_equations. lia.
Qed.
End Geo.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Frame.
Variables (L : alayout) (W0 : list (Z * Z)) (m m' : amem).
Hypothesis MU0 : munch W0 m m'.
Hypothesis WM : wmono asegs m m'.
Hypothesis SU0 : sec_untouched L W0.
Let W := List.filter nonempty W0.
Let MU : munch W m m' := munch_filter_nonempty W0 m m' MU0.
Let SU : sec_untouched L W := sec_untouched_filter L W0 SU0.
Let NE : Forall (fun iv => fst iv < snd iv) W := nonempty_filter W0.

Section WithLayout.
Hypothesis ALO : alayout_ok L.
#[using="rc tlsI L SU0 SU NE ALO"] Lemma D_inst : forall A k, AINSTANCE + 72 <= A -> A + k <= AINSTANCE + 728 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_inst L ALO). lia. Qed.
#[using="rc tlsI SU0 SU NE ALO"] Lemma D_ptr : forall A k, al_ptr_array L <= A -> A + k <= al_ptr_array L + 8388608 -> 0 < k -> disjoint_from W A k.
Proof. intros A k H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_ptr L ALO). lia. Qed.
#[using="SU0 SU NE ALO"] Lemma D_chunk : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> mb <= A -> A + k <= mb + ms -> 0 < k -> disjoint_from W A k.
Proof. intros mb ms n A k WF1 H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_chunk L ALO mb ms n); [exact WF1| lia]. Qed.
#[using="SU0 SU NE ALO"] Lemma D_shadow : forall mb ms n A k, sec_wf1 L (CSec mb ms n) -> shad mb <= A -> A + k <= shad mb + ms / 8 -> 0 < k -> disjoint_from W A k.
Proof. intros mb ms n A k WF1 H1 H2 H3. apply (su_disjoint L); [exact SU| exact NE| exact H3|]. intros a Ha. apply (clear_chunk_shadow L ALO mb ms n); [exact WF1| lia]. Qed.

(* [comment removed for export] *)
#[using="W0 MU0 WM SU0 W MU SU NE ALO"] Lemma asec_chunk_frame : forall mb ms n idx lv,
  sec_wf1 L (CSec mb ms n) -> asec_chunk m (CSec mb ms n) idx lv -> asec_chunk m' (CSec mb ms n) idx lv.
Proof.
  intros mb ms n idx lv WF1 CH. pose proof WF1 as WF0. cbn [sec_wf1] in WF0. (nd_pre WF0 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post).
  (pose proof (sec_facts n ltac:(lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ RSE RSR _ NSE _ MSR MSM _; nd_post). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  (nd_pre GR 3%nat; intros GR1 GR2 GR3; nd_post).
  cbn [asec_chunk] in CH |- *. (nd_pre CH 9%nat; intros H1 H2 H3 H4 (b1 & ctx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in *.
  split; [eapply cells_frame; [exact H1| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H2| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frame; [exact H3| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frame; [exact H4| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frame; [exact H5| exact MU| exact WM| cbn; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frame; [exact H6| exact MU| exact WM| intros _; eapply D_chunk; [exact WF1| | |]; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frame; [exact S1| exact MU| exact WM| intros _; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frame; [exact S2| exact MU| exact WM| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frame; [exact S3| exact MU| exact WM| intros POS; rewrite GR2; eapply D_shadow; [exact WF1| | |]; clear -GR3 GR1 POS; lia].
Qed.
End WithLayout.

#[using="W0 MU0 WM SU0 W MU SU NE"] Theorem asec_frame : forall st st' X X',
  ASEC_of L st X m -> sec_same st st' -> ASEC_of L st' X' m'.
Proof.
  intros st st' X X' (WFS & ARR & INST & PZ & SHZ) (EN & ER & EP & EL & PERM).
  unfold ASEC_of, ASECc.
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post).
  assert (ALLSEC : forall ch, In ch (sec_chunks_of st) -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split]]].
  - (* [comment removed for export] *)
    unfold asec_wf. rewrite EP, ER, EN. split; [exact ALO|]. split; [exact WP|]. split; [exact WR|]. split; [| split; [exact WB| split]].
    + rewrite (Permutation_length PERM). exact WL.
    + rewrite Forall_forall in WF1 |- *. intros ch Hin. apply WF1. eapply Permutation_in; [exact PERM| exact Hin].
    + eapply sec_disjoint_perm; [apply Permutation_sym; exact PERM| exact WD].
  - (* [comment removed for export] *)
    (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [eapply Permutation_trans; [exact PO| apply Permutation_sym; exact PERM]|].
    split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply (D_ptr ALO); cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply (D_ptr ALO); clear -POS WB WR; lia.
    + intros i ch Hi. (nd_pre (PER i ch Hi) 3%nat; intros lv LV CH; nd_post).
      assert (Hin : In ch (sec_chunks_of st)) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      (nd_pre (ALLSEC ch Hin) 4%nat; intros mb ms n ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into W1).
      exists lv. split; [| eapply asec_chunk_frame; [exact ALO| exact W1| exact CH]].
      rewrite LV. unfold sec_live. split; intros [p Hp]; exists p; [apply (proj2 (EL p mb ms n)); exact Hp| apply (proj1 (EL p mb ms n)); exact Hp].
  - (* [comment removed for export] *)
    (nd_pre INST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; apply (D_inst ALO); unfold AINSTANCE; lia]|].
    eapply junk_frame; [exact I6| exact MU| exact WM| intros _; apply (D_inst ALO); unfold AINSTANCE; lia].
  - (* [comment removed for export] *)
    unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
    apply (su_disjoint L); [exact SU| exact NE| exact POS|]. intros a Ha. apply (clear_prim0 L ALO). exact Ha.
  - (* [comment removed for export] *)
    intros x Hx HF HC.
    assert (SX : 0 <= shad x < 2^64) by (rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; pose proof atop_range as ATR; clear -Hx ATR; Z.div_mod_to_equations; lia).
    assert (HC0 : Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) (sec_chunks_of st)).
    { rewrite Forall_forall in HC |- *. intros ch Hin. apply HC. eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]. }
    rewrite <- (SHZ x Hx HF HC0). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.
End Frame.

(* [comment removed for export] *)
#[using="Type"] Theorem asec_hs_frame : forall L st st' X X' m m' W,
  ASEC_of L st X m -> munch W m m' -> wmono asegs m m' -> sec_untouched L W -> sec_same st st' -> ASEC_of L st' X' m'.
Proof. intros L st st' X X' m m' W HS MU WM SU SS. eapply (asec_frame L W m m' MU WM SU); [exact HS| exact SS]. Qed.
End CANSEC1.
End TwB.
End ASecFrame.

(* [comment removed for export] *)
Module ASF_kit.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AImg AProto ABase. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ABytes__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ALayout__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitR__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AHeapP__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ASecFacts. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AKitQ__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require ARepKit. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeModel__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFreeRep. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require F_memchr__A3W. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W Require AFake_iface. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.
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
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : ABase.atlsT}.
#[using="Type"] Lemma granules_rup : forall n, 0 <= n -> granules n = shlen (rup n 8).
Proof.
  intros n N. unfold granules, shlen, rup. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma rup8_facts : forall n, 0 <= n -> n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ shlen (rup n 8) = rup n 8 / 8.
Proof. intros n N. unfold rup, shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.

Lemma achunk_eq_dec : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; apply Z.eq_dec. Defined.

#[using="Type"] Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma live_in_achunks : forall st (p : aptr) ch, (a_live st) !! p = Some ch -> In ch (achunks st).
Proof.
  intros st p ch L. unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p ch L) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. eapply Permutation_in; [exact P| left; reflexivity].
Qed.
#[using="Type"] Lemma live_sec_in : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof. intros st p mb ms n L. unfold sec_chunks_of. apply List.filter_In. split; [eapply live_in_achunks; exact L| reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_delete_sec : forall st st' (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) ->
  a_live st' = delete p (a_live st) ->
  Permutation (List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
              (List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) ->
  Permutation (CSec mb ms n :: sec_chunks_of st') (sec_chunks_of st).
Proof.
  intros st st' p mb ms n SOME E1 PQ. unfold sec_chunks_of, achunks. rewrite E1, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete p (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete p (a_live st))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st'))).
  apply Permutation_app; [| exact PQ].
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn in P. exact P.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma enq_app_qfilt_sec : forall s1 ch s, is_sec ch = true -> enq_app s1 ch = Some s ->
  Permutation (qfilt is_sec s) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch s Hf E. unfold enq_app in E.
  destruct (rev (a_qloc s1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (b_count b =? Q_BATCH); [discriminate|]. injection E as <-.
  unfold qfilt. cbn [a_qloc a_qglob set_qloc].
  assert (QL : a_qloc s1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc s1)), RV; reflexivity).
  rewrite QL. cbn [rev]. rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !app_nil_r.
  rewrite !List.filter_app. cbn [List.filter]. rewrite Hf.
  rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
#[using="Type"] Lemma enq_new_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (enq_new s1 ch)) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. unfold enq_new, qfilt. cbn [a_qloc a_qglob set_qloc put_cls set_cls].
  rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !List.filter_app. cbn [List.filter]. rewrite Hf.
  rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
#[using="Type"] Lemma st_enq_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (st_enq s1 ch)) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. unfold st_enq. destruct (enq_app s1 ch) as [s|] eqn:E; [exact (enq_app_qfilt_sec s1 ch s Hf E)| exact (enq_new_qfilt_sec s1 ch Hf)].
Qed.
#[using="Type"] Lemma st_after_enq_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (st_after (st_enq s1 ch))) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. eapply Permutation_trans; [apply st_after_qfilt| apply st_enq_qfilt_sec; exact Hf].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_free_sec : forall st (p : aptr) mb ms n s,
  (a_live st) !! p = Some (CSec mb ms n) ->
  a_live s = delete p (a_live st) ->
  Permutation (qfilt is_sec s) (CSec mb ms n :: qfilt is_sec st) ->
  Permutation (sec_chunks_of s) (sec_chunks_of st).
Proof.
  intros st p mb ms n s SOME EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app.
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn in P.
  unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|].
  eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
  cbn [app]. rewrite app_comm_cons. apply Permutation_app_tail. exact P.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_quar_sec : forall s s' mb ms n,
  a_live s' = a_live s ->
  Permutation (qfilt is_sec s') (CSec mb ms n :: qfilt is_sec s) ->
  Permutation (sec_chunks_of s') (CSec mb ms n :: sec_chunks_of s).
Proof.
  intros s s' mb ms n EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app. unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|]. apply Permutation_sym. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
Definition awf_delete_sec__stmt : Prop := forall L st X (p : aptr) mb ms n s,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) ->
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = a_cinit st -> a_cls s = a_cls st ->
  a_live s = delete p (a_live st) -> a_next s = a_next st ->
  awf L s X.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 2).
Variable p : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 3).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 4).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 5).
Variable n : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 6).
Variable s : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 7).
#[using="Type"] Lemma awf_delete_sec__body : ltac:(let T := type of (fun (h : awf_delete_sec__stmt) => h L st X p mb ms n s) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (p, (mb, (ms, (n, s)))))))) as _.
  intros WF LIVE E1 E2 E3 E4 E5 E6.
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  assert (GC : forall c', get_cls s c' = get_cls st c') by (intros c'; unfold get_cls; rewrite E4; reflexivity).
  assert (MC : forall c', max_count s c' = max_count st c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (ND : forall c', ndist s c' = ndist st c') by (intros c'; unfold ndist; rewrite GC; reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. cbv zeta. rewrite GC, MC, ND. exact (PERC c Hc). }
  split. { intros c Hc. rewrite GC. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [q| |]; [| exact M| exact M].
           (nd_pre M 6%nat; intros M1 M2 M3 M4 M5 M6; nd_post). repeat (split; [assumption|]).
           rewrite lookup_delete_ne; [exact M6|]. intros ->. rewrite LIVE in M6. discriminate. }
  split. { intros q c n' Hq. apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exact (LIVEB q c n' Hq). }
  split. { intros q ch Hq. apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exact (FRESH q ch Hq). }
  exact UNIQ.
Qed.
End Zd1.
#[using="Type"] Lemma awf_delete_sec : ltac:(let t := eval cbv delta [awf_delete_sec__stmt] in awf_delete_sec__stmt in exact t).
Proof. exact awf_delete_sec__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ablocks_free_sec : forall L st X LB (p : aptr) mb ms n st' X',
  (a_live st) !! p = Some (CSec mb ms n) -> awf L st X ->
  a_live st' = delete p (a_live st) -> (forall y, In y (x_busy X) -> In y (x_busy X')) ->
  ablocks L st X LB -> ablocks L st' X' (lb_remove p LB).
Proof.
  intros L st X LB p mb ms n st' X' LIVE WF EL INCL (BH & BF & NDI & NDL). split; [| split; [| split]].
  - intros p' A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin NE]. cbn in NE.
    destruct (BH p' A n' Hin) as [(y & Hy & Sy & R)|(mb' & ms' & Lp & R)].
    + left. exists y. split; [apply INCL; exact Hy|]. split; [exact Sy| exact R].
    + right. exists mb', ms'. split; [| exact R]. rewrite EL, lookup_delete_ne; [exact Lp| congruence].
  - intros cls A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin _]. exact (BF cls A n' Hin).
  - rewrite hb_ids_lb_remove. apply List.NoDup_filter. exact NDI.
  - apply NoDup_lb_remove. exact NDL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma freed_block_sec : forall L st X LB (p : aptr) mb ms n A n',
  awf L st X -> ablocks L st X LB -> In (HB p A n') LB -> (a_live st) !! p = Some (CSec mb ms n) ->
  A = mb + SEC_UOFF /\ n' = n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st X LB p mb ms n A n' WF (BH & _) Hin LIVE.
  destruct (BH p A n' Hin) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA & G)].
  - exfalso. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _). destruct (BUSY y Hy) as [_ M]. rewrite Sy in M.
    (nd_pre M 6%nat; intros _ _ _ _ _ M6; nd_post). rewrite LIVE in M6. discriminate.
  - rewrite LIVE in Lp. injection Lp as <- <- <-. split; [exact EA|]. split; [reflexivity| exact G].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma no_busy_live_sec : forall L st X (p : aptr) mb ms n y,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) -> In y (x_busy X) -> xb_st y <> BLive p.
Proof.
  intros L st X p mb ms n y WF LIVE Hy E. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY y Hy) as [_ M]. rewrite E in M. (nd_pre M 6%nat; intros _ _ _ _ _ M6; nd_post). rewrite LIVE in M6. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma arng_sub : forall L RNG st st',
  (forall c, 1 <= c < K_NUM_CLASSES -> get_cls st' c = get_cls st c) -> a_nres st' = a_nres st ->
  (forall ch, In ch (sec_chunks_of st') -> In ch (sec_chunks_of st)) ->
  arng L RNG st -> arng L RNG st'.
Proof.
  intros L RNG st st' EC EN SUB (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  repeat (split; [assumption|]). split.
  { intros c Hc. rewrite (EC c Hc). exact (A7 c Hc). }
  rewrite EN. split; [exact A8|]. split; [| exact A10].
  unfold RSEC in *. rewrite Forall_forall in A9 |- *. intros x Hx. apply A9. apply SUB. exact Hx.
Qed.

(* [comment removed for export] *)
Definition sec_not_live_after__stmt : Prop := forall L st cs (p : aptr) mb ms n s,
  asec_wf L st cs -> Permutation cs (sec_chunks_of st) ->
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) ->
  ~ sec_live s (CSec mb ms n).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 1).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 2).
Variable p : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 3).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 4).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 5).
Variable n : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 6).
Variable s : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 7).
#[using="Type"] Lemma sec_not_live_after__body : ltac:(let T := type of (fun (h : sec_not_live_after__stmt) => h L st cs p mb ms n s) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (cs, (p, (mb, (ms, (n, s)))))))) as _.
  intros WFS PC LIVE EL [q Hq]. rewrite EL in Hq.
  apply lookup_delete_Some in Hq. destruct Hq as [NE Hq].
  (nd_pre WFS 7%nat; intros _ _ _ _ _ _ [ND _]; nd_post).
  (* [comment removed for export] *)
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) LIVE) as P1.
  assert (Hq' : delete p (a_live st) !! q = Some (CSec mb ms n)) by (rewrite lookup_delete_ne by exact NE; exact Hq).
  pose proof (map_to_list_delete (delete p (a_live st)) q (CSec mb ms n) Hq') as P2.
  assert (P : Permutation ((p, CSec mb ms n) :: (q, CSec mb ms n) :: map_to_list (delete q (delete p (a_live st)))) (map_to_list (a_live st))).
  { eapply Permutation_trans; [apply perm_skip; exact P2| exact P1]. }
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn [List.filter is_sec] in P.
  assert (P3 : Permutation (CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st)))))
                                 ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) cs).
  { eapply Permutation_trans; [| apply Permutation_sym; exact PC]. unfold sec_chunks_of, achunks. rewrite filter_is_sec_app.
    change (CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
      with ((CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st)))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
    apply Permutation_app_tail. exact P. }
  pose proof (Permutation_NoDup (Permutation_sym P3) ND) as ND2. cbn [app] in ND2.
  inversion ND2 as [|x l NI ND3]; subst. apply NI. left. reflexivity.
Qed.
End Zd2.
#[using="Type"] Lemma sec_not_live_after : ltac:(let t := eval cbv delta [sec_not_live_after__stmt] in sec_not_live_after__stmt in exact t).
Proof. exact sec_not_live_after__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_live_other : forall st (p : aptr) mb ms n s ch,
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) -> ch <> CSec mb ms n ->
  (sec_live s ch <-> sec_live st ch).
Proof.
  intros st p mb ms n s ch LIVE EL NE. unfold sec_live. rewrite EL. split; intros [q Hq].
  - apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exists q. exact Hq.
  - exists q. rewrite lookup_delete_ne; [exact Hq|]. intros ->. apply NE. pose proof (eq_trans (eq_sym Hq) LIVE) as XX. injection XX as <-. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma sec_wf1_facts' : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n /\ 64512 < n <= AREQMAX
  /\ rz_size n = 2048 /\ 73728 <= ms <= 536821760 /\ ms mod 4096 = 0 /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n
  /\ sec_clear L mb ms /\ is_primary n = false /\ n + 6144 <= needed_size n + 4096.
Proof.
  intros L mb ms n W. pose proof W as W0. destruct W0 as (MAL & MLO & MCE & MSE & NB & NPR & SCL).
  (pose proof (sec_facts n ltac:(lia) NPR) as ndP__; nd_pre ndP__ 10%nat; intros _ RZ _ RS1 _ NS MS MSB MSAL MSR; nd_post). rewrite <- MSE in MSB, MSAL, MSR.
  unfold AREQMAX in *.
  repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| reflexivity| lia].
Qed.

(* [comment removed for export] *)
Definition read_chunk_sec__stmt : Prop := forall cs L st X m (p : aptr) mb ms n,
  ASECc cs L st X m -> Permutation cs (sec_chunks_of st) -> (a_live st) !! p = Some (CSec mb ms n) ->
  let hm := mb + 6128 in
  exists order i b1 ctx uw,
     Permutation order cs /\ nth_error order i = Some (CSec mb ms n) /\ (i < length order)%nat
  /\ Z.of_nat (length order) = a_nsec st
  /\ Forall (sec_wf1 L) order /\ sec_disjoint order
  /\ u64arr asegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
  /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
  /\ (forall j ch, nth_error order j = Some ch -> exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat j) lv)
  /\ asec_chunk m (CSec mb ms n) (Z.of_nat i) true
  /\ rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 (Z.of_nat i))]
  /\ rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31
  /\ rw_cells asegs m (hm + 16) [C8 uw] /\ junk_at m (hm + 24) (ms - SEC_UOFF - 8)
  /\ fill_at m (shad mb) 768 0xfa
  /\ rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (block_shadow_bytes n)]
  /\ fill_at m (shad (hm + 16) + shlen (rup n 8)) (ms / 8 - 768 - shlen (rup n 8)) 0xfa.
Section Zd3.   (* [comment removed for export] *)
Variable cs : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 0).
Variable L : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 1).
Variable st : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 2).
Variable X : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 4).
Variable p : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 5).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 6).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 7).
Variable n : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 8).
#[using="Type"] Lemma read_chunk_sec__body : ltac:(let T := type of (fun (h : read_chunk_sec__stmt) => h cs L st X m p mb ms n) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (cs, (L, (st, (X, (m, (p, (mb, (ms, n))))))))) as _.
  intros (WFS & ARR & INST & PZ & SHZ) PC LIVE hm.
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post).
  (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post).
  assert (IN : In (CSec mb ms n) cs) by (eapply Permutation_in; [apply Permutation_sym; exact PC| eapply live_sec_in; exact LIVE]).
  assert (INo : In (CSec mb ms n) order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact IN]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  (nd_pre (PER i _ NTH) 3%nat; intros lv LV CH; nd_post).
  assert (Elv : lv = true) by (apply (proj2 LV); exists p; exact LIVE). subst lv.
  pose proof (proj1 (Forall_forall _ _) WF1o _ INo) as Wch.
  (nd_pre (sec_wf1_facts' L mb ms n Wch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  pose proof CH as CH0. cbn [asec_chunk] in CH0.
  (nd_pre CH0 9%nat; intros H1 H2 H3 H4 (b1 & cx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in H5, H6, S2, S3. replace (mb + 6144 - 16) with hm in H5 by (subst hm; lia).
  destruct (junk_split m _ 8 (ms - 6144 - 8) ltac:(replace (8 + (ms - 6144 - 8)) with (ms - 6144) by lia; exact H6) ltac:(lia) ltac:(lia)) as [U8 UR].
  destruct (c8_of_junk m _ U8) as [uw HUW].
  exists order, i, b1, cx, uw.
  split; [exact PO|]. split; [exact NTH|]. split; [exact IL|]. split; [rewrite (Permutation_length PO); exact WL|].
  split; [exact WF1o|]. split; [exact WDo|]. split; [exact U64|]. split; [exact JK|]. split; [exact PER|]. split; [exact CH|].
  split; [exact H1|]. split; [exact H5|]. split; [exact B1|]. split; [exact B3|]. split; [exact CX|].
  replace (hm + 16) with (mb + 6144) by (subst hm; lia). replace (hm + 24) with (mb + 6144 + 8) by (subst hm; lia).
  split; [exact HUW|]. split; [unfold SEC_UOFF; exact UR|]. split; [exact S1|].
  rewrite <- (granules_rup n) by lia. unfold sec_user_shadow in S2. split; [exact S2| exact S3].
Qed.
End Zd3.
#[using="Type"] Lemma read_chunk_sec : ltac:(let t := eval cbv delta [read_chunk_sec__stmt] in read_chunk_sec__stmt in exact t).
Proof. exact read_chunk_sec__body. Qed.

(* [comment removed for export] *)
Definition asec_chunk_frameD'__stmt : Prop := forall L W m m' mb ms n idx lv,
  munch W m m' -> sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb + 32 <= A -> 0 < k -> A + k <= mb + ms -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> 0 < k -> A + k <= shad mb + ms / 8 -> disjoint_from W A k) ->
  rw_cells asegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)] ->
  (exists idx0, asec_chunk m (CSec mb ms n) idx0 lv) -> asec_chunk m' (CSec mb ms n) idx lv.
Section Zd4.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 0).
Variable W : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 1).
Variable m : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 2).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 3).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 4).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 5).
Variable n : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 6).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 7).
Variable lv : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 8).
#[using="Type"] Lemma asec_chunk_frameD'__body : ltac:(let T := type of (fun (h : asec_chunk_frameD'__stmt) => h L W m m' mb ms n idx lv) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (W, (m, (m', (mb, (ms, (n, (idx, lv))))))))) as _.
  intros MU WF1 DC DS HDR [idx0 CH].
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. (nd_pre WF0 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post).
  (pose proof (sec_facts n ltac:(lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ RSE RSR _ NSE _ MSR MSM _; nd_post). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  (nd_pre GR 3%nat; intros GR1 GR2 GR3; nd_post).
  cbn [asec_chunk] in CH |- *. (nd_pre CH 9%nat; intros H1 H2 H3 H4 (b1 & ctx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in *.
  split; [exact HDR|].
  split; [eapply junk_frameD; [exact H2| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frameD; [exact H3| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frameD; [exact H4| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frameD; [exact H5| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frameD; [exact H6| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frameD; [exact S1| exact MU| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frameD; [exact S2| exact MU| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frameD; [exact S3| exact MU| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.
End Zd4.
#[using="Type"] Lemma asec_chunk_frameD' : ltac:(let t := eval cbv delta [asec_chunk_frameD'__stmt] in asec_chunk_frameD'__stmt in exact t).
Proof. exact asec_chunk_frameD'__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_same0 (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall ch, is_sec ch = true -> (sec_live st' ch <-> sec_live st ch)).

Definition asecc_frame__stmt : Prop := forall cs L W m m' st st' X X',
  ASECc cs L st X m -> munch W m m' -> wmono asegs m m' -> sec_untouched L W -> sec_same0 st st' ->
  ASECc cs L st' X' m'.
Section Zd5.   (* [comment removed for export] *)
Variable cs : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 0).
Variable L : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 1).
Variable W0 : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 2).
Variable m : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 3).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 4).
Variable st : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 5).
Variable st' : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 6).
Variable X : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 7).
Variable X' : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 8).
#[using="Type"] Lemma asecc_frame__body : ltac:(let T := type of (fun (h : asecc_frame__stmt) => h cs L W0 m m' st st' X X') in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (cs, (L, (W0, (m, (m', (st, (st', (X, X'))))))))) as _.
  intros (WFS & ARR & INST & PZ & SHZ) MU0 WM SU0 (EN & ER & EP & EL).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post).
  pose proof (munch_filter_nonempty W0 m m' MU0) as MU. pose proof (sec_untouched_filter L W0 SU0) as SU. pose proof (nonempty_filter W0) as NE.
  set (W := List.filter nonempty W0) in MU, SU, NE.
  assert (ALLSEC : forall ch, In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split]]].
  - unfold asec_wf. rewrite EP, ER, EN. exact WFS.
  - (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [exact PO|]. split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply (D_ptr L W0 SU0 ALO); cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply (D_ptr L W0 SU0 ALO); clear -POS WB WR; lia.
    + intros i ch Hi. (nd_pre (PER i ch Hi) 3%nat; intros lv LV CH; nd_post).
      assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      (nd_pre (ALLSEC ch Hin) 4%nat; intros mb ms n ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into W1).
      exists lv. split; [| eapply (asec_chunk_frame L W0 m m' MU0 WM SU0 ALO); [exact W1| exact CH]].
      rewrite LV. apply iff_sym. apply EL. reflexivity.
  - (nd_pre INST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    eapply junk_frame; [exact I6| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia].
  - unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
    apply (su_disjoint L); [exact SU| exact NE| exact POS|]. intros a Ha. apply (clear_prim0 L ALO). exact Ha.
  - intros x Hx HF HC.
    assert (SX : 0 <= shad x < 2^64) by (pose proof atop_range as ATR; rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; clear -Hx ATR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.
End Zd5.
#[using="Type"] Lemma asecc_frame : ltac:(let t := eval cbv delta [asecc_frame__stmt] in asecc_frame__stmt in exact t).
Proof. exact asecc_frame__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_frameD_law (AD : alayout -> amem -> Prop) : Prop :=
  forall L m m' W, AD L m -> munch W m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
              ~ (0x1804c8 <= a < 0x5d0510) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    AD L m'.
(* [comment removed for export] *)
Definition fake_frameD_law (AFK : alayout -> list ablock -> amem -> Prop) : Prop :=
  forall L LB m m' W, AFK L LB m -> munch W m m' -> fake_untouched L W ->
    Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AFK L LB m'.

#[using="Type"] Lemma dc_at_frameD : forall W m m' A n, dc_at m A n -> munch W m m' -> (0 < n -> disjoint_from W A n) -> dc_at m' A n.
Proof. intros W m m' A n H MU D. exact (junk_frameD W m m' A n H MU D). Qed.

Definition afake_frameD__stmt : Prop := fake_frameD_law AFAKE.
Section Zd6.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 0).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 1).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 2).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 3).
Variable W : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 4).
#[using="Type"] Lemma afake_frameD__body : ltac:(let T := type of (fun (h : afake_frameD__stmt) => h L LB m m' W) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (LB, (m, (m', W))))) as _.
  intros (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU UT UT2.
  (pose proof G as ndP__; nd_pre ndP__ 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11; nd_post). unfold FAKESZ in *. (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post).   (* [comment removed for export] *)
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0xa7288 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W (ATPv + -8) 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W (ATPv + 8) 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W (ATPv + 296) 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x1401b1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x13e098 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
  assert (DT : disjoint_from W (al_t L + 48) 16).
  { apply disjoint_from_Forall. eapply Forall_impl; [| exact UT2]. cbv beta. intros iv Hiv. lia. }
  split; [exact G|].
  split.
  { (nd_pre CE 8%nat; intros C1 C2 C3 C4 C5 C6 C7 C8; nd_post). unfold afake_cells.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transportD; [eassumption| exact MU| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
    eapply dc_at_frameD; [exact C8| exact MU| intros _; exact DT]. }
  split.
  { exists h0, h1, h2, hs. eapply rw_cells_transportD; [exact HS| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
  split; [eapply rw_cells_transportD; [exact LOG| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply rw_cells_transportD; [exact NGC| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply dc_at_frameD; [exact DC1| exact MU| intros _; unfold FAKESZ; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split.
  { eapply dc_at_frameD; [exact DC2| exact MU| intros _; unfold FAKESZ; exact DS]. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
  - intros c F n Hin. (nd_pre (LV c F n Hin) 6%nat; intros Hc Hn pos Hp HF Hb; nd_post). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.
End Zd6.
#[using="Type"] Lemma afake_frameD : ltac:(let t := eval cbv delta [afake_frameD__stmt] in afake_frameD__stmt in exact t).
Proof. exact afake_frameD__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qcoupled_add1_sec__stmt : Prop := forall L s s' X X' Q Q' mb ms n k (newb : list xbusy),
  qcoupled L s X Q ->
  length (q_loc Q') = length (a_qloc s') -> length (q_glob Q') = length (a_qglob s') ->
  Permutation (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q'))
              ((CSec mb ms n, k) :: qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) ->
  Permutation (map qb_slot (q_loc Q' ++ q_glob Q')) (map xb_slot newb ++ map qb_slot (q_loc Q ++ q_glob Q)) ->
  (forall y, In y (x_busy X') /\ xb_st y = BQuar <-> In y (x_busy X) /\ xb_st y = BQuar) ->
  (forall y, In y (x_busy X') /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y newb) ->
  Forall (fun y => xb_st y = BBatch /\ xb_class y = K_BATCH_CLASS /\ 0 <= xb_slot y) newb ->
  (forall y, In y (x_busy X) -> xb_st y = BBatch -> xb_class y = K_BATCH_CLASS -> In (xb_slot y) (map xb_slot newb) -> False) ->
  List.NoDup (map xb_slot newb) ->
  q_pend Q' = q_pend Q ->
  qcoupled L s' X' Q'.
Section Zd7.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 0).
Variable s : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 1).
Variable s' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 2).
Variable X : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 3).
Variable X' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 4).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 5).
Variable Q' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 6).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 7).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 8).
Variable n : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 9).
Variable k : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 10).
Variable newb : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 11).
#[using="Type"] Lemma qcoupled_add1_sec__body : ltac:(let T := type of (fun (h : qcoupled_add1_sec__stmt) => h L s s' X X' Q Q' mb ms n k newb) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (s, (s', (X, (X', (Q, (Q', (mb, (ms, (n, (k, newb)))))))))))) as _.
  intros (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB HQ HB NEWB FB NDB PD.
  assert (PEQ : Permutation (qprim_ids (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q')))
                             (qprim_ids (qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)))).
  { pose proof (qprim_ids_perm _ _ PE) as P. cbn [qprim_ids flat_map fst snd app] in P. exact P. }
  unfold qcoupled. cbv zeta. rewrite PD.
  split; [exact L1|]. split; [exact L2|]. split.
  { eapply Permutation_Forall; [apply Permutation_sym; exact PE|]. constructor; [exact I|].
    eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c' n'| mb' ms' n']; [| exact I]. (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'.
    apply (proj1 (proj2 (HQ _) (conj Hin eq_refl))). }
  split; [eapply Permutation_NoDup'; [apply Permutation_app_tail; apply Permutation_sym; exact PEQ| exact ND1]|].
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PB|]. apply List.NoDup_app; [exact NDB| exact ND2|].
    intros k0 Hn Ho. apply (BS k0) in Ho. (nd_pre Ho 5%nat; intros y Hy Sy Cy Ky; nd_post). subst k0. exact (FB y Hy Sy Cy Hn). }
  split.
  { intros k0. split.
    - intros H. apply (Permutation_in _ PB) in H. apply in_app_iff in H. destruct H as [H|H].
      + apply in_map_iff in H. (nd_pre H 2%nat; intros y ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hy). (pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as ndP__; nd_pre ndP__ 3%nat; intros Sy Cy _; nd_post).
        exists y. split; [apply (proj1 (proj2 (HB y) (or_intror Hy)))|]. auto.
      + apply (BS k0) in H. (nd_pre H 5%nat; intros y Hy Sy Cy Ky; nd_post). exists y. split; [apply (proj1 (proj2 (HB y) (or_introl (conj Hy Sy))))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PB|]. apply in_app_iff.
      destruct (proj1 (HB y) (conj Hy Sy)) as [[Hy0 _]|Hn].
      + right. apply (BS k0). exists y. auto.
      + left. subst k0. apply in_map. exact Hn. }
  split.
  { intros c0 k0. split.
    - intros H. apply (Permutation_in _ (Permutation_app_tail (q_pend Q) PEQ)) in H.
      apply (PS c0 k0) in H. (nd_pre H 5%nat; intros y Hy Sy Cy Ky; nd_post). exists y. split; [apply (proj1 (proj2 (HQ y) (conj Hy Sy)))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_app_tail; apply Permutation_sym; exact PEQ|].
      apply (PS c0 k0). exists y. pose proof (proj1 (HQ y) (conj Hy Sy)) as [Hy0 _]. auto. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB|]. apply Forall_app. split; [| exact NN].
  apply Forall_forall. intros k0 H. apply in_map_iff in H. (nd_pre H 2%nat; intros y ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hy).
  (pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as ndP__; nd_pre ndP__ 3%nat; intros _ _ P; nd_post). exact P.
Qed.
End Zd7.
#[using="Type"] Lemma qcoupled_add1_sec : ltac:(let t := eval cbv delta [qcoupled_add1_sec__stmt] in qcoupled_add1_sec__stmt in exact t).
Proof. exact qcoupled_add1_sec__body. Qed.

Section QUpdatesS.
Variables (L : alayout) (st : astate) (X : aconc) (Q : qconc) (mb ms n : Z).
Let ch := CSec mb ms n.
Hypothesis WF : awf L st X.
Hypothesis CP : qcoupled L st X Q.

(* [comment removed for export] *)
Definition qcoupled_app_sec__stmt : Prop := forall s' l bl ql qz ia k,
  a_qloc st = l ++ [bl] -> q_loc Q = ql ++ [qz] ->
  a_qloc s' = l ++ [mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)] -> a_qglob s' = a_qglob st ->
  qcoupled L s' X (mkQConc (ql ++ [mkQB (qb_slot qz) (k :: qb_ks qz)]) (q_glob Q) ia (q_pend Q)).
Section Zd8.   (* [comment removed for export] *)
Variable s' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 0).
Variable l : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 1).
Variable bl : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 2).
Variable ql : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 3).
Variable qz : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 4).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 5).
Variable k : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 6).
#[using="CP"] Lemma qcoupled_app_sec__body : ltac:(let T := type of (fun (h : qcoupled_app_sec__stmt) => h s' l bl ql qz ia k) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (s', (l, (bl, (ql, (qz, (ia, k))))))) as _.
  intros QL QQ QL' QG'.
  pose proof CP as CP0. (nd_pre CP0 3%nat; intros LN1 LN2 _; nd_post).
  assert (LNl : length ql = length l).
  { rewrite QL, QQ, !length_app in LN1. cbn in LN1. lia. }
  eapply (qcoupled_add1_sec L st s' X X Q _ mb ms n k []); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG', QL, QQ. rewrite !qentries_app by exact LNl. cbn [qentries combine b_chunks qb_ks app].
    rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. rewrite ?app_nil_r.
    apply Permutation_middle.
  - cbn [q_loc q_glob map app]. rewrite QQ, !map_app. cbn [map qb_slot]. apply Permutation_refl.
  - intros y; tauto.
  - intros y. cbn [In]. tauto.
  - constructor.
  - intros y _ _ _ [].
  - constructor.
  - reflexivity.
Qed.
End Zd8.
#[using="CP"] Lemma qcoupled_app_sec : ltac:(let t := eval cbv delta [qcoupled_app_sec__stmt] in qcoupled_app_sec__stmt in exact t).
Proof. exact qcoupled_app_sec__body. Qed.

(* [comment removed for export] *)
Definition qcoupled_new_sec__stmt : Prop := forall s' k24 cnt sz ia k,
  c_count (get_cls st K_BATCH_CLASS) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (cnt - 1)) = Some k24 ->
  a_qloc s' = a_qloc st ++ [mkABatch 1 sz [ch]] -> a_qglob s' = a_qglob st ->
  qcoupled L s' (xbatch X k24) (mkQConc (q_loc Q ++ [mkQB k24 [k]]) (q_glob Q) ia (q_pend Q)).
Section Zd9.   (* [comment removed for export] *)
Variable s' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 0).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 1).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 2).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 3).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 4).
Variable k : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 5).
#[using="rc WF CP"] Lemma qcoupled_new_sec__body : ltac:(let T := type of (fun (h : qcoupled_new_sec__stmt) => h s' k24 cnt sz ia k) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (s', (k24, (cnt, (sz, (ia, k)))))) as _.
  intros CNT POS NK QL' QG'.
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ _ BS _; nd_post).
  (pose proof (k24_not_busy L _ X k24 cnt WF CNT POS NK) as ndP__; nd_pre ndP__ 3%nat; intros NB KR _; nd_post).
  eapply (qcoupled_add1_sec L st s' X (xbatch X k24) Q _ mb ms n k [bbatch k24]); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG'. rewrite !qentries_app by exact LN1. cbn [qentries combine b_chunks qb_ks app].
    apply Permutation_sym. rewrite <- ?app_assoc. cbn [app]. apply Permutation_middle.
  - cbn [q_loc q_glob map xb_slot bbatch]. rewrite <- app_assoc, !map_app. cbn [map qb_slot app]. apply Permutation_sym.
    apply Permutation_middle.
  - intros y. rewrite (In_xbatch X k24 y). unfold bbatch. split.
    + intros [[-> |H] S]; [cbn in S; discriminate| exact (conj H S)].
    + intros [H S]. split; [right; exact H| exact S].
  - intros y. rewrite (In_xbatch X k24 y). cbn [In]. split.
    + intros [[-> |H] S]; [right; left; reflexivity| left; exact (conj H S)].
    + intros [[H S]|[<-|[]]]; [split; [right; exact H| exact S]| split; [left; reflexivity| reflexivity]].
  - constructor; [| constructor]. cbn. split; [reflexivity|]. split; [reflexivity| lia].
  - intros y Hy Sy Cy Hin. cbn in Hin. destruct Hin as [E|[]]. apply NB.
    unfold busy_slots. rewrite E. apply in_map. apply List.filter_In. split; [exact Hy| rewrite Cy; apply Z.eqb_refl].
  - constructor; [intros []| constructor].
  - reflexivity.
Qed.
End Zd9.
#[using="rc WF CP"] Lemma qcoupled_new_sec : ltac:(let t := eval cbv delta [qcoupled_new_sec__stmt] in qcoupled_new_sec__stmt in exact t).
Proof. exact qcoupled_new_sec__body. Qed.
End QUpdatesS.
End CANSEC1.
(* [comment removed for export] *)

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AImg.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AProto.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABase.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ABytes__A3W.ABytes.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ALayout.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AHeapP__A3W.AHeapP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASecFacts.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ASec__A3W.ASecFrame.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.AKitQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.ARepQ.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitQ__A3W.ARepQP.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ARepKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AKitR__A3W.ARepExt.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeModel__A3W.AFreeModel.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFreeRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.ALayout__A3W.AFrameD.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.F_memchr__A3W.FsKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.A3W.AFake_iface.TwB.
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
Ltac chg T x := repeat (match goal with H : context [T] |- _ => progress change T with x in H end); try change T with x.
Section CANSEC1. Context {rc : runConstT} {tlsI : A3W.ABase.TwB.atlsT}.
#[using="Type"] Lemma granules_rup : forall n, 0 <= n -> granules n = shlen (rup n 8).
Proof.
  intros n N. unfold granules, shlen, rup. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  Z.div_mod_to_equations. nia.
Qed.
#[using="Type"] Lemma rup8_facts : forall n, 0 <= n -> n <= rup n 8 <= n + 7 /\ rup n 8 mod 8 = 0 /\ shlen (rup n 8) = rup n 8 / 8.
Proof. intros n N. unfold rup, shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. Z.div_mod_to_equations. nia. Qed.

Lemma achunk_eq_dec : forall c1 c2 : achunk, {c1 = c2} + {c1 <> c2}.
Proof. decide equality; apply Z.eq_dec. Defined.

#[using="Type"] Lemma filter_is_sec_perm : forall (l l' : list achunk), Permutation l l' -> Permutation (List.filter is_sec l) (List.filter is_sec l').
Proof.
  intros l l' HP. induction HP; cbn; [constructor| | |].
  - destruct (is_sec x); [apply perm_skip|]; assumption.
  - destruct (is_sec x), (is_sec y); try apply perm_swap; try apply perm_skip; try apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma live_in_achunks : forall st (p : aptr) ch, (a_live st) !! p = Some ch -> In ch (achunks st).
Proof.
  intros st p ch L. unfold achunks. apply in_or_app. left.
  pose proof (map_to_list_delete (a_live st) p ch L) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. eapply Permutation_in; [exact P| left; reflexivity].
Qed.
#[using="Type"] Lemma live_sec_in : forall st (p : aptr) mb ms n, (a_live st) !! p = Some (CSec mb ms n) -> In (CSec mb ms n) (sec_chunks_of st).
Proof. intros st p mb ms n L. unfold sec_chunks_of. apply List.filter_In. split; [eapply live_in_achunks; exact L| reflexivity]. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_delete_sec : forall st st' (p : aptr) mb ms n,
  (a_live st) !! p = Some (CSec mb ms n) ->
  a_live st' = delete p (a_live st) ->
  Permutation (List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
              (List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) ->
  Permutation (CSec mb ms n :: sec_chunks_of st') (sec_chunks_of st).
Proof.
  intros st st' p mb ms n SOME E1 PQ. unfold sec_chunks_of, achunks. rewrite E1, !filter_is_sec_app.
  change (CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete p (a_live st)))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st')))
    with ((CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete p (a_live st))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st' ++ a_qglob st'))).
  apply Permutation_app; [| exact PQ].
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn in P. exact P.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma enq_app_qfilt_sec : forall s1 ch s, is_sec ch = true -> enq_app s1 ch = Some s ->
  Permutation (qfilt is_sec s) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch s Hf E. unfold enq_app in E.
  destruct (rev (a_qloc s1)) as [|b rl] eqn:RV; [discriminate|].
  destruct (b_count b =? Q_BATCH); [discriminate|]. injection E as <-.
  unfold qfilt. cbn [a_qloc a_qglob set_qloc].
  assert (QL : a_qloc s1 = rev rl ++ [b]) by (rewrite <- (rev_involutive (a_qloc s1)), RV; reflexivity).
  rewrite QL. cbn [rev]. rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !app_nil_r.
  rewrite !List.filter_app. cbn [List.filter]. rewrite Hf.
  rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
#[using="Type"] Lemma enq_new_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (enq_new s1 ch)) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. unfold enq_new, qfilt. cbn [a_qloc a_qglob set_qloc put_cls set_cls].
  rewrite !flat_map_app_chunks. cbn [flat_map b_chunks app]. rewrite !List.filter_app. cbn [List.filter]. rewrite Hf.
  rewrite <- app_assoc. cbn [app]. apply Permutation_sym. apply Permutation_middle.
Qed.
#[using="Type"] Lemma st_enq_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (st_enq s1 ch)) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. unfold st_enq. destruct (enq_app s1 ch) as [s|] eqn:E; [exact (enq_app_qfilt_sec s1 ch s Hf E)| exact (enq_new_qfilt_sec s1 ch Hf)].
Qed.
#[using="Type"] Lemma st_after_enq_qfilt_sec : forall s1 ch, is_sec ch = true -> Permutation (qfilt is_sec (st_after (st_enq s1 ch))) (ch :: qfilt is_sec s1).
Proof.
  intros s1 ch Hf. eapply Permutation_trans; [apply st_after_qfilt| apply st_enq_qfilt_sec; exact Hf].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_free_sec : forall st (p : aptr) mb ms n s,
  (a_live st) !! p = Some (CSec mb ms n) ->
  a_live s = delete p (a_live st) ->
  Permutation (qfilt is_sec s) (CSec mb ms n :: qfilt is_sec st) ->
  Permutation (sec_chunks_of s) (sec_chunks_of st).
Proof.
  intros st p mb ms n s SOME EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app.
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) SOME) as P.
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn in P.
  unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|].
  eapply Permutation_trans; [apply Permutation_sym; apply Permutation_middle|].
  cbn [app]. rewrite app_comm_cons. apply Permutation_app_tail. exact P.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_chunks_of_quar_sec : forall s s' mb ms n,
  a_live s' = a_live s ->
  Permutation (qfilt is_sec s') (CSec mb ms n :: qfilt is_sec s) ->
  Permutation (sec_chunks_of s') (CSec mb ms n :: sec_chunks_of s).
Proof.
  intros s s' mb ms n EL PQ. unfold sec_chunks_of, achunks. rewrite EL, !filter_is_sec_app. unfold qfilt in PQ.
  eapply Permutation_trans; [apply Permutation_app_head; exact PQ|]. apply Permutation_sym. apply Permutation_middle.
Qed.

(* [comment removed for export] *)
Definition awf_delete_sec__stmt : Prop := forall L st X (p : aptr) mb ms n s,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) ->
  a_space_beg s = a_space_beg st -> a_ptr_array s = a_ptr_array st -> a_cinit s = a_cinit st -> a_cls s = a_cls st ->
  a_live s = delete p (a_live st) -> a_next s = a_next st ->
  awf L s X.
Section Zd1.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 1).
Variable X : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 2).
Variable p : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 3).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 4).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 5).
Variable n : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 6).
Variable s : ltac2:(SecDietF.SzSecF.ty 'awf_delete_sec__stmt 7).
#[using="Type"] Lemma awf_delete_sec__body : ltac:(let T := type of (fun (h : awf_delete_sec__stmt) => h L st X p mb ms n s) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (X, (p, (mb, (ms, (n, s)))))))) as _.
  intros WF LIVE E1 E2 E3 E4 E5 E6.
  pose proof WF as WF0. (nd_pre WF0 11%nat; intros SBE PAE SAL SLO SHI PERC OUTC BUSY LIVEB FRESH UNIQ; nd_post).
  assert (GC : forall c', get_cls s c' = get_cls st c') by (intros c'; unfold get_cls; rewrite E4; reflexivity).
  assert (MC : forall c', max_count s c' = max_count st c') by (intros c'; unfold max_count; rewrite E3; reflexivity).
  assert (ND : forall c', ndist s c' = ndist st c') by (intros c'; unfold ndist; rewrite GC; reflexivity).
  unfold awf. rewrite E1, E2, E5, E6.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split. { intros c Hc. cbv zeta. rewrite GC, MC, ND. exact (PERC c Hc). }
  split. { intros c Hc. rewrite GC. exact (OUTC c Hc). }
  split. { intros b Hb. destruct (BUSY b Hb) as [CL M]. split; [exact CL|]. destruct (xb_st b) as [q| |]; [| exact M| exact M].
           (nd_pre M 6%nat; intros M1 M2 M3 M4 M5 M6; nd_post). repeat (split; [assumption|]).
           rewrite lookup_delete_ne; [exact M6|]. intros ->. rewrite LIVE in M6. discriminate. }
  split. { intros q c n' Hq. apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exact (LIVEB q c n' Hq). }
  split. { intros q ch Hq. apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exact (FRESH q ch Hq). }
  exact UNIQ.
Qed.
End Zd1.
#[using="Type"] Lemma awf_delete_sec : ltac:(let t := eval cbv delta [awf_delete_sec__stmt] in awf_delete_sec__stmt in exact t).
Proof. exact awf_delete_sec__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ablocks_free_sec : forall L st X LB (p : aptr) mb ms n st' X',
  (a_live st) !! p = Some (CSec mb ms n) -> awf L st X ->
  a_live st' = delete p (a_live st) -> (forall y, In y (x_busy X) -> In y (x_busy X')) ->
  ablocks L st X LB -> ablocks L st' X' (lb_remove p LB).
Proof.
  intros L st X LB p mb ms n st' X' LIVE WF EL INCL (BH & BF & NDI & NDL). split; [| split; [| split]].
  - intros p' A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin NE]. cbn in NE.
    destruct (BH p' A n' Hin) as [(y & Hy & Sy & R)|(mb' & ms' & Lp & R)].
    + left. exists y. split; [apply INCL; exact Hy|]. split; [exact Sy| exact R].
    + right. exists mb', ms'. split; [| exact R]. rewrite EL, lookup_delete_ne; [exact Lp| congruence].
  - intros cls A n' Hin. apply In_lb_remove in Hin. destruct Hin as [Hin _]. exact (BF cls A n' Hin).
  - rewrite hb_ids_lb_remove. apply List.NoDup_filter. exact NDI.
  - apply NoDup_lb_remove. exact NDL.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma freed_block_sec : forall L st X LB (p : aptr) mb ms n A n',
  awf L st X -> ablocks L st X LB -> In (HB p A n') LB -> (a_live st) !! p = Some (CSec mb ms n) ->
  A = mb + SEC_UOFF /\ n' = n /\ sec_wf1 L (CSec mb ms n).
Proof.
  intros L st X LB p mb ms n A n' WF (BH & _) Hin LIVE.
  destruct (BH p A n' Hin) as [(y & Hy & Sy & Uy & Ny)|(mb' & ms' & Lp & EA & G)].
  - exfalso. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _). destruct (BUSY y Hy) as [_ M]. rewrite Sy in M.
    (nd_pre M 6%nat; intros _ _ _ _ _ M6; nd_post). rewrite LIVE in M6. discriminate.
  - rewrite LIVE in Lp. injection Lp as <- <- <-. split; [exact EA|]. split; [reflexivity| exact G].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma no_busy_live_sec : forall L st X (p : aptr) mb ms n y,
  awf L st X -> (a_live st) !! p = Some (CSec mb ms n) -> In y (x_busy X) -> xb_st y <> BLive p.
Proof.
  intros L st X p mb ms n y WF LIVE Hy E. destruct WF as (_ & _ & _ & _ & _ & _ & _ & BUSY & _).
  destruct (BUSY y Hy) as [_ M]. rewrite E in M. (nd_pre M 6%nat; intros _ _ _ _ _ M6; nd_post). rewrite LIVE in M6. discriminate.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma arng_sub : forall L RNG st st',
  (forall c, 1 <= c < K_NUM_CLASSES -> get_cls st' c = get_cls st c) -> a_nres st' = a_nres st ->
  (forall ch, In ch (sec_chunks_of st') -> In ch (sec_chunks_of st)) ->
  arng L RNG st -> arng L RNG st'.
Proof.
  intros L RNG st st' EC EN SUB (A1 & A2 & A3 & A4 & A5 & A6 & A6a & A6b & A6c & A7 & A8 & A9 & A10).
  repeat (split; [assumption|]). split.
  { intros c Hc. rewrite (EC c Hc). exact (A7 c Hc). }
  rewrite EN. split; [exact A8|]. split; [| exact A10].
  unfold RSEC in *. rewrite Forall_forall in A9 |- *. intros x Hx. apply A9. apply SUB. exact Hx.
Qed.

(* [comment removed for export] *)
Definition sec_not_live_after__stmt : Prop := forall L st cs (p : aptr) mb ms n s,
  asec_wf L st cs -> Permutation cs (sec_chunks_of st) ->
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) ->
  ~ sec_live s (CSec mb ms n).
Section Zd2.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 0).
Variable st : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 1).
Variable cs : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 2).
Variable p : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 3).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 4).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 5).
Variable n : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 6).
Variable s : ltac2:(SecDietF.SzSecF.ty 'sec_not_live_after__stmt 7).
#[using="Type"] Lemma sec_not_live_after__body : ltac:(let T := type of (fun (h : sec_not_live_after__stmt) => h L st cs p mb ms n s) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (st, (cs, (p, (mb, (ms, (n, s)))))))) as _.
  intros WFS PC LIVE EL [q Hq]. rewrite EL in Hq.
  apply lookup_delete_Some in Hq. destruct Hq as [NE Hq].
  (nd_pre WFS 7%nat; intros _ _ _ _ _ _ [ND _]; nd_post).
  (* [comment removed for export] *)
  pose proof (map_to_list_delete (a_live st) p (CSec mb ms n) LIVE) as P1.
  assert (Hq' : delete p (a_live st) !! q = Some (CSec mb ms n)) by (rewrite lookup_delete_ne by exact NE; exact Hq).
  pose proof (map_to_list_delete (delete p (a_live st)) q (CSec mb ms n) Hq') as P2.
  assert (P : Permutation ((p, CSec mb ms n) :: (q, CSec mb ms n) :: map_to_list (delete q (delete p (a_live st)))) (map_to_list (a_live st))).
  { eapply Permutation_trans; [apply perm_skip; exact P2| exact P1]. }
  apply (Permutation_map snd) in P. cbn [map snd] in P. apply filter_is_sec_perm in P. cbn [List.filter is_sec] in P.
  assert (P3 : Permutation (CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st)))))
                                 ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))) cs).
  { eapply Permutation_trans; [| apply Permutation_sym; exact PC]. unfold sec_chunks_of, achunks. rewrite filter_is_sec_app.
    change (CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st)))
      with ((CSec mb ms n :: CSec mb ms n :: List.filter is_sec (map snd (map_to_list (delete q (delete p (a_live st)))))) ++ List.filter is_sec (flat_map b_chunks (a_qloc st ++ a_qglob st))).
    apply Permutation_app_tail. exact P. }
  pose proof (Permutation_NoDup (Permutation_sym P3) ND) as ND2. cbn [app] in ND2.
  inversion ND2 as [|x l NI ND3]; subst. apply NI. left. reflexivity.
Qed.
End Zd2.
#[using="Type"] Lemma sec_not_live_after : ltac:(let t := eval cbv delta [sec_not_live_after__stmt] in sec_not_live_after__stmt in exact t).
Proof. exact sec_not_live_after__body. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma sec_live_other : forall st (p : aptr) mb ms n s ch,
  (a_live st) !! p = Some (CSec mb ms n) -> a_live s = delete p (a_live st) -> ch <> CSec mb ms n ->
  (sec_live s ch <-> sec_live st ch).
Proof.
  intros st p mb ms n s ch LIVE EL NE. unfold sec_live. rewrite EL. split; intros [q Hq].
  - apply lookup_delete_Some in Hq. destruct Hq as [_ Hq]. exists q. exact Hq.
  - exists q. rewrite lookup_delete_ne; [exact Hq|]. intros ->. apply NE. pose proof (eq_trans (eq_sym Hq) LIVE) as XX. injection XX as <-. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="Type"] Lemma sec_wf1_facts' : forall L mb ms n, sec_wf1 L (CSec mb ms n) ->
     mb mod 4096 = 0 /\ ablk mb (mb + ms) /\ mb + ms <= ATOP /\ ms = sec_map_size n /\ 64512 < n <= AREQMAX
  /\ rz_size n = 2048 /\ 73728 <= ms <= 536821760 /\ ms mod 4096 = 0 /\ needed_size n + 4096 <= ms /\ 0 <= needed_size n
  /\ sec_clear L mb ms /\ is_primary n = false /\ n + 6144 <= needed_size n + 4096.
Proof.
  intros L mb ms n W. pose proof W as W0. destruct W0 as (MAL & MLO & MCE & MSE & NB & NPR & SCL).
  (pose proof (sec_facts n ltac:(lia) NPR) as ndP__; nd_pre ndP__ 10%nat; intros _ RZ _ RS1 _ NS MS MSB MSAL MSR; nd_post). rewrite <- MSE in MSB, MSAL, MSR.
  unfold AREQMAX in *.
  repeat (lazymatch goal with |- _ /\ _ => split end); first [assumption| reflexivity| lia].
Qed.

(* [comment removed for export] *)
Definition read_chunk_sec__stmt : Prop := forall cs L st X m (p : aptr) mb ms n,
  ASECc cs L st X m -> Permutation cs (sec_chunks_of st) -> (a_live st) !! p = Some (CSec mb ms n) ->
  let hm := mb + 6128 in
  exists order i b1 ctx uw,
     Permutation order cs /\ nth_error order i = Some (CSec mb ms n) /\ (i < length order)%nat
  /\ Z.of_nat (length order) = a_nsec st
  /\ Forall (sec_wf1 L) order /\ sec_disjoint order
  /\ u64arr asegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
  /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
  /\ (forall j ch, nth_error order j = Some ch -> exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat j) lv)
  /\ asec_chunk m (CSec mb ms n) (Z.of_nat i) true
  /\ rw_cells asegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 (Z.of_nat i))]
  /\ rw_cells asegs m hm [C1 (Z_to_bv 8 2); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31
  /\ rw_cells asegs m (hm + 16) [C8 uw] /\ junk_at m (hm + 24) (ms - SEC_UOFF - 8)
  /\ fill_at m (shad mb) 768 0xfa
  /\ rw_cells asegs m (shad (hm + 16)) [CB (Z.to_nat (shlen (rup n 8))) (block_shadow_bytes n)]
  /\ fill_at m (shad (hm + 16) + shlen (rup n 8)) (ms / 8 - 768 - shlen (rup n 8)) 0xfa.
Section Zd3.   (* [comment removed for export] *)
Variable cs : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 0).
Variable L : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 1).
Variable st : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 2).
Variable X : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 3).
Variable m : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 4).
Variable p : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 5).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 6).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 7).
Variable n : ltac2:(SecDietF.SzSecF.ty 'read_chunk_sec__stmt 8).
#[using="Type"] Lemma read_chunk_sec__body : ltac:(let T := type of (fun (h : read_chunk_sec__stmt) => h cs L st X m p mb ms n) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (cs, (L, (st, (X, (m, (p, (mb, (ms, n))))))))) as _.
  intros (WFS & ARR & INST & PZ & SHZ) PC LIVE hm.
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post).
  (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post).
  assert (IN : In (CSec mb ms n) cs) by (eapply Permutation_in; [apply Permutation_sym; exact PC| eapply live_sec_in; exact LIVE]).
  assert (INo : In (CSec mb ms n) order) by (eapply Permutation_in; [apply Permutation_sym; exact PO| exact IN]).
  destruct (In_nth_error _ _ INo) as [i NTH].
  assert (IL : (i < length order)%nat) by (apply (proj1 (nth_error_Some order i)); rewrite NTH; discriminate).
  assert (WF1o : Forall (sec_wf1 L) order).
  { rewrite Forall_forall in WF1 |- *. intros c Hc. apply WF1. eapply Permutation_in; [exact PO| exact Hc]. }
  assert (WDo : sec_disjoint order) by (eapply sec_disjoint_perm; [apply Permutation_sym; exact PO| exact WD]).
  (nd_pre (PER i _ NTH) 3%nat; intros lv LV CH; nd_post).
  assert (Elv : lv = true) by (apply (proj2 LV); exists p; exact LIVE). subst lv.
  pose proof (proj1 (Forall_forall _ _) WF1o _ INo) as Wch.
  (nd_pre (sec_wf1_facts' L mb ms n Wch) 13%nat; intros MAL MLO MCE MSE NB RZ MSB MSAL NMS NS0 SCL NPR N6; nd_post).
  pose proof CH as CH0. cbn [asec_chunk] in CH0.
  (nd_pre CH0 9%nat; intros H1 H2 H3 H4 (b1 & cx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in H5, H6, S2, S3. replace (mb + 6144 - 16) with hm in H5 by (subst hm; lia).
  destruct (junk_split m _ 8 (ms - 6144 - 8) ltac:(replace (8 + (ms - 6144 - 8)) with (ms - 6144) by lia; exact H6) ltac:(lia) ltac:(lia)) as [U8 UR].
  destruct (c8_of_junk m _ U8) as [uw HUW].
  exists order, i, b1, cx, uw.
  split; [exact PO|]. split; [exact NTH|]. split; [exact IL|]. split; [rewrite (Permutation_length PO); exact WL|].
  split; [exact WF1o|]. split; [exact WDo|]. split; [exact U64|]. split; [exact JK|]. split; [exact PER|]. split; [exact CH|].
  split; [exact H1|]. split; [exact H5|]. split; [exact B1|]. split; [exact B3|]. split; [exact CX|].
  replace (hm + 16) with (mb + 6144) by (subst hm; lia). replace (hm + 24) with (mb + 6144 + 8) by (subst hm; lia).
  split; [exact HUW|]. split; [unfold SEC_UOFF; exact UR|]. split; [exact S1|].
  rewrite <- (granules_rup n) by lia. unfold sec_user_shadow in S2. split; [exact S2| exact S3].
Qed.
End Zd3.
#[using="Type"] Lemma read_chunk_sec : ltac:(let t := eval cbv delta [read_chunk_sec__stmt] in read_chunk_sec__stmt in exact t).
Proof. exact read_chunk_sec__body. Qed.

(* [comment removed for export] *)
Definition asec_chunk_frameD'__stmt : Prop := forall L W m m' mb ms n idx lv,
  munch W m m' -> sec_wf1 L (CSec mb ms n) ->
  (forall A k, mb + 32 <= A -> 0 < k -> A + k <= mb + ms -> disjoint_from W A k) ->
  (forall A k, shad mb <= A -> 0 < k -> A + k <= shad mb + ms / 8 -> disjoint_from W A k) ->
  rw_cells asegs m' mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)] ->
  (exists idx0, asec_chunk m (CSec mb ms n) idx0 lv) -> asec_chunk m' (CSec mb ms n) idx lv.
Section Zd4.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 0).
Variable W : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 1).
Variable m : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 2).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 3).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 4).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 5).
Variable n : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 6).
Variable idx : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 7).
Variable lv : ltac2:(SecDietF.SzSecF.ty 'asec_chunk_frameD'__stmt 8).
#[using="Type"] Lemma asec_chunk_frameD'__body : ltac:(let T := type of (fun (h : asec_chunk_frameD'__stmt) => h L W m m' mb ms n idx lv) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (W, (m, (m', (mb, (ms, (n, (idx, lv))))))))) as _.
  intros MU WF1 DC DS HDR [idx0 CH].
  pose proof WF1 as WF0. cbn [sec_wf1] in WF0. (nd_pre WF0 7%nat; intros G1 G2 G3 G4 G5 G6 _; nd_post).
  (pose proof (sec_facts n ltac:(lia) G6) as ndP__; nd_pre ndP__ 10%nat; intros _ _ RSE RSR _ NSE _ MSR MSM _; nd_post). rewrite <- G4 in MSR, MSM.
  assert (GR : 0 <= granules n /\ shad (mb + SEC_UOFF) = shad mb + 768 /\ 768 + granules n <= ms / 8).
  { unfold granules, SEC_UOFF. rewrite !shad_div, shlen_div. clear -G1 G5 RSR NSE MSR MSM. Z.div_mod_to_equations. lia. }
  (nd_pre GR 3%nat; intros GR1 GR2 GR3; nd_post).
  cbn [asec_chunk] in CH |- *. (nd_pre CH 9%nat; intros H1 H2 H3 H4 (b1 & ctx & H5 & B1 & B3 & CX) H6 S1 S2 S3; nd_post).
  unfold SEC_UOFF in *.
  split; [exact HDR|].
  split; [eapply junk_frameD; [exact H2| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply cells_frameD; [exact H3| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply junk_frameD; [exact H4| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split. { exists b1, ctx. split; [| split; [exact B1| split; [exact B3| exact CX]]].
           eapply cells_frameD; [exact H5| exact MU| cbn; apply DC; clear -RSR NSE MSR G4 G5; lia]. }
  split; [eapply junk_frameD; [exact H6| exact MU| intros _; apply DC; clear -RSR NSE MSR G4 G5; lia]|].
  split; [eapply fill_frameD; [exact S1| exact MU| intros _; apply DS; clear -GR3 GR1; lia]|].
  assert (GRP : 0 < granules n) by (unfold granules; rewrite shlen_div; clear -G5; Z.div_mod_to_equations; lia).
  split; [eapply cells_frameD; [exact S2| exact MU| cbn; rewrite Nat.add_0_r, Z2Nat.id by exact GR1; rewrite GR2; apply DS; clear -GR3 GR1 GRP; lia]|].
  eapply fill_frameD; [exact S3| exact MU| intros POS; rewrite GR2; apply DS; clear -GR3 GR1 POS; lia].
Qed.
End Zd4.
#[using="Type"] Lemma asec_chunk_frameD' : ltac:(let t := eval cbv delta [asec_chunk_frameD'__stmt] in asec_chunk_frameD'__stmt in exact t).
Proof. exact asec_chunk_frameD'__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_same0 (st st' : astate) : Prop :=
     a_nsec st' = a_nsec st /\ a_nres st' = a_nres st /\ a_ptr_array st' = a_ptr_array st
  /\ (forall ch, is_sec ch = true -> (sec_live st' ch <-> sec_live st ch)).

Definition asecc_frame__stmt : Prop := forall cs L W m m' st st' X X',
  ASECc cs L st X m -> munch W m m' -> wmono asegs m m' -> sec_untouched L W -> sec_same0 st st' ->
  ASECc cs L st' X' m'.
Section Zd5.   (* [comment removed for export] *)
Variable cs : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 0).
Variable L : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 1).
Variable W0 : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 2).
Variable m : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 3).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 4).
Variable st : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 5).
Variable st' : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 6).
Variable X : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 7).
Variable X' : ltac2:(SecDietF.SzSecF.ty 'asecc_frame__stmt 8).
#[using="Type"] Lemma asecc_frame__body : ltac:(let T := type of (fun (h : asecc_frame__stmt) => h cs L W0 m m' st st' X X') in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (cs, (L, (W0, (m, (m', (st, (st', (X, X'))))))))) as _.
  intros (WFS & ARR & INST & PZ & SHZ) MU0 WM SU0 (EN & ER & EP & EL).
  (pose proof WFS as ndP__; nd_pre ndP__ 7%nat; intros ALO WP WR WL WB WF1 WD; nd_post).
  pose proof (munch_filter_nonempty W0 m m' MU0) as MU. pose proof (sec_untouched_filter L W0 SU0) as SU. pose proof (nonempty_filter W0) as NE.
  set (W := List.filter nonempty W0) in MU, SU, NE.
  assert (ALLSEC : forall ch, In ch cs -> exists mb ms n, ch = CSec mb ms n /\ sec_wf1 L (CSec mb ms n)).
  { intros ch Hin. pose proof (proj1 (Forall_forall _ _) WF1 ch Hin) as W1. destruct ch as [c n|mb ms n]; [destruct W1|].
    exists mb, ms, n. split; [reflexivity| exact W1]. }
  split; [| split; [| split; [| split]]].
  - unfold asec_wf. rewrite EP, ER, EN. exact WFS.
  - (nd_pre ARR 5%nat; intros order PO U64 JK PER; nd_post). exists order.
    assert (LEN : Z.of_nat (length order) = a_nsec st) by (rewrite (Permutation_length PO); exact WL).
    split; [exact PO|]. split; [| split].
    + destruct order as [|o0 order'].
      * destruct U64 as [[B0 [B1 _]] [V0 [V1 _]]]. split; [split; [exact B0| split; [exact B1| cbn; intros; lia]] | split; [exact V0| split; [exact V1| cbn; intros; lia]]].
      * eapply u64arr_frame; [exact U64| exact MU| exact WM|]. rewrite length_map. apply (D_ptr L W0 SU0 ALO); cbn [length] in LEN |- *; clear -LEN WB WR; lia.
    + rewrite EN, ER. eapply junk_frame; [exact JK| exact MU| exact WM|]. intros POS. apply (D_ptr L W0 SU0 ALO); clear -POS WB WR; lia.
    + intros i ch Hi. (nd_pre (PER i ch Hi) 3%nat; intros lv LV CH; nd_post).
      assert (Hin : In ch cs) by (eapply Permutation_in; [exact PO| eapply nth_error_In; exact Hi]).
      (nd_pre (ALLSEC ch Hin) 4%nat; intros mb ms n ndR1__; nd_post; destruct ndR1__ as (-> & ndR2__); rename ndR2__ into W1).
      exists lv. split; [| eapply (asec_chunk_frame L W0 m m' MU0 WM SU0 ALO); [exact W1| exact CH]].
      rewrite LV. apply iff_sym. apply EL. reflexivity.
  - (nd_pre INST 6%nat; intros I1 [srt I2] I3 I4 I5 I6; nd_post). unfold asec_inst. unfold AINSTANCE in *.
    split; [eapply cells_frame; [exact I1| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [exists srt; eapply cells_frame; [exact I2| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I3| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply junk_frame; [exact I4| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    split; [eapply cells_frame; [exact I5| exact MU| exact WM| cbn; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia]|].
    eapply junk_frame; [exact I6| exact MU| exact WM| intros _; apply (D_inst L W0 SU0 ALO); unfold AINSTANCE; lia].
  - unfold aprim0 in *. eapply azero_frame; [exact PZ| exact MU| exact WM|]. intros POS.
    apply (su_disjoint L); [exact SU| exact NE| exact POS|]. intros a Ha. apply (clear_prim0 L ALO). exact Ha.
  - intros x Hx HF HC.
    assert (SX : 0 <= shad x < 2^64) by (pose proof atop_range as ATR; rewrite shad_div; unfold ASHOFF, K_HIGH_MEM, AIMG_HI, KLS in *; clear -Hx ATR; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    rewrite <- (SHZ x Hx HF HC). apply MU. rewrite wa_unsigned by exact SX.
    eapply (disjoint_outside W (shad x) 1); [| clear; lia].
    apply (su_disjoint L); [exact SU| exact NE| clear; lia|]. intros a Ha K. apply (clear_free_shadow L ALO x Hx HF). replace (shad x) with a by (clear -Ha; lia). exact K.
Qed.
End Zd5.
#[using="Type"] Lemma asecc_frame : ltac:(let t := eval cbv delta [asecc_frame__stmt] in asecc_frame__stmt in exact t).
Proof. exact asecc_frame__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition depot_frameD_law (AD : alayout -> amem -> Prop) : Prop :=
  forall L m m' W, AD L m -> munch W m m' ->
    Forall (fun iv => forall a, fst iv <= a < snd iv ->
              ~ (0x1808c8 <= a < 0x5d0910) /\ ~ (al_nodes L <= a < al_nodes L + 1048576) /\ ~ (al_store L <= a < al_store L + 8388608)) W ->
    AD L m'.
(* [comment removed for export] *)
Definition fake_frameD_law (AFK : alayout -> list ablock -> amem -> Prop) : Prop :=
  forall L LB m m' W, AFK L LB m -> munch W m m' -> fake_untouched L W ->
    Forall (fun iv => snd iv <= al_t L + 48 \/ al_t L + 64 <= fst iv) W -> AFK L LB m'.

#[using="Type"] Lemma dc_at_frameD : forall W m m' A n, dc_at m A n -> munch W m m' -> (0 < n -> disjoint_from W A n) -> dc_at m' A n.
Proof. intros W m m' A n H MU D. exact (junk_frameD W m m' A n H MU D). Qed.

Definition afake_frameD__stmt : Prop := fake_frameD_law AFAKE.
Section Zd6.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 0).
Variable LB : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 1).
Variable m : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 2).
Variable m' : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 3).
Variable W : ltac2:(SecDietF.SzSecF.ty 'afake_frameD__stmt 4).
#[using="Type"] Lemma afake_frameD__body : ltac:(let T := type of (fun (h : afake_frameD__stmt) => h L LB m m' W) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (LB, (m, (m', W))))) as _.
  intros (G & CE & (h0 & h1 & h2 & hs & HS) & LOG & NGC & DC1 & DC2 & FL & LV) MU UT UT2.
  (pose proof G as ndP__; nd_pre ndP__ 11%nat; intros G1 G2 G3 G4 G5 G6 G7 G8 G9 G10 G11; nd_post). unfold FAKESZ in *. (pose proof (ablk_lin _ _ G2) as ndP__; nd_pre ndP__ 4%nat; intros GL1 GL2 GL3 GL4; nd_post).   (* [comment removed for export] *)
  assert (DF : disjoint_from W (al_fake L) 11571200) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X1).
  assert (DS : disjoint_from W (shad (al_fake L)) (shlen 11571200)) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X2).
  assert (DD : disjoint_from W (al_dtls L) 4096) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X3).
  assert (D1 : disjoint_from W 0xa7668 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X4).
  assert (D2 : disjoint_from W (ATPv + -8) 16) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X5).
  assert (D3 : disjoint_from W (ATPv + 8) 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X6).
  assert (D4 : disjoint_from W (ATPv + 296) 8) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X7).
  assert (D5 : disjoint_from W 0x1405b1 1) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X8).
  assert (D6 : disjoint_from W 0x13e498 4) by (apply disjoint_from_Forall; eapply Forall_impl; [|exact UT]; cbv beta; intros iv (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9); exact X9).
  assert (DT : disjoint_from W (al_t L + 48) 16).
  { apply disjoint_from_Forall. eapply Forall_impl; [| exact UT2]. cbv beta. intros iv Hiv. lia. }
  split; [exact G|].
  split.
  { (nd_pre CE 8%nat; intros C1 C2 C3 C4 C5 C6 C7 C8; nd_post). unfold afake_cells.
    repeat lazymatch goal with |- _ /\ _ => split end;
      try (eapply rw_cells_transportD; [eassumption| exact MU| cbn [cells_size csize Nat.add]; first [assumption | eapply disjoint_from_sub; [exact DD| lia| lia| lia]]]).
    eapply dc_at_frameD; [exact C8| exact MU| intros _; exact DT]. }
  split.
  { exists h0, h1, h2, hs. eapply rw_cells_transportD; [exact HS| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]. }
  split; [eapply rw_cells_transportD; [exact LOG| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply rw_cells_transportD; [exact NGC| exact MU| cbn; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split; [eapply dc_at_frameD; [exact DC1| exact MU| intros _; unfold FAKESZ; eapply disjoint_from_sub; [exact DF| lia| lia| lia]]|].
  split.
  { eapply dc_at_frameD; [exact DC2| exact MU| intros _; unfold FAKESZ; exact DS]. }
  split.
  - intros c pos b Hc Hp Hb NZ. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) in Hb by (assumption || lia). eauto.
  - intros c F n Hin. (nd_pre (LV c F n Hin) 6%nat; intros Hc Hn pos Hp HF Hb; nd_post). split; [exact Hc|]. split; [exact Hn|].
    exists pos. split; [exact Hp|]. split; [exact HF|]. pose proof (fk_flag_range L c pos Hc Hp).
    rewrite (munch_outside_range W m m' (al_fake L) 11571200) by (assumption || lia). exact Hb.
Qed.
End Zd6.
#[using="Type"] Lemma afake_frameD : ltac:(let t := eval cbv delta [afake_frameD__stmt] in afake_frameD__stmt in exact t).
Proof. exact afake_frameD__body. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qcoupled_add1_sec__stmt : Prop := forall L s s' X X' Q Q' mb ms n k (newb : list xbusy),
  qcoupled L s X Q ->
  length (q_loc Q') = length (a_qloc s') -> length (q_glob Q') = length (a_qglob s') ->
  Permutation (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q'))
              ((CSec mb ms n, k) :: qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)) ->
  Permutation (map qb_slot (q_loc Q' ++ q_glob Q')) (map xb_slot newb ++ map qb_slot (q_loc Q ++ q_glob Q)) ->
  (forall y, In y (x_busy X') /\ xb_st y = BQuar <-> In y (x_busy X) /\ xb_st y = BQuar) ->
  (forall y, In y (x_busy X') /\ xb_st y = BBatch <-> (In y (x_busy X) /\ xb_st y = BBatch) \/ In y newb) ->
  Forall (fun y => xb_st y = BBatch /\ xb_class y = K_BATCH_CLASS /\ 0 <= xb_slot y) newb ->
  (forall y, In y (x_busy X) -> xb_st y = BBatch -> xb_class y = K_BATCH_CLASS -> In (xb_slot y) (map xb_slot newb) -> False) ->
  List.NoDup (map xb_slot newb) ->
  q_pend Q' = q_pend Q ->
  qcoupled L s' X' Q'.
Section Zd7.   (* [comment removed for export] *)
Variable L : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 0).
Variable s : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 1).
Variable s' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 2).
Variable X : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 3).
Variable X' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 4).
Variable Q : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 5).
Variable Q' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 6).
Variable mb : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 7).
Variable ms : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 8).
Variable n : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 9).
Variable k : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 10).
Variable newb : ltac2:(SecDietF.SzSecF.ty 'qcoupled_add1_sec__stmt 11).
#[using="Type"] Lemma qcoupled_add1_sec__body : ltac:(let T := type of (fun (h : qcoupled_add1_sec__stmt) => h L s s' X X' Q Q' mb ms n k newb) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (L, (s, (s', (X, (X', (Q, (Q', (mb, (ms, (n, (k, newb)))))))))))) as _.
  intros (LN1 & LN2 & OK & ND1 & ND2 & BS & PS & NN) L1 L2 PE PB HQ HB NEWB FB NDB PD.
  assert (PEQ : Permutation (qprim_ids (qentries (a_qloc s') (q_loc Q') ++ qentries (a_qglob s') (q_glob Q')))
                             (qprim_ids (qentries (a_qloc s) (q_loc Q) ++ qentries (a_qglob s) (q_glob Q)))).
  { pose proof (qprim_ids_perm _ _ PE) as P. cbn [qprim_ids flat_map fst snd app] in P. exact P. }
  unfold qcoupled. cbv zeta. rewrite PD.
  split; [exact L1|]. split; [exact L2|]. split.
  { eapply Permutation_Forall; [apply Permutation_sym; exact PE|]. constructor; [exact I|].
    eapply Forall_impl; [| exact OK]. intros [ch k'] HOK. unfold qentry_ok in *. cbn [fst snd] in *.
    destruct ch as [c' n'| mb' ms' n']; [| exact I]. (nd_pre HOK 3%nat; intros b1' ctx' Hin; nd_post). exists b1', ctx'.
    apply (proj1 (proj2 (HQ _) (conj Hin eq_refl))). }
  split; [eapply Permutation_NoDup'; [apply Permutation_app_tail; apply Permutation_sym; exact PEQ| exact ND1]|].
  split.
  { eapply Permutation_NoDup'; [apply Permutation_sym; exact PB|]. apply List.NoDup_app; [exact NDB| exact ND2|].
    intros k0 Hn Ho. apply (BS k0) in Ho. (nd_pre Ho 5%nat; intros y Hy Sy Cy Ky; nd_post). subst k0. exact (FB y Hy Sy Cy Hn). }
  split.
  { intros k0. split.
    - intros H. apply (Permutation_in _ PB) in H. apply in_app_iff in H. destruct H as [H|H].
      + apply in_map_iff in H. (nd_pre H 2%nat; intros y ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hy). (pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as ndP__; nd_pre ndP__ 3%nat; intros Sy Cy _; nd_post).
        exists y. split; [apply (proj1 (proj2 (HB y) (or_intror Hy)))|]. auto.
      + apply (BS k0) in H. (nd_pre H 5%nat; intros y Hy Sy Cy Ky; nd_post). exists y. split; [apply (proj1 (proj2 (HB y) (or_introl (conj Hy Sy))))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_sym; exact PB|]. apply in_app_iff.
      destruct (proj1 (HB y) (conj Hy Sy)) as [[Hy0 _]|Hn].
      + right. apply (BS k0). exists y. auto.
      + left. subst k0. apply in_map. exact Hn. }
  split.
  { intros c0 k0. split.
    - intros H. apply (Permutation_in _ (Permutation_app_tail (q_pend Q) PEQ)) in H.
      apply (PS c0 k0) in H. (nd_pre H 5%nat; intros y Hy Sy Cy Ky; nd_post). exists y. split; [apply (proj1 (proj2 (HQ y) (conj Hy Sy)))|]. auto.
    - intros (y & Hy & Sy & Cy & Ky). eapply Permutation_in; [apply Permutation_app_tail; apply Permutation_sym; exact PEQ|].
      apply (PS c0 k0). exists y. pose proof (proj1 (HQ y) (conj Hy Sy)) as [Hy0 _]. auto. }
  eapply Permutation_Forall; [apply Permutation_sym; exact PB|]. apply Forall_app. split; [| exact NN].
  apply Forall_forall. intros k0 H. apply in_map_iff in H. (nd_pre H 2%nat; intros y ndR1__; nd_post; destruct ndR1__ as (<- & ndR2__); rename ndR2__ into Hy).
  (pose proof (proj1 (Forall_forall _ _) NEWB y Hy) as ndP__; nd_pre ndP__ 3%nat; intros _ _ P; nd_post). exact P.
Qed.
End Zd7.
#[using="Type"] Lemma qcoupled_add1_sec : ltac:(let t := eval cbv delta [qcoupled_add1_sec__stmt] in qcoupled_add1_sec__stmt in exact t).
Proof. exact qcoupled_add1_sec__body. Qed.

Section QUpdatesS.
Variables (L : alayout) (st : astate) (X : aconc) (Q : qconc) (mb ms n : Z).
Let ch := CSec mb ms n.
Hypothesis WF : awf L st X.
Hypothesis CP : qcoupled L st X Q.

(* [comment removed for export] *)
Definition qcoupled_app_sec__stmt : Prop := forall s' l bl ql qz ia k,
  a_qloc st = l ++ [bl] -> q_loc Q = ql ++ [qz] ->
  a_qloc s' = l ++ [mkABatch (b_count bl + 1) (b_size bl + n) (ch :: b_chunks bl)] -> a_qglob s' = a_qglob st ->
  qcoupled L s' X (mkQConc (ql ++ [mkQB (qb_slot qz) (k :: qb_ks qz)]) (q_glob Q) ia (q_pend Q)).
Section Zd8.   (* [comment removed for export] *)
Variable s' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 0).
Variable l : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 1).
Variable bl : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 2).
Variable ql : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 3).
Variable qz : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 4).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 5).
Variable k : ltac2:(SecDietF.SzSecF.ty 'qcoupled_app_sec__stmt 6).
#[using="CP"] Lemma qcoupled_app_sec__body : ltac:(let T := type of (fun (h : qcoupled_app_sec__stmt) => h s' l bl ql qz ia k) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (s', (l, (bl, (ql, (qz, (ia, k))))))) as _.
  intros QL QQ QL' QG'.
  pose proof CP as CP0. (nd_pre CP0 3%nat; intros LN1 LN2 _; nd_post).
  assert (LNl : length ql = length l).
  { rewrite QL, QQ, !length_app in LN1. cbn in LN1. lia. }
  eapply (qcoupled_add1_sec L st s' X X Q _ mb ms n k []); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG', QL, QQ. rewrite !qentries_app by exact LNl. cbn [qentries combine b_chunks qb_ks app].
    rewrite <- !app_assoc. cbn [app]. apply Permutation_sym. rewrite ?app_nil_r.
    apply Permutation_middle.
  - cbn [q_loc q_glob map app]. rewrite QQ, !map_app. cbn [map qb_slot]. apply Permutation_refl.
  - intros y; tauto.
  - intros y. cbn [In]. tauto.
  - constructor.
  - intros y _ _ _ [].
  - constructor.
  - reflexivity.
Qed.
End Zd8.
#[using="CP"] Lemma qcoupled_app_sec : ltac:(let t := eval cbv delta [qcoupled_app_sec__stmt] in qcoupled_app_sec__stmt in exact t).
Proof. exact qcoupled_app_sec__body. Qed.

(* [comment removed for export] *)
Definition qcoupled_new_sec__stmt : Prop := forall s' k24 cnt sz ia k,
  c_count (get_cls st K_BATCH_CLASS) = cnt -> 0 < cnt ->
  nth_error (xc_cache (x_cls X K_BATCH_CLASS)) (Z.to_nat (cnt - 1)) = Some k24 ->
  a_qloc s' = a_qloc st ++ [mkABatch 1 sz [ch]] -> a_qglob s' = a_qglob st ->
  qcoupled L s' (xbatch X k24) (mkQConc (q_loc Q ++ [mkQB k24 [k]]) (q_glob Q) ia (q_pend Q)).
Section Zd9.   (* [comment removed for export] *)
Variable s' : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 0).
Variable k24 : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 1).
Variable cnt : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 2).
Variable sz : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 3).
Variable ia : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 4).
Variable k : ltac2:(SecDietF.SzSecF.ty 'qcoupled_new_sec__stmt 5).
#[using="rc WF CP"] Lemma qcoupled_new_sec__body : ltac:(let T := type of (fun (h : qcoupled_new_sec__stmt) => h s' k24 cnt sz ia k) in lazymatch (eval cbv beta in T) with _ -> ?B => exact B end).
Proof.
  pose proof (fun (_ : True) => (s', (k24, (cnt, (sz, (ia, k)))))) as _.
  intros CNT POS NK QL' QG'.
  pose proof CP as CP0. (nd_pre CP0 7%nat; intros LN1 LN2 _ _ _ BS _; nd_post).
  (pose proof (k24_not_busy L _ X k24 cnt WF CNT POS NK) as ndP__; nd_pre ndP__ 3%nat; intros NB KR _; nd_post).
  eapply (qcoupled_add1_sec L st s' X (xbatch X k24) Q _ mb ms n k [bbatch k24]); try exact CP.
  - cbn [q_loc]. rewrite QL', !length_app. cbn. lia.
  - cbn [q_glob]. rewrite QG'. exact LN2.
  - cbn [q_loc q_glob]. rewrite QL', QG'. rewrite !qentries_app by exact LN1. cbn [qentries combine b_chunks qb_ks app].
    apply Permutation_sym. rewrite <- ?app_assoc. cbn [app]. apply Permutation_middle.
  - cbn [q_loc q_glob map xb_slot bbatch]. rewrite <- app_assoc, !map_app. cbn [map qb_slot app]. apply Permutation_sym.
    apply Permutation_middle.
  - intros y. rewrite (In_xbatch X k24 y). unfold bbatch. split.
    + intros [[-> |H] S]; [cbn in S; discriminate| exact (conj H S)].
    + intros [H S]. split; [right; exact H| exact S].
  - intros y. rewrite (In_xbatch X k24 y). cbn [In]. split.
    + intros [[-> |H] S]; [right; left; reflexivity| left; exact (conj H S)].
    + intros [[H S]|[<-|[]]]; [split; [right; exact H| exact S]| split; [left; reflexivity| reflexivity]].
  - constructor; [| constructor]. cbn. split; [reflexivity|]. split; [reflexivity| lia].
  - intros y Hy Sy Cy Hin. cbn in Hin. destruct Hin as [E|[]]. apply NB.
    unfold busy_slots. rewrite E. apply in_map. apply List.filter_In. split; [exact Hy| rewrite Cy; apply Z.eqb_refl].
  - constructor; [intros []| constructor].
  - reflexivity.
Qed.
End Zd9.
#[using="rc WF CP"] Lemma qcoupled_new_sec : ltac:(let t := eval cbv delta [qcoupled_new_sec__stmt] in qcoupled_new_sec__stmt in exact t).
Proof. exact qcoupled_new_sec__body. Qed.
End QUpdatesS.
End CANSEC1.
(* [comment removed for export] *)
End TwB.
End ASF_kit.
