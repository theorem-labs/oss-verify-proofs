(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase ABytes ARep ARepKit ARepFrame ALayout AHeapP. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison. From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import APoisonR_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AExh.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition sec_live (st : astate) (ch : achunk) : Prop := exists p, (a_live st) !! p = Some ch.
Definition SEC_MAGIC : Z := 0xCC6E96B9CC6E96B9.

Definition sec_disjoint (cs : list achunk) : Prop :=
  List.NoDup cs /\
  forall ci cj, In ci cs -> In cj cs -> ci <> cj ->
    sec_mb ci + sec_ms ci <= sec_mb cj \/ sec_mb cj + sec_ms cj <= sec_mb ci.
Lemma sec_disjoint_nil : sec_disjoint [].
Proof. split; [constructor| intros ci cj [] ]. Qed.
Lemma sec_disjoint_perm : forall cs cs', Permutation cs cs' -> sec_disjoint cs -> sec_disjoint cs'.
Proof.
  intros cs cs' P [ND D]. split; [eapply Permutation_NoDup; [exact P| exact ND]|].
  intros ci cj Hi Hj NE. apply D; [| | exact NE]; (eapply Permutation_in; [apply Permutation_sym; exact P| assumption]).
Qed.

Definition asec_wf (L : alayout) (st : astate) (cs : list achunk) : Prop :=
     alayout_ok L
  /\ a_ptr_array st = al_ptr_array L
  /\ (a_nres st mod 16384 = 0 /\ 0 <= a_nres st <= 1048576) /\ Z.of_nat (length cs) = a_nsec st /\ 0 <= a_nsec st <= a_nres st

  /\ Forall (sec_wf1 L) cs /\ sec_disjoint cs.

Definition sec_user_shadow (lv : bool) (n : Z) : list byte :=
  if lv then block_shadow_bytes n else repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)).

Lemma granules_eq : forall n, 0 <= n -> granules n = shlen n + (if n mod 8 =? 0 then 0 else 1).
Proof.
  intros n N. unfold granules, shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia.
Qed.
Lemma sec_user_shadow_length : forall lv n, 0 <= n -> length (sec_user_shadow lv n) = Z.to_nat (granules n).
Proof.
  intros lv n N. unfold sec_user_shadow. destruct lv; [| apply repeat_length].
  unfold block_shadow_bytes. rewrite length_app, repeat_length, granules_eq by lia.
  pose proof (proj2 (Z.shiftr_nonneg n 3) N) as S. unfold shlen in *. destruct (n mod 8 =? 0); cbn [length]; lia.
Qed.

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

Definition asec_arr (L : alayout) (st : astate) (cs : list achunk) (m : amem) : Prop :=
  exists order : list achunk,
       Permutation order cs
    /\ u64arr asegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
    /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
    /\ (forall i ch, nth_error order i = Some ch ->
          exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat i) lv).

Definition asec_inst (L : alayout) (m : amem) : Prop :=
     rw_cells asegs m 0xd64a8 [C8 (Z_to_bv 64 (al_ptr_array L))]
  /\ (exists srt : byte, rw_cells asegs m 0xd64d8 [C1 srt])
  /\ junk_at m 0xd64e0 32
  /\ junk_at m 0xd6500 512
  /\ rw_cells asegs m 0xd6701 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m 0xd6718 16.

Definition astartup_hulls (L : alayout) : list (Z * Z) :=
  let V := al_V L in
  [(4096 * V 584%nat, 4096 * V 584%nat + 4096); (4096 * V 503%nat, 4096 * V 503%nat + 4096);
   (al_store L, al_store L + 8388608); (al_nodes L, al_nodes L + 1048576); (al_fake L, al_fake L + 11571200);
   (al_dtls L, al_dtls L + 4096); (4096 * V 258%nat, 4096 * V 258%nat + 4096); (al_ctx L, al_ctx L + 65536);
   (al_t L, al_t L + 4096); (al_res L, al_res L + 137439023104);
   (4096 * V 220%nat, 4096 * V 220%nat + 0x38e000); (4096 * V 91%nat, 4096 * V 91%nat + 0x10000);
   (al_ptr_array L, al_ptr_array L + 8388608)].

Definition ashz (L : alayout) (cs : list achunk) (m : amem) : Prop :=
  forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
    Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
    Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) cs ->
    m (wa (shad x)) = Some (Z_to_bv 8 0).

Definition aprim0 (L : alayout) (m : amem) : Prop := azero m (shad (al_space_beg L)) (shlen K_REGION).

Definition ASECc (cs : list achunk) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
  asec_wf L st cs /\ asec_arr L st cs m /\ asec_inst L m /\ aprim0 L m /\ ashz L cs m /\ AEXHc cs L st m.

Definition ASEC_of (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop := ASECc (sec_chunks_of st) L st X m.

End CANSEC1.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB ABytes.TwinB ARep.TwinB ARepKit.TwinB ARepFrame.TwinB ALayout.TwinB AHeapP.TwinB.

  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison. Import APoisonR_iface.TwinB.
Import AExh.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition sec_live (st : astate) (ch : achunk) : Prop := exists p, (a_live st) !! p = Some ch.
Definition SEC_MAGIC : Z := 0xCC6E96B9CC6E96B9.

Definition sec_disjoint (cs : list achunk) : Prop :=
  List.NoDup cs /\
  forall ci cj, In ci cs -> In cj cs -> ci <> cj ->
    sec_mb ci + sec_ms ci <= sec_mb cj \/ sec_mb cj + sec_ms cj <= sec_mb ci.
Lemma sec_disjoint_nil : sec_disjoint [].
Proof. split; [constructor| intros ci cj [] ]. Qed.
Lemma sec_disjoint_perm : forall cs cs', Permutation cs cs' -> sec_disjoint cs -> sec_disjoint cs'.
Proof.
  intros cs cs' P [ND D]. split; [eapply Permutation_NoDup; [exact P| exact ND]|].
  intros ci cj Hi Hj NE. apply D; [| | exact NE]; (eapply Permutation_in; [apply Permutation_sym; exact P| assumption]).
Qed.

Definition asec_wf (L : alayout) (st : astate) (cs : list achunk) : Prop :=
     alayout_ok L
  /\ a_ptr_array st = al_ptr_array L
  /\ (a_nres st mod 16384 = 0 /\ 0 <= a_nres st <= 1048576) /\ Z.of_nat (length cs) = a_nsec st /\ 0 <= a_nsec st <= a_nres st

  /\ Forall (sec_wf1 L) cs /\ sec_disjoint cs.

Definition sec_user_shadow (lv : bool) (n : Z) : list byte :=
  if lv then block_shadow_bytes n else repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)).

Lemma granules_eq : forall n, 0 <= n -> granules n = shlen n + (if n mod 8 =? 0 then 0 else 1).
Proof.
  intros n N. unfold granules, shlen. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
  destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia.
Qed.
Lemma sec_user_shadow_length : forall lv n, 0 <= n -> length (sec_user_shadow lv n) = Z.to_nat (granules n).
Proof.
  intros lv n N. unfold sec_user_shadow. destruct lv; [| apply repeat_length].
  unfold block_shadow_bytes. rewrite length_app, repeat_length, granules_eq by lia.
  pose proof (proj2 (Z.shiftr_nonneg n 3) N) as S. unfold shlen in *. destruct (n mod 8 =? 0); cbn [length]; lia.
Qed.

Definition asec_chunk (m : amem) (ch : achunk) (idx : Z) (lv : bool) : Prop :=
  match ch with
  | CSec mb ms n =>
      let res := mb + 4096 in let ub := mb + SEC_UOFF in
         rw_cells bsegs m mb [C8 (Z_to_bv 64 mb); C8 (Z_to_bv 64 ms); C8 (Z_to_bv 64 (needed_size n)); C8 (Z_to_bv 64 idx)]
      /\ junk_at m (mb + 32) (4096 - 32)
      /\ rw_cells bsegs m res [C8 (Z_to_bv 64 SEC_MAGIC); C8 (Z_to_bv 64 (ub - 16))]
      /\ junk_at m (res + 16) (2048 - 32)
      /\ (exists b1 ctx, rw_cells bsegs m (ub - 16) [C1 (Z_to_bv 8 (if lv then 2 else 3)); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0);
                                                 C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
                        /\ 0 <= b1 < 256 /\ Z.land b1 3 = 1 /\ 0 <= ctx < 2^31)
      /\ junk_at m ub (ms - SEC_UOFF)
      /\ fill_at m (shad mb) 768 0xfa
      /\ rw_cells bsegs m (shad ub) [CB (Z.to_nat (granules n)) (sec_user_shadow lv n)]
      /\ fill_at m (shad ub + granules n) (ms / 8 - 768 - granules n) 0xfa
  | CPrim _ _ => False
  end.

Definition asec_arr (L : alayout) (st : astate) (cs : list achunk) (m : amem) : Prop :=
  exists order : list achunk,
       Permutation order cs
    /\ u64arr bsegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
    /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
    /\ (forall i ch, nth_error order i = Some ch ->
          exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat i) lv).

Definition asec_inst (L : alayout) (m : amem) : Prop :=
     rw_cells bsegs m 0xd8668 [C8 (Z_to_bv 64 (al_ptr_array L))]
  /\ (exists srt : byte, rw_cells bsegs m 0xd8698 [C1 srt])
  /\ junk_at m 0xd86a0 32
  /\ junk_at m 0xd86c0 512
  /\ rw_cells bsegs m 0xd88c1 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m 0xd88d8 16.

Definition astartup_hulls (L : alayout) : list (Z * Z) :=
  let V := al_V L in
  [(4096 * V 584%nat, 4096 * V 584%nat + 4096); (4096 * V 503%nat, 4096 * V 503%nat + 4096);
   (al_store L, al_store L + 8388608); (al_nodes L, al_nodes L + 1048576); (al_fake L, al_fake L + 11571200);
   (al_dtls L, al_dtls L + 4096); (4096 * V 258%nat, 4096 * V 258%nat + 4096); (al_ctx L, al_ctx L + 65536);
   (al_t L, al_t L + 4096); (al_res L, al_res L + 137439023104);
   (4096 * V 220%nat, 4096 * V 220%nat + 0x38e000); (4096 * V 91%nat, 4096 * V 91%nat + 0x10000);
   (al_ptr_array L, al_ptr_array L + 8388608)].

Definition ashz (L : alayout) (cs : list achunk) (m : amem) : Prop :=
  forall x, (AIMG_HI <= x < KLS \/ K_HIGH_MEM <= x < ATOP) ->
    Forall (fun iv => ~ (fst iv <= x < snd iv)) (astartup_hulls L) ->
    Forall (fun ch => ~ (sec_mb ch <= x < sec_mb ch + sec_ms ch)) cs ->
    m (wa (shad x)) = Some (Z_to_bv 8 0).

Definition aprim0 (L : alayout) (m : amem) : Prop := azero m (shad (al_space_beg L)) (shlen K_REGION).

Definition ASECc (cs : list achunk) (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop :=
  asec_wf L st cs /\ asec_arr L st cs m /\ asec_inst L m /\ aprim0 L m /\ ashz L cs m /\ AEXHc cs L st m.

Definition ASEC_of (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop := ASECc (sec_chunks_of st) L st X m.

End CANSEC1.
End TwinB.
