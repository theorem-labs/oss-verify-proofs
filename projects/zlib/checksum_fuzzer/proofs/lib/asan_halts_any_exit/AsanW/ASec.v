(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* reloc14 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg AProto ABase ABytes ARep ARepKit ARepFrame ALayout AHeapP F_ammap F_apoison APoisonR_iface.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.asan_halts_any_exit.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT}.
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
     rw_cells asegs m 0x9e3e8 [C8 (Z_to_bv 64 (al_ptr_array L))]
  /\ (exists srt : byte, rw_cells asegs m 0x9e418 [C1 srt])
  /\ junk_at m 0x9e420 32
  /\ junk_at m 0x9e440 512
  /\ rw_cells asegs m 0x9e641 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]
  /\ junk_at m 0x9e658 16.


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
  asec_wf L st cs /\ asec_arr L st cs m /\ asec_inst L m /\ aprim0 L m /\ ashz L cs m.

Definition ASEC_of (L : alayout) (st : astate) (X : aconc) (m : amem) : Prop := ASECc (sec_chunks_of st) L st X m.

End CANSEC1.
