(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (4 recorded proofs replaced by written proofs (sec_disjoint_nil, sec_disjoint_perm, granules_eq and 1 more)). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode.
From OSSVerify.Proofs.zstd.huf_decompress.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.huf_decompress.lib.BothW Require Import BImg AProto ABase ABytes ARep ARepKit ARepFrame ALayout AHeapP F_ammap F_apoison APoisonR_iface.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_ASec () := "C46Stdlib5Lists4List2InI47Corelib5Lists7ListDef6Forall00C47Corelib4Init9Datatypes3fstC35stdpp4base6LookupK47Corelib4Init9Datatypes4list01I46Stdlib5Lists4List5NoDup00I47Corelib4Init5Logic2eq00C47Corelib4Init5Logic3notC59OSSVerify5KrLib5BothW6AHeapP6sec_mbC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib5BothW6AHeapP6sec_msC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC56Stdlib6ZArith6BinInt1Z2leI47Corelib4Init5Logic2or00K46Stdlib5Lists4List5NoDup01K47Corelib4Init5Logic3and01I59OSSVerify5KrLib4Spec8AsanCtrl6achunk00C1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic5False00I47Corelib4Init9Datatypes4list00I46Stdlib7Sorting;Permutation;Permutation00c59OSSVerify5KrLib5BothW4ASec<sec_disjointC1?~~~~~~~~~~~~~~~C46Stdlib7Sorting;PermutationAPermutation_NoDupC46Stdlib7Sorting;Permutation?Permutation_symC46Stdlib7Sorting;Permutation>Permutation_inI47Corelib4Init5Logic3and00C46Stdlib5Lists4List2hdK47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K47Corelib7Numbers7BinNums8positive02C56Stdlib6ZArith6BinInt1Z3powC56Stdlib6ZArith6BinInt1Z3divC56Stdlib6ZArith6BinInt1Z6shiftrC56Stdlib6ZArith6BinInt1Z6moduloC56Stdlib6ZArith6BinInt1Z3eqbC56Stdlib6ZArith6BinInt1Z8eqb_specI47Corelib4Init9Datatypes7reflect00C56Stdlib6ZArith6BinInt1Z7div_modC56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z=mod_pos_boundC56Stdlib6ZArith6BinInt1Z2ltC56Stdlib6ZArith6BinInt1Z=mod_neg_boundC56Stdlib5omega8PreOmega1Z;div_0_r_extC56Stdlib5omega8PreOmega1Z;mod_0_r_extK47Corelib7Numbers7BinNums1Z03K46Stdlib9micromega7EnvRing3Pol01K47Corelib4Init9Datatypes3nat02K46Stdlib9micromega=RingMicromega5Psatz04K46Stdlib9micromega=RingMicromega5Psatz07K46Stdlib9micromega=RingMicromega5Psatz02K46Stdlib9micromega=RingMicromega5Psatz05K46Stdlib9micromega:ZMicromega;ZArithProof02K46Stdlib9micromega:ZMicromega;ZArithProof03K47Corelib4Init9Datatypes4list02K46Stdlib9micromega6VarMap1t02K46Stdlib9micromega6VarMap1t01K46Stdlib9micromega6VarMap1t03I46Stdlib9micromega6VarMap1t00I46Stdlib9micromega=RingMicromega7Formula00K46Stdlib9micromega7EnvRing5PExpr01K47Corelib4Init9Datatypes6option02K46Stdlib9micromega7EnvRing5PExpr02K46Stdlib9micromega7EnvRing5PExpr05K46Stdlib9micromega7EnvRing5PExpr03C46Stdlib9micromega5Tauto8BFormulaK47Corelib4Init5Logic2eq01C46Stdlib9micromega:ZMicromega=ZTautoCheckerC46Stdlib9micromega6VarMap4findC46Stdlib9micromega:ZMicromegaCZTautoChecker_soundC56Stdlib6ZArith6BinInt1Z?shiftr_div_pow2C47Corelib4Init5Logic8eq_ind_rC59OSSVerify5KrLib5BothW4ARep8granulesC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec9AsanEmbed5shlenC1?~~~~~~~~~~~~~~~K46Stdlib9micromega=RingMicromega5Psatz06K46Stdlib9micromega=RingMicromega7Formula01K46Stdlib9micromega5Tauto8GFormula04K46Stdlib9micromega5Tauto8GFormula07K46Stdlib9micromega5Tauto8GFormula08K46Stdlib9micromega5Tauto8GFormula05K47Corelib7Numbers7BinNums1Z01I47Corelib7Numbers7BinNums1Z00K46Stdlib9micromega=RingMicromega3Op201C46Stdlib9micromega5Tauto5eKindI47Corelib4Init9Datatypes4unit00K46Stdlib9micromega5Tauto4kind01K47Corelib4Init9Datatypes4unit01K46Stdlib9micromega=RingMicromega3Op205K46Stdlib9micromega=RingMicromega3Op203K47Corelib7Numbers7BinNums8positive03I47Corelib4Init9Datatypes4bool00I46Stdlib9micromega:ZMicromega;ZArithProof00K47Corelib4Init9Datatypes3nat01K46Stdlib9micromega:ZMicromega;ZArithProof01K47Corelib4Init9Datatypes4bool01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C59OSSVerify5KrLib5BothW4ARepBblock_shadow_bytesC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvC56Stdlib6ZArith6BinInt1Z6to_natC47Corelib5Lists7ListDef6repeatC47Corelib4Init9Datatypes6lengthC47Corelib4Init3Nat3addC56Stdlib6ZArith6BinInt1Z=shiftr_nonnegC47Corelib4Init5Logic5proj2C56Stdlib6ZArith6BinInt1Z6of_natC56Stdlib6ZArith4Znat5Nat2Z7inj_iffC47Corelib4Init5Logic7iff_symC56Stdlib6ZArith6BinInt1Z8max_specC46Stdlib9micromega;ZifyClasses;rew_iff_revc59OSSVerify5KrLib5BothW4ASec;granules_eqC1?~~~~~~~~~~~~~~~C46Stdlib5Lists4List=repeat_lengthC47Corelib4Init9Datatypes3appC46Stdlib5Lists4List:length_appc59OSSVerify5KrLib5BothW4ASec?sec_user_shadowC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3maxC46Stdlib9micromega;ZifyClasses5mkappC46Stdlib9micromega;ZifyClasses6mkapp2C46Stdlib9micromega;ZifyClasses5mkrelK46Stdlib9micromega5Tauto8GFormula06K46Stdlib9micromega5Tauto8GFormula03I47Corelib4Init9Datatypes3nat00C46Stdlib9micromega8ZifyInst@of_nat_to_nat_eqC56Stdlib5Arith8PeanoNat3Nat3addC56Stdlib6ZArith4Znat5Nat2Z7inj_add".
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition sec_live (st : astate) (ch : achunk) : Prop := exists p, (a_live st) !! p = Some ch.
Definition SEC_MAGIC : Z := 0xCC6E96B9CC6E96B9.  (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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

(* [comment removed for export] *)
Definition asec_arr (L : alayout) (st : astate) (cs : list achunk) (m : amem) : Prop :=
  exists order : list achunk,
       Permutation order cs
    /\ u64arr bsegs m (al_ptr_array L) (map (fun ch => Z_to_bv 64 (sec_mb ch)) order)
    /\ junk_at m (al_ptr_array L + 8 * a_nsec st) (8 * (a_nres st - a_nsec st))
    /\ (forall i ch, nth_error order i = Some ch ->
          exists lv : bool, (lv = true <-> sec_live st ch) /\ asec_chunk m ch (Z.of_nat i) lv).

(* [comment removed for export] *)
Definition asec_inst (L : alayout) (m : amem) : Prop :=
     rw_cells bsegs m 0xb6ce8 [C8 (Z_to_bv 64 (al_ptr_array L))]        (* [comment removed for export] *)
  /\ (exists srt : byte, rw_cells bsegs m 0xb6d18 [C1 srt])              (* [comment removed for export] *)
  /\ junk_at m 0xb6d20 32                                                (* [comment removed for export] *)
  /\ junk_at m 0xb6d40 512                                               (* [comment removed for export] *)
  /\ rw_cells bsegs m 0xb6f41 [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0)]   (* [comment removed for export] *)
  /\ junk_at m 0xb6f58 16.                                               (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition astartup_hulls (L : alayout) : list (Z * Z) :=
  let V := al_V L in
  [(4096 * V 584%nat, 4096 * V 584%nat + 4096); (4096 * V 503%nat, 4096 * V 503%nat + 4096);
   (al_store L, al_store L + 8388608); (al_nodes L, al_nodes L + 1048576); (al_fake L, al_fake L + 11571200);
   (al_dtls L, al_dtls L + 4096); (4096 * V 258%nat, 4096 * V 258%nat + 4096); (al_ctx L, al_ctx L + 65536);
   (al_t L, al_t L + 4096); (al_res L, al_res L + 137439023104);
   (4096 * V 220%nat, 4096 * V 220%nat + 0x38e000); (4096 * V 91%nat, 4096 * V 91%nat + 0x10000);
   (al_ptr_array L, al_ptr_array L + 8388608)].
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
