(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import Hoare.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Record FParams := mkFP {
  fp_entry  : Z;   (* [comment removed for export] *)
  fp_ret    : Z;   (* [comment removed for export] *)
  fp_tp     : Z;   (* [comment removed for export] *)
  fp_frame  : Z;   (* [comment removed for export] *)
  fp_prng   : Z;   (* [comment removed for export] *)
  fp_errno  : Z;   (* [comment removed for export] *)
  fp_mcount : Z;   (* [comment removed for export] *)
  fp_gotgrd : Z;   (* [comment removed for export] *)
  fp_ro_lo  : Z;   (* [comment removed for export] *)
  fp_ro_hi  : Z;
  fp_nmax   : Z    (* [comment removed for export] *)
}.

Definition FP_src0 : FParams :=
  mkFP 0x13e80 0x13d7c 0x367b0 132544 0x26360 0x3670c 0x366d8 0x252f8 0x10000 0x2427c (2^26).  (* [comment removed for export] *)
Definition FP_ub : FParams :=
  mkFP 0x13f60 0x13e5c 0x36c60 132624 0x26808 0x36bbc 0x36b88 0x257a0 0x10000 0x24724 (2^26).  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition F_SPLO : Z := 0x7fff80000000 - 4096.
Definition F_SPHI : Z := 0x800000000000.

(* [comment removed for export] *)
Definition ekept : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ekeeps (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r ekept -> getr regs' r = getr regs r.

Section WithFP.
  Variable SEGS : list Segment.
  Variable P : FParams.

  Definition pristine (mem : word -> option byte) (lo hi : Z) : Prop :=
    forall a : word, lo <= bv_unsigned a < hi -> mem a = None.

  Definition F_footprint (sp : word) : list (word * Z) :=
    [ (Z_to_bv 64 (bv_unsigned sp - fp_frame P), fp_frame P)
    ; (Z_to_bv 64 (fp_prng P), 8)
    ; (Z_to_bv 64 (fp_errno P), 4) ].

  Definition F_contract : Prop :=
    forall (regs : bvmap 5 word) (mem rom : word -> option byte) (sp data : word) (n : Z),
      getr regs 1 = Z_to_bv 64 (fp_ret P) ->
      getr regs 2 = sp ->
      getr regs 4 = Z_to_bv 64 (fp_tp P) ->
      getr regs 10 = data ->
      getr regs 11 = Z_to_bv 64 n ->
      0 <= n < fp_nmax P ->
      bv_unsigned data <> 0 ->
      bv_unsigned data + n < 2 ^ 63 ->
      bv_unsigned sp mod 16 = 0 ->
      F_SPLO <= bv_unsigned sp <= F_SPHI ->
      (* [comment removed for export] *)
      (bv_unsigned data + n <= bv_unsigned sp - fp_frame P \/ bv_unsigned sp <= bv_unsigned data) ->
      (* [comment removed for export] *)
      (forall i, 0 <= i < n ->
         exists b, rdn SEGS mem (Z_to_bv 64 (bv_unsigned data + i)) 1 = Some [b]) ->
      (* [comment removed for export] *)
      (forall a : word, bv_unsigned sp - fp_frame P <= bv_unsigned a < bv_unsigned sp ->
         store_ok SEGS mem a 1 = true) ->
      (* [comment removed for export] *)
      pristine mem (fp_ro_lo P) (fp_ro_hi P) ->
      pristine mem (fp_gotgrd P) (fp_gotgrd P + 8) ->
      pristine mem (fp_mcount P) (fp_mcount P + 8) ->
      exists regs' mem',
        msteps SEGS (mkst regs (Z_to_bv 64 (fp_entry P)) mem rom)
                    (mkst regs' (Z_to_bv 64 (fp_ret P)) mem' rom)
        /\ ekeeps regs regs'
        /\ getr regs' 10 = Z_to_bv 64 0
        /\ frame_mod mem mem' (F_footprint sp).
End WithFP.
