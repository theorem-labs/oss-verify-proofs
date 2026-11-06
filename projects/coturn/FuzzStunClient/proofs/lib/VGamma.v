(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VState VLogic.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wordZ (z : Z) : word := Z_to_bv 64 z.

Section Gamma.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.

  (* [comment removed for export] *)
  Definition cells_regions (l : list (Z * Z)) : list (word * Z) :=
    map (fun c : Z * Z => (wordZ (fst c), snd c)) l.

  (* [comment removed for export] *)
  Definition footprint : list (word * Z) :=
    (wordZ (e_sp0 E - vp_frame P), vp_frame P) :: cells_regions (vp_fcells P).

  (* [comment removed for export] *)
  Definition unit_regions : list (word * Z) :=
    map (fun r : Z * Z => (wordZ (e_sp0 E + fst r), snd r - fst r)) (vp_wstack P) ++ cells_regions (vp_wcells P).

  (* [comment removed for export] *)
  Definition env_ok : Prop :=
    e_sp0 E mod 16 = 0 /\ vp_splo P <= e_sp0 E <= vp_sphi P /\
    0 <= e_size E < vp_nmax P /\ e_data E <> 0 /\ 0 <= e_data E /\ e_data E + e_size E < 2 ^ 63 /\
    0 <= e_ra E < 2 ^ 64 /\ 0 <= e_tp E < 2 ^ 64 /\ 0 <= e_gp E < 2 ^ 64 /\
    length (e_sregs E) = 12%nat /\
    vp_frame P <= e_sp0 E.

  (* [comment removed for export] *)
  Definition MC (mem : word -> option byte) : Prop :=
    (forall a, e_sp0 E - vp_frame P <= a < e_sp0 E ->
        store_ok SEGS mem (wordZ a) 1 = true /\ exists b, rdn SEGS mem (wordZ a) 1 = Some [b])
    /\ (forall i, 0 <= i < e_size E -> exists b, rdn SEGS mem (wordZ (e_data E + i)) 1 = Some [b])
    /\ (forall lo hi a, In (lo, hi) (vp_pristine P) -> lo <= a < hi -> mem (wordZ a) = None)
    /\ frame_mod mem0 mem footprint.

  (* [comment removed for export] *)
  Definition gamma_val (nu : val) (v : absval) (w : word) : Prop :=
    match v with
    | None => True
    | Some e => bv_unsigned w = zwrap 64 (eval nu e)
    end.

  Definition gamma_regs (nu : val) (A : vstate) (regs : bvmap 5 word) : Prop :=
    forall (r : reg) e, bv_unsigned r <> 0 -> pm_get (reg_key (bv_unsigned r)) (vs_regs A) = Some e ->
                bv_unsigned (getr regs r) = zwrap 64 (eval nu e).

  (* [comment removed for export] *)
  Definition cell_holds (nu : val) (mem : word -> option byte) (a w : Z) (v : absval) : Prop :=
    match v with
    | None => True
    | Some e => exists bs, rdn SEGS mem (wordZ a) (Z.to_nat w) = Some bs
                           /\ bytes_le_to_Z bs = zwrap (8 * w) (eval nu e)
    end.

  Definition gamma_slots (nu : val) (A : vstate) (mem : word -> option byte) : Prop :=
    forall off w v, In (off, (w, v)) (vs_slots A) ->
      (- vp_frame P <= off /\ 0 < w /\ off + w <= 0) /\ cell_holds nu mem (e_sp0 E + off) w v.

  Definition gamma_globs (nu : val) (A : vstate) (mem : word -> option byte) : Prop :=
    forall a w v, In (a, (w, v)) (vs_globs A) ->
      (0 <= a /\ 0 < w /\ a + w <= vp_splo P - vp_frame P) /\ cell_holds nu mem a w v.

  Definition gamma_nul (A : vstate) (mem : word -> option byte) : Prop :=
    forall lo hi, In (lo, hi) (vs_nul A) ->
      exists off b, lo <= off <= hi /\ (- vp_frame P <= off < 0) /\
                    rdn SEGS mem (wordZ (e_sp0 E + off)) 1 = Some [b] /\ bv_unsigned b = 0.

  (* [comment removed for export] *)
  Definition gamma (A : vstate) (nu : val) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
    env_ok /\ MC mem /\ gamma_fix E nu /\
    sat nu (vs_store A) /\ gamma_conddef nu A /\ gamma_moddef nu A /\ gamma_valset nu A /\
    gamma_regs nu A regs /\ gamma_slots nu A mem /\ gamma_globs nu A mem /\ gamma_nul A mem /\
    state_below A.

End Gamma.
