(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType OSSVerify.glaze.binary_reflection.images.Ubsan OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module UbMhImgR0.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Abbreviation SEGS := Ubsan.M.loaded_segments.
Section Cells.
Context {fx : FPState}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma img_78d10_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 494944) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 699904)).
Proof using. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_8ae53_1 : rdn SEGS (fun _ => None) (Z_to_bv 64 699939) 1%nat = Some ([Z_to_bv 8 0]).
Proof using. vm_refl_bv. Qed.


(* [comment removed for export] *)
Lemma img_8b078_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 700488) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof using. vm_refl_bv. Qed.
(* [comment removed for export] *)
Lemma img_8b1f8_8 : rdn SEGS (fun _ => None) (Z_to_bv 64 700872) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0)).
Proof using. vm_refl_bv. Qed.
End Cells.
End UbMhImgR0.
Require Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhMSpecI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ctx_pristine (sec : Z) : ctx_rec :=
  CX sec 0 0 0 0 0 0 0 0 0 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) 0 0.
Definition st_pristine (can sec : Z) : mst :=
  MST (ctx_pristine sec) [] (fun _ => meta_zero) [] (fun _ => []) [] (fun _ => 0) (fun _ => GTop) (fun _ _ => SFreed)
      [] BrkUntried can 0 [].


Section Spec.
  Context {fx : FPState} {RN : run_ceil}.

  (* [comment removed for export] *)
  Record first_img (M : mem) : Prop := FI {
    fi_errno : img_clear M A_ERRNO (A_ERRNO + 4);
    fi_got : img_clear M A_GOT_CANARY (A_GOT_CANARY + 8);
    fi_ctz : img_clear M A_TAB_CTZ (A_TAB_CTZ + 32);
    fi_sc : img_clear M A_TAB_SC (A_TAB_MED + 4)
  }.

  (* [comment removed for export] *)
  Definition env_above_sp (auxw : Z) (avl : list (Z * Z)) (sp : Z) : Prop :=
    sp <= auxw /\ forall kv, In kv avl -> fst kv = 25 -> sp <= snd kv + 8.

  Lemma env_above_sp_mono : forall auxw avl sp sp', sp' <= sp -> env_above_sp auxw avl sp -> env_above_sp auxw avl sp'.
  Proof using. intros auxw avl sp sp' Hle [H1 H2]. split; [lia|]. intros kv Hk E. pose proof (H2 kv Hk E). lia. Qed.

  Definition AM_INIT : Prop :=
    forall (F : kfam) (bi bo : bool) (M : mem) mdl regs rom sp auxw avl,
      kfam_laws RSEGS F -> (bo = true -> bi = true) ->
      first_env M mdl auxw avl -> first_img M -> env_above_sp auxw avl sp ->
      m_halted mdl = None -> m_vm_lazy mdl = [] -> m_vm_materialized mdl = [] ->
      getr regs 2 = Z_to_bv 64 sp -> ret_ok (getr regs 1) -> CEIL + AMSTK <= sp -> sp < 2 ^ 64 ->
      getr regs 4 = Z_to_bv 64 TPV ->
      defined M (sp - AMSTK) sp ->
      (forall can sec c', am_ok (st_pristine can sec) [] [] sp regs M mdl rom c' -> kfx F bi c') ->
      (forall can sec c', am_fail (st_pristine can sec) [] [] sp regs M mdl rom c' -> Kf F c') ->
      kfx F bo (mkCfg (mkst regs (Z_to_bv 64 AM_ENTRY) M rom) mdl).
End Spec.
End UbMhMSpecI.
Require Stdlib.Sorting.Permutation LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaC OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhAMetaI.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mprotect.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim.StreamSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMemcpyBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMuslMemmove.UbMemcpy OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MuslStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes.Nodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.RefNodes OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.MhKSys OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1 OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhGap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM.UbMhRsegs OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhBrkK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhAMetaW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaR OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 UbMhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM.UbMhAMetaT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaM OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.PuStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac is_Z_lit ::= ps_is_Z_lit.   (* [comment removed for export] *)
#[local] Ltac check_closed_term_fast ::= ps_check_closed.
#[local] Ltac gres ::= pu_gres.
#[local] Ltac chain_step ::= pu_chain_step.   (* [comment removed for export] *)
#[local] Ltac vnorm ::= pu_vnorm.
#[local] Ltac step_simpl ::= pu_step_simpl.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac sok B SOK := store_ok_peel; eapply (store_ok_sub _ _ _ _ B); [ | exact SOK | | ]; zsimp; lia.

Definition A_LIBC : Z := 0xaae20.          (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section I.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Variables (m : mem) (sp can auxw : Z).
  Hypothesis Hsp : (CEIL + 64 <= sp)%Z /\ (sp < 2^64)%Z.
  Hypothesis Hcan : (0 <= can < 2^64)%Z.
  Hypothesis Hauxw : (0 <= auxw < 2^64)%Z.
  Hypothesis SOK : store_ok RSEGS m (Z_to_bv 64 (sp - 64)) 64%nat = true.
  Hypothesis M_got : rdn RSEGS m (Z_to_bv 64 A_GOT_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY)).
  Hypothesis M_can : rdn RSEGS m (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can)).
  Hypothesis M_init0 : rdn RSEGS m (Z_to_bv 64 ctx_init_done) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Hypothesis M_auxv : rdn RSEGS m (Z_to_bv 64 A_LIBC_AUXV) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 auxw)).

  #[local] Notation FR regs := (am_frame m sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)).

  (* [comment removed for export] *)
  Lemma amI1 : forall regs rom,
    getr regs 2 = Z_to_bv 64 sp ->
    exists regs' (w0 : word),
      msteps RSEGS (mkst regs (0x66c68%bv : word) m rom)
                   (mkst regs' (0x66cec%bv : word) (wbytes (FR regs) (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 8 w0)) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 64) /\ getr regs' 19 = Z_to_bv 64 MLOCK /\ getr regs' 8 = Z_to_bv 64 A_LIBC
      /\ getr regs' 18 = Z_to_bv 64 A_CANARY /\ getr regs' 9 = Z_to_bv 64 0 /\ getr regs' 20 = Z_to_bv 64 25
      /\ getr regs' 10 = Z_to_bv 64 auxw
      /\ keeps_but [2; 8; 9; 10; 11; 12; 18; 19; 20]%bv regs regs'.
  Proof using M_auxv M_init0 M_can M_got SOK Hsp RN.
    intros regs rom H2. ceil; unfold A_GOT_CANARY, A_CANARY, ctx_init_done, CTX, A_PAGESIZE, MLOCK, A_LIBC_AUXV, A_LIBC in *.
    eexists _, _. split.
    - stepn F_66c14 D_66c14. rewrite H2. addi_renorm.
      stepSTx F_66c18 D_66c18 (Z_to_bv 64 (sp - 8)) (getr regs 1) ltac:(sok 64%nat SOK).
      stepSTx F_66c1c D_66c1c (Z_to_bv 64 (sp - 16)) (getr regs 8) ltac:(sok 64%nat SOK).
      stepSTx F_66c20 D_66c20 (Z_to_bv 64 (sp - 24)) (getr regs 9) ltac:(sok 64%nat SOK).
      stepSTx F_66c24 D_66c24 (Z_to_bv 64 (sp - 32)) (getr regs 18) ltac:(sok 64%nat SOK).
      stepSTx F_66c28 D_66c28 (Z_to_bv 64 (sp - 40)) (getr regs 19) ltac:(sok 64%nat SOK).
      stepSTx F_66c2c D_66c2c (Z_to_bv 64 (sp - 48)) (getr regs 20) ltac:(sok 64%nat SOK).
      stepn F_66c30 D_66c30.
      stepLD8 F_66c34 D_66c34 (Z_to_bv 64 699904).
      stepLD8 F_66c38 D_66c38 (Z_to_bv 64 can).
      stepn F_66c3c D_66c3c.
      stepSTx F_66c40 D_66c40 (Z_to_bv 64 (sp - 56)) (Z_to_bv 64 can) ltac:(sok 64%nat SOK).
      stepn F_66c44 D_66c44.
      stepLD F_66c48 D_66c48 (word_to_le_bytes 4 (Z_to_bv 64 0)) (Z_to_bv 64 0)
        ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_4; u_norm; lia).
      vals_lit.
      stepn F_66c4c D_66c4c.
      stepn F_66c50 D_66c50.
      stepb_ft F_66c54 D_66c54 ltac:(cond_compute).
      stepn F_66c58 D_66c58.
      stepn F_66c5c D_66c5c.
      stepn F_66c60 D_66c60.
      stepLD8 F_66c64 D_66c64 (Z_to_bv 64 auxw).
      stepn F_66c68 D_66c68.
      stepn F_66c6c D_66c6c.
      stepSTx F_66c70 D_66c70 (Z_to_bv 64 (sp - 64)) (v_mul (Z_to_bv 64 (sp - 64)) (Z_to_bv 64 1103515245)) ltac:(sok 64%nat SOK).
      stepn F_66c74 D_66c74.
      stepn F_66c78 D_66c78.
      unfold am_frame. pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.


  (* [comment removed for export] *)
  Variable avl : list (Z * Z).
  Hypothesis Hav : 0 <= auxw /\ auxw + 16 * (Z.of_nat (length avl) + 1) <= 2 ^ 63 /\ auxw mod 8 = 0.
  Hypothesis AVK : forall i kv, nth_error avl i = Some kv ->
    cell m (auxw + 16 * Z.of_nat i) 8 (Datatypes.fst kv) /\ cell m (auxw + 16 * Z.of_nat i + 8) 8 (Datatypes.snd kv) /\ 0 < Datatypes.fst kv < 2 ^ 64 /\ 0 <= Datatypes.snd kv < 2 ^ 64.
  Hypothesis AVE : cell m (auxw + 16 * Z.of_nat (length avl)) 8 0.
  Hypothesis AVR : forall kv, In kv avl -> Datatypes.fst kv = 25 ->
    Datatypes.snd kv + 24 <= 2 ^ 63 /\ exists bs, length bs = 8%nat /\ rdn RSEGS m (Z_to_bv 64 (Datatypes.snd kv + 8)) 8%nat = Some bs.
  Hypothesis ENV : sp <= auxw /\ forall kv, In kv avl -> Datatypes.fst kv = 25 -> sp <= Datatypes.snd kv + 8.

  (* [comment removed for export] *)
  Lemma rd_high : forall (mc : mem) a k bs,
    (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mc (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
    sp <= a -> a + Z.of_nat k < 2 ^ 64 ->
    rdn RSEGS m (Z_to_bv 64 a) k = Some bs -> rdn RSEGS mc (Z_to_bv 64 a) k = Some bs.
  Proof using avl Hauxw Hsp auxw RN.
    intros mc a k bs AG Ha Hk R. pose proof Hsp as [S1 S2]. ceil. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
    apply AG; lia.
  Qed.
  Lemma rd_low : forall (mc : mem) a k bs,
    (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mc (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
    0 <= a -> a + Z.of_nat k <= sp - 64 ->
    rdn RSEGS m (Z_to_bv 64 a) k = Some bs -> rdn RSEGS mc (Z_to_bv 64 a) k = Some bs.
  Proof using ENV Hav avl Hauxw Hsp auxw RN.
    intros mc a k bs AG Ha Hk R. pose proof Hsp as [S1 S2]. ceil. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
    intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
    apply AG; lia.
  Qed.

  Definition clobL : list reg := [1; 5; 6; 7; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%bv.

  Lemma reg_cover : forall x : reg,
    (existsb (fun y => bv_eqb y x) clobL || existsb (fun y => bv_eqb y x) callee_kept || bv_eqb x 0%bv)%bool = true.
  Proof using avl auxw.
    intros x. pose proof (bv_unsigned_in_range 5 x) as R. rewrite <- (Z_to_bv_bv_unsigned 5 x).
    set (z := bv_unsigned x) in *. clearbody z.
    assert (Hz : 0 <= z < 32) by (unfold bv_modulus in R; cbn in R; lia).
    assert (E : z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/ z = 4 \/ z = 5 \/ z = 6 \/ z = 7 \/ z = 8 \/ z = 9 \/ z = 10 \/ z = 11 \/ z = 12 \/ z = 13 \/ z = 14 \/ z = 15 \/ z = 16 \/ z = 17 \/ z = 18 \/ z = 19 \/ z = 20 \/ z = 21 \/ z = 22 \/ z = 23 \/ z = 24 \/ z = 25 \/ z = 26 \/ z = 27 \/ z = 28 \/ z = 29 \/ z = 30 \/ z = 31) by lia.
    repeat (destruct E as [->|E]; [vm_compute; reflexivity|]). subst z. vm_compute. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma keeps_clobL : forall r r', keeps r r' -> keeps_but clobL r r'.
  Proof using avl auxw.
    intros r r' K x NI. pose proof (reg_cover x) as C.
    apply Bool.orb_true_iff in C. destruct C as [C|C].
    - apply Bool.orb_true_iff in C. destruct C as [C|C].
      + exfalso. exact (NI (in_regs_dec x clobL C)).
      + exact (K x (in_regs_dec x callee_kept C)).
    - unfold bv_eqb in C. apply Z.eqb_eq in C. assert (E0 : x = 0%bv) by (apply bv_eq; exact C). subst x. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma amI_loop : forall rest done regs (mc : mem) rom,
    avl = done ++ rest ->
    getr regs 9 = Z_to_bv 64 (16 * Z.of_nat (length done)) -> getr regs 10 = Z_to_bv 64 auxw -> getr regs 20 = Z_to_bv 64 25 ->
    getr regs 8 = Z_to_bv 64 A_LIBC -> getr regs 2 = Z_to_bv 64 (sp - 64) ->
    (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mc (Z_to_bv 64 x) = m (Z_to_bv 64 x)) ->
    store_ok RSEGS mc (Z_to_bv 64 (sp - 64)) 8%nat = true ->
    (exists bs0, length bs0 = 8%nat /\ rdn RSEGS mc (Z_to_bv 64 (sp - 64)) 8%nat = Some bs0) ->
    exists regs' mc',
      msteps RSEGS (mkst regs (0x66cec%bv : word) mc rom) (mkst regs' (0x66cfc%bv : word) mc' rom)
      /\ (forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp - 56) -> mc' (Z_to_bv 64 x) = mc (Z_to_bv 64 x))
      /\ mem_grows mc mc'
      /\ getr regs' 2 = Z_to_bv 64 (sp - 64) /\ getr regs' 8 = Z_to_bv 64 A_LIBC
      /\ keeps_but clobL regs regs'
      /\ (exists bs1, length bs1 = 8%nat /\ rdn RSEGS mc' (Z_to_bv 64 (sp - 64)) 8%nat = Some bs1).
  Proof using ENV AVR AVE AVK Hav M_auxv Hauxw Hcan Hsp can RN.
    pose proof Hsp as [S1 S2]. ceil. unfold A_LIBC, A_LIBC_AUXV in *.
    induction rest as [|kv rest IH]; intros done regs mc rom Havl G9 G10 G20 G8 G2 AG SOKc RD8.
    - (* [comment removed for export] *)
      assert (LEN : length done = length avl) by (rewrite Havl, app_nil_r; reflexivity).
      pose proof (rd_high mc (auxw + 16 * Z.of_nat (length avl)) 8%nat _ AG ltac:(lia) ltac:(cbn; lia) AVE) as K0. rewrite <- LEN in K0.
      eexists _, mc. split; [|split; [intros; reflexivity | split; [apply mem_grows_refl | split; [|split; [|split; [|exact RD8]]]]]].
      + stepn F_66c98 D_66c98. rewrite G10, G9. rewrite v_add_ZZ by lia.
        stepLD F_66c9c D_66c9c (word_to_le_bytes 8 (Z_to_bv 64 0)) (Z_to_bv 64 0) ltac:(addr_norm; exact K0) ltac:(apply bytes_le_to_Z_8).
        stepb_ft F_66ca0 D_66ca0 ltac:(rewrite G20; apply c_eq_neq; rewrite !u_Z2bv by lia; lia).
        stepb_ft F_66ca4 D_66ca4 ltac:(apply c_eq_refl).
        pu_refl.
      + gres. exact G2.
      + gres. exact G8.
      + solve_keeps_but.
    - (* [comment removed for export] *)
      assert (NTH : nth_error avl (length done) = Some kv) by (rewrite Havl, nth_error_app2, Nat.sub_diag by lia; reflexivity).
      destruct (AVK _ _ NTH) as (CK & CV & RK & RV).
      assert (INkv : In kv avl) by (rewrite Havl; apply in_or_app; right; left; reflexivity).
      assert (LENb : Z.of_nat (length done) + 1 <= Z.of_nat (length avl)) by (rewrite Havl, length_app; cbn; lia).
      pose proof (rd_high mc (auxw + 16 * Z.of_nat (length done)) 8%nat _ AG ltac:(lia) ltac:(cbn; lia) CK) as Kk.
      destruct (Z.eq_dec (Datatypes.fst kv) 25) as [E25|N25].
      + (* [comment removed for export] *)
        destruct (AVR kv INkv E25) as (RVh & bs & Lbs & Rbs). pose proof (proj2 ENV kv INkv E25) as SPlo.
        pose proof (rd_high mc (auxw + 16 * Z.of_nat (length done) + 8) 8%nat _ AG ltac:(lia) ltac:(cbn; lia) CV) as Kv.
        pose proof (rd_high mc (Datatypes.snd kv + 8) 8%nat _ AG SPlo ltac:(cbn; lia) Rbs) as Ksrc.
        (* [comment removed for export] *)
        assert (W1 : exists r1, msteps RSEGS (mkst regs (0x66cec%bv : word) mc rom) (mkst r1 (0x732b0%bv : word) mc rom)
                  /\ getr r1 1 = Z_to_bv 64 0x66ce4 /\ getr r1 10 = Z_to_bv 64 (sp - 64) /\ getr r1 11 = Z_to_bv 64 (Datatypes.snd kv + 8)
                  /\ getr r1 12 = Z_to_bv 64 8 /\ keeps_but [1; 10; 11; 12]%bv regs r1).
        { eexists. split.
          - stepn F_66c98 D_66c98. rewrite G10, G9. rewrite v_add_ZZ by lia.
            stepLD F_66c9c D_66c9c (word_to_le_bytes 8 (Z_to_bv 64 (Datatypes.fst kv))) (Z_to_bv 64 (Datatypes.fst kv)) ltac:(addr_norm; exact Kk) ltac:(apply bytes_le_to_Z_8).
            stepb_tk F_66ca0 D_66ca0 ltac:(rewrite G20, E25; apply c_eq_refl).
            stepLD F_66c7c D_66c7c (word_to_le_bytes 8 (Z_to_bv 64 (Datatypes.snd kv))) (Z_to_bv 64 (Datatypes.snd kv))
              ltac:(replace (v_addi (Z_to_bv 64 (auxw + 16 * Z.of_nat (length done))) 8) with (Z_to_bv 64 (auxw + 16 * Z.of_nat (length done) + 8))
                      by (unfold v_addi; rewrite u_Z2bv by lia; reflexivity); exact Kv)
              ltac:(apply bytes_le_to_Z_8).
            stepn F_66c80 D_66c80. addi_renorm.
            stepn F_66c84 D_66c84. rewrite G2.
            stepn F_66c88 D_66c88.
            stepn F_66c8c D_66c8c.
            pu_refl.
          - repeat split; gres; try reflexivity; try (apply bv_eq; reflexivity). solve_keeps_but. }
        destruct W1 as (r1 & RUN1 & R1 & R10 & R11 & R12 & K1).
        (* [comment removed for export] *)
        assert (MC : mcH mc (Z_to_bv 64 (sp - 64)) (Z_to_bv 64 (Datatypes.snd kv + 8)) 8 bs).
        { constructor; rewrite ?Lbs, ?u_Z2bv by lia; try lia.
          - exact Ksrc.
          - exact SOKc. }
        destruct (ref_memcpy mc _ _ 8 bs rom MC r1 (Z_to_bv 64 0x66ce4) ltac:(apply ret_ok_even; reflexivity) R1 R10 R11 R12) as (r2 & RUN2 & K2).
        pose proof (keeps_clobL _ _ K2) as K2'.
        set (mc2 := wbytes mc (Z_to_bv 64 (sp - 64)) bs).
        assert (AG2 : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mc2 (Z_to_bv 64 x) = m (Z_to_bv 64 x)).
        { intros x Hx NI. unfold mc2. rewrite wbytes_outZ by (rewrite ?Lbs; cbn; lia). exact (AG x Hx NI). }
        assert (SOK2 : store_ok RSEGS mc2 (Z_to_bv 64 (sp - 64)) 8%nat = true) by (unfold mc2; eapply store_ok_mono; [apply wbytes_grows | exact SOKc]).
        pose proof (rd_low mc2 0xaae28 8%nat _ AG2 ltac:(lia) ltac:(cbn; lia) M_auxv) as Kaux.
        (* [comment removed for export] *)
        assert (W3 : exists r3, msteps RSEGS (mkst r2 (Z_to_bv 64 0x66ce4) mc2 rom) (mkst r3 (0x66cec%bv : word) mc2 rom)
                  /\ getr r3 10 = Z_to_bv 64 auxw /\ getr r3 9 = Z_to_bv 64 (16 * Z.of_nat (length (done ++ [kv]))) /\ keeps_but [9; 10]%bv r2 r3).
        { eexists. split.
          - replace (Z_to_bv 64 0x66ce4) with (0x66ce4%bv : word) by (apply bv_eq; reflexivity).
            stepLD F_66c90 D_66c90 (word_to_le_bytes 8 (Z_to_bv 64 auxw)) (Z_to_bv 64 auxw)
              ltac:(rewrite (K2 8%bv ltac:(cbn; tauto)); kept_rw K1; rewrite G8; addr_norm; exact Kaux) ltac:(apply bytes_le_to_Z_8).
            stepn F_66c94 D_66c94. rewrite (K2 9%bv ltac:(cbn; tauto)). kept_rw K1. rewrite G9. addi_renorm.
            pu_refl.
          - repeat split; gres; try reflexivity.
            + rewrite length_app. cbn [length]. f_equal. lia.
            + solve_keeps_but. }
        destruct W3 as (r3 & RUN3 & Q10 & Q9 & K3).
        (* [comment removed for export] *)
        destruct (IH (done ++ [kv]) r3 mc2 rom ltac:(rewrite Havl, <- app_assoc; reflexivity) Q9 Q10
                     ltac:(kept_rw K3; rewrite (K2 20%bv ltac:(cbn; tauto)); kept_rw K1; exact G20)
                     ltac:(kept_rw K3; rewrite (K2 8%bv ltac:(cbn; tauto)); kept_rw K1; exact G8)
                     ltac:(kept_rw K3; rewrite (K2 2%bv ltac:(cbn; tauto)); kept_rw K1; exact G2) AG2 SOK2
                     ltac:(exists bs; split; [exact Lbs | unfold mc2; rewrite <- Lbs; apply rdn_wbytes_hit; rewrite Lbs, u_Z2bv by lia; cbn; lia]))
          as (r4 & mc4 & RUN4 & AG4 & GR4 & F2 & F8 & K4 & RD4).
        exists r4, mc4. split; [|split; [|split; [|split; [exact F2 | split; [exact F8 | split; [|exact RD4]]]]]].
        * eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3 | exact RUN4].
        * intros x Hx NI. rewrite (AG4 x Hx NI). unfold mc2. apply wbytes_outZ; rewrite ?Lbs; cbn; lia.
        * eapply mem_grows_trans; [unfold mc2; apply wbytes_grows | exact GR4].
        * eapply keeps_but_trans; [| eapply keeps_but_trans; [| eapply keeps_but_trans; [|exact K4]]].
          -- eapply keeps_but_mono; [exact K1 | intros r Hr; cbn in Hr |- *; tauto].
          -- eapply keeps_but_mono; [exact K2' | intros r Hr; exact Hr].
          -- eapply keeps_but_mono; [exact K3 | intros r Hr; cbn in Hr |- *; tauto].
      + (* [comment removed for export] *)
        assert (W1 : exists r1, msteps RSEGS (mkst regs (0x66cec%bv : word) mc rom) (mkst r1 (0x66cec%bv : word) mc rom)
                  /\ getr r1 9 = Z_to_bv 64 (16 * Z.of_nat (length (done ++ [kv]))) /\ keeps_but [9; 11; 12]%bv regs r1).
        { eexists. split.
          - stepn F_66c98 D_66c98. rewrite G10, G9. rewrite v_add_ZZ by lia.
            stepLD F_66c9c D_66c9c (word_to_le_bytes 8 (Z_to_bv 64 (Datatypes.fst kv))) (Z_to_bv 64 (Datatypes.fst kv)) ltac:(addr_norm; exact Kk) ltac:(apply bytes_le_to_Z_8).
            stepb_ft F_66ca0 D_66ca0 ltac:(rewrite G20; apply c_eq_neq; rewrite !u_Z2bv by lia; lia).
            stepb_tk F_66ca4 D_66ca4 ltac:(apply c_eq_0_false; rewrite u_Z2bv by lia; lia).
            stepn F_66c94 D_66c94. rewrite G9. addi_renorm.
            pu_refl.
          - repeat split; gres; try reflexivity.
            + rewrite length_app. cbn [length]. f_equal. lia.
            + solve_keeps_but. }
        destruct W1 as (r1 & RUN1 & R9 & K1).
        destruct (IH (done ++ [kv]) r1 mc rom ltac:(rewrite Havl, <- app_assoc; reflexivity) R9
                     ltac:(kept_rw K1; exact G10) ltac:(kept_rw K1; exact G20) ltac:(kept_rw K1; exact G8) ltac:(kept_rw K1; exact G2) AG SOKc RD8)
          as (r4 & mc4 & RUN4 & AG4 & GR4 & F2 & F8 & K4 & RD4).
        exists r4, mc4. split; [|split; [exact AG4 | split; [exact GR4 | split; [exact F2 | split; [exact F8 | split; [|exact RD4]]]]]].
        * eapply msteps_trans; [exact RUN1 | exact RUN4].
        * eapply keeps_but_trans; [|exact K4]. eapply keeps_but_mono; [exact K1 | intros r Hr; cbn in Hr |- *; tauto].
  Qed.

  (* [comment removed for export] *)
  Lemma amI3 : forall regs rom (mc : mem) (bs : list byte),
    getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 19 = Z_to_bv 64 MLOCK -> getr regs 8 = Z_to_bv 64 A_LIBC ->
    length bs = 8%nat -> rdn RSEGS mc (Z_to_bv 64 (sp - 64)) 8%nat = Some bs ->
    rdn RSEGS mc (Z_to_bv 64 A_PAGESIZE) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 4096)) ->
    exists regs',
      msteps RSEGS (mkst regs (0x66cfc%bv : word) mc rom)
                   (mkst regs' (0x66d1c%bv : word)
                      (wbytes (wbytes mc (Z_to_bv 64 ctx_secret) (word_to_le_bytes 8 (Z_to_bv 64 (bytes_le_to_Z bs))))
                              (Z_to_bv 64 ctx_init_done) (word_to_le_bytes 4 (Z_to_bv 64 1))) rom)
      /\ getr regs' 2 = Z_to_bv 64 (sp - 64) /\ getr regs' 19 = Z_to_bv 64 MLOCK /\ getr regs' 8 = Z_to_bv 64 4096
      /\ keeps_but [8; 10; 11]%bv regs regs'.
  Proof using avl Hsp auxw RN.
    intros regs rom mc bs G2 G19 G8 Lbs RD Mpg. pose proof Hsp as [S1 S2]. ceil.
    unfold ctx_secret, ctx_init_done, CTX, A_PAGESIZE, MLOCK, A_LIBC in *.
    pose proof (bytes_le_to_Z_range bs Lbs) as BR.
    pose proof (UbMhAMetaM.ctx_sok mc) as CS. unfold CTX in CS.
    eexists. split.
    - stepLD F_66ca8 D_66ca8 bs (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(addr_norm; exact RD) ltac:(rewrite u_Z2bv by lia; reflexivity).
      stepn F_66cac D_66cac.
      stepSTx F_66cb0 D_66cb0 (Z_to_bv 64 700056) (Z_to_bv 64 (bytes_le_to_Z bs)) ltac:(sok 928%nat CS).
      stepSTx F_66cb4 D_66cb4 (Z_to_bv 64 700064) (Z_to_bv 64 1) ltac:(sok 928%nat CS).
      stepLD8 F_66cb8 D_66cb8 (Z_to_bv 64 4096).
      stepn F_66cbc D_66cbc.
      stepb_ft F_66cc0 D_66cc0 ltac:(cond_compute).
      stepn F_66cc4 D_66cc4.
      pu_refl.
    - repeat split; gres; try reflexivity; try assumption; try (apply bv_eq; reflexivity). all: solve_keeps_but.
  Qed.
End I.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Pristine.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Definition img_byte0 (i : Z) : bool :=
    match rdn RSEGS (fun _ => None) (Z_to_bv 64 i) 1%nat with
    | Some [b] => bv_eqb b (Z_to_bv 8 0)
    | _ => false
    end.
  Lemma img_ctx_zero_all : forallb img_byte0 (map (fun n => MLOCK + Z.of_nat n) (seq 0 (Z.to_nat (CTX_END - MLOCK)))) = true.
  Proof using. vm_compute. reflexivity. Qed.
  Lemma img_ctx_zero : forall i, MLOCK <= i < CTX_END -> rdn RSEGS (fun _ => None) (Z_to_bv 64 i) 1%nat = Some [Z_to_bv 8 0].
  Proof using.
    intros i Hi.
    assert (IN : In i (map (fun n => MLOCK + Z.of_nat n) (seq 0 (Z.to_nat (CTX_END - MLOCK))))).
    { apply in_map_iff. exists (Z.to_nat (i - MLOCK)). split; [lia|]. apply in_seq. lia. }
    pose proof (proj1 (forallb_forall _ _) img_ctx_zero_all i IN) as B. unfold img_byte0 in B.
    destruct (rdn RSEGS (fun _ => None) (Z_to_bv 64 i) 1%nat) as [[|b [|b' l]]|]; try discriminate B.
    unfold bv_eqb in B. apply Z.eqb_eq in B. do 2 f_equal. apply bv_eq. exact B.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_zeros : forall (Mx : mem) a k,
    0 <= a -> a + Z.of_nat k < 2 ^ 64 ->
    (forall i, a <= i < a + Z.of_nat k -> rdn RSEGS Mx (Z_to_bv 64 i) 1%nat = Some [Z_to_bv 8 0]) ->
    rdn RSEGS Mx (Z_to_bv 64 a) k = Some (repeat (Z_to_bv 8 0) k).
  Proof using.
    intros Mx a k. revert a. induction k as [|k IH]; intros a Ha Hk H1; [reflexivity|].
    pose proof (H1 a ltac:(lia)) as B. cbn [rdn] in B |- *.
    destruct (match Mx (Z_to_bv 64 a) with Some b => Some b | None => seg_rom RSEGS (Z_to_bv 64 a) end) as [b|]; [|discriminate B].
    injection B as ->.
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)) by (apply Z_to_bv_u_eq'; rewrite u_add1 by (rewrite u_Z2bv by lia; lia); rewrite u_Z2bv by lia; reflexivity).
    rewrite (IH (a + 1)); [reflexivity | lia | lia |]. intros i Hi. apply H1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma byte_list_eq : forall l1 l2 : list byte, map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
  Proof using.
    induction l1 as [|a l1 IH]; intros [|b l2] E; cbn in E; try discriminate E; [reflexivity|].
    injection E as E1 E2. f_equal; [apply bv_eq; exact E1 | exact (IH _ E2)].
  Qed.
  Lemma w2b_zero : forall k, (k = 1%nat \/ k = 4%nat \/ k = 8%nat) -> word_to_le_bytes k (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) k.
  Proof using. intros k [->|[->| ->]]; apply byte_list_eq; vm_compute; reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma ctx_cell0 : forall (Mx : mem) a (k : nat),
    (forall i, a <= i < a + Z.of_nat k -> Mx (Z_to_bv 64 i) = None) ->
    MLOCK <= a -> a + Z.of_nat k <= CTX_END -> (k = 1%nat \/ k = 4%nat \/ k = 8%nat) ->
    cell Mx a k 0.
  Proof using.
    intros Mx a k CLR Ha Hk K. unfold cell.
    assert (R : rdn RSEGS Mx (Z_to_bv 64 a) k = Some (repeat (Z_to_bv 8 0) k)).
    { apply rdn_zeros; [unfold MLOCK in Ha; lia | unfold CTX_END, CTX in Hk; lia |].
      intros i Hi. rewrite (rdn_img RSEGS Mx i 1 a (a + Z.of_nat k) CLR) by (unfold MLOCK, CTX_END, CTX in *; cbn; lia).
      apply img_ctx_zero. lia. }
    rewrite R, (w2b_zero k K). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac img_read_eq :=
    lazymatch goal with |- ?r = Some ?bs =>
      let v := eval vm_compute in (option_map (map bv_unsigned) r) in
      lazymatch v with Some ?l =>
        let H2 := fresh in
        assert (H2 : option_map (map bv_unsigned) r = Some l) by (vm_compute; reflexivity);
        revert H2; generalize r; intros [bs0|] H2; [|discriminate H2];
        cbn [option_map] in H2; injection H2 as H2; f_equal; apply byte_list_eq; rewrite H2; vm_compute; reflexivity
      end
    end.
  Lemma img_errno0 : rdn RSEGS (fun _ => None) (Z_to_bv 64 A_ERRNO) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0)).
  Proof using. img_read_eq. Qed.
  Lemma img_got : rdn RSEGS (fun _ => None) (Z_to_bv 64 A_GOT_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY)).
  Proof using. img_read_eq. Qed.

  Variables (can sec : Z).
  Hypothesis Hcan : 0 <= can < 2 ^ 64.
  Hypothesis Hsec : 0 <= sec < 2 ^ 64.
  #[local] Notation ST := (st_pristine can sec).





  (* [comment removed for export] *)
  Ltac kill H :=
    lazymatch type of H with
    | False => contradiction
    | ex _ => let H1 := fresh in destruct H as [? H1]; kill H1
    | _ /\ _ => let H1 := fresh in let H2 := fresh in destruct H as [H1 H2]; first [kill H1 | kill H2]
    | _ \/ _ => let H1 := fresh in destruct H as [H1|H1]; [kill H1 | kill H1]
    | In _ [] => destruct H
    | _ => first [ progress (unfold metaU, is_meta_of, fresh, areab, appb, listed, in_flist, in_alist, is_group in H); kill H
                 | progress (cbn in H); kill H
                 | clear -H; lia ]
    end.
  Ltac pcrush :=
    cbn; intros;
    first [ exact Hsec | exact Hcan | reflexivity | contradiction | solve [constructor]
          | solve [unfold NSLOTS, AREAMAX, LMAX; cbn; lia]
          | solve [unfold dll, zlen; cbn; intros; lia]
          | solve [match goal with H : _ |- _ => kill H end] ].

  Lemma prist_WF : WF ST [].
  Proof using Hsec Hcan.
    unfold WF. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]]; constructor; pcrush.
  Qed.

  Lemma prist_LEDGERX : forall vm : VmMaps,
    vm_maps vm = [] -> vm_noaccess vm = [] -> vm_brk vm = vm_start_brk vm ->
    bv_unsigned (vm_start_brk vm) mod 4096 = 0 -> IMG_HI <= bv_unsigned (vm_start_brk vm) ->
    bv_unsigned (vm_start_brk vm) + 8192 <= CEIL ->
    vm_reserved vm = segments_reserved RSEGS -> page_floor (alloc_top vm) = CEIL ->
    LEDGERX ST [] vm.
  Proof using.
    intros vm Hm Hn Hb Hal Hhi Hce Hres Htop. constructor; cbn.
    - rewrite Hm. apply Permutation_refl.
    - rewrite Hn. unfold noacc_of. cbn. apply Permutation_refl.
    - repeat split; assumption.
    - exact Hres.
    - exact Htop.
  Qed.

  (* [comment removed for export] *)
  Lemma prist_REP : forall (Mx : mem),
    (forall i, MLOCK <= i < CTX_END -> ~ (CTX <= i < CTX + 12) -> Mx (Z_to_bv 64 i) = None) ->
    cell Mx ctx_secret 8 sec -> cell Mx ctx_init_done 4 1 ->
    cell Mx A_NEED_LOCKS 1 0 -> cell Mx A_PAGESIZE 8 4096 -> cell Mx A_CANARY 8 can ->
    cell Mx A_GOT_CANARY 8 A_CANARY -> cell Mx A_ERRNO 4 0 ->
    img_clear Mx A_TAB_CTZ (A_TAB_CTZ + 32) -> img_clear Mx A_TAB_SC (A_TAB_MED + 4) ->
    REP ST Mx.
  Proof using.
    intros Mx CLR SEC INIT NL PG CAN GOT ERR TC TS.
    assert (Z0 : forall a k, CTX + 12 <= a -> a + Z.of_nat k <= CTX_END -> (k = 1%nat \/ k = 4%nat \/ k = 8%nat) -> cell Mx a k 0).
    { intros a k Ha Hk K. apply ctx_cell0; [| unfold MLOCK, CTX in *; lia | exact Hk | exact K].
      intros i Hi. apply CLR; unfold MLOCK, CTX_END, CTX in *; lia. }
    constructor.
    - constructor; try assumption. apply ctx_cell0; [| lia | unfold MLOCK, CTX_END, CTX; cbn; lia | right; left; reflexivity].
      intros i Hi. apply CLR; unfold MLOCK, CTX_END, CTX in *; cbn in Hi; lia.
    - constructor; cbn; intros;
        first [ exact SEC | exact INIT
              | apply Z0; unfold ctx_mmap_counter, ctx_free_meta_head, ctx_avail_meta, ctx_avail_meta_count, ctx_avail_meta_area_count,
                  ctx_meta_alloc_shift, ctx_meta_area_head, ctx_meta_area_tail, ctx_avail_meta_areas, ctx_active, ctx_usage,
                  ctx_unmap_seq, ctx_bounces, ctx_seq, ctx_brk, CTX_END; cbn; lia ].
    - intros a [].
    - intros m [].
  Qed.
End Pristine.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Init.
  Context {RN : mh_run}.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Lemma am_frame_top : forall (X Y : mem) sp can ra s0 s1 s2 s3 s4 a,
    64 <= sp -> sp < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> sp - 56 <= a < sp ->
    am_frame X sp can ra s0 s1 s2 s3 s4 (Z_to_bv 64 a) = am_frame Y sp can ra s0 s1 s2 s3 s4 (Z_to_bv 64 a).
  Proof using.
    intros X Y sp can ra s0 s1 s2 s3 s4 a S1 S2 Ha Hin. unfold am_frame.
    repeat match goal with
    | |- wbytes ?MX (Z_to_bv 64 ?b) ?bs (Z_to_bv 64 a) = wbytes ?MY (Z_to_bv 64 ?b) ?bs (Z_to_bv 64 a) =>
        let IN := fresh "IN" in let OUT := fresh "OUT" in
        destruct (decide (b <= a < b + 8)) as [IN|OUT];
        [ rewrite !(wbytes_get_inside bs) by (wd_lenlit; rewrite ?length_N_to_le_bytes, ?u_Z2bv by lia; cbn; lia); reflexivity
        | rewrite !(wbytes_outZ _ b bs a) by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia) ]
    end.
    exfalso. lia.
  Qed.
  Lemma am_frame_out : forall (X : mem) sp can ra s0 s1 s2 s3 s4 a,
    64 <= sp -> sp < 2 ^ 64 -> 0 <= a < 2 ^ 64 -> ~ (sp - 56 <= a < sp) ->
    am_frame X sp can ra s0 s1 s2 s3 s4 (Z_to_bv 64 a) = X (Z_to_bv 64 a).
  Proof using.
    intros X sp can ra s0 s1 s2 s3 s4 a S1 S2 Ha Hout. unfold am_frame.
    rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma am_ok_xfer : forall st L X sp regs (M MI : mem) mdl rom c',
    (forall a, 0 <= a < 2 ^ 64 -> MI (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> (sp - AMSTK <= a < sp) \/ (CTX <= a < CTX_END)) ->
    am_ok st L X sp regs MI mdl rom c' -> am_ok st L X sp regs M mdl rom c'.
  Proof using.
    intros st L X sp regs M MI mdl rom c' DIF
      (st' & M' & mdl' & regs' & mm & E & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & X20 & FR & DF).
    exists st', M', mdl', regs', mm.
    split; [exact E|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|].
    split; [exact X7|]. split; [exact X8|]. split; [exact X9|]. split; [exact X10|]. split; [exact X11|]. split; [exact X12|]. split; [exact X13|].
    split; [exact X14|]. split; [exact X15|]. split; [exact X16|]. split; [exact X17|]. split; [exact X18|]. split; [exact X19|]. split; [exact X20|].
    split; [|exact DF].
    intros a Ha NE. destruct (decide (M' (Z_to_bv 64 a) = MI (Z_to_bv 64 a))) as [E1|NE1].
    - rewrite E1 in NE. left. destruct (DIF a Ha NE) as [W|W]; [left; exact W | right; left; exact W].
    - exact (FR a Ha NE1).
  Qed.
  Lemma am_fail_xfer : forall st L X sp regs (M MI : mem) mdl rom c',
    (forall a, 0 <= a < 2 ^ 64 -> MI (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> (sp - AMSTK <= a < sp) \/ (CTX <= a < CTX_END)) ->
    am_fail st L X sp regs MI mdl rom c' -> am_fail st L X sp regs M mdl rom c'.
  Proof using.
    intros st L X sp regs M MI mdl rom c' DIF
      (st' & M' & mdl' & regs' & E & X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X19 & FR & DF).
    exists st', M', mdl', regs'.
    split; [exact E|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|].
    split; [exact X7|]. split; [exact X8|]. split; [exact X9|]. split; [exact X10|]. split; [exact X11|]. split; [exact X12|]. split; [exact X13|].
    split; [exact X14|]. split; [exact X15|]. split; [exact X16|]. split; [exact X17|]. split; [exact X18|]. split; [exact X19|].
    split; [|exact DF].
    intros a Ha NE. destruct (decide (M' (Z_to_bv 64 a) = MI (Z_to_bv 64 a))) as [E1|NE1].
    - rewrite E1 in NE. destruct (DIF a Ha NE) as [W|W]; [left; exact W | right; left; exact W].
    - exact (FR a Ha NE1).
  Qed.

  Theorem alloc_meta_init : AM_INIT.
  Proof using.
    intros F bi bo M mdl regs rom sp auxw avl HL Hside FE FI ENV Hh Hlz Hmat H2 Hra Hsplo Hsphi H4 DEF Hok Hfail.
    destruct FE as [FEctx FEauxv FErng FEkeys FEend FErnd FEpg FElocks [canv FEcan] [FEmaps FEnoacc] (FB1 & FB2 & FB3 & FB4) FEres FEtop FElim].
    destruct FI as [FIerr FIgot FIctz FIsc]. pose proof ENV as [SPa SPr].
    assert (Hsp : CEIL + AMSTK <= sp /\ sp < 2 ^ 64) by (split; assumption).
    assert (Hsp64 : CEIL + 64 <= sp /\ sp < 2 ^ 64) by (unfold AMSTK in Hsplo; lia).
    ceil.
    assert (Hauxw : 0 <= auxw < 2 ^ 64) by lia.
    set (can := bv_unsigned (Z_to_bv 64 canv)). pose proof (u64_range (Z_to_bv 64 canv)) as Hcan. fold can in Hcan.
    assert (M_can : rdn RSEGS M (Z_to_bv 64 A_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 can))).
    { unfold can. rewrite Z_to_bv_bv_unsigned. exact FEcan. }
    assert (SOK64 : store_ok RSEGS M (Z_to_bv 64 (sp - 64)) 64%nat = true).
    { eapply (store_ok_defined M (sp - AMSTK) sp); [exact DEF | unfold AMSTK; lia | cbn; lia | unfold AMSTK; lia | lia]. }
    assert (M_got : rdn RSEGS M (Z_to_bv 64 A_GOT_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY))).
    { rewrite (rdn_img RSEGS M A_GOT_CANARY 8 A_GOT_CANARY (A_GOT_CANARY + 8) FIgot) by (unfold A_GOT_CANARY; cbn; lia). exact img_got. }
    assert (M_init0 : rdn RSEGS M (Z_to_bv 64 ctx_init_done) 4%nat = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
    { apply (ctx_cell0 M ctx_init_done 4); [| unfold ctx_init_done, MLOCK, CTX; lia | unfold ctx_init_done, CTX_END, CTX; cbn; lia | right; left; reflexivity].
      intros i Hi. apply FEctx. unfold ctx_init_done, MLOCK, CTX_END, CTX in *. cbn in Hi. lia. }
    (* [comment removed for export] *)
    destruct (amI1 M sp can auxw Hsp64 SOK64 M_got M_can M_init0 FEauxv regs rom H2) as (r1 & w0 & RUN1 & A2 & A19 & A8 & A18 & A9 & A20 & A10 & KA).
    unfold AM_ENTRY. replace (Z_to_bv 64 420968) with (0x66c68%bv : word) by (apply bv_eq; reflexivity).
    eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUN1 |].
    set (mc0 := wbytes (am_frame M sp can (getr regs 1) (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20)) (Z_to_bv 64 (sp - 64)) (word_to_le_bytes 8 w0)).
    assert (AG0 : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mc0 (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
    { intros x Hx NI. unfold mc0. rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). apply am_frame_out; lia. }
    assert (GR0 : mem_grows M mc0).
    { unfold mc0. eapply mem_grows_trans; [|apply wbytes_grows]. unfold am_frame. do 7 (eapply mem_grows_trans; [|apply wbytes_grows]). apply mem_grows_refl. }
    assert (SOK0 : store_ok RSEGS mc0 (Z_to_bv 64 (sp - 64)) 8%nat = true).
    { eapply (store_ok_defined mc0 (sp - AMSTK) sp); [| unfold AMSTK; lia | cbn; lia | unfold AMSTK; lia | lia]. eapply defined_grows; [exact GR0 | exact DEF]. }
    assert (RD0 : exists bs0, length bs0 = 8%nat /\ rdn RSEGS mc0 (Z_to_bv 64 (sp - 64)) 8%nat = Some bs0).
    { exists (word_to_le_bytes 8 w0). split; [rewrite length_N_to_le_bytes; reflexivity | unfold mc0; apply rdn_wbytes_hit8; zsimp; lia]. }
    assert (A9' : getr r1 9 = Z_to_bv 64 (16 * Z.of_nat (@length (Z * Z) []))) by (cbn [length Z.of_nat]; rewrite Z.mul_0_r; exact A9).
    (* [comment removed for export] *)
    destruct (amI_loop M sp can auxw Hsp64 Hcan Hauxw FEauxv avl FErng FEkeys FEend FErnd ENV avl [] r1 mc0 rom eq_refl
                A9' A10 A20 A8 A2 AG0 SOK0 RD0)
      as (rL & mcL & RUNL & AGL & GRL & L2 & L8 & KL & bs1 & Lbs1 & RD1).
    eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUNL |].
    assert (AGLM : forall x, 0 <= x < 2 ^ 64 -> ~ (sp - 64 <= x < sp) -> mcL (Z_to_bv 64 x) = M (Z_to_bv 64 x)).
    { intros x Hx NI. rewrite (AGL x Hx ltac:(lia)). exact (AG0 x Hx NI). }
    (* [comment removed for export] *)
    destruct (amI3 sp auxw Hsp64 avl rL rom mcL bs1 L2 ltac:(kept_rw KL; exact A19) L8 Lbs1 RD1
                (rd_low M sp auxw Hsp64 Hauxw avl FErng ENV mcL A_PAGESIZE 8%nat _ AGLM ltac:(unfold A_PAGESIZE; lia) ltac:(unfold A_PAGESIZE; cbn; lia) FEpg))
      as (rT & RUNT & T2 & T19 & T8 & KT).
    eapply (kfx_msteps RSEGS F HL); [exact Hh | exact Hlz | exact RUNT |].
    set (sec := bytes_le_to_Z bs1). pose proof (bytes_le_to_Z_range bs1 Lbs1) as Hsec. fold sec in Hsec.
    set (MI := wbytes (wbytes mcL (Z_to_bv 64 ctx_secret) (word_to_le_bytes 8 (Z_to_bv 64 sec))) (Z_to_bv 64 ctx_init_done) (word_to_le_bytes 4 (Z_to_bv 64 1))).
    (* [comment removed for export] *)
    assert (MIW : forall a, 0 <= a < 2 ^ 64 -> MI (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> (sp - AMSTK <= a < sp) \/ (CTX <= a < CTX_END)).
    { intros a Ha NE. unfold MI in NE.
      destruct (decide (mcL (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE2].
      - rewrite <- E in NE. right. unfold ctx_secret, ctx_init_done, CTX_END, CTX in NE |- *. wdiff NE mcL a.
      - left. destruct (decide (sp - 64 <= a < sp)) as [IN|OUT]; [unfold AMSTK; lia|]. exfalso. exact (NE2 (AGLM a Ha OUT)). }
    assert (MIlow : forall a, 0 <= a -> a < sp - 64 -> ~ (CTX <= a < CTX + 12) -> MI (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hlo NC. unfold MI, ctx_secret, ctx_init_done, CTX in *. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
      apply AGLM; lia. }
    assert (RDlow : forall a k bs, 0 <= a -> a + Z.of_nat k <= sp - 64 -> (a + Z.of_nat k <= CTX \/ CTX + 12 <= a) ->
                    rdn RSEGS M (Z_to_bv 64 a) k = Some bs -> rdn RSEGS MI (Z_to_bv 64 a) k = Some bs).
    { intros a k bs Ha Hk OUT R. rewrite <- R. apply rdn_ext; [rewrite u_Z2bv by lia; lia|].
      intros x Hx. rewrite u_Z2bv in Hx by lia. pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_u_eq' x (bv_unsigned x) eq_refl).
      apply MIlow; lia. }
    (* [comment removed for export] *)
    pose proof (prist_WF can sec Hcan Hsec) as PWF.
    assert (PREP : REP (st_pristine can sec) MI).
    { apply (prist_REP can sec MI).
      - intros i Hi NC. rewrite MIlow by (unfold MLOCK, CTX_END, CTX in *; lia). apply FEctx. exact Hi.
      - unfold cell, MI, ctx_secret, ctx_init_done, CTX. rdn_peel1. apply rdn_wbytes_hit8. zsimp; lia.
      - unfold cell, MI, ctx_init_done, CTX. pose proof (rdn_wbytes_hit RSEGS (word_to_le_bytes 4 (Z_to_bv 64 1)) (wbytes mcL (Z_to_bv 64 ctx_secret) (word_to_le_bytes 8 (Z_to_bv 64 sec))) (Z_to_bv 64 (CTX + 8))) as RH.
        rewrite length_N_to_le_bytes in RH. unfold CTX in RH. apply RH. zsimp; lia.
      - apply (RDlow A_NEED_LOCKS 1%nat _ ltac:(unfold A_NEED_LOCKS; lia) ltac:(unfold A_NEED_LOCKS; cbn; lia) ltac:(unfold A_NEED_LOCKS, CTX; cbn; lia) FElocks).
      - apply (RDlow A_PAGESIZE 8%nat _ ltac:(unfold A_PAGESIZE; lia) ltac:(unfold A_PAGESIZE; cbn; lia) ltac:(unfold A_PAGESIZE, CTX; cbn; lia) FEpg).
      - apply (RDlow A_CANARY 8%nat _ ltac:(unfold A_CANARY; lia) ltac:(unfold A_CANARY; cbn; lia) ltac:(unfold A_CANARY, CTX; cbn; lia) M_can).
      - apply (RDlow A_GOT_CANARY 8%nat _ ltac:(unfold A_GOT_CANARY; lia) ltac:(unfold A_GOT_CANARY; cbn; lia) ltac:(unfold A_GOT_CANARY, CTX; cbn; lia) M_got).
      - apply (RDlow A_ERRNO 4%nat _ ltac:(unfold A_ERRNO, TPV; lia) ltac:(unfold A_ERRNO, TPV; cbn; lia) ltac:(unfold A_ERRNO, TPV, CTX; cbn; lia)).
        rewrite (rdn_img RSEGS M A_ERRNO 4 A_ERRNO (A_ERRNO + 4) FIerr) by (unfold A_ERRNO, TPV; cbn; lia). exact img_errno0.
      - intros i Hi. rewrite MIlow by (unfold A_TAB_CTZ, CTX in *; lia). exact (FIctz i Hi).
      - intros i Hi. rewrite MIlow by (unfold A_TAB_SC, A_TAB_MED, CTX in *; lia). exact (FIsc i Hi). }
    assert (PLG : LEDGERX (st_pristine can sec) [] (m_vmmaps mdl)).
    { apply (prist_LEDGERX can sec); try assumption. lia. }
    (* [comment removed for export] *)
    assert (EMI : MI = UbMhAMetaS.M1 (st_pristine can sec) MI regs sp).
    { unfold UbMhAMetaS.M1, UbMhAMetaS.can. cbn [s_canary st_pristine].
      apply FunctionalExtensionality.functional_extensionality. intros x.
      pose proof (u64_range x) as XR. rewrite <- (Z_to_bv_bv_unsigned 64 x). set (a := bv_unsigned x) in *. clearbody a.
      destruct (decide (sp - 56 <= a < sp)) as [IN|OUT].
      - rewrite (am_frame_top MI M sp can _ _ _ _ _ _ a) by lia.
        unfold MI, ctx_secret, ctx_init_done, CTX. rewrite !wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia).
        rewrite (AGL a) by lia. unfold mc0. rewrite wbytes_outZ by (wd_lenlit; rewrite ?length_N_to_le_bytes; cbn; lia). reflexivity.
      - rewrite am_frame_out by lia. reflexivity. }
    rewrite EMI at 1.
    apply (UbMhAMetaC.arm_C2 (st_pristine can sec) [] [] MI mdl regs rom sp F bi HL PWF PREP PLG xok_nil Hh Hlz Hmat
             ltac:(intros _ _; cbn; unfold AREAMAX; lia) ltac:(cbn; lia) ltac:(change (XSUM [] + RSUM [] + 2 ^ 24 <= vm_limit (m_vmmaps mdl)); rewrite XSUM_nil; replace (RSUM []) with 0 by reflexivity; unfold VMLIM, MH_GBUDGET, MBASE in FElim; lia)
             H2 Hra Hsp H4
             ltac:(eapply defined_grows; [|exact DEF]; do 2 (eapply mem_grows_trans; [|apply wbytes_grows]); eapply mem_grows_trans; [|exact GRL]; unfold mc0; eapply mem_grows_trans; [|apply wbytes_grows]; unfold am_frame; do 7 (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl)
             (fun c' Hc' => Hok can sec c' (am_ok_xfer _ _ _ _ _ M MI _ _ _ MIW (UbMhAMetaS.am_post_ok _ _ _ _ _ _ _ _ _ Hc')))
             (fun c' Hc' => Hfail can sec c' (am_fail_xfer _ _ _ _ _ M MI _ _ _ MIW Hc'))
             eq_refl eq_refl eq_refl eq_refl bo rT Hside T2 T19 T8 ltac:(kept_rw KT; kept_rw KL; exact A18)).
    (* [comment removed for export] *)
    eapply keeps_but_trans; [| eapply keeps_but_trans; [|eapply keeps_but_mono; [exact KT | intros r Hr; unfold clobI, clobA; cbn in Hr |- *; tauto]]].
    - eapply keeps_but_mono; [exact KA | intros r Hr; unfold clobI, clobA; cbn in Hr |- *; tauto].
    - eapply keeps_but_mono; [exact KL | intros r Hr; unfold clobL, clobI, clobA in *; cbn in Hr |- *; tauto].
  Qed.
End Init.
End UbMhAMetaI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocKB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module UbMhMallocTop3.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.glaze.binary_reflection.images.Ubsan.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount.UbMhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocKB OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Top.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Hypothesis HAM : AM_SPEC3.

  (* [comment removed for export] *)
  Lemma malloc_thunk : forall regs (M : mem) rom mdl (Q : config -> Prop),
    m_halted mdl = None -> m_vm_lazy mdl = [] ->
    kat RSEGS (mkCfg (mkst regs (0x66f40%bv : word) M rom) mdl) Q ->
    kat RSEGS (mkCfg (mkst regs (0x662d0%bv : word) M rom) mdl) Q.
  Proof using.
    intros regs M rom mdl Q Hh Hl K.
    eapply kat_step; [exact Hh | exact Hl | reflexivity | exact (step_jal_x0 _ _ _ _ _ _ _ F_6627c eq_refl D_6627c) |].
    replace (btgt (0x662d0%bv : word) (bv_signed _)) with (0x66f40%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    exact K.
  Qed.

  Lemma word_of_u : forall (a : word), a = Z_to_bv 64 (bv_unsigned a).
  Proof using. intros a. pose proof (u64_range a). apply bv_eq. rewrite u_Z2bv by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma malloc_exit : forall (stk : Z) R M mdl Lc B C (ret n sp : Z),
    stk <= MSTK_M ->
    PHI Lc <= B -> Z.of_nat (length Lc) <= C -> VMLIM <= vm_limit (m_vmmaps mdl) ->
    getr R 1 = Z_to_bv 64 ret -> 1 <= n ->
    getr R 2 = Z_to_bv 64 sp -> CEIL + MSTK_M <= sp -> sp < 2 ^ 64 ->
    (forall a : word, sp - MSTK_M <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) ->
    forall c', malloc_postk stk Lc n sp R M mdl (seg_rom RSEGS) c' -> malloc_ok AINV MSTK_M R M mdl Lc B C ret n sp c'.
  Proof using.
    intros stk R M mdl Lc B C ret n sp Hstk HB HC HV H1 Hn E2 Hsplo Hsphi SOK c' POST.
    destruct POST as (R' & M' & mdl' & p & st' & -> & CS & P10 & P16 & Plo & Phi & Pimg & NIL & APL & FR & DF & DFp & W' & RP' & LG' & NJ' & NL' & X1 & X2 & X3 & X4 & X5 & X6).
    unfold MSTK_M in *. ceil.
    destruct CS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    assert (PU : bv_unsigned (Z_to_bv 64 p) = p) by (rewrite u_Z2bv by (unfold HEAPLO in *; lia); reflexivity).
    unfold malloc_ok. rewrite H1. exists R', M', mdl', (Z_to_bv 64 p). rewrite ?PU.
    split; [reflexivity|].
    split.
    { intros r Hr. unfold callee_saved_regs in Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20
                                             | exact Q21 | exact Q22 | exact Q23 | exact Q24 | exact Q25 | exact Q26 | exact Q27] |]).
      destruct Hr. }
    split; [exact P10|]. split; [exact P16|].
    split; [unfold blk_ok; repeat split; try assumption; lia|].
    split; [exact APL|].
    split.
    { intros a Ha. rewrite (word_of_u a). pose proof (u64_range a) as AR.
      split; [apply DFp; lia|]. eapply (store_ok_of_defined1 M' p (p + n)); [exact DFp | unfold HEAPLO in *; lia | lia | lia]. }
    split.
    { intros a NE. pose proof (u64_range a) as AR. rewrite (word_of_u a) in NE.
      destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold mh_changed.
      - right; left. lia.
      - left. unfold in_blocks, app_of in *. exact A.
      - right; right; left. exact A.
      - right; right; right. exact A. }
    split.
    { intros a Ha. pose proof (u64_range a) as AR.
      destruct (Z.lt_ge_cases (bv_unsigned a) (sp - stk)) as [LO|HI].
      - assert (EQ : M' a = M a).
        { destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso. rewrite (word_of_u a) in NE.
          destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in *; lia. }
        pose proof (SOK a Ha) as S0. cbn [store_ok] in S0 |- *. unfold wview in S0 |- *. rewrite EQ. exact S0.
      - rewrite (word_of_u a). eapply (store_ok_of_defined1 M' (sp - stk) sp); [exact DF | lia | lia | lia]. }
    split.
    { split; [exists st'; split; [exact W'|]; split; [exact RP'|]; split; [exact LG'|]; split; [exact NJ'|exact NL']|].
      cbn [PHI length snd fst]. rewrite Nat2Z.inj_succ. split; [lia|]. split; [lia|]. rewrite X6. exact HV. }
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma malloc_exitF : forall (stk : Z) R M mdl Lc B C (ret sp : Z),
    stk <= MSTK_M ->
    PHI Lc <= B -> Z.of_nat (length Lc) <= C -> VMLIM <= vm_limit (m_vmmaps mdl) ->
    getr R 1 = Z_to_bv 64 ret ->
    getr R 2 = Z_to_bv 64 sp -> CEIL + MSTK_M <= sp -> sp < 2 ^ 64 ->
    (forall a : word, sp - MSTK_M <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) ->
    forall c', malloc_failk stk Lc sp R M mdl (seg_rom RSEGS) c' -> malloc_null AINV MSTK_M R M mdl Lc B C ret sp c'.
  Proof using.
    intros stk R M mdl Lc B C ret sp Hstk HB HC HV H1 E2 Hsplo Hsphi SOK c' POST.
    destruct POST as (R' & M' & mdl' & st' & -> & CS & P10 & FR & DF & W' & RP' & LG' & NJ' & NL' & X1 & X2 & X3 & X4 & X5 & X6).
    unfold MSTK_M in *. ceil.
    destruct CS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    unfold malloc_null. rewrite H1. exists R', M', mdl'.
    split; [reflexivity|].
    split.
    { intros r Hr. unfold callee_saved_regs in Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20
                                             | exact Q21 | exact Q22 | exact Q23 | exact Q24 | exact Q25 | exact Q26 | exact Q27] |]).
      destruct Hr. }
    split; [exact P10|].
    split.
    { intros a NE. pose proof (u64_range a) as AR. rewrite (word_of_u a) in NE.
      destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold mh_changed.
      - right; left. lia.
      - left. unfold in_blocks, app_of in *. exact A.
      - right; right; left. exact A.
      - right; right; right. exact A. }
    split.
    { intros a Ha. pose proof (u64_range a) as AR.
      destruct (Z.lt_ge_cases (bv_unsigned a) (sp - stk)) as [LO|HI].
      - assert (EQ : M' a = M a).
        { destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso. rewrite (word_of_u a) in NE.
          destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in *; lia. }
        pose proof (SOK a Ha) as S0. cbn [store_ok] in S0 |- *. unfold wview in S0 |- *. rewrite EQ. exact S0.
      - rewrite (word_of_u a). eapply (store_ok_of_defined1 M' (sp - stk) sp); [exact DF | lia | lia | lia]. }
    split.
    { split; [exists st'; split; [exact W'|]; split; [exact RP'|]; split; [exact LG'|]; split; [exact NJ'|exact NL']|].
      split; [exact HB|]. split; [exact HC|]. rewrite X6. exact HV. }
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma malloc_kfx : forall F (bo : bool) R M mdl Lc B C ret n sp st,
    kfam_laws RSEGS F ->
    WF st Lc -> REP st M -> LEDGER st (m_vmmaps mdl) -> nojunk st -> nolimbo st ->
    (bo = true -> n < MMAP_THRESHOLD -> agf st) ->
    PHI Lc <= B -> Z.of_nat (length Lc) <= C -> VMLIM <= vm_limit (m_vmmaps mdl) ->
    malloc_pre MSTK_M R M mdl B C ret n sp ->
    (forall c', malloc_ok AINV MSTK_M R M mdl Lc B C ret n sp c' -> Kok F c') ->
    (forall c', malloc_null AINV MSTK_M R M mdl Lc B C ret sp c' -> Kf F c') ->
    kfx F bo (malloc_cfg R M mdl).
  Proof using HAM.
    intros F bo R M mdl Lc B C ret n sp st HL HWF HREP HLG NJ NL SIDE HBB HCC HV PRE Hok Hf.
    destruct PRE as (Hh & Hlz & Hmat & H1 & Hret & Hret2 & H10 & Hn & H2 & Hsp16 & Hsplo & H4 & SOK & HB & HC).
    pose proof (u64_range (getr R 2)) as SPR. rewrite H2 in SPR.
    assert (E2 : getr R 2 = Z_to_bv 64 sp) by (apply bv_eq; rewrite u_Z2bv by lia; exact H2).
    pose proof (u64_range (getr R 10)) as NR. rewrite H10 in NR.
    assert (E10 : getr R 10 = Z_to_bv 64 n) by (apply bv_eq; rewrite u_Z2bv by lia; exact H10).
    assert (Hra : ret_ok (getr R 1)) by (rewrite H1; apply ret_ok_even; rewrite u_Z2bv by lia; exact Hret2).
    pose proof Hsplo as Hsplo'. unfold MSTK_M in Hsplo'. ceil. unfold MH_GBUDGET in HB. unfold VMLIM, MH_GBUDGET in HV.
    pose proof (PHI_nonneg Lc ltac:(intros b Hb; destruct b as [b1 b2]; cbn; destruct (live_zone st Lc HWF b1 b2 Hb) as (_ & _ & X); exact (proj1 X))) as PH0.
    assert (DEF : defined M (sp - MSTK_M) sp).
    { apply (defined_of_store_ok M (sp - MSTK_M) sp); [unfold MSTK_M; lia | lia | right; unfold MSTK_M; lia |]. intros a Ha.
      pose proof (SOK (Z_to_bv 64 a)) as X. rewrite u_Z2bv in X by (unfold MSTK_M in *; lia). apply X. exact Ha. }
    unfold MSTK_M in DEF.
    pose proof (wL_len st Lc (WF_live st Lc HWF)) as LEN.
    unfold malloc_cfg, A_MALLOC. replace (Z_to_bv 64 418512) with (0x662d0%bv : word) by (apply bv_eq; reflexivity).
    apply (kfx_of_kat F HL bo). apply malloc_thunk; [exact Hh | exact Hlz|].
    destruct (Z.lt_ge_cases n MMAP_THRESHOLD) as [SMALL|BIG].
    - (* [comment removed for export] *)
      apply (malloc_small_kfx st Lc M mdl R (seg_rom RSEGS) n sp F bo HL (alloc_slot_run3 HAM) ltac:(intros Hbo; exact (SIDE Hbo SMALL))
               HWF HREP HLG NJ NL Hh Hlz Hmat ltac:(unfold MBASE, MBLK in *; lia) ltac:(lia) ltac:(lia) E10 Hra E2 H4
               ltac:(rewrite SSTK_val; lia) ltac:(intros y Hy; apply DEF; rewrite SSTK_val in Hy; lia) (fun _ => True)).
      + intros c' P'. apply Hok. exact (malloc_exit SSTK R M mdl Lc B C ret n sp ltac:(rewrite SSTK_val; unfold MSTK_M; lia) HBB HCC
                              ltac:(unfold VMLIM, MH_GBUDGET; exact HV) H1 ltac:(lia) E2 Hsplo ltac:(lia) SOK c' (postkX_postk _ _ _ _ _ _ _ _ _ _ P')).
      + intros c' P'. apply Hf. exact (malloc_exitF SSTK R M mdl Lc B C ret sp ltac:(rewrite SSTK_val; unfold MSTK_M; lia) HBB HCC
                              ltac:(unfold VMLIM, MH_GBUDGET; exact HV) H1 E2 Hsplo ltac:(lia) SOK c' P').
      + intros; exact I.
    - (* [comment removed for export] *)
      assert (J : junk_in st []) by (intros x k o Hx Hk E; exfalso; exact (NJ x k o Hx Hk E)).
      pose proof (regions_room st Lc [] HWF J ltac:(cbn; lia)) as HCR.
      pose proof (areas_room st Lc [] HWF J ltac:(cbn; lia) ltac:(rewrite NL; cbn; lia)) as HCA.
      pose proof (rsum_MBASE st Lc [] HWF J ltac:(cbn; lia) ltac:(rewrite NL; cbn; lia)
                    ltac:(intros m off Hm _; exact (NJ m 0 off Hm ltac:(pose proof (glast_rng st m); lia)))) as RS.
      apply (malloc_big_kfx st Lc M mdl R (seg_rom RSEGS) n sp F bo HL HAM HWF HREP HLG NJ NL Hh Hlz Hmat HCR HCA
               ltac:(unfold MBASE, MBLK in *; lia) ltac:(lia) ltac:(unfold MMAP_THRESHOLD, MBLK in *; lia) E10 Hra E2 H4
               ltac:(unfold BSTK; lia) ltac:(intros y Hy; apply DEF; unfold BSTK in Hy; lia)).
      + intros c' P'. apply Hok. exact (malloc_exit BSTK R M mdl Lc B C ret n sp ltac:(unfold BSTK, MSTK_M; lia) HBB HCC
                              ltac:(unfold VMLIM, MH_GBUDGET; exact HV) H1 ltac:(lia) E2 Hsplo ltac:(lia) SOK c' (postkR_postk _ _ _ _ _ _ _ _ _ _ P')).
      + intros c' P'. apply Hf. exact (malloc_exitF BSTK R M mdl Lc B C ret sp ltac:(unfold BSTK, MSTK_M; lia) HBB HCC
                              ltac:(unfold VMLIM, MH_GBUDGET; exact HV) H1 E2 Hsplo ltac:(lia) SOK c' (failkR_failk _ _ _ _ _ _ _ _ _ P')).
  Qed.

  Theorem malloc_katw3 : MALLOC_KATW MSTK_M.
  Proof using HAM.
    intros R M mdl Lc B C ret n sp HA PRE F HL Hok Hf.
    pose proof HA as ((st & HWF & HREP & HLG & NJ & NL) & HBB & HCC & HV).
    exact (malloc_kfx F false R M mdl Lc B C ret n sp st HL HWF HREP HLG NJ NL ltac:(intros X; discriminate X) HBB HCC HV PRE Hok Hf).
  Qed.


  Theorem malloc_alt_f3 : MALLOC_ALT_F MSTK_M.
  Proof using HAM.
    intros R M mdl Lc B C ret n sp HA PRE F HL Hok Hf.
    pose proof HA as ((st & HWF & HREP & HLG & NJ & NL & AGF) & HBB & HCC & HV).
    exact (malloc_kfx F true R M mdl Lc B C ret n sp st HL HWF HREP HLG NJ NL ltac:(intros _ _; exact AGF) HBB HCC HV PRE Hok Hf).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma malloc_exitR : forall st (stk : Z) R M mdl Lc B C (ret n sp : Z),
    stk <= MSTK_M ->
    PHI Lc <= B -> Z.of_nat (length Lc) <= C -> VMLIM <= vm_limit (m_vmmaps mdl) ->
    getr R 1 = Z_to_bv 64 ret -> 1 <= n ->
    getr R 2 = Z_to_bv 64 sp -> CEIL + MSTK_M <= sp -> sp < 2 ^ 64 ->
    (forall a : word, sp - MSTK_M <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) ->
    (forall g, is_group st g -> lone st g) ->
    forall c', malloc_postkR st stk Lc n sp R M mdl (seg_rom RSEGS) c' -> malloc_ok AINV_R MSTK_M R M mdl Lc B C ret n sp c'.
  Proof using.
    intros st stk R M mdl Lc B C ret n sp Hstk HB HC HV H1 Hn E2 Hsplo Hsphi SOK LONE c' POST.
    destruct POST as (R' & M' & mdl' & p & st' & -> & CS & P10 & P16 & Plo & Phi & Pimg & NIL & APL & FR & DF & DFp & W' & RP' & LG' & NJ' & NL' & X1 & X2 & X3 & X4 & X5 & X6 & GK).
    unfold MSTK_M in *. ceil.
    destruct CS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    assert (PU : bv_unsigned (Z_to_bv 64 p) = p) by (rewrite u_Z2bv by (unfold HEAPLO in *; lia); reflexivity).
    unfold malloc_ok. rewrite H1. exists R', M', mdl', (Z_to_bv 64 p). rewrite ?PU.
    split; [reflexivity|].
    split.
    { intros r Hr. unfold callee_saved_regs in Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20
                                             | exact Q21 | exact Q22 | exact Q23 | exact Q24 | exact Q25 | exact Q26 | exact Q27] |]).
      destruct Hr. }
    split; [exact P10|]. split; [exact P16|].
    split; [unfold blk_ok; repeat split; try assumption; lia|].
    split; [exact APL|].
    split.
    { intros a Ha. rewrite (word_of_u a). pose proof (u64_range a) as AR.
      split; [apply DFp; lia|]. eapply (store_ok_of_defined1 M' p (p + n)); [exact DFp | unfold HEAPLO in *; lia | lia | lia]. }
    split.
    { intros a NE. pose proof (u64_range a) as AR. rewrite (word_of_u a) in NE.
      destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold mh_changed.
      - right; left. lia.
      - left. unfold in_blocks, app_of in *. exact A.
      - right; right; left. exact A.
      - right; right; right. exact A. }
    split.
    { intros a Ha. pose proof (u64_range a) as AR.
      destruct (Z.lt_ge_cases (bv_unsigned a) (sp - stk)) as [LO|HI].
      - assert (EQ : M' a = M a).
        { destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso. rewrite (word_of_u a) in NE.
          destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in *; lia. }
        pose proof (SOK a Ha) as S0. cbn [store_ok] in S0 |- *. unfold wview in S0 |- *. rewrite EQ. exact S0.
      - rewrite (word_of_u a). eapply (store_ok_of_defined1 M' (sp - stk) sp); [exact DF | lia | lia | lia]. }
    split.
    { split; [exists st'; split; [exact W'|]; split; [exact RP'|]; split; [exact LG'|]; split; [exact NJ'|]; split; [exact NL'|]|].
      - exact (lone_all_keep st st' GK LONE).
      - cbn [PHI length snd fst]. rewrite Nat2Z.inj_succ. split; [lia|]. split; [lia|]. rewrite X6. exact HV. }
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma malloc_exitFR : forall st (stk : Z) R M mdl Lc B C (ret sp : Z),
    stk <= MSTK_M ->
    PHI Lc <= B -> Z.of_nat (length Lc) <= C -> VMLIM <= vm_limit (m_vmmaps mdl) ->
    getr R 1 = Z_to_bv 64 ret ->
    getr R 2 = Z_to_bv 64 sp -> CEIL + MSTK_M <= sp -> sp < 2 ^ 64 ->
    (forall a : word, sp - MSTK_M <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) ->
    (forall g, is_group st g -> lone st g) ->
    forall c', malloc_failkR st stk Lc sp R M mdl (seg_rom RSEGS) c' -> malloc_null AINV_R MSTK_M R M mdl Lc B C ret sp c'.
  Proof using.
    intros st stk R M mdl Lc B C ret sp Hstk HB HC HV H1 E2 Hsplo Hsphi SOK LONE c' POST.
    destruct POST as (R' & M' & mdl' & st' & -> & CS & P10 & FR & DF & W' & RP' & LG' & NJ' & NL' & X1 & X2 & X3 & X4 & X5 & X6 & GK).
    unfold MSTK_M in *. ceil.
    destruct CS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    unfold malloc_null. rewrite H1. exists R', M', mdl'.
    split; [reflexivity|].
    split.
    { intros r Hr. unfold callee_saved_regs in Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20
                                             | exact Q21 | exact Q22 | exact Q23 | exact Q24 | exact Q25 | exact Q26 | exact Q27] |]).
      destruct Hr. }
    split; [exact P10|].
    split.
    { intros a NE. pose proof (u64_range a) as AR. rewrite (word_of_u a) in NE.
      destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold mh_changed.
      - right; left. lia.
      - left. unfold in_blocks, app_of in *. exact A.
      - right; right; left. exact A.
      - right; right; right. exact A. }
    split.
    { intros a Ha. pose proof (u64_range a) as AR.
      destruct (Z.lt_ge_cases (bv_unsigned a) (sp - stk)) as [LO|HI].
      - assert (EQ : M' a = M a).
        { destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso. rewrite (word_of_u a) in NE.
          destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in *; lia. }
        pose proof (SOK a Ha) as S0. cbn [store_ok] in S0 |- *. unfold wview in S0 |- *. rewrite EQ. exact S0.
      - rewrite (word_of_u a). eapply (store_ok_of_defined1 M' (sp - stk) sp); [exact DF | lia | lia | lia]. }
    split.
    { split; [exists st'; split; [exact W'|]; split; [exact RP'|]; split; [exact LG'|]; split; [exact NJ'|]; split; [exact NL'|]|].
      - intros g Hg. exact (lone_gkeep st st' g (GK g Hg) (LONE g (proj1 (GK g Hg)))).
      - split; [exact HB|]. split; [exact HC|]. rewrite X6. exact HV. }
    repeat split; assumption.
  Qed.

  Theorem malloc_big_r3 : MALLOC_BIG_R MSTK_M.
  Proof using HAM.
    intros R M mdl Lc B C ret n sp BIG HA PRE F HL Hok Hf.
    pose proof HA as ((st & HWF & HREP & HLG & NJ & NL & LONE) & HBB & HCC & HV).
    destruct PRE as (Hh & Hlz & Hmat & H1 & Hret & Hret2 & H10 & Hn & H2 & Hsp16 & Hsplo & H4 & SOK & HB & HC).
    pose proof (u64_range (getr R 2)) as SPR. rewrite H2 in SPR.
    assert (E2 : getr R 2 = Z_to_bv 64 sp) by (apply bv_eq; rewrite u_Z2bv by lia; exact H2).
    pose proof (u64_range (getr R 10)) as NR. rewrite H10 in NR.
    assert (E10 : getr R 10 = Z_to_bv 64 n) by (apply bv_eq; rewrite u_Z2bv by lia; exact H10).
    assert (Hra : ret_ok (getr R 1)) by (rewrite H1; apply ret_ok_even; rewrite u_Z2bv by lia; exact Hret2).
    pose proof Hsplo as Hsplo'. unfold MSTK_M in Hsplo'. ceil. unfold MH_GBUDGET in HB. unfold VMLIM, MH_GBUDGET in HV.
    pose proof (PHI_nonneg Lc ltac:(intros b Hb; destruct b as [b1 b2]; cbn; destruct (live_zone st Lc HWF b1 b2 Hb) as (_ & _ & X); exact (proj1 X))) as PH0.
    assert (DEF : defined M (sp - MSTK_M) sp).
    { apply (defined_of_store_ok M (sp - MSTK_M) sp); [unfold MSTK_M; lia | lia | right; unfold MSTK_M; lia |]. intros a Ha.
      pose proof (SOK (Z_to_bv 64 a)) as X. rewrite u_Z2bv in X by (unfold MSTK_M in *; lia). apply X. exact Ha. }
    unfold MSTK_M in DEF.
    pose proof (wL_len st Lc (WF_live st Lc HWF)) as LEN.
    unfold malloc_cfg, A_MALLOC. replace (Z_to_bv 64 418512) with (0x662d0%bv : word) by (apply bv_eq; reflexivity).
    apply (kfx_of_kat F HL true). apply malloc_thunk; [exact Hh | exact Hlz|].
    assert (J : junk_in st []) by (intros x k o Hx Hk E; exfalso; exact (NJ x k o Hx Hk E)).
    pose proof (regions_room st Lc [] HWF J ltac:(cbn; lia)) as HCR.
    pose proof (areas_room st Lc [] HWF J ltac:(cbn; lia) ltac:(rewrite NL; cbn; lia)) as HCA.
    pose proof (rsum_MBASE st Lc [] HWF J ltac:(cbn; lia) ltac:(rewrite NL; cbn; lia)
                  ltac:(intros m off Hm _; exact (NJ m 0 off Hm ltac:(pose proof (glast_rng st m); lia)))) as RS.
    apply (malloc_big_kfx st Lc M mdl R (seg_rom RSEGS) n sp F true HL HAM HWF HREP HLG NJ NL Hh Hlz Hmat HCR HCA
             ltac:(unfold MBASE, MBLK in *; lia) ltac:(lia) ltac:(unfold MMAP_THRESHOLD, MBLK in *; lia) E10 Hra E2 H4
             ltac:(unfold BSTK; lia) ltac:(intros y Hy; apply DEF; unfold BSTK in Hy; lia)).
    - intros c' P'. apply Hok. exact (malloc_exitR st BSTK R M mdl Lc B C ret n sp ltac:(unfold BSTK, MSTK_M; lia) HBB HCC
                            ltac:(unfold VMLIM, MH_GBUDGET; exact HV) H1 ltac:(lia) E2 Hsplo ltac:(lia) SOK LONE c' P').
    - intros c' P'. apply Hf. exact (malloc_exitFR st BSTK R M mdl Lc B C ret sp ltac:(unfold BSTK, MSTK_M; lia) HBB HCC
                            ltac:(unfold VMLIM, MH_GBUDGET; exact HV) H1 E2 Hsplo ltac:(lia) SOK LONE c' P').
  Qed.
End Top.
End UbMhMallocTop3.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.glaze.binary_reflection.images Require Import Ubsan.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTake OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKM OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.SumWalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.MallocDefs OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnframeBase OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKN.UbMhEnframe OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFreeA.UbMhGetMeta OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhDefs OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhInv OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhFrame OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhOpen OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhExt OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhList OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhRepT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaN.UbMhNtfLib OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2.UbMhNest OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNest2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhRotate.UbMhCover OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMmapK.UbMhAcct OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhUnmap OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhNtf2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAInv OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount.UbMhCountSpec OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhCount OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhBudget OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhCtz OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTac.UbMhBits OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhSzc OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhTake OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhEnfr OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhEfh OSSVerify.Proofs.glaze.binary_reflection.lib.MhKXSys.MhKX OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3.UbMhSpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhAMetaS.UbMhMSpec3 UbMhMSpecI OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA.UbMhASpec3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK.UbMhMallocW OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhMallocH OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocH2.UbMhASlotW1 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5.UbMhASlotW4 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotW5 OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKA OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKF OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotK.UbMhASlotKG OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKM OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotKN OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhASlotK OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK.UbMhMallocKT OSSVerify.Proofs.glaze.binary_reflection.lib.UbMhMallocK UbMhMallocTop3 UbMhImgR0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.UbCodeM1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Ltac inCS := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma sc44 : size_to_class 65536 = 44. Proof. vm_compute. reflexivity. Qed.
Lemma scl44 : size_class 44 = 4680. Proof. vm_compute. reflexivity. Qed.
Lemma gsel44 : gsel 44 4680 0 = 7. Proof. vm_compute. reflexivity. Qed.
Lemma g4cnt44 : g4cnt 74880 7 = 7. Proof. reflexivity. Qed.
Lemma mred44 : mred 44 74880 7 0 0 = 3. Proof. vm_compute. reflexivity. Qed.
Lemma m3_44 : m3 74880 3 65536 0 0 = (1, 69632). Proof. vm_compute. reflexivity. Qed.


Section R0.
  Context {RN : mh_run}.
  Context {fx : FPState}.
  Hypothesis HAMI : AM_INIT.

  (* [comment removed for export] *)
  Lemma malloc_thunk0 : forall regs (M : mem) rom mdl (Q : config -> Prop),
    m_halted mdl = None -> m_vm_lazy mdl = [] ->
    kat RSEGS (mkCfg (mkst regs (0x66f40%bv : word) M rom) mdl) Q ->
    kat RSEGS (mkCfg (mkst regs (0x662d0%bv : word) M rom) mdl) Q.
  Proof using.
    intros regs M rom mdl Q Hh Hl K.
    eapply kat_step; [exact Hh | exact Hl | reflexivity | exact (step_jal_x0 _ _ _ _ _ _ _ F_6627c eq_refl D_6627c) |].
    replace (btgt (0x662d0%bv : word) (bv_signed _)) with (0x66f40%bv : word) by (apply bv_eq; vm_compute; reflexivity).
    exact K.
  Qed.

  Lemma word_of_u0 : forall (a : word), a = Z_to_bv 64 (bv_unsigned a).
  Proof using. intros a. pose proof (u64_range a). apply bv_eq. rewrite u_Z2bv by lia. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma rdn_noneZ : forall (Mx : mem) a k bs, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
    (forall y, a <= y < a + Z.of_nat k -> Mx (Z_to_bv 64 y) = None) ->
    rdn RSEGS (fun _ => None) (Z_to_bv 64 a) k = Some bs ->
    rdn RSEGS Mx (Z_to_bv 64 a) k = Some bs.
  Proof using.
    intros Mx a k bs Ha Hk NONE IMG. rewrite (UbMhASlotKA.rdn_agreeZ (fun _ => None) Mx a k Ha Hk); [exact IMG|].
    intros y Hy. exact (NONE y Hy).
  Qed.

  (* [comment removed for export] *)
  Lemma first_env_frame : forall (M M' : mem) mdl auxw avl lo hi,
    first_env M mdl auxw avl -> env_above_sp auxw avl hi -> CTX_END <= lo -> 0 <= lo ->
    (forall y, 0 <= y < 2 ^ 64 -> M' (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> lo <= y < hi) ->
    first_env M' mdl auxw avl.
  Proof using.
    intros M M' mdl auxw avl lo hi FE [AUX RND] Hlo Hlo0 FR.
    destruct FE as [C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14].
    assert (AG : forall a k, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= lo \/ hi <= a) ->
                 rdn RSEGS M' (Z_to_bv 64 a) k = rdn RSEGS M (Z_to_bv 64 a) k).
    { intros a k Ha Hk OUT. apply (UbMhASlotKA.rdn_agreeZ M M' a k Ha Hk). intros y Hy.
      destruct (decide (M' (Z_to_bv 64 y) = M (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
      pose proof (FR y ltac:(lia) NE). lia. }
    assert (CELL : forall a k v, 0 <= a -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= lo \/ hi <= a) -> cell M a k v -> cell M' a k v).
    { intros a k v Ha Hk OUT C. unfold cell in *. rewrite (AG a k Ha Hk OUT). exact C. }
    constructor.
    - intros a Ha. destruct (decide (M' (Z_to_bv 64 a) = M (Z_to_bv 64 a))) as [E|NE]; [rewrite E; exact (C1 a Ha)|]. exfalso.
      pose proof (FR a ltac:(unfold MLOCK, CTX_END, CTX in *; lia) NE). unfold CTX_END, CTX, MLOCK in *. lia.
    - apply CELL; [unfold A_LIBC_AUXV; lia | unfold A_LIBC_AUXV; cbn; lia | left; unfold A_LIBC_AUXV, CTX_END, CTX in *; cbn; lia | exact C2].
    - exact C3.
    - intros i kv Hi. destruct (C4 i kv Hi) as (K1 & K2 & K3 & K4).
      assert (LEN : (i < length avl)%nat) by (apply (proj1 (nth_error_Some avl i)); rewrite Hi; discriminate).
      split; [|split; [|split; [exact K3 | exact K4]]].
      + apply CELL; [lia | cbn; nia | right; nia | exact K1].
      + apply CELL; [lia | cbn; nia | right; nia | exact K2].
    - apply CELL; [lia | cbn; lia | right; lia | exact C5].
    - intros kv Hin H25. destruct (C6 kv Hin H25) as (R1 & bs & Lbs & Rd). split; [exact R1|]. exists bs. split; [exact Lbs|].
      pose proof (RND kv Hin H25). rewrite (AG (snd kv + 8) 8%nat); [exact Rd | | cbn; lia | right; lia].
      destruct (In_nth_error _ _ Hin) as (i & Hi). destruct (C4 i kv Hi) as (_ & _ & _ & K4). lia.
    - apply CELL; [unfold A_PAGESIZE; lia | unfold A_PAGESIZE; cbn; lia | left; unfold A_PAGESIZE, CTX_END, CTX in *; cbn; lia | exact C7].
    - apply CELL; [unfold A_NEED_LOCKS; lia | unfold A_NEED_LOCKS; cbn; lia | left; unfold A_NEED_LOCKS, CTX_END, CTX in *; cbn; lia | exact C8].
    - destruct C9 as (v & C). exists v. apply CELL; [unfold A_CANARY; lia | unfold A_CANARY; cbn; lia | left; unfold A_CANARY, CTX_END, CTX in *; cbn; lia | exact C].
    - exact C10. - exact C11. - exact C12. - exact C13. - exact C14.
  Qed.

  Lemma first_img_frame : forall (M M' : mem) lo hi,
    first_img M -> CTX_END <= lo -> lo < 2 ^ 64 ->
    (forall y, 0 <= y < 2 ^ 64 -> M' (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> lo <= y < hi) ->
    first_img M'.
  Proof using.
    intros M M' lo hi [F1 F2 F3 F4] Hlo Hlo2 FR.
    assert (KEEP : forall a b, b <= lo -> 0 <= a -> img_clear M a b -> img_clear M' a b).
    { intros a b Hb Ha IC i Hi. destruct (decide (M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))) as [E|NE]; [rewrite E; exact (IC i Hi)|].
      exfalso. pose proof (FR i ltac:(lia) NE). lia. }
    constructor.
    - apply (KEEP A_ERRNO (A_ERRNO + 4)); [unfold A_ERRNO, TPV, CTX_END, CTX in *; lia | unfold A_ERRNO, TPV; lia | exact F1].
    - apply (KEEP A_GOT_CANARY (A_GOT_CANARY + 8)); [unfold A_GOT_CANARY, CTX_END, CTX in *; lia | unfold A_GOT_CANARY; lia | exact F2].
    - apply (KEEP A_TAB_CTZ (A_TAB_CTZ + 32)); [unfold A_TAB_CTZ, CTX_END, CTX in *; lia | unfold A_TAB_CTZ; lia | exact F3].
    - apply (KEEP A_TAB_SC (A_TAB_MED + 4)); [unfold A_TAB_SC, A_TAB_MED, CTX_END, CTX in *; lia | unfold A_TAB_SC; lia | exact F4].
  Qed.

  Lemma sz_of_fi : forall Mx, first_img Mx -> sz_img Mx.
  Proof using. intros Mx FIx i Hi. apply (fi_sc Mx FIx). unfold A_TAB_SC, A_TAB_MED. lia. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition MALLOC_FIRST_ALT3 (stk : Z) : Prop :=
    forall R M mdl ret n sp auxw avl,
      first_env M mdl auxw avl -> first_img M -> env_above_sp auxw avl sp ->
      malloc_pre stk R M mdl 0 0 ret n sp -> n = 65536 ->
      kats RSEGS (malloc_cfg R M mdl)
           (malloc_ok AINV_R stk R M mdl [] 0 0 ret n sp) (malloc_null AINV stk R M mdl [] 0 0 ret sp).

  (* [comment removed for export] *)
  Definition PXL (st' : mst) : Prop := forall x, is_group st' x -> lone st' x.

  Lemma malloc_exit0 : forall R M mdl (ret n sp : Z),
    VMLIM <= vm_limit (m_vmmaps mdl) ->
    getr R 1 = Z_to_bv 64 ret -> 1 <= n ->
    getr R 2 = Z_to_bv 64 sp -> CEIL + MSTK_M <= sp -> sp < 2 ^ 64 ->
    (forall a : word, sp - MSTK_M <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) ->
    forall c', malloc_postkX PXL SSTK [] n sp R M mdl (seg_rom RSEGS) c' -> malloc_ok AINV_R MSTK_M R M mdl [] 0 0 ret n sp c'.
  Proof using.
    intros R M mdl ret n sp HV H1 Hn E2 Hsplo Hsphi SOK c' POST.
    destruct POST as (R' & M' & mdl' & p & st' & -> & CS & P10 & P16 & Plo & Phi & Pimg & NIL & APL & FR & DF & DFp & W' & RP' & LG' & NJ' & NL' & X1 & X2 & X3 & X4 & X5 & X6 & PX').
    rewrite SSTK_val in *. unfold MSTK_M in *. ceil.
    destruct CS as (Q2 & Q3 & Q4 & Q8 & Q9 & Q18 & Q19 & Q20 & Q21 & Q22 & Q23 & Q24 & Q25 & Q26 & Q27).
    assert (PU : bv_unsigned (Z_to_bv 64 p) = p) by (rewrite u_Z2bv by (unfold HEAPLO in *; lia); reflexivity).
    unfold malloc_ok. rewrite H1. exists R', M', mdl', (Z_to_bv 64 p). rewrite ?PU.
    split; [reflexivity|].
    split.
    { intros r Hr. unfold callee_saved_regs in Hr. cbn in Hr.
      repeat (destruct Hr as [<-|Hr]; [first [exact Q2 | exact Q3 | exact Q4 | exact Q8 | exact Q9 | exact Q18 | exact Q19 | exact Q20
                                             | exact Q21 | exact Q22 | exact Q23 | exact Q24 | exact Q25 | exact Q26 | exact Q27] |]).
      destruct Hr. }
    split; [exact P10|]. split; [exact P16|].
    split; [unfold blk_ok; repeat split; try assumption; lia|].
    split; [exact APL|].
    split.
    { intros a Ha. rewrite (word_of_u0 a). pose proof (u64_range a) as AR.
      split; [apply DFp; lia|]. eapply (store_ok_of_defined1 M' p (p + n)); [exact DFp | unfold HEAPLO in *; lia | lia | lia]. }
    split.
    { intros a NE. pose proof (u64_range a) as AR. rewrite (word_of_u0 a) in NE.
      destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold mh_changed.
      - right; left. lia.
      - left. unfold in_blocks, app_of in *. exact A.
      - right; right; left. exact A.
      - right; right; right. exact A. }
    split.
    { intros a Ha. pose proof (u64_range a) as AR.
      destruct (Z.lt_ge_cases (bv_unsigned a) (sp - 1200)) as [LO|HI].
      - assert (EQ : M' a = M a).
        { destruct (decide (M' a = M a)) as [E|NE]; [exact E|]. exfalso. rewrite (word_of_u0 a) in NE.
          destruct (FR (bv_unsigned a) ltac:(lia) NE) as [A|[A|[A|A]]]; unfold HEAPLO, CTX_END, CTX, A_ERRNO, TPV in *; lia. }
        pose proof (SOK a Ha) as S0. cbn [store_ok] in S0 |- *. unfold wview in S0 |- *. rewrite EQ. exact S0.
      - rewrite (word_of_u0 a). eapply (store_ok_of_defined1 M' (sp - 1200) sp); [exact DF | lia | lia | lia]. }
    split.
    { split; [exists st'; split; [exact W'|]; split; [exact RP'|]; split; [exact LG'|]; split; [exact NJ'|]; split; [exact NL'| exact PX']|].
      cbn [PHI length snd fst Z.of_nat]. unfold MBLK. split; [lia|]. split; [lia|]. rewrite X6. exact HV. }
    repeat split; assumption.
  Qed.

  (* [comment removed for export] *)
  Lemma malloc_exitF0 : forall R M mdl (ret sp : Z),
    VMLIM <= vm_limit (m_vmmaps mdl) ->
    getr R 1 = Z_to_bv 64 ret ->
    getr R 2 = Z_to_bv 64 sp -> CEIL + MSTK_M <= sp -> sp < 2 ^ 64 ->
    (forall a : word, sp - MSTK_M <= bv_unsigned a < sp -> store_ok RSEGS M a 1%nat = true) ->
    forall c', malloc_failk SSTK [] sp R M mdl (seg_rom RSEGS) c' -> malloc_null AINV MSTK_M R M mdl [] 0 0 ret sp c'.
  Proof using.
    intros R M mdl ret sp HV H1 E2 Hsplo Hsphi SOK c' POST.
    exact (UbMhMallocTop3.malloc_exitF SSTK R M mdl [] 0 0 ret sp ltac:(rewrite SSTK_val; unfold MSTK_M; lia) ltac:(cbn; lia) ltac:(cbn; lia) HV H1 E2 Hsplo Hsphi SOK c' POST).
  Qed.

  Theorem malloc_first_alt3 : MALLOC_FIRST_ALT3 MSTK_M.
  Proof using HAMI.
    intros R M mdl ret n sp auxw avl FE FI ENV PRE En F HL Hok Hf. subst n.
    destruct PRE as (Hh & Hlz & Hmat & H1 & Hret & Hret2 & H10 & Hn & H2 & Hsp16 & Hsplo & H4 & SOK & HB & HC).
    pose proof FE as [Cctx Cauxv Cavr Cavk Cave Carnd Cpg Clk Ccan Cmaps Cbrk Cres Ctop Clim].
    pose proof (u64_range (getr R 2)) as SPR. rewrite H2 in SPR.
    assert (E2 : getr R 2 = Z_to_bv 64 sp) by (apply bv_eq; rewrite u_Z2bv by lia; exact H2).
    assert (E10 : getr R 10 = Z_to_bv 64 65536) by (apply bv_eq; rewrite u_Z2bv by lia; exact H10).
    assert (Hra : ret_ok (getr R 1)) by (rewrite H1; apply ret_ok_even; rewrite u_Z2bv by lia; exact Hret2).
    pose proof Hsplo as Hsplo'. unfold MSTK_M in Hsplo'. ceil.
    assert (DEF : defined M (sp - MSTK_M) sp).
    { apply (defined_of_store_ok M (sp - MSTK_M) sp); [unfold MSTK_M; lia | lia | right; unfold MSTK_M; lia |]. intros a Ha.
      pose proof (SOK (Z_to_bv 64 a)) as X. rewrite u_Z2bv in X by (unfold MSTK_M in *; lia). apply X. exact Ha. }
    unfold MSTK_M in DEF.
    unfold malloc_cfg, A_MALLOC. replace (Z_to_bv 64 418512) with (0x662d0%bv : word) by (apply bv_eq; reflexivity).
    apply (kfx_of_kat F HL true). apply malloc_thunk0; [exact Hh | exact Hlz|].
    (* [comment removed for export] *)
    assert (SOK48 : store_ok RSEGS M (Z_to_bv 64 (sp - 48)) 48%nat = true).
    { eapply (store_ok_defined M (sp - 1280) sp); [exact DEF | lia | cbn; lia | lia | lia]. }
    destruct (mPro M sp 65536 ltac:(ceil; lia) ltac:(lia) SOK48 R (seg_rom RSEGS) E2 E10) as (r1 & RUN1 & A2 & A8 & A9 & A10 & K1).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN1 |].
    change (mal_frame M sp (getr R 1) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20)) with (UbMhMallocK.M1 M R sp).
    set (M1 := UbMhMallocK.M1 M R sp) in *.
    assert (HspS : CEIL + SSTK <= sp /\ sp < 2 ^ 64) by (rewrite SSTK_val; lia).
    assert (M1W : forall y, 0 <= y < 2 ^ 64 -> M1 (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> sp - 48 <= y < sp)
      by (intros y Hy NE; exact (UbMhMallocK.M1_writes [] M R sp HspS y Hy NE)).
    assert (G1 : mem_grows M M1) by (exact (UbMhMallocK.M1_grows M R sp)).
    assert (DF1 : defined M1 (sp - 1280) sp) by (eapply defined_grows; [exact G1 | exact DEF]).
    assert (FE1 : first_env M1 mdl auxw avl).
    { apply (first_env_frame M M1 mdl auxw avl (sp - 48) sp FE); [apply (env_above_sp_mono auxw avl sp); [lia | exact ENV] | unfold CTX_END, CTX; lia | lia | exact M1W]. }
    assert (FI1 : first_img M1) by (apply (first_img_frame M M1 (sp - 48) sp FI); [unfold CTX_END, CTX; lia | lia | exact M1W]).
    (* [comment removed for export] *)
    destruct (mSzcB M1 65536 ltac:(unfold MMAP_THRESHOLD; lia) (fi_ctz M1 FI1) (sz_of_fi M1 FI1) r1 (seg_rom RSEGS) A8 A10 ltac:(lia)) as (r2 & RUN2 & B20 & B19 & K2).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN2 |]. rewrite sc44 in B20.
    (* [comment removed for export] *)
    assert (NL1 : rdn RSEGS M1 (Z_to_bv 64 A_NEED_LOCKS) 1%nat = Some [Z_to_bv 8 0]).
    { apply (cell1_rdn M1 A_NEED_LOCKS 0 ltac:(lia)). exact (fe_locks M1 mdl auxw avl FE1). }
    destruct (mLck M1 NL1 r2 (seg_rom RSEGS)) as (r3 & RUN3 & K3).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN3 |].
    (* [comment removed for export] *)
    assert (CTXZ : forall y, MLOCK <= y < CTX_END -> M1 (Z_to_bv 64 y) = None) by (intros y Hy; exact (fe_ctx M1 mdl auxw avl FE1 y Hy)).
    assert (ACT1 : rdn RSEGS M1 (Z_to_bv 64 (ctx_active 44)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { apply rdn_noneZ; [unfold ctx_active, CTX; lia | unfold ctx_active, CTX; cbn; lia | | exact img_8b078_8].
      intros y Hy. apply CTXZ. unfold ctx_active, CTX_END, MLOCK, CTX in *. cbn in Hy. lia. }
    assert (USE1 : rdn RSEGS M1 (Z_to_bv 64 (ctx_usage 44)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { apply rdn_noneZ; [unfold ctx_usage, CTX; lia | unfold ctx_usage, CTX; cbn; lia | | exact img_8b1f8_8].
      intros y Hy. apply CTXZ. unfold ctx_usage, CTX_END, MLOCK, CTX in *. cbn in Hy. lia. }
    destruct (mClsZ M1 44 0 0 ltac:(lia) ltac:(lia) ACT1 USE1 eq_refl ltac:(right; right; left; lia) r3 (seg_rom RSEGS)
                ltac:(kept_rw K3; exact B20) ltac:(kept_rw K3; kept_rw K2; exact A9)) as (r4 & RUN4 & C18 & C10 & C20 & K4).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN4 |].
    assert (C8 : getr r4 8 = Z_to_bv 64 65536) by (kept_rw K4; kept_rw K3; kept_rw K2; exact A8).
    assert (C9 : getr r4 9 = Z_to_bv 64 MLOCK) by (kept_rw K4; kept_rw K3; kept_rw K2; exact A9).
    assert (C2 : getr r4 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K4; kept_rw K3; kept_rw K2; exact A2).
    assert (K14 : keeps_but (AS_CLOB ++ [1; 2; 8; 9; 18; 19; 20]%bv) R r4).
    { eapply keeps_but_trans; [eapply keeps_but_mono; [exact K1|]|]. 1: intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
      eapply keeps_but_trans; [eapply keeps_but_mono; [exact K2|]|]. 1: intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
      eapply keeps_but_trans; [eapply keeps_but_mono; [exact K3|]|]. 1: intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
      eapply keeps_but_mono; [exact K4|]. intros r Hr; apply in_regs_dec; revert r Hr; apply (proj1 (forallb_forall _ _)); reflexivity. }
    (* [comment removed for export] *)
    destruct (mMsk0 M1 44 65536 ltac:(lia) r4 (seg_rom RSEGS) C10 C20 C8) as (r5 & RUN5 & D10 & D11 & D18 & D1 & K5).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN5 |].
    assert (D2 : getr r5 2 = Z_to_bv 64 (sp - 48)) by (kept_rw K5; exact C2).
    assert (D4 : getr r5 4 = Z_to_bv 64 TPV) by (kept_rw K5; kept_rw K14; exact H4).
    assert (D9 : getr r5 9 = Z_to_bv 64 MLOCK) by (kept_rw K5; exact C9).
    assert (Dra : ret_ok (getr r5 1)) by (rewrite D1; apply ret_ok_even; reflexivity).
    (* [comment removed for export] *)
    set (spA := sp - 48) in *.
    assert (HspA : CEIL + ASSTK 0 <= spA /\ spA < 2 ^ 64) by (unfold ASSTK, AMSTK; cbn; lia).
    assert (SOK144 : store_ok RSEGS M1 (Z_to_bv 64 (spA - 144)) 144%nat = true).
    { eapply (store_ok_defined M1 (sp - 1280) sp); [exact DF1 | lia | cbn; lia | lia | lia]. }
    destruct (fe_canary M1 mdl auxw avl FE1) as (can0 & CAN1).
    assert (GOT1 : rdn RSEGS M1 (Z_to_bv 64 A_GOT_CANARY) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 A_CANARY))).
    { apply rdn_noneZ; [unfold A_GOT_CANARY; lia | unfold A_GOT_CANARY; cbn; lia | | exact img_78d10_8].
      intros y Hy. apply (fi_got M1 FI1). cbn in Hy. lia. }
    destruct (aPro M1 spA 44 65536 can0 ltac:(lia) ltac:(lia) SOK144 GOT1 CAN1 r5 (seg_rom RSEGS) D2 D10 D11)
      as (r6 & RUN6 & E2' & E8 & E18 & E20 & E10' & E22 & E23 & K6).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN6 |].
    change (as_frame M1 spA can0 (getr r5 1) (getr r5 8) (getr r5 9) (getr r5 18) (getr r5 19) (getr r5 20)
                        (getr r5 21) (getr r5 22) (getr r5 23) (getr r5 24) (getr r5 25)) with (UbMhASlotKA.M1 (st_pristine can0 0) M1 r5 spA).
    set (M2 := UbMhASlotKA.M1 (st_pristine can0 0) M1 r5 spA) in *.
    assert (M2W : forall y, 0 <= y < 2 ^ 64 -> M2 (Z_to_bv 64 y) <> M1 (Z_to_bv 64 y) -> spA - 96 <= y < spA)
      by (intros y Hy NE; exact (UbMhASlotKA.M1_writes (st_pristine can0 0) M1 r5 spA 0%nat HspA y Hy NE)).
    assert (G2 : mem_grows M1 M2) by (exact (UbMhASlotKA.M1_grows (st_pristine can0 0) M1 r5 spA)).
    pose proof (UbMhASlotKA.M1_stk (st_pristine can0 0) M1 r5 spA 0%nat HspA) as STK2. fold M2 in STK2.
    assert (M2W' : forall y, 0 <= y < 2 ^ 64 -> M2 (Z_to_bv 64 y) <> M (Z_to_bv 64 y) -> sp - 144 <= y < sp).
    { intros y Hy NE. destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE2].
      - rewrite E in NE. pose proof (M1W y Hy NE). lia.
      - pose proof (M2W y Hy NE2). lia. }
    assert (FE2 : first_env M2 mdl auxw avl).
    { apply (first_env_frame M M2 mdl auxw avl (sp - 144) sp FE); [apply (env_above_sp_mono auxw avl sp); [lia | exact ENV] | unfold CTX_END, CTX; lia | lia | exact M2W']. }
    assert (FI2 : first_img M2) by (apply (first_img_frame M M2 (sp - 144) sp FI); [unfold CTX_END, CTX; lia | lia | exact M2W']).
    (* [comment removed for export] *)
    assert (ACT2 : rdn RSEGS M2 (Z_to_bv 64 (ctx_active 44)) 8%nat = Some (word_to_le_bytes 8 (Z_to_bv 64 0))).
    { apply rdn_noneZ; [unfold ctx_active, CTX; lia | unfold ctx_active, CTX; cbn; lia | | exact img_8b078_8].
      intros y Hy. apply (fe_ctx M2 mdl auxw avl FE2). unfold ctx_active, CTX_END, MLOCK, CTX in *. cbn in Hy. lia. }
    destruct (aHead0 M2 44 0 ltac:(lia) ltac:(lia) ACT2 r6 (seg_rom RSEGS) E23 eq_refl) as (r7 & RUN7 & F21 & F12 & K7).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN7 |].
    (* [comment removed for export] *)
    destruct (aMeta M2 44 ltac:(lia) (sz_of_fi M2 FI2) r7 (seg_rom RSEGS) ltac:(kept_rw K7; exact E8)) as (r8 & RUN8 & G19 & G25 & G24 & G1r & K8).
    eapply kat_msteps; [exact Hh | exact Hlz | exact RUN8 |].
    set (spM := spA - 144) in *.
    assert (R8_2 : getr r8 2 = Z_to_bv 64 spM) by (kept_rw K8; kept_rw K7; exact E2').
    assert (R8_4 : getr r8 4 = Z_to_bv 64 TPV) by (kept_rw K8; kept_rw K7; kept_rw K6; exact D4).
    assert (DEFm : defined M2 (spM - AMSTK) spM).
    { intros y Hy. apply G2. apply DF1. unfold AMSTK, spM, spA in *. lia. }
    (* [comment removed for export] *)
    assert (Clim' : VMLIM <= vm_limit (m_vmmaps mdl)) by exact Clim.
    assert (Hsc44 : 0 <= 44 < 48) by lia.
    assert (Hreq44 : 0 <= 65536 /\ 65536 + 4 <= 16 * size_class 44) by (rewrite scl44; lia).
    assert (K6big : keeps_but BIG r5 r6).
    { eapply keeps_but_mono; [exact K6|]. intros r Hr. apply in_regs_dec.
      cbn in Hr. destruct Hr as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]; reflexivity. }
    assert (K58 : keeps_but BIG r5 r8).
    { eapply keeps_big; [eapply keeps_big; [exact K6big | exact K7 | reflexivity] | exact K8 | reflexivity]. }
    assert (STKM : forall dd v, 8 <= dd <= 48 -> rdn RSEGS M1 (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v) ->
                  forall Mx : mem, (forall y, sp - 48 <= y < sp -> Mx (Z_to_bv 64 y) = M1 (Z_to_bv 64 y)) ->
                  rdn RSEGS Mx (Z_to_bv 64 (sp - dd)) 8%nat = Some (word_to_le_bytes 8 v)).
    { intros dd v Hd Rd Mx AG. rewrite (UbMhASlotKA.rdn_agreeZ M1 Mx (sp - dd) 8 ltac:(lia) ltac:(cbn; lia)); [exact Rd|]. intros y Hy. apply AG. cbn in Hy. lia. }
    (* [comment removed for export] *)
    assert (FAILT : forall stX, s_limbo stX = [] -> forall c',
                    as_fail stX [] 44 0%nat spA r5 M1 mdl (seg_rom RSEGS) c' -> Kf F c').
    { intros stX ELX c' PF.
      destruct PF as (s3 & M3 & mdl3 & r6' & -> & W3 & RP3 & LG3 & Hh3 & Hlz3 & Hmat3 & Hfs3 & Hfds3 & Hlim3 & NJ3 & EL3 & Hcan3 &
                      LM3 & MU3 & F10 & F2 & K6' & FRM3 & DEF3).
      rewrite D1. replace (Z_to_bv 64 422480) with (0x67250%bv : word) by (apply bv_eq; reflexivity).
      apply (kf_of_kat F HL).
      assert (STK3 : forall y, sp - 48 <= y < sp -> M3 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y)).
      { intros y Hy. destruct (decide (M3 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE3]; [exact E|]. exfalso.
        destruct (FRM3 y ltac:(lia) NE3) as [A|[A|[A|A]]];
          [unfold ASSTK, AMSTK, spA in A; lia | ceil; unfold HEAPLO in A; lia | unfold CTX_END, CTX in A; lia | unfold A_ERRNO, TPV in A; lia]. }
      pose proof (rc_lock s3 M3 (rp_statics s3 M3 RP3)) as Mlk.
      destruct (tM1 M3 sp (getr R 1) (getr R 8) (getr R 9) (getr R 18) (getr R 19) (getr R 20) ltac:(ceil; lia) Hra
                  (STKM 8 _ ltac:(lia) ltac:(subst M1; unfold UbMhMallocK.M1, mal_frame; rdn_solve) M3 STK3)
                  (STKM 16 _ ltac:(lia) ltac:(subst M1; unfold UbMhMallocK.M1, mal_frame; rdn_solve) M3 STK3)
                  (STKM 24 _ ltac:(lia) ltac:(subst M1; unfold UbMhMallocK.M1, mal_frame; rdn_solve) M3 STK3)
                  (STKM 32 _ ltac:(lia) ltac:(subst M1; unfold UbMhMallocK.M1, mal_frame; rdn_solve) M3 STK3)
                  (STKM 40 _ ltac:(lia) ltac:(subst M1; unfold UbMhMallocK.M1, mal_frame; rdn_solve) M3 STK3)
                  (STKM 48 _ ltac:(lia) ltac:(subst M1; unfold UbMhMallocK.M1, mal_frame; rdn_solve) M3 STK3)
                  Mlk r6' (seg_rom RSEGS) ltac:(rewrite F2; exact D2) F10)
        as (r7' & RUN7' & E2x & E10x & E1x & E8x & E9x & E18x & E19x & E20x & K7').
      eapply kat_msteps; [exact Hh3 | exact Hlz3 | exact RUN7' |].
      apply kat_refl. apply Hf. apply (malloc_exitF0 R M mdl ret sp Clim' H1 E2 Hsplo ltac:(lia) SOK). unfold malloc_failk.
      exists r7', M3, mdl3, s3.
      split; [reflexivity|].
      split.
      { unfold cs_same. rewrite E2x, E8x, E9x, E18x, E19x, E20x, E2. repeat split; try reflexivity.
        all: kept_rw K7'; kept_rw K6'; kept_rw K5; kept_rw K14; reflexivity. }
      split; [exact E10x|].
      split.
      { intros a Ha NE. destruct (decide (M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E|NE3].
        - rewrite E in NE. left. pose proof (M1W a Ha NE). rewrite SSTK_val. lia.
        - destruct (FRM3 a Ha NE3) as [A|[A|[A|A]]]; [left; rewrite SSTK_val; unfold ASSTK, AMSTK, spA in A; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A]. }
      split.
      { intros y Hy. rewrite SSTK_val in Hy. destruct (decide (M3 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE3].
        - rewrite E. apply DF1. lia.
        - destruct (FRM3 y ltac:(lia) NE3) as [A|[A|[A|A]]]; [apply DEF3; exact A | exfalso; ceil; unfold HEAPLO in A; lia | exfalso; unfold CTX_END, CTX in A; lia | exfalso; unfold A_ERRNO, TPV in A; lia]. }
      split; [exact W3|]. split; [exact RP3|]. split; [exact LG3|]. split; [exact NJ3|]. split; [unfold nolimbo; rewrite EL3; exact ELX|].
      split; [exact Hh3|]. split; [exact Hlz3|]. split; [exact Hmat3|]. split; [exact Hfs3|]. split; [exact Hfds3|]. exact Hlim3. }
    (* [comment removed for export] *)
    assert (CANX : forall (Mx : mem) (sX : mst) (canX : Z),
              REP sX Mx -> s_canary sX = canX ->
              (forall y, A_CANARY <= y < A_CANARY + 8 -> Mx (Z_to_bv 64 y) = M1 (Z_to_bv 64 y)) ->
              Some (word_to_le_bytes 8 (Z_to_bv 64 canX)) = Some (word_to_le_bytes 8 (Z_to_bv 64 can0))).
    { intros Mx sX canX RPX EC AG. pose proof (rc_canary sX Mx (rp_statics sX Mx RPX)) as X. rewrite EC in X. unfold cell in X.
      rewrite (UbMhASlotKA.rdn_agreeZ M1 Mx A_CANARY 8 ltac:(unfold A_CANARY; lia) ltac:(unfold A_CANARY; cbn; lia)) in X.
      - unfold cell in CAN1. rewrite <- X. exact CAN1.
      - intros y Hy. apply AG. cbn in Hy. lia. }
    (* [comment removed for export] *)
    apply (kat_of_kfx F true). replace (0x66c68%bv : word) with (Z_to_bv 64 AM_ENTRY) by (apply bv_eq; reflexivity).
    apply (HAMI F true true M2 mdl r8 (seg_rom RSEGS) spM auxw avl HL (fun E => E) FE2 FI2
             (env_above_sp_mono auxw avl sp spM ltac:(unfold spM, spA; lia) ENV) Hh Hlz Hmat R8_2
             ltac:(rewrite G1r; apply ret_ok_even; reflexivity) ltac:(unfold AMSTK, spM, spA; lia) ltac:(unfold spM, spA; lia) R8_4 DEFm).
    - (* [comment removed for export] *)
      intros can sec c' POST.
      destruct POST as (s2 & Mo & mdl2 & r9 & m & -> & W2 & RP2 & LG2 & Hh2 & Hlz2 & Hmat2 & Hfs2 & Hfds2 & Hvl2 &
                        Elim & Um & Zm & NLm2 & Efl & Eerr & KEEP & REG & F10 & F2 & K9 & MoW & DEFo).
      destruct KEEP as (Egrp & Eslot & Ealist & Eai & Ekind & Ecan & Eact & Eus & Ebn & Euq & Esq & Ectr & Esec & Emg & Elm2 & MU2).
      rewrite G1r. replace (Z_to_bv 64 423080) with (0x674a8%bv : word) by (apply bv_eq; reflexivity).
      apply (kfx_of_kat F HL true).
      set (ST0 := st_pristine can sec) in *.
      (* [comment removed for export] *)
      assert (NG2 : forall x, ~ is_group s2 x) by (intros x Hx; unfold is_group in Hx; rewrite Egrp in Hx; cbn in Hx; exact Hx).
      assert (NJ2 : nojunk s2) by (intros x k o Hx; exfalso; exact (NG2 x Hx)).
      assert (AGF2 : agf s2) by (intros x Hx; exfalso; exact (NG2 x Hx)).
      assert (U0 : c_usage (s_ctx s2) = fun _ => 0) by (rewrite Eus; reflexivity).
      assert (RGo : forall rr, In rr (s_regions s2) -> HEAPLO <= rg_base rr /\ rg_base rr + rg_len rr <= CEIL).
      { intros rr Hrr. pose proof (wr_rng s2 (WF_regions s2 [] W2) rr Hrr). lia. }
      assert (MoM2 : forall y, 0 <= y < 2 ^ 64 -> (spA - 96 <= y < spA \/ A_CANARY <= y < A_CANARY + 8) -> Mo (Z_to_bv 64 y) = M2 (Z_to_bv 64 y)).
      { intros y Hy RG. destruct (decide (Mo (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
        destruct (MoW y Hy NE) as [[A|[A|[A|(rr & Hrr & NK & A)]]]|HOLE];
          [unfold AMSTK, spM, spA in *; unfold A_CANARY in RG; ceil; lia | unfold CTX_END, CTX, A_CANARY in *; ceil; lia
          | unfold A_ERRNO, TPV, A_CANARY in *; ceil; lia | pose proof (RGo rr Hrr); unfold A_CANARY in RG; ceil; lia
          | destruct (am_holeR_rng _ _ _ HOLE) as [B1 B2]; unfold A_CANARY in RG; ceil; lia]. }
      pose proof (CANX Mo s2 can RP2 ltac:(rewrite Ecan; reflexivity)
                    ltac:(intros y Hy; rewrite (MoM2 y ltac:(unfold A_CANARY in Hy; lia) (or_intror Hy));
                          destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE]; [exact E|]; exfalso;
                          pose proof (M2W y ltac:(unfold A_CANARY in Hy; lia) NE); unfold A_CANARY in Hy; ceil; lia)) as CANEQ.
      assert (STKo : UbMhASlotKA.stk_ok ST0 r5 spA Mo).
      { apply (UbMhASlotKA.stk_transfer ST0 r5 spA 44 65536 0%nat Hsc44 Hreq44 HspA M2 Mo); [intros y Hy; apply MoM2; [ceil; lia | left; exact Hy]|].
        unfold UbMhASlotKA.stk_ok in STK2 |- *. cbn [UbMhASlotKA.can s_canary st_pristine ST0] in STK2 |- *. rewrite CANEQ. exact STK2. }
      (* [comment removed for export] *)
      assert (P2 : UbMhASlotKA.pt ST0 [] M1 mdl r5 spA 44 0%nat s2 Mo mdl2 r9).
      { constructor.
        + exact W2. + exact RP2. + apply (proj2 (LEDGERX_nil s2 _)); exact LG2.
        + exact Hh2. + exact Hlz2. + exact Hmat2. + exact Hfs2. + exact Hfds2. + exact Hvl2.
        + exact Ecan.
        + exact Eerr.
        + intros k Hk. rewrite Ealist. reflexivity.
        + intros x Hx. cbn in Hx. destruct Hx.
        + exact MU2.
        + intros a Ha NE. destruct (decide (Mo (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))) as [E|NE9].
          * rewrite E in NE. left. pose proof (M2W a Ha NE). unfold ASSTK, AMSTK. lia.
          * destruct (MoW a Ha NE9) as [[A|[A|[A|(rr & Hrr & NK & A)]]]|HOLE].
            -- left. unfold ASSTK, AMSTK, spM, spA in *. lia.
            -- right; right; left. exact A.
            -- right; right; right. exact A.
            -- right; left. exact (UbMhASlotKA.nongroup_nonapp [] 0%nat s2 rr a W2 Hrr NK A).
            -- right; left. exact (am_holeR_nonapp s2 [] [] a W2 HOLE).
        + intros y Hy. destruct (decide (Mo (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E|NE9]; [rewrite E; apply G2; apply DF1; unfold ASSTK, AMSTK, spA in Hy; lia|].
          destruct (MoW y ltac:(ceil; lia) NE9) as [[A|[A|[A|(rr & Hrr & NK & A)]]]|HOLE];
            [apply DEFo; exact A | exfalso; ceil; unfold CTX_END, CTX in *; lia | exfalso; ceil; unfold A_ERRNO, TPV in *; lia
            | exfalso; destruct (UbMhASlotKA.nongroup_nonapp [] 0%nat s2 rr y W2 Hrr NK A) as [B _]; ceil; lia
            | exfalso; destruct (am_holeR_rng _ _ _ HOLE) as [B _]; ceil; lia].
        + exact STKo.
        + rewrite F2. exact R8_2.
        + kept_rw K9. kept_rw K8. kept_rw K7. exact E8.
        + kept_rw K9. kept_rw K8. kept_rw K7. exact E20.
        + kept_rw K9. kept_rw K8. exact F21.
        + kept_rw K9. kept_rw K8. kept_rw K7. exact E22.
        + kept_rw K9. kept_rw K8. kept_rw K7. exact E23.
        + eapply keeps_big; [exact K58 | exact K9 | reflexivity]. }
      (* [comment removed for export] *)
      assert (GCNT : UbMhASlotK.UbMhASlotKG.gcnt 44 s2 = 7).
      { unfold UbMhASlotK.UbMhASlotKG.gcnt. rewrite U0, scl44. change (16 * 4680) with 74880. cbn beta. rewrite gsel44. exact g4cnt44. }
      assert (ECN : UbMhASlotKM.cn_of 44 65536 s2 7 = (1, 69632)).
      { unfold UbMhASlotKM.cn_of, UbMhASlotKM.nosm_of. rewrite U0, scl44. cbn beta. change (16 * 4680) with 74880.
        change ((7 <=? 44) && (44 <=? 38))%bool with false. cbn iota.
        replace (ucoarse 44 0 0) with 0 by (vm_compute; reflexivity). rewrite mred44. exact m3_44. }
      (* [comment removed for export] *)
      assert (HOK0 : forall c'', malloc_postkX PXL SSTK [] 65536 sp R M mdl (seg_rom RSEGS) c'' -> Kok F c'').
      { intros c'' P'. apply Hok. exact (malloc_exit0 R M mdl ret 65536 sp Clim' H1 ltac:(lia) E2 Hsplo ltac:(lia) SOK c'' P'). }
      assert (ECONT : forall s1 Mc mdl1 r g idx,
        UbMhASlotKA.ptE ST0 [] M1 mdl r5 spA 44 0%nat s1 Mc mdl1 r -> UbMhASlotKM.xnew 44 65536 s2 (UbMhASlotK.UbMhASlotKG.gcnt 44 s2) s1 g ->
        s_limbo s1 = s_limbo ST0 ->
        head_of (s_alist s1 44) = g -> is_group s1 g -> g_sc s1 g = 44 -> 0 <= idx <= g_lastidx s1 g ->
        s_slot s1 g idx = SJunk 0 -> only_junk s1 g idx -> 65536 + 4 <= g_stride s1 g -> (16 * size_class 44 <= g_stride s1 g \/ 4080 <= g_stride s1 g) ->
        getr r 10 = Z_to_bv 64 idx ->
        kat RSEGS (mkCfg (mkst r (0x67b10%bv : word) Mc (seg_rom RSEGS)) mdl1) (kfx F false)).
      { intros s1 Mc mdl1 r g idx PE XN EL1 Hhd Hg Hgsc Hidx Hsl OJ Hstr Hbig B10.
        pose proof PE as [W1' RP1' LG1' Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hcan1 Herr1 BL1 LM1 MU1 FR1 DFE SK1 Q2 Q20 KB1].
        rewrite GCNT in XN. destruct XN as (XK & XS & XL & XM & XG). rewrite ECN in XL, XM. cbn [fst snd] in XL, XM.
        assert (ML17 : g_maplen s1 g = 17) by lia.
        assert (GL0 : g_lastidx s1 g = 0) by lia.
        assert (I0 : idx = 0) by lia.
        assert (ONLY : forall x, is_group s1 x -> x = g).
        { intros x Hx. destruct (proj1 (XG x) Hx) as [E|Hx2]; [exact E | exfalso; exact (NG2 x Hx2)]. }
        (* [comment removed for export] *)
        pose proof SK1 as SK1'. unfold UbMhASlotKA.stk_ok in SK1'. cbn [UbMhASlotKA.can s_canary st_pristine ST0] in SK1'.
        destruct SK1' as (Kc & K1' & K8' & K9' & K18' & K19' & K20' & K21' & K22' & K23' & K24' & K25').
        pose proof (rc_canary s1 Mc (rp_statics s1 Mc RP1')) as CAN. rewrite Hcan1 in CAN. cbn [s_canary st_pristine ST0] in CAN. unfold cell in CAN.
        pose proof (wc_canary s1 (WF_ctx s1 [] W1')) as CANR. rewrite Hcan1 in CANR. cbn [s_canary st_pristine ST0] in CANR.
        assert (HspE : CEIL + 144 <= spA /\ spA < 2 ^ 64) by (unfold ASSTK, AMSTK in HspA; lia).
        destruct (aEpi Mc spA can (getr r5 1) (getr r5 8) (getr r5 9) (getr r5 18) (getr r5 19) (getr r5 20) (getr r5 21)
                    (getr r5 22) (getr r5 23) (getr r5 24) (getr r5 25) HspE Dra CAN Kc K1' K8' K9' K18' K19' K20' K21' K22' K23' K24' K25'
                    r (seg_rom RSEGS) Q2 Q20) as (r' & RUN & E2x & E10x & E1x & E8x & E9x & E18x & E19x & E20x & E21x & E22x & E23x & E24x & E25x & K').
        eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN |].
        rewrite D1. replace (Z_to_bv 64 422480) with (0x67250%bv : word) by (apply bv_eq; reflexivity).
        (* [comment removed for export] *)
        pose proof (rc_active s1 Mc (rp_ctx s1 Mc RP1') 44 Hsc44) as Ract. rewrite (wc_active s1 (WF_ctx s1 [] W1') 44 Hsc44), Hhd in Ract.
        destruct (metaU_rng s1 [] W1' g (group_metaU s1 [] W1' g Hg)) as (GR1 & GR2 & GR8).
        assert (IDX32 : 0 <= idx < 32) by lia.
        assert (GRNG : 0 <= g < 2 ^ 64) by (clear -GR1 GR2 RN; ceil; unfold HEAPLO in *; lia).
        destruct (mRet Mc 44 idx g Hsc44 IDX32 Ract r' (seg_rom RSEGS)
                    ltac:(rewrite E10x; exact B10) ltac:(rewrite E18x; exact D18) ltac:(rewrite E9x; exact D9)) as (r10 & RUN10 & T19 & T18 & K10).
        eapply kat_msteps; [exact Hh1 | exact Hlz1 | exact RUN10 |].
        (* [comment removed for export] *)
        assert (FRx : forall a, 0 <= a < 2 ^ 64 -> Mc (Z_to_bv 64 a) <> M (Z_to_bv 64 a) -> m_wr SSTK [] sp a).
        { intros a Ha NE. rewrite SSTK_val. destruct (decide (Mc (Z_to_bv 64 a) = M1 (Z_to_bv 64 a))) as [E|NE1].
          - rewrite E in NE. left. pose proof (M1W a Ha NE). lia.
          - destruct (FR1 a Ha NE1) as [A|[A|[A|A]]]; [left; unfold ASSTK, AMSTK, spA in A; lia | right; left; exact A | right; right; left; exact A | right; right; right; exact A]. }
        assert (DFx : defined Mc (sp - SSTK) sp).
        { intros y Hy. rewrite SSTK_val in Hy. destruct (decide (Mc (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE1]; [rewrite E; apply DF1; lia|].
          destruct (FR1 y ltac:(lia) NE1) as [A|[A|[A|A]]]; [apply DFE; exact A | exfalso; ceil; unfold HEAPLO in A; lia | exfalso; unfold CTX_END, CTX in A; lia | exfalso; unfold A_ERRNO, TPV in A; lia]. }
        assert (STKx : forall y, sp - 48 <= y < sp -> Mc (Z_to_bv 64 y) = M1 (Z_to_bv 64 y)).
        { intros y Hy. destruct (decide (Mc (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE1]; [exact E|]. exfalso.
          destruct (FR1 y ltac:(lia) NE1) as [A|[A|[A|A]]]; [unfold ASSTK, AMSTK, spA in A; lia | ceil; unfold HEAPLO in A; lia | unfold CTX_END, CTX in A; lia | unfold A_ERRNO, TPV in A; lia]. }
        assert (KAS : keeps_but AS_CLOB r5 r').
        { apply (keeps_final_as r5 r'); try assumption.
          all: try (eapply keeps_big; [exact KB1 | exact K' | reflexivity]).
          all: try (rewrite E2x, D2; reflexivity). all: rewrite ?E1x; reflexivity. }
        apply (UbMhMallocK.small_tail [] M mdl R (seg_rom RSEGS) 65536 sp F HL ltac:(cbn; unfold LMAX; lia) ltac:(unfold MMAP_THRESHOLD; lia) Hra E2 HspS PXL HOK0
                 s1 Mc mdl1 r10 44 g idx W1' RP1' LG1' ltac:(rewrite EL1; reflexivity) Hh1 Hlz1 Hmat1 Hfs1 Hfds1 Hlim1 Hsc44
                 ltac:(left; unfold UbMhMallocK.sc0; rewrite sc44; reflexivity) Hhd Hg Hgsc Hidx Hsl OJ ltac:(lia) FRx DFx STKx T19 T18
                 ltac:(kept_rw K10; rewrite E9x; exact D9) ltac:(kept_rw K10; rewrite E8x; kept_rw K5; exact C8) ltac:(kept_rw K10; rewrite E2x; reflexivity)).
        + eapply keeps_but_trans; [exact K14|].
          eapply keeps_but_trans; [eapply keeps_but_mono; [exact K5|]|]. 1: intros rr Hr; apply in_regs_dec; revert rr Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
          eapply keeps_but_trans; [eapply keeps_but_mono; [exact KAS|]|]. 1: intros rr Hr; apply in_regs_dec; revert rr Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
          eapply keeps_but_mono; [exact K10|]. intros rr Hr; apply in_regs_dec; revert rr Hr; apply (proj1 (forallb_forall _ _)); reflexivity.
        + (* [comment removed for export] *)
          intros off x Hx. change (is_group s1 x) in Hx. pose proof (ONLY x Hx) as ->.
          unfold lone.
          change (g_lastidx (UbMhEnfr.st' s1 g idx 65536 off) g) with (g_lastidx s1 g).
          change (s_kind (UbMhEnfr.st' s1 g idx 65536 off) g) with (s_kind s1 g).
          change (g_maplen (UbMhEnfr.st' s1 g idx 65536 off) g) with (g_maplen s1 g).
          change (g_stride (UbMhEnfr.st' s1 g idx 65536 off) g) with (g_stride s1 g).
          change (g_sc (UbMhEnfr.st' s1 g idx 65536 off) g) with (g_sc s1 g).
          split; [exact GL0|]. split; [exact XK|]. split; [lia|].
          split. { right. unfold g_stride. rewrite ML17, GL0, Hgsc. apply Z.ltb_lt. vm_compute. reflexivity. }
          cbn [s_slot UbMhEnfr.st' set_slot]. subst idx. rewrite !Z.eqb_refl. cbn [andb]. eexists _, _, _, _. reflexivity. }
      (* [comment removed for export] *)
      apply (UbMhASlotK.UbMhASlotKG.L_G_cont ST0 [] M1 mdl r5 (seg_rom RSEGS) spA 44 65536 0%nat F false true Hsc44 HspA s2 Mo mdl2 r9 m P2 NJ2
               Elim ltac:(rewrite Ealist; reflexivity) Um Zm NLm2 ltac:(intros _; right; exact AGF2) F10
               ltac:(kept_rw K9; kept_rw K8; kept_rw K7; exact E18) ltac:(kept_rw K9; exact G19) ltac:(kept_rw K9; exact G24) ltac:(kept_rw K9; exact G25)).
      + (* [comment removed for export] *)
        intros rr GB LE _. exfalso. rewrite GCNT, scl44 in LE. lia.
      + (* [comment removed for export] *)
        intros rr GB GT. rewrite GCNT in GB, ECONT.
        assert (Hd0 : dle (dbound (16 * size_class 44)) 0%nat) by (rewrite scl44; unfold dle; change (dbound (16 * 4680)) with 0%nat; apply le_n).
        assert (Hlimbo0 : zlen (s_limbo ST0) + Z.of_nat 0 + 1 <= 8) by (change (zlen (s_limbo ST0)) with 0; cbn; lia).
        assert (HBUD0 : PHI [] + MBASE <= vm_limit (m_vmmaps mdl)) by (cbn [PHI]; unfold VMLIM, MH_GBUDGET in Clim'; lia).
        assert (DEFA : defined M1 (spA - ASSTK 0) spA) by (intros y Hy; apply DF1; unfold ASSTK, AMSTK, spA in Hy; lia).
        pose proof (FAILT ST0 eq_refl) as HQF0.
        eapply (UbMhASlotKM.L_M ST0 [] M1 mdl r5 (seg_rom RSEGS) spA 44 65536 0%nat F false true); try eassumption; try exact ECONT.
        all: try exact GB. all: rewrite scl44; lia.
    - (* [comment removed for export] *)
      intros can sec c' PF.
      destruct PF as (s2 & Mf & mdl2 & r9 & -> & W2 & RP2 & LG2 & Hh2 & Hlz2 & Hmat2 & Hfs2 & Hfds2 & Hvl2 &
                      Elim & Efl & Ear & Emeta & Eerr & KEEP & REG & F10 & F2 & K9 & MfW & DEFf).
      destruct KEEP as (Egrp & Eslot & Ealist & Eai & Ekind & Ecan & Eact & Eus & Ebn & Euq & Esq & Ectr & Esec & Emg & Elm2 & MU2).
      rewrite G1r. replace (Z_to_bv 64 423080) with (0x674a8%bv : word) by (apply bv_eq; reflexivity).
      apply (kf_of_kat F HL).
      set (ST0 := st_pristine can sec) in *.
      assert (RGf : forall rr, In rr (s_regions s2) -> HEAPLO <= rg_base rr /\ rg_base rr + rg_len rr <= CEIL).
      { intros rr Hrr. pose proof (wr_rng s2 (WF_regions s2 [] W2) rr Hrr). lia. }
      assert (MfM2 : forall y, 0 <= y < 2 ^ 64 -> (spA - 96 <= y < spA \/ A_CANARY <= y < A_CANARY + 8) -> Mf (Z_to_bv 64 y) = M2 (Z_to_bv 64 y)).
      { intros y Hy RG. destruct (decide (Mf (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E|NE]; [exact E|]. exfalso.
        destruct (MfW y Hy NE) as [A|[A|[A|(rr & Hrr & NK & A)]]];
          [unfold AMSTK, spM, spA in *; unfold A_CANARY in RG; ceil; lia | unfold CTX_END, CTX, A_CANARY in *; ceil; lia
          | unfold A_ERRNO, TPV, A_CANARY in *; ceil; lia | pose proof (RGf rr Hrr); unfold A_CANARY in RG; ceil; lia]. }
      pose proof (CANX Mf s2 can RP2 ltac:(rewrite Ecan; reflexivity)
                    ltac:(intros y Hy; rewrite (MfM2 y ltac:(unfold A_CANARY in Hy; lia) (or_intror Hy));
                          destruct (decide (M2 (Z_to_bv 64 y) = M1 (Z_to_bv 64 y))) as [E|NE]; [exact E|]; exfalso;
                          pose proof (M2W y ltac:(unfold A_CANARY in Hy; lia) NE); unfold A_CANARY in Hy; ceil; lia)) as CANEQ.
      apply (UbMhASlotKF.L_G1 ST0 [] M1 mdl r5 (seg_rom RSEGS) spA 44 (Kf F) 0%nat D2 Dra HspA (FAILT ST0 eq_refl) s2 Mf mdl2 r9).
      + constructor.
        * exact W2. * exact RP2. * apply (proj2 (LEDGERX_nil s2 _)); exact LG2.
        * exact Hh2. * exact Hlz2. * exact Hmat2. * exact Hfs2. * exact Hfds2. * exact Hvl2.
        * exact Ecan.
        * intros x Hx. cbn in Hx. destruct Hx.
        * exact MU2.
        * intros a Ha NE. destruct (decide (Mf (Z_to_bv 64 a) = M2 (Z_to_bv 64 a))) as [E|NE9].
          -- rewrite E in NE. left. pose proof (M2W a Ha NE). unfold ASSTK, AMSTK. lia.
          -- destruct (MfW a Ha NE9) as [A|[A|[A|(rr & Hrr & NK & A)]]].
             ++ left. unfold ASSTK, AMSTK, spM, spA in *. lia.
             ++ right; right; left. exact A.
             ++ right; right; right. exact A.
             ++ right; left. exact (UbMhASlotKA.nongroup_nonapp [] 0%nat s2 rr a W2 Hrr NK A).
        * intros y Hy. destruct (decide (Mf (Z_to_bv 64 y) = M2 (Z_to_bv 64 y))) as [E|NE9]; [rewrite E; apply G2; apply DF1; unfold ASSTK, AMSTK, spA in Hy; lia|].
          destruct (MfW y ltac:(ceil; lia) NE9) as [A|[A|[A|(rr & Hrr & NK & A)]]];
            [apply DEFf; exact A | exfalso; ceil; unfold CTX_END, CTX in *; lia | exfalso; ceil; unfold A_ERRNO, TPV in *; lia
            | exfalso; destruct (UbMhASlotKA.nongroup_nonapp [] 0%nat s2 rr y W2 Hrr NK A) as [B _]; ceil; lia].
        * apply (UbMhASlotKA.stk_transfer ST0 r5 spA 44 65536 0%nat Hsc44 Hreq44 HspA M2 Mf); [intros y Hy; apply MfM2; [ceil; lia | left; exact Hy]|].
          unfold UbMhASlotKA.stk_ok in STK2 |- *. cbn [UbMhASlotKA.can s_canary st_pristine ST0] in STK2 |- *. rewrite CANEQ. exact STK2.
        * rewrite F2. exact R8_2.
        * kept_rw K9. kept_rw K8. kept_rw K7. exact E20.
        * eapply keeps_big; [exact K58 | exact K9 | reflexivity].
      + intros x k o Hx. exfalso. unfold is_group in Hx. rewrite Egrp in Hx. cbn in Hx. exact Hx.
      + exact Elim.
      + exact F10.
  Qed.

End R0.
