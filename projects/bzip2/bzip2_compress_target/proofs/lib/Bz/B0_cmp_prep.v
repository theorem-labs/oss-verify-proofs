(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV B0_b2c_cbV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Definition B0_PREP : Z := 0x81e74.

Section B0PREP.
  Variable Q : machine_state -> Prop.
  Variables (E lo : Z) (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis E8 : (E mod 8 = 0)%Z.
  Hypothesis ELO : (0x62b000 <= E)%Z. Hypothesis EHI : (E + 55768 <= CEILv)%Z. Hypothesis LLO : (CEILv <= lo)%Z.

  Definition prep_W (usp : Z) : list (Z * Z) := [(E + 108, E + 124); (E + 128, E + 384); (E + 648, E + 652); (E + 660, E + 664); (usp - 16, usp)]%Z.

  Section Loop.
  Variables (usp : Z) (m0 : amem) (Jb : list byte).
  Variables (ra t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word).
  Hypothesis SHe : shzW b0segs [(E + 128, E + 384)]%Z m0 E (E + 55768).

  (* [comment removed for export] *)
  Lemma prep_loop : forall (n : nat) (i : Z) (a : zarr) (m : amem) (x17 : word),
    (1 <= Z.of_nat n)%Z -> (i + Z.of_nat n = 256)%Z -> (0 <= i)%Z ->
    u8arr b0segs m (E + 128) (ovb a Jb 256) -> mem_inv b0segs m -> munch [(E + 128, E + 384)]%Z m0 m -> wmono b0segs m0 m ->
    (forall m' (x11 x13 x14 x17' : word),
        u8arr b0segs m' (E + 128) (ovb (inUse_clear a i n) Jb 256) -> mem_inv b0segs m' -> munch [(E + 128, E + 384)]%Z m0 m' -> wmono b0segs m0 m' ->
        evt b0segs Q (MS (mkR ra (Z_to_bv 64 (usp - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) x11 cSB x13 x14 (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 256) x17'
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x81f44) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 (usp - 16)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 (E + 128 + i)) cSB (Z_to_bv 64 i) (Z_to_bv 64 (E + 128 + i))
                          (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 256) x17
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x81f08) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]; intros i a m x17 Hn Hi Hi0 INU MI MU WM K; [lia|].
    unfold CEILv in *. bz_ceil.
    pose proof (ovb_length a Jb 256 ltac:(lia)) as LIU.
    (* [comment removed for export] *)
    brun_to 0x81f1c%Z.
    pose proof (u8arr_store_ok b0segs m (E + 128) _ i _ INU ltac:(rewrite ovb_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ (le1 ?w)) _) =>
      pose proof (ovb_write1 b0segs mm (E + 128) a Jb 256 i w INU ltac:(lia)) as INU' end.
    clear INU. store_done. rename INU' into INU.
    replace (wr8 a i (bv_unsigned (Z_to_bv 64 0))) with (zset a i 0) in INU by reflexivity.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      enter_with (IH (i + 1)%Z (zset a i 0)); [st_eq | lia | lia | lia | exact INU | exact MI | exact MU | exact WM |].
      intros m' x11 x13 x14 x17' INU' MI' MU' WM'. eapply K; [| exact MI' | exact MU' | exact WM'].
      rewrite inUse_clear_S. exact INU'.
    - assert (n = 0)%nat by lia. subst n.
      (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _) end; [st_eq | | exact MI | exact MU | exact WM].
      rewrite inUse_clear_S. cbn [inUse_clear]. exact INU.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
  End Loop.

  (* [comment removed for export] *)
  Lemma B0_prep : forall (m : amem) (a : zarr) (Jb : list byte) (w108 w112 w116 w120 w648 : word) (bno : Z)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells b0segs m (E + 108) [C4 w108; C4 w112; C4 w116; C4 w120] -> u8arr b0segs m (E + 128) (ovb a Jb 256) ->
    rw_cells b0segs m (E + 648) [C4 w648] -> rw_cells b0segs m (E + 660) [C4 (Z_to_bv 64 bno)] -> (0 <= bno < 2147483647)%Z ->
    mem_inv b0segs m -> stk b0segs m lo (bv_unsigned sp) -> (lo + 16 <= (bv_unsigned sp))%Z -> aconsts B0C m -> shzW b0segs (prep_W (bv_unsigned sp)) m E (E + 55768) ->
    (forall m' (a0' a1' a2' a3' a4' a5' a6' a7' : word),
        rw_cells b0segs m' (E + 108) [C4 (Z_to_bv 64 0); C4 w112; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
        u8arr b0segs m' (E + 128) (ovb (inUse_clear a 0 256) Jb 256) ->
        rw_cells b0segs m' (E + 648) [C4 (Z_to_bv 64 4294967295)] -> rw_cells b0segs m' (E + 660) [C4 (Z_to_bv 64 (bno + 1))] ->
        mem_inv b0segs m' -> stk b0segs m' lo (bv_unsigned sp) -> munch (prep_W (bv_unsigned sp)) m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 B0_PREP) fc None m (seg_rom b0segs)).
  Proof.
    intros m a Jb w108 w112 w116 w120 w648 bno ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 W1 INU W6 BN BNR MI ST LOR AC SHe K.
    unfold CEILv in *. bz_ceil.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (munch_refl (prep_W (bv_unsigned sp)) m) as MU. pose proof (wmono_refl b0segs m) as WM. unfold prep_W in MU, SHe.
    pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (bv_unsigned_in_range _ sp) as RSP. unfold bv_modulus in RSP. change (2 ^ Z.of_N 64)%Z with 18446744073709551616%Z in RSP. fold (bv_unsigned sp) in RSP.
    unfold B0_PREP.
    carve_frame 16%nat ST.
    apply (rw_cells_split_CB b0segs _ _ [] 16 _ [] [8;8]%nat) in FR; [| reflexivity]. cbn [mk_CB_cells app] in FR.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    brun_to 0x81ea4%Z. wstep. lit_store.
    brun_to 0x81ebc%Z. wstep. lit_store.
    brun_to 0x81ed4%Z. wstep. lit_store.
    (* [comment removed for export] *)
    brun_to 0x81ef8%Z. wstep.
    reword_C4 W6 0%nat 4294967295%Z. { reflexivity. }
    (* [comment removed for export] *)
    brun_to 0x81f08%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (SHl : shzW b0segs [(E + 128, E + 384)]%Z mm E (E + 55768))
        by (eapply (shzW_sub b0segs _ _ m mm); [exact SHe| exact MU| a_sub_fp| lia| lia]);
      shelve_mem W1; shelve_mem W6; shelve_mem BN; shelve_mem FR; shelve_mem ST;
      enter_with (prep_loop (bv_unsigned sp) mm Jb ra t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 SHl 256%nat 0%Z a mm a7);
        [st_eq | cbn; lia | reflexivity | lia | exact INU | assumption | apply munch_refl | apply wmono_refl |] end.
    clear INU. intros m' x11 x13 x14 x17' INU MI' MUl WMl. unshelve_mems.
    lazymatch type of MUl with munch _ ?ma ?mb => transport_after_call b0segs ma mb MUl WMl end. clear MUl WMl.
    (* [comment removed for export] *)
    brun_to 0x81f6c%Z. wstep.
    (* [comment removed for export] *)
    replace (bv_unsigned sp - 16)%Z with (bv_unsigned sp + -16)%Z by lia.
    wstep. wstep. release_frame FR ST (bv_unsigned sp).
    replace (Z_to_bv 64 (bv_unsigned sp + -16 + 16)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _) end;
      [ st_eq | exact W1 | exact INU | exact W6 | exact BN | assumption | exact ST | unfold prep_W; exact MU | exact WM ].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  Lemma B0_prep_P : forall (P0 : Z) (m : amem) (a : zarr) (Jb : list byte) (w108 w112 w116 w120 w648 : word) (bno : Z)
      (ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= P0 < 18446744073709551616)%Z ->
    rw_cells b0segs m (E + 108) [C4 w108; C4 w112; C4 w116; C4 w120] -> u8arr b0segs m (E + 128) (ovb a Jb 256) ->
    rw_cells b0segs m (E + 648) [C4 w648] -> rw_cells b0segs m (E + 660) [C4 (Z_to_bv 64 bno)] -> (0 <= bno < 2147483647)%Z ->
    mem_inv b0segs m -> stk b0segs m lo P0 -> (lo + 16 <= P0)%Z -> aconsts B0C m -> shzW b0segs (prep_W P0) m E (E + 55768) ->
    (forall m' (a0' a1' a2' a3' a4' a5' a6' a7' : word),
        rw_cells b0segs m' (E + 108) [C4 (Z_to_bv 64 0); C4 w112; C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
        u8arr b0segs m' (E + 128) (ovb (inUse_clear a 0 256) Jb 256) ->
        rw_cells b0segs m' (E + 648) [C4 (Z_to_bv 64 4294967295)] -> rw_cells b0segs m' (E + 660) [C4 (Z_to_bv 64 (bno + 1))] ->
        mem_inv b0segs m' -> stk b0segs m' lo P0 -> munch (prep_W P0) m m' -> wmono b0segs m m' ->
        evt b0segs Q (MS (mkR ra (Z_to_bv 64 P0) gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (ret_pc ra) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 P0) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 B0_PREP) fc None m (seg_rom b0segs)).
  Proof.
    intros P0 m a Jb w108 w112 w116 w120 w648 bno ra t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 HP W1 INU W6 BN BNR MI ST LOR AC SHe K.
    pose proof (B0_prep m a Jb w108 w112 w116 w120 w648 bno ra (Z_to_bv 64 P0) t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as PN.
    rewrite (unsigned_lit P0) in PN by lia.
    exact (PN W1 INU W6 BN BNR MI ST LOR AC SHe K).
  Qed.
End B0PREP.
End ACeilS1.
