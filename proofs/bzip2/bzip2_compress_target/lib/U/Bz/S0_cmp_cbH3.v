(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast Frame.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Frame.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCBlock. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0 CmpCutSM CmpSdTac. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCNumZ. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzWalkArith4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require BzCLemmasSd.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_cbT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutBsw S0_cmp_bsx4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutCB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutCBw CmpCutMtf CmpCutMtf0 S0_cmp_cbT.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSdTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCNumZ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT.S0_cmp_bsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutBsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_bsx4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCBw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMtf OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutMtf0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require DecTac2 CmpLaws CmpMsKit CmpMsKit2 CmpFsKit0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require S0_cmp_cbT.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_cbH2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.DecTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCBlock OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCNumZ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpLaws OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCBw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpMsKit OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpMsKit2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpFsKit0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT.S0_cmp_bsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import ListNotations. Local Open Scope bv_scope.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut6.   (* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas8.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
(* [comment removed for export] *)
Ltac qlia := first [ zify_prune; zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker | zify_prune; Zify.zify; xlia zchecker ].
Ltac addr_eq_tac ::= symmetry; first [ apply wa_of_Z_to_bv; qlia | apply wa_of_var; qlia | unfold wa; f_equal; qlia ].
Ltac cbn_est_in H :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw bw_buff bw_live bw_numZ bw_zb] in H.
Ltac cbn_est :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw bw_buff bw_live bw_numZ bw_zb].


(* [comment removed for export] *)
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section Cells.
  Variable segs : list Segment.
  (* [comment removed for export] *)
  Lemma rw_cells_C44_CB8 : forall m A (a b : word) cs,
    rw_cells segs m A (C4 a :: C4 b :: cs) -> rw_cells segs m A (CB 8 (le4 a ++ le4 b) :: cs).
  Proof.
    intros m A a b cs H. destruct H as [[Hwf Hb] Hw]. split; [split|].
    - cbn in Hwf |- *. tauto.
    - cbn [cells_bytes cbytes app] in Hb |- *. rewrite <- app_assoc. exact Hb.
    - cbn [cells_size csize] in Hw |- *. exact Hw.
  Qed.
  (* [comment removed for export] *)
  Lemma rw_cells_C8z_C44 : forall m A cs,
    rw_cells segs m A (C8 (Z_to_bv 64 0) :: cs) -> rw_cells segs m A (C4 (Z_to_bv 64 0) :: C4 (Z_to_bv 64 0) :: cs).
  Proof.
    intros m A cs H. destruct H as [[Hwf Hb] Hw]. split; [split|].
    - cbn in Hwf |- *. tauto.
    - cbn [cells_bytes cbytes app] in Hb |- *. exact Hb.
    - cbn [cells_size csize] in Hw |- *. exact Hw.
  Qed.
  (* [comment removed for export] *)
  Lemma rw_cells_read_byte_C4lit : forall m A l1 v l2 a,
    rw_cells segs m A (l1 ++ C4 (Z_to_bv 64 v) :: l2) -> (0 <= v < 256)%Z -> a = wa (A + Z.of_nat (cells_size l1)) ->
    ov_read_bytes segs m a 1 = Some [Z_to_bv 8 v].
  Proof.
    intros m A l1 v l2 a H Hv ->.
    apply (proj1 (rw_cells_app_iff segs m A _ _)) in H. destruct H as [_ H].
    destruct H as [[Hwf Hb] Hw]. cbn [cells_bytes cbytes app] in Hb.
    rewrite <- (Z.add_0_r (A + Z.of_nat (cells_size l1))).
    rewrite (bytes_at_read segs m _ _ 0 1 Hb); [| lia| ]. 2:{ cbn. lia. }
    cbn [Z.to_nat skipn]. unfold le4. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. rewrite Z.mod_small by lia.
    cbn. f_equal.
  Qed.
End Cells.

(* [comment removed for export] *)
Definition cbH_W (cx : cctx) : list (Z * Z) := [(c_E cx + 80, c_E cx + 88); (c_E cx + 116, c_E cx + 128); (c_E cx + 640, c_E cx + 648); (c_A2 cx, c_A2 cx + ARR2_SIZE)]%Z.

Section CBH2.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation n := (e_nblock e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Hnb : (0 <= n)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 384 <= 18446744073709551616)%Z.
  Variable P : (word -> option byte) -> Prop.
  Hypothesis PT : forall m m', P m -> munch (cbH_W cx) m m' -> wmono s0segs m m' -> P m'.
  Local Ltac nt := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => notrap | _ => idtac end.
  (* [comment removed for export] *)
  Definition g3 : eg := EG (g_aie g) (g_sort g) (g_mtf g) true (Z_to_bv 64 (A2 + n)).

  Lemma S0_cb_H2 : forall (Q : machine_state -> Prop) (m : word -> option byte) (lo : Z)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_numZ (e_bw e) = 0%Z -> (1 <= e_blockNo e < 2147483647)%Z -> (e_blockNo e = 1%Z \/ (g_bs g = true /\ bw_ok (e_bw e))) ->
    (n <= (NBLOCKMAX + 19))%Z ->
    rw_cells s0segs m E (EHEAD1 cx g e) -> rw_cells s0segs m (E + 640) (EHEAD2 cx g e) -> u8arr s0segs m A2 (zb8 (e_arr2 e) ARR2_SIZE) ->
    mem_inv s0segs m -> stk s0segs m lo usp -> (CEIL <= lo)%Z -> P m ->
    (forall (m' : word -> option byte) (ra' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      let bS := cb_hdr e in
      rw_cells s0segs m' E (EHEAD1 cx g3 (est_set_bw e bS)) -> rw_cells s0segs m' (E + 640) (EHEAD2 cx g3 (est_set_bw e bS)) ->
      u8arr s0segs m' A2 (zb8 (zbl (e_arr2 e) n bS) ARR2_SIZE) ->
      mem_inv s0segs m' -> stk s0segs m' lo usp -> P m' -> munch (cbH_W cx) m m' -> wmono s0segs m m' ->
      bw_ok bS -> (bw_numZ bS <= 16)%Z ->
      evt s0segs Q (MS (mkR ra' sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1 (Z_to_bv 64 n) a1' a2' a3' a4' a5' a6' a7'
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x1645c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x163dc) fc None m (seg_rom s0segs)).
  Proof.
    intros Q m lo ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 NZ BN ALT NB EH1 EH2 AR2 MI ST Hlo HP K.
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    cps_destruct CX' as (RE & RE' & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & _ & _ & _ & _ & ME16 & MA1 & MA2 & MFT & _ & _ & LJ & _).
    pose proof SEP as SEP'. unfold cctx_sep, apart in SEP'. cbv zeta in SEP'. cps_destruct SEP' as (_ & SE2 & _).
    bz_ceil; bz_params; unfold FTAB_WORDS, ESTATE_SIZE, CEIL in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    pose proof (zb8_length (e_arr2 e) ARR2_SIZE ltac:(lia)) as LA2. pose proof (stk_lo_nonneg _ _ _ _ ST) as LONN.
    pose proof (munch_refl (cbH_W cx) m) as MU. pose proof (wmono_refl s0segs m) as WM. unfold cbH_W in MU.
    unfold EHEAD1 in EH1. cbn_est_in EH1. unfold EHEAD2 in EH2. cbn_est_in EH2. rewrite NZ in EH1.
    rename m into m0.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. flags. wstep. flags. wstep. nt. wstep. flags. wstep. flags. wstep. flags. wstep. flags. wstep. nt. wstep. wstep. wstep.
    try replace (n + A2)%Z with (A2 + n)%Z in EH1 by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kb; zify_cond_z Kb.
    - (* [comment removed for export] *)
      destruct ALT as [A1e|[Gbs OKb]]; [exfalso; lia|]. rewrite Gbs in EH2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      pose proof (proj2 (cb_hdr_cases e) ltac:(lia)) as HB. try rewrite (sx32_of_Z n) by (bz_params; lia).
      eapply K; rewrite ?HB;
        [ unfold EHEAD1, g3; cbn_est; rewrite NZ; exact EH1
        | unfold EHEAD2, g3; cbn_est; exact EH2
        | rewrite zbl_numZ0 by exact NZ; exact AR2
        | exact MI| exact ST| exact (PT _ _ HP MU WM)| unfold cbH_W; exact MU| exact WM| exact OKb| lia].
    - (* [comment removed for export] *)
      assert (B1 : e_blockNo e = 1%Z) by lia. clear Kb.
      apply rw_cells_C44_CB8 in EH2.
      wstep; lit_store.
      apply rw_cells_C8z_C44 in EH2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      set (B0 := BW 0 0 0 (bw_zb (e_bw e))).
      assert (OK0 : bw_ok B0) by (unfold bw_ok, B0; cbn; lia).
      assert (EH1b0 : EH1b cx g3 e m1 B0) by (unfold EH1b, EHEAD1, g3, B0; cbn_est; exact EH1). clear EH1.
      assert (EH2b0 : EH2b cx g3 e m1 B0) by (unfold EH2b, EHEAD2, g3, B0; cbn_est; exact EH2). clear EH2.
      assert (AR2b0 : AR2b cx e m1 B0) by (unfold AR2b; rewrite zbl_numZ0 by reflexivity; exact AR2). clear AR2.
      pose proof (proj1 (cb_hdr_cases e) B1) as HB. rewrite NZ in HB. fold B0 in HB. rewrite HB, bz_hdr4_eq in K.
      pose proof (Z.le_refl (bw_numZ B0)) as NZ0. cbn [B0 bw_numZ] in NZ0.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call cx g3 e sp gp tp F fc CX SEP eq_refl eq_refl Hnb Q B0 66 m1 lo);
        [lia| exact OK0| bz_params; cbn [B0 bw_numZ]; lia| exact EH1b0| exact EH2b0| exact AR2b0| exact MI| exact ST| bz_ceil; bz_params; unfold CEIL; exact Hlo|].
      clear EH1b0 EH2b0 AR2b0 MI ST.
      intros m2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      unfold cbT_W in MUc. transport_after_call s0segs m1 m2 MUc WMc. clear MUc WMc.
      replace (ret_pc (Z_to_bv 64 0x16428)) with (Z_to_bv 64 0x16428) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B0 66 OK0 ltac:(lia)) as G1.
      revert EH1 EH2 AR2 G1 K. generalize (bsW B0 8 66) as B1'. intros B1' EH1 EH2 AR2 G1 K. cps_destruct G1 as (OK1 & NZ1 & LV1). cbn [B0 bw_numZ] in NZ1.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call cx g3 e sp gp tp F fc CX SEP eq_refl eq_refl Hnb Q B1' 90 m2 lo);
        [lia| exact OK1| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| bz_ceil; bz_params; unfold CEIL; exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      unfold cbT_W in MUc. transport_after_call s0segs m2 m3 MUc WMc. clear MUc WMc.
      replace (ret_pc (Z_to_bv 64 0x16434)) with (Z_to_bv 64 0x16434) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B1' 90 OK1 ltac:(lia)) as G2.
      revert EH1 EH2 AR2 G2 K. generalize (bsW B1' 8 90) as B2. intros B2 EH1 EH2 AR2 G2 K. cps_destruct G2 as (OK2 & NZ2 & LV2).
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call cx g3 e sp gp tp F fc CX SEP eq_refl eq_refl Hnb Q B2 104 m3 lo);
        [lia| exact OK2| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| bz_ceil; bz_params; unfold CEIL; exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m4 t0_4 t1_4 t2_4 a0_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4 t6_4. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      unfold cbT_W in MUc. transport_after_call s0segs m3 m4 MUc WMc. clear MUc WMc.
      replace (ret_pc (Z_to_bv 64 0x16440)) with (Z_to_bv 64 0x16440) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B2 104 OK2 ltac:(lia)) as G3.
      revert EH1 EH2 AR2 G3 K. generalize (bsW B2 8 104) as B3. intros B3 EH1 EH2 AR2 G3 K. cps_destruct G3 as (OK3 & NZ3 & LV3).
      (* [comment removed for export] *)
      pose proof EH2 as EH2r. unfold EH2b, EHEAD2, g3 in EH2r. cbn_est_in EH2r.
      wstep. wstep. wstep. nt. wstep. wstep. wstep.
      (* [comment removed for export] *)
      replace (Z.land (BLOCKSIZE100K + 48) 255) with (48 + BLOCKSIZE100K)%Z
        by (change 255%Z with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small by (bz_params; lia); lia).
      eapply (bsw8_call cx g3 e sp gp tp F fc CX SEP eq_refl eq_refl Hnb Q B3 (48 + BLOCKSIZE100K) m4 lo);
        [lia| exact OK3| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| bz_ceil; bz_params; unfold CEIL; exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m5 t0_5 t1_5 t2_5 a0_5 a1_5 a2_5 a3_5 a4_5 a5_5 a6_5 a7_5 t3_5 t4_5 t5_5 t6_5. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      unfold cbT_W in MUc. transport_after_call s0segs m4 m5 MUc WMc. clear MUc WMc.
      replace (ret_pc (Z_to_bv 64 0x16458)) with (Z_to_bv 64 0x16458) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B3 (48 + BLOCKSIZE100K) OK3 ltac:(bz_params; lia)) as G4.
      revert EH1 EH2 AR2 G4 K. generalize (bsW B3 8 (48 + BLOCKSIZE100K)) as B4. intros B4 EH1 EH2 AR2 G4 K. cps_destruct G4 as (OK4 & NZ4 & LV4).
      (* [comment removed for export] *)
      pose proof EH1 as EH1r. unfold EH1b, EHEAD1, g3 in EH1r. cbn_est_in EH1r.
      wstep. clear EH1r. try rewrite (sx32_of_Z n) by (bz_params; lia).
      eapply K; [exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact (PT _ _ HP MU WM)| unfold cbH_W; exact MU| exact WM| exact OK4| lia].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End CBH2.

End ACeilS1.
End S0_cmp_cbH2.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbH3.S0_cmp_cbH2.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Local Ltac tlia ::= first [ Zify.zify; xlia zchecker
                         | sf_unhide; unhide_disj;
                           first [ zify_prune_neg; Zify.zify; xlia zchecker
                                 | zify_prune_plain; Zify.zify; xlia zchecker
                                 | Zify.zify; xlia zchecker ] ].
Local Ltac tslia ::= tslia_sep.
Local Ltac simpl_sizes_goal ::=
  literal_cell_sizes;
  try match goal with |- context [length (_ ++ _)] => rewrite !length_app end;
  cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ];
  try match goal with |- context [length (le8 _)] => rewrite !length_le8 end;
  try match goal with |- context [length (le4 _)] => rewrite !length_le4 end;
  try match goal with |- context [length (le2 _)] => rewrite !length_le2 end;
  try match goal with |- context [length (le1 _)] => rewrite !length_le1 end;
  try match goal with |- context [length (u32s _)] => rewrite !u32s_length end;
  try match goal with |- context [length (u64s _)] => rewrite !u64s_length end;
  try match goal with |- context [length (upd _ _ _)] => rewrite !upd_length end;
  try match goal with |- context [length (zb8 _ _)] => rewrite !zb8_length_nat end;
  try match goal with |- context [length (ovb _ _ _)] => rewrite !ovb_length_nat end;
  try match goal with |- context [length (ovw _ _ _)] => rewrite !ovw_length_nat end;
  try match goal with |- context [length (zw32 _ _)] => rewrite !zw32_length_nat end.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
#[local] Ltac2 Set RangeFast.RF.rc_skip_hyps := fun () => [@USP2].   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section CBH3.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gsort : g_sort g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 384 <= 18446744073709551616)%Z.
  Ltac openCX := openCX3 CX SEP USP1.
  Notation EH1b := (EH1b cx g e). Notation EH2b := (EH2b cx g e). Notation AR2b := (AR2b cx e).
  (* [comment removed for export] *)
  Notation HW := (((bv_unsigned sp + 8)%Z, (bv_unsigned sp + 16)%Z) :: cbH_W cx).
  Local Ltac nt := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => notrap | _ => idtac end.

  (* [comment removed for export] *)
  Lemma S0_cb_flushA : forall (f : nat) (Q : machine_state -> Prop) (b : bw) (m m0 : word -> option byte)
      (ra t0 t1 t2 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xb : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (nblock + bw_numZ b + Z.of_nat f <= ARR2_SIZE)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m ->
    munch (cbT_W cx) m0 m -> wmono s0segs m0 m ->
    (forall m' (a0' a1' a3' a4' a5' a6' : word),
        let b' := bs_needw f b in
        (0 <= bw_live b' < 8)%Z -> bw_ok b' -> (bw_numZ b <= bw_numZ b' <= bw_numZ b + Z.of_nat f)%Z ->
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv s0segs m' ->
        munch (cbT_W cx) m0 m' -> wmono s0segs m0 m' ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0' a1' (Z_to_bv 64 (bw_live b')) a3' a4' a5' a6' a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x16530) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 7) (Z_to_bv 64 (bw_numZ b)) a2 xb a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x164cc) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros Q b m m0 ra t0 t1 t2 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xb OK L8 Lf ROOM XB EH1 EH2 AR2 MI MU WM K; [lia|].
    cps_pose OK as (OKb & OKl & OKn).
    unfold S0_cmp_cbT.EH1b, S0_cmp_cbT.EH2b, S0_cmp_cbT.AR2b in EH1, EH2, AR2.
    openCX. unfold EHEAD1, EHEAD2 in EH1, EH2; cbn_est_in EH1; cbn_est_in EH2. rewrite Gbs in EH2. rewrite Gzb in EH1. unfold S0_cmp_cbT.cbT_W in MU. bz_params.
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    rewrite bs_needw_S in K. replace (8 <=? bw_live b)%Z with true in K by (symmetry; apply Z.leb_le; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. flags. wstep. flags. wstep. nt.
    wstep. flags. wstep. flags. wstep. flags. wstep. flags. wstep. nt. wstep. nt.
    wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. nt. wstep. wstep. wstep. wstep. wstep. wstep. wstep. nt. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    try replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with context [wr8 (zbl (e_arr2 e) nblock b) ?i ?u] =>
      replace (wr8 (zbl (e_arr2 e) nblock b) i u) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite XB. rewrite unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH Q (bw_emit b) _ m0 ra t0 t1 t2 s1 _ _ _ _ a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _);
        [st_eq| unfold bw_ok, bw_emit; cbn [bw_buff bw_live bw_numZ]; pose proof (Z.mod_pos_bound (Z.shiftl (bw_buff b) 8) 4294967296 ltac:(lia)); lia
        | unfold bw_emit; cbn [bw_live]; lia| unfold bw_emit; cbn [bw_live]; lia
        | unfold bw_emit; cbn [bw_numZ]; bz_params; lia| | | | unfold S0_cmp_cbT.AR2b; exact AR2| assumption| assumption| assumption|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + unfold S0_cmp_cbT.EH1b, EHEAD1, bw_emit. cbn_est. cbn [bw_numZ]. rewrite Gzb. exact EH1.
      + unfold S0_cmp_cbT.EH2b, EHEAD2, bw_emit. cbn_est. cbn [bw_buff bw_live]. rewrite Gbs. exact EH2.
      + intros m' a0' a1' a3' a4' a5' a6'. cbv zeta. intros LV' OK' NZ' EH1' EH2' AR2' MI' MU' WM'. eapply K; [exact LV'| exact OK'| | exact EH1'| exact EH2'| exact AR2'| exact MI'| exact MU'| exact WM'].
        revert NZ'. unfold bw_emit. cbn [bw_numZ]. intros NZ'. lia.
    - assert (EF : bs_needw f (bw_emit b) = bw_emit b).
      { destruct f as [|f']; [reflexivity|]. rewrite bs_needw_S. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; unfold bw_emit; cbn [bw_live]; lia). reflexivity. }
      rewrite EF in K.
      enter_with (K _ _ _ _ _ _ _); [st_eq| unfold bw_emit; cbn [bw_live]; lia
        | unfold bw_ok, bw_emit; cbn [bw_buff bw_live bw_numZ]; pose proof (Z.mod_pos_bound (Z.shiftl (bw_buff b) 8) 4294967296 ltac:(lia)); lia
        | unfold bw_emit; cbn [bw_numZ]; lia| | | unfold S0_cmp_cbT.AR2b; exact AR2| assumption| assumption| assumption].
      + unfold S0_cmp_cbT.EH1b, EHEAD1, bw_emit. cbn_est. cbn [bw_numZ]. rewrite Gzb. exact EH1.
      + unfold S0_cmp_cbT.EH2b, EHEAD2, bw_emit. cbn_est. cbn [bw_buff bw_live]. rewrite Gbs. exact EH2.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma S0_cb_flushB : forall (f : nat) (Q : machine_state -> Prop) (b : bw) (m m0 : word -> option byte)
      (ra t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xb x0 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (nblock + bw_numZ b + Z.of_nat f <= ARR2_SIZE)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m ->
    munch (cbT_W cx) m0 m -> wmono s0segs m0 m ->
    (forall m' (a2' a3' a5' a6' a7' : word),
        let b' := bs_needw f b in
        (0 <= bw_live b' < 8)%Z -> bw_ok b' -> (bw_numZ b <= bw_numZ b' <= bw_numZ b + Z.of_nat f)%Z ->
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv s0segs m' ->
        munch (cbT_W cx) m0 m' -> wmono s0segs m0 m' ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 x0 (Z_to_bv 64 7) a2' a3' (Z_to_bv 64 (bw_live b')) a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x165d4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 x0 (Z_to_bv 64 7) (Z_to_bv 64 (bw_numZ b)) xb a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x16570) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros Q b m m0 ra t0 t1 t2 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xb x0 OK L8 Lf ROOM XB EH1 EH2 AR2 MI MU WM K; [lia|].
    cps_pose OK as (OKb & OKl & OKn).
    unfold S0_cmp_cbT.EH1b, S0_cmp_cbT.EH2b, S0_cmp_cbT.AR2b in EH1, EH2, AR2.
    openCX. unfold EHEAD1, EHEAD2 in EH1, EH2; cbn_est_in EH1; cbn_est_in EH2. rewrite Gbs in EH2. rewrite Gzb in EH1. unfold S0_cmp_cbT.cbT_W in MU. bz_params.
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    rewrite bs_needw_S in K. replace (8 <=? bw_live b)%Z with true in K by (symmetry; apply Z.leb_le; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. flags. wstep. flags. wstep. nt.
    wstep. flags. wstep. flags. wstep. flags. wstep. flags. wstep. nt. wstep. nt.
    wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. nt. wstep. wstep. wstep. wstep. wstep. wstep. wstep. nt. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    try replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with context [wr8 (zbl (e_arr2 e) nblock b) ?i ?u] =>
      replace (wr8 (zbl (e_arr2 e) nblock b) i u) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite XB. rewrite unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH Q (bw_emit b) _ m0 ra t0 t1 t2 s1 _ _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ x0);
        [st_eq| unfold bw_ok, bw_emit; cbn [bw_buff bw_live bw_numZ]; pose proof (Z.mod_pos_bound (Z.shiftl (bw_buff b) 8) 4294967296 ltac:(lia)); lia
        | unfold bw_emit; cbn [bw_live]; lia| unfold bw_emit; cbn [bw_live]; lia
        | unfold bw_emit; cbn [bw_numZ]; bz_params; lia| | | | unfold S0_cmp_cbT.AR2b; exact AR2| assumption| assumption| assumption|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + unfold S0_cmp_cbT.EH1b, EHEAD1, bw_emit. cbn_est. cbn [bw_numZ]. rewrite Gzb. exact EH1.
      + unfold S0_cmp_cbT.EH2b, EHEAD2, bw_emit. cbn_est. cbn [bw_buff bw_live]. rewrite Gbs. exact EH2.
      + intros m' a2' a3' a5' a6' a7'. cbv zeta. intros LV' OK' NZ' EH1' EH2' AR2' MI' MU' WM'. eapply K; [exact LV'| exact OK'| | exact EH1'| exact EH2'| exact AR2'| exact MI'| exact MU'| exact WM'].
        revert NZ'. unfold bw_emit. cbn [bw_numZ]. intros NZ'. lia.
    - assert (EF : bs_needw f (bw_emit b) = bw_emit b).
      { destruct f as [|f']; [reflexivity|]. rewrite bs_needw_S. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; unfold bw_emit; cbn [bw_live]; lia). reflexivity. }
      rewrite EF in K.
      enter_with (K _ _ _ _ _ _); [st_eq| unfold bw_emit; cbn [bw_live]; lia
        | unfold bw_ok, bw_emit; cbn [bw_buff bw_live bw_numZ]; pose proof (Z.mod_pos_bound (Z.shiftl (bw_buff b) 8) 4294967296 ltac:(lia)); lia
        | unfold bw_emit; cbn [bw_numZ]; lia| | | unfold S0_cmp_cbT.AR2b; exact AR2| assumption| assumption| assumption].
      + unfold S0_cmp_cbT.EH1b, EHEAD1, bw_emit. cbn_est. cbn [bw_numZ]. rewrite Gzb. exact EH1.
      + unfold S0_cmp_cbT.EH2b, EHEAD2, bw_emit. cbn_est. cbn [bw_buff bw_live]. rewrite Gbs. exact EH2.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.

  (* [comment removed for export] *)
  Lemma bsW1_0_fields : forall b, let b1 := bs_needw BS_FUEL b in
    bw_buff (bsW b 1 0) = bw_buff b1 /\ bw_live (bsW b 1 0) = (bw_live b1 + 1)%Z /\ bw_numZ (bsW b 1 0) = bw_numZ b1 /\ bw_zb (bsW b 1 0) = bw_zb b1.
  Proof. intros b. unfold bsW. cbn [bw_buff bw_live bw_numZ bw_zb]. rewrite Z.shiftl_0_l, Z.mod_0_l, Z.lor_0_r by lia. repeat split; reflexivity. Qed.
  Lemma bsW24_fields : forall b v, let b1 := bs_needw BS_FUEL b in
    bw_buff (bsW b 24 v) = Z.lor (bw_buff b1) ((Z.shiftl v (8 - bw_live b1)) mod 4294967296) /\ bw_live (bsW b 24 v) = (bw_live b1 + 24)%Z /\
    bw_numZ (bsW b 24 v) = bw_numZ b1 /\ bw_zb (bsW b 24 v) = bw_zb b1.
  Proof. intros b v. unfold bsW. cbn [bw_buff bw_live bw_numZ bw_zb]. replace (32 - bw_live (bs_needw BS_FUEL b) - 24)%Z with (8 - bw_live (bs_needw BS_FUEL b))%Z by lia. repeat split; reflexivity. Qed.

  Variable P : (word -> option byte) -> Prop.
  Hypothesis PT3 : forall m m', P m -> munch HW m m' -> wmono s0segs m m' -> P m'.
  Notation SLOTS w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 :=
    [C8 w0; C8 w1; C8 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10; C8 w11; C8 w12; C8 w13; C8 w14; C8 w15; C8 w16; C8 w17; C8 w18; C8 w19; C8 w20; C8 w21].

  Lemma S0_cb_H3 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte) (lo : Z)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 wisl : word)
      (w8 : word),
    bw_ok b -> (nblock + bw_numZ b + 64 <= ARR2_SIZE)%Z -> (0 <= e_blockCRC e < 4294967296)%Z -> (0 <= e_origPtr e < 16777216)%Z -> (0 < nblock)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m -> stk s0segs m lo usp -> (CEIL <= lo)%Z ->
    rw_cells s0segs m (usp + 8) [C8 w8] -> P m ->
    (forall m' (ra' t1' t2' t3' t4' t5' t6' : word),
      let bH := cb_bhdr b e in
      rw_cells s0segs m' E (EHEAD1n cx g (est_set_bw e bH) 0) -> EH2b m' bH -> AR2b m' bH -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
      rw_cells s0segs m' (usp + 8) [C8 wisl] ->
      P m' -> munch HW m m' -> wmono s0segs m m' ->
      bw_ok bH -> (bw_numZ b <= bw_numZ bH <= bw_numZ b + 48)%Z ->
      evt s0segs Q (MS (mkR ra' sp gp tp (Z_to_bv 64 256) t1' t2' (Z_to_bv 64 E) wisl (Z_to_bv 64 A1) (Z_to_bv 64 0)
                            (Z_to_bv 64 (18446744073709551615 - (E + 128))) (Z_to_bv 64 0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                            (Z_to_bv 64 (E + 384)) (Z_to_bv 64 (18446744073709551615 - (E + 384)))
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                       F (Z_to_bv 64 0x16640) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) wisl a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16460) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ cx g e sp gp tp F fc CX SEP Gsort Gbs Gzb Hnb USP1 USP2 P PT3.
    intros Q b m lo ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 wisl w8.
    intros OK ROOM HBC HOP POS EH1 EH2 AR2 MI ST Hlo SL HP K.
    pose proof ROOM as RM. bz_params. pose proof USP1 as U1. bz_ceil; bz_params; unfold CEIL in U1.
    pose proof (munch_refl HW m) as MU. pose proof (wmono_refl s0segs m) as WM. unfold cbH_W in MU.
    rewrite cb_bhdr_eq, bz_magic6_eq in K.
    assert (USP1' : (CEIL <= usp + 8)%Z) by (bz_ceil; bz_params; unfold CEIL in *; lia).
    rename m into m0. rename b into B0. pose proof OK as OK0. pose proof (Z.le_refl (bw_numZ B0)) as NZ0.
    openCX. bz_ceil; bz_params; unfold CEIL in Hlo.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    eapply (bsw8_call cx g e sp gp tp F fc CX SEP Gbs Gzb Hnb Q B0 49 m0 lo); [lia| exact OK0| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
    clear EH1 EH2 AR2 MI ST.
    intros m1 t0_1 t1_1 t2_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 t3_1 t4_1 t5_1 t6_1. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
    unfold S0_cmp_cbT.cbT_W in MUc. transport_after_call s0segs m0 m1 MUc WMc. clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x1646c)) with (Z_to_bv 64 0x1646c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bsW8_growth B0 49 OK0 ltac:(lia)) as G1.
    revert EH1 EH2 AR2 G1 K. generalize (bsW B0 8 49) as B1. intros B1 EH1 EH2 AR2 G1 K. cps_destruct G1 as (OK1 & NZ1 & LV1).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    eapply (bsw8_call cx g e sp gp tp F fc CX SEP Gbs Gzb Hnb Q B1 65 m1 lo); [lia| exact OK1| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
    clear EH1 EH2 AR2 MI ST.
    intros m2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
    unfold S0_cmp_cbT.cbT_W in MUc. transport_after_call s0segs m1 m2 MUc WMc. clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x16478)) with (Z_to_bv 64 0x16478) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bsW8_growth B1 65 OK1 ltac:(lia)) as G2.
    revert EH1 EH2 AR2 G2 K. generalize (bsW B1 8 65) as B2. intros B2 EH1 EH2 AR2 G2 K. cps_destruct G2 as (OK2 & NZ2 & LV2).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    eapply (bsw8_call cx g e sp gp tp F fc CX SEP Gbs Gzb Hnb Q B2 89 m2 lo); [lia| exact OK2| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
    clear EH1 EH2 AR2 MI ST.
    intros m3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
    unfold S0_cmp_cbT.cbT_W in MUc. transport_after_call s0segs m2 m3 MUc WMc. clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x16484)) with (Z_to_bv 64 0x16484) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bsW8_growth B2 89 OK2 ltac:(lia)) as G3.
    revert EH1 EH2 AR2 G3 K. generalize (bsW B2 8 89) as B3. intros B3 EH1 EH2 AR2 G3 K. cps_destruct G3 as (OK3 & NZ3 & LV3).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    eapply (bsw8_call cx g e sp gp tp F fc CX SEP Gbs Gzb Hnb Q B3 38 m3 lo); [lia| exact OK3| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
    clear EH1 EH2 AR2 MI ST.
    intros m4 t0_4 t1_4 t2_4 a0_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4 t6_4. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
    unfold S0_cmp_cbT.cbT_W in MUc. transport_after_call s0segs m3 m4 MUc WMc. clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x16490)) with (Z_to_bv 64 0x16490) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bsW8_growth B3 38 OK3 ltac:(lia)) as G4.
    revert EH1 EH2 AR2 G4 K. generalize (bsW B3 8 38) as B4. intros B4 EH1 EH2 AR2 G4 K. cps_destruct G4 as (OK4 & NZ4 & LV4).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    eapply (bsw8_call cx g e sp gp tp F fc CX SEP Gbs Gzb Hnb Q B4 83 m4 lo); [lia| exact OK4| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
    clear EH1 EH2 AR2 MI ST.
    intros m5 t0_5 t1_5 t2_5 a0_5 a1_5 a2_5 a3_5 a4_5 a5_5 a6_5 a7_5 t3_5 t4_5 t5_5 t6_5. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
    unfold S0_cmp_cbT.cbT_W in MUc. transport_after_call s0segs m4 m5 MUc WMc. clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x1649c)) with (Z_to_bv 64 0x1649c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bsW8_growth B4 83 OK4 ltac:(lia)) as G5.
    revert EH1 EH2 AR2 G5 K. generalize (bsW B4 8 83) as B5. intros B5 EH1 EH2 AR2 G5 K. cps_destruct G5 as (OK5 & NZ5 & LV5).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    eapply (bsw8_call cx g e sp gp tp F fc CX SEP Gbs Gzb Hnb Q B5 89 m5 lo); [lia| exact OK5| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
    clear EH1 EH2 AR2 MI ST.
    intros m6 t0_6 t1_6 t2_6 a0_6 a1_6 a2_6 a3_6 a4_6 a5_6 a6_6 a7_6 t3_6 t4_6 t5_6 t6_6. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
    unfold S0_cmp_cbT.cbT_W in MUc. transport_after_call s0segs m5 m6 MUc WMc. clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x164a8)) with (Z_to_bv 64 0x164a8) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bsW8_growth B5 89 OK5 ltac:(lia)) as G6.
    revert EH1 EH2 AR2 G6 K. generalize (bsW B5 8 89) as B6. intros B6 EH1 EH2 AR2 G6 K. cps_destruct G6 as (OK6 & NZ6 & LV6).

    (* [comment removed for export] *)
    pose proof EH2 as EH2r. unfold S0_cmp_cbT.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r.
    wstep. clear EH2r. wstep. wstep.
    eapply (bsput32_call cx g e sp gp tp F fc CX SEP Gbs Gzb Hnb Q B6 (e_blockCRC e) m6 lo); [exact HBC| exact OK6| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
    clear EH1 EH2 AR2 MI ST.
    intros m7 t0_7 t1_7 t2_7 a0_7 a1_7 a2_7 a3_7 a4_7 a5_7 a6_7 a7_7 t3_7 t4_7 t5_7 t6_7. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
    unfold S0_cmp_cbT.cbT_W in MUc. transport_after_call s0segs m6 m7 MUc WMc. clear MUc WMc.
    replace (ret_pc (Z_to_bv 64 0x164b4)) with (Z_to_bv 64 0x164b4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    pose proof (bsPutUInt32_growth B6 (e_blockCRC e) OK6 ltac:(lia)) as G7.
    revert EH1 EH2 AR2 G7 K. generalize (bsPutUInt32 B6 (e_blockCRC e)) as B7.
    intros B7 EH1 EH2 AR2 G7 K. cps_destruct G7 as (OK7 & NZ7 & LV7). cps_pose OK7 as (OK7b & OK7l & OK7n).
    (* [comment removed for export] *)
    pose proof (bsW1_0_fields B7) as F8. cbv zeta in F8.
    assert (LF7 : (bw_live B7 < 40)%Z) by lia. pose proof (bs_needw_post BS_FUEL B7 OK7 LF7) as NP.
    set (B7' := bs_needw BS_FUEL B7) in *.
    (* [comment removed for export] *)
    assert (JN : forall (m8 : word -> option byte) (x10 x11 x13 x14 x15 x16 : word),
      (bw_numZ B7' <= bw_numZ B7 + 5)%Z ->
      EH1b m8 B7' -> EH2b m8 B7' -> AR2b m8 B7' -> mem_inv s0segs m8 -> stk s0segs m8 lo usp ->
      rw_cells s0segs m8 (usp + 8) [C8 w8] ->
      munch HW m0 m8 -> wmono s0segs m0 m8 ->
      evt s0segs Q (MS (mkR (Z_to_bv 64 0x164b4) sp gp tp t0_7 t1_7 t2_7 (Z_to_bv 64 E) wisl x10 x11 (Z_to_bv 64 (bw_live B7')) x13 x14 x15 x16 a7_7
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_7 t4_7 t5_7 t6_7)
                       F (Z_to_bv 64 0x16530) fc None m8 (seg_rom s0segs))).
    { clear EH1 EH2 AR2 MI ST SL MU WM. intros m8 x10 x11 x13 x14 x15 x16 NZB EH1 EH2 AR2 MI ST SL MU WM. unfold cbH_W in MU.
      cps_destruct NP as (OK7' & LVE & NZ7'). cps_pose OK7' as (OK7'b & OK7'l & OK7'n).
      assert (LV7' : (0 <= bw_live B7' < 8)%Z) by (rewrite LVE; Z.div_mod_to_equations; lia).
      pose proof (zb8_length (zbl (e_arr2 e) nblock B7') ARR2_SIZE ltac:(lia)) as LA2.
      (* [comment removed for export] *)
      pose proof EH1 as EH1r. unfold S0_cmp_cbT.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r. rewrite Gsort, Gzb in EH1r.
      pose proof EH2 as EH2r. unfold S0_cmp_cbT.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r. clear EH1 EH2.
      unfold S0_cmp_cbT.AR2b in AR2.
      wstep. wstep. wstep. wstep. nt. wstep. wstep. wstep. nt. wstep. wstep. nt. wstep. wstep. wstep. wstep.
      (* [comment removed for export] *)
      cps_destruct F8 as (F8b & F8l & F8n & F8z).
      replace (bw_buff B7') with (bw_buff (bsW B7 1 0)) in EH2r by (rewrite F8b; reflexivity).
      replace (bw_live B7' + 1)%Z with (bw_live (bsW B7 1 0)) in EH2r by (rewrite F8l; reflexivity).
      replace (bw_numZ B7') with (bw_numZ (bsW B7 1 0)) in EH1r by (rewrite F8n; reflexivity).
      rewrite <- (zbl_same_bytes (e_arr2 e) nblock B7' (bsW B7 1 0) F8n F8z) in AR2.
      pose proof (bsW_growth B7 1 0 OK7 ltac:(lia) ltac:(lia)) as G8.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m8s end.
      assert (EH1b8 : EH1b m8s (bsW B7 1 0)) by (unfold S0_cmp_cbT.EH1b, EHEAD1; cbn_est; rewrite Gsort, Gzb; exact EH1r). clear EH1r.
      assert (EH2b8 : EH2b m8s (bsW B7 1 0)) by (unfold S0_cmp_cbT.EH2b, EHEAD2; cbn_est; rewrite Gbs; exact EH2r). clear EH2r.
      assert (AR2b8 : AR2b m8s (bsW B7 1 0)) by (unfold S0_cmp_cbT.AR2b; exact AR2). clear AR2.
      revert EH1b8 EH2b8 AR2b8 G8 F8b F8l F8n F8z K. generalize (bsW B7 1 0) as B8. intros B8 EH1 EH2 AR2 G8 F8b F8l F8n F8z K.
      cps_destruct G8 as (OK8 & NZ8 & LV8). cps_pose OK8 as (OK8b & OK8l & OK8n).
      pose proof (bsW24_fields B8 (e_origPtr e)) as F9. cbv zeta in F9.
      assert (LF8 : (bw_live B8 < 40)%Z) by lia. pose proof (bs_needw_post BS_FUEL B8 OK8 LF8) as NP8.
      set (B8' := bs_needw BS_FUEL B8) in *.
      (* [comment removed for export] *)
      assert (JN2 : forall (m9 : word -> option byte) (y11 y12 y13 y15 y16 y17 : word),
        (bw_numZ B8' <= bw_numZ B8 + 5)%Z ->
        EH1b m9 B8' -> EH2b m9 B8' -> AR2b m9 B8' -> mem_inv s0segs m9 -> stk s0segs m9 lo usp ->
        rw_cells s0segs m9 (usp + 8) [C8 w8] ->
        munch HW m0 m9 -> wmono s0segs m0 m9 ->
        evt s0segs Q (MS (mkR (Z_to_bv 64 0x164b4) sp gp tp t0_7 t1_7 t2_7 (Z_to_bv 64 E) wisl (Z_to_bv 64 (e_origPtr e)) y11 y12 y13
                              (Z_to_bv 64 (bw_live B8')) y15 y16 y17
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3_7 t4_7 t5_7 t6_7)
                         F (Z_to_bv 64 0x165d4) fc None m9 (seg_rom s0segs))).
      { clear EH1 EH2 AR2 MI ST SL MU WM. intros m9 y11 y12 y13 y15 y16 y17 NZB2 EH1 EH2 AR2 MI ST SL MU WM. unfold cbH_W in MU.
        cps_destruct NP8 as (OK8' & LVE8 & NZ8'). cps_pose OK8' as (OK8'b & OK8'l & OK8'n).
        assert (LV8' : (0 <= bw_live B8' < 8)%Z) by (rewrite LVE8; Z.div_mod_to_equations; lia).
        pose proof (zb8_length (zbl (e_arr2 e) nblock B8') ARR2_SIZE ltac:(lia)) as LA2b.
        pose proof EH1 as EH1r. unfold S0_cmp_cbT.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r. rewrite Gsort, Gzb in EH1r.
        pose proof EH2 as EH2r. unfold S0_cmp_cbT.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r. clear EH1 EH2.
        unfold S0_cmp_cbT.AR2b in AR2.
        (* [comment removed for export] *)
        wstep. wstep. wstep. wstep. nt. wstep. wstep. wstep. nt.
        wstep. wstep. wstep. nt. wstep. wstep. wstep.
        (* [comment removed for export] *)
        wstep. wstep. wstep. wstep. wstep. wstep; lit_store. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
        (* [comment removed for export] *)
        cps_destruct F9 as (F9b & F9l & F9n & F9z).
        pose proof (bsW_growth B8 24 (e_origPtr e) OK8 ltac:(lia) ltac:(lia)) as G9. cps_destruct G9 as (OK9 & NZ9 & LV9).
        replace ((32 - bw_live B8' + -24) mod 32)%Z with (8 - bw_live B8')%Z in EH2r by (rewrite Z.mod_small by lia; lia).
        reword_C4 EH2r 0%nat (bw_buff (bsW B8 24 (e_origPtr e))).
        { rewrite F9b, low32_lit, low32_lor. change 18446744073709551615%Z with (Z.ones 64). rewrite Z.land_ones by lia.
          change (2 ^ 64)%Z with 18446744073709551616%Z. rewrite mod64_mod32, swrap32_mod32.
          rewrite low32_sx32, low32_lit, (low32_small (bw_buff B8')) by lia.
          symmetry. apply low32_small.
          pose proof (Z.mod_pos_bound (Z.shiftl (e_origPtr e) (8 - bw_live B8')) 4294967296 ltac:(lia)) as MB.
          pose proof (BzLemmasT.lor_lt_pow2 (bw_buff B8') ((Z.shiftl (e_origPtr e) (8 - bw_live B8')) mod 4294967296) 32) as LB.
          change (2 ^ 32)%Z with 4294967296%Z in LB. lia. }
        replace (bw_live B8' + 24)%Z with (bw_live (bsW B8 24 (e_origPtr e))) in EH2r by (rewrite F9l; reflexivity).
        replace (bw_numZ B8') with (bw_numZ (bsW B8 24 (e_origPtr e))) in EH1r by (rewrite F9n; reflexivity).
        rewrite <- (zbl_same_bytes (e_arr2 e) nblock B8' (bsW B8 24 (e_origPtr e)) F9n F9z) in AR2.
        eapply K;
          [ unfold EHEAD1n, EHEAD1; cbn [removelast app]; cbn_est; rewrite Gsort, Gzb; exact EH1r
          | unfold S0_cmp_cbT.EH2b, EHEAD2; cbn_est; rewrite Gbs; exact EH2r
          | unfold S0_cmp_cbT.AR2b; exact AR2
          | exact MI| exact ST| exact SL| exact (PT3 _ _ HP MU WM)| unfold cbH_W; exact MU| exact WM| exact OK9| lia].
      }
      (* [comment removed for export] *)
      wstep; if_cases Kg; zify_cond_z Kg.
      - assert (E8 : B8' = B8).
        { subst B8'. unfold BS_FUEL. rewrite bs_needw_S. replace (8 <=? bw_live B8)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        try rewrite (sx32_of_Z (e_origPtr e)) by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JN2 mm _ _ _ _ _ _) end; rewrite ?E8, ?F8l;
          [st_eq| lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact SL| exact MU| exact WM].
      - (* [comment removed for export] *)
        pose proof EH1 as EH1r. unfold S0_cmp_cbT.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r.
        pose proof EH2 as EH2r. unfold S0_cmp_cbT.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r.
        wstep. wstep. clear EH1r EH2r.
        try rewrite (sx32_of_Z (bw_numZ B8)) by (bz_params; lia).
        try rewrite (sx32_of_Z (e_origPtr e)) by lia.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m8t end.
        eapply (S0_cb_flushB BS_FUEL Q B8 m8t m8t); [exact OK8| lia| change (Z.of_nat BS_FUEL) with 5%Z; lia| bz_params; change (Z.of_nat BS_FUEL) with 5%Z; lia
          | rewrite low32_sx32, low32_lit; apply low32_small; lia| exact EH1| exact EH2| exact AR2| exact MI| apply munch_refl| apply wmono_refl|].
        clear EH1 EH2 AR2 MI.
        intros m9 a2' a3' a5' a6' a7'. cbv zeta. fold B8'. intros LVb OKb' NZb' EH1 EH2 AR2 MI MU9 WM9. change (Z.of_nat BS_FUEL) with 5%Z in NZb'.
        unfold S0_cmp_cbT.cbT_W in MU9. transport_after_call s0segs m8t m9 MU9 WM9. clear MU9 WM9.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JN2 mm _ _ _ _ _ _) end;
          [st_eq| lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact SL| exact MU| exact WM]. }
    (* [comment removed for export] *)
    pose proof EH2 as EH2r. unfold S0_cmp_cbT.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r.
    wstep. wstep. clear EH2r.
    wstep; if_cases Kf; zify_cond_z Kf.
    - (* [comment removed for export] *)
      assert (E7 : B7' = B7).
      { subst B7'. unfold BS_FUEL. rewrite bs_needw_S. replace (8 <=? bw_live B7)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      try rewrite (sx32_of_Z (bw_live B7)) by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JN mm _ _ _ _ _ _) end; rewrite ?E7;
        [st_eq| lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact SL| exact MU| exact WM].
    - (* [comment removed for export] *)
      pose proof EH2 as EH2r. unfold S0_cmp_cbT.EH2b, EHEAD2 in EH2r. cbn_est_in EH2r. rewrite Gbs in EH2r.
      pose proof EH1 as EH1r. unfold S0_cmp_cbT.EH1b, EHEAD1 in EH1r. cbn_est_in EH1r.
      wstep. wstep. wstep. clear EH2r EH1r.
      try rewrite (sx32_of_Z (bw_numZ B7)) by (bz_params; lia).
      eapply (S0_cb_flushA BS_FUEL Q B7 m7 m7); [exact OK7| lia| change (Z.of_nat BS_FUEL) with 5%Z; lia| bz_params; change (Z.of_nat BS_FUEL) with 5%Z; lia
        | rewrite low32_sx32, low32_lit; apply low32_small; lia| exact EH1| exact EH2| exact AR2| exact MI| apply munch_refl| apply wmono_refl|].
      clear EH1 EH2 AR2 MI.
      intros m8 a0' a1' a3' a4' a5' a6'. cbv zeta. fold B7'. intros LV' OK' NZ' EH1 EH2 AR2 MI MU8 WM8. change (Z.of_nat BS_FUEL) with 5%Z in NZ'.
      unfold S0_cmp_cbT.cbT_W in MU8. transport_after_call s0segs m7 m8 MU8 WM8. clear MU8 WM8.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (JN mm _ _ _ _ _ _) end;
        [st_eq| lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact SL| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Time Qed.
End CBH3.

End ACeilS1.
