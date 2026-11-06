(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpSess CmpSessB CmpFsKit0 AsanKit AsanCut AsanCutB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0_cmp_sdV.
Local Open Scope Z_scope.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition hc_slots (E SHE : Z) (v64 v72 v80 v88 : word) : list cell :=
  [C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 (E + 128)); C8 (Z_to_bv 64 (18446744073709551615 - (E + 128)));
   C8 (Z_to_bv 64 (E + 12)); C8 (Z_to_bv 64 (SHE + 1)); C8 v64; C8 v72; C8 v80; C8 v88; C8 (Z_to_bv 64 (E + 64)); C8 (Z_to_bv 64 (SHE + 14)); C8 (Z_to_bv 64 (SHE + 13));
   C8 (Z_to_bv 64 (E + 112)); C8 (Z_to_bv 64 (E + 16)); C8 (Z_to_bv 64 (E + 108)); C8 (Z_to_bv 64 (SHE + 1)); C8 (Z_to_bv 64 (E + 8)); C8 (Z_to_bv 64 (E + 96));
   C8 (Z_to_bv 64 (E + 92)); C8 (Z_to_bv 64 (E + 648))].
(* [comment removed for export] *)
Definition hc_slotsL (E SHE : Z) (v64 v72 : word) : list cell :=
  hc_slots E SHE v64 v72 (Z_to_bv 64 (SHE + -2147450872)) (Z_to_bv 64 (SHE + -2147450799)).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition HSAVED (s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
  [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Definition hkin (z0 z : zstrm) : Z := z_avail_in z0 - z_avail_in z.
Definition HPURE (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (cx : cctx) (on : Z) (z0 : zstrm) (pl : list byte) (g : eg) (e : est) (z : zstrm) : Prop :=
  HCXB cx on g e z /\ z_in z = map bv_unsigned (skipn (Z.to_nat (hkin z0 z)) pl) /\ 0 <= hkin z0 z.

(* [comment removed for export] *)
Definition hc_prep_a (e : est) : est :=
  EST (e_mode e) (e_state e) (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) 0 0 (e_nInUse e) (e_inUse e) (e_unseqToSeq e)
      (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) crc_init (e_combinedCRC e) (e_blockNo e)
      (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e) (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
(* [comment removed for export] *)
Lemma hc_prep_of_a : forall e, hc_prep e =
  EST (e_mode e) BZ_S_INPUT (e_avail_in_expect e) (e_arr1 e) (e_arr2 e) (e_ftab e) (e_origPtr e)
      (e_state_in_ch e) (e_state_in_len e) 0 0 (e_nInUse e) (inUse_clear (e_inUse e) 0 256) (e_unseqToSeq e)
      (BW (bw_buff (e_bw e)) (bw_live (e_bw e)) 0 znew) crc_init (e_combinedCRC e) (e_blockNo e + 1)
      (e_nMTF e) (e_mtfFreq e) (e_selector e) (e_selectorMtf e) (e_len e) (e_code e) (e_rfreq e) (e_len_pack e).
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition hc_after_cb (e : est) (il : bool) : est :=
  let '(e', _) := compressBlock e il znew in est_set_modes e' (e_mode e') BZ_S_OUTPUT (e_avail_in_expect e').
Lemma hc_cbR_after : forall e, hc_cbR e = hc_after_cb e false. Proof. reflexivity. Qed.
Lemma hc_cbF_after : forall e, hc_cbF e = hc_after_cb (hc_flush e) (e_mode (hc_flush e) =? BZ_M_FINISHING). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition hc_aft (e : est) (z : zstrm) (pout : bool) : est * zstrm * bool * bool :=
  if (e_state_out_pos e <? bw_numZ (e_bw e))%Z then (e, z, pout, true) else
  if ((e_mode e =? BZ_M_FINISHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool then (e, z, pout, true) else
  let e := hc_prep e in
  if ((e_mode e =? BZ_M_FLUSHING)%Z && (e_avail_in_expect e =? 0)%Z && isempty_RL_e e)%bool then (e, z, pout, true)
  else (e, z, pout, false).
Lemma hc_out_aft : forall e z pout,
  hc_out e z pout = let '(e1, z1, q1) := copy_output (Z.to_nat (z_avail_out z) + 1)%nat e z pout in hc_aft e1 z1 q1.
Proof. intros. unfold hc_out, hc_aft. destruct (copy_output _ e z pout) as [[e1 z1] q1]. reflexivity. Qed.

(* [comment removed for export] *)
Lemma copy_output_frame : forall f e z p, fst (fst (copy_output f e z p)) = est_set_outpos e (e_state_out_pos (fst (fst (copy_output f e z p)))).
Proof.
  induction f as [|f IH]; intros e z p; cbn [copy_output]; [destruct e; reflexivity|].
  destruct (z_avail_out z =? 0)%Z; [destruct e; reflexivity|]. destruct (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z; [destruct e; reflexivity|].
  destruct (inc64 (z_tout_lo z) (z_tout_hi z)) as [lo hi]. rewrite IH at 1. reflexivity.
Qed.

(* [comment removed for export] *)
Definition u8roW (W : list ivl) (m0 : amem) (A : Z) (bs : list byte) : Prop := forall m : amem, munch W m0 m -> u8ro b0segs m A bs.
Lemma u8roW_intro : forall W (m0 : amem) A bs, u8ro b0segs m0 A bs -> disjoint_from W A (Z.of_nat (length bs)) -> u8roW W m0 A bs.
Proof. intros W m0 A bs H D m MU. exact (u8ro_transport b0segs W m0 m A bs H MU D). Qed.
(* [comment removed for export] *)

Definition acimgW (W : list ivl) (m0 : amem) (sv : word) : Prop := forall m : amem, munch W m0 m -> acimg_mem B0C m sv.
Lemma acimgW_intro : forall W (m0 : amem) sv, acimg_mem B0C m0 sv ->
  disjoint_from W 0xcda98 8 -> disjoint_from W 0xcdab0 8 -> disjoint_from W 0xccd30 8 -> disjoint_from W 0xd13e0 1024 -> acimgW W m0 sv.
Proof.
  intros W m0 sv (H1 & H2 & H3 & H4) D1 D2 D3 D4 m MU. unfold acimg_mem. cbn [aci_segs aci_c B0C ci_segs ci_got ci_stderrp ci_crc ci_crcx] in *.
  split; [exact (ro_cells_transport b0segs W m0 m _ _ H1 MU D1)|].
  split; [exact (ro_cells_transport b0segs W m0 m _ _ H2 MU D2)|].
  split; [exact (ro_cells_transport b0segs W m0 m _ _ H3 MU D3)|].
  exact (A0_cmp_sdV.rw_cells_munch b0segs W m0 m _ _ H4 MU D4).
Qed.
Lemma acimgW_sub : forall W W' (m0 m1 : amem) sv, acimgW W m0 sv -> munch W m0 m1 -> sub_fp W' W -> acimgW W' m1 sv.
Proof. intros W W' m0 m1 sv H MU SF m MU'. apply H. apply (munch_trans W m0 m1 m MU). exact (munch_weaken W' W m1 m SF MU'). Qed.

(* [comment removed for export] *)
Definition u8arrW (W : list ivl) (m0 : amem) (A : Z) (bs : list byte) : Prop := forall m : amem, munch W m0 m -> u8arr b0segs m A bs.
Lemma u8arrW_intro : forall W (m0 : amem) A bs, u8arr b0segs m0 A bs -> disjoint_from W A (Z.of_nat (length bs)) -> u8arrW W m0 A bs.
Proof. intros W m0 A bs H D m MU. exact (A0_cmp_sdV.u8arr_munch b0segs W m0 m A bs H MU D). Qed.
(* [comment removed for export] *)

End ACeilS1.
