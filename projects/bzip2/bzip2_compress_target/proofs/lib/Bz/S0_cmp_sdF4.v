(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Tac WalkLib.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SegsS0 StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSD CmpCutSD0 CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith4 BzCLemmasSd BzCLemmasSd2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasSd2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSD CmpCutSD0 CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith4 BzCLemmasSd BzCLemmasSd2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasSd2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSdStep.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSdFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_sdF.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
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
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
#[local] Ltac2 Set RangeFast.RF.rc_skip_hyps := fun () => [@USP2].   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac CmpSdKit.pstep_with SC p q n k ::= CmpSdStep.pstep_with_fast SC p q n k.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac CmpSdKit.same_code_tac ::= CmpSdFast.same_code_tac_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDF.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.

  (* [comment removed for export] *)
  Notation RL ra a0 a1 a2 s2 s3 s4 s9 s10 t2 t3 t4 t5 t6 :=
    (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 a2 (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1))
         s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_len5_flush : forall (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t2 a0 a1 s2 s3 s9 s10 t3 t6 : word) (xb t40 t50 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' t5' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 xb' (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1)) s2 s3 (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 (Z_to_bv 64 (bw_live b1)) t5' t6)
            F (Z_to_bv 64 0x178d0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 xb (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1)) s2 s3 (Z_to_bv 64 (bw_numZ b)) (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t40 t50 t6)
            F (Z_to_bv 64 0x17898) fc None m (seg_rom s0segs)).
  Proof.
    intros Q f. induction f as [|f IH]; intros b m ra t2 a0 a1 s2 s3 s9 s10 t3 t6 xb t40 t50 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned xb / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned xb / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange xb). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned xb) (bw_buff b)); [| pose proof (word_urange xb); lia | exact X4 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' t5' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma S0_ud_flush : forall (q : Z) (SC : same_code s0segs q 0x17904 14) (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t2 a0 a1 s3 s9 s10 t3 t4 t6 : word) (xb s20 t50 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' s2' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 xb' (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1)) s2' s3 (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (bw_live b1)) t6)
            F (Z_to_bv 64 (q + 56)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 xb (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1)) s20 s3 (Z_to_bv 64 (bw_numZ b)) (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 t50 t6)
            F (Z_to_bv 64 q) fc None m (seg_rom s0segs)).
  Proof.
    intros q SC Q f. induction f as [|f IH]; intros b m ra t2 a0 a1 s3 s9 s10 t3 t4 t6 xb s20 t50 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    pstep SC. pstep SC. pstep SC.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    pstep SC.
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned xb / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    pstep SC. pstep SC. pstep SC. pstep SC. pstep SC. pstep SC. pstep SC. pstep SC. pstep SC.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned xb / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange xb). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned xb) (bw_buff b)); [| pose proof (word_urange xb); lia | exact X4 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    pstep SC; if_cases Kc; zify_cond_z Kc. pcnorm q.
    - enter_with (IH (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' s2' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma SCud_a : same_code s0segs 0x17904 0x17904 14. Proof. same_code_tac. Qed.
  Lemma SCud_b : same_code s0segs 0x17968 0x17904 14. Proof. same_code_tac. Qed.
  Lemma S0_len1_flush : forall (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t2 a0 a1 s2 s3 s9 s10 t3 t4 : word) (xb t50 t60 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' t6' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 xb' (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1)) s2 s3 (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (bw_live b1)) t6')
            F (Z_to_bv 64 0x17a00) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 xb (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1)) s2 s3 (Z_to_bv 64 (bw_numZ b)) (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 t50 t60)
            F (Z_to_bv 64 0x179c8) fc None m (seg_rom s0segs)).
  Proof.
    intros Q f. induction f as [|f IH]; intros b m ra t2 a0 a1 s2 s3 s9 s10 t3 t4 xb t50 t60 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned xb / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned xb / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange xb). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned xb) (bw_buff b)); [| pose proof (word_urange xb); lia | exact X4 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' t6' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_up_tail : forall (Q : machine_state -> Prop) (t i curr tgt : Z) (f : nat) (b b1 : bw) (m : word -> option byte)
      (ra a0 s3 s9 s10 xb : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) -> (1 <= curr < tgt)%Z -> (tgt - curr <= Z.of_nat (S f))%Z ->
    let r := sm_put_up f (bsW b 2 2) (curr + 1) tgt in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ (fst r) <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z -> MD b1 m ->
    (forall (Q : machine_state -> Prop) (t i curr tgt : Z) (b : bw) (m : word -> option byte) (ra a0 s3 s9 s10 xb : word),
      (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) ->
      (1 <= curr < tgt)%Z -> (tgt - curr <= Z.of_nat f)%Z ->
      let r := sm_put_up f b curr tgt in
      bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ (fst r) <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
      (forall m' (s3' xb' : word),
          MD (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z -> snd r = tgt ->
          evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' (Z_to_bv 64 tgt) s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 tgt) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                            F (Z_to_bv 64 0x17960) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb (Z_to_bv 64 tgt) s3 (Z_to_bv 64 (bw_numZ b)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                        F (Z_to_bv 64 0x17900) fc None m (seg_rom s0segs))) ->
    (forall m' (s3' xb' : word),
        MD (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z -> snd r = tgt ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' (Z_to_bv 64 tgt) s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 tgt) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                          F (Z_to_bv 64 0x17960) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb (Z_to_bv 64 tgt) s3 (Z_to_bv 64 (bw_numZ b1)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                      F (Z_to_bv 64 0x17940) fc None m (seg_rom s0segs)).
  Proof.
    intros Q t i curr tgt f b b1 m ra a0 s3 s9 s10 xb Ht Hi Htgt Hc Hf. cbv zeta. intros OK Eb1 NL L1 XB MEM IHn K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    pose proof (put_up_NZM f (bsW b 2 2) (curr + 1) tgt) as NZ1. unfold NZM in NZ1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 2 2 = BW (Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296)) (bw_live b1 + 2) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 2 2)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.mod_small (30 - bw_live b1) 32) in * by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296))%Z.
    { rewrite (low32_or_shifted 2 _ xb (bw_buff b1) XB) by lia. replace (30 - bw_live b1)%Z with (32 - bw_live b1 - 2)%Z by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    assert (XB2 : (bv_unsigned (Z_to_bv 64 (Z.lor (bv_swrap 32 (Z.shiftl 2 (30 - bw_live b1)) mod 18446744073709551616) (bv_unsigned xb))) mod 4294967296
                   = bw_buff (bsW b 2 2))%Z).
    { rewrite EBW. cbn [bw_buff]. rewrite (low32_or_shifted 2 _ xb (bw_buff b1) XB) by lia.
      replace (30 - bw_live b1)%Z with (32 - bw_live b1 - 2)%Z by lia. apply low32_small. exact XR. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      destruct f as [|f']; [exfalso; lia|].
      enter_with (IHn Q t i (curr + 1)%Z tgt (bsW b 2 2) _ _ _ _ _ _ _); 
        [st_eq; rewrite ?EBW; reflexivity| exact Ht| exact Hi| exact Htgt| lia| lia| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact NL| exact XB2| rewrite EBW; closeMD| exact K].
    - (* [comment removed for export] *)
      assert (ER : sm_put_up f (bsW b 2 2) (curr + 1) tgt = (bsW b 2 2, (curr + 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_up_S. replace (curr + 1 <? tgt)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ER in K. cbn [fst snd] in K.
      enter_with (K _ _ _); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact XB2| lia].
  Qed.

  Lemma S0_up_loop : forall (f : nat) (Q : machine_state -> Prop) (t i curr tgt : Z) (b : bw) (m : word -> option byte)
      (ra a0 s3 s9 s10 xb : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) ->
    (1 <= curr < tgt)%Z -> (tgt - curr <= Z.of_nat f)%Z ->
    let r := sm_put_up f b curr tgt in
    bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ (fst r) <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (s3' xb' : word),
        MD (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z -> snd r = tgt ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' (Z_to_bv 64 tgt) s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 tgt) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                          F (Z_to_bv 64 0x17960) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb (Z_to_bv 64 tgt) s3 (Z_to_bv 64 (bw_numZ b)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                      F (Z_to_bv 64 0x17900) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; [lia|].
    intros Q t i curr tgt b m ra a0 s3 s9 s10 xb Ht Hi Htgt Hc Hf. cbv zeta. intros OK L25 NL XB MEM K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    rewrite put_up_S in NL, K. replace (curr <? tgt)%Z with true in NL, K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (put_up_NZM f (bsW b 2 2) (curr + 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 2 2) as NZ0. unfold NZM in NZ0.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - eapply (S0_up_tail Q t i curr tgt f b b m); [exact Ht| exact Hi| exact Htgt| lia| lia| exact OK| | exact NL| lia| exact XB| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - eapply (S0_ud_flush 0x17904 SCud_a Q BS_FUEL b m); [exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
      { pose proof (bsW_bytes b 2 2) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' xb' s2' Eb1 MEM' XB' L1. change (Z_to_bv 64 (0x17904 + 56)) with (Z_to_bv 64 0x1793c).
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OKb1 & _ & _). rewrite <- Eb1 in OKb1. cps_destruct OKb1 as (OKb1 & OKl1 & OKn1).
      clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI. openMD MEM'.
      (* [comment removed for export] *)
      pose proof (ovb_read1 s0segs m' (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + i) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
      wstep. clear RD. cbv beta. rewrite <- Htgt. rewrite (unsigned_lit8 tgt) by lia.
      eapply (S0_up_tail Q t i curr tgt f b b1 m'); [exact Ht| exact Hi| exact Htgt| lia| lia| exact OK| exact Eb1| exact NL| exact L1| exact XB'| closeMD| exact IH| exact K].
  Qed.
End SDF.

End ACeilS1.
End S0_cmp_sdF.


From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasSd2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
Module S0_cmp_sdF2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdF4.S0_cmp_sdF.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
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
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDF2.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.

  Notation RL ra a0 a1 a2 s2 s3 s4 s9 s10 t2 t3 t4 t5 t6 :=
    (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 a2 (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1))
         s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation FL f := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A) (only parsing).
  Notation LP f := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A HA HG LENF) (only parsing).

  (* [comment removed for export] *)
  Lemma S0_down_tail : forall (Q : machine_state -> Prop) (t i curr tgt : Z) (f : nat) (b b1 : bw) (m : word -> option byte)
      (ra a0 s3 s9 s10 xb : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) -> (tgt < curr <= 17)%Z -> (curr - tgt <= Z.of_nat (S f))%Z ->
    let r := sm_put_down f (bsW b 2 3) (curr - 1) tgt in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ (fst r) <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z -> MD b1 m ->
    (forall (Q : machine_state -> Prop) (t i curr tgt : Z) (b : bw) (m : word -> option byte) (ra a0 s3 s9 s10 xb : word),
      (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) ->
      (tgt < curr <= 17)%Z -> (curr - tgt <= Z.of_nat f)%Z ->
      let r := sm_put_down f b curr tgt in
      bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ (fst r) <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
      (forall m' (s3' xb' : word),
          MD (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z -> snd r = tgt ->
          evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' (Z_to_bv 64 tgt) s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 tgt) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                            F (Z_to_bv 64 0x179c4) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb (Z_to_bv 64 tgt) s3 (Z_to_bv 64 (bw_numZ b)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                        F (Z_to_bv 64 0x17964) fc None m (seg_rom s0segs))) ->
    (forall m' (s3' xb' : word),
        MD (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z -> snd r = tgt ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' (Z_to_bv 64 tgt) s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 tgt) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                          F (Z_to_bv 64 0x179c4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb (Z_to_bv 64 tgt) s3 (Z_to_bv 64 (bw_numZ b1)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                      F (Z_to_bv 64 0x179a4) fc None m (seg_rom s0segs)).
  Proof.
    intros Q t i curr tgt f b b1 m ra a0 s3 s9 s10 xb Ht Hi Htgt Hc Hf. cbv zeta. intros OK Eb1 NL L1 XB MEM IHn K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    pose proof (put_down_NZM f (bsW b 2 3) (curr - 1) tgt) as NZ1. unfold NZM in NZ1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 2 3 = BW (Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296)) (bw_live b1 + 2) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 2 3)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.mod_small (30 - bw_live b1) 32) in * by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296))%Z.
    { rewrite (low32_or_shifted 3 _ xb (bw_buff b1) XB) by lia. replace (30 - bw_live b1)%Z with (32 - bw_live b1 - 2)%Z by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    assert (XB2 : (bv_unsigned (Z_to_bv 64 (Z.lor (bv_swrap 32 (Z.shiftl 3 (30 - bw_live b1)) mod 18446744073709551616) (bv_unsigned xb))) mod 4294967296
                   = bw_buff (bsW b 2 3))%Z).
    { rewrite EBW. cbn [bw_buff]. rewrite (low32_or_shifted 3 _ xb (bw_buff b1) XB) by lia.
      replace (30 - bw_live b1)%Z with (32 - bw_live b1 - 2)%Z by lia. apply low32_small. exact XR. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      destruct f as [|f']; [exfalso; lia|].
      enter_with (IHn Q t i (curr - 1)%Z tgt (bsW b 2 3) _ _ _ _ _ _ _); 
        [st_eq; rewrite ?EBW; reflexivity| exact Ht| exact Hi| exact Htgt| lia| lia| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact NL| exact XB2| rewrite EBW; closeMD| exact K].
    - (* [comment removed for export] *)
      assert (ER : sm_put_down f (bsW b 2 3) (curr - 1) tgt = (bsW b 2 3, (curr - 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_down_S. replace (tgt <? curr - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ER in K. cbn [fst snd] in K.
      enter_with (K _ _ _); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact XB2| lia].
  Qed.

  Lemma S0_down_loop : forall (f : nat) (Q : machine_state -> Prop) (t i curr tgt : Z) (b : bw) (m : word -> option byte)
      (ra a0 s3 s9 s10 xb : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) ->
    (tgt < curr <= 17)%Z -> (curr - tgt <= Z.of_nat f)%Z ->
    let r := sm_put_down f b curr tgt in
    bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ (fst r) <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (s3' xb' : word),
        MD (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 9)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z -> snd r = tgt ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' (Z_to_bv 64 tgt) s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 tgt) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live (fst r))) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                          F (Z_to_bv 64 0x179c4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb (Z_to_bv 64 tgt) s3 (Z_to_bv 64 (bw_numZ b)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 (E + 37708 + 258 * t + i)))
                      F (Z_to_bv 64 0x17964) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; [lia|].
    intros Q t i curr tgt b m ra a0 s3 s9 s10 xb Ht Hi Htgt Hc Hf. cbv zeta. intros OK L25 NL XB MEM K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    rewrite put_down_S in NL, K. replace (tgt <? curr)%Z with true in NL, K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (put_down_NZM f (bsW b 2 3) (curr - 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 2 3) as NZ0. unfold NZM in NZ0.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - eapply (S0_down_tail Q t i curr tgt f b b m); [exact Ht| exact Hi| exact Htgt| lia| lia| exact OK| | exact NL| lia| exact XB| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - eapply (FL S0_ud_flush 0x17968 SCud_b Q BS_FUEL b m); [exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
      { pose proof (bsW_bytes b 2 3) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' xb' s2' Eb1 MEM' XB' L1. change (Z_to_bv 64 (0x17968 + 56)) with (Z_to_bv 64 0x179a0).
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OKb1 & _ & _). rewrite <- Eb1 in OKb1. cps_destruct OKb1 as (OKb1 & OKl1 & OKn1).
      clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI. openMD MEM'.
      (* [comment removed for export] *)
      pose proof (ovb_read1 s0segs m' (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + i) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
      wstep. clear RD. cbv beta. rewrite <- Htgt. rewrite (unsigned_lit8 tgt) by lia.
      eapply (S0_down_tail Q t i curr tgt f b b1 m'); [exact Ht| exact Hi| exact Htgt| lia| lia| exact OK| exact Eb1| exact NL| exact L1| exact XB'| closeMD| exact IH| exact K].
  Qed.
End SDF2.

End ACeilS1.
End S0_cmp_sdF2.


From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCLemmasSd2. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
Module S0_cmp_sdF3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdF4.S0_cmp_sdF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdF4.S0_cmp_sdF2.
 Unset Lia Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
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
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDF3.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.

  Notation RL ra a0 a1 a2 s2 s3 s4 s9 s10 t2 t3 t4 t5 t6 :=
    (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 a2 (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1))
         s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation FL f := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A) (only parsing).
  Notation LP f := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A HA HG LENF) (only parsing).

  (* [comment removed for export] *)
  Definition LROW (n : nat) (t : Z) : Prop :=
    forall (Q : machine_state -> Prop) (i curr : Z) (b : bw) (m : word -> option byte) (ra a0 s2 s3 s9 s10 t6 xb : word),
      (0 <= t < nG)%Z -> (i + Z.of_nat n = A)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (1 <= curr <= 17)%Z ->
      let r := sm_put_lens_row n b LENA t i curr in
      bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ (fst r) <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
      MS3 cx g e nG nSel usp sv W m0 i16 b m ->
      (forall m' (s2' s3' t3' t6' xb' : word),
          MS3 cx g e nG nSel usp sv W m0 i16 (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 10)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z ->
          evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' s2' s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) t3' (Z_to_bv 64 A) (Z_to_bv 64 (bw_live (fst r))) t6')
                            F (Z_to_bv 64 0x17a14) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb s2 s3 (Z_to_bv 64 (bw_numZ b)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live b)) t6)
                        F (Z_to_bv 64 0x178f4) fc None m (seg_rom s0segs)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_lens_fin : forall (Q : machine_state -> Prop) (t i tgt : Z) (n : nat) (bo b1 : bw) (m : word -> option byte)
      (ra a0 s2 s3 s9 s10 t6 xb : word),
    (0 <= t < nG)%Z -> (i + Z.of_nat (S n) = A)%Z -> (0 <= i)%Z -> (1 <= tgt <= 17)%Z ->
    let r := sm_put_lens_row n (bsW bo 1 0) LENA t (i + 1) tgt in
    bw_ok bo -> b1 = bs_needw BS_FUEL bo -> (bw_numZ (fst r) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z -> MD b1 m ->
    LROW n t ->
    (forall m' (s2' s3' t3' t6' xb' : word),
        MD (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 10)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' s2' s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) t3' (Z_to_bv 64 A) (Z_to_bv 64 (bw_live (fst r))) t6')
                          F (Z_to_bv 64 0x17a14) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb s2 s3 (Z_to_bv 64 (bw_numZ b1)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 tgt) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live b1)) t6)
                      F (Z_to_bv 64 0x17a00) fc None m (seg_rom s0segs)).
  Proof.
    intros Q t i tgt n bo b1 m ra a0 s2 s3 s9 s10 t6 xb Ht Hi Hi0 Htg. cbv zeta. intros OK Eb1 NL XB MEM IHn K.
    pose proof (put_lens_row_NZM n (bsW bo 1 0) LENA t (i + 1) tgt) as NZ1. unfold NZM in NZ1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live bo) 8 ltac:(lia)) as MB.
    assert (EBW : bsW bo 1 0 = BW (bw_buff b1) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1)).
    { unfold bsW. rewrite <- Eb1. f_equal. change 4294967296%Z with M32. rewrite lor_shl0. reflexivity. }
    assert (OK2 : bw_ok (bsW bo 1 0)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat (bw_buff b1). { rewrite XB. symmetry. apply Z.mod_small. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IHn Q (i + 1)%Z tgt (bsW bo 1 0) _ _ _ _ _ _ _ _ xb);
        [st_eq; rewrite ?EBW; reflexivity| exact Ht| lia| lia| lia| exact Htg| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact NL| rewrite EBW; cbn [bw_buff]; exact XB| rewrite EBW; closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_lens_row fst snd] in K.
      enter_with (K _ _ _ _ _ xb); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| rewrite EBW; cbn [bw_live]; lia| rewrite EBW; cbn [bw_buff]; exact XB].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_lens_pre : forall (Q : machine_state -> Prop) (t i tgt : Z) (n : nat) (bo : bw) (m : word -> option byte)
      (ra a0 s3 s9 s10 t6 xb : word),
    (0 <= t < nG)%Z -> (i + Z.of_nat (S n) = A)%Z -> (0 <= i)%Z -> (1 <= tgt <= 17)%Z ->
    let r := sm_put_lens_row n (bsW bo 1 0) LENA t (i + 1) tgt in
    bw_ok bo -> (bw_live bo <= 25)%Z -> (bw_numZ (fst r) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff bo)%Z -> MD bo m ->
    LROW n t ->
    (forall m' (s2' s3' t3' t6' xb' : word),
        MD (fst r) m' -> bw_ok (fst r) -> (bw_live (fst r) <= 10)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff (fst r))%Z ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' s2' s3' (Z_to_bv 64 (bw_numZ (fst r))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) t3' (Z_to_bv 64 A) (Z_to_bv 64 (bw_live (fst r))) t6')
                          F (Z_to_bv 64 0x17a14) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb (Z_to_bv 64 tgt) s3 (Z_to_bv 64 (bw_numZ bo)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 tgt) (Z_to_bv 64 i) (Z_to_bv 64 (bw_live bo)) t6)
                      F (Z_to_bv 64 0x179c4) fc None m (seg_rom s0segs)).
  Proof.
    intros Q t i tgt n bo m ra a0 s3 s9 s10 t6 xb Ht Hi Hi0 Htg. cbv zeta. intros OK L25 NL XB MEM IHn K.
    pose proof (put_lens_row_NZM n (bsW bo 1 0) LENA t (i + 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM bo 1 0) as NZ0. unfold NZM in NZ0.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (S0_lens_fin Q t i tgt n bo bo m); [st_eq| exact Ht| lia| lia| exact Htg| exact OK| | exact NL| exact XB| closeMD| exact IHn| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live bo)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FL S0_len1_flush Q BS_FUEL bo m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
      { pose proof (bsW_bytes bo 1 0) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' xb' t6' Eb1 MEM' XB' L1.
      eapply (S0_lens_fin Q t i tgt n bo b1 m'); [exact Ht| lia| lia| exact Htg| exact OK| exact Eb1| exact NL| exact XB'| exact MEM'| exact IHn| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_lens_inner : forall (n : nat) (t : Z), LROW n t.
  Proof.
    induction n as [|n IH]; intros t; unfold LROW; [lia|].
    intros Q i curr b m ra a0 s2 s3 s9 s10 t6 xb Ht Hi Hi0 _ Hc. cbv zeta. intros OK L25 NL XB MEM K.
    destruct (LENF t i Ht ltac:(lia)) as [ZD ZR].
    rewrite put_lens_row_S in NL, K. cbv zeta in NL, K.
    set (tgt := zget LENA (258 * t + i)) in *.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    (* [comment removed for export] *)
    wstep.
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + i) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. fold tgt. rewrite (unsigned_lit8 tgt) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (EU : sm_put_up 40 b curr tgt = (b, curr)).
      { change 40%nat with (S 39). rewrite put_up_S. replace (curr <? tgt)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite EU in NL, K.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        assert (ED : sm_put_down 40 b curr tgt = (b, curr)).
        { change 40%nat with (S 39). rewrite put_down_S. replace (tgt <? curr)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
        rewrite ED in NL, K. assert (Ec : curr = tgt) by lia. subst curr.
        enter_with (S0_lens_pre Q t i tgt n b m); [st_eq| exact Ht| lia| lia| lia| exact OK| lia| exact NL| exact XB| closeMD| exact (IH t)| exact K].
      + (* [comment removed for export] *)
        destruct (sm_put_down 40 b curr tgt) as [b2 c2] eqn:ED.
        pose proof (put_lens_row_NZM n (bsW b2 1 0) LENA t (i + 1) c2) as NZ1. unfold NZM in NZ1.
        pose proof (bsW_NZM b2 1 0) as NZ0. unfold NZM in NZ0.
        enter_with (LP S0_down_loop 40%nat Q t i curr tgt b m); [st_eq| exact Ht| lia| reflexivity| lia| cbn; lia| exact OK| lia| rewrite ED; cbn [fst]; lia| exact XB| closeMD|].
        rewrite ED. cbn [fst snd]. intros m' s3' xb' MEM' OK' L9 XB' ->.
        eapply (S0_lens_pre Q t i tgt n b2 m'); [exact Ht| lia| lia| lia| exact OK'| lia| exact NL| exact XB'| exact MEM'| exact (IH t)| exact K].
    - (* [comment removed for export] *)
      destruct (sm_put_up 40 b curr tgt) as [b1 c1] eqn:EU.
      pose proof (put_down_NZM 40 b1 c1 tgt) as NZd. unfold NZM in NZd.
      destruct (sm_put_down 40 b1 c1 tgt) as [b2 c2] eqn:ED.
      pose proof (put_lens_row_NZM n (bsW b2 1 0) LENA t (i + 1) c2) as NZ1. unfold NZM in NZ1. cbn [fst] in NZd, NZ1.
      pose proof (bsW_NZM b2 1 0) as NZ0. unfold NZM in NZ0.
      enter_with (LP S0_up_loop 40%nat Q t i curr tgt b m); [st_eq| exact Ht| lia| reflexivity| lia| cbn; lia| exact OK| lia| rewrite EU; cbn [fst]; lia| exact XB| closeMD|].
      rewrite EU. cbn [fst snd]. intros m' s3' xb' MEM' OK' L9 XB' Ec1. subst c1.
      assert (ED' : (b2, c2) = (b1, tgt)).
      { rewrite <- ED. change 40%nat with (S 39). rewrite put_down_S. replace (tgt <? tgt)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      injection ED' as -> ->.
      clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI. cps_pose OK' as (OKb' & OKl' & OKn'). openMD MEM'.
      (* [comment removed for export] *)
      wstep; if_cases Kc2; zify_cond_z Kc2; [| exfalso; lia].
      enter_with (S0_lens_pre Q t i tgt n b1 m'); [st_eq| exact Ht| lia| lia| lia| exact OK'| lia| exact NL| exact XB'| closeMD| exact (IH t)| exact K].
  Qed.
End SDF3.

End ACeilS1.
End S0_cmp_sdF3.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdF4.S0_cmp_sdF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdF4.S0_cmp_sdF2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdF4.S0_cmp_sdF3.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.   (* [comment removed for export] *)
Local Ltac mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | mem_after_store_fast ].
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | sf_unhide; unhide_disj; first [ zify_prune_neg; Zify.zify; xlia zchecker | zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepVS.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDF4.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1008 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG nSel : Z) (sv : word) (W : s3w) (m0 : word -> option byte) (i16 : list byte).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.

  Notation RL ra a0 a1 a2 s2 s3 s4 s9 s10 t2 t3 t4 t5 t6 :=
    (mkR ra sp gp tp (Z_to_bv 64 30) (Z_to_bv 64 2) t2 (Z_to_bv 64 E) (Z_to_bv 64 3) a0 a1 a2 (Z_to_bv 64 258) (Z_to_bv 64 8) (Z_to_bv 64 15) (Z_to_bv 64 27) (Z_to_bv 64 (-1))
         s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation FL f := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A) (only parsing).
  Notation LP f := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A HA HG LENF) (only parsing).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_lens5_tail : forall (Q : machine_state -> Prop) (t curr : Z) (b b1 : bw) (m : word -> option byte)
      (ra a0 s2 s3 s9 s10 t5 t6 xb : word),
    (0 <= t < nG)%Z -> (curr = zget LENA (258 * t + 0)) ->
    let bf := bsW b 5 curr in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z -> MD b1 m ->
    (forall m' (t6' xb' : word),
        MD bf m' -> bw_ok bf -> (bw_live bf <= 12)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb' s2 s3 (Z_to_bv 64 (bw_numZ bf)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 0) (Z_to_bv 64 (bw_live bf)) t6')
                          F (Z_to_bv 64 0x178f4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb s2 s3 (Z_to_bv 64 (bw_numZ b1)) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 (bw_live b1)) t5 t6)
                      F (Z_to_bv 64 0x178d0) fc None m (seg_rom s0segs)).
  Proof.
    intros Q t curr b b1 m ra a0 s2 s3 s9 s10 t5 t6 xb Ht Hc. cbv zeta. intros OK Eb1 NL L1 XB MEM K.
    destruct (LENF t 0 Ht ltac:(lia)) as [ZD ZR]. rewrite <- Hc in ZR.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 5 curr = BW (Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296)) (bw_live b1 + 5) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 5 curr)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (Z.mod_small (27 - bw_live b1) 32) in * by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296))%Z.
    { rewrite (low32_or_shifted curr _ xb (bw_buff b1) XB) by lia. replace (27 - bw_live b1)%Z with (32 - bw_live b1 - 5)%Z by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|]. wstep.
    enter_with (K _ _ _); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| rewrite EBW; cbn [bw_live]; lia|].
    rewrite EBW. cbn [bw_buff]. rewrite (low32_or_shifted curr _ xb (bw_buff b1) XB) by lia.
    replace (27 - bw_live b1)%Z with (32 - bw_live b1 - 5)%Z by lia. apply low32_small. exact XR.
  Qed.


  (* [comment removed for export] *)
  Lemma S0_lens_body : forall (Q : machine_state -> Prop) (t curr : Z) (b1 : bw) (c1 : Z) (n : nat) (b : bw) (m : word -> option byte)
      (ra a0 s2 s3 s9 s10 t6 xb : word),
    (t + Z.of_nat (S n) = nG)%Z -> (0 <= t)%Z -> (curr = zget LENA (258 * t + 0)) ->
    sm_put_lens_row (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr = (b1, c1) ->
    let bf := sm_put_lens n b1 LENA A (t + 1) in
    bw_ok (bsW b 5 curr) -> (bw_live (bsW b 5 curr) <= 12)%Z -> (bw_numZ bf <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff (bsW b 5 curr))%Z -> MD (bsW b 5 curr) m ->
    (* [comment removed for export] *)
    (forall (Q : machine_state -> Prop) (t : Z) (b : bw) (m : word -> option byte) (ra a0 s2 s3 s9 s10 t2 t3 t5 t6 xb : word),
      (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
      let bf := sm_put_lens n b LENA A t in
      bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
      (forall m' (s2' s3' t2' t3' t5' t6' xb' : word),
          MD bf m' -> bw_ok bf -> (bw_live bf <= 10)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
          evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 nG) xb' s2' s3' (Z_to_bv 64 (bw_numZ bf)) s9 s10 t2' t3' (Z_to_bv 64 (bw_live bf)) t5' t6')
                            F (Z_to_bv 64 0x17a20) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb s2 s3 (Z_to_bv 64 (bw_numZ b)) s9 s10 t2 t3 (Z_to_bv 64 (bw_live b)) t5 t6)
                        F (Z_to_bv 64 0x17884) fc None m (seg_rom s0segs))) ->
    (forall m' (s2' s3' t2' t3' t5' t6' xb' : word),
        MD bf m' -> bw_ok bf -> (bw_live bf <= 10)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 nG) xb' s2' s3' (Z_to_bv 64 (bw_numZ bf)) s9 s10 t2' t3' (Z_to_bv 64 (bw_live bf)) t5' t6')
                          F (Z_to_bv 64 0x17a20) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb s2 s3 (Z_to_bv 64 (bw_numZ (bsW b 5 curr))) s9 s10 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 curr) (Z_to_bv 64 0) (Z_to_bv 64 (bw_live (bsW b 5 curr))) t6)
                      F (Z_to_bv 64 0x178f4) fc None m (seg_rom s0segs)).
  Proof.
    intros Q t curr b1 c1 n b m ra a0 s2 s3 s9 s10 t6 xb Ht Ht0 Hc ER. cbv zeta. intros OK L12 NL XB MEM IHn K.
    destruct (LENF t 0 ltac:(lia) ltac:(lia)) as [ZD ZR]. rewrite <- Hc in ZR.
    pose proof (put_lens_NZM n b1 LENA A (t + 1)) as NZ2. unfold NZM in NZ2.
    eapply (LP S0_lens_inner (Z.to_nat A) t Q 0%Z curr (bsW b 5 curr) m); [lia| lia| lia| lia| lia| exact OK| lia| rewrite ER; cbn [fst]; lia| exact XB| exact MEM|].
    rewrite ER. cbn [fst]. clear MEM. intros m' s2' s3' t3' t6' xb' MEM OK1 L10 XB1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK1 as (OK1b & OK1l & OK1n).
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - eapply (IHn Q (t + 1)%Z b1 _); [lia| lia| lia| exact OK1| lia| exact NL| exact XB1| closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_lens] in K.
      enter_with (K _ s2' s3' _ t3' _ t6' xb'); [st_eq| closeMD| exact OK1| lia| exact XB1].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_lens_outer : forall (n : nat) (Q : machine_state -> Prop) (t : Z) (b : bw) (m : word -> option byte)
      (ra a0 s2 s3 s9 s10 t2 t3 t5 t6 xb : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
    let bf := sm_put_lens n b LENA A t in
    bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z -> MD b m ->
    (forall m' (s2' s3' t2' t3' t5' t6' xb' : word),
        MD bf m' -> bw_ok bf -> (bw_live bf <= 10)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 nG) xb' s2' s3' (Z_to_bv 64 (bw_numZ bf)) s9 s10 t2' t3' (Z_to_bv 64 (bw_live bf)) t5' t6')
                          F (Z_to_bv 64 0x17a20) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RL ra a0 (Z_to_bv 64 t) xb s2 s3 (Z_to_bv 64 (bw_numZ b)) s9 s10 t2 t3 (Z_to_bv 64 (bw_live b)) t5 t6)
                      F (Z_to_bv 64 0x17884) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q t b m ra a0 s2 s3 s9 s10 t2 t3 t5 t6 xb Ht Ht0 _. cbv zeta. intros OK L25 NL XB MEM K.
    destruct (LENF t 0 ltac:(lia) ltac:(lia)) as [ZD ZR].
    rewrite put_lens_S in NL, K. cbv zeta in NL, K.
    set (curr := zget LENA (258 * t + 0)) in *.
    destruct (sm_put_lens_row (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr) as [b1 c1] eqn:ER.
    pose proof (put_lens_NZM n b1 LENA A (t + 1)) as NZ2. unfold NZM in NZ2.
    pose proof (put_lens_row_NZM (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr) as NZ1. rewrite ER in NZ1. unfold NZM in NZ1. cbn [fst] in NZ1.
    pose proof (bsW_NZM b 5 curr) as NZ0. unfold NZM in NZ0.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + 0) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. fold curr. rewrite (unsigned_lit8 curr) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (S0_lens5_tail Q t curr b b m); [st_eq| lia| reflexivity| exact OK| | lia| lia| exact XB| closeMD|].
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      intros m' t6' xb' MEM' OK' L12 XB'.
      eapply (S0_lens_body Q t curr b1 c1 n b m'); try eassumption; try lia.
    - (* [comment removed for export] *)
      enter_with (FL S0_len5_flush Q BS_FUEL b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
      { pose proof (bsW_bytes b 5 curr) as [BB _]. rewrite <- BB. lia. }
      intros b0 m' xb' t5' Eb0 MEM' XB' L1.
      enter_with (S0_lens5_tail Q t curr b b0 m'); [st_eq| lia| reflexivity| exact OK| exact Eb0| lia| exact L1| exact XB'| exact MEM'|].
      intros m'' t6'' xb'' MEM'' OK'' L12 XB''.
      eapply (S0_lens_body Q t curr b1 c1 n b m''); try eassumption; try lia.
  Qed.
End SDF4.

End ACeilS1.
