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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith.
From Stdlib Require Lia. 
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith2.
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
Module S0_cmp_sdD2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith.
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


Section SDD2.
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
  Notation MDi bs := (MS3 cx g e nG nSel usp sv W m0 bs).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Notation INUA := (e_inUse e).
  Hypothesis INUF : forall k, (0 <= k < 256)%Z -> zdef INUA k = true /\ (0 <= zget INUA k < 256)%Z.
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.

  (* [comment removed for export] *)
  Notation RM ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6).
  Notation RP a0 a1 a2 a3 a4 t2 t3 t4 s2 s3 s4 s9 s10 t6 ra :=
    (RM ra (Z_to_bv 64 15) (Z_to_bv 64 (-2147483648)) t2 a0 a1 a2 a3 a4 (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 16) (Z_to_bv 64 8) s2 s3 s4 s9 s10 t3 t4 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_pinuse_flush : forall (q : Z) (SC : same_code s0segs q 0x175e4 14) (Q : machine_state -> Prop) (f : nat) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra t2 a0 a4 s2 s3 s4 s9 s10 t3 t6 : word) (xb a30 t40 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MDi bs b m ->
    (forall b1 m' (xb' t4' : word),
        b1 = bs_needw f b -> MDi bs b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 15) (Z_to_bv 64 (-2147483648)) t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) a0 (Z_to_bv 64 (bw_numZ b1)) xb' (Z_to_bv 64 (bw_live b1)) a4 (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 16) (Z_to_bv 64 8) s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4' (Z_to_bv 64 (E + 128)) t6)
            F (Z_to_bv 64 (q + 56)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 15) (Z_to_bv 64 (-2147483648)) t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) a0 (Z_to_bv 64 (bw_numZ b)) xb a30 a4 (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 16) (Z_to_bv 64 8) s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t40 (Z_to_bv 64 (E + 128)) t6)
            F (Z_to_bv 64 q) fc None m (seg_rom s0segs)).
  Proof.
    intros q SC Q f. induction f as [|f IH]; intros bs b m ra t2 a0 a4 s2 s3 s4 s9 s10 t3 t6 xb a30 t40 OK L8 Lf NL X4 MEM K; [lia|].
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
    - enter_with (IH bs (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' t4' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma SCp3a : same_code s0segs 0x175e4 0x175e4 14. Proof. same_code_tac. Qed.
  Lemma SCp3b : same_code s0segs 0x1762c 0x175e4 14. Proof. same_code_tac. Qed.

  (* [comment removed for export] *)
  Lemma S0_pinuse_join : forall (Q : machine_state -> Prop) (i j : Z) (n : nat) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (xo ra a0 t4 s2 s3 s4 s9 s10 t6 : word) (v : Z),
    (j + Z.of_nat (S n) = 16)%Z -> (0 <= j)%Z -> (0 <= i < 16)%Z ->
    (0 <= v <= 1)%Z ->
    let bf := sm_put_inuse_row n (bsW b 1 v) INUA i (j + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z ->
    (bv_unsigned xo mod 4294967296 = Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296))%Z ->
    MDi bs b1 m ->
    (forall (Q : machine_state -> Prop) (i j : Z) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 t4 s2 s3 s4 s9 s10 t6 xb : word),
      (j + Z.of_nat n = 16)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < 16)%Z ->
      let bf := sm_put_inuse_row n b INUA i j in
      bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
      MDi bs b m ->
      (forall m' (t4' xb' : word),
          MDi bs bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
          evt s0segs Q (MS (RP a0 (Z_to_bv 64 (bw_numZ bf)) xb' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 i) (Z_to_bv 64 16) (Z_to_bv 64 (i * 16)) t4' s2 s3 s4 s9 s10 t6 ra)
                            F (Z_to_bv 64 0x17678) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RP a0 (Z_to_bv 64 (bw_numZ b)) xb (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 i) (Z_to_bv 64 j) (Z_to_bv 64 (i * 16)) t4 s2 s3 s4 s9 s10 t6 ra)
                        F (Z_to_bv 64 0x175d0) fc None m (seg_rom s0segs))) ->
    (forall m' (t4' xb' : word),
        MDi bs bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RP a0 (Z_to_bv 64 (bw_numZ bf)) xb' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 i) (Z_to_bv 64 16) (Z_to_bv 64 (i * 16)) t4' s2 s3 s4 s9 s10 t6 ra)
                          F (Z_to_bv 64 0x17678) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RP a0 (Z_to_bv 64 (bw_numZ b1)) xo (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 i) (Z_to_bv 64 j) (Z_to_bv 64 (i * 16)) t4 s2 s3 s4 s9 s10 t6 ra)
                      F (Z_to_bv 64 0x17664) fc None m (seg_rom s0segs)).
  Proof.
    intros Q i j n bs b b1 m xo ra a0 t4 s2 s3 s4 s9 s10 t6 v Hj Hj0 Hi Hv. cbv zeta. intros OK Eb1 NL XO MEM IHn K.
    pose proof (put_inuse_row_NZM n (bsW b 1 v) INUA i (j + 1)) as NZ1. unfold NZM in NZ1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 1 v = BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite XO. symmetry. apply Z.mod_small. exact XR. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IHn Q i (j + 1)%Z bs (bsW b 1 v) _ _ _ _ _ _ _ _ _ _ xo);
        [st_eq; rewrite ?EBW; reflexivity| lia| lia| lia| lia| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact NL| rewrite EBW; cbn [bw_buff]; exact XO| rewrite EBW; closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse_row] in K.
      enter_with (K _ _ xo); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| rewrite EBW; cbn [bw_live]; lia| rewrite EBW; cbn [bw_buff]; exact XO].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_pinuse_inner : forall (n : nat) (Q : machine_state -> Prop) (i j : Z) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra a0 t4 s2 s3 s4 s9 s10 t6 xb : word),
    (j + Z.of_nat n = 16)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < 16)%Z ->
    let bf := sm_put_inuse_row n b INUA i j in
    bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MDi bs b m ->
    (forall m' (t4' xb' : word),
        MDi bs bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RP a0 (Z_to_bv 64 (bw_numZ bf)) xb' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 i) (Z_to_bv 64 16) (Z_to_bv 64 (i * 16)) t4' s2 s3 s4 s9 s10 t6 ra)
                          F (Z_to_bv 64 0x17678) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RP a0 (Z_to_bv 64 (bw_numZ b)) xb (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 i) (Z_to_bv 64 j) (Z_to_bv 64 (i * 16)) t4 s2 s3 s4 s9 s10 t6 ra)
                      F (Z_to_bv 64 0x175d0) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q i j bs b m ra a0 t4 s2 s3 s4 s9 s10 t6 xb Hj Hj0 _ Hi. cbv zeta. intros OK L25 NL XB MEM K.
    rewrite put_inuse_row_S in NL, K.
    destruct (INUF (i * 16 + j) ltac:(lia)) as [ZD ZR].
    set (v := (if negb (zget INUA (i * 16 + j) =? 0) then 1 else 0)%Z) in NL, K.
    pose proof (put_inuse_row_NZM n (bsW b 1 v) INUA i (j + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 1 v) as NZ0. unfold NZM in NZ0.
    assert (Hv : (0 <= v <= 1)%Z) by (subst v; destruct (negb _); lia).
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (ovb_read1 s0segs m (E + 128) INUA (jseg J 128 256) 256 (i * 16 + j) _ INU ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget INUA (i * 16 + j))) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (Ev : v = 0%Z) by (subst v; replace (zget INUA (i * 16 + j) =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + eapply (S0_pinuse_join Q i j n bs b b _ xb) with (v := 0%Z); [lia| lia| lia| lia| exact OK| | exact NL| | closeMD| exact IH| exact K].
        { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        { rewrite lor_shl0. exact XB. }
      + eapply (S0_pinuse_flush 0x1762c SCp3b Q BS_FUEL bs b m); [exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
        { pose proof (bsW_bytes b 1 0) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' xb' t4' Eb1 MEM' XB' L1. change (Z_to_bv 64 (0x1762c + 56)) with (Z_to_bv 64 0x17664).
        eapply (S0_pinuse_join Q i j n bs b b1 m' xb') with (v := 0%Z); [lia| lia| lia| lia| exact OK| exact Eb1| exact NL| | exact MEM'| exact IH| exact K].
        rewrite lor_shl0. exact XB'.
    - (* [comment removed for export] *)
      assert (Ev : v = 1%Z) by (subst v; replace (zget INUA (i * 16 + j) =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        wstep. wstep. wstep.
        eapply (S0_pinuse_join Q i j n bs b b) with (v := 1%Z); [lia| lia| lia| lia| exact OK| | exact NL| | closeMD| exact IH| exact K].
        { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        { apply (low32_or_bit (bw_live b) xb (bw_buff b)); [lia| exact XB| lia]. }
      + eapply (S0_pinuse_flush 0x175e4 SCp3a Q BS_FUEL bs b m); [exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
        { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' xb' t4' Eb1 MEM' XB' L1. change (Z_to_bv 64 (0x175e4 + 56)) with (Z_to_bv 64 0x1761c).
        cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OKb1 & _ & _). rewrite <- Eb1 in OKb1. cps_destruct OKb1 as (OKb1 & OKl1 & OKn1).
        clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI. openMD MEM'.
        wstep. wstep. wstep.
        eapply (S0_pinuse_join Q i j n bs b b1) with (v := 1%Z); [lia| lia| lia| lia| exact OK| exact Eb1| exact NL| | closeMD| exact IH| exact K].
        { apply (low32_or_bit (bw_live b1) xb' (bw_buff b1)); [lia| exact XB'| lia]. }
  Qed.

  (* [comment removed for export] *)
  Lemma S0_pinuse_outer : forall (n : nat) (Q : machine_state -> Prop) (i : Z) (in16 : zarr) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra a0 t2 t3 t4 s2 s3 s4 s9 s10 t6 xb : word),
    (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    let bf := sm_put_inuse n b in16 INUA i in
    bw_ok b -> (bw_live b <= 25)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MDi bs b m ->
    (forall m' (t2' t3' t4' xb' : word),
        MDi bs bf m' -> bw_ok bf -> (bw_live bf <= 25)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z ->
        evt s0segs Q (MS (RP a0 (Z_to_bv 64 (bw_numZ bf)) xb' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 16) t2' t3' t4' s2 s3 s4 s9 s10 t6 ra)
                          F (Z_to_bv 64 0x17680) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RP a0 (Z_to_bv 64 (bw_numZ b)) xb (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 i) t2 t3 t4 s2 s3 s4 s9 s10 t6 ra)
                      F (Z_to_bv 64 0x175bc) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q i in16 bs b m ra a0 t2 t3 t4 s2 s3 s4 s9 s10 t6 xb Hi Hi0 _ Lbs ROWS IN16. cbv zeta. intros OK L25 NL XB MEM K.
    rewrite put_inuse_S in NL, K. rewrite (IN16 i) in NL, K by lia.
    assert (R01 : (0 <= ROW16 INUA i <= 1)%Z) by (destruct (ROW16_01 INUA i); lia).
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    (* [comment removed for export] *)
    wstep.
    pose proof (u8arr_read s0segs m (usp + 872) bs i _ _ I16 (ROWS i ltac:(lia)) ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (ROW16 INUA i)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      replace (negb (ROW16 INUA i =? 0))%Z with false in NL, K by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia).
      pose proof (put_inuse_NZM n b in16 INUA (i + 1)) as NZ1. unfold NZM in NZ1.
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH Q (i + 1)%Z in16 bs b m); [st_eq| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| lia| exact NL| exact XB| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse] in K.
        enter_with (K m _ _ _ xb); [st_eq| closeMD| exact OK| lia| exact XB].
    - (* [comment removed for export] *)
      replace (negb (ROW16 INUA i =? 0))%Z with true in NL, K by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      set (b16 := sm_put_inuse_row 16 b INUA i 0) in NL, K.
      pose proof (put_inuse_NZM n b16 in16 INUA (i + 1)) as NZ1. unfold NZM in NZ1.
      wstep. wstep.
      enter_with (S0_pinuse_inner 16 Q i 0 bs b m); [st_eq| lia| lia| lia| lia| exact OK| lia| fold b16; lia| exact XB| closeMD|].
      fold b16. clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI.
      intros m' t4' xb' MEM' OK' L8' XB'.
      openMD MEM'. cps_pose OK' as (OKb' & OKl' & OKn').
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH Q (i + 1)%Z in16 bs b16 m'); [st_eq| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK'| lia| exact NL| exact XB'| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse] in K.
        enter_with (K m' _ _ _ xb'); [st_eq| closeMD| exact OK'| lia| exact XB'].
  Qed.
End SDD2.

End ACeilS1.
End S0_cmp_sdD2.

Unset Lia Cache.
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
#[local] Ltac2 Set RangeFast.RF.rc_skip_hyps := fun () => [@USP2].   (* [comment removed for export] *)
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSdStep.   (* [comment removed for export] *)
Local Ltac CmpSdKit.pstep_with SC p q n k ::= CmpSdStep.pstep_with_fast SC p q n k.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSdFast.   (* [comment removed for export] *)
Local Ltac CmpSdKit.same_code_tac ::= CmpSdFast.same_code_tac_fast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDD.
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
  Notation MDi bs := (MS3 cx g e nG nSel usp sv W m0 bs).
  Notation MD := (MS3 cx g e nG nSel usp sv W m0 i16).
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openMD H := openMS3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMS3 Gmtf Gbs Gzb.

  (* [comment removed for export] *)
  Notation INUA := (e_inUse e).
  Hypothesis INUF : forall k, (0 <= k < 256)%Z -> zdef INUA k = true /\ (0 <= zget INUA k < 256)%Z.
  Variable A : Z. Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis Li16 : Z.of_nat (length i16) = 16%Z.

  (* [comment removed for export] *)
  Notation RM ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 nSel) a0 a1 a2 a3 a4 a5 a6 a7
         s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6).


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_in16_inner : forall (n : nat) (Q : machine_state -> Prop) (i j acc : Z) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s2 s3 s4 s9 s10 t3 t4 t6 : word),
    (j + Z.of_nat n = 16)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < 16)%Z -> (acc = 0 \/ acc = 1)%Z ->
    Z.of_nat (length bs) = 16%Z -> nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 acc) ->
    MDi bs b m ->
    (forall m' bs' (t0' : word),
        MDi bs' b m' -> Z.of_nat (length bs') = 16%Z ->
        nth_error bs' (Z.to_nat i) = Some (Z_to_bv 8 (sm_in16_row n INUA i j acc)) ->
        (forall k, k <> Z.to_nat i -> nth_error bs' k = nth_error bs k) ->
        evt s0segs Q (MS (RM ra t0' t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 16) (Z_to_bv 64 1) (Z_to_bv 64 (E + 128 + 16 * i))
                              (Z_to_bv 64 (usp + 872 + i)) (Z_to_bv 64 (E + 128 + 16 * i + 16)) (Z_to_bv 64 (E + 128 + 16 * i + 16)) s2 s3 s4 s9 s10 t3 t4 t6)
                          F (Z_to_bv 64 0x174cc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RM ra t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 16) (Z_to_bv 64 1) (Z_to_bv 64 (E + 128 + 16 * i))
                          (Z_to_bv 64 (usp + 872 + i)) (Z_to_bv 64 (E + 128 + 16 * i + 16)) (Z_to_bv 64 (E + 128 + 16 * i + j)) s2 s3 s4 s9 s10 t3 t4 t6)
                      F (Z_to_bv 64 0x174b8) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q i j acc bs b m ra t0 t1 t2 s2 s3 s4 s9 s10 t3 t4 t6 Hj Hj0 _ Hi Hacc Lbs Nbs MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    destruct (INUF (16 * i + j) ltac:(lia)) as [ZD ZR].
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 128) INUA (jseg J 128 256) 256 (16 * i + j) _ INU ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    wstep. clear RD. cbv beta.
    rewrite in16_row_S in K. replace (i * 16 + j)%Z with (16 * i + j)%Z in K by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      rewrite (unsigned_lit8 (zget INUA (16 * i + j))) in Kc by lia.
      replace (negb (zget INUA (16 * i + j) =? 0))%Z with false in K by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia).
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH Q i (j + 1)%Z acc bs b m); [st_eq| lia| lia| lia| lia| exact Hacc| exact Lbs| exact Nbs| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_in16_row] in K.
        enter_with (K m bs _); [st_eq| closeMD| exact Lbs| exact Nbs| intros; reflexivity].
    - (* [comment removed for export] *)
      rewrite (unsigned_lit8 (zget INUA (16 * i + j))) in Kc by lia.
      replace (negb (zget INUA (16 * i + j) =? 0))%Z with true in K by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      pose proof (u8arr_store_ok s0segs m (usp + 872) bs i _ I16 ltac:(lia) eq_refl) as SO.
      wstep. u8_store_done I16 i.
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH Q i (j + 1)%Z 1%Z (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1)))) b _);
          [st_eq| lia| lia| lia| lia| right; reflexivity| rewrite upd_length; exact Lbs| |closeMD|].
        { rewrite nth_error_upd_same by lia. f_equal. }
        intros m' bs' t0' MEM' L' N' O'. eapply K; [exact MEM'| exact L'| exact N'|].
        intros k Hk. rewrite O' by exact Hk. apply nth_error_upd_other. lia.
      + assert (n = 0%nat) by lia. subst n. cbn [sm_in16_row] in K.
        enter_with (K _ (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1)))) _); [st_eq| closeMD| rewrite upd_length; exact Lbs| |].
        { rewrite nth_error_upd_same by lia. f_equal. }
        intros k Hk. apply nth_error_upd_other. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_in16_outer : forall (n : nat) (Q : machine_state -> Prop) (i : Z) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 : word),
    (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < i)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    MDi bs b m ->
    (forall m' bs' (t0' a5' a6' a7' : word),
        MDi bs' b m' -> Z.of_nat (length bs') = 16%Z ->
        (forall k, (0 <= k < 16)%Z -> nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
        evt s0segs Q (MS (RM ra t0' t1 t2 (Z_to_bv 64 16) (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 16) (Z_to_bv 64 1) (Z_to_bv 64 (E + 128 + 16 * 16))
                              a5' a6' a7' s2 s3 s4 s9 s10 t3 t4 t6)
                          F (Z_to_bv 64 0x174d8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RM ra t0 t1 t2 (Z_to_bv 64 i) (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 16) (Z_to_bv 64 1) (Z_to_bv 64 (E + 128 + 16 * i))
                          a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6)
                      F (Z_to_bv 64 0x174a0) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q i bs b m ra t0 t1 t2 a5 a6 a7 s2 s3 s4 s9 s10 t3 t4 t6 Hi Hi0 _ Lbs ROWS MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m (usp + 872) bs i _ I16 ltac:(lia) eq_refl) as SO.
    wstep. u8_store_done I16 i.
    (* [comment removed for export] *)
    wstep.
    enter_with (S0_in16_inner 16 Q i 0 0 (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)))) b _);
      [st_eq| lia| lia| lia| lia| left; reflexivity| rewrite upd_length; exact Lbs| | closeMD|].
    { rewrite nth_error_upd_same by lia. f_equal. }
    intros m' bs' t0' MEM' L' N' O'. fold (ROW16 INUA i) in N'.
    assert (ROWS' : forall k, (0 <= k < i + 1)%Z -> nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))).
    { intros k Hk. destruct (Z.eq_dec k i) as [->|NE]; [exact N'|].
      rewrite O' by lia. rewrite nth_error_upd_other by lia. apply ROWS. lia. }
    clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI. openMD MEM'.
    (* [comment removed for export] *)
    wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH Q (i + 1)%Z bs' b m'); [st_eq| lia| lia| lia| exact L'| exact ROWS'| closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n.
      enter_with (K m' bs' t0' _ _ _); [st_eq| closeMD| exact L'|]. intros k Hk. apply ROWS'. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_pin16_flush : forall (q : Z) (SC : same_code s0segs q 0x17510 14) (Q : machine_state -> Prop) (f : nat) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra a0 a4 s2 s3 s4 s9 s10 t3 t4 t6 : word) (xb a30 t20 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MDi bs b m ->
    (forall b1 m' (xb' t2' : word),
        b1 = bs_needw f b -> MDi bs b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 (-2147483648)) t2' (Z_to_bv 64 E) (Z_to_bv 64 nSel) a0 (Z_to_bv 64 (bw_numZ b1)) xb' (Z_to_bv 64 (bw_live b1)) a4 (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 8) (Z_to_bv 64 15) s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6)
            F (Z_to_bv 64 (q + 56)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 16) (Z_to_bv 64 (-2147483648)) t20 (Z_to_bv 64 E) (Z_to_bv 64 nSel) a0 (Z_to_bv 64 (bw_numZ b)) xb a30 a4 (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 8) (Z_to_bv 64 15) s2 s3 s4 (Z_to_bv 64 A) (Z_to_bv 64 nG) sv (Z_to_bv 64 nSel) s9 s10 (Z_to_bv 64 A1) t3 t4 (Z_to_bv 64 (E + 128)) t6)
            F (Z_to_bv 64 q) fc None m (seg_rom s0segs)).
  Proof.
    intros q SC Q f. induction f as [|f IH]; intros bs b m ra a0 a4 s2 s3 s4 s9 s10 t3 t4 t6 xb a30 t20 OK L8 Lf NL X4 MEM K; [lia|].
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
    - enter_with (IH bs (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' xb' t2' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma SCp2a : same_code s0segs 0x17510 0x17510 14. Proof. same_code_tac. Qed.
  Lemma SCp2b : same_code s0segs 0x17558 0x17510 14. Proof. same_code_tac. Qed.

  (* [comment removed for export] *)
  Lemma S0_pin16_join : forall (Q : machine_state -> Prop) (i : Z) (n : nat) (in16 : zarr) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (xo ra a0 t2 s2 s3 s4 s9 s10 t3 t4 t6 : word) (v : Z),
    (i + Z.of_nat (S n) = 16)%Z -> (0 <= i)%Z ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    (0 <= v <= 1)%Z ->
    let bf := sm_put_in16 n (bsW b 1 v) in16 (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z ->
    (bv_unsigned xo mod 4294967296 = Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296))%Z ->
    MDi bs b1 m ->
    (* [comment removed for export] *)
    (forall (Q : machine_state -> Prop) (i : Z) (in16 : zarr) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra a0 t2 s2 s3 s4 s9 s10 t3 t4 t6 xb : word),
      (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
      Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
      (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
      let bf := sm_put_in16 n b in16 i in
      bw_ok b -> (bw_live b <= 32)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
      MDi bs b m ->
      (forall m' (a1' t2' xb' : word),
          MDi bs bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z -> a1' = Z_to_bv 64 (bw_numZ bf) ->
          evt s0segs Q (MS (RM ra (Z_to_bv 64 16) (Z_to_bv 64 (-2147483648)) t2' a0 a1' xb' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 16)
                                (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 8) (Z_to_bv 64 15) s2 s3 s4 s9 s10 t3 t4 t6)
                            F (Z_to_bv 64 0x175a4) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RM ra (Z_to_bv 64 16) (Z_to_bv 64 (-2147483648)) t2 a0 (Z_to_bv 64 (bw_numZ b)) xb (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 i)
                            (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 8) (Z_to_bv 64 15) s2 s3 s4 s9 s10 t3 t4 t6)
                        F (Z_to_bv 64 0x17500) fc None m (seg_rom s0segs))) ->
    (forall m' (a1' t2' xb' : word),
        MDi bs bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z -> a1' = Z_to_bv 64 (bw_numZ bf) ->
        evt s0segs Q (MS (RM ra (Z_to_bv 64 16) (Z_to_bv 64 (-2147483648)) t2' a0 a1' xb' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 16)
                              (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 8) (Z_to_bv 64 15) s2 s3 s4 s9 s10 t3 t4 t6)
                          F (Z_to_bv 64 0x175a4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RM ra (Z_to_bv 64 16) (Z_to_bv 64 (-2147483648)) t2 a0 (Z_to_bv 64 (bw_numZ b1)) xo (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 i)
                          (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 8) (Z_to_bv 64 15) s2 s3 s4 s9 s10 t3 t4 t6)
                      F (Z_to_bv 64 0x17590) fc None m (seg_rom s0segs)).
  Proof.
    intros Q i n in16 bs b b1 m xo ra a0 t2 s2 s3 s4 s9 s10 t3 t4 t6 v Hi Hi0 Lbs ROWS IN16 Hv. cbv zeta. intros OK Eb1 NL XO MEM IHn K.
    pose proof (put_in16_NZM n (bsW b 1 v) in16 (i + 1)) as NZ1. unfold NZM in NZ1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 1 v = BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite XO. symmetry. apply Z.mod_small. exact XR. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IHn Q (i + 1)%Z in16 bs (bsW b 1 v) _ _ _ _ _ _ _ _ _ _ _ _ xo);
        [st_eq; rewrite ?EBW; reflexivity| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK2| rewrite EBW; cbn [bw_live]; lia| exact NL| rewrite EBW; cbn [bw_buff]; exact XO| rewrite EBW; closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_in16] in K.
      enter_with (K _ _ _ xo); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| rewrite EBW; cbn [bw_live]; lia| rewrite EBW; cbn [bw_buff]; exact XO| rewrite EBW; reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_pin16_loop : forall (n : nat) (Q : machine_state -> Prop) (i : Z) (in16 : zarr) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra a0 t2 s2 s3 s4 s9 s10 t3 t4 t6 xb : word),
    (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    let bf := sm_put_in16 n b in16 i in
    bw_ok b -> (bw_live b <= 32)%Z -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MDi bs b m ->
    (forall m' (a1' t2' xb' : word),
        MDi bs bf m' -> bw_ok bf -> (bw_live bf <= 8)%Z -> (bv_unsigned xb' mod 4294967296 = bw_buff bf)%Z -> a1' = Z_to_bv 64 (bw_numZ bf) ->
        evt s0segs Q (MS (RM ra (Z_to_bv 64 16) (Z_to_bv 64 (-2147483648)) t2' a0 a1' xb' (Z_to_bv 64 (bw_live bf)) (Z_to_bv 64 16)
                              (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 8) (Z_to_bv 64 15) s2 s3 s4 s9 s10 t3 t4 t6)
                          F (Z_to_bv 64 0x175a4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RM ra (Z_to_bv 64 16) (Z_to_bv 64 (-2147483648)) t2 a0 (Z_to_bv 64 (bw_numZ b)) xb (Z_to_bv 64 (bw_live b)) (Z_to_bv 64 i)
                          (Z_to_bv 64 (usp + 872)) (Z_to_bv 64 8) (Z_to_bv 64 15) s2 s3 s4 s9 s10 t3 t4 t6)
                      F (Z_to_bv 64 0x17500) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q i in16 bs b m ra a0 t2 s2 s3 s4 s9 s10 t3 t4 t6 xb Hi Hi0 _ Lbs ROWS IN16. cbv zeta. intros OK L25 NL XB MEM K.
    rewrite put_in16_S in NL, K. rewrite (IN16 i) in NL, K by lia.
    set (v := (if negb (ROW16 INUA i =? 0) then 1 else 0)%Z) in NL, K.
    pose proof (put_in16_NZM n (bsW b 1 v) in16 (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 1 v) as NZ0. unfold NZM in NZ0.
    assert (R01 : (0 <= ROW16 INUA i <= 1)%Z) by (destruct (ROW16_01 INUA i); lia).
    assert (Hv : (0 <= v <= 1)%Z) by (subst v; destruct (negb _); lia).
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    pose proof (bsW_live_le b 1 v OK ltac:(lia) ltac:(lia)) as LV2.
    (* [comment removed for export] *)
    wstep.
    pose proof (u8arr_read s0segs m (usp + 872) bs i _ _ I16 (ROWS i ltac:(lia)) ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (ROW16 INUA i)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (Ev : v = 0%Z) by (subst v; replace (ROW16 INUA i =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      (* [comment removed for export] *)
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        eapply (S0_pin16_join Q i n in16 bs b b _ xb) with (v := 0%Z); [lia| lia| exact Lbs| exact ROWS| exact IN16| lia| exact OK| | exact NL| | closeMD| exact IH| exact K].
        { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        { rewrite lor_shl0. exact XB. }
      + eapply (S0_pin16_flush 0x17558 SCp2b Q BS_FUEL bs b m); [exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
        { pose proof (bsW_bytes b 1 0) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' xb' t2' Eb1 MEM' XB' L1. change (Z_to_bv 64 (0x17558 + 56)) with (Z_to_bv 64 0x17590).
        eapply (S0_pin16_join Q i n in16 bs b b1 m' xb') with (v := 0%Z); [lia| lia| exact Lbs| exact ROWS| exact IN16| lia| exact OK| exact Eb1| exact NL| | exact MEM'| exact IH| exact K].
        rewrite lor_shl0. exact XB'.
    - (* [comment removed for export] *)
      assert (Ev : v = 1%Z) by (subst v; replace (ROW16 INUA i =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + (* [comment removed for export] *)
        wstep. wstep. wstep.
        eapply (S0_pin16_join Q i n in16 bs b b) with (v := 1%Z); [lia| lia| exact Lbs| exact ROWS| exact IN16| lia| exact OK| | exact NL| | closeMD| exact IH| exact K].
        { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
        { apply (low32_or_bit (bw_live b) xb (bw_buff b)); [lia| exact XB| lia]. }
      + eapply (S0_pin16_flush 0x17510 SCp2a Q BS_FUEL bs b m); [exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
        { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' xb' t2' Eb1 MEM' XB' L1. change (Z_to_bv 64 (0x17510 + 56)) with (Z_to_bv 64 0x17548).
        cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OKb1 & _ & _). rewrite <- Eb1 in OKb1. cps_destruct OKb1 as (OKb1 & OKl1 & OKn1).
        clear EH1 EH2 AR2 AR1 INU SLM SEL LEN COD SLO SHI I16 MI. openMD MEM'.
        (* [comment removed for export] *)
        wstep. wstep. wstep.
        eapply (S0_pin16_join Q i n in16 bs b b1) with (v := 1%Z); [lia| lia| exact Lbs| exact ROWS| exact IN16| lia| exact OK| exact Eb1| exact NL| | closeMD| exact IH| exact K].
        { apply (low32_or_bit (bw_live b1) xb' (bw_buff b1)); [lia| exact XB'| lia]. }
  Qed.
End SDD.

End ACeilS1.
