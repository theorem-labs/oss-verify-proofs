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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSD CmpCutSD0 CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith4 BzCLemmasSd BzCSmF1 S0_cmp_sdA.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSD CmpCutSD0 CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith4 BzCLemmasSd S0_cmp_sdA.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
Module S0_cmp_sdB.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdA.
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
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDB.
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
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.

  (* [comment removed for export] *)
  Variables (sc gs : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i < gs + 50)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).
  Lemma Hsel : (0 <= sel < 6)%Z. Proof. pose proof (SELF sc Hsc). lia. Qed.
  Lemma LENFs : forall v, (0 <= v < A)%Z -> zdef LENA (258 * sel + v) = true /\ (1 <= zget LENA (258 * sel + v) <= 17)%Z.
  Proof. intros v Hv. apply LENF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.
  Lemma CODFs : forall v, (0 <= v < A)%Z -> zdef CODA (258 * sel + v) = true /\ (0 <= zget CODA (258 * sel + v) < 4294967296)%Z.
  Proof. intros v Hv. apply CODF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.

  Notation MT := (A1 + 2 * gs)%Z. Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  (* [comment removed for export] *)
  Notation RG ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 gs) (Z_to_bv 64 (gs + 50)) a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)
         (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation BLK := (S0_itah_blk cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).
  Notation HEAD := (S0_itah_head cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_blk0_flush : forall (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t1 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (a4' t1' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (RG ra (Z_to_bv 64 (bw_numZ b1)) t1' (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4' a5 a6 (Z_to_bv 64 (bw_live b1)) s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x17b30) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra (Z_to_bv 64 (bw_numZ b)) t1 (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4 a5 a6 a7 s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17af8) fc None m (seg_rom s0segs)).
  Proof.
    intros Q f. induction f as [|f IH]; intros b m ra t1 a4 a5 a6 a7 s4 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
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
    pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) (Z_to_bv 64 (bv_unsigned a4 / 16777216)) AR2 ltac:(lia)) as AR2'.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bv_unsigned a4 / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite unsigned_lit. 2:{ pose proof (word_urange a4). split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
        rewrite (high_byte_of_low32 (bv_unsigned a4) (bw_buff b)); [| pose proof (word_urange a4); lia | exact X4 | lia].
        apply Z.mod_small. pose proof (bw_emit_byte b ltac:(lia)). rewrite shiftr_div24 in *. lia. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (bw_emit b) m); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | |].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + closeMD.
      + intros b1 m' a4' t1' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_blk0_tail : forall (Q : machine_state -> Prop) (b b1 : bw) (m : word -> option byte)
      (ra t0 t1 a4 s4 t3 t4 t5 t6 : word),
    let v := mtfv_at ARR1 gs in
    let n := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ (bsW b n cv) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (t0' t1' a4' a5' a6' : word),
        MD (bsW b n cv) m' -> (bv_unsigned a6' mod 4294967296 = bw_buff (bsW b n cv))%Z ->
        evt s0segs Q (MS (RG ra t0' t1' (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4' a5' a6' (Z_to_bv 64 (bw_live (bsW b n cv))) s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x17b48) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4 (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 n) (Z_to_bv 64 (bw_live b1)) s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17b30) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb USP1 LIM nG nSel sv W m0 i16 A LENF CODF SELF sc gs Hsc Hgs HgsE MTFV.
    intros Q b b1 m ra t0 t1 a4 s4 t3 t4 t5 t6. cbv zeta. intros OK Eb1 NL X4 MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    pose proof (MTFV gs ltac:(lia)) as MV.
    destruct (LENFs (mtfv_at ARR1 gs) MV) as [LD LRG]. destruct (CODFs (mtfv_at ARR1 gs) MV) as [CD CRG].
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_destruct OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    rewrite (neg_shift_amount (bw_live b1) (zget LENA (258 * sel + mtfv_at ARR1 gs))) by lia.
    replace (bw_live b1 + zget LENA (258 * sel + mtfv_at ARR1 gs) =? 32)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl (zget CODA (258 * sel + mtfv_at ARR1 gs)) (32 - bw_live b1 - zget LENA (258 * sel + mtfv_at ARR1 gs))) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ (zget CODA (258 * sel + mtfv_at ARR1 gs))) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    replace (bsW b (zget LENA (258 * sel + mtfv_at ARR1 gs)) (zget CODA (258 * sel + mtfv_at ARR1 gs)))
      with (BW (Z.lor (bw_buff b1) ((Z.shiftl (zget CODA (258 * sel + mtfv_at ARR1 gs)) (32 - bw_live b1 - zget LENA (258 * sel + mtfv_at ARR1 gs))) mod 4294967296))
               (bw_live b1 + zget LENA (258 * sel + mtfv_at ARR1 gs)) (bw_numZ b1) (bw_zb b1)) in K by (unfold bsW; rewrite <- Eb1; reflexivity).
    eapply K.
    - closeMD.
    - cbn [bw_buff]. rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ (zget CODA (258 * sel + mtfv_at ARR1 gs))) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  Lemma S0_blk0 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte)
      (ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
    let v := mtfv_at ARR1 gs in
    let n := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    bw_ok b -> (bw_numZ (bsW b n cv) <= LIM)%Z ->
    MD b m ->
    (forall m' (t0' t1' a4' a5' a6' : word),
        MD (bsW b n cv) m' -> (bv_unsigned a6' mod 4294967296 = bw_buff (bsW b n cv))%Z ->
        evt s0segs Q (MS (RG ra t0' t1' (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4' a5' a6' (Z_to_bv 64 (bw_live (bsW b n cv))) s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x17b48) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17ab0) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b m ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6. cbv zeta. intros OK NL MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (MTFV gs ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    destruct (LENFs (mtfv_at ARR1 gs) MV) as [LD LRG]. destruct (CODFs (mtfv_at ARR1 gs) MV) as [CD CRG].
    pose proof (bsW_NZM b (zget LENA (258 * sel + mtfv_at ARR1 gs)) (zget CODA (258 * sel + mtfv_at ARR1 gs))) as NZ0. unfold NZM in NZ0.
    cps_pose (bs_needw_post BS_FUEL b ltac:(unfold bw_ok; lia) ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 1704) SELA (jseg J 1704 18002) 18002 sc _ SEL ltac:(lia) SD eq_refl) as RD0.
    wstep. clear RD0. cbv beta. rewrite (unsigned_lit8 sel) by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * gs) _ AR1 ltac:(lia) ltac:(lia) ZB1 eq_refl) as RD1.
    change (rd16 ARR1 (2 * gs)) with (mtfv_at ARR1 gs) in RD1.
    wstep. clear RD1. rewrite zx16_small by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + mtfv_at ARR1 gs) _ LEN ltac:(lia) LD ltac:(cbv delta [wa]; f_equal; lia)) as RD2.
    wstep. clear RD2. cbv beta. rewrite (unsigned_lit8 (zget LENA (258 * sel + mtfv_at ARR1 gs))) by lia.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + mtfv_at ARR1 gs) _ COD ltac:(lia) CD ltac:(cbv delta [wa]; f_equal; lia)) as RD3.
    wstep. clear RD3.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (S0_blk0_tail Q b b m); [st_eq| unfold bw_ok; lia| | lia| | closeMD| exact K].
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
    - (* [comment removed for export] *)
      wstep.
      enter_with (S0_blk0_flush Q BS_FUEL b m); [st_eq| unfold bw_ok; lia| lia| unfold BS_FUEL; cbn; lia| | | closeMD|].
      { pose proof (bsW_bytes b (zget LENA (258 * sel + mtfv_at ARR1 gs)) (zget CODA (258 * sel + mtfv_at ARR1 gs))) as [BB _]. rewrite <- BB. exact NL. }
      { rewrite low32_sx32, low32_lit. apply Z.mod_small. lia. }
      intros b1 m' a4' t1' Eb1 MEM' X4' L1.
      eapply (S0_blk0_tail Q b b1); [unfold bw_ok; lia| exact Eb1| lia| exact X4'| exact MEM'| exact K].
  Qed.
End SDB.

End ACeilS1.
End S0_cmp_sdB.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSdFast.
Module S0_cmp_sdB2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdA.
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
Local Ltac CmpSdKit.same_code_tac ::= CmpSdFast.same_code_tac_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDB2.
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
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.

  (* [comment removed for export] *)
  Variables (sc gs : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i < gs + 50)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).
  Lemma Hsel : (0 <= sel < 6)%Z. Proof. pose proof (SELF sc Hsc). lia. Qed.
  Lemma LENFs : forall v, (0 <= v < A)%Z -> zdef LENA (258 * sel + v) = true /\ (1 <= zget LENA (258 * sel + v) <= 17)%Z.
  Proof. intros v Hv. apply LENF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.
  Lemma CODFs : forall v, (0 <= v < A)%Z -> zdef CODA (258 * sel + v) = true /\ (0 <= zget CODA (258 * sel + v) < 4294967296)%Z.
  Proof. intros v Hv. apply CODF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.

  Notation MT := (A1 + 2 * gs)%Z. Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  (* [comment removed for export] *)
  Notation RG ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 gs) (Z_to_bv 64 (gs + 50)) a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)
         (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation BLK := (S0_itah_blk cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).
  Notation HEAD := (S0_itah_head cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma SC48 : same_code s0segs 0x18fdc 0x17b4c 21. Proof. same_code_tac. Qed.

  Lemma S0_blk48 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte)
      (ra t0 t1 a4 a5 a6 s4 t3 t4 t5 t6 : word),
    let v := mtfv_at ARR1 (gs + 48) in
    let n := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    bw_ok b -> (bw_numZ (bsW b n cv) <= LIM)%Z ->
    (bv_unsigned a6 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall m' (t0' t1' a4' a6' a7' : word),
        MD (bsW b n cv) m' -> (bv_unsigned a4' mod 4294967296 = bw_buff (bsW b n cv))%Z ->
        evt s0segs Q (MS (RG ra t0' t1' (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4' (Z_to_bv 64 (bw_live (bsW b n cv))) a6' a7' s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19048) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4 a5 a6 (Z_to_bv 64 (bw_live b)) s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x18fd8) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b m ra t0 t1 a4 a5 a6 s4 t3 t4 t5 t6. cbv zeta. intros OK NL X6 MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. pose proof (MTFV (gs + 48) ltac:(lia)) as MV.
    destruct (LENFs (mtfv_at ARR1 (gs + 48)) MV) as [LD LRG]. destruct (CODFs (mtfv_at ARR1 (gs + 48)) MV) as [CD CRG].
    cps_pose OK as (OKb & OKl & OKn).
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    (* [comment removed for export] *)
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 48)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 48))) with (mtfv_at ARR1 (gs + 48)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (HEAD 0x18fdc SC48 Q b (mtfv_at ARR1 (gs + 48)) m); [exact OK| exact MV| exact NL| exact X6| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST.
    intros b1 m' t0' t1' a6' Eb1 MEM' X6' L1.
    change (Z_to_bv 64 (0x18fdc + 84)) with (Z_to_bv 64 0x19030).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
    cps_destruct OK1 as (OK1b & OK1l & OK1n). pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    openMD MEM'. bz_params.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    rewrite (neg_shift_amount (bw_live b1) (zget LENA (258 * sel + mtfv_at ARR1 (gs + 48)))) by lia.
    replace (bw_live b1 + zget LENA (258 * sel + mtfv_at ARR1 (gs + 48)) =? 32)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48))) (32 - bw_live b1 - zget LENA (258 * sel + mtfv_at ARR1 (gs + 48)))) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a6' (bw_buff b1) X6') by lia.
      rewrite (shl_mod32_congr _ (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48)))) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    replace (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 48))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48))))
      with (BW (Z.lor (bw_buff b1) ((Z.shiftl (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48))) (32 - bw_live b1 - zget LENA (258 * sel + mtfv_at ARR1 (gs + 48)))) mod 4294967296))
               (bw_live b1 + zget LENA (258 * sel + mtfv_at ARR1 (gs + 48))) (bw_numZ b1) (bw_zb b1)) in K by (unfold bsW; rewrite <- Eb1; reflexivity).
    eapply K.
    - closeMD.
    - cbn [bw_buff]. rewrite (low32_or_shifted _ _ a6' (bw_buff b1) X6') by lia.
      rewrite (shl_mod32_congr _ (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48)))) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_blk49_flush : forall (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t0 t1 a1 a2 a7 s4 t3 t4 t5 t6 : word) (xb a50 a60 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' a6' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 gs) (Z_to_bv 64 (gs + 50)) a1 a2 (Z_to_bv 64 (bw_numZ b1)) xb' (Z_to_bv 64 (bw_live b1)) a6' a7 (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8) (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6)
            F (Z_to_bv 64 0x190a0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 gs) (Z_to_bv 64 (gs + 50)) a1 a2 (Z_to_bv 64 (bw_numZ b)) xb a50 a60 a7 (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8) (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6)
            F (Z_to_bv 64 0x19068) fc None m (seg_rom s0segs)).
  Proof.
    intros Q f. induction f as [|f IH]; intros b m ra t0 t1 a1 a2 a7 s4 t3 t4 t5 t6 xb a50 a60 OK L8 Lf NL X4 MEM K; [lia|].
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
      + intros b1 m' xb' a6' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_blk49_tail : forall (Q : machine_state -> Prop) (b b1 : bw) (m : word -> option byte)
      (ra t0 t1 a3 a4 a6 a7 s4 t3 t4 t5 t6 : word),
    let v := mtfv_at ARR1 (gs + 49) in
    let n := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ (bsW b n cv) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (forall m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
        MD (bsW b n cv) m' ->
        evt s0segs Q (MS (RG ra t0' t1' a1' a2' a3' a4' a5' a6' a7' s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19164) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 n) a3 a4 (Z_to_bv 64 (bw_live b1)) a6 a7 s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x190a0) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb USP1 LIM nG nSel sv W m0 i16 A LENF CODF SELF sc gs Hsc Hgs HgsE MTFV.
    intros Q b b1 m ra t0 t1 a3 a4 a6 a7 s4 t3 t4 t5 t6. cbv zeta. intros OK Eb1 NL X4 MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    pose proof (MTFV (gs + 49) ltac:(lia)) as MV.
    destruct (LENFs (mtfv_at ARR1 (gs + 49)) MV) as [LD LRG]. destruct (CODFs (mtfv_at ARR1 (gs + 49)) MV) as [CD CRG].
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_destruct OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    rewrite (neg_shift_amount (bw_live b1) (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49)))) by lia.
    replace (bw_live b1 + zget LENA (258 * sel + mtfv_at ARR1 (gs + 49)) =? 32)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49))) (32 - bw_live b1 - zget LENA (258 * sel + mtfv_at ARR1 (gs + 49)))) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ a4 (bw_buff b1) X4) by lia.
      rewrite (shl_mod32_congr _ (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49)))) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    replace (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49))))
      with (BW (Z.lor (bw_buff b1) ((Z.shiftl (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49))) (32 - bw_live b1 - zget LENA (258 * sel + mtfv_at ARR1 (gs + 49)))) mod 4294967296))
               (bw_live b1 + zget LENA (258 * sel + mtfv_at ARR1 (gs + 49))) (bw_numZ b1) (bw_zb b1)) in K by (unfold bsW; rewrite <- Eb1; reflexivity).
    eapply K. closeMD.
  Qed.

  Lemma S0_blk49 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte)
      (ra t0 t1 a4 a6 a7 s4 t3 t4 t5 t6 : word),
    let v := mtfv_at ARR1 (gs + 49) in
    let n := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    bw_ok b -> (bw_numZ (bsW b n cv) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
        MD (bsW b n cv) m' ->
        evt s0segs Q (MS (RG ra t0' t1' a1' a2' a3' a4' a5' a6' a7' s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19164) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4 (Z_to_bv 64 (bw_live b)) a6 a7 s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x19048) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b m ra t0 t1 a4 a6 a7 s4 t3 t4 t5 t6. cbv zeta. intros OK NL X4 MEM K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (MTFV (gs + 49) ltac:(lia)) as MV. pose proof (SELF sc Hsc) as [SD SR].
    destruct (LENFs (mtfv_at ARR1 (gs + 49)) MV) as [LD LRG]. destruct (CODFs (mtfv_at ARR1 (gs + 49)) MV) as [CD CRG].
    pose proof (bsW_NZM b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49)))) as NZ0. unfold NZM in NZ0.
    cps_pose (bs_needw_post BS_FUEL b ltac:(unfold bw_ok; lia) ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 49)) _ AR1 ltac:(lia) ltac:(lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 49))) with (mtfv_at ARR1 (gs + 49)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + mtfv_at ARR1 (gs + 49)) _ LEN ltac:(lia) LD ltac:(cbv delta [wa]; f_equal; lia)) as RD2.
    wstep. clear RD2. cbv beta. rewrite (unsigned_lit8 (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49)))) by lia.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + mtfv_at ARR1 (gs + 49)) _ COD ltac:(lia) CD ltac:(cbv delta [wa]; f_equal; lia)) as RD3.
    wstep. clear RD3.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (S0_blk49_tail Q b b m _ _ _ _); [st_eq| unfold bw_ok; lia| | lia| | closeMD| exact K].
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      { exact X4. }
    - (* [comment removed for export] *)
      wstep.
      enter_with (S0_blk49_flush Q BS_FUEL b m); [st_eq| unfold bw_ok; lia| lia| unfold BS_FUEL; cbn; lia| | exact X4| closeMD|].
      { pose proof (bsW_bytes b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49)))) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' xb' a6' Eb1 MEM' X4' L1.
      eapply (S0_blk49_tail Q b b1); [unfold bw_ok; lia| exact Eb1| lia| exact X4'| exact MEM'| exact K].
  Qed.
End SDB2.

End ACeilS1.
End S0_cmp_sdB2.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Module S0_cmp_sdB3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdA.
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
Local Ltac CmpSdKit.same_code_tac ::= CmpSdFast.same_code_tac_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDB3.
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
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.

  (* [comment removed for export] *)
  Variables (sc gs : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i < gs + 50)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).
  Lemma Hsel : (0 <= sel < 6)%Z. Proof. pose proof (SELF sc Hsc). lia. Qed.
  Lemma LENFs : forall v, (0 <= v < A)%Z -> zdef LENA (258 * sel + v) = true /\ (1 <= zget LENA (258 * sel + v) <= 17)%Z.
  Proof. intros v Hv. apply LENF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.
  Lemma CODFs : forall v, (0 <= v < A)%Z -> zdef CODA (258 * sel + v) = true /\ (0 <= zget CODA (258 * sel + v) < 4294967296)%Z.
  Proof. intros v Hv. apply CODF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.

  Notation MT := (A1 + 2 * gs)%Z. Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  (* [comment removed for export] *)
  Notation RG ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 gs) (Z_to_bv 64 (gs + 50)) a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)
         (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation BLK := (S0_itah_blk cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).
  Notation HEAD := (S0_itah_head cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).

  Lemma SC1 : same_code s0segs 0x17b4c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC2 : same_code s0segs 0x17bbc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC3 : same_code s0segs 0x17c2c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC4 : same_code s0segs 0x17c9c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC5 : same_code s0segs 0x17d0c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC6 : same_code s0segs 0x17d7c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC7 : same_code s0segs 0x17dec 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC8 : same_code s0segs 0x17e5c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC9 : same_code s0segs 0x17ecc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC10 : same_code s0segs 0x17f3c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC11 : same_code s0segs 0x17fac 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC12 : same_code s0segs 0x1801c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC13 : same_code s0segs 0x1808c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC14 : same_code s0segs 0x180fc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC15 : same_code s0segs 0x1816c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC16 : same_code s0segs 0x181dc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC17 : same_code s0segs 0x1824c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC18 : same_code s0segs 0x182bc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC19 : same_code s0segs 0x1832c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC20 : same_code s0segs 0x1839c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC21 : same_code s0segs 0x1840c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC22 : same_code s0segs 0x1847c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC23 : same_code s0segs 0x184ec 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC24 : same_code s0segs 0x1855c 0x17b4c 27. Proof. same_code_tac. Qed.

  (* [comment removed for export] *)
  Lemma S0_blocks_1_24 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte)
      (ra t0 t1 a4 a5 a6 s4 t3 t4 t5 t6 : word),
    let bf := sm_put_syms 24 b LENA CODA ARR1 sel (gs + 1) in
    bw_ok b -> (bw_numZ bf <= LIM)%Z ->
    (bv_unsigned a6 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall m' (t0' t1' a4' a5' a6' : word),
        MD bf m' -> (bv_unsigned a6' mod 4294967296 = bw_buff bf)%Z -> bw_ok bf ->
        evt s0segs Q (MS (RG ra t0' t1' (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4' a5' a6' (Z_to_bv 64 (bw_live bf)) s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x185c8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4 a5 a6 (Z_to_bv 64 (bw_live b)) s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17b48) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b m ra t0 t1 a4 a5 a6 s4 t3 t4 t5 t6. cbv zeta. intros OK NL X6 MEM K.
    pose proof (SELF sc Hsc) as [SD SR].
    pose proof CX as CXL; unfold cctx_ok in CXL; cbv zeta in CXL; cps_destruct CXL as (_ & _ & XA10 & XA11 & _).
    remember (sm_put_syms 24 b LENA CODA ARR1 sel (gs + 1)) as bf eqn:RES. symmetry in RES.
    revert t0 t1 a4 a5 a6 m OK X6 MEM RES. generalize b. intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 1 + 1)%Z with (gs + 2)%Z in RES by lia.
    pose proof (put_syms_NZM 23 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 1))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 1)))) LENA CODA ARR1 sel (gs + 2)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 1) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 1)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 1))) with (mtfv_at ARR1 (gs + 1)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17b4c SC1 Q B (mtfv_at ARR1 (gs + 1)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17b4c + 108)%Z) with (Z_to_bv 64 0x17bb8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 1))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 1))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 1))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 1)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 2 + 1)%Z with (gs + 3)%Z in RES by lia.
    pose proof (put_syms_NZM 22 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 2))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 2)))) LENA CODA ARR1 sel (gs + 3)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 2) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 2)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 2))) with (mtfv_at ARR1 (gs + 2)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17bbc SC2 Q B (mtfv_at ARR1 (gs + 2)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17bbc + 108)%Z) with (Z_to_bv 64 0x17c28).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 2))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 2))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 2))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 2)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 3 + 1)%Z with (gs + 4)%Z in RES by lia.
    pose proof (put_syms_NZM 21 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 3))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 3)))) LENA CODA ARR1 sel (gs + 4)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 3) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 3)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 3))) with (mtfv_at ARR1 (gs + 3)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17c2c SC3 Q B (mtfv_at ARR1 (gs + 3)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17c2c + 108)%Z) with (Z_to_bv 64 0x17c98).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 3))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 3))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 3))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 3)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 4 + 1)%Z with (gs + 5)%Z in RES by lia.
    pose proof (put_syms_NZM 20 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 4))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 4)))) LENA CODA ARR1 sel (gs + 5)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 4) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 4)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 4))) with (mtfv_at ARR1 (gs + 4)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17c9c SC4 Q B (mtfv_at ARR1 (gs + 4)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17c9c + 108)%Z) with (Z_to_bv 64 0x17d08).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 4))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 4))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 4))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 4)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 5 + 1)%Z with (gs + 6)%Z in RES by lia.
    pose proof (put_syms_NZM 19 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 5))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 5)))) LENA CODA ARR1 sel (gs + 6)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 5) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 5)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 5))) with (mtfv_at ARR1 (gs + 5)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17d0c SC5 Q B (mtfv_at ARR1 (gs + 5)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17d0c + 108)%Z) with (Z_to_bv 64 0x17d78).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 5))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 5))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 5))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 5)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 6 + 1)%Z with (gs + 7)%Z in RES by lia.
    pose proof (put_syms_NZM 18 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 6))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 6)))) LENA CODA ARR1 sel (gs + 7)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 6) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 6)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 6))) with (mtfv_at ARR1 (gs + 6)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17d7c SC6 Q B (mtfv_at ARR1 (gs + 6)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17d7c + 108)%Z) with (Z_to_bv 64 0x17de8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 6))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 6))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 6))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 6)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 7 + 1)%Z with (gs + 8)%Z in RES by lia.
    pose proof (put_syms_NZM 17 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 7))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 7)))) LENA CODA ARR1 sel (gs + 8)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 7) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 7)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 7))) with (mtfv_at ARR1 (gs + 7)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17dec SC7 Q B (mtfv_at ARR1 (gs + 7)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17dec + 108)%Z) with (Z_to_bv 64 0x17e58).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 7))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 7))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 7))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 7)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 8 + 1)%Z with (gs + 9)%Z in RES by lia.
    pose proof (put_syms_NZM 16 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 8))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 8)))) LENA CODA ARR1 sel (gs + 9)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 8) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 8)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 8))) with (mtfv_at ARR1 (gs + 8)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17e5c SC8 Q B (mtfv_at ARR1 (gs + 8)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17e5c + 108)%Z) with (Z_to_bv 64 0x17ec8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 8))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 8))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 8))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 8)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 9 + 1)%Z with (gs + 10)%Z in RES by lia.
    pose proof (put_syms_NZM 15 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9)))) LENA CODA ARR1 sel (gs + 10)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 9) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 9)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 9))) with (mtfv_at ARR1 (gs + 9)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17ecc SC9 Q B (mtfv_at ARR1 (gs + 9)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17ecc + 108)%Z) with (Z_to_bv 64 0x17f38).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 9))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 9)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 10 + 1)%Z with (gs + 11)%Z in RES by lia.
    pose proof (put_syms_NZM 14 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10)))) LENA CODA ARR1 sel (gs + 11)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 10) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 10)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 10))) with (mtfv_at ARR1 (gs + 10)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17f3c SC10 Q B (mtfv_at ARR1 (gs + 10)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17f3c + 108)%Z) with (Z_to_bv 64 0x17fa8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 10))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 10)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 11 + 1)%Z with (gs + 12)%Z in RES by lia.
    pose proof (put_syms_NZM 13 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11)))) LENA CODA ARR1 sel (gs + 12)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 11) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 11)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 11))) with (mtfv_at ARR1 (gs + 11)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x17fac SC11 Q B (mtfv_at ARR1 (gs + 11)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x17fac + 108)%Z) with (Z_to_bv 64 0x18018).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 11))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 11)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 12 + 1)%Z with (gs + 13)%Z in RES by lia.
    pose proof (put_syms_NZM 12 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12)))) LENA CODA ARR1 sel (gs + 13)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 12) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 12)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 12))) with (mtfv_at ARR1 (gs + 12)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1801c SC12 Q B (mtfv_at ARR1 (gs + 12)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1801c + 108)%Z) with (Z_to_bv 64 0x18088).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 12))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 12)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 13 + 1)%Z with (gs + 14)%Z in RES by lia.
    pose proof (put_syms_NZM 11 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13)))) LENA CODA ARR1 sel (gs + 14)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 13) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 13)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 13))) with (mtfv_at ARR1 (gs + 13)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1808c SC13 Q B (mtfv_at ARR1 (gs + 13)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1808c + 108)%Z) with (Z_to_bv 64 0x180f8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 13))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 13)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 14 + 1)%Z with (gs + 15)%Z in RES by lia.
    pose proof (put_syms_NZM 10 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14)))) LENA CODA ARR1 sel (gs + 15)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 14) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 14)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 14))) with (mtfv_at ARR1 (gs + 14)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x180fc SC14 Q B (mtfv_at ARR1 (gs + 14)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x180fc + 108)%Z) with (Z_to_bv 64 0x18168).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 14))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 14)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 15 + 1)%Z with (gs + 16)%Z in RES by lia.
    pose proof (put_syms_NZM 9 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15)))) LENA CODA ARR1 sel (gs + 16)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 15) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 15)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 15))) with (mtfv_at ARR1 (gs + 15)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1816c SC15 Q B (mtfv_at ARR1 (gs + 15)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1816c + 108)%Z) with (Z_to_bv 64 0x181d8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 15))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 15)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 16 + 1)%Z with (gs + 17)%Z in RES by lia.
    pose proof (put_syms_NZM 8 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16)))) LENA CODA ARR1 sel (gs + 17)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 16) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 16)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 16))) with (mtfv_at ARR1 (gs + 16)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x181dc SC16 Q B (mtfv_at ARR1 (gs + 16)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x181dc + 108)%Z) with (Z_to_bv 64 0x18248).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 16))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 16)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 17 + 1)%Z with (gs + 18)%Z in RES by lia.
    pose proof (put_syms_NZM 7 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17)))) LENA CODA ARR1 sel (gs + 18)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 17) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 17)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 17))) with (mtfv_at ARR1 (gs + 17)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1824c SC17 Q B (mtfv_at ARR1 (gs + 17)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1824c + 108)%Z) with (Z_to_bv 64 0x182b8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 17))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 17)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 18 + 1)%Z with (gs + 19)%Z in RES by lia.
    pose proof (put_syms_NZM 6 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18)))) LENA CODA ARR1 sel (gs + 19)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 18) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 18)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 18))) with (mtfv_at ARR1 (gs + 18)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x182bc SC18 Q B (mtfv_at ARR1 (gs + 18)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x182bc + 108)%Z) with (Z_to_bv 64 0x18328).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 18))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 18)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 19 + 1)%Z with (gs + 20)%Z in RES by lia.
    pose proof (put_syms_NZM 5 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19)))) LENA CODA ARR1 sel (gs + 20)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 19) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 19)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 19))) with (mtfv_at ARR1 (gs + 19)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1832c SC19 Q B (mtfv_at ARR1 (gs + 19)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1832c + 108)%Z) with (Z_to_bv 64 0x18398).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 19))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 19)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 20 + 1)%Z with (gs + 21)%Z in RES by lia.
    pose proof (put_syms_NZM 4 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20)))) LENA CODA ARR1 sel (gs + 21)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 20) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 20)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 20))) with (mtfv_at ARR1 (gs + 20)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1839c SC20 Q B (mtfv_at ARR1 (gs + 20)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1839c + 108)%Z) with (Z_to_bv 64 0x18408).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 20))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 20)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 21 + 1)%Z with (gs + 22)%Z in RES by lia.
    pose proof (put_syms_NZM 3 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21)))) LENA CODA ARR1 sel (gs + 22)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 21) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 21)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 21))) with (mtfv_at ARR1 (gs + 21)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1840c SC21 Q B (mtfv_at ARR1 (gs + 21)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1840c + 108)%Z) with (Z_to_bv 64 0x18478).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 21))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 21)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 22 + 1)%Z with (gs + 23)%Z in RES by lia.
    pose proof (put_syms_NZM 2 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22)))) LENA CODA ARR1 sel (gs + 23)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 22) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 22)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 22))) with (mtfv_at ARR1 (gs + 22)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1847c SC22 Q B (mtfv_at ARR1 (gs + 22)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1847c + 108)%Z) with (Z_to_bv 64 0x184e8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 22))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 22)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 23 + 1)%Z with (gs + 24)%Z in RES by lia.
    pose proof (put_syms_NZM 1 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23)))) LENA CODA ARR1 sel (gs + 24)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 23) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 23)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 23))) with (mtfv_at ARR1 (gs + 23)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x184ec SC23 Q B (mtfv_at ARR1 (gs + 23)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x184ec + 108)%Z) with (Z_to_bv 64 0x18558).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 23))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 23)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 24 + 1)%Z with (gs + 25)%Z in RES by lia.
    pose proof (put_syms_NZM 0 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24)))) LENA CODA ARR1 sel (gs + 25)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 24) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 24)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 24))) with (mtfv_at ARR1 (gs + 24)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1855c SC24 Q B (mtfv_at ARR1 (gs + 24)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1855c + 108)%Z) with (Z_to_bv 64 0x185c8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 24))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 24)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_0 in RES. subst B. eapply K; [exact MEM| exact XB| exact OKB].
  Qed.
End SDB3.

End ACeilS1.
End S0_cmp_sdB3.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Module S0_cmp_sdB4.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdA.
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
Local Ltac CmpSdKit.same_code_tac ::= CmpSdFast.same_code_tac_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDB4.
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
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.

  (* [comment removed for export] *)
  Variables (sc gs : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i < gs + 50)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).
  Lemma Hsel : (0 <= sel < 6)%Z. Proof. pose proof (SELF sc Hsc). lia. Qed.
  Lemma LENFs : forall v, (0 <= v < A)%Z -> zdef LENA (258 * sel + v) = true /\ (1 <= zget LENA (258 * sel + v) <= 17)%Z.
  Proof. intros v Hv. apply LENF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.
  Lemma CODFs : forall v, (0 <= v < A)%Z -> zdef CODA (258 * sel + v) = true /\ (0 <= zget CODA (258 * sel + v) < 4294967296)%Z.
  Proof. intros v Hv. apply CODF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.

  Notation MT := (A1 + 2 * gs)%Z. Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  (* [comment removed for export] *)
  Notation RG ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 gs) (Z_to_bv 64 (gs + 50)) a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)
         (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation BLK := (S0_itah_blk cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).
  Notation HEAD := (S0_itah_head cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).

  Lemma SC25 : same_code s0segs 0x185cc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC26 : same_code s0segs 0x1863c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC27 : same_code s0segs 0x186ac 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC28 : same_code s0segs 0x1871c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC29 : same_code s0segs 0x1878c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC30 : same_code s0segs 0x187fc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC31 : same_code s0segs 0x1886c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC32 : same_code s0segs 0x188dc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC33 : same_code s0segs 0x1894c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC34 : same_code s0segs 0x189bc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC35 : same_code s0segs 0x18a2c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC36 : same_code s0segs 0x18a9c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC37 : same_code s0segs 0x18b0c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC38 : same_code s0segs 0x18b7c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC39 : same_code s0segs 0x18bec 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC40 : same_code s0segs 0x18c5c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC41 : same_code s0segs 0x18ccc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC42 : same_code s0segs 0x18d3c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC43 : same_code s0segs 0x18dac 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC44 : same_code s0segs 0x18e1c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC45 : same_code s0segs 0x18e8c 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC46 : same_code s0segs 0x18efc 0x17b4c 27. Proof. same_code_tac. Qed.
  Lemma SC47 : same_code s0segs 0x18f6c 0x17b4c 27. Proof. same_code_tac. Qed.

  (* [comment removed for export] *)
  Lemma S0_blocks_25_47 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte)
      (ra t0 t1 a4 a5 a6 s4 t3 t4 t5 t6 : word),
    let bf := sm_put_syms 23 b LENA CODA ARR1 sel (gs + 25) in
    bw_ok b -> (bw_numZ bf <= LIM)%Z ->
    (bv_unsigned a6 mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall m' (t0' t1' a4' a5' a6' : word),
        MD bf m' -> (bv_unsigned a6' mod 4294967296 = bw_buff bf)%Z -> bw_ok bf ->
        evt s0segs Q (MS (RG ra t0' t1' (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4' a5' a6' (Z_to_bv 64 (bw_live bf)) s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x18fd8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 (Z_to_bv 64 MT) (Z_to_bv 64 CR) (Z_to_bv 64 LR) a4 a5 a6 (Z_to_bv 64 (bw_live b)) s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x185c8) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b m ra t0 t1 a4 a5 a6 s4 t3 t4 t5 t6. cbv zeta. intros OK NL X6 MEM K.
    pose proof (SELF sc Hsc) as [SD SR].
    pose proof CX as CXL; unfold cctx_ok in CXL; cbv zeta in CXL; cps_destruct CXL as (_ & _ & XA10 & XA11 & _).
    remember (sm_put_syms 23 b LENA CODA ARR1 sel (gs + 25)) as bf eqn:RES. symmetry in RES.
    revert t0 t1 a4 a5 a6 m OK X6 MEM RES. generalize b. intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 25 + 1)%Z with (gs + 26)%Z in RES by lia.
    pose proof (put_syms_NZM 22 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25)))) LENA CODA ARR1 sel (gs + 26)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 25) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 25)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 25))) with (mtfv_at ARR1 (gs + 25)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x185cc SC25 Q B (mtfv_at ARR1 (gs + 25)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x185cc + 108)%Z) with (Z_to_bv 64 0x18638).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 25))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 25)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 26 + 1)%Z with (gs + 27)%Z in RES by lia.
    pose proof (put_syms_NZM 21 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26)))) LENA CODA ARR1 sel (gs + 27)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 26) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 26)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 26))) with (mtfv_at ARR1 (gs + 26)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1863c SC26 Q B (mtfv_at ARR1 (gs + 26)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1863c + 108)%Z) with (Z_to_bv 64 0x186a8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 26))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 26)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 27 + 1)%Z with (gs + 28)%Z in RES by lia.
    pose proof (put_syms_NZM 20 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27)))) LENA CODA ARR1 sel (gs + 28)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 27) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 27)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 27))) with (mtfv_at ARR1 (gs + 27)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x186ac SC27 Q B (mtfv_at ARR1 (gs + 27)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x186ac + 108)%Z) with (Z_to_bv 64 0x18718).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 27))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 27)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 28 + 1)%Z with (gs + 29)%Z in RES by lia.
    pose proof (put_syms_NZM 19 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28)))) LENA CODA ARR1 sel (gs + 29)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 28) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 28)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 28))) with (mtfv_at ARR1 (gs + 28)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1871c SC28 Q B (mtfv_at ARR1 (gs + 28)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1871c + 108)%Z) with (Z_to_bv 64 0x18788).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 28))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 28)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 29 + 1)%Z with (gs + 30)%Z in RES by lia.
    pose proof (put_syms_NZM 18 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29)))) LENA CODA ARR1 sel (gs + 30)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 29) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 29)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 29))) with (mtfv_at ARR1 (gs + 29)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1878c SC29 Q B (mtfv_at ARR1 (gs + 29)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1878c + 108)%Z) with (Z_to_bv 64 0x187f8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 29))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 29)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 30 + 1)%Z with (gs + 31)%Z in RES by lia.
    pose proof (put_syms_NZM 17 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30)))) LENA CODA ARR1 sel (gs + 31)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 30) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 30)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 30))) with (mtfv_at ARR1 (gs + 30)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x187fc SC30 Q B (mtfv_at ARR1 (gs + 30)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x187fc + 108)%Z) with (Z_to_bv 64 0x18868).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 30))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 30)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 31 + 1)%Z with (gs + 32)%Z in RES by lia.
    pose proof (put_syms_NZM 16 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31)))) LENA CODA ARR1 sel (gs + 32)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 31) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 31)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 31))) with (mtfv_at ARR1 (gs + 31)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1886c SC31 Q B (mtfv_at ARR1 (gs + 31)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1886c + 108)%Z) with (Z_to_bv 64 0x188d8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 31))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 31)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 32 + 1)%Z with (gs + 33)%Z in RES by lia.
    pose proof (put_syms_NZM 15 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32)))) LENA CODA ARR1 sel (gs + 33)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 32) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 32)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 32))) with (mtfv_at ARR1 (gs + 32)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x188dc SC32 Q B (mtfv_at ARR1 (gs + 32)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x188dc + 108)%Z) with (Z_to_bv 64 0x18948).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 32))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 32)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 33 + 1)%Z with (gs + 34)%Z in RES by lia.
    pose proof (put_syms_NZM 14 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 33))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 33)))) LENA CODA ARR1 sel (gs + 34)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 33) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 33)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 33))) with (mtfv_at ARR1 (gs + 33)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x1894c SC33 Q B (mtfv_at ARR1 (gs + 33)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x1894c + 108)%Z) with (Z_to_bv 64 0x189b8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 33))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 33))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 33))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 33)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 34 + 1)%Z with (gs + 35)%Z in RES by lia.
    pose proof (put_syms_NZM 13 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 34))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 34)))) LENA CODA ARR1 sel (gs + 35)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 34) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 34)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 34))) with (mtfv_at ARR1 (gs + 34)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x189bc SC34 Q B (mtfv_at ARR1 (gs + 34)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x189bc + 108)%Z) with (Z_to_bv 64 0x18a28).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 34))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 34))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 34))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 34)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 35 + 1)%Z with (gs + 36)%Z in RES by lia.
    pose proof (put_syms_NZM 12 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 35))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 35)))) LENA CODA ARR1 sel (gs + 36)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 35) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 35)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 35))) with (mtfv_at ARR1 (gs + 35)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18a2c SC35 Q B (mtfv_at ARR1 (gs + 35)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18a2c + 108)%Z) with (Z_to_bv 64 0x18a98).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 35))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 35))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 35))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 35)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 36 + 1)%Z with (gs + 37)%Z in RES by lia.
    pose proof (put_syms_NZM 11 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 36))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 36)))) LENA CODA ARR1 sel (gs + 37)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 36) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 36)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 36))) with (mtfv_at ARR1 (gs + 36)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18a9c SC36 Q B (mtfv_at ARR1 (gs + 36)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18a9c + 108)%Z) with (Z_to_bv 64 0x18b08).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 36))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 36))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 36))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 36)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 37 + 1)%Z with (gs + 38)%Z in RES by lia.
    pose proof (put_syms_NZM 10 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 37))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 37)))) LENA CODA ARR1 sel (gs + 38)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 37) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 37)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 37))) with (mtfv_at ARR1 (gs + 37)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18b0c SC37 Q B (mtfv_at ARR1 (gs + 37)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18b0c + 108)%Z) with (Z_to_bv 64 0x18b78).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 37))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 37))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 37))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 37)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 38 + 1)%Z with (gs + 39)%Z in RES by lia.
    pose proof (put_syms_NZM 9 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 38))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 38)))) LENA CODA ARR1 sel (gs + 39)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 38) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 38)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 38))) with (mtfv_at ARR1 (gs + 38)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18b7c SC38 Q B (mtfv_at ARR1 (gs + 38)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18b7c + 108)%Z) with (Z_to_bv 64 0x18be8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 38))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 38))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 38))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 38)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 39 + 1)%Z with (gs + 40)%Z in RES by lia.
    pose proof (put_syms_NZM 8 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 39))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 39)))) LENA CODA ARR1 sel (gs + 40)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 39) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 39)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 39))) with (mtfv_at ARR1 (gs + 39)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18bec SC39 Q B (mtfv_at ARR1 (gs + 39)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18bec + 108)%Z) with (Z_to_bv 64 0x18c58).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 39))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 39))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 39))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 39)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 40 + 1)%Z with (gs + 41)%Z in RES by lia.
    pose proof (put_syms_NZM 7 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 40))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 40)))) LENA CODA ARR1 sel (gs + 41)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 40) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 40)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 40))) with (mtfv_at ARR1 (gs + 40)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18c5c SC40 Q B (mtfv_at ARR1 (gs + 40)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18c5c + 108)%Z) with (Z_to_bv 64 0x18cc8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 40))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 40))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 40))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 40)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 41 + 1)%Z with (gs + 42)%Z in RES by lia.
    pose proof (put_syms_NZM 6 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 41))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 41)))) LENA CODA ARR1 sel (gs + 42)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 41) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 41)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 41))) with (mtfv_at ARR1 (gs + 41)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18ccc SC41 Q B (mtfv_at ARR1 (gs + 41)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18ccc + 108)%Z) with (Z_to_bv 64 0x18d38).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 41))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 41))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 41))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 41)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 42 + 1)%Z with (gs + 43)%Z in RES by lia.
    pose proof (put_syms_NZM 5 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 42))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 42)))) LENA CODA ARR1 sel (gs + 43)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 42) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 42)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 42))) with (mtfv_at ARR1 (gs + 42)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18d3c SC42 Q B (mtfv_at ARR1 (gs + 42)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18d3c + 108)%Z) with (Z_to_bv 64 0x18da8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 42))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 42))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 42))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 42)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 43 + 1)%Z with (gs + 44)%Z in RES by lia.
    pose proof (put_syms_NZM 4 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 43))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 43)))) LENA CODA ARR1 sel (gs + 44)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 43) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 43)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 43))) with (mtfv_at ARR1 (gs + 43)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18dac SC43 Q B (mtfv_at ARR1 (gs + 43)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18dac + 108)%Z) with (Z_to_bv 64 0x18e18).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 43))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 43))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 43))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 43)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 44 + 1)%Z with (gs + 45)%Z in RES by lia.
    pose proof (put_syms_NZM 3 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 44))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 44)))) LENA CODA ARR1 sel (gs + 45)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 44) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 44)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 44))) with (mtfv_at ARR1 (gs + 44)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18e1c SC44 Q B (mtfv_at ARR1 (gs + 44)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18e1c + 108)%Z) with (Z_to_bv 64 0x18e88).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 44))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 44))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 44))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 44)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 45 + 1)%Z with (gs + 46)%Z in RES by lia.
    pose proof (put_syms_NZM 2 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 45))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 45)))) LENA CODA ARR1 sel (gs + 46)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 45) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 45)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 45))) with (mtfv_at ARR1 (gs + 45)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18e8c SC45 Q B (mtfv_at ARR1 (gs + 45)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18e8c + 108)%Z) with (Z_to_bv 64 0x18ef8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 45))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 45))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 45))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 45)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 46 + 1)%Z with (gs + 47)%Z in RES by lia.
    pose proof (put_syms_NZM 1 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 46))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 46)))) LENA CODA ARR1 sel (gs + 47)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 46) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 46)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 46))) with (mtfv_at ARR1 (gs + 46)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18efc SC46 Q B (mtfv_at ARR1 (gs + 46)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18efc + 108)%Z) with (Z_to_bv 64 0x18f68).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 46))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 46))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 46))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 46)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_S in RES. replace (gs + 47 + 1)%Z with (gs + 48)%Z in RES by lia.
    pose proof (put_syms_NZM 0 (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 47))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 47)))) LENA CODA ARR1 sel (gs + 48)) as NZ;
      rewrite RES in NZ; unfold NZM in NZ.
    pose proof (MTFV (gs + 47) ltac:(lia)) as MV.
    cps_destruct MEM as (EH1 & EH2 & AR2 & AR1 & REST).
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 47)) _ AR1 ltac:(lia) ltac:(bz_params; lia) ZB1 eq_refl) as RD.
    change (rd16 ARR1 (2 * (gs + 47))) with (mtfv_at ARR1 (gs + 47)) in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    eapply (BLK 0x18f6c SC47 Q B (mtfv_at ARR1 (gs + 47)) m); [exact OKB| exact MV| lia| exact XB| exact (conj EH1 (conj EH2 (conj AR2 (conj AR1 REST))))|].
    clear EH1 EH2 AR2 AR1 REST XB m t0 t1 a4 a5 xb.
    intros m t0 t1 a4 a5 xb MEM XB. change (Z_to_bv 64 (0x18f6c + 108)%Z) with (Z_to_bv 64 0x18fd8).
    pose proof (bw_ok_bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 47))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 47))) OKB
                  ltac:(pose proof (LENFs _ MV); lia) ltac:(pose proof (CODFs _ MV); lia)) as OKB'.
    clear OKB NZ MV. revert t0 t1 a4 a5 xb m OKB' XB MEM RES.
    generalize (bsW B (zget LENA (258 * sel + mtfv_at ARR1 (gs + 47))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 47)))). clear B.
    intros B t0 t1 a4 a5 xb m OKB XB MEM RES.
    (* [comment removed for export] *)
    rewrite put_syms_0 in RES. subst B. eapply K; [exact MEM| exact XB| exact OKB].
  Qed.
End SDB4.

End ACeilS1.
End S0_cmp_sdB4.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Module S0_cmp_sdB5.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.StoreFast.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzSepTac.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdC.S0_cmp_sdB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdC.S0_cmp_sdB2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdC.S0_cmp_sdB3 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdC.S0_cmp_sdB4.
 Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Local Open Scope bv_scope.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut6.   (* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpLiaP.   (* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
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
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepVS.tslia_vs.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDB5.
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
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.

  (* [comment removed for export] *)
  Variables (sc gs : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i < gs + 50)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).
  Lemma Hsel : (0 <= sel < 6)%Z. Proof. pose proof (SELF sc Hsc). lia. Qed.
  Lemma LENFs : forall v, (0 <= v < A)%Z -> zdef LENA (258 * sel + v) = true /\ (1 <= zget LENA (258 * sel + v) <= 17)%Z.
  Proof. intros v Hv. apply LENF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.
  Lemma CODFs : forall v, (0 <= v < A)%Z -> zdef CODA (258 * sel + v) = true /\ (0 <= zget CODA (258 * sel + v) < 4294967296)%Z.
  Proof. intros v Hv. apply CODF; [| exact Hv]. pose proof (SELF sc Hsc). lia. Qed.

  Notation MT := (A1 + 2 * gs)%Z. Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  (* [comment removed for export] *)
  Notation RG ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 gs) (Z_to_bv 64 (gs + 50)) a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)
         (Z_to_bv 64 (gs + 49)) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6).
  Notation BLK := (S0_itah_blk cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).
  Notation HEAD := (S0_itah_head cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 sel gs A Hsel HA LENFs CODFs).

  Notation APP f := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A HA HG HNS LENF CODF SELF ZB1 sc gs Hsc Hgs HgsE MTFV) (only parsing).
  Notation APP2 f := (f cx g e sp gp tp F fc CX SEP Gmtf Gbs Gzb Hnb USP1 LIM HLIM nG nSel sv W m0 i16 A HA HG LENF CODF SELF ZB1 sc gs Hsc Hgs HgsE MTFV) (only parsing).

  (* [comment removed for export] *)
  Lemma S0_fast50 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte)
      (ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 : word),
    let bf := sm_put_syms 50 b LENA CODA ARR1 sel gs in
    bw_ok b -> (bw_numZ bf <= LIM)%Z ->
    MD b m ->
    (forall m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
        MD bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RG ra t0' t1' a1' a2' a3' a4' a5' a6' a7' s4 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19164) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x17ab0) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b m ra t0 t1 a1 a2 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6. cbv zeta. intros OK NL MEM K.
    pose proof (SELF sc Hsc) as [SD SR].
    (* [comment removed for export] *)
    set (v0 := mtfv_at ARR1 gs). set (n0 := zget LENA (258 * sel + v0)). set (c0 := zget CODA (258 * sel + v0)).
    set (b1 := bsW b n0 c0).
    set (b25 := sm_put_syms 24 b1 LENA CODA ARR1 sel (gs + 1)).
    set (b48 := sm_put_syms 23 b25 LENA CODA ARR1 sel (gs + 25)).
    set (v48 := mtfv_at ARR1 (gs + 48)). set (n48 := zget LENA (258 * sel + v48)). set (c48 := zget CODA (258 * sel + v48)).
    set (b49 := bsW b48 n48 c48).
    set (v49 := mtfv_at ARR1 (gs + 49)). set (n49 := zget LENA (258 * sel + v49)). set (c49 := zget CODA (258 * sel + v49)).
    set (b50 := bsW b49 n49 c49).
    assert (E50 : sm_put_syms 50 b LENA CODA ARR1 sel gs = b50).
    { change 50%nat with (1 + 24 + 23 + 1 + 1)%nat. rewrite !put_syms_split. rewrite !put_syms_S, !put_syms_0.
      subst b50 b49 b48 b25 b1 v49 n49 c49 v48 n48 c48 v0 n0 c0.
      replace (gs + Z.of_nat 1)%Z with (gs + 1)%Z by lia.
      replace (gs + Z.of_nat (1 + 24))%Z with (gs + 25)%Z by lia.
      replace (gs + Z.of_nat (1 + 24 + 23))%Z with (gs + 48)%Z by lia.
      replace (gs + Z.of_nat (1 + 24 + 23 + 1))%Z with (gs + 49)%Z by lia. reflexivity. }
    rewrite E50 in NL, K.
    (* [comment removed for export] *)
    pose proof (bsW_NZM b49 n49 c49) as Z49. unfold NZM in Z49. fold b50 in Z49.
    pose proof (bsW_NZM b48 n48 c48) as Z48. unfold NZM in Z48. fold b49 in Z48.
    pose proof (put_syms_NZM 23 b25 LENA CODA ARR1 sel (gs + 25)) as Z25. unfold NZM in Z25. fold b48 in Z25.
    pose proof (put_syms_NZM 24 b1 LENA CODA ARR1 sel (gs + 1)) as Z1. unfold NZM in Z1. fold b25 in Z1.
    (* [comment removed for export] *)
    (eapply (APP S0_blk0 Q b m) || eapply (APP2 S0_blk0 Q b m)); [exact OK| subst v0 n0 c0; fold b1; lia| exact MEM|].
    fold v0. fold n0 c0. fold b1. clear MEM. intros m1 t0_1 t1_1 a4_1 a5_1 a6_1 MEM X6.
    assert (OK1 : bw_ok b1).
    { subst b1 n0 c0 v0. pose proof (MTFV gs ltac:(lia)) as MV. apply bw_ok_bsW; [exact OK| pose proof (LENF sel _ ltac:(lia) MV); lia| pose proof (CODF sel _ ltac:(lia) MV); lia]. }
    (* [comment removed for export] *)
    (eapply (APP S0_blocks_1_24 Q b1 m1) || eapply (APP2 S0_blocks_1_24 Q b1 m1)); [exact OK1| fold b25; lia| exact X6| exact MEM|].
    fold b25. clear MEM X6. intros m2 t0_2 t1_2 a4_2 a5_2 a6_2 MEM X6 OK25.
    (eapply (APP S0_blocks_25_47 Q b25 m2) || eapply (APP2 S0_blocks_25_47 Q b25 m2)); [exact OK25| fold b48; lia| exact X6| exact MEM|].
    fold b48. clear MEM X6. intros m3 t0_3 t1_3 a4_3 a5_3 a6_3 MEM X6 OK48.
    (* [comment removed for export] *)
    (eapply (APP S0_blk48 Q b48 m3) || eapply (APP2 S0_blk48 Q b48 m3)); [exact OK48| fold v48; fold n48 c48; fold b49; lia| exact X6| exact MEM|].
    fold v48. fold n48 c48. fold b49. clear MEM X6. intros m4 t0_4 t1_4 a4_4 a6_4 a7_4 MEM X4.
    assert (OK49 : bw_ok b49).
    { subst b49 n48 c48 v48. pose proof (MTFV (gs + 48) ltac:(lia)) as MV. apply bw_ok_bsW; [exact OK48| pose proof (LENF sel _ ltac:(lia) MV); lia| pose proof (CODF sel _ ltac:(lia) MV); lia]. }
    (* [comment removed for export] *)
    (eapply (APP S0_blk49 Q b49 m4) || eapply (APP2 S0_blk49 Q b49 m4)); [exact OK49| fold v49; fold n49 c49; fold b50; lia| exact X4| exact MEM|].
    fold v49. fold n49 c49. fold b50. clear MEM X4. intros m5 t0_5 t1_5 a1_5 a2_5 a3_5 a4_5 a5_5 a6_5 a7_5 MEM.
    eapply K; [exact MEM|].
    subst b50 n49 c49 v49. pose proof (MTFV (gs + 49) ltac:(lia)) as MV. apply bw_ok_bsW; [exact OK49| pose proof (LENF sel _ ltac:(lia) MV); lia| pose proof (CODF sel _ ltac:(lia) MV); lia].
  Qed.
End SDB5.

End ACeilS1.
End S0_cmp_sdB5.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSD0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSdTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCNumZ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzWalkArith4 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_sdC.S0_cmp_sdB5.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section SDC.
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
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.

  (* [comment removed for export] *)
  Variables (sc gs ge : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs <= ge)%Z. Hypothesis Hge : (ge <= gs + 49)%Z.
  Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i <= ge)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).
  Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  (* [comment removed for export] *)
  Notation RX ra t0 t1 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s9 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)
         s9 (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_slow_flush : forall (i : Z) (Q : machine_state -> Prop) (f : nat) (b : bw) (m : word -> option byte)
      (ra t0 t1 a3 a4 a7 s4 t3 t4 t5 t6 : word) (xb a20 a60 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z ->
    (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall b1 m' (xb' a6' : word),
        b1 = bs_needw f b -> MD b1 m' -> (bv_unsigned xb' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 i) (Z_to_bv 64 (ge + 1)) xb' (Z_to_bv 64 (bw_live b1)) a3 a4 (Z_to_bv 64 (bw_numZ b1)) a6' a7 (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8) (Z_to_bv 64 ge) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6)
            F (Z_to_bv 64 0x19140) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 E) (Z_to_bv 64 i) (Z_to_bv 64 (ge + 1)) xb a20 a3 a4 (Z_to_bv 64 (bw_numZ b)) a60 a7 (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 3006) s4 (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8) (Z_to_bv 64 ge) (Z_to_bv 64 15) (Z_to_bv 64 A1) t3 t4 t5 t6)
            F (Z_to_bv 64 0x19108) fc None m (seg_rom s0segs)).
  Proof.
    intros i Q f. induction f as [|f IH]; intros b m ra t0 t1 a3 a4 a7 s4 t3 t4 t5 t6 xb a20 a60 OK L8 Lf NL X4 MEM K; [lia|].
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
      + intros b1 m' xb' a6' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - enter_with (K (bw_emit b) m); [st_eq| | | | lia].
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeMD.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_slow_tail : forall (Q : machine_state -> Prop) (i : Z) (b b1 : bw) (m : word -> option byte)
      (n : nat) (ra t0 t1 a5 a6 a7 s4 t3 t4 t5 t6 xb : word),
    (i + Z.of_nat (S n) = ge + 1)%Z -> (gs <= i)%Z ->
    let v := mtfv_at ARR1 i in let nv := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    let bf := sm_put_syms n (bsW b nv cv) LENA CODA ARR1 sel (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b1)%Z ->
    MD b1 m ->
    (* [comment removed for export] *)
    (forall (Q : machine_state -> Prop) (i : Z) (b : bw) (m : word -> option byte)
      (ra t0 t1 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 xb : word),
      (1 <= n)%nat -> (i + Z.of_nat n = ge + 1)%Z -> (gs <= i)%Z ->
      let bf := sm_put_syms n b LENA CODA ARR1 sel i in
      bw_ok b -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
      MD b m ->
      (forall m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
          MD bf m' -> bw_ok bf ->
          evt s0segs Q (MS (RX ra t0' t1' (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 (ge + 1)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (E + 1704 + sc)) s4 (Z_to_bv 64 ge) t3 t4 t5 t6)
                            F (Z_to_bv 64 0x19164) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (RX ra t0 t1 (Z_to_bv 64 i) (Z_to_bv 64 (ge + 1)) xb (Z_to_bv 64 (bw_live b)) a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 1704 + sc)) s4 (Z_to_bv 64 ge) t3 t4 t5 t6)
                        F (Z_to_bv 64 0x190c8) fc None m (seg_rom s0segs))) ->
    (forall m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
        MD bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RX ra t0' t1' (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 (ge + 1)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (E + 1704 + sc)) s4 (Z_to_bv 64 ge) t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19164) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RX ra t0 t1 (Z_to_bv 64 i) (Z_to_bv 64 (ge + 1)) xb (Z_to_bv 64 (bw_live b1)) (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 nv) a5 a6 a7 (Z_to_bv 64 (E + 1704 + sc)) s4 (Z_to_bv 64 ge) t3 t4 t5 t6)
                      F (Z_to_bv 64 0x19140) fc None m (seg_rom s0segs)).
  Proof.
    intros Q i b b1 m n ra t0 t1 a5 a6 a7 s4 t3 t4 t5 t6 xb Hn Hi. cbv zeta. intros OK Eb1 NL XB MEM IHn K.
    set (v := mtfv_at ARR1 i) in *. set (nv := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (put_syms_NZM n (bsW b nv cv) LENA CODA ARR1 sel (i + 1)) as NZ1. unfold NZM in NZ1.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    pose proof (MTFV i ltac:(lia)) as MV. fold v in MV. pose proof (SELF sc Hsc) as [SD SR].
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG]. fold nv in LD, LRG. fold cv in CD, CRG.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    rewrite (neg_shift_amount (bw_live b1) nv) by lia.
    replace (bw_live b1 + nv =? 32)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - nv)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ xb (bw_buff b1) XB) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    assert (EBW : bsW b nv cv = BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - nv)) mod 4294967296)) (bw_live b1 + nv) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b nv cv)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (IHn Q (i + 1)%Z (bsW b nv cv) m); [st_eq; rewrite EBW; reflexivity| lia| lia| lia| exact OK2| exact NL| | rewrite EBW; closeMD| exact K].
      rewrite EBW. cbn [bw_buff]. rewrite (low32_or_shifted _ _ xb (bw_buff b1) XB) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      apply low32_small. change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
    - (* [comment removed for export] *)
      assert (n = 0%nat) by lia. subst n. rewrite put_syms_0 in K.
      enter_with (K m _ _ _ _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_slow_loop : forall (n : nat) (Q : machine_state -> Prop) (i : Z) (b : bw) (m : word -> option byte)
      (ra t0 t1 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 xb : word),
    (1 <= n)%nat -> (i + Z.of_nat n = ge + 1)%Z -> (gs <= i)%Z ->
    let bf := sm_put_syms n b LENA CODA ARR1 sel i in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    MD b m ->
    (forall m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
        MD bf m' -> bw_ok bf ->
        evt s0segs Q (MS (RX ra t0' t1' (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 (ge + 1)) a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 (E + 1704 + sc)) s4 (Z_to_bv 64 ge) t3 t4 t5 t6)
                          F (Z_to_bv 64 0x19164) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RX ra t0 t1 (Z_to_bv 64 i) (Z_to_bv 64 (ge + 1)) xb (Z_to_bv 64 (bw_live b)) a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 1704 + sc)) s4 (Z_to_bv 64 ge) t3 t4 t5 t6)
                      F (Z_to_bv 64 0x190c8) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]; [lia|].
    intros Q i b m ra t0 t1 a3 a4 a5 a6 a7 s4 t3 t4 t5 t6 xb _ Hn Hi. cbv zeta. intros OK NL XB MEM K.
    rewrite put_syms_S in NL, K.
    set (v := mtfv_at ARR1 i) in *. set (nv := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (put_syms_NZM n (bsW b nv cv) LENA CODA ARR1 sel (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b nv cv) as NZ0. unfold NZM in NZ0.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openMD MEM. bz_params.
    cps_pose OK as (OKb & OKl & OKn).
    pose proof (MTFV i ltac:(lia)) as MV. fold v in MV. pose proof (SELF sc Hsc) as [SD SR].
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG]. fold nv in LD, LRG. fold cv in CD, CRG.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 1704) SELA (jseg J 1704 18002) 18002 sc _ SEL ltac:(lia) SD eq_refl) as RD0.
    wstep. clear RD0. cbv beta. rewrite (unsigned_lit8 sel) by lia.
    (* [comment removed for export] *)
    wstep. wstep.
    (* [comment removed for export] *)
    pose proof (zb8_read2 s0segs m A1 ARR1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB1 eq_refl) as RD1.
    change (rd16 ARR1 (2 * i)) with (mtfv_at ARR1 i) in RD1. fold v in RD1.
    wstep. clear RD1. rewrite zx16_small by lia.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    pose proof (ovb_read1 s0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(cbv delta [wa]; f_equal; lia)) as RD2.
    wstep. clear RD2. cbv beta. fold nv. rewrite (unsigned_lit8 nv) by lia.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(cbv delta [wa]; f_equal; lia)) as RD3.
    wstep. clear RD3. fold cv.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      eapply (S0_slow_tail Q i b b m n); [lia | lia | exact OK| | exact NL| exact XB| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - (* [comment removed for export] *)
      wstep.
      enter_with (S0_slow_flush i Q BS_FUEL b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | exact XB| closeMD|].
      { pose proof (bsW_bytes b nv cv) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' xb' a6' Eb1 MEM' XB' L1.
      eapply (S0_slow_tail Q i b b1 m' n); [lia| lia| exact OK| exact Eb1| exact NL| exact XB'| exact MEM'| exact IH| exact K].
  Qed.
End SDC.

End ACeilS1.
