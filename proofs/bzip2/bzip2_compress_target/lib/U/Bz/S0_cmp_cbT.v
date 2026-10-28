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

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Module S0_cmp_bsw.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith.
 Unset Lia Cache.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.ACeil.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParams.
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
(* [comment removed for export] *)
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "qal" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.

Import ListNotations. Local Open Scope bv_scope.
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
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section BSW.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g : eg) (e : est) (v lo : Z).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A2 := (c_A2 cx).
  Notation nblock := (e_nblock e). Notation b0 := (e_bw e).
  Hypothesis CX : cctx_ok cx. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hv : (0 <= v < 256)%Z. Hypothesis OK0 : bw_ok b0. Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis ROOM : (nblock + bw_numZ b0 + 4 <= ARR2_SIZE)%Z.
  Hypothesis SEP2 : apart E ESTATE_SIZE A2 ARR2_SIZE.
  Hypothesis SPE : (usp <= E \/ E + ESTATE_SIZE <= lo)%Z.
  Hypothesis SPA : (usp <= A2 \/ A2 + ARR2_SIZE <= lo)%Z.

  Notation W := (bsW8_W cx e).
  Notation POST := (bsW8_post s0segs cx g e v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  (* [comment removed for export] *)
  Definition MEMb (b : bw) (m : word -> option byte) : Prop :=
    rw_cells s0segs m E (EHEAD1 cx g (est_set_bw e b)) /\ rw_cells s0segs m (E + 640) (EHEAD2 cx g (est_set_bw e b)) /\
    u8arr s0segs m A2 (zb8 (zbl (e_arr2 e) nblock b) ARR2_SIZE) /\
    mem_inv s0segs m /\ munch W m0 m /\ wmono s0segs m0 m /\ stk s0segs m lo usp.

  Ltac prep :=
    let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB); try lin16 ALE; try lin16 AL1; try lin16 AL2; try lin16 ALF; try lin16 ALB; try lin16 ALFb;
    pose proof SEP2 as SEP2'; pose proof SPE as SPE'; pose proof SPA as SPA'; unfold apart, ESTATE_SIZE in SEP2', SPE', SPA';
    unfold ESTATE_SIZE in *.

  Variables (t1 t2 t3 t4 t5 t6 : word).
  Notation ST pc x5 x12 x13 x14 x15 x16 x17 m :=
    (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None m (seg_rom s0segs)).
  Local Ltac nt := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => notrap | _ => idtac end.

  (* [comment removed for export] *)
  Lemma bsw_loop : forall (f : nat) (b : bw) (m : word -> option byte) (x5 x13 x15 x16 x17 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ b0 <= bw_numZ b)%Z ->
    (8 * bw_numZ b + bw_live b = 8 * bw_numZ b0 + bw_live b0)%Z ->
    (bv_unsigned x15 mod 4294967296 = bw_buff b)%Z ->
    MEMb b m ->
    (forall b1 m' (x5' x12' x14' x15' x16' x17' : word),
        b1 = bs_needw f b -> MEMb b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs POST (ST 0x16c30 x5' x12' (Z_to_bv 64 (bw_live b1)) x14' x15' x16' x17' m')) ->
    evt s0segs POST (ST 0x16bcc x5 (Z_to_bv 64 7) x13 (Z_to_bv 64 (bw_numZ b)) x15 x16 x17 m).
  Proof.
    induction f as [|f IH]; intros b m x5 x13 x15 x16 x17 OK L8 Lf N0 N4 X15 MEM K; [lia|].
    prep. cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. cbn [g_zbits] in EH1 || idtac. rewrite Gzb in EH1.
    unfold bsW8_W in MU, K |- *.
    cps_destruct OK as (OKb & OKl & OKn). cps_pose OK0 as (OK0b & OK0l & OK0n).
    (* [comment removed for export] *)
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(bz_params; lia)) as LA2.
    bz_params.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    wstep. wstep.
    wstep. flags. wstep. flags. wstep. nt.
    wstep. flags. wstep. flags. wstep. flags. wstep. flags. wstep. nt. wstep. nt.
    wstep.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. nt.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    (* [comment removed for export] *)
    wstep. nt. wstep.
    (* [comment removed for export] *)
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    (* [comment removed for export] *)
    lazymatch type of AR2 with context [wr8 (zbl (e_arr2 e) nblock b) ?i ?u] =>
      replace (wr8 (zbl (e_arr2 e) nblock b) i u) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite X15. rewrite unsigned_lit by lia. reflexivity. }
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (bw_emit b) mm _ _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| lia| lia| | |] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
             e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
             e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
      + intros b1 m' x5' x12' x14' x15' x16' x17' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - (* [comment removed for export] *)
      (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
             e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
             e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
  Qed.

  (* [comment removed for export] *)
  Lemma bsw_tail : forall (b1 : bw) (m : word -> option byte) (x5 x12 x14 x15 x16 x17 : word),
    b1 = bs_needw BS_FUEL b0 -> (0 <= bw_live b1 < 8)%Z -> MEMb b1 m ->
    evt s0segs POST (ST 0x16c30 x5 x12 (Z_to_bv 64 (bw_live b1)) x14 x15 x16 x17 m).
  Proof using BZP ACEIL__ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e v lo CX Gbs Gzb Hv OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6.
    intros b1 m x5 x12 x14 x15 x16 x17 Eb1 L1 MEM.
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsW8_W in MU |- *.
    cps_pose (bs_needw_post BS_FUEL b0 OK0 ltac:(cps_destruct OK0 as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK0 as (OK0b & OK0l & OK0n).
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. nt.
    wstep. wstep. wstep. nt.
    wstep. wstep. nt.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep.
    replace ((32 - bw_live b1 + -8) mod 32)%Z with (32 - bw_live b1 - 8)%Z in EH2 by (rewrite Z.mod_small by lia; lia).
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl v (32 - bw_live b1 - 8)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 v _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    wstep. unfold bsW8_post. cbv zeta.
    finish.
    - unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw bsW bw_numZ]. rewrite Gzb. subst b1. exact EH1.
    - unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF bsW bw_buff bw_live]. rewrite Gbs. subst b1. exact EH2.
    - rewrite (zbl_same_bytes (e_arr2 e) nblock b1 (bsW b0 8 v)); [exact AR2| subst b1; CmpFast.bsw_same| subst b1; CmpFast.bsw_same].
  Qed.

  Lemma bsw_entry : forall (x5 x12 x13 x14 x15 x16 x17 : word),
    MEMb b0 m0 ->
    evt s0segs POST (ST 0x16bac x5 x12 x13 x14 x15 x16 x17 m0).
  Proof.
    intros x5 x12 x13 x14 x15 x16 x17 MEM.
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsW8_W in MU |- *.
    cps_pose OK0 as (OK0b & OK0l & OK0n).
    (* [comment removed for export] *)
    wstep. wstep. nt. wstep. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (bsw_tail b0 m0 _ _ _ _ _ _); [st_eq| | lia| ].
      + unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b0)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
             e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
             e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. exact EH2.
    - (* [comment removed for export] *)
      wstep. wstep. wstep.
      enter_with (bsw_loop BS_FUEL b0 m0 _ _ _ _ _); [st_eq| exact OK0| lia| unfold BS_FUEL; cbn; lia| lia| lia| | |].
      + rewrite low32_sx32, low32_lit. apply Z.mod_small. lia.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
             e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
             e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. exact EH2.
      + intros b1 m' x5' x12' x14' x15' x16' x17' Eb1 MEM' L1. eapply (bsw_tail b1 m'); [exact Eb1| exact L1| exact MEM'].
  Qed.
End BSW.

Theorem S0_bsW8 : bsW8_spec S0C.
Proof.
  unfold bsW8_spec. cbn [ci_segs ci_bsW8 S0C]. intros until lo. intros -> -> Hv EH1 EH2 AR2 MI ST LO CX SEP Gbs Gzb OK Hnb ROOM.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. cps_destruct CX' as (_ & RE2 & _ & _ & _ & RA2' & _).
  unfold cctx_sep in SEP. cbv zeta in SEP. cps_destruct SEP as (_ & SEP2 & _).
  eapply bsw_entry; try eassumption; [lia | lia |].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [apply munch_refl|]. split; [apply wmono_refl| eassumption].
Qed.

End ACeilS1.
End S0_cmp_bsw.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutBsw S0_cmp_bsx4. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutCB. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutCBw.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutSM OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpSdTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCNumZ OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzWalkArith4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_cbT.S0_cmp_bsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutBsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_bsx4 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCB OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutCBw.
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
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section CBT.
  Variables (cx : cctx) (g : eg) (e : est).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 384 <= 18446744073709551616)%Z.
  Ltac openCX := openCX3 CX SEP USP1.
  Local Ltac nt := lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => notrap | _ => idtac end.
  (* [comment removed for export] *)
  Definition cbT_W : list (Z * Z) := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE)]%Z.

  (* [comment removed for export] *)
  Lemma hi_transport : forall m m' A cs, (CEIL <= A)%Z -> rw_cells s0segs m A cs -> munch cbT_W m m' -> wmono s0segs m m' -> rw_cells s0segs m' A cs.
  Proof.
    intros m m' A cs HA H MU WM. openCX. eapply rw_cells_transport; [exact H| exact MU| exact WM|].
    bz_ceil; bz_params; unfold cbT_W, CEIL in *. cbv [disjoint_from fst snd]. repeat split; try exact I; lia.
  Qed.
  (* [comment removed for export] *)

  Lemma stk_hi_transport : forall m m' lo, (CEIL <= lo)%Z -> stk s0segs m lo usp -> munch cbT_W m m' -> wmono s0segs m m' -> stk s0segs m' lo usp.
  Proof.
    intros m m' lo Hlo H MU WM. openCX. eapply stk_transport_disjoint; [exact H| exact MU| exact WM|].
    bz_ceil; bz_params; unfold cbT_W, CEIL in *. cbv [disjoint_from fst snd]. repeat split; try exact I; lia.
  Qed.

  Notation SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra :=
    [C8 x11; C8 x10; C8 x9; C8 x8; C8 x7; C8 x6; C8 x5; C8 x4; C8 x3; C8 x2; C8 x1; C8 x0; C8 xra].

  (* [comment removed for export] *)
  Definition EH1b (m : word -> option byte) (b : bw) : Prop := rw_cells s0segs m E (EHEAD1 cx g (est_set_bw e b)).
  Definition EH2b (m : word -> option byte) (b : bw) : Prop := rw_cells s0segs m (E + 640) (EHEAD2 cx g (est_set_bw e b)).
  Definition AR2b (m : word -> option byte) (b : bw) : Prop := u8arr s0segs m A2 (zb8 (zbl (e_arr2 e) nblock b) ARR2_SIZE).

  (* [comment removed for export] *)
  Lemma bsw8_call : forall (Q : machine_state -> Prop) (b : bw) (v : Z) (m : word -> option byte) (lo : Z)
      (ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= v < 256)%Z -> bw_ok b -> (nblock + bw_numZ b + 4 <= ARR2_SIZE)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m -> stk s0segs m lo usp -> (CEIL <= lo)%Z ->
    (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        let b' := bsW b 8 v in
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv s0segs m' -> stk s0segs m' lo usp -> munch cbT_W m m' -> wmono s0segs m m' ->
        evt s0segs Q (MS (mkR ra sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 E) (Z_to_bv 64 v) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x16bac) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b v m lo ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hv OK ROOM EH1 EH2 AR2 MI ST Hlo K.
    unfold EH1b, EH2b, AR2b in *.
    pose proof S0_bsW8 as BSW. unfold bsW8_spec in BSW. cbn [ci_segs ci_bsW8 S0C] in BSW.
    eapply evt_cut.
    { eapply (BSW ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g (est_set_bw e b) v lo);
        [reflexivity| reflexivity| exact Hv| exact EH1| exact EH2| cbn_est; exact AR2| exact MI| exact ST| exact Hlo| exact CX| exact SEP| exact Gbs
        | cbn_est; exact Gzb| cbn_est; exact OK| cbn_est; exact Hnb| cbn_est; exact ROOM]. }
    clear EH1 EH2 AR2 MI ST. unfold bsW8_post. cbn_est.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI2 [ST2 [EH1 [EH2 AR2]]]]]]]; subst ms'.
    lazymatch type of MUc with munch _ m ?m' =>
      assert (MU' : munch cbT_W m m');
      [ eapply munch_weaken; [| exact MUc];
        unfold sub_fp, bsW8_W, cbT_W; cbn [outside]; cbn_est; cps_pose OK as (? & ? & ?); pose proof ROOM as RM; bz_params; intros ? ?; lia
      | ] end.
    eapply K; [exact EH1| exact EH2| exact AR2| exact MI2| exact ST2| exact MU'| exact WMc].
  Qed.

  (* [comment removed for export] *)
  Lemma bsput32_call : forall (Q : machine_state -> Prop) (b : bw) (u : Z) (m : word -> option byte) (lo : Z)
      (ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 <= u < 4294967296)%Z -> bw_ok b -> (nblock + bw_numZ b + 16 <= ARR2_SIZE)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m -> stk s0segs m lo usp -> (CEIL <= lo)%Z ->
    (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
        let b' := bsPutUInt32 b u in
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv s0segs m' -> stk s0segs m' lo usp -> munch cbT_W m m' -> wmono s0segs m m' ->
        evt s0segs Q (MS (mkR ra sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                          F (ret_pc ra) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x16c74) fc None m (seg_rom s0segs)).
  Proof.
    intros Q b u m lo ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 Hu OK ROOM EH1 EH2 AR2 MI ST Hlo K.
    unfold EH1b, EH2b, AR2b in *.
    pose proof S0_bsPutUInt32S as BSP. unfold bsPutUInt32_specS in BSP. cbn [ci_segs ci_bsPutUInt32 S0C] in BSP.
    eapply evt_cut.
    { eapply (BSP ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m cx g (est_set_bw e b) u lo);
        [reflexivity| reflexivity| exact Hu| exact EH1| exact EH2| cbn_est; exact AR2| exact MI| exact ST| exact Hlo| exact CX| exact SEP| exact Gbs
        | cbn_est; exact Gzb| cbn_est; exact OK| cbn_est; exact Hnb| cbn_est; exact ROOM]. }
    clear EH1 EH2 AR2 MI ST. unfold bsPutUInt32_post. cbn_est.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI2 [ST2 [EH1 [EH2 AR2]]]]]]]; subst ms'.
    lazymatch type of MUc with munch _ m ?m' =>
      assert (MU' : munch cbT_W m m');
      [ eapply munch_weaken; [| exact MUc];
        unfold sub_fp, bsPutUInt32_W, cbT_W; cbn [outside]; cbn_est; cps_pose OK as (? & ? & ?); pose proof ROOM as RM; bz_params; intros ? ?; lia
      | ] end.
    eapply K; [exact EH1| exact EH2| exact AR2| exact MI2| exact ST2| exact MU'| exact WMc].
  Qed.

  (* [comment removed for export] *)
  Lemma S0_cb_finish : forall (f : nat) (Q : machine_state -> Prop) (b : bw) (m m0 : word -> option byte)
      (ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xb : word),
    (0 <= bw_buff b < 4294967296)%Z -> (0 < bw_live b <= 32)%Z -> (0 <= bw_numZ b)%Z -> (bw_live b <= 8 * Z.of_nat f)%Z ->
    (nblock + bw_numZ b + Z.of_nat f <= ARR2_SIZE)%Z ->
    (bv_unsigned xb mod 4294967296 = bw_buff b)%Z ->
    EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m ->
    munch cbT_W m0 m -> wmono s0segs m0 m ->
    (forall m' (a0' a1' a2' a3' a4' a5' : word),
        let b' := bs_finish f b in
        EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv s0segs m' ->
        munch cbT_W m0 m' -> wmono s0segs m0 m' -> (bw_numZ b' <= bw_numZ b + Z.of_nat f)%Z ->
        evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0' a1' a2' a3' a4' a5' a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 0x16b30) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 (bw_numZ b)) xb a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x16acc) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros Q b m m0 ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 xb OKb OKl OKn Lf ROOM XB EH1 EH2 AR2 MI MU WM K; [lia|].
    unfold EH1b, EH2b, AR2b in EH1, EH2, AR2.
    openCX. unfold EHEAD1, EHEAD2 in EH1, EH2; cbn_est_in EH1; cbn_est_in EH2. rewrite Gbs in EH2. rewrite Gzb in EH1. unfold cbT_W in MU. bz_params.
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    cbn [bs_needw bs_finish] in K. replace (0 <? bw_live b)%Z with true in K by (symmetry; apply Z.ltb_lt; lia).
    (* [comment removed for export] *)
    wstep. wstep. wstep. flags. wstep. flags. wstep. nt. wstep. flags. wstep. flags. wstep. flags. wstep. flags. wstep. nt. wstep. nt. wstep.
    (* [comment removed for export] *)
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. nt. wstep. wstep. wstep. wstep. wstep. wstep. wstep. nt. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite shiftl_mul256, low32_mod, low32_lit, low32_mul, low32_sx32, low32_lit, <- low32_mul. reflexivity. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with context [wr8 (zbl (e_arr2 e) nblock b) ?i ?u] =>
      replace (wr8 (zbl (e_arr2 e) nblock b) i u) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24.
        rewrite XB. rewrite unsigned_lit by lia. reflexivity. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; unfold bv_lts in Kc; [apply Z.ltb_lt in Kc | apply Z.ltb_ge in Kc]; rewrite ?signed_lit_small in Kc by (bz_params; lia).
    - enter_with (IH Q (bw_emit b) _ m0 ra t0 t1 t2 s1 _ _ _ _ a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _);
        [st_eq| unfold bw_emit; cbn [bw_buff]; apply Z.mod_pos_bound; lia| unfold bw_emit; cbn [bw_live]; lia| unfold bw_emit; cbn [bw_numZ]; lia
        | unfold bw_emit; cbn [bw_live]; lia| unfold bw_emit; cbn [bw_numZ]; bz_params; lia| | | | unfold AR2b; exact AR2| assumption| assumption| assumption|].
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + unfold EH1b, EHEAD1, bw_emit. cbn_est. cbn [bw_numZ]. rewrite Gzb. exact EH1.
      + unfold EH2b, EHEAD2, bw_emit. cbn_est. cbn [bw_buff bw_live]. rewrite Gbs. exact EH2.
      + intros m' a0' a1' a2' a3' a4' a5'. cbv zeta. intros EH1' EH2' AR2' MI' MU' WM' NZ'. eapply K; [exact EH1'| exact EH2'| exact AR2'| exact MI'| exact MU'| exact WM'|].
        revert NZ'. unfold bw_emit. cbn [bw_numZ]. intros NZ'. lia.
    - destruct f as [|f']; cbn [bs_finish] in K.
      + enter_with (K _ _ _ _ _ _ _); [st_eq| | | unfold AR2b; exact AR2| assumption| assumption| assumption| unfold bw_emit; cbn [bw_numZ]; lia].
        * unfold EH1b, EHEAD1, bw_emit. cbn_est. cbn [bw_numZ]. rewrite Gzb. exact EH1.
        * unfold EH2b, EHEAD2, bw_emit. cbn_est. cbn [bw_buff bw_live]. rewrite Gbs. exact EH2.
      + replace (0 <? bw_live (bw_emit b))%Z with false in K by (symmetry; apply Z.ltb_ge; unfold bw_emit; cbn [bw_live]; lia).
        enter_with (K _ _ _ _ _ _ _); [st_eq| | | unfold AR2b; exact AR2| assumption| assumption| assumption| unfold bw_emit; cbn [bw_numZ]; lia].
        * unfold EH1b, EHEAD1, bw_emit. cbn_est. cbn [bw_numZ]. rewrite Gzb. exact EH1.
        * unfold EH2b, EHEAD2, bw_emit. cbn_est. cbn [bw_buff bw_live]. rewrite Gbs. exact EH2.
  Qed.

  (* [comment removed for export] *)
  Lemma S0_cb_epilogue : forall (Q : machine_state -> Prop) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word),
    rw_cells s0segs m (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) ->
    evt s0segs Q (MS (mkR xra (Z_to_bv 64 (usp + 384)) gp tp t0 t1 t2 x0 x1 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                      F (ret_pc xra) fc None m (seg_rom s0segs)) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x16b30) fc None m (seg_rom s0segs)).
  Proof.
    intros Q m ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra SAV K.
    pose proof USP1 as U1. bz_ceil; bz_params; unfold CEIL in U1.
    do 13 wstep. wstep. wstep.
    enter_with K. st_eq.
  Qed.

  Section Tail.
    (* [comment removed for export] *)
    Variable P : (word -> option byte) -> Prop.
    Hypothesis PT : forall m m', P m -> munch cbT_W m m' -> wmono s0segs m m' -> P m'.

    (* [comment removed for export] *)
    Lemma S0_cb_tcalls : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte) (lo : Z)
        (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word),
      bw_ok b -> (nblock + bw_numZ b + 40 <= ARR2_SIZE)%Z -> (0 <= e_combinedCRC e < 4294967296)%Z ->
      EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m -> stk s0segs m lo usp -> (CEIL <= lo)%Z ->
      rw_cells s0segs m (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> P m ->
      (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          let b' := bsPutUInt32 (bz_fin6 b) (e_combinedCRC e) in
          EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
          rw_cells s0segs m' (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> P m' ->
          munch cbT_W m m' -> wmono s0segs m m' -> bw_ok b' -> (bw_numZ b <= bw_numZ b' <= bw_numZ b + 32)%Z ->
          evt s0segs Q (MS (mkR (Z_to_bv 64 0x16ab0) sp gp tp t0' t1' t2' (Z_to_bv 64 E) s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                            F (Z_to_bv 64 0x16ab0) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16a5c) fc None m (seg_rom s0segs)).
    Proof.
      intros Q b m lo ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra.
      intros OK ROOM HCC EH1 EH2 AR2 MI ST Hlo SAV HP K.
      pose proof ROOM as RM. bz_params. pose proof USP1 as U1. bz_ceil; bz_params; unfold CEIL in U1.
      pose proof (munch_refl cbT_W m) as MU. pose proof (wmono_refl s0segs m) as WM.
      rewrite bz_fin6_eq in K.
      assert (USP1' : (CEIL <= usp + 280)%Z) by (bz_ceil; bz_params; unfold CEIL in *; lia).
      (* [comment removed for export] *)
      rename m into m0. rename b into B0. pose proof OK as OK0. pose proof (Z.le_refl (bw_numZ B0)) as NZ0.
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call Q B0 23 m0 lo); [lia| exact OK0| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m1 t0_1 t1_1 t2_1 a0_1 a1_1 a2_1 a3_1 a4_1 a5_1 a6_1 a7_1 t3_1 t4_1 t5_1 t6_1. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      pose proof (hi_transport _ _ _ _ USP1' SAV MUc WMc) as SAV'. clear SAV. rename SAV' into SAV.
      pose proof (PT _ _ HP MUc WMc) as HP'. clear HP. rename HP' into HP.
      pose proof (munch_trans _ _ _ _ MU MUc) as MU'. pose proof (wmono_trans s0segs _ _ _ WM WMc) as WM'. clear MU WM MUc WMc. rename MU' into MU. rename WM' into WM.
      replace (ret_pc (Z_to_bv 64 0x16a68)) with (Z_to_bv 64 0x16a68) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B0 23 OK0 ltac:(lia)) as G1.
      revert EH1 EH2 AR2 G1 K. generalize (bsW B0 8 23) as B1. intros B1 EH1 EH2 AR2 G1 K.
      cps_destruct G1 as (OK1 & NZ1 & LV1).
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call Q B1 114 m1 lo); [lia| exact OK1| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m2 t0_2 t1_2 t2_2 a0_2 a1_2 a2_2 a3_2 a4_2 a5_2 a6_2 a7_2 t3_2 t4_2 t5_2 t6_2. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      pose proof (hi_transport _ _ _ _ USP1' SAV MUc WMc) as SAV'. clear SAV. rename SAV' into SAV.
      pose proof (PT _ _ HP MUc WMc) as HP'. clear HP. rename HP' into HP.
      pose proof (munch_trans _ _ _ _ MU MUc) as MU'. pose proof (wmono_trans s0segs _ _ _ WM WMc) as WM'. clear MU WM MUc WMc. rename MU' into MU. rename WM' into WM.
      replace (ret_pc (Z_to_bv 64 0x16a74)) with (Z_to_bv 64 0x16a74) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B1 114 OK1 ltac:(lia)) as G2.
      revert EH1 EH2 AR2 G2 K. generalize (bsW B1 8 114) as B2. intros B2 EH1 EH2 AR2 G2 K.
      cps_destruct G2 as (OK2 & NZ2 & LV2).
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call Q B2 69 m2 lo); [lia| exact OK2| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m3 t0_3 t1_3 t2_3 a0_3 a1_3 a2_3 a3_3 a4_3 a5_3 a6_3 a7_3 t3_3 t4_3 t5_3 t6_3. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      pose proof (hi_transport _ _ _ _ USP1' SAV MUc WMc) as SAV'. clear SAV. rename SAV' into SAV.
      pose proof (PT _ _ HP MUc WMc) as HP'. clear HP. rename HP' into HP.
      pose proof (munch_trans _ _ _ _ MU MUc) as MU'. pose proof (wmono_trans s0segs _ _ _ WM WMc) as WM'. clear MU WM MUc WMc. rename MU' into MU. rename WM' into WM.
      replace (ret_pc (Z_to_bv 64 0x16a80)) with (Z_to_bv 64 0x16a80) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B2 69 OK2 ltac:(lia)) as G3.
      revert EH1 EH2 AR2 G3 K. generalize (bsW B2 8 69) as B3. intros B3 EH1 EH2 AR2 G3 K.
      cps_destruct G3 as (OK3 & NZ3 & LV3).
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call Q B3 56 m3 lo); [lia| exact OK3| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m4 t0_4 t1_4 t2_4 a0_4 a1_4 a2_4 a3_4 a4_4 a5_4 a6_4 a7_4 t3_4 t4_4 t5_4 t6_4. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      pose proof (hi_transport _ _ _ _ USP1' SAV MUc WMc) as SAV'. clear SAV. rename SAV' into SAV.
      pose proof (PT _ _ HP MUc WMc) as HP'. clear HP. rename HP' into HP.
      pose proof (munch_trans _ _ _ _ MU MUc) as MU'. pose proof (wmono_trans s0segs _ _ _ WM WMc) as WM'. clear MU WM MUc WMc. rename MU' into MU. rename WM' into WM.
      replace (ret_pc (Z_to_bv 64 0x16a8c)) with (Z_to_bv 64 0x16a8c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B3 56 OK3 ltac:(lia)) as G4.
      revert EH1 EH2 AR2 G4 K. generalize (bsW B3 8 56) as B4. intros B4 EH1 EH2 AR2 G4 K.
      cps_destruct G4 as (OK4 & NZ4 & LV4).
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call Q B4 80 m4 lo); [lia| exact OK4| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m5 t0_5 t1_5 t2_5 a0_5 a1_5 a2_5 a3_5 a4_5 a5_5 a6_5 a7_5 t3_5 t4_5 t5_5 t6_5. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      pose proof (hi_transport _ _ _ _ USP1' SAV MUc WMc) as SAV'. clear SAV. rename SAV' into SAV.
      pose proof (PT _ _ HP MUc WMc) as HP'. clear HP. rename HP' into HP.
      pose proof (munch_trans _ _ _ _ MU MUc) as MU'. pose proof (wmono_trans s0segs _ _ _ WM WMc) as WM'. clear MU WM MUc WMc. rename MU' into MU. rename WM' into WM.
      replace (ret_pc (Z_to_bv 64 0x16a98)) with (Z_to_bv 64 0x16a98) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B4 80 OK4 ltac:(lia)) as G5.
      revert EH1 EH2 AR2 G5 K. generalize (bsW B4 8 80) as B5. intros B5 EH1 EH2 AR2 G5 K.
      cps_destruct G5 as (OK5 & NZ5 & LV5).
      (* [comment removed for export] *)
      wstep. wstep. wstep.
      eapply (bsw8_call Q B5 144 m5 lo); [lia| exact OK5| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo|].
      clear EH1 EH2 AR2 MI ST.
      intros m6 t0_6 t1_6 t2_6 a0_6 a1_6 a2_6 a3_6 a4_6 a5_6 a6_6 a7_6 t3_6 t4_6 t5_6 t6_6. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      pose proof (hi_transport _ _ _ _ USP1' SAV MUc WMc) as SAV'. clear SAV. rename SAV' into SAV.
      pose proof (PT _ _ HP MUc WMc) as HP'. clear HP. rename HP' into HP.
      pose proof (munch_trans _ _ _ _ MU MUc) as MU'. pose proof (wmono_trans s0segs _ _ _ WM WMc) as WM'. clear MU WM MUc WMc. rename MU' into MU. rename WM' into WM.
      replace (ret_pc (Z_to_bv 64 0x16aa4)) with (Z_to_bv 64 0x16aa4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsW8_growth B5 144 OK5 ltac:(lia)) as G6.
      revert EH1 EH2 AR2 G6 K. generalize (bsW B5 8 144) as B6. intros B6 EH1 EH2 AR2 G6 K.
      cps_destruct G6 as (OK6 & NZ6 & LV6).
      (* [comment removed for export] *)
      unfold EH2b, EHEAD2 in EH2. cbn_est_in EH2. rewrite Gbs in EH2.
      wstep. wstep. wstep.
      assert (EH2' : EH2b m6 B6) by (unfold EH2b, EHEAD2; cbn_est; rewrite Gbs; exact EH2). clear EH2.
      eapply (bsput32_call Q B6 (e_combinedCRC e) m6 lo); [exact HCC| exact OK6| bz_params; lia| exact EH1| exact EH2'| exact AR2| exact MI| exact ST| exact Hlo|].
      clear EH1 EH2' AR2 MI ST.
      intros m7 t0_7 t1_7 t2_7 a0_7 a1_7 a2_7 a3_7 a4_7 a5_7 a6_7 a7_7 t3_7 t4_7 t5_7 t6_7. cbv zeta. intros EH1 EH2 AR2 MI ST MUc WMc.
      pose proof (hi_transport _ _ _ _ USP1' SAV MUc WMc) as SAV7. clear SAV. rename SAV7 into SAV.
      pose proof (PT _ _ HP MUc WMc) as HP7. clear HP. rename HP7 into HP.
      pose proof (munch_trans _ _ _ _ MU MUc) as MU7. pose proof (wmono_trans s0segs _ _ _ WM WMc) as WM7. clear MU WM MUc WMc. rename MU7 into MU. rename WM7 into WM.
      replace (ret_pc (Z_to_bv 64 0x16ab0)) with (Z_to_bv 64 0x16ab0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      pose proof (bsPutUInt32_growth B6 (e_combinedCRC e) OK6 ltac:(lia)) as G7.
      revert EH1 EH2 AR2 G7 K. generalize (bsPutUInt32 B6 (e_combinedCRC e)) as B7. intros B7 EH1 EH2 AR2 G7 K.
      cps_destruct G7 as (OK7 & NZ7 & LV7).
      eapply K; [exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact SAV| exact HP| exact MU| exact WM| exact OK7| lia].
    Qed.

    (* [comment removed for export] *)
    Lemma S0_cb_tfin : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte) (lo : Z)
        (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word),
      bw_ok b -> (nblock + bw_numZ b + 8 <= ARR2_SIZE)%Z ->
      EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m -> stk s0segs m lo usp -> (CEIL <= lo)%Z ->
      rw_cells s0segs m (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> P m ->
      (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          let b' := bs_finish BS_FUEL b in
          EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
          rw_cells s0segs m' (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> P m' ->
          munch cbT_W m m' -> wmono s0segs m m' -> (bw_numZ b <= bw_numZ b' <= bw_numZ b + 4)%Z ->
          evt s0segs Q (MS (mkR xra (Z_to_bv 64 (usp + 384)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6')
                            F (ret_pc xra) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16ab0) fc None m (seg_rom s0segs)).
    Proof.
      intros Q b m lo ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra.
      intros OK ROOM EH1 EH2 AR2 MI ST Hlo SAV HP K.
      cps_pose OK as (OKb & OKl & OKn). pose proof ROOM as RM. bz_params. pose proof USP1 as U1. bz_ceil; bz_params; unfold CEIL in U1.
      assert (USP1' : (CEIL <= usp + 280)%Z) by (bz_ceil; bz_params; unfold CEIL in *; lia).
      (* [comment removed for export] *)
      unfold EH1b, EH2b, EHEAD1, EHEAD2 in EH1, EH2. cbn_est_in EH1. cbn_est_in EH2. rewrite Gbs in EH2. rewrite Gzb in EH1.
      wstep. wstep. wstep; if_cases Kv; zify_cond_z Kv; [exfalso; lia|].
      wstep. wstep; if_cases Kl; zify_cond_z Kl.
      - (* [comment removed for export] *)
        assert (FB : bs_finish BS_FUEL b = b) by (unfold BS_FUEL; cbn [bs_finish]; replace (0 <? bw_live b)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        rewrite FB in K.
        eapply S0_cb_epilogue; [exact SAV|].
        eapply K; [unfold EH1b, EHEAD1; cbn_est; rewrite Gzb; exact EH1| unfold EH2b, EHEAD2; cbn_est; rewrite Gbs; exact EH2| unfold AR2b; exact AR2
                  | exact MI| exact ST| exact SAV| exact HP| apply munch_refl| apply wmono_refl| lia].
      - (* [comment removed for export] *)
        wstep. wstep. try rewrite (sx32_of_Z (bw_numZ b)) by (bz_params; lia).
        eapply (S0_cb_finish BS_FUEL Q b _ m);
          [lia| lia| lia| unfold BS_FUEL; change (8 * Z.of_nat 5)%Z with 40%Z; lia| unfold BS_FUEL; change (Z.of_nat 5) with 5%Z; lia
          | rewrite low32_sx32, low32_lit; apply Z.mod_small; lia
          | unfold EH1b, EHEAD1; cbn_est; rewrite Gzb; exact EH1| unfold EH2b, EHEAD2; cbn_est; rewrite Gbs; exact EH2| unfold AR2b; exact AR2| exact MI
          | apply munch_refl| apply wmono_refl|].
        intros m8 a0_8 a1_8 a2_8 a3_8 a4_8 a5_8. cbv zeta. intros EH1' EH2' AR2' MI' MU78 WM78 NZ8.
        pose proof (hi_transport _ _ _ _ USP1' SAV MU78 WM78) as SAV8. pose proof (PT _ _ HP MU78 WM78) as HP8.
        pose proof (stk_hi_transport _ _ _ Hlo ST MU78 WM78) as ST8.
        eapply S0_cb_epilogue; [exact SAV8|].
        eapply K; [exact EH1'| exact EH2'| exact AR2'| exact MI'| exact ST8| exact SAV8| exact HP8| exact MU78| exact WM78| exact (bs_finish_growth b OK)].
    Qed.

    (* [comment removed for export] *)
    Lemma S0_cb_tail : forall (Q : machine_state -> Prop) (isl : bool) (b : bw) (m : word -> option byte) (lo : Z)
        (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
        (x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra : word),
      bw_ok b -> (nblock + bw_numZ b + 40 <= ARR2_SIZE)%Z -> (0 <= e_combinedCRC e < 4294967296)%Z ->
      EH1b m b -> EH2b m b -> AR2b m b -> mem_inv s0segs m -> stk s0segs m lo usp -> (CEIL <= lo)%Z ->
      rw_cells s0segs m (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> P m ->
      (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
          let b' := cb_trailer isl b (e_combinedCRC e) in
          EH1b m' b' -> EH2b m' b' -> AR2b m' b' -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
          rw_cells s0segs m' (usp + 280) (SAVL x11 x10 x9 x8 x7 x6 x5 x4 x3 x2 x1 x0 xra) -> P m' ->
          munch cbT_W m m' -> wmono s0segs m m' -> (bw_numZ b <= bw_numZ b' <= bw_numZ b + 36)%Z ->
          evt s0segs Q (MS (mkR xra (Z_to_bv 64 (usp + 384)) gp tp t0' t1' t2' x0 x1 a0' a1' a2' a3' a4' a5' a6' a7' x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3' t4' t5' t6')
                            F (ret_pc xra) fc None m' (seg_rom s0segs))) ->
      evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (if isl then 1 else 0)) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16a58) fc None m (seg_rom s0segs)).
    Proof.
      intros Q isl b m lo ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 xra.
      intros OK ROOM HCC EH1 EH2 AR2 MI ST Hlo SAV HP K.
      cps_pose OK as (OKb & OKl & OKn). pose proof ROOM as RM. bz_params. pose proof USP1 as U1. bz_ceil; bz_params; unfold CEIL in U1.
      destruct isl.
      2:{ (* [comment removed for export] *)
          wstep; if_cases Kz; zify_cond_z Kz; [| exfalso; lia].
          eapply S0_cb_epilogue; [exact SAV|]. rewrite BzCEmit.cb_trailer_false in K.
          eapply K; [exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact SAV| exact HP| apply munch_refl| apply wmono_refl| lia]. }
      wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
      rewrite cb_trailer_true in K.
      eapply (S0_cb_tcalls Q b m lo); [exact OK| exact ROOM| exact HCC| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo| exact SAV| exact HP|].
      clear EH1 EH2 AR2 MI ST SAV HP.
      intros m7 t0_7 t1_7 t2_7 a0_7 a1_7 a2_7 a3_7 a4_7 a5_7 a6_7 a7_7 t3_7 t4_7 t5_7 t6_7. cbv zeta. intros EH1 EH2 AR2 MI ST SAV HP MU7 WM7 OK7 NZ7.
      eapply (S0_cb_tfin Q (bsPutUInt32 (bz_fin6 b) (e_combinedCRC e)) m7 lo);
        [exact OK7| bz_params; lia| exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact Hlo| exact SAV| exact HP|].
      clear EH1 EH2 AR2 MI ST SAV HP.
      intros m8 t0_8 t1_8 t2_8 a0_8 a1_8 a2_8 a3_8 a4_8 a5_8 a6_8 a7_8 t3_8 t4_8 t5_8 t6_8. cbv zeta. intros EH1 EH2 AR2 MI ST SAV HP MU8 WM8 NZ8.
      eapply K; [exact EH1| exact EH2| exact AR2| exact MI| exact ST| exact SAV| exact HP
                | exact (munch_trans _ _ _ _ MU7 MU8)| exact (wmono_trans s0segs _ _ _ WM7 WM8)|].
      revert NZ7 NZ8. clear. generalize (bs_finish BS_FUEL (bsPutUInt32 (bz_fin6 b) (e_combinedCRC e))) as b2. generalize (bsPutUInt32 (bz_fin6 b) (e_combinedCRC e)) as b1.
      intros. lia.
    Qed.

    (* [comment removed for export] *)
    Lemma S0_cb_t0 : forall (Q : machine_state -> Prop) (b : bw) (m : word -> option byte) (wisl : word)
        (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
      EH2b m b -> rw_cells s0segs m (usp + 8) [C8 wisl] ->
      evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) wisl a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16a58) fc None m (seg_rom s0segs)) ->
      evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x16a54) fc None m (seg_rom s0segs)).
    Proof using BZP ACEIL__ cx g e sp gp tp F fc CX SEP Gbs USP1.
      intros Q b m wisl ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 EH2 SL K.
      pose proof USP1 as U1. bz_ceil; bz_params; unfold CEIL in U1. openCX.
      wstep. enter_with K. st_eq.
    Qed.
  End Tail.
End CBT.

End ACeilS1.
