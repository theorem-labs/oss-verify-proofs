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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require SegsA0 SegsB0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzArrD BzCLemmas1 CmpMem.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut CmpCut0 CmpArith.
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "qal" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.

Import ListNotations. Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzSepTac.
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
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
  Hypothesis LO : (CEIL <= lo)%Z. Hypothesis LO32 : (lo + 48 <= usp)%Z.

  Notation W := (bsW8_W cx e ++ [(usp - 48, usp)])%Z.
  Variable SHE : Z. Hypothesis AE : sanchor E SHE.
  Hypothesis SHe : shzW b0segs W m0 E (E + ESTATE_SIZE).
  Hypothesis SH2 : shzW b0segs W m0 A2 (A2 + ARR2_SIZE).
  Notation POST := (bsW8_post b0segs cx g e v ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  (* [comment removed for export] *)
  Definition MEMb (b : bw) (m : word -> option byte) : Prop :=
    rw_cells b0segs m E (EHEAD1 cx g (est_set_bw e b)) /\ rw_cells b0segs m (E + 640) (EHEAD2 cx g (est_set_bw e b)) /\
    u8arr b0segs m A2 (zb8 (zbl (e_arr2 e) nblock b) ARR2_SIZE) /\
    mem_inv b0segs m /\ munch W m0 m /\ wmono b0segs m0 m /\ stk b0segs m lo (usp + -48) /\
    rw_cells b0segs m (usp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  Ltac prep :=
    let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB); try lin16 ALE; try lin16 AL1; try lin16 AL2; try lin16 ALF; try lin16 ALB; try lin16 ALFb;
    pose proof SEP2 as SEP2'; pose proof SPE as SPE'; pose proof SPA as SPA'; unfold apart, ESTATE_SIZE in SEP2', SPE', SPA';
    unfold ESTATE_SIZE, CEIL in *.
  Ltac openb MEM :=
    let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let MU := ident:(MU) in
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK & FR); unfold EHEAD1, EHEAD2 in EH1, EH2;
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2;
    rewrite Gbs in EH2; rewrite Gzb in EH1; unfold bsW8_W in MU |- *; cbn [app] in MU |- *.
  (* [comment removed for export] *)
  Ltac closeb EH1 EH2 AR2 MI MU WM STK FR :=
    split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| split; [exact STK| exact FR]]]]]]];
    [ unfold EHEAD1; cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]; rewrite Gzb; unfold bw_emit; cbn [bw_numZ]; exact EH1
    | unfold EHEAD2; cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]; rewrite Gbs; unfold bw_emit; cbn [bw_buff bw_live]; exact EH2 ].

  Notation cSP := (Z_to_bv 64 (usp + -48)). Notation cSB := (Z_to_bv 64 2147450880).

  (* [comment removed for export] *)
  Lemma bsw_loop : forall (f : nat) (b : bw) (m : word -> option byte) (x6 x7 x8 x9 x15 x18 x19 x20 x30 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ b0 <= bw_numZ b)%Z ->
    (8 * bw_numZ b + bw_live b = 8 * bw_numZ b0 + bw_live b0)%Z ->
    MEMb b m ->
    (forall b1 m' (x8' x9' x18' x19' x20' : word),
        b1 = bs_needw f b -> MEMb b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt b0segs POST (MS (mkR ra cSP gp tp (Z_to_bv 64 (SHE + 80)) x6 x7 x8' x9' (Z_to_bv 64 (E + 644)) (Z_to_bv 64 v) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 80))
                                  (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 (SHE + 80)) cSB x18' x19' x20' s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (SHE + 14)) x30 (Z_to_bv 64 7))
                             F (Z_to_bv 64 0x8b330) fc None m' (seg_rom b0segs))) ->
    evt b0segs POST (MS (mkR ra cSP gp tp (Z_to_bv 64 (SHE + 80)) x6 x7 x8 x9 (Z_to_bv 64 (E + 644)) (Z_to_bv 64 v) (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 80))
                              x15 (Z_to_bv 64 (SHE + 80)) cSB x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (SHE + 14)) x30 (Z_to_bv 64 7))
                         F (Z_to_bv 64 0x8b230) fc None m (seg_rom b0segs)).
  Proof.
    induction f as [|f IH]; intros b m x6 x7 x8 x9 x15 x18 x19 x20 x30 OK L8 Lf N0 N4 MEM K; [lia|].
    prep. openb MEM. unfold bsW8_W in SHe, SH2, K. cbn [app] in SHe, SH2, K.
    cps_destruct OK as (OKb & OKl & OKn). cps_pose OK0 as (OK0b & OK0l & OK0n).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    brun.
    pose proof (rw_cells_read_byte3 b0segs m (E + 640) _ 0%nat _ _ EH2 eq_refl eq_refl) as RB.
    rewrite unsigned_lit in RB by lia.
    wstep. clear RB. cbv beta delta [zxb]. rewrite (unsigned_lit8 (bw_buff b / 16777216)) by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (u8arr_store_ok b0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 b0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    brun_to 0x8b2e4%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH (bw_emit b) mm x6 x7 _ _ _ _ _ _ x30); [st_eq| unfold bw_ok; lia| lia| lia| lia| lia| |] end.
      + closeb EH1 EH2 AR2 MI MU WM STK FR.
      + intros b1 m' x8' x9' x18' x19' x20' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + closeb EH1 EH2 AR2 MI MU WM STK FR.
  Qed.

  (* [comment removed for export] *)
  Lemma bsw_tail : forall (b1 : bw) (m : word -> option byte) (x5 x6 x7 x8 x9 x13 x14 x18 x19 x20 x28 x29 x30 x31 : word),
    b1 = bs_needw BS_FUEL b0 -> (0 <= bw_live b1 < 8)%Z -> MEMb b1 m ->
    evt b0segs POST (MS (mkR ra cSP gp tp x5 x6 x7 x8 x9 (Z_to_bv 64 (E + 644)) (Z_to_bv 64 v) (Z_to_bv 64 (E + 640)) x13 x14
                              (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 (SHE + 80)) cSB x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                         F (Z_to_bv 64 0x8b330) fc None m (seg_rom b0segs)).
  Proof.
    intros b1 m x5 x6 x7 x8 x9 x13 x14 x18 x19 x20 x28 x29 x30 x31 Eb1 L1 MEM.
    prep. openb MEM. unfold bsW8_W in SHe, SH2. cbn [app] in SHe, SH2.
    cps_pose (bs_needw_post BS_FUEL b0 OK0 ltac:(cps_destruct OK0 as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK0 as (OK0b & OK0l & OK0n).
    (* [comment removed for export] *)
    brun_to 0x8b374%Z.
    replace ((32 - bw_live b1 + -8) mod 32)%Z with (32 - bw_live b1 - 8)%Z in EH2 by (rewrite Z.mod_small by lia; lia).      (* [comment removed for export] *)
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl v (32 - bw_live b1 - 8)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 v _ (bw_buff b1)) by lia.      (* [comment removed for export] *)
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    brun_to 0x8b384%Z. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    release_frame FR STK (bv_unsigned sp).
    replace (Z_to_bv 64 (usp + -48 + 48)) with sp by (rewrite <- (Z_to_bv_bv_unsigned sp) at 1; f_equal; lia).
    wstep. unfold bsW8_post. cbv zeta.
    finish.
    - unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw bsW bw_numZ]. rewrite Gzb. subst b1. exact EH1.
    - unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF bsW bw_buff bw_live]. rewrite Gbs. subst b1. exact EH2.
    - rewrite (zbl_same_bytes (e_arr2 e) nblock b1 (bsW b0 8 v)); [exact AR2| subst b1; CmpFast.bsw_same| subst b1; CmpFast.bsw_same].
  Qed.

  (* [comment removed for export] *)
  Lemma bsw_entry : forall (t0 t1 t2 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 : word),
    rw_cells b0segs m0 E (EHEAD1 cx g e) -> rw_cells b0segs m0 (E + 640) (EHEAD2 cx g e) ->
    u8arr b0segs m0 A2 (zb8 (zbl (e_arr2 e) nblock b0) ARR2_SIZE) -> mem_inv b0segs m0 -> stk b0segs m0 lo usp -> aconsts B0C m0 ->
    evt b0segs POST (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 E) (Z_to_bv 64 v) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x8b19c) fc None m0 (seg_rom b0segs)).
  Proof.
    intros t0 t1 t2 x12 x13 x14 x15 x16 x17 t3 t4 t5 t6 EH1 EH2 AR2 MI STK AC.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar B0C ci_segs] in GOT, SBV.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl b0segs m0) as WM.
    prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsW8_W in MU, SHe, SH2 |- *. cbn [app] in MU, SHe, SH2 |- *.
    cps_pose OK0 as (OK0b & OK0l & OK0n).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b0) ARR2_SIZE ltac:(lia)) as LA2.
    carve_frame 48%nat STK.
    (* [comment removed for export] *)
    brun; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      sh_norm.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (bsw_tail b0 mm _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| | lia| ] end.
      + unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b0)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| split; [exact STK| exact FR]]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
             e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
             e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. exact EH2.
    - (* [comment removed for export] *)
      brun_to 0x8b230%Z. sh_norm.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (bsw_loop BS_FUEL b0 mm _ _ _ _ _ _ _ _ _); [st_eq| exact OK0| lia| unfold BS_FUEL; cbn; lia| lia| lia| |] end.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| split; [exact STK| exact FR]]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
             e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
             e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. exact EH2.
      + intros b1 m' x8' x9' x18' x19' x20' Eb1 MEM' L1. eapply (bsw_tail b1 m'); [exact Eb1| exact L1| exact MEM'].
  Qed.

End BSW.

Theorem B0_bsW8 : bsW8_aspecF B0C 48.
Proof.
  unfold bsW8_aspecF. cbn [aci_segs aci_c ci_segs ci_bsW8 B0C]. intros until lo. intros -> -> Hv EH1 EH2 AR2 MI ST LO32 LO CX SEP Gbs Gzb OK Hnb ROOM AC CSH.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. cps_destruct CX' as (_ & RE2 & _ & _ & _ & RA2' & _ & _ & _ & _ & _ & _ & ALE & _).
  unfold cctx_sep in SEP. cbv zeta in SEP. cps_destruct SEP as (_ & SEP2 & _).
  destruct CSH as (SHe & _ & SH2 & _ & _).
  assert (AE : sanchor (c_E cx) (c_E cx / 8 + 2147450880)).
  { apply sanchor_intro. clear - ALE. Z.div_mod_to_equations. lia. }
  eapply (bsw_entry ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m cx g e v lo); try eassumption; lia.
Qed.

End ACeilS1.
