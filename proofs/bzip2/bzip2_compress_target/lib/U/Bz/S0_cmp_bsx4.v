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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzArrD BzCLemmas1 CmpMem.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutBsw.

From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut CmpCut0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpArith. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCutBsw.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Module S0_cmp_bsx2.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutBsw.
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


Section PUT.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g : eg) (e : est) (u lo : Z).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A2 := (c_A2 cx).
  Notation nblock := (e_nblock e). Notation b0 := (e_bw e).
  Hypothesis CX : cctx_ok cx. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hu : (0 <= u < 4294967296)%Z. Hypothesis OK0 : bw_ok b0. Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis ROOM : (nblock + bw_numZ b0 + 16 <= ARR2_SIZE)%Z.
  Hypothesis SEP2 : apart E ESTATE_SIZE A2 ARR2_SIZE.
  Hypothesis SPE : (usp <= E \/ E + ESTATE_SIZE <= lo)%Z.
  Hypothesis SPA : (usp <= A2 \/ A2 + ARR2_SIZE <= lo)%Z.
  Variables (t1 t2 t3 t4 t5 t6 : word).
  Notation W := (bsPutUInt32_W cx e).
  Notation POST := (bsPutUInt32_post s0segs cx g e u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
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
  Ltac fl := wstep; flags.
  Ltac bnt := wstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_false_z | |- _ => idtac end.

  (* [comment removed for export] *)
  Lemma put_loop1 : forall (f : nat) (c b : bw) (m : word -> option byte) (xbuf x5 x13 x16 x17 : word),
    bw_ok c -> (bw_numZ b0 <= bw_numZ c)%Z -> (8 * bw_numZ c + bw_live c <= 8 * bw_numZ b0 + bw_live b0 + 24)%Z ->
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ c <= bw_numZ b)%Z ->
    (8 * bw_numZ b + bw_live b = 8 * bw_numZ c + bw_live c)%Z ->
    (bv_unsigned xbuf mod 4294967296 = bw_buff b)%Z ->
    MEMb b m ->
    (forall b1 m' (x5' x12' x14' x15' x16' x17' : word),
        b1 = bs_needw f b -> MEMb b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs POST (MS (mkR ra sp gp tp x5' t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) x12' (Z_to_bv 64 (bw_live b1)) x14' x15' x16' x17' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16cf8) fc None m' (seg_rom s0segs))) ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) (Z_to_bv 64 7) x13 (Z_to_bv 64 (bw_numZ b)) xbuf x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16c94) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros c b m xbuf x5 x13 x16 x17 OKc Nc0 Bc OK L8 Lf N0 N4 XB MEM K; [lia|].
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU, K |- *.
    cps_destruct OK as (OKb & OKl & OKn). cps_pose OK0 as (OK0b & OK0l & OK0n). cps_destruct OKc as (OKcb & OKcl & OKcn).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    wstep. wstep. fl. fl. bnt. fl. fl. wstep. wstep. bnt. bnt.
    wstep. rewrite XB.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. bnt. wstep. wstep. wstep. wstep. wstep. wstep. bnt. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH c (bw_emit b) mm _ _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| unfold bw_ok; lia| lia| lia| lia| lia| | |] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
      + intros b1 m' x5' x12' x14' x15' x16' x17' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - (* [comment removed for export] *)
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
  Lemma put_loop2 : forall (f : nat) (c b : bw) (m : word -> option byte) (xbuf x5 x14 x16 x17 : word),
    bw_ok c -> (bw_numZ b0 <= bw_numZ c)%Z -> (8 * bw_numZ c + bw_live c <= 8 * bw_numZ b0 + bw_live b0 + 24)%Z ->
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ c <= bw_numZ b)%Z ->
    (8 * bw_numZ b + bw_live b = 8 * bw_numZ c + bw_live c)%Z ->
    (bv_unsigned xbuf mod 4294967296 = bw_buff b)%Z ->
    MEMb b m ->
    (forall b1 m' (xbuf' x5' x13' x15' x16' x17' : word),
        b1 = bs_needw f b -> MEMb b1 m' -> (bv_unsigned xbuf' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs POST (MS (mkR ra sp gp tp x5' t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf' x13' (Z_to_bv 64 (bw_live b1)) x15' x16' x17' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16da8) fc None m' (seg_rom s0segs))) ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf (Z_to_bv 64 7) x14 (Z_to_bv 64 (bw_numZ b)) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16d44) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros c b m xbuf x5 x14 x16 x17 OKc Nc0 Bc OK L8 Lf N0 N4 XB MEM K; [lia|].
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU, K |- *.
    cps_destruct OK as (OKb & OKl & OKn). cps_pose OK0 as (OK0b & OK0l & OK0n). cps_destruct OKc as (OKcb & OKcl & OKcn).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    wstep. wstep. fl. fl. bnt. fl. fl. wstep. wstep. bnt. bnt.
    wstep. rewrite XB.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. bnt. wstep. wstep. wstep. wstep. wstep. wstep. bnt. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH c (bw_emit b) mm _ _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| unfold bw_ok; lia| lia| lia| lia| lia| | |] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
      + intros b1 m' xbuf' x5' x13' x15' x16' x17' Eb1 MEM' XB' L1. eapply K; [|exact MEM'| exact XB'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | | | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  Lemma put_loop3 : forall (f : nat) (c b : bw) (m : word -> option byte) (xbuf x5 x13 x16 x17 : word),
    bw_ok c -> (bw_numZ b0 <= bw_numZ c)%Z -> (8 * bw_numZ c + bw_live c <= 8 * bw_numZ b0 + bw_live b0 + 24)%Z ->
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ c <= bw_numZ b)%Z ->
    (8 * bw_numZ b + bw_live b = 8 * bw_numZ c + bw_live c)%Z ->
    (bv_unsigned xbuf mod 4294967296 = bw_buff b)%Z ->
    MEMb b m ->
    (forall b1 m' (xbuf' x5' x14' x15' x16' x17' : word),
        b1 = bs_needw f b -> MEMb b1 m' -> (bv_unsigned xbuf' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs POST (MS (mkR ra sp gp tp x5' t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf' (Z_to_bv 64 (bw_live b1)) x14' x15' x16' x17' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16e58) fc None m' (seg_rom s0segs))) ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf x13 (Z_to_bv 64 7) (Z_to_bv 64 (bw_numZ b)) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16df4) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros c b m xbuf x5 x13 x16 x17 OKc Nc0 Bc OK L8 Lf N0 N4 XB MEM K; [lia|].
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU, K |- *.
    cps_destruct OK as (OKb & OKl & OKn). cps_pose OK0 as (OK0b & OK0l & OK0n). cps_destruct OKc as (OKcb & OKcl & OKcn).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    wstep. wstep. fl. fl. bnt. fl. fl. wstep. wstep. bnt. bnt.
    wstep. rewrite XB.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. bnt. wstep. wstep. wstep. wstep. wstep. wstep. bnt. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH c (bw_emit b) mm _ _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| unfold bw_ok; lia| lia| lia| lia| lia| | |] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
      + intros b1 m' xbuf' x5' x14' x15' x16' x17' Eb1 MEM' XB' L1. eapply K; [|exact MEM'| exact XB'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | | | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  (* [comment removed for export] *)
  Lemma put_loop4 : forall (f : nat) (c b : bw) (m : word -> option byte) (xbuf x5 x14 x16 x17 : word),
    bw_ok c -> (bw_numZ b0 <= bw_numZ c)%Z -> (8 * bw_numZ c + bw_live c <= 8 * bw_numZ b0 + bw_live b0 + 24)%Z ->
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ c <= bw_numZ b)%Z ->
    (8 * bw_numZ b + bw_live b = 8 * bw_numZ c + bw_live c)%Z ->
    (bv_unsigned xbuf mod 4294967296 = bw_buff b)%Z ->
    MEMb b m ->
    (forall b1 m' (xbuf' x5' x13' x15' x16' x17' : word),
        b1 = bs_needw f b -> MEMb b1 m' -> (bv_unsigned xbuf' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs POST (MS (mkR ra sp gp tp x5' t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf' x13' (Z_to_bv 64 (bw_live b1)) x15' x16' x17' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16f08) fc None m' (seg_rom s0segs))) ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf (Z_to_bv 64 7) x14 (Z_to_bv 64 (bw_numZ b)) x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16ea4) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]; intros c b m xbuf x5 x14 x16 x17 OKc Nc0 Bc OK L8 Lf N0 N4 XB MEM K; [lia|].
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU, K |- *.
    cps_destruct OK as (OKb & OKl & OKn). cps_pose OK0 as (OK0b & OK0l & OK0n). cps_destruct OKc as (OKcb & OKcl & OKcn).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    wstep. wstep. fl. fl. bnt. fl. fl. wstep. wstep. bnt. bnt.
    wstep. rewrite XB.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    wstep. wstep. bnt. wstep. wstep. wstep. wstep. wstep. wstep. bnt. wstep.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH c (bw_emit b) mm _ _ _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| unfold bw_ok; lia| lia| lia| lia| lia| | |] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
      + intros b1 m' xbuf' x5' x13' x15' x16' x17' Eb1 MEM' XB' L1. eapply K; [|exact MEM'| exact XB'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | | | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. unfold bw_emit. cbn [bw_numZ]. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. unfold bw_emit. cbn [bw_buff bw_live]. exact EH2.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

End PUT.

End ACeilS1.
End S0_cmp_bsx2.


From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require ZBridge.
Module S0_cmp_bsx3.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib.ZBridge.Bytes OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib.SegsS0.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzTac2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmas1 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutBsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_bsx4.S0_cmp_bsx2.
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


(* [comment removed for export] *)
Lemma sx32_slli40 : forall u, (0 <= u < 4294967296)%Z ->
  Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 u)) * 1099511627776) = Z_to_bv 64 (u * 1099511627776).
Proof. intros u Hu. apply Z_to_bv_eqm. change (2 ^ 64)%Z with 18446744073709551616%Z. apply sx32_shl40. exact Hu. Qed.
Lemma sx32_slli48 : forall u, (0 <= u < 4294967296)%Z ->
  Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 u)) * 281474976710656) = Z_to_bv 64 (u * 281474976710656).
Proof. intros u Hu. apply Z_to_bv_eqm. change (2 ^ 64)%Z with 18446744073709551616%Z. apply sx32_shl48. exact Hu. Qed.

Section PUT.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g : eg) (e : est) (u lo : Z).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A2 := (c_A2 cx).
  Notation nblock := (e_nblock e). Notation b0 := (e_bw e).
  Hypothesis CX : cctx_ok cx. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hu : (0 <= u < 4294967296)%Z. Hypothesis OK0 : bw_ok b0. Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis ROOM : (nblock + bw_numZ b0 + 16 <= ARR2_SIZE)%Z.
  Hypothesis SEP2 : apart E ESTATE_SIZE A2 ARR2_SIZE.
  Hypothesis SPE : (usp <= E \/ E + ESTATE_SIZE <= lo)%Z.
  Hypothesis SPA : (usp <= A2 \/ A2 + ARR2_SIZE <= lo)%Z.
  Variables (t1 t2 t3 t4 t5 t6 : word).
  Notation W := (bsPutUInt32_W cx e).
  Notation POST := (bsPutUInt32_post s0segs cx g e u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  Notation MEMb := (S0_cmp_bsx2.MEMb sp m0 cx g e lo).
  Notation put_loop1 := (S0_cmp_bsx2.put_loop1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Notation put_loop2 := (S0_cmp_bsx2.put_loop2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Notation put_loop3 := (S0_cmp_bsx2.put_loop3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Notation put_loop4 := (S0_cmp_bsx2.put_loop4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Ltac prep :=
    let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB); try lin16 ALE; try lin16 AL1; try lin16 AL2; try lin16 ALF; try lin16 ALB; try lin16 ALFb;
    pose proof SEP2 as SEP2'; pose proof SPE as SPE'; pose proof SPA as SPA'; unfold apart, ESTATE_SIZE in SEP2', SPE', SPA';
    unfold ESTATE_SIZE in *.
  Ltac fl := wstep; flags.
  Ltac bnt := wstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_false_z | |- _ => idtac end.

  (* [comment removed for export] *)
  Lemma put_tail4 : forall (b1 : bw) (m : word -> option byte) (xbuf x5 x13 x15 x16 x17 : word),
    bw_ok (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) -> (bw_numZ b0 <= bw_numZ (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)))%Z ->
    (8 * bw_numZ (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) + bw_live (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) <= 8 * bw_numZ b0 + bw_live b0 + 24)%Z ->
    b1 = bs_needw BS_FUEL (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) -> (0 <= bw_live b1 < 8)%Z -> MEMb b1 m ->
    (bv_unsigned xbuf mod 4294967296 = bw_buff b1)%Z ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf x13 (Z_to_bv 64 (bw_live b1)) x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16f08) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb Hu OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6.
    intros b1 m xbuf x5 x13 x15 x16 x17 OKc Nc0 Bc Eb1 L1 MEM XB.
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU |- *.
    cps_pose (bs_needw_post BS_FUEL (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) OKc ltac:(cps_destruct OKc as (?&?&?); change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia)) as (OK1 & M1 & N1).
    pose proof (bs_needw_credit BS_FUEL (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255))) as CR1.
    rewrite <- Eb1 in OK1, M1, N1, CR1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK0 as (OK0b & OK0l & OK0n). cps_pose OKc as (OKcb & OKcl & OKcn).
    (* [comment removed for export] *)
    wstep. wstep. wstep. bnt. wstep. wstep. bnt. wstep. bnt.
    wstep. rewrite (sx32_land255 u Hu). wstep. wstep.
    replace ((32 - bw_live b1 + -8) mod 32)%Z with (32 - bw_live b1 - 8)%Z by (rewrite Z.mod_small by lia; lia).
    wstep. wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl (Z.land u 255) (32 - bw_live b1 - 8)) mod 4294967296))%Z.
    { first [ rewrite (low32_or_shifted _ _ xbuf (bw_buff b1) XB) by lia | rewrite (low32_or_shifted2 _ _ xbuf (bw_buff b1) XB) by lia ].
      rewrite <- ?(byte3_eq u), ?(byte2_eq u), ?(byte1_eq u) by lia. first [ reflexivity | rewrite low32_small; [reflexivity| change 4294967296%Z with (2^32)%Z; apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]] ]. }
    (* [comment removed for export] *)
    wstep. unfold bsPutUInt32_post. cbv zeta.
    finish.
    - unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. unfold bsPutUInt32; cbv zeta; rewrite CmpFast.bsW_numZ_needw (* [comment removed for export] *). rewrite Gzb. subst b1. exact EH1.
    - unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF bsPutUInt32 bsW bw_buff bw_live]. rewrite Gbs. subst b1. exact EH2.
    - rewrite (zbl_same_bytes (e_arr2 e) nblock b1 (bsPutUInt32 b0 u)); [exact AR2| subst b1; CmpFast.bsw_same| subst b1; CmpFast.bsw_same].
  Qed.

  (* [comment removed for export] *)
  Lemma put_tail3 : forall (b1 : bw) (m : word -> option byte) (xbuf x5 x14 x15 x16 x17 : word),
    bw_ok (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) -> (bw_numZ b0 <= bw_numZ (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)))%Z ->
    (8 * bw_numZ (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) + bw_live (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) <= 8 * bw_numZ b0 + bw_live b0 + 16)%Z ->
    b1 = bs_needw BS_FUEL (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) -> (0 <= bw_live b1 < 8)%Z -> MEMb b1 m ->
    (bv_unsigned xbuf mod 4294967296 = bw_buff b1)%Z ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf (Z_to_bv 64 (bw_live b1)) x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16e58) fc None m (seg_rom s0segs)).
  Proof.
    intros b1 m xbuf x5 x14 x15 x16 x17 OKc Nc0 Bc Eb1 L1 MEM XB.
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU |- *.
    cps_pose (bs_needw_post BS_FUEL (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) OKc ltac:(cps_destruct OKc as (?&?&?); change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia)) as (OK1 & M1 & N1).
    pose proof (bs_needw_credit BS_FUEL (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255))) as CR1.
    rewrite <- Eb1 in OK1, M1, N1, CR1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK0 as (OK0b & OK0l & OK0n). cps_pose OKc as (OKcb & OKcl & OKcn).
    (* [comment removed for export] *)
    wstep. wstep. wstep. bnt. wstep. wstep. bnt. wstep. bnt.
    wstep. rewrite (sx32_slli48 u Hu). wstep. wstep.
    replace ((32 - bw_live b1 + -8) mod 32)%Z with (32 - bw_live b1 - 8)%Z by (rewrite Z.mod_small by lia; lia).
    wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl (Z.land (Z.shiftr u 8) 255) (32 - bw_live b1 - 8)) mod 4294967296))%Z.
    { first [ rewrite (low32_or_shifted _ _ xbuf (bw_buff b1) XB) by lia | rewrite (low32_or_shifted2 _ _ xbuf (bw_buff b1) XB) by lia ].
      rewrite <- ?(byte3_eq u), ?(byte2_eq u), ?(byte1_eq u) by lia. first [ reflexivity | rewrite low32_small; [reflexivity| change 4294967296%Z with (2^32)%Z; apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]] ]. }
    cps_pose (bsW8_ok (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) (Z.land (Z.shiftr u 8) 255) OKc ltac:(apply Z.land_nonneg; right; lia)) as (OKk & Nk & Lk).
    pose proof (bsW_credit (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) as CRk.
    assert (XBk : (Z.lor (bw_buff b1) (Z.shiftl (Z.land (Z.shiftr u 8) 255) (32 - bw_live b1 - 8) mod 4294967296) = bw_buff (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)))%Z).
    { unfold bsW at 1. cbn [bw_buff bw_live]. subst b1. reflexivity. }
    (* [comment removed for export] *)
    bnt. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (put_loop4 BS_FUEL (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255)) mm _ _ _ _ _);
      [st_eq| exact OKk| lia| lia| exact OKk| lia| change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia| lia| lia| | |] end.
    + rewrite <- XBk. first [ rewrite (low32_or_shifted _ _ xbuf (bw_buff b1) XB) by lia | rewrite (low32_or_shifted2 _ _ xbuf (bw_buff b1) XB) by lia ].
      rewrite <- ?(byte3_eq u), ?(byte2_eq u), ?(byte1_eq u) by lia. apply Z.mod_small.
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
    + split; [|split; [|split; [| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
      * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. cbn [bsW bw_numZ]. rewrite Gzb. subst b1. exact EH1.
      * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. rewrite <- XBk.
        replace (bw_live (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255))) with (bw_live b1 + 8)%Z by (unfold bsW at 1; cbn [bw_live]; subst b1; reflexivity). exact EH2.
      * rewrite (zbl_same_bytes (e_arr2 e) nblock b1 (bsW (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) 8 (Z.land (Z.shiftr u 8) 255))); [exact AR2| subst b1; CmpFast.bsw_same| subst b1; CmpFast.bsw_same].
    + intros b2 m2 xbuf2 x52 x132 x152 x162 x172 Eb2 MEM2 XB2 L2.
      eapply (put_tail4 b2 m2); [exact OKk| lia| lia| exact Eb2| exact L2| exact MEM2| exact XB2].
  Qed.

End PUT.

End ACeilS1.
End S0_cmp_bsx3.

Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCut0 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpCutBsw OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_bsx4.S0_cmp_bsx2 OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.S0_cmp_bsx4.S0_cmp_bsx3.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
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
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "qal" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.

Import ListNotations. Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section PUT.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte).
  Variables (cx : cctx) (g : eg) (e : est) (u lo : Z).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A2 := (c_A2 cx).
  Notation nblock := (e_nblock e). Notation b0 := (e_bw e).
  Hypothesis CX : cctx_ok cx. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hu : (0 <= u < 4294967296)%Z. Hypothesis OK0 : bw_ok b0. Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis ROOM : (nblock + bw_numZ b0 + 16 <= ARR2_SIZE)%Z.
  Hypothesis SEP2 : apart E ESTATE_SIZE A2 ARR2_SIZE.
  Hypothesis SPE : (usp <= E \/ E + ESTATE_SIZE <= lo)%Z.
  Hypothesis SPA : (usp <= A2 \/ A2 + ARR2_SIZE <= lo)%Z.
  Variables (t1 t2 t3 t4 t5 t6 : word).
  Notation W := (bsPutUInt32_W cx e).
  Notation POST := (bsPutUInt32_post s0segs cx g e u ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo W m0).
  Notation MEMb := (S0_cmp_bsx2.MEMb sp m0 cx g e lo).
  Notation put_loop1 := (S0_cmp_bsx2.put_loop1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Notation put_loop2 := (S0_cmp_bsx2.put_loop2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Notation put_loop3 := (S0_cmp_bsx2.put_loop3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Notation put_loop4 := (S0_cmp_bsx2.put_loop4 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Notation put_tail3 := (S0_cmp_bsx3.put_tail3 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0 cx g e u lo CX Gbs Gzb Hu OK0 Hnb ROOM SEP2 SPE SPA t1 t2 t3 t4 t5 t6).
  Ltac prep :=
    let ALE := ident:(ALE) in let AL1 := ident:(AL1) in let AL2 := ident:(AL2) in let ALF := ident:(ALF) in let ALB := ident:(ALB) in let ALFb := ident:(ALFb) in pose proof CX as CX'; unfold cctx_ok in CX'; cbv zeta in CX';
    bz_ceil; bz_params; unfold ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, IMG_HI3, CEIL in CX';
    cps_destruct CX' as (RE1 & RE2 & RA1 & RA1' & RA2 & RA2' & RFT & RFT' & RBZ & RBZ' & RFB & RFB' & ALE & AL1 & AL2 & ALF & ALB & ALFb & LJ & LJB); try lin16 ALE; try lin16 AL1; try lin16 AL2; try lin16 ALF; try lin16 ALB; try lin16 ALFb;
    pose proof SEP2 as SEP2'; pose proof SPE as SPE'; pose proof SPA as SPA'; unfold apart, ESTATE_SIZE in SEP2', SPE', SPA';
    unfold ESTATE_SIZE in *.
  Ltac fl := wstep; flags.
  Ltac bnt := wstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => if_false_z | |- _ => idtac end.

  (* [comment removed for export] *)
  Lemma put_tail2 : forall (b1 : bw) (m : word -> option byte) (xbuf x5 x13 x15 x16 x17 : word),
    bw_ok (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) -> (bw_numZ b0 <= bw_numZ (bsW b0 8 (Z.land (Z.shiftr u 24) 255)))%Z ->
    (8 * bw_numZ (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) + bw_live (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) <= 8 * bw_numZ b0 + bw_live b0 + 8)%Z ->
    b1 = bs_needw BS_FUEL (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) -> (0 <= bw_live b1 < 8)%Z -> MEMb b1 m ->
    (bv_unsigned xbuf mod 4294967296 = bw_buff b1)%Z ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) xbuf x13 (Z_to_bv 64 (bw_live b1)) x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16da8) fc None m (seg_rom s0segs)).
  Proof.
    intros b1 m xbuf x5 x13 x15 x16 x17 OKc Nc0 Bc Eb1 L1 MEM XB.
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU |- *.
    cps_pose (bs_needw_post BS_FUEL (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) OKc ltac:(cps_destruct OKc as (?&?&?); change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia)) as (OK1 & M1 & N1).
    pose proof (bs_needw_credit BS_FUEL (bsW b0 8 (Z.land (Z.shiftr u 24) 255))) as CR1.
    rewrite <- Eb1 in OK1, M1, N1, CR1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK0 as (OK0b & OK0l & OK0n). cps_pose OKc as (OKcb & OKcl & OKcn).
    (* [comment removed for export] *)
    wstep. wstep. wstep. bnt. wstep. wstep. bnt. wstep. bnt.
    wstep. rewrite (sx32_slli40 u Hu). wstep. wstep.
    replace ((32 - bw_live b1 + -8) mod 32)%Z with (32 - bw_live b1 - 8)%Z by (rewrite Z.mod_small by lia; lia).
    wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl (Z.land (Z.shiftr u 16) 255) (32 - bw_live b1 - 8)) mod 4294967296))%Z.
    { first [ rewrite (low32_or_shifted _ _ xbuf (bw_buff b1) XB) by lia | rewrite (low32_or_shifted2 _ _ xbuf (bw_buff b1) XB) by lia ].
      rewrite <- ?(byte3_eq u), ?(byte2_eq u), ?(byte1_eq u) by lia. first [ reflexivity | rewrite low32_small; [reflexivity| change 4294967296%Z with (2^32)%Z; apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]] ]. }
    cps_pose (bsW8_ok (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) (Z.land (Z.shiftr u 16) 255) OKc ltac:(apply Z.land_nonneg; right; lia)) as (OKk & Nk & Lk).
    pose proof (bsW_credit (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) as CRk.
    assert (XBk : (Z.lor (bw_buff b1) (Z.shiftl (Z.land (Z.shiftr u 16) 255) (32 - bw_live b1 - 8) mod 4294967296) = bw_buff (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)))%Z).
    { unfold bsW at 1. cbn [bw_buff bw_live]. subst b1. reflexivity. }
    (* [comment removed for export] *)
    bnt. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (put_loop3 BS_FUEL (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255)) mm _ _ _ _ _);
      [st_eq| exact OKk| lia| lia| exact OKk| lia| change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia| lia| lia| | |] end.
    + rewrite <- XBk. first [ rewrite (low32_or_shifted _ _ xbuf (bw_buff b1) XB) by lia | rewrite (low32_or_shifted2 _ _ xbuf (bw_buff b1) XB) by lia ].
      rewrite <- ?(byte3_eq u), ?(byte2_eq u), ?(byte1_eq u) by lia. apply Z.mod_small.
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
    + split; [|split; [|split; [| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
      * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. cbn [bsW bw_numZ]. rewrite Gzb. subst b1. exact EH1.
      * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. rewrite <- XBk.
        replace (bw_live (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255))) with (bw_live b1 + 8)%Z by (unfold bsW at 1; cbn [bw_live]; subst b1; reflexivity). exact EH2.
      * rewrite (zbl_same_bytes (e_arr2 e) nblock b1 (bsW (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) 8 (Z.land (Z.shiftr u 16) 255))); [exact AR2| subst b1; CmpFast.bsw_same| subst b1; CmpFast.bsw_same].
    + intros b2 m2 xbuf2 x52 x142 x152 x162 x172 Eb2 MEM2 XB2 L2.
      eapply (put_tail3 b2 m2); [exact OKk| lia| lia| exact Eb2| exact L2| exact MEM2| exact XB2].
  Qed.

  (* [comment removed for export] *)
  Lemma put_tail1 : forall (b1 : bw) (m : word -> option byte) (x5 x12 x14 x15 x16 x17 : word),
    bw_ok b0 -> (bw_numZ b0 <= bw_numZ b0)%Z ->
    (8 * bw_numZ b0 + bw_live b0 <= 8 * bw_numZ b0 + bw_live b0 + 0)%Z ->
    b1 = bs_needw BS_FUEL b0 -> (0 <= bw_live b1 < 8)%Z -> MEMb b1 m ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) x12 (Z_to_bv 64 (bw_live b1)) x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x16cf8) fc None m (seg_rom s0segs)).
  Proof.
    intros b1 m x5 x12 x14 x15 x16 x17 OKc Nc0 Bc Eb1 L1 MEM.
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU |- *.
    cps_pose (bs_needw_post BS_FUEL b0 OKc ltac:(cps_destruct OKc as (?&?&?); change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia)) as (OK1 & M1 & N1).
    pose proof (bs_needw_credit BS_FUEL b0) as CR1.
    rewrite <- Eb1 in OK1, M1, N1, CR1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK0 as (OK0b & OK0l & OK0n). cps_pose OKc as (OKcb & OKcl & OKcn).
    (* [comment removed for export] *)
    wstep. wstep. wstep. bnt. wstep. wstep. bnt. wstep. bnt.
    wstep. wstep. rewrite (sx32_low32_div24 u Hu). wstep.
    replace ((32 - bw_live b1 + -8) mod 32)%Z with (32 - bw_live b1 - 8)%Z by (rewrite Z.mod_small by lia; lia).
    wstep. wstep. wstep. wstep.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl (Z.land (Z.shiftr u 24) 255) (32 - bw_live b1 - 8)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite <- ?(byte3_eq u), ?(byte2_eq u), ?(byte1_eq u) by lia. first [ reflexivity | rewrite low32_small; [reflexivity| change 4294967296%Z with (2^32)%Z; apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]] ]. }
    cps_pose (bsW8_ok b0 (Z.land (Z.shiftr u 24) 255) OKc ltac:(apply Z.land_nonneg; right; lia)) as (OKk & Nk & Lk).
    pose proof (bsW_credit b0 8 (Z.land (Z.shiftr u 24) 255)) as CRk.
    assert (XBk : (Z.lor (bw_buff b1) (Z.shiftl (Z.land (Z.shiftr u 24) 255) (32 - bw_live b1 - 8) mod 4294967296) = bw_buff (bsW b0 8 (Z.land (Z.shiftr u 24) 255)))%Z).
    { unfold bsW at 1. cbn [bw_buff bw_live]. subst b1. reflexivity. }
    (* [comment removed for export] *)
    bnt. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (put_loop2 BS_FUEL (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) (bsW b0 8 (Z.land (Z.shiftr u 24) 255)) mm _ _ _ _ _);
      [st_eq| exact OKk| lia| lia| exact OKk| lia| change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia| lia| lia| | |] end.
    + rewrite <- XBk. rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite <- ?(byte3_eq u), ?(byte2_eq u), ?(byte1_eq u) by lia. apply Z.mod_small.
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia].
    + split; [|split; [|split; [| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
      * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. cbn [bsW bw_numZ]. rewrite Gzb. subst b1. exact EH1.
      * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. rewrite <- XBk.
        replace (bw_live (bsW b0 8 (Z.land (Z.shiftr u 24) 255))) with (bw_live b1 + 8)%Z by (unfold bsW at 1; cbn [bw_live]; subst b1; reflexivity). exact EH2.
      * rewrite (zbl_same_bytes (e_arr2 e) nblock b1 (bsW b0 8 (Z.land (Z.shiftr u 24) 255))); [exact AR2| subst b1; CmpFast.bsw_same| subst b1; CmpFast.bsw_same].
    + intros b2 m2 xbuf2 x52 x132 x152 x162 x172 Eb2 MEM2 XB2 L2.
      eapply (put_tail2 b2 m2); [exact OKk| lia| lia| exact Eb2| exact L2| exact MEM2| exact XB2].
  Qed.

  (* [comment removed for export] *)
  Lemma put_entry : forall (x12 x13 x14 x15 x16 x17 x5 : word),
    MEMb b0 m0 ->
    evt s0segs POST (MS (mkR ra sp gp tp x5 t1 t2 s0 s1 (Z_to_bv 64 E) (sx32 (Z_to_bv 64 u)) x12 x13 x14 x15 x16 x17
                              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x16c74) fc None m0 (seg_rom s0segs)).
  Proof.
    intros x12 x13 x14 x15 x16 x17 x5 MEM.
    cps_destruct MEM as (EH1 & EH2 & AR2 & MI & MU & WM & STK). prep. unfold EHEAD1, EHEAD2 in EH1, EH2.
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw] in EH1, EH2.
    rewrite Gbs in EH2. rewrite Gzb in EH1. unfold bsPutUInt32_W in MU |- *.
    cps_pose OK0 as (OK0b & OK0l & OK0n).
    (* [comment removed for export] *)
    wstep. bnt. wstep. wstep.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      eapply (put_tail1 b0 m0); [exact OK0| lia| lia| | lia| ].
      + unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b0)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. exact EH2.
    - (* [comment removed for export] *)
      wstep. wstep. wstep.
      enter_with (put_loop1 BS_FUEL b0 b0 m0 _ _ _ _ _); [st_eq| exact OK0| lia| lia| exact OK0| lia| change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia| lia| lia| | |].
      + rewrite low32_sx32, low32_lit. apply Z.mod_small. lia.
      + split; [|split; [|split; [exact AR2| split; [exact MI| split; [exact MU| split; [exact WM| exact STK]]]]]].
        * unfold EHEAD1. cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_bw]. rewrite Gzb. exact EH1.
        * unfold EHEAD2. cbn [e_bw est_set_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF]. rewrite Gbs. exact EH2.
      + intros b1 m' x5' x12' x14' x15' x16' x17' Eb1 MEM' L1. eapply (put_tail1 b1 m'); [exact OK0| lia| lia| exact Eb1| exact L1| exact MEM'].
  Qed.
End PUT.

Theorem S0_bsPutUInt32S : bsPutUInt32_specS S0C.
Proof.
  unfold bsPutUInt32_specS. cbn [ci_segs ci_bsPutUInt32 S0C]. intros until lo. intros -> -> Hu EH1 EH2 AR2 MI ST LO CX SEP Gbs Gzb OK Hnb ROOM.
  pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'. cps_destruct CX' as (_ & RE2 & _ & _ & _ & RA2' & _).
  unfold cctx_sep in SEP. cbv zeta in SEP. cps_destruct SEP as (_ & SEP2 & _).
  eapply put_entry; try eassumption; [lia | lia |].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  split; [apply munch_refl|]. split; [apply wmono_refl| eassumption].
Qed.

End ACeilS1.
