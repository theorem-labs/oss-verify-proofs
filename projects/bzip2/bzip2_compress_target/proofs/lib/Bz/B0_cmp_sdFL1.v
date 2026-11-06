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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith2 BzWalkArith4 BzCLemmasSd BzCLemmasSd2 CmpFsKit CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_sdV.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac openCX_d CX SEP CEP :=
  let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in
  let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let ME := ident:(ME) in let MA1 := ident:(MA1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in
  let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in
  let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
  let U := fresh "CEPL" in pose proof CEP as U; unfold CEIL in U;
  cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
  clear XF0 XF1 Xb0 Xb1 Xf0 Xf1 MF Mb Mf LJb;
  let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
  cps_destruct S as (?AEA1 & ?AEA2 & _ & _ & _ & ?AA12 & _); hide_disj.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDFL1.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF : Z) (w64 w72 w104 : word).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Notation INUA := (e_inUse e). Notation SLMA := (e_selectorMtf e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG : Z) (m0 : word -> option byte).
  Notation WD := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P + 1384, P + 1568); (P + 1576, P + 1592)]%Z.
  Hypothesis VW : sd_vw cx e P FB SHF SHE w64 w72 w104 m0.
  Hypothesis SHe : shzW b0segs WD m0 E (E + ESTATE_SIZE).
  Hypothesis SH1 : shzW b0segs WD m0 A1 (A1 + ARR1_SIZE).
  Hypothesis SH2 : shzW b0segs WD m0 A2 (A2 + ARR2_SIZE).
  Notation MD H i16 b m := (MA3 cx g e nG P m0 H i16 b m).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX := openCX_d CX SEP CEP.
  Ltac openMD H := openMA3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMA3 Gmtf Gbs Gzb.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation RD ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 644))
         (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 80)) s10 (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Notation SX L := (L cx g e Q gp tp s0 F fc P SHE FB SHF w64 w72 w104 CX SEP Gmtf Gbs Gzb Hnb CEP PHI AE LIM HLIM nG m0 VW SHe SH1 SH2).
  (* [comment removed for export] *)
  Notation FLX L f H bs b m := (SX L f H bs b m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

  (* [comment removed for export] *)
  Lemma fl_93c8c : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (t4' t5' t6' a3' s10' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt b0segs Q (MS (RD ra t0 t1 t2 (Z_to_bv 64 (bw_live b1)) a1 a2 a3' a4 a5 a6 (Z_to_bv 64 7) s10' t3 t4' t5' t6')
                         F (Z_to_bv 64 0x94084) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 7) s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x93f50) fc None m (seg_rom b0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
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
    brun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm ra t0 t1 t2 _ a1 a2 _ a4 a5 a6 _ t3 _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' t4' t5' t6' a3' s10' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fl_93e08 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (t4' t5' t6' a3' s10' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt b0segs Q (MS (RD ra t0 t1 t2 (Z_to_bv 64 (bw_live b1)) a1 a2 a3' a4 a5 a6 (Z_to_bv 64 7) s10' t3 t4' t5' t6')
                         F (Z_to_bv 64 0x94200) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 7) s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x940cc) fc None m (seg_rom b0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
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
    brun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm ra t0 t1 t2 _ a1 a2 _ a4 a5 a6 _ t3 _ _ _); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' t4' t5' t6' a3' s10' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fl_9401c : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s10' a3' ra' a6' t4' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt b0segs Q (MS (RD ra' t0 (Z_to_bv 64 7) t2 (Z_to_bv 64 (bw_live b1)) a1 a2 a3' a4 a5 a6' a7 s10' t3 t4' t5 t6)
                         F (Z_to_bv 64 0x94414) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 (Z_to_bv 64 7) t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x942e0) fc None m (seg_rom b0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
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
    brun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm _ t0 t2 _ a1 a2 _ a4 a5 _ a7 _ t3 _ t5 t6); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' s10' a3' ra' a6' t4' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fl_9419c : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s10' ra' a3' a6' t4' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt b0segs Q (MS (RD ra' t0 (Z_to_bv 64 7) t2 (Z_to_bv 64 (bw_live b1)) a1 a2 a3' a4 a5 a6' a7 s10' t3 t4' t5 t6)
                         F (Z_to_bv 64 0x94594) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 (Z_to_bv 64 7) t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x94460) fc None m (seg_rom b0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
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
    brun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm _ t0 t2 _ a1 a2 _ a4 a5 _ a7 _ t3 _ t5 t6); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' s10' ra' a3' a6' t4' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fl_943a4 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (a3' a4' a2' a5' a6' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt b0segs Q (MS (RD ra t0 t1 t2 (Z_to_bv 64 (bw_live b1)) (Z_to_bv 64 7) a2' a3' a4' a5' a6' a7 s10 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x947a0) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 a0 (Z_to_bv 64 7) a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x94668) fc None m (seg_rom b0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
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
    brun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm ra t0 t1 t2 _ _ _ _ _ _ a7 s10 t3 t4 t5 t6); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' a3' a4' a2' a5' a6' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fl_9454c : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (a0' a4' a2' a5' a6' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt b0segs Q (MS (RD ra t0 t1 t2 a0' (Z_to_bv 64 7) a2' (Z_to_bv 64 (bw_live b1)) a4' a5' a6' a7 s10 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x94948) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 a0 (Z_to_bv 64 7) a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x94810) fc None m (seg_rom b0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
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
    brun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm ra t0 t1 t2 _ _ _ _ _ _ a7 s10 t3 t4 t5 t6); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' a0' a4' a2' a5' a6' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.
End SDFL1.
End ACeilS1.
