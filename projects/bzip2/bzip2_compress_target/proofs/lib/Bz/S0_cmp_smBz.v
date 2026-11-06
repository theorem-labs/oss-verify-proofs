(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsS0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCHuff BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCut0 CmpCutSM CmpCutSmA CmpCutSmA0 CmpCutSmB CmpCutSmB0 BzCFactsSmA.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpFsKit0 CmpHmKit CmpSmKit CmpSmKit2 CmpSmKit20.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit20.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_smBb.

From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzCHuffF1. From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require S0_cmp_hmZ.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl Require S0_memset.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeilTac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpCut6.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require CpsOpen.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.
Module S0_cmp_smBc.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.PropExec.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.Tac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.WalkLib OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.SegsS0.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzTac2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArr OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCStream OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCState OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuff OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCMtf OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzArrD OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCRebuildF OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpMem OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCut0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSM OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmA0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpCutSmB0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmA OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCHuffF1.BzCFactsHm OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCSmF1 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCFactsSmB2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpFsKit0 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit2 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpSmKit20 OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_hmZ.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Musl.S0_memset.
 Unset Lia Cache.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.ACeilTac.
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
(* [comment removed for export] *)

Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib.CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)

#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section GI.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word) (iter : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img S0C cx. Hypothesis GM : g_mtf g = true.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis W56 : w56 = Z_to_bv 64 (E + 51648).
  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  Ltac openCX :=
    let XA20 := ident:(XA20) in let XA21 := ident:(XA21) in let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA2 MF Mb Mf LJb;
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    destruct S as (?AEA1 & _).
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.

  (* [comment removed for export] *)
  Notation IR ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
         (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_rfz : forall (n : nat) (t : Z) (rf : zarr) (m mf : word -> option byte) (x584 : word)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
    u32arr s0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    rw_cells s0segs m (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
    mem_inv s0segs m -> munch [(E + 45448, E + 51640)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      u32arr s0segs m' (E + 45448) (ovw (sm_rfreq_zero n rf A t) (jseg J 45448 6192) 1548) ->
      rw_cells s0segs m' (usp + 576) [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))] ->
      mem_inv s0segs m' -> munch [(E + 45448, E + 51640)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (IR (Z_to_bv 64 0x16120) t0 t1 t2 (Z_to_bv 64 nG) (Z_to_bv 64 (E + 45448 + 1032 * (nG - 1))) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 (E + 45448 + 1032 * (nG - 1))) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16138) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (IR ra t0 t1 t2 (Z_to_bv 64 t) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nG - 1 - t)) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 (E + 45448 + 1032 * t)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16104) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t rf m mf x584 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ht Ht0 Hn RFQ C576 MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length_nat rf (jseg J 45448 6192) 1548) as LRF.
    rewrite sm_rfreq_zero_S in K.
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases Kn; zify_cond_z Kn; [exfalso; revert Kn; rewrite ?signed_lit by lia; lia|]. lstep. lstep. lstep.
    cps_destruct (rfrow_before_memset s0segs m (E + 45448) rf (jseg J 45448 6192) 1548 t A RFQ ltac:(lia) ltac:(lia) ltac:(lia)) as (R0 & R1 & R2). clear RFQ.
    (* [comment removed for export] *)
    lstep.
    eapply evt_cut.
    { eapply (S0_memset_specZ (E + 45448 + 1032 * t) (4 * A) 0); [exact R1 | exact MI | f_equal; lia | reflexivity | f_equal; lia | lia | lia | lia]. }
    clear R1. post_call s0segs m.
    match goal with H : rw_cells _ _ (E + 45448 + 1032 * t)%Z _ |- _ => rename H into R1 end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m2 := mm) in * end.
    pose proof (rfrow_after_memset s0segs m2 (E + 45448) rf (jseg J 45448 6192) 1548 t A R0 R1 R2 ltac:(lia) ltac:(lia) ltac:(lia)) as RFQ. clear R0 R1 R2.
    (* [comment removed for export] *)
    lstep; if_cases Ke; zify_cond_z Ke.
    - assert (n = 0)%nat by lia. subst n. cbn [sm_rfreq_zero] in K.
      enter_with (K m2 _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact RFQ| assumption| exact MI2| assumption| assumption].
    - lstep. lstep. lstep. lstep.
      enter_with (IH (t + 1)%Z (zfill0 (Z.to_nat A) rf (258 * t)) m2 mf x584); [st_eq| lia| lia| lia| exact RFQ| assumption| exact MI2| assumption| assumption| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_lpk : forall (n : nat) (v : Z) (lp len : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s4 s6 t3 t4 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    mem_inv s0segs m -> munch [(E + 51640, E + 55768)]%Z mf m -> wmono s0segs mf m ->
    (CEIL <= usp)%Z -> (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (a3 : word),
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (sm_lenpack n lp len v) (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      mem_inv s0segs m' -> munch [(E + 51640, E + 55768)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (IR ra t0 t1 t2 s1 (Z_to_bv 64 (E + 38998 + A)) (Z_to_bv 64 (E + 51648 + 16 * A)) (Z_to_bv 64 (E + 51648 + 16 * A)) a3 a4 a5 a6 a7 s2 s4 s6 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16194) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (IR ra t0 t1 t2 s1 (Z_to_bv 64 (E + 38998 + v)) (Z_to_bv 64 (E + 51648 + 16 * v)) a2 a3 a4 a5 a6 a7 s2 s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16148) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v lp len m mf ra t0 t1 t2 s1 a2 a3 a4 a5 a6 a7 s2 s4 s6 t3 t4 t5 t6 Hv Hv0 Hn LF LEN LPK S8 MI MU WM CE SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. bz_ceil; bz_params; unfold CEIL in CE. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LL.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length_nat lp (jseg J 51640 4128) 1032) as LLP.
    unfold sm_slots3 in S8. cbv zeta in S8.
    rewrite sm_lenpack_S in K. rewrite !lenpack_word_eq in K by (lazymatch goal with |- (0 <= zget _ (258 * ?t + _))%Z => exact (proj1 (proj2 (LF t v ltac:(lia) ltac:(lia)))) end).
    (* [comment removed for export] *)
    Ltac lprow LEN LPK LF len v thi tlo ih il j :=
      let Dh := fresh "Dh" in let Rh := fresh "Rh" in let Dl := fresh "Dl" in let Rl := fresh "Rl" in let RD := fresh "RD" in
      destruct (LF thi v ltac:(lia) ltac:(lia)) as [Dh Rh]; destruct (LF tlo v ltac:(lia) ltac:(lia)) as [Dl Rl];
      replace (258 * thi + v)%Z with ih in Dh, Rh by lia; replace (258 * tlo + v)%Z with il in Dl, Rl by lia;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovb_read1 s0segs mm (E + 37708) _ (jseg J 37708 1548) 1548 ih _ LEN ltac:(lia) Dh ltac:(unfold wa; f_equal; lia)) as RD end;
      lstep; clear RD; rewrite ?unsigned_lit8 by lia;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovb_read1 s0segs mm (E + 37708) _ (jseg J 37708 1548) 1548 il _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD end;
      lstep; clear RD; rewrite ?unsigned_lit8 by lia;
      lstep; lstep;
      pose proof (lenpack_word_range (zget len il) (zget len ih) ltac:(lia) ltac:(lia));
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch type of LPK with u32arr _ _ _ (ovw ?lpx _ _) =>
        pose proof (u32arr_store_ok s0segs mm (E + 51640) _ (4 * v + j) _ LPK ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
        lstep; store_addr (E + 51640 + 4 * (4 * v + j))%Z;
        ovw_store LPK (4 * v + j)%Z (Z.lor (zget len ih * 65536) (zget len il)) (rewrite unsigned_lit by lia; reflexivity) end end.
    replace (258 * 1 + v)%Z with (258 + v)%Z in K by lia. replace (258 * 0 + v)%Z with v in K by lia.
    replace (258 * 3 + v)%Z with (774 + v)%Z in K by lia. replace (258 * 2 + v)%Z with (516 + v)%Z in K by lia.
    replace (258 * 5 + v)%Z with (1290 + v)%Z in K by lia. replace (258 * 4 + v)%Z with (1032 + v)%Z in K by lia.
    lprow LEN LPK LF len v 1%Z 0%Z (258 + v)%Z v 0%Z. replace (4 * v + 0)%Z with (4 * v)%Z in LPK by lia.
    lprow LEN LPK LF len v 3%Z 2%Z (774 + v)%Z (516 + v)%Z 1%Z.
    lprow LEN LPK LF len v 5%Z 4%Z (1290 + v)%Z (1032 + v)%Z 2%Z.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (v + 1)%Z _ len _ mf); [st_eq| lia| lia| lia| exact LF| exact LEN| exact LPK| exact S8| assumption| exact MU| exact WM| bz_ceil; bz_params; unfold CEIL; lia| exact SPB| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_lenpack] in K.
      enter_with (K _ _); [st_eq| exact LEN| exact LPK| exact S8| assumption| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_mkl : forall (n t : nat) (s : sits) (rfe : zarr) (nSel lo : Z) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (Z.of_nat t + Z.of_nat n = nG)%Z -> (1 <= n)%nat ->
    (forall t', (Z.of_nat t' < nG)%Z ->
       hm_facts (ml_len e s t') rfe (258 * Z.of_nat t') (258 * Z.of_nat t') A /\
       ml_len e s (S t') = hs_len (hbMakeCodeLengths (ml_len e s t') rfe znew znew znew (258 * Z.of_nat t') (258 * Z.of_nat t') A 17)) ->
    (forall tt v, (0 <= tt < nG)%Z -> (0 <= v < A)%Z -> zdef rfe (258 * tt + v) = true /\ (0 <= zget rfe (258 * tt + v) <= nMTF)%Z) ->
    u8arr s0segs m (E + 37708) (ovb (ml_len e s t) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 45448) (ovw rfe (jseg J 45448 6192) 1548) ->
    cimg_mem S0C m sv -> mem_inv s0segs m ->
    stk s0segs m lo usp -> (lo + HM_FRAME <= usp)%Z -> (CEIL <= lo)%Z -> (usp mod 16 = 0)%Z ->
    munch [(E + 37708, E + 39256); (usp - HM_FRAME, usp)]%Z mf m -> wmono s0segs mf m ->
    (usp + 1008 <= 18446744073709551616)%Z ->
    (forall m' (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      u8arr s0segs m' (E + 37708) (ovb (ml_len e s (t + n)) (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 45448) (ovw rfe (jseg J 45448 6192) 1548) ->
      cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
      munch [(E + 37708, E + 39256); (usp - HM_FRAME, usp)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 45448 + 1032 * nG)) a0 a1 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) (Z_to_bv 64 nSel) (Z_to_bv 64 (usp + 616)) (Z_to_bv 64 (E + 37708 + 258 * nG)) (Z_to_bv 64 (E + 45448 + 1032 * nG))
                            (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17288) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 45448 + 1032 * nG)) a0 a1 a2 a3 a4 a5 a6 a7
                          (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) (Z_to_bv 64 nSel) (Z_to_bv 64 (usp + 616)) (Z_to_bv 64 (E + 37708 + 258 * Z.of_nat t)) (Z_to_bv 64 (E + 45448 + 1032 * Z.of_nat t))
                          (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17268) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t s rfe nSel lo m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Ht Hn MLF RFF LEN RFQ CM MI ST STK CLO AL MU WM SPB K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. unfold HM_FRAME in *. bz_ceil; bz_params; unfold CEIL in CLO. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3 in IMG'. cbn [ci_hi S0C] in IMG'. destruct IMG' as (IE & _). unfold ESTATE_SIZE in IE.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8.
    destruct (MLF t ltac:(lia)) as [HMF EML].
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep.
    pose proof S0_hbMakeCodeLengths as HBS. unfold hbMakeCodeLengths_spec in HBS. cbn [ci_segs ci_hbMakeCodeLengths ci_hi S0C] in HBS. unfold HM_FRAME in HBS.
    eapply evt_cut.
    { eapply (HBS _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m (E + 37708)%Z (E + 45448)%Z (258 * Z.of_nat t)%Z (258 * Z.of_nat t)%Z A 1548%Z 1548%Z lo (ml_len e s t) rfe (jseg J 37708 1548) (jseg J 45448 6192) sv);
        [ f_equal; lia | f_equal; lia | reflexivity | reflexivity
        | exact LEN | exact RFQ | exact CM | exact MI | exact ST | lia | bz_ceil; bz_params; unfold CEIL; lia | exact AL
        | lia | lia | lia | lia | lia | lia | bz_ceil; bz_params; unfold CEIL; lia | lia | bz_ceil; bz_params; unfold CEIL; lia
        | clear -ME; Z.div_mod_to_equations; lia
        | unfold apart; lia | unfold img_apart, IMG_LO3; cbn [ci_hi S0C]; lia | unfold img_apart, IMG_LO3; cbn [ci_hi S0C]; lia
        | intros v Hv; destruct (RFF (Z.of_nat t) v ltac:(lia) Hv) as [D R]; split; [exact D| lia]
        | exact HMF ]. }
    clear LEN MI ST. unfold hbMakeCodeLengths_post.
    intros ms' PO; destruct_exs PO. destruct PO as [EQ [MUc [WMc [MI2 [ST LEN]]]]]; subst ms'.
    lazymatch type of MUc with munch _ m ?m' =>
      pose proof (cimg_transportK0 S0C _ m m' sv eq_refl CM MUc WMc
                    ltac:(constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia| constructor; [cbn [fst snd ci_hi S0C]; unfold IMG_LO3; lia| constructor]])) as CM';
      clear CM; transport_after_call s0segs m m' MUc WMc; clear MUc WMc; try clear m end.
    lazymatch goal with |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
    rewrite <- EML in LEN.
    (* [comment removed for export] *)
    lstep. lstep. lstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (S t) s rfe nSel lo _ mf); [st_eq| lia| lia| exact MLF| exact RFF| exact LEN| assumption| exact CM'| exact MI2| exact ST| lia| bz_ceil; bz_params; unfold CEIL; lia| exact AL| assumption| assumption| exact SPB|].
      intros mm; intros *. replace (S t + n)%nat with (t + S n)%nat by lia. apply K.
    - assert (n = 0)%nat by lia. subst n. replace (t + 1)%nat with (S t) in K by lia.
      enter_with (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact LEN| assumption| exact CM'| exact MI2| exact ST| assumption| assumption].
  Qed.
End GI.

End ACeilS1.
End S0_cmp_smBc.

Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBb OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.S0_cmp_smBz.S0_cmp_smBc.
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
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.

(* [comment removed for export] *)
Ltac lin16 H := lazymatch type of H with (?x mod 16 = 0)%Z =>
  let E := fresh "E16" in pose proof (Z.div_mod x 16 ltac:(lia)) as E; rewrite H, Z.add_0_r in E; clear H;
  let q := fresh "q16" in set (q := (x / 16)%Z) in E; clearbody q; rename E into H end.
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section GZ.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (sp gp tp : word) (F : bvmap 5 word) (fc : bv 32) (sv w24 w56 : word).
  Variables (cost0 fave0 heap0 weight0 parent0 : zarr) (lo : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis IMG : cctx_img S0C cx. Hypothesis GM : g_mtf g = true.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation usp := (bv_unsigned sp).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis W56 : w56 = Z_to_bv 64 (E + 51648).
  Hypothesis FACTS : smB_facts e cost0 fave0 heap0 weight0 parent0.
  Hypothesis CLO : (CEIL <= lo)%Z. Hypothesis STK : (lo + HM_FRAME <= usp)%Z. Hypothesis AL : (usp mod 16 = 0)%Z.
  Hypothesis SPB : (usp + 1008 <= 18446744073709551616)%Z.
  Notation ITK k := (ITk e cost0 fave0 heap0 weight0 parent0 k).

  Ltac simpl_arr_sizes ::= CmpFast.sas10.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Local Ltac simpl_sizes ::=
    rewrite ?length_app;
    cbn [cells_size csize length cbytes Nat.add Z.of_nat Pos.of_succ_nat Pos.succ EHEAD2 sm_slots3];
    rewrite ?length_le8, ?length_le4, ?length_le2, ?length_le1, ?length_app; cbn [length].
  Ltac openCX :=
    let XA20 := ident:(XA20) in let XA21 := ident:(XA21) in let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
    clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 MA2 MF Mb Mf LJb;
    let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
    destruct S as (?AEA1 & _).
  Ltac openF :=
    let H := fresh "ST0" in pose proof (proj1 FACTS) as H; unfold smB_static in H;
    cps_destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.

  (* [comment removed for export] *)
  Notation IR ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s6 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
         (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6).
  Notation GR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 37708)) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) s4 (Z_to_bv 64 (usp + 616)) s6 (Z_to_bv 64 (usp + 616 + 4 * nG))
         (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6).
  Notation C576L x584 := [C8 (Z_to_bv 64 999999999); C8 x584; C8 (Z_to_bv 64 (flag6 nG)); C8 (Z_to_bv 64 (E + 1704)); C8 (Z_to_bv 64 (e_nInUse e))].

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_pre : forall (iter : Z) (lp len : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    mem_inv s0segs m -> munch [(E + 51640, E + 55768)]%Z mf m -> wmono s0segs mf m ->
    (forall m' (a1 a2 a3 : word),
      u8arr s0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (if (nG =? 6)%Z then sm_lenpack (Z.to_nat A) lp len 0 else lp) (jseg J 51640 4128) 1032) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      mem_inv s0segs m' -> munch [(E + 51640, E + 55768)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (GR ra (Z_to_bv 64 0) t1 t2 (Z_to_bv 64 nMTF) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (E + 45448 + 1032 * (nG - 1))) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x161b4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (IR ra t0 t1 t2 (Z_to_bv 64 nG) (Z_to_bv 64 (E + 45448 + 1032 * (nG - 1))) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 (E + 45448 + 1032 * (nG - 1))) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x16138) fc None m (seg_rom s0segs)).
  Proof.
    intros iter lp len m mf ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 LF LEN LPK S8 EH2 MI MU WM K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. openF. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    assert (CE : (alloc_ceiling <= usp)%Z) by (bz_ceil; bz_params; unfold CEIL, HM_FRAME in *; lia).
    unfold sm_slots3 in S8. cbv zeta in S8. unfold EHEAD2 in EH2. rewrite GM in EH2.
    (* [comment removed for export] *)
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    lstep. lstep; if_cases Kf; zify_cond_z Kf; unfold flag6 in Kf.
    - (* [comment removed for export] *)
      destruct (Z.eqb_spec nG 6) as [E6|N6]; [exfalso; lia|].
      (* [comment removed for export] *)
      lstep. rewrite (sx32_of_Z (e_nMTF e)) by (change (2^31)%Z with 2147483648%Z; lia).
      lstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
      lstep. lstep. lstep. lstep. lstep.
      enter_with (K m a1 a2 a3); [st_eq| exact LEN| exact LPK| unfold sm_slots3; cbv zeta; exact S8| unfold EHEAD2; rewrite GM; exact EH2| exact MI| exact MU| exact WM].
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [| exfalso; lia].
      (* [comment removed for export] *)
      lstep. lstep. subst w56.
      enter_with (S0_sm_lpk cx e Q sp gp tp F fc sv w24 (Z_to_bv 64 (E + 51648)) iter CX SEP HA (Z.to_nat A) 0 lp len m m);
        [st_eq| lia| lia| lia| exact LF| exact LEN| exact LPK| unfold sm_slots3; cbv zeta; exact S8| exact MI| apply munch_refl| apply wmono_refl| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
      clear LEN LPK S8 MI. intros m' a3' LEN LPK S8 MI MU' WM'.
      transport_after_call s0segs m m' MU' WM'. clear MU' WM'.
      (* [comment removed for export] *)
      unfold sm_slots3 in S8. cbv zeta in S8.
      lstep. rewrite (sx32_of_Z (e_nMTF e)) by (change (2^31)%Z with 2147483648%Z; lia).
      lstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
      lstep. lstep. lstep. lstep. lstep.
      enter_with (K m' (Z_to_bv 64 (E + 51648 + 16 * A)) (Z_to_bv 64 (E + 51648 + 16 * A)) a3');
        [st_eq| exact LEN| exact LPK| unfold sm_slots3; cbv zeta; exact S8| unfold EHEAD2; rewrite GM; exact EH2| exact MI| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_ihead : forall (iter : Z) (f : zarr) (J616 : list byte) (m mf : word -> option byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    length J616 = 24%nat ->
    u8arr s0segs m (usp + 616) J616 ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    mem_inv s0segs m -> munch [(usp + 616, usp + 640)]%Z mf m -> wmono s0segs mf m ->
    (forall m',
      u32arr s0segs m' (usp + 616) (zw32 (zero6 f) 6) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
      mem_inv s0segs m' -> munch [(usp + 616, usp + 640)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (IR ra t0 t1 t2 (Z_to_bv 64 0) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (nG - 1 - 0)) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 (E + 45448 + 1032 * 0)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x16104) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (IR ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 45448)) s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x160e8) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ cx e Q sp gp tp F fc sv w24 w56 cost0 fave0 heap0 weight0 parent0 lo CX SEP FACTS CLO STK SPB.
    intros iter f J616 m mf ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 LJ FAV S8 MI MU WM K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. openF. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    assert (CE : (alloc_ceiling <= usp)%Z) by (bz_ceil; bz_params; unfold CEIL, HM_FRAME in *; lia).
    unfold sm_slots3 in S8. cbv zeta in S8.
    cps_destruct (fave_cells_of_junk s0segs m (usp + 616) J616 FAV LJ) as (f1 & f2 & f3 & FC). clear FAV.
    (* [comment removed for export] *)
    lstep. (lstep; lit_store). (lstep; lit_store). (lstep; lit_store). lstep. lstep. lstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (fave_zero_cells s0segs mm (usp + 616) f FC) as FAVE end.
    enter_with (K _); [st_eq| exact FAVE| unfold sm_slots3; cbv zeta; assumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_mid : forall (iter totc nSel : Z) (m mf : word -> option byte)
      (ra t1 t2 a1 a2 a3 a4 a5 a6 s6 t3 t4 t5 t6 : word),
    (0 <= iter < 4)%Z -> (0 <= totc < 2147483648)%Z ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 iter) ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    mem_inv s0segs m -> munch [(usp + 104, usp + 112)]%Z mf m -> wmono s0segs mf m ->
    (forall m' (a3 : word),
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 (iter + 1)) ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      mem_inv s0segs m' -> munch [(usp + 104, usp + 112)]%Z mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (mkR ra sp gp tp (Z_to_bv 64 nMTF) t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 (E + 45448 + 1032 * nG)) (Z_to_bv 64 (iter + 1)) (Z_to_bv 64 3) a2 a3 a4 a5 a6 (Z_to_bv 64 totc)
                            (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A1) (Z_to_bv 64 nSel) (Z_to_bv 64 (usp + 616)) (Z_to_bv 64 (E + 37708 + 258 * Z.of_nat 0)) (Z_to_bv 64 (E + 45448 + 1032 * Z.of_nat 0))
                            (Z_to_bv 64 (usp + 888 + 2 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (-1)) (Z_to_bv 64 1032) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x17268) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (GR ra (Z_to_bv 64 nMTF) t1 t2 (Z_to_bv 64 nMTF) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 totc) (Z_to_bv 64 nSel) s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x17230) fc None m (seg_rom s0segs)).
  Proof using BZP ACEIL__ cx e g Q sp gp tp F fc sv w24 w56 cost0 fave0 heap0 weight0 parent0 lo CX SEP GM FACTS CLO STK SPB.
    intros iter totc nSel m mf ra t1 t2 a1 a2 a3 a4 a5 a6 s6 t3 t4 t5 t6 HIT HTC S8 EH2 MI MU WM K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. openF. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    assert (CE : (alloc_ceiling <= usp)%Z) by (bz_ceil; bz_params; unfold CEIL, HM_FRAME in *; lia).
    unfold sm_slots3 in S8. cbv zeta in S8. unfold EHEAD2 in EH2. rewrite GM in EH2.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep. lstep; if_cases Kv; zify_cond_z Kv; [exfalso; revert Kv; rewrite ?signed_lit by lia; lia|].
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep. lstep.
    enter_with (K _ _); [st_eq| unfold sm_slots3; cbv zeta; assumption| unfold EHEAD2; rewrite GM; assumption| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  Ltac cimgT CM MU WM :=
    let H := fresh "CMx" in
    pose proof (cimg_transportK0 S0C _ _ _ _ eq_refl CM MU WM
      ltac:(unfold w_img_apartK, Wg, IMG_LO3; repeat (apply Forall_cons; [cbn [fst snd ci_hi S0C]; lia|]); apply Forall_nil)) as H;
    clear CM; rename H into CM.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_iterk : forall (k : nat) (Jsp J616 jc : list byte) (x584 : word) (m me : word -> option byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    (k < 4)%nat ->
    length jc = 12%nat -> length Jsp = 392%nat -> length J616 = 24%nat ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr s0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
    u32arr s0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 (Z.of_nat k)) ->
    u8arr s0segs m (usp + 184) Jsp ->
    rw_cells s0segs m (usp + 576) (C576L x584) ->
    u8arr s0segs m (usp + 616) J616 ->
    u8arr s0segs m (usp + 888) jc ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo usp ->
    munch (smB_W3 cx usp) me m -> wmono s0segs me m ->
    (forall m' (Jsp' J616' jc' : list byte) (x584' : word) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      length jc' = 12%nat -> length Jsp' = 392%nat -> length J616' = 24%nat ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr s0segs m' (E + 37708) (ovb (it_len (ITK (S k))) (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (it_lp (ITK (S k))) (jseg J 51640 4128) 1032) ->
      u32arr s0segs m' (E + 45448) (ovw (it_rfreq (ITK (S k))) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (it_sel (ITK (S k))) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 (Z.of_nat k + 1)) ->
      u8arr s0segs m' (usp + 184) Jsp' ->
      rw_cells s0segs m' (usp + 576) (C576L x584') ->
      u8arr s0segs m' (usp + 616) J616' ->
      u8arr s0segs m' (usp + 888) jc' ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
      munch (smB_W3 cx usp) me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (IR ra' t0' t1' t2' (Z_to_bv 64 (E + 45448 + 1032 * nG)) (Z_to_bv 64 (Z.of_nat k + 1)) (Z_to_bv 64 4) a2' a3' a4' a5' a6' a7'
                            (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (it_nSel (ITK (S k)))) (Z_to_bv 64 (E + 37708 + 258 * nG)) t3' t4' t5' t6')
                       F (Z_to_bv 64 (if (Z.of_nat k + 1 =? 4)%Z then 0x172f0 else 0x160e8)) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (IR ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 45448)) s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x160e8) fc None m (seg_rom s0segs)).
  Proof.
    intros k Jsp J616 jc x584 m me ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6
           Hk Ljc LJsp LJ616 AR1 LEN LPK RFQ SEL S8 SPL C576 FAV COST EH2 CM MI ST MU WM K.
    openCX. try lin16 ME. try lin16 MA1. try lin16 MA2. try lin16 MF. try lin16 Mb. try lin16 Mf. openF. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    bz_ceil; bz_params; unfold CEIL, HM_FRAME in CLO, STK.
    assert (CE : (alloc_ceiling <= usp)%Z) by lia.
    pose proof IMG as IMG'. unfold cctx_img, img_apart, IMG_LO3, ESTATE_SIZE in IMG'. cbn [ci_hi S0C] in IMG'. destruct IMG' as (IE & _).
    cps_destruct (proj2 FACTS k Hk) as (BL & BP & BG & BM).
    remember (ITK k) as s eqn:Es.
    unfold smB_W3, HM_FRAME in MU.
    (* [comment removed for export] *)
    enter_with (S0_sm_ihead (Z.of_nat k) (it_fave s) J616 m m);
      [st_eq| exact LJ616| exact FAV| exact S8| exact MI| apply munch_refl| apply wmono_refl|].
    clear FAV S8 MI. intros m1 FAVE S8 MI MU1 WM1.
    cimgT CM MU1 WM1. transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    enter_with (S0_sm_rfz cx e Q sp gp tp F fc CX SEP HA HNG (Z.to_nat nG) 0 (it_rfreq s) m1 m1 x584);
      [st_eq| lia| lia| lia| exact RFQ| exact C576| exact MI| apply munch_refl| apply wmono_refl| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    clear RFQ C576 MI. intros m2 y0 y1 y2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 y3 y4 y5 y6 RFQ C576 MI MU2 WM2.
    cimgT CM MU2 WM2. transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
    change (sm_rfreq_zero (Z.to_nat nG) (it_rfreq s) A 0) with (it_rf0 e s) in RFQ.
    (* [comment removed for export] *)
    enter_with (S0_sm_pre (Z.of_nat k) (it_lp s) (it_len s) m2 m2);
      [st_eq| exact BL| exact LEN| exact LPK| exact S8| exact EH2| exact MI| apply munch_refl| apply wmono_refl|].
    clear LEN LPK S8 EH2 MI. intros m3 za1 za2 za3 LEN LPK S8 EH2 MI MU3 WM3.
    cimgT CM MU3 WM3. transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    change (if (nG =? 6)%Z then sm_lenpack (Z.to_nat A) (it_lp s) (it_len s) 0 else it_lp s) with (it_lpk e s) in LPK.
    (* [comment removed for export] *)
    assert (LPF : nG = 6%Z -> forall v j, (0 <= v < A)%Z -> (0 <= j < 3)%Z -> zdef (it_lpk e s) (4 * v + j) = true /\ (0 <= zget (it_lpk e s) (4 * v + j) < 2097152)%Z).
    { intros H6 v j Hv Hj. cps_destruct (BP H6 v j Hv Hj) as (D & _ & R). exact (conj D R). }
    enter_with (S0_sm_gloop cx e g Q sp gp tp F fc sv w24 w56 (Z.of_nat k) (it_lpk e s) (it_len s) CX SEP GM HA HNG HM ZB MV BL LPF
                  (Z.to_nat (KSEL e)) 0%nat s jc Jsp x584 m3 m3);
      [st_eq| exact BG| reflexivity| reflexivity| exact HK| exact HK2| lia| lia| exact Ljc| exact LJsp
      | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact S8| exact SPL| exact C576| exact FAVE| exact COST| exact EH2| exact MI
      | apply munch_refl| apply wmono_refl| bz_ceil; bz_params; unfold CEIL; lia| exact SPB|].
    clear AR1 LEN LPK RFQ SEL S8 SPL C576 FAVE COST EH2 MI.
    intros m4 Jsp' x584' jc' ra' u1 u2 ua1 ua2 ua3 ua4 ua5 ua6 us6 u3 u4 u5 u6 Ljc' LJsp' AR1 LEN LPK RFQ SEL S8 SPL C576 FAVE COST EH2 MI MU4 WM4.
    unfold Wg in MU4. cimgT CM MU4 WM4. transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    (* [comment removed for export] *)
    pose proof (proj1 BG (Z.to_nat (KSEL e)) ltac:(lia)) as GFE. cbv zeta in GFE. change (Gj e s (Z.to_nat (KSEL e))) with (Gend e s) in GFE.
    cps_destruct GFE as (Egs & EnS & Htc & RFF & FVB & SLF).
    assert (EgsN : g_gs (Gend e s) = nMTF) by (rewrite Egs; apply Z.min_r; lia).
    (* [comment removed for export] *)
    enter_with (S0_sm_mid (Z.of_nat k) (g_totc (Gend e s)) (g_nSel (Gend e s)) m4 m4);
      [st_eq| lia| lia| exact S8| exact EH2| exact MI| apply munch_refl| apply wmono_refl|].
    clear S8 EH2 MI. intros m5 va3 S8 EH2 MI MU5 WM5.
    cimgT CM MU5 WM5. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
    (* [comment removed for export] *)
    enter_with (S0_sm_mkl cx e Q sp gp tp F fc sv CX SEP IMG HA HNG HM (Z.to_nat nG) 0%nat s (g_rfreq (Gend e s)) (g_nSel (Gend e s)) lo m5 m5);
      [st_eq| lia| lia| | | exact LEN| exact RFQ| exact CM| exact MI| exact ST| unfold HM_FRAME; lia| bz_ceil; bz_params; unfold CEIL; lia| exact AL
      | apply munch_refl| apply wmono_refl| exact SPB|].
    { intros t' Ht'. cps_destruct (proj1 BM t' Ht') as (X1 & X2 & _). exact (conj X1 X2). }
    { intros tt v Htt Hv. destruct (RFF tt v Htt Hv) as [D R]. rewrite EgsN in R. exact (conj D R). }
    clear LEN RFQ CM MI ST. intros m6 wra w0 w1 w2 wa0 wa1 wa2 wa3 wa4 wa5 wa6 wa7 w3 w4 w5 w6 LEN RFQ CM MI ST MU6 WM6.
    unfold HM_FRAME in MU6. transport_after_call s0segs m5 m6 MU6 WM6. clear MU6 WM6.
    (* [comment removed for export] *)
    destruct (MLt e s (Z.to_nat nG)) as [[[l' h'] w'] p'] eqn:EML.
    assert (EIT : ITK (S k) = SITS l' (g_rfreq (Gend e s)) (it_lpk e s) (g_sel (Gend e s)) (g_cost (Gend e s)) (g_fave (Gend e s)) (g_nSel (Gend e s)) h' w' p').
    { rewrite ITk_S, <- Es, (proj2 BM), EML. reflexivity. }
    rewrite EIT in K. cbn [it_len it_lp it_rfreq it_sel it_nSel] in K.
    unfold ml_len in LEN. replace (0 + Z.to_nat nG)%nat with (Z.to_nat nG) in LEN by lia. rewrite EML in LEN. cbn [fst] in LEN.
    apply (proj1 (u32arr_u8arr' s0segs m6 (usp + 616) _)) in FAVE.
    unfold sm_slots3 in S8. cbv zeta in S8.
    (* [comment removed for export] *)
    lstep. lstep. lstep. lstep; if_cases Kx; zify_cond_z Kx.
    - replace (if (Z.of_nat k + 1 =? 4)%Z then 94960%Z else 90344%Z) with 94960%Z in K
        by (replace (Z.of_nat k + 1 =? 4)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      enter_with (K m6 Jsp' (u32s (zw32 (g_fave (Gend e s)) 6)) jc' x584');
        [st_eq| exact Ljc'| exact LJsp'| rewrite u32s_length, zw32_length_nat; reflexivity
        | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| unfold sm_slots3; cbv zeta; exact S8| exact SPL| exact C576| exact FAVE| exact COST| exact EH2
        | exact CM| exact MI| exact ST| exact MU| exact WM].
    - (* [comment removed for export] *)
      lstep.
      replace (if (Z.of_nat k + 1 =? 4)%Z then 94960%Z else 90344%Z) with 90344%Z in K
        by (replace (Z.of_nat k + 1 =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      enter_with (K m6 Jsp' (u32s (zw32 (g_fave (Gend e s)) 6)) jc' x584');
        [st_eq| exact Ljc'| exact LJsp'| rewrite u32s_length, zw32_length_nat; reflexivity
        | exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| unfold sm_slots3; cbv zeta; exact S8| exact SPL| exact C576| exact FAVE| exact COST| exact EH2
        | exact CM| exact MI| exact ST| exact MU| exact WM].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_sm_loop : forall (n k : nat) (Jsp J616 jc : list byte) (x584 : word) (m me : word -> option byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    (k + n = 4)%nat -> (1 <= n)%nat ->
    length jc = 12%nat -> length Jsp = 392%nat -> length J616 = 24%nat ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr s0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
    u32arr s0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (usp + 8) (sm_slots3 cx e usp sv w24 w56 (Z.of_nat k)) ->
    u8arr s0segs m (usp + 184) Jsp ->
    rw_cells s0segs m (usp + 576) (C576L x584) ->
    u8arr s0segs m (usp + 616) J616 ->
    u8arr s0segs m (usp + 888) jc ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    cimg_mem S0C m sv -> mem_inv s0segs m -> stk s0segs m lo usp ->
    munch (smB_W3 cx usp) me m -> wmono s0segs me m ->
    (forall m' (Jsp' J616' jc' : list byte) (x584' : word) (ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word),
      length jc' = 12%nat -> length Jsp' = 392%nat -> length J616' = 24%nat ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr s0segs m' (E + 37708) (ovb (it_len (ITK 4)) (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (it_lp (ITK 4)) (jseg J 51640 4128) 1032) ->
      u32arr s0segs m' (E + 45448) (ovw (it_rfreq (ITK 4)) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (it_sel (ITK 4)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (usp + 8) (sm_slots3 cx e usp sv w24 w56 4) ->
      u8arr s0segs m' (usp + 184) Jsp' ->
      rw_cells s0segs m' (usp + 576) (C576L x584') ->
      u8arr s0segs m' (usp + 616) J616' ->
      u8arr s0segs m' (usp + 888) jc' ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      cimg_mem S0C m' sv -> mem_inv s0segs m' -> stk s0segs m' lo usp ->
      munch (smB_W3 cx usp) me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (IR ra' t0' t1' t2' (Z_to_bv 64 (E + 45448 + 1032 * nG)) (Z_to_bv 64 4) (Z_to_bv 64 4) a2' a3' a4' a5' a6' a7'
                            (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (it_nSel (ITK 4))) (Z_to_bv 64 (E + 37708 + 258 * nG)) t3' t4' t5' t6')
                       F (Z_to_bv 64 0x172f0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (IR ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 45448)) s4 s6 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x160e8) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros k Jsp J616 jc x584 m me ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6
           Hk Hn Ljc LJsp LJ616 AR1 LEN LPK RFQ SEL S8 SPL C576 FAV COST EH2 CM MI ST MU WM K.
    eapply (S0_sm_iterk k Jsp J616 jc x584 m me);
      [lia| exact Ljc| exact LJsp| exact LJ616| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact S8| exact SPL| exact C576| exact FAV| exact COST| exact EH2
      | exact CM| exact MI| exact ST| exact MU| exact WM|].
    clear AR1 LEN LPK RFQ SEL S8 SPL C576 FAV COST EH2 CM MI ST MU WM.
    intros m' Jsp' J616' jc' x584' ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ljc' LJsp' LJ616' AR1 LEN LPK RFQ SEL S8 SPL C576 FAV COST EH2 CM MI ST MU WM.
    destruct (Nat.eq_dec (k + 1) 4) as [H4|H4].
    - replace (Z.of_nat k + 1 =? 4)%Z with true by (symmetry; apply Z.eqb_eq; lia). cbv iota.
      replace (S k) with 4%nat in LEN, LPK, RFQ, SEL |- * by lia. replace (Z.of_nat k + 1)%Z with 4%Z in S8 |- * by lia.
      eapply K; eassumption.
    - replace (Z.of_nat k + 1 =? 4)%Z with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
      replace (Z.of_nat k + 1)%Z with (Z.of_nat (S k)) in S8 |- * by lia.
      eapply (IH (S k) Jsp' J616' jc' x584' m' me);
        [lia| lia| exact Ljc'| exact LJsp'| exact LJ616'| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact S8| exact SPL| exact C576| exact FAV| exact COST| exact EH2
        | exact CM| exact MI| exact ST| exact MU| exact WM| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma S0_smB_body : forall (m : word -> option byte) (w584 : word) (J184 J616 J888 : list byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 : word),
    emem cx s0segs g (est_A e) m -> amem cx s0segs (est_A e) m -> cimg_mem S0C m sv ->
    rw_cells s0segs m (usp + 8) (smA_slots3 cx e usp sv w24 w56) ->
    u8arr s0segs m (usp + 184) J184 -> Z.of_nat (length J184) = 392%Z ->
    rw_cells s0segs m (usp + 576) (C576L w584) ->
    u8arr s0segs m (usp + 616) J616 -> Z.of_nat (length J616) = 24%Z ->
    u8arr s0segs m (usp + 888) J888 -> Z.of_nat (length J888) = 12%Z ->
    stk s0segs m lo usp -> mem_inv s0segs m ->
    (forall m' (w584' : word) (J184' J616' J888' : list byte) (ra t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
       emem cx s0segs g (est_B e cost0 fave0 heap0 weight0 parent0) m' -> amem cx s0segs (est_A e) m' -> cimg_mem S0C m' sv ->
       rw_cells s0segs m' (usp + 8) (smB_slots3 cx e usp sv w24 w56) ->
       u8arr s0segs m' (usp + 184) J184' -> Z.of_nat (length J184') = 392%Z ->
       rw_cells s0segs m' (usp + 576) (C576L w584') ->
       u8arr s0segs m' (usp + 616) J616' -> Z.of_nat (length J616') = 24%Z ->
       u8arr s0segs m' (usp + 888) J888' -> Z.of_nat (length J888') = 12%Z ->
       stk s0segs m' lo usp -> mem_inv s0segs m' -> munch (smB_W3 cx usp) m m' -> wmono s0segs m m' ->
       evt s0segs Q (MS (IR ra t0 t1 t2 (Z_to_bv 64 (E + 45448 + 1032 * nG)) (Z_to_bv 64 4) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7
                              (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (it_nSel (smB_it e cost0 fave0 heap0 weight0 parent0))) (Z_to_bv 64 (E + 37708 + 258 * nG)) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x172f0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (IR ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (E + 45448)) s4 s6 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x160e8) fc None m (seg_rom s0segs)).
  Proof.
    intros m w584 J184 J616 J888 ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 t3 t4 t5 t6 EM AM CM SA SPL L184 C576 FAV L616 COST L888 ST MI K.
    cps_destruct EM as (EH1 & INU & UNS & EH2 & MTF & SEL & SELM & LEN & CODE & RFQ & LPK). cps_destruct AM as (AR1 & AR2 & FTB).
    cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
         e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack est_A] in *.
    change (EHEAD2 cx g (est_A e)) with (EHEAD2 cx g e) in EH2.
    change (ip_len (smA_ip e)) with (it_len (ITK 0)) in LEN. change (e_rfreq e) with (it_rfreq (ITK 0)) in RFQ.
    change (e_len_pack e) with (it_lp (ITK 0)) in LPK. change (e_selector e) with (it_sel (ITK 0)) in SEL.
    rewrite smA_slots3_eq in SA. change 0%Z with (Z.of_nat 0) in SA.
    eapply (S0_sm_loop 4 0 J184 J616 J888 w584 m m);
      [reflexivity| lia| lia| lia| lia| exact AR1| exact LEN| exact LPK| exact RFQ| exact SEL| exact SA| exact SPL| exact C576| exact FAV| exact COST| exact EH2
      | exact CM| exact MI| exact ST| apply munch_refl| apply wmono_refl|].
    clear AR1 LEN LPK RFQ SEL SA SPL C576 FAV COST EH2 CM MI ST.
    intros m' Jsp' J616' jc' x584' ra' t0' t1' t2' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ljc' LJsp' LJ616' AR1 LEN LPK RFQ SEL S8 SPL C576 FAV COST EH2 CM MI ST MU WM.
    pose proof (smB_it_eq e cost0 fave0 heap0 weight0 parent0) as EIT.
    rewrite EIT in K.
    (* [comment removed for export] *)
    pose proof CX as CXL. bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in CXL. cbv zeta in CXL.
    cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & XF0 & XF1 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LJ & _).
    pose proof SEP as SP. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SP. cbv zeta in SP.
    cps_destruct SP as (AEA1 & AEA2 & AEF & _).
    bz_ceil; bz_params; unfold CEIL, HM_FRAME in CLO, STK. unfold FTAB_WORDS in AR2, FTB.
    pose proof (jseg_length J 128 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ1.
    pose proof (jseg_length J 384 256 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ2.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm.
    pose proof (jseg_length J 19706 18002 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ5.
    pose proof (jseg_length J 39256 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ7.
    unfold EHEAD1 in EH1. unfold smB_W3, HM_FRAME in MU.
    transport_after_call s0segs m m' MU WM.
    eapply (K m' x584' Jsp' J616' jc');
      [ unfold emem, est_B; rewrite EIT;
        cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos e_nInUse
             e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf e_len e_code e_rfreq e_len_pack];
        split; [unfold EHEAD1; exact EH1|]; split; [exact INU|]; split; [exact UNS|]; split; [exact EH2|]; split; [exact MTF|];
        split; [exact SEL|]; split; [exact SELM|]; split; [exact LEN|]; split; [exact CODE|]; split; [exact RFQ| exact LPK]
      | split; [exact AR1|]; split; [exact AR2| exact FTB]
      | exact CM
      | rewrite smB_slots3_eq; exact S8
      | exact SPL | lia | exact C576 | exact FAV | lia | exact COST | lia | exact ST | exact MI | exact MU | exact WM ].
  Qed.
End GZ.

Theorem S0_smB : S0_smB_spec smB_facts.
Proof.
  unfold S0_smB_spec. intros until fc. cbv zeta. intros GM W56 EM AM CM SA SPL L184 C576 FAV L616 COST L888 ST STK CLO AL MI CX SEP IMG SPB SF K.
  eapply S0_smB_body; eassumption.
Qed.

End ACeilS1.
