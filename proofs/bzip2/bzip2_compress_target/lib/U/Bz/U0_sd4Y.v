(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd BzCLemmasSd2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 BzWalkArith2 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac U.Bz.BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac U.Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac U.Bz.BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit U0_sd4P BzCFactsSd U0_sd4C U0_sd4Z.
Open Scope Z_scope.

Lemma sd4_wr_at_munch : forall segs W (m m' : word -> option byte) A n, wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
  intros segs W m m' A n (Ha & Hn & H) MU D. split; [lia|]. split; [lia|]. intros i Hi.
  specialize (H i Hi). unfold wview in *. rewrite (MU (wa (A + i))); [exact H|].
  eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
Qed.
Lemma sd4_u8arr_munch : forall segs W (m m' : word -> option byte) A bs, u8arr segs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof. intros segs W m m' A bs [Hb Hw] MU D. split; [eapply bytes_at_transport; eauto| eapply sd4_wr_at_munch; eauto]. Qed.
Lemma sd4_u32arr_munch : forall segs W (m m' : word -> option byte) A ws, u32arr segs m A ws -> munch W m m' -> disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr segs m' A ws.
Proof.
  intros segs W m m' A ws [Hb Hw] MU D. split; [| eapply sd4_wr_at_munch; eauto].
  eapply bytes_at_transport; eauto. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia. exact D.
Qed.
Lemma sd4_rw_cells_munch : forall segs W (m m' : word -> option byte) A cs, rw_cells segs m A cs -> munch W m m' -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells segs m' A cs.
Proof.
  intros segs W m m' A cs [[Hwf Hb] Hw] MU D. split; [split; [exact Hwf|]| eapply sd4_wr_at_munch; eauto].
  eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact D.
Qed.

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Lemma sd4_vw_intro : forall (cx : cctx) (e : est) (P : Z) (m0 : word -> option byte),
  cctx_ok cx -> cctx_sep cx -> CEIL <= P -> P + 1200 <= 18446744073709551616 ->
  sd_ro cx e m0 -> sd_vw cx e P m0.
Proof.
  intros cx e P m0 CX SEP CEP PHI RO m MU.
  pose proof CX as CXL. bz_ceil; bz_params. unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in CXL. cbv zeta in CXL.
  cps_destruct CXL as (XE0 & XE1 & XA10 & XA11 & XA20 & XA21 & _).
  pose proof SEP as SP. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SP. cbv zeta in SP.
  cps_destruct SP as (AEA1 & AEA2 & _ & _ & _ & AA12 & _).
  unfold CEIL in CEP. unfold sdWP in MU.
  destruct RO as (AR1 & INU & SLM & SEL & LEN & COD & _).
  unfold sd_ro. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ I)))))).
  - eapply sd4_u8arr_munch; [exact AR1| exact MU|]. rewrite zb8_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply sd4_u8arr_munch; [exact INU| exact MU|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply sd4_u8arr_munch; [exact SLM| exact MU|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply sd4_u8arr_munch; [exact SEL| exact MU|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply sd4_u8arr_munch; [exact LEN| exact MU|]. rewrite ovb_length by lia. cbn [disjoint_from]. repeat split; lia.
  - eapply sd4_u32arr_munch; [exact COD| exact MU|]. rewrite ovw_length by lia. cbn [disjoint_from]. repeat split; lia.
Qed.

End ACeilS1.

Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDY.
  Variables (cx : cctx) (g : eg) (e0 : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable P : Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e0).
  Notation A := (sm_alpha e0). Notation nG := (smA_ng e0).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1200 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variable in160 : zarr.
  Hypothesis OK0 : bw_ok (e_bw e0).
  Notation cP := (Z_to_bv 64 P). Notation cE := (Z_to_bv 64 E).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation WC := [(E + 19706, E + 37708); (E + 39256, E + 45448); (P + 888, P + 1040); (P + 1044, P + 1060); (P - 16, P)]%Z.
  Ltac openCX := openCX_d CX SEP CEP.
  Ltac sub_app :=
    unfold sub_fp, sdWP; let x := fresh "x" in let Ho := fresh "Ho" in intros x Ho; cbn [app outside] in Ho |- *;
    repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end; repeat split; first [ exact I | assumption ].

  Lemma U0_sd4_segC : forall (c0 f0 p0 h0 w0 q0 : zarr) (m : word -> option byte) (H : sdw) (i16 : list byte) (lo : Z)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    let eC := est_C e0 c0 f0 p0 h0 w0 q0 in
    let it := smB_it e0 c0 f0 h0 w0 q0 in let nSel := smB_nsel e0 c0 f0 h0 w0 q0 in
    sd_facts eC nG nSel ->
    u8arr s0segs m (E + 1704) (ovb (it_sel it) (jseg J 1704 18002) 18002) ->
    u8arr s0segs m (E + 19706) (ovb (e_selectorMtf e0) (jseg J 19706 18002) 18002) ->
    u8arr s0segs m (E + 37708) (ovb (it_len it) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 39256) (ovw (e_code e0) (jseg J 39256 6192) 1548) ->
    rw_cells s0segs m (P + 888) (sd_hc H) ->
    h928 H = Z_to_bv 64 nG -> h960 H = Z_to_bv 64 (E + 37708) -> h968 H = Z_to_bv 64 A ->
    h976 H = Z_to_bv 64 nSel -> h984 H = Z_to_bv 64 A ->
    frdW s0segs WC m (P + 816) [C8 (Z_to_bv 64 (E + 1704))] -> frdW s0segs WC m (P + 824) [C8 (NOT (E + 1704))] ->
    u8arr s0segs m (P + 1044) i16 -> Z.of_nat (length i16) = 16%Z ->
    stk s0segs m lo P -> (lo + 16 <= P)%Z -> (CEIL <= lo)%Z -> mem_inv s0segs m ->
    rw_cells s0segs m E (EHEAD1 cx g e0) -> rw_cells s0segs m (E + 640) (EHEAD2 cx g e0) ->
    u8arr s0segs m A2 (zb8 (zbl (e_arr2 e0) (e_nblock e0) (e_bw e0)) ARR2_SIZE) ->
    u8arr s0segs m A1 (zb8 (e_arr1 e0) ARR1_SIZE) ->
    u8arr s0segs m (E + 128) (ovb (e_inUse e0) (jseg J 128 256) 256) ->
    h904 H = Z_to_bv 64 (flag6 nG) -> h1008 H = Z_to_bv 64 1 -> h1016 H = Z_to_bv 64 1 -> h1032 H = Z_to_bv 64 A1 ->
    (bw_numZ (BE eC nG A nSel in160) <= LIM)%Z ->
    (forall (m0' m' : word -> option byte) (H' : sdw) (i16' : list byte) (s2 s4 s5 s6 s7 s8 s10 s11 t4 t5 t6 : word),
       MA3 cx g eC nG P m0' H' i16' (BE eC nG A nSel in160) m' -> sd_ro cx eC m' -> stk s0segs m' lo P ->
       munch (WC ++ sdWP cx P) m m' -> wmono s0segs m m' ->
       h904 H' = Z_to_bv 64 (flag6 nG) -> h928 H' = Z_to_bv 64 nG -> h944 H' = Z_to_bv 64 nSel -> h960 H' = Z_to_bv 64 (E + 37708) ->
       h992 H' = NOT (E + 39256) -> h1000 H' = Z_to_bv 64 (E + 39256) -> h1008 H' = Z_to_bv 64 1 -> h1016 H' = Z_to_bv 64 1 ->
       h1032 H' = Z_to_bv 64 A1 -> Z.of_nat (length i16') = 16%Z -> bw_ok (BE eC nG A nSel in160) ->
       evt s0segs Q (MS (mkR (NOT (E + 39256)) cP gp tp (Z_to_bv 64 257) (Z_to_bv 64 A) (Z_to_bv 64 2) cE (Z_to_bv 64 3)
                             (Z_to_bv 64 (bw_numZ (BD eC nG nSel in160))) (Z_to_bv 64 nG) (Z_to_bv 64 6) (Z_to_bv 64 258) (Z_to_bv 64 8)
                             (Z_to_bv 64 7) (Z_to_bv 64 32) (Z_to_bv 64 31) s2 (Z_to_bv 64 (bw_numZ (BE eC nG A nSel in160)))
                             s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 (Z_to_bv 64 nG) t4 t5 t6)
                        F (Z_to_bv 64 115096) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 111668) fc None m (seg_rom s0segs)).
  Proof using All.
    intros c0 f0 p0 h0 w0 q0 m H i16 lo ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 eC it nSel.
    intros SDF SEL SELM LEN CODE HC HS28 HS60 HS68 HS76 HS84 V816 V824 I16 L16 ST STK CLO MI EH1 EH2 AR2 AR1 INU HS04 HS08 HS16 HS32 NLE K.
    pose proof SDF as SF. unfold sd_facts, eC in SF. cbv zeta in SF.
    cbn [e_nInUse e_nMTF e_arr1 e_inUse e_selectorMtf e_selector e_len e_code est_C] in SF.
    cps_destruct SF as (FA & FG & FS & FM & F35 & FZB & FMV & FIU & FSM & FSEL & FLEN & FCODE & FCNT).
    eapply (U0_smC_body cx g e0 Q gp tp F fc P CX SEP CEP PHI FA FG c0 f0 p0 h0 w0 q0 m H i16 lo
              ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6
              SDF SEL SELM LEN CODE HC HS28 HS60 HS68 HS76 HS84 V816 V824 I16 L16 ST STK CLO MI EH1 EH2 AR2 AR1 INU).
    intros mC i16C u0 u1 u2 us1 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 us2 us3 us4 us5 us6 us7 us8 us10 us11 u3 u4 u5 u6
           MEMC G28 G44 G76 G60 G68 LC AR1C INUC SLMC SELC LENC CODC STC MIC MUC WMC.
    pose proof (sd4_vw_intro cx eC P mC CX SEP CEP PHI (conj AR1C (conj INUC (conj SLMC (conj SELC (conj LENC (conj CODC I))))))) as VW.
    lazymatch type of MEMC with MA3 _ _ _ _ _ _ ?HH _ _ _ =>
      eapply (U0_sd4_seg cx g eC Q gp tp F fc P CX SEP Gmtf Gbs Gzb Hnb CEP PHI LIM HLIM mC nG VW A nSel FA FG FS FIU FSM FLEN in160 OK0 NLE HH i16C);
        [exact G28| exact G44| exact G76| exact G60| exact G68| exact LC| exact MEMC|] end.
    intros m' i16' s2' s4' s5' s6' s8' s10' t4' t5' t6' MEM' L' OKBE.
    pose proof MEM' as MM. cps_destruct MM as (_ & _ & _ & _ & _ & _ & MU' & WM').
    refine (K mC m' _ i16' s2' s4' s5' s6' us7 s8' s10' us11 t4' t5' t6' MEM' (VW m' MU') _ _ (wmono_trans s0segs m mC m' WMC WM')
              HS04 G28 G44 G60 eq_refl eq_refl HS08 HS16 HS32 L' OKBE).
    - eapply (stk_transport_disjoint s0segs (sdWP cx P) mC m' lo P STC MU' WM').
      openCX. unfold CEIL in CLO. unfold sdWP. cbn [disjoint_from]. repeat split; lia.
    - apply (munch_trans _ m mC m').
      + apply (munch_weaken WC _ m mC); [sub_app| exact MUC].
      + apply (munch_weaken (sdWP cx P) _ mC m'); [sub_app| exact MU'].
  Qed.
End SDY.
End ACeilS2.
