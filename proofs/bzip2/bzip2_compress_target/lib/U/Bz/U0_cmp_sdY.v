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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzWalkArith2 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCLemmasSd BzCLemmasSd2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit U0_cmp_sdBV.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_cmp_sdB7 U0_cmp_smV BzCFactsSd.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCSmF1.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
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

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Definition SLOW_spec : Prop :=
  forall (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop)
         (sp gp tp ra s3 s7 s9 : word) (F : bvmap 5 word) (fc : bv 32),
  cctx_ok cx -> cctx_sep cx ->
  g_mtf g = true -> g_bs g = true -> g_zbits g = Z_to_bv 64 (c_A2 cx + e_nblock e) ->
  (0 <= e_nblock e)%Z ->
  (CEIL <= bv_unsigned sp)%Z -> (bv_unsigned sp + 1200 <= 18446744073709551616)%Z ->
  forall LIM : Z, (e_nblock e + LIM <= ARR2_SIZE)%Z ->
  forall m0 : word -> option byte,
  forall A : Z, (3 <= A <= 258)%Z ->
  forall nG : Z, (2 <= nG <= 6)%Z ->
  forall nSel : Z, (1 <= nSel <= 18002)%Z ->
  (forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef (e_len e) (258 * t + v) = true /\ (1 <= zget (e_len e) (258 * t + v) <= 17)%Z) ->
  (forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef (e_code e) (258 * t + v) = true /\ (0 <= zget (e_code e) (258 * t + v) < 4294967296)%Z) ->
  (forall i, (0 <= i < nSel)%Z -> zdef (e_selector e) i = true /\ (0 <= zget (e_selector e) i < nG)%Z) ->
  zbok (e_arr1 e) ->
  forall sc gs ge : Z,
  (0 <= sc < nSel)%Z -> (0 <= gs <= ge)%Z -> (ge <= gs + 49)%Z -> (2 * (gs + 50) <= ARR1_SIZE)%Z ->
  (forall i, (gs <= i <= ge)%Z -> (0 <= mtfv_at (e_arr1 e) i < A)%Z) ->
  u8arr s0segs m0 (c_E cx + 1704) (ovb (e_selector e) (jseg (c_J cx) 1704 18002) 18002) ->
  rw_cells s0segs m0 (bv_unsigned sp + 960) [C8 (Z_to_bv 64 (c_E cx + 37708))] ->
  rw_cells s0segs m0 (bv_unsigned sp + 1008) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 2147483647)] ->
  ra = Z_to_bv 64 (18446744073709551615 - (c_E cx + 39256)) ->
  s9 = Z_to_bv 64 (18446744073709551615 - (c_E cx + 37708)) ->
  forall (n : nat) (i : Z) (b : bw) (m : word -> option byte) (a1 a2 a3 a4 a5 a6 a7 t0 t1 t2 t3 : word),
    (1 <= n)%nat -> (i + Z.of_nat n = ge + 1)%Z -> (gs <= i)%Z -> bw_ok b ->
    (bw_numZ (sm_put_syms n b (e_len e) (e_code e) (e_arr1 e) (zget (e_selector e) sc) i) <= LIM)%Z ->
    MUd cx g e (bv_unsigned sp) m0 b m ->
    (forall m' (s1' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' : word),
       MUd cx g e (bv_unsigned sp) m0 (sm_put_syms n b (e_len e) (e_code e) (e_arr1 e) (zget (e_selector e) sc) i) m' ->
       bw_ok (sm_put_syms n b (e_len e) (e_code e) (e_arr1 e) (zget (e_selector e) sc) i) ->
       evt s0segs Q (MS (mkR ra sp gp tp t0' t1' t2' (Z_to_bv 64 (c_E cx)) s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3 (Z_to_bv 64 sc)
         (Z_to_bv 64 7) (Z_to_bv 64 32) s7 (Z_to_bv 64 (ge + 1)) s9 (Z_to_bv 64 50) (Z_to_bv 64 5) t3'
         (Z_to_bv 64 (c_E cx + 39256)) (Z_to_bv 64 258) (Z_to_bv 64 1032)) F (Z_to_bv 64 0x20238) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 (c_E cx)) (Z_to_bv 64 (c_E cx + 1704 + sc)) (Z_to_bv 64 (ge + 1)) a1 a2 a3 a4
      a5 a6 a7 (Z_to_bv 64 i) s3 (Z_to_bv 64 sc) (Z_to_bv 64 7) (Z_to_bv 64 32) s7 (Z_to_bv 64 (ge + 1)) s9 (Z_to_bv 64 50)
      (Z_to_bv 64 5) t3 (Z_to_bv 64 (c_E cx + 39256)) (Z_to_bv 64 258) (Z_to_bv 64 1032)) F (Z_to_bv 64 0x200dc) fc None m
      (seg_rom s0segs)).

Definition ROC (cx : cctx) (e : est) (usp nG nSel : Z) (m : word -> option byte) : Prop :=
  u8arr s0segs m (c_E cx + 1704) (ovb (e_selector e) (jseg (c_J cx) 1704 18002) 18002) /\
  rw_cells s0segs m (usp + 816) [C8 (Z_to_bv 64 (c_E cx + 1704)); C8 (Z_to_bv 64 (18446744073709551615 - (c_E cx + 1704)))] /\
  rw_cells s0segs m (usp + 904) [C8 (Z_to_bv 64 (flag6 nG))] /\
  rw_cells s0segs m (usp + 928) [C8 (Z_to_bv 64 nG)] /\
  rw_cells s0segs m (usp + 944) [C8 (Z_to_bv 64 nSel)] /\
  rw_cells s0segs m (usp + 960) [C8 (Z_to_bv 64 (c_E cx + 37708))] /\
  rw_cells s0segs m (usp + 976) [C8 (Z_to_bv 64 3006); C8 (Z_to_bv 64 18002)] /\
  rw_cells s0segs m (usp + 992)
    [C8 (Z_to_bv 64 (18446744073709551615 - (c_E cx + 39256))); C8 (Z_to_bv 64 (c_E cx + 39256)); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1)] /\
  rw_cells s0segs m (usp + 1024) [C8 (Z_to_bv 64 2147483647)].

Lemma rwc_drop : forall segs (m : word -> option byte) A pre post B,
  rw_cells segs m A (pre ++ post) -> B = (A + Z.of_nat (cells_size pre))%Z -> rw_cells segs m B post.
Proof. intros segs m A pre post B H ->. exact (proj2 (proj1 (rw_cells_app_iff_c segs m A pre post) H)). Qed.

Lemma rwc_glue : forall segs (m : word -> option byte) A l1 l2 B,
  rw_cells segs m A l1 -> rw_cells segs m B l2 -> B = (A + Z.of_nat (cells_size l1))%Z -> rw_cells segs m A (l1 ++ l2).
Proof. intros segs m A l1 l2 B H1 H2 ->. exact (proj2 (rw_cells_app_iff_c segs m A l1 l2) (conj H1 H2)). Qed.

Lemma MUe_MUd : forall cx g e usp (m0 : word -> option byte) b m, MUe cx g e usp m0 b m -> MUd cx g e usp m b m.
Proof.
  intros cx g e usp m0 b m H. unfold MUe in H. unfold MUd.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & _ & _).
  exact (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj (munch_refl _ _) (wmono_refl _ _)))))))))).
Qed.

Lemma MUd_MUe : forall cx g e usp (m0 m : word -> option byte) b b' m',
  MUe cx g e usp m0 b m -> MUd cx g e usp m b' m' -> MUe cx g e usp m0 b' m'.
Proof.
  intros cx g e usp m0 m b b' m' H0 H. unfold MUe in H0 |- *. unfold MUd in H.
  destruct H0 as (_ & _ & _ & _ & _ & _ & _ & _ & MU0 & WM0).
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & MU & WM).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8
    (conj (munch_trans _ _ _ _ MU0 (munch_weaken _ _ _ _ _ MU)) (wmono_trans _ _ _ _ WM0 WM)))))))))).
  unfold sub_fp, sdWe, sdWd. intros x Ho. cbn [app outside] in Ho |- *. tauto.
Qed.

Lemma MUd_MUe0 : forall cx g e usp (m0 : word -> option byte) b m, MUd cx g e usp m0 b m -> MUe cx g e usp m0 b m.
Proof.
  intros cx g e usp m0 b m H. unfold MUd in H. unfold MUe.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & MU & WM).
  refine (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj (munch_weaken _ _ _ _ _ MU) WM))))))))).
  unfold sub_fp, sdWe, sdWd. intros x Ho. cbn [app outside] in Ho |- *. tauto.
Qed.

Ltac lit_st8 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?z)) _) =>
      change (Z_to_le_bytes 8 z) with (Z_to_le_bytes 8 (bv_unsigned (Z_to_bv 64 z)));
      rewrite (Lib.Step.store_bytes_8' (Z_to_bv 64 z));
      Lib.Step.mem_after_store
  end.

Ltac openMUe Gmtf Gbs Gzb H :=
  let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let MU := ident:(MU) in
  cps_destruct H as (?EH1 & ?EH2 & ?AR2 & ?AR1 & ?LEN & ?COD & ?STK & ?MI & ?MU & ?WM);
  unfold sdWe, sdWd in MU; cbn [app] in MU;
  unfold EHEAD1, EHEAD2 in EH1, EH2; cbn_est_in EH1; cbn_est_in EH2;
  rewrite Gbs, Gmtf in EH2; rewrite Gzb, Gmtf in EH1.

Ltac closeMUe Gmtf Gbs Gzb :=
  split; [|split; [| repeat (split; [eassumption|]); eassumption]];
  [ unfold EHEAD1; cbn_est; rewrite Gzb, Gmtf; eassumption
  | unfold EHEAD2; cbn_est; rewrite Gbs, Gmtf; eassumption ].

Section EMIT.
Hypothesis HSLOW : SLOW_spec.

Section SDY.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (sp gp tp ra s3 s7 s9 : word) (F : bvmap 5 word) (fc : bv 32).
  Notation usp := (bv_unsigned sp). Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis USP1 : (CEIL <= usp)%Z. Hypothesis USP2 : (usp + 1200 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variable m0 : word -> option byte.
  Ltac openCX := openCX3 CX SEP USP1.
  Ltac openME H := openMUe Gmtf Gbs Gzb H.
  Ltac closeME := closeMUe Gmtf Gbs Gzb.
  Variable A : Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Variable nG : Z. Hypothesis HG : (2 <= nG <= 6)%Z.
  Variable nSel : Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.
  Variable NM : Z.
  Hypothesis HNM : (1 <= NM)%Z. Hypothesis HNMe : e_nMTF e = NM. Hypothesis HNMA : (2 * (NM + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFVN : forall i, (0 <= i < NM)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Hypothesis HRA : ra = Z_to_bv 64 (18446744073709551615 - (E + 39256)).
  Hypothesis HS9 : s9 = Z_to_bv 64 (18446744073709551615 - (E + 37708)).
  Notation MUE b m := (MUe cx g e usp m0 b m).
  Notation RC m := (ROC cx e usp nG nSel m).
  Notation RG t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 sc s8 t3 :=
    (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 sc) (Z_to_bv 64 7) (Z_to_bv 64 32) s7 s8 s9
         (Z_to_bv 64 50) (Z_to_bv 64 5) t3 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 258) (Z_to_bv 64 1032)).

  Lemma ROC_tr : forall m m', RC m -> munch (sdWd cx) m m' -> wmono s0segs m m' -> RC m'.
  Proof using CX SEP USP1 USP2.
    intros m m' R MU WM. openCX. unfold sdWd in MU.
    unfold ROC in R. cps_destruct R as (SEL & V816 & V904 & V928 & V944 & V960 & V976 & V992 & V1024).
    transport_after_call s0segs m m' MU WM.
    exact (conj SEL (conj V816 (conj V904 (conj V928 (conj V944 (conj V960 (conj V976 (conj V992 V1024)))))))).
  Qed.

  Lemma U0_group_tail : forall (sc s8v : Z) (b : bw) (m : word -> option byte) (t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 : word),
    (0 <= sc < nSel)%Z -> (0 <= s8v <= NM)%Z -> MUE b m ->
    ((s8v < NM)%Z -> evt s0segs Q (MS (RG t0 t1 t2 s1 (Z_to_bv 64 NM) a1 a2 a3 a4 a5 a6 a7 s2 (sc + 1) (Z_to_bv 64 s8v) t3)
                                      F (Z_to_bv 64 0x1c1fc) fc None m (seg_rom s0segs))) ->
    ((NM <= s8v)%Z -> evt s0segs Q (MS (RG t0 t1 t2 s1 (Z_to_bv 64 NM) a1 a2 a3 a4 a5 a6 a7 s2 (sc + 1) (Z_to_bv 64 s8v) t3)
                                       F (Z_to_bv 64 0x20274) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 sc (Z_to_bv 64 s8v) t3) F (Z_to_bv 64 0x20238) fc None m (seg_rom s0segs)).
  Proof using All.
    intros sc s8v b m t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 t3 Hsc H8 MEM KL KX.
    openCX. openME MEM. rewrite HNMe in EH2.
    ustep. ustep. ustep. if_cases Kc; zify_cond_z Kc.
    - enter_with (KX ltac:(lia)); st_eq.
    - ustep. enter_with (KL ltac:(lia)); st_eq.
  Qed.

  Lemma U0_group_sel : forall (sc gs : Z) (b : bw) (m : word -> option byte) (t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 : word),
    (0 <= sc < nSel)%Z -> (0 <= gs < NM)%Z ->
    let ge := GE NM gs in
    let bf := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MUE b m -> RC m ->
    (forall m' (t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' : word), MUE bf m' -> RC m' -> bw_ok bf ->
        evt s0segs Q (MS (RG t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' sc (Z_to_bv 64 (ge + 1)) t3')
                          F (Z_to_bv 64 0x20238) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 gs) sc (Z_to_bv 64 (ge + 1)) t3)
                      F (Z_to_bv 64 0x1c214) fc None m (seg_rom s0segs)).
  Proof using All.
    intros sc gs b m t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 t3 Hsc Hgs. cbv zeta. intros OK NL MEM RCm K.
    cps_pose (GE_facts NM gs Hgs) as (G1 & G2 & G3).
    set (ge := GE NM gs) in *.
    pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MUe_MUd _ _ _ _ _ _ _ MEM) as MD0.
    assert (KF : forall m' (t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' : word),
        MUd cx g e usp m (sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs) m' ->
        bw_ok (sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs) ->
        evt s0segs Q (MS (RG t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' sc (Z_to_bv 64 (ge + 1)) t3')
                          F (Z_to_bv 64 0x20238) fc None m' (seg_rom s0segs))).
    { intros m' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' MD' OK'.
      pose proof MD' as MM. unfold MUd in MM. destruct MM as (_ & _ & _ & _ & _ & _ & _ & _ & MU' & WM').
      exact (K m' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' (MUd_MUe _ _ _ _ _ _ _ _ _ MEM MD') (ROC_tr m m' RCm MU' WM') OK'). }
    clear K MEM.
    openCX.
    unfold ROC in RCm. cps_destruct RCm as (SEL & V816 & V904 & V928 & V944 & V960 & V976 & V992 & V1024).
    pose proof (rwc_drop s0segs m (usp + 992)
      [C8 (Z_to_bv 64 (18446744073709551615 - (E + 39256))); C8 (Z_to_bv 64 (E + 39256)); C8 (Z_to_bv 64 1)] [C8 (Z_to_bv 64 1)]
      (usp + 1016) V992 ltac:(cbn; lia)) as F1016.
    pose proof (rwc_drop s0segs m (usp + 992)
      [C8 (Z_to_bv 64 (18446744073709551615 - (E + 39256))); C8 (Z_to_bv 64 (E + 39256))] [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 1)]
      (usp + 1008) V992 ltac:(cbn; lia)) as V1008.
    pose proof (rwc_glue s0segs m (usp + 1008) _ _ (usp + 1024) V1008 V1024 ltac:(cbn; lia)) as F1008. cbn [app] in F1008. clear V1008.
    pose proof (ovb_read1 s0segs m (E + 1704) SELA (jseg J 1704 18002) 18002 sc _ SEL ltac:(lia) SD eq_refl) as RD0.
    urun_to 0x1c234.
    wstep. clear RD0. cbv beta. rewrite (unsigned_lit8 (zget SELA sc)) by lia.
    urun_to 0x1c23c. wstep; if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    assert (SLOWP : forall (y0 y1 : word),
      evt s0segs Q (MS (RG t0 t1 t2 (Z_to_bv 64 (E + 1704 + sc)) y0 y1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 gs) sc (Z_to_bv 64 (ge + 1)) t3)
                        F (Z_to_bv 64 0x200cc) fc None m (seg_rom s0segs))).
    { intros y0 y1.
      wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; lia|]. wstep. wstep; if_cases K2; zify_cond_z K2; [exfalso; lia|].
      enter_with (HSLOW cx g e Q sp gp tp ra s3 s7 s9 F fc CX SEP Gmtf Gbs Gzb Hnb USP1 USP2 LIM HLIM m A HA nG HG nSel HNS LENF CODF SELF ZB1
                    sc gs ge Hsc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros i Hi; apply MTFVN; lia) SEL V960 F1008 HRA HS9
                    (Z.to_nat (ge - gs + 1)) gs b m _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| exact OK| exact NL| exact MD0|].
      intros m' s1' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' MD' OK'.
      enter_with (KF m' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' MD' OK'); st_eq. }
    urun_to 0x1c25c. wstep; if_cases K6.
    2:{ wstep. enter_with (SLOWP _ _); st_eq. }
    urun_to 0x1c288. wstep; if_cases K50; zify_cond_z K50.
    2:{ wstep. enter_with (SLOWP _ _); st_eq. }
    replace (Z.to_nat (ge - gs + 1)) with 50%nat in NL, KF by lia.
    enter_with (fast50 cx g e Q sp gp tp ra s3 s7 s9 F fc CX SEP Gmtf Gbs Gzb Hnb USP1 USP2 LIM HLIM m A HA nG HG nSel HNS LENF CODF SELF ZB1
                  sc gs Hsc ltac:(lia) ltac:(lia) ltac:(intros i Hi; apply MTFVN; lia) HRA HS9 b m _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact OK| exact NL| exact MD0| exact SEL| exact V960| exact F1016|].
    intros m' s1' s2' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' MD' OK'.
    enter_with (KF m' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' MD' OK'); st_eq.
  Qed.

  Lemma U0_group : forall (sc gs : Z) (b : bw) (m : word -> option byte) (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 t3 : word),
    (0 <= sc < nSel)%Z -> (0 <= gs < NM)%Z ->
    let ge := GE NM gs in
    let bf := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MUE b m -> RC m ->
    (forall m' (t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' : word), MUE bf m' -> RC m' -> bw_ok bf ->
        evt s0segs Q (MS (RG t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' sc (Z_to_bv 64 (ge + 1)) t3')
                          F (Z_to_bv 64 0x20238) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG t0 t1 t2 s1 (Z_to_bv 64 NM) a1 a2 a3 a4 a5 a6 a7 s2 sc (Z_to_bv 64 gs) t3)
                      F (Z_to_bv 64 0x1c1fc) fc None m (seg_rom s0segs)).
  Proof using All.
    intros sc gs b m t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 t3 Hsc Hgs. cbv zeta. intros OK NL MEM RCm K.
    cps_pose (GE_facts NM gs Hgs) as (G1 & G2 & G3).
    openCX.
    urun_to 0x1c20c. wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (U0_group_sel sc gs b m _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact Hsc| exact Hgs| exact OK| exact NL| exact MEM| exact RCm| exact K].
    - wstep. enter_with (U0_group_sel sc gs b m _ _ _ _ _ _ _ _ _ _ _ _ _);
        [st_eq| exact Hsc| exact Hgs| exact OK| exact NL| exact MEM| exact RCm| exact K].
  Qed.

  Lemma U0_data_loop : forall (f : nat) (gs sc : Z) (b : bw) (m : word -> option byte) (t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 t3 : word),
    (0 <= sc)%Z -> (0 <= gs < NM)%Z -> (NM - gs <= Z.of_nat f)%Z ->
    let r := sm_put_data f b LENA CODA ARR1 SELA NM gs sc in
    (snd r <= nSel)%Z -> bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MUE b m -> RC m ->
    (forall m' (t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s8' t3' : word),
        MUE (fst r) m' -> RC m' -> bw_ok (fst r) ->
        evt s0segs Q (MS (RG t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' (snd r) s8' t3')
                          F (Z_to_bv 64 0x20274) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG t0 t1 t2 s1 (Z_to_bv 64 NM) a1 a2 a3 a4 a5 a6 a7 s2 sc (Z_to_bv 64 gs) t3)
                      F (Z_to_bv 64 0x1c1fc) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; [lia|].
    intros gs sc b m t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 t3 Hsc Hgs Hf. cbv zeta. intros SCN OK NL MEM RCm K.
    pose proof (put_data_snd_step f b LENA CODA ARR1 SELA NM gs sc ltac:(lia)) as SC1.
    rewrite put_data_S in SCN, NL, K, SC1. fold BZ_G_SIZE in SCN, NL, K, SC1.
    destruct (Z.leb_spec NM gs) as [Xg|Xg]; [lia|]. cbv zeta in SCN, NL, K, SC1.
    change (if NM <=? gs + BZ_G_SIZE - 1 then NM - 1 else gs + BZ_G_SIZE - 1)%Z with (GE NM gs) in SCN, NL, K, SC1.
    cps_pose (GE_facts NM gs ltac:(lia)) as (G1 & G2 & G3). set (ge := GE NM gs) in *.
    set (b1 := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs) in *.
    pose proof (put_data_NZM f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (put_data_snd_ge f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1)) as SG.
    eapply (U0_group sc gs b m); [lia| lia| exact OK| subst ge b1; lia| exact MEM| exact RCm|].
    fold ge. fold b1. clear MEM RCm. intros m1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' t3' MEM RCm OK1.
    eapply (U0_group_tail sc (ge + 1) b1 m1); [lia| lia| exact MEM| |].
    - intros Hlt.
      eapply (IH (ge + 1)%Z (sc + 1)%Z b1 m1); [lia| lia| lia| exact SCN| exact OK1| exact NL| exact MEM| exact RCm| exact K].
    - intros Hge.
      assert (ER : sm_put_data f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1) = (b1, (sc + 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_data_S. destruct (Z.leb_spec NM (ge + 1)); [reflexivity| lia]. }
      rewrite ER in K. cbn [fst snd] in K.
      eapply K; [exact MEM| exact RCm| exact OK1].
  Qed.

  Lemma U0_exit : forall (b : bw) (m : word -> option byte) (t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 t3 : word),
    MUE b m -> RC m ->
    (forall (ra' t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6' : word),
       evt s0segs Q (MS (mkR ra' sp gp tp t0' t1' t2' s0' s1' a0' a1' a2' a3' a4' a5' a6' a7'
                             s2' s3' s4' s5' s6' s7' s8' s9' s10' s11' t3' t4' t5' t6')
                         F (Z_to_bv 64 0x20298) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (RG t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 nSel s8 t3) F (Z_to_bv 64 0x20274) fc None m (seg_rom s0segs)).
  Proof using All.
    intros b m t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s8 t3 MEM RCm K.
    openCX. openME MEM.
    unfold ROC in RCm. cps_destruct RCm as (SEL & V816 & V904 & V928 & V944 & V960 & V976 & V992 & V1024).
    urun_to 0x2027c. wstep; if_cases Kq; zify_cond_z Kq; [| exfalso; lia].
    urun_to 0x20298. eapply K.
  Qed.

End SDY.

Lemma U0_sd_emit : U0_sd_emit_spec.
Proof.
  intros cx g e0 c0 f0 p0 in160 h0 w0 q0 Q gp tp F fc SP m0 m w976 w984 w1024
         t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 E eC nG nSel BE r.
  intros CX SEP Gmtf Gbs Gzb Hnb USP1 USP2 SDF OKB NLIM MEM SEL V816 V904 V928 V944 V960 V992 V976 V1024 K.
  subst E.
  assert (Er : r = sm_put_data (Z.to_nat (e_nMTF eC + 1)) BE (e_len eC) (e_code eC) (e_arr1 eC) (e_selector eC) (e_nMTF eC) 0 0)
    by reflexivity.
  change (e_nblock e0) with (e_nblock eC) in Gzb, Hnb, NLIM.
  clearbody r BE nG nSel eC.
  pose proof SDF as SF. unfold sd_facts in SF. cbv zeta in SF.
  set (A := (e_nInUse eC + 2)%Z) in SF. set (NM := e_nMTF eC) in SF, Er.
  cps_destruct SF as (FA & FG & FS & FM & F35 & FZB & FMV & FIU & FSM & FSEL & FLEN & FCODE & FCNT).
  assert (HNMe : e_nMTF eC = NM) by reflexivity. clearbody A NM.
  change (2^64)%Z with 18446744073709551616%Z in USP2.
  set (sp := Z_to_bv 64 SP) in *.
  assert (SPu : bv_unsigned sp = SP).
  { subst sp. apply unsigned_lit. pose proof USP1 as U. bz_ceil. bz_params. unfold CEIL in U. lia. }
  clearbody sp. subst SP.
  pose proof (U0_data_loop cx g eC Q sp gp tp (Z_to_bv 64 (18446744073709551615 - (c_E cx + 39256))) s3 s7
                (Z_to_bv 64 (18446744073709551615 - (c_E cx + 37708))) F fc CX SEP Gmtf Gbs Gzb Hnb USP1 USP2 (bw_numZ (fst r)) NLIM
                m0 A FA nG FG nSel FS FLEN FCODE FSEL FZB NM FM HNMe F35 FMV eq_refl eq_refl) as DL.
  pose proof (U0_exit cx g eC Q sp gp tp (Z_to_bv 64 (18446744073709551615 - (c_E cx + 39256))) s3 s7
                (Z_to_bv 64 (18446744073709551615 - (c_E cx + 37708))) F fc CX SEP Gmtf Gbs Gzb Hnb USP1 USP2 (bw_numZ (fst r)) NLIM
                m0 A FA nG FG nSel FS FLEN FCODE FSEL FZB NM FM HNMe F35 FMV eq_refl eq_refl) as EX.
  pose proof (MUd_MUe0 _ _ _ _ _ _ _ MEM) as ME. clear MEM.
  openCX3 CX SEP USP1.
  openMUe Gmtf Gbs Gzb ME. rewrite HNMe in EH2.
  urun_to 0x1c1ac. wstep; if_cases Kn; zify_cond_z Kn; [| exfalso; lia].
  urun_to 0x1c1e4. wstep. lit_st8.
  urun_to 0x1c1ec. wstep. lit_st8.
  urun_to 0x1c1f4. wstep. lit_st8.
  urun_to 0x1c1fc.
  enter_with (DL (Z.to_nat (NM + 1)) 0 0 BE _ _ _ _ _ _ _ _ _ _ _ _ _ _);
    [st_eq| lia| lia| lia| rewrite FCNT; lia| exact OKB| rewrite <- Er; lia| rewrite <- HNMe in EH2; closeMUe Gmtf Gbs Gzb| |].
  - unfold ROC. refine (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ (conj _ _)))))))); eassumption.
  - intros m' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s2' s8' t3' MEM' RC' OK'.
    rewrite (FCNT BE). rewrite <- Er in MEM', OK'.
    pose proof RC' as RR. unfold ROC in RR. destruct RR as (_ & _ & _ & _ & _ & _ & W976 & _ & W1024).
    enter_with (EX (fst r) m' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ MEM' RC'); [st_eq|].
    intros. eapply K; [exact MEM'| exact W976| exact W1024| exact OK'].
Qed.

End EMIT.
End ACeilS1.
