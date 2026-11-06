(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCState BzCSortM BzArrD CmpMem CmpCut CmpFsKit0 AsanKit AsanCut.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCQsortM1 BzCQsortM2 BzCSewA BzCSewC BzCSewF.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCLemmasMs BzCLemmasMs2 BzCLemmasMs3 CmpCutMS CmpMsKit CmpMsKit2.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas7_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_fsS A0_cmp_msV A0_cmp_msW A0_cmp_msS A0_cmp_bsV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)
Definition f1b : byte := Z_to_bv 8 (bv_unsigned (Z_to_bv 64 (-15))).
(* [comment removed for export] *)

Lemma rw_cells_cutJ : forall segs m A cs k, rw_cells segs m A cs ->
  rw_cells segs m A (firstn k cs) /\ rw_cells segs m (A + Z.of_nat (cells_size (firstn k cs)))%Z (skipn k cs).
Proof. intros segs m A cs k H. rewrite <- (firstn_skipn k cs) in H at 1. exact (proj1 (rw_cells_app_iff_c segs m A _ _) H). Qed.

(* [comment removed for export] *)
Lemma cells_bytes_C1s : forall bs, cells_bytes (map C1 bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity| cbn [map cells_bytes cbytes app]; rewrite IH; reflexivity]. Qed.
Lemma cells_size_C1s : forall bs, cells_size (map C1 bs) = length bs.
Proof. induction bs as [|b bs IH]; [reflexivity| cbn [map cells_size csize length Nat.add]; rewrite IH; reflexivity]. Qed.
Lemma cells_wf_C1s : forall bs, cells_wf (map C1 bs).
Proof. induction bs as [|b bs IH]; [exact I| cbn [map cells_wf cell_wf]; split; [exact I| exact IH]]. Qed.
Lemma rw_cells_CB_C1s : forall segs m A n bs, rw_cells segs m A [CB n bs] -> rw_cells segs m A (map C1 bs) /\ length bs = n.
Proof.
  intros segs m A n bs [[Hwf Hb] Hw]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _].
  cbn [cells_bytes cbytes app] in Hb. rewrite app_nil_r in Hb. cbn [cells_size csize Nat.add] in Hw. rewrite Nat.add_0_r in Hw.
  split; [| exact Hl]. split; [split; [apply cells_wf_C1s| rewrite cells_bytes_C1s; exact Hb]| rewrite cells_size_C1s, Hl; exact Hw].
Qed.

Section A0MS.
  Variable X : msenv. Variable Y : amenv. Variable SHF : Z. Variable Q : machine_state -> Prop.
  Hypothesis XOK : msenv_ok1 X. Hypothesis YOK : amenv_ok X Y. Hypothesis YSF : amenv_shf Y SHF. Hypothesis YOFF : amenv_offsh X Y. Hypothesis YSHX : amenv_shx X Y SHF.
  Notation usp := (bv_unsigned (me_sp X)). Notation P := (am_P Y). Notation FB := (am_FB Y).
  Notation gp := (me_gp X). Notation tp := (me_tp X). Notation F := (me_F X). Notation fc := (me_fc X).
  Notation WP2 := [(FB, FB + 24); (SHF, SHF + 178); (P + 424, P + 432)]%Z.

  Ltac sbf8 := wstep; change (le1 (Z_to_bv 64 (-8))) with [f8b]; mem_after_store.
  Ltac sbf2 := wstep; change (le1 (Z_to_bv 64 (-14))) with [f2b]; mem_after_store.
  Ltac sbf1 := wstep; change (le1 (Z_to_bv 64 (-15))) with [f1b]; mem_after_store.
  Ltac sbx := first [sbf8 | sbf2 | sbf1].
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.

  (* [comment removed for export] *)
  Lemma A0_bs_P2sb : forall (me m : word -> option byte) (bs : list byte)
      (ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m SHF [CB 178 bs] -> mem_inv a0segs m -> munch [(SHF, SHF + 178)]%Z me m -> wmono a0segs me m ->
    (forall m', rw_cells a0segs m' (SHF + 4) (shc3 f8b) -> mem_inv a0segs m' -> munch [(SHF, SHF + 178)]%Z me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (Z_to_bv 64 0x97938) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-15)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-8)) s3 (Z_to_bv 64 (-14)) s5 (Z_to_bv 64 SHF) s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x97670) fc None m (seg_rom a0segs)).
  Proof.
    intros me m bs ra sp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 RZ MI MU WMo K.
    destruct (rw_cells_CB_C1s a0segs _ _ _ _ RZ) as [RZc L]. clear RZ. rename RZc into RZ.
    do 178 (destruct bs as [|? bs]; [discriminate L| cbn [length] in L; apply Nat.succ_inj in L]). destruct bs; [clear L| discriminate L].
    cbn [map] in RZ.
    do 178 sbx.
    destruct (rw_cells_cutJ a0segs _ _ _ 4 RZ) as [_ RZ1]. cbn [firstn skipn cells_size csize Nat.add] in RZ1. change (Z.of_nat 4) with 4%Z in RZ1.
    destruct (rw_cells_cutJ a0segs _ _ _ 166 RZ1) as [RZ2 _]. cbn [firstn] in RZ2.
    apply K; [exact RZ2| exact MI| exact MU| exact WMo].
  Qed.

  Lemma A0_bs_P2 : forall (me m : word -> option byte) (bs : list byte) (h0 h1 h2 v424 : word)
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    rw_cells a0segs m FB [C8 h0; C8 h1; C8 h2] -> rw_cells a0segs m SHF [CB 178 bs] -> rw_cells a0segs m (P + 424) [C8 v424] ->
    mem_inv a0segs m -> munch WP2 me m -> wmono a0segs me m ->
    (forall m' (y12 y13 y14 : word),
       rw_cells a0segs m' FB [C8 (Z_to_bv 64 1102416563); C8 (Z_to_bv 64 81238); C8 (Z_to_bv 64 619912)] ->
       rw_cells a0segs m' (SHF + 4) (shc3 f8b) -> rw_cells a0segs m' (P + 424) [C8 (Z_to_bv 64 FB)] ->
       mem_inv a0segs m' -> munch WP2 me m' -> wmono a0segs me m' ->
       evt a0segs Q (MS (mkR (Z_to_bv 64 0x97948) (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                             (Z_to_bv 64 (SHF + 178)) (Z_to_bv 64 128) y12 y13 y14 x15 x16 x17
                             (Z_to_bv 64 (-8)) (Z_to_bv 64 2147450880) (Z_to_bv 64 (-14)) (Z_to_bv 64 FB) (Z_to_bv 64 SHF) x23 (Z_to_bv 64 FB) x25 (Z_to_bv 64 (SHF + 178)) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x559e4) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR x1 (Z_to_bv 64 P) gp tp x5 x6 x7 (me_sp X) (Z_to_bv 64 P)
                          (Z_to_bv 64 FB) x11 x12 x13 x14 x15 x16 x17
                          x18 (Z_to_bv 64 2147450880) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 0x975fc) fc None m (seg_rom a0segs)).
  Proof.
    intros me m bs h0 h1 h2 v424 x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 HD RZ SL MI MU WMo K.
    msenv_open1 XOK. amenv_open YOK. amenv_shx_open X Y SHF YSHX. destruct YSF as (AX & YSl & YSh). unfold SH_LO, SH_HI in YSl, YSh.
    assert (AFS : (FB + 5216 <= SHF \/ SHF + 652 <= FB)%Z) by (destruct YOFF as (_ & _ & _ & O4); unfold SH_LO, SH_HI in O4; lia). box_ors.
    (* [comment removed for export] *)
    wstep. wstep. wstep.
    wstep; if_cases Ks; zify_cond_z Ks; [| exfalso; lia].
    wstep.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep. wstep.
    wstep. lit_store. wstep. lit_store. wstep. lit_store. wstep. wstep.
    rewrite (sanchor_addr0 FB SHF AX).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => set (m1 := mm) in * end.
    enter_with (A0_bs_P2sb m1 m1 bs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _);
      [st_eq| exact RZ| exact MI| apply munch_refl| apply wmono_refl|].
    intros m2 RZ2 MI2 MU2 WM2. clear RZ MI. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    eapply K; [exact HD| exact RZ2| exact SL| exact MI2| exact MU| exact WMo].
  Qed.
End A0MS.

End ACeilS1.
