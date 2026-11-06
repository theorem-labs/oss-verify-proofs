(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
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
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GI.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE : Z).
  Hypothesis CX : cctx_ok cx.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.

  (* [comment removed for export] *)
  Notation LR ra v a0 a1 s2 s3 s6 s7 s8 s9 s10 s11 t5 t6 :=
    (mkR ra cP gp tp (Z_to_bv 64 (37708 + v)) (Z_to_bv 64 (E + 37708 + v)) (Z_to_bv 64 (38998 + v)) s0 cP a0 a1
         (Z_to_bv 64 (37966 + v)) (Z_to_bv 64 (38224 + v)) (Z_to_bv 64 (38482 + v)) (Z_to_bv 64 (51648 + 16 * v)) (Z_to_bv 64 (51644 + 16 * v)) (Z_to_bv 64 (51640 + 16 * v))
         s2 s3 cSB (Z_to_bv 64 E) s6 s7 s8 s9 s10 s11 (Z_to_bv 64 (A - v)) (Z_to_bv 64 (38740 + v)) t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wlp := [(E + 51640, E + 55768)]%Z.
  Lemma A0_sm_lpk : forall (n : nat) (v : Z) (lp len : zarr) (m mf : word -> option byte)
      (ra a0 a1 s2 s3 s6 s7 s8 s9 s10 s11 t5 t6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr a0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr a0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    mem_inv a0segs m -> munch Wlp mf m -> wmono a0segs mf m ->
    shzW a0segs Wlp mf E (E + ESTATE_SIZE) ->
    (forall m' (a0 a1 s2 t5 t6 : word),
      u8arr a0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr a0segs m' (E + 51640) (ovw (sm_lenpack n lp len v) (jseg J 51640 4128) 1032) ->
      mem_inv a0segs m' -> munch Wlp mf m' -> wmono a0segs mf m' ->
      evt a0segs Q (MS (LR ra A a0 a1 s2 s3 s6 s7 s8 s9 s10 s11 t5 t6)
                       F (Z_to_bv 64 0x8abe8) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (LR ra v a0 a1 s2 s3 s6 s7 s8 s9 s10 s11 t5 t6)
                     F (Z_to_bv 64 0x8aa4c) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v lp len m mf ra a0 a1 s2 s3 s6 s7 s8 s9 s10 s11 t5 t6 Hv Hv0 Hn LF LEN LPK MI MU WM SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LL.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length_nat lp (jseg J 51640 4128) 1032) as LLP.
    rewrite sm_lenpack_S in K. rewrite !lenpack_word_eq in K by (lazymatch goal with |- (0 <= zget _ (258 * ?t + _))%Z => exact (proj1 (proj2 (LF t v ltac:(lia) ltac:(lia)))) end).
    (* [comment removed for export] *)
    Ltac lprowA LEN LPK LF len v thi tlo ih il j :=
      let Dh := fresh "Dh" in let Rh := fresh "Rh" in let Dl := fresh "Dl" in let Rl := fresh "Rl" in let RD := fresh "RD" in
      destruct (LF thi v ltac:(lia) ltac:(lia)) as [Dh Rh]; destruct (LF tlo v ltac:(lia) ltac:(lia)) as [Dl Rl];
      replace (258 * thi + v)%Z with ih in Dh, Rh by lia; replace (258 * tlo + v)%Z with il in Dl, Rl by lia;
      arun;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovb_read1 a0segs mm (E + 37708) _ (jseg J 37708 1548) 1548 ih _ LEN ltac:(lia) Dh ltac:(unfold wa; f_equal; lia)) as RD end;
      lstep; clear RD; cbv beta; rewrite ?unsigned_lit8 by lia;
      arun;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovb_read1 a0segs mm (E + 37708) _ (jseg J 37708 1548) 1548 il _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD end;
      lstep; clear RD; cbv beta; rewrite ?unsigned_lit8 by lia;
      arun;
      pose proof (lenpack_word_range (zget len il) (zget len ih) ltac:(lia) ltac:(lia));
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch type of LPK with u32arr _ _ _ (ovw ?lpx _ _) =>
        pose proof (u32arr_store_ok a0segs mm (E + 51640) _ (4 * v + j) _ LPK ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
        lstep; store_addr (E + 51640 + 4 * (4 * v + j))%Z;
        ovw_store LPK (4 * v + j)%Z (Z.lor (zget len ih * 65536) (zget len il)) (rewrite unsigned_lit by lia; reflexivity) end end.
    replace (258 * 1 + v)%Z with (258 + v)%Z in K by lia. replace (258 * 0 + v)%Z with v in K by lia.
    replace (258 * 3 + v)%Z with (774 + v)%Z in K by lia. replace (258 * 2 + v)%Z with (516 + v)%Z in K by lia.
    replace (258 * 5 + v)%Z with (1290 + v)%Z in K by lia. replace (258 * 4 + v)%Z with (1032 + v)%Z in K by lia.
    lprowA LEN LPK LF len v 1%Z 0%Z (258 + v)%Z v 0%Z. replace (4 * v + 0)%Z with (4 * v)%Z in LPK by lia.
    lprowA LEN LPK LF len v 3%Z 2%Z (774 + v)%Z (516 + v)%Z 1%Z.
    lprowA LEN LPK LF len v 5%Z 4%Z (1290 + v)%Z (1032 + v)%Z 2%Z.
    (* [comment removed for export] *)
    arun; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (v + 1)%Z _ len _ mf); [st_eq| lia| lia| lia| exact LF| exact LEN| exact LPK| assumption| assumption| assumption| unfold ESTATE_SIZE; exact SHe| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_lenpack] in K. lstep.
      enter_with (K _ _ _ _ _ _); [st_eq| exact LEN| exact LPK| assumption| assumption| assumption].
  Qed.
End GI.
End ACeilS1.
