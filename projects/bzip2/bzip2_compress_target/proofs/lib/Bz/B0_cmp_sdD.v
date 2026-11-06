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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_sdFL1.


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

Section SDD.
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
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  (* [comment removed for export] *)
  Hypothesis INUF : forall k, (0 <= k < 256)%Z -> zdef INUA k = true /\ (0 <= zget INUA k < 256)%Z.
  (* [comment removed for export] *)
  Ltac curH k := let HI := ident:(HI) in
    lazymatch type of HI with rw_cells _ _ _ (_ :: _ :: C8 ?v00 :: C8 ?v08 :: C8 ?v16 :: C8 ?v24 :: C8 ?v32 :: _ :: C8 ?v48 :: C8 ?v56 :: _ :: C8 ?v72 :: _ ::
                                              C8 ?v88 :: C8 ?v96 :: C8 ?v04 :: C8 ?v12 :: C8 ?v20 :: C8 ?v28 :: _) =>
      k (SDW v00 v08 v16 v24 v32 v48 v56 v72 v88 v96 v04 v12 v20 v28) end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section PH1.
  Variables (x3 x4 x5 x6 x7 x8 x9 x10 x11 : word).
  Notation RI ra t0 t1 t2 a0 a3 a4 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 (Z_to_bv 64 (E + 128)) (NOT (E + 128)) a3 a4 (Z_to_bv 64 (P + 1576)) (Z_to_bv 64 16) (Z_to_bv 64 1)
         cSB x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6).
  Notation ROWP i := (Z_to_bv 64 (E + 128 + 16 * i)).

  Lemma B0_in16_inner : forall (n : nat) (i j acc : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra t6 : word),
    (j + Z.of_nat n = 16)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < 16)%Z -> (acc = 0 \/ acc = 1)%Z ->
    Z.of_nat (length bs) = 16%Z -> nth_error bs (Z.to_nat i) = Some (Z_to_bv 8 acc) ->
    MD H bs b m ->
    (forall m' bs' (t6' : word),
        MD H bs' b m' -> Z.of_nat (length bs') = 16%Z ->
        nth_error bs' (Z.to_nat i) = Some (Z_to_bv 8 (sm_in16_row n INUA i j acc)) ->
        (forall k, k <> Z.to_nat i -> nth_error bs' k = nth_error bs k) ->
        evt b0segs Q (MS (RI ra (ROWP i) (ROWP i) (Z_to_bv 64 (P + 1576 + i)) (Z_to_bv 64 (E + 128 + 16 * i + 16)) (Z_to_bv 64 (16 * i)) (Z_to_bv 64 i)
                              (Z_to_bv 64 0) (Z_to_bv 64 (16 * i + 16)) (Z_to_bv 64 (E + 128 + 16 * i + 16)) t6')
                          F (Z_to_bv 64 0x93e94) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RI ra (ROWP i) (ROWP i) (Z_to_bv 64 (P + 1576 + i)) (Z_to_bv 64 (E + 128 + 16 * i + j)) (Z_to_bv 64 (16 * i)) (Z_to_bv 64 i)
                          (Z_to_bv 64 (16 - j)) (Z_to_bv 64 (16 * i + j)) (Z_to_bv 64 (E + 128 + 16 * i + j)) t6)
                      F (Z_to_bv 64 0x93e4c) fc None m (seg_rom b0segs)).
  Proof using All.
    induction n as [|n IH]; [lia|].
    intros i j acc H bs b m ra t6 Hj Hj0 _ Hi Hacc Lbs Nbs MEM K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    destruct (INUF (16 * i + j) ltac:(lia)) as [ZD ZR].
    (* [comment removed for export] *)
    brun.
    openVW VW.
    pose proof (ovb_read1 b0segs m (E + 128) INUA (jseg J 128 256) 256 (16 * i + j) _ INU ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    closeVW.
    wstep. clear RD. cbv beta.
    rewrite in16_row_S in K. replace (i * 16 + j)%Z with (16 * i + j)%Z in K by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      rewrite (unsigned_lit8 (zget INUA (16 * i + j))) in Kc by lia.
      replace (negb (zget INUA (16 * i + j) =? 0))%Z with false in K by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia).
      (* [comment removed for export] *)
      wstep. wstep. wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH i (j + 1)%Z acc H bs b m ra _); [st_eq| lia| lia| lia| lia| exact Hacc| exact Lbs| exact Nbs| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_in16_row] in K. wstep.
        enter_with (K m bs _); [st_eq| closeMD| exact Lbs| exact Nbs| intros; reflexivity].
    - (* [comment removed for export] *)
      rewrite (unsigned_lit8 (zget INUA (16 * i + j))) in Kc by lia.
      replace (negb (zget INUA (16 * i + j) =? 0))%Z with true in K by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      pose proof (u8arr_store_ok b0segs m (P + 1576) bs i _ I16 ltac:(lia) eq_refl) as SO.
      wstep. u8_store_done I16 i.
      wstep. wstep. wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH i (j + 1)%Z 1%Z H (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1)))) b mm ra _);
          [st_eq| lia| lia| lia| lia| right; reflexivity| rewrite upd_length; exact Lbs| |closeMD|] end.
        { rewrite nth_error_upd_same by lia. f_equal. }
        intros m' bs' t6' MEM' L' N' O'. eapply K; [exact MEM'| exact L'| exact N'|].
        intros k Hk. rewrite O' by exact Hk. apply nth_error_upd_other. lia.
      + assert (n = 0%nat) by lia. subst n. cbn [sm_in16_row] in K. wstep.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 1)))) _); [st_eq| closeMD| rewrite upd_length; exact Lbs| |] end.
        { rewrite nth_error_upd_same by lia. f_equal. }
        intros k Hk. apply nth_error_upd_other. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_in16_outer : forall (n : nat) (i : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra t2 a0 t3 t4 t5 t6 : word),
    (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < i)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    MD H bs b m ->
    (forall m' bs' (t0' t1' t2' a0' a3' t3' t4' t5' t6' : word),
        MD H bs' b m' -> Z.of_nat (length bs') = 16%Z ->
        (forall k, (0 <= k < 16)%Z -> nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
        evt b0segs Q (MS (RI ra t0' t1' t2' a0' a3' (Z_to_bv 64 16) t3' t4' t5' t6')
                          F (Z_to_bv 64 0x93ea8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RI ra (ROWP i) (ROWP i) t2 a0 (Z_to_bv 64 (16 * i)) (Z_to_bv 64 i) t3 t4 t5 t6)
                      F (Z_to_bv 64 0x93e34) fc None m (seg_rom b0segs)).
  Proof using All.
    induction n as [|n IH]; [lia|].
    intros i H bs b m ra t2 a0 t3 t4 t5 t6 Hi Hi0 _ Lbs ROWS MEM K.
    openCX. openMD MEM.
    (* [comment removed for export] *)
    wstep.
    pose proof (u8arr_store_ok b0segs m (P + 1576) bs i _ I16 ltac:(lia) eq_refl) as SO.
    wstep. u8_store_done I16 i.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (B0_in16_inner 16 i 0 0 H (upd bs (Z.to_nat i) (Z_to_bv 8 (bv_unsigned (Z_to_bv 64 0)))) b mm ra _);
      [st_eq| lia| lia| lia| lia| left; reflexivity| rewrite upd_length; exact Lbs| | closeMD|] end.
    { rewrite nth_error_upd_same by lia. f_equal. }
    intros m' bs' t6' MEM' L' N' O'. fold (ROW16 INUA i) in N'.
    assert (ROWS' : forall k, (0 <= k < i + 1)%Z -> nth_error bs' (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))).
    { intros k Hk. destruct (Z.eq_dec k i) as [->|NE]; [exact N'|].
      rewrite O' by lia. rewrite nth_error_upd_other by lia. apply ROWS. lia. }
    clear EH1 EH2 AR2 HI I16 MI MU WM. openMD MEM'.
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (i + 1)%Z H bs' b m' ra _ _ _ _ _ _); [st_eq| lia| lia| lia| exact L'| exact ROWS'| closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n.
      enter_with (K m' bs' _ _ _ _ _ _ _ _ _); [st_eq| closeMD| exact L'|]. intros k Hk. apply ROWS'. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_in16_pre : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    MD H bs b m ->
    (forall (a0' : word), evt b0segs Q (MS (RI ra (ROWP 0) (ROWP 0) t2 a0' (Z_to_bv 64 (16 * 0)) (Z_to_bv 64 0) t3 t4 t5 t6) F (Z_to_bv 64 0x93e34) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6) F (Z_to_bv 64 0x93e0c) fc None m (seg_rom b0segs)).
  Proof using All.
    intros H bs b m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MEM K.
    openCX. openMD MEM. openVW VW.
    brun_to 0x93e34%Z.
    enter_with (K _); st_eq.
  Qed.
  End PH1.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_pin16_pre : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a3 a4 a6 a7 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 : word),
    MD H bs b m ->
    (forall m' (H' : sdw) (a0' a3' : word), w1448 H' = w1448 H -> w1496 H' = w1496 H -> w1504 H' = w1504 H -> w1512 H' = w1512 H -> w1520 H' = w1520 H -> MD H' bs b m' ->
        evt b0segs Q (MS (RD ra (Z_to_bv 64 32) (Z_to_bv 64 31) (Z_to_bv 64 16) a0' (Z_to_bv 64 (E + 128)) (NOT (E + 128)) a3' (Z_to_bv 64 0) (Z_to_bv 64 (P + 1576))
                              (Z_to_bv 64 8) (Z_to_bv 64 7) x10 (Z_to_bv 64 1) t4 t5 t6)
                          F (Z_to_bv 64 0x93f34) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 (Z_to_bv 64 (E + 128)) (NOT (E + 128)) a3 a4 (Z_to_bv 64 (P + 1576)) a6 a7 cSB x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6)
                      F (Z_to_bv 64 0x93ea8) fc None m (seg_rom b0segs)).
  Proof using All.
    intros H bs b m ra t0 t1 t2 a0 a3 a4 a6 a7 x3 x4 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 t6 MEM K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. openVW VW.
    brun_to 0x93f34%Z. sh_norm. closeVW.
    curH ltac:(fun HH => lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm HH _ _); [st_eq| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| closeMD] end).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HG : (2 <= nG <= 6)%Z.
  Notation RP ra a0 a3 i s10 t4 t5 t6 :=
    (RD ra (Z_to_bv 64 32) (Z_to_bv 64 31) (Z_to_bv 64 16) a0 (Z_to_bv 64 (E + 128)) (NOT (E + 128)) a3 (Z_to_bv 64 i) (Z_to_bv 64 (P + 1576)) (Z_to_bv 64 8) (Z_to_bv 64 7)
        s10 (Z_to_bv 64 1) t4 t5 t6).
  (* [comment removed for export] *)
  Notation BWmid b1 n v := (BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - n) mod 4294967296)) (bw_live b1) (bw_numZ b1) (bw_zb b1)).
  (* [comment removed for export] *)
  Notation PIN16_IH n :=
    (forall (i : Z) (in16 : zarr) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a3 s10 t4 t5 t6 : word),
      (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
      Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
      (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
      let bf := sm_put_in16 n b in16 i in
      bw_ok b -> (bw_numZ bf <= LIM)%Z ->
      MD H bs b m ->
      (forall m' (ra' a0' a3' s10' t4' t5' t6' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt b0segs Q (MS (RP ra' a0' a3' 16 s10' t4' t5' t6') F (Z_to_bv 64 0x9426c) fc None m' (seg_rom b0segs))) ->
      evt b0segs Q (MS (RP ra a0 a3 i s10 t4 t5 t6) F (Z_to_bv 64 0x93f34) fc None m (seg_rom b0segs))).

  (* [comment removed for export] *)
  Lemma B0_pin16_join : forall (i : Z) (n : nat) (in16 : zarr) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (ra a3 s10 t4 t5 t6 : word) (v : Z),
    (i + Z.of_nat (S n) = 16)%Z -> (0 <= i)%Z ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    (0 <= v <= 1)%Z ->
    let bf := sm_put_in16 n (bsW b 1 v) in16 (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z ->
    MD H bs (BWmid b1 1 v) m ->
    PIN16_IH n ->
    (forall m' (ra' a0' a3' s10' t4' t5' t6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RP ra' a0' a3' 16 s10' t4' t5' t6') F (Z_to_bv 64 0x9426c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RP ra (Z_to_bv 64 (bw_live b1)) a3 i s10 t4 t5 t6) F (Z_to_bv 64 0x94228) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i n in16 H bs b b1 m ra a3 s10 t4 t5 t6 v Hi Hi0 Lbs ROWS IN16 Hv. cbv zeta. intros OK Eb1 NL MEM IHn K.
    pose proof (put_in16_NZM n (bsW b 1 v) in16 (i + 1)) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM. cbn [bw_buff bw_live bw_numZ bw_zb] in EH1, EH2. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 1 v = BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    (* [comment removed for export] *)
    brun. if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn (i + 1)%Z in16 H bs (bsW b 1 v) mm ra _ _ s10 t4 t5 t6);
        [st_eq| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_in16] in K. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_pin16_tail1 : forall (i : Z) (n : nat) (in16 : zarr) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (ra a3 s10 t4 t5 t6 : word),
    (i + Z.of_nat (S n) = 16)%Z -> (0 <= i)%Z ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    let bf := sm_put_in16 n (bsW b 1 1) in16 (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (0 <= bw_live b1 < 8)%Z -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b1 m ->
    PIN16_IH n ->
    (forall m' (ra' a0' a3' s10' t4' t5' t6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RP ra' a0' a3' 16 s10' t4' t5' t6') F (Z_to_bv 64 0x9426c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RP ra (Z_to_bv 64 (bw_live b1)) a3 i s10 t4 t5 t6) F (Z_to_bv 64 0x94084) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i n in16 H bs b b1 m ra a3 s10 t4 t5 t6 Hi Hi0 Lbs ROWS IN16. cbv zeta. intros OK Eb1 L1 NL MEM IHn K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n).
    brun_to 0x94228%Z.
    lazymatch type of EH2 with context [Z.shiftl 1 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 1)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_pin16_join i n in16 H bs b b1 mm ra _ s10 _ t5 t6 1%Z); [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| lia| exact OK| exact Eb1| exact NL| closeMD| exact IHn| exact K] end.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_pin16_tail0 : forall (i : Z) (n : nat) (in16 : zarr) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte)
      (ra a3 s10 t4 t5 t6 : word),
    (i + Z.of_nat (S n) = 16)%Z -> (0 <= i)%Z ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    let bf := sm_put_in16 n (bsW b 1 0) in16 (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (0 <= bw_live b1 < 8)%Z -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b1 m ->
    PIN16_IH n ->
    (forall m' (ra' a0' a3' s10' t4' t5' t6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RP ra' a0' a3' 16 s10' t4' t5' t6') F (Z_to_bv 64 0x9426c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RP ra (Z_to_bv 64 (bw_live b1)) a3 i s10 t4 t5 t6) F (Z_to_bv 64 0x94200) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i n in16 H bs b b1 m ra a3 s10 t4 t5 t6 Hi Hi0 Lbs ROWS IN16. cbv zeta. intros OK Eb1 L1 NL MEM IHn K.
    openCX.
    brun_to 0x94228%Z.
    enter_with (B0_pin16_join i n in16 H bs b b1 m ra _ s10 _ t5 t6 0%Z); [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| lia| exact OK| exact Eb1| exact NL| | exact IHn| exact K].
    rewrite lor_shl0. openMD MEM. closeMD.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_pin16_loop : forall (n : nat), PIN16_IH n.
  Proof using All.
    induction n as [|n IH]; [intros; lia|].
    intros i in16 H bs b m ra a0 a3 s10 t4 t5 t6 Hi Hi0 _ Lbs ROWS IN16. cbv zeta. intros OK NL MEM K.
    rewrite put_in16_S in NL, K. rewrite (IN16 i) in NL, K by lia.
    set (v := (if negb (ROW16 INUA i =? 0) then 1 else 0)%Z) in NL, K.
    pose proof (put_in16_NZM n (bsW b 1 v) in16 (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 1 v) as NZ0. unfold NZM in NZ0.
    assert (R01 : (0 <= ROW16 INUA i <= 1)%Z) by (destruct (ROW16_01 INUA i); lia).
    assert (Hv : (0 <= v <= 1)%Z) by (subst v; destruct (negb _); lia).
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (NF : b = bs_needw BS_FUEL b \/ (8 <= bw_live b)%Z).
    { destruct (Z.leb_spec 8 (bw_live b)); [right; assumption|left]. unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    (* [comment removed for export] *)
    brun.
    pose proof (u8arr_read b0segs m (P + 1576) bs i _ _ I16 (ROWS i ltac:(lia)) ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (ROW16 INUA i)) by lia.
    (* [comment removed for export] *)
    brun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (Ev : v = 0%Z) by (subst v; replace (ROW16 INUA i =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + destruct NF as [NF|NF]; [|exfalso; lia].
        enter_with (B0_pin16_tail0 i n in16 H bs b b m ra _ s10 _ t5 t6); [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact NF| lia| exact NL| closeMD| exact IH| exact K].
      + enter_with (FLX fl_93e08 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
        { pose proof (bsW_bytes b 1 0) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' t4' t5' t6' a3' s10' Eb1 MEM' L1.
        enter_with (B0_pin16_tail0 i n in16 H bs b b1 m' ra _ _ _ _ _); [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact Eb1| exact L1| exact NL| exact MEM'| exact IH| exact K].
    - (* [comment removed for export] *)
      assert (Ev : v = 1%Z) by (subst v; replace (ROW16 INUA i =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + destruct NF as [NF|NF]; [|exfalso; lia].
        enter_with (B0_pin16_tail1 i n in16 H bs b b m ra _ s10 _ t5 t6); [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact NF| lia| exact NL| closeMD| exact IH| exact K].
      + enter_with (FLX fl_93c8c BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
        { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' t4' t5' t6' a3' s10' Eb1 MEM' L1.
        enter_with (B0_pin16_tail1 i n in16 H bs b b1 m' ra _ _ _ _ _); [st_eq| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact Eb1| exact L1| exact NL| exact MEM'| exact IH| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation RUo ra a0 a3 a6 s10 t4 t5 t6 i :=
    (RD ra (Z_to_bv 64 8) (Z_to_bv 64 7) (Z_to_bv 64 32) a0 (Z_to_bv 64 (E + 128)) (NOT (E + 128)) a3 (Z_to_bv 64 i) (Z_to_bv 64 (256 - 16 * i)) a6 (Z_to_bv 64 16)
        s10 (Z_to_bv 64 31) t4 t5 t6).
  Notation RU ra a0 a3 a6 s10 t4 i j := (RUo ra a0 a3 a6 s10 t4 (Z_to_bv 64 j) (Z_to_bv 64 (16 * i)) i).
  Notation PINUSE_IH n :=
    (forall (i j : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a3 a6 s10 t4 : word),
      (j + Z.of_nat n = 16)%Z -> (0 <= j)%Z -> (1 <= n)%nat -> (0 <= i < 16)%Z ->
      let bf := sm_put_inuse_row n b INUA i j in
      bw_ok b -> (bw_numZ bf <= LIM)%Z ->
      MD H bs b m ->
      (forall m' (ra' a0' a3' a6' s10' t4' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt b0segs Q (MS (RU ra' a0' a3' a6' s10' t4' i 16) F (Z_to_bv 64 0x94608) fc None m' (seg_rom b0segs))) ->
      evt b0segs Q (MS (RU ra a0 a3 a6 s10 t4 i j) F (Z_to_bv 64 0x942a0) fc None m (seg_rom b0segs))).

  (* [comment removed for export] *)
  Lemma B0_pinuse_join : forall (i j : Z) (n : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (ra a3 a6 s10 t4 : word) (v : Z),
    (j + Z.of_nat (S n) = 16)%Z -> (0 <= j)%Z -> (0 <= i < 16)%Z -> (0 <= v <= 1)%Z ->
    let bf := sm_put_inuse_row n (bsW b 1 v) INUA i (j + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z ->
    MD H bs (BWmid b1 1 v) m ->
    PINUSE_IH n ->
    (forall m' (ra' a0' a3' a6' s10' t4' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RU ra' a0' a3' a6' s10' t4' i 16) F (Z_to_bv 64 0x94608) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RU ra (Z_to_bv 64 (bw_live b1)) a3 a6 s10 t4 i j) F (Z_to_bv 64 0x945bc) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i j n H bs b b1 m ra a3 a6 s10 t4 v Hj Hj0 Hi Hv. cbv zeta. intros OK Eb1 NL MEM IHn K.
    pose proof (put_inuse_row_NZM n (bsW b 1 v) INUA i (j + 1)) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM. cbn [bw_buff bw_live bw_numZ bw_zb] in EH1, EH2. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 1 v = BW (Z.lor (bw_buff b1) (Z.shiftl v (32 - bw_live b1 - 1) mod 4294967296)) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 1 v)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    brun. if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn i (j + 1)%Z H bs (bsW b 1 v) mm ra _ _ a6 s10 t4);
        [st_eq| lia| lia| lia| lia| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse_row] in K. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_pinuse_tail1 : forall (i j : Z) (n : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (ra a3 a6 s10 t4 : word),
    (j + Z.of_nat (S n) = 16)%Z -> (0 <= j)%Z -> (0 <= i < 16)%Z ->
    let bf := sm_put_inuse_row n (bsW b 1 1) INUA i (j + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (0 <= bw_live b1 < 8)%Z -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b1 m ->
    PINUSE_IH n ->
    (forall m' (ra' a0' a3' a6' s10' t4' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RU ra' a0' a3' a6' s10' t4' i 16) F (Z_to_bv 64 0x94608) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RU ra (Z_to_bv 64 (bw_live b1)) a3 a6 s10 t4 i j) F (Z_to_bv 64 0x94414) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i j n H bs b b1 m ra a3 a6 s10 t4 Hj Hj0 Hi. cbv zeta. intros OK Eb1 L1 NL MEM IHn K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n).
    brun_to 0x945bc%Z.
    lazymatch type of EH2 with context [Z.shiftl 1 (?s mod 32)] => replace (s mod 32)%Z with (32 - bw_live b1 - 1)%Z in EH2 by (rewrite Z.mod_small; lia) end.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 1 (32 - bw_live b1 - 1) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_pinuse_join i j n H bs b b1 mm ra _ _ _ t4 1%Z); [st_eq| lia| lia| lia| lia| exact OK| exact Eb1| exact NL| closeMD| exact IHn| exact K] end.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_pinuse_tail0 : forall (i j : Z) (n : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (ra a3 a6 s10 t4 : word),
    (j + Z.of_nat (S n) = 16)%Z -> (0 <= j)%Z -> (0 <= i < 16)%Z ->
    let bf := sm_put_inuse_row n (bsW b 1 0) INUA i (j + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (0 <= bw_live b1 < 8)%Z -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b1 m ->
    PINUSE_IH n ->
    (forall m' (ra' a0' a3' a6' s10' t4' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RU ra' a0' a3' a6' s10' t4' i 16) F (Z_to_bv 64 0x94608) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RU ra (Z_to_bv 64 (bw_live b1)) a3 a6 s10 t4 i j) F (Z_to_bv 64 0x94594) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i j n H bs b b1 m ra a3 a6 s10 t4 Hj Hj0 Hi. cbv zeta. intros OK Eb1 L1 NL MEM IHn K.
    openCX.
    brun_to 0x945bc%Z.
    enter_with (B0_pinuse_join i j n H bs b b1 m ra _ _ _ t4 0%Z); [st_eq| lia| lia| lia| lia| exact OK| exact Eb1| exact NL| | exact IHn| exact K].
    rewrite lor_shl0. openMD MEM. closeMD.
  Qed.

  Lemma B0_pinuse_inner : forall (n : nat), PINUSE_IH n.
  Proof using All.
    induction n as [|n IH]; [intros; lia|].
    intros i j H bs b m ra a0 a3 a6 s10 t4 Hj Hj0 _ Hi. cbv zeta. intros OK NL MEM K.
    rewrite put_inuse_row_S in NL, K.
    destruct (INUF (i * 16 + j) ltac:(lia)) as [ZD ZR].
    set (v := (if negb (zget INUA (i * 16 + j) =? 0) then 1 else 0)%Z) in NL, K.
    pose proof (put_inuse_row_NZM n (bsW b 1 v) INUA i (j + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 1 v) as NZ0. unfold NZM in NZ0.
    assert (Hv : (0 <= v <= 1)%Z) by (subst v; destruct (negb _); lia).
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (NF : b = bs_needw BS_FUEL b \/ (8 <= bw_live b)%Z).
    { destruct (Z.leb_spec 8 (bw_live b)); [right; assumption|left]. unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    (* [comment removed for export] *)
    brun.
    openVW VW.
    pose proof (ovb_read1 b0segs m (E + 128) INUA (jseg J 128 256) 256 (i * 16 + j) _ INU ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    closeVW.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (zget INUA (i * 16 + j))) by lia.
    (* [comment removed for export] *)
    brun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (Ev : v = 0%Z) by (subst v; replace (zget INUA (i * 16 + j) =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + destruct NF as [NF|NF]; [|exfalso; lia].
        enter_with (B0_pinuse_tail0 i j n H bs b b m ra _ a6 _ t4); [st_eq| lia| lia| lia| exact OK| exact NF| lia| exact NL| closeMD| exact IH| exact K].
      + enter_with (FLX fl_9419c BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
        { pose proof (bsW_bytes b 1 0) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' s10' ra' a3' a6' t4' Eb1 MEM' L1.
        enter_with (B0_pinuse_tail0 i j n H bs b b1 m' _ _ _ _ _); [st_eq| lia| lia| lia| exact OK| exact Eb1| exact L1| exact NL| exact MEM'| exact IH| exact K].
    - (* [comment removed for export] *)
      assert (Ev : v = 1%Z) by (subst v; replace (zget INUA (i * 16 + j) =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia); reflexivity).
      rewrite Ev in *. clear Hv.
      wstep; if_cases Kc2; zify_cond_z Kc2.
      + destruct NF as [NF|NF]; [|exfalso; lia].
        enter_with (B0_pinuse_tail1 i j n H bs b b m ra _ a6 _ t4); [st_eq| lia| lia| lia| exact OK| exact NF| lia| exact NL| closeMD| exact IH| exact K].
      + enter_with (FLX fl_9401c BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
        { pose proof (bsW_bytes b 1 1) as [BB _]. rewrite <- BB. lia. }
        intros b1 m' s10' a3' ra' a6' t4' Eb1 MEM' L1.
        enter_with (B0_pinuse_tail1 i j n H bs b b1 m' _ _ _ _ _); [st_eq| lia| lia| lia| exact OK| exact Eb1| exact L1| exact NL| exact MEM'| exact IH| exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_pinuse_outer : forall (n : nat) (i : Z) (in16 : zarr) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte)
      (ra a0 a3 a6 s10 t4 t5 t6 : word),
    (i + Z.of_nat n = 16)%Z -> (0 <= i)%Z -> (1 <= n)%nat ->
    Z.of_nat (length bs) = 16%Z -> (forall k, (0 <= k < 16)%Z -> nth_error bs (Z.to_nat k) = Some (Z_to_bv 8 (ROW16 INUA k))) ->
    (forall k, (0 <= k < 16)%Z -> zget in16 k = ROW16 INUA k) ->
    let bf := sm_put_inuse n b in16 INUA i in
    bw_ok b -> (bw_numZ bf <= LIM)%Z ->
    MD H bs b m ->
    (forall m' (ra' a0' a3' a6' s10' t4' t5' t6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RUo ra' a0' a3' a6' s10' t4' t5' t6' 16) F (Z_to_bv 64 0x94614) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RUo ra a0 a3 a6 s10 t4 t5 t6 i) F (Z_to_bv 64 0x94288) fc None m (seg_rom b0segs)).
  Proof using All.
    induction n as [|n IH]; [lia|].
    intros i in16 H bs b m ra a0 a3 a6 s10 t4 t5 t6 Hi Hi0 _ Lbs ROWS IN16. cbv zeta. intros OK NL MEM K.
    rewrite put_inuse_S in NL, K. rewrite (IN16 i) in NL, K by lia.
    assert (R01 : (0 <= ROW16 INUA i <= 1)%Z) by (destruct (ROW16_01 INUA i); lia).
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    (* [comment removed for export] *)
    wstep. wstep.
    pose proof (u8arr_read b0segs m (P + 1576) bs i _ _ I16 (ROWS i ltac:(lia)) ltac:(lia) eq_refl) as RD.
    wstep. clear RD. cbv beta. rewrite (unsigned_lit8 (ROW16 INUA i)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      replace (negb (ROW16 INUA i =? 0))%Z with false in NL, K by (symmetry; apply Bool.negb_false_iff; apply Z.eqb_eq; lia).
      pose proof (put_inuse_NZM n b in16 INUA (i + 1)) as NZ1. unfold NZM in NZ1.
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH (i + 1)%Z in16 H bs b m ra _ _ _ _ _ _ _); [st_eq| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK| exact NL| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse] in K.
        enter_with (K m _ _ _ _ _ _ _ _); [st_eq| closeMD| exact OK].
    - (* [comment removed for export] *)
      replace (negb (ROW16 INUA i =? 0))%Z with true in NL, K by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
      set (b16 := sm_put_inuse_row 16 b INUA i 0) in NL, K.
      pose proof (put_inuse_NZM n b16 in16 INUA (i + 1)) as NZ1. unfold NZM in NZ1.
      wstep. wstep.
      enter_with (B0_pinuse_inner 16 i 0 H bs b m ra _ _ _ _ _); [st_eq| lia| lia| lia| lia| exact OK| fold b16; lia| closeMD|].
      fold b16. clear EH1 EH2 AR2 HI I16 MI MU WM.
      intros m' ra' a0' a3' a6' s10' t4' MEM' OK'.
      openMD MEM'. cps_pose OK' as (OKb' & OKl' & OKn').
      (* [comment removed for export] *)
      wstep. wstep. wstep; if_cases Kc2; zify_cond_z Kc2.
      + enter_with (IH (i + 1)%Z in16 H bs b16 m' _ _ _ _ _ _ _ _); [st_eq| lia| lia| lia| exact Lbs| exact ROWS| exact IN16| exact OK'| exact NL| closeMD| exact K].
      + assert (n = 0%nat) by lia. subst n. cbn [sm_put_inuse] in K.
        enter_with (K m' _ _ _ _ _ _ _ _); [st_eq| closeMD| exact OK'].
  Qed.

  (* [comment removed for export] *)
  Lemma B0_pinuse_pre : forall (m : word -> option byte) (ra a0 a3 s10 t4 t5 t6 : word),
    (forall (a6' : word), evt b0segs Q (MS (RUo ra a0 a3 a6' s10 t4 t5 t6 0) F (Z_to_bv 64 0x94288) fc None m (seg_rom b0segs))) ->
    evt b0segs Q (MS (RP ra a0 a3 16 s10 t4 t5 t6) F (Z_to_bv 64 0x9426c) fc None m (seg_rom b0segs)).
  Proof using All.
    intros m ra a0 a3 s10 t4 t5 t6 K.
    brun_to 0x94288%Z.
    enter_with (K _); st_eq.
  Qed.
End SDD.
End ACeilS1.
