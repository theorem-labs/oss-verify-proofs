(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 DecTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCSortM BzArrD CmpMem CmpCut BzCNumZ CmpLaws CmpCutCB CmpArith CmpSdTac BzSepTac BzCLemmas1 BzLemmasMtf BzLemmasT CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require BzParamsLia.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzParamsLia.BzParamsX.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_fsV B0_cmp_msV CmpSmKit CmpHmKit B0_cmp_cbV B0_cmp_cbP.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require A0_cmp_cbH1.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store4 :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.

Section B0CBH1.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Hypothesis CE : cb_entry g e.
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation n := (e_nblock e).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WH1 := [(E + 116, E + 120); (E + 648, E + 656); (P, P + 184)]%Z.
  (* [comment removed for export] *)
  Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s6 s7 s9 s10 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         cSB (il_w (ce_il X)) s4 (Z_to_bv 64 FB) s6 s7 (Z_to_bv 64 FB) s9 s10 (Z_to_bv 64 SHF) t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma B0_cb_numz : forall (m1 : word -> option byte) (ra t0 t1 t2 a1 a3 a4 a5 a7 s6 s7 s9 s10 t3 t4 t5 t6 : word),
    (0 < n)%Z ->
    rw_cells b0segs m1 E (EHEAD1 cx g (cb_e0 e)) -> mem_inv b0segs m1 -> shzW b0segs [(E + 116, E + 120)]%Z m1 E (E + 55768) ->
    (forall m2 (y10 : word), rw_cells b0segs m2 E (EHEAD1 cx g (cb_e0 e)) -> mem_inv b0segs m2 -> munch [(E + 116, E + 120)]%Z m1 m2 -> wmono b0segs m1 m2 ->
      evt b0segs Q (MS (RB ra t0 t1 t2 y10 a1 (Z_to_bv 64 (e_blockNo e)) a3 a4 a5 (Z_to_bv 64 E) a7 (Z_to_bv 64 (E + 116)) s6 s7 s9 s10 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x89be8) fc None m2 (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 (Z_to_bv 64 2) a1 (Z_to_bv 64 (e_blockNo e)) a3 a4 a5 (Z_to_bv 64 E) a7 (Z_to_bv 64 (E + 116)) s6 s7 s9 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x89bcc) fc None m1 (seg_rom b0segs)).
  Proof.
    intros m1 ra t0 t1 t2 a1 a3 a4 a5 a7 s6 s7 s9 s10 t3 t4 t5 t6 POS EH1 MI SHe K.
    cbenv_open XOK. cb_ranges CX. clear CX SEP. acenv_open YOK.
    pose proof (cb_entry_facts g e CE) as (EOK & _). cps_pose EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BN).
    pose proof (munch_refl [(E + 116, E + 120)]%Z m1) as MU. pose proof (wmono_refl b0segs m1) as WM.
    unfold EHEAD1, cb_e0 in EH1. cbn_est_in EH1.
    wstep; if_cases Kb; zify_cond_z Kb.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end; [st_eq| unfold EHEAD1, cb_e0; cbn_est; exact EH1| exact MI| exact MU| exact WM].
    - brun_to 0x89be4%Z. wstep; lit_store4.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _) end; [st_eq| unfold EHEAD1, cb_e0; cbn_est; exact EH1| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation sl1 sl := (bset144 (bset48 sl (Z_to_bv 64 (E + 656))) (Z_to_bv 64 (SHE + 13))).
  Lemma B0_cb_H1 : forall (m : word -> option byte) (sl : cbslB) (ra t0 t1 t2 a2 a3 a4 a5 a7 s4 s6 s7 s9 s10 t3 t4 t5 t6 : word),
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells b0segs m P (cbslB_cells sl) -> mem_inv b0segs m -> shzW b0segs WH1 m E (E + 55768) ->
    ((0 < n)%Z -> forall m' (y11 y13 y14 y15 y17 : word),
       rw_cells b0segs m' E (EHEAD1 cx g (cb_e0 e)) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g (cb_e0 e)) ->
       rw_cells b0segs m' P (cbslB_cells (sl1 sl)) -> mem_inv b0segs m' -> munch WH1 m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (RB (Z_to_bv 64 0x89c18) t0 t1 t2 (Z_to_bv 64 E) y11 (Z_to_bv 64 (e_blockNo e)) y13 y14 y15 (Z_to_bv 64 E) y17
                            (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 108)) (Z_to_bv 64 (E + 648)) (Z_to_bv 64 (E + 660)) (Z_to_bv 64 (E + 652)) t3 t4 t5 t6)
                        F (Z_to_bv 64 0xa0988) fc None m' (seg_rom b0segs))) ->
    (n = 0%Z -> forall m' (y10 : word),
       rw_cells b0segs m' E (EHEAD1 cx g e) -> rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
       rw_cells b0segs m' P (cbslB_cells (sl1 sl)) -> mem_inv b0segs m' -> munch WH1 m m' -> wmono b0segs m m' ->
       evt b0segs Q (MS (RB ra t0 t1 t2 y10 (Z_to_bv 64 (-13)) a2 a3 a4 (Z_to_bv 64 0) (Z_to_bv 64 E) (Z_to_bv 64 (SHE + 13))
                            (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 108)) (Z_to_bv 64 (E + 648)) (Z_to_bv 64 (E + 660)) (Z_to_bv 64 (E + 652)) t3 t4 t5 t6)
                        F (Z_to_bv 64 0x89c20) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RB ra t0 t1 t2 (Z_to_bv 64 (-8)) (Z_to_bv 64 (-13)) a2 a3 a4 a5 (Z_to_bv 64 E) a7 s4 s6 s7 s9 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x89b08) fc None m (seg_rom b0segs)).
  Proof.
    intros m sl ra t0 t1 t2 a2 a3 a4 a5 a7 s4 s6 s7 s9 s10 t3 t4 t5 t6 EH1 EH2 SL MI SHe Kbs Kz.
    cbenv_open XOK. cb_ranges CX. acenv_open YOK.
    pose proof CX as CX'. unfold cctx_ok in CX'. cbv zeta in CX'.
    destruct CX' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ME16 & _). clear CX SEP.
    assert (EL7 : Z.land E 7 = 0%Z). { change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. clear - ME16. Z.div_mod_to_equations. lia. }
    cps_pose (cb_entry_facts g e CE) as (EOK & NBR & _ & _ & _ & NZ0 & _ & _). bz_params.
    cps_pose EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BC & CC & BNR).
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2. unfold cbslB_cells in SL. rewrite NZ0 in EH1.
    pose proof (munch_refl WH1 m) as MU. pose proof (wmono_refl b0segs m) as WM.
    (* [comment removed for export] *)
    brun_to 0x89b14%Z. try rewrite EL7. brun_to 0x89b48%Z. wstep. brun_to 0x89b50%Z. sh_norm. wstep.
    try rewrite (sx32_of_Z n) by lia.
    (* [comment removed for export] *)
    (wstep; if_cases Kn; zify_cond_z Kn).
    - (* [comment removed for export] *)
      assert (N0 : n = 0%Z) by lia.
      replace (Z_to_bv 64 n) with (Z_to_bv 64 0) by (rewrite N0; reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (Kz N0 mm _) end;
        [st_eq| unfold EHEAD1; rewrite NZ0; exact EH1| exact EH2| exact SL| exact MI| exact MU| exact WM].
    - assert (POS : (0 < n)%Z) by lia. try clear Kn.
      (* [comment removed for export] *)
      brun_to 0x89b78%Z. wstep. brun_to 0x89bb0%Z. wstep. brun_to 0x89bcc%Z.
      reword_C4 EH2 2%nat (crc_final (e_blockCRC e)). { apply A0_cmp_cbH1.low32_final. exact BC. }
      reword_C4 EH2 3%nat (Z.lxor (Z.lor ((Z.shiftl (e_combinedCRC e) 1) mod 4294967296) (Z.shiftr (e_combinedCRC e) 31)) (crc_final (e_blockCRC e))).
      { apply A0_cmp_cbH1.low32_combine; [exact CC| exact BC]. }
      assert (EH2f : rw_cells b0segs _ (E + 640) (EHEAD2 cx g (cb_e0 e))) by (unfold EHEAD2, cb_e0; cbn_est; exact EH2). clear EH2.
      assert (EH1f : rw_cells b0segs _ E (EHEAD1 cx g (cb_e0 e))) by (unfold EHEAD1, cb_e0; cbn_est; exact EH1). clear EH1.
      try rewrite (sx32_of_Z (e_blockNo e)) by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      enter_with (B0_cb_numz m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ POS EH1f MI);
        [st_eq| eapply (shzW_sub b0segs WH1 _ m m1); [exact SHe| exact MU| a_sub_fp| lia| lia]|].
      clear EH1f MI. intros m2 y10 EH1 MI MU2 WM2. transport_after_call b0segs m1 m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      pose proof EH2f as EH2r. unfold EHEAD2, cb_e0 in EH2r. cbn_est_in EH2r.
      brun_to 0xa0988%Z. clear EH2r.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (Kbs POS mm _ _ _ _ _) end;
        [st_eq| exact EH1| exact EH2f| exact SL| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0CBH1.
End ACeilS1.
