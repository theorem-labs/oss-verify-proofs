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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 DecTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzArrD CmpMem CmpCut BzCNumZ CmpLaws CmpCutCB CmpArith CmpSdTac BzSepTac BzCLemmas1 BzLemmasMtf BzLemmasT CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
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
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV.
(* [comment removed for export] *)
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
(* [comment removed for export] *)

Section CrcArith.
  Open Scope Z_scope.
  Lemma low32_lxor_ones64 : forall a, Z.lxor a 18446744073709551615 mod M32 = Z.lxor (a mod M32) 4294967295.
  Proof. intros a. rewrite low32_lxor. reflexivity. Qed.
  Lemma crc_final_mod : forall c, 0 <= c < 4294967296 -> crc_final c mod M32 = crc_final c.
  Proof. intros c Hc. apply low32_small. pose proof (BzCLemmas1.crc_final_range c Hc). lia. Qed.
  (* [comment removed for export] *)
  Lemma low32_final : forall c, 0 <= c < 4294967296 ->
    bv_unsigned (Z_to_bv 64 (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 c))) 18446744073709551615)) mod M32 = crc_final c mod M32.
  Proof.
    intros c Hc. rewrite low32_lit, low32_lxor_ones64, low32_sx32, low32_lit, (low32_small c) by lia.
    rewrite crc_final_mod by lia. reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma low32_combine : forall c bc, 0 <= c < 4294967296 -> 0 <= bc < 4294967296 ->
    bv_unsigned (Z_to_bv 64
      (Z.lxor (Z.lor (Z.land (bv_swrap 32 (bv_unsigned (sx32 (Z_to_bv 64 c)) * 2)) 18446744073709551615)
                     (bv_unsigned (sx32 (Z_to_bv 64 c)) mod 4294967296 / 2147483648))
              (Z.lxor (bv_unsigned (sx32 (Z_to_bv 64 bc))) 18446744073709551615))) mod M32
    = Z.lxor (Z.lor ((Z.shiftl c 1) mod 4294967296) (Z.shiftr c 31)) (crc_final bc) mod M32.
  Proof.
    intros c bc Hc Hb. rewrite low32_lit, low32_lxor, low32_lxor_ones64.
    rewrite (low32_sx32 (Z_to_bv 64 bc)), (low32_lit bc), (low32_small bc) by lia. fold (crc_final bc).
    rewrite low32_lor. change 18446744073709551615 with (Z.ones 64) at 1. rewrite Z.land_ones by lia.
    change (2 ^ 64) with 18446744073709551616. rewrite mod64_mod32, swrap32_mod32, low32_mul.
    rewrite (low32_sx32 (Z_to_bv 64 c)), (low32_lit c), (low32_small c) by lia.
    rewrite (low32_small (c / 2147483648)). 2:{ split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. change (2 ^ 31) with 2147483648.
    symmetry. apply low32_small. change 4294967296 with (2 ^ 32) at 3.
    apply BzLemmasMtf.lxor_lt_pow2.
    - apply BzLemmasT.lor_lt_pow2.
      + pose proof (Z.mod_pos_bound (c * 2) 4294967296 ltac:(lia)). change (2 ^ 32) with 4294967296. lia.
      + split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. change (2147483648 * 2 ^ 32) with (2 ^ 63). lia.
    - change (2 ^ 32) with 4294967296. apply BzCLemmas1.crc_final_range. exact Hb.
  Qed.
End CrcArith.


Section A0CBH1.
  Variable X : cbenv. Variable Y : acenv. Variables (g : eg) (e : est). Variable Q : machine_state -> Prop.
  Hypothesis XOK : cbenv_ok X. Hypothesis YOK : acenv_ok X Y.
  Hypothesis AE : sanchor (c_E (ce_cx X)) (ac_SHE Y).
  Hypothesis CE : cb_entry g e.
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation P := (ac_P Y). Notation FB := (ac_FB Y). Notation SHF := (ac_SHF Y). Notation SHE := (ac_SHE Y).
  Notation E := (c_E cx). Notation n := (e_nblock e).
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Notation WH1 := [(E + 116, E + 120); (E + 648, E + 656); (P, P + 120)]%Z.
  (* [comment removed for export] *)
  Notation RB ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s9 s10 s11 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 P) gp tp t0 t1 t2 (ce_sp X) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
         (il_w (ce_il X)) cSB (Z_to_bv 64 E) s5 (Z_to_bv 64 SHF) (Z_to_bv 64 FB) (Z_to_bv 64 FB) s9 s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Lemma A0_cb_numz : forall (m1 : word -> option byte) (ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s5 s9 s10 s11 t3 t4 t5 t6 : word),
    (0 < n)%Z ->
    rw_cells a0segs m1 E (EHEAD1 cx g (cb_e0 e)) -> mem_inv a0segs m1 -> shzW a0segs [(E + 116, E + 120)]%Z m1 E (E + 55768) ->
    (forall m2 (y10 y11 : word), rw_cells a0segs m2 E (EHEAD1 cx g (cb_e0 e)) -> mem_inv a0segs m2 -> munch [(E + 116, E + 120)]%Z m1 m2 -> wmono a0segs m1 m2 ->
      evt a0segs Q (MS (RB ra t0 t1 t2 y10 y11 (Z_to_bv 64 (e_blockNo e)) a3 a4 a5 a6 a7 s5 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x88c58) fc None m2 (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t0 t1 t2 (Z_to_bv 64 2) a1 (Z_to_bv 64 (e_blockNo e)) a3 a4 a5 a6 a7 s5 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88c38) fc None m1 (seg_rom a0segs)).
  Proof.
    intros m1 ra t0 t1 t2 a1 a3 a4 a5 a6 a7 s5 s9 s10 s11 t3 t4 t5 t6 POS EH1 MI SHe K.
    cbenv_open XOK. cb_ranges CX. clear CX SEP.
    pose proof (cb_entry_facts g e CE) as (EOK & _). cps_pose EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BN).
    pose proof (munch_refl [(E + 116, E + 120)]%Z m1) as MU. pose proof (wmono_refl a0segs m1) as WM.
    unfold EHEAD1, cb_e0 in EH1. cbn_est_in EH1.
    wstep; if_cases Kb; zify_cond_z Kb.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end; [st_eq| unfold EHEAD1, cb_e0; cbn_est; exact EH1| exact MI| exact MU| exact WM].
    - arun_to 0x88c54%Z. wstep; lit_store. 
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _) end; [st_eq| unfold EHEAD1, cb_e0; cbn_est; exact EH1| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation sl1 sl := (set64 (set112 (set88 sl (Z_to_bv 64 (SHE + 13))) (Z_to_bv 64 FB)) (Z_to_bv 64 (E + 108))).
  Lemma A0_cb_H1 : forall (m : word -> option byte) (sl : cbsl) (ra t0 t1 t2 a1 a2 a4 a5 a6 a7 s5 s9 s10 s11 t3 t4 t5 t6 : word),
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells a0segs m P (cbsl_cells sl) -> mem_inv a0segs m -> shzW a0segs WH1 m E (E + 55768) ->
    ((0 < n)%Z -> forall m' (y10 y11 y12 y13 y14 y15 : word),
       rw_cells a0segs m' E (EHEAD1 cx g (cb_e0 e)) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g (cb_e0 e)) ->
       rw_cells a0segs m' P (cbsl_cells (sl1 sl)) -> mem_inv a0segs m' -> munch WH1 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (RB (Z_to_bv 64 0x88c7c) t0 t1 t2 (Z_to_bv 64 E) y11 y12 y13 y14 y15 a6 a7
                            (Z_to_bv 64 (E + 648)) (Z_to_bv 64 (E + 660)) (Z_to_bv 64 (E + 656)) (Z_to_bv 64 (E + 652)) t3 t4 t5 t6)
                        F (Z_to_bv 64 0x97588) fc None m' (seg_rom a0segs))) ->
    (n = 0%Z -> forall m' (y10 : word),
       rw_cells a0segs m' E (EHEAD1 cx g e) -> rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) ->
       rw_cells a0segs m' P (cbsl_cells (sl1 sl)) -> mem_inv a0segs m' -> munch WH1 m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (RB ra t0 t1 t2 y10 a1 a2 (Z_to_bv 64 (E + 108)) a4 (Z_to_bv 64 0) a6 a7
                            (Z_to_bv 64 (E + 648)) (Z_to_bv 64 (E + 660)) (Z_to_bv 64 (E + 656)) (Z_to_bv 64 (E + 652)) t3 t4 t5 t6)
                        F (Z_to_bv 64 0x88c80) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RB ra t0 t1 t2 (Z_to_bv 64 (SHE + -2147450867)) a1 a2 (Z_to_bv 64 (E + 108)) a4 a5 a6 a7 s5 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x88ba4) fc None m (seg_rom a0segs)).
  Proof.
    intros m sl ra t0 t1 t2 a1 a2 a4 a5 a6 a7 s5 s9 s10 s11 t3 t4 t5 t6 EH1 EH2 SL MI SHe Kbs Kz.
    cbenv_open XOK. cb_ranges CX. clear CX SEP. acenv_open YOK.
    cps_pose (cb_entry_facts g e CE) as (EOK & NBR & _ & _ & _ & NZ0 & _ & _). bz_params.
    cps_pose EOK as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & BC & CC & BNR).
    unfold EHEAD1 in EH1. unfold EHEAD2 in EH2. unfold cbsl_cells in SL. rewrite NZ0 in EH1.
    pose proof (munch_refl WH1 m) as MU. pose proof (wmono_refl a0segs m) as WM.
    (* [comment removed for export] *)
    arun_to 0x88ba8%Z. wstep. arun_to 0x88bb0%Z. wstep. arun_to 0x88bcc%Z. wstep.
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
      arun_to 0x88bf0%Z. wstep. arun_to 0x88c20%Z. wstep. arun_to 0x88c38%Z.
      reword_C4 EH2 2%nat (crc_final (e_blockCRC e)). { apply low32_final. exact BC. }
      reword_C4 EH2 3%nat (Z.lxor (Z.lor ((Z.shiftl (e_combinedCRC e) 1) mod 4294967296) (Z.shiftr (e_combinedCRC e) 31)) (crc_final (e_blockCRC e))).
      { apply low32_combine; [exact CC| exact BC]. }
      assert (EH2f : rw_cells a0segs _ (E + 640) (EHEAD2 cx g (cb_e0 e))) by (unfold EHEAD2, cb_e0; cbn_est; exact EH2). clear EH2.
      assert (EH1f : rw_cells a0segs _ E (EHEAD1 cx g (cb_e0 e))) by (unfold EHEAD1, cb_e0; cbn_est; exact EH1). clear EH1.
      try rewrite (sx32_of_Z (e_blockNo e)) by lia.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into m1 end.
      enter_with (A0_cb_numz m1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ POS EH1f MI);
        [st_eq| eapply (shzW_sub a0segs WH1 _ m m1); [exact SHe| exact MU| a_sub_fp| lia| lia]|].
      clear EH1f MI. intros m2 y10 y11 EH1 MI MU2 WM2. transport_after_call a0segs m1 m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      pose proof EH2f as EH2r. unfold EHEAD2, cb_e0 in EH2r. cbn_est_in EH2r.
      arun_to 0x97588%Z. clear EH2r.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (Kbs POS mm _ _ _ _ _ _) end;
        [st_eq| exact EH1| exact EH2f| exact SL| exact MI| exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

End A0CBH1.

End ACeilS1.
