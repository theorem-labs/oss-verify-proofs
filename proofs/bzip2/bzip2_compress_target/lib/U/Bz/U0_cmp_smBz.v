(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpFsKit BzCSmF1.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpHmKit CmpCutSmB BzCFactsSmB BzCFactsSmB2 CmpSmKit CmpSmKit2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
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
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import U0_cmp_smBc U0_cmp_smBb U0_cmp_smBrz U0_cmp_smBfz.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GZB.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac lit_store :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
    | _ => idtac
    end.
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.

  Notation RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 (Z_to_bv 64 (4 * A)) s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wm := [(SP + 32, SP + 40)]%Z.
  Lemma U0_sm_mid : forall (iter : Z) (w912 : word) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (0 <= iter < 4)%Z ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells s0segs m (SP + 32) [C8 (Z_to_bv 64 iter)] ->
    mem_inv s0segs m -> munch Wm mf m -> wmono s0segs mf m ->
    frdW s0segs Wm mf (SP + 912) [C8 w912] ->
    (forall m' (a0 a1 a3 : word),
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells s0segs m' (SP + 32) [C8 (Z_to_bv 64 (iter + 1))] ->
      mem_inv s0segs m' -> munch Wm mf m' -> wmono s0segs mf m' ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 (-1548)) s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b36c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b32c) fc None m (seg_rom s0segs)).
  Proof.
    intros iter w912 m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 HIT EH2 LOW MI MU WM V912 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    unfold EHEAD2 in EH2. rewrite GM in EH2.
    (* [comment removed for export] *)
    poseV V912 RO. wstep. clear RO. urun_to 0x1b354%Z.
    (* [comment removed for export] *)
    wstep; if_cases Kv; zify_cond_z Kv; [exfalso; revert Kv; rewrite ?signed_lit by lia; lia|].
    (* [comment removed for export] *)
    urun_to 0x1b364%Z. try rewrite (sx32_of_Z (iter + 1)) by lia. wstep; lit_store. urun_to 0x1b36c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _); [st_eq| unfold EHEAD2; rewrite GM; assumption| assumption| assumption| assumption| assumption] end.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_sm_itail : forall (iter : Z) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (1 <= iter <= 4)%Z ->
    rw_cells s0segs m (SP + 32) [C8 (Z_to_bv 64 iter)] ->
    ((iter < 4)%Z ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 (Z_to_bv 64 iter) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 1084)) s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1745c) fc None m (seg_rom s0segs))) ->
    ((iter = 4)%Z ->
      evt s0segs Q (MS (RIT ra t0 t1 t2 (Z_to_bv 64 iter) (Z_to_bv 64 4) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 1084)) s5 s7 s8 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x1b434) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b3bc) fc None m (seg_rom s0segs)).
  Proof.
    intros iter m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 HIT LOW K1 K2.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP.
    urun_to 0x1b3c8%Z.
    wstep; if_cases Ki; zify_cond_z Ki.
    - enter_with (K2 ltac:(lia)); st_eq.
    - urun_to 0x1745c%Z. enter_with (K1 ltac:(lia)); st_eq.
  Qed.
End GZB.

Lemma wr_at_munchU : forall segs W (m m' : word -> option byte) A n, wr_at segs m A n -> munch W m m' -> disjoint_from W A n -> wr_at segs m' A n.
Proof.
  intros segs W m m' A n (Ha & Hn & H) MU D. split; [lia|]. split; [lia|]. intros i Hi.
  specialize (H i Hi). unfold wview in *. rewrite (MU (wa (A + i))); [exact H|].
  eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
Qed.
Lemma u8arr_munchU : forall segs W (m m' : word -> option byte) A bs, u8arr segs m A bs -> munch W m m' -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr segs m' A bs.
Proof. intros segs W m m' A bs [Hb Hw] MU D. split; [eapply bytes_at_transport; eauto| eapply wr_at_munchU; eauto]. Qed.
Lemma u32arr_munchU : forall segs W (m m' : word -> option byte) A ws, u32arr segs m A ws -> munch W m m' -> disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr segs m' A ws.
Proof.
  intros segs W m m' A ws [Hb Hw] MU D. split; [| eapply wr_at_munchU; eauto].
  eapply bytes_at_transport; eauto. rewrite u32s_length. replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws))%Z by lia. exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section GZI.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (cost0 fave0 heap0 weight0 parent0 : zarr).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Hypothesis FACTS : smB_facts e cost0 fave0 heap0 weight0 parent0.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation ITK k := (ITk e cost0 fave0 heap0 weight0 parent0 k).
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Lemma HFC : forall lp, U0_cmp_smBb.FC_spec cx e Q gp tp F fc lp SP.
  Proof.
    intros lp. pose proof (proj1 FACTS) as H. unfold smB_static in H.
    cps_destruct H as (HA & HNG & HM & HNI & ZB & MV & HK & HK2 & HN6).
    exact (U0_fc cx e Q gp tp F fc lp SP CX CEP PHI HA HM ZB).
  Qed.
  Lemma HFR : U0_cmp_smBb.FR_spec cx e Q gp tp F fc SP.
  Proof.
    pose proof (proj1 FACTS) as H. unfold smB_static in H.
    cps_destruct H as (HA & HNG & HM & HNI & ZB & MV & HK & HK2 & HN6).
    exact (U0_fr cx e Q gp tp F fc SP CX HA HNG HM ZB).
  Qed.
  Ltac openF :=
    let H := fresh "ST0" in pose proof (proj1 FACTS) as H; unfold smB_static in H;
    cps_destruct H as (?HA & ?HNG & ?HM & ?HNI & ?ZB & ?MV & ?HK & ?HK2 & ?HN6).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).

  Notation RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s5 s7 s8 s10 s11 t3 t4 t5 t6 :=
    (mkR ra cSP gp tp t0 t1 t2 (Z_to_bv 64 E) (Z_to_bv 64 257) a0 a1 a2 a3 a4 a5 a6 a7
         s2 (Z_to_bv 64 1548) (Z_to_bv 64 (258 * nG)) s5 (Z_to_bv 64 (4 * A)) s7 s8 (NOT (E + 37708)) s10 s11 t3 t4 t5 t6).

  (* [comment removed for export] *)
  Definition Wit : list (Z * Z) :=
    [(E + 1704, E + 19706); (E + 45448, E + 51640); (E + 51640, E + 55768); (SP + 32, SP + 40); (SP + 48, SP + 528); (SP + 584, SP + 800); (SP + 832, SP + 888); (SP + 896, SP + 904);
     (SP + 912, SP + 928); (SP + 936, SP + 944); (SP + 976, SP + 984); (SP + 1024, SP + 1032); (SP + 1060, SP + 1096)]%Z.
  Ltac vdisj := cbn [disjoint_from]; rewrite ?ovw_length_nat, ?ovb_length_nat, ?zw32_length_nat, ?zb8_length_nat; rewrite ?Z2Nat.id by (bz_params; lia); Lib.Step.slia.
  (* [comment removed for export] *)
  Ltac iside MU AR1 LEN LPK :=
    first [ eassumption | apply HFC | apply HFR |
    lazymatch goal with
    | |- munch _ ?a ?a => apply munch_refl
    | |- wmono _ ?a ?a => apply wmono_refl
    | |- forall _, munch _ _ _ -> u8arr _ _ A1 _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply (u8arr_munchU s0segs _ _ m_ _ _ AR1 MU_); unfold U0_cmp_smBb.Wg; vdisj
    | |- forall _, munch _ _ _ -> u8arr _ _ (E + 37708)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply (u8arr_munchU s0segs _ _ m_ _ _ LEN MU_); unfold U0_cmp_smBb.Wg; vdisj
    | |- forall _, munch _ _ _ -> u32arr _ _ (E + 51640)%Z _ => let m_ := fresh "m_" in let MU_ := fresh "MU_" in intros m_ MU_; apply (u32arr_munchU s0segs _ _ m_ _ _ LPK MU_); unfold U0_cmp_smBb.Wg; vdisj
    | |- frdW _ ?W' ?mm ?a _ =>
        first [ lazymatch goal with V : frdW _ _ _ a _ |- _ => eapply (frdW_sub s0segs _ W' _ mm); [exact V| exact MU| unfold Wit, U0_cmp_smBb.Wg; u_sub_fp] end
              | lazymatch goal with R : rw_cells _ mm a _ |- _ => apply frdW_intro; [exact R| unfold U0_cmp_smBb.Wg; cbn [disjoint_from]; simpl_sizes; Lib.Step.slia] end
              | idtac ]
    | |- (_ <= _)%nat => first [lia | idtac]
    | |- (_ < _)%nat => first [lia | idtac]
    | |- (_ <= _)%Z => first [lia | idtac]
    | |- (_ < _)%Z => first [lia | idtac]
    | |- (_ /\ _) => first [lia | idtac]
    | |- (@eq Z _ _) => first [lia | idtac]
    | |- _ => idtac
    end ].

  Lemma U0_sm_iterA : forall (k : nat) (J1 J2 J3 jc jf : list byte) (w896 w912 w920 w936 w976 w1024 : word) (m me : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word),
    (k < 4)%nat -> length J1 = 480%nat -> length J2 = 216%nat -> length J3 = 56%nat -> length jc = 12%nat -> length jf = 24%nat ->
    u8arr s0segs m A1 (zb8 arr1 ARR1_SIZE) ->
    u8arr s0segs m (E + 37708) (ovb (it_len (ITK k)) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 51640) (ovw (it_lp (ITK k)) (jseg J 51640 4128) 1032) ->
    u32arr s0segs m (E + 45448) (ovw (it_rfreq (ITK k)) (jseg J 45448 6192) 1548) ->
    u8arr s0segs m (E + 1704) (ovb (it_sel (ITK k)) (jseg J 1704 18002) 18002) ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells s0segs m (SP + 32) [C8 (Z_to_bv 64 (Z.of_nat k))] ->
    u8arr s0segs m (SP + 48) J1 -> u8arr s0segs m (SP + 584) J2 -> u8arr s0segs m (SP + 832) J3 ->
    rw_cells s0segs m (SP + 896) [C8 w896] -> rw_cells s0segs m (SP + 912) [C8 w912] -> rw_cells s0segs m (SP + 920) [C8 w920] ->
    rw_cells s0segs m (SP + 936) [C8 w936] -> rw_cells s0segs m (SP + 976) [C8 w976] -> rw_cells s0segs m (SP + 1024) [C8 w1024] ->
    u8arr s0segs m (SP + 1060) jf -> u8arr s0segs m (SP + 1084) jc ->
    mem_inv s0segs m -> munch Wit me m -> wmono s0segs me m ->
    frdW s0segs Wit me (SP + 24) [C8 (Z_to_bv 64 (flag6 nG))] -> frdW s0segs Wit me (SP + 40) [C8 (Z_to_bv 64 (4 * A))] ->
    frdW s0segs Wit me (SP + 528) [C8 (NOT (E + 38740))] -> frdW s0segs Wit me (SP + 536) [C8 (NOT (E + 38998))] ->
    frdW s0segs Wit me (SP + 544) [C8 (NOT (E + 38224))] -> frdW s0segs Wit me (SP + 552) [C8 (NOT (E + 38482))] ->
    frdW s0segs Wit me (SP + 560) [C8 (Z_to_bv 64 (E + 38998))] -> frdW s0segs Wit me (SP + 568) [C8 (NOT (E + 51640))] ->
    frdW s0segs Wit me (SP + 576) [C8 (NOT (E + 37966))] ->
    frdW s0segs Wit me (SP + 800) [C8 (Z_to_bv 64 18002)] -> frdW s0segs Wit me (SP + 808) [C8 (NOT (SP + 1060))] ->
    frdW s0segs Wit me (SP + 816) [C8 (Z_to_bv 64 (E + 1704))] -> frdW s0segs Wit me (SP + 824) [C8 (NOT (E + 1704))] ->
    frdW s0segs Wit me (SP + 904) [C8 (Z_to_bv 64 (flag6 nG))] -> frdW s0segs Wit me (SP + 928) [C8 (Z_to_bv 64 nG)] ->
    frdW s0segs Wit me (SP + 944) [C8 (NOT (E + 45448))] -> frdW s0segs Wit me (SP + 952) [C8 (Z_to_bv 64 (E + 45448))] ->
    frdW s0segs Wit me (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] -> frdW s0segs Wit me (SP + 968) [C8 (Z_to_bv 64 A)] ->
    frdW s0segs Wit me (SP + 992) [C8 (Z_to_bv 64 (E + 37708))] -> frdW s0segs Wit me (SP + 1000) [C8 (Z_to_bv 64 (E + 51640))] ->
    frdW s0segs Wit me (SP + 1008) [C8 (Z_to_bv 64 1)] -> frdW s0segs Wit me (SP + 1016) [C8 (Z_to_bv 64 1)] ->
    frdW s0segs Wit me (SP + 1032) [C8 (Z_to_bv 64 A1)] ->
    (forall m' (J1' J2' J3' jc' : list byte) (w896' w936' w1024' : word) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7' s8' s10' s11' t3' t4' t5' t6' : word),
      let s := ITK k in
      length J1' = 480%nat -> length J2' = 216%nat -> length J3' = 56%nat -> length jc' = 12%nat ->
      u8arr s0segs m' A1 (zb8 arr1 ARR1_SIZE) ->
      u8arr s0segs m' (E + 37708) (ovb (it_len s) (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 51640) (ovw (it_lpk e s) (jseg J 51640 4128) 1032) ->
      u32arr s0segs m' (E + 45448) (ovw (g_rfreq (Gend e s)) (jseg J 45448 6192) 1548) ->
      u8arr s0segs m' (E + 1704) (ovb (g_sel (Gend e s)) (jseg J 1704 18002) 18002) ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells s0segs m' (SP + 32) [C8 (Z_to_bv 64 (Z.of_nat k + 1))] ->
      u8arr s0segs m' (SP + 48) J1' -> u8arr s0segs m' (SP + 584) J2' -> u8arr s0segs m' (SP + 832) J3' ->
      rw_cells s0segs m' (SP + 896) [C8 w896'] -> rw_cells s0segs m' (SP + 912) [C8 (Z_to_bv 64 (g_totc (Gend e s)))] ->
      rw_cells s0segs m' (SP + 920) [C8 (Z_to_bv 64 nMTF)] ->
      rw_cells s0segs m' (SP + 936) [C8 w936'] -> rw_cells s0segs m' (SP + 976) [C8 (Z_to_bv 64 (g_nSel (Gend e s)))] ->
      rw_cells s0segs m' (SP + 1024) [C8 w1024'] ->
      u32arr s0segs m' (SP + 1060) (zw32 (g_fave (Gend e s)) 6) -> u8arr s0segs m' (SP + 1084) jc' ->
      mem_inv s0segs m' -> munch Wit me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RIT ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 0) (Z_to_bv 64 (-1548)) s7' s8' s10' s11' t3' t4' t5' t6')
                       F (Z_to_bv 64 0x1b36c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIT ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SP + 1084)) s5 s7 s8 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1745c) fc None m (seg_rom s0segs)).
  Proof.
    intros k J1 J2 J3 jc jf w896 w912 w920 w936 w976 w1024 m me ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s7 s8 s10 s11 t3 t4 t5 t6
           Hk LJ1 LJ2 LJ3 Ljc Ljf AR1 LEN LPK RFQ SEL EH2 C32 SP1 SP2 SP3 C896 C912 C920 C936 C976 C1024 FAV COST MI MU WM
           V24 V40 V528 V536 V544 V552 V560 V568 V576 V800 V808 V816 V824 V904 V928 V944 V952 V960 V968 V992 V1000 V1008 V1016 V1032 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. openF.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    pose proof CEP as CEP'. unfold CEIL in CEP'.
    pose proof SEP as SP'. unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in SP'. cbv zeta in SP'. destruct SP' as (AEA1 & _).
    cps_destruct (proj2 FACTS k Hk) as (BL & BP & BG & BM).
    cbv zeta in K. remember (ITK k) as s eqn:Es.
    unfold Wit in MU. unfold EHEAD2 in EH2.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply U0_sm_ihead with (f := it_fave s) (jf := jf) (mf := m)].
    all: iside MU AR1 LEN LPK.
    { st_eq. }
    clear FAV MI. intros m1 FAVE MI MU1 WM1.
    transport_after_call s0segs m m1 MU1 WM1. clear MU1 WM1.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply U0_sm_rfzo with (n := Z.to_nat nG) (t := 0%Z) (rf := it_rfreq s) (mf := m1)].
    all: iside MU AR1 LEN LPK.
    { st_eq. }
    clear RFQ MI. intros m2 ya0 ya1 ya2 ya3 ya4 RFQ MI MU2 WM2.
    transport_after_call s0segs m1 m2 MU2 WM2. clear MU2 WM2.
    change (sm_rfreq_zero (Z.to_nat nG) (it_rfreq s) A 0) with (it_rf0 e s) in RFQ.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply U0_sm_pre1 with (lp := it_lp s) (len := it_len s) (mf := m2)].
    all: iside MU AR1 LEN LPK.
    { st_eq. }
    clear LEN LPK MI. intros m3 za0 za1 za2 za3 za4 za5 LEN LPK MI MU3 WM3.
    transport_after_call s0segs m2 m3 MU3 WM3. clear MU3 WM3.
    change (if (nG =? 6)%Z then sm_lenpack (Z.to_nat A) (it_lp s) (it_len s) 0 else it_lp s) with (it_lpk e s) in LPK.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply U0_sm_pre2 with (w912 := w912) (w920 := w920) (w976 := w976) (w1024 := w1024) (mf := m3)].
    all: iside MU AR1 LEN LPK.
    { st_eq. }
    clear EH2 C912 C920 C976 C1024 MI. intros m4 xa0 EH2 C912 C920 C976 C1024 MI MU4 WM4. unfold EHEAD2 in EH2.
    transport_after_call s0segs m3 m4 MU4 WM4. clear MU4 WM4.
    (* [comment removed for export] *)
    assert (LPF : nG = 6%Z -> forall v j, (0 <= v < A)%Z -> (0 <= j < 3)%Z -> zdef (it_lpk e s) (4 * v + j) = true /\ (0 <= zget (it_lpk e s) (4 * v + j) < 2097152)%Z).
    { intros H6 v j Hv Hj. cps_destruct (BP H6 v j Hv Hj) as (D & _ & R). exact (conj D R). }
    eapply evt_eq; [| eapply U0_sm_gloop with (n := Z.to_nat (KSEL e)) (j := 0%nat) (s := s) (J1 := J1) (J2 := J2) (J3 := J3) (jc := jc) (lp := it_lpk e s) (len := it_len s)
                                             (v896 := w896) (v936 := w936) (me := m4)].
    all: iside MU AR1 LEN LPK.
    { st_eq. }
    all: try reflexivity.
    clear RFQ SEL SP1 SP2 SP3 C896 C912 C936 C976 C1024 FAVE COST MI.
    intros m5 J1' J2' J3' jc' v896' v936' w1024' ura u0 u1 u2 ua0 ua1 ua2 ua3 ua4 ua5 ua6 ua7 us2 us5 us7 us8 us10 us11 u3 u4 u5 u6
           LJ1' LJ2' LJ3' Ljc' RFQ SEL SP1' SP2' SP3' R896 R912 R936 R976 R1024 FAVE COST MI MU5 WM5.
    unfold U0_cmp_smBb.Wg in MU5. transport_after_call s0segs m4 m5 MU5 WM5. clear MU5 WM5.
    (* [comment removed for export] *)
    eapply evt_eq; [| eapply U0_sm_mid with (iter := Z.of_nat k) (w912 := Z_to_bv 64 (g_totc (Gend e s))) (mf := m5)].
    all: iside MU AR1 LEN LPK.
    { st_eq. }
    clear EH2 C32 MI. intros m6 xb0 xb1 xb3 EH2 C32 MI MU6 WM6.
    transport_after_call s0segs m5 m6 MU6 WM6. clear MU6 WM6.
    enter_with (K m6 J1' J2' J3' jc' v896' v936' w1024'); [st_eq| exact LJ1'| exact LJ2'| exact LJ3'| exact Ljc'| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption
      | exact C32| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| eassumption| exact MI| exact MU| exact WM].
  Qed.
End GZI.
End ACeilS1.
