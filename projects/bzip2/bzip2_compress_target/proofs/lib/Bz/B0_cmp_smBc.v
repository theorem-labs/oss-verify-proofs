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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit CmpCutSmB BzCFactsSmB BzCSmF1 BzCFactsSmB2 CmpSmKit CmpSmKit2.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV B0_cmp_sdV B0_cmp_smV.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section GIB.
  Variables (cx : cctx) (e : est) (g : eg) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO FV : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis GM : g_mtf g = true.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis COL : (0 < CO)%Z. Hypothesis COH : (CO + 12 <= CEIL)%Z. Hypothesis FVL : (0 < FV)%Z. Hypothesis FVH : (FV + 24 <= CEIL)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HNG : (2 <= nG <= 6)%Z. Hypothesis HM : (1 <= nMTF <= (NBLOCKMAX + 20))%Z.
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
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
  Ltac lit_store4 :=
    lazymatch goal with
    | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v))
    | _ => idtac
    end.

  (* [comment removed for export] *)
  Notation ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s10 t3 t4 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (258 * nG)) s4 (Z_to_bv 64 1032) (Z_to_bv 64 1548) (Z_to_bv 64 (4 * A)) (Z_to_bv 64 257)
         (Z_to_bv 64 CO) s10 (Z_to_bv 64 (CO + 12)) t3 t4 (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (-9))).
  (* [comment removed for export] *)
  Notation HIT v32 v48 v56 v88 v20 v28 :=
    (sd_hi cx nG (SDW (Z_to_bv 64 FV) (Z_to_bv 64 (1032 * nG)) (Z_to_bv 64 A) (Z_to_bv 64 (E + 37708)) v32 v48 v56 (Z_to_bv 64 (E + 37708)) v88 (NOT (E + 45448)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 A) v20 v28)).
  Ltac openHI H := unfold sd_hi in H; cbv zeta in H; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528] in H.
  (* [comment removed for export] *)
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.
  Notation ROWF t := (E + 45448 + 1032 * t)%Z.
  Lemma zfill0_S : forall n a i, zfill0 (S n) a i = zfill0 n (zset a i 0) (i + 1)%Z. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wfv := [(FV, FV + 24)]%Z.
  Lemma B0_sm_ihead : forall (f : zarr) (jf : list byte) (v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    length jf = 24%nat -> u8arr b0segs m FV jf ->
    mem_inv b0segs m -> munch Wfv mf m -> wmono b0segs mf m ->
    frdW b0segs Wfv mf (P + 128) [C8 (Z_to_bv 64 (E + 51640))] -> frdW b0segs Wfv mf (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    (forall m',
      u32arr b0segs m' FV (zw32 (zero6 f) 6) ->
      mem_inv b0segs m' -> munch Wfv mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (ITR (Z_to_bv 64 (E + 51640)) t0 t1 t2 (Z_to_bv 64 (FV + 24)) (Z_to_bv 64 0) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (E + 45448)) a4 a5 a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                       F (Z_to_bv 64 0x8c4a4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (FV + 24)) s10 t3 t4)
                     F (Z_to_bv 64 0x8c480) fc None m (seg_rom b0segs)).
  Proof.
    intros f jf v32 v48 v56 v88 v20 v28 m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 LJf FAV MI MU WM V128 VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. pose proof FVH as FVH'. unfold CEIL in FVH'. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    cps_destruct (fave_cells_of_junk6 b0segs m FV jf FAV LJf) as (f1 & f2 & f3 & f4 & f5 & f6 & FC). clear FAV.
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. wstep. clear RO.
    do 5 ((wstep; lit_store4; try mem_after_store); wstep; wstep; if_cases Kl; zify_cond_z Kl; [clear Kl| exfalso; lia]).
    (wstep; lit_store4; try mem_after_store). wstep. wstep; if_cases Kl; zify_cond_z Kl; [exfalso; lia| clear Kl].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (fave_zero_cells6 b0segs mm FV f FC) as FAVE end. clear FC.
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. poseV V128 RO2. wstep. wstep. wstep. wstep. wstep. clear RO RO2.
    enter_with (K _); [st_eq| exact FAVE| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  Lemma B0_sm_rfzi : forall (n : nat) (t v : Z) (rf : zarr) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a6 a7 s10 t3 t4 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < nG)%Z ->
    u32arr b0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    mem_inv b0segs m -> munch Wrf mf m -> wmono b0segs mf m ->
    shzW b0segs Wrf mf E (E + ESTATE_SIZE) ->
    (forall m' (a0 a6 : word),
      u32arr b0segs m' (E + 45448) (ovw (zfill0 n rf (258 * t + v)) (jseg J 45448 6192) 1548) ->
      mem_inv b0segs m' -> munch Wrf mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (ITR ra t0 t1 t2 a0 (Z_to_bv 64 t) (Z_to_bv 64 (ROWF t)) (Z_to_bv 64 (ROWF t)) (Z_to_bv 64 (4 * A)) (NOT (ROWF t)) a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                       F (Z_to_bv 64 0x8c520) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR ra t0 t1 t2 a0 (Z_to_bv 64 t) (Z_to_bv 64 (ROWF t)) (Z_to_bv 64 (ROWF t)) (Z_to_bv 64 (4 * v)) (NOT (ROWF t)) a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                     F (Z_to_bv 64 0x8c4d8) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t v rf m mf ra t0 t1 t2 a0 a6 a7 s10 t3 t4 Hv Hv0 Hn Ht RFQ MI MU WM SHe K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rf (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    rewrite zfill0_S in K. replace (258 * t + v + 1)%Z with (258 * t + (v + 1))%Z in K by lia.
    (* [comment removed for export] *)
    brun_to 0x8c504%Z.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u32arr_store_ok b0segs mm (E + 45448) _ (258 * t + v) _ RFQ ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO end.
    wstep. lit_store4. store_addr (E + 45448 + 4 * (258 * t + v))%Z. ovw_store RFQ (258 * t + v)%Z 0%Z (rewrite unsigned_lit by lia; reflexivity).
    (* [comment removed for export] *)
    wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH t (v + 1)%Z _ _ mf); [st_eq| lia| lia| lia| lia| exact RFQ| assumption| assumption| assumption| unfold ESTATE_SIZE; exact SHe| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [zfill0] in K. wstep.
      enter_with (K _ _ _); [st_eq| exact RFQ| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_rfzo : forall (n : nat) (t : Z) (rf : zarr) (v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a4 a5 a6 a7 s10 t3 t4 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
    u32arr b0segs m (E + 45448) (ovw rf (jseg J 45448 6192) 1548) ->
    mem_inv b0segs m -> munch Wrf mf m -> wmono b0segs mf m ->
    shzW b0segs Wrf mf E (E + ESTATE_SIZE) ->
    frdW b0segs Wrf mf (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    (forall m' (a0 a4 a5 a6 : word),
      u32arr b0segs m' (E + 45448) (ovw (sm_rfreq_zero n rf A t) (jseg J 45448 6192) 1548) ->
      mem_inv b0segs m' -> munch Wrf mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (ITR ra t0 t1 t2 a0 (Z_to_bv 64 nG) (Z_to_bv 64 (ROWF nG)) (Z_to_bv 64 (ROWF nG)) a4 a5 a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                       F (Z_to_bv 64 0x8c534) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR ra t0 t1 t2 a0 (Z_to_bv 64 t) (Z_to_bv 64 (ROWF t)) (Z_to_bv 64 (ROWF t)) a4 a5 a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                     F (Z_to_bv 64 0x8c4a4) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros t rf v32 v48 v56 v88 v20 v28 m mf ra t0 t1 t2 a0 a4 a5 a6 a7 s10 t3 t4 Ht Ht0 Hn RFQ MI MU WM SHe VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    rewrite sm_rfreq_zero_S in K.
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. wstep. wstep; if_cases K0; zify_cond_z K0; [exfalso; lia|].
    (* [comment removed for export] *)
    brun_to 0x8c4d8%Z. clear RO.
    enter_with (B0_sm_rfzi (Z.to_nat A) t 0 rf m m);
      [st_eq| lia| lia| lia| lia| exact RFQ| exact MI| apply munch_refl| apply wmono_refl| |].
    { eapply (shzW_sub b0segs Wrf Wrf mf m); [exact SHe| exact MU| a_sub_fp| lia| unfold ESTATE_SIZE; lia]. }
    clear RFQ MI. intros m1 ya0 ya6 RFQ MI MU1 WM1.
    transport_after_call b0segs m m1 MU1 WM1. clear MU1 WM1.
    replace (258 * t + 0)%Z with (258 * t)%Z in RFQ by lia.
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. wstep. wstep. wstep. wstep. clear RO. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (t + 1)%Z _ v32 v48 v56 v88 v20 v28 m1 mf); [st_eq| lia| lia| lia| exact RFQ| exact MI| assumption| assumption| exact SHe| exact VHI| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_rfreq_zero] in K.
      enter_with (K m1 _ _ _ _); [st_eq| exact RFQ| exact MI| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  Notation Wlp := [(E + 51640, E + 55768)]%Z.
  Lemma B0_sm_lpk : forall (n : nat) (v : Z) (lp len : zarr) (v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a6 a7 s10 t3 t4 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat ->
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr b0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr b0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    mem_inv b0segs m -> munch Wlp mf m -> wmono b0segs mf m ->
    shzW b0segs Wlp mf E (E + ESTATE_SIZE) ->
    frdW b0segs Wlp mf (P + 1264) (sm_set cx FV) -> frdW b0segs Wlp mf (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    (forall m' (a0 a1 a2 a3 a6 a7 : word),
      u8arr b0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr b0segs m' (E + 51640) (ovw (sm_lenpack n lp len v) (jseg J 51640 4128) 1032) ->
      mem_inv b0segs m' -> munch Wlp mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (ITR (Z_to_bv 64 (E + 51640)) t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (16 * A)) (Z_to_bv 64 A) a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                       F (Z_to_bv 64 0x8c774) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR (Z_to_bv 64 (E + 51640)) t0 t1 t2 a0 a1 a2 a3 (Z_to_bv 64 (16 * v)) (Z_to_bv 64 v) a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                     F (Z_to_bv 64 0x8c554) fc None m (seg_rom b0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v lp len v32 v48 v56 v88 v20 v28 m mf t0 t1 t2 a0 a1 a2 a3 a6 a7 s10 t3 t4 Hv Hv0 Hn LF LEN LPK MI MU WM SHe VSET VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ6. pose proof (ovb_length_nat len (jseg J 37708 1548) 1548) as LL.
    pose proof (jseg_length J 51640 4128 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ9. pose proof (ovw_length_nat lp (jseg J 51640 4128) 1032) as LLP.
    rewrite sm_lenpack_S in K. rewrite !lenpack_word_eq in K by (lazymatch goal with |- (0 <= zget _ (258 * ?t + _))%Z => exact (proj1 (proj2 (LF t v ltac:(lia) ltac:(lia)))) end).
    (* [comment removed for export] *)
    Ltac lprowB VSET VHI LEN LPK LF len v thi tlo ih il j :=
      let Dh := fresh "Dh" in let Rh := fresh "Rh" in let Dl := fresh "Dl" in let Rl := fresh "Rl" in let RD := fresh "RD" in let RO1 := fresh "RO" in let RO2 := fresh "RO" in
      destruct (LF thi v ltac:(lia) ltac:(lia)) as [Dh Rh]; destruct (LF tlo v ltac:(lia) ltac:(lia)) as [Dl Rl];
      replace (258 * thi + v)%Z with ih in Dh, Rh by lia; replace (258 * tlo + v)%Z with il in Dl, Rl by lia;
      poseV VSET RO1; unfold sm_set in RO1; cbv zeta in RO1; poseV VHI RO2; openHI RO2;
      brun;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovb_read1 b0segs mm (E + 37708) _ (jseg J 37708 1548) 1548 ih _ LEN ltac:(lia) Dh ltac:(unfold wa; f_equal; lia)) as RD end;
      lstep; clear RD; cbv beta; rewrite ?unsigned_lit8 by lia;
      brun;
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        pose proof (ovb_read1 b0segs mm (E + 37708) _ (jseg J 37708 1548) 1548 il _ LEN ltac:(lia) Dl ltac:(unfold wa; f_equal; lia)) as RD end;
      lstep; clear RD; cbv beta; rewrite ?unsigned_lit8 by lia;
      brun; clear RO1 RO2;
      pose proof (lenpack_word_range (zget len il) (zget len ih) ltac:(lia) ltac:(lia));
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        lazymatch type of LPK with u32arr _ _ _ (ovw ?lpx _ _) =>
        pose proof (u32arr_store_ok b0segs mm (E + 51640) _ (4 * v + j) _ LPK ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
        lstep; store_addr (E + 51640 + 4 * (4 * v + j))%Z;
        ovw_store LPK (4 * v + j)%Z (Z.lor (zget len ih * 65536) (zget len il)) (rewrite unsigned_lit by lia; reflexivity) end end.
    replace (258 * 1 + v)%Z with (258 + v)%Z in K by lia. replace (258 * 0 + v)%Z with v in K by lia.
    replace (258 * 3 + v)%Z with (774 + v)%Z in K by lia. replace (258 * 2 + v)%Z with (516 + v)%Z in K by lia.
    replace (258 * 5 + v)%Z with (1290 + v)%Z in K by lia. replace (258 * 4 + v)%Z with (1032 + v)%Z in K by lia.
    lprowB VSET VHI LEN LPK LF len v 1%Z 0%Z (258 + v)%Z v 0%Z. replace (4 * v + 0)%Z with (4 * v)%Z in LPK by lia.
    lprowB VSET VHI LEN LPK LF len v 3%Z 2%Z (774 + v)%Z (516 + v)%Z 1%Z.
    lprowB VSET VHI LEN LPK LF len v 5%Z 4%Z (1290 + v)%Z (1032 + v)%Z 2%Z.
    (* [comment removed for export] *)
    poseV VHI RO. openHI RO. wstep. wstep. clear RO. wstep; if_cases Ke; zify_cond_z Ke.
    - enter_with (IH (v + 1)%Z _ len v32 v48 v56 v88 v20 v28 _ mf); [st_eq| lia| lia| lia| exact LF| exact LEN| exact LPK| assumption| assumption| assumption| unfold ESTATE_SIZE; exact SHe| exact VSET| exact VHI| exact K].
    - assert (n = 0)%nat by lia. subst n. cbn [sm_lenpack] in K. wstep.
      enter_with (K _ _ _ _ _ _ _); [st_eq| exact LEN| exact LPK| assumption| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_sm_pre1 : forall (lp len : zarr) (v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    (forall t v, 0 <= t < 6 -> 0 <= v < A -> zdef len (258 * t + v) = true /\ 0 <= zget len (258 * t + v) <= 17)%Z ->
    u8arr b0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
    u32arr b0segs m (E + 51640) (ovw lp (jseg J 51640 4128) 1032) ->
    mem_inv b0segs m -> munch Wlp mf m -> wmono b0segs mf m ->
    shzW b0segs Wlp mf E (E + ESTATE_SIZE) ->
    frdW b0segs Wlp mf (P + 72) [C8 (Z_to_bv 64 (flag6 nG))] ->
    frdW b0segs Wlp mf (P + 1264) (sm_set cx FV) -> frdW b0segs Wlp mf (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    (forall m' (a0 a1 a2 a3 a4 a5 a6 a7 : word),
      u8arr b0segs m' (E + 37708) (ovb len (jseg J 37708 1548) 1548) ->
      u32arr b0segs m' (E + 51640) (ovw (if (nG =? 6)%Z then sm_lenpack (Z.to_nat A) lp len 0 else lp) (jseg J 51640 4128) 1032) ->
      mem_inv b0segs m' -> munch Wlp mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (ITR (Z_to_bv 64 (E + 51640)) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                       F (Z_to_bv 64 0x8c774) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR (Z_to_bv 64 (E + 51640)) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                     F (Z_to_bv 64 0x8c534) fc None m (seg_rom b0segs)).
  Proof.
    intros lp len v32 v48 v56 v88 v20 v28 m mf t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 LF LEN LPK MI MU WM SHe V72 VSET VHI K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    assert (Hf6 : (0 <= flag6 nG <= 1)%Z) by (unfold flag6; destruct (nG =? 6)%Z; lia).
    (* [comment removed for export] *)
    poseV V72 RO. wstep. clear RO. wstep; if_cases Kf; zify_cond_z Kf; unfold flag6 in Kf.
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [exfalso; lia|].
      enter_with (K m _ _ _ _ _ _ _ _); [st_eq| exact LEN| exact LPK| exact MI| exact MU| exact WM].
    - destruct (Z.eqb_spec nG 6) as [E6|N6]; [| exfalso; lia].
      (* [comment removed for export] *)
      poseV VHI RO. openHI RO. brun_to 0x8c554%Z. clear RO.
      enter_with (B0_sm_lpk (Z.to_nat A) 0 lp len v32 v48 v56 v88 v20 v28 m m);
        [st_eq| lia| lia| lia| exact LF| exact LEN| exact LPK| exact MI| apply munch_refl| apply wmono_refl| | | |].
      { eapply (shzW_sub b0segs Wlp Wlp mf m); [exact SHe| exact MU| a_sub_fp| lia| unfold ESTATE_SIZE; lia]. }
      { eapply (frdW_sub b0segs Wlp Wlp mf m); [exact VSET| exact MU| a_sub_fp]. }
      { eapply (frdW_sub b0segs Wlp Wlp mf m); [exact VHI| exact MU| a_sub_fp]. }
      clear LEN LPK MI. intros m' ya0 ya1 ya2 ya3 ya6 ya7 LEN LPK MI MU' WM'.
      transport_after_call b0segs m m' MU' WM'. clear MU' WM'.
      enter_with (K m' _ _ _ _ _ _ _ _); [st_eq| exact LEN| exact LPK| exact MI| assumption| assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation Wp2 := [(P + 1384, P + 1568)]%Z.
  Lemma B0_sm_pre2 : forall (v32 v48 v56 v88 v20 v28 : word) (m mf : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 : word),
    rw_cells b0segs m (E + 640) (EHEAD2 cx g e) ->
    rw_cells b0segs m (P + 1384) (HIT v32 v48 v56 v88 v20 v28) ->
    mem_inv b0segs m -> munch Wp2 mf m -> wmono b0segs mf m ->
    shzW b0segs Wp2 mf E (E + ESTATE_SIZE) ->
    frdW b0segs Wp2 mf (P + 88) [C8 (Z_to_bv 64 (SHE + 83))] -> frdW b0segs Wp2 mf (P + 96) [C8 (Z_to_bv 64 (E + 668))] ->
    (forall m',
      rw_cells b0segs m' (E + 640) (EHEAD2 cx g e) ->
      rw_cells b0segs m' (P + 1384) (HIT v32 (Z_to_bv 64 0) (Z_to_bv 64 nMTF) v88 (Z_to_bv 64 0) v28) ->
      mem_inv b0segs m' -> munch Wp2 mf m' -> wmono b0segs mf m' ->
      evt b0segs Q (MS (ITR ra t0 t1 t2 (Z_to_bv 64 nMTF) a1 a2 a3 (Z_to_bv 64 0) a5 a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                       F (Z_to_bv 64 0x8c7a4) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (ITR ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 258) s10 t3 t4)
                     F (Z_to_bv 64 0x8c774) fc None m (seg_rom b0segs)).
  Proof.
    intros v32 v48 v56 v88 v20 v28 m mf ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 EH2 HI MI MU WM SHe V88 V96 K.
    openCX. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb. unfold CEIL in CEP. unfold ESTATE_SIZE in SHe.
    assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity. assert (HMd : nMTF = e_nMTF e) by reflexivity.
    openHI HI. unfold EHEAD2 in EH2. rewrite GM in EH2.
    (* [comment removed for export] *)
    poseV V88 RO. poseV V96 RO2. brun_to 0x8c78c%Z. clear RO RO2.
    try rewrite (sx32_of_Z (e_nMTF e)) by (change (2^31)%Z with 2147483648%Z; lia).
    (* [comment removed for export] *)
    wstep; lit_store. wstep; if_cases Kp; zify_cond_z Kp; [| exfalso; lia].
    wstep. wstep; lit_store. wstep; lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm); [st_eq| unfold EHEAD2; rewrite GM; assumption| unfold sd_hi; cbv zeta; cbn [w1400 w1408 w1416 w1424 w1432 w1448 w1456 w1472 w1488 w1496 w1504 w1512 w1520 w1528]; assumption| assumption| assumption| assumption] end.
  Qed.
End GIB.
End ACeilS1.
