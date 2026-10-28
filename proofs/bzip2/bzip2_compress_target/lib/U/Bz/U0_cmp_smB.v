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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpFsKit.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2 CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpHmKit CmpSmKit.
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
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.


Section U0SMB.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (ra gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (SP : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SF : smA_facts e.
  Hypothesis CEP : (CEIL <= SP)%Z. Hypothesis PHI : (SP + 1200 <= 18446744073709551616)%Z.
  Notation E := (c_E cx). Notation J := (c_J cx).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSP := (Z_to_bv 64 SP).
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  Notation MASK := (Z_to_bv 64 18446744071562067969).
  Notation Wlen := [(E + 37708, E + 39256)]%Z.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  Ltac poseV V RO := lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (V mm MU') as RO end.

  Notation RIu t0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 :=
    (mkR ra cSP gp tp t0 (Z_to_bv 64 258) (Z_to_bv 64 1) (Z_to_bv 64 E) s1 a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 6) s3 s4 s5 s6 (Z_to_bv 64 (A - 1)) (Z_to_bv 64 257) (NOT (E + 37708)) (Z_to_bv 64 (E + 672)) (NOT (E + 672))
         MASK (Z_to_bv 64 0) (Z_to_bv 64 3) (Z_to_bv 64 15)).

  Lemma U0_smA_grow : forall (f : nat) (ge aF gs tF remF : Z) (m : word -> option byte)
      (t0 s1 a5 a6 a7 s4 s6 : word),
    (A - 1 - ge < Z.of_nat f)%Z ->
    (0 <= gs)%Z -> (gs - 1 <= ge <= A - 1)%Z -> (aF < tF)%Z -> (0 < tF <= nMTF)%Z -> (0 <= aF <= remF)%Z ->
    aF = sumF (fun v => zget mf v) gs (Z.to_nat (ge + 1 - gs)) ->
    remF = sumF (fun v => zget mf v) gs (Z.to_nat (A - gs)) -> (remF <= nMTF)%Z ->
    u32arr s0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    (forall (ge' aF' : Z) (a4 a5 a6 : word),
      sm_grow f mf tF A ge aF = (ge', aF') -> (ge <= ge' <= A - 1)%Z -> aF' = sumF (fun v => zget mf v) gs (Z.to_nat (ge' + 1 - gs)) -> (0 <= aF' <= remF)%Z ->
      evt s0segs Q (MS (RIu t0 s1 (Z_to_bv 64 aF') (Z_to_bv 64 tF) (Z_to_bv 64 258) (Z_to_bv 64 A) a4 a5 a6 a7 (Z_to_bv 64 gs) s4 (Z_to_bv 64 ge') s6)
                       F (Z_to_bv 64 0x171a4) fc None m (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIu t0 s1 (Z_to_bv 64 aF) (Z_to_bv 64 tF) (Z_to_bv 64 258) (Z_to_bv 64 A) (Z_to_bv 64 (ge + 1)) a5 a6 a7 (Z_to_bv 64 gs) s4 (Z_to_bv 64 (A - 1)) s6)
                     F (Z_to_bv 64 0x17164) fc None m (seg_rom s0segs)).
  Proof.
    induction f as [|f IH]. { intros; lia. }
    intros ge aF gs tF remF m t0 s1 a5 a6 a7 s4 s6 Hf Hgs Hge HaF HtF BaF EaF EremF HremF MTF K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold CEIL in CEP. unfold sm_alpha, sm_nmtf in *.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    rewrite sm_grow_S in K.
    (* [comment removed for export] *)
    wstep; if_cases Kx; zify_cond_z Kx.
    { enter_with (K ge aF _ _ _); [st_eq| | lia| exact EaF| lia].
      replace ((aF <? tF) && (ge <? nInUse + 2 - 1))%Z%bool with false by (symmetry; apply Bool.andb_false_iff; right; apply Z.ltb_ge; lia). reflexivity. }
    replace ((aF <? tF) && (ge <? nInUse + 2 - 1))%Z%bool with true in K
      by (symmetry; apply Bool.andb_true_iff; split; apply Z.ltb_lt; lia).
    pose proof (MFD (ge + 1)%Z ltac:(lia)) as [Dq Rq].
    (* [comment removed for export] *)
    assert (EaF' : (aF + zget mf (ge + 1))%Z = sumF (fun v => zget mf v) gs (Z.to_nat (ge + 2 - gs))).
    { rewrite EaF. replace (Z.to_nat (ge + 2 - gs)) with (S (Z.to_nat (ge + 1 - gs))) by lia. rewrite sumF_S_last. f_equal. f_equal. lia. }
    assert (BaF' : (0 <= aF + zget mf (ge + 1) <= remF)%Z).
    { rewrite EaF', EremF. apply sumF_prefix_le; [lia|]. intros b Hb. apply (proj1 (proj2 (MFD b ltac:(lia)))). }
    (* [comment removed for export] *)
    urun.
    (* [comment removed for export] *)
    pose proof (ovw_read s0segs m (E + 672) mf (jseg J 672 1032) 258 (ge + 1) _ MTF ltac:(lia) Dq ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD. try rewrite (sx32_of_Z (zget mf (ge + 1))) by lia.
    (* [comment removed for export] *)
    wstep. wstep. try rewrite (sx32_of_Z (aF + zget mf (ge + 1))) by lia. urun_to 0x1719c%Z.
    try rewrite (sx32_of_Z (aF + zget mf (ge + 1))) by lia. try rewrite (sx32_of_Z (ge + 1 + 1)) by lia.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - enter_with (IH (ge + 1)%Z (aF + zget mf (ge + 1))%Z gs tF remF m); [st_eq| lia| lia| lia| lia| lia| lia| | exact EremF| lia| exact MTF|].
      + rewrite EaF'. f_equal. lia.
      + intros ge' aF' y4 y5 y6 E' Hge' EaF2 B2. eapply K; [exact E'| lia| exact EaF2| exact B2].
    - (* [comment removed for export] *)
      urun_to 0x171a4%Z. try rewrite (sx32_of_Z (ge + 1 + 1 + -1)) by lia. try rewrite (sx32_of_Z_signed (ge + 1 + 1 + -1)) by lia.
      enter_with (K (ge + 1)%Z (aF + zget mf (ge + 1))%Z _ _ _); [st_eq| | lia| | lia].
      + apply sm_grow_stop. lia.
      + rewrite EaF'. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma U0_smA_setrow : forall (n : nat) (v t gs ge : Z) (len : zarr) (me m : word -> option byte)
      (t0 a4 a5 a6 a7 s6 : word),
    (v + Z.of_nat n = A)%Z -> (0 <= v)%Z -> (1 <= n)%nat -> (0 <= t < 6)%Z ->
    (0 <= gs <= 258)%Z -> (gs - 1 <= ge <= 258)%Z ->
    u8arr s0segs m (E + 37708) (ovb len (jseg J 37708 1548) 1548) -> mem_inv s0segs m ->
    munch Wlen me m -> wmono s0segs me m ->
    frdW s0segs Wlen me (SP + 984) [C8 (Z_to_bv 64 A)] ->
    (forall m' (a1 a4 : word),
      u8arr s0segs m' (E + 37708) (ovb (sm_setrow n len t gs ge v) (jseg J 37708 1548) 1548) -> mem_inv s0segs m' ->
      munch Wlen me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RIu t0 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 t) a1 (Z_to_bv 64 (258 * t)) (NOT (E + 37708 + 258 * t)) a4 a5 a6 a7
                            (Z_to_bv 64 gs) (Z_to_bv 64 (t + 1)) (Z_to_bv 64 ge) s6)
                       F (Z_to_bv 64 0x172a0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIu t0 (Z_to_bv 64 (E + 37708 + 258 * t)) (Z_to_bv 64 t) (Z_to_bv 64 v) (Z_to_bv 64 (258 * t)) (NOT (E + 37708 + 258 * t)) a4 a5 a6 a7
                          (Z_to_bv 64 gs) (Z_to_bv 64 (t + 1)) (Z_to_bv 64 ge) s6)
                     F (Z_to_bv 64 0x17230) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros v t gs ge len me m t0 a4 a5 a6 a7 s6 Hv Hv0 Hn Ht Hgs Hge LEN MI MU WM V984 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold CEIL in CEP. unfold sm_alpha in *.
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length len (jseg J 37708 1548) 1548 ltac:(lia)) as LL.
    rewrite sm_setrow_S in K.
    pose proof (u8arr_store_ok s0segs m (E + 37708) _ (258 * t + v) _ LEN ltac:(rewrite ovb_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO.
    (* [comment removed for export] *)
    wstep; if_cases K1; zify_cond_z K1;
      [ urun_to 0x17288%Z | wstep; if_cases K2; zify_cond_z K2; [ urun_to 0x17288%Z | urun_to 0x1725c%Z ] ].
    all: wstep; store_addr (E + 37708 + (258 * t + v))%Z.
    3: change (Z_to_le_bytes 1 0) with (le1 (Z_to_bv 64 0)).
    all: ovb_store1 LEN (258 * t + v)%Z.
    all: lazymatch type of LEN with context [wr8 ?l0 ?i0 ?w] =>
           replace (wr8 l0 i0 w) with (zset l0 i0 (setrow_val gs ge v)) in LEN
             by (unfold wr8, setrow_val, BZ_LESSER_ICOST, BZ_GREATER_ICOST; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia;
                 destruct (Z.leb_spec gs v), (Z.leb_spec v ge); cbn [andb]; first [reflexivity| exfalso; lia]) end.
    (* [comment removed for export] *)
    3: wstep.
    all: wstep; poseV V984 RO; wstep; clear RO.
    all: wstep; if_cases Ke; zify_cond_z Ke;
      [ enter_with (IH (v + 1)%Z t gs ge (zset len (258 * t + v) (setrow_val gs ge v)) me);
          [st_eq| lia| lia| lia| lia| lia| lia| exact LEN| assumption| assumption| assumption| exact V984| exact K]
      | assert (n = 0)%nat by lia; subst n; cbn [sm_setrow] in K; urun_to 0x172a0%Z;
        enter_with (K _ _ _); [st_eq| exact LEN| assumption| assumption| assumption] ].
  Qed.

  (* [comment removed for export] *)
  Lemma u0_divw_lit : forall a b, (0 <= a < 2147483648)%Z -> (0 < b < 2147483648)%Z ->
    v_divw (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a / b).
  Proof.
    intros a b Ha Hb. unfold v_divw. rewrite !unsigned_lit by lia. unfold bv_wrap, bv_modulus.
    change (2 ^ Z.of_N 32)%Z with 4294967296%Z. rewrite (Z.mod_small b 4294967296%Z ltac:(lia)).
    replace (b =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite (swrap32_small a) by lia. rewrite (swrap32_small b) by lia. rewrite Z.quot_div_nonneg by lia.
    pose proof (Z.div_pos a b ltac:(lia) ltac:(lia)). pose proof (Z.div_le_upper_bound a b a ltac:(lia) ltac:(nia)).
    rewrite swrap32_small by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation smGROW := (U0_smA_grow).
  Notation smSETROW := (U0_smA_setrow).
  Lemma U0_smA_iloop : forall (n k : nat) (me m : word -> option byte)
      (t0 a1 a2 a3 a4 a5 a6 s4 s5 s6 : word),
    let s := sip_k e k in
    ip_nPart s = Z.of_nat n -> (1 <= n)%nat -> (Z.of_nat k + Z.of_nat n = nG)%Z ->
    u8arr s0segs m (E + 37708) (ovb (ip_len s) (jseg J 37708 1548) 1548) ->
    u32arr s0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    rw_cells s0segs m (E + 640) (EHEAD2 cx g e) -> mem_inv s0segs m ->
    munch Wlen me m -> wmono s0segs me m ->
    frdW s0segs Wlen me (SP + 928) [C8 (Z_to_bv 64 nG)] -> frdW s0segs Wlen me (SP + 960) [C8 (Z_to_bv 64 (E + 37708))] ->
    frdW s0segs Wlen me (SP + 968) [C8 (Z_to_bv 64 A)] -> frdW s0segs Wlen me (SP + 984) [C8 (Z_to_bv 64 A)] ->
    (forall m' (t0 a0 a1 a2 a3 a4 a5 a6 s4 s5 s6 : word), let s' := sip_k e (k + n) in
      u8arr s0segs m' (E + 37708) (ovb (ip_len s') (jseg J 37708 1548) 1548) ->
      u32arr s0segs m' (E + 672) (ovw mf (jseg J 672 1032) 258) ->
      rw_cells s0segs m' (E + 640) (EHEAD2 cx g e) -> mem_inv s0segs m' ->
      munch Wlen me m' -> wmono s0segs me m' ->
      evt s0segs Q (MS (RIu t0 (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))) a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (ip_remF s')) (Z_to_bv 64 (ip_gs s')) s4 s5 s6)
                       F (Z_to_bv 64 0x17338) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (RIu t0 (Z_to_bv 64 (E + 37708 + 258 * (ip_nPart s - 1))) (Z_to_bv 64 (ip_nPart s)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (ip_remF s)) (Z_to_bv 64 (ip_gs s)) s4 s5 s6)
                     F (Z_to_bv 64 0x17120) fc None m (seg_rom s0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros k me m t0 a1 a2 a3 a4 a5 a6 s4 s5 s6 s HnP Hn Hk LEN MTF EH2 MI MU WM V928 V960 V968 V984 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. unfold CEIL in CEP. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (IPK k ltac:(lia)) as IK. cbv zeta in IK. fold s in IK. cps_destruct IK as (EnP & Hgs & EremF & HremF).
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length_nat (ip_len s) (jseg J 37708 1548) 1548) as LLn.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    unfold EHEAD2 in EH2.
    set (nP := ip_nPart s) in *. set (gs := ip_gs s) in *. set (remF := ip_remF s) in *.
    (* [comment removed for export] *)
    destruct (ex_intro (fun t => t = (remF / nP)%Z) (remF / nP)%Z eq_refl) as [tF EtF].
    assert (HtF : (0 <= tF <= remF)%Z).
    { rewrite EtF. split; [apply Z.div_pos; lia|]. pose proof (Z.div_le_compat_l remF 1 nP ltac:(lia) ltac:(lia)) as Hd. rewrite Z.div_1_r in Hd. exact Hd. }
    change (id (tF = remF / nP)%Z) in EtF.
    (* [comment removed for export] *)
    wstep. try rewrite (sx32_of_Z_signed (gs + -1)) by lia. urun_to 0x17130%Z. wstep. rewrite (u0_divw_lit remF nP) by lia. replace (remF / nP)%Z with tF by exact EtF.
    assert (ADJ : forall ge1, ip_adj nG s ge1 = ((gs <? ge1) && negb (nP =? nG) && negb (nP =? 1) && ((nG - nP) mod 2 =? 1))%Z%bool) by (intros; reflexivity).
    set (ROW := (E + 37708 + 258 * (nP - 1))%Z) in *.
    (* [comment removed for export] *)
    assert (POSTADJ : forall ge1 aF1 ge2 aF2 (ya1 ya2 ya3 ya4 ya5 ya6 ys6 : word),
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z ->
        (ge2 = (if ip_adj nG s ge1 then ge1 - 1 else ge1))%Z -> (aF2 = (if ip_adj nG s ge1 then aF1 - zget mf ge1 else aF1))%Z ->
        (gs - 1 <= ge2 <= A - 1)%Z -> (0 <= aF2 <= remF)%Z ->
      evt s0segs Q (MS (RIu t0 (Z_to_bv 64 ROW) (Z_to_bv 64 aF2) ya1 ya2 ya3 ya4 ya5 ya6 (Z_to_bv 64 remF) (Z_to_bv 64 gs) (Z_to_bv 64 nP) (Z_to_bv 64 ge2) ys6)
                       F (Z_to_bv 64 0x17204) fc None m (seg_rom s0segs))).
    { intros ge1 aF1 ge2 aF2 ya1 ya2 ya3 ya4 ya5 ya6 ys6 EG Hge1 EaF1 BaF1 Ege2 EaF2 Hge2 BaF2.
      (* [comment removed for export] *)
      urun_to 0x1720c%Z.
      try rewrite (sx32_of_Z aF2) by lia.
      wstep; if_cases Kv; zify_cond_z Kv; [exfalso; lia|].
      (* [comment removed for export] *)
      pose proof (V968 m MU) as RO. wstep. clear RO. wstep; if_cases Ka; zify_cond_z Ka; [exfalso; lia|].
      pose proof (V960 m MU) as RO. urun_to 0x17230%Z. clear RO.
      subst ROW.
      enter_with (smSETROW (Z.to_nat A) 0 (nP - 1) gs ge2 (ip_len s) m m);
        [st_eq| lia| lia| lia| lia| lia| lia| exact LEN| exact MI| apply munch_refl| apply wmono_refl| |].
      { eapply (frdW_sub s0segs Wlen Wlen me m); [exact V984| exact MU| u_sub_fp]. }
      intros m2 za1 za4 LEN2 MI2 MU2 WM2. clear LEN MI. transport_after_call s0segs m m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      wstep. try rewrite (sx32_of_Z (ge2 + 1)) by lia. try rewrite (sx32_of_Z_signed (ge2 + 1)) by lia. wstep; u_guard.
      wstep. try rewrite (sx32_of_Z remF) by lia. wstep. wstep. try rewrite (sx32_of_Z (remF - aF2)) by lia. try rewrite (sx32_of_Z_signed (remF - aF2)) by lia.
      wstep; u_guard. wstep.
      (* [comment removed for export] *)
      assert (Es' : sip_k e (S k) = SIP (sm_setrow (Z.to_nat A) (ip_len s) (nP - 1) gs ge2 0) (nP - 1) (remF - aF2) (ge2 + 1)).
      { rewrite sip_k_S. fold s. rewrite (sm_init_iter_spec mf nG A s ge1 aF1).
        2:{ unfold id in EtF. subst nP gs remF. rewrite <- EtF. exact EG. }
        cbv zeta. subst nP gs remF. rewrite <- Ege2, <- EaF2. reflexivity. }
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        pose proof (IH (S k)) as IH'. cbv zeta in IH'. rewrite Es' in IH'. cbn [ip_nPart ip_remF ip_gs ip_len] in IH'.
        enter_with (IH' me m2);
          [st_eq| lia| lia| lia| exact LEN2| assumption| assumption| exact MI2| assumption| assumption| exact V928| exact V960| exact V968| exact V984|].
        intros m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10. replace (S k + n)%nat with (k + S n)%nat by lia. exact (K m' y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10).
      - (* [comment removed for export] *)
        assert (n = 0)%nat by lia. subst n. urun_to 0x17338%Z.
        pose proof K as K'. cbv zeta in K'. replace (k + 1)%nat with (S k) in K' by lia. rewrite Es' in K'. cbn [ip_nPart ip_remF ip_gs ip_len] in K'.
        enter_with (K' m2); [st_eq| exact LEN2| assumption| assumption| exact MI2| assumption| assumption]. }
    (* [comment removed for export] *)
    assert (POSTGROW2 : forall ge1 aF1 (xa1 xa2 xa3 xa4 xa5 xa6 xs6 : word),
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z -> (gs < ge1)%Z ->
      evt s0segs Q (MS (RIu t0 (Z_to_bv 64 ROW) (Z_to_bv 64 aF1) xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 remF) (Z_to_bv 64 gs) (Z_to_bv 64 nP) (Z_to_bv 64 ge1) xs6)
                       F (Z_to_bv 64 0x171b4) fc None m (seg_rom s0segs))).
    { intros ge1 aF1 xa1 xa2 xa3 xa4 xa5 xa6 xs6 EG Hge1 EaF1 BaF1 Hlt.
      (* [comment removed for export] *)
      pose proof (V928 m MU) as RO. wstep. clear RO. wstep; if_cases K2; zify_cond_z K2.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (nP =? nG)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          destruct (gs <? ge1)%Z; reflexivity. }
      (* [comment removed for export] *)
      wstep; if_cases K1; zify_cond_z K1.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (nP =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          destruct (gs <? ge1)%Z, (nP =? nG)%Z; reflexivity. }
      (* [comment removed for export] *)
      pose proof (V928 m MU) as RO. wstep. clear RO. wstep. try rewrite (sx32_of_Z (nG - nP)) by lia. try rewrite (sx32_of_Z_signed (nG - nP)) by lia.
      wstep.
      try rewrite (land_mask31 (nG - nP)) by lia.
      destruct (ex_intro (fun p => p = ((nG - nP) mod 2)%Z) ((nG - nP) mod 2)%Z eq_refl) as [par Epar].
      assert (Hpar : (0 <= par <= 1)%Z) by (rewrite Epar; Z.div_mod_to_equations; lia).
      rewrite <- Epar. change (id (par = (nG - nP) mod 2)%Z) in Epar.
      (* [comment removed for export] *)
      wstep; if_cases K4; zify_cond_z K4.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); unfold id in Epar; rewrite <- Epar;
          replace (par =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia);
          destruct (gs <? ge1)%Z, (nP =? nG)%Z, (nP =? 1)%Z; reflexivity. }
      (* [comment removed for export] *)
      assert (AT : ip_adj nG s ge1 = true).
      { rewrite (ADJ ge1). unfold id in Epar. rewrite <- Epar. replace (gs <? ge1)%Z with true by (symmetry; apply Z.ltb_lt; lia).
        replace (nP =? nG)%Z with false by (symmetry; apply Z.eqb_neq; lia). replace (nP =? 1)%Z with false by (symmetry; apply Z.eqb_neq; lia).
        replace (par =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia). reflexivity. }
      pose proof (MFD ge1 ltac:(lia)) as [Dg Rg].
      assert (BaF2 : (0 <= aF1 - zget mf ge1)%Z).
      { rewrite EaF1. replace (Z.to_nat (ge1 + 1 - gs)) with (S (Z.to_nat (ge1 - gs))) by lia. rewrite sumF_S_last.
        replace (gs + Z.of_nat (Z.to_nat (ge1 - gs)))%Z with ge1 by lia.
        pose proof (sumF_nonneg (Z.to_nat (ge1 - gs)) (fun v => zget mf v) gs ltac:(intros b Hb; apply (proj1 (proj2 (MFD b ltac:(lia)))))). lia. }
      (* [comment removed for export] *)
      urun.
      pose proof (ovw_read s0segs m (E + 672) mf (jseg J 672 1032) 258 ge1 _ MTF ltac:(lia) Dg ltac:(unfold wa; f_equal; lia)) as RD.
      (* [comment removed for export] *)
      wstep. clear RD. try rewrite (sx32_of_Z (zget mf ge1)) by lia.
      wstep. wstep. try rewrite (sx32_of_Z (aF1 - zget mf ge1)) by lia. try rewrite (sx32_of_Z_signed (aF1 - zget mf ge1)) by lia.
      wstep; u_guard. wstep. try rewrite (sx32_of_Z_signed (ge1 + -1)) by lia. try rewrite (sx32_of_Z (ge1 + -1)) by lia. wstep.
      enter_with (POSTADJ ge1 aF1 (ge1 - 1)%Z (aF1 - zget mf ge1)%Z _ _ _ _ _ _ _); [st_eq| exact EG| lia| exact EaF1| lia| rewrite AT; reflexivity| rewrite AT; reflexivity| lia| lia]. }
    (* [comment removed for export] *)
    assert (POSTGROW : forall (pcx ge1 aF1 : Z) (xa1 xa2 xa3 xa4 xa5 xa6 xs6 : word),
      (pcx = 0x171a4 \/ pcx = 0x171b0)%Z ->
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z ->
      evt s0segs Q (MS (RIu t0 (Z_to_bv 64 ROW) (Z_to_bv 64 aF1) xa1 xa2 xa3 xa4 xa5 xa6 (Z_to_bv 64 remF) (Z_to_bv 64 gs) (Z_to_bv 64 nP) (Z_to_bv 64 ge1) xs6)
                       F (Z_to_bv 64 pcx) fc None m (seg_rom s0segs))).
    { intros pcx ge1 aF1 xa1 xa2 xa3 xa4 xa5 xa6 xs6 Hpc EG Hge1 EaF1 BaF1.
      destruct Hpc as [-> | ->]; wstep; if_cases K3; zify_cond_z K3.
      - eapply (POSTGROW2 ge1 aF1); [exact EG| lia| exact EaF1| exact BaF1| lia].
      - urun_to 0x17204%Z. eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1);
          replace (gs <? ge1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity.
      - eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1);
          replace (gs <? ge1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity.
      - eapply (POSTGROW2 ge1 aF1); [exact EG| lia| exact EaF1| exact BaF1| lia]. }
    (* [comment removed for export] *)
    assert (E0 : 0%Z = sumF (fun v => zget mf v) gs (Z.to_nat (gs - 1 + 1 - gs))) by (replace (Z.to_nat (gs - 1 + 1 - gs)) with 0%nat by lia; reflexivity).
    wstep; if_cases K5; zify_cond_z K5.
    { wstep. eapply (POSTGROW 0x171b0%Z (gs - 1)%Z 0%Z); [right; reflexivity| apply sm_grow_stop; lia| lia| exact E0| lia]. }
    (* [comment removed for export] *)
    urun_to 0x17140%Z.
    wstep; if_cases K7; zify_cond_z K7; [exfalso; lia|]. wstep. wstep. wstep. wstep; if_cases K8; zify_cond_z K8; [exfalso; lia|].
    wstep. wstep. wstep. try rewrite (sx32_of_Z (A - 1 + 1)) by lia. try rewrite (sx32_of_Z_signed (A - 1 + 1)) by lia. wstep.
    enter_with (smGROW 260%nat (gs - 1)%Z 0%Z gs tF remF m);
      [st_eq| lia| lia| lia| lia| lia| lia| exact E0| exact EremF| lia| exact MTF|].
    intros ge' aF' y4 y5 y6 EG' Hge' EaF' BaF'. eapply (POSTGROW 0x171a4%Z ge' aF'); [left; reflexivity| exact EG'| lia| exact EaF'| exact BaF'].
  Qed.
End U0SMB.
End ACeilS1.
