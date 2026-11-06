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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA BzCFactsSmA CmpFsKit CmpHmKit.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smA.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section A0SMB.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE : Z).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis SF : smA_facts e.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation mf := (e_mtfFreq e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e). Notation nInUse := (e_nInUse e).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  Ltac openSF :=
    let H := fresh "SFL" in pose proof SF as H; unfold smA_facts in H; cbv zeta in H; cps_destruct H as (?NI & ?NM & ?MFD & ?IPK & ?IPT).
  (* [comment removed for export] *)

  Notation RI ra a0 a1 a2 a3 a4 a5 a6 s2 s3 s5 s7 s8 s9 s11 t6 :=
    (mkR ra cP gp tp (Z_to_bv 64 E) (Z_to_bv 64 (E + 672)) (Z_to_bv 64 (E + 676)) s0 cP a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 nInUse)
         s2 s3 cSB s5 (Z_to_bv 64 (E + 668)) s7 s8 s9 (Z_to_bv 64 1) s11 (Z_to_bv 64 3) (Z_to_bv 64 (-1)) (Z_to_bv 64 (-2147483647)) t6).
  Notation Wlen := [(E + 37708, E + 39256)]%Z.
  Notation smGROW := (A0_smA_grow cx e Q gp tp s0 F fc P CX SF).
  Notation smSETROW := (A0_smA_setrow cx e Q gp tp s0 F fc P CX SF).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_smA_iloop : forall (n k : nat) (me m : word -> option byte)
      (ra a1 a2 a3 a4 a5 a6 s2 s3 s8 t6 : word),
    let s := sip_k e k in
    ip_nPart s = Z.of_nat n -> (1 <= n)%nat -> (Z.of_nat k + Z.of_nat n = nG)%Z ->
    u8arr a0segs m (E + 37708) (ovb (ip_len s) (jseg J 37708 1548) 1548) ->
    u32arr a0segs m (E + 672) (ovw mf (jseg J 672 1032) 258) ->
    rw_cells a0segs m (E + 640) (EHEAD2 cx g e) -> mem_inv a0segs m ->
    munch Wlen me m -> wmono a0segs me m ->
    shzW a0segs Wlen me E (E + ESTATE_SIZE) ->
    frdW a0segs Wlen me (P + 128) [C8 (Z_to_bv 64 (SHE + 82))] -> frdW a0segs Wlen me (P + 136) [C8 (Z_to_bv 64 (E + 656))] ->
    frdW a0segs Wlen me (P + 200) [C8 (Z_to_bv 64 nG)] ->
    frdW a0segs Wlen me (P + 1416) [C8 (Z_to_bv 64 A)] ->
    (forall m' (a1 a2 a3 a4 a5 a6 s2 s3 s8 : word), let s' := sip_k e (k + n) in
      u8arr a0segs m' (E + 37708) (ovb (ip_len s') (jseg J 37708 1548) 1548) ->
      u32arr a0segs m' (E + 672) (ovw mf (jseg J 672 1032) 258) ->
      rw_cells a0segs m' (E + 640) (EHEAD2 cx g e) -> mem_inv a0segs m' ->
      munch Wlen me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (RI ra (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 s2 s3 (Z_to_bv 64 (ip_remF s')) (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))) s8 (Z_to_bv 64 (E + 37708 + 258 * (0 - 1))) (Z_to_bv 64 (ip_gs s')) t6)
                       F (Z_to_bv 64 0x8a914) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RI ra (Z_to_bv 64 (ip_nPart s)) a1 a2 a3 a4 a5 a6 s2 s3 (Z_to_bv 64 (ip_remF s)) (Z_to_bv 64 (E + 37708 + 258 * (ip_nPart s - 1))) s8 (Z_to_bv 64 (E + 37708 + 258 * (ip_nPart s - 1))) (Z_to_bv 64 (ip_gs s)) t6)
                     F (Z_to_bv 64 0x8a720) fc None m (seg_rom a0segs)).
  Proof.
    induction n as [|n IH]. { intros; lia. }
    intros k me m ra a1 a2 a3 a4 a5 a6 s2 s3 s8 t6 s HnP Hn Hk LEN MTF EH2 MI MU WM SHe V128 V136 V200 V1416 K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. openSF. assert (HA : A = (nInUse + 2)%Z) by reflexivity. assert (HM : nMTF = e_nMTF e) by reflexivity.
    pose proof (sm_nGroups_range (e_nMTF e)) as NGR. change (sm_nGroups (e_nMTF e)) with nG in NGR.
    pose proof (IPK k ltac:(lia)) as IK. cbv zeta in IK. fold s in IK. cps_destruct IK as (EnP & Hgs & EremF & HremF).
    pose proof (jseg_length J 37708 1548 ltac:(lia) ltac:(lia) ltac:(lia)) as LJl. pose proof (ovb_length_nat (ip_len s) (jseg J 37708 1548) 1548) as LLn.
    pose proof (jseg_length J 672 1032 ltac:(lia) ltac:(lia) ltac:(lia)) as LJm. pose proof (ovw_length mf (jseg J 672 1032) 258 ltac:(lia)) as LM.
    unfold EHEAD2 in EH2. unfold ESTATE_SIZE in SHe.
    set (nP := ip_nPart s) in *. set (gs := ip_gs s) in *. set (remF := ip_remF s) in *.
    (* [comment removed for export] *)
    destruct (ex_intro (fun t => t = (remF / nP)%Z) (remF / nP)%Z eq_refl) as [tF EtF].
    assert (HtF : (0 <= tF <= remF)%Z).
    { rewrite EtF. split; [apply Z.div_pos; lia|]. pose proof (Z.div_le_compat_l remF 1 nP ltac:(lia) ltac:(lia)) as Hd. rewrite Z.div_1_r in Hd. exact Hd. }
    change (id (tF = remF / nP)%Z) in EtF.
    (* [comment removed for export] *)
    wstep. wstep. wstep. rewrite (v_divw_lit remF nP) by lia. replace (remF / nP)%Z with tF by exact EtF. wstep. try rewrite (sx32_of_Z_signed (gs + -1)) by lia.
    assert (ADJ : forall ge1, ip_adj nG s ge1 = ((gs <? ge1) && negb (nP =? nG) && negb (nP =? 1) && ((nG - nP) mod 2 =? 1))%Z%bool) by (intros; reflexivity).
    set (ROW := (E + 37708 + 258 * (nP - 1))%Z) in *.
    (* [comment removed for export] *)
    assert (POSTADJ : forall ge1 aF1 ge2 aF2 (ya0 ya1 ya2 ya3 ya4 ya5 ya6 : word),
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z ->
        (ge2 = (if ip_adj nG s ge1 then ge1 - 1 else ge1))%Z -> (aF2 = (if ip_adj nG s ge1 then aF1 - zget mf ge1 else aF1))%Z ->
        (gs - 1 <= ge2 <= A - 1)%Z -> (0 <= aF2 <= remF)%Z ->
      evt a0segs Q (MS (RI ra ya0 ya1 ya2 ya3 ya4 ya5 ya6 (Z_to_bv 64 nP) (Z_to_bv 64 aF2) (Z_to_bv 64 remF) (Z_to_bv 64 ROW) (Z_to_bv 64 ge2) (Z_to_bv 64 ROW) (Z_to_bv 64 gs) t6)
                       F (Z_to_bv 64 0x8a7e4) fc None m (seg_rom a0segs))).
    { intros ge1 aF1 ge2 aF2 ya0 ya1 ya2 ya3 ya4 ya5 ya6 EG Hge1 EaF1 BaF1 Ege2 EaF2 Hge2 BaF2.
      (* [comment removed for export] *)
      pose proof (V128 m MU) as RO. pose proof (V136 m MU) as RO2. arun_to 0x8a7f8%Z. clear RO RO2.
      wstep; if_cases Kv; zify_cond_z Kv; [exfalso; lia|].
      (* [comment removed for export] *)
      wstep; if_cases Kn2; zify_cond_z Kn2; [exfalso; lia|].
      wstep.
      subst ROW.
      enter_with (smSETROW (Z.to_nat A) 0 (nP - 1) gs ge2 (ip_len s) m m);
        [st_eq| lia| lia| lia| lia| lia| lia| exact LEN| exact MI| apply munch_refl| apply wmono_refl| | |].
      { eapply (shzW_sub a0segs Wlen Wlen me m); [exact SHe| exact MU| a_sub_fp| lia| unfold ESTATE_SIZE; lia]. }
      { eapply (frdW_sub a0segs Wlen Wlen me m); [exact V1416| exact MU| a_sub_fp]. }
      intros m2 za0 za2 LEN2 MI2 MU2 WM2. clear LEN MI. transport_after_call a0segs m m2 MU2 WM2. clear MU2 WM2.
      (* [comment removed for export] *)
      wstep. wstep. try rewrite (sx32_of_Z (ge2 + 1)) by lia. wstep. try rewrite (sx32_of_Z (remF - aF2)) by lia. try rewrite (sx32_of_Z_signed (remF - aF2)) by lia. wstep. wstep.
      (* [comment removed for export] *)
      assert (Es' : sip_k e (S k) = SIP (sm_setrow (Z.to_nat A) (ip_len s) (nP - 1) gs ge2 0) (nP - 1) (remF - aF2) (ge2 + 1)).
      { rewrite sip_k_S. fold s. rewrite (sm_init_iter_spec mf nG A s ge1 aF1).
        2:{ unfold id in EtF. subst nP gs remF. rewrite <- EtF. exact EG. }
        cbv zeta. subst nP gs remF. rewrite <- Ege2, <- EaF2. reflexivity. }
      (* [comment removed for export] *)
      wstep; if_cases Kb; zify_cond_z Kb.
      - (* [comment removed for export] *)
        pose proof (IH (S k)) as IH'. cbv zeta in IH'. rewrite Es' in IH'. cbn [ip_nPart ip_remF ip_gs ip_len] in IH'.
        enter_with (IH' me m2 _ _ _ _ _ _ _ _ _ _ _);
          [st_eq| lia| lia| lia| exact LEN2| assumption| assumption| exact MI2| assumption| assumption| exact SHe| exact V128| exact V136| exact V200| exact V1416|].
        intros m' y1 y2 y3 y4 y5 y6 y7 y8 y9. replace (S k + n)%nat with (k + S n)%nat by lia. exact (K m' y1 y2 y3 y4 y5 y6 y7 y8 y9).
      - (* [comment removed for export] *)
        assert (n = 0)%nat by lia. subst n. wstep.
        pose proof K as K'. cbv zeta in K'. replace (k + 1)%nat with (S k) in K' by lia. rewrite Es' in K'. cbn [ip_nPart ip_remF ip_gs ip_len] in K'.
        enter_with (K' m2 _ _ _ _ _ _ _ _ _); [st_eq| exact LEN2| assumption| assumption| exact MI2| assumption| assumption]. }
    (* [comment removed for export] *)
    assert (POSTGROW : forall ge1 aF1 (xa0 xa3 xa4 xa5 xa6 : word),
      sm_grow 260%nat mf tF A (gs - 1) 0 = (ge1, aF1) -> (gs - 1 <= ge1 <= A - 1)%Z ->
      aF1 = sumF (fun v => zget mf v) gs (Z.to_nat (ge1 + 1 - gs)) -> (0 <= aF1 <= remF)%Z ->
      evt a0segs Q (MS (RI ra xa0 (Z_to_bv 64 (ge1 * 4294967296)) (Z_to_bv 64 tF) xa3 xa4 xa5 xa6 (Z_to_bv 64 nP) (Z_to_bv 64 aF1) (Z_to_bv 64 remF) (Z_to_bv 64 ROW) (Z_to_bv 64 ge1) (Z_to_bv 64 ROW) (Z_to_bv 64 gs) t6)
                       F (Z_to_bv 64 0x8a7a0) fc None m (seg_rom a0segs))).
    { intros ge1 aF1 xa0 xa3 xa4 xa5 xa6 EG Hge1 EaF1 BaF1.
      (* [comment removed for export] *)
      wstep; if_cases K3; zify_cond_z K3.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (nP =? 1)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          destruct (gs <? ge1)%Z, (nP =? nG)%Z; reflexivity. }
      (* [comment removed for export] *)
      pose proof (V200 m MU) as RO. wstep. clear RO. wstep; if_cases K2; zify_cond_z K2.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (nP =? nG)%Z with true by (symmetry; apply Z.eqb_eq; lia);
          destruct (gs <? ge1)%Z; reflexivity. }
      (* [comment removed for export] *)
      wstep; if_cases K1; zify_cond_z K1.
      { eapply (POSTADJ ge1 aF1 ge1 aF1); [exact EG| lia| exact EaF1| lia| | | lia| lia]; rewrite (ADJ ge1); replace (gs <? ge1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
      (* [comment removed for export] *)
      pose proof (V200 m MU) as RO. wstep. clear RO. wstep. try rewrite (sx32_of_Z (nG - nP)) by lia. try rewrite (sx32_of_Z_signed (nG - nP)) by lia. wstep.
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
      wstep. replace (ge1 * 4294967296 / 1073741824)%Z with (4 * ge1)%Z
        by (replace (ge1 * 4294967296)%Z with ((4 * ge1) * 1073741824)%Z by lia; rewrite Z.div_mul by lia; reflexivity).
      wstep.
      arun.
      pose proof (ovw_read a0segs m (E + 672) mf (jseg J 672 1032) 258 ge1 _ MTF ltac:(lia) Dg ltac:(unfold wa; f_equal; lia)) as RD.
      wstep. clear RD. try rewrite (sx32_of_Z (zget mf ge1)) by lia.
      wstep. try rewrite (sx32_of_Z (aF1 - zget mf ge1)) by lia. try rewrite (sx32_of_Z_signed (aF1 - zget mf ge1)) by lia.
      wstep. try rewrite (sx32_of_Z_signed (ge1 + -1)) by lia. try rewrite (sx32_of_Z (ge1 + -1)) by lia.
      enter_with (POSTADJ ge1 aF1 (ge1 - 1)%Z (aF1 - zget mf ge1)%Z _ _ _ _ _ _ _); [st_eq| exact EG| lia| exact EaF1| lia| rewrite AT; reflexivity| rewrite AT; reflexivity| lia| lia]. }
    (* [comment removed for export] *)
    assert (E0 : 0%Z = sumF (fun v => zget mf v) gs (Z.to_nat (gs - 1 + 1 - gs))) by (replace (Z.to_nat (gs - 1 + 1 - gs)) with 0%nat by lia; reflexivity).
    wstep; if_cases K5; zify_cond_z K5.
    { eapply (POSTADJ (gs - 1)%Z 0%Z (gs - 1)%Z 0%Z); [apply sm_grow_stop; lia| lia| exact E0| lia| | | lia| lia];
        rewrite (ADJ (gs - 1)%Z); replace (gs <? gs - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
    (* [comment removed for export] *)
    wstep; if_cases K6; zify_cond_z K6.
    { eapply (POSTADJ (gs - 1)%Z 0%Z (gs - 1)%Z 0%Z); [apply sm_grow_stop; lia| lia| exact E0| lia| | | lia| lia];
        rewrite (ADJ (gs - 1)%Z); replace (gs <? gs - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity. }
    (* [comment removed for export] *)
    wstep. wstep. wstep. wstep. wstep. wstep. rewrite ?zbv_mod_mul, ?zbv_add_mod_mul.
    enter_with (smGROW 260%nat (gs - 1)%Z 0%Z gs tF remF m);
      [st_eq| lia| lia| lia| lia| lia| lia| exact E0| exact EremF| lia| exact MTF| |].
    { eapply (shzW_sub a0segs Wlen [] me m); [exact SHe| exact MU| a_sub_fp| lia| unfold ESTATE_SIZE; lia]. }
    intros ge' aF' y0 y3 y4 y5 y6 EG' Hge' EaF' BaF'. eapply (POSTGROW ge' aF'); [exact EG'| lia| exact EaF'| exact BaF'].
  Qed.
End A0SMB.
End ACeilS1.
