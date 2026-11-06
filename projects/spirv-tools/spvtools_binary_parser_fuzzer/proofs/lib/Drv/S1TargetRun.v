(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import Amb PropExec CatExec CatSim SeqExec StoreOk MemSplit Frame Hoare ShapeAlg ShapeLaws Nodes RefNodes
  SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX SymAux SymTac SymBranch RefMemcpyLib RefPrintfLib SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import S1Cells S1RwWindow S1PrintfBufBase S1TargetDefs S1TargetBlocks.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require S1TargetConsts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope Z_scope.
Import SX2. Import SX2S.

Abbreviation RSEGS := Plain.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation LLVM_ENTRY := S1TargetConsts.LLVM_ENTRY.
Abbreviation EMPTY_OBJ := S1TargetConsts.EMPTY_OBJ.
Abbreviation TD_LOCALE := S1TargetConsts.TD_LOCALE.
Abbreviation GLOBAL_LOCALE := S1TargetConsts.GLOBAL_LOCALE.

Definition calls_of (content : list byte) : Z :=
  if hdr_cfglen content =? 0 then 1 else (bv_unsigned (nth 2 content (Z_to_bv 8 0)) mod 4) + 1.

Record front_cells (M : word -> option byte) : Prop := {
  fc_init : cell M INITIALIZED 1 1;
  fc_slot : cell M AT_SLOT 4 2;
  fc_f1   : cell M AT_F1 8 AT_CALL;
  fc_a1   : cell M AT_A1 8 AEF_GUARD;
  fc_cb   : cell M AEF_CB 1 0;
  fc_nh   : cell M NEW_HANDLER 8 OOM_SPIN
}.

Section Front.
  Context {fx : FPState}.
  Variables (R : bvmap 5 word) (M : word -> option byte) (model : Model).
  Variables (sp0 buf cfglen n b2 : Z).
  Hypothesis Hsp : 0x7fff80000000 <= sp0 <= 0x800000000000 /\ sp0 mod 16 = 0.
  Hypothesis Hbuf : 0x122000 <= buf /\ buf + 3 <= sp0 - 8388608.
  Hypothesis Hcfglen : 0 <= cfglen < 32768.
  Hypothesis Hn : 0 <= n < 2 ^ 26.
  Hypothesis Hb2 : 0 <= b2 < 256.
  Hypothesis R1 : getr R 1 = Z_to_bv 64 TR_MAINRET.
  Hypothesis R2 : getr R 2 = Z_to_bv 64 (sp0 - 128).
  Hypothesis R3 : getr R 3 = Z_to_bv 64 0x10800.
  Hypothesis R4 : getr R 4 = Z_to_bv 64 0x1006b8.
  Hypothesis R10 : getr R 10 = Z_to_bv 64 (buf + 2).
  Hypothesis R11 : getr R 11 = Z_to_bv 64 cfglen.
  Hypothesis R12 : getr R 12 = Z_to_bv 64 (buf + 6 + cfglen).
  Hypothesis R13 : getr R 13 = Z_to_bv 64 n.
  Hypothesis Mstack : stack_writableZ M sp0.
  Hypothesis Mtext : forall i, 0x10000 <= i < 0xee000 -> M (Z_to_bv 64 i) = None.
  Hypothesis Mgap : forall i, 0xfe4e9 <= i < 0xfe790 -> M (Z_to_bv 64 i) = None.
  Hypothesis Mnl : cell M NEED_LOCKS 1 0.
  Hypothesis Mlock : forall i, 0x120700 <= i < 0x120708 -> M (Z_to_bv 64 i) = None.
  Hypothesis Mnext : forall i, AT_BUILTIN <= i < 0x120720 -> M (Z_to_bv 64 i) = None.
  Hypothesis Mslot : cell M AT_SLOT 4 1.
  Hypothesis Mhead : cell M AT_HEAD 8 AT_BUILTIN.
  Hypothesis Mb2 : rdn RSEGS M (Z_to_bv 64 (buf + 2)) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 b2)).
  Hypothesis Hh : m_halted model = None.
  Hypothesis Hlazy : m_vm_lazy model = [].

  Definition fvals : list word :=
    [Z_to_bv 64 sp0; Z_to_bv 64 (buf + 2); Z_to_bv 64 cfglen; Z_to_bv 64 (buf + 6 + cfglen); Z_to_bv 64 n; Z_to_bv 64 b2]
    ++ junk_vals R ++ [Z_to_bv 64 0; Z_to_bv 64 0].
  Definition fE : env := Env (vals_ev fvals) (blobs_ev []).

  Ltac evl := lazy [fE edenot ev eb vals_ev fvals junk_vals blobs_ev nth app map seq length].
  Tactic Notation "evl" "in" hyp(H) := lazy [fE edenot ev eb vals_ev fvals junk_vals blobs_ev nth app map seq length] in H.

  Lemma front_regs_ok : regs_ok fE tr_sr R.
  Proof.
    apply regs_ok_by_idx. intros i Hi.
    destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
      cbn [nth tr_sr allregs32]; evl;
      first [ apply getr_zero | assumption
            | rewrite alu_add_ZZ, R2; f_equal; lia
            | f_equal; apply bv_eq; reflexivity ].
  Qed.

  Lemma kword_cell : forall (a : Z) (w : nat) (v : Z),
    (w <= 8)%nat -> 0 <= a < 2 ^ 64 -> a + Z.of_nat w <= 2 ^ 64 -> cell M a w v ->
    kentry_ok RSEGS fE M (KWord (SA (ELit 0) a) w (ELit v)).
  Proof.
    intros a w v Hw Ha Hnw HC. cbn [kentry_ok a_base a_off edenot]. split; [exact Hw|].
    unfold flat, estart, adenot. cbn [a_base a_off edenot]. rewrite (u_small 0) by lia.
    split; [lia|]. unfold v_addi. rewrite (u_small 0) by lia. rewrite Z.add_0_l. exact HC.
  Qed.

  Lemma front_know_ok : know_ok RSEGS fE M tr_kn.
  Proof.
    unfold tr_kn. repeat apply Forall_cons; try apply Forall_nil.
    - cbn [kentry_ok]. evl. rewrite u_small by lia. split; [lia | exact (proj2 Hsp)].
    - cbn [kentry_ok]. evl. rewrite u_small by lia. lia.
    - cbn [kentry_ok a_base a_off]. unfold flat, estart. cbn [a_base a_off]. evl. rewrite u_small by lia.
      split; [lia|]. intros d m Hd Hm. replace (sp0 + -8388608 + d) with (sp0 - 8388608 + d) by lia. apply Mstack; lia.
    - cbn [kentry_ok]. repeat split; [lia | lia | exact Mtext].
    - cbn [kentry_ok]. repeat split; [lia | lia | exact Mgap].
    - cbn [kentry_ok a_base a_off]. unfold flat, estart. cbn [a_base a_off edenot].
      rewrite (u_small 0) by lia. split; [lia|]. intros d m Hd Hm.
      apply store_ok_of_all; [rewrite u_small by lia; lia|]. intros x Hx. rewrite u_small in Hx by lia.
      apply rw_wview_. lia.
    - apply kword_cell; [lia | unfold NEED_LOCKS; lia | unfold NEED_LOCKS; cbn; lia | exact Mnl].
    - cbn [kentry_ok]. repeat split; [lia | lia | exact Mlock].
    - cbn [kentry_ok]. repeat split; [unfold AT_BUILTIN; lia | lia | exact Mnext].
    - apply kword_cell; [lia | unfold AT_SLOT; lia | unfold AT_SLOT; cbn; lia | exact Mslot].
    - apply kword_cell; [lia | unfold AT_HEAD; lia | unfold AT_HEAD; cbn; lia | exact Mhead].
    - cbn [kentry_ok]. evl. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. evl. rewrite u_small by lia. lia.
    - cbn [kentry_ok a_base a_off]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off]. evl.
      rewrite (u_small (buf + 2)) by lia. split; [lia|]. unfold v_addi. rewrite (u_small (buf + 2)), Z.add_0_r by lia. exact Mb2.
    - cbn [kentry_ok]. evl. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. evl. rewrite u_small by lia. lia.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. evl.
      rewrite (u_small (buf + 2)), (u_small sp0) by lia. left. lia.
  Qed.

  Definition callsv : Z := if cfglen =? 0 then 1 else (b2 mod 4) + 1.

  Definition front_common (R1 : bvmap 5 word) : Prop :=
    getr R1 2 = Z_to_bv 64 (sp0 - 208) /\ getr R1 3 = Z_to_bv 64 0x10800 /\ getr R1 4 = Z_to_bv 64 0x1006b8
    /\ getr R1 8 = Z_to_bv 64 n /\ getr R1 19 = Z_to_bv 64 (buf + 2) /\ getr R1 20 = Z_to_bv 64 INITIALIZED
    /\ getr R1 21 = Z_to_bv 64 callsv.

  Definition front_regions : list (word * Z) :=
    [(Z_to_bv 64 (sp0 - 256), 128); (Z_to_bv 64 INITIALIZED, 1); (Z_to_bv 64 AT_SLOT, 4); (Z_to_bv 64 AT_F1, 8); (Z_to_bv 64 AT_A1, 8)].

  Theorem tr_front : forall K,
    (0 < n -> forall R1 M1,
       front_common R1 -> getr R1 1 = Z_to_bv 64 RET_MALLOC -> getr R1 10 = Z_to_bv 64 n ->
       getr R1 9 = Z_to_bv 64 (buf + 6 + cfglen) -> getr R1 18 = Z_to_bv 64 cfglen ->
       tr_frame sp0 R M1 -> front_cells M1 -> frame_mod M M1 front_regions ->
       srealizes RSEGS (mkCfg (mkst R1 (Z_to_bv 64 TR_MALLOC) M1 (seg_rom RSEGS)) model) K) ->
    (n = 0 -> forall R1 M1,
       front_common R1 -> getr R1 9 = Z_to_bv 64 EMPTY -> getr R1 18 = Z_to_bv 64 0 ->
       getr R1 22 = Z_to_bv 64 0 -> getr R1 23 = Z_to_bv 64 MINUS2 ->
       tr_frame sp0 R M1 -> front_cells M1 -> frame_mod M M1 front_regions ->
       srealizes RSEGS (mkCfg (mkst R1 (Z_to_bv 64 TR_CALLHEAD) M1 (seg_rom RSEGS)) model) K) ->
    srealizes RSEGS (mkCfg (mkst R (Z_to_bv 64 TR_ENTRY) M (seg_rom RSEGS)) model) K.
  Proof.
    intros K KM KL.
    pose proof front_regs_ok as HR. pose proof front_know_ok as HK.

    destruct (run_sound RSEGS 3000 tr_stops (SCR [] [] []) TR_ENTRY tr_sr tr_kn 40 ssI [] scrI
                fE M (seg_rom RSEGS) R rI_eq HR HK ltac:(constructor)) as (RJ & HRJ & HlfI & HmsI).
    rewrite rI_pc in HmsI. change (s_regs ssI) with srJ in HRJ.
    pose proof (carry_after RSEGS fE M _ tr_kn [] _ _ _ cJ_eq HlfI HK ltac:(constructor)) as HKJ.
    set (MJ := mem_denot fE M (s_log ssI)) in *.
    eapply srz_msteps; [exact Hh | exact Hlazy | exact HmsI |].

    assert (FR : tr_frame sp0 R MJ).
    { constructor; unfold TR_MAINRET.
      all: (lazymatch goal with |- rdn _ _ (Z_to_bv 64 (sp0 - ?k)) 8 = _ =>
             let H := fresh in
             krdv HKJ 0%nat (- k) 8%nat H; [apply flat_intro; evl; rewrite ?u_small by lia; lia|];
             unfold adenot, v_addi in H; cbn [a_base a_off] in H; evl in H; rewrite u_small in H by lia;
             replace (sp0 + - k) with (sp0 - k) in H by lia; rewrite H; evl;
             do 3 f_equal; apply bv_eq; lazy; reflexivity end). }
    assert (FC : front_cells MJ).
    { constructor; unfold cell, INITIALIZED, AT_SLOT, AT_F1, AT_A1, AT_CALL, AEF_GUARD, AEF_CB, NEW_HANDLER, OOM_SPIN.
      - krd HKJ 0xfe4f0%Z 1%nat H; exact H.
      - krd HKJ 0x120708%Z 4%nat H; exact H.
      - krd HKJ 0x120728%Z 8%nat H; exact H.
      - krd HKJ 0x120828%Z 8%nat H; exact H.
      - krd HKJ 0xfe4f4%Z 1%nat H; exact H.
      - krd HKJ 0xfe520%Z 8%nat H; exact H. }
    assert (FM : frame_mod M MJ front_regions).
    { assert (RG : map (rdenot fE) tr_regions = front_regions).
      { unfold tr_regions, front_regions, rdenot, estart. cbn [map fst snd a_base a_off]. evl.
        unfold INITIALIZED, AT_SLOT, AT_F1, AT_A1. rewrite (u_small 0), (u_small sp0) by lia. repeat f_equal; lia. }
      assert (RF : regions_flat fE tr_regions).
      { intros rg Hrg. unfold tr_regions in Hrg. unfold flat, estart.
        repeat (destruct Hrg as [<-|Hrg]; [cbn [fst snd a_base a_off]; evl; unfold INITIALIZED, AT_SLOT, AT_F1, AT_A1; rewrite ?(u_small 0), ?(u_small sp0) by lia; lia|]); destruct Hrg. }
      rewrite <- RG. exact (log_covered_frame fE M tr_regions _ rI_cov RF HlfI). }

    assert (SCn : forall t, (t = true <-> 0 < n) -> sc_denot RSEGS MJ fE (SCBr t BC_NE (EVar 4) (ELit 0))).
    { intros t Ht. unfold sc_denot. evl. rewrite bt_ne0_Z by lia.
      destruct t; [destruct Ht as [Ht _]; specialize (Ht eq_refl) | destruct Ht as [_ Ht]];
        destruct (n =? 0) eqn:En; try reflexivity; [apply Z.eqb_eq in En; lia | apply Z.eqb_neq in En; exfalso; pose proof (Ht ltac:(lia)); discriminate]. }
    assert (SCz : forall t, (t = true <-> n = 0) -> sc_denot RSEGS MJ fE (SCBr t BC_EQ (EVar 4) (ELit 0))).
    { intros t Ht. unfold sc_denot. evl. rewrite bt_eq0_Z by lia.
      destruct t; [destruct Ht as [Ht _]; specialize (Ht eq_refl) | destruct Ht as [_ Ht]];
        destruct (n =? 0) eqn:En; try reflexivity; [apply Z.eqb_neq in En; lia | apply Z.eqb_eq in En; exfalso; pose proof (Ht En); discriminate]. }
    assert (SCc : forall t, (t = true <-> cfglen = 0) -> sc_denot RSEGS MJ fE (SCBr t BC_EQ (EVar 2) (ELit 0))).
    { intros t Ht. unfold sc_denot. evl. rewrite bt_eq0_Z by lia.
      destruct t; [destruct Ht as [Ht _]; specialize (Ht eq_refl) | destruct Ht as [_ Ht]];
        destruct (cfglen =? 0) eqn:En; try reflexivity; [apply Z.eqb_neq in En; lia | apply Z.eqb_eq in En; exfalso; pose proof (Ht En); discriminate]. }
    assert (CALLS1 : cfglen = 0 -> Z_to_bv 64 1 = Z_to_bv 64 callsv) by (intros Hc; unfold callsv; destruct (cfglen =? 0) eqn:En; [reflexivity | apply Z.eqb_neq in En; lia]).
    assert (CALLS2 : cfglen <> 0 ->
              alu64 ALU_ADD (alu64 ALU_AND (ext_val false 0 1 (Z_to_bv 64 b2)) (Z_to_bv 64 3)) (Z_to_bv 64 1) = Z_to_bv 64 callsv).
    { intros Hc. unfold callsv. destruct (cfglen =? 0) eqn:En; [apply Z.eqb_eq in En; lia|].
      rewrite ext_val_zx_id by (rewrite u_small by lia; cbn; lia).
      rewrite alu_and. unfold v_and. rewrite !u_small by lia.
      replace (Z.land b2 3) with (b2 mod 4) by (change 3 with (Z.ones 2); rewrite Z.land_ones by lia; reflexivity).
      rewrite alu_add_ZZ. reflexivity. }
    destruct (Z.eq_dec cfglen 0) as [Hc0|Hc1]; destruct (Z.eq_dec n 0) as [Hn0|Hn1].
    -
      destruct (run_sound RSEGS 3000 tr_stops (SCR [true; false] [] []) TR_POSTINIT srJ knJ 40 ssC_tf scsC_tf _
                  fE MJ (seg_rom RSEGS) RJ rC_tf_eq HRJ HKJ
                  ltac:(repeat apply Forall_cons; try apply Forall_nil; [apply SCn | apply SCc]; split; intros; try lia; try discriminate; reflexivity))
        as (RC & HRC & _ & HmsC).
      rewrite rC_tf_pc, rC_tf_log in HmsC. cbn [mem_denot] in HmsC.
      eapply srz_msteps; [exact Hh | exact Hlazy | exact HmsC |].
      apply (KL Hn0); try exact FR; try exact FC; try exact FM.
      all: try (unfold front_common; repeat split).
      all: try (lazymatch goal with |- getr _ ?r = _ => regv HRC r end; evl; unfold INITIALIZED, EMPTY, MINUS2;
                first [ reflexivity | rewrite alu_add_ZZ; f_equal; lia | rewrite Hn0; reflexivity | apply CALLS1; exact Hc0 ]).
    -
      destruct (run_sound RSEGS 3000 tr_stops (SCR [true; true] [] []) TR_POSTINIT srJ knJ 40 ssC_tt scsC_tt _
                  fE MJ (seg_rom RSEGS) RJ rC_tt_eq HRJ HKJ
                  ltac:(repeat apply Forall_cons; try apply Forall_nil; [apply SCn | apply SCc]; split; intros; try lia; try discriminate; reflexivity))
        as (RC & HRC & _ & HmsC).
      rewrite rC_tt_pc, rC_tt_log in HmsC. cbn [mem_denot] in HmsC.
      eapply srz_msteps; [exact Hh | exact Hlazy | exact HmsC |].
      apply (KM ltac:(lia)); try exact FR; try exact FC; try exact FM.
      all: try (unfold front_common; repeat split).
      all: try (lazymatch goal with |- getr _ ?r = _ => regv HRC r end; evl; unfold INITIALIZED, EMPTY, RET_MALLOC;
                first [ reflexivity | rewrite alu_add_ZZ; f_equal; lia | apply CALLS1; exact Hc0 ]).
    -
      destruct (run_sound RSEGS 3000 tr_stops (SCR [false; true] [] []) TR_POSTINIT srJ knJ 40 ssC_ft scsC_ft _
                  fE MJ (seg_rom RSEGS) RJ rC_ft_eq HRJ HKJ
                  ltac:(repeat apply Forall_cons; try apply Forall_nil; [apply SCz | apply SCc]; split; intros; try lia; try discriminate; reflexivity))
        as (RC & HRC & _ & HmsC).
      rewrite rC_ft_pc, rC_ft_log in HmsC. cbn [mem_denot] in HmsC.
      eapply srz_msteps; [exact Hh | exact Hlazy | exact HmsC |].
      apply (KL Hn0); try exact FR; try exact FC; try exact FM.
      all: try (unfold front_common; repeat split).
      all: try (lazymatch goal with |- getr _ ?r = _ => regv HRC r end; evl; unfold INITIALIZED, EMPTY, MINUS2;
                first [ reflexivity | rewrite alu_add_ZZ; f_equal; lia | rewrite Hn0; reflexivity | apply CALLS2; exact Hc1 ]).
    -
      destruct (run_sound RSEGS 3000 tr_stops (SCR [false; false] [] []) TR_POSTINIT srJ knJ 40 ssC_ff scsC_ff _
                  fE MJ (seg_rom RSEGS) RJ rC_ff_eq HRJ HKJ
                  ltac:(repeat apply Forall_cons; try apply Forall_nil; [apply SCz | apply SCc]; split; intros; try lia; try discriminate; reflexivity))
        as (RC & HRC & _ & HmsC).
      rewrite rC_ff_pc, rC_ff_log in HmsC. cbn [mem_denot] in HmsC.
      eapply srz_msteps; [exact Hh | exact Hlazy | exact HmsC |].
      apply (KM ltac:(lia)); try exact FR; try exact FC; try exact FM.
      all: try (unfold front_common; repeat split).
      all: try (lazymatch goal with |- getr _ ?r = _ => regv HRC r end; evl; unfold INITIALIZED, EMPTY, RET_MALLOC;
                first [ reflexivity | rewrite alu_add_ZZ; f_equal; lia | apply CALLS2; exact Hc1 ]).
  Qed.
End Front.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
