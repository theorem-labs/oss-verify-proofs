(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import SymStepR AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ExecNodes ExecNodesSound MoveNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import MVN.
Open Scope Z_scope.

Module MVNS.
Section Sound.
  Context {fx : FPState}.
  Variable SEGS : list Segment.
  Variable IT : itab.
  Hypothesis IT_ok : itab_sound SEGS IT.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E a, argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' a, env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  Lemma it_fetch : forall pc i, itab_lookup IT pc = Some i -> 0 <= pc < two64 ->
    exists w, fetch_word SEGS (Z_to_bv 64 pc) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4).
  Proof.
    intros pc i H Hpc. pose proof (IT_ok _ _ H) as E. unfold itab_entry in E.
    destruct (fetch_word SEGS (Z_to_bv 64 pc)) as [w|] eqn:Hf; [|discriminate].
    destruct (is_ecall w) eqn:Hec; [discriminate|].
    destruct (decode_any w) as [[ins sz]|] eqn:Hd; [|discriminate].
    destruct (Z.eqb sz 4) eqn:Hsz; [|discriminate]. apply Z.eqb_eq in Hsz. subst sz. injection E as ->.
    exists w. repeat split; auto.
  Qed.

  Lemma rq_eq : forall r z, rq r z = true -> r = r5 z.
  Proof. intros r z H. unfold rq in H. apply bv_eqb_eq in H. exact H. Qed.

  (* [comment removed for export] *)
  Lemma memcpy_branch : forall (d s n : Z),
    1 <= n -> n <= 2 ^ 62 -> 0 <= d -> d + n <= 2 ^ 64 -> 0 <= s -> s + n <= 2 ^ 64 ->
    (d + n <= s \/ s + n <= d) ->
    (s - (n + d) mod 2 ^ 64) mod 2 ^ 64 <= (0 - (n * 2) mod 2 ^ 64) mod 2 ^ 64.
  Proof.
    intros d s n Hn1 Hn62 Hd0 Hdn Hs0 Hsn Hap.
    rewrite (Z.mod_small (n * 2)) by lia.
    replace (0 - n * 2) with ((2 ^ 64 - 2 * n) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
    rewrite (Z.mod_small (2 ^ 64 - 2 * n)) by lia.
    destruct (Z.eq_dec (d + n) (2 ^ 64)) as [Heq|Hne].
    - replace (n + d) with (2 ^ 64) by lia. rewrite Z.mod_same, Z.sub_0_r by lia.
      rewrite Z.mod_small by lia. lia.
    - rewrite (Z.mod_small (n + d)) by lia.
      destruct Hap as [H|H].
      + rewrite Z.mod_small by lia. lia.
      + replace (s - (n + d)) with ((2 ^ 64 + s - n - d) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full.
        rewrite Z.mod_small by lia. lia.
  Qed.

  Lemma is_beq_spec : forall r1 r2 i, is_beq r1 r2 (Some i) = true -> exists imm, i = Branch BC_EQ (r5 r1) (r5 r2) imm.
  Proof.
    intros r1 r2 i H. unfold is_beq in H. destruct i; try discriminate H. destruct c; try discriminate H.
    apply andb_prop in H as [H1 H2]. apply rq_eq in H1. apply rq_eq in H2. subst. eexists; reflexivity.
  Qed.
  Lemma bgeu_off_spec : forall r1 r2 i o, bgeu_off r1 r2 (Some i) = Some o -> exists imm, i = Branch BC_GEU (r5 r1) (r5 r2) imm /\ o = bv_signed imm.
  Proof.
    intros r1 r2 i o H. unfold bgeu_off in H. destruct i; try discriminate H. destruct c; try discriminate H.
    destruct (rq rs1 r1 && rq rs2 r2)%bool eqn:Hq; [|discriminate H]. injection H as <-.
    apply andb_prop in Hq as [H1 H2]. apply rq_eq in H1. apply rq_eq in H2. subst. eexists; split; reflexivity.
  Qed.
  Lemma is_op_spec : forall o rd r1 r2 i, is_op o rd r1 r2 (Some i) = true -> i = Op o (r5 rd) (r5 r1) (r5 r2).
  Proof.
    intros o rd r1 r2 i H. unfold is_op in H. destruct i; try discriminate H.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply aluop_eqb_eq in H0. apply rq_eq in H1. apply rq_eq in H2. apply rq_eq in H3. subst. reflexivity.
  Qed.
  Lemma is_slli1_spec : forall rd r1 i, is_slli1 rd r1 (Some i) = true -> exists sh, i = ShiftImm ALU_SLL (r5 rd) (r5 r1) sh /\ bv_unsigned sh = 1.
  Proof.
    intros rd r1 i H. unfold is_slli1 in H. destruct i; try discriminate H.
    apply andb_prop in H as [H H3]. apply andb_prop in H as [H H2]. apply andb_prop in H as [H0 H1].
    apply aluop_eqb_eq in H0. apply rq_eq in H1. apply rq_eq in H2. apply Z.eqb_eq in H3. subst. eexists; split; [reflexivity | exact H3].
  Qed.
  Lemma jal0_off_spec : forall i o, jal0_off (Some i) = Some o -> exists imm, i = Jal (r5 0) imm /\ o = bv_signed imm.
  Proof.
    intros i o H. unfold jal0_off in H. destruct i; try discriminate H.
    destruct (rq rd 0) eqn:Hq; [|discriminate H]. injection H as <-. apply rq_eq in Hq. subst. eexists; split; reflexivity.
  Qed.
  (* [comment removed for export] *)
  Lemma lk_some : forall (P : option instr -> bool) x, (P None = false) -> P x = true -> exists i, x = Some i.
  Proof. intros P [i|] HN H; [exists i; reflexivity | rewrite HN in H; discriminate]. Qed.

  (* [comment removed for export] *)
  Lemma memmove_pro_spec : forall p tgt, memmove_pro IT A p = Some tgt ->
    tgt = x_memcpy A /\ 0 <= p /\ p + 24 < two64 /\ 0 <= x_memcpy A < two64 /\
    exists (i0m : bv 13) (sh : bv 6) (i5m : bv 13) (jm : bv 21),
      itab_lookup IT p = Some (Branch BC_EQ (r5 10) (r5 11) i0m) /\
      itab_lookup IT (p + 4) = Some (Op ALU_ADD (r5 13) (r5 12) (r5 10)) /\
      itab_lookup IT (p + 8) = Some (ShiftImm ALU_SLL (r5 14) (r5 12) sh) /\ bv_unsigned sh = 1 /\
      itab_lookup IT (p + 12) = Some (Op ALU_SUB (r5 13) (r5 11) (r5 13)) /\
      itab_lookup IT (p + 16) = Some (Op ALU_SUB (r5 14) (r5 0) (r5 14)) /\
      itab_lookup IT (p + 20) = Some (Branch BC_GEU (r5 14) (r5 13) i5m) /\
      let pcJ := p + 20 + bv_signed i5m in
      0 <= pcJ /\ pcJ + 4 < two64 /\
      itab_lookup IT pcJ = Some (Jal (r5 0) jm) /\ pcJ + bv_signed jm = x_memcpy A.
  Proof.
    intros p tgt H. unfold memmove_pro in H.
    destruct (itab_lookup IT (p + 20)) as [i5|] eqn:L5; [|discriminate H].
    destruct (bgeu_off 14 13 (Some i5)) as [o5|] eqn:B5; [|discriminate H].
    destruct (bgeu_off_spec _ _ _ _ B5) as (i5m & -> & ->).
    destruct (itab_lookup IT (p + 20 + bv_signed i5m)) as [i6|] eqn:L6; [|discriminate H].
    destruct (jal0_off (Some i6)) as [oj|] eqn:J6; [|discriminate H].
    destruct (jal0_off_spec _ _ J6) as (jm & -> & ->).
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate H] end.
    injection H as <-.
    repeat match type of Hc with (_ && _)%bool = true => apply andb_prop in Hc as [Hc ?X] end.
    apply Z.ltb_lt in X. apply Z.leb_le in X0. apply Z.ltb_lt in X1. apply Z.leb_le in X2. apply Z.ltb_lt in X3. apply Z.leb_le in X4.
    apply Z.eqb_eq in X5.
    destruct (lk_some (is_op ALU_SUB 14 0 14) _ eq_refl X6) as [i4 L4]. rewrite L4 in X6. apply is_op_spec in X6.
    destruct (lk_some (is_op ALU_SUB 13 11 13) _ eq_refl X7) as [i3 L3]. rewrite L3 in X7. apply is_op_spec in X7.
    destruct (lk_some (is_slli1 14 12) _ eq_refl X8) as [i2 L2]. rewrite L2 in X8. apply is_slli1_spec in X8 as (sh & X8 & Hsh).
    destruct (lk_some (is_op ALU_ADD 13 12 10) _ eq_refl X9) as [i1 L1]. rewrite L1 in X9. apply is_op_spec in X9.
    destruct (lk_some (is_beq 10 11) _ eq_refl Hc) as [i0 L0]. rewrite L0 in Hc. apply is_beq_spec in Hc as [i0m Hc].
    subst i0 i1 i2 i3 i4.
    split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|].
    exists i0m, sh, i5m, jm. repeat split; try assumption; lia.
  Qed.

  Lemma r5_ne : forall a b, Z.eqb (a mod 32) (b mod 32) = false -> 0 <= a < 32 -> 0 <= b < 32 -> r5 a <> r5 b.
  Proof.
    intros a b H Ha Hb X. apply Z.eqb_neq in H. apply H.
    apply (f_equal bv_unsigned) in X. unfold r5 in X. rewrite !Z_to_bv_unsigned in X.
    unfold bv_wrap in X. exact X.
  Qed.
  Ltac rne := let X := fresh in intro X; apply (f_equal bv_unsigned) in X; cbv in X; first [discriminate X | lia].
  Lemma some_inj : forall {X : Type} (a b : X), Some a = Some b -> a = b.
  Proof. intros X a b H. injection H as ->. reflexivity. Qed.

  Theorem xn_soundF : forall args, node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (MVN.xn IT A args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold MVN.xn in Hn.
    destruct args as [|? ?]; [|discriminate Hn].
    destruct (memmove_pro IT A (pc cs)) as [tgt|] eqn:Hpro; [|discriminate Hn].
    destruct (memmove_pro_spec _ _ Hpro) as (Htgt & Hp0 & Hp24 & Hmc & i0m & sh & i5m & jm & L0 & L1 & L2 & Hsh & L3 & L4 & L5 & HJ).
    cbv zeta in HJ. destruct HJ as (HJ0 & HJ4 & L6 & HJt). subst tgt.
    cbv zeta in Hn.
    destruct (split_lit (reg cs 10)) as [db dk] eqn:Hsd.
    destruct (split_lit (reg cs 11)) as [sb sk] eqn:Hss.
    destruct (xlo (kn cs) (reg cs 12)) as [nlo|] eqn:Hnlo; [|discriminate Hn].
    destruct (xhi (kn cs) (reg cs 12)) as [nhi|] eqn:Hnhi; [|discriminate Hn].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate Hn] end.
    apply some_inj in Hn. subst cs'.   (* [comment removed for export] *)
    apply andb_prop in Hc as [Hc Hlen]. apply andb_prop in Hc as [Hc Hap]. apply andb_prop in Hc as [Hc Hfs].
    apply andb_prop in Hc as [Hc Hfd]. apply andb_prop in Hc as [Hn1 Hn62].
    apply Z.leb_le in Hn1. apply Z.leb_le in Hn62. apply Nat.eqb_eq in Hlen.
    (* [comment removed for export] *)
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (co_regs _ _ _ _ _ _ _ _ _ _ _ HC) as HR.
    set (H := hid A argH E cs model). set (MR := Mr A argH E cs model FULL).
    set (d := getr R (r5 10)). set (s := getr R (r5 11)). set (n := getr R (r5 12)).
    assert (Ed : edenot E (reg cs 10) = d) by (unfold d; rewrite (HR (r5 10)); reflexivity).
    assert (Es : edenot E (reg cs 11) = s) by (unfold s; rewrite (HR (r5 11)); reflexivity).
    assert (En : edenot E (reg cs 12) = n) by (unfold n; rewrite (HR (r5 12)); reflexivity).
    pose proof (xlo_sound SEGS E MR (kn cs) _ _ HK Hnlo) as Hnlo'. rewrite En in Hnlo'.
    pose proof (xhi_sound SEGS E MR (kn cs) _ _ HK Hnhi) as Hnhi'. rewrite En in Hnhi'.
    destruct (flat_x_sound SEGS E MR (kn cs) db dk (reg cs 12) HK Hfd) as (Fd1 & Fd2 & Fd3).
    destruct (flat_x_sound SEGS E MR (kn cs) sb sk (reg cs 12) HK Hfs) as (Fs1 & Fs2 & Fs3).
    pose proof (ranges_apart_x_sound SEGS E MR (kn cs) db dk (reg cs 12) sb sk (reg cs 12) HK Hap) as Hapart.
    unfold elenZ in Hapart. rewrite En in Fd2, Fd3, Fs2, Fs3, Hapart.
    pose proof (u_of_split E _ _ _ Hsd ltac:(lia)) as Ud. rewrite Ed in Ud.
    pose proof (u_of_split E _ _ _ Hss ltac:(lia)) as Us. rewrite Es in Us.
    set (ud := bv_unsigned d) in *. set (us := bv_unsigned s) in *. set (un := bv_unsigned n) in *.
    assert (Hds : d <> s) by (intros X; assert (ud = us) by (unfold ud, us; rewrite X; reflexivity); lia).
    pose proof (memcpy_branch ud us un ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hbr.
    (* [comment removed for export] *)
    set (v13a := alu64 ALU_ADD n d). set (R1 := regupd R (r5 13) v13a).
    set (v14a := alu64 ALU_SLL n (Z_to_bv 64 1)). set (R2 := regupd R1 (r5 14) v14a).
    set (v13b := alu64 ALU_SUB s v13a). set (R3 := regupd R2 (r5 13) v13b).
    set (v14b := alu64 ALU_SUB (Z_to_bv 64 0) v14a). set (R4 := regupd R3 (r5 14) v14b).
    assert (G1_12 : getr R1 (r5 12) = n) by (unfold R1; rewrite getr_other by rne; reflexivity).
    assert (G2_11 : getr R2 (r5 11) = s) by (unfold R2, R1; rewrite !getr_other by rne; reflexivity).
    assert (G2_13 : getr R2 (r5 13) = v13a) by (unfold R2, R1; rewrite getr_other by rne; apply getr_same; rne).
    assert (G3_0 : getr R3 (r5 0) = Z_to_bv 64 0) by reflexivity.
    assert (G3_14 : getr R3 (r5 14) = v14a) by (unfold R3, R2; rewrite getr_other by rne; apply getr_same; rne).
    assert (G4_14 : getr R4 (r5 14) = v14b) by (unfold R4; apply getr_same; rne).
    assert (G4_13 : getr R4 (r5 13) = v13b) by (unfold R4, R3; rewrite getr_other by rne; apply getr_same; rne).
    assert (U13b : bv_unsigned v13b = (us - (un + ud) mod 2 ^ 64) mod 2 ^ 64).
    { unfold v13b, v13a. rewrite u_sub64, u_add64. reflexivity. }
    assert (U14b : bv_unsigned v14b = (0 - (un * 2) mod 2 ^ 64) mod 2 ^ 64).
    { unfold v14b, v14a. rewrite u_sub64, u_sll64, !u_lit64.
      replace (0 mod two64) with 0 by reflexivity. replace ((1 mod two64) mod 64) with 1 by reflexivity.
      rewrite Z.pow_1_r. reflexivity. }
    (* [comment removed for export] *)
    set (p := pc cs) in *.
    destruct (it_fetch _ _ L0 ltac:(lia)) as (w0 & F0 & E0 & D0).
    destruct (it_fetch _ _ L1 ltac:(lia)) as (w1 & F1 & E1 & D1).
    destruct (it_fetch _ _ L2 ltac:(lia)) as (w2 & F2 & E2 & D2).
    destruct (it_fetch _ _ L3 ltac:(lia)) as (w3 & F3 & E3 & D3).
    destruct (it_fetch _ _ L4 ltac:(lia)) as (w4 & F4 & E4 & D4).
    destruct (it_fetch _ _ L5 ltac:(lia)) as (w5 & F5 & E5 & D5).
    destruct (it_fetch _ _ L6 ltac:(lia)) as (w6 & F6 & E6 & D6).
    set (rom := seg_rom SEGS).
    pose proof two64_eq as T64.
    (* [comment removed for export] *)
    assert (ST1 : RiscvSemantics.step SEGS (mkst R (Z_to_bv 64 p) MR rom) = MachineOk (mkst R (Z_to_bv 64 (p + 4)) MR rom)).
    { rewrite <- !mkstR_None. rewrite (stepR_branch_ft_gen SEGS R _ MR rom None w0 BC_EQ (r5 10) (r5 11) i0m F0 E0 D0).
      - rewrite v_addi_lit by lia. reflexivity.
      - cbn [branch_taken]. fold d s. apply bv_eqb_neq. exact Hds. }
    assert (ST2 : RiscvSemantics.step SEGS (mkst R (Z_to_bv 64 (p + 4)) MR rom) = MachineOk (mkst R1 (Z_to_bv 64 (p + 8)) MR rom)).
    { rewrite <- !mkstR_None. rewrite (stepR_op_gen SEGS R _ MR rom None w1 ALU_ADD (r5 13) (r5 12) (r5 10) F1 E1 D1).
      replace (bv_eqb (r5 13) 0) with false by reflexivity.
      rewrite v_addi_lit by lia. replace (p + 4 + 4) with (p + 8) by lia. reflexivity. }
    assert (ST3 : RiscvSemantics.step SEGS (mkst R1 (Z_to_bv 64 (p + 8)) MR rom) = MachineOk (mkst R2 (Z_to_bv 64 (p + 12)) MR rom)).
    { rewrite <- !mkstR_None. rewrite (stepR_shiftimm_gen SEGS R1 _ MR rom None w2 ALU_SLL (r5 14) (r5 12) sh F2 E2 D2).
      replace (bv_eqb (r5 14) 0) with false by reflexivity. rewrite G1_12.
      replace (zext 64 sh) with (Z_to_bv 64 1) by (rewrite <- Hsh; symmetry; apply Z_to_bv_bv_unsigned || reflexivity).
      rewrite v_addi_lit by lia. replace (p + 8 + 4) with (p + 12) by lia. reflexivity. }
    assert (ST4 : RiscvSemantics.step SEGS (mkst R2 (Z_to_bv 64 (p + 12)) MR rom) = MachineOk (mkst R3 (Z_to_bv 64 (p + 16)) MR rom)).
    { rewrite <- !mkstR_None. rewrite (stepR_op_gen SEGS R2 _ MR rom None w3 ALU_SUB (r5 13) (r5 11) (r5 13) F3 E3 D3).
      replace (bv_eqb (r5 13) 0) with false by reflexivity. rewrite G2_11, G2_13.
      rewrite v_addi_lit by lia. replace (p + 12 + 4) with (p + 16) by lia. reflexivity. }
    assert (ST5 : RiscvSemantics.step SEGS (mkst R3 (Z_to_bv 64 (p + 16)) MR rom) = MachineOk (mkst R4 (Z_to_bv 64 (p + 20)) MR rom)).
    { rewrite <- !mkstR_None. rewrite (stepR_op_gen SEGS R3 _ MR rom None w4 ALU_SUB (r5 14) (r5 0) (r5 14) F4 E4 D4).
      replace (bv_eqb (r5 14) 0) with false by reflexivity. rewrite G3_0, G3_14.
      rewrite v_addi_lit by lia. replace (p + 16 + 4) with (p + 20) by lia. reflexivity. }
    assert (ST6 : RiscvSemantics.step SEGS (mkst R4 (Z_to_bv 64 (p + 20)) MR rom)
                  = MachineOk (mkst R4 (Z_to_bv 64 (p + 20 + bv_signed i5m)) MR rom)).
    { rewrite <- !mkstR_None. rewrite (stepR_branch_tk_gen SEGS R4 _ MR rom None w5 BC_GEU (r5 14) (r5 13) i5m F5 E5 D5).
      - rewrite btgt_lit by lia. reflexivity.
      - cbn [branch_taken]. rewrite G4_14, G4_13. unfold bv_ltu. rewrite U13b, U14b.
        apply negb_true_iff. apply Z.ltb_ge. exact Hbr. }
    assert (ST7 : RiscvSemantics.step SEGS (mkst R4 (Z_to_bv 64 (p + 20 + bv_signed i5m)) MR rom)
                  = MachineOk (mkst R4 (Z_to_bv 64 (x_memcpy A)) MR rom)).
    { rewrite <- !mkstR_None. rewrite (stepR_jal_link SEGS R4 _ MR rom None w6 (r5 0) jm F6 E6 D6).
      replace (bv_eqb (r5 0) 0) with true by reflexivity.
      rewrite btgt_lit by lia. rewrite HJt. reflexivity. }
    set (ms := mkst R (Z_to_bv 64 p) FULL rom).
    assert (Hms' : msteps SEGS (restrict H ms) (mkst R4 (Z_to_bv 64 (x_memcpy A)) MR rom)).
    { unfold ms. rewrite restrict_mkst. change (mrestrict H FULL) with MR.
      eapply mst_step; [reflexivity | exact ST1 |]. eapply mst_step; [reflexivity | exact ST2 |].
      eapply mst_step; [reflexivity | exact ST3 |]. eapply mst_step; [reflexivity | exact ST4 |].
      eapply mst_step; [reflexivity | exact ST5 |]. eapply mst_step; [reflexivity | exact ST6 |].
      eapply mst_step; [reflexivity | exact ST7 | apply mst_refl]. }
    (* [comment removed for export] *)
    unfold cfg_of. fold rom. fold ms.
    apply (srz_msteps_restricted_T SEGS H (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high E cs model) SEGS_wx (allowA A E cs)
             ms _ model T (lazy_cover_hid SEGS A LIMIT SINV argH FS0 HULL_ok E cs R FULL model HC) (A_wf_allowA' A E cs)
             (co_minv _ _ _ _ _ _ _ _ _ _ _ HC) (co_halt _ _ _ _ _ _ _ _ _ _ _ HC) Hms').
    intros model' Hinv' Hsame Hclean.
    change (unrestrict H (ms_mem ms) (mkst R4 (Z_to_bv 64 (x_memcpy A)) MR rom))
      with (mkst R4 (Z_to_bv 64 (x_memcpy A)) (munrestrict H FULL MR) rom).
    unfold MR, Mr. fold H. rewrite munrestrict_mrestrict.
    (* [comment removed for export] *)
    specialize (Hk E R4 model' (conj (env_agree_refl _ _) (env_agree_refl _ _))).
    unfold cfg_of, pc in Hk. cbn [with_ss a_ss mk_ss s_pc] in Hk.
    apply Hk; [| apply (same_but_materialized_frame _ _ Hsame) | exact (APS.mvis_of_materialized _ _ Hsame) | ].
    2: { apply APS.hid_extF0; [reflexivity | exact (APS.mvis_of_materialized _ _ Hsame)]. }
    eapply cs_ok_frame; [exact SINV_frame | exact HC | exact Hsame | exact Hinv' | | reflexivity | | intros; reflexivity].
    - (* [comment removed for export] *)
      cbn [s_regs].
      assert (Q0 : (0%bv : bv 5) = r5 0) by (apply bv_eq; reflexivity).
      assert (Q10 : (10%bv : bv 5) = r5 10) by (apply bv_eq; reflexivity).
      assert (Q11 : (11%bv : bv 5) = r5 11) by (apply bv_eq; reflexivity).
      assert (Q12 : (12%bv : bv 5) = r5 12) by (apply bv_eq; reflexivity).
      assert (Q13 : (13%bv : bv 5) = r5 13) by (apply bv_eq; reflexivity).
      assert (Q14 : (14%bv : bv 5) = r5 14) by (apply bv_eq; reflexivity).
      set (sr0 := s_regs (a_ss cs)) in *.
      pose proof (regs_ok_upd E _ _ (r5 13) v13a (mkAlu ALU_ADD (sr_get sr0 12%bv) (sr_get sr0 10%bv)) HR) as RU1.
      replace (bv_eqb (r5 13) 0) with false in RU1 by reflexivity.
      specialize (RU1 ltac:(rewrite mkAlu_denot, <- (HR 12%bv), <- (HR 10%bv), Q12, Q10; reflexivity)).
      fold R1 in RU1. set (sr1 := sr_upd _ _ _) in RU1.
      pose proof (regs_ok_upd E _ _ (r5 14) v14a (mkAlu ALU_SLL (sr_get sr1 12%bv) (ELit 1)) RU1) as RU2.
      replace (bv_eqb (r5 14) 0) with false in RU2 by reflexivity.
      specialize (RU2 ltac:(rewrite mkAlu_denot, <- (RU1 12%bv), Q12, G1_12; reflexivity)).
      fold R2 in RU2. set (sr2 := sr_upd sr1 _ _) in RU2.
      pose proof (regs_ok_upd E _ _ (r5 13) v13b (mkAlu ALU_SUB (sr_get sr2 11%bv) (sr_get sr2 13%bv)) RU2) as RU3.
      replace (bv_eqb (r5 13) 0) with false in RU3 by reflexivity.
      specialize (RU3 ltac:(rewrite mkAlu_denot, <- (RU2 11%bv), <- (RU2 13%bv), Q11, Q13, G2_11, G2_13; reflexivity)).
      fold R3 in RU3. set (sr3 := sr_upd sr2 _ _) in RU3.
      pose proof (regs_ok_upd E _ _ (r5 14) v14b (mkAlu ALU_SUB (sr_get sr3 0%bv) (sr_get sr3 14%bv)) RU3) as RU4.
      replace (bv_eqb (r5 14) 0) with false in RU4 by reflexivity.
      specialize (RU4 ltac:(rewrite mkAlu_denot, <- (RU3 0%bv), <- (RU3 14%bv), Q0, Q14, G3_0, G3_14; reflexivity)).
      fold R4 in RU4. exact RU4.
    - (* [comment removed for export] *)
      cbn [s_know]. exact HK.
  Qed.

  Theorem xn_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (MVN.xn IT A args).
  Proof. intros args. apply node1_stmtF_stmt. apply xn_soundF. Qed.
End Sound.
End MVNS.
