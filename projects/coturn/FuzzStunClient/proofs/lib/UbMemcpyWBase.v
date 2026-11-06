(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Ubsan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import UbMemcpyBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk.store_ok_peel ::= store_ok_peel_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.

Abbreviation RSEGS := Ubsan.M.loaded_segments.

(* [comment removed for export] *)
Record mcW (mem0 : word -> option byte) (dst src : word) (n : Z) : Prop := MCW {
  Wn : (0 <= n < 2 ^ 64)%Z;
  Wsrc : forall i, (0 <= i < n)%Z -> exists b, rdn RSEGS mem0 (at_ src i) 1 = Some [b];
  Wdst : store_ok RSEGS mem0 dst (Z.to_nat n) = true;
  Wnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Wnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

(* [comment removed for export] *)
Definition rdv (m : word -> option byte) (a : word) (k : nat) : list byte :=
  match rdn RSEGS m a k with Some l => l | None => repeat (Z_to_bv 8 0) k end.
Definition rd1 (m : word -> option byte) (a : word) : byte := nth 0 (rdv m a 1) (Z_to_bv 8 0).

Lemma length_rdv : forall m a k, length (rdv m a k) = k.
Proof.
  intros m a k. unfold rdv. destruct (rdn RSEGS m a k) as [l|] eqn:E.
  - exact (rdn_length _ _ _ _ _ E).
  - apply repeat_length.
Qed.

(* [comment removed for export] *)
Definition LEN (acc : list byte) (k : Z) : Prop := Z.of_nat (length acc) = k.

Lemma LEN_nil : LEN [] 0.
Proof. reflexivity. Qed.
Lemma LEN_app4 : forall acc k (v : word), LEN acc k -> LEN (acc ++ word_to_le_bytes 4 v) (k + 4).
Proof. intros acc k v H. unfold LEN in *. rewrite length_app, length_N_to_le_bytes. lia. Qed.
Lemma LEN_app1 : forall acc k (b : byte), LEN acc k -> LEN (acc ++ [b]) (k + 1).
Proof. intros acc k b H. unfold LEN in *. rewrite length_app. cbn [length]. lia. Qed.
Lemma LEN_to_nat : forall acc k, LEN acc k -> length acc = Z.to_nat k.
Proof. intros acc k H. unfold LEN in H. lia. Qed.

(* [comment removed for export] *)
Lemma rdn_grows : forall m m' k (a : word) l,
  mem_grows m m' -> rdn RSEGS m a k = Some l -> exists l', rdn RSEGS m' a k = Some l' /\ length l' = k.
Proof.
  intros m m' k. induction k as [|k IH]; intros a l Hg H.
  - exists []. split; reflexivity.
  - cbn [rdn] in H |- *.
    destruct (match m a with Some b => Some b | None => seg_rom RSEGS a end) as [b|] eqn:Eb; [|discriminate].
    destruct (rdn RSEGS m (a + 1) k) as [rest|] eqn:Er; [|discriminate].
    destruct (IH (a + 1) rest Hg Er) as [l' [Hl' Hlen]]. rewrite Hl'.
    assert (Hb' : exists b', (match m' a with Some b0 => Some b0 | None => seg_rom RSEGS a end) = Some b').
    { destruct (m' a) as [b'|] eqn:E'; [eauto|].
      destruct (m a) as [b0|] eqn:E0.
      - exfalso. apply (Hg a); [rewrite E0; discriminate|exact E'].
      - exists b. exact Eb. }
    destruct Hb' as [b' ->]. exists (b' :: l'). split; [reflexivity|cbn; lia].
Qed.

Section MCW.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Hypothesis HOK : mcW mem0 dst src n.

  Let Hn := Wn _ _ _ _ HOK.
  Let Hsrc := Wsrc _ _ _ _ HOK.
  Let Hdst := Wdst _ _ _ _ HOK.
  Let Hnws := Wnws _ _ _ _ HOK.
  Let Hnwd := Wnwd _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition MW (acc : list byte) : word -> option byte := wbytes mem0 dst acc.

  Lemma MW_nil : MW [] = mem0.
  Proof. reflexivity. Qed.

  Lemma MW_app : forall acc l, wbytes (MW acc) (at_ dst (Z.of_nat (length acc))) l = MW (acc ++ l).
  Proof. intros acc l. unfold MW. symmetry. apply wbytes_app. Qed.

  (* [comment removed for export] *)
  Lemma rd_src0 : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
    exists l, rdn RSEGS mem0 (at_ src j) m = Some l /\ length l = m.
  Proof.
    intros j m. revert j. induction m as [|m IH]; intros j Hj Hm.
    - exists []. split; reflexivity.
    - destruct (Hsrc j ltac:(lia)) as [b Hb]. rewrite rdn_1 in Hb || cbn [rdn] in Hb.
      cbn [rdn].
      destruct (match mem0 (at_ src j) with Some b0 => Some b0 | None => seg_rom RSEGS (at_ src j) end) as [b0|]; [|discriminate].
      destruct (IH (j + 1)%Z ltac:(lia) ltac:(lia)) as [l [Hl Hlen]].
      rewrite at_succ, Hl. exists (b0 :: l). split; [reflexivity|cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma rd_srcW : forall acc j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
    exists l, rdn RSEGS (MW acc) (at_ src j) m = Some l /\ length l = m.
  Proof.
    intros acc j m Hj Hm. destruct (rd_src0 j m Hj Hm) as [l [Hl _]].
    destruct (rdn_grows mem0 (MW acc) m (at_ src j) l (wbytes_grows acc mem0 dst) Hl) as [l' [Hl' Hlen']]. eauto.
  Qed.

  Lemma rdv_spec : forall acc j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
    rdn RSEGS (MW acc) (at_ src j) m = Some (rdv (MW acc) (at_ src j) m).
  Proof.
    intros acc j m Hj Hm. destruct (rd_srcW acc j m Hj Hm) as [l [Hl _]]. unfold rdv. rewrite Hl. reflexivity.
  Qed.

  Lemma rd1_spec : forall acc j, (0 <= j)%Z -> (j + 1 <= n)%Z ->
    rdn RSEGS (MW acc) (at_ src j) 1 = Some [rd1 (MW acc) (at_ src j)].
  Proof.
    intros acc j Hj H1. destruct (rd_srcW acc j 1 Hj ltac:(lia)) as [l [Hl Hlen]].
    unfold rd1, rdv. rewrite Hl. destruct l as [|b [|? ?]]; cbn in Hlen; try discriminate. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma wr_dstW : forall acc j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z ->
    store_ok RSEGS (MW acc) (at_ dst j) m = true.
  Proof.
    intros acc j m Hj Hm. unfold MW.
    apply (store_ok_at RSEGS mem0 dst (Z.to_nat n)); try assumption; rewrite ?Z2Nat.id; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Lemma mc_lbuW : forall regs pc rom w rd rs (imm : bv 12) acc j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MW acc) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (rd1 (MW acc) (at_ src j)))) (v_addi pc 4) (MW acc) rom).
  Proof.
    intros regs pc rom w rd rs imm acc j0 j Hf He Hd Hrs Hj Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd1_spec; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_lwW : forall regs pc rom w rd rs (imm : bv 12) acc j0 j,
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= j)%Z -> (j + 4 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MW acc) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LWv (rdv (MW acc) (at_ src j) 4))) (v_addi pc 4) (MW acc) rom).
  Proof.
    intros regs pc rom w rd rs imm acc j0 j Hf He Hd Hrs Hj Hj0 Hj4.
    eapply step_lw; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rdv_spec acc j 4); lia.
    - symmetry. apply u_lez4. apply length_rdv.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_sbW : forall regs pc rom w rs1 rs2 (imm : bv 12) acc k k0 (v : word),
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ1 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> LEN acc k -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v ->
    (0 <= k)%Z -> (k + 1 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MW acc) rom) =
    MachineOk (mkst regs (v_addi pc 4) (MW (acc ++ [Z_to_bv 8 (bv_unsigned v)])) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm acc k k0 v Hf He Hd Hrs1 HL Hk Hrs2 Hk0 Hk1.
    unfold LEN in HL. rewrite <- MW_app, HL.
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | reflexivity |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dstW; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma mc_swW : forall regs pc rom w rs1 rs2 (imm : bv 12) acc k k0 (v : word),
    fetch_word RSEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store SZ4 rs1 rs2 imm, 4%Z) ->
    getr regs rs1 = at_ dst k0 -> LEN acc k -> (k0 + bv_signed imm = k)%Z ->
    getr regs rs2 = v ->
    (0 <= k)%Z -> (k + 4 <= n)%Z ->
    RiscvSemantics.step RSEGS (mkst regs pc (MW acc) rom) =
    MachineOk (mkst regs (v_addi pc 4) (MW (acc ++ word_to_le_bytes 4 v)) rom).
  Proof.
    intros regs pc rom w rs1 rs2 imm acc k k0 v Hf He Hd Hrs1 HL Hk Hrs2 Hk0 Hk4.
    unfold LEN in HL. rewrite <- MW_app, HL.
    eapply step_sw_at; [exact Hf | exact He | exact Hd | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dstW; lia.
  Qed.
End MCW.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma LEN_eqk : forall a k k', LEN a k -> k = k' -> LEN a k'.
Proof. intros a k k' H <-. exact H. Qed.

(* [comment removed for export] *)
Lemma runsW_trans : forall segs (s0 : machine_state)
    (st1 : bvmap 5 word -> list byte -> machine_state) (P1 : bvmap 5 word -> list byte -> Prop)
    (st2 : bvmap 5 word -> list byte -> machine_state) (P2 : bvmap 5 word -> list byte -> Prop),
  (exists r1 a1, msteps segs s0 (st1 r1 a1) /\ P1 r1 a1) ->
  (forall r1 a1, P1 r1 a1 -> exists r2 a2, msteps segs (st1 r1 a1) (st2 r2 a2) /\ P2 r2 a2) ->
  exists r2 a2, msteps segs s0 (st2 r2 a2) /\ P2 r2 a2.
Proof.
  intros segs s0 st1 P1 st2 P2 (r1 & a1 & R1 & H1) K.
  destruct (K r1 a1 H1) as (r2 & a2 & R2 & H2).
  exists r2, a2. split; [eapply msteps_trans; eassumption | exact H2].
Qed.

(* [comment removed for export] *)
Ltac cur_acc mem0 dst :=
  match goal with |- msteps _ (mkst _ _ (MW mem0 dst ?a) _) _ => a end.
Ltac len_hyp a :=
  match goal with H : LEN a _ |- _ => H end.
(* [comment removed for export] *)
Ltac solve_len :=
  lazymatch goal with |- LEN ?a ?k =>
    first [ let H := len_hyp a in first [exact H | eapply (LEN_eqk a _ k H); lia]
          | unfold LEN; repeat rewrite length_app; rewrite ?length_N_to_le_bytes; cbn [length];
            repeat match goal with H : LEN _ _ |- _ => unfold LEN in H end; lia ] end.

(* [comment removed for export] *)
Ltac mlwW HOK F D jj :=
  chain_step; [reflexivity
    | eapply (mc_lwW _ _ _ _ HOK) with (j := jj);
      [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia]
    | step_simpl]; vnorm.
Ltac mlbuW HOK F D jj :=
  chain_step; [reflexivity
    | eapply (mc_lbuW _ _ _ _ HOK) with (j := jj);
      [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | imm_norm; lia | lia | lia]
    | step_simpl]; vnorm.

(* [comment removed for export] *)
Ltac mswW HOK mem0 dst F D kk :=
  let a := cur_acc mem0 dst in let HL := len_hyp a in
  let HLk := fresh "LENk" in
  assert (HLk : LEN a kk) by (first [exact HL | eapply (LEN_eqk a _ kk HL); lia]);
  chain_step; [reflexivity
    | eapply (mc_swW _ _ _ _ HOK) with (k := kk) (acc := a);
      [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | exact HLk | imm_norm; lia
      | gres; rwH; reflexivity | lia | lia]
    | step_simpl];
  lazymatch goal with |- msteps _ (mkst _ _ (MW mem0 dst (a ++ word_to_le_bytes 4 ?v)) _) _ =>
    pose proof (LEN_app4 a kk v HLk) end.
Ltac msbW HOK mem0 dst F D kk :=
  let a := cur_acc mem0 dst in let HL := len_hyp a in
  let HLk := fresh "LENk" in
  assert (HLk : LEN a kk) by (first [exact HL | eapply (LEN_eqk a _ kk HL); lia]);
  chain_step; [reflexivity
    | eapply (mc_sbW _ _ _ _ HOK) with (k := kk) (acc := a);
      [exact F | reflexivity | exact D | gres; rwH; rewrite ?at_addi; reflexivity | exact HLk | imm_norm; lia
      | gres; rwH; reflexivity | lia | lia]
    | step_simpl];
  lazymatch goal with |- msteps _ (mkst _ _ (MW mem0 dst (a ++ [?b])) _) _ =>
    pose proof (LEN_app1 a kk b HLk) end.
