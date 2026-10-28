(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg
  AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums LibSym SegRun SegPlan SegPlanAuto. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10PlanKit_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import L5Defs L5Core
  FrmInv. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import Pm10FrmInv_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import CutVF DecIface DecIfaceU DecJson DecScanPure DecOkDefs DecOkSem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import DecfloatPre_u DecfloatAt_u DecfloatOk_u. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import StrtodPure StrtodIface.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.FCutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutL5 CutOpsD CutAutoD. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutCert Require Import Pm10CutKitD_u.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U.FCutGen Require Import Cut_fshead_csrc_u.
Import ListNotations. Import AX2. Import AX2B. Import AX2S. Import DOK.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module FHO.
Definition GADDR : Z := 0xf6a70.   Definition TPV : Z := 0xd6800.   Definition E1PC : Z := 0xb2a80.   Definition E2PC : Z := 0xb2bd0.
Definition F0 : list SGP.region := [(EVar 2, -8672, ELit 8672); (EVar 10, 8, ELit 8)].
Fixpoint find_byte (kn : list kentry) (o : Z) : option nat :=
  match kn with
  | [] => None
  | KWord (SA (EVar 32) o') 1 (EVar v) :: r => if Z.eqb o' o then Some v else find_byte r o
  | _ :: r => find_byte r o
  end.
Lemma find_byte_In : forall kn o v, find_byte kn o = Some v -> In (KWord (SA (EVar 32) o) 1 (EVar v)) kn.
Proof.
  induction kn as [|K r IH]; intros o v H; [discriminate|]. cbn [find_byte] in H.
  destruct K as [[b o'] w x| | | | | | | | |]; try (right; exact (IH _ _ H)).
  destruct b as [|n| | | | | |]; try (right; exact (IH _ _ H)).
  do 33 (destruct n as [|n]; try (right; exact (IH _ _ H))).
  do 2 (destruct w as [|w]; try (right; exact (IH _ _ H))).
  destruct x as [|v'| | | | | |]; try (right; exact (IH _ _ H)).
  destruct (Z.eqb_spec o' o) as [->|]; [injection H as ->; left; reflexivity | right; exact (IH _ _ H)].
Qed.
Definition rawx (e : expr) : expr := EAlu ALU_SLTU (EAlu ALU_SUB (EAlu ALU_AND e (ELit (-33))) (ELit 88)) (ELit 1).
Definition live_chk (e2 : bool) (q : Z) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  (CL.ps_reg_is ps 2 (APC.eaddz (EVar 2) (-8416)) && CL.ps_reg_is ps 3 (EVar 3) && CL.ps_reg_is ps 4 (ELit TPV) && CL.ps_reg_is ps 21 (EVar 10) && CL.ps_reg_is ps 23 (ELit 1)
   && CL.ps_reg_is ps 18 (ELit 53) && CL.ps_reg_is ps 22 (ELit 18446744073709550542) && CL.ps_reg_is ps 24 (ELit 1)
   && (CL.ps_reg_is ps 9 (ELit 1) || CL.ps_reg_is ps 9 (ELit 18446744073709551615)) && CL.ps_reg_is ps 20 (ELit GADDR)
   && forallb (fun ro : nat * Z => has cells (KWord (SA (EVar 2) (snd ro - 2032)) 8 (EVar (fst ro)))) PDC.SAVES
   && has cells (KWord (SA (EVar 2) (-120)) 8 (EVar 33)) && has cells (KWord (SA (ELit 0) GADDR) 8 (EVar 33))
   && has cells (KWord (SA (EVar 10) 8) 8 (APC.eaddz (EVar 32) (q + (if e2 then 2 else 1))))
   && has cells (KWord (SA (EVar 10) 184) 8 (ELit 18446744073709551615)) && has cells (KWord (SA (EVar 10) 192) 8 (ELit 0))
   && match find_byte cells q with
      | Some cv => if e2 then DOS.rng_in cells (EVar cv) 48 48 else (DOS.rng_in cells (EVar cv) 49 57 && CL.ps_reg_is ps 10 (EVar cv))%bool
      | None => false
      end)%bool.
Definition dead_chk (q : Z) (ps : SR.post_spec) : bool :=
  let cells := SR.ps_cells ps in
  match find_byte cells q, find_byte cells (q + 1) with
  | Some c0, Some c2 => (DOS.rng_in cells (EVar c0) 48 48 && DOS.rng_in cells (EVar c2) 0 255 && has cells (KRange (rawx (EVar c2)) 1 1))%bool
  | _, _ => false
  end.

Section Bridges.
Context {SCFG_P : ScfgP}.
Hypothesis FMODL : CVF.vf_contract RSEGS 0xb4980 192 DFO.IMGc.
Hypothesis SCX : PDC.scanexp_contract RSEGS PDCU.ubsan11.
Variable R : bvmap 5 word.
Variable M0 : word -> option byte.
Variable model0 : Model.
Variable K : ShapeAlg.TSet.
Variables sp F s CAN : Z.
Variable txt : list Z.
Variable E0 : env.
Variable q : Z.
Definition N : Z := Z.of_nat (length txt).
Definition txt' : list Z := txt ++ [0].
Hypothesis Hh : m_halted model0 = None.
Hypothesis Hl : m_vm_lazy model0 = [].
Hypothesis EVr : forall r, (r < 32)%nat -> ev E0 r = getr R (Z_to_bv 5 (Z.of_nat r)).
Hypothesis EVs : bv_unsigned (ev E0 32) = s.
Hypothesis EVc : ev E0 33 = Z_to_bv 64 CAN.
Hypothesis Rsp : PDC.rz R 2 = sp.
Hypothesis Hal : sp mod 16 = 0.
Hypothesis Hrng : PDC.STK_FLOOR + PSI.WIN <= sp <= 2 ^ 47.
Hypothesis Hdef : L5.defined M0 (sp - PSI.WIN) PSI.WIN.
Hypothesis RF : PDC.rz R 10 = F.
Hypothesis R4 : PDC.rz R 4 = TPV.
Hypothesis Hret : Hoare.ret_ok (getr R (PDC.reg_of 1)).
Hypothesis Hfile : PDC.file_ok RSEGS M0 F s.
Hypothesis Hfs : PDC.apart (F + 8) 192 (sp - PSI.WIN) PSI.WIN.
Hypothesis Hguard : L5.u64_at RSEGS M0 GADDR CAN.
Hypothesis Hgap : PDC.apart GADDR 8 (sp - PSI.WIN) PSI.WIN.
Hypothesis Htext : PDC.text_ok RSEGS M0 s txt.
Hypothesis Htap : PDC.text_apart PDCU.ubsan11 s txt F (sp - PSI.WIN) PSI.WIN.
Hypothesis Herrw : L5.writable RSEGS M0 (TPV - 164) 4.
Hypothesis Himg : L5.img_clear M0 65536 801400.

Hypothesis Hq : 0 <= q <= 1 /\ q < N.
Hypothesis Hfull : q + PD.dec_len (skipn (Z.to_nat q) txt) = N.
Hypothesis Hafter0 : nth (Z.to_nat q) txt' 0 = 48 -> PSP.after0_ok (nth (Z.to_nat (q + 1)) txt' 0).
Hypothesis HK : forall (fx' : FPState) R' M', FrmInv.fp_ok fx' ->
      (forall x : nat, In x PSI.CSAVED -> getr R' (PDC.reg_of x) = getr R (PDC.reg_of x)) ->
      (forall a : word, ~ (sp - PSI.WIN <= bv_unsigned a < sp) -> ~ (F + 8 <= bv_unsigned a < F + 16) -> ~ (TPV - 164 <= bv_unsigned a < TPV - 160) -> M' a = M0 a) ->
      mem_grows M0 M' -> L5.u64_at RSEGS M' (F + 8) (s + N) ->
      srealizes RSEGS SCFG (mkCfg (@mkst fx' R' (getr R (PDC.reg_of 1)) M' (seg_rom RSEGS)) model0) K.

Definition NFh : nat := 34.
Abbreviation Amb := (CL.pure_amb NFh E0 M0 model0 F0).

Lemma EV2 : bv_unsigned (ev E0 2) = sp. Proof. rewrite EVr by lia. exact Rsp. Qed.
Lemma EV10 : bv_unsigned (ev E0 10) = F. Proof. rewrite EVr by lia. exact RF. Qed.
Lemma out_F0 : forall x : word, ~ (sp - 8672 <= bv_unsigned x < sp) -> ~ (F + 8 <= bv_unsigned x < F + 16) -> SGP.outside E0 F0 x.
Proof.
  intros x H1 H2. destruct Hfile as (_ & _ & _ & _ & HF1 & HF2). unfold PDC.STK_FLOOR, PSI.WIN in *. unfold SGP.outside, F0.
  repeat apply Forall_cons; [| | apply Forall_nil]; rewrite ?(DOS.estart_reg E0 2 _ sp EV2), ?(DOS.estart_reg E0 10 _ F EV10); rewrite DOS.elen_lit by lia; lia.
Qed.
Lemma text_byte : forall i, 0 <= i <= N -> L5.u8_at RSEGS M0 (s + i) (nth (Z.to_nat i) txt' 0) /\ 0 <= nth (Z.to_nat i) txt' 0 < 256.
Proof.
  destruct Htext as (Tb & Tn & _ & _ & _ & _ & Tr). intros i Hi. unfold txt'. destruct (Z.eq_dec i N) as [->|Hne].
  - rewrite app_nth2 by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat by (unfold N; lia). cbn [nth]. split; [exact Tn | lia].
  - assert (Hlt : (Z.to_nat i < length txt)%nat) by (unfold N in *; lia). rewrite app_nth1 by exact Hlt. split.
    + pose proof (Tb (Z.to_nat i) Hlt) as B. rewrite Z2Nat.id in B by lia. exact B.
    + rewrite Forall_forall in Tr. apply Tr. apply nth_In. exact Hlt.
Qed.

Lemma leaf_amb : forall (i : nat) c ps E (M1 : word -> option byte) m1 E' R' M', CC.cp_F c = F0 -> (NFh <= CC.cp_nx c)%nat ->
  CL.pure_amb NFh E0 M0 model0 F0 i E M1 m1 -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts RSEGS c ps E' R' M1 M' ->
  m1 = model0 /\ env_agree NFh E0 E' /\ (forall a : word, SGP.outside E0 F0 a -> M' a = M0 a) /\ mem_grows M0 M'.
Proof.
  intros i c ps E M1 m1 E' R' M' HF Hnf HAmb Hag HLF.
  assert (HA' : CL.pure_amb NFh E0 M0 model0 F0 0%nat E' M' m1).
  { eapply CL.pure_amb_step with (c := c); [| exact Hnf | exact HAmb | exact Hag | exact HLF | apply CC.env_agree_refl].
    intros Ex a Hagx Ho. rewrite HF. exact (CL.outside_agree_F0 NFh E0 F0 eq_refl Ex a Hagx Ho). }
  exact HA'.
Qed.
Lemma leaf_byte : forall c ps E' R' (M1 M' : word -> option byte) o cv, CC.leaf_facts RSEGS c ps E' R' M1 M' -> env_agree NFh E0 E' ->
  (forall a : word, SGP.outside E0 F0 a -> M' a = M0 a) ->
  find_byte (SR.ps_cells ps) o = Some cv -> 0 <= o <= N -> 0 <= uE E' (EVar cv) <= 255 -> uE E' (EVar cv) = nth (Z.to_nat o) txt' 0.
Proof.
  intros c ps E' R' M1 M' o cv HLF Hag0 Hfr Hf Ho Rc. apply find_byte_In in Hf. pose proof (CC.lf_cells _ _ _ _ _ _ _ HLF _ Hf) as Y.
  destruct Htext as (_ & _ & TQ1 & TQ2 & TQ3 & _ & _). fold N in TQ2, TQ3. destruct Htap as (Ta1 & Ta2 & _). fold N in Ta1, Ta2. unfold PDC.apart, PSI.WIN in *.
  assert (U32 : bv_unsigned (ev E' 32) = s) by (rewrite <- (proj1 Hag0 32%nat) by (unfold NFh; lia); exact EVs).
  apply (kword8_elim RSEGS E' M' _ _ (s + o)) in Y; [|apply (DOS.estart_reg E' 32 o s U32)].
  unfold uE in *. rewrite Z.mod_small in Y by lia. destruct (text_byte o Ho) as [Ht Rt].
  assert (Hm0 : L5.u8_at RSEGS M0 (s + o) (bv_unsigned (edenot E' (EVar cv)))).
  { apply (u8_at_same RSEGS M' M0 (s + o) _ ltac:(lia) ltac:(lia)); [|exact Y]. intros x Hx. symmetry. apply Hfr. apply out_F0; rewrite Hx; lia. }
  symmetry. exact (u8_at_inj RSEGS M0 _ _ _ Ht Hm0 Rt ltac:(lia)).
Qed.

Lemma dead_leaf : forall (i : nat) c ps, CC.cp_F c = F0 -> (NFh <= CC.cp_nx c)%nat -> dead_chk q ps = true ->
  forall (fx' : FPState) E (M1 : word -> option byte) m1 E' R' M', Amb i E M1 m1 -> FrmInv.fp_ok fx' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts RSEGS c ps E' R' M1 M' ->
  srealizes RSEGS SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom RSEGS)) m1) K.
Proof.
  intros i c ps HF Hnf H fx' E M1 m1 E' R' M' HAmb HFP Hag HLF. exfalso.
  destruct (leaf_amb i c ps E M1 m1 E' R' M' HF Hnf HAmb Hag HLF) as (_ & Hag0 & Hfr & _).
  unfold dead_chk in H. destruct (find_byte (SR.ps_cells ps) q) as [c0|] eqn:F1; [|discriminate]. destruct (find_byte (SR.ps_cells ps) (q + 1)) as [c2|] eqn:F2; [|discriminate].
  do 2 (apply andb_prop in H as [H ?X]).
  assert (HK' : know_ok RSEGS E' M' (SR.ps_cells ps)) by (apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY)).
  pose proof (DOS.rng_in_sem RSEGS E' M' _ _ _ _ HK' H) as R0. pose proof (DOS.rng_in_sem RSEGS E' M' _ _ _ _ HK' X0) as R2.
  pose proof (leaf_byte c ps E' R' M1 M' q c0 HLF Hag0 Hfr F1 ltac:(lia) ltac:(lia)) as B0.
  pose proof (leaf_byte c ps E' R' M1 M' (q + 1) c2 HLF Hag0 Hfr F2 ltac:(lia) ltac:(lia)) as B2.
  pose proof (Hafter0 ltac:(lia)) as A0. rewrite <- B2 in A0. apply PSP.after0_not_x in A0. apply A0.
  pose proof (DOS.know_in RSEGS E' M' _ _ HK' X) as Y. cbn [kentry_ok] in Y. unfold rawx in Y. cbn [edenot] in Y. rewrite u_sltu64, u_sub64, u_and64 in Y.
  change (bv_unsigned (Z_to_bv 64 (-33))) with (2 ^ 64 - 33) in Y. change (bv_unsigned (Z_to_bv 64 88)) with 88 in Y. change (bv_unsigned (Z_to_bv 64 1)) with 1 in Y.
  unfold uE in *. cbn [edenot] in *. set (x := bv_unsigned (ev E' c2)) in *.
  pose proof (DOS.byte_enum (fun x => if (Z.land x (2 ^ 64 - 33) - 88) mod 2 ^ 64 <? 1 then Z.land x (2 ^ 64 - 33) =? 88 else true) ltac:(vm_compute; reflexivity) x R2) as Z. cbv beta in Z.
  destruct ((Z.land x (2 ^ 64 - 33) - 88) mod 2 ^ 64 <? 1); [apply Z.eqb_eq; exact Z | lia].
Qed.

Lemma u64_at_mod : forall (M : word -> option byte) a v, L5.u64_at RSEGS M a (bv_unsigned (Z_to_bv 64 v)) -> L5.u64_at RSEGS M a v.
Proof. intros M a v H. unfold L5.u64_at in *. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.

Lemma reg_lit : forall c ps E' R' (M1 M' : word -> option byte) n z, CC.leaf_facts RSEGS c ps E' R' M1 M' -> CL.ps_reg_is ps n (ELit z) = true -> 0 <= z < 2 ^ 64 -> PDC.rz R' n = z.
Proof. intros c ps E' R' M1 M' n z HLF H Hz. unfold PDC.rz, PDC.reg_of. rewrite (CL.ps_reg_is_sound RSEGS c ps E' R' M1 M' n _ HLF H). cbn [edenot]. apply u64_of_Z. exact Hz. Qed.

Lemma live_leaf : forall (i : nat) c ps (e2 : bool), CC.cp_F c = F0 -> (NFh <= CC.cp_nx c)%nat -> SR.ps_pc ps = (if e2 then E2PC else E1PC) -> live_chk e2 q ps = true ->
  forall (fx' : FPState) E (M1 : word -> option byte) m1 E' R' M', Amb i E M1 m1 -> FrmInv.fp_ok fx' -> env_agree (CC.cp_nx c) E E' -> CC.leaf_facts RSEGS c ps E' R' M1 M' ->
  srealizes RSEGS SCFG (mkCfg (@mkst fx' R' (Z_to_bv 64 (SR.ps_pc ps)) M' (seg_rom RSEGS)) m1) K.
Proof.
  intros i c ps e2 HF Hnf Hpc H fx' E M1 m1 E' R' M' HAmb HFP Hag HLF.
  destruct (leaf_amb i c ps E M1 m1 E' R' M' HF Hnf HAmb Hag HLF) as (-> & Hag0 & Hfr & Hgr).
  unfold live_chk in H. do 16 (apply andb_prop in H as [H ?X]).
  assert (HK' : know_ok RSEGS E' M' (SR.ps_cells ps)) by (apply Forall_forall; intros Y HY; exact (CC.lf_cells _ _ _ _ _ _ _ HLF Y HY)).
  destruct Hfile as (Hf8 & Hf184 & Hf192 & Hfw & HF1 & HF2). destruct Htext as (Tb & Tn & TQ1 & TQ2 & TQ3 & Td & Tr). destruct Htap as (Ta1 & Ta2 & Ta3).
  fold N in Tn, TQ2, TQ3, Td, Ta1, Ta2, Ta3. unfold PDC.STK_FLOOR, PSI.WIN, PDC.apart in *. cbn [PDC.a_TP PDCU.ubsan11] in Ta3. change (878592 - 164) with (TPV - 164) in Ta3.
  assert (EVf : forall n, (n < 34)%nat -> ev E' n = ev E0 n) by (intros n Hn; symmetry; apply (proj1 Hag0); exact Hn).
  assert (U2 : bv_unsigned (ev E' 2) = sp) by (rewrite EVf by lia; exact EV2).
  assert (U10 : bv_unsigned (ev E' 10) = F) by (rewrite EVf by lia; exact EV10).
  assert (U32 : bv_unsigned (ev E' 32) = s) by (rewrite EVf by lia; exact EVs).
  set (SP := sp - 8416). set (dl := if e2 then 2 else 1). set (tq := skipn (Z.to_nat q) txt).
  assert (Ltq : Z.of_nat (length tq) = N - q) by (unfold tq; rewrite length_skipn; unfold N in *; lia).
  assert (OUT : forall x : word, ~ (sp - 8672 <= bv_unsigned x < sp) -> ~ (F + 8 <= bv_unsigned x < F + 16) -> M' x = M0 x) by (intros x A1 A2; apply Hfr; apply out_F0; assumption).
  assert (TXT' : forall j, 0 <= j <= N -> L5.u8_at RSEGS M' (s + j) (nth (Z.to_nat j) txt' 0)).
  { intros j Hj. apply (u8_at_same RSEGS M0 M' (s + j) _ ltac:(lia) ltac:(lia)); [|exact (proj1 (text_byte j Hj))]. intros x Hx. apply OUT; rewrite Hx; lia. }
  rewrite Hpc.
  replace (if e2 then E2PC else E1PC) with (if e2 then PDC.a_E2 PDCU.ubsan11 else PDC.a_E1 PDCU.ubsan11) by (destruct e2; reflexivity).
  destruct (find_byte (SR.ps_cells ps) q) as [cv|] eqn:Fb; [|discriminate X].
  eapply (DFT.decfloat_ok FMODL SCX e2 fx' R' M' model0 K SP F (s + q + dl) (s + q) CAN (fun r => PDC.rz R r) tq Hh Hl HFP).
  -
    unfold PDC.dec_pre, PDC.FRAME, PDC.SCR_D, PDC.STK_FLOOR. cbn [PDC.a_G PDC.a_TP PDC.a_img_lo PDC.a_img_hi PDCU.ubsan11].
    assert (G2 : PDC.rz R' 2 = SP).
    { unfold PDC.rz, PDC.reg_of. rewrite (CL.ps_reg_is_sound RSEGS c ps E' R' M1 M' 2 _ HLF H). fold (uE E' (APC.eaddz (EVar 2) (-8416))).
      unfold uE, APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite U2. change (bv_unsigned (Z_to_bv 64 (-8416))) with (2 ^ 64 - 8416).
      replace (sp + (2 ^ 64 - 8416)) with (sp - 8416 + 1 * 2 ^ 64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. unfold SP. lia. }
    split; [exact G2|]. split; [unfold SP; rewrite Zminus_mod, Hal; reflexivity|]. split; [unfold SP; lia|]. split; [unfold SP; lia|].
    split; [unfold PDC.rz, PDC.reg_of; rewrite (CL.ps_reg_is_sound RSEGS c ps E' R' M1 M' 21 _ HLF X12); exact U10|].
    split; [exact (reg_lit c ps E' R' M1 M' 23 1 HLF X11 ltac:(lia))|]. split; [exact (reg_lit c ps E' R' M1 M' 18 53 HLF X10 ltac:(lia))|].
    split; [exact (reg_lit c ps E' R' M1 M' 22 _ HLF X9 ltac:(lia))|]. split; [exact (reg_lit c ps E' R' M1 M' 24 1 HLF X8 ltac:(lia))|].
    split; [apply orb_prop in X7 as [X7|X7]; [left; exact (reg_lit c ps E' R' M1 M' 9 1 HLF X7 ltac:(lia)) | right; exact (reg_lit c ps E' R' M1 M' 9 _ HLF X7 ltac:(lia))]|].
    split; [exact (reg_lit c ps E' R' M1 M' 20 GADDR HLF X6 ltac:(unfold GADDR; lia))|]. split; [exact (reg_lit c ps E' R' M1 M' 4 TPV HLF X13 ltac:(unfold TPV; lia))|].
    assert (DEFW : L5.defined M' (SP - 256) (256 + 8416)).
    { intros d Hd. apply Hgr. replace (SP - 256 + d) with (sp - 8672 + d) by (unfold SP; lia). apply Hdef. lia. }
    split; [exact DEFW|]. split; [apply (L5C.writable_of_defined RSEGS M' _ _ DEFW); unfold SP; lia|].
    split.
    { intros r o Hin. rewrite forallb_forall in X5. pose proof (X5 _ Hin) as Y. cbn [fst snd] in Y. pose proof (DOS.know_in RSEGS E' M' _ _ HK' Y) as Z.
      split; [|unfold PDC.rz; pose proof (u64_range (getr R (PDC.reg_of r))) as B; unfold two64 in B; exact B].
      assert (Ho : 1928 <= o <= 2024 /\ (r < 32)%nat) by (unfold PDC.SAVES in Hin; cbn [In] in Hin; intuition (match goal with HH : (_, _) = (_, _) |- _ => injection HH as <- <- end; lia)).
      apply (CL5.kword64_elim RSEGS E' M' _ _ (SP + 6384 + o) _ Z); [rewrite (DOS.estart_reg E' 2 _ sp U2); unfold SP; lia|].
      cbn [edenot]. rewrite EVf by lia. rewrite EVr by lia. reflexivity. }
    split; [unfold PDC.rz; rewrite Z_to_bv_bv_unsigned; exact Hret|].
    split.
    { pose proof (DOS.know_in RSEGS E' M' _ _ HK' X4) as Z. apply u64_at_mod. apply (CL5.kword64_elim RSEGS E' M' _ _ (SP + 8296) _ Z); [rewrite (DOS.estart_reg E' 2 _ sp U2); unfold SP; lia|].
      cbn [edenot]. rewrite EVf by lia. rewrite EVc. reflexivity. }
    split.
    { pose proof (DOS.know_in RSEGS E' M' _ _ HK' X3) as Z. apply u64_at_mod. apply (CL5.kword64_elim RSEGS E' M' _ _ GADDR _ Z); [rewrite DOS.estart_lit by (unfold GADDR; lia); unfold GADDR; lia|].
      cbn [edenot]. rewrite EVf by lia. rewrite EVc. reflexivity. }
    split; [unfold PDC.apart, SP; fold GADDR; lia|].
    assert (Hdl : 1 <= dl <= 2) by (unfold dl; destruct e2; lia).
    assert (Rq : 0 <= q + dl < 2 ^ 64) by lia.
    split.
    { unfold PDC.file_ok, PDC.STK_FLOOR. split; [|split; [|split; [|split; [exact (L5.writable_grows RSEGS M0 M' _ _ Hgr Hfw) | lia]]]].
      - pose proof (DOS.know_in RSEGS E' M' _ _ HK' X2) as Z. apply (CL5.kword64_elim RSEGS E' M' _ _ (F + 8) _ Z); [apply (DOS.estart_reg E' 10 8 F U10)|].
        unfold APC.eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite U32. fold dl. rewrite u64_of_Z by exact Rq. rewrite Z.mod_small by lia. lia.
      - pose proof (DOS.know_in RSEGS E' M' _ _ HK' X1) as Z. apply (CL5.kword64_elim RSEGS E' M' _ _ (F + 184) _ Z); [apply (DOS.estart_reg E' 10 184 F U10)|]. cbn [edenot]. apply u64_of_Z. lia.
      - pose proof (DOS.know_in RSEGS E' M' _ _ HK' X0) as Z. apply (CL5.kword64_elim RSEGS E' M' _ _ (F + 192) _ Z); [apply (DOS.estart_reg E' 10 192 F U10)|]. cbn [edenot]. apply u64_of_Z. lia. }
    split; [unfold PDC.apart, SP; lia|].
    assert (NTH : forall j, 0 <= j < N - q -> nth (Z.to_nat j) tq 0 = nth (Z.to_nat (q + j)) txt' 0).
    { intros j Hj. unfold tq, txt'. rewrite nth_skipn. rewrite app_nth1 by (unfold N in *; lia). f_equal. lia. }
    split.
    { unfold PDC.text_ok. rewrite Ltq. split; [|split; [|split; [lia | split; [lia | split; [lia | split]]]]].
      - intros j Hj. pose proof (TXT' (q + Z.of_nat j) ltac:(lia)) as Y. replace (s + q + Z.of_nat j) with (s + (q + Z.of_nat j)) by lia.
        rewrite <- (NTH (Z.of_nat j)) in Y by lia. rewrite Nat2Z.id in Y. exact Y.
      - replace (s + q + (N - q)) with (s + N) by lia. pose proof (TXT' N ltac:(lia)) as Y.
        unfold txt' in Y. rewrite app_nth2 in Y by (unfold N; lia). replace (Z.to_nat N - length txt)%nat with 0%nat in Y by (unfold N; lia). exact Y.
      - intros d Hd. apply Hgr. replace (s + q + d) with (s + (q + d)) by lia. apply Td. lia.
      - apply Forall_forall. intros x Hx. rewrite Forall_forall in Tr. apply Tr. unfold tq in Hx. rewrite <- (firstn_skipn (Z.to_nat q) txt). apply in_or_app. right. exact Hx. }
    split; [unfold PDC.text_apart, PDC.apart; rewrite Ltq; cbn [PDC.a_TP PDCU.ubsan11]; change (878592 - 164) with (TPV - 164); cbv zeta; unfold SP; lia|].
    split; [exact (L5.writable_grows RSEGS M0 M' _ _ Hgr Herrw)|].
    split; [intros a Ha; rewrite OUT by (rewrite u64_of_Z by lia; lia); apply Himg; exact Ha|].

    assert (Rcv : 0 <= uE E' (EVar cv) <= 255 /\ (if e2 then uE E' (EVar cv) = 48 else 49 <= uE E' (EVar cv) <= 57)).
    { destruct e2; [pose proof (DOS.rng_in_sem RSEGS E' M' _ _ _ _ HK' X) as Y; lia|]. apply andb_prop in X as [X _]. pose proof (DOS.rng_in_sem RSEGS E' M' _ _ _ _ HK' X) as Y. lia. }
    pose proof (leaf_byte c ps E' R' M1 M' q cv HLF Hag0 Hfr Fb ltac:(lia) (proj1 Rcv)) as Bq.
    assert (Etq : tq = nth (Z.to_nat q) txt' 0 :: skipn (S (Z.to_nat q)) txt).
    { unfold tq. rewrite (PDS.skipn_nth txt (Z.to_nat q) 0) by (unfold N in *; lia). f_equal. unfold txt'. rewrite app_nth1 by (unfold N in *; lia). reflexivity. }
    destruct e2.
    + split; [unfold dl; lia|]. exists (skipn (S (Z.to_nat q)) txt). rewrite Etq, <- Bq. f_equal. exact (proj2 Rcv).
    + split; [unfold dl; lia|]. exists (nth (Z.to_nat q) txt' 0), (skipn (S (Z.to_nat q)) txt). split; [exact Etq|]. rewrite <- Bq. split; [exact (proj2 Rcv)|].
      apply andb_prop in X as [_ X]. unfold PDC.rz, PDC.reg_of. rewrite (CL.ps_reg_is_sound RSEGS c ps E' R' M1 M' 10 _ HLF X). reflexivity.
  -
    intros fx2 R2 M2 HFP2 (P1 & P2 & P3 & P4 & P5 & P6 & P7). unfold PDC.FRAME, PDC.SCR_D in *. cbn [PDC.a_TP PDCU.ubsan11] in P5. change (878592 - 164) with (TPV - 164) in P5. change (878592 - 160) with (TPV - 160) in P5.
    assert (Era : Z_to_bv 64 (PDC.rz R 1) = getr R (PDC.reg_of 1)) by (unfold PDC.rz; apply Z_to_bv_bv_unsigned).
    cbv beta in *. rewrite Era. apply HK; [exact HFP2 | | | eapply mem_grows_trans; [exact Hgr | exact P6] |].
    + intros x Hx. assert (Hsv : forall r o, In (r, o) PDC.SAVES -> getr R2 (PDC.reg_of r) = getr R (PDC.reg_of r)).
      { intros r o Hin. apply bv_eq. exact (P2 r o Hin). }
      unfold PSI.CSAVED in Hx. cbn [In] in Hx.
      destruct Hx as [<-|[<-|[<-|[<-|Hx]]]].
      * apply (Hsv 1%nat 2024). unfold PDC.SAVES. cbn. tauto.
      * apply bv_eq. fold (PDC.rz R2 2). fold (PDC.rz R 2). rewrite P1, Rsp. unfold SP. lia.
      * rewrite P3. unfold PDC.reg_of. rewrite (CL.ps_reg_is_sound RSEGS c ps E' R' M1 M' 3 _ HLF X14). cbn [edenot]. rewrite EVf by lia. apply EVr. lia.
      * rewrite P4. unfold PDC.reg_of. rewrite (CL.ps_reg_is_sound RSEGS c ps E' R' M1 M' 4 _ HLF X13). cbn [edenot]. symmetry. exact (DOK.rz_word R 4 _ R4).
      * repeat (destruct Hx as [<-|Hx]; [eapply Hsv; unfold PDC.SAVES; cbn; tauto|]). contradiction.
    + intros a A1 A2 A3. rewrite P5 by (unfold SP; lia). apply OUT; lia.
    + replace (s + N) with (s + q + PD.dec_len tq) by (unfold tq; lia). exact P7.
Qed.

Variable i0 : nat.
Hypothesis Hi0 : (i0 = 0%nat /\ q = 0) \/ (i0 = 1%nat /\ q = 1).
Definition AmbI (i : nat) (E : env) (M : word -> option byte) (model : Model) : Prop := Amb i E M model /\ i = i0.
Lemma head_run : forall (fx : FPState) c, nth_error CPS i0 = Some c -> CC.At RSEGS c E0 R M0 -> FrmInv.fp_ok fx ->
  srealizes RSEGS SCFG (mkCfg (@mkst fx R (Z_to_bv 64 (CC.cp_pc c)) M0 (seg_rom RSEGS)) model0) K.
Proof.
  intros fx c Hc HAt Hfx.
  eapply (CC.cutcert_sound_tagged RSEGS CPS TAGS NFh AmbI K FrmInv.fp_ok
            (fun fx1 fx2 R1 pc1 M1 R2 pc2 M2 H => FrmInv.msteps_fp_ok RSEGS Pm10FrmInv.text_safe fx1 fx2 R1 _ M1 _ R2 _ M2 _ H) (plans (Forall_nil _)) tags_ok)
    with (i := i0) (c := c) (E := E0).
  - intros i E M1 m1 [H _]. exact (CL.pure_amb_model NFh E0 M0 model0 F0 i E M1 m1 Hh Hl H).
  - intros i c1 tags k ps j sg Hc1 Htags Hps Htag. exfalso.
    destruct i as [|[|i]]; cbv [TAGS nth_error] in Htags; [| | destruct i; discriminate Htags];
      (injection Htags as <-; destruct k as [|[|[|k]]]; cbv [nth_error] in Htag; [discriminate Htag | discriminate Htag | discriminate Htag | destruct k; discriminate Htag]).
  - intros i c1 tags k ps id Hc1 Htags Hps Htag fx' E R1 M1 m1 E' R' M' _ [HAmb Hi] HFP Hag HLF _.
    destruct i as [|[|i]]; cbv [CPS nth_error] in Hc1; [| | destruct i; discriminate Hc1]; injection Hc1 as <-;
      (destruct Hi0 as [[-> Hq0] | [-> Hq0]]; [|]; try discriminate Hi); clear Hi;
      (destruct k as [|[|[|k]]]; cbv [cp0 cp1 CC.cp_PSS nth_error] in Hps; [| | | destruct k; discriminate Hps]); injection Hps as <-.
    + eapply (dead_leaf 0%nat cp0 (nth 0 (CC.cp_PSS cp0) (SR.PS 0 [] [] [])) eq_refl ltac:(vm_compute; lia)); [rewrite Hq0; vm_compute; reflexivity | exact HAmb | exact HFP | exact Hag | exact HLF].
    + eapply (live_leaf 0%nat cp0 (nth 1 (CC.cp_PSS cp0) (SR.PS 0 [] [] [])) true eq_refl ltac:(vm_compute; lia) eq_refl); [rewrite Hq0; vm_compute; reflexivity | exact HAmb | exact HFP | exact Hag | exact HLF].
    + eapply (live_leaf 0%nat cp0 (nth 2 (CC.cp_PSS cp0) (SR.PS 0 [] [] [])) false eq_refl ltac:(vm_compute; lia) eq_refl); [rewrite Hq0; vm_compute; reflexivity | exact HAmb | exact HFP | exact Hag | exact HLF].
    + eapply (dead_leaf 1%nat cp1 (nth 0 (CC.cp_PSS cp1) (SR.PS 0 [] [] [])) eq_refl ltac:(vm_compute; lia)); [rewrite Hq0; vm_compute; reflexivity | exact HAmb | exact HFP | exact Hag | exact HLF].
    + eapply (live_leaf 1%nat cp1 (nth 1 (CC.cp_PSS cp1) (SR.PS 0 [] [] [])) true eq_refl ltac:(vm_compute; lia) eq_refl); [rewrite Hq0; vm_compute; reflexivity | exact HAmb | exact HFP | exact Hag | exact HLF].
    + eapply (live_leaf 1%nat cp1 (nth 2 (CC.cp_PSS cp1) (SR.PS 0 [] [] [])) false eq_refl ltac:(vm_compute; lia) eq_refl); [rewrite Hq0; vm_compute; reflexivity | exact HAmb | exact HFP | exact Hag | exact HLF].
  - exact Hc.
  - exact HAt.
  - split; [|reflexivity]. split; [reflexivity|]. split; [apply CC.env_agree_refl|]. split; [reflexivity | apply mem_grows_refl].
  - exact Hfx.
Qed.
End Bridges.
End FHO.
