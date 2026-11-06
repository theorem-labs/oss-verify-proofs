(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon Require Import PropExec StepTac SeqExec CatExec StoreOk CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSWord AsanSLibc AsanSMat AsanSMiz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

From OSSVerify.Proofs.openssl.bignum.lib.VCommon.Ax Require Import AsanSRipA.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Hint Extern 0 (BvWf _ _) =>
  (lazymatch goal with |- BvWf ?n ?v => is_closed_term n; is_closed_term v end; exact I) : typeclass_instances.

Section Rip.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable b : Z.
Local Notation h := (b - 0x48c)%Z.
Variable z : Z.
Variables gK gMB gME gHE aK aMB aME aHE : Z.
Hypothesis HW : words_ok segs b RIP_WORDS = true.
Hypothesis HWh : words_ok segs h HLP_WORDS = true.
Hypothesis HWz : words_ok segs z MIZ_WORDS = true.
Hypothesis HJz : jal_ok segs b 0x170 1 z = true.
Hypothesis HPh0 : pair_ok segs h 0x0 11 11 gK = true.
Hypothesis HPh20 : pair_ok segs h 0x20 13 13 gMB = true.
Hypothesis HPh28 : pair_ok segs h 0x28 14 14 gME = true.
Hypothesis HPh44 : pair_ok segs h 0x44 14 14 gHE = true.
Hypothesis HP2c : pair_ok segs b 0x2c 10 21 gK = true.
Hypothesis HP4c : pair_ok segs b 0x4c 13 13 gMB = true.
Hypothesis HP54 : pair_ok segs b 0x54 14 14 gME = true.
Hypothesis HP70 : pair_ok segs b 0x70 14 14 gHE = true.
Hypothesis HP94 : pair_ok segs b 0x94 12 12 gMB = true.
Hypothesis HP9c : pair_ok segs b 0x9c 13 13 gME = true.
Hypothesis HPb8 : pair_ok segs b 0xb8 13 13 gHE = true.
Hypothesis Hgb : (0 <= gK < 2 ^ 60 /\ 0 <= gMB < 2 ^ 60 /\ 0 <= gME < 2 ^ 60 /\ 0 <= gHE < 2 ^ 60 /\
                  0 <= aK < 2 ^ 60 /\ 0 <= aMB < 2 ^ 60 /\ 0 <= aME < 2 ^ 60 /\ 0 <= aHE < 2 ^ 60)%Z.

Local Ltac inw := repeat (first [left; reflexivity | right]).
Local Ltac fw := apply (words_get_l segs b RIP_WORDS); [exact HW | reflexivity | reflexivity].
Local Ltac fwh := apply (words_get_l segs h HLP_WORDS); [exact HWh | reflexivity | reflexivity].

Local Notation globals := (@AsanSRipA.globals segs gK gMB gME gHE aK aMB aME aHE) (only parsing).
Local Notation globals_nl := (@AsanSRipA.globals_nl gK gMB gME gHE aK aMB aME aHE) (only parsing).
Local Notation h_sum := (@AsanSRipA.h_sum segs cfg b gK gMB gME gHE aK aMB aME aHE HWh HPh0 HPh20 HPh28 HPh44 Hgb) (only parsing).

Ltac wpair P Hl Hv Hnl :=
  let wa := fresh "wa" in let wl := fresh "wl" in let ia := fresh "ia" in let il := fresh "il" in
  let HFa := fresh "HFa" in let HEa := fresh "HEa" in let HDa := fresh "HDa" in
  let HFl := fresh "HFl" in let HEl := fresh "HEl" in let HDl := fresh "HDl" in let HA := fresh "HA" in
  destruct (pair_ok_sound _ _ _ _ _ _ P ltac:(lia)) as (wa & wl & ia & il & HFa & HEa & HDa & HFl & HEl & HDl & HA);
  eapply rzc_acc; [ assumption | first [ reflexivity | assumption ]
                  | eapply wacc_Auipc; [ fetch_tac HFa | exact HEa | exact HDa ] | apply acc_ok_nil | ];
  try (match goal with H : ms_pc_val ?S = _ |- context [ms_pc_val ?S] => rewrite H end); pcn;
  eapply rzc_acc; [ assumption | reflexivity
                  | eapply wacc_Load; [ fetch_tac HFl | exact HEl | exact HDl | rgn; rewrite HA, ?mem_setx; exact Hl ]
                  | rgn; rewrite HA; apply cell_nl; [lia | exact Hnl]
                  | ];
  pcn; rewrite Hv.

Ltac wvar F D Hl Hv Hnl :=
  eapply rzc_acc; [ assumption | reflexivity
                  | eapply wacc_Load; [ fetch_tac F | reflexivity | exact D | rgn; rewrite add_sext0, ?mem_setx; exact Hl ]
                  | rgn; rewrite add_sext0; apply cell_nl; [lia | exact Hnl]
                  | ];
  pcn; rewrite Hv.

Section Main.
Variable model0 : Model.
Hypothesis Hh0 : m_halted model0 = None.
Variable ms0 : machine_state.
Variable T : TSet.
Variables (beg : word) (size : Z) (sp0 : word).
Local Notation B := (bv_unsigned beg).
Local Notation SP := (bv_unsigned sp0).
Hypothesis Hsz : (1 <= size)%Z.
Hypothesis Hhi : (B + size + 8 <= 0x800000000000 /\ size <= 2 ^ 40)%Z.
Hypothesis Hreg : (0x10007fff8000 <= B \/ B + size + 8 <= 0x7fff8000)%Z.
Hypothesis H2 : rg ms0 2 = sp0.
Hypothesis Hg0 : globals (ms_mem ms0).
Hypothesis HgN : globals_nl model0.
Hypothesis Hsh : forall q, (0x7fff8000 + B / 8 <= q <= 0x7fff8000 + (B + size - 1) / 8)%Z ->
  bat segs (ms_mem ms0) (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Hypothesis Hbud : (vm_backing_used model0 + 4096 * rpg size <= vm_limit (m_vmmaps model0))%Z.
Let Hrpg : (2 <= rpg size /\ 8 * (rpg size - 2) <= size)%Z.
Proof. pose proof (rpg_f size). lia. Qed.
Hypothesis Hsp : (0x10007fff8000 <= SP <= 0x800000000000)%Z.
Hypothesis Hok : store_ok segs (ms_mem ms0) (Z_to_bv 64 (SP - 72)) 72 = true.
Hypothesis HnlS : no_lazy model0 (SP - 72) SP.
Hypothesis Hdsh : (SP <= 0x7fff8000 + B / 8 \/ 0x7fff8000 + (B + size - 1) / 8 < SP - 72)%Z.
Hypothesis Hdg : forall a, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> (a + 8 <= SP - 72 \/ SP <= a)%Z.
Hypothesis Hra : (bv_unsigned (rg ms0 1) mod 2 = 0)%Z.
Hypothesis HK : forall ms' model', RPOST ms0 ms' (SP - 72) SP -> ms_pc_val ms' = rg ms0 1 -> rg ms' 10 = w0 ->
  mat_of model0 model' (rpg size) -> realizes_cfg segs cfg (mkCfg ms' model') T.

Hypothesis Hb : (0x10000 <= b /\ b + 0x20000 < 2 ^ 47 /\ b mod 4 = 0)%Z.
Local Notation K := 0x7fff8000%Z.
Local Notation E := (bv_unsigned beg + size)%Z.

Definition SB (o : Z) (v : word) (m : word -> option byte) : word -> option byte :=
  write_to_mem m (Z_to_bv 64 (SP + -64 + o)) (store_bytes SZ8 v).
Definition Mf : word -> option byte :=
  SB 8 (rg ms0 21) (SB 16 (rg ms0 20) (SB 24 (rg ms0 19) (SB 32 (rg ms0 18)
    (SB 40 (rg ms0 9) (SB 48 (rg ms0 8) (SB 56 (rg ms0 1) (ms_mem ms0))))))).

Lemma u_sp0 : (0 <= SP < 2 ^ 64)%Z.
Proof. pose proof (bv_unsigned_in_range 64 sp0) as R. change (bv_modulus 64) with (2 ^ 64)%Z in R. exact R. Qed.

Lemma grows_w : forall m1 m2 a bs, mem_grows m1 m2 -> mem_grows m1 (write_to_mem m2 a bs).
Proof. intros m1 m2 a bs H. apply (mem_grows_trans m1 m2); [exact H | apply write_to_mem_grows]. Qed.

Lemma st_slot : forall m (o : Z), mem_grows (ms_mem ms0) m -> (-8 <= o <= 56)%Z ->
  store_ok segs m (Z_to_bv 64 (SP + -64 + o)) 8 = true.
Proof.
  intros m o Hg Ho. pose proof u_sp0. apply (store_ok_mono segs 8 (ms_mem ms0)); [exact Hg|].
  apply (store_ok_sub segs (ms_mem ms0) (Z_to_bv 64 (SP - 72)) _ 72 8); rewrite ?bvu_z by lia; [lia | exact Hok | lia | lia].
Qed.

Lemma acc_slot : forall model k (o : Z), mat_of model0 model k -> (-8 <= o <= 56)%Z ->
  acc_ok model [(Z_to_bv 64 (SP + -64 + o), 8%nat)].
Proof.
  intros model k o Hm Ho. pose proof u_sp0. apply acc_ok_one; rewrite bvu_z by lia; [lia|].
  apply (no_lazy_mat model0 model k); [exact Hm|]. apply (no_lazy_sub model0 _ _ _ _ HnlS); lia.
Qed.

Ltac wsd F D o :=
  eapply rzc_acc;
  [ assumption | reflexivity
  | eapply wacc_Store; [ fetch_tac F | reflexivity | exact D
                       | rgn; rewrite zw_add_sext; lits; cbn [msz_n]; apply st_slot;
                         [ repeat (apply grows_w); apply mem_grows_refl | lia ] ]
  | rgn; rewrite zw_add_sext; lits; cbn [msz_n]; apply (acc_slot model0 0 o); [ apply mat_of_refl | lia ]
  | pcn; rgn; rewrite ?zw_add_sext; lits ].

Lemma Mf_out : forall x : word, ~ (SP - 56 <= bv_unsigned x < SP)%Z -> Mf x = ms_mem ms0 x.
Proof.
  intros x Hx. pose proof u_sp0. unfold Mf, SB.
  rewrite !w2m_outside; try reflexivity; rewrite store_bytes8_len; rewrite bvu_z by lia; lia.
Qed.

Lemma Mf_grows : mem_grows (ms_mem ms0) Mf.
Proof. unfold Mf, SB. repeat apply grows_w. apply mem_grows_refl. Qed.

Lemma rdn_Mf_out : forall (a : Z), (0 <= a)%Z -> (a + 8 <= SP - 56 \/ SP <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
  rdn segs Mf (Z_to_bv 64 a) 8 = rdn segs (ms_mem ms0) (Z_to_bv 64 a) 8.
Proof.
  intros a Ha Hd Hn. pose proof u_sp0. apply rdn_ext; rewrite bvu_z by lia; [lia|].
  intros x Hx. apply Mf_out. lia.
Qed.

Lemma cell8_Mf : forall a v, In a [gK; aK; gMB; aMB; gME; aME; gHE; aHE] -> cell8 segs (ms_mem ms0) a v -> cell8 segs Mf a v.
Proof.
  intros a v Hin (l & Hl & Hv). exists l. split; [|exact Hv].
  pose proof (Hdg a Hin) as Hd. pose proof Hgb as Hgb2.
  assert (Ha : (0 <= a < 2 ^ 60)%Z) by (destruct Hgb2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8);
    cbn in Hin; destruct Hin as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [] ]]]]]]]]; lia).
  rewrite rdn_Mf_out by lia. exact Hl.
Qed.

Lemma globals_Mf : globals Mf.
Proof.
  destruct Hg0 as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8).
  repeat split; apply cell8_Mf; try assumption; cbn; tauto.
Qed.

Lemma shadow_Mf : forall q, (0x7fff8000 + B / 8 <= q <= 0x7fff8000 + (B + size - 1) / 8)%Z ->
  bat segs Mf (Z_to_bv 64 q) = Some (Z_to_bv 8 0).
Proof.
  intros q Hq. pose proof u_sp0. unfold bat. rewrite Mf_out.
  - exact (Hsh q Hq).
  - rewrite bvu_z; [lia|]. pose proof (bv_unsigned_in_range 64 beg) as R. change (bv_modulus 64) with (2 ^ 64)%Z in R.
    pose proof (Z.div_pos B 8 ltac:(lia) ltac:(lia)). split; [lia|].
    assert ((B + size - 1) / 8 <= (2 ^ 64) / 8)%Z by (apply Z.div_le_mono; lia). lia.
Qed.

Lemma rdn_SB_same : forall o v m, (8 <= o <= 56)%Z ->
  rdn segs (SB o v m) (Z_to_bv 64 (SP + -64 + o)) 8 = Some (store_bytes SZ8 v).
Proof.
  intros o v m Ho. pose proof u_sp0. unfold SB. rewrite write_to_mem_wbytes.
  exact (rdn_wbytes_hit segs (store_bytes SZ8 v) m (Z_to_bv 64 (SP + -64 + o)) ltac:(rewrite store_bytes8_len, bvu_z by lia; lia)).
Qed.

Lemma rdn_SB_other : forall o o' v m, (8 <= o <= 56)%Z -> (8 <= o' <= 56)%Z -> (o + 8 <= o' \/ o' + 8 <= o)%Z ->
  rdn segs (SB o v m) (Z_to_bv 64 (SP + -64 + o')) 8 = rdn segs m (Z_to_bv 64 (SP + -64 + o')) 8.
Proof.
  intros o o' v m Ho Ho' Hd. pose proof u_sp0. apply rdn_ext; rewrite bvu_z by lia; [lia|].
  intros x Hx. unfold SB. apply w2m_outside; rewrite store_bytes8_len, bvu_z by lia; lia.
Qed.

Ltac rdf := unfold Mf;
  repeat first [ rewrite rdn_SB_same by lia; reflexivity | rewrite rdn_SB_other by lia ].

Lemma Mf_read56 : rdn segs Mf (Z_to_bv 64 (SP + -64 + 56)) 8 = Some (store_bytes SZ8 (rg ms0 1)). Proof. rdf. Qed.
Lemma Mf_read48 : rdn segs Mf (Z_to_bv 64 (SP + -64 + 48)) 8 = Some (store_bytes SZ8 (rg ms0 8)). Proof. rdf. Qed.
Lemma Mf_read40 : rdn segs Mf (Z_to_bv 64 (SP + -64 + 40)) 8 = Some (store_bytes SZ8 (rg ms0 9)). Proof. rdf. Qed.
Lemma Mf_read32 : rdn segs Mf (Z_to_bv 64 (SP + -64 + 32)) 8 = Some (store_bytes SZ8 (rg ms0 18)). Proof. rdf. Qed.
Lemma Mf_read24 : rdn segs Mf (Z_to_bv 64 (SP + -64 + 24)) 8 = Some (store_bytes SZ8 (rg ms0 19)). Proof. rdf. Qed.
Lemma Mf_read16 : rdn segs Mf (Z_to_bv 64 (SP + -64 + 16)) 8 = Some (store_bytes SZ8 (rg ms0 20)). Proof. rdf. Qed.
Lemma Mf_read8 : rdn segs Mf (Z_to_bv 64 (SP + -64 + 8)) 8 = Some (store_bytes SZ8 (rg ms0 21)). Proof. rdf. Qed.

End Main.
End Rip.
