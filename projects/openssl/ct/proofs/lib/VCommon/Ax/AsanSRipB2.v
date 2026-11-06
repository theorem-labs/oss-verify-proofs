(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec StepTac SeqExec CatExec StoreOk CatSim ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.BootWitness Require Import BootDefs BootStep.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanWLazy AsanWAcc AsanWBase AsanSBase AsanSWord AsanSLibc AsanSMat AsanSMiz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.


From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AsanSRipA AsanSRipA1 AsanSRipA2 AsanSRipB.
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
Variable z : Z.   (* [comment removed for export] *)
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

Lemma F_0 : fetch_word segs (pcw b 0x0) = Some (Z_to_bv 32 0xfc010113). Proof. fw. Qed.
Lemma F_4 : fetch_word segs (pcw b 0x4) = Some (Z_to_bv 32 0x02113c23). Proof. fw. Qed.
Lemma F_8 : fetch_word segs (pcw b 0x8) = Some (Z_to_bv 32 0x02813823). Proof. fw. Qed.
Lemma F_c : fetch_word segs (pcw b 0xc) = Some (Z_to_bv 32 0x02913423). Proof. fw. Qed.
Lemma F_10 : fetch_word segs (pcw b 0x10) = Some (Z_to_bv 32 0x03213023). Proof. fw. Qed.
Lemma F_14 : fetch_word segs (pcw b 0x14) = Some (Z_to_bv 32 0x01313c23). Proof. fw. Qed.
Lemma F_18 : fetch_word segs (pcw b 0x18) = Some (Z_to_bv 32 0x01413823). Proof. fw. Qed.
Lemma F_1c : fetch_word segs (pcw b 0x1c) = Some (Z_to_bv 32 0x01513423). Proof. fw. Qed.
Lemma F_20 : fetch_word segs (pcw b 0x20) = Some (Z_to_bv 32 0x14058c63). Proof. fw. Qed.
Lemma F_24 : fetch_word segs (pcw b 0x24) = Some (Z_to_bv 32 0x00058493). Proof. fw. Qed.
Lemma F_28 : fetch_word segs (pcw b 0x28) = Some (Z_to_bv 32 0x00050413). Proof. fw. Qed.
Lemma F_34 : fetch_word segs (pcw b 0x34) = Some (Z_to_bv 32 0x000ab583). Proof. fw. Qed.
Lemma F_38 : fetch_word segs (pcw b 0x38) = Some (Z_to_bv 32 0xfff58513). Proof. fw. Qed.
Lemma F_3c : fetch_word segs (pcw b 0x3c) = Some (Z_to_bv 32 0x00a5b633). Proof. fw. Qed.
Lemma F_40 : fetch_word segs (pcw b 0x40) = Some (Z_to_bv 32 0xfff60613). Proof. fw. Qed.
Lemma F_44 : fetch_word segs (pcw b 0x44) = Some (Z_to_bv 32 0x00a67633). Proof. fw. Qed.
Lemma F_48 : fetch_word segs (pcw b 0x48) = Some (Z_to_bv 32 0x04867263). Proof. fw. Qed.
Lemma F_5c : fetch_word segs (pcw b 0x5c) = Some (Z_to_bv 32 0x0006b803). Proof. fw. Qed.
Lemma F_60 : fetch_word segs (pcw b 0x60) = Some (Z_to_bv 32 0x00073683). Proof. fw. Qed.
Lemma F_64 : fetch_word segs (pcw b 0x64) = Some (Z_to_bv 32 0xfff80793). Proof. fw. Qed.
Lemma F_68 : fetch_word segs (pcw b 0x68) = Some (Z_to_bv 32 0x0087f463). Proof. fw. Qed.
Lemma F_6c : fetch_word segs (pcw b 0x6c) = Some (Z_to_bv 32 0x0286f063). Proof. fw. Qed.
Lemma F_78 : fetch_word segs (pcw b 0x78) = Some (Z_to_bv 32 0x00073283). Proof. fw. Qed.
Lemma F_7c : fetch_word segs (pcw b 0x7c) = Some (Z_to_bv 32 0x0032d713). Proof. fw. Qed.
Lemma F_80 : fetch_word segs (pcw b 0x80) = Some (Z_to_bv 32 0x00b708b3). Proof. fw. Qed.
Lemma F_84 : fetch_word segs (pcw b 0x84) = Some (Z_to_bv 32 0x1282e063). Proof. fw. Qed.
Lemma F_88 : fetch_word segs (pcw b 0x88) = Some (Z_to_bv 32 0x1088fe63). Proof. fw. Qed.
Lemma F_8c : fetch_word segs (pcw b 0x8c) = Some (Z_to_bv 32 0x00848933). Proof. fw. Qed.
Lemma F_90 : fetch_word segs (pcw b 0x90) = Some (Z_to_bv 32 0x05267263). Proof. fw. Qed.
Lemma F_a4 : fetch_word segs (pcw b 0xa4) = Some (Z_to_bv 32 0x00063783). Proof. fw. Qed.
Lemma F_a8 : fetch_word segs (pcw b 0xa8) = Some (Z_to_bv 32 0x0006b603). Proof. fw. Qed.
Lemma F_ac : fetch_word segs (pcw b 0xac) = Some (Z_to_bv 32 0xfff78713). Proof. fw. Qed.
Lemma F_b0 : fetch_word segs (pcw b 0xb0) = Some (Z_to_bv 32 0x01277463). Proof. fw. Qed.
Lemma F_b4 : fetch_word segs (pcw b 0xb4) = Some (Z_to_bv 32 0x03267063). Proof. fw. Qed.
Lemma F_c0 : fetch_word segs (pcw b 0xc0) = Some (Z_to_bv 32 0x0006b883). Proof. fw. Qed.
Lemma F_c4 : fetch_word segs (pcw b 0xc4) = Some (Z_to_bv 32 0x0038d693). Proof. fw. Qed.
Lemma F_c8 : fetch_word segs (pcw b 0xc8) = Some (Z_to_bv 32 0x00b68833). Proof. fw. Qed.
Lemma F_cc : fetch_word segs (pcw b 0xcc) = Some (Z_to_bv 32 0x1328e463). Proof. fw. Qed.
Lemma F_d0 : fetch_word segs (pcw b 0xd0) = Some (Z_to_bv 32 0x13287263). Proof. fw. Qed.
Lemma F_d4 : fetch_word segs (pcw b 0xd4) = Some (Z_to_bv 32 0x23247863). Proof. fw. Qed.
Lemma F_d8 : fetch_word segs (pcw b 0xd8) = Some (Z_to_bv 32 0x00740513). Proof. fw. Qed.
Lemma F_dc : fetch_word segs (pcw b 0xdc) = Some (Z_to_bv 32 0xff857513). Proof. fw. Qed.
Lemma F_e0 : fetch_word segs (pcw b 0xe0) = Some (Z_to_bv 32 0xff897a13). Proof. fw. Qed.
Lemma F_e4 : fetch_word segs (pcw b 0xe4) = Some (Z_to_bv 32 0xa91ff0ef). Proof. fw. Qed.
Lemma F_e8 : fetch_word segs (pcw b 0xe8) = Some (Z_to_bv 32 0x00050993). Proof. fw. Qed.
Lemma F_ec : fetch_word segs (pcw b 0xec) = Some (Z_to_bv 32 0x000a0513). Proof. fw. Qed.
Lemma F_f0 : fetch_word segs (pcw b 0xf0) = Some (Z_to_bv 32 0xa85ff0ef). Proof. fw. Qed.
Lemma F_f4 : fetch_word segs (pcw b 0xf4) = Some (Z_to_bv 32 0x000ab583). Proof. fw. Qed.
Lemma F_f8 : fetch_word segs (pcw b 0xf8) = Some (Z_to_bv 32 0x00345613). Proof. fw. Qed.
Lemma F_fc : fetch_word segs (pcw b 0xfc) = Some (Z_to_bv 32 0x00c58633). Proof. fw. Qed.
Lemma F_100 : fetch_word segs (pcw b 0x100) = Some (Z_to_bv 32 0x00060603). Proof. fw. Qed.
Lemma F_104 : fetch_word segs (pcw b 0x104) = Some (Z_to_bv 32 0x00060663). Proof. fw. Qed.
Lemma F_108 : fetch_word segs (pcw b 0x108) = Some (Z_to_bv 32 0x00747693). Proof. fw. Qed.
Lemma F_10c : fetch_word segs (pcw b 0x10c) = Some (Z_to_bv 32 0x02c6d063). Proof. fw. Qed.
Lemma F_110 : fetch_word segs (pcw b 0x110) = Some (Z_to_bv 32 0xfff90913). Proof. fw. Qed.
Lemma F_114 : fetch_word segs (pcw b 0x114) = Some (Z_to_bv 32 0x00395613). Proof. fw. Qed.
Lemma F_118 : fetch_word segs (pcw b 0x118) = Some (Z_to_bv 32 0x00c585b3). Proof. fw. Qed.
Lemma F_11c : fetch_word segs (pcw b 0x11c) = Some (Z_to_bv 32 0x00058583). Proof. fw. Qed.
Lemma F_120 : fetch_word segs (pcw b 0x120) = Some (Z_to_bv 32 0x04058263). Proof. fw. Qed.
Lemma F_124 : fetch_word segs (pcw b 0x124) = Some (Z_to_bv 32 0x00797613). Proof. fw. Qed.
Lemma F_128 : fetch_word segs (pcw b 0x128) = Some (Z_to_bv 32 0x02b64e63). Proof. fw. Qed.
Lemma F_12c : fetch_word segs (pcw b 0x12c) = Some (Z_to_bv 32 0x000ab503). Proof. fw. Qed.
Lemma F_130 : fetch_word segs (pcw b 0x130) = Some (Z_to_bv 32 0x00040593). Proof. fw. Qed.
Lemma F_134 : fetch_word segs (pcw b 0x134) = Some (Z_to_bv 32 0x0140006f). Proof. fw. Qed.
Lemma F_138 : fetch_word segs (pcw b 0x138) = Some (Z_to_bv 32 0x00140413). Proof. fw. Qed.
Lemma F_13c : fetch_word segs (pcw b 0x13c) = Some (Z_to_bv 32 0xfff48493). Proof. fw. Qed.
Lemma F_140 : fetch_word segs (pcw b 0x140) = Some (Z_to_bv 32 0x00158593). Proof. fw. Qed.
Lemma F_144 : fetch_word segs (pcw b 0x144) = Some (Z_to_bv 32 0x1e048063). Proof. fw. Qed.
Lemma F_148 : fetch_word segs (pcw b 0x148) = Some (Z_to_bv 32 0x00345613). Proof. fw. Qed.
Lemma F_14c : fetch_word segs (pcw b 0x14c) = Some (Z_to_bv 32 0x00c50633). Proof. fw. Qed.
Lemma F_150 : fetch_word segs (pcw b 0x150) = Some (Z_to_bv 32 0x00060603). Proof. fw. Qed.
Lemma F_154 : fetch_word segs (pcw b 0x154) = Some (Z_to_bv 32 0xfe0602e3). Proof. fw. Qed.
Lemma F_158 : fetch_word segs (pcw b 0x158) = Some (Z_to_bv 32 0x0075f693). Proof. fw. Qed.
Lemma F_15c : fetch_word segs (pcw b 0x15c) = Some (Z_to_bv 32 0xfcc6cee3). Proof. fw. Qed.
Lemma F_160 : fetch_word segs (pcw b 0x160) = Some (Z_to_bv 32 0x01c0006f). Proof. fw. Qed.
Lemma F_164 : fetch_word segs (pcw b 0x164) = Some (Z_to_bv 32 0x00a9fa63). Proof. fw. Qed.
Lemma F_168 : fetch_word segs (pcw b 0x168) = Some (Z_to_bv 32 0x413505b3). Proof. fw. Qed.
Lemma F_16c : fetch_word segs (pcw b 0x16c) = Some (Z_to_bv 32 0x00098513). Proof. fw. Qed.
Lemma F_174 : fetch_word segs (pcw b 0x174) = Some (Z_to_bv 32 0xfa050ce3). Proof. fw. Qed.
Lemma F_178 : fetch_word segs (pcw b 0x178) = Some (Z_to_bv 32 0x00000413). Proof. fw. Qed.
Lemma F_17c : fetch_word segs (pcw b 0x17c) = Some (Z_to_bv 32 0x00040513). Proof. fw. Qed.
Lemma F_180 : fetch_word segs (pcw b 0x180) = Some (Z_to_bv 32 0x03813083). Proof. fw. Qed.
Lemma F_184 : fetch_word segs (pcw b 0x184) = Some (Z_to_bv 32 0x03013403). Proof. fw. Qed.
Lemma F_188 : fetch_word segs (pcw b 0x188) = Some (Z_to_bv 32 0x02813483). Proof. fw. Qed.
Lemma F_18c : fetch_word segs (pcw b 0x18c) = Some (Z_to_bv 32 0x02013903). Proof. fw. Qed.
Lemma F_190 : fetch_word segs (pcw b 0x190) = Some (Z_to_bv 32 0x01813983). Proof. fw. Qed.
Lemma F_194 : fetch_word segs (pcw b 0x194) = Some (Z_to_bv 32 0x01013a03). Proof. fw. Qed.
Lemma F_198 : fetch_word segs (pcw b 0x198) = Some (Z_to_bv 32 0x00813a83). Proof. fw. Qed.
Lemma F_19c : fetch_word segs (pcw b 0x19c) = Some (Z_to_bv 32 0x04010113). Proof. fw. Qed.
Lemma F_1a0 : fetch_word segs (pcw b 0x1a0) = Some (Z_to_bv 32 0x00008067). Proof. fw. Qed.
Lemma G_8 : fetch_word segs (pcw h 0x8) = Some (Z_to_bv 32 0x0005b583). Proof. fwh. Qed.
Lemma G_c : fetch_word segs (pcw h 0xc) = Some (Z_to_bv 32 0xfff58613). Proof. fwh. Qed.
Lemma G_10 : fetch_word segs (pcw h 0x10) = Some (Z_to_bv 32 0x00c5b6b3). Proof. fwh. Qed.
Lemma G_14 : fetch_word segs (pcw h 0x14) = Some (Z_to_bv 32 0xfff68693). Proof. fwh. Qed.
Lemma G_18 : fetch_word segs (pcw h 0x18) = Some (Z_to_bv 32 0x00c6f6b3). Proof. fwh. Qed.
Lemma G_1c : fetch_word segs (pcw h 0x1c) = Some (Z_to_bv 32 0x04a6f263). Proof. fwh. Qed.
Lemma G_30 : fetch_word segs (pcw h 0x30) = Some (Z_to_bv 32 0x0006b803). Proof. fwh. Qed.
Lemma G_34 : fetch_word segs (pcw h 0x34) = Some (Z_to_bv 32 0x00073683). Proof. fwh. Qed.
Lemma G_38 : fetch_word segs (pcw h 0x38) = Some (Z_to_bv 32 0xfff80793). Proof. fwh. Qed.
Lemma G_3c : fetch_word segs (pcw h 0x3c) = Some (Z_to_bv 32 0x00a7f463). Proof. fwh. Qed.
Lemma G_40 : fetch_word segs (pcw h 0x40) = Some (Z_to_bv 32 0x02a6f063). Proof. fwh. Qed.
Lemma G_4c : fetch_word segs (pcw h 0x4c) = Some (Z_to_bv 32 0x00073283). Proof. fwh. Qed.
Lemma G_50 : fetch_word segs (pcw h 0x50) = Some (Z_to_bv 32 0x0032d713). Proof. fwh. Qed.
Lemma G_54 : fetch_word segs (pcw h 0x54) = Some (Z_to_bv 32 0x00b708b3). Proof. fwh. Qed.
Lemma G_58 : fetch_word segs (pcw h 0x58) = Some (Z_to_bv 32 0x00a2ea63). Proof. fwh. Qed.
Lemma G_5c : fetch_word segs (pcw h 0x5c) = Some (Z_to_bv 32 0x00a8f863). Proof. fwh. Qed.
Lemma G_60 : fetch_word segs (pcw h 0x60) = Some (Z_to_bv 32 0x00355513). Proof. fwh. Qed.
Lemma G_64 : fetch_word segs (pcw h 0x64) = Some (Z_to_bv 32 0x00a58533). Proof. fwh. Qed.
Lemma G_68 : fetch_word segs (pcw h 0x68) = Some (Z_to_bv 32 0x00008067). Proof. fwh. Qed.

Local Notation globals := (@AsanSRipA.globals segs gK gMB gME gHE aK aMB aME aHE) (only parsing).
Local Notation globals_nl := (@AsanSRipA.globals_nl gK gMB gME gHE aK aMB aME aHE) (only parsing).
Local Notation h_sum := (@AsanSRipA.h_sum segs cfg b gK gMB gME gHE aK aMB aME aHE HWh HPh0 HPh20 HPh28 HPh44 Hgb) (only parsing).

(* [comment removed for export] *)
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

(* [comment removed for export] *)
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
Local Notation SB := (@AsanSRipA1.SB sp0) (only parsing).
Local Notation Mf := (@AsanSRipA1.Mf ms0 sp0) (only parsing).
Local Notation u_sp0 := (@AsanSRipA1.u_sp0 sp0) (only parsing).
Local Notation st_slot := (@AsanSRipA1.st_slot segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hok Hb) (only parsing).
Local Notation acc_slot := (@AsanSRipA1.acc_slot b model0 ms0 beg size sp0 Hsz Hhi Hreg Hsp HnlS Hb) (only parsing).
Local Notation Mf_out := (@AsanSRipA1.Mf_out b ms0 beg size sp0 Hsp) (only parsing).
Local Notation Mf_grows := (@AsanSRipA1.Mf_grows ms0 sp0) (only parsing).
Local Notation rdn_Mf_out := (@AsanSRipA1.rdn_Mf_out segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation cell8_Mf := (@AsanSRipA1.cell8_Mf segs b gK gMB gME gHE aK aMB aME aHE Hgb ms0 beg size sp0 Hsz Hhi Hreg Hsp Hdg Hb) (only parsing).
Local Notation globals_Mf := (@AsanSRipA1.globals_Mf segs b gK gMB gME gHE aK aMB aME aHE Hgb ms0 beg size sp0 Hsz Hhi Hreg Hg0 Hsp Hdsh Hdg Hb) (only parsing).
Local Notation shadow_Mf := (@AsanSRipA1.shadow_Mf segs b ms0 beg size sp0 Hsz Hhi Hreg Hsh Hsp Hdsh Hb) (only parsing).
Local Notation rdn_SB_same := (@AsanSRipA1.rdn_SB_same segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation rdn_SB_other := (@AsanSRipA1.rdn_SB_other segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read56 := (@AsanSRipA1.Mf_read56 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read48 := (@AsanSRipA1.Mf_read48 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read40 := (@AsanSRipA1.Mf_read40 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read32 := (@AsanSRipA1.Mf_read32 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read24 := (@AsanSRipA1.Mf_read24 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read16 := (@AsanSRipA1.Mf_read16 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation Mf_read8 := (@AsanSRipA1.Mf_read8 segs b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation BI := (@AsanSRipA2.BI model0 ms0) (only parsing).
Local Notation hclob_cases := (@AsanSRipA2.hclob_cases ) (only parsing).
Local Notation B6 := (@AsanSRipA2.B6 segs cfg b HW model0 Hh0 ms0 T beg size sp0 Hsz Hhi Hreg H2 Hsp HnlS Hra HK Hb) (only parsing).
Local Notation mat_of_trans := (@AsanSRipA2.mat_of_trans b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation ra_even := (@AsanSRipA2.ra_even b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation ab8 := (@AsanSRipA2.ab8 beg) (only parsing).
Local Notation ae8 := (@AsanSRipA2.ae8 beg size) (only parsing).
Local Notation bq := (@AsanSRipA2.bq beg) (only parsing).
Local Notation eq8 := (@AsanSRipA2.eq8 beg size) (only parsing).
Local Notation ab8_f := (@AsanSRipA2.ab8_f b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation ae8_f := (@AsanSRipA2.ae8_f b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation bq_f := (@AsanSRipA2.bq_f b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation eq8_f := (@AsanSRipA2.eq8_f b ms0 beg size sp0 Hsz Hhi Hreg Hsp Hb) (only parsing).
Local Notation shadow_Mf' := (@AsanSRipA2.shadow_Mf' segs b ms0 beg size sp0 Hsz Hhi Hreg Hsh Hsp Hdsh Hb) (only parsing).
Local Notation B5 := (@AsanSRipA2.B5 segs cfg b z gK gMB gME gHE aK aMB aME aHE HW HWz HJz Hgb model0 Hh0 ms0 T beg size sp0 Hsz Hhi Hreg H2 Hsh Hbud Hsp Hok HnlS Hdsh Hra HK Hb) (only parsing).
Local Notation globals_nl_mat := (@AsanSRipB.globals_nl_mat gK gMB gME gHE aK aMB aME aHE model0 HgN) (only parsing).
Local Notation B4 := (@AsanSRipB.B4 segs cfg b z gK gMB gME gHE aK aMB aME aHE HW HWz HJz Hgb model0 Hh0 ms0 T beg size sp0 Hsz Hhi Hreg H2 Hg0 HgN Hsh Hbud Hsp Hok HnlS Hdsh Hdg Hra HK Hb) (only parsing).
Local Notation B3 := (@AsanSRipB.B3 segs cfg b z gK gMB gME gHE aK aMB aME aHE HW HWh HWz HJz HPh0 HPh20 HPh28 HPh44 Hgb model0 Hh0 ms0 T beg size sp0 Hsz Hhi Hreg H2 Hg0 HgN Hsh Hbud Hsp Hok HnlS Hdsh Hdg Hra HK Hb) (only parsing).
Local Notation pgone := (@AsanSRipB.pgone b ms0 beg size) (only parsing).
Local Notation addzw := (@AsanSRipB.addzw b ms0 beg size) (only parsing).
Local Notation div8 := (@AsanSRipB.div8 b ms0 beg size) (only parsing).

Lemma br_geu_wr : forall (a : word) x, (0 <= x < 2 ^ 64)%Z -> branch_taken BC_GEU a (Z_to_bv 64 x) = negb (bv_unsigned a <? x)%Z.
Proof. intros a x Hx. pose proof (u64_range a). rewrite <- (Z_to_bv_u a) at 1. apply branch_geu_z; lia. Qed.

Lemma u_beg' : (0 <= B < 2 ^ 64)%Z.
Proof. pose proof (bv_unsigned_in_range 64 beg) as R. change (bv_modulus 64) with (2 ^ 64)%Z in R. exact R. Qed.

(* [comment removed for export] *)
Lemma B2t : forall ms model, BI ms model 0 Mf ->
  ms_pc_val ms = pcw b 0xd4 -> rg ms 2 = Z_to_bv 64 (SP + -64) ->
  rg ms 8 = beg -> rg ms 18 = Z_to_bv 64 E -> rg ms 21 = Z_to_bv 64 aK -> realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model (HF & Hmat & Hk0) Hpc Hsp2 H8 H18 H21.
  pose proof HF as (Hsvc & HR1 & HR2 & HR3 & HR4 & HR & Hmem). pose proof u_sp0. pose proof (u64_range beg). pose proof u_beg'.
  pose proof ab8_f. pose proof ae8_f.
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model 0 Hmat); exact Hh0).
  wsx wacc_Branch F_d4 D_23247863. rgn. rewrite H8, H18. rewrite (br_geu_wr beg E) by lia. rewrite (proj2 (Z.ltb_lt B E)) by lia. cbn [negb]. pcn.
  wsx wacc_OpImm F_d8 D_00740513. rgn. rewrite H8, alu_add, w_add_sext. lits.
  wsx wacc_OpImm F_dc D_ff857513. rgn. rewrite andm8, u_add_small by lia.
  replace ((B + 7) / 8 * 8)%Z with (8 * ab8)%Z by (unfold ab8; lia).
  wsx wacc_OpImm F_e0 D_ff897a13. rgn. rewrite ?H18, andm8, bvu_z by lia.
  replace (E / 8 * 8)%Z with (8 * ae8)%Z by (unfold ae8; lia).
  eapply rzc_acc; [ assumption | reflexivity | eapply wacc_Jal; [ fetch_tac F_e4 | reflexivity | exact D_a91ff0ef ] | apply acc_ok_nil | ].
  pcn.
  apply (h_sum model Hh _ T (8 * ab8)).
  - reflexivity.
  - cbn [ms_pc_val setx]. unfold pcw. f_equal. lia.
  - rgn. reflexivity.
  - destruct Hreg as [HH|HL]; [right | left]; lia.
  - cbn [ms_mem setx]. rewrite Hmem. exact globals_Mf.
  - exact (globals_nl_mat model 0 Hmat).
  - rgn. apply ra_even; lia.
  - intros ms' HFR Hpc' H10'.
    rewrite div8 in H10'.
    pose proof HFR as (_ & _ & _ & _ & _ & _ & GR).
    apply (B3 ms' model).
    + split; [|split; [exact Hmat | lia]].
      refine (MF_FR ms0 _ ms' BCLOB HCLOB Mf _ HFR _); [ mfs HF | intros r Hin; cbn in Hin |- *; tauto ].
    + rewrite Hpc'. rgn. reflexivity.
    + rewrite GR by (cbn; intuition discriminate). rgn. exact Hsp2.
    + rewrite GR by (cbn; intuition discriminate). rgn. exact H8.
    + rewrite GR by (cbn; intuition discriminate). rgn. exact H18.
    + rewrite GR by (cbn; intuition discriminate). rgn. reflexivity.
    + rewrite GR by (cbn; intuition discriminate). rgn. exact H21.
    + exact H10'.
Qed.

(* [comment removed for export] *)
Lemma B2 : forall ms model, BI ms model 0 Mf ->
  ms_pc_val ms = pcw b 0x8c -> rg ms 2 = Z_to_bv 64 (SP + -64) ->
  rg ms 8 = beg -> rg ms 9 = Z_to_bv 64 size -> rg ms 21 = Z_to_bv 64 aK ->
  rg ms 11 = Z_to_bv 64 K -> rg ms 12 = Z_to_bv 64 0x7fff7fff -> realizes_cfg segs cfg (mkCfg ms model) T.
Proof.
  intros ms model (HF & Hmat & Hk0) Hpc Hsp2 H8 H9 H21 H11 H12.
  pose proof HF as (Hsvc & HR1 & HR2 & HR3 & HR4 & HR & Hmem). pose proof u_sp0. pose proof (u64_range beg). pose proof u_beg'.
  pose proof ab8_f. pose proof ae8_f.
  assert (Hh : m_halted model = None) by (rewrite (mat_of_halted model0 model 0 Hmat); exact Hh0).
  pose proof (globals_nl_mat model 0 Hmat) as (NgK & NaK & NgMB & NaMB & NgME & NaME & NgHE & NaHE).
  pose proof globals_Mf as ((lgK & HlgK & HvgK) & (laK & HlaK & HvaK) & (lgMB & HlgMB & HvgMB) & (laMB & HlaMB & HvaMB) &
                            (lgME & HlgME & HvgME) & (laME & HlaME & HvaME) & (lgHE & HlgHE & HvgHE) & (laHE & HlaHE & HvaHE)).
  rewrite <- Hmem in HlgK, HlaK, HlgMB, HlaMB, HlgME, HlaME, HlgHE, HlaHE.
  wsx wacc_Op F_8c D_00848933. rgn. rewrite H9, H8, alu_add, addzw.
  wsx wacc_Branch F_90 D_05267263. rgn. rewrite H12, branch_geu_z by lia.
  destruct Hreg as [HH|HL].
  2:{ (* [comment removed for export] *)
    rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [negb]. pcn.
    apply (B2t _ model); [ split; [mfs HF | split; [exact Hmat | lia]] | reflexivity | rgn; exact Hsp2 | rgn; exact H8
      | rgn; reflexivity | rgn; exact H21 ]. }
  rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb]. pcn.
  wpair HP94 HlgMB HvgMB NgMB.
  wpair HP9c HlgME HvgME NgME.
  wvar F_a4 D_00063783 HlaMB HvaMB NaMB.
  wvar F_a8 D_0006b603 HlaME HvaME NaME.
  wsx wacc_OpImm F_ac D_fff78713. rgn. cnorm.
  wsx wacc_Branch F_b0 D_01277463. rgn. rewrite branch_geu_z by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbn [negb]. pcn.
  wpair HPb8 HlgHE HvgHE NgHE.
  wvar F_c0 D_0006b883 HlaHE HvaHE NaHE.
  wsx wacc_ShiftImm F_c4 D_0038d693. rgn. cnorm.
  wsx wacc_Op F_c8 D_00b68833. rgn. rewrite H11. cnorm.
  wsx wacc_Branch F_cc D_1328e463. rgn. rewrite branch_ltu_z by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. pcn.
  wsx wacc_Branch F_d0 D_13287263. rgn. rewrite branch_geu_z by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [negb]. pcn.
  apply (B2t _ model); [ split; [mfs HF | split; [exact Hmat | lia]] | reflexivity | rgn; exact Hsp2 | rgn; exact H8
    | rgn; reflexivity | rgn; exact H21 ].
Qed.

End Main.
End Rip.
