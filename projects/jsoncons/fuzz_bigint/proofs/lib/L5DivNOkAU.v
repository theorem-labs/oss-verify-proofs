(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkGlueUb0 BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU L5Defs L5CoreKit L5Kn
     L5Core L5CoreSpecsU L5CoreKitU L5Words L5WordsB L5ReduceU L5ReduceGU L5DDqU L5SubMulU L5ShlU L5MulMU L5Hp L5NormU L5NormOkAU L5NormOkU
     L5DivSpecsU L5DivPartsU L5DivNPU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5DIVNOKAU.
Import L5CSU. Import L5W. Import L5DSU. Import L5DIVPU. Import L5DIVNPU.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r3 : (3%bv : bv 5) = reg 3. Proof. apply bv_eq; reflexivity. Qed.
Lemma r4 : (4%bv : bv 5) = reg 4. Proof. apply bv_eq; reflexivity. Qed.
Lemma r8 : (8%bv : bv 5) = reg 8. Proof. apply bv_eq; reflexivity. Qed.
Lemma r9 : (9%bv : bv 5) = reg 9. Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.
Lemma r12 : (12%bv : bv 5) = reg 12. Proof. apply bv_eq; reflexivity. Qed.
Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.
Lemma r14 : (14%bv : bv 5) = reg 14. Proof. apply bv_eq; reflexivity. Qed.
Lemma r18 : (18%bv : bv 5) = reg 18. Proof. apply bv_eq; reflexivity. Qed.
Lemma rK k : 0 <= k < 32 -> (Z_to_bv 5 k : bv 5) = reg (Z.to_nat k). Proof. intros Hk. apply bv_eq. rewrite Z2Nat.id by lia. reflexivity. Qed.

Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall i, In i cs_all -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Lemma preserved_sregs R R' i : regs_preserved R R' -> In i cs_all -> getr R' (reg i) = getr R (reg i).
Proof.
  intros RP Hi. apply RP. unfold callee_saved_idx. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [cbn; tauto|]). destruct Hi.
Qed.

Lemma u64_at_agree1 M M' a v : (forall i, a <= i < a + 8 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 8 <= 2 ^ 64 ->
  L5.u64_at RSEGS M a v -> L5.u64_at RSEGS M' a v.
Proof. intros HA Ha H8 Hu. eapply (L5C.u64_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact Hu. Qed.
Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.
Lemma u8_at_agree1 M M' a v : (forall i, a <= i < a + 1 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 1 <= 2 ^ 64 ->
  L5.u8_at RSEGS M a v -> L5.u8_at RSEGS M' a v.
Proof. intros HA Ha H1 Hu. eapply (L5C.u8_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact Hu. Qed.
Lemma defined_agree1 M M' a n : (forall i, a <= i < a + n -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> L5.defined M a n -> L5.defined M' a n.
Proof. intros HA D i Hi. rewrite HA by lia. apply D. exact Hi. Qed.
Lemma big_at_agree1 M M' o b : (forall i, o <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  L5.big_at RSEGS M o b -> L5.big_at RSEGS M' o b.
Proof. intros HA Ho H32 OB. eapply (L5C.big_at_agree RSEGS M M'). intros i Hi. apply HA. exact Hi. lia. lia. exact OB. Qed.

(* [comment removed for export] *)
Lemma framew_Z (M M' : word -> option byte) (P : Z -> Prop) :
  (forall a : word, P (bv_unsigned a) -> M' a = M a) -> forall i, 0 <= i < 2 ^ 64 -> P i -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i).
Proof. intros HF i Hi HP. apply HF. rewrite BG.unsigned_lit by lia. exact HP. Qed.

Lemma model_ok_but_vm m m' : model_ok m -> model_but_vm m m' -> model_ok m'.
Proof.
  intros (A & B & C) H. split. rewrite (L5C.halted_but_vm _ _ H). exact A. split. rewrite (L5C.lazy_but_vm _ _ H). exact B.
  rewrite (L5C.materialized_but_vm _ _ H). exact C.
Qed.
Lemma mem_eq (M M' : word -> option byte) : (forall a, M' a = M a) -> M' = M.
Proof. intros H. apply functional_extensionality. exact H. Qed.
Lemma mod16_mod8 q : q mod 16 = 0 -> q mod 8 = 0.
Proof.
  intros H. pose proof (Z.div_mod q 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E.
  replace (16 * (q / 16)) with ((2 * (q / 16)) * 8) by lia. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma defined_byte M a : L5.defined M a 1 -> 0 <= a -> a + 1 <= 2 ^ 64 -> exists b, 0 <= b < 256 /\ L5.u8_at RSEGS M a b.
Proof.
  intros D Ha H1. unfold L5.u8_at. cbn [rdn].
  destruct (M (Z_to_bv 64 a)) as [b|] eqn:E.
  2:{ exfalso. apply (D 0). lia. rewrite Z.add_0_r. exact E. }
  exists (bv_unsigned b). split. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
  cbn. f_equal. f_equal. symmetry. apply Z_to_bv_bv_unsigned.
Qed.

(* [comment removed for export] *)
Lemma div_saves_kept M M' sp R : (forall i, sp - 104 <= i < sp -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= sp - 104 -> sp <= 2 ^ 64 ->
  div_saves M sp R -> div_saves M' sp R.
Proof.
  intros HA Hlo Hhi (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13). unfold div_saves.
  repeat split; (eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]).
Qed.

(* [comment removed for export] *)
Lemma lb_remove_head A n LB : lb_remove A ((A, n) :: LB) = LB.
Proof. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma lb_remove_skip A B m LB : B <> A -> lb_remove A ((B, m) :: LB) = (B, m) :: lb_remove A LB.
Proof. intros NE. cbn. destruct (Z.eqb_spec B A). contradiction. reflexivity. Qed.

(* [comment removed for export] *)
Lemma credit_chain L cr : 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L -> credit_for L cr DIVN_K DIVN_BYTES ->
  credit_ok L cr 64 /\ credit_ok L (debit L cr 64) 64 /\ credit_ok L (debit L (debit L cr 64) 64) 64.
Proof. unfold credit_for, credit_ok, debit, DIVN_K, DIVN_BYTES. cbn [fst snd]. intros KP BP [A B]. repeat split; lia. Qed.
Lemma credit_after2 L cr : 0 <= hl_k_per_malloc L -> 0 <= hl_b_overhead L ->
  credit_after L cr DIVN_K DIVN_BYTES (debit L (debit L cr 64) 64).
Proof. unfold credit_after, debit, DIVN_K, DIVN_BYTES. cbn [fst snd]. intros A B. split; lia. Qed.
Lemma credit_after3 L cr : credit_after L cr DIVN_K DIVN_BYTES (debit L (debit L (debit L cr 64) 64) 64).
Proof. unfold credit_after, debit, DIVN_K, DIVN_BYTES. cbn [fst snd]. split; lia. Qed.

(* [comment removed for export] *)
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].
(* [comment removed for export] *)
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac uSCR := unfold DIV_SCR, L5NORMU.NORM_SCR, L5MULMU.MULM_SCR, L5SHLU.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR,
  OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
(* [comment removed for export] *)
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
(* [comment removed for export] *)
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; lia.
Local Ltac fsclia := prune_impl; prune_disj; uSCR; lia.

(* [comment removed for export] *)
Definition VdG (sp X qX rr dv fbX lenX nR : Z) (R0 : bvmap 5 word)
           (B1 f41 c42 p43 f44 v68 v69 v70 v71 v72 v73 v75 v76 v79 : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp
  | 33%nat => X | 34%nat => dv | 35%nat => X | 36%nat => rr | 37%nat => 0 | 38%nat => fbX | 39%nat => lenX | 40%nat => qX
  | 41%nat => f41 | 42%nat => c42 | 43%nat => p43 | 44%nat => f44 | 45%nat => lenX | 46%nat => B1 | 47%nat => 1
  | 48%nat => U R0 1 | 49%nat => U R0 8 | 50%nat => U R0 9 | 51%nat => U R0 18 | 52%nat => U R0 19 | 53%nat => U R0 20 | 54%nat => U R0 21
  | 55%nat => U R0 22 | 56%nat => U R0 23 | 57%nat => U R0 24 | 58%nat => U R0 25 | 59%nat => U R0 26 | 60%nat => U R0 27
  | 61%nat => 0 | 62%nat => 0 | 63%nat => MWORD | 64%nat => 0 | 65%nat => nR | 66%nat => sp - 120 | 67%nat => 1
  | 68%nat => v68 | 69%nat => v69 | 70%nat => v70 | 71%nat => v71 | 72%nat => v72 | 73%nat => v73 | 74%nat => MWORD | 75%nat => v75 | 76%nat => v76 | 77%nat => 0 | 78%nat => 0 | 79%nat => v79
  | _ => 0
  end.

(* [comment removed for export] *)
Definition rem_blocks (rst : L5.bstore) : list (Z * Z) := match rst with L5.BInl _ _ => [] | L5.BDyn _ q => [(q, 64)] end.
Definition rem_store (L : heap_layout) (LB : list (Z * Z)) (M : word -> option byte) (B0 B1 : Z) (rst : L5.bstore) : Prop :=
  match rst with
  | L5.BInl _ _ => True
  | L5.BDyn c q => c = 8 /\ block_range L q 64 /\ blocks_apart q 64 LB /\ L5.defined M q 64 /\ q <> B0 /\ q <> B1
  end.

(* [comment removed for export] *)
Definition locals_N (M : word -> option byte) (sp B0 B1 fd0 fn0 fnum fden : Z) : Prop :=
  L5.u8_at RSEGS M (sp - 280) fd0 /\ 0 <= fd0 < 256 /\ Z.testbit fd0 0 = false /\
  L5.u8_at RSEGS M (sp - 216) fn0 /\ 0 <= fn0 < 256 /\ Z.testbit fn0 0 = true /\ L5.u64_at RSEGS M (sp - 200) 8 /\ L5.u64_at RSEGS M (sp - 192) B0 /\
  L5.u8_at RSEGS M (sp - 184) fnum /\ 0 <= fnum < 256 /\ Z.testbit fnum 0 = true /\ L5.u64_at RSEGS M (sp - 168) 8 /\ L5.u64_at RSEGS M (sp - 160) B1 /\
  L5.u8_at RSEGS M (sp - 136) fden /\ 0 <= fden < 256 /\ Z.testbit fden 0 = false.
Lemma locals_N_kept M M' sp B0 B1 fd0 fn0 fnum fden :
  (forall i, sp - 280 <= i < sp - 104 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= sp - 352 -> sp <= 2 ^ 64 ->
  locals_N M sp B0 B1 fd0 fn0 fnum fden -> locals_N M' sp B0 B1 fd0 fn0 fnum fden.
Proof.
  intros HA Hlo Hhi (A1 & A2 & A3 & B1' & B2 & B3 & B4 & B5 & C1 & C2 & C3 & C4 & C5 & D1 & D2 & D3). unfold locals_N.
  repeat split;
    first [ assumption | lia
          | eapply u8_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]
          | eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption] ].
Qed.
(* [comment removed for export] *)
Definition marks_N (M : word -> option byte) (sp rr : Z) : Prop :=
  L5.u64_at RSEGS M (sp - 320) 0 /\ L5.u64_at RSEGS M (sp - 328) 0 /\ L5.u64_at RSEGS M (sp - 336) 0.
Lemma marks_N_kept M M' sp rr :
  (forall i, sp - 336 <= i < sp - 312 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= sp - 352 -> sp <= 2 ^ 64 ->
  marks_N M sp rr -> marks_N M' sp rr.
Proof.
  intros HA Hlo Hhi (A & B & C). unfold marks_N.
  repeat split; (eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]).
Qed.

Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L.
Hypothesis BPOS : 0 <= hl_b_overhead L.
Hypothesis COPYA : copya_spec L HI.
Hypothesis ASSIGN : assign_spec L HI.
Hypothesis RESIZE : resize_spec L HI.
Hypothesis OPDEL : opdel_sized_spec L HI.
Hypothesis HUGE : resize_huge_spec.
Hypothesis DIVLOOP : divloop_run_stmt.
Hypothesis DIVTAIL : divtail_stmt L HI.
Let norm_ok := L5NORMOKU.norm_ok L HI LY HIok RESIZE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (X qX rr dv fdv sp r : Z) (bX : L5.bigobj) (wX : list Z).
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G10 : getr R0 10%bv = Z_to_bv 64 X.
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 dv.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 X.
Hypothesis G13 : getr R0 13%bv = Z_to_bv 64 rr.
Hypothesis G14 : getr R0 14%bv = Z_to_bv 64 0.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 r.
Hypothesis RA : L5.ra_ok r.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 sp DIV_SCR.
Hypothesis IMGC : L5.img_clear M0 0x10000 0x20000.
Hypothesis OBX : L5.big_at RSEGS M0 X bX.
Hypothesis OLX : L5C.obj_limbs RSEGS M0 bX wX.
Hypothesis STX : L5.bo_st bX = L5.BDyn 8 qX.
Hypothesis LENX : (2 <= L5.bo_len bX <= 6)%nat.
Hypothesis SGNX : Z.testbit (L5.bo_fb bX) 1 = false.
Hypothesis INQ : In (qX, 64) LB.
Hypothesis DEFQ : L5.defined M0 qX 64.
Hypothesis AX8 : X mod 8 = 0.
Hypothesis SX : sp <= X.
Hypothesis HX : X + 32 <= hl_sptop L.
Hypothesis DEFX : L5.defined M0 X 32.
Hypothesis MW : mword_obj M0 dv fdv.
Hypothesis ADV : dv mod 8 = 0.
Hypothesis SDV : sp <= dv.
Hypothesis HDV : dv + 32 <= hl_sptop L.
Hypothesis ZR : zero_obj M0 rr.
Hypothesis ARR : rr mod 8 = 0.
Hypothesis SRR : sp <= rr.
Hypothesis HRR : rr + 32 <= hl_sptop L.
Hypothesis DEFR : L5.defined M0 rr 32.
Hypothesis AP1 : X + 32 <= dv \/ dv + 32 <= X.
Hypothesis AP2 : X + 32 <= rr \/ rr + 32 <= X.
Hypothesis AP3 : dv + 32 <= rr \/ rr + 32 <= dv.
Hypothesis CR : credit_for L cr DIVN_K DIVN_BYTES.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divN_post L LB cr M0 M' R0 R' X qX rr dv fdv sp LB' cr' ->
        model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K.
Hypothesis KONT3 : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divN_e3 L LB cr M0 M' R0 R' X qX (L5.bo_len bX) rr dv sp LB' cr' ->
        model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K.

(* [comment removed for export] *)
Let lenX : nat := L5.bo_len bX.
Let fbX : Z := L5.bo_fb bX.
Let nR : nat := rlen wX.
Let spd : Z := sp - 352.
Let WN : list L5.range := [(X, 32); (qX, 64); (rr, 32)].
Let Vd := VdG sp X qX rr dv fbX (Z.of_nat lenX) (Z.of_nat nR) R0.

(* [comment removed for export] *)
Lemma stk0 : sp mod 16 = 0 /\ hl_sptop L - 2 ^ 23 + DIV_SCR <= sp /\ sp <= hl_sptop L /\ (0x7fff80000000 <= hl_sptop L <= 2 ^ 47) /\ L5.defined M0 (sp - DIV_SCR) DIV_SCR.
Proof. exact STK. Qed.
Lemma IMG : hl_img_hi L = 0x92000. Proof. apply (ly_img_hi L LY). Qed.
Lemma IMGLO : hl_img_lo L = 0x10000. Proof. apply (ly_img_lo L LY). Qed.
Lemma ERRNO : hl_errno L + 4 <= 0x7fff7f800000. Proof using L LY R0 X qX rr dv sp bX wX LENX. rewrite (ly_errno L LY). lia. Qed.
Lemma ERRNOV : hl_errno L = 0x70e94. Proof. apply (ly_errno L LY). Qed.
Lemma SPTOP : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47. Proof. pose proof STK as (_ & _ & _ & WND & _). exact WND. Qed.
(* [comment removed for export] *)
Lemma SPW : sp mod 16 = 0 /\ 0x7fff7f800000 + 8976 <= sp /\ sp <= 2 ^ 47 /\ hl_sptop L - 8388608 + 8976 <= sp /\ sp <= hl_sptop L.
Proof using L R0 M0 X qX rr dv sp bX wX STK LENX AX8 SX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3. clear HX. pose proof STK as (A & B & C & D & _). uSCR. repeat split; try lia. Qed.
Lemma DIV_SCR_val : DIV_SCR = 8976. Proof. reflexivity. Qed.
Lemma LBhi LBx crx M VM : hi_heap HI LBx crx M VM -> forall b, In b LBx -> fst b + snd b <= (hl_sptop L - 8388608).
Proof. intros HH b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. Qed.
Lemma LBdef LBx crx M VM : hi_heap HI LBx crx M VM -> forall A n, In (A, n) LBx ->
  L5.defined M A n /\ (4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A)) /\ A + n <= (hl_sptop L - 8388608) /\ 0 < n.
Proof. intros HH A n Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) (A, n) Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Dd & _). cbn in *. repeat split; assumption. Qed.
(* [comment removed for export] *)
Lemma QX : 4096 <= qX /\ (qX + 64 <= 0x10000 \/ 0x92000 <= qX) /\ qX + 64 <= hl_sptop L - 8388608 /\ qX mod 8 = 0.
Proof.
  pose proof (LBdef _ _ _ _ HH0 qX 64 INQ) as (_ & (A & B) & C & _). rewrite IMG, IMGLO in B.
  pose proof OBX as OB. unfold L5.big_at in OB. rewrite STX in OB.
  destruct OB as (_ & _ & _ & _ & _ & _ & _ & _ & Q8 & _). repeat split; try assumption.
Qed.
Lemma wX_len : length wX = lenX. Proof. exact (proj1 OLX). Qed.
Lemma wX_ok : words_ok wX. Proof. exact (proj1 (proj2 OLX)). Qed.
Lemma nR_le : (nR <= lenX)%nat. Proof. unfold nR. rewrite <- wX_len. apply rlen_le. Qed.
Lemma fbX_rng : 0 <= fbX < 256. Proof. pose proof OBX as OB. unfold L5.big_at in OB. destruct OB as (_ & F & _). exact F. Qed.
Lemma UR1 : U R0 1 = r.
Proof using R0 X qX rr dv sp r bX wX G1 RA LENX. unfold U. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G1. pose proof RA as [Hr _]. apply BG.unsigned_lit. lia. Qed.
Lemma fbX_bit0 : Z.testbit fbX 0 = true.
Proof. pose proof OBX as OB. unfold L5.big_at in OB. rewrite STX in OB. destruct OB as (_ & _ & _ & D & _). exact D. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_Z (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (nq : nat) (B0 B1 fd0 fn0 fnum fden frem : Z) (nrem : nat) (rst : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = rem_blocks rst ++ (B0, 64) :: (B1, 64) :: LB -> B0 <> B1 -> credit_after L cr DIVN_K DIVN_BYTES crc ->
  div_saves M sp R0 -> marks_N M sp rr -> locals_N M sp B0 B1 fd0 fn0 fnum fden ->
  L5.big_at RSEGS M X (L5.BO fbX nq (L5.BDyn 8 qX)) -> (nq <= 6)%nat -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5.big_at RSEGS M rr (L5.BO frem nrem rst) -> rem_store L LB M B0 B1 rst -> L5.defined M rr 32 ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R LEXIT M model) K.
Proof using SCFG_P L HI LY HIok DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 KONT KONT3.
  intros H2 H9 H3 H4 MBV HH ELB NE01 CRA DS MK LOC OBq NQ DQ DX OBr RS DR MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (XHI: X + 32 <= 2 ^ 47) by flia.
  (* [comment removed for export] *)
  pose proof (d5ux1_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P1. cbn [Vd VdG] in P1.
  destruct (P1 ltac:(flia) ltac:(flia) H2 H9 ltac:(flia) A16) as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & A1 & A10). clear P1.
  pose proof (mem_eq M M1 FR1) as EM1. subst M1.
  (* [comment removed for export] *)
  destruct (L5KU.limbs_of_defined M qX nq ltac:(eapply L5.defined_sub; [exact DQ | flia | flia]) ltac:(flia) ltac:(flia)) as (wq & WQL & WQR & WQA).
  destruct (L5REDGU.reduce_run fx1 R1 M X 0x229e8 (L5.BO fbX nq (L5.BDyn 8 qX)) wq A10 A1 ltac:(split; [flia | reflexivity]) OBq AX8 ltac:(flia) XHI
              ltac:(eapply L5.writable_sub; [apply (L5C.writable_of_defined RSEGS); [exact DX | flia | flia] | flia | flia])
              ltac:(cbn [L5.bo_data L5.bo_cap L5.bo_st]; eapply L5.defined_sub; [exact DQ | flia | flia]) WQA WQL WQR
              ltac:(cbn [L5.bo_st]; intros cap q E; inversion E; subst; left; flia))
    as (fx2 & R2 & M2 & MS2 & OB2 & RP2 & B10 & FR2 & MG2).
  cbn [L5.bo_fb L5.bo_st] in OB2.
  set (fq := if (rlen wq =? 0)%nat then Z.land fbX 253 else fbX) in OB2.
  assert (FQ: 0 <= fq < 256 /\ Z.testbit fq 0 = true).
  { subst fq. destruct (rlen wq =? 0)%nat. split. apply L5.land_byte_range. lia. rewrite Z.land_spec, fbX_bit0. reflexivity.
    split. exact FBX. exact fbX_bit0. }
  assert (KEEP2: forall i, 0 <= i < 2 ^ 64 -> ~ (X <= i < X + 16) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. apply FR2. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by lia. lia. }
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  (* [comment removed for export] *)
  assert (E2: getr R2 (reg 2) = Z_to_bv 64 spd). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H2. }
  assert (E9: getr R2 (reg 9) = Z_to_bv 64 X). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H9. }
  assert (MK2: marks_N M2 sp rr). { eapply marks_N_kept. 4: exact MK. intros i Hi. apply KEEP2; flia. flia. flia. }
  pose proof MK2 as (C320 & C328 & C336).
  pose proof OB2 as (U0 & _ & U8 & _ & U16 & U24 & _).
  pose proof (d5ux2n_conc fx2 R2 M2 (Vd 0 0 0 0 0 0 fq 0 0 0 0 0 0 0)) as P2. cbn [Vd VdG] in P2.
  destruct (P2 ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) E2 E9 ltac:(flia) A16
               ltac:(eapply L5.writable_grows; [exact MG2|]; apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR0|flia|flia] | flia | flia])
               C320 C328 C336 ltac:(flia) AX8 ltac:(left; flia) U0 ltac:(flia)
               ltac:(eapply L5.writable_grows; [exact MG2|]; apply (L5C.writable_of_defined RSEGS); [exact DX | flia | flia]) ltac:(flia) ltac:(flia))
    as (fx3 & R3 & M3 & MG3 & _ & FR3 & MS3 & K3 & B10' & B11 & B19 & U0'). clear P2.
  rewrite Z.mul_0_r, Z.mod_0_l, Z.lor_0_r in U0' by flia.
  assert (KEEP3: forall i, 0 <= i < 2 ^ 64 -> ~ (X <= i < X + 16) -> M3 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. rewrite (FR3 i Hi) by flia. apply KEEP2; assumption. }
  pose proof (mem_grows_trans _ _ _ MG2 MG3) as MG13.
  (* [comment removed for export] *)
  set (fq' := Z.land fq 253) in U0'.
  assert (FQ': 0 <= fq' < 256 /\ Z.testbit fq' 0 = true /\ Z.testbit fq' 1 = false).
  { subst fq'. split. apply L5.land_byte_range. lia. rewrite !Z.land_spec. destruct FQ as [_ ->]. split. reflexivity. change (Z.testbit 253 1) with false. apply Bool.andb_false_r. }
  assert (OB3: L5.big_at RSEGS M3 X (L5.BO fq' (rlen wq) (L5.BDyn 8 qX))).
  { pose proof OB2 as (_ & _ & V8 & _ & V16 & V24 & Vle & Vcap & Vq8 & Vq & Vhi & Vha). unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st].
    split. exact U0'. split. exact (proj1 FQ'). split.
    { eapply u64_at_agree1. 4: exact V8. intros i Hi. apply FR3; flia. flia. flia. }
    split. exact (proj1 (proj2 FQ')). split.
    { eapply u64_at_agree1. 4: exact V16. intros i Hi. apply FR3; flia. flia. flia. }
    split. { eapply u64_at_agree1. 4: exact V24. intros i Hi. apply FR3; flia. flia. flia. }
    cbn [L5.bo_len] in Vle. repeat split; first [assumption | flia]. }
  (* [comment removed for export] *)
  assert (HH3: hi_heap HI LBc crc M3 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M3). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia.
    intros a Ha. destruct (Z_lt_le_dec a X) as [Y|Y]. left; apply KEEP3; flia.
    destruct (Z_lt_le_dec a (X + 16)) as [U|U]. right; left; flia. left; apply KEEP3; flia. exact MG13. }
  assert (SCR3: L5.defined M3 (sp - 8976) 8976). { eapply L5.defined_grows. exact MG13. exact SCR0. }
  assert (DS3: div_saves M3 sp R0). { eapply div_saves_kept. 4: exact DS. intros i Hi. apply KEEP3; flia. flia. flia. }
  assert (LOC3: locals_N M3 sp B0 B1 fd0 fn0 fnum fden). { eapply locals_N_kept. 4: exact LOC. intros i Hi. apply KEEP3; flia. flia. flia. }
  pose proof LOC3 as (Ld0 & Ld0r & Ld0b & Ln0 & Ln0r & Ln0b & Ln0c & Ln0p & Lnm & Lnmr & Lnmb & Lnmc & Lnmp & Ldn & Ldnr & Ldnb).
  assert (IN0: In (B0, 64) LBc). { subst LBc. apply in_app_iff. right. left. reflexivity. }
  assert (IN1: In (B1, 64) LBc). { subst LBc. apply in_app_iff. right. right. left. reflexivity. }
  pose proof (LBdef _ _ _ _ HH B0 64 IN0) as (DB0 & (B0lo & B0img) & B0hi & _).
  pose proof (LBdef _ _ _ _ HH B1 64 IN1) as (DB1 & (B1lo & B1img) & B1hi & _).
  assert (E2': getr R3 (reg 2) = Z_to_bv 64 spd). { rewrite (K3 2%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact E2. }
  assert (E3': getr R3 (reg 3) = Z_to_bv 64 GP).
  { rewrite (K3 3%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (preserved_sregs R1 R2 3 RP2) by inl.
    rewrite (K1 3%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H3. }
  assert (E4': getr R3 (reg 4) = Z_to_bv 64 TP).
  { rewrite (K3 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (preserved_sregs R1 R2 4 RP2) by inl.
    rewrite (K1 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H4. }
  (* [comment removed for export] *)
  assert (RB: forall q c, rst = L5.BDyn c q -> q <> B0 /\ q <> B1). { intros q c E. subst rst. cbn in RS. destruct RS as (_ & _ & _ & _ & N0 & N1). split; assumption. }
  assert (LBF1: lb_free fd0 0 LBc = LBc). { unfold lb_free. rewrite Ld0b. reflexivity. }
  assert (LBF2: lb_free fn0 B0 LBc = rem_blocks rst ++ (B1, 64) :: LB).
  { unfold lb_free. rewrite Ln0b. subst LBc. destruct rst as [v0 v1|c q]; cbn [rem_blocks app].
    apply lb_remove_head. destruct (RB q c eq_refl) as [N0 N1]. rewrite lb_remove_skip by exact N0. rewrite lb_remove_head. reflexivity. }
  assert (LBF3: lb_free fnum B1 (rem_blocks rst ++ (B1, 64) :: LB) = rem_blocks rst ++ LB).
  { unfold lb_free. rewrite Lnmb. destruct rst as [v0 v1|c q]; cbn [rem_blocks app].
    apply lb_remove_head. destruct (RB q c eq_refl) as [N0 N1]. rewrite lb_remove_skip by exact N1. rewrite lb_remove_head. reflexivity. }
  assert (LBF4: lb_free fden 0 (rem_blocks rst ++ LB) = rem_blocks rst ++ LB). { unfold lb_free. rewrite Ldnb. reflexivity. }
  (* [comment removed for export] *)
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml.
  eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. exact MS3.
  eapply (DIVTAIL fx3 R3 M3 model K LBc crc sp R0 fd0 0 0 fn0 8 B0 fnum 8 B1 fden 0 0 HH3 MOK HK0 E2' E4').
  - (* [comment removed for export] *) split. { replace (sp - 352) with (sp + (-22) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. exact SPTOP. uSCR. eapply L5.defined_sub. exact SCR3. flia. flia.
  - flia.
  - eapply L5.defined_sub. exact SCR3. flia. flia.
  - exact DS3.
  - rewrite UR1. exact RA.
  - split. exact Ld0. split. exact Ld0r. intros T. rewrite Ld0b in T. discriminate.
  - split. exact Ln0. split. exact Ln0r. intros _. split. exactA Ln0c. split. flia. split. exactA Ln0p. flia.
  - split. exact Lnm. split. exact Lnmr. intros _. split. exactA Lnmc. split. flia. split. exactA Lnmp. flia.
  - split. exact Ldn. split. exact Ldnr. intros T. rewrite Ldnb in T. discriminate.
  - intros T. rewrite Ld0b in T. discriminate.
  - intros _. rewrite LBF1. exact IN0.
  - intros _. rewrite LBF1, LBF2. apply in_app_iff. right. left. reflexivity.
  - intros T. rewrite Ldnb in T. discriminate.
  - (* [comment removed for export] *)
    cbv zeta. rewrite LBF1, LBF2, LBF3, LBF4. rewrite UR1.
    intros fx5 R5 M5 model5 T2 T3 T4 TS HP5 MBV5 HH5.
    assert (KST5: forall a, sp - 352 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
      apply L5C.outside_nil. }
    assert (KBL5: forall A n a, In (A, n) (rem_blocks rst ++ LB) -> A <= a < A + n -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros A n a Hin Ha. pose proof (LBdef _ _ _ _ HH5 A n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG, IMGLO in Aimg.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia. apply L5C.outside_nil. }
    assert (DQ5: L5.defined M5 qX 64).
    { eapply defined_agree1. intros i Hi. apply (KBL5 qX 64). apply in_app_iff; right; exact INQ. exact Hi. eapply L5.defined_grows. exact MG13. exact DQ. }
    destruct (L5KU.limbs_of_defined M5 qX (rlen wq) ltac:(eapply L5.defined_sub; [exact DQ5 | flia | pose proof (rlen_le wq); flia]) ltac:(flia) ltac:(pose proof (rlen_le wq); flia))
      as (wq' & WQL' & WQR' & WQA').
    assert (HP3: L5C.hpres L LB sp DIV_SCR WN M0 M3).
    { eapply (L5HP.hpres_trans L LB LB sp DIV_SCR WN M0 M M3 sp DIV_SCR WN). exact HP.
      - eapply (L5HP.hpres_piece L LB sp DIV_SCR WN M M3 (fun a => X <= a < X + 16)).
        + intros a Ha Hn. apply KEEP3; assumption.
        + intros a KA CH. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. apply (L5HP.outside_in _ _ X 32 OW). cbn. left; reflexivity. flia.
        + rewrite DIV_SCR_val. exact SCR3.
        + exact MG13.
      - intros a KA; exact KA.
      - intros b Hb; exact Hb.
      - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
    apply (KONT fx5 R5 M5 model5 (rem_blocks rst ++ LB) crc).
    + unfold divN_post. split.
      { apply preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|[<-|[<-|Hi]]];
          [ rewrite T2, <- r2, G2; reflexivity | rewrite T3, E3', <- r3, G3; reflexivity | rewrite T4, E4', <- r4, G4; reflexivity
          | apply TS; cbn; right; exact Hi ]. }
      split. { exists fq', (rlen wq), wq'. split.
               { eapply big_at_agree1. 4: exact OB3. intros i Hi. apply KST5; flia. flia. flia. }
               split. { unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. exact WQL'. split. exact WQR'. exact WQA'. }
               split. exact (proj2 (proj2 FQ')). split. pose proof (rlen_le wq). flia. exact DQ5. }
      split. { exists frem, nrem, rst.
               assert (OBr5: L5.big_at RSEGS M5 rr (L5.BO frem nrem rst)).
               { eapply big_at_agree1. 4: { eapply big_at_agree1. 4: exact OBr. intros i Hi. apply KEEP3; generalize AP2; flia. flia. flia. }
                 intros i Hi. apply KST5; flia. flia. flia. }
               destruct rst as [v0 v1|c q].
               - exists (firstn nrem [v0; v1]). split. exact OBr5. split.
                 { pose proof OBr5 as (_ & _ & _ & _ & _ & _ & Hl2 & Hv0 & Hv1). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Hl2, Hv0, Hv1.
                   unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split.
                   { rewrite length_firstn. cbn [length]. flia. }
                   split. { destruct nrem as [|[|[|n3]]]; cbn; repeat constructor; flia. } reflexivity. }
                 reflexivity.
               - cbn in RS. destruct RS as (-> & BRq & BAq & DQq & Nq0 & Nq1).
                 pose proof OBr5 as (_ & _ & _ & _ & _ & _ & Hle & _). cbn [L5.bo_len L5.bo_st] in Hle.
                 assert (DQq5: L5.defined M5 q 64).
                 { eapply defined_agree1. intros i Hi. apply (KBL5 q 64). cbn. left; reflexivity. exact Hi. eapply L5.defined_grows. exact MG13. exact DQq. }
                 pose proof BRq as (Bq0 & Bq1 & Bq2 & Bq3 & Bq4).
                 destruct (L5KU.limbs_of_defined M5 q nrem ltac:(eapply L5.defined_sub; [exact DQq5 | flia | flia]) ltac:(flia) ltac:(flia)) as (wr & WRL & WRR & WRA).
                 exists wr. split. exact OBr5. split. { unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. exact WRL. split. exact WRR. exact WRA. }
                 split. reflexivity. split. reflexivity. split. exact BRq. split. exact BAq. exact DQq5. }
      split. { destruct MWc as [OBd SGd]. split. 2: exact SGd.
               eapply big_at_agree1. 4: { eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KEEP3; generalize AP1; flia. flia. flia. }
               intros i Hi. apply KST5; flia. flia. flia. }
      split. exact CRA.
      eapply (L5HP.hpres_trans L LB (rem_blocks rst ++ LB) sp DIV_SCR WN M0 M3 M5 (sp - 352) OPDEL_SCR []). exact HP3. exact HP5.
      * intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. apply in_app_iff. right; exact Hb. } fsclia. flia. intros _. apply L5C.outside_nil.
      * intros b Hb. apply in_app_iff. right; exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
    + eapply L5C.model_but_vm_trans. exact MBV. exact MBV5.
    + exact HH5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_L (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc : list (Z * Z)) (crc : credit)
      (n : nat) (B0 B1 fd0 fn0 fnum fden frem remd : Z) (nrem : nat) (rst : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 9) = Z_to_bv 64 X -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  L5.u64_at RSEGS M (sp - 304) remd -> getr R (reg 18) = Z_to_bv 64 X -> L5.u64_at RSEGS M (sp - 152) (sp - 120) ->
  getr R (reg 21) = Z_to_bv 64 1 -> getr R (reg 22) = Z_to_bv 64 0 -> L5.u64_at RSEGS M (sp - 144) 1 -> L5.u64_at RSEGS M (sp - 232) qX ->
  getr R (reg 23) = Z_to_bv 64 (Z.of_nat n) -> (n <= 6)%nat ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = rem_blocks rst ++ (B0, 64) :: (B1, 64) :: LB -> B0 <> B1 -> credit_after L cr DIVN_K DIVN_BYTES crc ->
  div_saves M sp R0 -> marks_N M sp rr -> locals_N M sp B0 B1 fd0 fn0 fnum fden -> L5.u64_at RSEGS M (sp - 120) MWORD ->
  L5.big_at RSEGS M X (L5.BO fbX n (L5.BDyn 8 qX)) -> L5.defined M qX 64 -> L5.defined M X 32 ->
  L5.big_at RSEGS M rr (L5.BO frem nrem rst) -> rem_store L LB M B0 B1 rst -> L5.defined M rr 32 ->
  remd = L5.bo_data rr (L5.BO frem nrem rst) -> nrem = S n ->
  mword_obj M dv fdv ->
  L5C.hpres L LB sp DIV_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R PRE M model) K.
Proof using SCFG_P L HI LY HIok DIVLOOP DIVTAIL R0 M0 model0 K LB cr X qX rr dv fdv sp r bX wX HH0 MOK0 HK0 G1 RA G2 G3 G4 STK OBX STX LENX INQ DEFQ AX8 SX HX ADV SDV HDV ARR SRR HRR AP1 AP2 AP3 KONT KONT3.
  intros H2 H9 H3 H4 VR H18 VD H21 H22 VS VQ H23 Hn MBV HH ELB NE01 CRA DS MK LOC C120 OBq DQ DX OBr RS DR Eremd Enrem MWc HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof QX as (Q1 & Q2 & Q3 & Q4). pose proof fbX_rng as FBX.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (XHI: X + 32 <= 2 ^ 47) by flia. assert (RRHI: rr + 32 <= 2 ^ 47) by flia.
  assert (SCR0: L5.defined M (sp - DIV_SCR) DIV_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIV_SCR_val in SCR0.
  (* [comment removed for export] *)
  assert (REMD: remd mod 8 = 0 /\ 4096 <= remd /\ remd + 8 * (Z.of_nat n + 1) <= 2 ^ 47 /\ L5.defined M remd (8 * (Z.of_nat n + 1)) /\
                apart remd (8 * (Z.of_nat n + 1)) (sp - 416) 416 /\ apart remd (8 * (Z.of_nat n + 1)) qX (8 * (Z.of_nat n - Z.of_nat 0)) /\
                apart remd (8 * (Z.of_nat n + 1)) (sp - 120) (8 * (Z.of_nat 0 + 1)) /\
                (forall a, remd <= a < remd + 8 * (Z.of_nat n + 1) -> (rr + 16 <= a < rr + 32) \/ in_block LBc a)).
  { subst remd. destruct rst as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st].
    - pose proof OBr as (_ & _ & _ & _ & _ & _ & Hl2 & _). cbn [L5.bo_len] in Hl2. unfold apart.
      split. rewrite <- Zplus_mod_idemp_l, ARR. reflexivity. split. flia. split. flia.
      split. eapply L5.defined_sub. exact DR. flia. flia.
      split. flia. split. flia. split. flia. intros a Ha. left. flia.
    - cbn in RS. destruct RS as (-> & (Bq0 & Bq1 & Bq2 & Bq3 & Bq4) & BAq & DQq & Nq0 & Nq1). unfold apart.
      pose proof (BAq (qX, 64) INQ) as APQ. cbn in APQ.
      split. { apply mod16_mod8. exact Bq2. }
      split. flia. split. flia. split. eapply L5.defined_sub. exact DQq. flia. flia.
      split. flia. split. { generalize APQ Hn; clear; intros; lia. } split. flia.
      intros a Ha. right. exists (q, 64). split. subst LBc. cbn. left; reflexivity. cbn. flia. }
  destruct REMD as (RM8 & RMlo & RMhi & RMdef & RAP1 & RAP2 & RAP3 & RMin).
  (* [comment removed for export] *)
  destruct (DIVLOOP fx R M sp X remd qX (sp - 120) MWORD 0%nat n H2 H18 H21 H22 H23 VR VQ VD VS
              ltac:(replace (sp - 120 + 8 * Z.of_nat 0%nat) with (sp - 120) by (clear; lia); exact C120)
              ltac:(unfold MWORD; flia) ltac:(flia) ltac:(flia) A16 ltac:(flia)
              RM8 RMlo RMhi RMdef ltac:(apply (L5C.writable_of_defined RSEGS); [exact RMdef | flia | flia])
              Q4 Q1 ltac:(flia) ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact DQ | flia | flia] | flia | flia])
              ltac:(rewrite <- Zminus_mod_idemp_l, (mod16_mod8 _ A16); reflexivity) ltac:(flia) ltac:(flia) ltac:(eapply L5.defined_sub; [exact SCR0 | flia | flia])
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR0 | flia | flia] | flia | flia])
              ltac:(eapply L5.defined_sub; [exact SCR0 | flia | flia])
              RAP1 ltac:(unfold apart; flia) RAP2 RAP3 ltac:(unfold apart; flia) ltac:(unfold apart; flia) ltac:(unfold apart; flia))
    as (fx1 & R1 & M1 & MS1 & A2 & K1 & FR1 & MG1).
  change (Z.of_nat 0%nat) with 0 in FR1. rewrite Z.sub_0_r in FR1.
  assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (remd <= i < remd + 8 * (Z.of_nat n + 1)) -> ~ (qX <= i < qX + 8 * Z.of_nat n) ->
                 ~ (sp - 312 <= i < sp - 312 + 8) -> ~ (sp - 416 <= i < sp - 416 + 64) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi N1 N2 N3 N4. apply FR1; unfold inr; rewrite BG.unsigned_lit by exact Hi; assumption. }
  (* [comment removed for export] *)
  assert (NREM: forall a, remd <= a < remd + 8 * (Z.of_nat n + 1) -> (rr + 16 <= a < rr + 32) \/ a < hl_sptop L - 8388608).
  { intros a Ha. destruct (RMin a Ha) as [Hr|(b & Hb & Hin)]. left; exact Hr. right. pose proof (LBhi _ _ _ _ HH b Hb). flia. }
  assert (KFR: forall i, sp - 352 <= i < sp -> ~ (sp - 312 <= i < sp - 304) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Nq. apply KEEP1. flia. { intros C. destruct (NREM i C) as [D|D]. generalize AP2 D Hi SRR; clear; lia. flia. } flia. flia. flia. }
  assert (KX: forall i, X <= i < X + 32 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. { intros C. destruct (NREM i C) as [D|D]. generalize AP2 D Hi; clear; lia. flia. } flia. flia. flia. }
  assert (KRH: forall i, rr <= i < rr + 16 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. { intros C. destruct (NREM i C) as [D|D]. generalize D Hi; clear; lia. flia. } flia. flia. flia. }
  assert (KDV: forall i, dv <= i < dv + 32 -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi. apply KEEP1. flia. { intros C. destruct (NREM i C) as [D|D]. generalize AP3 D Hi; clear; lia. flia. } flia. flia. flia. }
  (* [comment removed for export] *)
  assert (E9: getr R1 (reg 9) = Z_to_bv 64 X). { rewrite (K1 9%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H9. }
  assert (E3: getr R1 (reg 3) = Z_to_bv 64 GP). { rewrite (K1 3%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H3. }
  assert (E4: getr R1 (reg 4) = Z_to_bv 64 TP). { rewrite (K1 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H4. }
  (* [comment removed for export] *)
  assert (INQc: In (qX, 64) LBc). { rewrite ELB. apply in_app_iff. right. right. right. exact INQ. }
  assert (HH1: hi_heap HI LBc crc M1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M1). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia. 2: exact MG1.
    assert (CASES: forall a, 0 <= a < 2 ^ 64 ->
       (sp - 416 <= a < sp) \/ (qX <= a < qX + 8 * Z.of_nat n) \/ (remd <= a < remd + 8 * (Z.of_nat n + 1)) \/
       (~ (remd <= a < remd + 8 * (Z.of_nat n + 1)) /\ ~ (qX <= a < qX + 8 * Z.of_nat n) /\ ~ (sp - 312 <= a < sp - 312 + 8) /\ ~ (sp - 416 <= a < sp - 416 + 64))).
    { intros a Ha. clear - Ha. lia. }
    intros a Ha. destruct (CASES a Ha) as [C|[C|[C|(C1 & C2 & C3 & C4)]]].
    - right; left; flia.
    - right; right. exists (qX, 64). split. exact INQc. cbn; flia.
    - destruct (RMin a C) as [Hr|Hb]. right; left; flia. right; right; exact Hb.
    - left. apply KEEP1; assumption. }
  assert (SCR1: L5.defined M1 (sp - 8976) 8976). { eapply L5.defined_grows. exact MG1. exact SCR0. }
  assert (DS1: div_saves M1 sp R0). { eapply div_saves_kept. 4: exact DS. intros i Hi. apply KFR; flia. flia. flia. }
  assert (MK1: marks_N M1 sp rr). { eapply marks_N_kept. 4: exact MK. intros i Hi. apply KFR; flia. flia. flia. }
  assert (LOC1: locals_N M1 sp B0 B1 fd0 fn0 fnum fden). { eapply locals_N_kept. 4: exact LOC. intros i Hi. apply KFR; flia. flia. flia. }
  assert (OBq1: L5.big_at RSEGS M1 X (L5.BO fbX n (L5.BDyn 8 qX))). { eapply big_at_agree1. 4: exact OBq. intros i Hi. apply KX; flia. flia. flia. }
  assert (DQ1: L5.defined M1 qX 64). { eapply L5.defined_grows. exact MG1. exact DQ. }
  assert (DX1: L5.defined M1 X 32). { eapply L5.defined_grows. exact MG1. exact DX. }
  assert (DR1: L5.defined M1 rr 32). { eapply L5.defined_grows. exact MG1. exact DR. }
  assert (MW1: mword_obj M1 dv fdv). { destruct MWc as [OBd SGd]. split. 2: exact SGd. eapply big_at_agree1. 4: exact OBd. intros i Hi. apply KDV; flia. flia. flia. }
  (* [comment removed for export] *)
  assert (RST1: exists rst1, rem_blocks rst1 = rem_blocks rst /\ rem_store L LB M1 B0 B1 rst1 /\ L5.big_at RSEGS M1 rr (L5.BO frem nrem rst1)).
  { pose proof OBr as (Ob0 & Obf & Ob8 & ObS). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Ob0, Obf, Ob8, ObS.
    destruct rst as [v0 v1|c q].
    - destruct ObS as (Tb & _ & _ & Hle & _).
      destruct (BDU.defined_word M1 (rr + 16) ltac:(eapply L5.defined_sub; [exact DR1 | flia | flia]) ltac:(flia) ltac:(flia)) as (v0' & R0' & U0').
      destruct (BDU.defined_word M1 (rr + 24) ltac:(eapply L5.defined_sub; [exact DR1 | flia | flia]) ltac:(flia) ltac:(flia)) as (v1' & R1' & U1').
      exists (L5.BInl v0' v1'). split. reflexivity. split. exact I.
      unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. split. { eapply u8_at_agree1. 4: exact Ob0. intros i Hi; apply KRH; flia. flia. flia. }
      split. exact Obf. split. { eapply u64_at_agree1. 4: exact Ob8. intros i Hi; apply KRH; flia. flia. flia. }
      split. exact Tb. split. exact U0'. split. exact U1'. split. exact Hle. split. exact R0'. exact R1'.
    - exists (L5.BDyn c q). split. reflexivity. split.
      { unfold rem_store in RS |- *. destruct RS as (RSa & RSb & RSc & RSd & RSe & RSf).
        refine (conj RSa (conj RSb (conj RSc (conj _ (conj RSe RSf))))). eapply L5.defined_grows. exact MG1. exact RSd. }
      eapply big_at_agree1. 4: exact OBr. 2: flia. 2: flia. intros i Hi. apply KEEP1. flia.
      { intros C. rewrite Eremd in C. cbn [L5.bo_data L5.bo_st] in C. unfold rem_store in RS. destruct RS as (_ & (_ & _ & _ & _ & Bq4) & _). flia. }
      flia. flia. flia. }
  destruct RST1 as (rst1 & RB1 & RS1 & OBr1).
  (* [comment removed for export] *)
  assert (HP1: L5C.hpres L LB sp DIV_SCR WN M0 M1).
  { eapply (L5HP.hpres_trans L LB LB sp DIV_SCR WN M0 M M1 sp DIV_SCR WN). exact HP.
    - eapply (L5HP.hpres_piece L LB sp DIV_SCR WN M M1
                (fun a => (remd <= a < remd + 8 * (Z.of_nat n + 1)) \/ (qX <= a < qX + 8 * Z.of_nat n) \/ (sp - 416 <= a < sp))).
      + intros a Ha Hn'. apply KEEP1; flia.
      + intros a KA [C|[C|C]].
        * pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW.
          subst remd. destruct rst as [v0 v1|c q]; cbn [L5.bo_data L5.bo_st] in C.
          { apply (L5HP.outside_in _ _ rr 32 OW). cbn. right; right; left; reflexivity.
            pose proof OBr as (_ & _ & _ & _ & _ & _ & Hle2 & _). cbn [L5.bo_len] in Hle2. flia. }
          cbn in RS. destruct RS as (-> & (Bq0 & Bq1 & Bq2 & Bq3 & Bq4) & BAq & DQq & Nq0 & Nq1).
          refine (L5C.kept_not_fresh L LB sp DIV_SCR WN a q 64 KA BAq _ Bq4 (LBhi _ _ _ _ HH0) _). exact Bq1. flia.
        * pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. apply (L5HP.outside_in _ _ qX 64 OW). cbn. right; left; reflexivity. flia.
        * refine (L5HP.kept_not_in_scratch L LB sp DIV_SCR WN a KA (LBhi _ _ _ _ HH0) _ _ _). fsclia. rewrite IMG; flia. fsclia.
      + rewrite DIV_SCR_val. exact SCR1.
      + exact MG1.
    - intros a KA; exact KA.
    - intros b Hb; exact Hb.
    - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
  (* [comment removed for export] *)
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  apply (stage_Z fx1 R1 M1 model LBc crc n B0 B1 fd0 fn0 fnum fden frem nrem rst1).
  - exact A2. - exact E9. - exact E3. - exact E4. - exact MBV. - exact HH1. - rewrite RB1. exact ELB. - exact NE01. - exact CRA.
  - exact DS1. - exact MK1. - exact LOC1. - exact OBq1. - exact Hn. - exact DQ1. - exact DX1. - exact OBr1. - exact RS1. - exact DR1.
  - exact MW1. - exact HP1.
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVNOKAU.
