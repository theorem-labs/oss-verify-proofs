(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Plain.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Src0PlanKit AsanPlanCore
     Src0_code_22348_22f60 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce BigLinkShl L5Defs L5CoreKit L5Kn
     L5Core L5CoreSpecs L5CoreKitS L5Words L5WordsB L5Reduce L5ReduceG L5DDq L5SubMul L5Shl L5MulM L5Hp L5Norm
     Src0Sums L5DivSpecs L5DivParts L5DivNP L5DivO2P L5DivO2S L5DivTail.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5DIVO2A.
Import L5CS. Import L5W. Import L5DS. Import L5DIVP. Import L5DIVNP. Import L5DIVO2P. Import L5DO2S.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
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
Lemma limbs_at_agree1 M M' q ws : (forall i, q <= i < q + 8 * Z.of_nat (length ws) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) ->
  0 <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 -> L5.limbs_at RSEGS M q ws -> L5.limbs_at RSEGS M' q ws.
Proof.
  intros HA Hq Hhi LA i Hi. eapply u64_at_agree1. 4: exact (LA i Hi). intros j Hj. apply HA. lia. lia. lia.
Qed.

Lemma mod16_mod8 q : q mod 16 = 0 -> q mod 8 = 0.
Proof. intros H. pose proof (Z.div_mod q 16 ltac:(lia)) as E. rewrite H, Z.add_0_r in E. rewrite E. rewrite Z.mul_comm. replace 16 with (2 * 8) by lia. rewrite Z.mul_assoc. apply Z_mod_mult. Qed.

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
Lemma lb_remove_app A X Z : (forall b, In b X -> fst b <> A) -> lb_remove A (X ++ Z) = X ++ lb_remove A Z.
Proof.
  induction X as [|[B m] X IH]; intros H. reflexivity.
  cbn [app]. rewrite lb_remove_skip. rewrite IH. reflexivity. intros b Hb. apply H. right. exact Hb. apply (H (B, m)). left. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma img_clear_kept L LB sp scr W M M' : L5C.hpres L LB sp scr W M M' -> layout L ->
  (forall a, 0x10000 <= a < 0x20000 -> L5.outside W a) -> L5.img_clear M 0x10000 0x20000 -> L5.img_clear M' 0x10000 0x20000.
Proof.
  intros HP LY HW IC i Hi. rewrite (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply IC. exact Hi.
  apply L5C.kept_static. rewrite (ly_img_lo L LY), (ly_img_hi L LY). lia.
  { intros HS. destruct (ly_static L LY i HS) as [X _]. lia. }
  rewrite (ly_img_lo L LY); lia. rewrite (ly_img_hi L LY); lia. rewrite (ly_errno L LY); lia. apply HW. exact Hi.
Qed.

(* [comment removed for export] *)
Definition MEMSET : Z := 0x58ea4.
Lemma memset_run fx R M (dst k r : Z) :
  getr R (reg 10) = Z_to_bv 64 dst -> getr R (reg 11) = Z_to_bv 64 0 -> getr R (reg 12) = Z_to_bv 64 k ->
  getr R (reg 1) = Z_to_bv 64 r -> L5.ra_ok r ->
  0 <= k -> 0 <= dst -> dst + k < 2 ^ 64 -> L5.writable RSEGS M dst k ->
  exists R3, msteps RSEGS (st fx R MEMSET M) (st fx R3 r (wbytes M (Z_to_bv 64 dst) (repeat (Z_to_bv 8 0) (Z.to_nat k))))
    /\ (forall i, In i L5CoreKit.L5K.CS -> getr R3 (reg i) = getr R (reg i)) /\ getr R3 (reg 10) = Z_to_bv 64 dst.
Proof.
  intros H10 H11 H12 H1 RA Hk Hd Hdk W.
  destruct (src0_fill_spec_memset fx M (Z_to_bv 64 dst) (Z_to_bv 64 0) k R (Z_to_bv 64 r) Hk
              ltac:(rewrite BG.unsigned_lit by lia; lia)
              ltac:(replace (Z_to_bv 64 dst) with (Z_to_bv 64 (dst + 0)) by (f_equal; lia); apply W; lia)
              ltac:(rewrite BG.unsigned_lit by lia; unfold AX2.two64; lia)
              (L5CoreKit.L5K.ret_ok_lit r RA) H1 H10 H11 H12) as (R3 & MS & KO & A10).
  exists R3. split. { rewrite BG.unsigned_lit in MS by lia. exact MS. }
  split. { intros i Hi. apply (L5CoreKit.L5K.kept_ok_index R R3 i KO Hi). } exact A10.
Qed.

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
Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac uSCR := unfold DIVO2_SCR, UNNORM_SCR, DIVEQ_SCR, DIV_SCR, L5NORM.NORM_SCR, L5MULM.MULM_SCR, L5SHL.SHL_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR,
  RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; lia.
Local Ltac fsclia := prune_impl; prune_disj; uSCR; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ob (o : option (Z * Z)) : list (Z * Z) := match o with Some b => [b] | None => [] end.

(* [comment removed for export] *)
Definition localsO2 (M : word -> option byte) (sp : Z) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad : Z) : Prop :=
  L5.u8_at RSEGS M (sp - 232) fd0 /\ 0 <= fd0 < 256 /\ Z.testbit fd0 0 = false /\
  local_obj M (sp - 200) fn0 c1 p1 /\ local_obj M (sp - 168) fnum c2 p2 /\
  L5.u8_at RSEGS M (sp - 136) fden /\ 0 <= fden < 256 /\ Z.testbit fden 0 = true /\ L5.u64_at RSEGS M (sp - 120) 8 /\ L5.u64_at RSEGS M (sp - 112) Ad.
Lemma local_obj_kept M M' o f c p : (forall i, o <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  local_obj M o f c p -> local_obj M' o f c p.
Proof.
  intros HA Ho Hhi (U0 & Hf & HD). split. { eapply u8_at_agree1. 4: exact U0. intros i Hi; apply HA; lia. lia. lia. } split. exact Hf.
  intros T. destruct (HD T) as (C16 & Hc & C24 & Hp & Hpc). split.
  eapply u64_at_agree1. 4: exact C16. intros i Hi; apply HA; lia. lia. lia. split. exact Hc. split.
  eapply u64_at_agree1. 4: exact C24. intros i Hi; apply HA; lia. lia. lia. split. exact Hp. exact Hpc.
Qed.
Lemma localsO2_kept M M' sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad :
  (forall i, sp - 232 <= i < sp - 104 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= sp - 304 -> sp <= 2 ^ 64 ->
  localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad -> localsO2 M' sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad.
Proof.
  intros HA Hlo Hhi (A1 & A2 & A3 & LO1 & LO2 & D1 & D2 & D3 & D4 & D5). unfold localsO2.
  split. eapply u8_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]. split. exact A2. split. exact A3.
  split. eapply local_obj_kept; [intros i Hi; apply HA; lia | lia | lia | eassumption].
  split. eapply local_obj_kept; [intros i Hi; apply HA; lia | lia | lia | eassumption].
  split. eapply u8_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]. split. exact D2. split. exact D3.
  split; (eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]).
Qed.
(* [comment removed for export] *)
Definition marksO2 (M : word -> option byte) (sp Y sgn qneg : Z) : Prop :=
  L5.u64_at RSEGS M (sp - 272) Y /\ L5.u64_at RSEGS M (sp - 280) sgn /\ L5.u64_at RSEGS M (sp - 288) qneg /\ L5.u64_at RSEGS M (sp - 256) 1
  /\ L5.u32_at RSEGS M (sp - 236) 2 /\ L5.u64_at RSEGS M (sp - 296) 0.
Lemma marksO2_kept M M' sp Y sgn qneg :
  (forall i, sp - 296 <= i < sp - 232 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= sp - 304 -> sp <= 2 ^ 64 ->
  marksO2 M sp Y sgn qneg -> marksO2 M' sp Y sgn qneg.
Proof.
  intros HA Hlo Hhi (A & B & C & D & E & F). unfold marksO2.
  repeat split; first [ eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]
                      | eapply u32_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption] ].
Qed.

(* [comment removed for export] *)
Definition ends (L : heap_layout) (LB : list (Z * Z)) (sty stR stq : L5.bstore) (eb : option (Z * Z)) : Prop :=
  match stq with
  | L5.BDyn capq Aq => eb = Some (Aq, 8 * capq) /\ block_range L Aq (8 * capq) /\ blocks_apart Aq (8 * capq) LB /\ 1 <= capq <= 300 /\
                       match sty, stR with L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q | _, _ => False end
  | L5.BInl _ _ =>
      match sty, stR with
      | L5.BDyn cap q, L5.BDyn cap' q' => cap' = cap /\ q' = q /\ eb = None
      | L5.BInl _ _, L5.BInl _ _ => eb = None
      | L5.BInl _ _, L5.BDyn cap' q' => cap' = 8 /\ eb = Some (q', 64) /\ block_range L q' 64 /\ blocks_apart q' 64 LB
      | L5.BDyn _ _, L5.BInl _ _ => False
      end
  end.

(* [comment removed for export] *)
Definition VdO (sp Y Q A fbY : Z) (R0 : bvmap 5 word)
           (v40 f41 c42 p43 f44 v45 v46 v47 v61 v65 v66 v68 v69 v70 v71 v72 v73 : Z) (j : nat) : Z :=
  match j with
  | 2%nat => sp
  | 33%nat => Y | 34%nat => A | 35%nat => Q | 36%nat => Y | 37%nat => 1 | 38%nat => fbY | 40%nat => v40
  | 41%nat => f41 | 42%nat => c42 | 43%nat => p43 | 44%nat => f44 | 45%nat => v45 | 46%nat => v46 | 47%nat => v47
  | 48%nat => U R0 1 | 49%nat => U R0 8 | 50%nat => U R0 9 | 51%nat => U R0 18 | 52%nat => U R0 19 | 53%nat => U R0 20 | 54%nat => U R0 21
  | 55%nat => U R0 22 | 56%nat => U R0 23 | 57%nat => U R0 24 | 58%nat => U R0 25 | 59%nat => U R0 26 | 60%nat => U R0 27
  | 61%nat => v61 | 62%nat => Z.land fbY 2 | 63%nat => 0 | 64%nat => 0 | 65%nat => v65 | 66%nat => v66 | 67%nat => 2
  | 68%nat => v68 | 69%nat => v69 | 70%nat => v70 | 71%nat => v71 | 72%nat => v72 | 73%nat => v73 | 74%nat => D1 | 75%nat => 0 | 76%nat => 0 | 77%nat => 2 | 78%nat => 0 | 79%nat => 0
  | _ => 0
  end.
(* [comment removed for export] *)
Lemma land2_rng f : 0 <= f -> 0 <= Z.land f 2 <= 2.
Proof. intros Hf. split. apply Z.land_nonneg. right; lia. pose proof (L5K.land_le_r f 2 Hf ltac:(lia)). lia. Qed.
Lemma land2_bit0 f : Z.testbit (Z.land f 2) 0 = false.
Proof. rewrite Z.land_spec. change (Z.testbit 2 0) with false. apply Bool.andb_false_r. Qed.
Lemma signfix_bit0 f s : Z.testbit s 0 = false -> Z.testbit (Z.lor (Z.land f 253) s) 0 = Z.testbit f 0.
Proof. intros Hs. rewrite Z.lor_spec, Z.land_spec, Hs. change (Z.testbit 253 0) with true. rewrite Bool.andb_true_r, Bool.orb_false_r. reflexivity. Qed.
Lemma signfix_rng f s : 0 <= f -> 0 <= s < 256 -> 0 <= Z.lor (Z.land f 253) s < 256.
Proof. intros Hf Hs. apply lor_byte. apply land_byte. exact Hf. lia. exact Hs. Qed.
(* [comment removed for export] *)
Lemma big_at_refb M M' o fb fb' n stx : L5.big_at RSEGS M o (L5.BO fb n stx) ->
  (forall i, o + 1 <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  L5.u8_at RSEGS M' o fb' -> 0 <= fb' < 256 -> Z.testbit fb' 0 = Z.testbit fb 0 -> L5.big_at RSEGS M' o (L5.BO fb' n stx).
Proof.
  intros (U0 & F & U8 & ST) HA Ho Hhi U0' F' B0. unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st] in *. split. exact U0'. split. exact F'. split.
  eapply u64_at_agree1. 4: exact U8. intros i Hi; apply HA; lia. lia. lia.
  destruct stx as [v0 v1|c q]; rewrite B0.
  - destruct ST as (T0 & V0 & V1 & REST). split. exact T0. split. eapply u64_at_agree1. 4: exact V0. intros i Hi; apply HA; lia. lia. lia.
    split. eapply u64_at_agree1. 4: exact V1. intros i Hi; apply HA; lia. lia. lia. exact REST.
  - destruct ST as (T0 & V0 & V1 & REST). split. exact T0. split. eapply u64_at_agree1. 4: exact V0. intros i Hi; apply HA; lia. lia. lia.
    split. eapply u64_at_agree1. 4: exact V1. intros i Hi; apply HA; lia. lia. lia. exact REST.
Qed.

(* [comment removed for export] *)
Definition same_st (a b : L5.bstore) : Prop :=
  match a, b with L5.BDyn c q, L5.BDyn c' q' => c' = c /\ q' = q | L5.BInl _ _, L5.BInl _ _ => True | _, _ => False end.
Lemma ends_same L LB sty stR st' stq eb : ends L LB sty stR stq eb -> same_st stR st' -> ends L LB sty st' stq eb.
Proof.
  unfold ends, same_st. intros E SM.
  destruct stq as [q0 q1|capq Aq]; destruct sty as [y0 y1|cy qy]; destruct stR as [v0 v1|c q]; destruct st' as [v0' v1'|c' q'];
    try (exfalso; exact SM); try (exfalso; exact E); try exact E.
  - destruct E as (-> & -> & BR & BA). destruct SM as (-> & ->). split. reflexivity. split. reflexivity. split. exact BR. exact BA.
  - destruct E as (-> & -> & ->). destruct SM as (-> & ->). split. reflexivity. split; reflexivity.
  - destruct E as (E1 & BR & BA & CQ & (-> & ->)). destruct SM as (-> & ->). split. exact E1. split. exact BR. split. exact BA. split. exact CQ. split; reflexivity.
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
Hypothesis NORM : L5NORM.norm_spec L HI.
Hypothesis UNNORMS : unnorm_spec L HI.
Hypothesis DIVLOOP : divloop_run_stmt.
Hypothesis DIVTAIL : divtail_stmt L HI.
Hypothesis DIVTAIL2 : L5DIVTAIL.divtail2_stmt L HI.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (Y Q A fba sp r : Z) (by_ : L5.bigobj) (wy : list Z).
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G10 : getr R0 10%bv = Z_to_bv 64 Y.
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 A.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 Q.
Hypothesis G13 : getr R0 13%bv = Z_to_bv 64 Y.
Hypothesis G14 : getr R0 14%bv = Z_to_bv 64 1.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 r.
Hypothesis RA : L5.ra_ok r.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 sp DIVO2_SCR.
Hypothesis IMGC : L5.img_clear M0 0x10000 0x20000.
Hypothesis YOK : y_ok LB M0 Y by_ wy.
Hypothesis LEN1 : (1 <= L5.bo_len by_)%nat.
Hypothesis CAPY : L5.bo_cap by_ <= 268.
Hypothesis AY8 : Y mod 8 = 0.
Hypothesis SY : sp + 48 <= Y.
Hypothesis HY : Y + 32 <= hl_sptop L.
Hypothesis WRY : L5.writable RSEGS M0 Y 32.
Hypothesis WRB : forall cap q, L5.bo_st by_ = L5.BDyn cap q -> L5.writable RSEGS M0 q (8 * cap).
Hypothesis AOK : a_ok M0 A fba.
Hypothesis AA8 : A mod 8 = 0.
Hypothesis SA : sp + 48 <= A.
Hypothesis HA : A + 32 <= hl_sptop L.
Hypothesis ZQ : zero_obj M0 Q.
Hypothesis AQ8 : Q mod 8 = 0.
Hypothesis SQ : sp <= Q.
Hypothesis HQ : Q + 32 <= hl_sptop L.
Hypothesis WRQ : L5.writable RSEGS M0 Q 32.
Hypothesis AP1 : Y + 32 <= A \/ A + 32 <= Y.
Hypothesis AP2 : Q + 32 <= Y.
Hypothesis AP3 : Q + 32 <= A.
Hypothesis CR : credit_for L cr DIVO2_K (divO2_bytes (L5.bo_cap by_)).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
        divO2_post L LB cr M0 M' R0 R' Y Q A fba sp by_ LB' cr' ->
        model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K.

(* [comment removed for export] *)
Let Ln : nat := L5.bo_len by_.
Let fbY : Z := L5.bo_fb by_.
Let sty : L5.bstore := L5.bo_st by_.
Let capy : Z := L5.bo_cap by_.
Let yd0 : Z := L5.bo_data Y by_.
Let spd : Z := sp - 304.
Let WN : list L5.range := [(Y, 32); (yd0, 8 * capy); (Q, 32)].
Let Vd := VdO sp Y Q A fbY R0.

(* [comment removed for export] *)
Lemma IMG : hl_img_hi L = 0x91000. Proof. apply (ly_img_hi L LY). Qed.
Lemma IMGLO : hl_img_lo L = 0x10000. Proof. apply (ly_img_lo L LY). Qed.
Lemma ERRNO : hl_errno L + 4 <= 0x7fff7f800000. Proof using L LY R0 Y Q A sp by_ LEN1. rewrite (ly_errno L LY). lia. Qed.
Lemma ERRNOV : hl_errno L = 0x70394. Proof. apply (ly_errno L LY). Qed.
Lemma SPTOP : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47. Proof. pose proof STK as (_ & _ & _ & WND & _). exact WND. Qed.
Lemma DIVO2_SCR_val : DIVO2_SCR = 9264. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma SPW : sp mod 16 = 0 /\ 0x7fff7f800000 + 9264 <= sp /\ sp <= 2 ^ 47 /\ hl_sptop L - 8388608 + 9264 <= sp /\ sp <= hl_sptop L.
Proof using L R0 M0 Y Q A sp by_ STK LEN1 AY8 SY AA8 SA HA AQ8 SQ. clear HY. pose proof STK as (A0 & B & C & D & _). rewrite DIVO2_SCR_val in B. repeat split; try lia. Qed.
Lemma LBhi LBx crx M VM : hi_heap HI LBx crx M VM -> forall b, In b LBx -> fst b + snd b <= (hl_sptop L - 8388608).
Proof. intros HH b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. Qed.
Lemma LBdef LBx crx M VM : hi_heap HI LBx crx M VM -> forall A0 n, In (A0, n) LBx ->
  L5.defined M A0 n /\ (4096 <= A0 /\ (A0 + n <= hl_img_lo L \/ hl_img_hi L <= A0)) /\ A0 + n <= (hl_sptop L - 8388608) /\ 0 < n /\ A0 mod 16 = 0.
Proof. intros HH A0 n Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) (A0, n) Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Dd & _). cbn in *. repeat split; assumption. Qed.
Lemma LBapart LBx crx M VM : hi_heap HI LBx crx M VM -> forall b, In b LBx -> blocks_apart (fst b) (snd b) (lb_remove (fst b) LBx).
Proof. intros HH b Hb. exact (proj2 (proj2 (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) b Hb))). Qed.
Lemma UR1 : U R0 1 = r.
Proof using R0 Y Q A sp r by_ G1 RA LEN1. unfold U. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G1. pose proof RA as [Hr _]. apply BG.unsigned_lit. lia. Qed.
Lemma YB : L5.big_at RSEGS M0 Y by_. Proof. exact (proj1 YOK). Qed.
Lemma fbY_rng : 0 <= fbY < 256. Proof. pose proof YB as OB. unfold L5.big_at in OB. destruct OB as (_ & F & _). exact F. Qed.
Lemma capy_rng : 1 <= capy <= 268.
Proof using R0 M0 LB Y Q A sp by_ wy YOK LEN1 CAPY WRB. split. 2: exact CAPY. unfold capy, L5.bo_cap. pose proof YB as OB. unfold L5.big_at in OB. destruct (L5.bo_st by_) as [v0 v1|c q]. lia. destruct OB as (_ & _ & _ & _ & _ & _ & _ & Hc & _). lia. Qed.
Lemma Ln_le : (1 <= Ln)%nat /\ match sty with L5.BDyn cap q => Z.of_nat Ln + 1 <= cap | L5.BInl _ _ => (Ln <= 2)%nat end.
Proof.
  split. exact LEN1. unfold Ln, sty. pose proof YOK as (OB & _ & _ & BLK). unfold L5.big_at in OB.
  destruct (L5.bo_st by_) as [v0 v1|c q]. destruct OB as (_ & _ & _ & _ & _ & _ & Hl & _). exact Hl. destruct BLK as (_ & _ & Hc). exact Hc.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_T (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad : Z) (fbR : Z) (nR : nat) (stR : L5.bstore) (fq : Z) (nq : nat) (stq : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr DIVO2_K (divO2_bytes capy) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB ->
  (* [comment removed for export] *)
  L5.big_at RSEGS M Y (L5.BO fbR nR stR) -> L5.defined M Y 32 -> L5.defined M (L5.bo_data Y (L5.BO fbR nR stR)) (8 * L5.bo_cap (L5.BO fbR nR stR)) ->
  L5.big_at RSEGS M Q (L5.BO fq nq stq) ->
  ends L LB sty stR stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R DT0 M model) K.
Proof using SCFG_P L HI LY HIok DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.
  intros H2 H3 H4 MBV HH ELB CRA DS LOC IN1 IN2 IN3 LBF OBY DY DYD OBQ ENDS DEB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof capy_rng as CAPR.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  pose proof LOC as (Ld0 & Ld0r & Ld0b & LO1 & LO2 & Ldn & Ldnr & Ldnb & Ldnc & Ldnp).
  pose proof (LBdef _ _ _ _ HH Ad 64 ltac:(apply (L5DIVTAIL.in_lb_free _ fn0 p1); apply (L5DIVTAIL.in_lb_free _ fnum p2); exact IN3)) as (DAd & (Adlo & Adimg) & Adhi & _ & Ad16).
  assert (LBF0: lb_free fd0 0 LBc = LBc). { unfold lb_free. rewrite Ld0b. reflexivity. }
  assert (LBF3: lb_free fden Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB). { unfold lb_free at 1. rewrite Ldnb. exact LBF. }
  unfold cfg.
  eapply (DIVTAIL fx R M model K LBc crc sp R0 fd0 0 0 fn0 c1 p1 fnum c2 p2 fden 8 Ad HH MOK HK0 H2 H4).
  - (* [comment removed for export] *) split. { replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. exact SPTOP. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - flia.
  - eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact DS.
  - rewrite UR1. exact RA.
  - split. exact Ld0. split. exact Ld0r. intros T. rewrite Ld0b in T. discriminate.
  - exact LO1.
  - exact LO2.
  - split. exact Ldn. split. exact Ldnr. intros _. split. exactA Ldnc. split. flia. split. exactA Ldnp. flia.
  - intros T. rewrite Ld0b in T. discriminate.
  - intros T. rewrite LBF0. exact (IN1 T).
  - intros T. rewrite LBF0. exact (IN2 T).
  - intros _. rewrite LBF0. exact IN3.
  - (* [comment removed for export] *)
    cbv zeta. rewrite LBF0, LBF3. rewrite UR1.
    intros fx5 R5 M5 model5 T2 T3 T4 TS HP5 MBV5 HH5.
    assert (KST5: forall a, sp - 304 <= a < 2 ^ 64 -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
      apply L5C.outside_nil. }
    assert (KBL5: forall A0 n a, In (A0, n) (ob eb ++ LB) -> A0 <= a < A0 + n -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros A0 n a Hin Ha. pose proof (LBdef _ _ _ _ HH5 A0 n Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG, IMGLO in Aimg.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia. apply L5C.outside_nil. }
    assert (OBY5: L5.big_at RSEGS M5 Y (L5.BO fbR nR stR)). { eapply big_at_agree1. 4: exact OBY. intros i Hi. apply KST5; flia. flia. flia. }
    assert (OBQ5: L5.big_at RSEGS M5 Q (L5.BO fq nq stq)). { eapply big_at_agree1. 4: exact OBQ. intros i Hi. apply KST5; flia. flia. flia. }
    (* [comment removed for export] *)
    assert (YL5: exists wy2 : list Z, L5C.obj_limbs RSEGS M5 (L5.BO fbR nR stR) wy2 /\ match stR with L5.BDyn cap q => L5.defined M5 q (8 * cap) | L5.BInl _ _ => True end).
    { pose proof OBY5 as (_ & _ & _ & ST5). cbn [L5.bo_st L5.bo_fb L5.bo_len] in ST5.
      destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_cap L5.bo_st] in DYD.
      - exists (firstn nR [v0; v1]). destruct ST5 as (_ & _ & _ & Hl2 & Hv0 & Hv1). split. 2: exact I.
        unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. { rewrite length_firstn. cbn [length]. flia. }
        split. { destruct nR as [|[|[|n3]]]; cbn; repeat constructor; flia. } reflexivity.
      - destruct ST5 as (_ & _ & _ & Hle & Hcap & Rq8 & Rq & Rhi & _).
        assert (INR: In (rd, 8 * capR) (ob eb ++ LB)).
        { unfold ends in ENDS. destruct stq as [q0 q1|capq Aq].
          + unfold sty in ENDS. destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY.
            * destruct ENDS as (-> & -> & _). left. reflexivity.
            * destruct ENDS as (-> & -> & ->). apply in_app_iff. right. pose proof YOK as (_ & _ & _ & BLK). rewrite EY in BLK. exact (proj1 BLK).
          + destruct ENDS as (-> & _ & _ & _ & SM). unfold sty in SM. destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY. destruct SM.
            destruct SM as (-> & ->). apply in_app_iff. right. pose proof YOK as (_ & _ & _ & BLK). rewrite EY in BLK. exact (proj1 BLK). }
        assert (DR5: L5.defined M5 rd (8 * capR)). { eapply defined_agree1. intros i Hi. apply (KBL5 rd (8 * capR)). exact INR. exact Hi. exact DYD. }
        destruct (L5KS.limbs_of_defined M5 rd nR ltac:(eapply L5.defined_sub; [exact DR5 | flia | flia]) ltac:(flia) ltac:(flia)) as (wr & WRL & WRR & WRA).
        exists wr. split. { unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. exact WRL. split. exact WRR. exact WRA. } exact DR5. }
    destruct YL5 as (wy' & YL5 & YD5).
    assert (FRESH5: forall A0 n LBx, block_range L A0 n -> blocks_apart A0 n LBx -> In (A0, n) (ob eb) -> L5C.fresh_block L LBx M5 A0 n).
    { intros A0 n LBx FB1 FB2 Hin. split. exact FB1. split. exact FB2. eapply defined_agree1. intros i Hi. apply (KBL5 A0 n). apply in_app_iff. left; exact Hin. exact Hi.
      exact (DEB _ Hin). }
    apply (KONT fx5 R5 M5 model5 (ob eb ++ LB) crc).
    + unfold divO2_post. split.
      { apply preserved_by_index. intros i Hi. cbn in Hi.
        destruct Hi as [<-|[<-|[<-|Hi]]];
          [ rewrite T2, <- r2, G2; reflexivity | rewrite T3, H3, <- r3, G3; reflexivity | rewrite T4, H4, <- r4, G4; reflexivity
          | apply TS; cbn; right; exact Hi ]. }
      split.
      { (* [comment removed for export] *)
        unfold ends in ENDS. destruct stq as [q0 q1|capq Aq].
        - exists (ob eb ++ LB). split.
          + exists (L5.BO fbR nR stR), wy'. split. exact OBY5. split. exact YL5. cbn [L5.bo_st]. unfold sty in ENDS.
            destruct (L5.bo_st by_) as [y0 y1|cy qy]; destruct stR as [v0 v1|capR rd]; try (exact ENDS).
            * rewrite ENDS. reflexivity.
            * destruct ENDS as (-> & -> & BR & BA). split. reflexivity. split. reflexivity. apply FRESH5. exact BR. exact BA. left. reflexivity.
            * destruct ENDS as (-> & -> & ->). split. reflexivity. split. reflexivity. split. reflexivity. exact YD5.
          + exists fq, nq, (L5.BInl q0 q1). split. exact OBQ5. reflexivity.
        - destruct ENDS as (-> & BR & BA & CQ & SM). exists LB. split.
          + exists (L5.BO fbR nR stR), wy'. split. exact OBY5. split. exact YL5. cbn [L5.bo_st]. unfold sty in SM.
            destruct (L5.bo_st by_) as [y0 y1|cy qy]; destruct stR as [v0 v1|capR rd]; try (destruct SM; fail); try exact SM.
            destruct SM as (-> & ->). split. reflexivity. split. reflexivity. split. reflexivity. exact YD5.
          + exists fq, nq, (L5.BDyn capq Aq). split. exact OBQ5. split. reflexivity. split. apply FRESH5. exact BR. exact BA. left. reflexivity. flia. }
      split.
      { destruct AOK as [OBa SGa]. split. 2: exact SGa.
        eapply big_at_agree1. 4: { eapply (L5C.big_at_agree RSEGS M0 M). 4: exact OBa. 2: flia. 2: flia.
          intros i Hi. apply (L5C.hpres_kept _ _ _ _ _ _ _ i HP). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
          unfold WN. apply L5C.outside_cons. unfold L5.in_rng; cbn; generalize AP1; flia. apply L5C.outside_cons.
          { unfold L5.in_rng; cbn. unfold yd0, capy, L5.bo_data, L5.bo_cap. pose proof YOK as (OB0 & _ & _ & BLK). unfold L5.big_at in OB0.
            destruct (L5.bo_st by_) as [y0 y1|cy qy]. generalize AP1; flia.
            pose proof (LBhi _ _ _ _ HH0 _ (proj1 BLK)) as BH. cbn in BH. flia. }
          apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
        intros i Hi. apply KST5; flia. flia. flia. }
      split. exact CRA.
      eapply (L5HP.hpres_trans L LB (ob eb ++ LB) sp DIVO2_SCR WN M0 M M5 (sp - 304) OPDEL_SCR []). exact HP. exact HP5.
      * intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. apply in_app_iff. right; exact Hb. } fsclia. flia. intros _. apply L5C.outside_nil.
      * intros b Hb. apply in_app_iff. right; exact Hb.
      * fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
    + eapply L5C.model_but_vm_trans. exact MBV. exact MBV5.
    + exact HH5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_X3 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad : Z) (fbR : Z) (nR : nat) (stR : L5.bstore) (fq : Z) (nq : nat) (stq : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 8) = Z_to_bv 64 Y -> getr R (reg 19) = Z_to_bv 64 (Z.land fbY 2) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr DIVO2_K (divO2_bytes capy) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB ->
  L5.big_at RSEGS M Y (L5.BO fbR nR stR) -> L5.defined M Y 32 -> L5.defined M (L5.bo_data Y (L5.BO fbR nR stR)) (8 * L5.bo_cap (L5.BO fbR nR stR)) ->
  L5.big_at RSEGS M Q (L5.BO fq nq stq) ->
  ends L LB sty stR stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R UNNORM_RET M model) K.
Proof using SCFG_P L HI LY HIok DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.
  intros H2 H3 H4 H8 H19 MBV HH ELB CRA DS LOC IN1 IN2 IN3 LBF OBY DY DYD OBQ ENDS DEB HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  pose proof OBY as (U0 & FR & U8 & ST).  cbn [L5.bo_fb L5.bo_len L5.bo_st] in U0, FR, U8, ST.
  pose proof (land2_rng fbY (proj1 FBY)) as S2.
  pose proof (d7x3_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0 fbR 0 0)) as P. cbn [Vd VdO] in P.
  destruct (P ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) H2 H8 H19 ltac:(flia) A16 ltac:(flia) AY8 ltac:(left; flia) U0 ltac:(flia)
              ltac:(apply (L5C.writable_of_defined RSEGS); [exact DY | flia | flia]) S2)
    as (fx1 & R1 & M1 & MG1 & FR1 & FRZ1 & MS1 & K1 & _ & U0'). clear P.
  assert (KEEP1: forall i, 0 <= i < 2 ^ 64 -> ~ (Y <= i < Y + 1) -> M1 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. apply FRZ1. exact Hi. flia. }
  set (fbR' := Z.lor (Z.land fbR 253) (Z.land fbY 2)) in U0'.
  assert (FB': 0 <= fbR' < 256 /\ Z.testbit fbR' 0 = Z.testbit fbR 0).
  { subst fbR'. split. apply signfix_rng. flia. flia. apply signfix_bit0. apply land2_bit0. }
  assert (OBY1: L5.big_at RSEGS M1 Y (L5.BO fbR' nR stR)).
  { eapply (big_at_refb M M1). exact OBY. intros i Hi. apply KEEP1; flia. flia. flia. exact U0'. exact (proj1 FB'). exact (proj2 FB'). }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (stage_T fx1 R1 M1 model LBc TB crc eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad fbR' nR stR fq nq stq).
  - rewrite (K1 2%nat) by inl. exact H2.
  - rewrite (K1 3%nat) by inl. exact H3.
  - rewrite (K1 4%nat) by inl. exact H4.
  - exact MBV.
  - eapply (L5C.hi_heap_client L SCFG HI). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia.
    intros a Ha. destruct (Z.eq_dec a Y) as [->|NE]. right; left. unfold hl_ceil. flia. left. apply KEEP1. exact Ha. flia. exact MG1.
  - exact ELB.
  - exact CRA.
  - eapply div_saves_kept. 4: exact DS. intros i Hi. apply KEEP1; flia. flia. flia.
  - eapply localsO2_kept. 4: exact LOC. intros i Hi. apply KEEP1; flia. flia. flia.
  - exact IN1. - exact IN2. - exact IN3. - exact LBF.
  - exact OBY1.
  - eapply L5.defined_grows. exact MG1. exact DY.
  - cbn [L5.bo_data L5.bo_cap L5.bo_st] in DYD |- *. eapply L5.defined_grows. exact MG1. exact DYD.
  - eapply big_at_agree1. 4: exact OBQ. intros i Hi. apply KEEP1; flia. flia. flia.
  - exact ENDS.
  - intros b Hb. eapply L5.defined_grows. exact MG1. apply DEB. exact Hb.
  - eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M1 sp DIVO2_SCR WN). exact HP.
    + eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M1 (fun a => Y <= a < Y + 1)).
      * intros a Ha Hn. apply KEEP1; assumption.
      * intros a KA CH. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. apply (L5HP.outside_in _ _ Y 32 OW). cbn. left; reflexivity. flia.
      * rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG1. exact SCR0.
      * exact MG1.
    + intros a KA; exact KA.
    + intros b Hb; exact Hb.
    + fsclia. + flia. + fsclia. + exact ERRNO. + exact (proj1 SPTOP).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma credit_after_unnorm crc cr' : credit_after L cr (DIVO2_K - DIVN_K) (divO2_bytes capy - DIVN_BYTES) crc ->
  credit_after L crc DIVN_K DIVN_BYTES cr' -> credit_after L cr DIVO2_K (divO2_bytes capy) cr'.
Proof using L cr Y Q A sp by_ LEN1. unfold credit_after. intros [A1 A2] [B1 B2]. split; flia. Qed.

Lemma stage_U (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad : Z) (fbR : Z) (nR : nat) (stR : L5.bstore) (wR : list Z) (fq : Z) (nq : nat) (stq : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 1) = Z_to_bv 64 UNNORM_RET -> getr R (reg 11) = Z_to_bv 64 Y -> getr R (reg 12) = Z_to_bv 64 2 -> getr R (reg 13) = Z_to_bv 64 0 ->
  getr R (reg 8) = Z_to_bv 64 Y -> getr R (reg 19) = Z_to_bv 64 (Z.land fbY 2) ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr (DIVO2_K - DIVN_K) (divO2_bytes capy - DIVN_BYTES) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB ->
  L5.big_at RSEGS M Y (L5.BO fbR nR stR) -> L5C.obj_limbs RSEGS M (L5.BO fbR nR stR) wR -> (2 <= nR <= 299)%nat -> Z.testbit fbR 1 = false ->
  L5.defined M Y 32 -> L5.defined M (L5.bo_data Y (L5.BO fbR nR stR)) (8 * L5.bo_cap (L5.BO fbR nR stR)) ->
  (forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) (ob eb ++ LB)) ->
  L5.big_at RSEGS M Q (L5.BO fq nq stq) ->
  ends L LB sty stR stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R UNNORM M model) K.
Proof using SCFG_P L HI LY HIok UNNORMS DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.
  intros H2 H3 H4 H1 H11 H12 H13 H8 H19 MBV HH ELB CRA DS LOC IN1 IN2 IN3 LBF OBY OLY NR SGN DY DYD INR OBQ ENDS DEB IMG1 HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (INR': forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) LBc).
  { intros cap q E. subst LBc. destruct (in_app_or _ _ _ (INR cap q E)) as [X|X]. apply in_app_iff. left; exact X. apply in_app_iff. right. apply in_app_iff. right. exact X. }
  unfold cfg.
  eapply (UNNORMS fx R M model K LBc crc Y 2 0 spd UNNORM_RET (L5.BO fbR nR stR) wR HH MOK HK0).
  - rewrite r11. exact H11.
  - rewrite r12. exact H12.
  - flia.
  - rewrite r13. exact H13.
  - left; reflexivity.
  - rewrite r1. exact H1.
  - split. unfold UNNORM_RET. flia. reflexivity.
  - rewrite r2. exact H2.
  - rewrite r3. exact H3.
  - rewrite r4. exact H4.
  - (* [comment removed for export] *) split. { unfold spd. replace (sp - 304) with (sp + (-19) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd. fsclia. split. unfold spd. flia. split. exact SPTOP. unfold spd. uSCR. eapply L5.defined_sub. exact SCR0. flia. flia.
  - exact IMG1.
  - exact OBY.
  - exact OLY.
  - cbn [L5.bo_len]. flia.
  - cbn [L5.bo_fb]. exact SGN.
  - exact AY8.
  - unfold spd. flia.
  - exact HY.
  - exact DY.
  - cbn [L5.bo_st]. intros cap q E. split. exact (INR' cap q E). subst stR. cbn [L5.bo_data L5.bo_cap L5.bo_st] in DYD. exact DYD.
  - intros X. discriminate X.
  - intros X. discriminate X.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 cr2 POST MBV2 HH2.
    destruct POST as (RP2 & (fb' & n' & st' & w' & OBY2 & OLY2 & SGN2 & SM2) & CRA2 & HP2). cbn [L5.bo_st] in SM2.
    cbn [L5.bo_data L5.bo_cap L5.bo_st] in HP2.
    (* [comment removed for export] *)
    assert (KST2: forall a, sp - 304 <= a < 2 ^ 64 -> ~ (Y <= a < Y + 32) ->
                  ~ (match stR with L5.BInl _ _ => Y + 16 <= a < Y + 16 + 8 * 2 | L5.BDyn cap q => q <= a < q + 8 * cap end) ->
                  M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha NY ND. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). apply L5C.kept_stack. unfold spd; fsclia. fsclia. unfold spd; flia. exact ERRNO. exact (proj1 SPTOP).
      apply L5C.outside_cons. unfold L5.in_rng; cbn. flia. apply L5C.outside_cons. 2: apply L5C.outside_nil.
      unfold L5.in_rng; cbn. destruct stR as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st]; flia. }
    assert (KBL2: forall A0 n a, In (A0, n) LBc -> (forall cap q, stR = L5.BDyn cap q -> A0 <> q) -> A0 <= a < A0 + n -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros A0 n a Hin NQ Ha. pose proof (LBdef _ _ _ _ HH A0 n Hin) as (_ & (Alo & Aimg) & Ahi & An0 & _). rewrite IMG, IMGLO in Aimg.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP2). eapply L5C.kept_block. exact Hin. exact Ha. flia. flia. rewrite ERRNOV. generalize Aimg; flia.
      apply L5C.outside_cons. { unfold L5.in_rng; cbn. pose proof (LBhi _ _ _ _ HH _ Hin) as BH. cbn in BH. unfold hl_ceil in *. flia. }
      apply L5C.outside_cons. 2: apply L5C.outside_nil.
      unfold L5.in_rng. cbn [fst snd]. destruct stR as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st].
      { pose proof (LBhi _ _ _ _ HH _ Hin) as BH. cbn in BH. unfold hl_ceil in *. flia. }
      specialize (NQ cap q eq_refl).
      pose proof (LBapart _ _ _ _ HH _ (INR' cap q eq_refl)) as BA. cbn [fst snd] in BA.
      assert (INrm: In (A0, n) (lb_remove q LBc)). { apply L5C.in_lb_remove_neq. exact Hin. exact NQ. }
      specialize (BA _ INrm). cbn in BA. generalize BA; flia. }
    pose proof MOK as MOK1. pose proof (model_ok_but_vm _ _ MOK1 MBV2) as (Mh2 & Ml2 & _).
    assert (SMR: same_st stR st'). { unfold same_st. destruct stR as [v0 v1|c q]; destruct st' as [v0' v1'|c' q']; first [exact (conj (proj1 SM2) (proj1 (proj2 SM2))) | exact SM2 | exact I]. }
    eapply (stage_X3 fx2 R2 M2 model2 LBc TB cr2 eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad fb' n' st' fq nq stq).
    + rewrite (preserved_sregs R R2 2 RP2) by inl. exact H2.
    + rewrite (preserved_sregs R R2 3 RP2) by inl. exact H3.
    + rewrite (preserved_sregs R R2 4 RP2) by inl. exact H4.
    + rewrite (preserved_sregs R R2 8 RP2) by inl. exact H8.
    + rewrite (preserved_sregs R R2 19 RP2) by inl. exact H19.
    + eapply L5C.model_but_vm_trans. exact MBV. exact MBV2.
    + exact HH2.
    + exact ELB.
    + exact (credit_after_unnorm crc cr2 CRA CRA2).
    + eapply div_saves_kept. 4: exact DS. 2: flia. 2: flia. intros i Hi. apply KST2. flia. flia.
      destruct stR as [v0 v1|cap q]. flia. pose proof (LBhi _ _ _ _ HH _ (INR' cap q eq_refl)) as BH. cbn in BH. unfold hl_ceil in *. flia.
    + eapply localsO2_kept. 4: exact LOC. 2: flia. 2: flia. intros i Hi. apply KST2. flia. flia.
      destruct stR as [v0 v1|cap q]. flia. pose proof (LBhi _ _ _ _ HH _ (INR' cap q eq_refl)) as BH. cbn in BH. unfold hl_ceil in *. flia.
    + exact IN1. + exact IN2. + exact IN3. + exact LBF.
    + exact OBY2.
    + intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Y + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno. rewrite ERRNOV. flia. apply DY. exact Hi.
    + (* [comment removed for export] *)
      destruct stR as [v0 v1|cap q]; destruct st' as [v0' v1'|cap' q']; try (exfalso; exact SM2); cbn [L5.bo_data L5.bo_cap L5.bo_st] in DYD |- *.
      * intros i Hi. apply (L5C.hpres_cdef _ _ _ _ _ _ _ (Y + 16 + i) HP2). flia. right; left. unfold hl_ceil, spd. fsclia. unfold in_errno. rewrite ERRNOV. flia. apply DYD. exact Hi.
      * destruct SM2 as (-> & -> & D2). exact D2.
    + exact OBQ || (eapply big_at_agree1; [ | | | exact OBQ]; [intros i Hi; apply KST2; [flia | flia | ] | flia | flia];
         destruct stR as [v0 v1|cap q]; [flia | pose proof (LBhi _ _ _ _ HH _ (INR' cap q eq_refl)) as BH; cbn in BH; unfold hl_ceil in *; flia]).
    + exact (ends_same _ _ _ _ _ _ _ ENDS SMR).
    + (* [comment removed for export] *)
      intros b Hb. unfold ends in ENDS. destruct stq as [q0 q1|capq Aq].
      * unfold sty in ENDS. destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY; destruct stR as [v0 v1|cap q]; destruct st' as [v0' v1'|cap' q'];
          try (exfalso; exact SM2); try (exfalso; exact ENDS).
        -- rewrite ENDS in Hb. destruct Hb.
        -- destruct ENDS as (-> & -> & BR & BA). destruct SM2 as (-> & -> & D2). destruct Hb as [<-|[]]. cbn [fst snd]. exactA D2.
        -- destruct ENDS as (-> & -> & ->). destruct Hb.
      * destruct ENDS as (-> & BR & BA & CQ & SM). destruct Hb as [<-|[]]. cbn [fst snd].
        unfold sty in SM. destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY; destruct stR as [v0 v1|cap q]; try (exfalso; exact SM). destruct SM as (-> & ->).
        pose proof YOK as (_ & _ & _ & BLK). rewrite EY in BLK. pose proof (BA _ (proj1 BLK)) as AP. cbn [fst snd] in AP.
        pose proof (LBdef _ _ _ _ HH0 qy (8 * cy) (proj1 BLK)) as (_ & _ & _ & Pn & _).
        eapply defined_agree1. 2: { apply (DEB (Aq, 8 * capq)). left; reflexivity. } cbn [fst snd]. intros i Hi. apply (KBL2 Aq (8 * capq)). subst LBc. left; reflexivity.
        intros cap0 q0 E. injection E. intros <- <-. generalize AP Pn CQ; flia. exact Hi.
    + eapply (L5HP.hpres_trans L LB LBc sp DIVO2_SCR WN M0 M M2 spd UNNORM_SCR). exact HP. exact HP2.
      * intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb. } unfold spd; fsclia. unfold spd; flia.
        intros OW.
        assert (OWY: ~ (Y <= a < Y + 32)) by exact (OW _ ltac:(left; reflexivity)).
        assert (OWD: ~ (yd0 <= a < yd0 + 8 * capy)) by exact (OW _ ltac:(right; left; reflexivity)).
        unfold yd0, capy, L5.bo_data, L5.bo_cap in OWD.
        (* [comment removed for export] *)
        assert (NYD: ~ match stR with L5.BInl _ _ => Y + 16 <= a < Y + 16 + 8 * 2 | L5.BDyn cap q => q <= a < q + 8 * cap end).
        { destruct stR as [v0 v1|cap q]. flia. unfold ends in ENDS. unfold sty in ENDS.
          destruct stq as [q0 q1|capq Aq]; destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY in ENDS, OWD |- *.
          - destruct ENDS as (-> & -> & BR & BA). pose proof (LBhi _ _ _ _ HH0) as LBH.
            apply (L5C.kept_not_fresh L LB sp DIVO2_SCR WN a q 64 KA BA). destruct BR as (_ & B1 & _ & _ & B4). exact B1. destruct BR as (_ & _ & _ & _ & B4). exact B4. exact LBH.
          - destruct ENDS as (-> & -> & _). exact OWD.
          - destruct ENDS as (_ & _ & _ & _ & SM). exfalso; exact SM.
          - destruct ENDS as (-> & _ & _ & _ & (-> & ->)). exact OWD. }
        apply L5C.outside_cons. exact OWY. apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng. cbn [fst snd].
        destruct stR as [v0 v1|cap q]; cbn [L5.bo_data L5.bo_cap L5.bo_st]; exact NYD.
      * intros b Hb. subst LBc. rewrite !in_app_iff. right; right; exact Hb.
      * unfold spd; fsclia. * flia. * fsclia. * exact ERRNO. * exact (proj1 SPTOP).
  - (* [comment removed for export] *) intros until 1. discriminate H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_Z (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LBc TB : list (Z * Z)) (crc : credit)
      (eb : option (Z * Z)) (fd0 fn0 c1 p1 fnum c2 p2 fden Ad qneg : Z) (fbR : Z) (nR : nat) (stR : L5.bstore) (fq : Z) (nq : nat) (stq : L5.bstore) :
  getr R (reg 2) = Z_to_bv 64 spd -> getr R (reg 3) = Z_to_bv 64 GP -> getr R (reg 4) = Z_to_bv 64 TP ->
  getr R (reg 9) = Z_to_bv 64 Q -> getr R (reg 18) = Z_to_bv 64 Y ->
  model_but_vm model0 model -> hi_heap HI LBc crc M (m_vmmaps model) ->
  LBc = ob eb ++ TB ++ LB -> credit_after L cr (DIVO2_K - DIVN_K) (divO2_bytes capy - DIVN_BYTES) crc ->
  div_saves M sp R0 -> localsO2 M sp fd0 fn0 c1 p1 fnum c2 p2 fden Ad -> marksO2 M sp Y (Z.land fbY 2) qneg -> 0 <= qneg <= 1 ->
  (Z.testbit fn0 0 = true -> In (p1, 8 * c1) LBc) -> (Z.testbit fnum 0 = true -> In (p2, 8 * c2) (lb_free fn0 p1 LBc)) ->
  In (Ad, 64) (lb_free fnum p2 (lb_free fn0 p1 LBc)) -> lb_remove Ad (lb_free fnum p2 (lb_free fn0 p1 LBc)) = ob eb ++ LB ->
  L5.big_at RSEGS M Y (L5.BO fbR nR stR) -> (2 <= nR <= 299)%nat -> Z.testbit fbR 1 = false ->
  L5.defined M Y 32 -> L5.defined M (L5.bo_data Y (L5.BO fbR nR stR)) (8 * L5.bo_cap (L5.BO fbR nR stR)) ->
  (forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) (ob eb ++ LB)) ->
  L5.big_at RSEGS M Q (L5.BO fq nq stq) -> L5.defined M Q 32 -> L5.defined M (L5.bo_data Q (L5.BO fq nq stq)) (8 * L5.bo_cap (L5.BO fq nq stq)) ->
  ends L LB sty stR stq eb ->
  (forall b, In b (ob eb) -> L5.defined M (fst b) (snd b)) ->
  L5.img_clear M 0x10000 0x20000 ->
  L5C.hpres L LB sp DIVO2_SCR WN M0 M ->
  srealizes RSEGS SCFG (cfg R LEXIT M model) K.
Proof using SCFG_P L HI LY HIok UNNORMS DIVTAIL R0 M0 model0 K LB cr Y Q A fba sp r by_ wy HH0 MOK0 HK0 G1 RA G2 G3 G4 STK YOK LEN1 CAPY AY8 SY HY WRB AOK AA8 SA HA AQ8 SQ HQ AP1 AP2 AP3 KONT.
  intros H2 H3 H4 H9 H18 MBV HH ELB CRA DS LOC MK Hq IN1 IN2 IN3 LBF OBY NR SGN DY DYD INR OBQ DQ DQD ENDS DEB IMG1 HP.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI'). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO.
  pose proof ERRNOV as ERRNOV. pose proof SPTOP as SPTOP. pose proof fbY_rng as FBY.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (SCR0: L5.defined M (sp - DIVO2_SCR) DIVO2_SCR) by exact (L5C.hpres_defined _ _ _ _ _ _ _ HP). rewrite DIVO2_SCR_val in SCR0.
  assert (QHI: Q + 32 <= 2 ^ 47) by flia.
  assert (INR': forall cap q, stR = L5.BDyn cap q -> In (q, 8 * cap) LBc).
  { intros cap q E. subst LBc. destruct (in_app_or _ _ _ (INR cap q E)) as [X|X]. apply in_app_iff. left; exact X. apply in_app_iff. right. apply in_app_iff. right. exact X. }
  (* [comment removed for export] *)
  assert (QD: forall cap q, stq = L5.BDyn cap q -> eb = Some (q, 8 * cap) /\ In (q, 8 * cap) LBc /\ (forall c' q', stR = L5.BDyn c' q' -> q + 8 * cap <= q' \/ q' + 8 * c' <= q)).
  { intros cap q E. subst stq. unfold ends in ENDS. destruct ENDS as (-> & BR & BA & CQ & SM). split. reflexivity. split. subst LBc. left; reflexivity.
    intros c' q' E'. subst stR. unfold sty in SM. destruct (L5.bo_st by_) as [y0 y1|cy qy] eqn:EY. exfalso; exact SM. destruct SM as (-> & ->).
    pose proof YOK as (_ & _ & _ & BLK). rewrite EY in BLK. pose proof (BA _ (proj1 BLK)) as AP. cbn [fst snd] in AP. generalize AP; flia. }
  (* [comment removed for export] *)
  pose proof (d5x1_conc fx R M (Vd 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0 0)) as P1. cbn [Vd VdO] in P1.
  destruct (P1 ltac:(flia) ltac:(flia) H2 H9 ltac:(flia) A16) as (fx1 & R1 & M1 & MG1 & FR1 & _ & MS1 & K1 & A1 & A10). clear P1.
  pose proof (mem_eq M M1 FR1) as EM1. subst M1.
  (* [comment removed for export] *)
  assert (WQ: exists wq, L5.limbs_at RSEGS M (L5.bo_data Q (L5.BO fq nq stq)) wq /\ length wq = nq /\ words_ok wq).
  { pose proof OBQ as (_ & _ & _ & STQ). cbn [L5.bo_fb L5.bo_len L5.bo_st] in STQ.
    destruct stq as [q0 q1|capq Aq]; cbn [L5.bo_data L5.bo_cap L5.bo_st] in DQD |- *.
    - destruct STQ as (_ & V0 & V1 & Hl2 & R0' & R1'). exists (firstn nq [q0; q1]). split.
      { intros i Hi. rewrite length_firstn in Hi. cbn [length] in Hi. unfold nth_w.
        destruct i as [|[|i]]; destruct nq as [|[|[|nq']]]; cbn; try flia; first [exactA V0 | exactA V1]. }
      split. rewrite length_firstn. cbn [length]. flia. destruct nq as [|[|[|nq']]]; cbn; repeat constructor; flia.
    - destruct STQ as (_ & _ & _ & Hle & Hcap & Q8' & Qlo & Qhi & _).
      destruct (L5KS.limbs_of_defined M Aq nq ltac:(eapply L5.defined_sub; [exact DQD | flia | flia]) ltac:(flia) ltac:(flia)) as (wq & WQL & WQR & WQA).
      exists wq. split. exact WQA. split. exact WQL. exact WQR. }
  destruct WQ as (wq & WQA & WQL & WQR).
  destruct (L5REDG.reduce_run fx1 R1 M Q 0x22244 (L5.BO fq nq stq) wq A10 A1 ltac:(split; [flia | reflexivity]) OBQ AQ8 ltac:(flia) QHI
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact DQ | flia | flia] | flia | flia])
              DQD WQA WQL WQR
              ltac:(cbn [L5.bo_st]; intros cap q E; destruct (QD cap q E) as (_ & INQ & _);
                    pose proof (LBhi _ _ _ _ HH _ INQ) as BH; cbn in BH; unfold hl_ceil in *; left; flia))
    as (fx2 & R2 & M2 & MS2 & OB2 & RP2 & B10 & FR2 & MG2).
  cbn [L5.bo_fb L5.bo_st] in OB2.
  set (fq2 := if (rlen wq =? 0)%nat then Z.land fq 253 else fq) in OB2.
  assert (FQ2: 0 <= fq2 < 256 /\ Z.testbit fq2 0 = Z.testbit fq 0).
  { pose proof OBQ as (_ & Ffq & _). cbn [L5.bo_fb] in Ffq. subst fq2. destruct (rlen wq =? 0)%nat. split. apply L5.land_byte_range. lia.
    rewrite Z.land_spec. change (Z.testbit 253 0) with true. apply Bool.andb_true_r. split. exact Ffq. reflexivity. }
  assert (KEEP2: forall i, 0 <= i < 2 ^ 64 -> ~ (Q <= i < Q + 16) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. apply FR2. intros rg [<-|[]]. unfold L5.in_rng. cbn. rewrite BG.unsigned_lit by lia. lia. }
  (* [comment removed for export] *)
  assert (E2: getr R2 (reg 2) = Z_to_bv 64 spd). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact H2. }
  assert (E9: getr R2 (reg 9) = Z_to_bv 64 Q). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by inl. exact H9. }
  assert (E18: getr R2 (reg 18) = Z_to_bv 64 Y). { rewrite (preserved_sregs R1 R2 18 RP2) by inl. rewrite (K1 18%nat) by inl. exact H18. }
  assert (MK2: marksO2 M2 sp Y (Z.land fbY 2) qneg). { eapply marksO2_kept. 4: exact MK. intros i Hi. apply KEEP2; flia. flia. flia. }
  pose proof MK2 as (C272 & C280 & C288 & C256 & C236 & C296).
  pose proof OB2 as (U0 & _ & U8 & _). pose proof (land2_rng fbY (proj1 FBY)) as S2.
  pose proof (d7x2_conc fx2 R2 M2 (Vd 0 0 0 0 0 0 0 0 qneg 0 0 0 fq2 0 0 0 0)) as P2. cbn [Vd VdO] in P2.
  destruct (P2 ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) ltac:(flia) E2 E9 E18 ltac:(flia) A16
               ltac:(eapply L5.writable_grows; [exact MG2|]; apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR0|flia|flia] | flia | flia])
               C272 C280 C288 C256 C236 C296 ltac:(flia) AQ8 ltac:(left; flia) U0 ltac:(flia)
               ltac:(eapply L5.writable_grows; [exact MG2|]; apply (L5C.writable_of_defined RSEGS); [exact DQ | flia | flia]) Hq ltac:(flia) ltac:(flia) ltac:(flia))
    as (fx3 & R3 & M3 & MG3 & _ & FR3 & MS3 & K3 & B1 & B8 & B10' & B11 & B12 & B13 & B19 & U0'). clear P2.
  assert (KEEP3: forall i, 0 <= i < 2 ^ 64 -> ~ (Q <= i < Q + 16) -> M3 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. rewrite (FR3 i Hi) by flia. apply KEEP2; assumption. }
  pose proof (mem_grows_trans _ _ _ MG2 MG3) as MG13.
  set (fq3 := Z.lor (Z.land fq2 253) (2 * qneg mod 2 ^ 64)) in U0'.
  assert (FQ3: 0 <= fq3 < 256 /\ Z.testbit fq3 0 = Z.testbit fq 0).
  { subst fq3. rewrite Z.mod_small by flia. split. apply signfix_rng. flia. flia. rewrite <- (proj2 FQ2). apply signfix_bit0.
    apply Z.testbit_even_0. }
  assert (OBQ3: L5.big_at RSEGS M3 Q (L5.BO fq3 (rlen wq) stq)).
  { eapply (big_at_refb M2 M3). exact OB2. intros i Hi. apply FR3; flia. flia. flia. exact U0'. exact (proj1 FQ3). rewrite (proj2 FQ3). symmetry. exact (proj2 FQ2). }
  (* [comment removed for export] *)
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml.
  eapply msteps_trans. exact MS1. eapply msteps_trans. exact MS2. exact MS3.
  assert (HH3: hi_heap HI LBc crc M3 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LBc crc M M3). exact HIok. exact HH. exact (ly_ro L LY). rewrite IMG; flia. flia.
    intros a Ha. destruct (Z_lt_le_dec a Q) as [X|X]. left; apply KEEP3; flia.
    destruct (Z_lt_le_dec a (Q + 16)) as [X'|X']. right; left; unfold hl_ceil; flia. left; apply KEEP3; flia. exact MG13. }
  (* [comment removed for export] *)
  assert (YL3: exists wR, L5C.obj_limbs RSEGS M3 (L5.BO fbR nR stR) wR).
  { pose proof OBY as (_ & _ & _ & STY). cbn [L5.bo_fb L5.bo_len L5.bo_st] in STY.
    destruct stR as [v0 v1|capR rd]; cbn [L5.bo_data L5.bo_cap L5.bo_st] in DYD |- *.
    - destruct STY as (_ & V0 & V1 & Hl2 & R0' & R1'). exists (firstn nR [v0; v1]). unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st].
      split. rewrite length_firstn. cbn [length]. flia. split. destruct nR as [|[|[|n3]]]; cbn; repeat constructor; flia. reflexivity.
    - destruct STY as (_ & _ & _ & Hle & Hcap & Q8' & Qlo & Qhi & _).
      destruct (L5KS.limbs_of_defined M3 rd nR ltac:(eapply L5.defined_sub; [eapply L5.defined_grows; [exact MG13 | exact DYD] | flia | flia]) ltac:(flia) ltac:(flia)) as (wr & WRL & WRR & WRA).
      exists wr. unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st]. split. exact WRL. split. exact WRR. exact WRA. }
  destruct YL3 as (wR & YL3).
  eapply (stage_U fx3 R3 M3 model LBc TB crc eb fd0 fn0 c1 p1 fnum c2 p2 fden Ad fbR nR stR wR fq3 (rlen wq) stq).
  - rewrite (K3 2%nat) by inl. exact E2.
  - rewrite (K3 3%nat) by inl. rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3.
  - rewrite (K3 4%nat) by inl. rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4.
  - exact B1.
  - exact B11.
  - exact B12.
  - exact B13.
  - exact B8.
  - exact B19.
  - exact MBV.
  - exact HH3.
  - exact ELB.
  - exact CRA.
  - eapply div_saves_kept. 4: exact DS. intros i Hi. apply KEEP3; flia. flia. flia.
  - eapply localsO2_kept. 4: exact LOC. intros i Hi. apply KEEP3; flia. flia. flia.
  - exact IN1. - exact IN2. - exact IN3. - exact LBF.
  - eapply big_at_agree1. 4: exact OBY. intros i Hi. apply KEEP3; flia. flia. flia.
  - exact YL3.
  - exact NR.
  - exact SGN.
  - eapply L5.defined_grows. exact MG13. exact DY.
  - eapply L5.defined_grows. exact MG13. exact DYD.
  - exact INR.
  - exact OBQ3.
  - exact ENDS.
  - intros b Hb. eapply L5.defined_grows. exact MG13. apply DEB. exact Hb.
  - intros i Hi. rewrite KEEP3. apply IMG1. exact Hi. flia. flia.
  - eapply (L5HP.hpres_trans L LB LB sp DIVO2_SCR WN M0 M M3 sp DIVO2_SCR WN). exact HP.
    + eapply (L5HP.hpres_piece L LB sp DIVO2_SCR WN M M3 (fun a => Q <= a < Q + 16)).
      * intros a Ha Hn. apply KEEP3; assumption.
      * intros a KA CH. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. apply (L5HP.outside_in _ _ Q 32 OW). cbn. right; right; left; reflexivity. flia.
      * rewrite DIVO2_SCR_val. eapply L5.defined_grows. exact MG13. exact SCR0.
      * exact MG13.
    + intros a KA; exact KA.
    + intros b Hb; exact Hb.
    + fsclia. + flia. + fsclia. + exact ERRNO. + exact (proj1 SPTOP).
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5DIVO2A.
