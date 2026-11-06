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
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore AsanAcct
     Ub0_code_201fc_21084 Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkGlueUb0 BigLinkDivBaseU L5Defs L5Kn L5Core L5CoreSpecsU L5CoreKitU L5Words L5Hp
     L5ReduceU L5ReduceGU L5DivSpecsU L5DivSpecsOU L5DivPartsU L5DivNPU L5DivOPU L5DivO2PU L5OpModPU L5DivTailU L5DivEarlyU L5OpMod1SU L5OpMod1HU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require BigFactsBase.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Module L5OPMOD1TU.
Import L5CSU. Import L5DSU. Import L5DIVPU. Import L5DIVNPU. Import L5DIVOPU. Import L5DIVO2PU. Import L5OPMODPU. Import L5OM1SU.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.

(* [comment removed for export] *)
Local Notation preserved_sregs := L5DIVEARLYU.preserved_sregs.
Local Notation u64_at_agree1 := L5DIVEARLYU.u64_at_agree1.
Local Notation u8_at_agree1 := L5DIVEARLYU.u8_at_agree1.
Local Notation big_at_agree1 := L5DIVEARLYU.big_at_agree1.
Local Notation defined_agree1 := L5DIVEARLYU.defined_agree1.
Local Notation model_ok_but_vm := L5DIVEARLYU.model_ok_but_vm.
Local Notation mem_eq := L5DIVEARLYU.mem_eq.
Local Notation mod16_mod8 := L5DIVEARLYU.mod16_mod8.
Local Notation div_saves_kept := L5DIVEARLYU.div_saves_kept.
Local Notation outside1 := L5DIVEARLYU.outside1.
Local Notation outside2 := L5DIVEARLYU.outside2.
Local Notation obj_limbs_agree1 := L5DIVEARLYU.obj_limbs_agree1.
Local Notation outside3 := L5DIVEARLYU.outside3.

Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall i, In i cs_all -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
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
Lemma segs_below : segs_below_b RSEGS 0x92000 = true. Proof. vm_compute. reflexivity. Qed.
Lemma writable_defined_hi M a n : L5.writable RSEGS M a n -> L5KU.IMG_HI <= a -> 0 <= n -> a + n <= 2 ^ 64 -> L5.defined M a n.
Proof.
  intros W Hlo Hn Hhi i Hi. specialize (W i 1%nat ltac:(lia) ltac:(cbn; lia)). cbn [store_ok] in W.
  unfold wview in W. destruct (M (Z_to_bv 64 (a + i))) eqn:E. congruence.
  unfold L5KU.IMG_HI in Hlo. rewrite BG.unsigned_lit in W by lia. rewrite (find_segment1_none_above RSEGS 0x92000 (a + i) segs_below) in W by lia. discriminate W.
Qed.
Lemma u32_at_agree1 M M' a v : (forall i, a <= i < a + 4 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= a -> a + 4 <= 2 ^ 64 ->
  L5.u32_at RSEGS M a v -> L5.u32_at RSEGS M' a v.
Proof.
  intros HA Ha H4 Hu. unfold L5.u32_at in *. rewrite <- Hu. apply (L5C.rdn_agree RSEGS M M' 4 a). lia. cbn; lia.
  intros i Hi. apply HA. cbn in Hi. lia.
Qed.
Lemma top_frame_kept M M' S R0 : (forall i, S - 32 <= i < S -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= S - 32 -> S <= 2 ^ 64 ->
  top_frame M S R0 -> top_frame M' S R0.
Proof. intros HA Hlo Hhi (A & B & C & D). repeat split; (eapply u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]). Qed.

Local Ltac inl := apply L5K.in_b; vm_compute; reflexivity.
Local Ltac kreg K i H := etransitivity; [exact (K i ltac:(inl)) | exact H].
Local Ltac uSCR := unfold SCR_OPMOD, DIV_SCR, ASSIGN_SCR, COPY_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, OPDEL_SCR, HEAP_STACK in *.
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         | H : forall _, _ |- _ => lazymatch type of H with _ -> False => fail | _ => clear H end
         end.
Local Ltac prune_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Local Ltac prune_mod := repeat match goal with H : _ mod _ = _ |- _ => clear H end.
Local Ltac flia := prune_impl; prune_disj; prune_mod; lia.
Local Ltac fsclia := prune_impl; prune_disj; prune_mod; uSCR; lia.
Local Ltac exactA H :=
  first [ exact H
        | lazymatch goal with
          | |- L5.u64_at _ _ ?a _ => lazymatch type of H with L5.u64_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u8_at _ _ ?a _ => lazymatch type of H with L5.u8_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.u32_at _ _ ?a _ => lazymatch type of H with L5.u32_at _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.writable _ _ ?a _ => lazymatch type of H with L5.writable _ _ ?b _ => replace a with b by (clear; lia) end
          | |- L5.defined _ ?a _ => lazymatch type of H with L5.defined _ ?b _ => replace a with b by (clear; lia) end
          end; exact H ].

Lemma al8 a k : a mod 16 = 0 -> (a + 8 * k) mod 8 = 0.
Proof. intros H. replace (a + 8 * k) with (a + k * 8) by lia. rewrite Z_mod_plus_full. apply L5DIVEARLYU.mod16_mod8. exact H. Qed.
Lemma hpres_wmono L LB sp scr W W' M M' : (forall a, L5.outside W' a -> L5.outside W a) -> L5C.hpres L LB sp scr W M M' -> L5C.hpres L LB sp scr W' M M'.
Proof.
  intros HW (P & D & C). split. { intros a (Ha & CA & NE & OW). apply P. split. exact Ha. split. exact CA. split. exact NE. apply HW. exact OW. }
  split. exact D. exact C.
Qed.
Lemma lb_remove_head A n LBx : lb_remove A ((A, n) :: LBx) = LBx.
Proof. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
(* [comment removed for export] *)
Definition VP (S X fq qp qc u1 u8 : Z) (j : nat) : Z :=
  match j with 2%nat => S | 33%nat => X | 36%nat => fq | 37%nat => qp | 38%nat => qc | 43%nat => u1 | 44%nat => u8 | _ => 0 end.
(* [comment removed for export] *)
Definition VO (Q X bo fbx c fnum fden nd pd d : Z) (j : nat) : Z :=
  match j with
  | 2%nat => Q | 33%nat => X | 34%nat => bo | 35%nat => Q | 36%nat => X | 37%nat => 1 | 38%nat => fbx
  | 41%nat => fden | 42%nat => nd | 43%nat => pd | 44%nat => fnum | 47%nat => c | 63%nat => d
  | _ => 0
  end.
Lemma SCR_OPMOD_val : SCR_OPMOD = 10240. Proof. reflexivity. Qed.
Lemma DIV_SCR_val : DIV_SCR = 8976. Proof. reflexivity. Qed.
Lemma OPDEL_SCR_val : OPDEL_SCR = 8224. Proof. reflexivity. Qed.
Lemma COPY_SCR_val : COPY_SCR = 8304. Proof. reflexivity. Qed.

Lemma local_obj_kept M M' o f c p : (forall i, o <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  local_obj M o f c p -> local_obj M' o f c p.
Proof.
  intros HA Ho Hhi (U0 & F & D). split. { eapply L5DIVEARLYU.u8_at_agree1. 4: exact U0. intros i Hi; apply HA; lia. lia. lia. } split. exact F.
  intros T. destruct (D T) as (C16 & Hc & C24 & Hp). split. { eapply L5DIVEARLYU.u64_at_agree1. 4: exact C16. intros i Hi; apply HA; lia. lia. lia. }
  split. exact Hc. split. { eapply L5DIVEARLYU.u64_at_agree1. 4: exact C24. intros i Hi; apply HA; lia. lia. lia. } exact Hp.
Qed.
Lemma big_at_reflag M M' o f f' n st :
  L5.big_at RSEGS M o (L5.BO f n st) -> L5.u8_at RSEGS M' o f' -> 0 <= f' < 256 -> Z.testbit f' 0 = Z.testbit f 0 ->
  (forall i, o + 1 <= i < o + 32 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= o -> o + 32 <= 2 ^ 64 ->
  L5.big_at RSEGS M' o (L5.BO f' n st).
Proof.
  intros OB U F T HA Ho Hhi. unfold L5.big_at in OB |- *. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB |- *. destruct OB as (_ & _ & U8 & ST).
  split. exact U. split. exact F. split. { eapply L5DIVEARLYU.u64_at_agree1. 4: exact U8. intros i Hi; apply HA; lia. lia. lia. }
  destruct st as [v0 v1|c q].
  - destruct ST as (T0 & U16 & U24 & R). rewrite T. split. exact T0. split. { eapply L5DIVEARLYU.u64_at_agree1. 4: exact U16. intros i Hi; apply HA; lia. lia. lia. }
    split. { eapply L5DIVEARLYU.u64_at_agree1. 4: exact U24. intros i Hi; apply HA; lia. lia. lia. } exact R.
  - destruct ST as (T0 & U16 & U24 & R). rewrite T. split. exact T0. split. { eapply L5DIVEARLYU.u64_at_agree1. 4: exact U16. intros i Hi; apply HA; lia. lia. lia. }
    split. { eapply L5DIVEARLYU.u64_at_agree1. 4: exact U24. intros i Hi; apply HA; lia. lia. lia. } exact R.
Qed.
Lemma o1_saves_kept M M' S R0 : (forall i, S - 168 <= i < S - 64 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> 0 <= S - 168 -> S <= 2 ^ 64 ->
  o1_saves M S R0 -> o1_saves M' S R0.
Proof.
  intros HA Hlo Hhi (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13). unfold o1_saves.
  repeat split; (eapply L5DIVEARLYU.u64_at_agree1; [intros i Hi; apply HA; lia | lia | lia | eassumption]).
Qed.
Lemma lb_remove_app_skip A pre LBx : (forall b, In b pre -> fst b <> A) -> lb_remove A (pre ++ LBx) = pre ++ lb_remove A LBx.
Proof.
  induction pre as [|[b m] pre IH]; intros H. reflexivity.
  cbn [app lb_remove fst]. destruct (Z.eqb_spec b A) as [E|NE]. exfalso. apply (H (b, m)). left; reflexivity. exact E.
  rewrite IH. reflexivity. intros b' Hb'. apply H. right. exact Hb'.
Qed.
Lemma UNNORM_SCR_val : UNNORM_SCR = 9088. Proof. reflexivity. Qed.
(* [comment removed for export] *)
Definition VT (Q X qneg sgn sd fq fxr c : Z) (j : nat) : Z :=
  match j with
  | 2%nat => Q | 33%nat => X | 35%nat => Q | 36%nat => X | 61%nat => qneg | 62%nat => sgn | 64%nat => sd | 69%nat => fq | 71%nat => fxr | 77%nat => c
  | _ => 0
  end.
Lemma reg_ne0 (i : nat) : (0 < i < 32)%nat -> (reg i : bv 5) <> 0%bv.
Proof. intros Hi E. apply (f_equal bv_unsigned) in E. rewrite Z_to_bv_unsigned, bv_wrap_small in E. change (bv_unsigned (0%bv : bv 5)) with 0 in E. lia. unfold bv_modulus; cbn; lia. Qed.
Lemma reg_ne (i j : nat) : (i < 32)%nat -> (j < 32)%nat -> i <> j -> (reg i : bv 5) <> reg j.
Proof. intros Hi Hj NE E. apply (f_equal bv_unsigned) in E. rewrite !Z_to_bv_unsigned in E. rewrite !bv_wrap_small in E. lia. all: unfold bv_modulus; cbn; lia. Qed.

(* [comment removed for export] *)
Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis KPOS : 0 <= hl_k_per_malloc L.
Hypothesis BPOS : 0 <= hl_b_overhead L.
Hypothesis OPDEL : opdel_sized_spec L HI.
Hypothesis UNNORM : unnorm_spec L HI.
Hypothesis COPYC : copy_spec L HI.

Let IMG := L5DIVEARLYU.IMG L LY.
Let IMGLO := L5DIVEARLYU.IMGLO L LY.
Let ERRNOV := L5DIVEARLYU.ERRNOV L LY.
Let LBdef := @L5DIVEARLYU.LBdef _ L HI HIok.
Let kept_above := L5DIVEARLYU.kept_above L LY.
Let cdef_above := L5DIVEARLYU.cdef_above L LY.
Let cdef_below := L5DIVEARLYU.cdef_below L LY.
Let hi_heap_stackwrite := @L5DIVEARLYU.hi_heap_stackwrite _ L HI LY HIok.
Let divtail := @L5DIVTAILU.divtail_ok _ L HI LY HIok OPDEL.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr crc : credit) (R0 : bvmap 5 word) (M0 : word -> option byte) (S fco bo : Z) (bb : L5.bigobj) (wb : list Z)
          (c sd qneg : Z) (n : nat) (fq : Z) (nq : nat) (stq : L5.bstore) (fx_ : Z) (rst : L5.bstore) (wr : list Z)
          (fnum cnum pnum fden cden pden fn0 fd0 : Z).
Let capb : Z := L5.bo_cap bb.
Let X : Z := S + 64.
Let Q : Z := S - 64.
Let spd : Z := S - 416.
Let BN : list (Z * Z) := if Z.testbit fnum 0 then [(pnum, 8 * cnum)] else [].
Let BD : list (Z * Z) := if Z.testbit fden 0 then [(pden, 8 * cden)] else [].
Let LBc : list (Z * Z) := blocks_ofst stq ++ blocks_ofst rst ++ BN ++ BD ++ LB.
(* [comment removed for export] *)
Hypothesis H2 : getr R (reg 2) = Z_to_bv 64 spd.
Hypothesis H3 : getr R (reg 3) = Z_to_bv 64 GP.
Hypothesis H4 : getr R (reg 4) = Z_to_bv 64 TP.
Hypothesis H8 : getr R (reg 8) = Z_to_bv 64 X.
Hypothesis H9 : getr R (reg 9) = Z_to_bv 64 Q.
Hypothesis H18 : getr R (reg 18) = Z_to_bv 64 X.
(* [comment removed for export] *)
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 OPMOD1_RET.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 S.
Hypothesis G3 : getr R0 3%bv = Z_to_bv 64 GP.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis BO : bo = S + 128.
Hypothesis STK : L5C.stk (hl_sptop L) M0 S SCR_OPMOD.
Hypothesis HS : S + 240 <= hl_sptop L.
Hypothesis WX : L5.writable RSEGS M0 (S + 64) 64.
Hypothesis FCO : L5.u8_at RSEGS M0 (S + 96) fco.
Hypothesis FCOR : 0 <= fco < 256.
Hypothesis BOK : b_ok LB M0 bo bb wb.
Hypothesis DYN3 : L5.bo_dyn bb = true -> (3 <= L5.bo_len bb)%nat.
Hypothesis CR : credit_for L cr OPMOD1_K (opmod1_bytes capb).
Hypothesis CAPB : L5.bo_cap bb <= 268.
Hypothesis MBV : model_but_vm model0 model.
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis HH : hi_heap HI LBc crc M (m_vmmaps model).
Hypothesis CRK : fst cr - 4 * hl_k_per_malloc L <= fst crc.
Hypothesis CRB : snd cr - 4 * (64 + hl_b_overhead L) <= snd crc.
Hypothesis SCR : L5.defined M (S - SCR_OPMOD) SCR_OPMOD.
Hypothesis IMGC : L5.img_clear M 0x10000 0x20000.
(* [comment removed for export] *)
Hypothesis TF : top_frame M S R0.
Hypothesis SAV : o1_saves M S R0.
Hypothesis LO0 : local_obj M (S - 344) fd0 0 0.
Hypothesis F0b : Z.testbit fd0 0 = false.
Hypothesis LO1 : local_obj M (S - 280) fn0 0 0.
Hypothesis F1b : Z.testbit fn0 0 = false.
Hypothesis LO2 : local_obj M (S - 248) fnum cnum pnum.
Hypothesis FRESH2 : Z.testbit fnum 0 = true -> cnum = 8 /\ L5C.fresh_block L LB M pnum 64.
Hypothesis LO3 : local_obj M (S - 200) fden cden pden.
Hypothesis FRESH3 : Z.testbit fden 0 = true -> cden = 8 /\ L5C.fresh_block L (BN ++ LB) M pden 64.
Hypothesis C348 : L5.u32_at RSEGS M (S - 348) c.
Hypothesis Hc : 0 <= c <= 63.
Hypothesis C400 : L5.u64_at RSEGS M (S - 400) 1.
Hypothesis C384 : L5.u64_at RSEGS M (S - 384) 0.
Hypothesis C392 : L5.u64_at RSEGS M (S - 392) qneg.
Hypothesis Hq : 0 <= qneg <= 1.
Hypothesis C408 : L5.u64_at RSEGS M (S - 408) sd.
Hypothesis Hsd : sd = 0 \/ sd = 1.
(* [comment removed for export] *)
Hypothesis OQ : L5.big_at RSEGS M Q (L5.BO fq nq stq).
Hypothesis NQ : (nq <= 3)%nat.
Hypothesis QDYN : forall cq p, stq = L5.BDyn cq p -> cq = 8 /\ L5C.fresh_block L (blocks_ofst rst ++ BN ++ BD ++ LB) M p 64.
(* [comment removed for export] *)
Hypothesis OX : L5.big_at RSEGS M X (L5.BO fx_ (Datatypes.S n) rst).
Hypothesis NEGX : Z.testbit fx_ 1 = false.
Hypothesis OLX : L5C.obj_limbs RSEGS M (L5.BO fx_ (Datatypes.S n) rst) wr.
Hypothesis DX : L5.defined M X 32.
Hypothesis XDYN : forall cx p, rst = L5.BDyn cx p -> cx = 8 /\ L5C.fresh_block L (BN ++ BD ++ LB) M p 64.
(* [comment removed for export] *)
Hypothesis SD1 : sd = 1 -> (exists qx, rst = L5.BDyn 8 qx) /\ (1 <= n <= 5)%nat /\ (exists q0 q1, stq = L5.BInl q0 q1) /\ Z.testbit fnum 0 = true /\ Z.testbit fden 0 = true.
(* [comment removed for export] *)
Hypothesis OBB : L5.big_at RSEGS M bo bb.
Hypothesis OLB : L5C.obj_limbs RSEGS M bb wb.
Hypothesis LENB : (1 <= L5.bo_len bb)%nat.
Hypothesis BBLK : forall cap q, L5.bo_st bb = L5.BDyn cap q -> In (q, 8 * cap) LB.
Hypothesis HP : L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M.
(* [comment removed for export] *)
Hypothesis KN : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) LB' cr',
    opmod1_post L LB cr M0 M' R0 R' S bo fco bb wb capb LB' cr' ->
    model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
    srealizes RSEGS SCFG (cfg R' OPMOD1_RET M' model') K.
(* [comment removed for export] *)
Hypothesis KT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (B0 B1 qx : Z) (crT : credit),
    L5DSOU.assert_throw_at L [(B0, 64); (B1, 64); (pnum, 64); (pden, 64)] ((qx, 64) :: LB) R0 M0 R' M' S ->
    rst = L5.BDyn 8 qx -> sd = 1 ->
    hi_heap HI ((B0, 64) :: (B1, 64) :: (qx, 64) :: (pnum, 64) :: (pden, 64) :: LB) crT M' (m_vmmaps model') -> model_but_vm model0 model' ->
    fst cr - 6 * hl_k_per_malloc L <= fst crT -> snd cr - 6 * (64 + hl_b_overhead L) <= snd crT ->
    L5.big_at RSEGS M' X (L5.BO fx_ (Datatypes.S n) (L5.BDyn 8 qx)) -> L5C.fresh_block L LB M' qx 64 ->
    L5.big_at RSEGS M' bo bb -> L5C.obj_limbs RSEGS M' bb wb ->
    L5.defined M' (S - SCR_OPMOD) SCR_OPMOD ->
    L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M' ->
    srealizes RSEGS SCFG (cfg R' ASSERT_THROW M' model') K.

(* [comment removed for export] *)
Lemma SPW : S mod 16 = 0 /\ 0x7fff7f800000 + 10240 <= S /\ S + 240 <= 2 ^ 47 /\ hl_sptop L - 8388608 + 10240 <= S /\ S + 240 <= hl_sptop L
            /\ 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof using L M0 S fco bb sd n nq stq rst fnum fden STK HS FCOR DYN3 Hsd NQ SD1 LENB. pose proof STK as (A & B & C' & D & _). uSCR. repeat split; try lia. Qed.
Lemma UR01 : U R0 1 = OPMOD1_RET.
Proof using R0 S fco bb sd n nq stq rst fnum fden G1 FCOR DYN3 NQ SD1 LENB. unfold U. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G1. apply BG.unsigned_lit. unfold OPMOD1_RET. lia. Qed.
Lemma CAPB1 : 1 <= capb <= 268.
Proof using M LB S fco bo bb sd n nq stq rst fnum fden FCOR DYN3 CAPB NQ SD1 OBB LENB BBLK. pose proof CAPB as C0. pose proof OBB as OB. unfold capb, L5.bo_cap in C0 |- *. unfold L5.big_at in OB.
  destruct (L5.bo_st bb) as [v0 v1|cq q]. lia. destruct OB as (_ & _ & _ & _ & _ & _ & _ & Hc' & _). lia. Qed.
(* [comment removed for export] *)
Definition Rd : bvmap 5 word := regupd (regupd R0 (reg 1) (Z_to_bv 64 DIV_RET)) (reg 8) (Z_to_bv 64 (S + 64)).
Lemma DER : div_entry_regs S R0 Rd.
Proof using R0 S fco bb sd n nq stq rst fnum fden FCOR DYN3 NQ SD1 LENB.
  unfold Rd. split. { rewrite getr_other by (apply reg_ne; lia). apply getr_same. apply reg_ne0; lia. } split. { apply getr_same. apply reg_ne0; lia. }
  intros i Hi. cbn in Hi. repeat (destruct Hi as [<-|Hi]; [rewrite !getr_other by (apply reg_ne; lia); reflexivity|]). destruct Hi.
Qed.
(* [comment removed for export] *)
Let stage_FIN := @L5OPMOD1HU.stage_FIN _ L HI LY HIok COPYC R0 M0 model0 K LB cr S fco bo bb wb HH0 MOK0 HK0 BO G1 G2 G3 G4 STK HS WX FCO FCOR BOK DYN3 KN.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage_RET (fx5 : FPState) (R5 : bvmap 5 word) (M5 : word -> option byte) (model5 : Model) (cr4 : credit) (fq3 : Z) (bx : L5.bigobj) (wx : list Z) :
  let LBx := blocks_ofst rst ++ LB in
  getr R5 (reg 2) = Z_to_bv 64 Q -> getr R5 (reg 3) = Z_to_bv 64 GP -> getr R5 (reg 4) = Z_to_bv 64 TP ->
  (forall i, In i [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg i) = getr Rd (reg i)) ->
  model_but_vm model0 model5 -> hi_heap HI (blocks_ofst stq ++ LBx) cr4 M5 (m_vmmaps model5) ->
  fst cr - 7 * hl_k_per_malloc L <= fst cr4 -> snd cr - (448 + 7 * hl_b_overhead L) <= snd cr4 ->
  L5.defined M5 (S - SCR_OPMOD) SCR_OPMOD -> top_frame M5 S R0 ->
  L5.u8_at RSEGS M5 Q fq3 -> 0 <= fq3 < 256 ->
  match stq with
  | L5.BInl _ _ => Z.testbit fq3 0 = false
  | L5.BDyn cq p => Z.testbit fq3 0 = true /\ cq = 8 /\ L5.u64_at RSEGS M5 (Q + 16) 8 /\ L5.u64_at RSEGS M5 (Q + 24) p /\ L5C.fresh_block L LBx M5 p 64
  end ->
  L5.big_at RSEGS M5 X bx -> L5C.obj_limbs RSEGS M5 bx wx -> L5.bo_neg bx = false ->
  match rst, L5.bo_st bx with
  | L5.BInl _ _, L5.BInl _ _ => True
  | L5.BDyn _ qx, L5.BDyn cap' q' => cap' = 8 /\ q' = qx /\ L5C.fresh_block L LB M5 qx 64
  | _, _ => False end ->
  L5.big_at RSEGS M5 bo bb -> L5C.obj_limbs RSEGS M5 bb wb ->
  L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M5 ->
  srealizes RSEGS SCFG (cfg R5 DIV_RET M5 model5) K.
Proof.
  cbv zeta. intros E2 E3 E4 ES MBV5 HH5 CRK4 CRB4 SCR5 TF5 Qf Qfr QST OBX5 OLX5 NEGX5 STM OBB5 OLB5 HP5.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV5) as MOK5. pose proof MOK5 as (Mh5 & Ml5 & _).
  pose proof DER as (RD1 & RD8 & RDS). pose proof UR01 as UR01'. pose proof ERRNOV as EV. pose proof IMG as IMG'. rewrite SCR_OPMOD_val in SCR5. pose proof CAPB1 as CB.
  assert (E1: getr R5 (reg 1) = Z_to_bv 64 DIV_RET). { rewrite (ES 1%nat) by inl. exact RD1. }
  assert (E8: getr R5 (reg 8) = Z_to_bv 64 X). { rewrite (ES 8%nat) by inl. exact RD8. }
  pose proof TF5 as (T1 & T8 & T3 & T4).
  assert (W48: L5.writable RSEGS M5 (S - 64) 48). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact SCR5. clear; lia. clear; lia. flia. flia. }
  assert (CROK: credit_ok L cr4 64).
  { pose proof CR as [C1 C2]. unfold credit_for, credit_ok, OPMOD1_K, opmod1_bytes in *. pose proof KPOS. pose proof BPOS. split; clear - C1 C2 CRK4 CRB4 H H0 CB; unfold capb in *; lia. }
  assert (CRA: forall d : bool, credit_after L cr OPMOD1_K (opmod1_bytes capb) (if d then debit L cr4 64 else cr4)).
  { intros d. pose proof CR as [C1 C2]. unfold credit_after, credit_for, debit, OPMOD1_K, opmod1_bytes in *. pose proof KPOS. pose proof BPOS.
    destruct d; cbn [fst snd]; split; clear - C1 C2 CRK4 CRB4 H H0 CB; unfold capb in *; lia. }
  assert (EQB: blocks_ofst (L5.bo_st bx) = blocks_ofst rst).
  { destruct rst as [u0 u1|cx qx]; destruct (L5.bo_st bx) as [v0 v1|cap' q']; try contradiction. reflexivity.
    destruct STM as (-> & -> & _). destruct (XDYN cx qx eq_refl) as [-> _]. reflexivity. }
  assert (XD5: forall cap q, L5.bo_st bx = L5.BDyn cap q -> cap = 8 /\ L5C.fresh_block L LB M5 q 64).
  { intros cap q E. rewrite E in STM. destruct rst as [u0 u1|cx qx]. contradiction. destruct STM as (-> & -> & FB). split. reflexivity. exact FB. }
  assert (HRS5: forall i, In i [9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5 (reg i) = getr R0 (reg i)).
  { intros i Hi. rewrite ES. apply RDS. exact Hi. revert Hi. apply (L5K.incl_b _ _). vm_compute. reflexivity. }
  assert (E2': getr R5 (reg 2) = Z_to_bv 64 (S - 16 - 48)). { rewrite E2. unfold Q. f_equal. clear; lia. }
  assert (A16': aligned (S - 16) 16). { unfold aligned. replace (S - 16) with (S + (-1) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (Qf': L5.u8_at RSEGS M5 (S - 16 - 48) fq3). { replace (S - 16 - 48) with Q by (unfold Q; clear; lia). exact Qf. }
  unfold cfg. destruct stq as [q0 q1|cq p].
  - (* [comment removed for export] *)
    cbn [blocks_ofst app] in HH5.
    pose proof (dopu2i_conc fx5 R5 M5 (VP (S - 16) X fq3 0 0 OPF_BACK (S + 96))) as P. cbn [VP] in P.
    destruct (P ltac:(flia) ltac:(unfold X; flia) ltac:(clear - Qfr; lia) ltac:(unfold OPF_BACK; clear; lia) ltac:(flia)
                E2' E8 ltac:(flia) A16' ltac:(exactA W48) ltac:(exactA T3) ltac:(exactA T4) Qf' ltac:(clear - Qfr; lia) QST)
      as (fx6 & R6 & M6 & _ & FR6 & _ & (MS6 & K6 & B1 & B2 & B8 & B10)). clear P.
    pose proof (mem_eq M5 M6 FR6) as EM. subst M6.
    eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5.
    { eapply msteps_trans. exact MS6. apply (BDU.ret_to fx6 R6 M5 0x224c4 W_224c4 OPF_BACK F_224c4 eq_refl D_224c4 B1). unfold OPF_BACK; clear; lia. reflexivity. }
    apply (stage_FIN fx6 R6 M5 model5 cr4 bx wx).
    + exact B2. + rewrite (K6 3%nat) by inl. exact E3. + rewrite (K6 4%nat) by inl. exact E4. + exact B8. + exact B10.
    + intros i Hi. rewrite K6. apply HRS5. exact Hi. revert Hi. apply (L5K.incl_b _ KS_dopu2i). vm_compute. reflexivity.
    + exact MBV5. + rewrite EQB. exact HH5.
    + exact (CRA (L5.bo_dyn bx)). + intros _. exact CROK. + exact XD5.
    + rewrite SCR_OPMOD_val. exact SCR5. + exact T1. + exact T8.
    + exact OBX5. + exact OLX5. + exact NEGX5. + exact OBB5. + exact OLB5. + exact LENB. + exact HP5.
  - (* [comment removed for export] *)
    destruct QST as (Qb1 & -> & C16 & C24 & FBq). cbn [blocks_ofst app] in HH5. change (8 * 8) with 64 in HH5.
    pose proof (L5C.fresh_block_bounds _ _ _ _ _ FBq) as (Plo & Pimg & _ & _ & Phi). unfold hl_ceil in Phi.
    pose proof (dopu2d_conc fx5 R5 M5 (VP (S - 16) X fq3 p 8 OPF_BACK (S + 96))) as P. cbn [VP] in P.
    destruct (P ltac:(flia) ltac:(unfold X; flia) ltac:(clear - Qfr; lia) ltac:(clear - Plo Phi SPT; lia) ltac:(clear; lia) ltac:(unfold OPF_BACK; clear; lia) ltac:(flia)
                E2' E8 ltac:(flia) A16' ltac:(exactA W48) ltac:(exactA T3) ltac:(exactA T4) Qf' ltac:(clear - Qfr; lia) Qb1
                ltac:(replace (S - 16 - 24) with (Q + 24) by (unfold Q; clear; lia); exact C24) ltac:(clear - Plo Phi SPT; lia)
                ltac:(replace (S - 16 - 32) with (Q + 16) by (unfold Q; clear; lia); exact C16) ltac:(clear; lia))
      as (fx6 & R6 & M6 & _ & FR6 & _ & (MS6 & K6 & B1 & B10 & B11)). clear P.
    pose proof (mem_eq M5 M6 FR6) as EM. subst M6.
    eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5. exact MS6.
    eapply (OPDEL fx6 R6 M5 model5 K ((p, 64) :: blocks_ofst rst ++ LB) cr4 p 64 Q 0x224b4 HH5 MOK5 HK0).
    + left. reflexivity.
    + exact B10.
    + exact B1.
    + split. clear; lia. reflexivity.
    + kreg K6 2%nat E2.
    + kreg K6 4%nat E4.
    + split. { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
      split. unfold Q; fsclia. split. unfold Q; flia. split. exact SPT. unfold Q. rewrite OPDEL_SCR_val. eapply L5.defined_sub. exact SCR5. clear; lia. clear; lia.
    + (* [comment removed for export] *)
      intros fx7 R7 M7 model7 RP7 HP7 MBV7 HH7. rewrite lb_remove_head in HP7, HH7.
      pose proof (model_ok_but_vm _ _ MOK5 MBV7) as MOK7. pose proof MOK7 as (Mh7 & Ml7 & _).
      assert (KA7: forall a, Q <= a < 2 ^ 64 -> M7 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
      { intros a Ha. apply (kept_above M5 M7 (blocks_ofst rst ++ LB) Q OPDEL_SCR _ a HP7). unfold Q; fsclia. rewrite OPDEL_SCR_val; clear; lia. flia. exact Ha. apply L5C.outside_nil. }
      assert (KB7: forall A n' a, In (A, n') (blocks_ofst rst ++ LB) -> A <= a < A + n' -> M7 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
      { intros A n' a Hin Ha. pose proof (LBdef _ _ _ _ HH7 A n' Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP7). eapply L5C.kept_block. exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; lia. rewrite EV; clear - Aimg Ha; lia. apply L5C.outside_nil. }
      assert (D7: L5.defined M7 (S - 10240) 10240).
      { replace 10240 with (1952 + (8224 + 64)) at 2 by (clear; lia). apply L5C.defined_app. 3: clear; lia.
        { eapply (cdef_below M5 M7 _ Q OPDEL_SCR _ (S - 10240) 1952 HP7). flia. unfold Q; rewrite OPDEL_SCR_val; clear; lia. rewrite OPDEL_SCR_val; clear; lia. flia. unfold Q; flia.
          eapply L5.defined_sub. exact SCR5. clear; lia. clear; lia. }
        apply L5C.defined_app. 3: clear; lia.
        { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP7) as D. unfold Q in D. rewrite OPDEL_SCR_val in D. exactA D. }
        eapply (cdef_above M5 M7 _ Q OPDEL_SCR _ _ 64 HP7). unfold Q; rewrite OPDEL_SCR_val; fsclia. rewrite OPDEL_SCR_val; clear; lia. flia. unfold Q; clear; lia. flia.
        eapply L5.defined_sub. exact SCR5. clear; lia. clear; lia. }
      assert (W48': L5.writable RSEGS M7 (S - 16 - 48) 48). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_sub. exact D7. clear; lia. clear; lia. flia. flia. }
      pose proof (dopu3_conc fx7 R7 M7 (VP (S - 16) X 0 0 0 OPF_BACK (S + 96))) as P. cbn [VP] in P.
      destruct (P ltac:(flia) ltac:(unfold X; flia) ltac:(unfold OPF_BACK; clear; lia) ltac:(flia)
                  ltac:(rewrite (preserved_sregs R6 R7 2 RP7) by inl; rewrite (K6 2%nat) by inl; exact E2')
                  ltac:(rewrite (preserved_sregs R6 R7 8 RP7) by inl; rewrite (K6 8%nat) by inl; exact E8)
                  ltac:(flia) A16' W48'
                  ltac:(eapply u64_at_agree1; [intros i Hi; apply KA7; unfold Q; flia | flia | flia | exactA T3])
                  ltac:(eapply u64_at_agree1; [intros i Hi; apply KA7; unfold Q; flia | flia | flia | exactA T4]))
        as (fx8 & R8 & M8 & _ & FR8 & _ & (MS8 & K8 & B1' & B2' & B8' & B10')). clear P.
      pose proof (mem_eq M7 M8 FR8) as EM. subst M8.
      eapply (L5.cps_of_msteps RSEGS). exact Mh7. exact Ml7.
      { eapply msteps_trans. exact MS8. apply (BDU.ret_to fx8 R8 M7 0x224c4 W_224c4 OPF_BACK F_224c4 eq_refl D_224c4 B1'). unfold OPF_BACK; clear; lia. reflexivity. }
      apply (stage_FIN fx8 R8 M7 model7 cr4 bx wx).
      * exact B2'.
      * rewrite (K8 3%nat) by inl. rewrite (preserved_sregs R6 R7 3 RP7) by inl. rewrite (K6 3%nat) by inl. exact E3.
      * rewrite (K8 4%nat) by inl. rewrite (preserved_sregs R6 R7 4 RP7) by inl. rewrite (K6 4%nat) by inl. exact E4.
      * exact B8'. * exact B10'.
      * intros i Hi. rewrite K8. rewrite (preserved_sregs R6 R7 i RP7). rewrite K6. apply HRS5. exact Hi.
        revert Hi; apply (L5K.incl_b _ KS_dopu2d); vm_compute; reflexivity. revert Hi; apply (L5K.incl_b _ cs_all); vm_compute; reflexivity. revert Hi; apply (L5K.incl_b _ KS_dopu3); vm_compute; reflexivity.
      * exact (L5C.model_but_vm_trans _ _ _ MBV5 MBV7).
      * rewrite EQB. exact HH7.
      * exact (CRA (L5.bo_dyn bx)). * intros _. exact CROK.
      * intros cap q E. destruct (XD5 cap q E) as [-> (BR & BA & _)]. split. reflexivity. split. exact BR. split. exact BA.
        pose proof (LBdef _ _ _ _ HH7 q 64 ltac:(rewrite <- EQB, E; cbn; left; reflexivity)) as (D' & _). exact D'.
      * rewrite SCR_OPMOD_val. exact D7.
      * eapply u64_at_agree1. 4: exact T1. intros i Hi; apply KA7; unfold Q; flia. flia. flia.
      * eapply u64_at_agree1. 4: exact T8. intros i Hi; apply KA7; unfold Q; flia. flia. flia.
      * eapply big_at_agree1. 4: exact OBX5. intros i Hi; apply KA7; unfold Q, X in *; flia. unfold X; flia. unfold X; flia.
      * eapply obj_limbs_agree1. 3: exact OLX5.
        -- intros cap q E i Hi. destruct rst as [u0 u1|cx qx]; rewrite E in STM. contradiction. destruct STM as (-> & -> & _).
           pose proof OLX5 as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln in Hi.
           pose proof OBX5 as OB'. unfold L5.big_at in OB'. rewrite E in OB'. destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & _). cbn [L5.bo_len] in Hlc.
           apply (KB7 qx 64 i). cbn. left. destruct (XDYN cx qx eq_refl) as [-> _]. reflexivity. clear - Hi Hlc; lia.
        -- intros cap q E. destruct rst as [u0 u1|cx qx]; rewrite E in STM. contradiction. destruct STM as (-> & -> & FB).
           pose proof OLX5 as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln.
           pose proof OBX5 as OB'. unfold L5.big_at in OB'. rewrite E in OB'. destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & _). cbn [L5.bo_len] in Hlc.
           pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo' & _ & _ & _ & Phi'). unfold hl_ceil in Phi'. clear - Hlc Plo' Phi' SPT; lia.
      * exact NEGX5.
      * eapply big_at_agree1. 4: exact OBB5. intros i Hi; apply KA7; generalize BO; unfold Q; flia. generalize BO; flia. generalize BO; flia.
      * eapply obj_limbs_agree1. 3: exact OLB5.
        -- intros cap q E i Hi. pose proof OLB5 as (Ln & _ & _). pose proof OBB5 as OB'. unfold L5.big_at in OB'. rewrite E in OB'.
           destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & _). apply (KB7 q (8 * cap) i). apply in_app_iff. right. exact (BBLK cap q E). rewrite Ln in Hi; clear - Hi Hlc; lia.
        -- intros cap q E. pose proof OLB5 as (Ln & _ & _). pose proof OBB5 as OB'. unfold L5.big_at in OB'. rewrite E in OB'.
           destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
      * exact LENB.
      * eapply (L5HP.hpres_trans L LB (blocks_ofst rst ++ LB) S SCR_OPMOD [(X, 32)] M0 M5 M7 Q OPDEL_SCR []). exact HP5. exact HP7.
        -- intros a KA. eapply L5HP.kept_mono. exact KA. intros b Hb; apply in_app_iff; right; exact Hb. unfold Q; fsclia. unfold Q; flia. intros _; apply L5C.outside_nil.
        -- intros b Hb; apply in_app_iff; right; exact Hb. -- unfold hl_ceil; fsclia. -- flia. -- rewrite SCR_OPMOD_val; clear; lia. -- rewrite EV; clear; lia. -- flia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem o1_tail : srealizes RSEGS SCFG (cfg R LEXIT M model) K.
Proof.
  pose proof SPW as (A16 & SLO & SHI & SLO' & SHI' & SPT). pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof ERRNOV as EV. pose proof IMG as IMG'. pose proof SCR as SCR'. rewrite SCR_OPMOD_val in SCR'. pose proof CAPB1 as CB.
  pose proof DER as DER'. pose proof (o1_saves_div_saves M S R0 Rd ltac:(flia) DER' SAV) as DS. fold Q in DS |- *.
  pose proof OQ as OQ'. unfold L5.big_at in OQ'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OQ'. destruct OQ' as (Qf & Qfr & Ql & QST).
  pose proof OX as OX'. unfold L5.big_at in OX'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OX'. destruct OX' as (Xf & Xfr & Xl & XST).
  assert (AQ16: Q mod 16 = 0). { unfold Q. replace (S - 64) with (S + (-4) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  assert (AX8: X mod 8 = 0). { unfold X. rewrite <- Zplus_mod_idemp_l, (mod16_mod8 _ A16). reflexivity. }
  assert (E2: getr R (reg 2) = Z_to_bv 64 (Q - 352)). { replace (Q - 352) with spd by (unfold Q, spd; clear; lia). exact H2. }
  assert (CEIL: hl_ceil L <= S - SCR_OPMOD). { unfold hl_ceil. rewrite SCR_OPMOD_val. clear - SLO'. lia. }
  assert (LBceil: forall b, In b LB -> fst b + snd b <= hl_ceil L).
  { intros [A n'] Hb. pose proof (LBdef _ _ _ _ HH A n' ltac:(unfold LBc; rewrite !in_app_iff; right; right; right; right; exact Hb)) as (_ & _ & Ahi & _). unfold hl_ceil. cbn. exact Ahi. }
  (* [comment removed for export] *)
  assert (QB: forall cq p, stq = L5.BDyn cq p -> cq = 8 /\ 4096 <= p /\ p + 64 <= hl_sptop L - 8388608 /\ L5.defined M p 64 /\ In (p, 64) LBc).
  { intros cq p E. destruct (QDYN cq p E) as [-> FB]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi.
    destruct FB as (_ & _ & FD). split. reflexivity. split. exact Plo. split. exact Phi. split. exact FD. unfold LBc. subst stq. cbn. left. reflexivity. }
  assert (XB: forall cx p, rst = L5.BDyn cx p -> cx = 8 /\ 4096 <= p /\ p + 64 <= hl_sptop L - 8388608 /\ L5.defined M p 64 /\ In (p, 64) LBc).
  { intros cx p E. destruct (XDYN cx p E) as [-> FB]. pose proof (L5C.fresh_block_bounds _ _ _ _ _ FB) as (Plo & _ & _ & _ & Phi). unfold hl_ceil in Phi.
    destruct FB as (_ & _ & FD). split. reflexivity. split. exact Plo. split. exact Phi. split. exact FD. unfold LBc. subst rst. apply in_app_iff. right. cbn. left. reflexivity. }
  (* [comment removed for export] *)
  pose proof (d5ux1_conc fx R M (VT Q X qneg 0 sd fq fx_ c)) as P. cbn [VT] in P.
  destruct (P ltac:(unfold Q; flia) ltac:(unfold Q; flia) E2 H9 ltac:(unfold Q; flia) AQ16) as (fx1 & R1 & M1 & _ & FR1 & _ & (MS1 & K1 & A1 & A10)). clear P.
  pose proof (mem_eq M M1 FR1) as EM1. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  assert (QD: L5.defined M (L5.bo_data Q (L5.BO fq nq stq)) (8 * L5.bo_cap (L5.BO fq nq stq)) /\ (Z.of_nat nq <= L5.bo_cap (L5.BO fq nq stq))
              /\ 0 <= L5.bo_data Q (L5.BO fq nq stq) /\ L5.bo_data Q (L5.BO fq nq stq) + 8 * L5.bo_cap (L5.BO fq nq stq) <= 2 ^ 64).
  { unfold L5.bo_data, L5.bo_cap. cbn [L5.bo_st]. destruct stq as [q0 q1|cq p].
    - destruct QST as (_ & _ & _ & Hl & _). split. eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. split. clear - Hl; lia. unfold Q; flia.
    - destruct (QB cq p eq_refl) as (-> & Plo & Phi & PD & _). split. exact PD. split. clear - NQ; lia. clear - Plo Phi SPT; lia. }
  destruct QD as (QD & QLC & QDlo & QDhi).
  destruct (L5KU.limbs_of_defined M (L5.bo_data Q (L5.BO fq nq stq)) nq ltac:(eapply L5.defined_sub; [exact QD | clear; lia | clear - QLC; lia]) QDlo ltac:(clear - QLC QDhi; lia))
    as (wq & WQL & WQR & WQA).
  destruct (L5REDGU.reduce_run fx1 R1 M Q 0x229e8 (L5.BO fq nq stq) wq A10 A1 ltac:(split; [clear; lia | reflexivity]) OQ ltac:(apply mod16_mod8; exact AQ16) ltac:(unfold Q; flia) ltac:(unfold Q; flia)
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_sub; [exact SCR' | unfold Q; clear; lia | unfold Q; clear; lia] | unfold Q; flia | unfold Q; flia])
              QD WQA WQL WQR
              ltac:(cbn [L5.bo_st]; intros cap q E; destruct (QB cap q E) as (-> & _ & Phi & _); left; unfold Q; clear - Phi SLO'; lia))
    as (fx2 & R2 & M2 & MS2 & OQ2 & RP2 & C10 & FR2 & MG2).
  cbn [L5.bo_fb L5.bo_st] in OQ2. set (fq2 := if (L5W.rlen wq =? 0)%nat then Z.land fq 253 else fq) in OQ2.
  assert (FQ2: 0 <= fq2 < 256 /\ Z.testbit fq2 0 = Z.testbit fq 0).
  { subst fq2. destruct (L5W.rlen wq =? 0)%nat. split. apply L5.land_byte_range. clear; lia. rewrite Z.land_spec. apply Bool.andb_true_r. split. exact Qfr. reflexivity. }
  assert (FR2Z: forall i, 0 <= i < 2 ^ 64 -> ~ (Q <= i < Q + 16) -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. apply FR2. apply outside1. rewrite BG.unsigned_lit by exact Hi. exact Hn. }
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS2.
  pose proof OQ2 as OQ2'. unfold L5.big_at in OQ2'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OQ2'. destruct OQ2' as (Qf2 & _ & Ql2 & QST2).
  (* [comment removed for export] *)
  assert (KF2: forall i, S - 416 <= i < S - 64 -> M2 (Z_to_bv 64 i) = M (Z_to_bv 64 i)). { intros i Hi. apply FR2Z. flia. unfold Q; clear - Hi; lia. }
  assert (E2': getr R2 (reg 2) = Z_to_bv 64 (Q - 352)). { rewrite (preserved_sregs R1 R2 2 RP2) by inl. rewrite (K1 2%nat) by inl. exact E2. }
  assert (E8': getr R2 (reg 8) = Z_to_bv 64 X). { rewrite (preserved_sregs R1 R2 8 RP2) by inl. rewrite (K1 8%nat) by inl. exact H8. }
  assert (E9': getr R2 (reg 9) = Z_to_bv 64 Q). { rewrite (preserved_sregs R1 R2 9 RP2) by inl. rewrite (K1 9%nat) by inl. exact H9. }
  assert (E18': getr R2 (reg 18) = Z_to_bv 64 X). { rewrite (preserved_sregs R1 R2 18 RP2) by inl. rewrite (K1 18%nat) by inl. exact H18. }
  assert (WF2: L5.writable RSEGS M2 (Q - 352) 352).
  { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG2. eapply L5.defined_sub. exact SCR'. unfold Q; clear; lia. unfold Q; clear; lia. unfold Q; flia. unfold Q; flia. }
  pose proof (d7ux2_conc fx2 R2 M2 (VT Q X qneg 0 sd fq2 fx_ c)) as P. cbn [VT] in P.
  destruct (P ltac:(unfold Q; flia) ltac:(unfold X; flia) ltac:(unfold Q; flia) ltac:(unfold X; flia) ltac:(clear - Hq; lia) ltac:(clear; lia) ltac:(clear - Hsd; lia) ltac:(clear - FQ2; lia) ltac:(clear - Hc; lia)
              E2' E8' E9' E18' ltac:(unfold Q; flia) AQ16 WF2
              ltac:(eapply u64_at_agree1; [intros i Hi; apply KF2; unfold Q in Hi; clear - Hi; lia | unfold Q; flia | unfold Q; flia | unfold Q; exactA C384])
              ltac:(eapply u64_at_agree1; [intros i Hi; apply KF2; unfold Q in Hi; clear - Hi; lia | unfold Q; flia | unfold Q; flia | unfold Q; exactA C392])
              ltac:(eapply u64_at_agree1; [intros i Hi; apply KF2; unfold Q in Hi; clear - Hi; lia | unfold Q; flia | unfold Q; flia | unfold Q; exactA C400])
              ltac:(eapply u32_at_agree1; [intros i Hi; apply KF2; unfold Q in Hi; clear - Hi; lia | unfold Q; flia | unfold Q; flia | unfold Q; exactA C348])
              ltac:(eapply u64_at_agree1; [intros i Hi; apply KF2; unfold Q in Hi; clear - Hi; lia | unfold Q; flia | unfold Q; flia | unfold Q; exactA C408])
              ltac:(unfold Q; flia) ltac:(apply mod16_mod8; exact AQ16) ltac:(left; clear; lia) Qf2 ltac:(clear - FQ2; lia)
              ltac:(apply (L5C.writable_of_defined RSEGS); [eapply L5.defined_grows; [exact MG2|]; eapply L5.defined_sub; [exact SCR' | unfold Q; clear; lia | unfold Q; clear; lia] | unfold Q; flia | unfold Q; flia])
              Hq ltac:(clear; lia) Hc ltac:(clear - Hsd; lia))
    as (fx3 & R3 & M3 & MG3 & _ & FR3 & (MS3 & K3 & B1 & B10 & B11 & B12 & B13 & B19 & CQ3)). clear P.
  rewrite Z.mod_small in CQ3 by (clear - Hq; lia).
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS3.
  pose proof (mem_grows_trans _ _ _ MG2 MG3) as MG23.
  assert (KA3: forall i, 0 <= i < 2 ^ 64 -> ~ (Q <= i < Q + 16) -> M3 (Z_to_bv 64 i) = M (Z_to_bv 64 i)).
  { intros i Hi Hn. rewrite FR3. apply FR2Z. exact Hi. exact Hn. exact Hi. clear - Hn; lia. }
  assert (HH3: hi_heap HI LBc crc M3 (m_vmmaps model)).
  { eapply (hi_heap_stackwrite LBc crc M M3 _ Q (Q + 16)). exact HH. exact KA3. unfold Q; flia. unfold Q; flia. flia. exact MG23. }
  assert (HP3: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M3).
  { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M M3 S SCR_OPMOD [(X, 32)]). exact HP.
    - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M M3 (fun a => Q <= a < Q + 16)). exact KA3.
      { intros a KA' C'. apply (L5HP.kept_not_in_scratch _ _ _ _ _ _ KA' LBceil CEIL ltac:(unfold hl_ceil; rewrite IMG'; clear - SPT; lia)). rewrite SCR_OPMOD_val. unfold Q in C'. clear - C'; lia. }
      rewrite SCR_OPMOD_val. eapply L5.defined_grows. exact MG23. exact SCR'. exact MG23.
    - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - flia. }
  (* [comment removed for export] *)
  eapply (UNNORM fx3 R3 M3 model K LBc crc X c sd spd 0x22a20 (L5.BO fx_ (Datatypes.S n) rst) wr HH3 MOK HK0 B11 B12 Hc B13 Hsd B1).
  - split. clear; lia. reflexivity.
  - etransitivity. exact (K3 2%nat ltac:(inl)). rewrite E2'. unfold Q, spd. f_equal. clear; lia.
  - etransitivity. exact (K3 3%nat ltac:(inl)). rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3.
  - etransitivity. exact (K3 4%nat ltac:(inl)). rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4.
  - split. { unfold spd. replace (S - 416) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
    split. unfold spd; rewrite UNNORM_SCR_val; fsclia. split. unfold spd; flia. split. exact SPT. unfold spd. rewrite UNNORM_SCR_val.
    eapply L5.defined_grows. exact MG23. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia.
  - intros i Hi. rewrite KA3. apply IMGC. exact Hi. clear - Hi; lia. unfold Q; clear - Hi SLO; lia.
  - eapply big_at_agree1. 4: exact OX. intros i Hi; apply KA3; unfold Q, X in *; flia. unfold X; flia. unfold X; flia.
  - eapply obj_limbs_agree1. 3: exact OLX.
    + cbn [L5.bo_st L5.bo_len]. intros cx p E i Hi. destruct (XB cx p E) as (-> & Plo & Phi & _). pose proof OLX as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln in Hi.
      rewrite E in XST. destruct XST as (_ & _ & _ & Hlc & _). apply KA3. clear - Hi Plo Phi Hlc SPT; lia. unfold Q; clear - Hi Phi Hlc SLO'; lia.
    + cbn [L5.bo_st L5.bo_len]. intros cx p E. destruct (XB cx p E) as (-> & Plo & Phi & _). pose proof OLX as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln.
      rewrite E in XST. destruct XST as (_ & _ & _ & Hlc & _). clear - Plo Phi Hlc SPT; lia.
  - cbn [L5.bo_len]. destruct rst as [v0 v1|cx p]. destruct XST as (_ & _ & _ & Hl & _); clear - Hl; lia. destruct (XB cx p eq_refl) as (-> & _). destruct XST as (_ & _ & _ & Hlc & _); clear - Hlc; lia.
  - exact NEGX.
  - exact AX8. - unfold spd, X; clear; lia. - unfold X; flia.
  - eapply L5.defined_grows. exact MG23. exact DX.
  - cbn [L5.bo_st]. intros cap q E. destruct (XB cap q E) as (-> & _ & _ & PD & INB). split. exact INB. eapply L5.defined_grows. exact MG23. exact PD.
  - intros SD. destruct (SD1 SD) as ((qx & ->) & Hn & _). exists qx. split. reflexivity. cbn [L5.bo_len]. clear - Hn; lia.
  - intros SD. pose proof CR as [C1 C2]. unfold credit_for, OPMOD1_K, opmod1_bytes, DIVN_K, DIVN_BYTES in *. pose proof KPOS. pose proof BPOS. split; clear - C1 C2 CRK CRB H H0 CB; lia.
  - (* [comment removed for export] *)
    intros fx4 R4 M4 model4 cr4 UP MBV4 HH4.
    destruct UP as (RP4 & (fb' & n' & st' & w' & OX4 & OL4 & NEG4 & STM4) & CRA4 & HP4). cbn [L5.bo_st L5.bo_data L5.bo_cap] in STM4, HP4.
    pose proof (model_ok_but_vm _ _ MOK MBV4) as MOK4. pose proof MOK4 as (Mh4 & Ml4 & _).
    pose proof OX4 as OX4'. unfold L5.big_at in OX4'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OX4'. destruct OX4' as (Xf4 & F4 & _).
    (* [comment removed for export] *)
    assert (KA4: forall a, spd <= a < 2 ^ 64 -> ~ (X <= a < X + 32) -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros a Ha NX. apply (kept_above M3 M4 LBc spd UNNORM_SCR _ a HP4). unfold spd; rewrite UNNORM_SCR_val; fsclia. rewrite UNNORM_SCR_val; clear; lia. flia. exact Ha.
      apply outside2. exact NX. destruct rst as [v0 v1|cx p]; cbn [L5.bo_data L5.bo_cap L5.bo_st]. unfold X in NX |- *; clear - NX; lia.
      destruct (XB cx p eq_refl) as (-> & Plo & Phi & _). unfold spd in Ha. clear - Ha Phi SLO'; lia. }
    assert (KB4: forall A n0 a, In (A, n0) LB -> A <= a < A + n0 -> M4 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros A n0 a Hin Ha. assert (INC: In (A, n0) LBc). { unfold LBc. rewrite !in_app_iff. right; right; right; right; exact Hin. }
      pose proof (LBdef _ _ _ _ HH A n0 INC) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO in Aimg.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP4). eapply L5C.kept_block. exact INC. exact Ha. clear - Alo; lia. clear - Ahi SPT; lia. rewrite EV; clear - Aimg Ha; lia.
      apply outside2. unfold X; clear - Ha Ahi SLO'; lia. destruct rst as [v0 v1|cx p]; cbn [L5.bo_data L5.bo_cap L5.bo_st]. unfold X; clear - Ha Ahi SLO'; lia.
      destruct (XDYN cx p eq_refl) as [-> FB]. destruct FB as (_ & BA & _). pose proof (BA (A, n0) ltac:(rewrite !in_app_iff; right; right; exact Hin)) as AP. cbn in AP. clear - AP Ha. lia. }
    assert (D4: L5.defined M4 (S - 10240) 10240).
    { replace 10240 with (736 + (9088 + 416)) at 2 by (clear; lia). apply L5C.defined_app. 3: clear; lia.
      { eapply (cdef_below M3 M4 LBc spd UNNORM_SCR _ (S - 10240) 736 HP4). flia. unfold spd; rewrite UNNORM_SCR_val; clear; lia. rewrite UNNORM_SCR_val; clear; lia. flia. unfold spd; flia.
        eapply L5.defined_grows. exact MG23. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia. }
      apply L5C.defined_app. 3: clear; lia.
      { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP4) as D. unfold spd in D. rewrite UNNORM_SCR_val in D. exactA D. }
      eapply (cdef_above M3 M4 LBc spd UNNORM_SCR _ _ 416 HP4). unfold spd; rewrite UNNORM_SCR_val; fsclia. rewrite UNNORM_SCR_val; clear; lia. flia. unfold spd; clear; lia. flia.
      eapply L5.defined_grows. exact MG23. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia. }
    assert (DX4: L5.defined M4 X 32).
    { eapply (cdef_above M3 M4 LBc spd UNNORM_SCR _ X 32 HP4). unfold spd; rewrite UNNORM_SCR_val; fsclia. rewrite UNNORM_SCR_val; clear; lia. flia. unfold spd, X; clear; lia. unfold X; flia.
      eapply L5.defined_grows. exact MG23. exact DX. }
    assert (F2: getr R4 (reg 2) = Z_to_bv 64 (Q - 352)). { rewrite (preserved_sregs R3 R4 2 RP4) by inl. rewrite (K3 2%nat) by inl. exact E2'. }
    assert (F8: getr R4 (reg 8) = Z_to_bv 64 X). { rewrite (preserved_sregs R3 R4 8 RP4) by inl. rewrite (K3 8%nat) by inl. exact E8'. }
    assert (F19: getr R4 (reg 19) = Z_to_bv 64 0). { rewrite (preserved_sregs R3 R4 19 RP4) by inl. exact B19. }
    (* [comment removed for export] *)
    pose proof (d7ux3_conc fx4 R4 M4 (VT Q X qneg 0 sd fq2 fb' c)) as P. cbn [VT] in P.
    destruct (P ltac:(unfold Q; flia) ltac:(unfold X; flia) ltac:(clear; lia) ltac:(clear - F4; lia) F2 F8 F19 ltac:(unfold Q; flia) AQ16 ltac:(unfold X; flia) AX8
                ltac:(left; unfold Q, X; clear; lia) Xf4 ltac:(clear - F4; lia) ltac:(apply (L5C.writable_of_defined RSEGS); [exact DX4 | unfold X; flia | unfold X; flia]) ltac:(clear; lia))
      as (fx5 & R5 & M5 & MG5 & _ & FR5 & (MS5 & K5 & _ & CX5)). clear P.
    rewrite Z.lor_0_r in CX5.
    unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh4. exact Ml4. exact MS5.
    assert (KX5: forall a, 0 <= a < 2 ^ 64 -> a <> X -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)). { intros a Ha Hn. apply FR5. exact Ha. clear - Hn; lia. }
    assert (HH5: hi_heap HI LBc cr4 M5 (m_vmmaps model4)).
    { eapply (hi_heap_stackwrite LBc cr4 M4 M5 _ X (X + 1)). exact HH4. { intros i Hi Hn. apply KX5. exact Hi. clear - Hn; lia. } unfold X; flia. unfold X; flia. flia. exact MG5. }
    assert (D5: L5.defined M5 (S - 10240) 10240). { eapply L5.defined_grows. exact MG5. exact D4. }
    (* [comment removed for export] *)
    assert (KEEP: forall a, S - 416 <= a < S - 64 -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite KX5. rewrite KA4. rewrite KA3. reflexivity. flia. unfold Q; clear - Ha; lia. unfold spd; flia. unfold X; clear - Ha; lia. flia. unfold X; clear - Ha; lia. }
    assert (OX5: L5.big_at RSEGS M5 X (L5.BO (Z.land fb' 253) n' st')).
    { eapply big_at_reflag. exact OX4. exact CX5. apply L5.land_byte_range; clear; lia. rewrite Z.land_spec. apply Bool.andb_true_r.
      intros i Hi; apply KX5; unfold X in *; flia. unfold X; flia. unfold X; flia. }
    (* [comment removed for export] *)
    assert (PNE: Z.testbit fnum 0 = true -> forall b, In b (blocks_ofst stq ++ blocks_ofst rst) -> fst b <> pnum).
    { intros Tn [b m] Hb. rewrite in_app_iff in Hb. destruct Hb as [Hb|Hb].
      - destruct stq as [u0 u1|cq p]. destruct Hb. cbn in Hb. destruct Hb as [Hb|[]]. injection Hb. intros <- <-.
        destruct (QDYN cq p eq_refl) as [-> FB]. destruct FB as (_ & BA & _).
        pose proof (BA (pnum, 8 * cnum) ltac:(rewrite !in_app_iff; right; left; unfold BN; rewrite Tn; left; reflexivity)) as AP. cbn in AP |- *.
        destruct (FRESH2 Tn) as [-> _]. clear - AP. lia.
      - destruct rst as [u0 u1|cx p]. destruct Hb. cbn in Hb. destruct Hb as [Hb|[]]. injection Hb. intros <- <-.
        destruct (XDYN cx p eq_refl) as [-> FB]. destruct FB as (_ & BA & _).
        pose proof (BA (pnum, 8 * cnum) ltac:(rewrite !in_app_iff; left; unfold BN; rewrite Tn; left; reflexivity)) as AP. cbn in AP |- *.
        destruct (FRESH2 Tn) as [-> _]. clear - AP. lia. }
    assert (PDE: Z.testbit fden 0 = true -> forall b, In b (blocks_ofst stq ++ blocks_ofst rst) -> fst b <> pden).
    { intros Td [b m] Hb. rewrite in_app_iff in Hb. destruct Hb as [Hb|Hb].
      - destruct stq as [u0 u1|cq p]. destruct Hb. cbn in Hb. destruct Hb as [Hb|[]]. injection Hb. intros <- <-.
        destruct (QDYN cq p eq_refl) as [-> FB]. destruct FB as (_ & BA & _).
        pose proof (BA (pden, 8 * cden) ltac:(rewrite !in_app_iff; right; right; left; unfold BD; rewrite Td; left; reflexivity)) as AP. cbn in AP |- *.
        destruct (FRESH3 Td) as [-> _]. clear - AP. lia.
      - destruct rst as [u0 u1|cx p]. destruct Hb. cbn in Hb. destruct Hb as [Hb|[]]. injection Hb. intros <- <-.
        destruct (XDYN cx p eq_refl) as [-> FB]. destruct FB as (_ & BA & _).
        pose proof (BA (pden, 8 * cden) ltac:(rewrite !in_app_iff; right; left; unfold BD; rewrite Td; left; reflexivity)) as AP. cbn in AP |- *.
        destruct (FRESH3 Td) as [-> _]. clear - AP. lia. }
    assert (PND: Z.testbit fnum 0 = true -> Z.testbit fden 0 = true -> pnum <> pden).
    { intros Tn Td. destruct (FRESH3 Td) as [-> FB]. destruct FB as (_ & BA & _).
      pose proof (BA (pnum, 8 * cnum) ltac:(rewrite in_app_iff; left; unfold BN; rewrite Tn; left; reflexivity)) as AP. cbn in AP. destruct (FRESH2 Tn) as [-> _]. clear - AP. lia. }
    assert (ELB4: lb_free fden pden (lb_free fnum pnum (lb_free fn0 0 (lb_free fd0 0 LBc))) = blocks_ofst stq ++ blocks_ofst rst ++ LB).
    { unfold lb_free. rewrite F0b, F1b. unfold LBc, BN, BD. rewrite !(app_assoc (blocks_ofst stq) (blocks_ofst rst)).
      set (pre := blocks_ofst stq ++ blocks_ofst rst) in *.
      destruct (Z.testbit fnum 0) eqn:Tn; destruct (Z.testbit fden 0) eqn:Td; cbn [app].
      - rewrite (lb_remove_app_skip pnum pre) by (apply PNE; reflexivity). rewrite lb_remove_head.
        rewrite (lb_remove_app_skip pden pre) by (apply PDE; reflexivity). rewrite lb_remove_head. reflexivity.
      - rewrite (lb_remove_app_skip pnum pre) by (apply PNE; reflexivity). rewrite lb_remove_head. reflexivity.
      - rewrite (lb_remove_app_skip pden pre) by (apply PDE; reflexivity). rewrite lb_remove_head. reflexivity.
      - reflexivity. }
    (* [comment removed for export] *)
    eapply (divtail fx5 R5 M5 model4 K LBc cr4 Q Rd fd0 0 0 fn0 0 0 fnum cnum pnum fden cden pden HH5 MOK4 HK0).
    + kreg K5 2%nat F2.
    + etransitivity. exact (K5 4%nat ltac:(inl)). rewrite (preserved_sregs R3 R4 4 RP4) by inl. rewrite (K3 4%nat) by inl. rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4.
    + split. { unfold Q. replace (S - 64 - 352) with (S + (-26) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
      split. unfold Q; fsclia. split. unfold Q; flia. split. exact SPT. unfold Q; rewrite OPDEL_SCR_val. eapply L5.defined_sub. exact D5. clear; lia. clear; lia.
    + unfold Q; flia.
    + eapply L5.defined_sub. exact D5. unfold Q; clear; lia. unfold Q; clear; lia.
    + eapply div_saves_kept. 4: exact DS. intros i Hi; apply KEEP; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
    + pose proof DER' as (RD1 & _). unfold U. change (getr Rd (Z_to_bv 5 1)) with (getr Rd (reg 1)). rewrite RD1. rewrite BG.unsigned_lit by (unfold DIV_RET; clear; lia).
      unfold DIV_RET. split. clear; lia. reflexivity.
    + eapply local_obj_kept. 4:{ unfold Q. replace (S - 64 - 280) with (S - 344) by (clear; lia). exact LO0. } intros i Hi; apply KEEP; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
    + eapply local_obj_kept. 4:{ unfold Q. replace (S - 64 - 216) with (S - 280) by (clear; lia). exact LO1. } intros i Hi; apply KEEP; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
    + eapply local_obj_kept. 4:{ unfold Q. replace (S - 64 - 184) with (S - 248) by (clear; lia). exact LO2. } intros i Hi; apply KEEP; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
    + eapply local_obj_kept. 4:{ unfold Q. replace (S - 64 - 136) with (S - 200) by (clear; lia). exact LO3. } intros i Hi; apply KEEP; unfold Q in Hi; clear - Hi; lia. unfold Q; flia. unfold Q; flia.
    + intros T. rewrite F0b in T. discriminate T.
    + intros T. rewrite F1b in T. discriminate T.
    + intros Tn. unfold lb_free. rewrite F0b, F1b. unfold LBc, BN. rewrite Tn. rewrite !in_app_iff. right; right; left. left. reflexivity.
    + intros Td. unfold lb_free. rewrite F0b, F1b. destruct (Z.testbit fnum 0) eqn:Tn.
      * apply L5C.in_lb_remove_neq. unfold LBc, BD. rewrite Td. rewrite !in_app_iff. right; right; right; left. left. reflexivity. intros E. apply (PND eq_refl Td). symmetry. exact E.
      * unfold LBc, BD. rewrite Td. rewrite !in_app_iff. right; right; right; left. left. reflexivity.
    + (* [comment removed for export] *)
      cbv zeta. rewrite ELB4. intros fx6 R6 M6 model6 T2 T3 T4 TS HP6 MBV6 HH6.
      pose proof (L5C.model_but_vm_trans _ _ _ MBV (L5C.model_but_vm_trans _ _ _ MBV4 MBV6)) as MBV06.
      assert (KA6: forall a, Q - 352 <= a < 2 ^ 64 -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
      { intros a Ha. apply (kept_above M5 M6 _ (Q - 352) OPDEL_SCR _ a HP6). unfold Q; fsclia. rewrite OPDEL_SCR_val; clear; lia. flia. exact Ha. apply L5C.outside_nil. }
      assert (KB6: forall A n0 a, In (A, n0) (blocks_ofst stq ++ blocks_ofst rst ++ LB) -> A <= a < A + n0 -> M6 (Z_to_bv 64 a) = M5 (Z_to_bv 64 a)).
      { intros A n0 a Hin Ha. pose proof (LBdef _ _ _ _ HH6 A n0 Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO in Aimg.
        apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP6). eapply L5C.kept_block. exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; lia. rewrite EV; clear - Aimg Ha; lia. apply L5C.outside_nil. }
      assert (D6: L5.defined M6 (S - 10240) 10240).
      { replace 10240 with (1600 + (8224 + 416)) at 2 by (clear; lia). apply L5C.defined_app. 3: clear; lia.
        { eapply (cdef_below M5 M6 _ (Q - 352) OPDEL_SCR _ (S - 10240) 1600 HP6). flia. unfold Q; rewrite OPDEL_SCR_val; clear; lia. rewrite OPDEL_SCR_val; clear; lia. flia. unfold Q; flia.
          eapply L5.defined_sub. exact D5. clear; lia. clear; lia. }
        apply L5C.defined_app. 3: clear; lia.
        { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP6) as D. unfold Q in D. rewrite OPDEL_SCR_val in D. exactA D. }
        eapply (cdef_above M5 M6 _ (Q - 352) OPDEL_SCR _ _ 416 HP6). unfold Q; rewrite OPDEL_SCR_val; fsclia. rewrite OPDEL_SCR_val; clear; lia. flia. unfold Q; clear; lia. flia.
        eapply L5.defined_sub. exact D5. clear; lia. clear; lia. }
      assert (UD1: U Rd 1 = DIV_RET). { pose proof DER' as (RD1 & _). unfold U. change (getr Rd (Z_to_bv 5 1)) with (getr Rd (reg 1)). rewrite RD1. apply BG.unsigned_lit. unfold DIV_RET; clear; lia. }
      rewrite UD1. apply (stage_RET fx6 R6 M6 model6 cr4 (Z.lor (Z.land fq2 253) (2 * qneg)) (L5.BO (Z.land fb' 253) n' st') w').
      * exact T2.
      * rewrite T3. etransitivity. exact (K5 3%nat ltac:(inl)). rewrite (preserved_sregs R3 R4 3 RP4) by inl. rewrite (K3 3%nat) by inl. rewrite (preserved_sregs R1 R2 3 RP2) by inl. rewrite (K1 3%nat) by inl. exact H3.
      * rewrite T4. etransitivity. exact (K5 4%nat ltac:(inl)). rewrite (preserved_sregs R3 R4 4 RP4) by inl. rewrite (K3 4%nat) by inl. rewrite (preserved_sregs R1 R2 4 RP2) by inl. rewrite (K1 4%nat) by inl. exact H4.
      * exact TS.
      * exact MBV06.
      * exact HH6.
      * destruct CRA4 as [C3 C4]. unfold credit_after, DIVN_K, DIVN_BYTES in C3, C4. pose proof KPOS. clear - C3 CRK H. lia.
      * destruct CRA4 as [C3 C4]. unfold credit_after, DIVN_K, DIVN_BYTES in C3, C4. pose proof BPOS. clear - C4 CRB H. lia.
      * rewrite SCR_OPMOD_val. exact D6.
      * eapply top_frame_kept. 4: exact TF. 2: flia. 2: flia. intros i Hi. rewrite KA6. rewrite KX5. rewrite KA4. apply KA3. flia. unfold Q; clear - Hi; lia. unfold spd; flia.
        unfold X; clear - Hi; lia. flia. unfold X; clear - Hi; lia. unfold Q; flia.
      * eapply u8_at_agree1. 4: exact CQ3. 2: unfold Q; flia. 2: unfold Q; flia. intros i Hi. rewrite KA6. rewrite KX5. apply KA4. unfold Q, spd in *; flia. unfold Q, X in *; clear - Hi; lia. flia.
        unfold Q, X in *; clear - Hi; lia. unfold Q in *; flia.
      * apply L5DIVOPU.lor_byte. apply L5.land_byte_range. clear; lia. clear - Hq; lia.
      * destruct stq as [q0 q1|cq p].
        -- rewrite Z.lor_spec, Z.land_spec, (proj2 FQ2), Z.testbit_even_0. destruct QST as (T0 & _). rewrite T0. reflexivity.
        -- destruct QST2 as (T0 & C16 & C24 & _). destruct (QB cq p eq_refl) as (-> & Plo & Phi & PD & INP).
           split. { rewrite Z.lor_spec, Z.land_spec, T0. reflexivity. } split. reflexivity.
           assert (KQ: forall i, Q + 16 <= i < Q + 32 -> M6 (Z_to_bv 64 i) = M2 (Z_to_bv 64 i)).
           { intros i Hi. rewrite KA6. rewrite KX5. rewrite KA4. apply FR3. unfold Q in *; flia. unfold Q in *; clear - Hi; lia. unfold Q, spd in *; flia. unfold Q, X in *; clear - Hi; lia.
             unfold Q in *; flia. unfold Q, X in *; clear - Hi; lia. unfold Q in *; flia. }
           split. { eapply u64_at_agree1. 4: exact C16. intros i Hi; apply KQ; flia. unfold Q; flia. unfold Q; flia. }
           split. { eapply u64_at_agree1. 4: exact C24. intros i Hi; apply KQ; flia. unfold Q; flia. unfold Q; flia. }
           destruct (QDYN 8 p eq_refl) as [_ (BR & BA & _)]. split. exact BR. split. { intros b Hb. apply BA. apply in_app_iff in Hb. rewrite !in_app_iff. destruct Hb as [Hb|Hb]. left; exact Hb. right; right; right; exact Hb. }
           pose proof (LBdef _ _ _ _ HH6 p 64 ltac:(cbn; left; reflexivity)) as (D' & _). exact D'.
      * eapply big_at_agree1. 4: exact OX5. intros i Hi; apply KA6; unfold Q, X in *; flia. unfold X; flia. unfold X; flia.
      * eapply obj_limbs_agree1. 3: exact OL4.
        -- cbn [L5.bo_st L5.bo_len]. intros cap q E i Hi. subst st'. destruct rst as [u0 u1|cx p]. contradiction. destruct STM4 as (-> & -> & _).
           destruct (XB cx p eq_refl) as (-> & Plo & Phi & _). pose proof OL4 as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln in Hi.
           pose proof OX4 as OB'. unfold L5.big_at in OB'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB'. destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & _).
           rewrite (KB6 p 64 i). apply KX5. clear - Hi Hlc Plo Phi SPT; lia. unfold X; clear - Hi Hlc Phi SLO'; lia. rewrite !in_app_iff. right; left. cbn. left. reflexivity. clear - Hi Hlc; lia.
        -- cbn [L5.bo_st L5.bo_len]. intros cap q E. subst st'. destruct rst as [u0 u1|cx p]. contradiction. destruct STM4 as (-> & -> & _).
           destruct (XB cx p eq_refl) as (-> & Plo & Phi & _). pose proof OL4 as (Ln & _). cbn [L5.bo_len] in Ln. rewrite Ln.
           pose proof OX4 as OB'. unfold L5.big_at in OB'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in OB'. destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & _). clear - Hlc Plo Phi SPT; lia.
      * unfold L5.bo_neg. cbn [L5.bo_fb]. rewrite Z.land_spec. apply Bool.andb_false_intro2. reflexivity.
      * cbn [L5.bo_st]. destruct rst as [u0 u1|cx p]; destruct st' as [v0 v1|cap' q']; try exact STM4. destruct STM4 as (-> & -> & _).
        destruct (XDYN cx p eq_refl) as [-> (BR & BA & _)]. split. reflexivity. split. reflexivity. split. exact BR. split. { intros b Hb. apply BA. rewrite !in_app_iff. right; right; exact Hb. }
        pose proof (LBdef _ _ _ _ HH6 p 64 ltac:(rewrite !in_app_iff; right; left; cbn; left; reflexivity)) as (D' & _). exact D'.
      * eapply big_at_agree1. 4: exact OBB. 2: subst bo; flia. 2: subst bo; flia. intros i Hi. rewrite KA6. rewrite KX5. rewrite KA4. apply KA3.
        subst bo; flia. subst bo; unfold Q; clear - Hi; lia. subst bo; unfold spd; flia. subst bo; unfold X; clear - Hi; lia. subst bo; flia. subst bo; unfold X; clear - Hi; lia. subst bo; unfold Q; flia.
      * eapply obj_limbs_agree1. 3: exact OLB.
        -- intros cap q E i Hi. pose proof (BBLK cap q E) as INB. pose proof OLB as (Ln & _ & _). pose proof OBB as OB'. unfold L5.big_at in OB'. rewrite E in OB'.
           destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln in Hi.
           pose proof (LBdef _ _ _ _ HH q (8 * cap) ltac:(unfold LBc; rewrite !in_app_iff; right; right; right; right; exact INB)) as (_ & _ & Ahi & _).
           rewrite (KB6 q (8 * cap) i). rewrite KX5. rewrite (KB4 q (8 * cap) i INB). apply KA3.
           clear - Hi Hlc Qlo Qhi; lia. unfold Q; clear - Hi Hlc Ahi SLO'; lia. clear - Hi Hlc; lia. clear - Hi Hlc Qlo Qhi; lia. unfold X; clear - Hi Hlc Ahi SLO'; lia.
           rewrite !in_app_iff; right; right; exact INB. clear - Hi Hlc; lia.
        -- intros cap q E. pose proof OLB as (Ln & _ & _). pose proof OBB as OB'. unfold L5.big_at in OB'. rewrite E in OB'.
           destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
      * (* [comment removed for export] *)
        assert (HPx4: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M4).
        { eapply (L5HP.hpres_trans L LB LBc S SCR_OPMOD [(X, 32)] M0 M3 M4 spd UNNORM_SCR). exact HP3. exact HP4.
          - intros a KA'. eapply L5HP.kept_mono. exact KA'. intros b Hb; unfold LBc; rewrite !in_app_iff; right; right; right; right; exact Hb.
            unfold spd; rewrite UNNORM_SCR_val; fsclia. unfold spd; flia.
            intros OW. apply outside2. exact (L5HP.outside_in _ _ X 32 OW ltac:(left; reflexivity)).
            destruct rst as [v0 v1|cx p]; cbn [L5.bo_data L5.bo_cap L5.bo_st]. { pose proof (L5HP.outside_in _ _ X 32 OW ltac:(left; reflexivity)) as NX. unfold X in NX |- *. clear - NX; lia. }
            destruct (XDYN cx p eq_refl) as [-> (BR & BA & _)]. destruct BR as (_ & Bimg & _ & _ & Bhi).
            eapply (L5C.kept_not_fresh L LB S SCR_OPMOD [(X, 32)] a p 64 KA'). intros b Hb; apply BA; rewrite !in_app_iff; right; right; exact Hb. exact Bimg. exact Bhi. exact LBceil.
          - intros b Hb; unfold LBc; rewrite !in_app_iff; right; right; right; right; exact Hb. - exact CEIL. - flia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - flia. }
        assert (HPx5: L5C.hpres L LB S SCR_OPMOD [(X, 32)] M0 M5).
        { eapply (L5HP.hpres_trans L LB LB S SCR_OPMOD [(X, 32)] M0 M4 M5 S SCR_OPMOD [(X, 32)]). exact HPx4.
          - eapply (L5HP.hpres_piece L LB S SCR_OPMOD [(X, 32)] M4 M5 (fun a => a = X)). { intros a Ha Hn. apply KX5. exact Ha. exact Hn. }
            intros a KA' C'. apply (L5HP.outside_in _ _ X 32 (L5HP.kept_outside_W _ _ _ _ _ _ KA') ltac:(left; reflexivity)). unfold X in C' |- *; clear - C'; lia.
            rewrite SCR_OPMOD_val. exact D5. exact MG5.
          - intros a KA'; exact KA'. - intros b Hb; exact Hb. - exact CEIL. - flia. - rewrite SCR_OPMOD_val; clear; lia. - rewrite EV; clear; lia. - flia. }
        eapply (L5HP.hpres_trans L LB _ S SCR_OPMOD [(X, 32)] M0 M5 M6 (Q - 352) OPDEL_SCR []). exact HPx5. exact HP6.
        -- intros a KA'. eapply L5HP.kept_mono. exact KA'. intros b Hb; rewrite !in_app_iff; right; right; exact Hb. unfold Q; fsclia. unfold Q; flia. intros _; apply L5C.outside_nil.
        -- intros b Hb; rewrite !in_app_iff; right; right; exact Hb. -- exact CEIL. -- flia. -- rewrite SCR_OPMOD_val; clear; lia. -- rewrite EV; clear; lia. -- flia.
  - (* [comment removed for export] *)
    intros fx7 R7 M7 model7 qX LB7 cr7 SD E3X UE MBV7 HH7. cbn [L5.bo_st L5.bo_len] in E3X, UE.
    destruct (SD1 SD) as ((qx & EX) & Hn & (q0 & q1 & EQ) & Tn & Td). rewrite EX in E3X. injection E3X. intros <-.
    destruct (FRESH2 Tn) as [ECN FBN]. destruct (FRESH3 Td) as [ECD FBD].
    destruct UE as (RQ & MQ & Q1 & Q2 & Q8 & Q9 & Q3 & Q4 & QS & DE & U8 & U16 & U24 & U56 & U48 & U40 & U32 & HPU).
    destruct DE as (RN & MN & N1 & N2 & N8 & N3 & N4 & N9 & NS & DN & V8 & V16 & ZR & HPQ).
    destruct DN as (Bk0 & Bk1 & nn & gd0 & gn0 & gn & gden & gd3 & gbX & R2' & R3' & R4' & R1' & R10' & R11' & R12' & Enn & R8' & R9' & R18' & R19' & R20' & R21' & R22' & R23' & R24' & R25' & R26' & R27'
                     & Fd3r & Fd3b & Fd3b1 & UbX & FbXr
                     & C360 & C368 & C376 & C384r & C424 & C432 & C440 & C448 & C456 & C464 & DSN
                     & Gd0 & Gd0r & Gd0b & C272 & C264 & C256 & Gn0 & Gn0r & Gn0b & C208 & C200 & C192 & Gn & Gnr & Gnb & Gnb1 & C176 & C168 & C160
                     & Gden & Gdenr & Gdenb & Gdenb1 & C128 & C120 & D112 & V152 & V144 & V232 & V224 & V248 & V240 & C284x & C344x & ELB7 & FB1 & FB0 & ECR & HPN).
    pose proof (L5C.model_but_vm_trans _ _ _ MBV MBV7) as MBV07.
    (* [comment removed for export] *)
    assert (T7: forall a, S - 416 <= a < 2 ^ 64 -> ~ (Q <= a < Q + 16) -> M7 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha NQa. rewrite <- (KA3 a) by (first [exact NQa | flia]). apply (kept_above M3 M7 LBc spd UNNORM_SCR _ a HPU). unfold spd; rewrite UNNORM_SCR_val; fsclia.
      rewrite UNNORM_SCR_val; clear; lia. flia. unfold spd; exact Ha. apply L5C.outside_nil. }
    assert (TB7: forall A n0 a, In (A, n0) LBc -> A <= a < A + n0 -> M7 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros A n0 a Hin Ha. pose proof (LBdef _ _ _ _ HH A n0 Hin) as (_ & (Alo & Aimg) & Ahi & _). rewrite IMG', IMGLO in Aimg.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HPU). eapply L5C.kept_block. exact Hin. exact Ha. clear - Alo; lia. clear - Ahi SPT; lia. rewrite EV; clear - Aimg Ha; lia. apply L5C.outside_nil. }
    (* [comment removed for export] *)
    assert (E18_3: getr R3 (reg 18) = Z_to_bv 64 X). { rewrite (K3 18%nat) by inl. exact E18'. }
    assert (URN1: U RN 1 = DIVN_RET). { unfold U. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite N1. apply BG.unsigned_lit. unfold DIVN_RET; clear; lia. }
    assert (URN8: U RN 8 = X). { unfold U. replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite N8. apply BG.unsigned_lit. unfold X; flia. }
    assert (URN18: U RN 18 = X). { unfold U. rewrite (NS 18) by (clear; lia). rewrite (QS 18) by (clear; lia). change (getr R3 (Z_to_bv 5 18)) with (getr R3 (reg 18)). rewrite E18_3. apply BG.unsigned_lit. unfold X; flia. }
    assert (URQ1: U RQ 1 = DIVEQ_RET). { unfold U. replace (Z_to_bv 5 1) with (1%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q1. apply BG.unsigned_lit. unfold DIVEQ_RET; clear; lia. }
    assert (URQ8: U RQ 8 = X). { unfold U. replace (Z_to_bv 5 8) with (8%bv : bv 5) by (apply bv_eq; reflexivity). rewrite Q8. apply BG.unsigned_lit. unfold X; flia. }
    assert (UR31: U R3 1 = 141856). { unfold U. change (getr R3 (Z_to_bv 5 1)) with (getr R3 (reg 1)). rewrite B1. apply BG.unsigned_lit. clear; lia. }
    assert (UR38: U R3 8 = X). { unfold U. change (getr R3 (Z_to_bv 5 8)) with (getr R3 (reg 8)). rewrite (K3 8%nat) by inl. rewrite E8'. apply BG.unsigned_lit. unfold X; flia. }
    assert (UR39: U R3 9 = Q). { unfold U. change (getr R3 (Z_to_bv 5 9)) with (getr R3 (reg 9)). rewrite (K3 9%nat) by inl. rewrite E9'. apply BG.unsigned_lit. unfold Q; flia. }
    pose proof DSN as (W1 & W8 & W9 & W18 & W19 & W20 & W21 & W22 & W23 & W24 & W25 & W26 & W27). rewrite URN1 in W1. rewrite URN8 in W8. rewrite URN18 in W18.
    rewrite URQ1 in V8. rewrite URQ8 in V16. rewrite UR31 in U8. rewrite UR38 in U16. rewrite UR39 in U24.
    pose proof ZR as ZR'. unfold zero_obj, L5.big_at in ZR'. cbn [L5.bo_fb L5.bo_len L5.bo_st] in ZR'. destruct ZR' as (Z0 & _).
    (* [comment removed for export] *)
    assert (Tfr: forall a, S - 416 <= a < S - 64 -> M7 (Z_to_bv 64 a) = M (Z_to_bv 64 a)). { intros a Ha. apply T7. flia. unfold Q; clear - Ha; lia. }
    pose proof (local_obj_kept M M7 (S - 344) fd0 0 0 ltac:(intros i Hi; apply Tfr; clear - Hi; lia) ltac:(flia) ltac:(flia) LO0) as (L0a & L0r & _).
    pose proof (local_obj_kept M M7 (S - 280) fn0 0 0 ltac:(intros i Hi; apply Tfr; clear - Hi; lia) ltac:(flia) ltac:(flia) LO1) as (L1a & L1r & _).
    pose proof (local_obj_kept M M7 (S - 248) fnum cnum pnum ltac:(intros i Hi; apply Tfr; clear - Hi; lia) ltac:(flia) ltac:(flia) LO2) as (L2a & L2r & L2d). destruct (L2d Tn) as (L2c & _ & L2p & _).
    pose proof (local_obj_kept M M7 (S - 200) fden cden pden ltac:(intros i Hi; apply Tfr; clear - Hi; lia) ltac:(flia) ltac:(flia) LO3) as (L3a & L3r & L3d). destruct (L3d Td) as (L3c & _ & L3p & _).
    rewrite ECN in L2c. rewrite ECD in L3c.
    pose proof (o1_saves_kept M M7 S R0 ltac:(intros i Hi; apply Tfr; clear - Hi; lia) ltac:(flia) ltac:(flia) SAV) as SAV7.
    pose proof SAV7 as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8 & Y9 & Y10 & Y11 & Y12 & Y13).
    pose proof (top_frame_kept M M7 S R0 ltac:(intros i Hi; apply T7; [flia | unfold Q; clear - Hi; lia]) ltac:(flia) ltac:(flia) TF) as (Z1 & Z8 & Z3 & Z4). rewrite UR01 in Z1.
    assert (CQ7: L5.u8_at RSEGS M7 Q (Z.lor (Z.land fq2 253) (2 * qneg))).
    { eapply u8_at_agree1. 4: exact CQ3. 2: unfold Q; flia. 2: unfold Q; flia. intros i Hi. apply (kept_above M3 M7 LBc spd UNNORM_SCR _ i HPU). unfold spd; rewrite UNNORM_SCR_val; fsclia.
      rewrite UNNORM_SCR_val; clear; lia. flia. unfold spd, Q in *; flia. apply L5C.outside_nil. }
    assert (FQ7: 0 <= Z.lor (Z.land fq2 253) (2 * qneg) < 256 /\ Z.testbit (Z.lor (Z.land fq2 253) (2 * qneg)) 0 = false).
    { split. apply L5DIVOPU.lor_byte. apply L5.land_byte_range. clear; lia. clear - Hq; lia.
      rewrite Z.lor_spec, Z.land_spec, (proj2 FQ2), Z.testbit_even_0. subst stq. destruct QST as (T0 & _). rewrite T0. reflexivity. }
    (* [comment removed for export] *)
    assert (ELB7': LB7 = (Bk0, 64) :: (Bk1, 64) :: (qx, 64) :: (pnum, 64) :: (pden, 64) :: LB).
    { rewrite ELB7. unfold LBc, BN, BD. rewrite EQ, EX, Tn, Td, ECN, ECD. reflexivity. }
    unfold cfg. apply (KT fx7 R7 M7 model7 Bk0 Bk1 qx cr7).
    + exists Bk0, Bk1, pnum, pden, qx. split. reflexivity. split. left; reflexivity. split.
      { split. { rewrite R2'. unfold spd. f_equal. clear; lia. } split. { rewrite R3', N3, Q3. transitivity (Z_to_bv 64 GP). 2: symmetry; exact G3.
          etransitivity. exact (K3 3%nat ltac:(inl)). etransitivity. exact (preserved_sregs R1 R2 3 RP2 ltac:(inl)). etransitivity. exact (K1 3%nat ltac:(inl)). exact H3. }
        split. { rewrite R4', N4, Q4. transitivity (Z_to_bv 64 TP). 2: symmetry; exact G4.
          etransitivity. exact (K3 4%nat ltac:(inl)). etransitivity. exact (preserved_sregs R1 R2 4 RP2 ltac:(inl)). etransitivity. exact (K1 4%nat ltac:(inl)). exact H4. }
        split. exact R10'. rewrite R9'. reflexivity. }
      split. { exact I. }
      unfold L5DSOU.assert_throw_frames.
      eexists _, _, _, _, _, _, _, _, _, _. eexists _, _, _, _, _, _, _, _, _, _. eexists _, _, _.
      unfold DIVN_RESIZE_RET, RESIZE_RET1, DIVN_RET, DIVEQ_RET, spd, X, Q in *.
      split. exactA C448. split. exactA C440. split. exactA C432. split. exactA C424.
      split. exactA C384r. split. exactA C376. split. { replace (S - 528) with (S - 416 - 64 - 48) by (clear; lia). exactA C368. } split. exactA C360.
      split. exactA Gd0. split. exact Gd0r. split. exact Gd0b.
      split. exactA Gn0. split. exact Gn0r. split. exact Gn0b. split. exactA C200. split. exactA C192.
      split. exactA Gn. split. exact Gnr. split. exact Gnb. split. exactA C168. split. exactA C160.
      split. exactA Gden. split. exact Gdenr. split. exact Gdenb.
      split. exactA W27. split. exactA W26. split. exactA W25. split. exactA W24. split. exactA W23. split. exactA W22. split. exactA W21. split. exactA W20. split. exactA W19.
      split. exactA W18. split. exactA W9. split. exactA W8. split. exactA W1.
      split. exactA Z0. split. clear; lia. split. reflexivity.
      split. exactA V16. split. exactA V8.
      split. exactA U56. split. clear; lia. split. reflexivity.
      split. exactA U24. split. exactA U16. split. exactA U8.
      split. exactA L0a. split. exact L0r. split. exact F0b.
      split. exactA L1a. split. exact L1r. split. exact F1b.
      split. exactA L2a. split. exact L2r. split. exact Tn. split. exactA L2c. split. exactA L2p.
      split. exactA L3a. split. exact L3r. split. exact Td. split. exactA L3c. split. exactA L3p.
      split. exactA Y13. split. exactA Y12. split. exactA Y11. split. exactA Y10. split. exactA Y9. split. exactA Y8. split. exactA Y7. split. exactA Y6. split. exactA Y5. split. exactA Y4. split. exactA Y3.
      split. exactA Y2. split. { unfold DIV_RET in Y1. exactA Y1. }
      split. exactA CQ7. split. exact (proj1 FQ7). split. exact (proj2 FQ7).
      split. exactA Z4. split. { unfold OPF_BACK in Z3. exactA Z3. } split. exactA Z8. unfold OPMOD1_RET in Z1. exactA Z1.
    + exact EX. + exact SD.
    + rewrite <- ELB7'. exact HH7.
    + exact MBV07.
    + rewrite ECR. unfold debit. cbn [fst]. pose proof KPOS. clear - CRK H. lia.
    + rewrite ECR. unfold debit. cbn [snd]. pose proof BPOS. clear - CRB H. lia.
    + rewrite EX in OX. eapply big_at_agree1. 4: exact OX. intros i Hi; apply T7; unfold X, Q in *; flia. unfold X; flia. unfold X; flia.
    + destruct (XDYN 8 qx EX) as [_ (BR & BA & _)]. split. exact BR. split. { intros b Hb. apply BA. rewrite !in_app_iff. right; right; exact Hb. }
      pose proof (LBdef _ _ _ _ HH7 qx 64 ltac:(rewrite ELB7'; cbn; right; right; left; reflexivity)) as (D' & _). exact D'.
    + eapply big_at_agree1. 4: exact OBB. intros i Hi; apply T7; generalize BO; unfold Q; flia. generalize BO; flia. generalize BO; flia.
    + eapply obj_limbs_agree1. 3: exact OLB.
      * intros cap q E i Hi. pose proof (BBLK cap q E) as INB. pose proof OLB as (Ln & _ & _). pose proof OBB as OB'. unfold L5.big_at in OB'. rewrite E in OB'.
        destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln in Hi.
        assert (INC: In (q, 8 * cap) LBc). { unfold LBc. rewrite !in_app_iff. right; right; right; right; exact INB. }
        pose proof (LBdef _ _ _ _ HH q (8 * cap) INC) as (_ & _ & Ahi & _).
        rewrite (TB7 q (8 * cap) i INC). apply KA3. clear - Hi Hlc Qlo Qhi; lia. unfold Q; clear - Hi Hlc Ahi SLO'; lia. clear - Hi Hlc; lia.
      * intros cap q E. pose proof OLB as (Ln & _ & _). pose proof OBB as OB'. unfold L5.big_at in OB'. rewrite E in OB'.
        destruct OB' as (_ & _ & _ & _ & _ & _ & Hlc & Hcap & _ & Qlo & Qhi & _). rewrite Ln. clear - Hlc Hcap Qlo Qhi. lia.
    + replace SCR_OPMOD with (736 + (9088 + 416)) at 2 by (rewrite SCR_OPMOD_val; clear; lia). rewrite SCR_OPMOD_val. apply L5C.defined_app. 3: clear; lia.
      { eapply (cdef_below M3 M7 LBc spd UNNORM_SCR _ (S - 10240) 736 HPU). flia. unfold spd; rewrite UNNORM_SCR_val; clear; lia. rewrite UNNORM_SCR_val; clear; lia. flia. unfold spd; flia.
        eapply L5.defined_grows. exact MG23. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia. }
      apply L5C.defined_app. 3: clear; lia.
      { pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HPU) as D. unfold spd in D. rewrite UNNORM_SCR_val in D. exactA D. }
      eapply (cdef_above M3 M7 LBc spd UNNORM_SCR _ _ 416 HPU). unfold spd; rewrite UNNORM_SCR_val; fsclia. rewrite UNNORM_SCR_val; clear; lia. flia. unfold spd; clear; lia. flia.
      eapply L5.defined_grows. exact MG23. eapply L5.defined_sub. exact SCR'. clear; lia. clear; lia.
    + eapply (L5HP.hpres_trans L LB LBc S SCR_OPMOD [(X, 32)] M0 M3 M7 spd UNNORM_SCR []). exact HP3. exact HPU.
      * intros a KA'. eapply L5HP.kept_mono. exact KA'. intros b Hb; unfold LBc; rewrite !in_app_iff; right; right; right; right; exact Hb.
        unfold spd; rewrite UNNORM_SCR_val; fsclia. unfold spd; flia. intros _; apply L5C.outside_nil.
      * intros b Hb; unfold LBc; rewrite !in_app_iff; right; right; right; right; exact Hb. * exact CEIL. * flia. * rewrite SCR_OPMOD_val; clear; lia. * rewrite EV; clear; lia. * flia.
Qed.

End Call.
End WithHeap.
End SCFG_1.
End L5OPMOD1TU.
