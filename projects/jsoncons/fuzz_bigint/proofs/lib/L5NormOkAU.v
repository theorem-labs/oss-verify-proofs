(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg HeapIface
     AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 SegRun SegPlan Ub0PlanKit AsanPlanCore
     Ub0_code_221b0_23098 BigBranchUb0 BigLinkBase BigLinkGlue BigLinkInlBaseU BigLinkDqU BigLinkDivBaseU BigClzUb0 L5Defs L5Kn
     L5Core L5CoreSpecsU L5Words L5WordsB L5ReduceU L5ShlU L5ShlUOk L5MulMU L5MulMOkU L5Hp L5NormU.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nra Cache. Unset Nia Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto0.

Module L5NORMOKAU.
Import L5CSU. Import L5W. Import L5NORMU.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Ubsan.M.loaded_segments)) (only parsing).
Section SCFG_1.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma r1 : (1%bv : bv 5) = reg 1. Proof. apply bv_eq; reflexivity. Qed.
Lemma r2 : (2%bv : bv 5) = reg 2. Proof. apply bv_eq; reflexivity. Qed.
Lemma r4 : (4%bv : bv 5) = reg 4. Proof. apply bv_eq; reflexivity. Qed.
Lemma r10 : (10%bv : bv 5) = reg 10. Proof. apply bv_eq; reflexivity. Qed.
Lemma r11 : (11%bv : bv 5) = reg 11. Proof. apply bv_eq; reflexivity. Qed.
Lemma r12 : (12%bv : bv 5) = reg 12. Proof. apply bv_eq; reflexivity. Qed.
Lemma r13 : (13%bv : bv 5) = reg 13. Proof. apply bv_eq; reflexivity. Qed.

(* [comment removed for export] *)
Lemma pass_of_preserved R R' : regs_preserved R R' -> forall i, In i cs_pass -> getr R' (reg i) = getr R (reg i).
Proof.
  intros RP i Hi. apply RP. unfold callee_saved_idx. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [cbn; tauto|]). destruct Hi.
Qed.
Definition cs_all : list nat := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat.
Lemma preserved_by_index (R R' : bvmap 5 word) : (forall i, In i cs_all -> getr R' (reg i) = getr R (reg i)) -> regs_preserved R R'.
Proof.
  intros KR x Hx. rewrite <- (AX2S.ridx_roundtrip x). apply KR.
  unfold callee_saved_idx in Hx. unfold AX2.ridx. set (z := bv_unsigned x) in *. cbn in Hx.
  repeat (destruct Hx as [Hx|Hx]; [rewrite <- Hx; cbn; tauto|]). destruct Hx.
Qed.
Lemma preserved_of_ret (R R' : bvmap 5 word) sp rv :
  getr R (reg 2) = Z_to_bv 64 sp -> at_ret R R' sp rv -> (forall i, In i cs_pass -> getr R' (reg i) = getr R (reg i)) ->
  regs_preserved R R'.
Proof.
  intros H2 (T1 & T2 & T8 & T9 & T18 & T19 & T20 & _) KR. apply preserved_by_index. intros i Hi. cbn in Hi.
  repeat (destruct Hi as [<-|Hi]; [first [rewrite T2, H2; reflexivity | assumption | apply KR; cbn; tauto] |]). destruct Hi.
Qed.
(* [comment removed for export] *)
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

Lemma model_ok_but_vm m m' : model_ok m -> model_but_vm m m' -> model_ok m'.
Proof.
  intros (A & B & C) H. split. rewrite (L5C.halted_but_vm _ _ H). exact A. split. rewrite (L5C.lazy_but_vm _ _ H). exact B.
  rewrite (L5C.materialized_but_vm _ _ H). exact C.
Qed.

Lemma obj_limbs_at M o b ws : L5.big_at RSEGS M o b -> L5C.obj_limbs RSEGS M b ws -> L5.limbs_at RSEGS M (L5.bo_data o b) ws.
Proof.
  intros OB (Lw & Rw & V). destruct b as [fb len [v0 v1|cap q]]; cbn [L5.bo_st L5.bo_data L5.bo_len] in *.
  - destruct OB as (_ & _ & _ & _ & O16 & O24 & Hl2 & _). subst ws.
    intros i Hi. rewrite length_firstn in Hi. cbn [length] in Hi.
    destruct len as [|[|[|len]]]; cbn; try lia.
    + destruct i; [|lia]. cbn -[Z.add Z.mul Z.of_nat]. rewrite Z.add_0_r. exact O16.
    + destruct i as [|[|i]]; try lia; cbn -[Z.add Z.mul Z.of_nat]. rewrite Z.add_0_r. exact O16. replace (o + 16 + 8 * Z.of_nat 1) with (o + 24) by lia. exact O24.
    + exfalso. cbn [L5.bo_len] in Hl2. lia.
  - exact V.
Qed.

(* [comment removed for export] *)
Lemma obj_limbs_prefix M fb m st rw n :
  L5C.obj_limbs RSEGS M (L5.BO fb m st) rw -> (n <= m)%nat -> (match st with L5.BInl _ _ => (m <= 2)%nat | _ => True end) ->
  L5C.obj_limbs RSEGS M (L5.BO fb n st) (firstn n rw).
Proof.
  intros (Lw & Rw & V) Hn Hst. unfold L5C.obj_limbs. cbn [L5.bo_len L5.bo_st] in *. split. rewrite length_firstn. lia.
  split. apply (proj2 (words_ok_BF _)). apply (BigFactsBase.words_ok_firstn n rw). apply (proj1 (words_ok_BF rw)). exact Rw.
  destruct st as [v0 v1|cap q].
  - subst rw. rewrite L5C.firstn_firstn_le by lia. reflexivity.
  - apply L5C.limbs_at_firstn. exact V.
Qed.

Local Ltac uSCR := unfold NORM_SCR, L5MULMU.MULM_SCR, L5SHLU.SHL_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *.
Local Ltac sclia := unfold NORM_SCR, L5MULMU.MULM_SCR, L5SHLU.SHL_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *; lia.
(* [comment removed for export] *)
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         end.
Local Ltac flia := prune_impl; lia.
Local Ltac fsclia := prune_impl; unfold NORM_SCR, L5MULMU.MULM_SCR, L5SHLU.SHL_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *; lia.

Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis RESIZE : resize_spec L HI.
Let shl_ok := L5SHLUOK.shl_ok L HI LY HIok RESIZE.
Let mulm_ok := L5MULMOKU.mulm_ok L HI LY HIok RESIZE.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Call.
Variables (fx0 : FPState) (R0 : bvmap 5 word) (M0 : word -> option byte) (model0 : Model) (K : TSet)
          (LB : list (Z * Z)) (cr : credit) (od on px sp r : Z) (bd bn : L5.bigobj) (wd wn : list Z).
Hypothesis HH0 : hi_heap HI LB cr M0 (m_vmmaps model0).
Hypothesis MOK0 : model_ok model0.
Hypothesis HK0 : K [].
Hypothesis G11 : getr R0 11%bv = Z_to_bv 64 od.
Hypothesis G12 : getr R0 12%bv = Z_to_bv 64 on.
Hypothesis G13 : getr R0 13%bv = Z_to_bv 64 px.
Hypothesis G1 : getr R0 1%bv = Z_to_bv 64 r.
Hypothesis RA : L5.ra_ok r.
Hypothesis G2 : getr R0 2%bv = Z_to_bv 64 sp.
Hypothesis G4 : getr R0 4%bv = Z_to_bv 64 TP.
Hypothesis STK : L5C.stk (hl_sptop L) M0 sp NORM_SCR.
Hypothesis OBd : L5.big_at RSEGS M0 od bd.
Hypothesis OLd : L5C.obj_limbs RSEGS M0 bd wd.
Hypothesis Hnd : (1 <= L5.bo_len bd <= 290)%nat.
Hypothesis TOPnz : nth_w wd (L5.bo_len bd - 1) <> 0.
Hypothesis TOPsm : (2 <= L5.bo_len bd)%nat -> nth_w wd (L5.bo_len bd - 1) < 2 ^ 63.
Hypothesis OBn : L5.big_at RSEGS M0 on bn.
Hypothesis OLn : L5C.obj_limbs RSEGS M0 bn wn.
Hypothesis Hnn : (1 <= L5.bo_len bn <= 290)%nat.
Hypothesis NN2 : (2 <= L5.bo_len bd)%nat -> (2 <= L5.bo_len bn)%nat /\ exists i, (i < L5.bo_len bn)%nat /\ nth_w wn i <> 0.
Hypothesis Aod : od mod 8 = 0.
Hypothesis Aon : on mod 8 = 0.
Hypothesis Sod : sp <= od.
Hypothesis Son : sp <= on.
Hypothesis Hod : od + 32 <= hl_sptop L.
Hypothesis Hon : on + 32 <= hl_sptop L.
Hypothesis APdn : apart od 32 on 32.
Hypothesis DEFd : L5.defined M0 od 32.
Hypothesis DEFn : L5.defined M0 on 32.
Hypothesis P4 : px mod 4 = 0.
Hypothesis Spx : sp <= px.
Hypothesis Hpx : px + 4 <= hl_sptop L.
Hypothesis APpd : apart px 4 od 32.
Hypothesis APpn : apart px 4 on 32.
Hypothesis DEFp : L5.defined M0 px 4.
Hypothesis BLKd : forall cap q, L5.bo_st bd = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len bd) + 1 <= cap /\ apart px 4 q (8 * cap).
Hypothesis BLKn : forall cap q, L5.bo_st bn = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len bn) + 1 <= cap /\ apart px 4 q (8 * cap).
Hypothesis APB : forall cd qd cn qn, L5.bo_st bd = L5.BDyn cd qd -> L5.bo_st bn = L5.BDyn cn qn -> apart qd (8 * cd) qn (8 * cn).
Hypothesis SECcap : second (L5.bo_len bd) (L5SHLU.shl_result wd (clz_of (nth_w wd (L5.bo_len bd - 1)))) = true ->
       (L5.bo_dyn bd = true -> Z.of_nat (L5.bo_len bd) + 2 <= L5.bo_cap bd) /\ (L5.bo_dyn bn = true -> Z.of_nat (L5.bo_len bn) + 2 <= L5.bo_cap bn).
Hypothesis CR : credits L cr (cnt bd + cnt bn).
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (c : Z) (gd gn : growth) LB' cr',
        norm_post L LB cr M0 M' R0 R' od on px sp bd bn wd wn c gd gn LB' cr' ->
        model_but_vm model0 model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K.

(* [comment removed for export] *)
Let nd : nat := L5.bo_len bd.
Let nn : nat := L5.bo_len bn.
Let w0 : Z := nth_w wd (nd - 1).
Let C0 : Z := clz_of w0.
Let D : list Z := L5SHLU.shl_result wd C0.
Let Dn : list Z := L5SHLU.shl_result wn C0.
Let SEC : bool := second nd D.
Let W : list L5.range := norm_W od on px bd bn.

(* [comment removed for export] *)
Lemma stk0 : sp mod 16 = 0 /\ hl_sptop L - 2 ^ 23 + NORM_SCR <= sp /\ sp <= hl_sptop L /\ (0x7fff80000000 <= hl_sptop L <= 2 ^ 47) /\ L5.defined M0 (sp - NORM_SCR) NORM_SCR.
Proof. exact STK. Qed.
Lemma IMG : hl_img_hi L = 0x92000. Proof. apply (ly_img_hi L LY). Qed.
Lemma IMGLO : hl_img_lo L = 0x10000. Proof. apply (ly_img_lo L LY). Qed.
Lemma ERRNO : hl_errno L + 4 <= 0x7fff7f800000. Proof using L LY od on px bd bn wd wn Hnd TOPsm Hnn NN2. rewrite (ly_errno L LY). lia. Qed.
Lemma SPTOP : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47. Proof. pose proof STK as (_ & _ & _ & WND & _). exact WND. Qed.
Lemma ERRNOV : hl_errno L = 0x70e94. Proof. apply (ly_errno L LY). Qed.
Lemma LBhi LBx crx M VM : hi_heap HI LBx crx M VM -> forall b, In b LBx -> fst b + snd b <= (hl_sptop L - 8388608).
Proof. intros HH b Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) b Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & _). exact Q4. Qed.
Lemma LBdef LBx crx M VM : hi_heap HI LBx crx M VM -> forall A n, In (A, n) LBx -> L5.defined M A n /\ (4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A)) /\ A + n <= (hl_sptop L - 8388608).
Proof. intros HH A n Hb. pose proof (proj1 (hio_wf L SCFG HI HIok LBx crx M _ HH) (A, n) Hb) as ((Q0 & Q1 & Q2 & Q3 & Q4) & Dd & _). cbn in *. repeat split; assumption. Qed.

Lemma wd_len : length wd = nd. Proof. exact (proj1 OLd). Qed.
Lemma wn_len : length wn = nn. Proof. exact (proj1 OLn). Qed.
Lemma wd_ok : words_ok wd. Proof. exact (proj1 (proj2 OLd)). Qed.
Lemma wn_ok : words_ok wn. Proof. exact (proj1 (proj2 OLn)). Qed.
Lemma w0_rng : 1 <= w0 < 2 ^ 64.
Proof. pose proof (words_ok_nth wd (nd - 1) wd_ok) as X. subst w0. fold nd in TOPnz. lia. Qed.
Lemma C0_rng : 0 <= C0 <= 63 /\ 2 ^ 63 <= w0 * 2 ^ C0 < 2 ^ 64.
Proof. apply clz_of_spec. apply w0_rng. Qed.
(* [comment removed for export] *)
Lemma D_len : length D = (if C0 =? 0 then nd else S nd).
Proof. subst D. unfold L5SHLU.shl_result. destruct (Z.eqb_spec C0 0). apply wd_len. rewrite shl_words_length, wd_len. reflexivity. Qed.
Lemma Dn_len : length Dn = (if C0 =? 0 then nn else S nn).
Proof. subst Dn. unfold L5SHLU.shl_result. destruct (Z.eqb_spec C0 0). apply wn_len. rewrite shl_words_length, wn_len. reflexivity. Qed.
Lemma D_ok : words_ok D.
Proof. subst D. unfold L5SHLU.shl_result. destruct (Z.eqb_spec C0 0). apply wd_ok. apply shl_words_ok. pose proof C0_rng; lia. apply wd_ok. Qed.
Lemma Dn_ok : words_ok Dn.
Proof. subst Dn. unfold L5SHLU.shl_result. destruct (Z.eqb_spec C0 0). apply wn_ok. apply shl_words_ok. pose proof C0_rng; lia. apply wn_ok. Qed.
Lemma val_shl_result ws : words_ok ws -> BigFactsBase.val (L5SHLU.shl_result ws C0) = 2 ^ C0 * BigFactsBase.val ws.
Proof.
  intros Wo. unfold L5SHLU.shl_result. destruct (Z.eqb_spec C0 0) as [E|NE]. rewrite E. lia.
  apply shl_words_val. pose proof C0_rng; lia. exact Wo.
Qed.
Lemma D_rlen_pos : (1 <= rlen D)%nat.
Proof.
  apply L5WB.rlen_pos_of_val. subst D. rewrite (val_shl_result wd wd_ok).
  pose proof (L5WB.val_pos_of_nonzero wd (nd - 1) wd_ok ltac:(rewrite wd_len; lia) TOPnz). pose proof (Z.pow_pos_nonneg 2 C0 ltac:(lia) ltac:(pose proof C0_rng; lia)). nia.
Qed.
Lemma Dn_rlen_pos : (2 <= nd)%nat -> (1 <= rlen Dn)%nat.
Proof.
  intros H2. destruct (NN2 H2) as [_ (i & Hi & Hnz)]. apply L5WB.rlen_pos_of_val. subst Dn. rewrite (val_shl_result wn wn_ok).
  pose proof (L5WB.val_pos_of_nonzero wn i wn_ok ltac:(rewrite wn_len; exact Hi) Hnz). pose proof (Z.pow_pos_nonneg 2 C0 ltac:(lia) ltac:(pose proof C0_rng; lia)). nia.
Qed.
Lemma rlen_D_le : (rlen D <= S nd)%nat. Proof using M0 od on px bd bn wd wn OLd Hnd TOPsm Hnn NN2. pose proof (rlen_le D). rewrite D_len in H. destruct (C0 =? 0); lia. Qed.
Lemma rlen_Dn_le : (rlen Dn <= S nn)%nat. Proof using M0 od on px bd bn wd wn Hnd TOPsm OLn Hnn NN2. pose proof (rlen_le Dn). rewrite Dn_len in H. destruct (C0 =? 0); lia. Qed.

(* [comment removed for export] *)
Lemma bd_shape : match L5.bo_st bd with L5.BInl _ _ => L5.bo_dyn bd = false /\ (nd <= 2)%nat | L5.BDyn cap q => L5.bo_dyn bd = true /\ Z.of_nat nd <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 end.
Proof.
  destruct bd as [fb len sto]. destruct OBd as (_ & _ & _ & ST). unfold L5.bo_dyn. cbn [L5.bo_st L5.bo_fb L5.bo_len] in *. subst nd. cbn [L5.bo_len].
  destruct sto as [v0 v1|cap q]. destruct ST as (B0 & _ & _ & Hl & _). split. exact B0. exact Hl.
  destruct ST as (B0 & _ & _ & Hlc & Hc & Q8 & Qlo & Qhi). repeat split; assumption || lia.
Qed.
Lemma bn_shape : match L5.bo_st bn with L5.BInl _ _ => L5.bo_dyn bn = false /\ (nn <= 2)%nat | L5.BDyn cap q => L5.bo_dyn bn = true /\ Z.of_nat nn <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 end.
Proof.
  destruct bn as [fb len sto]. destruct OBn as (_ & _ & _ & ST). unfold L5.bo_dyn. cbn [L5.bo_st L5.bo_fb L5.bo_len] in *. subst nn. cbn [L5.bo_len].
  destruct sto as [v0 v1|cap q]. destruct ST as (B0 & _ & _ & Hl & _). split. exact B0. exact Hl.
  destruct ST as (B0 & _ & _ & Hlc & Hc & Q8 & Qlo & Qhi). repeat split; assumption || lia.
Qed.

(* [comment removed for export] *)
Definition limb_loc (b : L5.bigobj) (o : Z) (g : growth) (st' : L5.bstore) (q : Z) (cap : Z) : Prop :=
  match st' with
  | L5.BDyn cap' q' => cap' = cap /\ q' = q /\ In (q, 8 * cap) (blocks_of g ++ LB) /\
                       match g with Same => L5.bo_st b = L5.BDyn cap q | Grown A c => q = A /\ cap = 8 /\ c = 8 /\ L5.bo_dyn b = false end
  | L5.BInl _ _ => g = Same /\ L5.bo_dyn b = false /\ q = o + 16 /\ cap = 2
  end.

Lemma limb_loc_of_after M o b rw g st' :
  (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
  match L5.bo_st b with L5.BInl _ _ => L5.bo_dyn b = false | L5.BDyn _ _ => L5.bo_dyn b = true end ->
  obj_after M o b rw g st' -> exists q cap, limb_loc b o g st' q cap.
Proof.
  intros BLK SH (_ & _ & _ & _ & _ & GM). destruct g as [|A c].
  - destruct (L5.bo_st b) as [v0 v1|cap q] eqn:E; destruct st' as [v0' v1'|cap' q']; try contradiction.
    + exists (o + 16), 2. cbn. repeat split; auto.
    + destruct GM as [-> ->]. exists q, cap. cbn. repeat split; auto; apply BLK; exact E.
  - destruct GM as (ND & C8 & ->). exists A, c. cbn. subst c. repeat split; auto.
Qed.

(* [comment removed for export] *)
Lemma mem_eq (M M' : word -> option byte) : (forall a, M' a = M a) -> M' = M.
Proof. intros H. apply functional_extensionality. exact H. Qed.

Lemma spok0 : spok sp. Proof using L M0 od on px sp bd bn wd wn STK Hnd TOPsm Hnn NN2 Aod Aon Sod Son Hod P4 Spx. pose proof stk0. split. lia. sclia. Qed.
Lemma blocks_apart_app A n l1 l2 : blocks_apart A n (l1 ++ l2) -> blocks_apart A n l2.
Proof. intros H b Hb. apply H. apply in_app_iff. right; exact Hb. Qed.


(* [comment removed for export] *)
Lemma hp_defined_stack M a n : L5C.hpres L LB sp NORM_SCR W M0 M -> sp <= a -> a + n <= 2 ^ 64 -> L5.defined M0 a n -> L5.defined M a n.
Proof using L LY M0 LB od on px sp bd bn wd wn STK Hnd TOPsm Hnn NN2 Aod Aon Sod Son P4 Spx.
  intros HP Ha Hn D0 i Hi. pose proof stk0 as (_ & SLO & _ & WND & _). pose proof ERRNOV.
  eapply (L5C.hpres_cdef L LB sp NORM_SCR W M0 M). exact HP. sclia.
  right; left. sclia. unfold in_errno; sclia. apply D0. exact Hi.
Qed.
Lemma hp_defined_block LBx crx Mx VMx M A m a n :
  hi_heap HI LBx crx Mx VMx -> In (A, m) LB -> In (A, m) LBx ->
  L5C.hpres L LB sp NORM_SCR W M0 M -> A <= a -> a + n <= A + m -> L5.defined M0 a n -> L5.defined M a n.
Proof.
  intros HHx HinLB Hin HP Ha Hn D0 i Hi. pose proof (LBdef _ _ _ _ HHx A m Hin) as (_ & LO & HIb). pose proof IMG. pose proof IMGLO. pose proof ERRNOV. pose proof SPTOP.
  eapply (L5C.hpres_cdef L LB sp NORM_SCR W M0 M). exact HP. lia.
  left. exists (A, m). split. exact HinLB. cbn. lia. unfold in_errno; lia. apply D0. exact Hi.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage4 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit)
      (gd gn : growth) (std stn : L5.bstore) (qd capd qn capn : Z) :
  SEC = true ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 on ->
  (forall i, In i cs_pass -> getr R (reg i) = getr R0 (reg i)) ->
  model_but_vm model0 model -> hi_heap HI LB3 cr3 M (m_vmmaps model) ->
  saved M sp R0 -> L5.defined M (sp - NORM_SCR) NORM_SCR ->
  L5.u32_at RSEGS M px C0 ->
  obj_after M od bd (norm_words wd C0 true) gd std -> limb_loc bd od gd std qd capd -> (match std with L5.BDyn _ _ => True | _ => False end) ->
  obj_after M on bn Dn gn stn -> limb_loc bn on gn stn qn capn -> (match stn with L5.BDyn _ _ => True | _ => False end) ->
  Z.of_nat (rlen Dn) + 1 <= capn -> apart qd (8 * capd) qn (8 * capn) ->
  LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = debits L cr (blocks_of gn ++ blocks_of gd) ->
  (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M A (8 * cap) end) ->
  (match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M A (8 * cap) end) ->
  L5C.hpres L LB sp NORM_SCR W M0 M ->
  srealizes RSEGS SCFG (cfg R AFTER3 M model) K.
Proof using SCFG_P L HI LY HIok RESIZE R0 M0 model0 K LB cr od on px sp r bd bn wd wn HH0 MOK0 HK0 G1 RA G2 G4 STK OBd OLd Hnd TOPnz TOPsm OBn OLn Hnn NN2 Aod Aon Sod Son Hod Hon APdn DEFn P4 Spx Hpx APpn BLKd BLKn APB SECcap CR KONT.
  intros HSEC H2 H8 PASS MBV HH SV DEF PX OAd LLd SDd OAn LLn SDn CAPn APQ ELB ECR FRd FRn HP.
  pose proof stk0 as (A16 & SLO & SHI & STOP & _). pose proof IMG as IMG. pose proof ERRNO as ERRNO. pose proof spok0 as SP.
  assert (SPlo: hl_sptop L - 8388608 + 64 <= sp) by fsclia.
  pose proof (LBhi _ _ _ _ HH) as LBhi3.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  assert (Hnd2: (2 <= nd)%nat). { unfold SEC, second in HSEC. apply andb_prop in HSEC. destruct HSEC as [X _]. apply Nat.leb_le in X. exact X. }
  pose proof (Dn_rlen_pos Hnd2) as RPn. pose proof rlen_Dn_le as RLn. pose proof Dn_ok as DOK. pose proof Dn_len as DLEN.
  (* [comment removed for export] *)
  destruct stn as [v0 v1|capn' qn']; [contradiction|]. destruct LLn as (-> & -> & INn & GNn).
  destruct std as [u0 u1|capd' qd']; [contradiction|]. destruct LLd as (-> & -> & INd & GNd).
  pose proof bn_shape as BNS. pose proof bd_shape as BDS.
  assert (INn3: In (qn, 8 * capn) LB3). { subst LB3. apply in_app_iff in INn. apply in_app_iff. destruct INn. left; assumption. right. apply in_app_iff. right; assumption. }
  assert (INd3: In (qd, 8 * capd) LB3). { subst LB3. apply in_app_iff in INd. apply in_app_iff. destruct INd. right; apply in_app_iff; left; assumption. right. apply in_app_iff. right; assumption. }
  pose proof (LBdef _ _ _ _ HH qn (8 * capn) INn3) as (BDn & BLOn & BHIn).
  pose proof (LBdef _ _ _ _ HH qd (8 * capd) INd3) as (BDd & BLOd & BHId). rewrite IMG, IMGLO in BLOn, BLOd.
  (* [comment removed for export] *)
  unfold obj_after in OAn. cbv zeta in OAn. destruct OAn as (WOn & NLEn & OBn2 & OLn2 & CAPm & GMn).
  replace (rlen Dn =? 0)%nat with false in OBn2, OLn2 by (symmetry; apply Nat.eqb_neq; flia).
  set (fbn := match gn with Same => L5.bo_fb bn | Grown _ _ => Z.lor (L5.bo_fb bn) 1 end) in *.
  pose proof OBn2 as (Pn0 & Hfbn & Pn8 & Bn1 & Pn16 & Pn24 & CAPn2 & Ccapn & Qn8 & QnLO & QnHI & QnHAP). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Pn0, Hfbn, Pn8, Bn1, Pn16, Pn24, CAPn2, Ccapn, Qn8, QnLO, QnHI.
  (* [comment removed for export] *)
  destruct (nzG_conc fx R0 R M sp on SP ltac:(flia) H2 H8) as (fx1 & R1 & M1 & MS1 & K1 & (A1 & A2 & A10 & A11) & MM1 & MG1).
  pose proof (mem_eq M M1 MM1) as EM1. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (mulm_ok fx1 R1 M model K LB3 cr3 on (sp - 64) AFTER4 MAXW (L5.BO fbn (rlen Dn) (L5.BDyn capn qn)) (firstn (rlen Dn) Dn) HH MOK HK0).
  + rewrite r10. exact A10.
  + rewrite r11. exact A11.
  + unfold MAXW. flia.
  + rewrite r1. exact A1.
  + split. unfold AFTER4. flia. reflexivity.
  + rewrite r2. exact A2.
  + rewrite r4. rewrite (K1 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (PASS 4%nat) by (cbn; tauto). exact G4.
  + split. { replace (sp - 64) with (sp + (-4) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. flia. uSCR. eapply L5.defined_sub. exact DEF. flia. flia.
  + exact OBn2.
  + apply (obj_limbs_prefix M fbn (length Dn)). exact OLn2. pose proof (rlen_le Dn). flia. exact I.
  + cbn [L5.bo_len]. flia.
  + exact Aon. + flia. + flia.
  + apply (hp_defined_stack M on 32 HP). flia. flia. exact DEFn.
  + cbn [L5.bo_dyn L5.bo_cap L5.bo_st L5.bo_len]. intros _. flia.
  + cbn [L5.bo_len L5.bo_dyn L5.bo_fb]. intros _ ND. unfold L5.bo_dyn in ND. cbn [L5.bo_fb] in ND. congruence.
  + cbn [L5.bo_st]. intros cap q E. inversion E; subst. exact INn3.
  + (* [comment removed for export] *)
    intros fx5 R5 M5 model5 g5 LB5 cr5 POST MBV5 HH5.
    unfold L5MULMU.mulm_post in POST. cbv zeta in POST. cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn L5.bo_data] in POST.
    destruct POST as (RP5 & B10 & LRW & WRW & st5 & OB5 & OL5 & NLE5 & GG).
    set (Fn := mulw_words (firstn (rlen Dn) Dn) MAXW) in *.
    destruct g5 as [|A5 c5].
    2:{ exfalso. destruct GG as (ND & _). unfold L5.bo_dyn in ND. cbn [L5.bo_fb] in ND. congruence. }
    destruct GG as (_ & -> & -> & STM & HP5). destruct st5 as [z0 z1|capn5 qn5]; [contradiction|]. destruct STM as [-> ->].
    pose proof (L5C.halted_but_vm _ _ MBV5) as Mh5. rewrite Mh in Mh5. pose proof (L5C.lazy_but_vm _ _ MBV5) as Ml5. rewrite Ml in Ml5.
    (* [comment removed for export] *)
    assert (LEN8: 8 * Z.of_nat (S (rlen Dn)) <= 8 * capn) by flia.
    assert (KST: forall a, sp - 64 <= a < 2 ^ 64 -> ~ (on <= a < on + 32) -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn. flia. apply L5C.outside_nil. }
    assert (KBD: forall a, qd <= a < qd + 8 * capd -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). eapply L5C.kept_block. exact INd3. flia. flia. flia. rewrite ERRNOV. flia.
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn. unfold apart in APQ. flia. apply L5C.outside_nil. }
    assert (SV5: saved M5 sp R0).
    { destruct SV as (S1 & S2 & S3 & S4 & S5 & S6). unfold apart in APdn.
      repeat split; (eapply u64_at_agree1; [intros i Hi; apply KST; flia | flia | flia | assumption]). }
    assert (DEF5: L5.defined M5 (sp - NORM_SCR) NORM_SCR).
    { intros i Hi. destruct (Z_lt_le_dec (sp - NORM_SCR + i) (sp - 64)) as [X|X].
      - pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP5) as D5. uSCR.
        replace (sp - (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))) + i) with (sp - 64 - (144 + (64 + (48 + (64 + (16 + 8224))))) + i) by flia. apply D5. flia.
      - rewrite KST. apply DEF. flia. fsclia. unfold apart in APdn. fsclia. }
    assert (PX5: L5.u32_at RSEGS M5 px C0). { eapply u32_at_agree1. intros i Hi. apply KST. flia. unfold apart in APpn. flia. flia. flia. exact PX. }
    (* [comment removed for export] *)
    assert (OAd5: obj_after M5 od bd (norm_words wd C0 true) gd (L5.BDyn capd qd)).
    { unfold obj_after in OAd |- *. cbv zeta in OAd. cbv zeta. destruct OAd as (WOd & NLEd & OBd2 & OLd2 & CAPmd & GMd).
      split. exact WOd. split. exact NLEd.
      split. { eapply (L5C.big_at_agree RSEGS M M5). intros i Hi. apply KST. flia. unfold apart in APdn. flia. flia. flia. exact OBd2. }
      split. { destruct OLd2 as (L1 & L2 & L3). split. exact L1. split. exact L2. cbn [L5.bo_st L5.bo_len] in L3 |- *.
               eapply (L5C.limbs_at_agree RSEGS M M5). 2: flia. 3: exact L3. intros i Hi. apply KBD. rewrite L1 in Hi. flia. rewrite L1. flia. }
      split. exact CAPmd. exact GMd. }
    (* [comment removed for export] *)
    assert (FnL: length Fn = S (rlen Dn)). { subst Fn. rewrite mulw_words_length, length_firstn. pose proof (rlen_le Dn). rewrite Nat.min_l by flia. reflexivity. }
    assert (OAn5: obj_after M5 on bn (norm_words wn C0 true) gn (L5.BDyn capn qn)).
    { unfold obj_after, norm_words. cbv zeta. fold Dn. fold Fn. rewrite FnL. fold fbn.
      split. exact WRW. split. exact NLE5. split. exact OB5. split. exact OL5. split. cbn in CAPm |- *. flia.
      destruct gn as [|An cn]. cbn in GNn. rewrite GNn. split; reflexivity. destruct GNn as (-> & -> & -> & ND). split. exact ND. split; reflexivity. }
    (* [comment removed for export] *)
    assert (FRd5: match gd with Same => True | Grown A cap => L5C.fresh_block L LB M5 A (8 * cap) end).
    { destruct gd as [|Ad cd]. exact I. destruct FRd as (BR & BA & BDEF). split. exact BR. split. exact BA.
      cbn in GNd. destruct GNd as (-> & -> & -> & _).
      intros i Hi. eapply (L5C.hpres_cdef _ _ _ _ _ _ _ (Ad + i) HP5). flia. left. exists (Ad, 8 * 8). split. exact INd3. cbn; flia.
      unfold in_errno; rewrite ERRNOV; flia. apply BDEF. flia. }
    assert (FRn5: match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M5 A (8 * cap) end).
    { destruct gn as [|An cn]. exact I. destruct FRn as (BR & BA & BDEF). split. exact BR. split. exact BA.
      cbn in GNn. destruct GNn as (-> & -> & -> & _).
      intros i Hi. eapply (L5C.hpres_cdef _ _ _ _ _ _ _ (An + i) HP5). flia. left. exists (An, 8 * 8). split. exact INn3. cbn; flia.
      unfold in_errno; rewrite ERRNOV; flia. apply BDEF. flia. }
    (* [comment removed for export] *)
    assert (HPA: L5C.hpres L LB sp NORM_SCR W M0 M5).
    { eapply (L5HP.hpres_trans L LB LB3). exact HP. exact HP5.
      - intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LB3. rewrite !in_app_iff. tauto. } fsclia. flia.
        intros OW. apply L5C.outside_cons. { unfold L5.in_rng; cbn. apply (L5HP.outside_in _ _ on 32 OW). unfold W, norm_W. cbn. tauto. }
        apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng; cbn.
        destruct gn as [|An cn]; cbn in GNn.
        + (* [comment removed for export] *)
          intros X. apply (L5HP.outside_in _ _ qn (8 * capn) OW). 2: flia.
          unfold W, norm_W, dyn_area. rewrite GNn. rewrite !in_app_iff. cbn. tauto.
        + (* [comment removed for export] *)
          destruct GNn as (-> & -> & -> & _). destruct FRn as (BR & BA & _).
          pose proof (L5C.kept_not_fresh L LB sp NORM_SCR W a An 64 KA (blocks_apart_app _ _ _ _ BA) ltac:(destruct BR as (_ & B1 & _); exact B1) ltac:(destruct BR as (_&_&_&_&B4); exact B4) (LBhi _ _ _ _ HH0)). flia.
      - intros b Hb. subst LB3. rewrite !in_app_iff. tauto.
      - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
    (* [comment removed for export] *)
    assert (E2: getr R5 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite (preserved_sregs R1 R5 2 RP5) by (cbn; tauto). exact A2. }
    assert (WR5: L5.writable RSEGS M5 (sp - 64) 64).
    { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF5. fsclia. fsclia. fsclia. fsclia. }
    destruct (nzH_conc fx5 R0 R5 M5 sp SP WR5 SV5 E2) as (fx7 & R7 & M7 & MS7 & K7 & RET7 & MM7 & G7).
    pose proof (mem_eq M5 M7 MM7) as EM7. subst M7.
    pose proof RET7 as (T1 & T2 & T8 & T9 & T18 & T19 & T20 & T10).
    pose proof RA as [Hr He].
    pose proof (ret_22d54 fx7 R7 M5 r ltac:(rewrite T1, <- r1; exact G1) Hr He) as MS8.
    unfold cfg, L5REDU.cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh5. exact Ml5. eapply msteps_trans. exact MS7. exact MS8.
    apply (KONT fx7 R7 M5 model5 C0 gd gn LB3 cr3).
    * unfold norm_post. cbv zeta. fold nd. fold w0. fold C0. fold D. fold SEC. rewrite HSEC.
      split. { apply (preserved_of_ret R0 R7 sp 1). rewrite <- r2. exact G2. exact RET7.
               intros i Hi. rewrite (K7 i) by (apply (L5K.incl_b cs_pass KSH ltac:(vm_compute; reflexivity)); exact Hi).
               rewrite (preserved_sregs R1 R5 i RP5) by (revert Hi; apply (L5K.incl_b cs_pass cs_all ltac:(vm_compute; reflexivity))).
               rewrite (K1 i) by (apply (L5K.incl_b cs_pass KSG ltac:(vm_compute; reflexivity)); exact Hi). apply PASS. exact Hi. }
      split. reflexivity. split. { pose proof C0_rng; flia. } split. { pose proof C0_rng. subst w0. flia. }
      split. { rewrite r10. exact T10. }
      split. exact PX5.
      split. { exists (L5.BDyn capd qd), (L5.BDyn capn qn). split. exact OAd5. exact OAn5. }
      split. exact ELB. split. exact ECR. split. exact FRd5. split. exact FRn5. split. exact HPA.
      split; [destruct gd; [exact I | right; reflexivity] | destruct gn; [exact I | right; reflexivity]].
    * eapply L5C.model_but_vm_trans. exact MBV. exact MBV5.
    * exact HH5.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma stage3 (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit)
      (gd gn : growth) (std stn : L5.bstore) (qd capd qn capn : Z) :
  SEC = true ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 on -> getr R (reg 9) = Z_to_bv 64 od ->
  (forall i, In i cs_pass -> getr R (reg i) = getr R0 (reg i)) ->
  model_but_vm model0 model -> hi_heap HI LB3 cr3 M (m_vmmaps model) ->
  saved M sp R0 -> L5.defined M (sp - NORM_SCR) NORM_SCR ->
  L5.u32_at RSEGS M px C0 ->
  obj_after M od bd D gd std -> limb_loc bd od gd std qd capd -> (match std with L5.BDyn _ _ => True | _ => False end) ->
  obj_after M on bn Dn gn stn -> limb_loc bn on gn stn qn capn -> (match stn with L5.BDyn _ _ => True | _ => False end) ->
  Z.of_nat (rlen D) + 1 <= capd -> Z.of_nat (rlen Dn) + 1 <= capn -> apart qd (8 * capd) qn (8 * capn) ->
  LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = debits L cr (blocks_of gn ++ blocks_of gd) ->
  (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M A (8 * cap) end) ->
  (match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M A (8 * cap) end) ->
  L5C.hpres L LB sp NORM_SCR W M0 M ->
  srealizes RSEGS SCFG (cfg R F M model) K.
Proof using SCFG_P L HI LY HIok RESIZE R0 M0 model0 K LB cr od on px sp r bd bn wd wn HH0 MOK0 HK0 G1 RA G2 G4 STK OBd OLd Hnd TOPnz TOPsm OBn OLn Hnn NN2 Aod Aon Sod Son Hod Hon APdn DEFd DEFn P4 Spx Hpx APpd APpn BLKd BLKn APB SECcap CR KONT.
  intros HSEC H2 H8 H9 PASS MBV HH SV DEF PX OAd LLd SDd OAn LLn SDn CAPd CAPn APQ ELB ECR FRd FRn HP.
  pose proof stk0 as (A16 & SLO & SHI & STOP & _). pose proof IMG as IMG. pose proof ERRNO as ERRNO. pose proof spok0 as SP.
  assert (SPlo: hl_sptop L - 8388608 + 64 <= sp) by fsclia.
  pose proof (LBhi _ _ _ _ HH) as LBhi3.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof D_rlen_pos as RPd. pose proof rlen_D_le as RLd. pose proof D_ok as DOK. pose proof D_len as DLEN.
  (* [comment removed for export] *)
  destruct stn as [v0 v1|capn' qn']; [contradiction|]. pose proof LLn as LLn0. destruct LLn as (-> & -> & INn & GNn).
  destruct std as [u0 u1|capd' qd']; [contradiction|]. pose proof LLd as LLd0. destruct LLd as (-> & -> & INd & GNd).
  assert (INn3: In (qn, 8 * capn) LB3). { subst LB3. apply in_app_iff in INn. apply in_app_iff. destruct INn. left; assumption. right. apply in_app_iff. right; assumption. }
  assert (INd3: In (qd, 8 * capd) LB3). { subst LB3. apply in_app_iff in INd. apply in_app_iff. destruct INd. right; apply in_app_iff; left; assumption. right. apply in_app_iff. right; assumption. }
  pose proof (LBdef _ _ _ _ HH qn (8 * capn) INn3) as (BDn & BLOn & BHIn).
  pose proof (LBdef _ _ _ _ HH qd (8 * capd) INd3) as (BDd & BLOd & BHId). rewrite IMG, IMGLO in BLOn, BLOd.
  (* [comment removed for export] *)
  pose proof OAd as OAd0. unfold obj_after in OAd. cbv zeta in OAd. destruct OAd as (WOd & NLEd & OBd2 & OLd2 & CAPm & GMd).
  replace (rlen D =? 0)%nat with false in OBd2, OLd2 by (symmetry; apply Nat.eqb_neq; flia).
  set (fbd := match gd with Same => L5.bo_fb bd | Grown _ _ => Z.lor (L5.bo_fb bd) 1 end) in *.
  pose proof OBd2 as (Pd0 & Hfbd & Pd8 & Bd1 & Pd16 & Pd24 & CAPd2 & Ccapd & Qd8 & QdLO & QdHI & QdHAP). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Pd0, Hfbd, Pd8, Bd1, Pd16, Pd24, CAPd2, Ccapd, Qd8, QdLO, QdHI.
  (* [comment removed for export] *)
  destruct (nzF_conc fx R0 R M sp od SP ltac:(flia) H2 H9) as (fx1 & R1 & M1 & MS1 & K1 & (A1 & A2 & A10 & A11) & MM1 & MG1).
  pose proof (mem_eq M M1 MM1) as EM1. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (mulm_ok fx1 R1 M model K LB3 cr3 od (sp - 64) AFTER3 MAXW (L5.BO fbd (rlen D) (L5.BDyn capd qd)) (firstn (rlen D) D) HH MOK HK0).
  + rewrite r10. exact A10.
  + rewrite r11. exact A11.
  + unfold MAXW. flia.
  + rewrite r1. exact A1.
  + split. unfold AFTER3. flia. reflexivity.
  + rewrite r2. exact A2.
  + rewrite r4. rewrite (K1 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (PASS 4%nat) by (cbn; tauto). exact G4.
  + split. { replace (sp - 64) with (sp + (-4) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. flia. uSCR. eapply L5.defined_sub. exact DEF. flia. flia.
  + exact OBd2.
  + apply (obj_limbs_prefix M fbd (length D)). exact OLd2. pose proof (rlen_le D). flia. exact I.
  + cbn [L5.bo_len]. flia.
  + exact Aod. + flia. + flia.
  + apply (hp_defined_stack M od 32 HP). flia. flia. exact DEFd.
  + cbn [L5.bo_dyn L5.bo_cap L5.bo_st L5.bo_len]. intros _. flia.
  + cbn [L5.bo_len L5.bo_dyn L5.bo_fb]. intros _ ND. unfold L5.bo_dyn in ND. cbn [L5.bo_fb] in ND. congruence.
  + cbn [L5.bo_st]. intros cap q E. inversion E; subst. exact INd3.
  + (* [comment removed for export] *)
    intros fx5 R5 M5 model5 g5 LB5 cr5 POST MBV5 HH5.
    unfold L5MULMU.mulm_post in POST. cbv zeta in POST. cbn [L5.bo_len L5.bo_fb L5.bo_st L5.bo_dyn L5.bo_data] in POST.
    destruct POST as (RP5 & B10 & LRW & WRW & st5 & OB5 & OL5 & NLE5 & GG).
    set (Fd := mulw_words (firstn (rlen D) D) MAXW) in *.
    destruct g5 as [|A5 c5].
    2:{ exfalso. destruct GG as (ND & _). unfold L5.bo_dyn in ND. cbn [L5.bo_fb] in ND. congruence. }
    destruct GG as (_ & -> & -> & STM & HP5). destruct st5 as [z0 z1|capd5 qd5]; [contradiction|]. destruct STM as [-> ->].
    assert (LEN8: 8 * Z.of_nat (S (rlen D)) <= 8 * capd) by flia.
    assert (KST: forall a, sp - 64 <= a < 2 ^ 64 -> ~ (od <= a < od + 32) -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn. flia. apply L5C.outside_nil. }
    assert (KBN: forall a, qn <= a < qn + 8 * capn -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). eapply L5C.kept_block. exact INn3. flia. flia. flia. rewrite ERRNOV. flia.
      apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn. unfold apart in APQ. flia. apply L5C.outside_nil. }
    assert (SV5: saved M5 sp R0).
    { destruct SV as (S1 & S2 & S3 & S4 & S5 & S6). unfold apart in APdn.
      repeat split; (eapply u64_at_agree1; [intros i Hi; apply KST; flia | flia | flia | assumption]). }
    assert (DEF5: L5.defined M5 (sp - NORM_SCR) NORM_SCR).
    { intros i Hi. destruct (Z_lt_le_dec (sp - NORM_SCR + i) (sp - 64)) as [X|X].
      - pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP5) as D5. uSCR.
        replace (sp - (64 + (144 + (64 + (48 + (64 + (16 + 8224)))))) + i) with (sp - 64 - (144 + (64 + (48 + (64 + (16 + 8224))))) + i) by flia. apply D5. flia.
      - rewrite KST. apply DEF. flia. fsclia. unfold apart in APdn. fsclia. }
    assert (PX5: L5.u32_at RSEGS M5 px C0). { eapply u32_at_agree1. intros i Hi. apply KST. flia. unfold apart in APpd. flia. flia. flia. exact PX. }
    (* [comment removed for export] *)
    assert (OAn5: obj_after M5 on bn Dn gn (L5.BDyn capn qn)).
    { unfold obj_after in OAn |- *. cbv zeta in OAn. cbv zeta. destruct OAn as (WOn & NLEn & OBn2 & OLn2 & CAPmn & GMn).
      split. exact WOn. split. exact NLEn.
      split. { eapply (L5C.big_at_agree RSEGS M M5). intros i Hi. apply KST. flia. unfold apart in APdn. flia. flia. flia. exact OBn2. }
      split. { destruct OLn2 as (L1 & L2 & L3). split. exact L1. split. exact L2. cbn [L5.bo_st L5.bo_len] in L3 |- *.
               eapply (L5C.limbs_at_agree RSEGS M M5). 2: flia. 3: exact L3. intros i Hi. apply KBN. rewrite L1 in Hi. flia. rewrite L1. flia. }
      split. exact CAPmn. exact GMn. }
    (* [comment removed for export] *)
    assert (FdL: length Fd = S (rlen D)). { subst Fd. rewrite mulw_words_length, length_firstn. pose proof (rlen_le D). rewrite Nat.min_l by flia. reflexivity. }
    assert (OAd5: obj_after M5 od bd (norm_words wd C0 true) gd (L5.BDyn capd qd)).
    { unfold obj_after, norm_words. cbv zeta. fold D. fold Fd. rewrite FdL. fold fbd.
      split. exact WRW. split. exact NLE5. split. exact OB5. split. exact OL5. split. cbn in CAPm |- *. flia.
      destruct gd as [|Ad cd]. cbn in GNd. rewrite GNd. split; reflexivity. destruct GNd as (-> & -> & -> & ND). split. exact ND. split; reflexivity. }
    assert (FRd5: match gd with Same => True | Grown A cap => L5C.fresh_block L LB M5 A (8 * cap) end).
    { destruct gd as [|Ad cd]. exact I. destruct FRd as (BR & BA & BDEF). split. exact BR. split. exact BA.
      cbn in GNd. destruct GNd as (-> & -> & -> & _).
      intros i Hi. eapply (L5C.hpres_cdef _ _ _ _ _ _ _ (Ad + i) HP5). flia. left. exists (Ad, 8 * 8). split. exact INd3. cbn; flia.
      unfold in_errno; rewrite ERRNOV; flia. apply BDEF. flia. }
    assert (FRn5: match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M5 A (8 * cap) end).
    { destruct gn as [|An cn]. exact I. destruct FRn as (BR & BA & BDEF). split. exact BR. split. exact BA.
      cbn in GNn. destruct GNn as (-> & -> & -> & _).
      intros i Hi. eapply (L5C.hpres_cdef _ _ _ _ _ _ _ (An + i) HP5). flia. left. exists (An, 8 * 8). split. exact INn3. cbn; flia.
      unfold in_errno; rewrite ERRNOV; flia. apply BDEF. flia. }
    assert (HPA: L5C.hpres L LB sp NORM_SCR W M0 M5).
    { eapply (L5HP.hpres_trans L LB LB3). exact HP. exact HP5.
      - intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LB3. rewrite !in_app_iff. tauto. } fsclia. flia.
        intros OW. apply L5C.outside_cons. { unfold L5.in_rng; cbn. apply (L5HP.outside_in _ _ od 32 OW). unfold W, norm_W. cbn. tauto. }
        apply L5C.outside_cons. 2: apply L5C.outside_nil. unfold L5.in_rng; cbn.
        destruct gd as [|Ad cd]; cbn in GNd.
        + intros X. apply (L5HP.outside_in _ _ qd (8 * capd) OW). 2: flia.
          unfold W, norm_W, dyn_area. rewrite GNd. rewrite !in_app_iff. cbn. tauto.
        + destruct GNd as (-> & -> & -> & _). destruct FRd as (BR & BA & _).
          pose proof (L5C.kept_not_fresh L LB sp NORM_SCR W a Ad 64 KA BA ltac:(destruct BR as (_ & B1 & _); exact B1) ltac:(destruct BR as (_&_&_&_&B4); exact B4) (LBhi _ _ _ _ HH0)). flia.
      - intros b Hb. subst LB3. rewrite !in_app_iff. tauto.
      - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
    assert (E2: getr R5 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite (preserved_sregs R1 R5 2 RP5) by (cbn; tauto). exact A2. }
    assert (E8: getr R5 (reg 8) = Z_to_bv 64 on). { rewrite (preserved_sregs R1 R5 8 RP5) by (cbn; tauto). rewrite (K1 8%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H8. }
    unfold L5REDU.cfg.
    eapply (stage4 fx5 R5 M5 model5 LB3 cr3 gd gn (L5.BDyn capd qd) (L5.BDyn capn qn) qd capd qn capn HSEC E2 E8).
    * intros i Hi. rewrite (preserved_sregs R1 R5 i RP5) by (revert Hi; apply (L5K.incl_b cs_pass cs_all ltac:(vm_compute; reflexivity))).
      rewrite (K1 i) by (apply (L5K.incl_b cs_pass KSF ltac:(vm_compute; reflexivity)); exact Hi). apply PASS. exact Hi.
    * eapply L5C.model_but_vm_trans. exact MBV. exact MBV5.
    * exact HH5.
    * exact SV5. * exact DEF5. * exact PX5.
    * exact OAd5. * exact LLd0. * exact I.
    * exact OAn5. * exact LLn0. * exact I.
    * exact CAPn. * exact APQ. * exact ELB. * exact ECR. * exact FRd5. * exact FRn5. * exact HPA.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma finish_false (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit)
      (gd gn : growth) (std stn : L5.bstore) :
  SEC = false ->
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> (forall i, In i cs_pass -> getr R (reg i) = getr R0 (reg i)) ->
  model_but_vm model0 model -> hi_heap HI LB3 cr3 M (m_vmmaps model) ->
  saved M sp R0 -> L5.defined M (sp - NORM_SCR) NORM_SCR -> L5.u32_at RSEGS M px C0 ->
  obj_after M od bd D gd std -> obj_after M on bn Dn gn stn ->
  LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = debits L cr (blocks_of gn ++ blocks_of gd) ->
  (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M A (8 * cap) end) ->
  (match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M A (8 * cap) end) ->
  L5C.hpres L LB sp NORM_SCR W M0 M ->
  (match gd with Same => True | Grown _ _ => (3 <= length D)%nat end) ->
  (match gn with Same => True | Grown _ _ => (3 <= length Dn)%nat end) ->
  srealizes RSEGS SCFG (cfg R L5NORMU.K M model) K.
Proof using SCFG_P L HI R0 M0 model0 K LB cr od on px sp r bd bn wd wn MOK0 G1 RA G2 STK OLd Hnd TOPnz TOPsm Hnn NN2 Aod Aon Sod Son Hod P4 Spx KONT.
  intros HSEC H2 PASS MBV HH SV DEF PX OAd OAn ELB ECR FRd FRn HP GWd GWn.
  pose proof stk0 as (A16 & SLO & SHI & STOP & _). pose proof spok0 as SP.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as (Mh & Ml & _).
  assert (WR: L5.writable RSEGS M (sp - 64) 64).
  { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. fsclia. fsclia. fsclia. fsclia. }
  destruct (nzK_conc fx R0 R M sp SP WR SV H2) as (fx7 & R7 & M7 & MS7 & K7 & RET7 & MM7 & G7).
  pose proof (mem_eq M M7 MM7) as EM7. subst M7.
  pose proof RET7 as (T1 & T2 & T8 & T9 & T18 & T19 & T20 & T10).
  pose proof RA as [Hr He].
  pose proof (ret_22d54 fx7 R7 M r ltac:(rewrite T1, <- r1; exact G1) Hr He) as MS8.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. eapply msteps_trans. exact MS7. exact MS8.
  apply (KONT fx7 R7 M model C0 gd gn LB3 cr3).
  * unfold norm_post. cbv zeta. fold nd. fold w0. fold C0. fold D. fold SEC. rewrite HSEC.
    split. { apply (preserved_of_ret R0 R7 sp 0). rewrite <- r2. exact G2. exact RET7.
             intros i Hi. rewrite (K7 i) by (apply (L5K.incl_b cs_pass KSK ltac:(vm_compute; reflexivity)); exact Hi). apply PASS. exact Hi. }
    split. reflexivity. split. { pose proof C0_rng; flia. } split. { pose proof C0_rng. subst w0. flia. }
    split. { rewrite r10. exact T10. }
    split. exact PX.
    split. { exists std, stn. split. exact OAd. exact OAn. }
    split. exact ELB. split. exact ECR. split. exact FRd. split. exact FRn. split. exact HP.
    split; [destruct gd; [exact I | left; exact GWd] | destruct gn; [exact I | left; exact GWn]].
  * exact MBV.
  * exact HH.
Qed.

End Call.
End WithHeap.
End SCFG_1.

End L5NORMOKAU.
