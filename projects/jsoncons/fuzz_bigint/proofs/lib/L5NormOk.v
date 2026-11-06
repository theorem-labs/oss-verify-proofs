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
     Src0_code_22348_22f60 BigBranchSrc0 BigLinkBase BigLinkGlue BigLinkInlBase BigLinkDq BigLinkReduce BigClz L5Defs L5Kn
     L5Core L5CoreSpecs L5Words L5WordsB L5Reduce L5Shl L5ShlOk L5MulM L5MulMOk L5Hp L5Norm L5NormOkA.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastTauto. Local Ltac tauto := L5FastTauto.ptauto.

Module L5NORMOK.
Import L5CS. Import L5W. Import L5NORM.

Notation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Plain.M.loaded_segments)) (only parsing).
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
  intros H2 (T1 & T2 & T8 & T9 & T18 & T19 & T20 & T21 & T22 & _) KR. apply preserved_by_index. intros i Hi. cbn in Hi.
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

Local Ltac uSCR := unfold NORM_SCR, L5MULM.MULM_SCR, L5SHL.SHL_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *.
Local Ltac sclia := unfold NORM_SCR, L5MULM.MULM_SCR, L5SHL.SHL_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *; lia.
(* [comment removed for export] *)
Local Ltac prune_impl :=
  repeat match goal with
         | H : ?A -> ?B |- _ => lazymatch B with False => fail | _ => clear H end
         | H : _ <-> _ |- _ => clear H
         end.
Local Ltac flia := prune_impl; lia.
Local Ltac fsclia := prune_impl; unfold NORM_SCR, L5MULM.MULM_SCR, L5SHL.SHL_SCR, RESIZE_SCR, RESERVE_SCR, ARESERVE_SCR, OPNEW_SCR, HEAP_STACK in *; lia.

Section WithHeap.
Variables (L : heap_layout) (HI : heap_iface).
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.
Hypothesis RESIZE : resize_spec L HI.
Let shl_ok := L5SHLOK.shl_ok L HI LY HIok RESIZE.
Let mulm_ok := L5MULMOK.mulm_ok L HI LY HIok RESIZE.

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
Hypothesis SECcap : second (L5.bo_len bd) (L5SHL.shl_result wd (clz_of (nth_w wd (L5.bo_len bd - 1)))) = true ->
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
Let D : list Z := L5SHL.shl_result wd C0.
Let Dn : list Z := L5SHL.shl_result wn C0.
Let SEC : bool := second nd D.
Let W : list L5.range := norm_W od on px bd bn.

(* [comment removed for export] *)
Lemma stk0 : sp mod 16 = 0 /\ hl_sptop L - 2 ^ 23 + NORM_SCR <= sp /\ sp <= hl_sptop L /\ (0x7fff80000000 <= hl_sptop L <= 2 ^ 47) /\ L5.defined M0 (sp - NORM_SCR) NORM_SCR.
Proof. exact (@L5NORMOKA.stk0 L M0 sp STK). Qed.
Lemma IMG : hl_img_hi L = 0x91000.
Proof. exact (@L5NORMOKA.IMG L LY). Qed.
Lemma IMGLO : hl_img_lo L = 0x10000.
Proof. exact (@L5NORMOKA.IMGLO L LY). Qed.
Lemma ERRNO : hl_errno L + 4 <= 0x7fff7f800000.
Proof. exact (@L5NORMOKA.ERRNO L LY od on px bd bn wd wn Hnd TOPsm Hnn NN2). Qed.
Lemma SPTOP : 0x7fff80000000 <= hl_sptop L <= 2 ^ 47.
Proof. exact (@L5NORMOKA.SPTOP L M0 sp STK). Qed.
Lemma ERRNOV : hl_errno L = 0x70394.
Proof. exact (@L5NORMOKA.ERRNOV L LY). Qed.
Lemma LBhi : forall LBx crx M VM, hi_heap HI LBx crx M VM -> forall b, In b LBx -> fst b + snd b <= (hl_sptop L - 8388608).
Proof. exact (@L5NORMOKA.LBhi _ L HI HIok). Qed.
Lemma LBdef : forall LBx crx M VM, hi_heap HI LBx crx M VM -> forall A n, In (A, n) LBx -> L5.defined M A n /\ (4096 <= A /\ (A + n <= hl_img_lo L \/ hl_img_hi L <= A)) /\ A + n <= (hl_sptop L - 8388608).
Proof. exact (@L5NORMOKA.LBdef _ L HI HIok). Qed.
Lemma wd_len : length wd = nd.
Proof. exact (@L5NORMOKA.wd_len M0 bd wd OLd). Qed.
Lemma wn_len : length wn = nn.
Proof. exact (@L5NORMOKA.wn_len M0 bn wn OLn). Qed.
Lemma wd_ok : words_ok wd.
Proof. exact (@L5NORMOKA.wd_ok M0 bd wd OLd). Qed.
Lemma wn_ok : words_ok wn.
Proof. exact (@L5NORMOKA.wn_ok M0 bn wn OLn). Qed.
Lemma w0_rng : 1 <= w0 < 2 ^ 64.
Proof. exact (@L5NORMOKA.w0_rng M0 od on px bd bn wd wn OLd Hnd TOPnz TOPsm Hnn NN2). Qed.
Lemma C0_rng : 0 <= C0 <= 63 /\ 2 ^ 63 <= w0 * 2 ^ C0 < 2 ^ 64.
Proof. exact (@L5NORMOKA.C0_rng M0 od on px bd bn wd wn OLd Hnd TOPnz TOPsm Hnn NN2). Qed.
Lemma D_len : length D = (if C0 =? 0 then nd else S nd).
Proof. exact (@L5NORMOKA.D_len M0 bd wd OLd). Qed.
Lemma Dn_len : length Dn = (if C0 =? 0 then nn else S nn).
Proof. exact (@L5NORMOKA.Dn_len M0 bd bn wd wn OLn). Qed.
Lemma D_ok : words_ok D.
Proof. exact (@L5NORMOKA.D_ok M0 od on px bd bn wd wn OLd Hnd TOPnz TOPsm Hnn NN2). Qed.
Lemma Dn_ok : words_ok Dn.
Proof. exact (@L5NORMOKA.Dn_ok M0 od on px bd bn wd wn OLd Hnd TOPnz TOPsm OLn Hnn NN2). Qed.
Lemma val_shl_result : forall ws, words_ok ws -> BigFactsBase.val (L5SHL.shl_result ws C0) = 2 ^ C0 * BigFactsBase.val ws.
Proof. exact (@L5NORMOKA.val_shl_result M0 od on px bd bn wd wn OLd Hnd TOPnz TOPsm Hnn NN2). Qed.
Lemma D_rlen_pos : (1 <= rlen D)%nat.
Proof. exact (@L5NORMOKA.D_rlen_pos M0 od on px bd bn wd wn OLd Hnd TOPnz TOPsm Hnn NN2). Qed.
Lemma Dn_rlen_pos : (2 <= nd)%nat -> (1 <= rlen Dn)%nat.
Proof. exact (@L5NORMOKA.Dn_rlen_pos M0 od on px bd bn wd wn OLd Hnd TOPnz TOPsm OLn Hnn NN2). Qed.
Lemma rlen_D_le : (rlen D <= S nd)%nat.
Proof. exact (@L5NORMOKA.rlen_D_le M0 od on px bd bn wd wn OLd Hnd TOPsm Hnn NN2). Qed.
Lemma rlen_Dn_le : (rlen Dn <= S nn)%nat.
Proof. exact (@L5NORMOKA.rlen_Dn_le M0 od on px bd bn wd wn Hnd TOPsm OLn Hnn NN2). Qed.
Lemma bd_shape : match L5.bo_st bd with L5.BInl _ _ => L5.bo_dyn bd = false /\ (nd <= 2)%nat | L5.BDyn cap q => L5.bo_dyn bd = true /\ Z.of_nat nd <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 end.
Proof. exact (@L5NORMOKA.bd_shape _ L HI R0 M0 model0 K LB cr od on px sp r bd bn wd wn OBd OLd Hnd TOPnz TOPsm Hnn NN2 BLKd APB SECcap CR KONT). Qed.
Lemma bn_shape : match L5.bo_st bn with L5.BInl _ _ => L5.bo_dyn bn = false /\ (nn <= 2)%nat | L5.BDyn cap q => L5.bo_dyn bn = true /\ Z.of_nat nn <= cap /\ 1 <= cap <= 2 ^ 27 /\ q mod 8 = 0 /\ 4096 <= q /\ q + 8 * cap <= 2 ^ 47 end.
Proof. exact (@L5NORMOKA.bn_shape _ L HI R0 M0 model0 K LB cr od on px sp r bd bn wd wn Hnd TOPsm OBn OLn Hnn NN2 BLKn APB SECcap CR KONT). Qed.
Definition limb_loc := @L5NORMOKA.limb_loc LB.
Lemma limb_loc_of_after : forall M o b rw g st', (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB) -> match L5.bo_st b with L5.BInl _ _ => L5.bo_dyn b = false | L5.BDyn _ _ => L5.bo_dyn b = true end -> obj_after M o b rw g st' -> exists q cap, limb_loc b o g st' q cap.
Proof. exact (@L5NORMOKA.limb_loc_of_after LB). Qed.
Lemma mem_eq : forall (M M' : word -> option byte), (forall a, M' a = M a) -> M' = M.
Proof. exact (@L5NORMOKA.mem_eq). Qed.
Lemma spok0 : spok sp.
Proof. exact (@L5NORMOKA.spok0 L M0 od on px sp bd bn wd wn STK Hnd TOPsm Hnn NN2 Aod Aon Sod Son Hod P4 Spx). Qed.
Lemma blocks_apart_app : forall A n l1 l2, blocks_apart A n (l1 ++ l2) -> blocks_apart A n l2.
Proof. exact (@L5NORMOKA.blocks_apart_app). Qed.
Lemma hp_defined_stack : forall M a n, L5C.hpres L LB sp NORM_SCR W M0 M -> sp <= a -> a + n <= 2 ^ 64 -> L5.defined M0 a n -> L5.defined M a n.
Proof. exact (@L5NORMOKA.hp_defined_stack L LY M0 LB od on px sp bd bn wd wn STK Hnd TOPsm Hnn NN2 Aod Aon Sod Son P4 Spx). Qed.
Lemma hp_defined_block : forall LBx crx Mx VMx M A m a n, hi_heap HI LBx crx Mx VMx -> In (A, m) LB -> In (A, m) LBx -> L5C.hpres L LB sp NORM_SCR W M0 M -> A <= a -> a + n <= A + m -> L5.defined M0 a n -> L5.defined M a n.
Proof. exact (@L5NORMOKA.hp_defined_block _ L HI LY HIok M0 LB od on px sp bd bn wd wn STK Hnd TOPsm Hnn NN2). Qed.
Lemma stage4 : forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (gd gn : growth) (std stn : L5.bstore) (qd capd qn capn : Z), SEC = true -> getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 on -> (forall i, In i cs_pass -> getr R (reg i) = getr R0 (reg i)) -> model_but_vm model0 model -> hi_heap HI LB3 cr3 M (m_vmmaps model) -> saved M sp R0 -> L5.defined M (sp - NORM_SCR) NORM_SCR -> L5.u32_at RSEGS M px C0 -> obj_after M od bd (norm_words wd C0 true) gd std -> limb_loc bd od gd std qd capd -> (match std with L5.BDyn _ _ => True | _ => False end) -> obj_after M on bn Dn gn stn -> limb_loc bn on gn stn qn capn -> (match stn with L5.BDyn _ _ => True | _ => False end) -> Z.of_nat (rlen Dn) + 1 <= capn -> apart qd (8 * capd) qn (8 * capn) -> LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = debits L cr (blocks_of gn ++ blocks_of gd) -> (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M A (8 * cap) end) -> (match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M A (8 * cap) end) -> L5C.hpres L LB sp NORM_SCR W M0 M -> srealizes RSEGS SCFG (cfg R AFTER3 M model) K.
Proof. exact (@L5NORMOKA.stage4 _ L HI LY HIok RESIZE R0 M0 model0 K LB cr od on px sp r bd bn wd wn HH0 MOK0 HK0 G1 RA G2 G4 STK OBd OLd Hnd TOPnz TOPsm OBn OLn Hnn NN2 Aod Aon Sod Son Hod Hon APdn DEFn P4 Spx Hpx APpn BLKd BLKn APB SECcap CR KONT). Qed.
Lemma stage3 : forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (gd gn : growth) (std stn : L5.bstore) (qd capd qn capn : Z), SEC = true -> getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 on -> getr R (reg 9) = Z_to_bv 64 od -> (forall i, In i cs_pass -> getr R (reg i) = getr R0 (reg i)) -> model_but_vm model0 model -> hi_heap HI LB3 cr3 M (m_vmmaps model) -> saved M sp R0 -> L5.defined M (sp - NORM_SCR) NORM_SCR -> L5.u32_at RSEGS M px C0 -> obj_after M od bd D gd std -> limb_loc bd od gd std qd capd -> (match std with L5.BDyn _ _ => True | _ => False end) -> obj_after M on bn Dn gn stn -> limb_loc bn on gn stn qn capn -> (match stn with L5.BDyn _ _ => True | _ => False end) -> Z.of_nat (rlen D) + 1 <= capd -> Z.of_nat (rlen Dn) + 1 <= capn -> apart qd (8 * capd) qn (8 * capn) -> LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = debits L cr (blocks_of gn ++ blocks_of gd) -> (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M A (8 * cap) end) -> (match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M A (8 * cap) end) -> L5C.hpres L LB sp NORM_SCR W M0 M -> srealizes RSEGS SCFG (cfg R F M model) K.
Proof. exact (@L5NORMOKA.stage3 _ L HI LY HIok RESIZE R0 M0 model0 K LB cr od on px sp r bd bn wd wn HH0 MOK0 HK0 G1 RA G2 G4 STK OBd OLd Hnd TOPnz TOPsm OBn OLn Hnn NN2 Aod Aon Sod Son Hod Hon APdn DEFd DEFn P4 Spx Hpx APpd APpn BLKd BLKn APB SECcap CR KONT). Qed.
Lemma finish_false : forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit) (gd gn : growth) (std stn : L5.bstore), SEC = false -> getr R (reg 2) = Z_to_bv 64 (sp - 64) -> (forall i, In i cs_pass -> getr R (reg i) = getr R0 (reg i)) -> model_but_vm model0 model -> hi_heap HI LB3 cr3 M (m_vmmaps model) -> saved M sp R0 -> L5.defined M (sp - NORM_SCR) NORM_SCR -> L5.u32_at RSEGS M px C0 -> obj_after M od bd D gd std -> obj_after M on bn Dn gn stn -> LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = debits L cr (blocks_of gn ++ blocks_of gd) -> (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M A (8 * cap) end) -> (match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M A (8 * cap) end) -> L5C.hpres L LB sp NORM_SCR W M0 M -> (match gd with Same => True | Grown _ _ => (3 <= length D)%nat end) -> (match gn with Same => True | Grown _ _ => (3 <= length Dn)%nat end) -> srealizes RSEGS SCFG (cfg R L5NORM.K M model) K.
Proof. exact (@L5NORMOKA.finish_false _ L HI R0 M0 model0 K LB cr od on px sp r bd bn wd wn MOK0 G1 RA G2 STK OLd Hnd TOPnz TOPsm Hnn NN2 Aod Aon Sod Son Hod P4 Spx KONT). Qed.


(* [comment removed for export] *)
Lemma stageE (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB3 : list (Z * Z)) (cr3 : credit)
      (gd gn : growth) (std stn : L5.bstore) (qd capd qn capn : Z) :
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 on -> getr R (reg 9) = Z_to_bv 64 od ->
  getr R (reg 19) = Z_to_bv 64 (Z.of_nat nd) -> getr R (reg 20) = Z_to_bv 64 (od + 16) ->
  getr R (reg 21) = Z_to_bv 64 (8 * Z.of_nat nd - 8) -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat nd - 1) ->
  (forall i, In i cs_pass -> getr R (reg i) = getr R0 (reg i)) ->
  model_but_vm model0 model -> hi_heap HI LB3 cr3 M (m_vmmaps model) ->
  saved M sp R0 -> L5.defined M (sp - NORM_SCR) NORM_SCR -> L5.u32_at RSEGS M px C0 ->
  obj_after M od bd D gd std -> limb_loc bd od gd std qd capd ->
  obj_after M on bn Dn gn stn -> limb_loc bn on gn stn qn capn ->
  ((2 <= nd)%nat -> match std with L5.BDyn _ _ => True | _ => False end /\ match stn with L5.BDyn _ _ => True | _ => False end) ->
  (SEC = true -> Z.of_nat (rlen D) + 1 <= capd /\ Z.of_nat (rlen Dn) + 1 <= capn /\ apart qd (8 * capd) qn (8 * capn)) ->
  LB3 = blocks_of gn ++ blocks_of gd ++ LB -> cr3 = debits L cr (blocks_of gn ++ blocks_of gd) ->
  (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M A (8 * cap) end) ->
  (match gn with Same => True | Grown A cap => L5C.fresh_block L (blocks_of gd ++ LB) M A (8 * cap) end) ->
  L5C.hpres L LB sp NORM_SCR W M0 M ->
  (match gd with Same => True | Grown _ _ => (3 <= length D)%nat end) ->
  (match gn with Same => True | Grown _ _ => (3 <= length Dn)%nat end) ->
  srealizes RSEGS SCFG (cfg R AFTER2 M model) K.
Proof.
  intros H2 H8 H9 H19 H20 H21 H22 PASS MBV HH SV DEF PX OAd LLd OAn LLn DYN2 SCAP ELB ECR FRd FRn HP GWd GWn.
  pose proof stk0 as (A16 & SLO & SHI & STOP & _). pose proof IMG as IMG. pose proof ERRNO as ERRNO. pose proof spok0 as SP.
  assert (SPlo: hl_sptop L - 8388608 + 64 <= sp) by sclia.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof D_rlen_pos as RPd. pose proof rlen_D_le as RLd. pose proof D_ok as DOK. pose proof D_len as DLEN. pose proof wd_len as WDL.
  (* [comment removed for export] *)
  pose proof (br_223c8 fx R M) as BR1. rewrite <- rl0, getr_zero, H22 in BR1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact BR1.
  destruct (Nat.eq_dec nd 1) as [ND1|ND1].
  { (* [comment removed for export] *)
    rewrite ND1. cbn [branch_taken]. replace (Z.of_nat 1 - 1) with 0 by lia. rewrite bv_eqb_refl.
    assert (HSEC: SEC = false). { unfold SEC, second. rewrite ND1. reflexivity. }
    apply (finish_false fx R M model LB3 cr3 gd gn std stn HSEC H2 PASS MBV HH SV DEF PX OAd OAn ELB ECR FRd FRn HP GWd GWn). }
  cbn [branch_taken]. rewrite bv_eqb_neq. 2:{ intros E. apply (f_equal bv_unsigned) in E. rewrite !BG.unsigned_lit in E by lia. lia. }
  (* [comment removed for export] *)
  destruct (DYN2 ltac:(lia)) as [SDd SDn].
  destruct stn as [v0 v1|capn' qn']; [contradiction|]. pose proof LLn as LLn0. destruct LLn as (-> & -> & INn & GNn).
  destruct std as [u0 u1|capd' qd']; [contradiction|]. pose proof LLd as LLd0. destruct LLd as (-> & -> & INd & GNd).
  assert (INd3: In (qd, 8 * capd) LB3). { subst LB3. apply in_app_iff in INd. apply in_app_iff. destruct INd. right; apply in_app_iff; left; assumption. right. apply in_app_iff. right; assumption. }
  pose proof (LBdef _ _ _ _ HH qd (8 * capd) INd3) as (BDd & BLOd & BHId). rewrite IMG, IMGLO in BLOd.
  pose proof OAd as OAd0. unfold obj_after in OAd. cbv zeta in OAd. destruct OAd as (WOd & NLEd & OBd2 & OLd2 & CAPm & GMd).
  replace (rlen D =? 0)%nat with false in OBd2, OLd2 by (symmetry; apply Nat.eqb_neq; lia).
  set (fbd := match gd with Same => L5.bo_fb bd | Grown _ _ => Z.lor (L5.bo_fb bd) 1 end) in *.
  pose proof OBd2 as (Pd0 & Hfbd & Pd8 & Bd1 & Pd16 & Pd24 & CAPd2 & Ccapd & Qd8 & QdLO & QdHI & QdHAP). cbn [L5.bo_fb L5.bo_len L5.bo_st] in Pd0, Hfbd, Pd8, Bd1, Pd16, Pd24, CAPd2, Ccapd, Qd8, QdLO, QdHI.
  destruct OLd2 as (L1 & L2 & L3). cbn [L5.bo_st L5.bo_len] in L1, L3.
  (* [comment removed for export] *)
  set (w1 := nth_w D (nd - 1)). set (wz := nth_w D (nd - 2)).
  pose proof (words_ok_nth D (nd - 1) DOK) as Rw1. pose proof (words_ok_nth D (nd - 2) DOK) as Rwz. fold w1 in Rw1. fold wz in Rwz.
  assert (LD2: (nd <= length D)%nat). { rewrite DLEN. destruct (C0 =? 0); lia. }
  assert (X1: L5.u64_at RSEGS M (qd + 8 * Z.of_nat nd - 8) w1).
  { replace (qd + 8 * Z.of_nat nd - 8) with (qd + 8 * Z.of_nat (nd - 1)) by lia. subst w1. unfold nth_w. apply L3. lia. }
  assert (X0: L5.u64_at RSEGS M (qd + 8 * Z.of_nat nd - 16) wz).
  { replace (qd + 8 * Z.of_nat nd - 16) with (qd + 8 * Z.of_nat (nd - 2)) by lia. subst wz. unfold nth_w. apply L3. lia. }
  destruct (nzEd_conc fx R0 R M sp od fbd qd w1 wz nd SP ltac:(unfold apart; lia) ltac:(lia) ltac:(lia) Aod Pd0 Hfbd Bd1 Pd24 QdLO ltac:(lia) Qd8 ltac:(lia)
              X1 X0 Rw1 Rwz H2 H9 H19 H20 H21 H22) as (fx1 & R1 & M1 & MS1 & K1 & (B2 & B9 & B10 & B11) & MM1 & MG1).
  pose proof (mem_eq M M1 MM1) as EM1. subst M1.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  (* [comment removed for export] *)
  pose proof (br_223f0 fx1 R1 M) as BR2. rewrite B10, B11 in BR2. unfold branch_taken, bv_ltu in BR2. rewrite !BG.unsigned_lit in BR2 by lia.
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact BR2.
  assert (PASS1: forall i, In i cs_pass -> getr R1 (reg i) = getr R0 (reg i)).
  { intros i Hi. rewrite (K1 i) by (apply (L5K.incl_b cs_pass KSE ltac:(vm_compute; reflexivity)); exact Hi). apply PASS. exact Hi. }
  assert (E8: getr R1 (reg 8) = Z_to_bv 64 on). { rewrite (K1 8%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H8. }
  destruct (Z.ltb_spec w1 wz) as [LT|GE]; cbn [negb].
  - (* [comment removed for export] *)
    assert (HSEC: SEC = true). { unfold SEC, second. fold w1 wz. rewrite (proj2 (Nat.leb_le 2 nd)) by lia. cbn [andb]. apply Z.ltb_lt. exact LT. }
    destruct (SCAP HSEC) as (CAPd & CAPn & APQ).
    apply (stage3 fx1 R1 M model LB3 cr3 gd gn (L5.BDyn capd qd) (L5.BDyn capn qn) qd capd qn capn HSEC B2 E8 B9 PASS1 MBV HH SV DEF PX OAd0 LLd0 I OAn LLn0 I
             CAPd CAPn APQ ELB ECR FRd FRn HP).
  - (* [comment removed for export] *)
    assert (HSEC: SEC = false). { unfold SEC, second. fold w1 wz. rewrite (proj2 (Nat.leb_le 2 nd)) by lia. cbn [andb]. apply Z.ltb_ge. exact GE. }
    apply (finish_false fx1 R1 M model LB3 cr3 gd gn (L5.BDyn capd qd) (L5.BDyn capn qn) HSEC B2 PASS1 MBV HH SV DEF PX OAd0 OAn ELB ECR FRd FRn HP GWd GWn).
Qed.


(* [comment removed for export] *)
Lemma round_up_3 : round_up 3 = 8. Proof. reflexivity. Qed.
Lemma debits_app cr0 l1 l2 : debits L cr0 (l1 ++ l2) = debits L (debits L cr0 l2) l1.
Proof. induction l1 as [|[A n] l1 IH]; cbn. reflexivity. rewrite IH. reflexivity. Qed.

Lemma stageD (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (LB2 : list (Z * Z)) (cr2 : credit)
      (gd : growth) (std : L5.bstore) (qd capd : Z) :
  getr R (reg 2) = Z_to_bv 64 (sp - 64) -> getr R (reg 8) = Z_to_bv 64 on -> getr R (reg 9) = Z_to_bv 64 od -> getr R (reg 18) = Z_to_bv 64 px ->
  getr R (reg 19) = Z_to_bv 64 (Z.of_nat nd) -> getr R (reg 20) = Z_to_bv 64 (od + 16) ->
  getr R (reg 21) = Z_to_bv 64 (8 * Z.of_nat nd - 8) -> getr R (reg 22) = Z_to_bv 64 (Z.of_nat nd - 1) ->
  (forall i, In i cs_pass -> getr R (reg i) = getr R0 (reg i)) ->
  model_but_vm model0 model -> hi_heap HI LB2 cr2 M (m_vmmaps model) ->
  saved M sp R0 -> L5.defined M (sp - NORM_SCR) NORM_SCR -> L5.u32_at RSEGS M px C0 ->
  obj_after M od bd D gd std -> limb_loc bd od gd std qd capd ->
  L5.big_at RSEGS M on bn -> L5C.obj_limbs RSEGS M bn wn -> L5.defined M on 32 ->
  (L5.bo_dyn bn = false -> credit_ok L cr2 (8 * round_up 3)) ->
  LB2 = blocks_of gd ++ LB -> cr2 = debits L cr (blocks_of gd) ->
  (match gd with Same => True | Grown A cap => L5C.fresh_block L LB M A (8 * cap) end) ->
  L5C.hpres L LB sp NORM_SCR W M0 M ->
  (match gd with Same => True | Grown _ _ => (3 <= length D)%nat end) ->
  srealizes RSEGS SCFG (cfg R AFTER1 M model) K.
Proof.
  intros H2 H8 H9 H18 H19 H20 H21 H22 PASS MBV HH SV DEF PX OAd LLd OBnM OLnM DEFn2 CRn ELB ECR FRd HP GWd.
  pose proof stk0 as (A16 & SLO & SHI & STOP & _). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO. pose proof ERRNOV as ERRNOV.
  pose proof spok0 as SP.
  assert (SPlo: hl_sptop L - 8388608 + 64 <= sp) by fsclia.
  pose proof (LBhi _ _ _ _ HH) as LBhi2.
  pose proof (model_ok_but_vm _ _ MOK0 MBV) as MOK. pose proof MOK as (Mh & Ml & _).
  pose proof C0_rng as CR0. pose proof wn_len as WNL. pose proof wd_len as WDL. pose proof bn_shape as BNS. pose proof bd_shape as BDS.
  pose proof D_len as DLEN. pose proof Dn_len as DNLEN. pose proof rlen_D_le as RLd. pose proof rlen_Dn_le as RLn. pose proof Dn_ok as DNOK.
  (* [comment removed for export] *)
  destruct (nzD_conc fx R0 R M sp on px C0 SP ltac:(fsclia) ltac:(flia) P4 ltac:(unfold apart; flia) PX ltac:(flia) ltac:(flia) H2 H8 H18)
    as (fx1 & R1 & M1 & MS1 & K1 & (A1 & A2 & A8 & A10 & A11 & A18) & MM1 & MG1).
  pose proof (mem_eq M M1 MM1) as EM1. subst M1.
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  eapply (shl_ok fx1 R1 M model K LB2 cr2 on (sp - 64) AFTER2 C0 bn wn HH MOK HK0).
  + rewrite r10. exact A10.
  + rewrite r11. exact A11.
  + flia.
  + rewrite r1. exact A1.
  + split. unfold AFTER2. flia. reflexivity.
  + rewrite r2. exact A2.
  + rewrite r4. rewrite (K1 4%nat) by (apply L5K.in_b; vm_compute; reflexivity). rewrite (PASS 4%nat) by (cbn; tauto). exact G4.
  + split. { replace (sp - 64) with (sp + (-4) * 16) by flia. rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. flia. split. flia. uSCR. eapply L5.defined_sub. exact DEF. flia. flia.
  + exact OBnM.
  + exact OLnM.
  + fold nn. flia.
  + exact Aon. + flia. + flia.
  + exact DEFn2.
  + unfold L5.bo_dyn, L5.bo_cap. destruct (L5.bo_st bn) as [v0 v1|cap q] eqn:EST.
    { destruct BNS as [X _]. unfold L5.bo_dyn in X. intros Y. congruence. }
    intros _. destruct (BLKn cap q eq_refl) as (_ & X & _). fold nn in X. flia.
  + intros _ _ DYf. apply CRn. exact DYf.
  + intros cap q EST. subst LB2. apply in_app_iff. right. exact (proj1 (BLKn cap q EST)).
  + (* [comment removed for export] *)
    intros fx5 R5 M5 model5 g5 LB5 cr5 POST MBV5 HH5.
    unfold L5SHL.shl_post in POST. cbv zeta in POST.
    destruct POST as (RP5 & B10 & st5 & OB5 & OL5 & NLE5 & GG).
    fold Dn in OB5, OL5, NLE5, GG.
    set (fbn := match g5 with Same => L5.bo_fb bn | Grown _ _ => Z.lor (L5.bo_fb bn) 1 end) in *.
    assert (NN: (1 <= nn <= 290)%nat) by (fold nn in Hnn; exact Hnn).
    (* [comment removed for export] *)
    assert (C0pos: (2 <= nd)%nat -> 1 <= C0).
    { intros ND2. destruct CR0 as [C1 [C2 C3]]. pose proof (TOPsm ltac:(fold nd; flia)) as TS. fold nd in TS. fold w0 in TS.
      destruct (Z.eq_dec C0 0) as [E|NE]; [|flia]. rewrite E in C2. rewrite Z.pow_0_r in C2. flia. }
    assert (LDn2: (2 <= nd)%nat -> length Dn = S nn).
    { intros ND2. rewrite DNLEN. replace (C0 =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (C0pos ND2); flia). reflexivity. }
    assert (LD2: (2 <= nd)%nat -> length D = S nd).
    { intros ND2. rewrite DLEN. replace (C0 =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (C0pos ND2); flia). reflexivity. }
    assert (LDnle: (length Dn <= S nn)%nat) by (rewrite DNLEN; destruct (C0 =? 0); flia).
    assert (LDle: (length D <= S nd)%nat) by (rewrite DLEN; destruct (C0 =? 0); flia).
    assert (SEC2: SEC = true -> (2 <= nd)%nat).
    { unfold SEC, second. intros X. apply andb_prop in X. destruct X as [X _]. apply Nat.leb_le in X. exact X. }
    (* [comment removed for export] *)
    pose proof LLd as LLd0.
    assert (QD: match std with L5.BDyn _ _ => In (qd, 8 * capd) LB2 /\ qd + 8 * capd <= hl_sptop L - 8388608 /\ (4096 <= qd /\ (qd + 8 * capd <= 0x10000 \/ 0x91000 <= qd))
                                  /\ (forall cap0 q0, L5.bo_st bn = L5.BDyn cap0 q0 -> apart qd (8 * capd) q0 (8 * cap0))
                | L5.BInl _ _ => gd = Same /\ qd = od + 16 /\ capd = 2 end).
    { destruct std as [u0 u1|capd' qd']; cbn in LLd.
      - destruct LLd as (-> & _ & -> & ->). repeat split; reflexivity.
      - destruct LLd as (-> & -> & INd & GD). assert (INd2: In (qd, 8 * capd) LB2) by (subst LB2; exact INd).
        pose proof (LBdef _ _ _ _ HH qd (8 * capd) INd2) as (_ & QLO & QHI). rewrite IMG, IMGLO in QLO.
        split. exact INd2. split. exact QHI. split. exact QLO.
        intros cap0 q0 EST. destruct gd as [|Ad cd].
        + exact (APB capd qd cap0 q0 GD EST).
        + destruct GD as (-> & -> & -> & _). destruct FRd as (_ & BA & _). unfold apart.
          pose proof (BA (q0, 8 * cap0) (proj1 (BLKn cap0 q0 EST))) as X. cbn in X. flia. }
    (* [comment removed for export] *)
    assert (PKG: exists W5 qn capn,
       L5C.hpres L LB2 (sp - 64) L5SHL.SHL_SCR W5 M M5 /\
       LB5 = blocks_of g5 ++ LB2 /\ cr5 = debits L cr2 (blocks_of g5) /\
       (forall a, sp - 64 <= a -> ~ (on <= a < on + 32) -> L5.outside W5 a) /\
       (match std with L5.BDyn _ _ => forall a, qd <= a < qd + 8 * capd -> L5.outside W5 a | L5.BInl _ _ => True end) /\
       (forall a, L5C.kept L LB sp NORM_SCR W a -> L5.outside W5 a) /\
       obj_after M5 on bn Dn g5 st5 /\ limb_loc bn on g5 st5 qn capn /\
       (SEC = true -> Z.of_nat (rlen Dn) + 1 <= capn /\ apart qd (8 * capd) qn (8 * capn)) /\
       ((2 <= nd)%nat -> match st5 with L5.BDyn _ _ => True | _ => False end) /\
       (match g5 with Same => True | Grown A cap => L5C.fresh_block L LB2 M5 A (8 * cap) end) /\
       (match g5 with Same => True | Grown _ _ => (3 <= length Dn)%nat end)).
    { destruct g5 as [|A5 c5].
      - (* [comment removed for export] *)
        destruct GG as (DS & ELB5 & ECR5 & STM & HP5).
        destruct (L5.bo_st bn) as [u0 u1|cap0 q0] eqn:EST.
        + (* [comment removed for export] *)
          destruct st5 as [z0 z1|c' q']; [|contradiction].
          destruct BNS as [ND NNle].
          assert (LDn: (length Dn <= 2)%nat) by (destruct DS as [X|X]; [congruence|exact X]).
          assert (ND1: ~ (2 <= nd)%nat). { intros ND2. pose proof (LDn2 ND2). destruct (NN2 ND2) as [X _]. fold nn in X. flia. }
          exists [(on, 32); (L5.bo_data on bn, 8 * Z.of_nat (length Dn))], (on + 16), 2.
          unfold L5.bo_data. rewrite EST.
          split. { unfold L5.bo_data in HP5. rewrite EST in HP5. exact HP5. }
          split. { cbn. exact ELB5. } split. { cbn. exact ECR5. }
          split. { intros a Ha Hna. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
          split. { destruct std as [v0 v1|cd' qd']. exact I. destruct QD as (_ & QHI & _ & _). intros a Ha.
                   apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
          split. { intros a KA. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW.
                   pose proof (L5HP.outside_in _ _ on 32 OW ltac:(unfold W, norm_W; cbn; tauto)) as X.
                   apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
          split. { unfold obj_after. cbv zeta. fold fbn. split. exact DNOK. split. exact NLE5. split. exact OB5. split. exact OL5. split. exact LDn.
                   rewrite EST. exact I. }
          split. { cbn. repeat split; auto. }
          split. { intros HS. exfalso. exact (ND1 (SEC2 HS)). }
          split. { intros ND2. exfalso. exact (ND1 ND2). }
          split; exact I.
        + (* [comment removed for export] *)
          destruct st5 as [z0 z1|c' q']; [contradiction|]. destruct STM as [-> ->].
          destruct BNS as (DY & NNC & CAPR & Q8 & QLO & QHI).
          destruct (BLKn cap0 q0 eq_refl) as (INn & CAPn1 & APXn). fold nn in CAPn1.
          assert (INn2: In (q0, 8 * cap0) LB2) by (subst LB2; apply in_app_iff; right; exact INn).
          pose proof (LBhi2 _ INn2) as BHn. cbn in BHn.
          exists [(on, 32); (L5.bo_data on bn, 8 * Z.of_nat (length Dn))], q0, cap0.
          unfold L5.bo_data. rewrite EST.
          split. { unfold L5.bo_data in HP5. rewrite EST in HP5. exact HP5. }
          split. { cbn. exact ELB5. } split. { cbn. exact ECR5. }
          split. { intros a Ha Hna. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn. flia. apply L5C.outside_nil. }
          split. { destruct std as [v0 v1|cd' qd']. exact I. destruct QD as (_ & QHId & _ & APQ). pose proof (APQ cap0 q0 eq_refl) as AP. unfold apart in AP.
                   intros a Ha. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn. flia. apply L5C.outside_nil. }
          split. { intros a KA. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW.
                   pose proof (L5HP.outside_in _ _ on 32 OW ltac:(unfold W, norm_W; cbn; tauto)) as X.
                   pose proof (L5HP.outside_in _ _ q0 (8 * cap0) OW ltac:(unfold W, norm_W, dyn_area; rewrite EST; rewrite !in_app_iff; cbn; tauto)) as Y.
                   apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_cons. unfold L5.in_rng; cbn. flia. apply L5C.outside_nil. }
          split. { unfold obj_after. cbv zeta. fold fbn. split. exact DNOK. split. exact NLE5. split. exact OB5. split. exact OL5. split. flia.
                   rewrite EST. split; reflexivity. }
          split. { cbn. repeat split; auto. }
          split. { intros HS. pose proof (SEC2 HS) as ND2. destruct (SECcap HS) as [_ CB]. unfold L5.bo_cap in CB. rewrite EST in CB. fold nn in CB.
                   specialize (CB DY). split. flia.
                   destruct std as [v0 v1|cd' qd']. { destruct QD as (_ & -> & ->). unfold apart. flia. }
                   destruct QD as (_ & _ & _ & APQ). exact (APQ cap0 q0 eq_refl). }
          split. { intros _. exact I. }
          split. exact I. exact I.
      - (* [comment removed for export] *)
        destruct GG as (ND & M3 & CAPE & ELB5 & ECR5 & FB5 & EST5 & HP5). subst st5.
        destruct (L5.bo_st bn) as [u0 u1|cap0 q0] eqn:EST. 2:{ destruct BNS as [DY _]. congruence. }
        destruct BNS as [_ NNle].
        assert (L3: length Dn = 3%nat) by flia.
        assert (C8: c5 = 8). { rewrite CAPE, L3. reflexivity. }
        clear CAPE. subst c5.
        pose proof FB5 as (BR5 & BA5 & BDEF5). pose proof BR5 as (B50 & B51 & B52 & B53 & B54).
        exists [(on, 32)], A5, 8.
        split. exact HP5.
        split. { cbn. exact ELB5. } split. { cbn. exact ECR5. }
        split. { intros a Ha Hna. apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
        split. { destruct std as [v0 v1|cd' qd']. exact I. destruct QD as (_ & QHId & _ & _). intros a Ha.
                 apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
        split. { intros a KA. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW.
                 pose proof (L5HP.outside_in _ _ on 32 OW ltac:(unfold W, norm_W; cbn; tauto)) as X.
                 apply L5C.outside_cons. unfold L5.in_rng; cbn; flia. apply L5C.outside_nil. }
        split. { unfold obj_after. cbv zeta. fold fbn. split. exact DNOK. split. exact NLE5. split. exact OB5. split. exact OL5. split. flia.
                 split. exact ND. split; reflexivity. }
        split. { cbn. repeat split; auto. }
        split. { intros HS. split. pose proof (rlen_le Dn). flia.
                 destruct std as [v0 v1|cd' qd']. { destruct QD as (_ & -> & ->). unfold apart. flia. }
                 destruct QD as (INd2 & _ & _ & _). pose proof (BA5 _ INd2) as X. cbn in X. unfold apart. flia. }
        split. { intros _. exact I. }
        split. exact FB5. exact M3. }
    clear GG.
    destruct PKG as (W5 & qn & capn & HP5 & ELB5 & ECR5 & OUT5 & OUTB & OUTW & OAn5 & LLn5 & SCAPn & DYNn & FRn5 & GWn5).
    (* [comment removed for export] *)
    assert (KST: forall a, sp - 64 <= a < 2 ^ 64 -> ~ (on <= a < on + 32) -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
      apply OUT5; flia. }
    assert (KBD: match std with L5.BDyn _ _ => forall a, qd <= a < qd + 8 * capd -> M5 (Z_to_bv 64 a) = M (Z_to_bv 64 a) | L5.BInl _ _ => True end).
    { destruct std as [v0 v1|cd' qd']. exact I. destruct QD as (INd2 & QHI & QLO & _). intros a Ha.
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). eapply L5C.kept_block. exact INd2. flia. flia. flia. rewrite ERRNOV. flia.
      apply OUTB. flia. }
    assert (SV5: saved M5 sp R0).
    { destruct SV as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
      repeat split; (eapply u64_at_agree1; [intros i Hi; apply KST; flia | flia | flia | assumption]). }
    assert (DEF5: L5.defined M5 (sp - NORM_SCR) NORM_SCR).
    { intros i Hi. destruct (Z_lt_le_dec (sp - NORM_SCR + i) (sp - 64)) as [X|X].
      - pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP5) as D5. uSCR.
        replace (sp - (64 + (48 + (64 + (64 + (64 + (16 + 8224)))))) + i) with (sp - 64 - (48 + (64 + (64 + (64 + (16 + 8224))))) + i) by flia. apply D5. flia.
      - rewrite KST. apply DEF. flia. fsclia. fsclia. }
    assert (PX5: L5.u32_at RSEGS M5 px C0). { eapply u32_at_agree1. intros i Hi. apply KST. flia. unfold apart in APpn. flia. flia. flia. exact PX. }
    (* [comment removed for export] *)
    assert (OAd5: obj_after M5 od bd D gd std).
    { unfold obj_after in OAd |- *. cbv zeta in OAd. cbv zeta. destruct OAd as (WOd & NLEd & OBd2 & OLd2 & CAPmd & GMd).
      split. exact WOd. split. exact NLEd.
      split. { eapply (L5C.big_at_agree RSEGS M M5). intros i Hi. apply KST. flia. unfold apart in APdn. flia. flia. flia. exact OBd2. }
      split. { destruct OLd2 as (L1 & L2 & L3). split. exact L1. split. exact L2. cbn [L5.bo_st L5.bo_len] in L3 |- *.
               destruct std as [v0 v1|cd' qd']. exact L3.
               cbn in LLd. destruct LLd as (Ecd & Eqd & _). subst cd' qd'.
               eapply (L5C.limbs_at_agree RSEGS M M5). 2: flia. 3: exact L3. intros i Hi. apply KBD. cbn in CAPmd. flia. cbn in CAPmd. flia. }
      split. exact CAPmd. exact GMd. }
    assert (FRd5: match gd with Same => True | Grown A cap => L5C.fresh_block L LB M5 A (8 * cap) end).
    { destruct gd as [|Ad cd]. exact I. destruct FRd as (BR & BA & BDEF). split. exact BR. split. exact BA.
      destruct std as [v0 v1|cd' qd']. { destruct QD as (X & _). discriminate. }
      cbn in LLd. destruct LLd as (Ecd & Eqd & _ & -> & -> & -> & _). subst cd' qd'. destruct QD as (INd2 & QHI & QLO & _).
      intros i Hi. eapply (L5C.hpres_cdef _ _ _ _ _ _ _ (Ad + i) HP5). flia. left. exists (Ad, 8 * 8). split. exact INd2. cbn; flia.
      unfold in_errno; rewrite ERRNOV; flia. apply BDEF. flia. }
    assert (HPA: L5C.hpres L LB sp NORM_SCR W M0 M5).
    { eapply (L5HP.hpres_trans L LB LB2). exact HP. exact HP5.
      - intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. subst LB2. rewrite in_app_iff. tauto. } fsclia. flia.
        intros _. apply OUTW. exact KA.
      - intros b Hb. subst LB2. rewrite in_app_iff. tauto.
      - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
    (* [comment removed for export] *)
    assert (E2: getr R5 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite (preserved_sregs R1 R5 2 RP5) by (cbn; tauto). exact A2. }
    assert (E8: getr R5 (reg 8) = Z_to_bv 64 on). { rewrite (preserved_sregs R1 R5 8 RP5) by (cbn; tauto). exact A8. }
    assert (E9: getr R5 (reg 9) = Z_to_bv 64 od). { rewrite (preserved_sregs R1 R5 9 RP5) by (cbn; tauto). rewrite (K1 9%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H9. }
    assert (E19: getr R5 (reg 19) = Z_to_bv 64 (Z.of_nat nd)). { rewrite (preserved_sregs R1 R5 19 RP5) by (cbn; tauto). rewrite (K1 19%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H19. }
    assert (E20: getr R5 (reg 20) = Z_to_bv 64 (od + 16)). { rewrite (preserved_sregs R1 R5 20 RP5) by (cbn; tauto). rewrite (K1 20%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H20. }
    assert (E21: getr R5 (reg 21) = Z_to_bv 64 (8 * Z.of_nat nd - 8)). { rewrite (preserved_sregs R1 R5 21 RP5) by (cbn; tauto). rewrite (K1 21%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H21. }
    assert (E22: getr R5 (reg 22) = Z_to_bv 64 (Z.of_nat nd - 1)). { rewrite (preserved_sregs R1 R5 22 RP5) by (cbn; tauto). rewrite (K1 22%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact H22. }
    eapply (stageE fx5 R5 M5 model5 (blocks_of g5 ++ LB2) cr5 gd g5 std st5 qd capd qn capn E2 E8 E9 E19 E20 E21 E22).
    * intros i Hi. rewrite (preserved_sregs R1 R5 i RP5) by (revert Hi; apply (L5K.incl_b cs_pass cs_all ltac:(vm_compute; reflexivity))).
      rewrite (K1 i) by (apply (L5K.incl_b cs_pass KSD ltac:(vm_compute; reflexivity)); exact Hi). apply PASS. exact Hi.
    * eapply L5C.model_but_vm_trans. exact MBV. exact MBV5.
    * rewrite <- ELB5. exact HH5.
    * exact SV5. * exact DEF5. * exact PX5.
    * exact OAd5. * exact LLd0. * exact OAn5. * exact LLn5.
    * intros ND2. split. 2: exact (DYNn ND2).
      destruct std as [v0 v1|cd' qd']. 2: exact I. exfalso.
      destruct QD as (GS & _). subst gd. unfold obj_after in OAd. cbv zeta in OAd. destruct OAd as (_ & _ & _ & _ & CAPmd & _). cbn in CAPmd.
      pose proof (LD2 ND2). flia.
    * intros HS. pose proof (SEC2 HS) as ND2. destruct (SCAPn HS) as [C1 C2]. split. 2: { split. exact C1. exact C2. }
      destruct std as [v0 v1|cd' qd'].
      { exfalso. destruct QD as (GS & _). subst gd. unfold obj_after in OAd. cbv zeta in OAd. destruct OAd as (_ & _ & _ & _ & CAPmd & _). cbn in CAPmd.
        pose proof (LD2 ND2). flia. }
      cbn in LLd. destruct LLd as (Ecd & Eqd & _ & GD). subst cd' qd'. pose proof (rlen_le D) as RL. pose proof (LD2 ND2) as L2.
      destruct gd as [|Ad cd].
      -- destruct (SECcap HS) as [CB _]. unfold L5.bo_cap in CB. rewrite GD in CB. fold nd in CB.
         rewrite GD in BDS. destruct BDS as [DY _]. specialize (CB DY). flia.
      -- destruct GD as (-> & -> & -> & DYf).
         assert (NDle: (nd <= 2)%nat). { generalize BDS. destruct (L5.bo_st bd) as [v0 v1|c0 q0]; intros [X Y]; [exact Y | unfold L5.bo_dyn in X; cbn in X; congruence]. }
         flia.
    * subst LB2. reflexivity.
    * rewrite ECR5, ECR. symmetry. apply debits_app.
    * exact FRd5.
    * subst LB2. exact FRn5.
    * exact HPA.
    * exact GWd.
    * exact GWn5.
Qed.

(* [comment removed for export] *)
Lemma swrap64 (w : Z) : bv_swrap 64 w = (w + 2 ^ 63) mod 2 ^ 64 - 2 ^ 63.
Proof. unfold bv_swrap, bv_wrap. change (bv_half_modulus 64) with (2 ^ 63). change (bv_modulus 64) with (2 ^ 64). reflexivity. Qed.
Lemma lts0_neg (w : Z) : 2 ^ 63 <= w < 2 ^ 64 -> branch_taken BC_LT (Z_to_bv 64 w) (Z_to_bv 64 0) = true.
Proof using od on px bd bn wd wn Hnd TOPsm Hnn NN2.
  intros Hw. unfold branch_taken, bv_lts. rewrite !Z_to_bv_signed, !swrap64. apply Z.ltb_lt.
  rewrite (Z.mod_small (0 + 2 ^ 63)) by lia.
  replace ((w + 2 ^ 63) mod 2 ^ 64) with (w + 2 ^ 63 - 2 ^ 64). lia.
  symmetry. rewrite <- (Z.mod_small (w + 2 ^ 63 - 2 ^ 64) (2 ^ 64)) by lia.
  replace (w + 2 ^ 63) with ((w + 2 ^ 63 - 2 ^ 64) + 1 * 2 ^ 64) at 1 by lia. rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma lts0_pos (w : Z) : 0 <= w < 2 ^ 63 -> branch_taken BC_LT (Z_to_bv 64 w) (Z_to_bv 64 0) = false.
Proof using od on px bd bn wd wn Hnd TOPsm Hnn NN2.
  intros Hw. unfold branch_taken, bv_lts. rewrite !Z_to_bv_signed, !swrap64. apply Z.ltb_ge.
  rewrite (Z.mod_small (0 + 2 ^ 63)) by lia. rewrite Z.mod_small by lia. lia.
Qed.

Lemma stageA : srealizes RSEGS SCFG (cfg R0 NORM M0 model0) K.
Proof.
  pose proof stk0 as (A16 & SLO & SHI & STOP & DEF). pose proof IMG as IMG. pose proof IMGLO as IMGLO. pose proof ERRNO as ERRNO. pose proof ERRNOV as ERRNOV.
  pose proof spok0 as SP. pose proof MOK0 as (Mh & Ml & _).
  pose proof (LBhi _ _ _ _ HH0) as LBhi0.
  pose proof (proj2 (hio_wf L SCFG HI HIok LB cr M0 _ HH0)) as (_ & CRf & CRs).
  pose proof C0_rng as CR0. pose proof w0_rng as W0. pose proof wd_len as WDL. pose proof wd_ok as WDOK. pose proof bd_shape as BDS. pose proof bn_shape as BNS.
  assert (ND: (1 <= nd <= 290)%nat) by (fold nd in Hnd; exact Hnd).
  assert (SPlo: hl_sptop L - 8388608 + 64 <= sp) by fsclia.
  assert (WR64: L5.writable RSEGS M0 (sp - 64) 64). { eapply L5.writable_sub. apply (L5C.writable_of_defined RSEGS). exact DEF. fsclia. fsclia. fsclia. fsclia. }
  pose proof G2 as H2. rewrite r2 in H2. pose proof G11 as H11. rewrite r11 in H11. pose proof G12 as H12. rewrite r12 in H12. pose proof G13 as H13. rewrite r13 in H13.
  pose proof OBd as OBd'. destruct OBd' as (Pd0 & Hfbd & Pd8 & PST).
  pose proof (obj_limbs_at M0 od bd wd OBd OLd) as LAT.
  assert (TOPW: L5.u64_at RSEGS M0 (L5.bo_data od bd + 8 * (Z.of_nat nd - 1)) w0).
  { unfold w0, nth_w. replace (L5.bo_data od bd + 8 * (Z.of_nat nd - 1)) with (L5.bo_data od bd + 8 * Z.of_nat (nd - 1)) by lia. apply LAT. rewrite WDL. lia. }
  (* [comment removed for export] *)
  assert (ENTRY: exists fx1 R1 M1 dynb, msteps RSEGS (st fx0 R0 NORM M0) (st fx1 R1 BLTZ M1)
      /\ (forall x, In x KSA -> getr R1 (reg x) = getr R0 (reg x)) /\ at_bltz R1 sp od on px nd w0 dynb /\ saved M1 sp R0
      /\ (forall a : word, ~ (sp - 64 <= bv_unsigned a < sp) -> M1 a = M0 a) /\ mem_grows M0 M1).
  { unfold L5.bo_data in TOPW. destruct (L5.bo_st bd) as [v0 v1|capd0 qd0] eqn:EST.
    - destruct PST as (Bd0 & _ & _ & Hl2 & _). destruct BDS as [DYd NDle].
      destruct (nzAi_conc fx0 R0 M0 sp od on px (L5.bo_fb bd) w0 nd SP WR64 ltac:(unfold apart; lia) ltac:(fsclia) ltac:(lia) Aod ltac:(lia) ltac:(lia)
                  Pd0 Hfbd Bd0 Pd8 ltac:(lia) ltac:(replace (od + 16 + 8 * (Z.of_nat nd - 1)) with (od + 16 + 8 * (Z.of_nat nd - 1)) by lia; exact TOPW) ltac:(lia)
                  H2 H11 H12 H13) as (fx1 & R1 & M1 & X).
      exists fx1, R1, M1, 0. exact X.
    - destruct PST as (Bd0 & P16 & P24 & Hlc & Hcap & Q8 & QLO & QHI & HAP). destruct BDS as (DYd & NDC & CAPR & _).
      destruct (BLKd capd0 qd0 eq_refl) as (INd & _ & _). pose proof (LBhi0 _ INd) as BH. cbn in BH.
      destruct (nzAd_conc fx0 R0 M0 sp od on px (L5.bo_fb bd) qd0 w0 nd SP WR64 ltac:(unfold apart; lia) ltac:(fsclia) ltac:(lia) Aod ltac:(lia) ltac:(lia)
                  Pd0 Hfbd Bd0 Pd8 ltac:(lia) P24 QLO ltac:(lia) Q8 ltac:(unfold apart; lia)
                  ltac:(replace (qd0 + 8 * Z.of_nat nd - 8) with (qd0 + 8 * (Z.of_nat nd - 1)) by lia; exact TOPW) ltac:(lia)
                  H2 H11 H12 H13) as (fx1 & R1 & M1 & X).
      exists fx1, R1, M1, 1. exact X. }
  destruct ENTRY as (fx1 & R1 & M1 & dynb & MS1 & K1 & ATB & SV1 & FR1 & MG1).
  assert (FR1z: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 <= a < sp) -> M1 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR1. rewrite BG.unsigned_lit by lia. exact Hna. }
  unfold cfg. eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS1.
  destruct ATB as (B2 & B8 & B9 & B10 & B11 & B18 & B19 & B20 & B21 & B22).
  assert (PASS1: forall i, In i cs_pass -> getr R1 (reg i) = getr R0 (reg i)).
  { intros i Hi. apply K1. revert Hi. apply (L5K.incl_b cs_pass KSA ltac:(vm_compute; reflexivity)). }
  (* [comment removed for export] *)
  assert (TOSHL: exists fx3 R3 M3, msteps RSEGS (st fx1 R1 BLTZ M1) (st fx3 R3 L5SHL.SHL M3)
      /\ (forall i, In i cs_pass -> getr R3 (reg i) = getr R0 (reg i))
      /\ getr R3 (reg 8) = Z_to_bv 64 on /\ getr R3 (reg 19) = Z_to_bv 64 (Z.of_nat nd) /\ getr R3 (reg 20) = Z_to_bv 64 (od + 16)
      /\ getr R3 (reg 21) = Z_to_bv 64 (8 * Z.of_nat nd - 8) /\ getr R3 (reg 22) = Z_to_bv 64 (Z.of_nat nd - 1)
      /\ at_shl1 R3 sp od px C0 /\ L5.u32_at RSEGS M3 px C0
      /\ (forall a : word, ~ (px <= bv_unsigned a < px + 4) -> M3 a = M1 a) /\ mem_grows M1 M3).
  { pose proof (br_22394 fx1 R1 M1) as BR. rewrite B10, <- rl0, getr_zero in BR.
    destruct (Z_lt_le_dec w0 (2 ^ 63)) as [POS|NEG].
    - (* [comment removed for export] *)
      rewrite (lts0_pos w0) in BR by lia.
      pose proof (li_22398 fx1 R1 M1) as LI.
      set (R1' := regupd R1 (reg 11) (Z_to_bv 64 0)) in LI.
      assert (Y10: getr R1' (10%bv : bv 5) = Z_to_bv 64 w0). { subst R1'. rewrite getr_other. rewrite rl10. exact B10. rewrite <- rl11. discriminate. }
      assert (Y11: getr R1' (11%bv : bv 5) = Z_to_bv 64 0). { subst R1'. rewrite rl11. apply getr_same. rewrite <- rl11. discriminate. }
      destruct (clz_loop M1 (seg_rom RSEGS) R1' w0 0 Y10 Y11 ltac:(lia) ltac:(lia)) as (c & R2 & Hc & Hpow & Z10 & Z11 & ZK & MSC).
      assert (EC: c = C0). { unfold C0. apply clz_of_unique; lia. }
      subst c. rewrite Z.add_0_l in Z11.
      assert (K2: forall i, i <> 10%nat -> i <> 11%nat -> (i < 32)%nat -> getr R2 (reg i) = getr R1 (reg i)).
      { intros i Hi10 Hi11 Hi32. rewrite ZK. subst R1'. rewrite getr_other. reflexivity.
        all: try rewrite r10; try rewrite r11; intros E; apply (f_equal bv_unsigned) in E;
             rewrite !Z_to_bv_small in E by (unfold bv_modulus; replace (2 ^ Z.of_N 5) with 32 by reflexivity; lia); lia. }
      assert (PW1: L5.writable RSEGS M1 px 4). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG1. exact DEFp. lia. lia. }
      assert (R2_2: getr R2 (reg 2) = Z_to_bv 64 (sp - 64)) by (rewrite (K2 2%nat) by lia; exact B2).
      assert (R2_9: getr R2 (reg 9) = Z_to_bv 64 od) by (rewrite (K2 9%nat) by lia; exact B9).
      assert (R2_11: getr R2 (reg 11) = Z_to_bv 64 C0) by (rewrite <- rl11; exact Z11).
      assert (R2_18: getr R2 (reg 18) = Z_to_bv 64 px) by (rewrite (K2 18%nat) by lia; exact B18).
      destruct (nzB_conc fx1 R0 R2 M1 sp od px C0 SP ltac:(fsclia) ltac:(lia) P4 ltac:(unfold apart; lia) PW1 ltac:(lia) ltac:(lia) R2_2 R2_9 R2_11 R2_18)
        as (fx3 & R3 & M3 & MS3 & K3 & ATS & PX3 & FR3 & MG3).
      assert (E1: (0x224d4%bv : word) = Z_to_bv 64 0x224d4) by (apply bv_eq; reflexivity).
      assert (E2: (0x224e0%bv : word) = Z_to_bv 64 0x224e0) by (apply bv_eq; reflexivity).
      rewrite E1, E2 in MSC.
      exists fx3, R3, M3. split.
      { eapply msteps_trans. exact BR. eapply msteps_trans. exact LI. eapply msteps_trans. exact MSC. exact MS3. }
      assert (K23: forall i, i <> 10%nat -> i <> 11%nat -> (i < 32)%nat -> In i KSB -> getr R3 (reg i) = getr R1 (reg i)).
      { intros i I1 I2 I3 I4. rewrite (K3 i I4). apply K2; assumption. }
      split. { intros i Hi. rewrite K23. apply PASS1. exact Hi. all: revert Hi; cbn; intros Hi; decompose [or] Hi; subst; try lia; try (vm_compute; tauto); contradiction. }
      split. { rewrite K23 by first [lia | vm_compute; tauto]. exact B8. }
      split. { rewrite K23 by first [lia | vm_compute; tauto]. exact B19. }
      split. { rewrite K23 by first [lia | vm_compute; tauto]. exact B20. }
      split. { rewrite K23 by first [lia | vm_compute; tauto]. exact B21. }
      split. { rewrite K23 by first [lia | vm_compute; tauto]. exact B22. }
      split. exact ATS. split. exact PX3. split. exact FR3. exact MG3.
    - (* [comment removed for export] *)
      rewrite (lts0_neg w0) in BR by lia.
      assert (C00: C0 = 0). { unfold C0. symmetry. apply clz_of_unique. lia. lia. rewrite Z.pow_0_r. lia. }
      assert (PW1: L5.writable RSEGS M1 px 4). { apply (L5C.writable_of_defined RSEGS). eapply L5.defined_grows. exact MG1. exact DEFp. lia. lia. }
      destruct (nzN_conc fx1 R0 R1 M1 sp od px SP ltac:(fsclia) ltac:(lia) P4 ltac:(unfold apart; lia) PW1 ltac:(lia) B2 B9 B18)
        as (fx3 & R3 & M3 & MS3 & K3 & ATS & PX3 & FR3 & MG3).
      exists fx3, R3, M3. split. { eapply msteps_trans. exact BR. exact MS3. }
      split. { intros i Hi. rewrite (K3 i). apply PASS1. exact Hi. revert Hi. apply (L5K.incl_b cs_pass KSN ltac:(vm_compute; reflexivity)). }
      split. { rewrite (K3 8%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact B8. }
      split. { rewrite (K3 19%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact B19. }
      split. { rewrite (K3 20%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact B20. }
      split. { rewrite (K3 21%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact B21. }
      split. { rewrite (K3 22%nat) by (apply L5K.in_b; vm_compute; reflexivity). exact B22. }
      rewrite C00. split. exact ATS. split. exact PX3. split. exact FR3. exact MG3. }
  clear K1 B10 B11.
  destruct TOSHL as (fx3 & R3 & M3 & MS3 & PASS3 & C8 & C19 & C20 & C21 & C22 & (A1 & A2 & A9 & A10 & A11 & A18) & PX3 & FR3 & MG3).
  assert (FR3z: forall a, 0 <= a < 2 ^ 64 -> ~ (px <= a < px + 4) -> M3 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR3. rewrite BG.unsigned_lit by lia. exact Hna. }
  assert (FR03: forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 <= a < sp) -> ~ (px <= a < px + 4) -> M3 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha X Y. rewrite FR3z by lia. apply FR1z; lia. }
  assert (MG3': mem_grows M0 M3) by (eapply mem_grows_trans; [exact MG1 | exact MG3]).
  eapply (L5.cps_of_msteps RSEGS). exact Mh. exact Ml. exact MS3.
  (* [comment removed for export] *)
  assert (HH3: hi_heap HI LB cr M3 (m_vmmaps model0)).
  { eapply (L5C.hi_heap_client L SCFG HI LB cr M0 M3). exact HIok. exact HH0. exact (ly_ro L LY). rewrite IMG; lia. lia.
    intros a Ha. destruct (Z_lt_le_dec a (sp - 64)) as [X|X]. left; apply FR03; lia.
    destruct (Z_lt_le_dec a sp) as [Y|Y]. right; left; fsclia.
    destruct (Z_lt_le_dec a px) as [U|U]. left; apply FR03; lia.
    destruct (Z_lt_le_dec a (px + 4)) as [V|V]. right; left; fsclia. left; apply FR03; lia. exact MG3'. }
  (* [comment removed for export] *)
  assert (KEEP03: forall a, sp <= a < 2 ^ 64 -> ~ (px <= a < px + 4) -> M3 (Z_to_bv 64 a) = M0 (Z_to_bv 64 a)).
  { intros a Ha Hna. apply FR03; lia. }
  assert (OBd3: L5.big_at RSEGS M3 od bd).
  { eapply (L5C.big_at_agree RSEGS M0 M3). intros i Hi. apply KEEP03. lia. unfold apart in APpd. lia. lia. lia. exact OBd. }
  assert (OBn3: L5.big_at RSEGS M3 on bn).
  { eapply (L5C.big_at_agree RSEGS M0 M3). intros i Hi. apply KEEP03. lia. unfold apart in APpn. lia. lia. lia. exact OBn. }
  assert (OL3: forall o b ws, L5.big_at RSEGS M0 o b -> L5C.obj_limbs RSEGS M0 b ws ->
               (forall cap q, L5.bo_st b = L5.BDyn cap q -> In (q, 8 * cap) LB /\ Z.of_nat (L5.bo_len b) + 1 <= cap /\ apart px 4 q (8 * cap)) ->
               L5C.obj_limbs RSEGS M3 b ws).
  { intros o b ws OB (L1 & L2 & L3) BLK. split. exact L1. split. exact L2. destruct (L5.bo_st b) as [v0 v1|cap q] eqn:EST. exact L3.
    destruct (BLK cap q eq_refl) as (INq & CAPq & _). pose proof (LBhi0 _ INq) as BH. cbn in BH.
    pose proof (LBdef _ _ _ _ HH0 q (8 * cap) INq) as (_ & QLO & _).
    eapply (L5C.limbs_at_agree RSEGS M0 M3). 2: lia. 3: exact L3. 2: lia. intros i Hi. apply FR03; fsclia. }
  pose proof (OL3 od bd wd OBd OLd BLKd) as OLd3. pose proof (OL3 on bn wn OBn OLn BLKn) as OLn3. clear OL3.
  (* [comment removed for export] *)
  eapply (shl_ok fx3 R3 M3 model0 K LB cr od (sp - 64) AFTER1 C0 bd wd HH3 MOK0 HK0).
  + rewrite r10. exact A10.
  + rewrite r11. exact A11.
  + lia.
  + rewrite r1. exact A1.
  + split. unfold AFTER1. lia. reflexivity.
  + rewrite r2. exact A2.
  + rewrite r4. rewrite (PASS3 4%nat) by (cbn; tauto). exact G4.
  + split. { replace (sp - 64) with (sp + (-4) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
    split. fsclia. split. lia. split. lia. uSCR. eapply L5.defined_grows. exact MG3'. eapply L5.defined_sub. exact DEF. lia. lia.
  + exact OBd3.
  + exact OLd3.
  + fold nd. lia.
  + exact Aod. + lia. + lia.
  + eapply L5.defined_grows. exact MG3'. exact DEFd.
  + unfold L5.bo_dyn, L5.bo_cap. destruct (L5.bo_st bd) as [v0 v1|cap q] eqn:EST.
    { destruct BDS as [X _]. unfold L5.bo_dyn in X. intros Y. congruence. }
    intros _. destruct (BLKd cap q eq_refl) as (_ & X & _). fold nd in X. lia.
  + (* [comment removed for export] *)
    intros _ _ DYf. destruct CR as [CRa CRb]. unfold cnt in CRa, CRb. rewrite DYf in CRa, CRb. rewrite round_up_3.
    unfold credit_ok. destruct (L5.bo_dyn bn); cbn [Z.add] in CRa, CRb; lia.
  + intros cap q EST. exact (proj1 (BLKd cap q EST)).
  + (* [comment removed for export] *)
    intros fx5 R5 M5 model5 g5 LB5 cr5 POST MBV5 HH5.
    unfold L5SHL.shl_post in POST. cbv zeta in POST.
    destruct POST as (RP5 & B10 & st5 & OB5 & OL5 & NLE5 & GG).
    fold D in OB5, OL5, NLE5, GG.
    set (fbd := match g5 with Same => L5.bo_fb bd | Grown _ _ => Z.lor (L5.bo_fb bd) 1 end) in *.
    pose proof D_len as DLEN. pose proof D_ok as DOK.
    assert (LDle: (length D <= S nd)%nat) by (rewrite DLEN; destruct (C0 =? 0); lia).
    (* [comment removed for export] *)
    assert (QN: forall cap0 q0, L5.bo_st bn = L5.BDyn cap0 q0 ->
                In (q0, 8 * cap0) LB /\ q0 + 8 * cap0 <= hl_sptop L - 8388608 /\ (4096 <= q0 /\ (q0 + 8 * cap0 <= 0x10000 \/ 0x91000 <= q0))
                /\ (forall cd0 qd0, L5.bo_st bd = L5.BDyn cd0 qd0 -> apart qd0 (8 * cd0) q0 (8 * cap0))).
    { intros cap0 q0 EST. destruct (BLKn cap0 q0 EST) as (INn & _ & _). pose proof (LBhi0 _ INn) as BH. cbn in BH.
      pose proof (LBdef _ _ _ _ HH0 q0 (8 * cap0) INn) as (_ & QLO & _). rewrite IMG, IMGLO in QLO.
      split. exact INn. split. exact BH. split. exact QLO. intros cd0 qd0 ESTd. exact (APB cd0 qd0 cap0 q0 ESTd EST). }
    (* [comment removed for export] *)
    assert (PKG: exists W5 qd capd,
       L5C.hpres L LB (sp - 64) L5SHL.SHL_SCR W5 M3 M5 /\
       LB5 = blocks_of g5 ++ LB /\ cr5 = debits L cr (blocks_of g5) /\
       (forall a, sp - 64 <= a -> ~ (od <= a < od + 32) -> L5.outside W5 a) /\
       (forall cap0 q0, L5.bo_st bn = L5.BDyn cap0 q0 -> forall a, q0 <= a < q0 + 8 * cap0 -> L5.outside W5 a) /\
       (forall a, L5C.kept L LB sp NORM_SCR W a -> L5.outside W5 a) /\
       obj_after M5 od bd D g5 st5 /\ limb_loc bd od g5 st5 qd capd /\
       (match g5 with Same => True | Grown A cap => L5C.fresh_block L LB M5 A (8 * cap) end) /\
       (match g5 with Same => True | Grown _ _ => (3 <= length D)%nat end)).
    { destruct g5 as [|A5 c5].
      - (* [comment removed for export] *)
        destruct GG as (DS & ELB5 & ECR5 & STM & HP5).
        destruct (L5.bo_st bd) as [u0 u1|cd0 qd0] eqn:EST.
        + destruct st5 as [z0 z1|c' q']; [|contradiction].
          destruct BDS as [DYd NDle].
          assert (LDn: (length D <= 2)%nat) by (destruct DS as [X|X]; [congruence|exact X]).
          exists [(od, 32); (L5.bo_data od bd, 8 * Z.of_nat (length D))], (od + 16), 2.
          unfold L5.bo_data. rewrite EST.
          split. { unfold L5.bo_data in HP5. rewrite EST in HP5. exact HP5. }
          split. { cbn. exact ELB5. } split. { cbn. exact ECR5. }
          split. { intros a Ha Hna. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
          split. { intros cap0 q0 ESTn a Ha. destruct (QN cap0 q0 ESTn) as (_ & QHI & _ & _).
                   apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
          split. { intros a KA. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW.
                   pose proof (L5HP.outside_in _ _ od 32 OW ltac:(unfold W, norm_W; cbn; tauto)) as X.
                   apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
          split. { unfold obj_after. cbv zeta. fold fbd. split. exact DOK. split. exact NLE5. split. exact OB5. split. exact OL5. split. exact LDn.
                   rewrite EST. exact I. }
          split. { cbn. repeat split; auto. }
          split; exact I.
        + destruct st5 as [z0 z1|c' q']; [contradiction|]. destruct STM as [-> ->].
          destruct BDS as (DY & NDC & CAPR & Q8 & QLO & QHI).
          destruct (BLKd cd0 qd0 eq_refl) as (INd & CAPd1 & APXd). fold nd in CAPd1.
          pose proof (LBhi0 _ INd) as BHd. cbn in BHd.
          exists [(od, 32); (L5.bo_data od bd, 8 * Z.of_nat (length D))], qd0, cd0.
          unfold L5.bo_data. rewrite EST.
          split. { unfold L5.bo_data in HP5. rewrite EST in HP5. exact HP5. }
          split. { cbn. exact ELB5. } split. { cbn. exact ECR5. }
          split. { intros a Ha Hna. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_cons. unfold L5.in_rng; cbn. lia. apply L5C.outside_nil. }
          split. { intros cap0 q0 ESTn a Ha. destruct (QN cap0 q0 ESTn) as (_ & QHIn & _ & APQ). pose proof (APQ cd0 qd0 eq_refl) as AP. unfold apart in AP.
                   apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_cons. unfold L5.in_rng; cbn. lia. apply L5C.outside_nil. }
          split. { intros a KA. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW.
                   pose proof (L5HP.outside_in _ _ od 32 OW ltac:(unfold W, norm_W; cbn; tauto)) as X.
                   pose proof (L5HP.outside_in _ _ qd0 (8 * cd0) OW ltac:(unfold W, norm_W, dyn_area; rewrite EST; rewrite !in_app_iff; cbn; tauto)) as Y.
                   apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_cons. unfold L5.in_rng; cbn. lia. apply L5C.outside_nil. }
          split. { unfold obj_after. cbv zeta. fold fbd. split. exact DOK. split. exact NLE5. split. exact OB5. split. exact OL5. split. lia.
                   rewrite EST. split; reflexivity. }
          split. { cbn. repeat split; auto. }
          split. exact I. exact I.
      - (* [comment removed for export] *)
        destruct GG as (DYd & M3' & CAPE & ELB5 & ECR5 & FB5 & EST5 & HP5). subst st5.
        destruct (L5.bo_st bd) as [u0 u1|cd0 qd0] eqn:EST. 2:{ destruct BDS as [DY _]. congruence. }
        destruct BDS as [_ NDle].
        assert (L3: length D = 3%nat) by lia.
        assert (C8': c5 = 8). { rewrite CAPE, L3. reflexivity. }
        clear CAPE. subst c5.
        pose proof FB5 as (BR5 & BA5 & BDEF5). pose proof BR5 as (B50 & B51 & B52 & B53 & B54).
        exists [(od, 32)], A5, 8.
        split. exact HP5.
        split. { cbn. exact ELB5. } split. { cbn. exact ECR5. }
        split. { intros a Ha Hna. apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
        split. { intros cap0 q0 ESTn a Ha. destruct (QN cap0 q0 ESTn) as (_ & QHIn & _ & _).
                 apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
        split. { intros a KA. pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW.
                 pose proof (L5HP.outside_in _ _ od 32 OW ltac:(unfold W, norm_W; cbn; tauto)) as X.
                 apply L5C.outside_cons. unfold L5.in_rng; cbn; lia. apply L5C.outside_nil. }
        split. { unfold obj_after. cbv zeta. fold fbd. split. exact DOK. split. exact NLE5. split. exact OB5. split. exact OL5. split. lia.
                 split. exact DYd. split; reflexivity. }
        split. { cbn. repeat split; auto. }
        split. exact FB5. clear - L3; lia. }
    clear GG.
    destruct PKG as (W5 & qd & capd & HP5 & ELB5 & ECR5 & OUT5 & OUTB & OUTW & OAd5 & LLd5 & FRd5 & GWd5).
    (* [comment removed for export] *)
    assert (KST: forall a, sp - 64 <= a < 2 ^ 64 -> ~ (od <= a < od + 32) -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros a Ha Hna. apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). apply L5C.kept_stack. fsclia. fsclia. flia. exact ERRNO. exact (proj1 SPTOP).
      apply OUT5; flia. }
    assert (KBN: forall cap0 q0, L5.bo_st bn = L5.BDyn cap0 q0 -> forall a, q0 <= a < q0 + 8 * cap0 -> M5 (Z_to_bv 64 a) = M3 (Z_to_bv 64 a)).
    { intros cap0 q0 ESTn a Ha. destruct (QN cap0 q0 ESTn) as (INn & QHIn & QLOn & _).
      apply (L5C.hpres_kept _ _ _ _ _ _ _ a HP5). eapply L5C.kept_block. exact INn. flia. flia. flia. rewrite ERRNOV. flia.
      apply (OUTB cap0 q0 ESTn). flia. }
    assert (SV5: saved M5 sp R0).
    { destruct SV1 as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8).
      repeat split; (eapply u64_at_agree1; [intros i Hi; rewrite KST by flia; apply FR3z; flia | flia | flia | assumption]). }
    assert (DEF5: L5.defined M5 (sp - NORM_SCR) NORM_SCR).
    { intros i Hi. destruct (Z_lt_le_dec (sp - NORM_SCR + i) (sp - 64)) as [X|X].
      - pose proof (L5C.hpres_defined _ _ _ _ _ _ _ HP5) as D5. uSCR.
        replace (sp - (64 + (48 + (64 + (64 + (64 + (16 + 8224)))))) + i) with (sp - 64 - (48 + (64 + (64 + (64 + (16 + 8224))))) + i) by lia. apply D5. lia.
      - rewrite KST. apply MG3'. apply DEF. lia. fsclia. fsclia. }
    assert (PX5: L5.u32_at RSEGS M5 px C0). { eapply u32_at_agree1. intros i Hi. apply KST. flia. unfold apart in APpd. flia. flia. flia. exact PX3. }
    assert (OBn5: L5.big_at RSEGS M5 on bn).
    { eapply (L5C.big_at_agree RSEGS M3 M5). intros i Hi. apply KST. flia. unfold apart in APdn. flia. flia. flia. exact OBn3. }
    assert (OLn5: L5C.obj_limbs RSEGS M5 bn wn).
    { destruct OLn3 as (L1 & L2 & L3). split. exact L1. split. exact L2. destruct (L5.bo_st bn) as [v0 v1|cap0 q0] eqn:ESTn. exact L3.
      destruct (QN cap0 q0 eq_refl) as (INn & QHIn & QLOn & _). destruct (BLKn cap0 q0 eq_refl) as (_ & CAPn1 & _). pose proof wn_len as WNL.
      eapply (L5C.limbs_at_agree RSEGS M3 M5). 2: flia. 3: exact L3. 2: flia. intros i Hi. apply (KBN cap0 q0 eq_refl). unfold L5.bo_len in CAPn1. fold nn in CAPn1. flia. }
    assert (DEFn5: L5.defined M5 on 32).
    { intros i Hi. rewrite KST. apply MG3'. apply DEFn. exact Hi. flia. unfold apart in APdn. flia. }
    assert (HP03: L5C.hpres L LB sp NORM_SCR W M0 M3).
    { apply (L5HP.hpres_piece L LB sp NORM_SCR W M0 M3 (fun a => (sp - 64 <= a < sp) \/ (px <= a < px + 4))).
      - intros a Ha Hn. apply FR03. exact Ha. tauto. tauto.
      - intros a KA [X|X].
        + exact (L5HP.kept_not_in_scratch L LB sp NORM_SCR W a KA LBhi0 ltac:(fsclia) ltac:(rewrite IMG; flia) ltac:(fsclia)).
        + pose proof (L5HP.kept_outside_W _ _ _ _ _ _ KA) as OW. exact (L5HP.outside_in _ _ px 4 OW ltac:(unfold W, norm_W; cbn; tauto) X).
      - eapply L5.defined_grows. exact MG3'. exact DEF.
      - exact MG3'. }
    assert (HPA: L5C.hpres L LB sp NORM_SCR W M0 M5).
    { eapply (L5HP.hpres_trans L LB LB). exact HP03. exact HP5.
      - intros a KA. eapply L5HP.kept_mono. exact KA. { intros b Hb. exact Hb. } fsclia. flia.
        intros _. apply OUTW. exact KA.
      - intros b Hb. exact Hb.
      - fsclia. - flia. - fsclia. - exact ERRNO. - exact (proj1 SPTOP). }
    (* [comment removed for export] *)
    assert (E2: getr R5 (reg 2) = Z_to_bv 64 (sp - 64)). { rewrite (preserved_sregs R3 R5 2 RP5) by (cbn; tauto). exact A2. }
    assert (E8: getr R5 (reg 8) = Z_to_bv 64 on). { rewrite (preserved_sregs R3 R5 8 RP5) by (cbn; tauto). exact C8. }
    assert (E9: getr R5 (reg 9) = Z_to_bv 64 od). { rewrite (preserved_sregs R3 R5 9 RP5) by (cbn; tauto). exact A9. }
    assert (E18: getr R5 (reg 18) = Z_to_bv 64 px). { rewrite (preserved_sregs R3 R5 18 RP5) by (cbn; tauto). exact A18. }
    assert (E19: getr R5 (reg 19) = Z_to_bv 64 (Z.of_nat nd)). { rewrite (preserved_sregs R3 R5 19 RP5) by (cbn; tauto). exact C19. }
    assert (E20: getr R5 (reg 20) = Z_to_bv 64 (od + 16)). { rewrite (preserved_sregs R3 R5 20 RP5) by (cbn; tauto). exact C20. }
    assert (E21: getr R5 (reg 21) = Z_to_bv 64 (8 * Z.of_nat nd - 8)). { rewrite (preserved_sregs R3 R5 21 RP5) by (cbn; tauto). exact C21. }
    assert (E22: getr R5 (reg 22) = Z_to_bv 64 (Z.of_nat nd - 1)). { rewrite (preserved_sregs R3 R5 22 RP5) by (cbn; tauto). exact C22. }
    eapply (stageD fx5 R5 M5 model5 (blocks_of g5 ++ LB) cr5 g5 st5 qd capd E2 E8 E9 E18 E19 E20 E21 E22).
    * intros i Hi. rewrite (preserved_sregs R3 R5 i RP5) by (revert Hi; apply (L5K.incl_b cs_pass cs_all ltac:(vm_compute; reflexivity))). apply PASS3. exact Hi.
    * exact MBV5.
    * rewrite <- ELB5. exact HH5.
    * exact SV5. * exact DEF5. * exact PX5.
    * exact OAd5. * exact LLd5.
    * exact OBn5. * exact OLn5. * exact DEFn5.
    * (* [comment removed for export] *)
      intros DYf. destruct CR as [CRa CRb]. unfold cnt in CRa, CRb. rewrite DYf in CRa, CRb. rewrite round_up_3. rewrite ECR5.
      unfold credit_ok. destruct g5 as [|A5 c5]; cbn [blocks_of debits].
      -- destruct (L5.bo_dyn bd); cbn [Z.add] in CRa, CRb; flia.
      -- unfold debit. cbn [fst snd]. pose proof OAd5 as X. unfold obj_after in X. cbv zeta in X. destruct X as (_ & _ & _ & _ & _ & DYd & C8' & _).
         rewrite DYd in CRa, CRb. subst c5. cbn [Z.add Z.mul] in CRa, CRb |- *. flia.
    * reflexivity.
    * exact ECR5.
    * exact FRd5.
    * exact HPA.
    * exact GWd5.
Qed.
End Call.

(* [comment removed for export] *)
Theorem norm_ok : norm_spec L HI.
Proof.
  intros fx R M model K LB cr od on px sp r bd bn wd wn HH MOK HK0 G11 G12 G13 G1 RA G2 G4 STK OBd OLd Hnd TOPnz TOPsm OBn OLn Hnn NN2
         Aod Aon Sod Son Hod Hon APdn DEFd DEFn P4 Spx Hpx APpd APpn DEFp BLKd BLKn SECcap APB CR KONT.
  eapply stageA; eassumption.
Qed.

End WithHeap.
End SCFG_1.

End L5NORMOK.
