(* fuzz_state: enqueue (lib/A/AFew.v) under ARU for ANY set UP of user-poisoned heads: tfib_enqueue_roomU, tfib_enqueue_nbU. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The twins of the released cgif_file_fuzzer theorems tfib_enqueue_room (lib/A/AFg4.v:381) and tfib_enqueue_nb
   (lib/A/AFg6.v:904). The donor walks are kept: their facts, their runs (AFh3.segP, AFh4.segQH, AFh5.segR1, AFh6.segT)
   and their leaf lemmas (AFg4.FINPH, AFg5.FINQH, AFg6.FINR) are applied unchanged, over FSupoison.unpoison UP mem where
   they read memory and over the real memory where the machine runs; FSupoisonAllocFeqR.v carries the two transfers.
   UP survives the call: enqueue keeps st_chunks (its leaf says so), so every UP range stays in a live block, and the
   new batch is a batch-class chunk, never a live block, so the run's write window stays in application memory, off
   UP's shadow. *)
(* Modified by Theorem Labs, 2026-10: each arm proves enq_leafU's raw frame from its runs' frames on the real memory (FSupoisonAllocFeqR's at_*_u) read through the donors' AFf1.D_owned / AFf2.D_owned, and the miss arm composes them with the refill leaf's raw frame: raw memory frame re-exported for the ARU lift of route 1. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG02 YG06 YG07 YG03 YG0f YG0v YG0n YG0d YG0s YG0q YG0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0l YG0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0 AFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AFeq AFex AFf0 AFf1 AFf2 AFgi AFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj YFfk YFfp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFew AFgp AFgq AFgr AFh3 AFh4 AFh5 AFh6 AFg3 AFft AFfq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AFg4 AFg5 AFg6.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU FSupoisonAllocR FSupoisonAllocFK FSupoisonAllocFeqR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFK.
Module FeqR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonAllocFeqR.

Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis TB : TfibSyms B.
Variables (ly : alayout) (X : astate) (UP : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
          (mem : word -> option byte) (md : Model) (k : chunk).
Hypothesis ENQU : FK.enq_preU B ly X UP W regs mem md k.
Local Notation mu := (FSP.unpoison UP mem).

Lemma PRE_u : enq_pre B ly X W regs mu md k. Proof. exact (proj1 ENQU). Qed.
Lemma OK0 : FSP.upoison_ok B ly X UP. Proof. exact (proj1 (proj2 ENQU)). Qed.
Lemma PO0 : FSP.upoisoned tfibsegs W mem UP. Proof. exact (proj2 (proj2 ENQU)). Qed.
Lemma ARUx : FSP.ARU tfibsegs B ly X UP W mem md.
Proof. exact (conj (proj1 PRE_u) (conj OK0 PO0)). Qed.
Lemma HTSD : ly_tsd ly = TFIB_TSD.
Proof. pose proof PRE_u as ((M0 & _) & _). rewrite (am_tsd B ly X _ M0). exact (ts_tsd _ TB). Qed.

(* enqueue never frees a chunk: whatever it does to the quarantine, st_chunks is the one of X (enq_leaf), so every
   live block that holds a UP range is still a live block of the new state. *)
Lemma ablocks_of_chunks : forall X', st_chunks X' = st_chunks X -> ablocks B ly X' = ablocks B ly X.
Proof. intros X' E. unfold ablocks, blocks. rewrite E. reflexivity. Qed.

Lemma upoison_ok_keep_chunks : forall X', st_chunks X' = st_chunks X -> FSP.upoison_ok B ly X' UP.
Proof.
intros X' E. apply (FAR.upoison_ok_keep B ly X ly X' UP OK0).
intros r p n _ Hb _ _. rewrite (ablocks_of_chunks X' E). exact Hb.
Qed.

(* The donor's return configuration, in the two shapes cfg_at and mkCfg. *)
Lemma cfg_ret : forall (regs' : bvmap 5 word) (m0 : word -> option byte) (md' : Model),
  mkCfg (YK11.mkst regs' (YK11.getr regs 1) m0 (YK11.seg_rom tfibsegs)) md' = cfg_at tfibsegs (raZ regs) regs' m0 md'.
Proof. intros regs' m0 md'. unfold cfg_at, raZ, w64. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 1. Room in the last batch (lib/A/AFg4.v:371 tfib_enqueue_room_arm).                                               *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section room.
Hypothesis HNB : need_new_batch (st_qthread X) = false.

(* The room run's write window (AFgp.WIN at the donor's last batch) is owned by X or in Enqueue's stack window: the
   window lies in the donor's D (as in AFg4.FINPH), and AFf1.D_owned places D; ownership reads no memory, so the
   donor's facts at the unpoisoned reading serve. *)
Lemma WINP_own : forall a, 0 <= a < 2 ^ 64 -> AFgp.WIN ly regs (AFg4.QLv ly X) (AFg4.CNTv X) a ->
  aowned B ly X a \/ (spZ regs - QSTACK <= a < spZ regs) \/ False.
Proof.
intros a Ha HW.
assert (HD : AFf1.D ly (AFg4.lb X) (bv_unsigned (getr regs 2)) a).
{ unfold AFf1.D, AFf1.DT, AFf1.DL, AFf1.DS, AFf1.QLv, AFf1.CNTv.
  unfold AFgp.WIN, AFgp.SLv in HW. unfold AFg4.QLv, AFg4.CNTv in HW.
  destruct HW as [HW|[HW|[HW|HW]]];
    [do 2 right; clear - HW; unfold QSTACK in *; lia | left; exact HW | right; left; left; exact HW
    | right; left; right; lia]. }
destruct (AFf1.D_owned B ly X (aview tfibsegs (w_H W) mu) (AFg4.M B ly X W regs mu md k PRE_u)
  (AFg4.lb X) (AFg4.initr X) (AFg4.Hrev X HNB) (AFg4.Hroom B ly X W regs mu md k PRE_u HNB)
  (bv_unsigned (getr regs 2)) (AFg4.HSP B ly X W regs mu md k PRE_u)
  (AFg4.IMG B ly X W regs mu md k PRE_u) a (proj1 Ha) HD) as [O|O].
- left. exact O.
- right; left. unfold AFf1.DS in O. unfold spZ. exact O.
Qed.

Theorem tfib_enqueue_room_armU :
  amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (FK.enq_leafU B ly X UP W regs mem md k).
Proof.
first [ pose proof (AFg4.FH_ok B TB ly X W regs mu md k PRE_u HNB) as FHmu
      | pose proof (AFg4.FH_ok B TB ly X W regs mu md k PRE_u HNB HTSD) as FHmu
      | pose proof (AFg4.FH_ok B ly X W regs mu md k PRE_u HNB) as FHmu ].
pose proof (FeqR.FHp_real B ly X UP W mem md ARUx regs _ _ _ _ _ _ _ FHmu) as FHreal.
rewrite (enqueue_room_eq k X HNB). cbn [amreal].
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- exact (AFh3.segP W ly regs mem md _ _ _ _ _ _ _ (m_vm_materialized md) FHreal).
- intros W' c' _ HR.
  destruct (FeqR.at_RETP_u B ly X UP W mem md ARUx regs _ _ _ _ _ _ _ W' c' FHmu HR)
    as (regs' & mem' & mat & -> & -> & HRu & PO & MEQ).
  assert (LEAF : enq_leaf B ly X W regs mu md k (tt, AFf1.S' X k) W
                   (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs))
                          (with_vm_backing (m_vm_lazy md) mat md)))
    by (eapply AFg4.FINPH; first [exact TB | exact PRE_u | exact HNB | exact HTSD | exact HRu]).
  pose proof LEAF as LEAF0.
  destruct LEAF0 as (rr & mm & dd & nb & E1 & POST & QT1 & QT2 & QTc & QTg & QTf).
  rewrite (cfg_ret regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  apply (FK.enq_leafU_intro B ly X UP W regs mem md k _ W regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  + rewrite <- (cfg_ret regs' (FSP.unpoison UP mem') (with_vm_backing (m_vm_lazy md) mat md)). exact LEAF.
  + exact (upoison_ok_keep_chunks _ QTc).
  + exact PO.
  + exact (FK.raw_of_meq B ly X _ QSTACK regs (fun _ => False) _ mem mem' MEQ WINP_own).
Qed.
End room.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. A new batch, taken from the batch-class cache (lib/A/AFg5.v:629 tfib_enqueue_hit_arm).                          *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section hit.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Hypothesis Hne : pc_chunks (cache X kBatchClass) <> [].
Local Notation lc := (pc_chunks (cache X kBatchClass)).

Lemma HC5 : 1 <= Z.of_nat (length lc).
Proof.
destruct (pc_chunks (cache X kBatchClass)) as [|z zs];
  [exfalso; apply Hne; reflexivity | cbn [length]; lia].
Qed.

(* The hit run's write window (AFgq.WIN) is owned by X or in Enqueue's stack window: in the donor's D (as in
   AFg5.FINQH), placed by AFf2.D_owned. *)
Lemma WINQ_own : forall a, 0 <= a < 2 ^ 64 -> AFgq.WIN ly regs (st_qthread X) (AFg5.cnt lc) (AFg5.coff lc) a ->
  aowned B ly X a \/ (spZ regs - QSTACK <= a < spZ regs) \/ False.
Proof.
intros a Ha HW.
assert (ENB : AFgq.NBv ly (AFg5.coff lc) = ly_space ly + (region_off kBatchClass + last lc 0))
  by (unfold AFgq.NBv, AFg5.coff; lia).
assert (HD : AFf2.D ly X lc (bv_unsigned (getr regs 2)) a).
{ unfold AFf2.D, AFf2.DT, AFf2.DN, AFf2.DL, AFf2.DS.
  unfold AFgq.WIN, AFgq.WINT, AFgq.WINA in HW. rewrite ENB in HW.
  destruct HW as [HW|[HW|[[_ HW]|[Hq HW]]]].
  - do 3 right. clear - HW. unfold QSTACK. lia.
  - left. exact HW.
  - right; left. exact HW.
  - right; right; left. split; [exact Hq|]. unfold AFf2.QLv. unfold AFgq.QLv in HW. exact HW. }
destruct (AFf2.D_owned B ly X (aview tfibsegs (w_H W) mu) (AFg5.M B ly X W regs mu md k PRE_u) k
  (AFg5.Hci B ly X W regs mu md k PRE_u lc eq_refl Hne) lc eq_refl Hne (bv_unsigned (getr regs 2))
  (AFg5.HSP B ly X W regs mu md k PRE_u) a (proj1 Ha) HD) as [O|O].
- left. exact O.
- right; left. unfold AFf2.DS in O. unfold spZ. exact O.
Qed.

Theorem tfib_enqueue_hit_armU :
  amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (FK.enq_leafU B ly X UP W regs mem md k).
Proof.
first [ pose proof (AFg5.FH_ok B TB ly X W regs mu md k PRE_u HNB lc eq_refl Hne) as FHmu
      | pose proof (AFg5.FH_ok B TB ly X W regs mu md k PRE_u HNB lc eq_refl Hne HTSD) as FHmu
      | pose proof (AFg5.FH_ok B ly X W regs mu md k PRE_u HNB lc eq_refl Hne) as FHmu ].
pose proof (FeqR.FHq_real B ly X UP W mem md ARUx regs _ _ _ _ _ _ FHmu) as FHreal.
assert (HEQ : enqueue k X = IRet (tt, AFf2.S' X k lc))
  by (eapply AFg5.enqueue_hit_eq; first [exact TB | exact PRE_u | exact HNB | exact Hne | reflexivity]).
rewrite HEQ. cbn [amreal].
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- exact (AFh4.segQH W ly regs mem md _ _ _ _ _ _ (m_vm_materialized md) FHreal HC5).
- intros W' c' _ HR.
  destruct (FeqR.at_RETQ_u B ly X UP W mem md ARUx regs _ _ _ _ _ _ W' c' FHmu HC5 HR)
    as (regs' & mem' & mat & -> & -> & HRu & PO & MEQ).
  assert (LEAF : enq_leaf B ly X W regs mu md k (tt, AFf2.S' X k lc) W
                   (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs))
                          (with_vm_backing (m_vm_lazy md) mat md)))
    by (eapply AFg5.FINQH; first [exact TB | exact PRE_u | exact HNB | exact Hne | exact HTSD | exact HRu | reflexivity]).
  pose proof LEAF as LEAF0.
  destruct LEAF0 as (rr & mm & dd & nb & E1 & POST & QT1 & QT2 & QTc & QTg & QTf).
  rewrite (cfg_ret regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  apply (FK.enq_leafU_intro B ly X UP W regs mem md k _ W regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  + rewrite <- (cfg_ret regs' (FSP.unpoison UP mem') (with_vm_backing (m_vm_lazy md) mat md)). exact LEAF.
  + exact (upoison_ok_keep_chunks _ QTc).
  + exact PO.
  + exact (FK.raw_of_meq B ly X _ QSTACK regs (fun _ => False) _ mem mem' MEQ WINQ_own).
Qed.
End hit.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. A new batch, with the batch-class cache empty: refill first (lib/A/AFg6.v:870 tfib_enqueue_miss_arm).           *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section miss.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Hypothesis Hl0 : pc_chunks (cache X kBatchClass) = [].
Hypothesis R1 : FAR.tfib_refill_specU B.

Theorem tfib_enqueue_miss_armU :
  amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (FK.enq_leafU B ly X UP W regs mem md k).
Proof.
first [ pose proof (AFg6.FH0_ok B TB ly X W regs mu md k PRE_u HNB Hl0) as FH0mu
      | pose proof (AFg6.FH0_ok B TB ly X W regs mu md k PRE_u HNB Hl0 HTSD) as FH0mu
      | pose proof (AFg6.FH0_ok B ly X W regs mu md k PRE_u HNB Hl0) as FH0mu ].
pose proof (FeqR.FHq_real B ly X UP W mem md ARUx regs _ _ _ _ _ _ FH0mu) as FH0real.
apply (amreal_enqueue_nb k X W _ _ HNB).
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
apply amreal_after_SRr. eapply SRr_mono.
- exact (AFh5.segR1 W ly regs mem md _ _ _ _ _ _ (m_vm_materialized md) FH0real eq_refl).
- intros W' c' _ HC.
  destruct (FeqR.at_CALLR_u B ly X UP W mem md ARUx regs _ _ _ _ _ _ W' c' FH0mu HC)
    as (regs1 & mem1 & mat & -> & -> & HCu & PO1 & MR1).
  pose proof HCu as HCu0.
  destruct HCu0 as (_ & regs1' & mem1' & mat' & ECFG & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 &
                    R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
  apply FK.cfg_at_inj in ECFG as (<- & <- & _).
  cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (RPRE : FAR.refill_preU B ly X UP W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) kBatchClass).
  { unfold FAR.refill_preU. split; [|split; [exact OK0 | exact PO1]].
    eapply AFg6.REFILL_PRE; first [exact TB | exact PRE_u | exact HNB | exact Hl0 | exact HTSD | eassumption]. }
  pose proof (R1 ly X UP W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) kBatchClass RPRE) as RR.
  unfold cfg_at, A_Refill in RR.
  assert (WfX1 : WfP (as_universe B) 1 0 0 X) by (eapply AFg6.WfX1; first [exact TB | exact PRE_u]).
  pose proof (AFg6.refill_tree_apostg (as_universe B) 1 0 0 X kBatchClass WfX1 ltac:(unfold kBatchClass; lia)
                ltac:(lia) (proj1 (proj2 (proj1 (proj2 (proj2 (proj2 PRE_u))))))) as APOST.
  pose proof (amreal_apostg tfibsegs (refill_tree kBatchClass X) _ W _ _ APOST RR) as RR2. clear RR.
  eapply amreal_mono; [|exact RR2]. cbv beta.
  intros [[] X1] W5 c5 [(WX1 & RO & CI & NE1) HL]. cbn [fst snd] in WX1, RO, CI, NE1, HL.
  destruct HL as (regs' & mem' & md' & -> & POSTU & HA0 & RRAW).
  destruct POSTU as (POST & OK1 & PO2).
  pose proof (FAR.ARU_intro B ly X1 UP W5 mem' md' (proj1 POST) OK1 PO2) as ARU1.
  unfold enq_after_refill. cbn [snd].
  destruct (pc_chunks (cache X1 kBatchClass)) as [|o1 l1'] eqn:El1.
  + exfalso. apply NE1. first [reflexivity | exact El1].
  + cbn [snd] in HA0. rewrite El1 in HA0.
    assert (FHRmu : AFgr.free_hyps W5 ly regs' (FSP.unpoison UP mem')
              (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X1)
              (Z.of_nat (length (o1 :: l1'))) (last (o1 :: l1') 0) (AFfq.jst ly W5 (FSP.unpoison UP mem'))
              (bv_unsigned (YK11.getr regs 1)) (bv_unsigned (YK11.getr regs 8)) (bv_unsigned (YK11.getr regs 9))
              (bv_unsigned (YK11.getr regs 18)) (bv_unsigned (YK11.getr regs 19)) (bv_unsigned (YK11.getr regs 20))
              (bv_unsigned (YK11.getr regs 21)))
      by (eapply AFg6.FHR_ok;
          first [exact TB | exact PRE_u | exact HNB | exact Hl0 | exact HTSD | exact El1 | eassumption]).
    pose proof (FeqR.FHr_real B ly X1 UP W5 mem' md' ARU1 regs' _ _ _ _ _ _ _ _ _ _ _ _ _ FHRmu) as FHRreal.
    assert (TAILU : SRr tfibsegs W5
              (mkCfg (YK11.mkst regs' (w64 0x36504) mem' (YK11.seg_rom tfibsegs))
                     (with_vm_backing (m_vm_lazy md') (m_vm_materialized md') md'))
              (FK.enq_leafU B ly X UP W regs mem md k (tt, AFf2.S' X1 k (o1 :: l1')))).
    { eapply SRr_mono.
      - exact (AFh6.segT W5 ly regs' mem' md' _ _ _ _ _ _ _ _ _ _ _ _ _ (m_vm_materialized md') FHRreal).
      - intros W6 c6 _ HR6.
        destruct (FeqR.at_RETR_u B ly X1 UP W5 mem' md' ARU1 regs' _ _ _ _ _ _ _ _ _ _ _ _ _ W6 c6 FHRmu HR6)
          as (regs6 & mem6 & mat6 & -> & -> & HR6u & PO6 & MEQ6).
        assert (LEAF : enq_leaf B ly X W regs mu md k (tt, AFf2.S' X1 k (o1 :: l1')) W5
                         (mkCfg (YK11.mkst regs6 (w64 (bv_unsigned (YK11.getr regs 1))) (FSP.unpoison UP mem6)
                                 (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md') mat6 md')))
          by (eapply AFg6.FINR;
              first [exact TB | exact PRE_u | exact HNB | exact Hl0 | exact HTSD | exact El1 | exact HR6u | eassumption]).
        pose proof LEAF as LEAF0.
        destruct LEAF0 as (rr & mm & dd & nb & E1 & POSTl & QT1 & QT2 & QTc & QTg & QTf).
        apply (FK.enq_leafU_intro B ly X UP W regs mem md k _ W5 regs6 mem6 (with_vm_backing (m_vm_lazy md') mat6 md')).
        + exact LEAF.
        + exact (upoison_ok_keep_chunks _ QTc).
        + exact PO6.
        (* The raw frame, mem -> mem1 -> mem' -> mem6: segT's window is in D at X1 (as in AFg6.FINR), placed by
           AFf2.D_owned at X1, whose owned bytes are X's (the refill keeps st_chunks and st_fs); the refill leaf's
           raw frame excludes owned X, owned X1 and its stack window [sp - 64 - RSTACK, sp - 64), inside Enqueue's
           [sp - QSTACK, sp); segR1's window is Enqueue's frame [sp - 64, sp) and thread-object words in D. *)
        + pose proof RO as (Rck & _ & _ & _ & _ & _ & Rfs & _).
          intros x NO _ NS _.
          assert (Ha : 0 <= bv_unsigned x < 2 ^ 64) by (apply u64_range).
          assert (NO1 : ~ aowned B ly X1 (bv_unsigned x))
            by (intros O; apply NO; exact (AFg6.aowned_same B ly X X1 (bv_unsigned x) Rck Rfs O)).
          assert (NDS : ~ AFf2.DS (bv_unsigned (getr regs 2)) (bv_unsigned x))
            by (intros O; apply NS; unfold ascratch; left; unfold spZ, AFf2.DS in *; exact O).
          assert (NDX : ~ AFf2.D ly X1 (o1 :: l1') (bv_unsigned (getr regs 2)) (bv_unsigned x)).
          { intros HD. destruct (AFf2.D_owned B ly X1 _ (proj1 (proj1 POST)) k CI
              (o1 :: l1') El1 ltac:(discriminate) (bv_unsigned (getr regs 2))
              (AFg6.HSP B ly X W regs mu md k PRE_u) (bv_unsigned x) (proj1 Ha) HD) as [O|O];
              [exact (NO1 O) | exact (NDS O)]. }
          rewrite (MEQ6 x ltac:(intros HW; apply NDX; unfold AFf2.D, AFf2.DT, AFf2.DN, AFf2.DL, AFf2.DS;
            unfold AFgr.WIN, AFgr.WINT, AFgr.WINA, AFgr.NBv, AFgr.QLv, AFg6.cnt1, AFg6.coff1 in HW;
            unfold AFf2.QLv;
            destruct HW as [HW|[[_ HW]|[Hq HW]]];
            [left; exact HW | right; left; lia | right; right; left; split; [exact Hq | first [exact HW | lia]]])).
          assert (SP1 : spZ regs1 = bv_unsigned (getr regs 2) - 64).
          { unfold spZ. rewrite R_sp. unfold w64. apply unsigned_lit_small.
            pose proof (u64_range (getr regs 2)) as U.
            pose proof (AFg6.HSP B ly X W regs mu md k PRE_u) as HSP0.
            pose proof (AFg6.HI0 B ly X W regs mu md k PRE_u) as HI0.
            destruct HI0 as (_ & _ & _ & _ & hS1 & _).
            clear - U HSP0 hS1. unfold QSTACK, kHighMemBeg in *. lia. }
          assert (NSC : ~ (spZ regs1 - RSTACK <= bv_unsigned x < spZ regs1)).
          { rewrite SP1. intros O. apply NS. unfold ascratch. left. unfold spZ, QSTACK, RSTACK in *. clear - O. lia. }
          rewrite (RRAW x NO NO1 NSC).
          apply MR1. intros HW0. unfold AFgq.WIN0 in HW0. destruct HW0 as [HW0|HW0].
          * apply NS. unfold ascratch. left. unfold spZ, QSTACK in *. clear - HW0. lia.
          * apply NDX. unfold AFf2.D. left. unfold AFf2.DT. unfold AFgq.WINT in HW0.
            first [exact HW0 | unfold t_qc, t_cache, t_cache_stats in *; clear - HW0; lia]. }
    unfold cfg_at, raZ. rewrite R_ra. unfold w64 at 1. rewrite unsigned_lit_small by lia.
    rewrite <- (wvb_self md') at 1. exact TAILU.
Qed.
End miss.
End e.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The two exported contracts (lib/A/AFg4.v:381 and lib/A/AFg6.v:904), for any UP.                                 *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Theorem tfib_enqueue_roomU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FK.tfib_enqueue_spec_nbU B false.
Proof.
intros B LAWS TB ly X UP W regs mem md k HNB PRE.
exact (tfib_enqueue_room_armU B TB ly X UP W regs mem md k PRE HNB).
Qed.

Theorem tfib_enqueue_nbU : forall B, AR_laws tfibsegs B -> TfibSyms B -> FAR.tfib_refill_specU B ->
  FK.tfib_enqueue_spec_nbU B true.
Proof.
intros B LAWS TB R1 ly X UP W regs mem md k HNB PRE.
destruct (pc_chunks (cache X kBatchClass)) as [|o l0] eqn:E.
- exact (tfib_enqueue_miss_armU B TB ly X UP W regs mem md k PRE HNB E R1).
- apply (tfib_enqueue_hit_armU B TB ly X UP W regs mem md k PRE HNB). rewrite E. discriminate.
Qed.
End d.
