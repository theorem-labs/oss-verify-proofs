(* fuzz_state: enqueue (lib/A/AFew.v) under ARU for ANY set UP of user-poisoned heads: tfib_enqueue_roomU, tfib_enqueue_nbU. *)
(* Shared any-U allocator, within-budget units (cgif's EV_MAX 11,776, < 2 GiB per class); the cf form (fuzz_preset / fuzz_reply, YG0dcf.v) bridges to this. *)
(* The twins of the released cgif_file_fuzzer theorems tfib_enqueue_room (lib/A/AFg4.v:381) and tfib_enqueue_nb
   (lib/A/AFg6.v:904). The donor walks are kept: their facts, their runs (AFh3.segP, AFh4.segQH, AFh5.segR1, AFh6.segT)
   and their leaf lemmas (AFg4.FINPH, AFg5.FINQH, AFg6.FINR) are applied unchanged, over FSupoison.unpoison UP mem where
   they read memory and over the real memory where the machine runs; FSupoisonAllocFeqR.v carries the two transfers.
   UP survives the call: enqueue keeps st_chunks (its leaf says so), so every UP range stays in a live block, and the
   new batch is a batch-class chunk, never a live block, so the run's write window stays in application memory, off
   UP's shadow. *)
(* Modified by Theorem Labs, 2026-10: the image-B port (fuzz_state.asan-ubsan) of lib/A/FSupoisonAllocFeq.v at 5cc58921ee2: each lib/A donor is its lib/B twin (AFxx -> YFxx, ABxx -> YBxx, AExx -> YExx), every statement is over B's tfibsegs (lib/B/YB1v.v), the kit is lib/B/FSupoisonAllocR / Rf / Rt; the pcs are by name: PC_ENQ_RA. *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0 YFl1.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1w YFeq YFex YFf0 YFf1 YFf2 YFgi YFfu.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YFfj YFfk YFfp.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFew YFgp YFgq YFgr YFh3 YFh4 YFh5 YFh6 YFg3 YFft YFfq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0k.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB13.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YFg4 YFg5 YFg6.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSupoison FSupoisonU.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSupoisonAllocR FSupoisonAllocFK FSupoisonAllocFeqR.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Local Open Scope am_scope.
(* The pcs inside a function, by name: the entry is lib/B/YFeu.v / lib/B/YFew.v A_xxx or the lib/B/YB1w.v row, the offset is the B donor's pc minus that entry. *)
(* the return address of Enqueue's new-batch call (lib/B/YFgr.v:128, SS0's pc; lib/B/YFg6.v:276 R_ra). *)
Definition PC_ENQ_RA : Z := A_Enqueue + 0x154.
Module FSP := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoison.
Module FSU := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.FSupoisonU.
Module FAR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocR.
Module FK := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFK.
Module FeqR := OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B.FSupoisonAllocFeqR.

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
(* 1. Room in the last batch (lib/B/YFg4.v:369 tfib_enqueue_room_arm).                                               *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section room.
Hypothesis HNB : need_new_batch (st_qthread X) = false.

Theorem tfib_enqueue_room_armU :
  amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (FK.enq_leafU B ly X UP W regs mem md k).
Proof.
first [ pose proof (YFg4.FH_ok B TB ly X W regs mu md k PRE_u HNB) as FHmu
      | pose proof (YFg4.FH_ok B TB ly X W regs mu md k PRE_u HNB HTSD) as FHmu
      | pose proof (YFg4.FH_ok B ly X W regs mu md k PRE_u HNB) as FHmu ].
pose proof (FeqR.FHp_real B ly X UP W mem md ARUx regs _ _ _ _ _ _ _ FHmu) as FHreal.
rewrite (enqueue_room_eq k X HNB). cbn [amreal].
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- exact (YFh3.segP W ly regs mem md _ _ _ _ _ _ _ (m_vm_materialized md) FHreal).
- intros W' c' _ HR.
  destruct (FeqR.at_RETP_u B ly X UP W mem md ARUx regs _ _ _ _ _ _ _ W' c' FHmu HR)
    as (regs' & mem' & mat & -> & -> & HRu & PO & MQ).
  assert (LEAF : enq_leaf B ly X W regs mu md k (tt, YFf1.S' X k) W
                   (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs))
                          (with_vm_backing (m_vm_lazy md) mat md)))
    by (eapply YFg4.FINPH; first [exact TB | exact PRE_u | exact HNB | exact HTSD | exact HRu]).
  pose proof LEAF as LEAF0.
  destruct LEAF0 as (rr & mm & dd & nb & E1 & POST & QT1 & QT2 & QTc & QTg & QTf).
  rewrite (cfg_ret regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  apply (FK.enq_leafU_intro B ly X UP W regs mem md k _ W regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  + rewrite <- (cfg_ret regs' (FSP.unpoison UP mem') (with_vm_backing (m_vm_lazy md) mat md)). exact LEAF.
  + exact (upoison_ok_keep_chunks _ QTc).
  + exact PO.
  + (* the raw frame: the run's window (YFgp.WIN) is in YFf1.D at the last batch lb (as in YFg4.FINPH), owned by X or in
       the stack scratch (YFf1.D_owned) *)
    apply (FK.raw_of_meq _ (aowned B ly X) (aowned B ly (snd (tt, YFf1.S' X k))) (ascratch B QSTACK regs) (fun _ => False)
      mem mem' MQ).
    intros a Ha Hw.
    pose proof PRE_u as ((M0 & LED0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _).
    assert (HSP0 : ly_stk_lo ly + QSTACK <= bv_unsigned (YK11.getr regs 2) <= ly_stk_hi ly) by (unfold spZ in Hlo, Hhi; lia).
    pose proof HNB as HNB'. unfold need_new_batch in HNB'.
    destruct (rev (qc_list (st_qthread X))) as [|lb initr] eqn:Hrev; [discriminate|]. apply Z.eqb_neq in HNB'.
    assert (Hroom : Z.of_nat (length (b_items lb)) < kBatchSlots).
    { pose proof (proj1 (Forall_forall _ _) (wq_batches _ (wf_quarantine _ _ _ _ _ (am_wf B ly X _ M0))) lb) as HB.
      assert (IN : In lb (all_batches X)) by (unfold all_batches; apply in_app_iff; left; apply in_rev; rewrite Hrev; left; reflexivity).
      specialize (HB IN). unfold kBatchSlots in *. lia. }
    assert (EQL : YFg4.lb X = lb) by (unfold YFg4.lb; rewrite Hrev; reflexivity).
    assert (HD : YFf1.D ly lb (bv_unsigned (YK11.getr regs 2)) a).
    { unfold YFf1.D, YFf1.DT, YFf1.DL, YFf1.DS. unfold YFf1.QLv, YFf1.CNTv.
      unfold YFgp.WIN, YFgp.SLv in Hw. unfold YFg4.QLv, YFg4.CNTv in Hw. rewrite EQL in Hw.
      destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [do 2 right; clear - Hw; unfold QSTACK; lia | left; exact Hw | right; left; left; exact Hw | right; left; right; lia]. }
    destruct (YFf1.D_owned B ly X _ M0 lb initr Hrev Hroom _ HSP0 (img_cover_of_ledger ly X _ LED0) a (proj1 Ha) HD) as [O|O].
    * left. exact O.
    * right; right; left. unfold ascratch, spZ. left. exact O.
Qed.
End room.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 2. A new batch, taken from the batch-class cache (lib/B/YFg5.v:627 tfib_enqueue_hit_arm).                          *)
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

Theorem tfib_enqueue_hit_armU :
  amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (FK.enq_leafU B ly X UP W regs mem md k).
Proof.
first [ pose proof (YFg5.FH_ok B TB ly X W regs mu md k PRE_u HNB lc eq_refl Hne) as FHmu
      | pose proof (YFg5.FH_ok B TB ly X W regs mu md k PRE_u HNB lc eq_refl Hne HTSD) as FHmu
      | pose proof (YFg5.FH_ok B ly X W regs mu md k PRE_u HNB lc eq_refl Hne) as FHmu ].
pose proof (FeqR.FHq_real B ly X UP W mem md ARUx regs _ _ _ _ _ _ FHmu) as FHreal.
assert (HEQ : enqueue k X = IRet (tt, YFf2.S' X k lc))
  by (eapply YFg5.enqueue_hit_eq; first [exact TB | exact PRE_u | exact HNB | exact Hne | reflexivity]).
rewrite HEQ. cbn [amreal].
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
eapply SRr_mono.
- exact (YFh4.segQH W ly regs mem md _ _ _ _ _ _ (m_vm_materialized md) FHreal HC5).
- intros W' c' _ HR.
  destruct (FeqR.at_RETQ_u B ly X UP W mem md ARUx regs _ _ _ _ _ _ W' c' FHmu HC5 HR)
    as (regs' & mem' & mat & -> & -> & HRu & PO & MQ).
  assert (LEAF : enq_leaf B ly X W regs mu md k (tt, YFf2.S' X k lc) W
                   (mkCfg (YK11.mkst regs' (YK11.getr regs 1) (FSP.unpoison UP mem') (YK11.seg_rom tfibsegs))
                          (with_vm_backing (m_vm_lazy md) mat md)))
    by (eapply YFg5.FINQH; first [exact TB | exact PRE_u | exact HNB | exact Hne | exact HTSD | exact HRu | reflexivity]).
  pose proof LEAF as LEAF0.
  destruct LEAF0 as (rr & mm & dd & nb & E1 & POST & QT1 & QT2 & QTc & QTg & QTf).
  rewrite (cfg_ret regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  apply (FK.enq_leafU_intro B ly X UP W regs mem md k _ W regs' mem' (with_vm_backing (m_vm_lazy md) mat md)).
  + rewrite <- (cfg_ret regs' (FSP.unpoison UP mem') (with_vm_backing (m_vm_lazy md) mat md)). exact LEAF.
  + exact (upoison_ok_keep_chunks _ QTc).
  + exact PO.
  + (* the raw frame: the run's window (YFgq.WIN) is in YFf2.D at the cache list lc (as in YFg5.FINQH), owned by X or in
       the stack scratch (YFf2.D_owned) *)
    apply (FK.raw_of_meq _ (aowned B ly X) (aowned B ly (snd (tt, YFf2.S' X k lc))) (ascratch B QSTACK regs) (fun _ => False)
      mem mem' MQ).
    intros a Ha Hw.
    pose proof PRE_u as ((M0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _).
    assert (HSP0 : ly_stk_lo ly + QSTACK <= bv_unsigned (YK11.getr regs 2) <= ly_stk_hi ly) by (unfold spZ in Hlo, Hhi; lia).
    assert (Hci0 : st_cache_inited X = true)
      by (eapply YFg5.Hci; first [exact TB | exact PRE_u | exact HNB | exact Hne | reflexivity | eassumption]).
    assert (HD : YFf2.D ly X lc (bv_unsigned (YK11.getr regs 2)) a).
    { unfold YFf2.D, YFf2.DT, YFf2.DN, YFf2.DL, YFf2.DS.
      unfold YFgq.WIN, YFgq.WINT, YFgq.WINA, YFgq.NBv in Hw.
      destruct Hw as [Hw|[Hw|[[_ Hw]|[Hq Hw]]]].
      - do 3 right. clear - Hw. unfold QSTACK. lia.
      - left. exact Hw.
      - right; left. unfold YFg5.coff in Hw. cbv zeta. clear - Hw. lia.
      - right; right; left. split; [exact Hq|]. unfold YFf2.QLv. unfold YFgq.QLv in Hw. exact Hw. }
    destruct (YFf2.D_owned B ly X _ M0 k Hci0 lc eq_refl Hne _ HSP0 a (proj1 Ha) HD) as [O|O].
    * left. exact O.
    * right; right; left. unfold ascratch, spZ. left. exact O.
Qed.
End hit.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 3. A new batch, with the batch-class cache empty: refill first (lib/B/YFg6.v:868 tfib_enqueue_miss_arm).           *)
(* ---------------------------------------------------------------------------------------------------------------- *)
Section miss.
Hypothesis HNB : need_new_batch (st_qthread X) = true.
Hypothesis Hl0 : pc_chunks (cache X kBatchClass) = [].
Hypothesis R1 : FAR.tfib_refill_specU B.

Theorem tfib_enqueue_miss_armU :
  amreal tfibsegs (enqueue k X) W (cfg_at tfibsegs A_Enqueue regs mem md) (FK.enq_leafU B ly X UP W regs mem md k).
Proof.
first [ pose proof (YFg6.FH0_ok B TB ly X W regs mu md k PRE_u HNB Hl0) as FH0mu
      | pose proof (YFg6.FH0_ok B TB ly X W regs mu md k PRE_u HNB Hl0 HTSD) as FH0mu
      | pose proof (YFg6.FH0_ok B ly X W regs mu md k PRE_u HNB Hl0) as FH0mu ].
pose proof (FeqR.FHq_real B ly X UP W mem md ARUx regs _ _ _ _ _ _ FH0mu) as FH0real.
apply (amreal_enqueue_nb k X W _ _ HNB).
unfold cfg_at, A_Enqueue. rewrite <- (wvb_self md) at 1.
apply amreal_after_SRr. eapply SRr_mono.
- exact (YFh5.segR1 W ly regs mem md _ _ _ _ _ _ (m_vm_materialized md) FH0real eq_refl).
- intros W' c' _ HC.
  destruct (FeqR.at_CALLR_u B ly X UP W mem md ARUx regs _ _ _ _ _ _ W' c' FH0mu HC)
    as (regs1 & mem1 & mat & -> & -> & HCu & PO1 & MQ1r).
  pose proof HCu as HCu0.
  destruct HCu0 as (_ & regs1' & mem1' & mat' & ECFG & R_ra & R_sp & R_gp & R_tp & R_a0 & R_a1 & R_a2 & R_a3 &
                    R_s0 & R_s1 & R_s2 & R_s3 & R_s4 & R_s5 & R_hi & MQ1 & PR1 & VALS).
  apply FK.cfg_at_inj in ECFG as (<- & <- & _).
  cbv zeta in VALS. destruct VALS as (V1 & V2 & V3 & V4 & V5 & V6 & F1 & F2 & F3 & F4 & F5 & F6 & F7).
  assert (RPRE : FAR.refill_preU B ly X UP W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) kBatchClass).
  { unfold FAR.refill_preU. split; [|split; [exact OK0 | exact PO1]].
    eapply YFg6.REFILL_PRE; first [exact TB | exact PRE_u | exact HNB | exact Hl0 | exact HTSD | eassumption]. }
  pose proof (R1 ly X UP W regs1 mem1 (with_vm_backing (m_vm_lazy md) mat md) kBatchClass RPRE) as RR.
  unfold cfg_at, A_Refill in RR.
  assert (WfX1 : WfP (as_universe B) 1 0 0 X) by (eapply YFg6.WfX1; first [exact TB | exact PRE_u]).
  pose proof (YFg6.refill_tree_apostg (as_universe B) 1 0 0 X kBatchClass WfX1 ltac:(unfold kBatchClass; lia)
                ltac:(lia) (proj1 (proj2 (proj1 (proj2 (proj2 (proj2 PRE_u))))))) as APOST.
  pose proof (amreal_apostg tfibsegs (refill_tree kBatchClass X) _ W _ _ APOST RR) as RR2. clear RR.
  eapply amreal_mono; [|exact RR2]. cbv beta.
  intros [[] X1] W5 c5 [(WX1 & RO & CI & NE1) HL]. cbn [fst snd] in WX1, RO, CI, NE1, HL.
  destruct HL as (regs' & mem' & md' & -> & POSTU & HA0 & HRAWR).
  destruct POSTU as (POST & OK1 & PO2).
  pose proof (FAR.ARU_intro B ly X1 UP W5 mem' md' (proj1 POST) OK1 PO2) as ARU1.
  unfold enq_after_refill. cbn [snd].
  destruct (pc_chunks (cache X1 kBatchClass)) as [|o1 l1'] eqn:El1.
  + exfalso. apply NE1. first [reflexivity | exact El1].
  + cbn [snd] in HA0. rewrite El1 in HA0.
    assert (FHRmu : YFgr.free_hyps W5 ly regs' (FSP.unpoison UP mem')
              (sptr_addr B ly (ck_user k)) (ck_n k) (st_qthread X1)
              (Z.of_nat (length (o1 :: l1'))) (last (o1 :: l1') 0) (YFfq.jst ly W5 (FSP.unpoison UP mem'))
              (bv_unsigned (YK11.getr regs 1)) (bv_unsigned (YK11.getr regs 8)) (bv_unsigned (YK11.getr regs 9))
              (bv_unsigned (YK11.getr regs 18)) (bv_unsigned (YK11.getr regs 19)) (bv_unsigned (YK11.getr regs 20))
              (bv_unsigned (YK11.getr regs 21)))
      by (eapply YFg6.FHR_ok;
          first [exact TB | exact PRE_u | exact HNB | exact Hl0 | exact HTSD | exact El1 | eassumption]).
    pose proof (FeqR.FHr_real B ly X1 UP W5 mem' md' ARU1 regs' _ _ _ _ _ _ _ _ _ _ _ _ _ FHRmu) as FHRreal.
    assert (TAILU : SRr tfibsegs W5
              (mkCfg (YK11.mkst regs' (w64 PC_ENQ_RA) mem' (YK11.seg_rom tfibsegs))
                     (with_vm_backing (m_vm_lazy md') (m_vm_materialized md') md'))
              (FK.enq_leafU B ly X UP W regs mem md k (tt, YFf2.S' X1 k (o1 :: l1')))).
    { eapply SRr_mono.
      - exact (YFh6.segT W5 ly regs' mem' md' _ _ _ _ _ _ _ _ _ _ _ _ _ (m_vm_materialized md') FHRreal).
      - intros W6 c6 _ HR6.
        destruct (FeqR.at_RETR_u B ly X1 UP W5 mem' md' ARU1 regs' _ _ _ _ _ _ _ _ _ _ _ _ _ W6 c6 FHRmu HR6)
          as (regs6 & mem6 & mat6 & -> & -> & HR6u & PO6 & MQ6).
        assert (LEAF : enq_leaf B ly X W regs mu md k (tt, YFf2.S' X1 k (o1 :: l1')) W5
                         (mkCfg (YK11.mkst regs6 (w64 (bv_unsigned (YK11.getr regs 1))) (FSP.unpoison UP mem6)
                                 (YK11.seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md') mat6 md')))
          by (eapply YFg6.FINR;
              first [exact TB | exact PRE_u | exact HNB | exact Hl0 | exact HTSD | exact El1 | exact HR6u | eassumption]).
        pose proof LEAF as LEAF0.
        destruct LEAF0 as (rr & mm & dd & nb & E1 & POSTl & QT1 & QT2 & QTc & QTg & QTf).
        apply (FK.enq_leafU_intro B ly X UP W regs mem md k _ W5 regs6 mem6 (with_vm_backing (m_vm_lazy md') mat6 md')).
        + exact LEAF.
        + exact (upoison_ok_keep_chunks _ QTc).
        + exact PO6.
        + (* the raw frame: the tail's (MQ6; YFgr.WIN is the thread object's cells, owned by X, or in YFf2.D at X1, as
             in YFg6.FINR, owned by X1, which owns only what X owns) after the refill's (HRAWR, at regs1 whose sp is
             sp0 - 64, so its stack window lies in enqueue's scratch) after the prologue's (MQ1r; YFgq.WIN0 is the
             stack frame or the thread object's cells) *)
          pose proof PRE_u as ((M0 & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hlo & Hhi & _).
          pose proof POST as ((M5 & _) & _).
          assert (HSP0 : ly_stk_lo ly + QSTACK <= bv_unsigned (YK11.getr regs 2) <= ly_stk_hi ly) by (unfold spZ in Hlo, Hhi; lia).
          pose proof (YFgq.LYB W ly regs mu _ _ _ _ _ _ FH0mu) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SLO & _).
          assert (Usp : 0 <= bv_unsigned (YK11.getr regs 2) < 2 ^ 64) by exact (bv_unsigned_in_range _ _).
          assert (SPR : bv_unsigned (YK11.getr regs1 2) = bv_unsigned (YK11.getr regs 2) - 64).
          { rewrite R_sp. unfold w64. apply unsigned_lit_small. clear - HSP0 SLO Usp. unfold QSTACK, kHighMemBeg in *. lia. }
          assert (THR : forall a, (ly_T ly + t_qc <= a < ly_T ly + t_qc + 32) \/ (ly_T ly + t_cache + 1920 <= a < ly_T ly + t_cache + 1924) \/
            (ly_T ly + t_cache_stats + 16 <= a < ly_T ly + t_cache_stats + 24) -> aowned B ly X a).
          { intros a Ha. apply (own_core B ly X _ (ly_T ly, kThreadObjSize) a M0); [unfold core_extents; cbn; tauto|].
            cbn [fst snd]. clear - Ha. unfold t_qc, t_cache, t_cache_stats, kThreadObjSize in *. lia. }
          intros x NO _ NS _.
          assert (NO1 : ~ aowned B ly X1 (bv_unsigned x)).
          { intros O. apply NO. destruct RO as (Rck & _ & _ & _ & _ & _ & Rfs & _).
            unfold aowned, aclient_byte, sec_extents, frames in *. rewrite Rck, Rfs in O. exact O. }
          unfold ascratch, spZ in NS.
          rewrite MQ6.
          * rewrite HRAWR; [| exact NO | exact NO1 |].
            -- apply MQ1r. intros Hw. unfold YFgq.WIN0, YFgq.WINT in Hw. destruct Hw as [Hw|Hw].
               ++ apply NS. left. clear - Hw. unfold QSTACK. lia.
               ++ exact (NO (THR _ Hw)).
            -- unfold spZ. rewrite SPR. intros Hw. apply NS. left. clear - Hw. unfold QSTACK, RSTACK in *. lia.
          * intros Hw. unfold YFgr.WIN, YFgr.WINT in Hw. destruct Hw as [Hw|Hw].
            -- exact (NO (THR _ Hw)).
            -- assert (HD : YFf2.D ly X1 (o1 :: l1') (bv_unsigned (YK11.getr regs 2)) (bv_unsigned x)).
               { unfold YFf2.D, YFf2.DT, YFf2.DN, YFf2.DL, YFf2.DS. unfold YFgr.WINA, YFgr.NBv in Hw.
                 destruct Hw as [[_ Hw]|[Hq Hw]].
                 - right; left. cbv zeta. clear - Hw. lia.
                 - right; right; left. split; [exact Hq|]. unfold YFf2.QLv. unfold YFgr.QLv in Hw. exact Hw. }
               destruct (YFf2.D_owned B ly X1 _ M5 k CI (o1 :: l1') El1 ltac:(discriminate) _ HSP0 _
                 (proj1 (bv_unsigned_in_range _ x)) HD) as [O|O].
               ++ exact (NO1 O).
               ++ apply NS. left. exact O. }
    unfold cfg_at, raZ. rewrite R_ra. unfold w64 at 1. rewrite unsigned_lit_small by lia.
    rewrite <- (wvb_self md') at 1. exact TAILU.
Qed.
End miss.
End e.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* 4. The two exported contracts (lib/B/YFg4.v:379 and lib/B/YFg6.v:902), for any UP.                                 *)
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
