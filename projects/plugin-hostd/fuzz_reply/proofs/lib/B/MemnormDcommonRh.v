(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/MemnormDcommon.v (a working branch 30a1993588f, c5 + memnorm; file sha256 95731bec3ae1) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 2 image addresses moved by code-verified function pairs (2 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); 2 model labels (YG00 mcheck / spin tags) kept; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/MemnormDcommon.v, with its module paths, module names and addresses changed; 11 of its 239 lines of code are new or changed and 10 lines of the source are left out. *)
(* lib/B MemnormDcommon.v (image B: the arm whose last batch has room, memnorm kept) at round 3 part 3, over DIfaceRh.DIface_rh: the
   Hypothesis IF and its field names (the di_ prefix renamed to DIfaceRh.dih_) only; the scripts are MemnormDcommon's.
   For WalkSigDrh's instance at the primed top, whose interface instance is DIfaceRh.DIface_rh (CfF2a's
   YGcfInstFree.diface_rh_cf): a DIface_rh -> DIface projection cannot exist, and a released DIface at drain_body_cf would
   claim the released drain, which a real recycle breaks.
   rule 24: no function proved (kind: restatement of an already proved arm over a weaker interface record). *)
(* Theorem Labs, 2026-10 (task MEMNORM): the common Deallocate arm of DGfy.v (the last batch has room) with memnorm
   kept.  [dealloc_common_em] is DGfy.dealloc_common_e with MemnormDleaf.dealloc_leaf_raw_eem
   (DGleafE.dealloc_leaf_raw_ee plus `memnorm mem -> memnorm mem'`) in place of DGleafE.dealloc_leaf_raw_ee.
   rule 24: no function proved (kind: arm twin, frame corollary).

   The keep comes from the arm's own raw frame: dmem_c's frame clause (DGif0.dmem_c, the clause DGfy.dmem_c_ok
   proves) keeps every byte outside DGgi.WIN (the stack window, the thread object's cells WINT, the freed chunk's header
   and first word and the last batch's cells WINB), DGgi.DZONE, DGgi.IZONE and the freed block's shadow
   [SPv p, + CNT8v nn); none of those zones holds a read-only byte or reaches TASK_SIZE ([memnorm_dmem_c]), from the
   seed's free_hyps record:
   - a WIN byte is off the image (DGgi.WIN_zone, DGgi.v:394) and below ASAN_CEIL or kHighMemEnd (DGgi.LYB :222,
     DGgi.derived_ranges :305, fh_Hsp :162);
   - DZONE's static part [0x177f88, 0x5c8710) and IZONE lie in tfibsegs' read-write segments
     (MemnormSafecgif.mn_safe_rw); its node and store blocks are zone3 (off the image, YF0x zone3_off_img) and below
     ASAN_CEIL (LYB);
   - the shadow lies in [SHADOW_OFF + 514, kHighMemBeg) (derived_ranges), above the image.
   The proof of dealloc_common_em is DGfy.v:256-399 (blocks marked as copies; the section header is DGfy.v:219-245),
   plus the memnorm conjunct from the same frame; the one line that splits the leaf's conjuncts (DGfy.v:369) gets the
   extra conjunct.  No runner is swapped and no walk is touched.  DGfy.v is unchanged. *)
(* Theorem Labs, 2026-10 (task MEMNORM): the common Deallocate arm of DGfy.v (the last batch has room) with memnorm
   kept.  [dealloc_common_em] is DGfy.dealloc_common_e with MemnormDleaf.dealloc_leaf_raw_eem
   (DGleafE.dealloc_leaf_raw_ee plus `memnorm mem -> memnorm mem'`) in place of DGleafE.dealloc_leaf_raw_ee.
   rule 24: no function proved (kind: arm twin, frame corollary).

   The keep comes from the arm's own raw frame: dmem_c's frame clause (DGif0.dmem_c, the clause DGfy.dmem_c_ok
   proves) keeps every byte outside DGgi.WIN (the stack window, the thread object's cells WINT, the freed chunk's header
   and first word and the last batch's cells WINB), DGgi.DZONE, DGgi.IZONE and the freed block's shadow
   [SPv p, + CNT8v nn); none of those zones holds a read-only byte or reaches TASK_SIZE ([memnorm_dmem_c]), from the
   seed's free_hyps record:
   - a WIN byte is off the image (DGgi.WIN_zone, DGgi.v:394) and below ASAN_CEIL or kHighMemEnd (DGgi.LYB :222,
     DGgi.derived_ranges :305, fh_Hsp :162);
   - DZONE's static part [0x178508, 0x5c8c90) and IZONE lie in tfibsegs' read-write segments
     (MemnormSafecgif.mn_safe_rw); its node and store blocks are zone3 (off the image, YF0x zone3_off_img) and below
     ASAN_CEIL (LYB);
   - the shadow lies in [SHADOW_OFF + 514, kHighMemBeg) (derived_ranges), above the image.
   The proof of dealloc_common_em is DGfy.v:256-399 (blocks marked as copies; the section header is DGfy.v:219-245),
   plus the memnorm conjunct from the same frame; the one line that splits the leaf's conjuncts (DGfy.v:369) gets the
   extra conjunct.  No runner is swapped and no walk is touched.  DGfy.v is unchanged. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import YB1w YE3d YFeq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif0n AGif0reply DeallocG DGbase DGgi DGfv DGgc DGge DGif0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import AGif2reply ImgBaseDG DGif0reply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ErrnoG DGleafE.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import DGfy.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require MemnormT MemnormDleaf MemnormHitG MemnormSafereply.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YAkMemnorm.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require DIfaceRh.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.
Local Open Scope am_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* memnorm is kept by a memory that equals [mem0] outside dmem_c's raw frame zones, over the seed's free_hyps. *)
Lemma memnorm_dmem_c : forall W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU (mem' : word -> option byte),
  DGgi.free_hyps W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU ->
  (forall x : word, ~ DGgi.WIN ly regs0 p lastb (bv_unsigned x) -> ~ DGgi.DZONE ly (bv_unsigned x) ->
    ~ DGgi.IZONE (bv_unsigned x) -> ~ (DGgi.SPv p <= bv_unsigned x < DGgi.SPv p + DGgi.CNT8v nn) -> mem' x = mem0 x) ->
  MemnormT.memnorm_keep tfibsegs mem0 mem'.
Proof.
intros W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU mem' FH MEQ.
pose proof (DGgi.LYB W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH)
  as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & T1 & T2 & T3 & T4 & T5).
pose proof (DGgi.derived_ranges W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH) as DR.
pose proof (DGgi.fh_Hsp _ _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (S1 & S2 & S3).
pose proof (ASAN_CEIL_range) as [CR _].
apply (MemnormT.memnorm_frame4 tfibsegs (DGgi.WIN ly regs0 p lastb) (DGgi.DZONE ly) DGgi.IZONE
  (fun a => DGgi.SPv p <= a < DGgi.SPv p + DGgi.CNT8v nn) mem0 mem').
- intros x Hw. destruct (DGgi.WIN_zone W ly regs0 mem0 tr p nn hb1 q lastb j1 j2 j3 regsU FH _ Hw) as (Z1 & _ & _).
  apply MemnormSafereply.mn_safe_offimg; [unfold TFIB_IMG_LO, TFIB_IMG_END in *; lia|].
  unfold DGgi.WIN, DGgi.WINT, DGgi.WINB in Hw. cbv beta zeta in Hw.
  unfold kHighMemEnd, TASK_SIZE, kThreadObjSize, t_qc, t_cache, t_unwinding, t_stats in *. lia.
- intros x Hd. unfold DGgi.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
  + apply MemnormSafereply.mn_safe_rw. unfold TASK_SIZE. lia.
  + pose proof (zone3_off_img _ _ _ F9 Hd) as O.
    apply MemnormSafereply.mn_safe_offimg; unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE in *; lia.
  + pose proof (zone3_off_img _ _ _ F11 Hd) as O.
    apply MemnormSafereply.mn_safe_offimg; unfold off_img, TFIB_IMG_LO, TFIB_IMG_END, TASK_SIZE in *; lia.
- intros x Hz. unfold DGgi.IZONE in Hz. apply MemnormSafereply.mn_safe_rw.
  unfold TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TASK_SIZE in *. lia.
- intros x Hs. apply MemnormSafereply.mn_safe_offimg; unfold TFIB_IMG_LO, TFIB_IMG_END, SHADOW_OFF, kHighMemBeg, TASK_SIZE in *; lia.
- exact MEQ.
Qed.

(* copy of DGfy.v:219-245 (the section header), unchanged *)
Section b.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variable ARX : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop.
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable MP : (word -> option byte) -> Prop.
Hypothesis IF : DIfaceRh.DIface_rh B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Local Notation Finst := (DIfaceRh.dih_inst B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fview := (DIfaceRh.dih_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fshape := (DIfaceRh.dih_shape B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fdepot := (DIfaceRh.dih_depot B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fdaok := (DIfaceRh.dih_dpost_aok B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fpost_c := (DIfaceRh.dih_post_c B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fown := (DIfaceRh.dih_owned B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fown_b := (DIfaceRh.dih_owned_b B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fown_i := (DIfaceRh.dih_owned_i B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Hypothesis TS : TfibSyms B.
Hypothesis FHC : fh_c_spec B.

(* DGfy.dealloc_common_e with memnorm kept. *)
Theorem dealloc_common_em : forall inst so bp ly S W regs mem md p n tr lastb initr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
(MemnormDleaf.dealloc_leaf_raw_eem B ft ARX AOX lpost inst ly S W regs mem md p n tr).
Proof.
(* copy of DGfy.v:256-368, unchanged *)
intros inst so bp ly S W regs mem md p n tr lastb initr PRE HBLK Hrev Hroom Hcache.
pose proof PRE as PRE0.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (Finst _ _ _ _ _ _ HARX) as HIO.
pose proof (Fview inst ly S W mem md p n HARX HRP HFP HBLK) as DV.
pose proof DV as [DVn DVnn DVch DVhdr DVpres DVsh DVjunk DVzone DVqb DVbatch].
destruct DVch as (k & Hf & Hst & Hu & Hr).
destruct (FHC U ARX rpre fpre inst so bp ly S W regs mem md p n tr lastb initr PRE0 HBLK HIO DV Hrev Hroom Hcache)
as (hb1 & j1 & j2 & j3 & Hhb1 & Hhdr & FH).
pose proof (Fshape p n tr S k DVnn HRP HBLK Hf Hst) as ESH.
set (pa := sptr_addr B ly p) in *. set (nn := req_size n) in *. set (q := st_qthread S) in *.
set (regs0 := dregs regs pa inst bp so) in *.
unfold spZ, raZ in *.
assert (R1 : getr regs0 1%bv = getr regs 1%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
assert (R2 : getr regs0 2%bv = getr regs 2%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (sp_facts W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH) as SPF. rewrite R2 in SPF. unfold DFSTACK in SPF.
assert (Usp : 0 <= bv_unsigned (getr regs 2) < 2 ^ 64) by apply u64_range.
assert (BP0 : bv_unsigned (getr regs0 12) = bp).
{ unfold regs0. rewrite dregs_12. unfold w64. apply unsigned_lit_small. unfold kHighMemEnd, kHighMemBeg in *. lia. }
(* the walk, with its machine post at Put's ret *)
assert (MAIN : amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x3191c regs mem md)
(fun r W' c' => exists z, r = (tt, qfin_c S k z tr) /\ W' = W /\ exists regs' mem' mat,
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
(forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs0 r) /\
dmem_c W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 q lastb (dpost inst ly S W tr z) mem')).
{ rewrite ESH. unfold depot_put. cbn [bind askz ibind]. apply amreal_ask_depot.
  unfold cfg_at. rewrite <- (wvb_self md) at 1.
  eapply SRr_bind; [exact (DGgc.segB W ly regs0 mem md tr pa nn hb1 q lastb j1 j2 j3 regs (m_vm_materialized md) FH)|].
  intros W1 c1 _ (-> & msD & mat1 & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
  rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
  rewrite (HEn3 2%nat ltac:(cbv; lia)), (DGgi.E2 ly regs0 tr pa nn hb1 q lastb j1 j2 j3) in Q2.
  assert (SPD : bv_unsigned (getr (ms_regs msD) 2) = bv_unsigned (getr regs0 2) - 48).
  { rewrite Q2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite R2. clear - SPF Usp. numc. lia. }
  rewrite HshD. eapply SRr_bind.
  { apply (Fdepot inst ly S W mem md tr (ms_regs msD) (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat1 md) bp HARX Htr).
    - intros x Hx. apply (proj1 MEQD).
      + destruct Hx as [Hd|[Hc _]]; [exact (proj1 (DZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hd)) |
        exact (CZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hc)].
      + destruct Hx as [Hd|[_ Hi]]; [exact (proj1 (proj2 (DZONE_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH _ Hd))) | exact Hi].
    - rreg HS (10%bv : bv 5) R. rewrite R, (HEn3 12%nat ltac:(cbv; lia)), (DGgi.E12 ly regs0 tr pa nn hb1 q lastb j1 j2 j3).
      unfold regs0. rewrite dregs_12. reflexivity.
    - rreg HS (11%bv : bv 5) R. rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (DGgi.EaLEN ly regs0 tr pa nn hb1 q lastb j1 j2 j3). reflexivity.
    - rreg HS (3%bv : bv 5) R. rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (DGgi.Er ly regs0 tr pa nn hb1 q lastb j1 j2 j3 3 3%bv eq_refl).
      unfold regs0. rewrite dregs_other by (vm_compute; discriminate). exact Hgp.
    - rreg HS (4%bv : bv 5) R. rewrite R. reflexivity.
    - rreg HS (1%bv : bv 5) R. rewrite R. apply YK0s.ret_ok_even. reflexivity.
    - intros i Hi. pose proof (TRQ i Hi) as TQ. rewrite BP0 in TQ. exact TQ.
    - exact Hbp3.
    - clear - SPF Hbp1. lia.
    - exact Hbp2.
    - right. rewrite SPD, R2. lia.
    - rewrite SPD, R2. replace (bv_unsigned (getr regs 2) - 48) with (bv_unsigned (getr regs 2) + (-3) * 16) by lia.
      rewrite Z_mod_plus_full. exact Hal.
    - rewrite SPD, R2. clear - SPF. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia.
    - rewrite SPD, R2. lia.
    - intros a Ha. rewrite SPD in Ha. apply PRESD. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia. }
  intros W2 c2 _ (-> & z & regs4 & mem4 & mat4 & -> & HP4 & Hfr4 & Hpr4 & DP4). srr_norm_model.
  apply SRr_ret. exists z. split; [exact (Fdaok _ _ _ _ _ _ _ DP4)|].
  rewrite SPD in Hfr4.
  assert (Qsd : st_qthread (depot_after z tr (dtick S)) = q) by (unfold depot_after; destruct (z =? 0); reflexivity).
  assert (QT : st_qthread (qx S k z tr) = q).
  { unfold qx. cbn [st_qthread set_chunks]. exact Qsd. }
  assert (NNB : need_new_batch (st_qthread (qx S k z tr)) = false).
  { rewrite QT. unfold need_new_batch. rewrite Hrev. apply Z.eqb_neq. lia. }
  assert (QBY : (qc_bytes (qc_push (st_qthread (qx S k z tr)) (qk k) None) <=? kQuarantineCacheMax) = true).
  { apply Z.leb_le. rewrite QT. cbn [qc_push qc_bytes]. unfold qk, ck_n. cbn [ck_req]. rewrite Hr. exact Hcache. }
  assert (TAIL : amreal tfibsegs ((modify (fun s : astate => set_chunks (upd_chunk (st_chunks s) (qk k)) s) ;; enqueue (qk k) ;; dmd dbody)
    (depot_after z tr (dtick S))) W
    (mkCfg (mkst regs4 (getr (ms_regs msD) 1) mem4 (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat4 md))
    (fun r W' c' => exists z0, r = (tt, qfin_c S k z0 tr) /\ W' = W /\ exists regs' mem' mat,
      c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md) mat md) /\
      (forall r : bv 5, In r CALLEE_SAVED -> getr regs' r = getr regs0 r) /\
      dmem_c W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 q lastb (dpost inst ly S W tr z0) mem')).
  { unfold enqueue, dmd. cbn [bind modify ibind get].
    change (set_chunks (upd_chunk (st_chunks (depot_after z tr (dtick S))) (qk k)) (depot_after z tr (dtick S))) with (qx S k z tr).
    rewrite NNB. cbn [bind ret ibind modify st_qthread set_qthread].
    rewrite QBY. cbn [ret amreal].
    rewrite Q1. eapply SRr_mono.
    { apply (DGge.segC W ly regs0 mem md tr pa nn hb1 q lastb j1 j2 j3 regs FH msD E3 regs4 mem4 mat4).
      split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact Hfr4|].
      split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
    intros W' c' _ HR. exists z. split; [reflexivity|].
    destruct HR as (-> & regs' & mem' & mat & -> & CS & EQS4 & PRS & PRW & VALS).
    split; [reflexivity|]. exists regs', mem', mat. split; [reflexivity|]. split; [exact CS|].
    exact (dmem_c_ok W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH (dpost inst ly S W tr z) (ms_mem msD) mem4 mem'
      MEQD Hfr4 Hpr4 DP4 EQS4 PRS PRW VALS). }
  pose proof (Fdaok _ _ _ _ _ _ _ DP4) as AOK.
  destruct AOK as [-> | [-> _]].
  - cbn [Z.eqb ret ibind]. exact TAIL.
  - cbn [Z.eqb bind get ret ibind].
    lazymatch goal with |- context [mcheck ?b1 469488] => destruct b1 end; cbn [mcheck ret ibind]; [|exact I].
    lazymatch goal with |- context [mcheck ?b2 460508] => destruct b2 end; cbn [mcheck ret put ibind]; [|exact I].
    exact TAIL. }
(* the leaf *)
eapply amreal_mono; [| exact (amreal_apath_gflag tfibsegs _ _ _ _ MAIN)].
intros r W' c' [(z & -> & -> & regs' & mem' & mat & -> & RCS & DM) HPATH].
rewrite R2 in DM.
destruct (Fpost_c inst ly S W mem md p n tr k lastb initr hb1 z (bv_unsigned (getr regs 2)) mem' mat HARX HRP HFP HBLK Htr Hf Hst Hrev Hroom Hcache
  ltac:(unfold DFSTACK_G, DFSTACK, DGbaseC.DFSTACK in *; lia) Hhi Hbot Hal Hhb1 Hhdr DM HPATH) as [HARX' HLP].
exists ly, regs', mem', (with_vm_backing (m_vm_lazy md) mat md).
split. { unfold cfg_at, raZ, w64. rewrite R1, Z_to_bv_bv_unsigned. reflexivity. }
destruct DM as (_ & DMfr & _ & _ & DMps & _).
assert (ERR : ErrnoG.errno_kept B mem mem').
{ intros i Hi.
  assert (EB : bv_unsigned (w64 (as_errno B + i)) = TFIB_ERRNO + i)
    by (rewrite (ts_errno _ TS); apply unsigned_lit_small; unfold TFIB_ERRNO; lia).
  destruct (errno_out W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs FH (TFIB_ERRNO + i) ltac:(lia)) as (NW & ND & NI & NS).
  apply DMfr; rewrite EB.
  - intros Hw. apply NW. unfold DGgi.WIN. unfold dwin_c in Hw. rewrite R2. exact Hw.
  - exact ND.
  - exact NI.
  - exact NS. }
(* memnorm: the same raw frame (DMfr) keeps it (memnorm_dmem_c). *)
assert (MNK : MemnormT.memnorm_keep tfibsegs mem mem').
{ apply (memnorm_dmem_c W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs mem' FH).
  intros x NW ND NI NS. apply DMfr; [| exact ND | exact NI | exact NS].
  intros Hw. apply NW. unfold DGgi.WIN. unfold dwin_c in Hw. rewrite R2. exact Hw. }
(* DGfy.v:369 with the memnorm conjunct (MNK) after errno's two *)
split; [|split; [exact ERR | split; [|split; [exact MNK | split; [exact HLP | exact HPATH]]]]].
(* copy of DGfy.v:370-399, unchanged *)
2:{ intros a Ha. apply aview_same. pose proof (ERR (a - as_errno B) ltac:(lia)) as E.
    replace (as_errno B + (a - as_errno B)) with a in E by lia. unfold w64 in E. exact E. }
split; [exact HARX'|]. split; [apply layout_le_refl|]. split; [apply wle_refl|].
split; [exact (aregs_of_cs regs pa inst bp so regs' RCS)|].
split. { unfold same_io. destruct md; cbn; repeat split; reflexivity. }
assert (FRAW : forall x : word, ~ AOX ly S (bv_unsigned x) -> ~ AOX ly (qfin_c S k z tr) (bv_unsigned x) ->
  ~ ascratch B DFSTACK_G regs (bv_unsigned x) ->
  ~ (p <> PNull /\ sptr_addr B ly p <= bv_unsigned x < sptr_addr B ly p + req_size n) -> mem' x = mem x).
{ intros x NO NO' NS NE. assert (Ra : 0 <= bv_unsigned x < 2 ^ 64) by apply u64_range. apply DMfr.
  - intros Hw. unfold dwin_c in Hw. destruct Hw as [Hs|[Hw|Hw]].
    + apply NS. unfold ascratch. left. unfold spZ, DFSTACK_G. unfold DFSTACK in Hs. exact Hs.
    + destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(left; exact Hw)) as [O|O];
      [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
    + unfold DGgi.WINB in Hw. destruct Hw as [Hw|[Hw|[Hw|Hw]]].
      * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; left; exact Hw)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
      * destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; left; exact Hw)) as [O|O];
        [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
      * exact (NO (Fown_b inst ly S W mem md lastb initr _ HARX Hrev Ra ltac:(left; exact Hw))).
      * exact (NO (Fown_b inst ly S W mem md lastb initr _ HARX Hrev Ra ltac:(right; exact Hw))).
  - intros Hd. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; right; left; exact Hd)) as [O|O];
    [exact (NO O) | apply NE; split; [exact DVnn | exact O]].
  - intros Hi. exact (NO (Fown_i inst ly S W mem md _ HARX Hi)).
  - intros Hs. destruct (Fown inst ly S W mem md p n k _ HARX HRP HBLK Hf Ra ltac:(right; right; right; right; exact Hs)) as [O|O];
    [exact (NO O) | apply NE; split; [exact DVnn | exact O]]. }
split.
{ intros a Ra NO NO' NS NE. apply aview_same. apply FRAW; rewrite unsigned_lit_small by exact Ra; assumption. }
split; [exact FRAW|].
intros a Ha. unfold spZ, DFSTACK_G in Ha. apply DMps. unfold DFSTACK. exact Ha.
Qed.
End b.
End d.
