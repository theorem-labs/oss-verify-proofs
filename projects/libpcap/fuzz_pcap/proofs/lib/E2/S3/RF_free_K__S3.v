(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBase.
From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Image ZBridge SysStep Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RF_free_K.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

Lemma rdrop_regions : s_regions st' = delete rid (s_regions st). Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st). Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof using CEILV MSECV rid. pin_using (fun (CEILV MSECV rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.

Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof using CEILV MSECV PTR. pin_using (fun (CEILV MSECV PTR : unit) => tt). ceil_facts. msec_facts.
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof using CEILV MSECV PTR. pin_using (fun (CEILV MSECV PTR : unit) => tt). ceil_facts. msec_facts.
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
Lemma ractives_drop : actives st' = actives st.
Proof using CEILV MSECV PTR. pin_using (fun (CEILV MSECV PTR : unit) => tt). ceil_facts. msec_facts.
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof using CEILV MSECV PTR. pin_using (fun (CEILV MSECV PTR : unit) => tt). ceil_facts. msec_facts.
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof using PTR. pin_using (fun (PTR : unit) => tt). ceil_facts. msec_facts.
  intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

Lemma rptrs_in_norid st2 LB c rid r m :
  KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
  ci_mptrs st2 ->
  ptrs_in (fun x => x <> rid) st2.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rfree_fp_hdr_st st pf lo (sp sp' : Z) a : ticks_ok st ->
  (forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w) ->
  sp' <= sp -> rfree_fp (hdr_st st pf) lo sp' a -> rfree_fp st lo sp a.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros TK HK HS H. destruct H as [H|[H|H]].
  - left. destruct H as [H|[H|H]]; [left; lia| right; left; exact H| right; right; exact H].
  - right; left. exact H.
  - right; right. destruct H as (rid & r & v & H1 & H2 & H3 & H4). destruct (hdr_st_known_back st pf rid _ v TK HK H4) as [w Hw].
    exists rid, r, w. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section DROP.
Variables (st : mstate) (rid : N).
Let st' := drop_region rid st.
Hypothesis PTR : ptrs_in (fun x => x <> rid) st.

Lemma rdrop_regions : s_regions st' = delete rid (s_regions st). Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rdrop_shadow : s_shadow st' = delete rid (s_shadow st). Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rconc_drop q : fst q <> rid -> conc st' q = conc st q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros NE. unfold conc, get_region. cbn [st' drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rpw_drop p : optr_in (fun x => x <> rid) p -> pw st' p = pw st p.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. destruct p as [q|]; cbn; intros H; [| reflexivity]. unfold pw. cbn [oconc]. rewrite rconc_drop by exact H. reflexivity. Qed.
Lemma rget_shadow_drop rid' : rid' <> rid -> get_shadow st' rid' = get_shadow st rid'.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros NE. rewrite !get_shadow_unfold. cbn [st' drop_region s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rrec_drop q : get_meta_rec st' q = get_meta_rec st q. Proof using CEILV MSECV rid. pin_using (fun (CEILV MSECV rid : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.

Lemma rmeta_cells_drop q : meta_cells st' (get_meta_rec st q) = meta_cells st (get_meta_rec st q).
Proof using CEILV MSECV PTR. pin_using (fun (CEILV MSECV PTR : unit) => tt). ceil_facts. msec_facts.
  destruct PTR as (_ & _ & _ & _ & _ & _ & _ & PM & _). destruct (PM q) as (P1 & P2 & P3).
  unfold meta_cells. rewrite !rpw_drop by assumption. reflexivity.
Qed.

Lemma rctx_head_cells_drop : ctx_head_cells st' = ctx_head_cells st.
Proof using CEILV MSECV PTR. pin_using (fun (CEILV MSECV PTR : unit) => tt). ceil_facts. msec_facts.
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & _). unfold ctx_head_cells. change (ctx st') with (ctx st).
  rewrite !rpw_drop by assumption. reflexivity.
Qed.
Lemma ractives_drop : actives st' = actives st.
Proof using CEILV MSECV PTR. pin_using (fun (CEILV MSECV PTR : unit) => tt). ceil_facts. msec_facts.
  destruct PTR as (_ & _ & _ & _ & _ & PA & _). unfold actives. apply map_ext. intros i.
  change (active st' (Z.of_nat i)) with (active st (Z.of_nat i)). apply rpw_drop. apply PA.
Qed.
Lemma rctx_tail_cells_drop : ctx_tail_cells st' = ctx_tail_cells st.
Proof using CEILV MSECV PTR. pin_using (fun (CEILV MSECV PTR : unit) => tt). ceil_facts. msec_facts.
  destruct PTR as (_ & _ & _ & _ & _ & _ & PB & _). unfold ctx_tail_cells, brk_word. change (ctx st') with (ctx st).
  destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity. rewrite (rconc_drop (brid, boff)) by exact PB. reflexivity.
Qed.

Lemma rmrep_drop_region m : rmrep st m -> rmrep st' m.
Proof using PTR. pin_using (fun (PTR : unit) => tt). ceil_facts. msec_facts.
  intros MR. pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct PTR as (P1 & P2 & P3 & P4 & P5 & PA & PB & PM & PAR & PG).
  split; [|split; [|split; [|split; [|split]]]].
  - split; [exact Hres|]. split; [|split; [|split]].
    + intros k r Hk. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. apply (WR k r). tauto.
    + intros k1 r1 k2 r2 H1 H2 NE. cbn [st' drop_region s_regions set_shadow set_regions] in H1, H2.
      apply lookup_delete_Some in H1. apply lookup_delete_Some in H2. apply (DJ k1 r1 k2 r2); tauto.
    + intros a ar Ha. destruct (PAR a ar Ha) as [Pa _]. destruct (WA a ar Ha) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_areas]. rewrite lookup_delete_ne by congruence. auto.
    + intros b gh Hb. destruct (PG b gh Hb) as [Pb _]. destruct (WG b gh Hb) as (r & Hr & REST). exists r.
      cbn [st' drop_region s_regions set_shadow set_regions s_groups]. rewrite lookup_delete_ne by congruence. auto.
  - unfold rmrep_ctx. rewrite rctx_head_cells_drop, ractives_drop, rctx_tail_cells_drop.
    change (usages st') with (usages st). change (unmap_seqs st') with (unmap_seqs st). change (bouncess st') with (bouncess st). exact CX.
  - exact GL.
  - intros a ar Ha. destruct (PAR a ar Ha) as [Pa Pn]. destruct (AR a ar Ha) as (A1 & A2 & A3).
    unfold rarea_rep. rewrite (rconc_drop a) by exact Pa. rewrite rpw_drop by exact Pn. split; [exact A1|]. split; [| exact A3].
    intros k Hk. rewrite rrec_drop, rmeta_cells_drop. apply A2. exact Hk.
  - intros b gh Hb. destruct (PG b gh Hb) as [Pb Pm]. destruct (GR b gh Hb) as (w8 & R & Hw). exists w8.
    rewrite (rconc_drop b) by exact Pb. rewrite rpw_drop by exact Pm. auto.
  - intros k r Hk Kr. cbn [st' drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
    unfold rshadow_rep. rewrite rget_shadow_drop by congruence. exact (SH k r Hk Kr).
Qed.
End DROP.

Lemma rptrs_in_norid st2 LB c rid r m :
  KINV st2 LB c -> ZINV st2 [] -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  (forall b gh, (s_groups st2) !! b = Some gh -> fst b <> rid) ->
  ci_mptrs st2 ->
  ptrs_in (fun x => x <> rid) st2.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros K ZI MR Hr Kr NOG (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split; [| split].
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
    + destruct (m_mem (get_meta_rec st2 g)) as [b|] eqn:MB; cbn; [| exact I].
      destruct (ZI g b MB) as [[ai Hb]|[]]. exact (NOG b _ Hb).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb. split; [exact (NOG b gh Hb)|].
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_free_K.

(* [comment removed for export] *)
Module RF_am_E.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Import F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_E.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
  bytes_at ssegs m S src -> length src = Z.to_nat n ->
  rw_cells ssegs m D [CB (Z.to_nat n) junk] ->
  0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
  (S + n <= D \/ D + n <= S) ->
  mem_inv ssegs m ->
  evt ssegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' D [CB (Z.to_nat n) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x207e0) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
      [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
  destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
  do 15 eexists. split; [reflexivity|]. auto.
Qed.

Lemma ru64s_read : forall m A ws (i : Z) w a,
  bytes_at ssegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes ssegs m a 8 = Some (le8 w).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read ssegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrw_cells_app_split : forall m A cs1 cs2,
  rw_cells ssegs m A (cs1 ++ cs2) -> rw_cells ssegs m A cs1 /\ rw_cells ssegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma rrw_cells_app_join : forall m A cs1 cs2,
  rw_cells ssegs m A cs1 -> rw_cells ssegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells ssegs m A (cs1 ++ cs2).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19038) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
    /\ stk ssegs m' lo (bv_unsigned sp + -64)
    /\ rmrep (am_init_st st) m'.

Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv ssegs m -> rauxv_ok m (bv_unsigned sp) ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  (c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = msecret -> 0 <= c_secret (ctx st) < 2^64 ->
  evt ssegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18f84) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5) & _). unfold ctx_head_cells in C1.
  unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *; ceil_facts. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & X3 & X4 & X5 & X16 & X6 & X11 & X12 & X23 & XR).
  unfold RAUXV_CELL in AVC.
  (* [comment removed for export] *)
  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with H : rw_cells ssegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{ (* [comment removed for export] *)
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; ceil_facts; lia. }
  (* [comment removed for export] *)
  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  Ltac skip_iter i key HB :=
    let RD := fresh "RD" in
    st1;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ i (wz key) (wa (_ + 8 * i)) HB eq_refl ltac:(lia) eq_refl) as RD end;
    st1; try clear RD;
    st1; change (bv_eqb (wz key) (Z_to_bv 64 25)) with false; cbv iota;
    st1; change (negb (bv_eqb (wz key) (Z_to_bv 64 0))) with true; cbv iota;
    st1.
  (* [comment removed for export] *)
  skip_iter 0 3 AVL.
  skip_iter 2 4 AVL. skip_iter 4 5 AVL. skip_iter 6 16 AVL. skip_iter 8 6 AVL.
  skip_iter 10 11 AVL. skip_iter 12 12 AVL. skip_iter 14 23 AVL.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 16 (wz 25) (wa (_ + 8 * 16)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD.
  st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 17 (wz rnd) (wa (_ + 8 * 17)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD. st1. st1. st1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge ssegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  (* [comment removed for export] *)
  st1.
  call rmemcpy_callZ3.
  1:{ exact RND. } 1:{ reflexivity. } 1:{ exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ lazymatch goal with H : mem_inv ssegs ?mX |- mem_inv ssegs ?mX => exact H end. }
  lazymatch goal with H : rw_cells ssegs ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz msecret))] |- _ => rename H into DST end.
  (* [comment removed for export] *)
  st1. st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 18 (wz 0) (wa (_ + 8 * 18)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD.
  st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
  st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* [comment removed for export] *)
  lazymatch type of DST with rw_cells _ ?mX _ _ =>
    assert (DST8 : rw_cells ssegs mX (bv_unsigned sp + -64) [C8 (wz msecret)])
      by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
          split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
    clear DST end.
  st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; ceil_facts; lia);
    pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl ssegs mX) as WMc end.
  clear MUh. unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1.
  set (stI := upd_ctx (fun c => set_init_done 1 (set_secret msecret c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
  { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw stI ?q) with (pw st q). unfold wz at 2.
      lazymatch goal with H : rw_cells ssegs ?mX 343456 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc MRX.
  (* [comment removed for export] *)
  st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with Hm : rw_cells ssegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells ssegs mX (bv_unsigned sp + -56) ?csc |- _ =>
      pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
      cbn [app] in J2; clear Hm Hc;
      lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
        apply (rw_cells_merge ssegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
    end end.
  apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
  unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_am_E.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_am_A.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rmemcpy_callZ3 : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (D S n : Z) (src junk : list byte),
  bytes_at usegs m S src -> length src = Z.to_nat n ->
  rw_cells usegs m D [CB (Z.to_nat n) junk] ->
  0 <= D -> D + n <= 2^64 -> 0 <= S -> S + n <= 2^64 -> 0 < n ->
  (S + n <= D \/ D + n <= S) ->
  mem_inv usegs m ->
  evt usegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 D) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' D [CB (Z.to_nat n) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20fa0) fc None m (seg_rom usegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until junk. intros SRC LEN DST D0 D1 S0 S1 N0 SEP MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  eapply evt_mono.
  { eapply (memcpy_spec ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 n)); rewrite ?ED, ?ES, ?EN;
      [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' P. unfold memcpy_post in P. rewrite !ED, !EN in P.
  destruct P as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m' & -> & MU & WM & MI' & DST' & _).
  do 15 eexists. split; [reflexivity|]. auto.
Qed.

Lemma ru64s_read : forall m A ws (i : Z) w a,
  bytes_at usegs m A (u64s ws) -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i -> a = wa (A + 8 * i) ->
  ov_read_bytes usegs m a 8 = Some (le8 w).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros m A ws i w a Hb Hn Hi ->.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  replace (8 * i)%Z with (Z.of_nat (8 * Z.to_nat i))%Z by lia.
  rewrite (bytes_at_ov_read usegs m A (u64s ws) (8 * Z.to_nat i) 8 Hb).
  2:{ rewrite Eu, !length_app, length_le8, Hlu. lia. }
  rewrite Eu, skipn_app, skipn_all2, Hlu, Nat.sub_diag by lia. rewrite skipn_O, app_nil_l.
  rewrite firstn_app, firstn_all2 by (rewrite length_le8; lia).
  rewrite length_le8, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma rrw_cells_app_split : forall m A cs1 cs2,
  rw_cells usegs m A (cs1 ++ cs2) -> rw_cells usegs m A cs1 /\ rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m A cs1 cs2 H. split; [eapply rw_cells_prefix; exact H|].
  destruct H as [[WF B] W].
  apply cells_wf_app in WF. destruct WF as [WF1 WF2].
  rewrite cells_bytes_app in B. apply bytes_at_app in B. destruct B as [_ B2]. rewrite cells_bytes_length in B2 by exact WF1.
  split; [split; [exact WF2 | exact B2] |].
  rewrite cells_size_app in W. eapply wr_at_sub; [exact W | lia | lia].
Qed.

Lemma rrw_cells_app_join : forall m A cs1 cs2,
  rw_cells usegs m A cs1 -> rw_cells usegs m (A + Z.of_nat (cells_size cs1)) cs2 -> rw_cells usegs m A (cs1 ++ cs2).
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros m A cs1 cs2 [[WF1 B1] W1] [[WF2 B2] W2]. split; [split|].
  - apply cells_wf_app. split; assumption.
  - rewrite cells_bytes_app. apply bytes_at_app. split; [exact B1|]. rewrite cells_bytes_length by exact WF1. exact B2.
  - rewrite cells_size_app. destruct W1 as (H0 & H1 & X1). destruct W2 as (H2 & H3 & X2). split; [lia|]. split; [lia|].
    intros i Hi. destruct (Z.lt_ge_cases i (Z.of_nat (cells_size cs1))).
    + apply X1. lia.
    + replace (A + i) with (A + Z.of_nat (cells_size cs1) + (i - Z.of_nat (cells_size cs1))) by lia. apply X2. lia.
Qed.

Definition ram_entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists x1 t0 t1 t2 s1x s4x a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' junk,
    ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (Z_to_bv 64 4096) s1x a0 a1 a2 a3 a4 a5 a6 a7
                  (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 RMLOCK) s4x s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x197f8) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' (bv_unsigned sp + -64) (ram_frame junk s4 s3 s2 s1 s0 ra)
    /\ stk usegs m' lo (bv_unsigned sp + -64)
    /\ rmrep (am_init_st st) m'.

Lemma ram_entry : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m : word -> option byte) (lo : Z) (st : mstate),
  rmrep st m -> mem_inv usegs m -> rauxv_ok m (bv_unsigned sp) ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  (c_init_done (ctx st) = 0 \/ c_init_done (ctx st) = 1) -> s_secret st = msecret -> 0 <= c_secret (ctx st) < 2^64 ->
  evt usegs (ram_entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19744) fc None m (seg_rom usegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until st. intros MR MI AUX ST LO LOLE INIT SEC0 SECR.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR as (WF & (C1 & _) & (_ & _ & PGS & G4 & G5) & _). unfold ctx_head_cells in C1.
  unfold RCTX, RGOT_SSP, RSSP_GUARD, RPAGE_SIZE in *; ceil_facts. unfold wz in G4.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (RCTX, RCTX + 16)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM. unfold RCTX in MU.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MUh.
  destruct AUX as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & AVC & AVL & RND & AB & BAV & AVH & BR & RH & X3 & X4 & X5 & X16 & X6 & X11 & X12 & X23 & XR).
  unfold RAUXV_CELL in AVC.
  (* [comment removed for export] *)
  st1. carve_frame 64%nat ST. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned sp + -64) (CB 8 ?j :: _) |- _ => set (junk8 := j) in H; clearbody junk8 end.
  destruct INIT as [I0|I1].
  2:{ (* [comment removed for export] *)
      rewrite I1. change (negb (bv_eqb (wz 1) (Z_to_bv 64 0))) with true. cbv iota.
      st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
      apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
      split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact FR|]. split; [exact ST|].
      unfold am_init_st. rewrite I1. cbn [Z.eqb Pos.eqb].
      eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]. intros l h [E|[]]; inversion E; subst; ceil_facts; lia. }
  (* [comment removed for export] *)
  rewrite I0. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1. st1.
  (* [comment removed for export] *)
  Ltac skip_iter i key HB :=
    let RD := fresh "RD" in
    st1;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      pose proof (ru64s_read mX _ _ i (wz key) (wa (_ + 8 * i)) HB eq_refl ltac:(lia) eq_refl) as RD end;
    st1; try clear RD;
    st1; change (bv_eqb (wz key) (Z_to_bv 64 25)) with false; cbv iota;
    st1; change (negb (bv_eqb (wz key) (Z_to_bv 64 0))) with true; cbv iota;
    st1.
  (* [comment removed for export] *)
  skip_iter 0 3 AVL.
  skip_iter 2 4 AVL. skip_iter 4 5 AVL. skip_iter 6 16 AVL. skip_iter 8 6 AVL.
  skip_iter 10 11 AVL. skip_iter 12 12 AVL. skip_iter 14 23 AVL.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 16 (wz 25) (wa (_ + 8 * 16)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD.
  st1. change (bv_eqb (wz 25) (Z_to_bv 64 25)) with true. cbv iota.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 17 (wz rnd) (wa (_ + 8 * 17)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD. st1. st1. st1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch type of FR with rw_cells _ _ _ (?c1 :: ?rest) =>
      destruct (rrw_cells_app_split mX _ [c1] rest FR) as [FRm FRc];
      cbn [cells_size csize Nat.add] in FRc;
      replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) in FRc by lia;
      apply (rw_cells_merge usegs mX _ [] [c1] []) in FRm; cbn [cells_size csize Nat.add cells_bytes cbytes app] in FRm;
      rewrite app_nil_r in FRm; clear FR
    end end.
  (* [comment removed for export] *)
  st1.
  call rmemcpy_callZ3.
  1:{ exact RND. } 1:{ reflexivity. } 1:{ exact FRm. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
  1:{ lazymatch goal with H : mem_inv usegs ?mX |- mem_inv usegs ?mX => exact H end. }
  lazymatch goal with H : rw_cells usegs ?mX (bv_unsigned sp + -64) [CB _ (le8 (wz msecret))] |- _ => rename H into DST end.
  (* [comment removed for export] *)
  st1. st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (ru64s_read mX _ _ 18 (wz 0) (wa (_ + 8 * 18)) AVL eq_refl ltac:(lia) eq_refl) as RD end.
  st1. try clear RD.
  st1. change (bv_eqb (wz 0) (Z_to_bv 64 25)) with false. cbv iota.
  st1. change (negb (bv_eqb (wz 0) (Z_to_bv 64 0))) with false. cbv iota.
  (* [comment removed for export] *)
  lazymatch type of DST with rw_cells _ ?mX _ _ =>
    assert (DST8 : rw_cells usegs mX (bv_unsigned sp + -64) [C8 (wz msecret)])
      by (destruct DST as [[_ B] W]; cbn [cells_bytes cbytes app] in B; rewrite app_nil_r in B;
          split; [split; [cbn; tauto| cbn [cells_bytes cbytes app]; rewrite app_nil_r; exact B]| exact W]);
    clear DST end.
  st1.
  (* [comment removed for export] *)
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRX : rmrep st mX) by (eapply rmrep_transport_high; [exact MR| exact MUh| exact WM|]; intros l h [E|[]]; inversion E; subst; ceil_facts; lia);
    pose proof (munch_refl [(RCTX, RCTX + 16)]%Z mX) as MUc; pose proof (wmono_refl usegs mX) as WMc end.
  clear MUh. unfold RCTX in MUc.
  (* [comment removed for export] *)
  st1. st1.
  set (stI := upd_ctx (fun c => set_init_done 1 (set_secret msecret c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRI : rmrep stI mX) end.
  { eapply (rmrep_ctx_frameW st stI _ _ _ MRX MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - left. unfold ctx_head_cells, RCTX. cbn [ctx stI upd_ctx s_ctx set_init_done set_secret c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      change (pw stI ?q) with (pw st q). unfold wz at 2.
      lazymatch goal with H : rw_cells usegs ?mX 345440 _ |- _ => exact H end.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold RCTX; lia. }
  clear MUc WMc MRX.
  (* [comment removed for export] *)
  st1. st1. st1. change (bv_ltu (Z_to_bv 64 4096) (wz 4096)) with false. cbv iota. st1.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    lazymatch goal with Hm : rw_cells usegs mX (bv_unsigned sp + -64) ?csm, Hc : rw_cells usegs mX (bv_unsigned sp + -56) ?csc |- _ =>
      pose proof (rrw_cells_app_join mX _ csm csc Hm ltac:(cbn [cells_size csize Nat.add]; replace (bv_unsigned sp + -64 + Z.of_nat 8) with (bv_unsigned sp + -56) by lia; exact Hc)) as J2;
      cbn [app] in J2; clear Hm Hc;
      lazymatch type of J2 with rw_cells _ _ _ (?c1 :: ?rest) =>
        apply (rw_cells_merge usegs mX _ [] [c1] rest) in J2; cbn [cells_size csize Nat.add cells_bytes cbytes app] in J2; rewrite app_nil_r in J2 end
    end end.
  apply evt_done. unfold ram_entry_post, RCTX, RSSP_GUARD, RMLOCK. do 20 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact J2|]. split; [exact ST|].
  unfold am_init_st. rewrite I0, SEC0. cbn [Z.eqb]. exact MRI.
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_am_E.

(* [comment removed for export] *)
Module RF_ntf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_C.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_ntf_D. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_ntf_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_F OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_G OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_H OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_F OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_G OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_H.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
    (st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp) /\ rmrep st' m'
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
    /\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_entry st lo (sp : word) m m1 :
  munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono ssegs m m1 -> lo <= bv_unsigned sp - 96 ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.

Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
  oracle_ok o m st -> rmrep st mw -> alloc_ceiling <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
  rewrite (OK rid r q h Hr Hk Hq M8 Hc).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  ceil_facts.
  symmetry. apply (PE (r_base r + q)); [lia|].
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid' & r' & Hr' & Hk' & Hin).
    destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
    pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
  - destruct A as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RbB0 & _).
    destruct (WR (fst b) rb Hrb) as (_ & RbAL & _).
    assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
    Z.div_mod_to_equations. lia.
  - destruct A as (rid' & r' & v & Hr' & Hk' & Hin & HC).
    destruct (N.eq_dec rid' rid) as [->|NE].
    + rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

Lemma rfree_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

(* [comment removed for export] *)
Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> alloc_ceiling <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
  ceil_facts.
  destruct H as [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). ceil_facts. lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
Qed.

(* [comment removed for export] *)
Lemma rknown_byte st m (q : aptr) r v :
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v ->
  bytes_at ssegs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

(* [comment removed for export] *)
Lemma rimplT_queue {R} o h g st0 (k : mstate -> Malloc.M R) bail s Q ms :
  (m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
  rimplT o (queue h g st0 k bail) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
  assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
  assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
  specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.

Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
  rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
  (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
  (exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
  oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
  rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof using LO. pin_using (fun (LO : unit) => tt). ceil_facts. msec_facts.
  intros RP PE FP KI ZI FR RES OOK MRX ER ES.
  destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
  unfold rntf_q. do 16 eexists. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
  split. { eapply rpres_except_trans; [exact PE|]. eapply rpres_except_mono; [exact PE'|]. exact FP. }
  split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
  eapply oracle_ok_frame; [| exact ER | exact ES]. eapply roracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> Malloc.M R) (bail : Malloc.M R)
    (s : PState) (Q : R -> PState -> machine_state -> Prop)
    (ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
  KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
  rmrep st m -> mem_inv ssegs m -> oracle_ok o m st ->
  stk ssegs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
  (forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
  rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x18bac) fc None m (seg_rom ssegs)).
Proof using LO. pin_using (fun (LO : unit) => tt). ceil_facts. msec_facts.
  induction fuel as [|f IH]; intros until Zs; intros KI LP ZI MR MI OOK ST DEPTH KH.
  { cbn [nontrivial_free]. apply rimplT_undef. }
  rewrite ntf_unfold. cbv zeta.
  pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
  pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
  pose proof (go_slot _ _ _ GO) as MSL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
  set (ms0 := MS _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (ENTRY : entry_hyps st g i ->
    evt ssegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
  { intros EH. subst ms0. eapply rntf_entry; eauto. }
  (* [comment removed for export] *)
  assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
                       (G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
                       (G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
                             m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
             entry_hyps st g i).
  { intros. constructor; auto.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - pose proof (go_sc _ _ _ GO). lia.
    - intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
    - intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
    - split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
  destruct (ntf_cond st g i) eqn:HC.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
      rfg_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
              (m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
      (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
      wmono ssegs m m2 -> oracle_ok o m2 stX ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
    { intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
      pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
      unfold rfg_post in FGP. destruct FGP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
      set (stU := fg_usage_st stX g) in *.
      assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
      assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
      rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
      rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).
      (* [comment removed for export] *)
      assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
      { destruct (data_of_fields _ _ g DATX) as (_ & EA & EF & EL & _).
        unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
        unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
        pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
        apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
          try lia; try exact HALL.
        - exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
        - destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tauto.
        - destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tauto. }
      assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
      assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; exact LPX).
      assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact GNX)).
      rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
          [ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
          | pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact Hj) ltac:(rewrite RU; apply ALLFREE; [exact Hj| exact NE])) as FC;
            rewrite RU in FC; exact FC ])).
      fold stG in GD. destruct GD as (KIG & NGM & NSL).
      assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; exact MR3).
      assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; exact FRX).
      assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).
      (* [comment removed for export] *)
      pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
      pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
      replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
      change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
      destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
      - (* [comment removed for export] *)
        assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
        rewrite free_meta_eq.
        eapply rimplT_evt.
        { eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
            first [exact MRG | exact MI3 | exact MSG | exact MWU | exact MEMU | exact MLNZ | exact FR3 | exact ST3 | exact LO | exact LOLE | reflexivity
                  | apply munch_refl | apply wmono_refl | idtac].
          - pose proof (ki_cx _ _ _ KIG) as (SQ & _). exact SQ.
          - intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [exact GNU| exact Hhd]. }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try exact RP.
        + destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
            (eapply rpres_except_mono; [exact PE3| exact FPX]).
        + intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | exact Ha].
          unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
        + eexists. apply KINV_fm; [apply KINV_seq; exact KIG| | | |].
          * unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [exact MSG|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros [b Hb]. apply NGM. exists b. unfold hosts in *.
            replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [exact Hb|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [exact GNU|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
        + apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + (* [comment removed for export] *)
          pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8).
          set (stS := record_seq _ (step_seq stG)) in *.
          assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; exact GNU).
          unfold fm_st. apply frame_queue.
          * apply frame_put_meta; [apply frame_seq; exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
          * apply links_put_meta0; [exact (ki_links _ _ _ KIS)| exact GNS].
          * cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
            intros hd Hhd. destruct (kinv_free_head stS LB _ hd KIS Hhd) as (_ & NX' & _).
            rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| exact NX'].
          * right; exact (hosts_is_gm _ _ _ HOSTS).
        + (* [comment removed for export] *)
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & FS2 & FS3 & _).
          destruct (go_region _ _ _ GOX) as (r & Hr & Kr & _ & _ & _ & TOP). rewrite <- RU in TOP.
          change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
          pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
          unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [exact SND| split]]]].
          * unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
          * exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
          * intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
            apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
            apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; exact MLNZ | exact ALLFREE | exact Hb' | exact E].
        + eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [exact OOK2 | exact MRW | exact LO | exact PE3].
        + exact MRG.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (_ & SR2 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (_ & FS2 & _). rewrite FS2, SR2. reflexivity.
      - (* [comment removed for export] *)
        assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).
        (* [comment removed for export] *)
        pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
        destruct (NEST MLZ) as (g1 & i1 & b1 & SL1 & HB1 & FB1 & PSS & I1 & NF1 & LT1 & v3 & lo8 & hi8 & K3 & V31 & K2 & K1 & OFF).
        clear NEST.
        pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
        destruct (go_region _ _ _ GOX) as (r & Hr & Kr & SP0 & SP16 & SPAN & _).
        destruct (go_region _ _ _ GO1) as (r1 & Hr1 & _ & SB0 & SB16 & SPAN1 & _).
        rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
        assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
        assert (B1LT : snd b1 + 16 <= snd p).
        { rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
          pose proof (go_stride _ _ _ GO1) as [S16 _].
          assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
        assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
        assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; exact HB1).
        assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [exact NEb1| exact HB1U]).
        (* [comment removed for export] *)
        pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
        assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
        { split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
          rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
          unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
          rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
          assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
          unfold UNIT, IB in *. lia. }
        destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].
        (* [comment removed for export] *)
        unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
        assert (SHG : forall c', get_shadow stG c' = get_shadow stX c').
        { intros c'. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow. reflexivity. }
        apply rimplT_rd16; [peek_known_sh SHG| peek_known_sh SHG|]. apply rimplT_rd8; [peek_known_sh SHG|]. cbv zeta. apply rimplT_rd8; [peek_known_sh SHG|].
        assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
        { intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
          unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
        rewrite !ESH.
        rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; exact K4).
        rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; exact K3).
        rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; exact K2).
        rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; exact K1).
        cbn [Z.eqb negb].
        set (off16 := lo8 + 256 * hi8).
        assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
        { unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
        rewrite EB. unfold get_group.
        replace (s_groups stG !! b1) with (s_groups stX !! b1).
        2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
        destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
        apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
        apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
        (* [comment removed for export] *)
        assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
        change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
        rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
        destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
        apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
        apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
        (* [comment removed for export] *)
        assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
        assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
        assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
                   bytes_at ssegs m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
        { intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; exact Hr) Kr ltac:(cbn; lia)
                   ltac:(cbn; unfold get_shadow; rewrite ESU; exact Hc)) as [B V].
          cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; exact Hr). cbn [snd] in B.
          rewrite (conc_region' stU p r) by (rewrite ERU; exact Hr). split; [| exact V].
          replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. exact B. }
        destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
        destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
        assert (HDR : bytes_at ssegs m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
        { change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
          apply bytes_at_app. split; [exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; exact Y3|].
          apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; exact Y2|].
          cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. exact Y1. }
        (* [comment removed for export] *)
        destruct HOSTSX as [aig Hghp].
        eapply rimplT_evt.
        { eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
          all: first [exact MR3 | exact MI3 | exact MWU | exact MLZ | exact MEMU | exact HDR | exact FR3 | exact ST3 | exact LO | exact LOLE
                     | exact R3 | exact R2 | exact R1 | exact AR1 | exact G15 | apply rntf_frame_size | idtac].
          all: try reflexivity.
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
          all: rewrite ?EU1.
          all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
               try exact G12; try exact G13; try exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
          all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); lia).
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
          all: try (unfold stU; rewrite fg_usage_groups; first [exact Hghp | exact Hgh1]).
          all: try (symmetry; exact EB).
          all: match goal with
               | |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
               | |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
                                   apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
               | |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
                                   fold off16 in G17; unfold UNIT in G17;
                                   replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
                                   rewrite Z.div_mul in G17 by lia; lia
               | |- ?G => idtac "NCGOAL" G; fail
               end. }
        intros ms3 NC. unfold rnest_call_post in NC.
        destruct NC as (z0 & z1 & z2 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
        fold stG in MR4.
        (* [comment removed for export] *)
        pose proof (bv_unsigned_in_range _ sp) as SPR'.
        assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (ceil_facts; rewrite unsigned_lit; lia).
        rewrite V31. replace (conc stU g1) with (conc stG g1) by reflexivity.
        eapply (IH R _ bail s Q (Z_to_bv 64 0x18e34) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
        + exact KIG.
        + constructor.
          * exact HB1G.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact I1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact NF1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
            apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
            pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
            pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
        + unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + exact MR4.
        + exact MI4.
        + apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [exact OOK2 | exact MRW | exact LO |].
          eapply rpres_except_trans; [exact PE3|]. eapply rpres_except_mono; [exact PE4|].
          intros a Ha. eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha].
        + rewrite SPU. exact ST4.
        + rewrite SPU. lia.
        + (* [comment removed for export] *)
          intros st3 mi ms5 NQ. rewrite free_meta_eq.
          unfold rntf_q in NQ. rewrite SPU in NQ.
          destruct NQ as (u0 & u1 & u2 & ra0' & ra1' & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MI5 & ST5 & MR5 & PE5 & [c3 KI3] & ZI3 & FR35 & RES5 & OOK5).
          replace (ret_pc (Z_to_bv 64 0x18e34)) with (Z_to_bv 64 0x18e34) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
          assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
          { apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
          assert (NGM3 : ~ is_gm st3 g).
          { intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). exact Hb. }
          eapply rimplT_evt.
          { eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
              first [exact MR5 | exact MI5 | exact LO | exact LOLE | reflexivity | idtac].
            - unfold meta_slot. rewrite (nf_areas _ _ FR35). exact MSG.
            - intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; exact GNU| exact Hhd].
            - unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
            - eapply rpres_except_rw_cells; [exact PE5 | exact FR4 |].
              intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
            - exact ST5. }
          intros ms6 RP. apply KH.
          pose proof (frame_trans _ _ _ FRG FR35) as FR03.
          pose proof (fm_shape st3 g) as (FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
          eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try exact RP.
          * destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE3| exact FPX]|]);
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha]]|]);
              (eapply rpres_except_mono; [exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [exact FRG| lia| exact Ha]]).
          * intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [exact FR03| lia| exact Ha].
          * exists c3. apply KINV_fm; [exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); exact MSG| exact NGM3| rewrite RG3; exact GNU|].
            intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). exact Hs.
          * apply ZINV_fm. exact ZI3.
          * unfold fm_st. apply frame_queue.
            -- apply frame_put_meta; [exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
            -- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; exact GNU].
            -- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
               intros hd Hhd. destruct (kinv_free_head st3 LB _ hd KI3 Hhd) as (_ & NX' & _).
               rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; exact GNU| exact NX'].
            -- right; exact (hosts_is_gm _ _ _ HOSTS).
          * destruct mi as [[bb len]|]; [| exact RES5].
            destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
            unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
            split; [exact A1|]. split; [exact LEN|]. split; [exact SND|]. split; [exists rr; rewrite FS1; auto|].
            intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
          * exact OOK5.
          * exact MR5.
          * exact FS1.
          * exact FS2. }
    (* [comment removed for export] *)
    assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
      s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
      (m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
      rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono ssegs m m4 -> mem_inv ssegs m4 ->
      stk ssegs m4 lo (bv_unsigned sp + -96) -> rw_cells ssegs m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
      ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
               F (Z_to_bv 64 0x18dd4) fc None m4 (seg_rom ssegs) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
    { intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
      assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
      eapply rimplT_evt.
      { eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
          first [exact MR4 | exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | exact USX | exact FR4 | apply rntf_frame_size | exact ST4 | exact LO | exact LOLE]. }
      intros ms5 FGP.
      eapply (FG2 stX m4 junk); [exact KIX | exact ZIX | exact LPX | exact FRX | exact GNX | right; exact PE4 | exact FGP | | exact WM4 | | exact DATX | exists m4; exact MR4].
      - intros a Ha. eapply (rfree_fp_same st stX); eauto.
      - apply (oracle_ok_frame o m4 st stX); [| exact ERX | exact ESX].
        eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [exact OOK | exact MR | exact LO | exact PE4]. }
    destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
    + (* [comment removed for export] *)
      apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
      set (sc := m_sizeclass (get_meta_rec st g)) in *.
      set (an := optr_eqb (active st sc) (Some g)).
      set (stm := deq_mid (LActive sc) g st).
      set (st1 := dequeue (LActive sc) g st).
      assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
      pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
      pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
      assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
      assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; exact ZI).
      assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [exact SBL1| exact LP]).
      assert (FR1' : ntf_frame st st1).
      { unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
      destruct (kinv_next _ _ _ _ _ KI NX) as (MSnx & Pnx & Nnx & pv & PV & MSpv & Npv & NEpv).
      pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
      destruct DS as (DSdata & GN1 & GP1 & _).
      (* [comment removed for export] *)
      assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono ssegs m m2 ->
        rat9c_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
                   (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (match an, active st1 sc with
                 | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
                 | _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
                 end) s Q ms2).
      { intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
        unfold rat9c_post in AP. destruct AP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
        assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
        { destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE3]| eapply rpres_except_trans; [exact PE0| exact PE3]]. }
        (* [comment removed for export] *)
        assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
        { pose proof (rmeta_slot_bounds st m g MR MSL) as (B0 & B1 & _). ceil_facts.
          rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
          - destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
            pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. pose proof (rmeta_slot_bounds st m h MR MSh) as (C0 & C1 & _). ceil_facts.
            unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). exact E.
          - unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
        assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
          evt ssegs (rat00_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x18d70) fc None m3 (seg_rom ssegs))).
        { intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
          eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
            first [exact MR3 | exact MI3 | exact HA3 | exact FR3 | apply rntf_frame_size | exact ST3 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBLm| exact MSL].
          - pose proof (go_sc _ _ _ GO). subst sc. lia.
          - rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
            destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
            destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
            destruct Hba as [ai Hgh]. pose proof (ki_grps _ _ _ KI1 ba _ Hgh) as (g' & Eg' & AI). cbn in Eg', AI. inversion Eg'; subst g'.
            split; [exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
            exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
        assert (AVK : forall a, an = true -> active st1 sc = Some a ->
                 rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x18d70) fc None m3 (seg_rom ssegs))).
        { intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
          change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
          set (stA := act_st st1 a (act_of st1 a)).
          destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
          assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
          eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; exact AV0|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX stA m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4.
          - unfold stA. apply KINV_act; [exact KI1| exact GMa| exact AV0| apply act_of_nonneg].
          - unfold stA. apply ZINV_act. exact ZI1.
          - unfold stA, act_st. apply LPRE_upd_other; [exact NEa| exact LP1].
          - unfold stA. apply frame_act; [exact FR1'| eapply (LG_frame st st1 a FR1'); left; exact Na].
          - unfold stA. rewrite act_st_rec_other by congruence. exact GN1.
          - unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
          - unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
          - unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
          - unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
          - unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
            change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
            apply (ki_usage _ _ _ KI1). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        assert (NOACT : (an = false \/ active st1 sc = None) ->
                 rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x18d70) fc None m3 (seg_rom ssegs))).
        { intros NA.
          eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
          rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX st1 m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4; try exact KI1; try exact ZI1; try exact LP1; try exact FR1'; try exact GN1.
          - apply DSdata.
          - apply (sbl_regions _ _ SBL1).
          - apply (sbl_shadow _ _ SBL1).
          - apply (sbl_groups _ _ SBL1).
          - intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| exact SC48b]|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); congruence).
      * (* [comment removed for export] *)
        destruct D as (_ & NXg & _ & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx = g) by congruence.
        eapply rimplT_evt.
        { eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - rewrite NX, Enx. reflexivity. }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
      * (* [comment removed for export] *)
        destruct D as (_ & _ & nx' & NX' & NE & x0 & x1 & x2 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx' = nx) by congruence. subst nx'.
        eapply rimplT_evt.
        { eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact NX | exact PV | exact NE | exact MSnx | exact MSpv | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | reflexivity | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - apply NEpv. exact NE.
          - destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
            exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
    + (* [comment removed for export] *)
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as (nx0 & D3 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
      eapply (FGX st m1 junk); [exact KI | exact ZI | exact LP | apply frame_refl | exact NX | reflexivity | reflexivity | reflexivity | reflexivity
                               | | eapply rpres_except_entry; eauto | exact WM | exact MI1 | exact ST1 | exact FR1 | exact MR1 | reflexivity].
      intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
  - destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
    + (* [comment removed for export] *)
      apply Z.eqb_eq in HM.
      apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.
      (* [comment removed for export] *)
      assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono ssegs m m1 ->
        stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
        (active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
        forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
                      x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (k (aor_st stq g i) None) s Q ms2).
      { intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
        assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
        assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); exact ZI).
        assert (KIq : KINV stq LB c).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [exact KI|].
          apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
        assert (FRq : ntf_frame st stq).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
          apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
          cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
        unfold rqpath_post in QP. cbv beta in QP.
        destruct QP as (qa0 & qa2 & qa3 & qa5 & m2 & -> & PE2 & WM2 & MI2 & ST2 & FR2 & MR2).
        pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
        rewrite <- (conc_sbl st stq g SBL).
        eapply rimplT_evt.
        { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
            first [exact MR2 | exact MI2 | reflexivity | exact FR2 | exact ST2 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBL| exact MSL].
          - pose proof (go_li _ _ _ GO). lia.
          - destruct (data_of_fields st stq g (sbl_data _ _ SBL g)) as (_ & _ & -> & _). exact (go_freed _ _ _ GO). }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try exact RP.
        * eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [exact FRq| lia| exact Ha].
        * exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
        * apply ZINV_aor. exact ZIq.
        * apply frame_aor; [exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
        * exact eq_refl.
        * apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
          eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO|].
          eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * exact MR2.
        * reflexivity.
        * reflexivity. }
      destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
      * (* [comment removed for export] *)
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
        { destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; fastfirst (first [ noevar_assumption |congruence | lia | exact HAct])|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - right. exists g. split; [exact HAct| exact MSL].
          - intros NE. exfalso. exact (NE HAct).
          - intros hd Hhd NE. exfalso. apply NE. congruence. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| exact QP].
      * (* [comment removed for export] *)
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
        { intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
        apply rimplT_queue. intros GN GPV.
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; fastfirst (first [ noevar_assumption |congruence | lia])|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as [D3 _]; congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
            exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
          - intros _. split; assumption.
          - intros hd Hhd NE. destruct (kinv_active _ _ _ _ _ KI Hhd) as (_ & Shd & Nhd & _ & _ & pv & Ppv & Spv & Npv).
            split; [exact Shd|]. exists pv. split; [exact Ppv|]. split; [| exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros _; split; assumption| exact QP].
    + (* [comment removed for export] *)
      apply Z.eqb_neq in HM.
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y0 & y2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
      eapply rimplT_evt.
      { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
          first [exact MR1 | exact MI1 | exact MSL | reflexivity | exact FR1 | exact ST1 | exact LO | exact LOLE | idtac].
        - pose proof (go_li _ _ _ GO). lia.
        - exact (go_freed _ _ _ GO). }
      intros ms2 RP. apply KH.
      eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try exact RP.
      * eapply rpres_except_entry; eauto.
      * auto.
      * exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
      * apply ZINV_aor. exact ZI.
      * apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
      * exact eq_refl.
      * eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO| eapply rpres_except_entry; eauto].
      * exact MR1.
      * reflexivity.
      * reflexivity.
Qed.
End NTF.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.F_ntf_C.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_ntf_D OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_E OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_F OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_G OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_ntf_H OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RF_ntf_C.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_D.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_E.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_F.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_G.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_ntf_H.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Definition rntf_q (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (LB : list block) (Zs : list aptr) (lo : Z) (m o : word -> option byte)
    (st' : mstate) (mi : mapinfo) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp) /\ rmrep st' m'
    /\ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m'
    /\ (exists c, KINV st' LB c) /\ ZINV st' Zs /\ ntf_frame st st' /\ ntf_result st' mi a0 a1 /\ oracle_ok o m' st'.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rpres_except_entry st lo (sp : word) m m1 :
  munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m1 -> wmono usegs m m1 -> lo <= bv_unsigned sp - 96 ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m m1.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros MU WM LOLE. apply (rpres_except_of_munch_cov (rfree_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
  cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply rfree_fp_stack. lia.
Qed.

Lemma roracle_ok_pres o m m' st lo (sp : Z) (mw : word -> option byte) :
  oracle_ok o m st -> rmrep st mw -> alloc_ceiling <= lo -> rpres_except (rfree_fp st lo sp) m m' -> oracle_ok o m' st.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros OK MR LO PE rid r q h Hr Hk Hq M8 Hc.
  rewrite (OK rid r q h Hr Hk Hq M8 Hc).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4).
  ceil_facts.
  symmetry. apply (PE (r_base r + q)); [lia|].
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid' & r' & Hr' & Hk' & Hin).
    destruct (N.eq_dec rid' rid) as [->|NE]; [rewrite Hr in Hr'; assert (r' = r) by congruence; subst r'; exact (Hk' Hk)|].
    pose proof (lr_lo_group r Hk). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
  - destruct A as (b & gh & Hb & Hin).
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & SbA & RbB0 & _).
    destruct (WR (fst b) rb Hrb) as (_ & RbAL & _).
    assert (Cm : conc st b mod 16 = 0) by (rewrite Cb; apply base16_mod; assumption).
    Z.div_mod_to_equations. lia.
  - destruct A as (rid' & r' & v & Hr' & Hk' & Hin & HC).
    destruct (N.eq_dec rid' rid) as [->|NE].
    + rewrite Hr in Hr'. assert (r' = r) by congruence. subst r'. replace (r_base r + q - r_base r) with q in HC by lia. rewrite Hc in HC. discriminate.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group r' Hk'). destruct (DJ rid' r' rid r Hr' Hr NE); lia.
Qed.

Lemma rfree_fp_frame st st' lo (sp sp' : Z) a : ntf_frame st st' -> sp' <= sp -> rfree_fp st' lo sp' a -> rfree_fp st lo sp a.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros FR HS H. eapply (rfree_fp_mono st st' lo sp sp' a (nf_regions _ _ FR) (nf_shadow _ _ FR) (nf_groups _ _ FR) HS H).
Qed.

Lemma rfree_fp_same st st' lo (sp : Z) a :
  s_regions st' = s_regions st -> s_shadow st' = s_shadow st -> s_groups st' = s_groups st ->
  rfree_fp st' lo sp a -> rfree_fp st lo sp a.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros ER ES EG H. eapply (rfree_fp_mono st st' lo sp sp a ER ES); [rewrite EG; auto| lia| exact H]. Qed.

(* [comment removed for export] *)
Lemma rfree_fp_lt st mw lo (sp : Z) a : rmrep st mw -> alloc_ceiling <= lo -> lo <= sp -> rfree_fp st lo sp a -> a < sp.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR LO LS H. pose proof MR as (WF & _). pose proof WF as (_ & WR & _ & _ & _).
  ceil_facts.
  destruct H as [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). ceil_facts. lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR rid r Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
Qed.

(* [comment removed for export] *)
Lemma rknown_byte st m (q : aptr) r v :
  rmrep st m -> (s_regions st) !! (fst q) = Some r -> r_kind r = RKGroup -> 0 <= snd q < round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst q)) (snd q) = Known v ->
  bytes_at usegs m (conc st q + 0) [b8 v] /\ 0 <= v < 256.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR Hr Hk Ho Hc. rewrite (conc_region' st q r Hr), Z.add_0_r.
  pose proof MR as (_ & _ & _ & _ & _ & SH). destruct (SH (fst q) r Hr Hk) as [_ HB]. apply HB; auto.
Qed.

(* [comment removed for export] *)
Lemma rimplT_queue {R} o h g st0 (k : mstate -> Malloc.M R) bail s Q ms :
  (m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None -> rimplT o (k (queue_st h g st0)) s Q ms) ->
  rimplT o (queue h g st0 k bail) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H. unfold queue. apply rimplT_guard. intros G1. apply rimplT_guard. intros G2.
  assert (N : m_next (get_meta_rec st0 g) = None) by (destruct (m_next _); [discriminate|reflexivity]).
  assert (P : m_prev (get_meta_rec st0 g) = None) by (destruct (m_prev _); [discriminate|reflexivity]).
  specialize (H N P). unfold queue_st, fm_link, fm_single in H. destruct (get_head st0 h); exact H.
Qed.

Lemma rntf_frame_size junk (s3 s2 s1 s0 ra : word) : cells_size (rntf_frame junk s3 s2 s1 s0 ra) = 96%nat.
Proof using CEILV. pin_using (fun (CEILV : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.

Section NTF.
Variables (gp tp s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.

Lemma rntf_q_intro (Zs : list aptr) (ra sp s0 s1 s2 s3 : word) st stX st' (m mX : word -> option byte) mi a0v a1v ms' :
  rntf_ret_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo stX mX st' a0v a1v ms' ->
  rpres_except (rfree_fp st lo (bv_unsigned sp)) m mX ->
  (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
  (exists c, KINV st' LB c) -> ZINV st' Zs -> ntf_frame st st' -> ntf_result st' mi a0v a1v ->
  oracle_ok o mX stX -> rmrep stX mX -> s_regions st' = s_regions stX -> s_shadow st' = s_shadow stX ->
  rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms'.
Proof using LO. pin_using (fun (LO : unit) => tt). ceil_facts. msec_facts.
  intros RP PE FP KI ZI FR RES OOK MRX ER ES.
  destruct RP as (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & -> & PE' & WM' & MI' & ST' & MR').
  unfold rntf_q. do 16 eexists. split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|]. split; [exact MR'|].
  split. { eapply rpres_except_trans; [exact PE|]. eapply rpres_except_mono; [exact PE'|]. exact FP. }
  split; [exact KI|]. split; [exact ZI|]. split; [exact FR|]. split; [exact RES|].
  eapply oracle_ok_frame; [| exact ER | exact ES]. eapply roracle_ok_pres; [exact OOK | exact MRX | exact LO | exact PE'].
Qed.

Theorem rntf_implT : forall (fuel : nat) (R : Type) (k : mstate -> mapinfo -> Malloc.M R) (bail : Malloc.M R)
    (s : PState) (Q : R -> PState -> machine_state -> Prop)
    (ra sp s0 s1 s2 s3 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte)
    (st : mstate) (g p : aptr) (i c : Z) (Zs : list aptr),
  KINV st LB c -> LPRE st LB c g p i -> ZINV st Zs ->
  rmrep st m -> mem_inv usegs m -> oracle_ok o m st ->
  stk usegs m lo (bv_unsigned sp) -> lo + 96 * Z.of_nat fuel <= bv_unsigned sp ->
  (forall st' mi ms', rntf_q ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB Zs lo m o st' mi ms' -> rimplT o (k st' mi) s Q ms') ->
  rimplT o (nontrivial_free dec_hdr fuel st g i k bail) s Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st g)) (Z_to_bv 64 i) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1936c) fc None m (seg_rom usegs)).
Proof using LO. pin_using (fun (LO : unit) => tt). ceil_facts. msec_facts.
  induction fuel as [|f IH]; intros until Zs; intros KI LP ZI MR MI OOK ST DEPTH KH.
  { cbn [nontrivial_free]. apply rimplT_undef. }
  rewrite ntf_unfold. cbv zeta.
  pose proof (lpre_gmeta _ _ _ _ _ _ KI LP) as GO. pose proof (gmeta_mw _ _ _ GO) as MW.
  pose proof (lp_hosts _ _ _ _ _ _ LP) as HOSTS. pose proof (lp_i _ _ _ _ _ _ LP) as HI.
  pose proof (go_slot _ _ _ GO) as MSL.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  assert (LOLE : lo <= bv_unsigned sp - 96) by lia.
  set (ms0 := MS _ _ _ _ _ _ _).
  (* [comment removed for export] *)
  assert (ENTRY : entry_hyps st g i ->
    evt usegs (rentry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m) ms0).
  { intros EH. subst ms0. eapply rntf_entry; eauto. }
  (* [comment removed for export] *)
  assert (EH0 : forall (G50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48)
                       (G51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48)
                       (G1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
                             m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g),
             entry_hyps st g i).
  { intros. constructor; auto.
    - exact (go_avail _ _ _ GO).
    - exact (go_freed _ _ _ GO).
    - pose proof (go_sc _ _ _ GO). lia.
    - intros nx NX. exact (proj1 (kinv_next _ _ _ _ _ KI NX)).
    - intros h HA. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI HA))).
    - split; [intros j; apply (ki_cx _ _ _ KI)|]. intros _. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP). }
  destruct (ntf_cond st g i) eqn:HC.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (FG2 : forall stX m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 : word) ms2,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 ->
      rfg_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 F fc lo stX m2 (fg_usage_st stX g) g
              (m_sizeclass (get_meta_rec stX g)) (meta_word (get_meta_rec stX g)) (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
      (forall a, rfree_fp stX lo (bv_unsigned sp) a -> rfree_fp st lo (bv_unsigned sp) a) ->
      wmono usegs m m2 -> oracle_ok o m2 stX ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) -> (exists mw, rmrep stX mw) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms2).
    { intros stX m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x9 x10 ms2 KIX ZIX LPX FRX GNX PRE FGP FPX WM2 OOK2 DATX [mw MRW].
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX. pose proof (gmeta_mw _ _ _ GOX) as MWX.
      pose proof (lp_hosts _ _ _ _ _ _ LPX) as HOSTSX.
      unfold rfg_post in FGP. destruct FGP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
      set (stU := fg_usage_st stX g) in *.
      assert (RU : get_meta_rec stU g = get_meta_rec stX g) by (unfold stU; apply fg_usage_rec).
      assert (CU : forall q, conc stU q = conc stX q) by (intros; unfold stU; apply conc_fg_usage).
      rewrite free_group_unfold. cbv zeta. fold stU. rewrite (go_mem _ _ _ GOX).
      rewrite <- RU. fold (grp_del stU g p). set (stG := grp_del stU g p).
      (* [comment removed for export] *)
      assert (ALLFREE : forall j, 0 <= j <= m_last_idx (get_meta_rec stX g) -> j <> i -> slot_free (get_meta_rec stX g) j).
      { destruct (data_of_fields _ _ g DATX) as (_ & EA & EF & EL & _).
        unfold slot_free. rewrite EA, EF, EL. intros j Hj NE.
        unfold ntf_cond in HC. apply andb_true_iff in HC. destruct HC as [HALL _]. apply Z.eqb_eq in HALL.
        pose proof (lp_nonfree _ _ _ _ _ _ LP) as NF. unfold slot_free in NF.
        apply (all_free_of_mask (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) i (m_last_idx (get_meta_rec st g)));
          try lia; try exact HALL.
        - exact (go_freed _ _ _ GO). - exact (go_avail _ _ _ GO). - pose proof (go_li _ _ _ GO); lia.
        - destruct (Z.testbit (m_freed (get_meta_rec st g)) i); tauto.
        - destruct (Z.testbit (m_avail (get_meta_rec st g)) i); tauto. }
      assert (KIU : KINV stU LB (m_sizeclass (get_meta_rec stX g) + 1)) by (unfold stU; eapply KINV_fg_usage; eauto).
      assert (LPU : LPRE stU LB c g p i) by (unfold stU; apply LPRE_fg_usage; exact LPX).
      assert (GD := KINV_grp_del stU LB _ g p KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact GNX)).
      rewrite RU in GD. specialize (GD ltac:(intros j Hj; destruct (Z.eq_dec j i) as [->|NE];
          [ split; [rewrite <- RU; exact (lp_nogroup _ _ _ _ _ _ LPU) | rewrite <- RU; exact (lp_noblock _ _ _ _ _ _ LPU)]
          | pose proof (free_slot_clear stU LB _ g p j KIU (lp_hosts _ _ _ _ _ _ LPU) ltac:(rewrite RU; exact Hj) ltac:(rewrite RU; apply ALLFREE; [exact Hj| exact NE])) as FC;
            rewrite RU in FC; exact FC ])).
      fold stG in GD. destruct GD as (KIG & NGM & NSL).
      assert (MRG : rmrep stG m3) by (unfold stG; apply rmrep_grp_del_eq; apply rmrep_del_group; exact MR3).
      assert (FRG : ntf_frame st stG) by (unfold stG, stU; apply frame_grp_del; apply frame_fg_usage; exact FRX).
      assert (MSG : meta_slot stG g) by (unfold stG, stU; unfold meta_slot; rewrite grp_del_areas, fg_usage_areas; exact (go_slot _ _ _ GOX)).
      (* [comment removed for export] *)
      pose proof MWX as MWU. rewrite <- RU in MWU. pose proof GNX as GNU. rewrite <- RU in GNU.
      pose proof (go_mem _ _ _ GOX) as MEMU. rewrite <- RU in MEMU.
      replace (conc stX g) with (conc stG g) by (unfold stG; rewrite conc_grp_del; apply CU).
      change (get_meta_rec stU g) with (get_meta_rec stG g) in *.
      destruct (negb (m_maplen (get_meta_rec stG g) =? 0)) eqn:HML.
      - (* [comment removed for export] *)
        assert (MLNZ : m_maplen (get_meta_rec stG g) <> 0) by (intros E; rewrite E in HML; discriminate).
        rewrite free_meta_eq.
        eapply rimplT_evt.
        { eapply (rntf_top ra sp gp tp _ _ _ s0 _ ra _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 junk ra s0 s1 s2 s3 stG stG g p _ lo);
            first [exact MRG | exact MI3 | exact MSG | exact MWU | exact MEMU | exact MLNZ | exact FR3 | exact ST3 | exact LO | exact LOLE | reflexivity
                  | apply munch_refl | apply wmono_refl | idtac].
          - pose proof (ki_cx _ _ _ KIG) as (SQ & _). exact SQ.
          - intros hd Hhd. eapply (kinv_fm_facts_raw stG LB _ g KIG); [exact GNU| exact Hhd]. }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stG _ m m3); try exact RP.
        + destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
            (eapply rpres_except_mono; [exact PE3| exact FPX]).
        + intros a Ha. apply FPX. eapply (rfree_fp_frame stX stG lo (bv_unsigned sp) (bv_unsigned sp)); [| lia | exact Ha].
          unfold stG, stU. apply frame_grp_del. apply frame_fg_usage. apply frame_refl.
        + eexists. apply KINV_fm; [apply KINV_seq; exact KIG| | | |].
          * unfold meta_slot. replace (s_areas (record_seq _ (step_seq stG))) with (s_areas stG); [exact MSG|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros [b Hb]. apply NGM. exists b. unfold hosts in *.
            replace (s_groups (record_seq _ (step_seq stG))) with (s_groups stG) in Hb; [exact Hb|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * replace (get_meta_rec (record_seq _ (step_seq stG)) g) with (get_meta_rec stG g); [exact GNU|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
          * intros sx j. replace (s_slots (record_seq _ (step_seq stG))) with (s_slots stG); [apply NSL|].
            unfold record_seq, step_seq. destruct (c_seq _ =? 255); destruct (sc_in_seq_range _); reflexivity.
        + apply ZINV_fm. apply ZINV_seq. unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + (* [comment removed for export] *)
          pose proof (KINV_seq _ _ _ (m_sizeclass (get_meta_rec stG g)) KIG) as KIS.
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & SR4 & SR5 & SR6 & SR7 & SR8).
          set (stS := record_seq _ (step_seq stG)) in *.
          assert (GNS : m_next (get_meta_rec stS g) = None) by (unfold get_meta_rec; rewrite SR6; exact GNU).
          unfold fm_st. apply frame_queue.
          * apply frame_put_meta; [apply frame_seq; exact FRG| right; exact (hosts_is_gm _ _ _ HOSTS)].
          * apply links_put_meta0; [exact (ki_links _ _ _ KIS)| exact GNS].
          * cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 stS))) with (c_free_meta_head (ctx stS)).
            intros hd Hhd. destruct (kinv_free_head stS LB _ hd KIS Hhd) as (_ & NX' & _).
            rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; exact (NX' GNS)| exact NX'].
          * right; exact (hosts_is_gm _ _ _ HOSTS).
        + (* [comment removed for export] *)
          pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & SR2 & SR3 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & FS2 & FS3 & _).
          destruct (go_region _ _ _ GOX) as (r & Hr & Kr & _ & _ & _ & TOP). rewrite <- RU in TOP.
          change (get_meta_rec stU g) with (get_meta_rec stG g) in TOP. destruct (TOP MLNZ) as [SND LEN].
          pose proof (go_maplen _ _ _ GOX) as MLR. rewrite <- RU in MLR. change (get_meta_rec stU g) with (get_meta_rec stG g) in MLR.
          unfold ntf_result. split; [| split; [reflexivity| split; [lia| split; [exact SND| split]]]].
          * unfold wz. f_equal. unfold conc, get_region. rewrite FS1, SR1. reflexivity.
          * exists r. rewrite FS1, SR1. unfold stG, stU. rewrite grp_del_regions, fg_usage_regions. auto.
          * intros b' gh Hb' E. rewrite FS3, SR3 in Hb'. unfold stG in Hb'. rewrite grp_del_groups in Hb'.
            apply lookup_delete_Some in Hb'. destruct Hb' as [NE Hb']. unfold stU in Hb'. rewrite fg_usage_groups in Hb'.
            apply NE. symmetry. eapply (top_region_clear stX LB c g p i KIX LPX); [rewrite <- RU; exact MLNZ | exact ALLFREE | exact Hb' | exact E].
        + eapply (oracle_ok_frame o m3 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m3 stX lo (bv_unsigned sp)); [exact OOK2 | exact MRW | exact LO | exact PE3].
        + exact MRG.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (SR1 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (FS1 & _). rewrite FS1, SR1. reflexivity.
        + pose proof (seq_shape stG (m_sizeclass (get_meta_rec stG g))) as (_ & SR2 & _).
          pose proof (fm_shape (record_seq (m_sizeclass (get_meta_rec stG g)) (step_seq stG)) g) as (_ & FS2 & _). rewrite FS2, SR2. reflexivity.
      - (* [comment removed for export] *)
        assert (MLZ : m_maplen (get_meta_rec stG g) = 0) by (destruct (Z.eqb_spec (m_maplen (get_meta_rec stG g)) 0); [assumption| discriminate]).
        (* [comment removed for export] *)
        pose proof (go_nest _ _ _ GOX) as NEST. rewrite <- RU in NEST. change (get_meta_rec stU g) with (get_meta_rec stG g) in NEST.
        destruct (NEST MLZ) as (g1 & i1 & b1 & SL1 & HB1 & FB1 & PSS & I1 & NF1 & LT1 & v3 & lo8 & hi8 & K3 & V31 & K2 & K1 & OFF).
        clear NEST.
        pose proof (ki_gmetas _ _ _ KIX b1 g1 HB1) as GO1.
        destruct (go_region _ _ _ GOX) as (r & Hr & Kr & SP0 & SP16 & SPAN & _).
        destruct (go_region _ _ _ GO1) as (r1 & Hr1 & _ & SB0 & SB16 & SPAN1 & _).
        rewrite FB1, Hr in Hr1. assert (r1 = r) by congruence. subst r1.
        assert (SNDP : snd p = sstart_of (get_meta_rec stX g1) i1) by (rewrite PSS, slot_start'_eq; reflexivity).
        assert (B1LT : snd b1 + 16 <= snd p).
        { rewrite SNDP. unfold sstart_of. rewrite (go_mem _ _ _ GO1). cbn [default id fst snd].
          pose proof (go_stride _ _ _ GO1) as [S16 _].
          assert (0 <= get_stride (get_meta_rec stX g1) * i1) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia). unfold UNIT in *. lia. }
        assert (NEb1 : b1 <> p) by (intros E; rewrite E in B1LT; lia).
        assert (HB1U : hosts stU b1 g1) by (unfold hosts in *; unfold stU; rewrite fg_usage_groups; exact HB1).
        assert (HB1G : hosts stG b1 g1) by (apply (proj2 (hosts_grp_del stU g p b1 g1)); split; [exact NEb1| exact HB1U]).
        (* [comment removed for export] *)
        pose proof (ki_h0 _ _ _ KIX g1 b1 i1 HB1 I1) as K4. rewrite <- SNDP, FB1 in K4.
        assert (PR : 0 <= snd p - 4 /\ snd p < round_up_pg (r_len r)).
        { split; [lia|]. pose proof (go_li _ _ _ GOX) as LIX. pose proof (go_stride _ _ _ GOX) as [S16 _].
          rewrite <- RU in LIX, S16. change (get_meta_rec stU g) with (get_meta_rec stG g) in LIX, S16.
          unfold sstart_of in SPAN. rewrite <- RU in SPAN. change (get_meta_rec stU g) with (get_meta_rec stG g) in SPAN.
          rewrite MEMU in SPAN. cbn [default id snd] in SPAN.
          assert (0 <= get_stride (get_meta_rec stG g) * (m_last_idx (get_meta_rec stG g) + 1)) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
          unfold UNIT, IB in *. lia. }
        destruct (rknown_byte stX mw (fst p, snd p - 4) r 0 MRW Hr Kr ltac:(cbn; lia) K4) as [_ _].
        (* [comment removed for export] *)
        unfold dec_hdr, get_meta. apply rimplT_guard. intros P16.
        assert (SHG : forall c', get_shadow stG c' = get_shadow stX c').
        { intros c'. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow. reflexivity. }
        apply rimplT_rd16; [peek_known_sh SHG| peek_known_sh SHG|]. apply rimplT_rd8; [peek_known_sh SHG|]. cbv zeta. apply rimplT_rd8; [peek_known_sh SHG|].
        assert (ESH : forall q, rdv pans_mem o stG q = rdv pans_mem o stX q).
        { intros q. unfold rdv. unfold get_shadow. unfold stG, stU. rewrite grp_del_shadow, fg_usage_shadow.
          unfold conc, get_region. rewrite grp_del_regions, fg_usage_regions. reflexivity. }
        rewrite !ESH.
        rewrite (rdv_known o stX (aadd p (-4)) 0) by (cbn [aadd fst snd]; replace (snd p + -4) with (snd p - 4) by lia; exact K4).
        rewrite (rdv_known o stX (aadd p (-3)) v3) by (cbn [aadd fst snd]; replace (snd p + -3) with (snd p - 3) by lia; exact K3).
        rewrite (rdv_known o stX (aadd p (-2)) lo8) by (cbn [aadd fst snd]; replace (snd p + -2) with (snd p - 2) by lia; exact K2).
        rewrite (rdv_known o stX (aadd (aadd p (-2)) 1) hi8) by (cbn [aadd fst snd]; replace (snd p + -2 + 1) with (snd p - 1) by lia; exact K1).
        cbn [Z.eqb negb].
        set (off16 := lo8 + 256 * hi8).
        assert (EB : aadd p (- (UNIT * off16) - UNIT) = b1).
        { unfold aadd, UNIT, off16. rewrite <- FB1. apply injective_projections; cbn; [reflexivity| lia]. }
        rewrite EB. unfold get_group.
        replace (s_groups stG !! b1) with (s_groups stX !! b1).
        2:{ unfold stG, stU. rewrite grp_del_groups, lookup_delete_ne, fg_usage_groups by congruence. reflexivity. }
        destruct HB1 as [ai1 Hgh1]. rewrite Hgh1. cbn [g_meta].
        apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
        apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
        (* [comment removed for export] *)
        assert (EU1 : get_meta_rec stU g1 = get_meta_rec stX g1) by (unfold stU; apply fg_usage_rec).
        change (get_meta_rec stG g1) with (get_meta_rec stU g1) in G11, G12, G13, G14, G15, G16, G17 |- *.
        rewrite ?EU1 in G11. rewrite ?EU1 in G12. rewrite ?EU1 in G13. rewrite ?EU1 in G14. rewrite ?EU1 in G16. rewrite ?EU1 in G17. rewrite ?EU1.
        destruct (s_areas stG !! area_of g1) as [ar1|] eqn:AR1; [|discriminate].
        apply Z.eqb_eq in G15. change (c_secret (ctx stG)) with (c_secret (ctx stU)) in G15.
        apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
        (* [comment removed for export] *)
        assert (ERU : s_regions stU = s_regions stX) by (unfold stU; apply fg_usage_regions).
        assert (ESU : s_shadow stU = s_shadow stX) by (unfold stU; apply fg_usage_shadow).
        assert (KB : forall k v, 1 <= k <= 4 -> cell_read (get_shadow stX (fst p)) (snd p - k) = Known v ->
                   bytes_at usegs m3 (conc stU p - k) [b8 v] /\ 0 <= v < 256).
        { intros kk v Hk Hc. destruct (rknown_byte stU m3 (fst p, snd p - kk) r v MR3 ltac:(cbn; rewrite ERU; exact Hr) Kr ltac:(cbn; lia)
                   ltac:(cbn; unfold get_shadow; rewrite ESU; exact Hc)) as [B V].
          cbn [fst snd] in B. rewrite (conc_region' stU (fst p, snd p - kk) r) in B by (cbn; rewrite ERU; exact Hr). cbn [snd] in B.
          rewrite (conc_region' stU p r) by (rewrite ERU; exact Hr). split; [| exact V].
          replace (r_base r + snd p - kk) with (r_base r + (snd p - kk) + 0) by lia. exact B. }
        destruct (KB 4 0 ltac:(lia) K4) as [Y4 _]. destruct (KB 3 v3 ltac:(lia) K3) as [Y3 R3].
        destruct (KB 2 lo8 ltac:(lia) K2) as [Y2 R2]. destruct (KB 1 hi8 ltac:(lia) K1) as [Y1 R1]. clear KB.
        assert (HDR : bytes_at usegs m3 (conc stU p - 4) [b8 0; b8 v3; b8 lo8; b8 hi8]).
        { change [b8 0; b8 v3; b8 lo8; b8 hi8] with ([b8 0] ++ ([b8 v3] ++ ([b8 lo8] ++ [b8 hi8]))).
          apply bytes_at_app. split; [exact Y4|]. apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1) with (conc stU p - 3) by lia; exact Y3|].
          apply bytes_at_app. split; [cbn; replace (conc stU p - 4 + 1 + 1) with (conc stU p - 2) by lia; exact Y2|].
          cbn. replace (conc stU p - 4 + 1 + 1 + 1) with (conc stU p - 1) by lia. exact Y1. }
        (* [comment removed for export] *)
        destruct HOSTSX as [aig Hghp].
        eapply rimplT_evt.
        { eapply (rntf_nest_call ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stU g p b1 g1 (mkGhdr (Some g) aig) (mkGhdr (Some g1) ai1) ar1 v3 lo8 hi8 off16 lo).
          all: first [exact MR3 | exact MI3 | exact MWU | exact MLZ | exact MEMU | exact HDR | exact FR3 | exact ST3 | exact LO | exact LOLE
                     | exact R3 | exact R2 | exact R1 | exact AR1 | exact G15 | apply rntf_frame_size | idtac].
          all: try reflexivity.
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GO1)).
          all: rewrite ?EU1.
          all: try exact (go_mem _ _ _ GO1); try exact (go_avail _ _ _ GO1); try exact (go_freed _ _ _ GO1);
               try exact G12; try exact G13; try exact G14; try exact (proj2 (proj2 (proj2 (ki_cx _ _ _ KIU)))).
          all: try (pose proof (go_li _ _ _ GO1); pose proof (go_freeable _ _ _ GO1); pose proof (go_sc _ _ _ GO1); pose proof (go_maplen _ _ _ GO1); lia).
          all: try (unfold meta_slot; unfold stU; rewrite fg_usage_areas; exact (go_slot _ _ _ GOX)).
          all: try (unfold stU; rewrite fg_usage_groups; first [exact Hghp | exact Hgh1]).
          all: try (symmetry; exact EB).
          all: match goal with
               | |- forall _, _ <= _ < 12 -> _ => intros oo Ho; unfold get_shadow; rewrite ESU; exact (ki_unk _ _ _ KIX p _ oo Hghp Ho)
               | |- _ < 48 -> _ => intros Hsc; apply Z.ltb_lt in Hsc; rewrite Hsc in G16; apply andb_true_iff in G16; destruct G16 as [G16a G16b];
                                   apply Z.leb_le in G16a; apply Z.ltb_lt in G16b; fold off16 in G16a, G16b; lia
               | |- _ <> 0 -> _ => intros Hml; destruct (Z.eqb_spec (m_maplen (get_meta_rec stX g1)) 0); [lia|]; cbn [negb] in G17; apply Z.leb_le in G17;
                                   fold off16 in G17; unfold UNIT in G17;
                                   replace (m_maplen (get_meta_rec stX g1) * 4096) with (m_maplen (get_meta_rec stX g1) * 256 * 16) in G17 by lia;
                                   rewrite Z.div_mul in G17 by lia; lia
               | |- ?G => idtac "NCGOAL" G; fail
               end. }
        intros ms3 NC. unfold rnest_call_post in NC.
        destruct NC as (z0 & z1 & z2 & w2 & w3 & w4 & w5 & w6 & w7 & z3 & z4 & z5 & z6 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
        fold stG in MR4.
        (* [comment removed for export] *)
        pose proof (bv_unsigned_in_range _ sp) as SPR'.
        assert (SPU : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp - 96) by (ceil_facts; rewrite unsigned_lit; lia).
        rewrite V31. replace (conc stU g1) with (conc stG g1) by reflexivity.
        eapply (IH R _ bail s Q (Z_to_bv 64 0x195f4) (Z_to_bv 64 (bv_unsigned sp + -96)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m4 stG g1 b1 i1 (m_sizeclass (get_meta_rec stX g) + 1) (g :: Zs)).
        + exact KIG.
        + constructor.
          * exact HB1G.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact I1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1. exact NF1.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS. unfold stG. rewrite grp_del_groups. apply lookup_delete_eq.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1, <- PSS.
            apply Forall_forall. intros blk Hblk E. pose proof (proj1 (Forall_forall _ _) (ki_blks _ _ _ KIX) blk Hblk) as BK.
            pose proof (bk_nogroup _ _ BK) as NG. rewrite E, Hghp in NG. discriminate.
          * change (get_meta_rec stG g1) with (get_meta_rec stU g1). rewrite EU1.
            pose proof LT1 as LT1'. first [rewrite RU in LT1' | change (get_meta_rec stG g) with (get_meta_rec stU g) in LT1'; rewrite RU in LT1']. lia.
        + unfold stG. apply ZINV_grp_del; [unfold stU; apply ZINV_fg_usage; exact ZIX| exact (lp_hosts _ _ _ _ _ _ LPU)].
        + exact MR4.
        + exact MI4.
        + apply (oracle_ok_frame o m4 stX stG); [| unfold stG, stU; rewrite grp_del_regions, fg_usage_regions; reflexivity | unfold stG, stU; rewrite grp_del_shadow, fg_usage_shadow; reflexivity].
          eapply (roracle_ok_pres o m2 m4 stX lo (bv_unsigned sp) mw); [exact OOK2 | exact MRW | exact LO |].
          eapply rpres_except_trans; [exact PE3|]. eapply rpres_except_mono; [exact PE4|].
          intros a Ha. eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha].
        + rewrite SPU. exact ST4.
        + rewrite SPU. lia.
        + (* [comment removed for export] *)
          intros st3 mi ms5 NQ. rewrite free_meta_eq.
          unfold rntf_q in NQ. rewrite SPU in NQ.
          destruct NQ as (u0 & u1 & u2 & ra0' & ra1' & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m5 & -> & MI5 & ST5 & MR5 & PE5 & [c3 KI3] & ZI3 & FR35 & RES5 & OOK5).
          replace (ret_pc (Z_to_bv 64 0x195f4)) with (Z_to_bv 64 0x195f4) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
          assert (RG3 : get_meta_rec st3 g = get_meta_rec stG g).
          { apply (nf_metas _ _ FR35). intros [L|L]; [exact (L GNU)| exact (NGM L)]. }
          assert (NGM3 : ~ is_gm st3 g).
          { intros [b [ai Hb]]. apply NGM. exists b, ai. apply (nf_groups _ _ FR35). exact Hb. }
          eapply rimplT_evt.
          { eapply (rntf_nest_ret sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m5 junk ra s0 s1 s2 s3 stU st3 g lo);
              first [exact MR5 | exact MI5 | exact LO | exact LOLE | reflexivity | idtac].
            - unfold meta_slot. rewrite (nf_areas _ _ FR35). exact MSG.
            - intros hd Hhd. eapply (kinv_fm_facts_raw st3 LB c3 g KI3); [rewrite RG3; exact GNU| exact Hhd].
            - unfold conc, get_region. rewrite (nf_regions _ _ FR35). reflexivity.
            - eapply rpres_except_rw_cells; [exact PE5 | exact FR4 |].
              intros a Ha Hfp. pose proof (rfree_fp_lt stG m4 lo (bv_unsigned sp - 96) a MR4 LO ltac:(lia) Hfp). lia.
            - exact ST5. }
          intros ms6 RP. apply KH.
          pose proof (frame_trans _ _ _ FRG FR35) as FR03.
          pose proof (fm_shape st3 g) as (FS1 & FS2 & FS3 & FS4 & FS5 & FS6).
          eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st3 _ m m5); try exact RP.
          * destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto|]|eapply rpres_except_trans; [exact PE0|]];
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE3| exact FPX]|]);
              (eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE4| intros a Ha; apply FPX; eapply (rfree_fp_same stX stU); [exact ERU | exact ESU | unfold stU; apply fg_usage_groups | exact Ha]]|]);
              (eapply rpres_except_mono; [exact PE5| intros a Ha; eapply (rfree_fp_frame st stG lo (bv_unsigned sp) (bv_unsigned sp - 96)); [exact FRG| lia| exact Ha]]).
          * intros a Ha. eapply (rfree_fp_frame st st3 lo (bv_unsigned sp) (bv_unsigned sp)); [exact FR03| lia| exact Ha].
          * exists c3. apply KINV_fm; [exact KI3| unfold meta_slot; rewrite (nf_areas _ _ FR35); exact MSG| exact NGM3| rewrite RG3; exact GNU|].
            intros sx j Hs. apply (NSL sx j). apply (nf_slots _ _ FR35). exact Hs.
          * apply ZINV_fm. exact ZI3.
          * unfold fm_st. apply frame_queue.
            -- apply frame_put_meta; [exact FR03| right; exact (hosts_is_gm _ _ _ HOSTS)].
            -- apply links_put_meta0; [exact (ki_links _ _ _ KI3)| rewrite RG3; exact GNU].
            -- cbn [get_head]. change (c_free_meta_head (ctx (put_meta g meta0 st3))) with (c_free_meta_head (ctx st3)).
               intros hd Hhd. destruct (kinv_free_head st3 LB _ hd KI3 Hhd) as (_ & NX' & _).
               rewrite rec_put. destruct (aptr_eqb_spec' hd g); [subst; exfalso; apply NX'; rewrite RG3; exact GNU| exact NX'].
            -- right; exact (hosts_is_gm _ _ _ HOSTS).
          * destruct mi as [[bb len]|]; [| exact RES5].
            destruct RES5 as (A0 & A1 & LEN & SND & (rr & Hrr & Krr & Lrr) & NOG).
            unfold ntf_result. split; [rewrite A0; unfold wz; f_equal; unfold conc, get_region; rewrite FS1; reflexivity|].
            split; [exact A1|]. split; [exact LEN|]. split; [exact SND|]. split; [exists rr; rewrite FS1; auto|].
            intros b' gh Hb'. rewrite FS3 in Hb'. exact (NOG b' gh Hb').
          * exact OOK5.
          * exact MR5.
          * exact FS1.
          * exact FS2. }
    (* [comment removed for export] *)
    assert (FGX : forall stX m4 junk (z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 : word) ms4,
      KINV stX LB c -> ZINV stX Zs -> LPRE stX LB c g p i -> ntf_frame st stX -> m_next (get_meta_rec stX g) = None ->
      data_of (get_meta_rec stX g) = data_of (get_meta_rec st g) ->
      s_regions stX = s_regions st -> s_shadow stX = s_shadow st -> s_groups stX = s_groups st ->
      (m_sizeclass (get_meta_rec stX g) < 48 -> 0 <= usage stX (m_sizeclass (get_meta_rec stX g)) < 2^64) ->
      rpres_except (rfree_fp st lo (bv_unsigned sp)) m m4 -> wmono usegs m m4 -> mem_inv usegs m4 ->
      stk usegs m4 lo (bv_unsigned sp + -96) -> rw_cells usegs m4 (bv_unsigned sp + -96) (rntf_frame junk s3 s2 s1 s0 ra) -> rmrep stX m4 ->
      ms4 = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp z0 z1 z2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) w1 w2 w3 w4 w5 w6 w7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 z3 z4 z5 z6)
               F (Z_to_bv 64 0x19594) fc None m4 (seg_rom usegs) ->
      rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) stX g k bail) s Q ms4).
    { intros stX m4 junk z0 z1 z2 w1 w2 w3 w4 w5 w6 w7 z3 z4 z5 z6 ms4 KIX ZIX LPX FRX GNX DATX ERX ESX EGX USX PE4 WM4 MI4 ST4 FR4 MR4 ->.
      pose proof (lpre_gmeta _ _ _ _ _ _ KIX LPX) as GOX.
      assert (CX : conc st g = conc stX g) by (unfold conc, get_region; rewrite ERX; reflexivity). rewrite CX.
      eapply rimplT_evt.
      { eapply (rntf_fg ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m4 _ stX g lo);
          first [exact MR4 | exact MI4 | exact (go_slot _ _ _ GOX) | exact (gmeta_mw _ _ _ GOX) | exact USX | exact FR4 | apply rntf_frame_size | exact ST4 | exact LO | exact LOLE]. }
      intros ms5 FGP.
      eapply (FG2 stX m4 junk); [exact KIX | exact ZIX | exact LPX | exact FRX | exact GNX | right; exact PE4 | exact FGP | | exact WM4 | | exact DATX | exists m4; exact MR4].
      - intros a Ha. eapply (rfree_fp_same st stX); eauto.
      - apply (oracle_ok_frame o m4 st stX); [| exact ERX | exact ESX].
        eapply (roracle_ok_pres o m m4 st lo (bv_unsigned sp) m); [exact OOK | exact MR | exact LO | exact PE4]. }
    destruct (m_next (get_meta_rec st g)) as [nx|] eqn:NX.
    + (* [comment removed for export] *)
      apply rimplT_guard. intros SC48b. apply Z.ltb_lt in SC48b. cbv zeta.
      set (sc := m_sizeclass (get_meta_rec st g)) in *.
      set (an := optr_eqb (active st sc) (Some g)).
      set (stm := deq_mid (LActive sc) g st).
      set (st1 := dequeue (LActive sc) g st).
      assert (E1 : st1 = upd_meta g clr_links stm) by (unfold st1, stm; apply dequeue_mid).
      pose proof (deq_mid_shape st (LActive sc) g) as SBLm. fold stm in SBLm.
      pose proof (sbl_dequeue st (LActive sc) g) as SBL1. fold st1 in SBL1.
      assert (KI1 : KINV st1 LB c) by (unfold st1; eapply (KINV_dequeue st LB c g p sc nx); eauto).
      assert (ZI1 : ZINV st1 Zs) by (unfold st1; apply ZINV_dequeue; exact ZI).
      assert (LP1 : LPRE st1 LB c g p i) by (eapply LPRE_sbl; [exact SBL1| exact LP]).
      assert (FR1' : ntf_frame st st1).
      { unfold st1. apply frame_dequeue; [apply frame_refl| exact (ki_links _ _ _ KI)| right; exact (hosts_is_gm _ _ _ HOSTS)]. }
      destruct (kinv_next _ _ _ _ _ KI NX) as (MSnx & Pnx & Nnx & pv & PV & MSpv & Npv & NEpv).
      pose proof (dequeue_shape st g sc nx pv NX PV) as DS. cbv zeta in DS. fold st1 in DS.
      destruct DS as (DSdata & GN1 & GP1 & _).
      (* [comment removed for export] *)
      assert (DQ2 : forall m2 junk (x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 : word) ms2,
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m2 \/ rpres_except (rfree_fp st lo (bv_unsigned sp)) m m2 -> wmono usegs m m2 ->
        rat9c_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x0 x1 x2 (pw st (active st sc)) x5 x6 x7 x3 x4 x8 x9 F fc lo st m2 stm g sc
                   (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (match an, active st1 sc with
                 | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail
                 | _, _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail
                 end) s Q ms2).
      { intros m2 junk x0 x1 x2 x5 x6 x7 x3 x4 x8 x9 ms2 PRE WM2 AP.
        unfold rat9c_post in AP. destruct AP as (y3 & y4 & m3 & -> & PE3 & WM3 & MI3 & ST3 & FR3 & MR3).
        assert (PE03 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
        { destruct PRE as [MU0|PE0]; [eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE3]| eapply rpres_except_trans; [exact PE0| exact PE3]]. }
        (* [comment removed for export] *)
        assert (HA3 : if an then bv_unsigned (pw st (active st sc)) = conc stm g else bv_unsigned (pw st (active st sc)) <> conc stm g).
        { pose proof (rmeta_slot_bounds st m g MR MSL) as (B0 & B1 & _). ceil_facts.
          rewrite (conc_sbl _ _ g SBLm). subst an. destruct (active st sc) as [h|] eqn:Hh; cbn [optr_eqb].
          - destruct (aptr_eqb_spec' h g); [subst; unfold pw, wz; cbn [oconc]; rewrite unsigned_lit by lia; reflexivity|].
            pose proof (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))) as MSh. pose proof (rmeta_slot_bounds st m h MR MSh) as (C0 & C1 & _). ceil_facts.
            unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. intros E. apply n. apply (rconc_meta_inj st m g h MR MSL MSh). exact E.
          - unfold pw, wz; cbn [oconc]. rewrite unsigned_lit by lia. lia. }
        assert (PDQ : forall (avz : an = true -> forall a, active st1 sc = Some a -> m_avail (get_meta_rec st1 a) = 0),
          evt usegs (rat00_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 x1 x2 x3 x4 x8 x9 F fc lo stm m3 (pd_st an st1 sc) g (rntf_frame junk s3 s2 s1 s0 ra))
            (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x19530) fc None m3 (seg_rom usegs))).
        { intros avz. rewrite <- (conc_sbl _ _ g SBLm). rewrite E1.
          eapply (rntf_postdeq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m3 _ stm g sc lo an);
            first [exact MR3 | exact MI3 | exact HA3 | exact FR3 | apply rntf_frame_size | exact ST3 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBLm| exact MSL].
          - pose proof (go_sc _ _ _ GO). subst sc. lia.
          - rewrite <- E1. intros AN a A1. specialize (avz AN a A1).
            destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
            destruct GMa as [ba Hba]. pose proof (ki_gmetas _ _ _ KI1 ba a Hba) as GOa.
            destruct Hba as [ai Hgh]. pose proof (ki_grps _ _ _ KI1 ba _ Hgh) as (g' & Eg' & AI). cbn in Eg', AI. inversion Eg'; subst g'.
            split; [exact MSa|]. split; [intros ->; exact (Na GN1)|]. split; [exact avz|]. split; [exact (go_freed _ _ _ GOa)|].
            exists ba, (mkGhdr (Some a) ai). split; [exact (go_mem _ _ _ GOa)|]. split; [exact Hgh|]. cbn. pose proof (go_li _ _ _ GOa). lia. }
        assert (AVK : forall a, an = true -> active st1 sc = Some a ->
                 rimplT o (activate_group a st1 (fun st2 _ => free_group R dec_hdr (nontrivial_free dec_hdr f) st2 g k bail) bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x19530) fc None m3 (seg_rom usegs))).
        { intros a AN A1. apply rimplT_guard. intros AV0. apply Z.eqb_eq in AV0. cbv zeta.
          change (upd_meta a _ st1) with (act_st st1 a (act_of st1 a)).
          set (stA := act_st st1 a (act_of st1 a)).
          destruct (kinv_active _ _ _ _ _ KI1 A1) as (_ & MSa & Na & GMa & _).
          assert (NEa : a <> g) by (intros ->; exact (Na GN1)).
          eapply rimplT_evt; [apply PDQ; intros _ a' A1'; rewrite A1 in A1'; inversion A1'; subst; exact AV0|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = stA) by (unfold pd_st; rewrite AN, A1; reflexivity). rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX stA m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4.
          - unfold stA. apply KINV_act; [exact KI1| exact GMa| exact AV0| apply act_of_nonneg].
          - unfold stA. apply ZINV_act. exact ZI1.
          - unfold stA, act_st. apply LPRE_upd_other; [exact NEa| exact LP1].
          - unfold stA. apply frame_act; [exact FR1'| eapply (LG_frame st st1 a FR1'); left; exact Na].
          - unfold stA. rewrite act_st_rec_other by congruence. exact GN1.
          - unfold stA. rewrite act_st_rec_other by congruence. apply DSdata.
          - unfold stA. rewrite act_st_regions. apply (sbl_regions _ _ SBL1).
          - unfold stA. rewrite act_st_shadow. apply (sbl_shadow _ _ SBL1).
          - unfold stA. rewrite act_st_groups. apply (sbl_groups _ _ SBL1).
          - unfold stA. rewrite act_st_rec_other by congruence. intros Hsc. unfold usage. cbn [ctx act_st upd_meta put_meta set_metas s_ctx].
            change (default 0 (c_usage (s_ctx st1) !! m_sizeclass (get_meta_rec st1 g))) with (usage st1 (m_sizeclass (get_meta_rec st1 g))).
            apply (ki_usage _ _ _ KI1). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        assert (NOACT : (an = false \/ active st1 sc = None) ->
                 rimplT o (free_group R dec_hdr (nontrivial_free dec_hdr f) st1 g k bail) s Q
                   (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x0 x1 x2 s0 (Z_to_bv 64 RSSP_GUARD) (Z_to_bv 64 (conc st g)) (Z_to_bv 64 (RCTX + sc * 8)) (pw st (active st sc)) y3 y4 x5 x6 x7 (Z_to_bv 64 RCTX) s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x8 x9) F (Z_to_bv 64 0x19530) fc None m3 (seg_rom usegs))).
        { intros NA.
          eapply rimplT_evt; [apply PDQ; intros AN a' A1'; exfalso; destruct NA as [NA|NA]; congruence|].
          intros ms4 AQ. unfold rat00_post in AQ. destruct AQ as (z0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & m4 & -> & PE4 & WM4 & MI4 & ST4 & FR4 & MR4).
          assert (EP : pd_st an st1 sc = st1) by (unfold pd_st; destruct NA as [-> | NA]; [reflexivity| rewrite NA; destruct an; reflexivity]).
          rewrite EP in MR4.
          rewrite (conc_sbl _ _ g SBLm).
          eapply (FGX st1 m4 junk); try reflexivity; try exact MR4; try exact MI4; try exact ST4; try exact FR4; try exact KI1; try exact ZI1; try exact LP1; try exact FR1'; try exact GN1.
          - apply DSdata.
          - apply (sbl_regions _ _ SBL1).
          - apply (sbl_shadow _ _ SBL1).
          - apply (sbl_groups _ _ SBL1).
          - intros Hsc. rewrite (sbl_usage _ _ SBL1). apply (ki_usage _ _ _ KI). destruct (data_of_fields _ _ g (DSdata g)) as (_ & _ & _ & _ & _ & -> & _). exact (lp_class _ _ _ _ _ _ LP).
          - eapply rpres_except_trans; [exact PE03|]. eapply rpres_except_mono; [exact PE4|]. intros a0' Ha. eapply (rfree_fp_same st stm); eauto using sbl_regions, sbl_shadow, sbl_groups.
          - eapply wmono_trans; [| exact WM4]. eapply wmono_trans; [exact WM2| exact WM3]. }
        destruct an eqn:AN; [destruct (active st1 sc) as [a|] eqn:A1; [apply (AVK a eq_refl eq_refl)| apply NOACT; right; reflexivity] | apply NOACT; left; reflexivity]. }
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; first [congruence| exact SC48b]|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); congruence).
      * (* [comment removed for export] *)
        destruct D as (_ & NXg & _ & x0 & x1 & x2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx = g) by congruence.
        eapply rimplT_evt.
        { eapply (rntf_deqself ra sp gp tp _ _ _ s0 _ _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - rewrite NX, Enx. reflexivity. }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
      * (* [comment removed for export] *)
        destruct D as (_ & _ & nx' & NX' & NE & x0 & x1 & x2 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
        assert (Enx : nx' = nx) by congruence. subst nx'.
        eapply rimplT_evt.
        { eapply (rntf_deq ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g nx pv sc lo);
            first [exact MR1 | exact MI1 | exact MSL | exact NX | exact PV | exact NE | exact MSnx | exact MSpv | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | reflexivity | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - apply NEpv. exact NE.
          - destruct (active st sc) as [h|] eqn:Hh; [right| left; reflexivity]. exists h. split; [reflexivity|].
            exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))). }
        intros ms2 AP. eapply (DQ2 m1 junk); [left; exact MU| exact WM| exact AP].
    + (* [comment removed for export] *)
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]];
        try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as (nx0 & D3 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & ->).
      eapply (FGX st m1 junk); [exact KI | exact ZI | exact LP | apply frame_refl | exact NX | reflexivity | reflexivity | reflexivity | reflexivity
                               | | eapply rpres_except_entry; eauto | exact WM | exact MI1 | exact ST1 | exact FR1 | exact MR1 | reflexivity].
      intros Hsc. apply (ki_usage _ _ _ KI). exact (lp_class _ _ _ _ _ _ LP).
  - destruct (Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) =? 0) eqn:HM.
    + (* [comment removed for export] *)
      apply Z.eqb_eq in HM.
      apply rimplT_guard. intros SC48. apply Z.ltb_lt in SC48.
      (* [comment removed for export] *)
      assert (QTAIL : forall m1 junk stq (x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x : word),
        munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m1 -> wmono usegs m m1 ->
        stq = (if optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g) then st else queue_st (LActive (m_sizeclass (get_meta_rec st g))) g st) ->
        (active st (m_sizeclass (get_meta_rec st g)) <> Some g -> m_next (get_meta_rec st g) = None /\ m_prev (get_meta_rec st g) = None) ->
        forall ms2, rqpath_post ra sp gp tp s0 (Z_to_bv 64 RSSP_GUARD) (wz (sxv (2 ^ i))) s2x s3 s4 s5 s6 s7 s8 s9 s10 s11
                      x0 x1 x2 x6 x7 x3 x4 x5 x8 F fc lo st g m1 stq (rntf_frame junk s3 s2 s1 s0 ra) ms2 ->
        rimplT o (k (aor_st stq g i) None) s Q ms2).
      { intros m1 junk stq x0 x1 x2 x6 x7 x3 x4 x5 x8 s2x MU WM Estq GNP ms2 QP.
        assert (SBL : same_but_links st stq) by (rewrite Estq; destruct (optr_eqb _ _); [apply sbl_refl| apply sbl_queue]).
        assert (ZIq : ZINV stq Zs) by (apply (ZINV_sbl st stq Zs SBL); exact ZI).
        assert (KIq : KINV stq LB c).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [exact KI|].
          apply (KINV_queue st LB c g p _ KI HOSTS eq_refl ltac:(pose proof (go_sc _ _ _ GO); lia)).
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - apply GNP. intros E. rewrite E, optr_eqb_refl in HA. discriminate.
          - intros E. rewrite E, optr_eqb_refl in HA. discriminate. }
        assert (FRq : ntf_frame st stq).
        { rewrite Estq. destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; [apply frame_refl|].
          apply frame_queue; [apply frame_refl| apply (ki_links _ _ _ KI)| | right; exact (hosts_is_gm _ _ _ HOSTS)].
          cbn [get_head]. intros hd Hhd. exact (proj1 (proj2 (proj2 (kinv_active _ _ _ _ _ KI Hhd)))). }
        unfold rqpath_post in QP. cbv beta in QP.
        destruct QP as (qa0 & qa2 & qa3 & qa5 & m2 & -> & PE2 & WM2 & MI2 & ST2 & FR2 & MR2).
        pose proof (LPRE_sbl _ _ _ _ _ _ _ SBL LP) as LPq.
        rewrite <- (conc_sbl st stq g SBL).
        eapply rimplT_evt.
        { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 junk ra s0 s1 s2 s3 stq g i lo);
            first [exact MR2 | exact MI2 | reflexivity | exact FR2 | exact ST2 | exact LO | exact LOLE | idtac].
          - eapply meta_slot_sbl; [exact SBL| exact MSL].
          - pose proof (go_li _ _ _ GO). lia.
          - destruct (data_of_fields st stq g (sbl_data _ _ SBL g)) as (_ & _ & -> & _). exact (go_freed _ _ _ GO). }
        intros ms3 RP. apply KH.
        eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st stq _ m m2); try exact RP.
        * eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * intros a Ha. eapply (rfree_fp_frame st stq lo (bv_unsigned sp) (bv_unsigned sp)); [exact FRq| lia| exact Ha].
        * exists c. apply (KINV_aor _ _ _ _ _ _ KIq LPq).
        * apply ZINV_aor. exact ZIq.
        * apply frame_aor; [exact FRq| right; exact (hosts_is_gm _ _ _ HOSTS)].
        * exact eq_refl.
        * apply (oracle_ok_frame o m2 st stq); [| exact (sbl_regions _ _ SBL) | exact (sbl_shadow _ _ SBL)].
          eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO|].
          eapply rpres_except_trans; [eapply rpres_except_entry; eauto| exact PE2].
        * exact MR2.
        * reflexivity.
        * reflexivity. }
      destruct (optr_eqb (active st (m_sizeclass (get_meta_rec st g))) (Some g)) eqn:HA; cbn [negb].
      * (* [comment removed for export] *)
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) = Some g).
        { destruct (active st _) as [h|]; [|discriminate]. cbn in HA. apply aptr_eqb_eq in HA. congruence. }
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; fastfirst (first [ noevar_assumption |congruence | lia | exact HAct])|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - right. exists g. split; [exact HAct| exact MSL].
          - intros NE. exfalso. exact (NE HAct).
          - intros hd Hhd NE. exfalso. apply NE. congruence. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros NE; exfalso; exact (NE HAct)| exact QP].
      * (* [comment removed for export] *)
        assert (HAct : active st (m_sizeclass (get_meta_rec st g)) <> Some g).
        { intros E. rewrite E in HA. cbn in HA. rewrite aptr_eqb_refl in HA. discriminate. }
        apply rimplT_queue. intros GN GPV.
        eapply rimplT_evt; [apply ENTRY; apply EH0; intros; fastfirst (first [ noevar_assumption |congruence | lia])|].
        intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
        destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & D3); try destruct D3 as [D3 _]; congruence).
        destruct D as (_ & _ & x0 & x1 & x2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
        eapply rimplT_evt.
        { eapply (rntf_qpath ra sp gp tp _ _ _ s0 _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 _ st g (m_sizeclass (get_meta_rec st g)) lo);
            first [exact MR1 | exact MI1 | exact MSL | exact FR1 | apply rntf_frame_size | exact ST1 | exact LO | exact LOLE | idtac].
          - pose proof (go_sc _ _ _ GO). lia.
          - destruct (active st (m_sizeclass (get_meta_rec st g))) as [h|] eqn:Hh; [right| left; reflexivity].
            exists h. split; [reflexivity|]. exact (proj1 (proj2 (kinv_active _ _ _ _ _ KI Hh))).
          - intros _. split; assumption.
          - intros hd Hhd NE. destruct (kinv_active _ _ _ _ _ KI Hhd) as (_ & Shd & Nhd & _ & _ & pv & Ppv & Spv & Npv).
            split; [exact Shd|]. exists pv. split; [exact Ppv|]. split; [| exact Spv]. intros ->. rewrite GN in Npv. discriminate. }
        intros ms2 QP. unfold qpath_st in QP. rewrite HA in QP.
        eapply (QTAIL m1 junk); [exact MU| exact WM| reflexivity| intros _; split; assumption| exact QP].
    + (* [comment removed for export] *)
      apply Z.eqb_neq in HM.
      eapply rimplT_evt; [apply ENTRY; apply EH0; intros; congruence|].
      intros ms1 (m1 & junk & CASES & MU & WM & MI1 & ST1 & FR1 & MR1).
      destruct CASES as [D|[D|[D|[D|D]]]]; try (exfalso; destruct D as (D1 & D2 & _); congruence).
      destruct D as (_ & _ & x0 & x1 & x2 & y0 & y2 & y3 & y5 & y6 & y7 & s2x & x3 & x4 & x5 & x6 & ->).
      eapply rimplT_evt.
      { eapply (rntf_aor _ sp gp tp _ _ _ s0 _ _ _ _ _ _ _ _ s2x s3 s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ F fc m1 junk ra s0 s1 s2 s3 st g i lo);
          first [exact MR1 | exact MI1 | exact MSL | reflexivity | exact FR1 | exact ST1 | exact LO | exact LOLE | idtac].
        - pose proof (go_li _ _ _ GO). lia.
        - exact (go_freed _ _ _ GO). }
      intros ms2 RP. apply KH.
      eapply (rntf_q_intro Zs ra sp s0 s1 s2 s3 st st _ m m1); try exact RP.
      * eapply rpres_except_entry; eauto.
      * auto.
      * exists c. apply (KINV_aor _ _ _ _ _ _ KI LP).
      * apply ZINV_aor. exact ZI.
      * apply frame_aor; [apply frame_refl| right; exact (hosts_is_gm _ _ _ HOSTS)].
      * exact eq_refl.
      * eapply (roracle_ok_pres o _ _ st lo _ m); [exact OOK| exact MR| exact LO| eapply rpres_except_entry; eauto].
      * exact MR1.
      * reflexivity.
      * reflexivity.
Qed.
End NTF.

End PORT.

End WithCeil.
End TwB.
End RF_ntf.

(* [comment removed for export] *)
Module RMallocKit_A2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof using CEILV Hconc MSECV. pin_using (fun (CEILV Hconc MSECV : unit) => tt). ceil_facts. msec_facts. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof using CEILV Hmetas MSECV. pin_using (fun (CEILV Hmetas MSECV : unit) => tt). ceil_facts. msec_facts. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof using CEILV HP Hconc MSECV. pin_using (fun (CEILV HP Hconc MSECV : unit) => tt). ceil_facts. msec_facts.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof using CEILV HP Hconc Hctx MSECV. pin_using (fun (CEILV HP Hconc Hctx MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  assert (E1 : ctx_head_cells st' = ctx_head_cells st).
  { unfold ctx_head_cells. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
  { unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
    rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
  unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof using CEILV HP Hconc Hmetas MSECV. pin_using (fun (CEILV HP Hconc Hmetas MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof using CEILV HP Hconc MSECV. pin_using (fun (CEILV HP Hconc MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

Lemma rbytes_at_agree m m' A bs : bytes_at ssegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at ssegs m' A bs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rwr_at_agree m m' A n : wr_at ssegs m A n -> agree_on m m' A n -> wr_at ssegs m' A n.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree m m' A cs : rw_cells ssegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells ssegs m' A cs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree m m' A ws : u64arr ssegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr ssegs m' A ws.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree m m' A bs : u8arr ssegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr ssegs m' A bs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

(* [comment removed for export] *)
Lemma rmrep_agree : forall st m m',
  rmrep st m ->
  agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x418 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep st m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGA AGG AGR.
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof using CEILV MSECV k len st x. pin_using (fun (CEILV MSECV k len st x : unit) => tt). ceil_facts. msec_facts. rewrite rnr_regions. apply lookup_insert_eq. Qed.
Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof using CEILV MSECV r0. pin_using (fun (CEILV MSECV r0 : unit) => tt). ceil_facts. msec_facts. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rnr_lookup_new in H. inversion H. auto.
  - right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof using CEILV MSECV r0. pin_using (fun (CEILV MSECV r0 : unit) => tt). ceil_facts. msec_facts. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof using CEILV MSECV r0 st. pin_using (fun (CEILV MSECV r0 st : unit) => tt). ceil_facts. msec_facts. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof using MSECV TB ZF rid. pin_using (fun (MSECV TB ZF rid : unit) => tt). ceil_facts. msec_facts. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

(* [comment removed for export] *)
Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof using MSECV RF TB. pin_using (fun (MSECV RF TB : unit) => tt). ceil_facts. msec_facts.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma rnr_regions_wf : rregions_wf st'.
Proof using LEN MR PT RF X0 XA XC ZF r0. pin_using (fun (LEN MR PT RF X0 XA XC ZF r0 : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RFimg : ranges_free ref_reserved x L = true).
  { apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  split; [exact RS|]. split; [|split; [|split]].
  - intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
    + exact (WR q r H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
    exists r. rewrite rnr_lookup_old by exact Pa. auto.
  - intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
    exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.

Lemma rmrep_new_region : rmrep st' m'.
Proof using AG FRs LEN MR PT RF X0 XA XC ZF r0. pin_using (fun (AG FRs LEN MR PT RF X0 XA XC ZF r0 : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
  { intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
  pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
  pose proof (round_up_pg_ge len) as LG. fold L in LG. ceil_facts.
  (* [comment removed for export] *)
  assert (MR1 : rmrep st m').
  { eapply rmrep_agree; [exact MR| | | | | | |].
    - intros a Ha. apply AG; unfold RMLOCK in *; lia.
    - intros a Ha. apply AG; unfold RLIBC in *; lia.
    - intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
    - intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
    - intros a ar Ha a0 Ha0.
      destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
      ceil_facts. apply AG; lia.
    - intros b gh Hb a0 Ha0.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
      pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). ceil_facts. apply AG; lia.
    - intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). ceil_facts.
      pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
  pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
  assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
  split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
  - eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
  - intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
  - intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
  - intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + (* [comment removed for export] *)
      cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
      split.
      * split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
      * intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
        rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
        split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
        unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
    + eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.

Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts. intros H. exact H. Qed.

Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x418 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
   \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).

Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

Lemma rmrep_drop_region : rmrep st' m'.
Proof using AG Hr MR PT. pin_using (fun (AG Hr MR PT : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
  destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). ceil_facts.
  assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
            r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
    by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *)
    split; [exact RS|]. split; [|split; [|split]].
    + intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
    + intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
    + intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
      exists ra. rewrite rdr_lookup_old by exact Pa. auto.
    + intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
      exists rb. rewrite rdr_lookup_old by exact Pb. auto.
  - (* [comment removed for export] *)
    eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x55000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; pose proof (rreserved_disjoint2 _ _ RFr ltac:(lia)); tauto]. }
    assert (AGC : agree_on m m' RLIBC 0x418).
    { intros a Ha. unfold RLIBC in Ha. apply AG; [lia| lia| right; left; unfold RLIBC; lia]. }
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x55000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; pose proof (rreserved_disjoint2 _ _ RFr ltac:(lia)); tauto]. }
    unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; lia].
    + eapply rrw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rrw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rrw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
    + eapply rrw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
  - intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
    eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). ceil_facts.
    assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
    pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
    assert (AGA : agree_on m m' (conc st a) 4096).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
    destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
    + intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
  - intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
    eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
    pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). ceil_facts.
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
    right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
  - intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
    eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
    destruct (WR q rq H) as (Bq & _ & _ & BCq & _). ceil_facts.
    pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
    assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
    destruct (SH q rq H Hk) as [HWr HB]. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof using CEILV MSECV rid. pin_using (fun (CEILV MSECV rid : unit) => tt). ceil_facts. msec_facts.
  intros [T1 T2]. split.
  - intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
  - intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
  rmrep st m -> (s_groups st) !! b = None ->
  (s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
  rw_cells ssegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
  pose proof WF as (RS & WR & DJ & WA & WG).
  split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
  - split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
    + rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
  - intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
    + rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_set_mmap_counter : forall st m v,
  rmrep st m -> 0 <= v < 2^32 ->
  rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le4 (wz v)) as L4.
  pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
  pose proof (wmono_write ssegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl ssegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
  - left.
    pose proof (rw_cells_write ssegs m RCTX (ctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
    replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
    unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB.
Export OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

Lemma rpw_extP p : optr_in P p -> pw st' p = pw st p.
Proof using CEILV Hconc MSECV. pin_using (fun (CEILV Hconc MSECV : unit) => tt). ceil_facts. msec_facts. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

Lemma rget_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof using CEILV Hmetas MSECV. pin_using (fun (CEILV Hmetas MSECV : unit) => tt). ceil_facts. msec_facts. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

Lemma rmeta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof using CEILV HP Hconc MSECV. pin_using (fun (CEILV HP Hconc MSECV : unit) => tt). ceil_facts. msec_facts.
  destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
  unfold meta_cells. rewrite !rpw_extP by assumption. reflexivity.
Qed.

Lemma rmrep_ctx_extP m : rmrep_ctx st m -> rmrep_ctx st' m.
Proof using CEILV HP Hconc Hctx MSECV. pin_using (fun (CEILV HP Hconc Hctx MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H. destruct HP as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & _).
  assert (E1 : ctx_head_cells st' = ctx_head_cells st).
  { unfold ctx_head_cells. rewrite Hctx. rewrite !rpw_extP by assumption. reflexivity. }
  assert (E2 : actives st' = actives st).
  { unfold actives. apply map_ext. intros a. unfold active. rewrite Hctx. apply rpw_extP. apply (H6 (Z.of_nat a)). }
  assert (E3 : usages st' = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite Hctx. reflexivity. }
  assert (E4 : unmap_seqs st' = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite Hctx. reflexivity. }
  assert (E5 : bouncess st' = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite Hctx. reflexivity. }
  assert (E6 : ctx_tail_cells st' = ctx_tail_cells st).
  { unfold ctx_tail_cells, brk_word. rewrite Hctx. destruct (c_brk (ctx st)) as [| |rid off]; try reflexivity.
    rewrite (Hconc (rid, off)) by exact H7. reflexivity. }
  unfold rmrep_ctx in *. rewrite E1, E2, E3, E4, E5, E6. exact H.
Qed.

Lemma rarea_rep_extP m a ar : (s_areas st) !! a = Some ar -> rarea_rep st m a ar -> rarea_rep st' m a ar.
Proof using CEILV HP Hconc Hmetas MSECV. pin_using (fun (CEILV HP Hconc Hmetas MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Ha (A1 & A2 & A3). destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & H9 & _).
  destruct (H9 a ar Ha) as [Pa Pn].
  unfold rarea_rep. rewrite (Hconc a Pa). rewrite (rpw_extP _ Pn). split; [exact A1|]. split; [|exact A3].
  intros k Hk. rewrite rget_meta_rec_extP, rmeta_cells_extP. apply A2. exact Hk.
Qed.

Lemma rgroup_rep_extP m b gh : (s_groups st) !! b = Some gh -> rgroup_rep st m b gh -> rgroup_rep st' m b gh.
Proof using CEILV HP Hconc MSECV. pin_using (fun (CEILV HP Hconc MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Hb (w8 & R & Hw8). destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & H10).
  destruct (H10 b gh Hb) as [Pb Pg]. exists w8. rewrite (Hconc b Pb), (rpw_extP _ Pg). auto.
Qed.
End PEXT.

Lemma rbytes_at_agree m m' A bs : bytes_at usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> bytes_at usegs m' A bs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros (H0 & H1 & HB) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold mrd. rewrite (AG (A + Z.of_nat i)) by lia. apply HB. exact Hi.
Qed.

Lemma rwr_at_agree m m' A n : wr_at usegs m A n -> agree_on m m' A n -> wr_at usegs m' A n.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros (H0 & H1 & HW) AG. split; [exact H0|]. split; [exact H1|]. intros i Hi.
  unfold wview. rewrite (AG (A + i)) by lia. apply HW. exact Hi.
Qed.

Lemma rrw_cells_agree m m' A cs : rw_cells usegs m A cs -> agree_on m m' A (Z.of_nat (cells_size cs)) -> rw_cells usegs m' A cs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros [[Hwf HB] HW] AG. split; [split; [exact Hwf|]|].
  - eapply rbytes_at_agree; [exact HB|]. rewrite cells_bytes_length by assumption. exact AG.
  - eapply rwr_at_agree; eauto.
Qed.

Lemma ru64arr_agree m m' A ws : u64arr usegs m A ws -> agree_on m m' A (8 * Z.of_nat (length ws)) -> u64arr usegs m' A ws.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros [HB HW] AG. split.
  - eapply rbytes_at_agree; [exact HB|]. rewrite u64s_length. replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia. exact AG.
  - eapply rwr_at_agree; [exact HW|]. exact AG.
Qed.

Lemma ru8arr_agree m m' A bs : u8arr usegs m A bs -> agree_on m m' A (Z.of_nat (length bs)) -> u8arr usegs m' A bs.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros [HB HW] AG. split; [eapply rbytes_at_agree; eauto| eapply rwr_at_agree; eauto]. Qed.

(* [comment removed for export] *)
Lemma rmrep_agree : forall st m m',
  rmrep st m ->
  agree_on m m' RMLOCK 4 -> agree_on m m' RLIBC 0x418 -> agree_on m m' RGOT_SSP 8 -> agree_on m m' RSSP_GUARD 8 ->
  (forall a ar, (s_areas st) !! a = Some ar -> agree_on m m' (conc st a) 4096) ->
  (forall b gh, (s_groups st) !! b = Some gh -> agree_on m m' (conc st b) 9) ->
  (forall rid r, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> agree_on m m' (r_base r) (round_up_pg (r_len r))) ->
  rmrep st m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' (WF & CX & GL & AR & GR & SH) AGL AGC AGS1 AGS2 AGA AGG AGR.
  split; [exact WF|]. split; [|split; [|split; [|split]]].
  - destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. eapply agree_on_sub; [exact AGL| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G2|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G3|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G4|]. eapply agree_on_sub; [exact AGS1| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact G5|]. eapply agree_on_sub; [exact AGS2| lia| cbn; lia].
  - intros a ar Ha. destruct (AR a ar Ha) as (A1 & A2 & A3). pose proof (AGA a ar Ha) as AG.
    split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
    + intros k Hk. eapply rrw_cells_agree; [apply A2; exact Hk|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AG| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AG| lia| cbn; lia].
  - intros b gh Hb. destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. cbn. exact (AGG b gh Hb).
  - intros rid r Hr Hk. destruct (SH rid r Hr Hk) as [HWr HB]. pose proof (AGR rid r Hr Hk) as AG. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis MR : rmrep st m.
Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.
(* [comment removed for export] *)
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

Lemma rnr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rnr_lookup_new : (s_regions st') !! rid = Some r0.
Proof using CEILV MSECV k len st x. pin_using (fun (CEILV MSECV k len st x : unit) => tt). ceil_facts. msec_facts. rewrite rnr_regions. apply lookup_insert_eq. Qed.
Lemma rnr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof using CEILV MSECV r0. pin_using (fun (CEILV MSECV r0 : unit) => tt). ceil_facts. msec_facts. intros. rewrite rnr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rnr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rnr_lookup_new in H. inversion H. auto.
  - right. rewrite rnr_lookup_old in H by exact NE. auto.
Qed.
Lemma rnr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof using CEILV MSECV r0. pin_using (fun (CEILV MSECV r0 : unit) => tt). ceil_facts. msec_facts. intros. unfold conc, get_region. rewrite rnr_lookup_old by assumption. reflexivity. Qed.
Lemma rnr_conc_new off : conc st' (rid, off) = x + off.
Proof using CEILV MSECV r0 st. pin_using (fun (CEILV MSECV r0 st : unit) => tt). ceil_facts. msec_facts. unfold conc, get_region. cbn [fst snd]. rewrite rnr_lookup_new. reflexivity. Qed.
Lemma rnr_shadow q : get_shadow st' q = get_shadow st q.
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rnr_lr_lo_new : x <= lr_lo r0.
Proof using MSECV TB ZF rid. pin_using (fun (MSECV TB ZF rid : unit) => tt). ceil_facts. msec_facts. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

(* [comment removed for export] *)
Lemma rnr_old_disjoint q r : (s_regions st) !! q = Some r ->
  x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof using MSECV RF TB. pin_using (fun (MSECV RF TB : unit) => tt). ceil_facts. msec_facts.
  intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
  unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
  destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

Lemma rnr_regions_wf : rregions_wf st'.
Proof using LEN MR PT RF X0 XA XC ZF r0. pin_using (fun (LEN MR PT RF X0 XA XC ZF r0 : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RFimg : ranges_free ref_reserved x L = true).
  { apply ranges_free_intro. intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  split; [exact RS|]. split; [|split; [|split]].
  - intros q r Hq. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + unfold r0. cbn. fold L. repeat split; try lia. exact RFimg.
    + exact (WR q r H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (rnr_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rnr_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q2 r2 H2'). pose proof rnr_lr_lo_new. lia.
    + cbn [r_base r_len r0]. fold L. pose proof (rnr_old_disjoint q1 r1 H1'). pose proof rnr_lr_lo_new. lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
    exists r. rewrite rnr_lookup_old by exact Pa. auto.
  - intros b gh Hb. destruct (WG b gh Hb) as (r & Hr & REST).
    destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
    exists r. rewrite rnr_lookup_old by exact Pb. auto.
Qed.

Lemma rmrep_new_region : rmrep st' m'.
Proof using AG FRs LEN MR PT RF X0 XA XC ZF r0. pin_using (fun (AG FRs LEN MR PT RF X0 XA XC ZF r0 : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (RI : forall b n, In (b, n) ref_reserved -> x + L <= b \/ b + n <= x).
  { intros b n HI. apply (ranges_free_In _ _ _ _ _ RF). unfold live_ranges. apply in_or_app. left. rewrite RS. exact HI. }
  pose proof (RI _ _ ltac:(left; reflexivity)) as RI1. pose proof (RI _ _ ltac:(right; right; left; reflexivity)) as RI2.
  pose proof (RI _ _ ltac:(right; right; right; left; reflexivity)) as RI3.
  pose proof (round_up_pg_ge len) as LG. fold L in LG. ceil_facts.
  (* [comment removed for export] *)
  assert (MR1 : rmrep st m').
  { eapply rmrep_agree; [exact MR| | | | | | |].
    - intros a Ha. apply AG; unfold RMLOCK in *; lia.
    - intros a Ha. apply AG; unfold RLIBC in *; lia.
    - intros a Ha. apply AG; unfold RGOT_SSP in *; lia.
    - intros a Ha. apply AG; unfold RSSP_GUARD in *; lia.
    - intros a ar Ha a0 Ha0.
      destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
      pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rnr_old_disjoint _ _ Hra).
      ceil_facts. apply AG; lia.
    - intros b gh Hb a0 Ha0.
      destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
      pose proof (lr_lo_group rb Kb). pose proof (rnr_old_disjoint _ _ Hrb). ceil_facts. apply AG; lia.
    - intros q r Hq Hk a0 Ha0. destruct (WR q r Hq) as (B0 & _ & _ & BC & _). ceil_facts.
      pose proof (lr_lo_group r Hk). pose proof (rnr_old_disjoint _ _ Hq). apply AG; lia. }
  pose proof MR1 as (_ & CX1 & GL1 & AR1 & GR1 & SH1).
  assert (Hconc : forall q, (fun r => r <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rnr_conc; exact Hq).
  split; [exact rnr_regions_wf|]. split; [|split; [exact GL1|split; [|split]]].
  - eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl). exact CX1.
  - intros a ar Ha. eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|]. exact (AR1 a ar Ha).
  - intros b gh Hb. eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|]. exact (GR1 b gh Hb).
  - intros q r Hq Hk. destruct (rnr_lookup_inv q r Hq) as [[-> ->]|[NE H]].
    + (* [comment removed for export] *)
      cbn [r_kind r0] in Hk. unfold rshadow_rep. cbn [r_base r_len r0]. fold L.
      split.
      * split; [lia|]. split; [lia|]. intros i Hi. unfold wview. rewrite (ZF Hk) by lia. discriminate.
      * intros o v Ho Hc. rewrite rnr_shadow in Hc. unfold get_shadow in Hc. fold rid in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc.
        rewrite cell_read_shadow0 in Hc. inversion Hc; subst v. split; [|lia].
        split; [lia|]. split; [cbn; lia|]. intros i Hi. destruct i; [|cbn in Hi; lia]. cbn [nth_error].
        unfold mrd. rewrite Z.add_0_r. rewrite (ZF Hk) by lia. reflexivity.
    + eapply rshadow_rep_ext; [apply rnr_shadow|]. exact (SH1 q r H Hk).
Qed.

Lemma rticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts. intros H. exact H. Qed.

Lemma rptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof using CEILV MSECV k len x. pin_using (fun (CEILV MSECV k len x : unit) => tt). ceil_facts. msec_facts. intros H. exact H. Qed.
End NEWREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.
Hypothesis MR : rmrep st m.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
  (RMLOCK <= a < RMLOCK + 4 \/ RLIBC <= a < RLIBC + 0x418 \/ RGOT_SSP <= a < RGOT_SSP + 8 \/ RSSP_GUARD <= a < RSSP_GUARD + 8
   \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
  m' (wa a) = m (wa a).

Lemma rdr_regions : s_regions st' = delete rid (s_regions st).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. reflexivity. Qed.
Lemma rdr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H. rewrite rdr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
  - rewrite lookup_delete_eq in H. discriminate.
  - rewrite lookup_delete_ne in H by congruence. auto.
Qed.
Lemma rdr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros. rewrite rdr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
Lemma rdr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros. unfold conc, get_region. rewrite rdr_lookup_old by assumption. reflexivity. Qed.
Lemma rdr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

Lemma rmrep_drop_region : rmrep st' m'.
Proof using AG Hr MR PT. pin_using (fun (AG Hr MR PT : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  assert (Hconc : forall q, (fun q => q <> rid) (fst q) -> conc st' q = conc st q) by (intros q Hq; apply rdr_conc; exact Hq).
  destruct (WR rid r Hr) as (B0 & _ & RL0 & BC & RFr). ceil_facts.
  assert (OTHER : forall q rq, (s_regions st) !! q = Some rq -> q <> rid ->
            r_base rq + round_up_pg (r_len rq) <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= lr_lo rq)
    by (intros q rq Hq NE; exact (DJ q rq rid r Hq Hr NE)).
  split; [|split; [|split; [|split; [|split]]]].
  - (* [comment removed for export] *)
    split; [exact RS|]. split; [|split; [|split]].
    + intros q rq Hq. destruct (rdr_lookup_inv q rq Hq) as [_ H]. exact (WR q rq H).
    + intros q1 r1 q2 r2 H1 H2 NE. destruct (rdr_lookup_inv _ _ H1) as [_ H1']. destruct (rdr_lookup_inv _ _ H2) as [_ H2']. exact (DJ _ _ _ _ H1' H2' NE).
    + intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _). destruct (P9 a ar Ha) as [Pa _].
      exists ra. rewrite rdr_lookup_old by exact Pa. auto.
    + intros b gh Hb. destruct (WG b gh Hb) as (rb & Hrb & REST).
      destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10). destruct (P10 b gh Hb) as [Pb _].
      exists rb. rewrite rdr_lookup_old by exact Pb. auto.
  - (* [comment removed for export] *)
    eapply (rmrep_ctx_extP st st' _ PT Hconc eq_refl).
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite map_length, seq_length; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite map_length, seq_length; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite map_length, seq_length; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite map_length, seq_length; reflexivity).
    pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x56000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; pose proof (rreserved_disjoint2 _ _ RFr ltac:(lia)); tauto]. }
    assert (AGC : agree_on m m' RLIBC 0x418).
    { intros a Ha. unfold RLIBC in Ha. apply AG; [lia| lia| right; left; unfold RLIBC; lia]. }
    unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - destruct GL as (G1 & G2 & G3 & G4 & G5). pose proof (round_up_pg_ge (r_len r)). pose proof (lr_lo_ge r).
    assert (DD : ((r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x22000 <= r_base r) /\ (r_base r + round_up_pg (r_len r) <= 0x22000 \/ 0x56000 <= r_base r)) \/ round_up_pg (r_len r) = 0).
    { destruct (Z.eq_dec (round_up_pg (r_len r)) 0); [right; lia| left; pose proof (rreserved_disjoint2 _ _ RFr ltac:(lia)); tauto]. }
    unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]].
    + eapply rrw_cells_agree; [exact G1|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|left; lia].
    + eapply rrw_cells_agree; [exact G2|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rrw_cells_agree; [exact G3|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; left; lia].
    + eapply rrw_cells_agree; [exact G4|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; left; lia].
    + eapply rrw_cells_agree; [exact G5|]. intros a Ha. cbn in Ha. apply AG; [lia|lia|right; right; right; left; lia].
  - intros a ar Ha. cbn [s_areas drop_region set_shadow set_regions] in Ha.
    eapply (rarea_rep_extP st st' _ PT Hconc eq_refl); [exact Ha|].
    destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
    pose proof (rarea_lr_lo st a ar ra WF Ha Hra). ceil_facts.
    assert (NE : fst a <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _); exact (proj1 (P9 a ar Ha))).
    pose proof (OTHER _ _ Hra NE). pose proof (lr_lo_ge r). pose proof (lr_lo_ge ra).
    assert (AGA : agree_on m m' (conc st a) 4096).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists (fst a), ra. split; [exact Hra|]. lia. }
    destruct (AR a ar Ha) as (A1 & A2 & A3). split; [|split].
    + eapply rrw_cells_agree; [exact A1|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
    + intros k0 Hk0. eapply rrw_cells_agree; [apply A2; exact Hk0|]. unfold meta_cells. cbn [cells_size csize Nat.add length].
      unfold AREA_HDR, META_SIZE, NSLOTS in *. eapply agree_on_sub; [exact AGA| lia| lia].
    + eapply rrw_cells_agree; [exact A3|]. eapply agree_on_sub; [exact AGA| lia| cbn; lia].
  - intros b gh Hb. cbn [s_groups drop_region set_shadow set_regions] in Hb.
    eapply (rgroup_rep_extP st st' _ PT Hconc); [exact Hb|].
    destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
    assert (NE : fst b <> rid) by (destruct PT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10); exact (proj1 (P10 b gh Hb))).
    pose proof (OTHER _ _ Hrb NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rb Kb). ceil_facts.
    destruct (GR b gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
    eapply rrw_cells_agree; [exact R|]. intros a0 Ha0. cbn in Ha0. apply AG; [lia| lia|].
    right; right; right; right. exists (fst b), rb. split; [exact Hrb|]. lia.
  - intros q rq Hq Hk. destruct (rdr_lookup_inv q rq Hq) as [NE H].
    eapply rshadow_rep_ext; [apply rdr_shadow; exact NE|].
    destruct (WR q rq H) as (Bq & _ & _ & BCq & _). ceil_facts.
    pose proof (OTHER _ _ H NE). pose proof (lr_lo_ge r). pose proof (lr_lo_group rq Hk).
    assert (AGR : agree_on m m' (r_base rq) (round_up_pg (r_len rq))).
    { intros a0 Ha0. apply AG; [lia| lia|]. right; right; right; right. exists q, rq. split; [exact H|]. lia. }
    destruct (SH q rq H Hk) as [HWr HB]. split.
    + eapply rwr_at_agree; eauto.
    + intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AGR| lia| lia].
Qed.

Lemma rticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof using CEILV MSECV rid. pin_using (fun (CEILV MSECV rid : unit) => tt). ceil_facts. msec_facts.
  intros [T1 T2]. split.
  - intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
  - intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
    destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
    rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rmrep_put_group_new : forall st m b g ai r (w8 : byte),
  rmrep st m -> (s_groups st) !! b = None ->
  (s_regions st) !! (fst b) = Some r -> r_kind r = RKGroup -> 0 <= snd b -> snd b + 16 <= round_up_pg (r_len r) -> snd b mod 16 = 0 ->
  rw_cells usegs m (conc st b) [C8 (pw st (Some g)); C1 w8] -> Z.land (bv_unsigned w8) 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m b g ai r w8 (WF & CX & GL & AR & GR & SH) Hb Hr Hk B0 B16 BA R Hw8.
  pose proof WF as (RS & WR & DJ & WA & WG).
  split; [|split; [exact CX|split; [exact GL|split; [exact AR|split; [|exact SH]]]]].
  - split; [exact RS|]. split; [exact WR|]. split; [exact DJ|]. split; [exact WA|].
    intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists r. auto.
    + rewrite lookup_insert_ne in Hb' by congruence. exact (WG b' gh Hb').
  - intros b' gh Hb'. unfold put_group in Hb'. cbn [s_groups set_groups] in Hb'.
    destruct (decide (b' = b)) as [->|NE].
    + rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. exists w8. cbn [g_meta g_active_idx]. split; [exact R| exact Hw8].
    + rewrite lookup_insert_ne in Hb' by congruence. exact (GR b' gh Hb').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rmrep_set_mmap_counter : forall st m v,
  rmrep st m -> 0 <= v < 2^32 ->
  rmrep (upd_ctx (set_mmap_counter v) st) (write_to_mem m (wa (RCTX + 12)) (le4 (wz v))).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m v MR Hv. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (length_le4 (wz v)) as L4.
  pose proof (munch_write [(RCTX + 12, RCTX + 16)] m m (RCTX + 12) (le4 (wz v)) (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(rewrite L4; unfold RCTX; lia) ltac:(rewrite L4; cbn [inside]; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 12)) (le4 (wz v)) (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st (upd_ctx (set_mmap_counter v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst. unfold RCTX. lia.
  - left.
    pose proof (rw_cells_write usegs m RCTX (ctx_head_cells st) 12 (C4 (wz (c_mmap_counter (ctx st)))) (C4 (wz v)) X1 eq_refl eq_refl I) as W.
    replace (RCTX + Z.of_nat 12) with (RCTX + 12) in W by reflexivity.
    unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_mmap_counter c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    cbn [cell_upd csize Nat.eqb Nat.sub cbytes] in W. exact W.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold actives, active, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_active]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold usages, usage, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_usage]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold unmap_seqs, unmap_seq, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_unmap_seq]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold bouncess, bounces, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_bounces]. reflexivity.
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold RCTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_mmap_counter c_seq c_brk]. reflexivity.
Qed.

End PORT.

End WithCeil.
End TwB.
End RMallocKit_A2.

(* [comment removed for export] *)
Module RF_realloc63R.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Definition ptrs_ctx_in (P : N -> Prop) (st : mstate) : Prop :=
  let c := ctx st in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive rid _ => P rid | _ => True end
  /\ (forall q, optr_in P (m_prev (get_meta_rec st q)) /\ optr_in P (m_next (get_meta_rec st q)))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> optr_in P (g_meta gh)).

Lemma round_up_pg_id' x : x mod 4096 = 0 -> round_up_pg x = x.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section RELOC.
Variables (st : mstate) (m1 mA m3 : mem) (g b pf : aptr) (ai : Z) (r : region) (nb needed G : Z).
Let rid := fst b.
Let mr := get_meta_rec st g.
Let old := r_base r.
Let on := round_up_pg (r_len r).
Let mr' := m_set_maplen (needed / 4096) mr.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) st.
Let st2 := upd_meta g (m_set_maplen (needed / 4096)) st1.

Hypothesis MR : rmrep st m1.
Hypothesis TK : ticks_ok st.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Hgh : (s_groups st) !! b = Some (mkGhdr (Some g) ai).
Hypothesis Sb : snd b = 0.
Hypothesis ONLYG : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = rid -> b' = b.
Hypothesis MEMG : forall q b'', m_mem (get_meta_rec st q) = Some b'' -> fst b'' = rid -> q = g.
Hypothesis MSg : meta_slot st g.
Hypothesis HG : conc st g = G.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis PTX : ptrs_ctx_in (fun x => x <> rid) st.
Hypothesis Fpf : fst pf = rid.
Hypothesis PF : 16 <= snd pf /\ snd pf <= on /\ snd pf + 4 <= needed.
Hypothesis NOK : forall o v, snd pf <= o < needed -> cell_read (get_shadow st rid) o = Known v -> False.
Hypothesis ON0 : 0 < on.
Hypothesis NB0 : 0 < nb.
Hypothesis NBAL : nb mod 4096 = 0.
Hypothesis ND : 4096 <= needed.
Hypothesis NDAL : needed mod 4096 = 0.
Hypothesis NC : nb + needed <= alloc_ceiling.
Hypothesis RFN : ranges_free ref_reserved nb needed = true.
Hypothesis DJN : forall rid' r', (s_regions st) !! rid' = Some r' -> rid' <> rid ->
  nb + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb.
(* [comment removed for export] *)
Hypothesis AGA : forall A n, 0 <= A -> 0 <= n -> (A + n <= old \/ old + on <= A) -> (A + n <= nb \/ nb + needed <= A) ->
  A + n <= alloc_ceiling -> agree_on m1 mA A n.
Hypothesis CPY : forall o, 0 <= o < snd pf -> mA (wa (nb + o)) = m1 (wa (old + o)).
Hypothesis WRN : wr_at ssegs mA nb needed.
Hypothesis MU3 : munch [(G + 16, G + 24); (G + 32, G + 40)]%Z mA m3.
Hypothesis WM3 : wmono ssegs mA m3.
Hypothesis MC3 : rw_cells ssegs m3 G [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz nb); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr'))].

(* [comment removed for export] *)
Lemma rl_regions : s_regions st2 = <[rid := mkRegion (r_kind r) nb needed]> (s_regions st).
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_lookup_new : (s_regions st2) !! rid = Some (mkRegion (r_kind r) nb needed).
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. rewrite rl_regions. apply lookup_insert_eq. Qed.
Lemma rl_lookup_old q : q <> rid -> (s_regions st2) !! q = (s_regions st) !! q.
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. intros. rewrite rl_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rl_lookup_inv q rq : (s_regions st2) !! q = Some rq -> (q = rid /\ rq = mkRegion (r_kind r) nb needed) \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rl_lookup_new in H. inversion H. auto.
  - right. rewrite rl_lookup_old in H by exact NE. auto.
Qed.
Lemma rl_conc q : fst q <> rid -> conc st2 q = conc st q.
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. intros. unfold conc, get_region. rewrite rl_lookup_old by assumption. reflexivity. Qed.
Lemma rl_conc_new q : fst q = rid -> conc st2 q = nb + snd q.
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. intros E. unfold conc, get_region. rewrite E, rl_lookup_new. reflexivity. Qed.
Lemma rl_areas : s_areas st2 = s_areas st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_groups : s_groups st2 = s_groups st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_ctx : ctx st2 = ctx st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_reserved : s_reserved st2 = s_reserved st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_shadow q : get_shadow st2 q = get_shadow st q. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_tick : s_tick st2 = s_tick st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_sshadow : s_shadow st2 = s_shadow st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_meta1 q : get_meta_rec st1 q = get_meta_rec st q.
Proof using CEILV Hr MSECV nb needed. pin_using (fun (CEILV Hr MSECV nb needed : unit) => tt). ceil_facts. msec_facts. unfold st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_meta_same : get_meta_rec st2 g = mr'.
Proof using CEILV Hr MSECV mr st1. pin_using (fun (CEILV Hr MSECV mr st1 : unit) => tt). ceil_facts. msec_facts. unfold st2. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.get_meta_rec_upd_same, rl_meta1. reflexivity. Qed.
Lemma rl_meta_other q : q <> g -> get_meta_rec st2 q = get_meta_rec st q.
Proof using CEILV Hr MSECV st1. pin_using (fun (CEILV Hr MSECV st1 : unit) => tt). ceil_facts. msec_facts. intros NE. unfold st2. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.get_meta_rec_upd_other by exact NE. apply rl_meta1. Qed.

(* [comment removed for export] *)
Lemma rl_old_facts : 0 < old /\ old mod 4096 = 0 /\ old + on <= alloc_ceiling /\ ranges_free ref_reserved old on = true /\ 0 <= on.
Proof using Fpf Hr MR ON0 nb needed. pin_using (fun (Fpf Hr MR ON0 nb needed : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG). destruct (WR _ _ Hr) as (B0 & BAL & L0 & BC & RF).
  pose proof (round_up_pg_ge (r_len r)). subst old on. repeat split; auto; lia.
Qed.

Lemma rl_area_far a ar : (s_areas st) !! a = Some ar ->
  exists ra, (s_regions st) !! (fst a) = Some ra /\ fst a <> rid /\ conc st a = r_base ra + snd a
    /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len ra) /\ 0 < r_base ra /\ r_base ra + round_up_pg (r_len ra) <= alloc_ceiling
    /\ (r_base ra + snd a + 4096 <= old \/ old + on <= r_base ra + snd a)
    /\ (r_base ra + snd a + 4096 <= nb \/ nb + needed <= r_base ra + snd a).
Proof using AGA CPY DJN Fpf HG Hr Kr MC3 MR MU3 NB0 ND ON0 PF TLSFACTS. pin_using (fun (AGA CPY DJN Fpf HG Hr Kr MC3 MR MU3 NB0 ND ON0 PF TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Ha. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (NE : fst a <> rid). { intros E. rewrite E in Hra. fold rid in Hr. rewrite Hr in Hra. inversion Hra; subst. exact (NK Kr). }
  pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LL. pose proof (lr_lo_group r Kr) as LR.
  exists ra. repeat (split; [first [exact Hra| exact NE| exact Ca| exact Sa0| exact Sa1| exact RB0| exact RBC] |]).
  split.
  - fold rid in Hr. destruct (DJ _ _ _ _ Hra Hr NE); subst old on; lia.
  - destruct (DJN _ _ Hra NE); lia.
Qed.

Lemma rl_group_far b' gh : (s_groups st) !! b' = Some gh -> b' <> b ->
  exists rb, (s_regions st) !! (fst b') = Some rb /\ fst b' <> rid /\ conc st b' = r_base rb + snd b' /\ r_kind rb = RKGroup
    /\ 0 <= snd b' /\ snd b' + 16 <= round_up_pg (r_len rb) /\ 0 < r_base rb /\ r_base rb + round_up_pg (r_len rb) <= alloc_ceiling
    /\ (r_base rb + round_up_pg (r_len rb) <= old \/ old + on <= r_base rb)
    /\ (r_base rb + round_up_pg (r_len rb) <= nb \/ nb + needed <= r_base rb).
Proof using DJN Fpf Hr Kr MR NB0 ND ONLYG TLSFACTS. pin_using (fun (DJN Fpf Hr Kr MR NB0 ND ONLYG TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hb NEb. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rgroup_conc st b' gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
  assert (NE : fst b' <> rid). { intros E. apply NEb. exact (ONLYG _ _ Hb E). }
  pose proof (lr_lo_group rb Kb) as LL. pose proof (lr_lo_group r Kr) as LR.
  exists rb. repeat (split; [first [exact Hrb| exact NE| exact Cb| exact Kb| exact Sb0| exact Sb1| exact RB0| exact RBC] |]).
  split.
  - fold rid in Hr. destruct (DJ _ _ _ _ Hrb Hr NE); subst old on; lia.
  - destruct (DJN _ _ Hrb NE); lia.
Qed.

Lemma rl_greg_far q rq : (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq = RKGroup ->
  0 < r_base rq /\ r_base rq + round_up_pg (r_len rq) <= alloc_ceiling
  /\ (r_base rq + round_up_pg (r_len rq) <= old \/ old + on <= r_base rq)
  /\ (r_base rq + round_up_pg (r_len rq) <= nb \/ nb + needed <= r_base rq).
Proof using DJN Fpf Hr Kr MR NB0 ND TLSFACTS. pin_using (fun (DJN Fpf Hr Kr MR NB0 ND TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hq NE Kq. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (WR _ _ Hq) as (B0 & _ & _ & BC & _). pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Kr).
  split; [exact B0|]. split; [exact BC|]. split.
  - fold rid in Hr. destruct (DJ _ _ _ _ Hq Hr NE); subst old on; lia.
  - destruct (DJN _ _ Hq NE); lia.
Qed.

Lemma rl_regions_wf : rregions_wf st2.
Proof using AGA CPY DJN Fpf HG Hr Kr MC3 MR MU3 NB0 NBAL NC ND NDAL ON0 ONLYG PF RFN Sb st1. pin_using (fun (AGA CPY DJN Fpf HG Hr Kr MC3 MR MU3 NB0 NBAL NC ND NDAL ON0 ONLYG PF RFN Sb st1 : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  unfold rregions_wf. rewrite rl_reserved, rl_areas, rl_groups.
  split; [exact RS|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rl_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + cbn [r_base r_len]. rewrite (round_up_pg_id' needed) by exact NDAL. repeat split; try lia. exact RFN.
    + exact (WR q rq H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (rl_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rl_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r_kind]. rewrite (round_up_pg_id' needed) by exact NDAL. unfold lr_lo at 2. cbn [r_kind r_base]. rewrite Kr.
      pose proof (DJN q2 r2 H2' NE2). lia.
    + cbn [r_base r_len r_kind]. rewrite (round_up_pg_id' needed) by exact NDAL. unfold lr_lo at 1. cbn [r_kind r_base]. rewrite Kr.
      pose proof (DJN q1 r1 H1' NE1). lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST). destruct (rl_area_far a ar Ha) as (ra' & _ & NE & _).
    exists ra. rewrite rl_lookup_old by exact NE. auto.
  - intros b' gh Hb. destruct (aptr_eq_dec b' b) as [->|NEb].
    + exists (mkRegion (r_kind r) nb needed). fold rid. rewrite rl_lookup_new. cbn [r_kind r_len]. rewrite (round_up_pg_id' needed) by exact NDAL.
      rewrite Sb. repeat split; auto; try lia.
    + destruct (WG b' gh Hb) as (rb & Hrb & REST). destruct (rl_group_far b' gh Hb NEb) as (rb' & _ & NE & _).
      exists rb. rewrite rl_lookup_old by exact NE. auto.
Qed.

(* [comment removed for export] *)
Lemma rl_agree13 A n :
  0 <= A -> 0 <= n -> (A + n <= old \/ old + on <= A) -> (A + n <= nb \/ nb + needed <= A) -> A + n <= alloc_ceiling ->
  (forall a, A <= a < A + n -> ~ (G + 16 <= a < G + 24) /\ ~ (G + 32 <= a < G + 40)) ->
  agree_on m1 m3 A n.
Proof using AGA Fpf HG MC3 MSECV MU3 NB0 ND PF TLSFACTS. pin_using (fun (AGA Fpf HG MC3 MSECV MU3 NB0 ND PF TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros A0 N0 DO DN AC DG a Ha. ceil_facts.
  rewrite <- (AGA A n A0 N0 DO DN ltac:(ceil_facts; lia) a Ha).
  apply (munch_agree _ _ _ (fun x => ~ (G + 16 <= x < G + 24) /\ ~ (G + 32 <= x < G + 40)) A n MU3); [| exact DG| lia| lia| exact Ha].
  intros lo hi x [E|[E|[]]] Hx; inversion E; subst; tauto.
Qed.

Lemma rl_TC A cs :
  rw_cells ssegs m1 A cs -> 0 <= A -> (A + Z.of_nat (cells_size cs) <= old \/ old + on <= A) -> (A + Z.of_nat (cells_size cs) <= nb \/ nb + needed <= A) ->
  A + Z.of_nat (cells_size cs) <= alloc_ceiling ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ (G + 16 <= a < G + 24) /\ ~ (G + 32 <= a < G + 40)) ->
  rw_cells ssegs m3 A cs.
Proof using AGA Fpf HG MC3 MSECV MU3 NB0 ND PF TLSFACTS. pin_using (fun (AGA Fpf HG MC3 MSECV MU3 NB0 ND PF TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros H A0 DO DN AC DG. eapply rrw_cells_agree; [exact H|]. apply rl_agree13; auto; lia. Qed.

(* [comment removed for export] *)
Lemma rl_gslot : exists ag arg kg rag,
  (s_areas st) !! ag = Some arg /\ 0 <= kg < NSLOTS /\ g = aadd ag (AREA_HDR + META_SIZE * kg)
  /\ (s_regions st) !! (fst ag) = Some rag /\ fst ag <> rid /\ conc st ag = r_base rag + snd ag
  /\ G = conc st ag + AREA_HDR + META_SIZE * kg
  /\ 0 <= snd ag /\ snd ag + 4096 <= round_up_pg (r_len rag) /\ 0 < r_base rag /\ r_base rag + round_up_pg (r_len rag) <= alloc_ceiling
  /\ (r_base rag + snd ag + 4096 <= old \/ old + on <= r_base rag + snd ag)
  /\ (r_base rag + snd ag + 4096 <= nb \/ nb + needed <= r_base rag + snd ag)
  /\ ranges_free ref_reserved (r_base rag) (round_up_pg (r_len rag)) = true.
Proof using AGA CPY DJN Fpf HG Hr Kr MC3 MR MSg MU3 NB0 ND ON0 PF. pin_using (fun (AGA CPY DJN Fpf HG Hr Kr MC3 MR MSg MU3 NB0 ND ON0 PF : unit) => tt). ceil_facts. msec_facts.
  destruct MSg as (ag & arg & kg & Hag & Hkg & Eg).
  destruct (rl_area_far ag arg Hag) as (rag & Hrag & NE & Cag & S0 & S1 & B0 & BC & DO & DN).
  pose proof MR as (WF & _). pose proof WF as (RS & WR & _). destruct (WR _ _ Hrag) as (_ & _ & _ & _ & RF).
  exists ag, arg, kg, rag. repeat (split; [assumption|]).
  split. { rewrite <- HG, Eg. rewrite conc_aadd by (rewrite Hrag; eauto). lia. }
  repeat (split; [assumption|]). exact RF.
Qed.

(* [comment removed for export] *)
Lemma rl_img A n : 0x22000 <= A -> 0 <= n -> A + n <= 0x55000 -> agree_on m1 m3 A n.
Proof using AGA CPY DJN Fpf HG Hr Kr MC3 MR MSg MU3 NB0 ND ON0 PF RFN TLSFACTS. pin_using (fun (AGA CPY DJN Fpf HG Hr Kr MC3 MR MSg MU3 NB0 ND ON0 PF RFN TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros HA Hn HB. destruct rl_old_facts as (O0 & OAL & OC & ORF & ONN).
  pose proof (rreserved_disjoint _ _ ORF) as (_ & _ & D3 & D4). pose proof (rreserved_disjoint _ _ RFN) as (_ & _ & E3 & E4). pose proof ON0 as ONpos.
  destruct rl_gslot as (ag & arg & kg & rag & Hag & Hkg & Eg & Hrag & NEg & Cag & EG & S0 & S1 & B0 & BC & _ & _ & RFg).
  pose proof (rreserved_disjoint _ _ RFg) as (_ & _ & G3 & G4). pose proof (round_up_pg_ge (r_len rag)).
  unfold AREA_HDR, META_SIZE, NSLOTS in *; ceil_facts.
  apply rl_agree13; [lia| lia| lia| lia| ceil_facts; lia|]. intros a Ha. split; lia.
Qed.

(* [comment removed for export] *)
Lemma rl_pw p : optr_in (fun x => x <> rid) p -> pw st2 p = pw st p.
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite rl_conc by exact H|]; reflexivity. Qed.

Lemma rl_meta_cells_other q : q <> g -> meta_cells st2 (get_meta_rec st2 q) = meta_cells st (get_meta_rec st q).
Proof using CEILV Hr MEMG MSECV PTX st1. pin_using (fun (CEILV Hr MEMG MSECV PTX st1 : unit) => tt). ceil_facts. msec_facts.
  intros NE. rewrite rl_meta_other by exact NE.
  destruct PTX as (_ & _ & _ & _ & _ & _ & _ & P8 & _ & _). destruct (P8 q) as [X1 X2].
  unfold meta_cells. rewrite (rl_pw _ X1), (rl_pw _ X2). f_equal. f_equal. f_equal.
  destruct (m_mem (get_meta_rec st q)) as [b''|] eqn:MB; [| reflexivity].
  rewrite rl_pw; [reflexivity|]. cbn. intros E. apply NE. exact (MEMG q b'' MB E).
Qed.

Lemma rl_meta_cells_g : meta_cells st2 (get_meta_rec st2 g) =
  [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz nb); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr'))].
Proof using CEILV Hmem Hr MSECV PTX Sb st1. pin_using (fun (CEILV Hmem Hr MSECV PTX Sb st1 : unit) => tt). ceil_facts. msec_facts.
  rewrite rl_meta_same. destruct PTX as (_ & _ & _ & _ & _ & _ & _ & P8 & _ & _). destruct (P8 g) as [X1 X2].
  unfold meta_cells. unfold mr', mr in *. cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen].
  rewrite (rl_pw _ X1), (rl_pw _ X2). rewrite Hmem. unfold pw, oconc. rewrite rl_conc_new by reflexivity. rewrite Sb, Z.add_0_r. reflexivity.
Qed.

Theorem rl_rmrep : rmrep st2 m3 /\ ticks_ok st2.
Proof using AGA CPY DJN Fpf HG Hgh Hmem Hr Kr MC3 MEMG MR MSg MU3 NB0 NBAL NC ND NDAL NOK ON0 ONLYG PF PTX RFN Sb TK WM3 WRN st1. pin_using (fun (AGA CPY DJN Fpf HG Hgh Hmem Hr Kr MC3 MEMG MR MSg MU3 NB0 NBAL NC ND NDAL NOK ON0 ONLYG PF PTX RFN Sb TK WM3 WRN st1 : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct rl_old_facts as (O0 & OAL & OC & ORF & ONN).
  destruct rl_gslot as (ag & arg & kg & rag & Hag & Hkg & Eg & Hrag & NEg & Cag & EG & Sg0 & Sg1 & Bg0 & BgC & DgO & DgN & RFg).
  pose proof (round_up_pg_ge (r_len rag)) as RUg.
  destruct PTX as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  split.
  2:{ (* [comment removed for export] *)
      unfold ticks_ok. rewrite rl_sshadow, rl_tick. exact TK. }
  split; [exact rl_regions_wf|]. split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *)
    assert (E1 : ctx_head_cells st2 = ctx_head_cells st).
    { unfold ctx_head_cells. rewrite rl_ctx. rewrite !rl_pw by assumption. reflexivity. }
    assert (E2 : actives st2 = actives st).
    { unfold actives. apply map_ext. intros a. unfold active. rewrite rl_ctx. apply rl_pw. apply (P6 (Z.of_nat a)). }
    assert (E3 : usages st2 = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite rl_ctx. reflexivity. }
    assert (E4 : unmap_seqs st2 = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite rl_ctx. reflexivity. }
    assert (E5 : bouncess st2 = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite rl_ctx. reflexivity. }
    assert (E6 : ctx_tail_cells st2 = ctx_tail_cells st).
    { unfold ctx_tail_cells, brk_word. rewrite rl_ctx. destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity.
      rewrite (rl_conc (brid, boff)) by exact P7. reflexivity. }
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx. rewrite E1, E2, E3, E4, E5, E6.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite length_map, length_seq; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite length_map, length_seq; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite length_map, length_seq; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite length_map, length_seq; reflexivity).
    pose proof (rl_img RLIBC 0x418 ltac:(unfold RLIBC; lia) ltac:(lia) ltac:(unfold RLIBC; lia)) as AGC. unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - (* [comment removed for export] *)
    destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (eapply rrw_cells_agree; [eassumption|]; apply rl_img; cbn; lia).
  - (* [comment removed for export] *)
    intros a ar Ha. rewrite rl_areas in Ha.
    destruct (rl_area_far a ar Ha) as (ra & Hra & NEa & Ca & Sa0 & Sa1 & Ba0 & BaC & DaO & DaN). pose proof (round_up_pg_ge (r_len ra)) as RUa.
    destruct (AR a ar Ha) as (HD & SL & PD). destruct (P9 a ar Ha) as [_ Pn].
    (* [comment removed for export] *)
    assert (PG : a = ag \/ (conc st a + 4096 <= conc st ag \/ conc st ag + 4096 <= conc st a)).
    { destruct (aptr_eq_dec a ag) as [->|NE]; [left; reflexivity| right].
      rewrite Ca, Cag. destruct (N.eq_dec (fst a) (fst ag)) as [E|NE2].
      - rewrite E, Hrag in Hra. inversion Hra; subst ra.
        assert (snd a <> snd ag) by (intros E2; apply NE; destruct a, ag; cbn in *; congruence).
        destruct (rarea_conc st a ar WF Ha) as (ra2 & _ & _ & _ & _ & SaL & _). destruct (rarea_conc st ag arg WF Hag) as (rg2 & _ & _ & _ & _ & SgL & _).
        Z.div_mod_to_equations. nia.
      - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st ag arg rag WF Hag Hrag).
        destruct (DJ (fst a) ra (fst ag) rag Hra Hrag NE2); lia. }
    unfold rarea_rep. rewrite (rl_conc a NEa), (rl_pw _ Pn).
    split; [|split].
    + apply (rl_TC _ _ HD); cbn [cells_size csize Nat.add length]; try lia. intros x Hx. rewrite EG. unfold AREA_HDR, META_SIZE, NSLOTS in *. destruct PG as [->|PG]; lia.
    + intros k Hk. destruct (aptr_eq_dec (aadd a (AREA_HDR + META_SIZE * k)) g) as [Ek|NEk].
      * rewrite Ek, rl_meta_cells_g. replace (conc st a + AREA_HDR + META_SIZE * k) with G; [exact MC3|].
        rewrite <- HG, <- Ek. rewrite conc_aadd by (rewrite Hra; eauto). lia.
      * rewrite (rl_meta_cells_other _ NEk). apply (rl_TC _ _ (SL k Hk)); unfold meta_cells; cbn [cells_size csize Nat.add length]; unfold AREA_HDR, META_SIZE, NSLOTS in *; try lia.
        intros x Hx. rewrite EG. destruct PG as [->|PG]; [| lia].
        assert (k <> kg) by (intros ->; apply NEk; rewrite Eg; reflexivity). nia.
    + apply (rl_TC _ _ PD); cbn [cells_size csize Nat.add length]; try lia. intros x Hx. rewrite EG. unfold AREA_HDR, META_SIZE, NSLOTS in *. destruct PG as [->|PG]; lia.
  - (* [comment removed for export] *)
    intros b' gh Hb. rewrite rl_groups in Hb. pose proof (P10 b' gh Hb) as Pg.
    destruct (aptr_eq_dec b' b) as [->|NEb].
    + (* [comment removed for export] *)
      destruct (GR b _ Hgh) as (w8 & R & Hw8). rewrite Hgh in Hb. inversion Hb; subst gh. exists w8. split; [|exact Hw8].
      rewrite rl_conc_new by reflexivity. rewrite (rl_pw _ Pg). rewrite Sb, Z.add_0_r.
      destruct (rgroup_conc st b _ WF Hgh) as (rb & Hrb & Cb & _). fold rid in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
      rewrite Cb, Sb, Z.add_0_r in R. fold old in R.
      destruct R as [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
      * cbn [cells_bytes cbytes app] in HB |- *. destruct HB as (B0 & B1 & B2). split; [lia|]. split; [cbn in B1 |- *; ceil_facts; lia|].
        intros i Hi. cbn in Hi. rewrite <- (B2 i Hi). unfold mrd.
        rewrite <- (CPY (Z.of_nat i)) by lia.
        assert (AG : agree_on mA m3 (nb + Z.of_nat i) 1).
        { apply (munch_agree _ _ _ (fun x => ~ (G + 16 <= x < G + 24) /\ ~ (G + 32 <= x < G + 40)) _ 1 MU3); [| | lia| ceil_facts; lia].
          - intros lo hi x [E|[E|[]]] Hx; inversion E; subst; tauto.
          - intros x Hx. rewrite EG, Cag. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
        rewrite <- (AG (nb + Z.of_nat i)) by lia.
        destruct (m3 (wa (nb + Z.of_nat i))); [reflexivity|].
        pose proof (rreserved_disjoint1 _ _ ORF ON0) as OI. pose proof (rreserved_disjoint1 _ _ RFN ltac:(lia)) as NI. ceil_facts.
        rewrite !ref_seg_rom_none by (rewrite wa_unsigned by lia; lia). reflexivity.
      * cbn [cells_size csize Nat.add] in HW |- *. eapply wr_at_transport; [| exact WM3].
        destruct WRN as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
    + destruct (rl_group_far b' gh Hb NEb) as (rb & Hrb & NE & Cb & Kb & Sb0 & Sb1 & Bb0 & BbC & DbO & DbN).
      destruct (GR b' gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
      rewrite (rl_conc b' NE), (rl_pw _ Pg). apply (rl_TC _ _ R); cbn [cells_size csize Nat.add length]; try lia.
      intros x Hx. rewrite EG, Cag.
      assert (NE2 : fst b' <> fst ag). { intros E. rewrite E, Hrag in Hrb. inversion Hrb; subst. destruct (rarea_conc st ag arg WF Hag) as (r2 & Hr2 & _ & _ & _ & _ & NK & _). rewrite Hrag in Hr2. inversion Hr2; subst. exact (NK Kb). }
      pose proof (rarea_lr_lo st ag arg rag WF Hag Hrag). pose proof (lr_lo_group rb Kb). unfold AREA_HDR, META_SIZE, NSLOTS in *.
      destruct (DJ (fst b') rb (fst ag) rag Hrb Hrag NE2); lia.
  - (* [comment removed for export] *)
    intros q rq Hq Kq. unfold rshadow_rep. rewrite rl_shadow.
    destruct (rl_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + (* [comment removed for export] *)
      cbn [r_base r_len]. rewrite (round_up_pg_id' needed) by exact NDAL. split.
      * eapply wr_at_transport; [exact WRN| exact WM3].
      * intros o v Ho Hc. fold rid in Hc.
        assert (OLO : o < snd pf). { destruct (Z.lt_ge_cases o (snd pf)); [assumption|]. exfalso. exact (NOK o v ltac:(lia) Hc). }
        destruct (SH rid r Hr Kr) as [_ HB]. destruct (HB o v ltac:(subst on; lia) Hc) as [Bt Hv]. split; [|exact Hv].
        destruct Bt as (B0 & B1 & B2). split; [lia|]. split; [cbn; ceil_facts; lia|].
        intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. specialize (B2 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B2. cbn [nth_error] in B2.
        unfold mrd in B2 |- *. fold old in B2. rewrite <- B2. rewrite <- (CPY o) by lia.
        assert (AG : agree_on mA m3 (nb + o) 1).
        { apply (munch_agree _ _ _ (fun x => ~ (G + 16 <= x < G + 24) /\ ~ (G + 32 <= x < G + 40)) _ 1 MU3); [| | lia| ceil_facts; lia].
          - intros lo hi x [E|[E|[]]] Hx; inversion E; subst; tauto.
          - intros x Hx. rewrite EG, Cag. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
        rewrite <- (AG (nb + o)) by lia.
        destruct (m3 (wa (nb + o))); [reflexivity|].
        pose proof (rreserved_disjoint1 _ _ ORF ON0) as OI. pose proof (rreserved_disjoint1 _ _ RFN ltac:(lia)) as NI. ceil_facts.
        rewrite !ref_seg_rom_none by (rewrite wa_unsigned by lia; lia). reflexivity.
    + destruct (rl_greg_far q rq H NE Kq) as (Bq0 & BqC & DqO & DqN).
      destruct (SH q rq H Kq) as [HWr HB]. pose proof (round_up_pg_ge (r_len rq)) as RUq. destruct (WR _ _ H) as (_ & _ & Lq0 & _ & _).
      assert (AG : agree_on m1 m3 (r_base rq) (round_up_pg (r_len rq))).
      { apply rl_agree13; [lia| lia| lia| lia| lia|]. intros x Hx. rewrite EG, Cag.
        assert (NE2 : q <> fst ag). { intros E. subst q. rewrite Hrag in H. inversion H; subst. destruct (rarea_conc st ag arg WF Hag) as (r2 & Hr2 & _ & _ & _ & _ & NK & _). rewrite Hrag in Hr2. inversion Hr2; subst. exact (NK Kq). }
        pose proof (rarea_lr_lo st ag arg rag WF Hag Hrag). pose proof (lr_lo_group rq Kq). unfold AREA_HDR, META_SIZE, NSLOTS in *.
        destruct (DJ q rq (fst ag) rag H Hrag NE2); lia. }
      split; [eapply rwr_at_agree; [exact HWr| exact AG]|].
      intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.
End RELOC.
(* [comment removed for export] *)
Lemma rptrs_ctx_norid st2 LB c rid r m :
  KINV st2 LB c -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  ci_mptrs st2 ->
  ptrs_ctx_in (fun x => x <> rid) st2.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros K MR Hr Kr (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_ctx_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split.
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb.
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

(* [comment removed for export] *)
Lemma rmem_only st LB rid b g ai :
  CINV st LB -> (s_groups st) !! b = Some (mkGhdr (Some g) ai) ->
  (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = rid -> b' = b) ->
  forall q b'', m_mem (get_meta_rec st q) = Some b'' -> fst b'' = rid -> q = g.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros C Hgh ONLY q b'' MB E. destruct (ZINV_of_CINV _ _ C q b'' MB) as [[ai' Hb'']|[]].
  pose proof (ONLY _ _ Hb'' E) as ->. rewrite Hgh in Hb''. inversion Hb''. reflexivity.
Qed.

Lemma put_meta_same st g mr : (s_metas st) !! g = Some mr -> put_meta g mr st = st.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros H. unfold put_meta. rewrite insert_id by exact H. destruct st; reflexivity. Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Definition ptrs_ctx_in (P : N -> Prop) (st : mstate) : Prop :=
  let c := ctx st in
  optr_in P (c_free_meta_head c) /\ optr_in P (c_avail_meta c) /\ optr_in P (c_meta_area_head c)
  /\ optr_in P (c_meta_area_tail c) /\ optr_in P (c_avail_meta_areas c)
  /\ (forall sc, optr_in P (active st sc))
  /\ match c_brk c with BrkLive rid _ => P rid | _ => True end
  /\ (forall q, optr_in P (m_prev (get_meta_rec st q)) /\ optr_in P (m_next (get_meta_rec st q)))
  /\ (forall a ar, (s_areas st) !! a = Some ar -> P (fst a) /\ optr_in P (a_next ar))
  /\ (forall b gh, (s_groups st) !! b = Some gh -> optr_in P (g_meta gh)).

Lemma round_up_pg_id' x : x mod 4096 = 0 -> round_up_pg x = x.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros H. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. Z.div_mod_to_equations. lia. Qed.

Section RELOC.
Variables (st : mstate) (m1 mA m3 : mem) (g b pf : aptr) (ai : Z) (r : region) (nb needed G : Z).
Let rid := fst b.
Let mr := get_meta_rec st g.
Let old := r_base r.
Let on := round_up_pg (r_len r).
Let mr' := m_set_maplen (needed / 4096) mr.
Let st1 := upd_region rid (fun rg => mkRegion (r_kind rg) nb needed) st.
Let st2 := upd_meta g (m_set_maplen (needed / 4096)) st1.

Hypothesis MR : rmrep st m1.
Hypothesis TK : ticks_ok st.
Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis Kr : r_kind r = RKGroup.
Hypothesis Hgh : (s_groups st) !! b = Some (mkGhdr (Some g) ai).
Hypothesis Sb : snd b = 0.
Hypothesis ONLYG : forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = rid -> b' = b.
Hypothesis MEMG : forall q b'', m_mem (get_meta_rec st q) = Some b'' -> fst b'' = rid -> q = g.
Hypothesis MSg : meta_slot st g.
Hypothesis HG : conc st g = G.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis PTX : ptrs_ctx_in (fun x => x <> rid) st.
Hypothesis Fpf : fst pf = rid.
Hypothesis PF : 16 <= snd pf /\ snd pf <= on /\ snd pf + 4 <= needed.
Hypothesis NOK : forall o v, snd pf <= o < needed -> cell_read (get_shadow st rid) o = Known v -> False.
Hypothesis ON0 : 0 < on.
Hypothesis NB0 : 0 < nb.
Hypothesis NBAL : nb mod 4096 = 0.
Hypothesis ND : 4096 <= needed.
Hypothesis NDAL : needed mod 4096 = 0.
Hypothesis NC : nb + needed <= alloc_ceiling.
Hypothesis RFN : ranges_free ref_reserved nb needed = true.
Hypothesis DJN : forall rid' r', (s_regions st) !! rid' = Some r' -> rid' <> rid ->
  nb + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb.
(* [comment removed for export] *)
Hypothesis AGA : forall A n, 0 <= A -> 0 <= n -> (A + n <= old \/ old + on <= A) -> (A + n <= nb \/ nb + needed <= A) ->
  A + n <= alloc_ceiling -> agree_on m1 mA A n.
Hypothesis CPY : forall o, 0 <= o < snd pf -> mA (wa (nb + o)) = m1 (wa (old + o)).
Hypothesis WRN : wr_at usegs mA nb needed.
Hypothesis MU3 : munch [(G + 16, G + 24); (G + 32, G + 40)]%Z mA m3.
Hypothesis WM3 : wmono usegs mA m3.
Hypothesis MC3 : rw_cells usegs m3 G [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz nb); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr'))].

(* [comment removed for export] *)
Lemma rl_regions : s_regions st2 = <[rid := mkRegion (r_kind r) nb needed]> (s_regions st).
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_lookup_new : (s_regions st2) !! rid = Some (mkRegion (r_kind r) nb needed).
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. rewrite rl_regions. apply lookup_insert_eq. Qed.
Lemma rl_lookup_old q : q <> rid -> (s_regions st2) !! q = (s_regions st) !! q.
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. intros. rewrite rl_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
Lemma rl_lookup_inv q rq : (s_regions st2) !! q = Some rq -> (q = rid /\ rq = mkRegion (r_kind r) nb needed) \/ (q <> rid /\ (s_regions st) !! q = Some rq).
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts.
  intros H. destruct (N.eq_dec q rid) as [->|NE].
  - left. rewrite rl_lookup_new in H. inversion H. auto.
  - right. rewrite rl_lookup_old in H by exact NE. auto.
Qed.
Lemma rl_conc q : fst q <> rid -> conc st2 q = conc st q.
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. intros. unfold conc, get_region. rewrite rl_lookup_old by assumption. reflexivity. Qed.
Lemma rl_conc_new q : fst q = rid -> conc st2 q = nb + snd q.
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. intros E. unfold conc, get_region. rewrite E, rl_lookup_new. reflexivity. Qed.
Lemma rl_areas : s_areas st2 = s_areas st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_groups : s_groups st2 = s_groups st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_ctx : ctx st2 = ctx st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_reserved : s_reserved st2 = s_reserved st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_shadow q : get_shadow st2 q = get_shadow st q. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_tick : s_tick st2 = s_tick st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_sshadow : s_shadow st2 = s_shadow st. Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. unfold st2, st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_meta1 q : get_meta_rec st1 q = get_meta_rec st q.
Proof using CEILV Hr MSECV nb needed. pin_using (fun (CEILV Hr MSECV nb needed : unit) => tt). ceil_facts. msec_facts. unfold st1, upd_region, get_region. rewrite Hr. reflexivity. Qed.
Lemma rl_meta_same : get_meta_rec st2 g = mr'.
Proof using CEILV Hr MSECV mr st1. pin_using (fun (CEILV Hr MSECV mr st1 : unit) => tt). ceil_facts. msec_facts. unfold st2. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.get_meta_rec_upd_same, rl_meta1. reflexivity. Qed.
Lemma rl_meta_other q : q <> g -> get_meta_rec st2 q = get_meta_rec st q.
Proof using CEILV Hr MSECV st1. pin_using (fun (CEILV Hr MSECV st1 : unit) => tt). ceil_facts. msec_facts. intros NE. unfold st2. rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.get_meta_rec_upd_other by exact NE. apply rl_meta1. Qed.

(* [comment removed for export] *)
Lemma rl_old_facts : 0 < old /\ old mod 4096 = 0 /\ old + on <= alloc_ceiling /\ ranges_free ref_reserved old on = true /\ 0 <= on.
Proof using Fpf Hr MR ON0 nb needed. pin_using (fun (Fpf Hr MR ON0 nb needed : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG). destruct (WR _ _ Hr) as (B0 & BAL & L0 & BC & RF).
  pose proof (round_up_pg_ge (r_len r)). subst old on. repeat split; auto; lia.
Qed.

Lemma rl_area_far a ar : (s_areas st) !! a = Some ar ->
  exists ra, (s_regions st) !! (fst a) = Some ra /\ fst a <> rid /\ conc st a = r_base ra + snd a
    /\ 0 <= snd a /\ snd a + 4096 <= round_up_pg (r_len ra) /\ 0 < r_base ra /\ r_base ra + round_up_pg (r_len ra) <= alloc_ceiling
    /\ (r_base ra + snd a + 4096 <= old \/ old + on <= r_base ra + snd a)
    /\ (r_base ra + snd a + 4096 <= nb \/ nb + needed <= r_base ra + snd a).
Proof using AGA CPY DJN Fpf HG Hr Kr MC3 MR MU3 NB0 ND ON0 PF TLSFACTS. pin_using (fun (AGA CPY DJN Fpf HG Hr Kr MC3 MR MU3 NB0 ND ON0 PF TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Ha. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC).
  assert (NE : fst a <> rid). { intros E. rewrite E in Hra. fold rid in Hr. rewrite Hr in Hra. inversion Hra; subst. exact (NK Kr). }
  pose proof (rarea_lr_lo st a ar ra WF Ha Hra) as LL. pose proof (lr_lo_group r Kr) as LR.
  exists ra. repeat (split; [first [exact Hra| exact NE| exact Ca| exact Sa0| exact Sa1| exact RB0| exact RBC] |]).
  split.
  - fold rid in Hr. destruct (DJ _ _ _ _ Hra Hr NE); subst old on; lia.
  - destruct (DJN _ _ Hra NE); lia.
Qed.

Lemma rl_group_far b' gh : (s_groups st) !! b' = Some gh -> b' <> b ->
  exists rb, (s_regions st) !! (fst b') = Some rb /\ fst b' <> rid /\ conc st b' = r_base rb + snd b' /\ r_kind rb = RKGroup
    /\ 0 <= snd b' /\ snd b' + 16 <= round_up_pg (r_len rb) /\ 0 < r_base rb /\ r_base rb + round_up_pg (r_len rb) <= alloc_ceiling
    /\ (r_base rb + round_up_pg (r_len rb) <= old \/ old + on <= r_base rb)
    /\ (r_base rb + round_up_pg (r_len rb) <= nb \/ nb + needed <= r_base rb).
Proof using DJN Fpf Hr Kr MR NB0 ND ONLYG TLSFACTS. pin_using (fun (DJN Fpf Hr Kr MR NB0 ND ONLYG TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hb NEb. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rgroup_conc st b' gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & SbA & RB0 & RBC).
  assert (NE : fst b' <> rid). { intros E. apply NEb. exact (ONLYG _ _ Hb E). }
  pose proof (lr_lo_group rb Kb) as LL. pose proof (lr_lo_group r Kr) as LR.
  exists rb. repeat (split; [first [exact Hrb| exact NE| exact Cb| exact Kb| exact Sb0| exact Sb1| exact RB0| exact RBC] |]).
  split.
  - fold rid in Hr. destruct (DJ _ _ _ _ Hrb Hr NE); subst old on; lia.
  - destruct (DJN _ _ Hrb NE); lia.
Qed.

Lemma rl_greg_far q rq : (s_regions st) !! q = Some rq -> q <> rid -> r_kind rq = RKGroup ->
  0 < r_base rq /\ r_base rq + round_up_pg (r_len rq) <= alloc_ceiling
  /\ (r_base rq + round_up_pg (r_len rq) <= old \/ old + on <= r_base rq)
  /\ (r_base rq + round_up_pg (r_len rq) <= nb \/ nb + needed <= r_base rq).
Proof using DJN Fpf Hr Kr MR NB0 ND TLSFACTS. pin_using (fun (DJN Fpf Hr Kr MR NB0 ND TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hq NE Kq. pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (WR _ _ Hq) as (B0 & _ & _ & BC & _). pose proof (lr_lo_group rq Kq). pose proof (lr_lo_group r Kr).
  split; [exact B0|]. split; [exact BC|]. split.
  - fold rid in Hr. destruct (DJ _ _ _ _ Hq Hr NE); subst old on; lia.
  - destruct (DJN _ _ Hq NE); lia.
Qed.

Lemma rl_regions_wf : rregions_wf st2.
Proof using AGA CPY DJN Fpf HG Hr Kr MC3 MR MU3 NB0 NBAL NC ND NDAL ON0 ONLYG PF RFN Sb st1. pin_using (fun (AGA CPY DJN Fpf HG Hr Kr MC3 MR MU3 NB0 NBAL NC ND NDAL ON0 ONLYG PF RFN Sb st1 : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  unfold rregions_wf. rewrite rl_reserved, rl_areas, rl_groups.
  split; [exact RS|]. split; [|split; [|split]].
  - intros q rq Hq. destruct (rl_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + cbn [r_base r_len]. rewrite (round_up_pg_id' needed) by exact NDAL. repeat split; try lia. exact RFN.
    + exact (WR q rq H).
  - intros q1 r1 q2 r2 H1 H2 NE.
    destruct (rl_lookup_inv q1 r1 H1) as [[-> ->]|[NE1 H1']]; destruct (rl_lookup_inv q2 r2 H2) as [[-> ->]|[NE2 H2']].
    + congruence.
    + cbn [r_base r_len r_kind]. rewrite (round_up_pg_id' needed) by exact NDAL. unfold lr_lo at 2. cbn [r_kind r_base]. rewrite Kr.
      pose proof (DJN q2 r2 H2' NE2). lia.
    + cbn [r_base r_len r_kind]. rewrite (round_up_pg_id' needed) by exact NDAL. unfold lr_lo at 1. cbn [r_kind r_base]. rewrite Kr.
      pose proof (DJN q1 r1 H1' NE1). lia.
    + exact (DJ q1 r1 q2 r2 H1' H2' NE).
  - intros a ar Ha. destruct (WA a ar Ha) as (ra & Hra & REST). destruct (rl_area_far a ar Ha) as (ra' & _ & NE & _).
    exists ra. rewrite rl_lookup_old by exact NE. auto.
  - intros b' gh Hb. destruct (aptr_eq_dec b' b) as [->|NEb].
    + exists (mkRegion (r_kind r) nb needed). fold rid. rewrite rl_lookup_new. cbn [r_kind r_len]. rewrite (round_up_pg_id' needed) by exact NDAL.
      rewrite Sb. repeat split; auto; try lia.
    + destruct (WG b' gh Hb) as (rb & Hrb & REST). destruct (rl_group_far b' gh Hb NEb) as (rb' & _ & NE & _).
      exists rb. rewrite rl_lookup_old by exact NE. auto.
Qed.

(* [comment removed for export] *)
Lemma rl_agree13 A n :
  0 <= A -> 0 <= n -> (A + n <= old \/ old + on <= A) -> (A + n <= nb \/ nb + needed <= A) -> A + n <= alloc_ceiling ->
  (forall a, A <= a < A + n -> ~ (G + 16 <= a < G + 24) /\ ~ (G + 32 <= a < G + 40)) ->
  agree_on m1 m3 A n.
Proof using AGA Fpf HG MC3 MSECV MU3 NB0 ND PF TLSFACTS. pin_using (fun (AGA Fpf HG MC3 MSECV MU3 NB0 ND PF TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros A0 N0 DO DN AC DG a Ha. ceil_facts.
  rewrite <- (AGA A n A0 N0 DO DN ltac:(ceil_facts; lia) a Ha).
  apply (munch_agree _ _ _ (fun x => ~ (G + 16 <= x < G + 24) /\ ~ (G + 32 <= x < G + 40)) A n MU3); [| exact DG| lia| lia| exact Ha].
  intros lo hi x [E|[E|[]]] Hx; inversion E; subst; tauto.
Qed.

Lemma rl_TC A cs :
  rw_cells usegs m1 A cs -> 0 <= A -> (A + Z.of_nat (cells_size cs) <= old \/ old + on <= A) -> (A + Z.of_nat (cells_size cs) <= nb \/ nb + needed <= A) ->
  A + Z.of_nat (cells_size cs) <= alloc_ceiling ->
  (forall a, A <= a < A + Z.of_nat (cells_size cs) -> ~ (G + 16 <= a < G + 24) /\ ~ (G + 32 <= a < G + 40)) ->
  rw_cells usegs m3 A cs.
Proof using AGA Fpf HG MC3 MSECV MU3 NB0 ND PF TLSFACTS. pin_using (fun (AGA Fpf HG MC3 MSECV MU3 NB0 ND PF TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros H A0 DO DN AC DG. eapply rrw_cells_agree; [exact H|]. apply rl_agree13; auto; lia. Qed.

(* [comment removed for export] *)
Lemma rl_gslot : exists ag arg kg rag,
  (s_areas st) !! ag = Some arg /\ 0 <= kg < NSLOTS /\ g = aadd ag (AREA_HDR + META_SIZE * kg)
  /\ (s_regions st) !! (fst ag) = Some rag /\ fst ag <> rid /\ conc st ag = r_base rag + snd ag
  /\ G = conc st ag + AREA_HDR + META_SIZE * kg
  /\ 0 <= snd ag /\ snd ag + 4096 <= round_up_pg (r_len rag) /\ 0 < r_base rag /\ r_base rag + round_up_pg (r_len rag) <= alloc_ceiling
  /\ (r_base rag + snd ag + 4096 <= old \/ old + on <= r_base rag + snd ag)
  /\ (r_base rag + snd ag + 4096 <= nb \/ nb + needed <= r_base rag + snd ag)
  /\ ranges_free ref_reserved (r_base rag) (round_up_pg (r_len rag)) = true.
Proof using AGA CPY DJN Fpf HG Hr Kr MC3 MR MSg MU3 NB0 ND ON0 PF. pin_using (fun (AGA CPY DJN Fpf HG Hr Kr MC3 MR MSg MU3 NB0 ND ON0 PF : unit) => tt). ceil_facts. msec_facts.
  destruct MSg as (ag & arg & kg & Hag & Hkg & Eg).
  destruct (rl_area_far ag arg Hag) as (rag & Hrag & NE & Cag & S0 & S1 & B0 & BC & DO & DN).
  pose proof MR as (WF & _). pose proof WF as (RS & WR & _). destruct (WR _ _ Hrag) as (_ & _ & _ & _ & RF).
  exists ag, arg, kg, rag. repeat (split; [assumption|]).
  split. { rewrite <- HG, Eg. rewrite conc_aadd by (rewrite Hrag; eauto). lia. }
  repeat (split; [assumption|]). exact RF.
Qed.

(* [comment removed for export] *)
Lemma rl_img A n : 0x22000 <= A -> 0 <= n -> A + n <= 0x56000 -> agree_on m1 m3 A n.
Proof using AGA CPY DJN Fpf HG Hr Kr MC3 MR MSg MU3 NB0 ND ON0 PF RFN TLSFACTS. pin_using (fun (AGA CPY DJN Fpf HG Hr Kr MC3 MR MSg MU3 NB0 ND ON0 PF RFN TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros HA Hn HB. destruct rl_old_facts as (O0 & OAL & OC & ORF & ONN).
  pose proof (rreserved_disjoint _ _ ORF) as (_ & _ & D3 & D4). pose proof (rreserved_disjoint _ _ RFN) as (_ & _ & E3 & E4). pose proof ON0 as ONpos.
  destruct rl_gslot as (ag & arg & kg & rag & Hag & Hkg & Eg & Hrag & NEg & Cag & EG & S0 & S1 & B0 & BC & _ & _ & RFg).
  pose proof (rreserved_disjoint _ _ RFg) as (_ & _ & G3 & G4). pose proof (round_up_pg_ge (r_len rag)).
  unfold AREA_HDR, META_SIZE, NSLOTS in *; ceil_facts.
  apply rl_agree13; [lia| lia| lia| lia| ceil_facts; lia|]. intros a Ha. split; lia.
Qed.

(* [comment removed for export] *)
Lemma rl_pw p : optr_in (fun x => x <> rid) p -> pw st2 p = pw st p.
Proof using CEILV Hr MSECV g st1. pin_using (fun (CEILV Hr MSECV g st1 : unit) => tt). ceil_facts. msec_facts. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite rl_conc by exact H|]; reflexivity. Qed.

Lemma rl_meta_cells_other q : q <> g -> meta_cells st2 (get_meta_rec st2 q) = meta_cells st (get_meta_rec st q).
Proof using CEILV Hr MEMG MSECV PTX st1. pin_using (fun (CEILV Hr MEMG MSECV PTX st1 : unit) => tt). ceil_facts. msec_facts.
  intros NE. rewrite rl_meta_other by exact NE.
  destruct PTX as (_ & _ & _ & _ & _ & _ & _ & P8 & _ & _). destruct (P8 q) as [X1 X2].
  unfold meta_cells. rewrite (rl_pw _ X1), (rl_pw _ X2). f_equal. f_equal. f_equal.
  destruct (m_mem (get_meta_rec st q)) as [b''|] eqn:MB; [| reflexivity].
  rewrite rl_pw; [reflexivity|]. cbn. intros E. apply NE. exact (MEMG q b'' MB E).
Qed.

Lemma rl_meta_cells_g : meta_cells st2 (get_meta_rec st2 g) =
  [C8 (pw st (m_prev mr)); C8 (pw st (m_next mr)); C8 (wz nb); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr'))].
Proof using CEILV Hmem Hr MSECV PTX Sb st1. pin_using (fun (CEILV Hmem Hr MSECV PTX Sb st1 : unit) => tt). ceil_facts. msec_facts.
  rewrite rl_meta_same. destruct PTX as (_ & _ & _ & _ & _ & _ & _ & P8 & _ & _). destruct (P8 g) as [X1 X2].
  unfold meta_cells. unfold mr', mr in *. cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen].
  rewrite (rl_pw _ X1), (rl_pw _ X2). rewrite Hmem. unfold pw, oconc. rewrite rl_conc_new by reflexivity. rewrite Sb, Z.add_0_r. reflexivity.
Qed.

Theorem rl_rmrep : rmrep st2 m3 /\ ticks_ok st2.
Proof using AGA CPY DJN Fpf HG Hgh Hmem Hr Kr MC3 MEMG MR MSg MU3 NB0 NBAL NC ND NDAL NOK ON0 ONLYG PF PTX RFN Sb TK WM3 WRN st1. pin_using (fun (AGA CPY DJN Fpf HG Hgh Hmem Hr Kr MC3 MEMG MR MSg MU3 NB0 NBAL NC ND NDAL NOK ON0 ONLYG PF PTX RFN Sb TK WM3 WRN st1 : unit) => tt). ceil_facts. msec_facts.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct rl_old_facts as (O0 & OAL & OC & ORF & ONN).
  destruct rl_gslot as (ag & arg & kg & rag & Hag & Hkg & Eg & Hrag & NEg & Cag & EG & Sg0 & Sg1 & Bg0 & BgC & DgO & DgN & RFg).
  pose proof (round_up_pg_ge (r_len rag)) as RUg.
  destruct PTX as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10).
  split.
  2:{ (* [comment removed for export] *)
      unfold ticks_ok. rewrite rl_sshadow, rl_tick. exact TK. }
  split; [exact rl_regions_wf|]. split; [|split; [|split; [|split]]].
  - (* [comment removed for export] *)
    assert (E1 : ctx_head_cells st2 = ctx_head_cells st).
    { unfold ctx_head_cells. rewrite rl_ctx. rewrite !rl_pw by assumption. reflexivity. }
    assert (E2 : actives st2 = actives st).
    { unfold actives. apply map_ext. intros a. unfold active. rewrite rl_ctx. apply rl_pw. apply (P6 (Z.of_nat a)). }
    assert (E3 : usages st2 = usages st). { unfold usages. apply map_ext. intros. unfold usage. rewrite rl_ctx. reflexivity. }
    assert (E4 : unmap_seqs st2 = unmap_seqs st). { unfold unmap_seqs. apply map_ext. intros. unfold unmap_seq. rewrite rl_ctx. reflexivity. }
    assert (E5 : bouncess st2 = bouncess st). { unfold bouncess. apply map_ext. intros. unfold bounces. rewrite rl_ctx. reflexivity. }
    assert (E6 : ctx_tail_cells st2 = ctx_tail_cells st).
    { unfold ctx_tail_cells, brk_word. rewrite rl_ctx. destruct (c_brk (ctx st)) as [| |brid boff]; try reflexivity.
      rewrite (rl_conc (brid, boff)) by exact P7. reflexivity. }
    destruct CX as (C1 & C2 & C3 & C4 & C5 & C6). unfold rmrep_ctx. rewrite E1, E2, E3, E4, E5, E6.
    assert (L1 : length (actives st) = 48%nat) by (unfold actives; rewrite length_map, length_seq; reflexivity).
    assert (L2 : length (usages st) = 48%nat) by (unfold usages; rewrite length_map, length_seq; reflexivity).
    assert (L3 : length (unmap_seqs st) = 32%nat) by (unfold unmap_seqs; rewrite length_map, length_seq; reflexivity).
    assert (L4 : length (bouncess st) = 32%nat) by (unfold bouncess; rewrite length_map, length_seq; reflexivity).
    pose proof (rl_img RLIBC 0x418 ltac:(unfold RLIBC; lia) ltac:(lia) ltac:(unfold RLIBC; lia)) as AGC. unfold RLIBC, RCTX in *.
    split; [|split; [|split; [|split; [|split]]]].
    + eapply rrw_cells_agree; [exact C1|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C2|]. rewrite L1. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru64arr_agree; [exact C3|]. rewrite L2. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C4|]. rewrite L3. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply ru8arr_agree; [exact C5|]. rewrite L4. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
    + eapply rrw_cells_agree; [exact C6|]. eapply agree_on_sub; [exact AGC| lia| cbn; lia].
  - (* [comment removed for export] *)
    destruct GL as (G1 & G2 & G3 & G4 & G5). unfold rmrep_globals, RMLOCK, RNEED_LOCKS, RPAGE_SIZE, RLIBC, RGOT_SSP, RSSP_GUARD in *.
    split; [|split; [|split; [|split]]]; (eapply rrw_cells_agree; [eassumption|]; apply rl_img; cbn; lia).
  - (* [comment removed for export] *)
    intros a ar Ha. rewrite rl_areas in Ha.
    destruct (rl_area_far a ar Ha) as (ra & Hra & NEa & Ca & Sa0 & Sa1 & Ba0 & BaC & DaO & DaN). pose proof (round_up_pg_ge (r_len ra)) as RUa.
    destruct (AR a ar Ha) as (HD & SL & PD). destruct (P9 a ar Ha) as [_ Pn].
    (* [comment removed for export] *)
    assert (PG : a = ag \/ (conc st a + 4096 <= conc st ag \/ conc st ag + 4096 <= conc st a)).
    { destruct (aptr_eq_dec a ag) as [->|NE]; [left; reflexivity| right].
      rewrite Ca, Cag. destruct (N.eq_dec (fst a) (fst ag)) as [E|NE2].
      - rewrite E, Hrag in Hra. inversion Hra; subst ra.
        assert (snd a <> snd ag) by (intros E2; apply NE; destruct a, ag; cbn in *; congruence).
        destruct (rarea_conc st a ar WF Ha) as (ra2 & _ & _ & _ & _ & SaL & _). destruct (rarea_conc st ag arg WF Hag) as (rg2 & _ & _ & _ & _ & SgL & _).
        Z.div_mod_to_equations. nia.
      - pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st ag arg rag WF Hag Hrag).
        destruct (DJ (fst a) ra (fst ag) rag Hra Hrag NE2); lia. }
    unfold rarea_rep. rewrite (rl_conc a NEa), (rl_pw _ Pn).
    split; [|split].
    + apply (rl_TC _ _ HD); cbn [cells_size csize Nat.add length]; try lia. intros x Hx. rewrite EG. unfold AREA_HDR, META_SIZE, NSLOTS in *. destruct PG as [->|PG]; lia.
    + intros k Hk. destruct (aptr_eq_dec (aadd a (AREA_HDR + META_SIZE * k)) g) as [Ek|NEk].
      * rewrite Ek, rl_meta_cells_g. replace (conc st a + AREA_HDR + META_SIZE * k) with G; [exact MC3|].
        rewrite <- HG, <- Ek. rewrite conc_aadd by (rewrite Hra; eauto). lia.
      * rewrite (rl_meta_cells_other _ NEk). apply (rl_TC _ _ (SL k Hk)); unfold meta_cells; cbn [cells_size csize Nat.add length]; unfold AREA_HDR, META_SIZE, NSLOTS in *; try lia.
        intros x Hx. rewrite EG. destruct PG as [->|PG]; [| lia].
        assert (k <> kg) by (intros ->; apply NEk; rewrite Eg; reflexivity). nia.
    + apply (rl_TC _ _ PD); cbn [cells_size csize Nat.add length]; try lia. intros x Hx. rewrite EG. unfold AREA_HDR, META_SIZE, NSLOTS in *. destruct PG as [->|PG]; lia.
  - (* [comment removed for export] *)
    intros b' gh Hb. rewrite rl_groups in Hb. pose proof (P10 b' gh Hb) as Pg.
    destruct (aptr_eq_dec b' b) as [->|NEb].
    + (* [comment removed for export] *)
      destruct (GR b _ Hgh) as (w8 & R & Hw8). rewrite Hgh in Hb. inversion Hb; subst gh. exists w8. split; [|exact Hw8].
      rewrite rl_conc_new by reflexivity. rewrite (rl_pw _ Pg). rewrite Sb, Z.add_0_r.
      destruct (rgroup_conc st b _ WF Hgh) as (rb & Hrb & Cb & _). fold rid in Hrb. rewrite Hr in Hrb. inversion Hrb; subst rb.
      rewrite Cb, Sb, Z.add_0_r in R. fold old in R.
      destruct R as [[Hwf HB] HW]. split; [split; [exact Hwf|]|].
      * cbn [cells_bytes cbytes app] in HB |- *. destruct HB as (B0 & B1 & B2). split; [lia|]. split; [cbn in B1 |- *; ceil_facts; lia|].
        intros i Hi. cbn in Hi. rewrite <- (B2 i Hi). unfold mrd.
        rewrite <- (CPY (Z.of_nat i)) by lia.
        assert (AG : agree_on mA m3 (nb + Z.of_nat i) 1).
        { apply (munch_agree _ _ _ (fun x => ~ (G + 16 <= x < G + 24) /\ ~ (G + 32 <= x < G + 40)) _ 1 MU3); [| | lia| ceil_facts; lia].
          - intros lo hi x [E|[E|[]]] Hx; inversion E; subst; tauto.
          - intros x Hx. rewrite EG, Cag. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
        rewrite <- (AG (nb + Z.of_nat i)) by lia.
        destruct (m3 (wa (nb + Z.of_nat i))); [reflexivity|].
        pose proof (rreserved_disjoint1 _ _ ORF ON0) as OI. pose proof (rreserved_disjoint1 _ _ RFN ltac:(lia)) as NI. ceil_facts.
        rewrite !ref_seg_rom_none by (rewrite wa_unsigned by lia; lia). reflexivity.
      * cbn [cells_size csize Nat.add] in HW |- *. eapply wr_at_transport; [| exact WM3].
        destruct WRN as (W0 & W1 & W2). split; [lia|]. split; [lia|]. intros i Hi. apply W2. lia.
    + destruct (rl_group_far b' gh Hb NEb) as (rb & Hrb & NE & Cb & Kb & Sb0 & Sb1 & Bb0 & BbC & DbO & DbN).
      destruct (GR b' gh Hb) as (w8 & R & Hw8). exists w8. split; [|exact Hw8].
      rewrite (rl_conc b' NE), (rl_pw _ Pg). apply (rl_TC _ _ R); cbn [cells_size csize Nat.add length]; try lia.
      intros x Hx. rewrite EG, Cag.
      assert (NE2 : fst b' <> fst ag). { intros E. rewrite E, Hrag in Hrb. inversion Hrb; subst. destruct (rarea_conc st ag arg WF Hag) as (r2 & Hr2 & _ & _ & _ & _ & NK & _). rewrite Hrag in Hr2. inversion Hr2; subst. exact (NK Kb). }
      pose proof (rarea_lr_lo st ag arg rag WF Hag Hrag). pose proof (lr_lo_group rb Kb). unfold AREA_HDR, META_SIZE, NSLOTS in *.
      destruct (DJ (fst b') rb (fst ag) rag Hrb Hrag NE2); lia.
  - (* [comment removed for export] *)
    intros q rq Hq Kq. unfold rshadow_rep. rewrite rl_shadow.
    destruct (rl_lookup_inv q rq Hq) as [[-> ->]|[NE H]].
    + (* [comment removed for export] *)
      cbn [r_base r_len]. rewrite (round_up_pg_id' needed) by exact NDAL. split.
      * eapply wr_at_transport; [exact WRN| exact WM3].
      * intros o v Ho Hc. fold rid in Hc.
        assert (OLO : o < snd pf). { destruct (Z.lt_ge_cases o (snd pf)); [assumption|]. exfalso. exact (NOK o v ltac:(lia) Hc). }
        destruct (SH rid r Hr Kr) as [_ HB]. destruct (HB o v ltac:(subst on; lia) Hc) as [Bt Hv]. split; [|exact Hv].
        destruct Bt as (B0 & B1 & B2). split; [lia|]. split; [cbn; ceil_facts; lia|].
        intros i Hi. cbn in Hi. destruct i; [|lia]. cbn [nth_error]. rewrite Z.add_0_r. specialize (B2 0%nat ltac:(cbn; lia)). rewrite Z.add_0_r in B2. cbn [nth_error] in B2.
        unfold mrd in B2 |- *. fold old in B2. rewrite <- B2. rewrite <- (CPY o) by lia.
        assert (AG : agree_on mA m3 (nb + o) 1).
        { apply (munch_agree _ _ _ (fun x => ~ (G + 16 <= x < G + 24) /\ ~ (G + 32 <= x < G + 40)) _ 1 MU3); [| | lia| ceil_facts; lia].
          - intros lo hi x [E|[E|[]]] Hx; inversion E; subst; tauto.
          - intros x Hx. rewrite EG, Cag. unfold AREA_HDR, META_SIZE, NSLOTS in *. lia. }
        rewrite <- (AG (nb + o)) by lia.
        destruct (m3 (wa (nb + o))); [reflexivity|].
        pose proof (rreserved_disjoint1 _ _ ORF ON0) as OI. pose proof (rreserved_disjoint1 _ _ RFN ltac:(lia)) as NI. ceil_facts.
        rewrite !ref_seg_rom_none by (rewrite wa_unsigned by lia; lia). reflexivity.
    + destruct (rl_greg_far q rq H NE Kq) as (Bq0 & BqC & DqO & DqN).
      destruct (SH q rq H Kq) as [HWr HB]. pose proof (round_up_pg_ge (r_len rq)) as RUq. destruct (WR _ _ H) as (_ & _ & Lq0 & _ & _).
      assert (AG : agree_on m1 m3 (r_base rq) (round_up_pg (r_len rq))).
      { apply rl_agree13; [lia| lia| lia| lia| lia|]. intros x Hx. rewrite EG, Cag.
        assert (NE2 : q <> fst ag). { intros E. subst q. rewrite Hrag in H. inversion H; subst. destruct (rarea_conc st ag arg WF Hag) as (r2 & Hr2 & _ & _ & _ & _ & NK & _). rewrite Hrag in Hr2. inversion Hr2; subst. exact (NK Kq). }
        pose proof (rarea_lr_lo st ag arg rag WF Hag Hrag). pose proof (lr_lo_group rq Kq). unfold AREA_HDR, META_SIZE, NSLOTS in *.
        destruct (DJ q rq (fst ag) rag H Hrag NE2); lia. }
      split; [eapply rwr_at_agree; [exact HWr| exact AG]|].
      intros o v Ho Hc. destruct (HB o v Ho Hc) as [Bt Hv]. split; [|exact Hv].
      eapply rbytes_at_agree; [exact Bt|]. cbn. eapply agree_on_sub; [exact AG| lia| lia].
Qed.
End RELOC.
(* [comment removed for export] *)
Lemma rptrs_ctx_norid st2 LB c rid r m :
  KINV st2 LB c -> rmrep st2 m ->
  (s_regions st2) !! rid = Some r -> r_kind r = RKGroup ->
  ci_mptrs st2 ->
  ptrs_ctx_in (fun x => x <> rid) st2.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros K MR Hr Kr (M1 & M2 & M3 & M4 & M5).
  pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG).
  assert (MSr : forall q, meta_slot st2 q -> fst q <> rid).
  { intros q (a & ar & k & Ha & Hk & ->) E. cbn in E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _).
    rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr). }
  assert (NGr : forall p, ng_ptr st2 p -> optr_in (fun x => x <> rid) p).
  { intros [q|]; cbn; [| exact (fun _ => I)]. intros (r' & Hr' & NK) E. rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. exact (NK Kr). }
  assert (OM : forall p, (forall q, p = Some q -> meta_slot st2 q) -> optr_in (fun x => x <> rid) p).
  { intros [q|] H; cbn; [apply MSr; apply H; reflexivity| exact I]. }
  pose proof (ki_links _ _ _ K) as [LN LP LNN LS].
  unfold ptrs_ctx_in. cbv zeta. split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
  - apply OM. intros h Hh. exact (proj1 (kinv_free_head st2 LB c h K Hh)).
  - apply NGr. exact M1.
  - apply NGr. exact M2.
  - apply NGr. exact M3.
  - apply NGr. exact M4.
  - intros sc. apply OM. intros a Ha. exact (proj1 (proj2 (kinv_active st2 LB c sc a K Ha))).
  - destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB; try exact I.
    intros E. destruct (ki_bk _ _ _ K brid boff HB) as (r' & Hr' & K'). rewrite E, Hr in Hr'. assert (r' = r) by congruence. subst r'. rewrite Kr in K'. discriminate.
  - intros g. split.
    + apply OM. intros pv Hp. exact (proj2 (LP g pv Hp)).
    + apply OM. intros nx Hn. exact (proj2 (LN g nx Hn)).
  - intros a ar Ha. split; [| apply NGr; exact (M5 a ar Ha)].
    intros E. destruct (WA a ar Ha) as (ra & Hra & _ & _ & _ & NK & _). rewrite E, Hr in Hra. assert (ra = r) by congruence. subst ra. exact (NK Kr).
  - intros b gh Hb.
    destruct (ki_grps _ _ _ K b gh Hb) as (g & Hg & _). rewrite Hg. cbn. apply MSr.
    assert (HB : hosts st2 b g) by (exists (g_active_idx gh); rewrite Hb; destruct gh; cbn in Hg |- *; subst; reflexivity).
    exact (go_slot _ _ _ (ki_gmetas _ _ _ K b g HB)).
Qed.

(* [comment removed for export] *)
Lemma rmem_only st LB rid b g ai :
  CINV st LB -> (s_groups st) !! b = Some (mkGhdr (Some g) ai) ->
  (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = rid -> b' = b) ->
  forall q b'', m_mem (get_meta_rec st q) = Some b'' -> fst b'' = rid -> q = g.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros C Hgh ONLY q b'' MB E. destruct (ZINV_of_CINV _ _ C q b'' MB) as [[ai' Hb'']|[]].
  pose proof (ONLY _ _ Hb'' E) as ->. rewrite Hgh in Hb''. inversion Hb''. reflexivity.
Qed.

Lemma put_meta_same st g mr : (s_metas st) !! g = Some mr -> put_meta g mr st = st.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros H. unfold put_meta. rewrite insert_id by exact H. destruct st; reflexivity. Qed.

End PORT.

End WithCeil.
End TwB.
End RF_realloc63R.

(* [comment removed for export] *)
Module RMallocKit_A3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rmrep_set_bounce : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (set_bounce i v st) (write_to_mem m (wa (RCTX + 880 + i)) [b8 v]).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write ssegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl ssegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
    apply (u8arr_write ssegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame ssegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write ssegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write ssegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv ssegs mX |- _ =>
      apply (mem_inv_store ssegs mX (wa A) bs') in HI;
      [| fastfirst (first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ]) ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac rraw_store_finish0 A bs' MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write ssegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv ssegs mX |- _ =>
      apply (mem_inv_store ssegs mX (wa A) bs') in HI;
      [| fastfirst (first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ]) ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.
End PORT.
End WithCeil.


Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; first [ solve [repeat split] | tauto ]]);
    clear MUq WMq CH end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac rmchunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rmrep_regroup : forall st m m' b gh g ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some gh ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono ssegs m m' ->
  rw_cells ssegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
  pose proof (rmrep_del_group st m b MR) as MR1.
  assert (MR2 : rmrep (del_group b st) m').
  { eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
    intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
    pose proof (round_up_pg_ge (r_len r)).
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
      destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
      rewrite lookup_delete_ne in Hb2 by congruence.
      destruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
      destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
      + rewrite E, Hr in Hr2. inversion Hr2; subst r2.
        assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
        assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
      + destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
    - change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
      destruct (N.eq_dec q (fst b)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
        rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold RGOT_SSP in R8. lia.
    - unfold RSSP_GUARD in R9. lia. }
  rewrite <- put_group_del.
  eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
  unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

Lemma rmrep_set_group_ai : forall st m m' b g ai0 ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some (mkGhdr (Some g) ai0) ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono ssegs m m' ->
  rw_cells ssegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (set_group_active_idx b ai st) m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
  eapply rmrep_regroup; eauto.
Qed.

(* [comment removed for export] *)
Lemma rmrep_ctr_byte_read : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
  ov_read_bytes ssegs m (wa (RCTX + 12)) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m (_ & (HD & _) & _) CR.
  destruct HD as [[_ HB] _]. unfold ctx_head_cells in HB. cbn [cells_bytes cbytes app] in HB.
  rewrite (bytes_at_read ssegs m RCTX _ 12 1 HB).
  all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
  change (Z.to_nat 12) with 12%nat.
  unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
  rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_AB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rmrep_set_bounce : forall st m i v,
  rmrep st m -> 0 <= i < 32 ->
  rmrep (set_bounce i v st) (write_to_mem m (wa (RCTX + 880 + i)) [b8 v]).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m i v MR Hi. pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _).
  pose proof (munch_write [(RCTX + 880 + i, RCTX + 880 + i + 1)] m m (RCTX + 880 + i) [b8 v] (munch_refl _ m)
                ltac:(unfold RCTX; lia) ltac:(cbn; unfold RCTX; lia) ltac:(cbn; lia)) as MU.
  pose proof (wmono_write usegs m m (wa (RCTX + 880 + i)) [b8 v] (wmono_refl usegs m)) as WM.
  eapply (rmrep_ctx_frameW st _ m _ _ MR MU WM); try reflexivity.
  - rctx_same.
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - right. split; [reflexivity| rctx_same].
  - left. rewrite bouncess_set by lia. replace (RCTX + 880 + i) with ((RCTX + 880) + i) by lia.
    apply (u8arr_write usegs m (RCTX + 880) (bouncess st) i (b8 v)); [exact X5| rewrite bouncess_length; lia].
  - right. split; [| rctx_same].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx c_seq c_brk set_bounces_map]. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac rraw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame usegs mX _ _ A bs') in FR; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write usegs mX _ _ A bs') in ST; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write usegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv usegs mX |- _ =>
      apply (mem_inv_store usegs mX (wa A) bs') in HI;
      [| fastfirst (first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ]) ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac rraw_store_finish0 A bs' MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, RCTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (munch_write _ _ mX A bs') in MU; [| unfold RCTX; lia | rewrite <- L; unfold RCTX; lia | rewrite <- L; unfold RCTX; cbn [inside]; lia];
    apply (wmono_write usegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv usegs mX |- _ =>
      apply (mem_inv_store usegs mX (wa A) bs') in HI;
      [| fastfirst (first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, RCTX; f_equal; lia); exact SOK ]) ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rconc_meta_inj : forall st m g q, rmrep st m -> meta_slot st g -> meta_slot st q ->
  conc st q = conc st g -> q = g.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m g q MR (a & ar & k & Ha & Hk & Eg) (a' & ar' & k' & Ha' & Hk' & Eqq) E.
  pose proof MR as (WF & _). pose proof WF as (_ & WR & DJ & _).
  destruct (rarea_conc st a ar WF Ha) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & _).
  destruct (rarea_conc st a' ar' WF Ha') as (ra' & Hra' & Ca' & Sa0' & Sa1' & SaL' & NK' & _).
  assert (HG : conc st g = conc st a + (AREA_HDR + META_SIZE * k)) by (rewrite Eg, conc_aadd by (rewrite Hra; eauto); reflexivity).
  assert (HQ : conc st q = conc st a' + (AREA_HDR + META_SIZE * k')) by (rewrite Eqq, conc_aadd by (rewrite Hra'; eauto); reflexivity).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  destruct (N.eq_dec (fst a') (fst a)) as [Ef|NEf].
  - rewrite Ef, Hra in Hra'. inversion Hra'; subst ra'.
    assert (snd a' = snd a /\ k' = k) as [E1 E2] by (Z.div_mod_to_equations; nia).
    rewrite Eqq, Eg. unfold aadd. rewrite Ef, E1, E2. reflexivity.
  - exfalso. pose proof (rarea_lr_lo st a ar ra WF Ha Hra). pose proof (rarea_lr_lo st a' ar' ra' WF Ha' Hra'). destruct (DJ (fst a') ra' (fst a) ra Hra' Hra NEf); lia.
Qed.
End PORT.
End WithCeil.


Ltac rmeta_close2 MRold MSq MUq WMq CH st' MRnew E1 E2 :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRnew : rmrep st' mX)
      by (eapply rmrep_put_meta_frame; [exact MRold | exact MSq | exact MUq | exact WMq |];
          eapply rw_cells_congr; [ | | | exact CH];
          [ unfold meta_cells; unfold pw; cbn [oconc m_prev m_next m_mem m_avail m_freed meta_word m_last_idx m_freeable m_sizeclass m_maplen m_set_prev m_set_next];
            unfold wz; rewrite ?E1, ?E2; cbn [oconc]; reflexivity
          | reflexivity | cbn; first [ solve [repeat split] | tauto ]]);
    clear MUq WMq CH end.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
End PORT.
End WithCeil.

Ltac rmchunk MR MSq CH :=
  pose proof (rmrep_meta_chunk _ _ _ MR MSq) as CH;
  rewrite ?meta_cells_put_meta in CH; unfold meta_cells in CH;
  rewrite ?get_meta_rec_put_same in CH;
  rewrite ?conc_put_meta, ?pw_put_meta in CH;
  cbn [m_prev m_next m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen
       m_set_prev m_set_next m_set_mem m_set_avail m_set_freed] in CH;
  unfold pw in CH; cbn [oconc] in CH; unfold wz in CH.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rmrep_regroup : forall st m m' b gh g ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some gh ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono usegs m m' ->
  rw_cells usegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (put_group b (Some g) ai st) m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' b gh g ai w8' MR Hb UNK MU WM RC Hw8.
  pose proof MR as (WF & _). pose proof WF as (RS & WR & DJ & WA & WG).
  destruct (rgroup_conc st b gh WF Hb) as (r & Hr & Cb & Kr & B0 & B16 & BA & RB0 & RC0).
  pose proof (rmrep_del_group st m b MR) as MR1.
  assert (MR2 : rmrep (del_group b st) m').
  { eapply (rmrep_transport_unowned _ _ _ _ MR1 MU WM). apply ivs_avoid_cons; [|apply ivs_avoid_nil].
    intros a Ha RF. destruct (WR (fst b) r Hr) as (_ & _ & _ & _ & RFr). destruct (rreserved_disjoint _ _ RFr) as (I1 & _ & I23 & I2).
    pose proof (round_up_pg_ge (r_len r)).
    destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b2 & gh2 & Hb2 & Rb2)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]].
    - unfold RCTX in R1. lia.
    - unfold RMLOCK in R2. lia.
    - unfold RNEED_LOCKS in R3. lia.
    - unfold RPAGE_SIZE in R4. lia.
    - change (s_areas (del_group b st)) with (s_areas st) in Hak. change (conc (del_group b st) ak) with (conc st ak) in Rak.
      destruct (rarea_conc st ak ar WF Hak) as (rga & Hra & Ca & Sa0 & Sa1 & _ & NK & _).
      assert (NE : fst ak <> fst b) by (intros E; rewrite E, Hr in Hra; inversion Hra; subst; congruence).
      pose proof (rarea_lr_lo st ak ar rga WF Hak Hra). destruct (DJ _ _ _ _ Hra Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold del_group in Hb2. cbn [s_groups set_groups] in Hb2. change (conc (del_group b st) b2) with (conc st b2) in Rb2.
      destruct (decide (b2 = b)) as [->|NE2]; [rewrite lookup_delete_eq in Hb2; discriminate|].
      rewrite lookup_delete_ne in Hb2 by congruence.
      destruct (rgroup_conc st b2 gh2 WF Hb2) as (r2 & Hr2 & Cb2 & Kr2 & B20 & B216 & B2A & _).
      destruct (N.eq_dec (fst b2) (fst b)) as [E|NE].
      + rewrite E, Hr in Hr2. inversion Hr2; subst r2.
        assert (snd b2 <> snd b) by (intros E2; apply NE2; destruct b, b2; cbn in *; congruence).
        assert (snd b2 + 16 <= snd b \/ snd b + 16 <= snd b2) by (Z.div_mod_to_equations; lia). lia.
      + destruct (DJ _ _ _ _ Hr2 Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr), ?(lr_lo_group r2 Kr2) in D; lia.
    - change (s_regions (del_group b st)) with (s_regions st) in Hq. change (get_shadow (del_group b st) q) with (get_shadow st q) in Cq.
      destruct (N.eq_dec q (fst b)) as [->|NE].
      + rewrite Hr in Hq. inversion Hq; subst rq.
        destruct (UNK (a - r_base r - snd b) ltac:(lia)) as [h Hh]. replace (snd b + (a - r_base r - snd b)) with (a - r_base r) in Hh by lia.
        rewrite Hh in Cq. discriminate.
      + pose proof (lr_lo_group rq Kq). destruct (DJ _ _ _ _ Hq Hr NE) as [D|D]; rewrite ?(lr_lo_group r Kr) in D; lia.
    - unfold RGOT_SSP in R8. lia.
    - unfold RSSP_GUARD in R9. lia. }
  rewrite <- put_group_del.
  eapply (rmrep_put_group_new _ _ b _ ai r w8' MR2); [ | exact Hr | exact Kr | exact B0 | exact B16 | exact BA | exact RC | exact Hw8].
  unfold del_group. cbn [s_groups set_groups]. apply lookup_delete_eq.
Qed.

Lemma rmrep_set_group_ai : forall st m m' b g ai0 ai (w8' : byte),
  rmrep st m -> (s_groups st) !! b = Some (mkGhdr (Some g) ai0) ->
  (forall o, 0 <= o < 9 -> exists h, cell_read (get_shadow st (fst b)) (snd b + o) = Unknown h) ->
  munch [(conc st b, conc st b + 9)]%Z m m' -> wmono usegs m m' ->
  rw_cells usegs m' (conc st b) [C8 (pw st (Some g)); C1 w8'] -> Z.land (bv_unsigned w8') 31 = Z.land ai 31 ->
  rmrep (set_group_active_idx b ai st) m'.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m m' b g ai0 ai w8' MR Hb UNK MU WM RC Hw8. rewrite (set_group_ai_eq st b _ ai Hb), put_group_del. cbn [g_meta].
  eapply rmrep_regroup; eauto.
Qed.

(* [comment removed for export] *)
Lemma rmrep_ctr_byte_read : forall st m, rmrep st m -> 0 <= c_mmap_counter (ctx st) < 2^32 ->
  ov_read_bytes usegs m (wa (RCTX + 12)) 1 = Some [b8 (c_mmap_counter (ctx st) mod 256)].
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st m (_ & (HD & _) & _) CR.
  destruct HD as [[_ HB] _]. unfold ctx_head_cells in HB. cbn [cells_bytes cbytes app] in HB.
  rewrite (bytes_at_read usegs m RCTX _ 12 1 HB).
  all: try (rewrite ?app_length, ?length_le8, ?length_le4; change (Z.to_nat 12) with 12%nat; cbn; lia); try lia.
  change (Z.to_nat 12) with 12%nat.
  unfold le8, le4, word_to_le_bytes. cbn [Z_to_le_bytes app drop take].
  rewrite wz_unsigned by lia. apply (f_equal Some). apply (f_equal (fun x => [x])). unfold b8. apply bv_eq. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_mod by lia. reflexivity.
Qed.

End PORT.

End WithCeil.
End TwB.
End RMallocKit_A3.
