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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_mm_syscalls.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_P__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
From Stdlib Require Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_small.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_reallocA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_slot.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_P__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_meta.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module RF_free.
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
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B_reach.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_mm_syscalls. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_P__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_free_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_free_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_free_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_free_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_ntf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_free_K.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
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

Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
    (st' : mstate) (s' : PState) : machine_state -> Prop :=
  fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st' m'
    /\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ RERRNO <= a < RERRNO + 4) m m'
    /\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
    /\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
    /\ c_brk (ctx st') = c_brk (ctx st)
    /\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> RERRNO <= a < RERRNO + 4 -> ~ rfree_fp st lo sp a.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR LO Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). pose proof (lr_lo_ge r). lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
Qed.

(* [comment removed for export] *)
Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
  rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
  (s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
  munch [(slo, shi); (RERRNO, RERRNO + 4); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
  alloc_ceiling <= slo ->
  rmrep (drop_region rid st2) m5.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  pose proof (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (rreserved_tlsF _ _ RF). ceil_facts.
  eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
  assert (LOW : a < alloc_ceiling /\ ~ (RERRNO <= a < RERRNO + 4) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
  { destruct HF as [HF|HF].
    - split; [| split].
      + destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.RPAGE_SIZE in C; lia.
        * destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). ceil_facts. lia.
        * destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). ceil_facts. lia.
        * destruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
          destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). ceil_facts. lia.
        * unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
      + intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
      + intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.RPAGE_SIZE in C; lia.
        * destruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
          destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
          assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
          rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
          pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
        * destruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
          destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
          assert (NE : fst b <> rid).
          { intros E. pose proof (proj1 MRd) as (_ & _ & _ & _ & WG'). destruct (WG' b gh Hb) as (rb' & Hrb' & _).
            cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
          rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
        * destruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
        * unfold RGOT_SSP in C. lia.
        * unfold RSSP_GUARD in C. lia.
    - destruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
      destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). pose proof (rreserved_disjoint _ _ RFk) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RFk). ceil_facts.
      split; [lia|]. split; [lia|].
      pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
  destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

(* [comment removed for export] *)
Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

Lemma bytes4_range (x0 x1 x2 x3 : byte) :
  0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
  le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
  rewrite le4_bytes by lia. unfold b8.
  (* [comment removed for export] *)
  f_equal; [|f_equal; [|f_equal; [|f_equal]]];
    (apply bv_eq; rewrite Z_to_bv_unsigned;
     match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
     Z.div_mod_to_equations; lia).
Qed.

Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Definition rlibc_free_implT__stmt : Prop := forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
    (st : mstate) (blk : block) (off : Z) (errv : word),
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  rmrep st m -> mem_inv ssegs m ->
  stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
        (rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st blk off errv : ltac2:(SecDiet.SzSec.tyM 'rlibc_free_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rlibc_free_implT__body : ltac2:(SecDiet.SzSec.bodyP 'rlibc_free_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
Proof using LO TP. ceil_facts. msec_facts.
  intros C Hin Hoff HA MR MI ST SLO ERR A0.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rerrno_addr tp TP) as ETP.
  pose proof LO as LOv. ceil_facts.
  (* [comment removed for export] *)
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (ceil_facts; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x55000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  (* [comment removed for export] *)
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  (* [comment removed for export] *)
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  (* [comment removed for export] *)
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at ssegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at ssegs m (r_base r + snd q) 1).
    { destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
    destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
    eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }
  (* [comment removed for export] *)
  unfold free.
  eapply (rimplT_bind m (free_hdr st pf) _ s
           (fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
              rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
  { unfold free_hdr, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16; [peek_same MR| peek_same MR|]. apply rimplT_rd8; [peek_same MR|]. cbv zeta. apply rimplT_rd8; [peek_same MR|].
    rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
    assert (Fe : fst e = fst b) by reflexivity.
    assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
    { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
    (* [comment removed for export] *)
    pose proof (go_sc _ _ _ GO) as GSC.
    assert (WALK : forall r32 : Z,
      (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
          /\ bytes_at ssegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
          /\ bytes_at ssegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
      (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
      bytes_at ssegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
      bytes_at ssegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
      evt ssegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
                 rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom ssegs))).
    { intros r32 BIG RSVLE RB0r RE0.
      eapply evt_mono.
      { eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
          first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        - lia.
        - rewrite Fp. exact Hr.
        - rewrite A0, HAp. apply unsigned_lit. lia.
        - exact P16m.
        - rewrite Sp, Sc. lia.
        - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
        - exact PHI.
        - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
        - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
        - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
        - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
        - exact Hgh.
        - reflexivity.
        - exact (go_slot _ _ _ GO).
        - destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
        - exact (go_mem _ _ _ GO).
        - exact AR1.
        - exact G15.
        - exact (go_avail _ _ _ GO).
        - exact (go_freed _ _ _ GO).
        - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        - lia.
        - rewrite (go_freeable _ _ _ GO). lia.
        - lia.
        - pose proof (go_maplen _ _ _ GO). lia.
        - exact G12.
        - exact G13.
        - exact G14.
        - intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
          apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        - intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
        - intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        - lia.
        - exact S16.
        - rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
        - rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
        - exact BIG.
        - exact RSVLE.
        - exact RB0r.
        - exact RE0.
        - intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
          rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
          clear - HD HAp SZ. lia. (* [comment removed for export] *) }
      intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }
    (* [comment removed for export] *)
    assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
    { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
    { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
    assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    
    unfold get_nominal_size. apply rimplT_rd8; [peek_same MR|]. cbv zeta.
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    apply rimplT_if; intros HR5.
    - (* [comment removed for export] *)
      apply Z.leb_le in HR5.
      apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
      apply rimplT_rd32; [peek_same MR| peek_same MR| peek_same MR| peek_same MR|].
      destruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0. 
      destruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1. 
      destruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
      destruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
      pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
      set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
      apply rimplT_guard; intros G21. apply Z.leb_le in G21.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
      apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
      
      apply (WALK r32).
      + intros _. split; [exact G20|]. split; [lia|]. split.
        * rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
          apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
          apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
          -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
          -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
        * rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
    - (* [comment removed for export] *)
      apply Z.leb_gt in HR5.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
      
      apply (WALK 0).
      + intros H. exfalso. clear -H V160. lia.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

  intros r1 s' ms1 (-> & -> & FH). cbv beta iota.
  destruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
  set (st1 := hdr_st st pf) in *.
  assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
  assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
  assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
  { intros k Hk. unfold pf; cbn [aadd fst snd].
    assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct CS as [-> |[-> | ->]];
      [exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
      |exists lo8|exists v3];
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
  assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
  assert (ERR1 : rw_cells ssegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
    rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
  assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
  assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }
  (* [comment removed for export] *)
  assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
  { intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
  unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
  apply rimplT_guard. intros _.
  apply rimplT_if; intros HC.
  - (* [comment removed for export] *)
    apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
    apply rimplT_ret.
    eapply evt_mono.
    { eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms' TPo. unfold rftriv_post in TPo.
    destruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
             rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
    split; [exact MR'|].
    split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
    split; [intros rid r' H; exact H|].
    split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
    split; reflexivity.
  - (* [comment removed for export] *)
    
    assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
    { apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
    eapply rimplT_evt.
    { eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms2 (y2 & y3 & y4 & y5 & y6 & y7 & ->).
    assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
    { intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
      intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
    assert (K1 : KINV st1 LB' 0).
    { unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
      unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
    assert (L1 : LPRE st1 LB' 0 g b i).
    { unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
    assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
    assert (OOK1 : oracle_ok m m1 st1).
    { unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
    change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
    eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
      [exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].
    (* [comment removed for export] *)
    
    intros st2 mi ms3 NQ. unfold rntf_q in NQ.
    destruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
    rewrite unsigned_lit in ST3, PE3 by lia.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
    replace (ret_pc (Z_to_bv 64 0x18a44)) with (Z_to_bv 64 0x18a44) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
    { eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
    assert (FR3' : rw_cells ssegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
      pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
    assert (ERR3 : rw_cells ssegs m3 (errno_addr tp) [C4 errv]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
      rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
    pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
    pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
    destruct mi as [[bm len]|].
    + (* [comment removed for export] *)
      cbv beta iota.
      destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
      replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
      destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). ceil_facts.
      assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x55000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
      assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
      pose proof (round_up_pg_ge (r_len r2)) as RU2.
      eapply rimplT_evt.
      { eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
          [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LEN]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR3']) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ERR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LOv]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) ]. }
      intros ms4 FM. unfold rfmun_post in FM.
      destruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
      eapply (rimplT_munmap m (conc st2 bm) len _ s).
      { eapply rmunmap_spec.
        - rewrite unsigned_lit by lia. exact ST4.
        - exact ERR4.
        - exact MI4.
        - unfold wz. reflexivity.
        - unfold wz. reflexivity.
        - lia.
        - rewrite Lr2, mmap_len_round. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite ETP, unsigned_lit by lia. lia.
        - rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
        - rewrite ETP, Lr2, mmap_len_round. pose proof (rreserved_tlsF _ _ R2F). pose proof (round_up_pg_ge (r_len r2)). lia.
        - rewrite TP, RATP_unsigned. lia. }
      intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
      destruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
      rewrite (munmap_ok_range_val a (rg_err_range _ a ERNG)).
      apply rimplT_ret.
      replace (ret_pc (Z_to_bv 64 0x18a74)) with (Z_to_bv 64 0x18a74) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.
      (* [comment removed for export] *)
      assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
      assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
      assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
      pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
      pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
      assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
      { eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
      assert (FR5 : rw_cells ssegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
        rewrite ?ETP. cbn [outside]. repeat split; lia. }
      eapply evt_mono.
      { eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
          [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MRd5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [apply le4_sx32]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ERR5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LOv]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) ]. }
      intros ms' FIN. unfold rffin_post in FIN.
      destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { (* [comment removed for export] *)
        assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
        { intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
          cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
        eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ RERRNO <= a < RERRNO + 4)); [| exact NC].
          cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ RERRNO <= a < RERRNO + 4)); [| exact NC].
          cover_intervals ltac:(fun y Hy => [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [left; apply rfree_fp_stack; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [right; right; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [right; left; apply DR; lia]) ]). }
        eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ RERRNO <= a < RERRNO + 4)); [| exact NC].
        cover_intervals ltac:(fun y Hy => [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [left; apply rfree_fp_stack; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [right; right; lia]) ]). }
      split.
      { intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
      split.
      { intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
        destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
        destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
        exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
        intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
      split; [exact EB3|].
      intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
      rewrite <- EB3 in HB0. destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
      rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
      intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
    + (* [comment removed for export] *)
      
      cbv beta iota. cbn in RES3. subst a1v.
      apply rimplT_ret.
      eapply evt_mono.
      { eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
          [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR3']) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ERR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LOv]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) ]. }
      intros ms' FIN. unfold rffin_post in FIN.
      destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ RERRNO <= a < RERRNO + 4)); [| exact NC].
        cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
      split; [intros rid r' H; rewrite <- ER3; exact H|].
      split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
      split; [exact EB3|].
      intros brid boff _. rewrite ER3. reflexivity.
Qed.
End Sz1.
Theorem rlibc_free_implT : ltac:(let t := eval cbv delta [rlibc_free_implT__stmt] in rlibc_free_implT__stmt in exact t).
Proof using LO TP. intros ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st blk off errv. ltac2:(SecDiet.SzSec.closeP 'rlibc_free_implT__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FREE.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B_reach.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_free_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_free_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_free_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_free_C.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_ntf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_free_K.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
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

Definition rfree_end (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (st : mstate) (LB' : list block) (m : mem) (errv : word) (s : PState)
    (st' : mstate) (s' : PState) : machine_state -> Prop :=
  fun ms' => s' = s /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv]
    /\ rmrep st' m'
    /\ rpres_except (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st' a \/ RERRNO <= a < RERRNO + 4) m m'
    /\ (forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r')
    /\ (forall blk', In blk' LB' -> exists r', (s_regions st') !! (fst (blk_slot blk')) = Some r')
    /\ c_brk (ctx st') = c_brk (ctx st)
    /\ (forall brid boff, c_brk (ctx st) = BrkLive brid boff -> (s_regions st') !! brid = (s_regions st) !! brid).

Lemma rerrno_not_free_fp st m lo (sp : Z) a : rmrep st m -> alloc_ceiling <= lo -> RERRNO <= a < RERRNO + 4 -> ~ rfree_fp st lo sp a.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MR LO Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  intros [[A|[A|A]]|[A|A]].
  - lia.
  - unfold RCTX in A. lia.
  - destruct A as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). pose proof (lr_lo_ge r). lia.
  - destruct A as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
    destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
  - destruct A as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
Qed.

(* [comment removed for export] *)
Lemma rmrep_after_munmap st2 rid r2 m4 m5 (slo shi : Z) :
  rmrep (drop_region rid st2) m4 -> rmrep st2 m4 ->
  (s_regions st2) !! rid = Some r2 -> r_kind r2 = RKGroup ->
  munch [(slo, shi); (RERRNO, RERRNO + 4); (r_base r2, r_base r2 + round_up_pg (r_len r2))]%Z m4 m5 ->
  alloc_ceiling <= slo ->
  rmrep (drop_region rid st2) m5.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros MRd MR Hr Kr MU LO. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  pose proof (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF). pose proof (rreserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4). pose proof (rreserved_tlsF _ _ RF). ceil_facts.
  eapply rmrep_transport_agree'; [exact MRd|]. intros a Ha HF. apply MU. rewrite wa_unsigned by lia.
  assert (LOW : a < alloc_ceiling /\ ~ (RERRNO <= a < RERRNO + 4) /\ ~ (r_base r2 <= a < r_base r2 + round_up_pg (r_len r2))).
  { destruct HF as [HF|HF].
    - split; [| split].
      + destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB.RPAGE_SIZE in C; lia.
        * destruct C as (ak & ar & Hak & Hin). destruct (rarea_conc (drop_region rid st2) ak ar (proj1 MRd) Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & _ & _ & _ & RC). ceil_facts. lia.
        * destruct C as (b & gh & Hb & Hin). destruct (rgroup_conc (drop_region rid st2) b gh (proj1 MRd) Hb) as (rb & Hrb & Cb & _ & _ & Sb1 & _ & _ & RC). ceil_facts. lia.
        * destruct C as (k & rk & v & Hk & _ & Hin & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [_ Hk].
          destruct (WR _ _ Hk) as (_ & _ & _ & RC & _). ceil_facts. lia.
        * unfold RGOT_SSP in C; lia. * unfold RSSP_GUARD in C; lia.
      + intros Hea. exact (rerrno_avoids_repfoot _ _ a MRd Hea HF).
      + intros Hin. destruct HF as [C|[C|[C|[C|[C|[C|[C|[C|C]]]]]]]].
        * unfold RCTX in C; lia. * unfold RMLOCK in C; lia. * unfold RNEED_LOCKS in C; lia. * unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB.RPAGE_SIZE in C; lia.
        * destruct C as (ak & ar & Hak & Ha'). cbn [drop_region s_areas set_shadow set_regions] in Hak.
          destruct (WA ak ar Hak) as (ra & Hra & Sa0 & Sa1 & _ & NK & ALR).
          assert (NE : fst ak <> rid) by (intros E; rewrite E, Hr in Hra; assert (ra = r2) by congruence; subst; exact (NK Kr)).
          rewrite (rconc_drop st2 rid ak NE) in Ha'. rewrite (conc_region' st2 ak ra Hra) in Ha'.
          pose proof (lr_lo_group r2 Kr). destruct (DJ _ _ _ _ Hra Hr NE); lia.
        * destruct C as (b & gh & Hb & Ha'). cbn [drop_region s_groups set_shadow set_regions] in Hb.
          destruct (WG b gh Hb) as (rb & Hrb & Krb & Sb0 & Sb1 & _).
          assert (NE : fst b <> rid).
          { intros E. pose proof (proj1 MRd) as (_ & _ & _ & _ & WG'). destruct (WG' b gh Hb) as (rb' & Hrb' & _).
            cbn [drop_region s_regions set_shadow set_regions] in Hrb'. rewrite E, lookup_delete_eq in Hrb'. discriminate. }
          rewrite (rconc_drop st2 rid b NE) in Ha'. rewrite (conc_region' st2 b rb Hrb) in Ha'.
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
        * destruct C as (k & rk & v & Hk & Kk & Ha' & _). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
          pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia.
        * unfold RGOT_SSP in C. lia.
        * unfold RSSP_GUARD in C. lia.
    - destruct HF as (k & rk & Hk & Kk & Ha'). cbn [drop_region s_regions set_shadow set_regions] in Hk. apply lookup_delete_Some in Hk. destruct Hk as [NE Hk].
      destruct (WR _ _ Hk) as (_ & _ & _ & RC & RFk). pose proof (rreserved_disjoint _ _ RFk) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RFk). ceil_facts.
      split; [lia|]. split; [lia|].
      pose proof (lr_lo_group r2 Kr). pose proof (lr_lo_group rk Kk). destruct (DJ _ _ _ _ Hk Hr ltac:(congruence)); lia. }
  destruct LOW as (L1 & L2 & L3). cbn [outside]. split; [lia|]. split; [exact L2|]. split; [exact L3| exact I].
Qed.

(* [comment removed for export] *)
Lemma byte_zero_list (x : byte) : bv_unsigned x = 0 -> [x] = [b8 0].
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros Hx. f_equal. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 x). rewrite Hx. reflexivity. Qed.

Lemma bytes4_range (x0 x1 x2 x3 : byte) :
  0 <= bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3 < 2^32.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *. lia.
Qed.

Lemma le4_of_bytes (x0 x1 x2 x3 : byte) :
  le4 (wz (bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3)) = [x0; x1; x2; x3].
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  pose proof (bv_unsigned_in_range 8 x0). pose proof (bv_unsigned_in_range 8 x1).
  pose proof (bv_unsigned_in_range 8 x2). pose proof (bv_unsigned_in_range 8 x3).
  unfold bv_modulus in *. cbn [Z.pow_pos Pos.iter Z.mul Pos.mul] in *.
  rewrite le4_bytes by lia. unfold b8.
  (* [comment removed for export] *)
  f_equal; [|f_equal; [|f_equal; [|f_equal]]];
    (apply bv_eq; rewrite Z_to_bv_unsigned;
     match goal with |- bv_wrap 8 ?a = _ => change (bv_wrap 8 a) with (a mod 256)%Z end;
     Z.div_mod_to_equations; lia).
Qed.

Lemma shiftr5_ge v : 0 <= v < 256 -> 5 <= Z.shiftr v 5 -> 160 <= v.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_lt v : 0 <= v < 256 -> Z.shiftr v 5 < 5 -> v < 160.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros Hv H. rewrite Z.shiftr_div_pow2 in H by lia. change (2^5) with 32 in H. Z.div_mod_to_equations. lia. Qed.
Lemma shiftr5_range v : 0 <= v < 256 -> 0 <= Z.shiftr v 5 < 8.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts. intros Hv. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32. Z.div_mod_to_equations. lia. Qed.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis TP : tp = Z_to_bv 64 RATP.

Definition rlibc_free_implT__stmt : Prop := forall (ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem) (s : PState)
    (st : mstate) (blk : block) (off : Z) (errv : word),
  CINV st LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st (blk_slot blk) + UNIT * off ->
  rmrep st m -> mem_inv usegs m ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 8192 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  rimplT m (free st (Some (aadd (blk_slot blk) (UNIT * off)))) s
        (rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB blk) m errv s)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st blk off errv : ltac2:(SecDiet.SzSec.tyM 'rlibc_free_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rlibc_free_implT__body : ltac2:(SecDiet.SzSec.bodyP 'rlibc_free_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
Proof using LO TP. ceil_facts. msec_facts.
 intros C Hin Hoff HA MR MI ST SLO ERR A0.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *. set (LB' := lbrm LB blk) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rerrno_addr tp TP) as ETP.
  pose proof LO as LOv. ceil_facts.
  (* [comment removed for export] *)
  assert (SIM : (get_stride (get_meta_rec st g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st g) * (i + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st g) * i) in *. set (stq := get_stride (get_meta_rec st g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (ceil_facts; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x56000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  (* [comment removed for export] *)
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  (* [comment removed for export] *)
  assert (Cb : conc st b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  (* [comment removed for export] *)
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at usegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at usegs m (r_base r + snd q) 1).
    { destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs & L & B).
    destruct bs as [|x [|]]; try discriminate. exists x. split; [exact B|].
    eapply (rrdv_cur m st m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B]. }
  (* [comment removed for export] *)
  unfold free.
  eapply (rimplT_bind m (free_hdr st pf) _ s
           (fun r1 s' ms' => s' = s /\ r1 = Some (hdr_st st pf, g, i) /\
              rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')).
  { unfold free_hdr, get_meta. apply rimplT_guard. intros _.
    apply rimplT_rd16; [peek_same MR| peek_same MR|]. apply rimplT_rd8; [peek_same MR|]. cbv zeta. apply rimplT_rd8; [peek_same MR|].
    rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
    rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
    cbn [Z.eqb negb]. rewrite EB. unfold get_group. rewrite Hgh. cbn [g_meta].
    apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
    destruct (s_areas st !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
    apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
    unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
    apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
    rewrite V31 in G12, G13, G14, G16.
    set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st g) * Z.land v3 31)) (get_stride (get_meta_rec st g) - IB)).
    assert (Fe : fst e = fst b) by reflexivity.
    assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - 4).
    { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
    (* [comment removed for export] *)
    pose proof (go_sc _ _ _ GO) as GSC.
    assert (WALK : forall r32 : Z,
      (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32
          /\ bytes_at usegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 4) (le4 (wz r32))
          /\ bytes_at usegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - 5) [b8 0]) ->
      (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf) ->
      bytes_at usegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
      bytes_at usegs m (conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB) [b8 0] ->
      evt usegs (fun ms' => s = s /\ Some (hdr_st st pf, g, i) = Some (hdr_st st pf, g, i) /\
                 rfhead_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 t3 t4 t5 t6 a0 F fc lo st m (hdr_st st pf) g i (m_last_idx (get_meta_rec st g)) ms')
          (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs))).
    { intros r32 BIG RSVLE RB0r RE0.
      eapply evt_mono.
      { eapply (rfree_head ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo st pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi r32);
          first [exact MR | exact MI | exact TK | exact ST | exact LO | exact Kr | idtac].
        all: rewrite ?EB, ?V31.
        - lia.
        - rewrite Fp. exact Hr.
        - rewrite A0, HAp. apply unsigned_lit. lia.
        - exact P16m.
        - rewrite Sp, Sc. lia.
        - unfold pf in OFF |- *. cbn [aadd snd] in OFF |- *. lia.
        - exact PHI.
        - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
        - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
        - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
        - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
        - exact Hgh.
        - reflexivity.
        - exact (go_slot _ _ _ GO).
        - destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. lia.
        - exact (go_mem _ _ _ GO).
        - exact AR1.
        - exact G15.
        - exact (go_avail _ _ _ GO).
        - exact (go_freed _ _ _ GO).
        - exact (proj2 (proj2 (proj2 (ki_cx _ _ _ K0)))).
        - lia.
        - rewrite (go_freeable _ _ _ GO). lia.
        - lia.
        - pose proof (go_maplen _ _ _ GO). lia.
        - exact G12.
        - exact G13.
        - exact G14.
        - intros Hsc. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
          apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. lia.
        - intros Hsc. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st g)) 48); [lia|]. apply Z.eqb_eq in G16. exact G16.
        - intros Hml. destruct (Z.eqb_spec (m_maplen (get_meta_rec st g)) 0); [lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
          unfold UNIT in G17.
          replace (m_maplen (get_meta_rec st g) * 4096) with (m_maplen (get_meta_rec st g) * 256 * 16) in G17 by lia.
          rewrite Z.div_mul in G17 by lia. lia.
        - lia.
        - exact S16.
        - rewrite Cb, Sp, Sc. unfold UNIT, IB in *. lia.
        - rewrite Cb. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia.
        - exact BIG.
        - exact RSVLE.
        - exact RB0r.
        - exact RE0.
        - intros b' gh' Hb' Fb'. specialize (HD b' gh' Hb' ltac:(rewrite Fb', Fp; exact FB)).
          rewrite (conc_region' st b' r) in HD by (rewrite Fb', Fp; exact Hr). unfold IB in HD.
          clear - HD HAp SZ. lia. (* [comment removed for export] *) }
      intros ms' FP. split; [reflexivity|]. split; [reflexivity|]. unfold hdr_st. rewrite <- V31. exact FP. }
    (* [comment removed for export] *)
    assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - k).
    { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (EQE0 : r_base r + snd e = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
    { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
    assert (DIFF : snd e - snd pf = conc st b + UNIT + get_stride (get_meta_rec st g) * i + get_stride (get_meta_rec st g) - IB - (r_base r + snd pf)).
    { rewrite Se, Cb. unfold UNIT, IB. lia. }
    
    unfold get_nominal_size. apply rimplT_rd8; [peek_same MR|]. cbv zeta.
    rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
    apply rimplT_if; intros HR5.
    - (* [comment removed for export] *)
      apply Z.leb_le in HR5.
      apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
      apply rimplT_rd32; [peek_same MR| peek_same MR| peek_same MR| peek_same MR|].
      destruct (RDB (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0. 
      destruct (RDB (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1. 
      destruct (RDB (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
      destruct (RDB (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
      pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
      set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
      apply rimplT_guard; intros G21. apply Z.leb_le in G21.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
      apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
      
      apply (WALK r32).
      + intros _. split; [exact G20|]. split; [lia|]. split.
        * rewrite <- (EQE 4). rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
          apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
          apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
          -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
          -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
        * rewrite <- (EQE 5), <- (byte_zero_list x5 G25). exact BX5.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE r32), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe.
    - (* [comment removed for export] *)
      apply Z.leb_gt in HR5.
      apply rimplT_guard; intros G22. apply Z.leb_le in G22.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
      apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
      apply rimplT_rd8; [peek_same MR|]. destruct (RDB e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
      apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
      apply rimplT_ret. rewrite V31.
      specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
      assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
      
      apply (WALK 0).
      + intros H. exfalso. clear -H V160. lia.
      + rewrite H160, <- DIFF. exact G22.
      + rewrite H160, <- (EQE (Z.shiftr v3 5)), <- (byte_zero_list xc G23). exact BXc.
      + rewrite <- EQE0, <- (byte_zero_list xe G24). exact BXe. }

  intros r1 s' ms1 (-> & -> & FH). cbv beta iota.
  destruct FH as (x1 & x5 & x6 & x7 & junk & m1 & -> & PE1 & WM1 & MI1 & ST1 & FR1 & MR1).
  set (st1 := hdr_st st pf) in *.
  assert (TK1 : ticks_ok st1) by (unfold st1; apply ticks_ok_hdr_st; exact TK).
  assert (MSL1 : meta_slot st1 g) by (exact (go_slot _ _ _ GO)).
  assert (HK123 : forall k, 1 <= k <= 3 -> exists w, cell_read (get_shadow st (fst pf)) (snd pf - k) = Known w).
  { intros k Hk. unfold pf; cbn [aadd fst snd].
    assert (CS : k = 1 \/ k = 2 \/ k = 3) by lia.
    destruct CS as [-> |[-> | ->]];
      [exists hi; replace (snd c0 + UNIT * off - 1) with (snd c0 + UNIT * off - 1) by lia
      |exists lo8|exists v3];
      [rewrite <- C1 | rewrite <- C2 | rewrite <- C3]; f_equal; unfold UNIT; lia. }
  assert (FP1 : forall a, rfree_fp st1 lo (bv_unsigned sp - 48) a -> rfree_fp st lo (bv_unsigned sp) a).
  { intros a Ha. eapply (rfree_fp_hdr_st st pf lo (bv_unsigned sp) (bv_unsigned sp - 48) a TK HK123); [lia| exact Ha]. }
  assert (ERR1 : rw_cells usegs m1 (errno_addr tp) [C4 errv]).
  { eapply rpres_except_rw_cells; [exact PE1 | exact ERR |]. cbn [cells_size csize Nat.add]. intros a Ha.
    rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
  assert (TF : Z.testbit (m_freed (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_freed (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; left; exact E| reflexivity]. }
  assert (TA : Z.testbit (m_avail (get_meta_rec st g)) i = false).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) i) eqn:E; [exfalso; apply NFR; right; exact E| reflexivity]. }
  (* [comment removed for export] *)
  assert (BLKR : forall stX blk', s_regions stX = s_regions st -> In blk' (lbrm LB blk) -> exists r', s_regions stX !! fst (blk_slot blk') = Some r').
  { intros stX blk' ERX Hb'. rewrite ERX. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' _].
    destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hb') as [(r' & Hr' & _) _ _]. exists r'. exact Hr'. }
  unfold free_tail. cbv zeta. change (get_meta_rec st1 g) with (get_meta_rec st g).
  apply rimplT_guard. intros _.
  apply rimplT_if; intros HC.
  - (* [comment removed for export] *)
    apply negb_true_iff in HC. apply orb_false_iff in HC. destruct HC as [Hfz Hall]. apply Z.eqb_neq in Hfz. apply Z.eqb_neq in Hall.
    apply rimplT_ret.
    eapply evt_mono.
    { eapply (rfree_triv ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 junk lo st st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact Hfz | exact Hall | exact FR1 | exact ST1 | exact LO | reflexivity | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms' TPo. unfold rftriv_post in TPo.
    destruct TPo as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & PE' & WM' & MI' & ST' & MR').
    split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE' | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
             rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR | exact LO | lia]. }
    split; [exact MR'|].
    split. { eapply rpres_except_mono; [eapply rpres_except_trans; [exact PE1| exact PE']|]. intros a Ha. left. exact Ha. }
    split; [intros rid r' H; exact H|].
    split; [intros blk' Hb'; apply (BLKR _ blk' eq_refl Hb')|].
    split; reflexivity.
  - (* [comment removed for export] *)
    
    assert (HNT : m_freed (get_meta_rec st g) = 0 \/ Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) + bit i = mask_upto (m_last_idx (get_meta_rec st g))).
    { apply negb_false_iff in HC. apply orb_true_iff in HC. destruct HC as [HC|HC]; apply Z.eqb_eq in HC; auto. }
    eapply rimplT_evt.
    { eapply (rfree_tocall ra sp gp tp t0 t1 t2 s0 s1 a0 x5 x6 x7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 F fc m1 st1 g i);
        first [exact MR1 | exact MI1 | exact MSL1 | exact TF | exact TA | exact HNT | idtac].
      all: try exact (go_freed _ _ _ GO). all: try exact (go_avail _ _ _ GO). all: change (get_meta_rec st1 g) with (get_meta_rec st g); lia. }
    intros ms2 (y2 & y3 & y4 & y5 & y6 & y7 & ->).
    assert (HLB : forall b', In b' LB' -> In b' LB /\ blk_slot b' <> blk_slot blk).
    { intros b' Hb'. unfold LB', lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [H1 H2]. split; [exact H1|].
      intros E. rewrite E, aptr_eqb_refl in H2. exact H2. }
    assert (K1 : KINV st1 LB' 0).
    { unfold st1. eapply (KINV_hdr_st st LB LB' 0 pf blk r C Hin); [| exact HLB | rewrite Fp, FB; reflexivity | rewrite Fp; exact Hr | symmetry; exact HAp | exact P16m].
      unfold LB', lbrm. apply (KINV_filter_slot st LB 0 (fun s => negb (aptr_eqb s (blk_slot blk)))). exact K0. }
    assert (L1 : LPRE st1 LB' 0 g b i).
    { unfold LB', lbrm. apply (LPRE_intro st1 LB 0 g b i blk); [exact (ki_slts _ _ _ K0) | exists ai; exact Hgh | exact SL | exact NFR | exact NG | pose proof (go_sc _ _ _ GO); change (get_meta_rec st1 g) with (get_meta_rec st g); lia]. }
    assert (Z1 : ZINV st1 []) by (unfold st1; apply ZINV_hdr_st; apply (ZINV_of_CINV _ _ C)).
    assert (OOK1 : oracle_ok m m1 st1).
    { unfold st1. apply oracle_ok_hdr_st; [exact TK|]. eapply (roracle_ok_pres m m m1 st lo (bv_unsigned sp) m); [apply oracle_ok_refl | exact MR | exact LO | exact PE1]. }
    change (wz (conc st g)) with (Z_to_bv 64 (conc st1 g)). change (Z_to_bv 64 (conc st g)) with (Z_to_bv 64 (conc st1 g)).
    eapply (rntf_implT gp tp s4 s5 s6 s7 s8 s9 s10 s11 F fc m LB' lo LO);
      [exact K1 | exact L1 | exact Z1 | exact MR1 | exact MI1 | exact OOK1 | rewrite unsigned_lit by lia; exact ST1 | rewrite unsigned_lit by lia; unfold FUEL; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]; lia |].
    (* [comment removed for export] *)
    
    intros st2 mi ms3 NQ. unfold rntf_q in NQ.
    destruct NQ as (u0 & u1 & u2 & a0v & a1v & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & u14 & m3 & -> & MI3 & ST3 & MR3 & PE3 & [c3 KI3] & ZI3 & FR3 & RES3 & OOK3).
    rewrite unsigned_lit in ST3, PE3 by lia.
    replace (bv_unsigned sp + -48) with (bv_unsigned sp - 48) in PE3 by lia.
    replace (ret_pc (Z_to_bv 64 0x19204)) with (Z_to_bv 64 0x19204) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    assert (PE13 : rpres_except (rfree_fp st lo (bv_unsigned sp)) m m3).
    { eapply rpres_except_trans; [exact PE1|]. eapply rpres_except_mono; [exact PE3| exact FP1]. }
    assert (FR3' : rw_cells usegs m3 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact FR1 |]. cbn [cells_size csize Nat.add length]. intros a Ha Hfp.
      pose proof (rfree_fp_lt st1 m1 lo (bv_unsigned sp - 48) a MR1 LO ltac:(lia) Hfp). lia. }
    assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 errv]).
    { eapply rpres_except_rw_cells; [exact PE3 | exact ERR1 |]. cbn [cells_size csize Nat.add]. intros a Ha.
      rewrite ETP in Ha. eapply rerrno_not_free_fp; [exact MR1 | exact LO | lia]. }
    pose proof (nf_regions _ _ FR3) as ER3. change (s_regions st1) with (s_regions st) in ER3.
    pose proof (nf_brk _ _ FR3) as EB3. change (ctx st1) with (ctx st) in EB3.
    destruct mi as [[bm len]|].
    + (* [comment removed for export] *)
      cbv beta iota.
      destruct RES3 as (-> & -> & LEN & SND & (r2 & Hr2 & Kr2 & Lr2) & NOG).
      replace (negb (len =? 0)) with true by (symmetry; apply negb_true_iff, Z.eqb_neq; lia).
      pose proof Hr2 as Hr2'. rewrite ER3 in Hr2'.
      destruct (WR _ _ Hr2') as (R2B0 & R2AL & R2L & R2C & R2F). ceil_facts.
      assert (R2D : r_base r2 + round_up_pg (r_len r2) <= 0x10000 \/ 0x56000 <= r_base r2) by (apply (rreserved_disjoint1 _ _ R2F); lia).
      assert (CB2 : conc st2 bm = r_base r2) by (rewrite (conc_region' st2 bm r2 Hr2); lia).
      pose proof (round_up_pg_ge (r_len r2)) as RU2.
      eapply rimplT_evt.
      { eapply (rfree_tomunmap sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra (wz (conc st2 bm)) _ _ F fc m3 junk lo len st2 errv);
          [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LEN]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR3']) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ERR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LOv]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) ]. }
      intros ms4 FM. unfold rfmun_post in FM.
      destruct FM as (w0 & w1 & w2 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MU4 & WM4 & MI4 & ST4 & FR4 & ERR4 & MR4).
      eapply (rimplT_munmap m (conc st2 bm) len _ s).
      { eapply rmunmap_spec.
        - rewrite unsigned_lit by lia. exact ST4.
        - exact ERR4.
        - exact MI4.
        - unfold wz. reflexivity.
        - unfold wz. reflexivity.
        - lia.
        - rewrite Lr2, mmap_len_round. lia.
        - lia.
        - rewrite unsigned_lit by lia. lia.
        - rewrite ETP, unsigned_lit by lia. lia.
        - rewrite Lr2, mmap_len_round, unsigned_lit by lia. lia.
        - rewrite ETP, Lr2, mmap_len_round. pose proof (rreserved_tlsF _ _ R2F). pose proof (round_up_pg_ge (r_len r2)). lia.
        - rewrite TP, RATP_unsigned. lia. }
      intros a ms5 MP. cbv beta. unfold rmunmap_post in MP.
      destruct MP as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m5 & -> & MU5 & _ & MI5 & ST5 & ERR5 & ERNG).
      rewrite (munmap_ok_range_val a (rg_err_range _ a ERNG)).
      apply rimplT_ret.
      replace (ret_pc (Z_to_bv 64 0x19234)) with (Z_to_bv 64 0x19234) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      rewrite unsigned_lit in MU5, ST5 by lia. rewrite Lr2, mmap_len_round, ETP in MU5.
      (* [comment removed for export] *)
      assert (AMC2 : amc (ctx st2) = amc (ctx st)) by (rewrite (nf_amc _ _ FR3); reflexivity).
      assert (MP2 : ci_mptrs st2) by (eapply (ci_mptrs_frame st st2 (ci_mp _ _ C) AMC2); [rewrite (nf_areas _ _ FR3); reflexivity| exact ER3]).
      assert (NOG' : forall b' gh, s_groups st2 !! b' = Some gh -> fst b' <> fst bm) by (intros b' gh Hb'; exact (NOG b' gh Hb')).
      pose proof (rptrs_in_norid st2 LB' c3 (fst bm) r2 m4 KI3 ZI3 MR4 Hr2 Kr2 NOG' MP2) as PTR.
      pose proof (rmrep_drop_region st2 (fst bm) PTR m4 MR4) as MRd4.
      assert (MRd5 : rmrep (drop_region (fst bm) st2) m5).
      { eapply (rmrep_after_munmap st2 (fst bm) r2 m4 m5); [exact MRd4 | exact MR4 | exact Hr2 | exact Kr2 | rewrite <- CB2; exact MU5 | lia]. }
      assert (FR5 : rw_cells usegs m5 (bv_unsigned sp + -48) [CB 8 junk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply rrw_cells_agree'; [exact FR4|]. cbn [cells_size csize Nat.add length]. intros x Hx. apply MU5. rewrite wa_unsigned by lia.
        rewrite ?ETP. cbn [outside]. repeat split; lia. }
      eapply evt_mono.
      { eapply (rfree_fin1 sp gp tp z0 z1 z2 s0 s1 (munmap_ret a) z3 z4 z5 z6 z7 z8 z9 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 z10 z11 z12 z13 _ ra (sx32 errv) (wz (conc st2 bm)) (wz len) (rg_errno a errv) F fc m5 junk lo (drop_region (fst bm) st2) errv);
          [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MRd5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [apply le4_sx32]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ERR5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST5]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LOv]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) ]. }
      intros ms' FIN. unfold rffin_post in FIN.
      destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { (* [comment removed for export] *)
        assert (DR : forall x, r_base r2 <= x < r_base r2 + round_up_pg (r_len r2) -> DROPPED st (drop_region (fst bm) st2) x).
        { intros x Hx. exists (fst bm), r2. split; [exact Hr2'|]. split; [| split; [exact Kr2| exact Hx]].
          cbn [drop_region s_regions set_shadow set_regions]. apply lookup_delete_eq. }
        eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m3 m4 MU4)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ RERRNO <= a < RERRNO + 4)); [| exact NC].
          cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
        eapply rpres_except_trans; [eapply (rpres_except_of_munch_nw _ _ m4 m5 MU5)|].
        { intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ RERRNO <= a < RERRNO + 4)); [| exact NC].
          cover_intervals ltac:(fun y Hy => [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [left; apply rfree_fp_stack; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [right; right; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [right; left; apply DR; lia]) ]). }
        eapply (rpres_except_of_munch_nw _ _ m5 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st (drop_region (fst bm) st2) a \/ RERRNO <= a < RERRNO + 4)); [| exact NC].
        cover_intervals ltac:(fun y Hy => [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [left; apply rfree_fp_stack; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [right; right; lia]) ]). }
      split.
      { intros rid r' H. cbn [drop_region s_regions set_shadow set_regions] in H. apply lookup_delete_Some in H. destruct H as [_ H]. rewrite <- ER3. exact H. }
      split.
      { intros blk' Hb'. pose proof (proj1 (List.Forall_forall _ _) (ki_blks _ _ _ KI3) blk' Hb') as BK'.
        destruct BK' as [(g' & i' & bb & SL' & HB' & FB' & _) _ _].
        destruct (go_region _ _ _ (ki_gmetas _ _ _ KI3 bb g' HB')) as (rr & Hrr & _).
        exists rr. cbn [drop_region s_regions set_shadow set_regions]. rewrite lookup_delete_ne; [rewrite <- FB'; exact Hrr|].
        intros E. destruct HB' as [ai' Hbb]. apply (NOG bb _ Hbb). rewrite E. exact FB'. }
      split; [exact EB3|].
      intros brid boff HB0. cbn [drop_region s_regions set_shadow set_regions ctx s_ctx].
      rewrite <- EB3 in HB0. destruct (ki_bk _ _ _ KI3 brid boff HB0) as (rb & Hrb & Krb).
      rewrite lookup_delete_ne; [rewrite ER3; reflexivity |].
      intros E. rewrite <- E, Hr2 in Hrb. assert (rb = r2) by congruence. subst rb. rewrite Kr2 in Krb. discriminate.
    + (* [comment removed for export] *)
      
      cbv beta iota. cbn in RES3. subst a1v.
      apply rimplT_ret.
      eapply evt_mono.
      { eapply (rfree_fin0 sp gp tp u0 u1 u2 s0 s1 u5 u6 u7 u8 u9 u10 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u11 u12 u13 u14 _ ra a0v _ _ F fc m3 junk lo st2 errv);
          [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact TP]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FR3']) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ERR3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST3]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LOv]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) ]. }
      intros ms' FIN. unfold rffin_post in FIN.
      destruct FIN as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & v15 & m' & -> & MUf & WMf & MIf & STf & ERRf & MRf).
      split; [reflexivity|]. do 16 eexists. split; [reflexivity|].
      split; [exact MIf|]. split; [exact STf|]. split; [exact ERRf|]. split; [exact MRf|].
      split.
      { eapply rpres_except_trans; [eapply rpres_except_mono; [exact PE13| intros x Hx; left; exact Hx]|].
        eapply (rpres_except_of_munch_nw _ _ m3 m' MUf).
        intros x Hx NC. apply (outside_of_cover (fun a => rfree_fp st lo (bv_unsigned sp) a \/ DROPPED st st2 a \/ RERRNO <= a < RERRNO + 4)); [| exact NC].
        cover_intervals ltac:(fun y Hy => left; apply rfree_fp_stack; lia). }
      split; [intros rid r' H; rewrite <- ER3; exact H|].
      split; [intros blk' Hb'; apply (BLKR st2 blk' ER3 Hb')|].
      split; [exact EB3|].
      intros brid boff _. rewrite ER3. reflexivity.
Qed.
End Sz1.
Theorem rlibc_free_implT : ltac:(let t := eval cbv delta [rlibc_free_implT__stmt] in rlibc_free_implT__stmt in exact t).
Proof using LO TP. intros ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st blk off errv. ltac2:(SecDiet.SzSec.closeP 'rlibc_free_implT__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End FREE.

End PORT.

End WithCeil.
End TwB.
End RF_free.

(* [comment removed for export] *)
Module RF_free_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep  Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B_reach OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_P__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free_spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_ntf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_free_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
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
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rauxv_ok_pres_B : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof using TLSFACTS. pin_using (fun (TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ RERRNO <= a < RERRNO + 4) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ RERRNO <= a < RERRNO + 4.

(* [comment removed for export] *)
Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof using LO LS MR TLSFACTS st'. pin_using (fun (LO LS MR TLSFACTS st' : unit) => tt). ceil_facts. msec_facts.
  intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  intros [FP|[DR|ER]].
  - pose proof (rfree_fp_lt st m lo sp a MR ltac:(ceil_facts; lia) LS FP). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - lia.
Qed.

Lemma rfp_not_img a : 0x22000 <= a < 0x55000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (RERRNO <= a < RERRNO + 4) -> ~ FPT a.
Proof using LO MR sp st'. pin_using (fun (LO MR sp st' : unit) => tt). ceil_facts. msec_facts.
  intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + exact (N1 X).
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). pose proof (lr_lo_ge r). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
  - exact (N2 ER).
Qed.

(* [comment removed for export] *)
Lemma rfp_not_tls a : the_tb <= a < the_tb + 4096 -> ~ (RERRNO <= a < RERRNO + 4) -> ~ FPT a.
Proof using LO MR sp st'. pin_using (fun (LO MR sp st' : unit) => tt). ceil_facts. msec_facts.
  intros Ha N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_tlsF _ _ RF). pose proof (lr_lo_ge r). pose proof (round_up_pg_ge (r_len r)). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len rb)). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len r)). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len r)). lia.
  - exact (N2 ER).
Qed.

Lemma rfp_not_image a : 0x22000 <= a < 0x55000 -> ~ ralloc_static a -> ~ (RERRNO <= a < RERRNO + 4) -> ~ FPT a.
Proof using LO MR TLSFACTS sp st'. pin_using (fun (LO MR TLSFACTS sp st' : unit) => tt). ceil_facts. msec_facts.
  intros Ha NS NE0. apply rfp_not_img; [exact Ha| |exact NE0]; intros X; fastfirst (first [ noevar_assumption |apply NS; unfold ralloc_static, RLIBC, RCTX, RMLOCK, RSSP_GUARD, RGOT_SSP in *; lia | exfalso; lia]).
Qed.

Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof using BLKR C LO MR SHR TLSFACTS sp. pin_using (fun (BLKR C LO MR SHR TLSFACTS sp : unit) => tt). ceil_facts. msec_facts.
  intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RGF). ceil_facts.
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + destruct X as (rid & r & Hr & NK & Hin).
      assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
      destruct (DJ _ _ _ _ Hr Hrg NE); lia.
    + destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
      * specialize (HD b gh Hb E). unfold IB in HD. lia.
      * destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
        pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
    + destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
      * rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
      * pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
    destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
    assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
    pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - lia.
Qed.

Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof using BLKR C FPT LO LS MR PE SHR. pin_using (fun (BLKR C FPT LO LS MR PE SHR : unit) => tt). ceil_facts. msec_facts.
  intros HLB a Ha CA. apply PE; [exact Ha|].
  destruct CA as [CA|[[CA [NS NE0]]|[(blk' & Hb' & Hab)|[CA NE]]]].
  - apply rfp_not_high. exact CA.
  - apply rfp_not_image; assumption.
  - apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
  - apply rfp_not_tls; assumption.
Qed.

Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof using FPT LO LS MR PE TLSFACTS. pin_using (fun (FPT LO LS MR PE TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
  - intros a Ha. apply rfp_not_high. lia.
  - intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rfree_spec_proof : rfree_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  destruct HP as (LB0 & PERM & MR & [BL AR] & REPL).
  set (st := ps_m s) in *.
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  (* [comment removed for export] *)
  assert (EOFF : off = snd p).
  { destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _ & _ & _ & CR).
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin0) as (k & HkB & (C1 & C2 & C3 & C4)).
    cbn [blk_addr blk_slot blk_id fst snd] in C1, C3, C4. rewrite C1 in OA. rewrite OA in C3. unfold UNIT in C3. lia. }
  (* [comment removed for export] *)
  eapply (implM_evt ssegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rfree_entry) fc None m (seg_rom ssegs))).
  { unfold RFREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  replace (aadd (fst p) (UNIT * snd p)) with (aadd (blk_slot (p, A, n)) (UNIT * off)) by (rewrite EOFF; reflexivity).
  eapply (rraw_free_bridge s (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - apply rimplT_reach.
    apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
    unfold rfree_post. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
    split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
    split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
             intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split; [rewrite ps_rest_set_m; reflexivity|].
    assert (REPL' : rw_cells ssegs m' RMREPLACED [C4 (Z_to_bv 64 0)]).
    { eapply rpres_except_rw_cells; [exact PE| exact REPL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha.
      pose proof the_tb_facts.
      eapply rfp_not_img; try eassumption; unfold RMREPLACED, RCTX in *; lia. }
    unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
    exists (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
    split; [exact MR'|]. split; [| exact REPL']. split.
    + (* [comment removed for export] *) unfold brk_link in *. rewrite EB.
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
    + (* [comment removed for export] *)
      destruct LEAF as (l0 & ans & l1 & FF).
      exact (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_free _ _ _ st LB0 (p, A, n) l0 l1 ans st' AR Hin0 ltac:(unfold blk_ptr; cbn [blk_slot blk_id fst snd]; rewrite <- EOFF; exact FF)).
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
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B_reach OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free_spec.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_ntf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_free_K.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
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
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma rauxv_ok_pres_B : forall C m m' B,
  rauxv_ok m B -> rpres_except C m m' ->
  (forall a, B <= a -> ~ C a) -> (forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> ~ C a) ->
  rauxv_ok m' B.
Proof using TLSFACTS. pin_using (fun (TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros C m m' B (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C1 & A1 & A2 & H) HP HB HC.
  exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd. split; [|split; [|split; [|exact H]]].
  - eapply rpres_except_rw_cells; [exact HP| exact C1|]. cbn. intros a Ha. apply HC. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A1|]. intros a Ha. apply HB. lia.
  - eapply rpres_except_bytes_at; [exact HP| exact A2|]. intros a Ha. apply HB. lia.
Qed.

(* [comment removed for export] *)
Section FP.
Variables (st st' : mstate) (LB0 : list block) (blk : block) (lo sp : Z) (m m' : mem).
Hypothesis C : CINV st LB0.
Hypothesis MR : rmrep st m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LS : lo <= sp.
Hypothesis BLKR : forall blk', In blk' (lbrm LB0 blk) -> exists r', (s_regions st') !! fst (blk_slot blk') = Some r'.
Hypothesis SHR : forall rid r', (s_regions st') !! rid = Some r' -> (s_regions st) !! rid = Some r'.
Hypothesis PE : rpres_except (fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ RERRNO <= a < RERRNO + 4) m m'.

Let FPT := fun a => rfree_fp st lo sp a \/ DROPPED st st' a \/ RERRNO <= a < RERRNO + 4.

(* [comment removed for export] *)
Lemma rfp_not_high a : sp <= a -> ~ FPT a.
Proof using LO LS MR TLSFACTS st'. pin_using (fun (LO LS MR TLSFACTS st' : unit) => tt). ceil_facts. msec_facts.
  intros Ha. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  intros [FP|[DR|ER]].
  - pose proof (rfree_fp_lt st m lo sp a MR ltac:(ceil_facts; lia) LS FP). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & RC & _). ceil_facts. lia.
  - lia.
Qed.

Lemma rfp_not_img a : 0x22000 <= a < 0x56000 -> ~ (RCTX <= a < RCTX + 928) -> ~ (RERRNO <= a < RERRNO + 4) -> ~ FPT a.
Proof using LO MR sp st'. pin_using (fun (LO MR sp st' : unit) => tt). ceil_facts. msec_facts.
  intros Ha N1 N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + exact (N1 X).
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). pose proof (lr_lo_ge r). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_disjoint _ _ RF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RF). lia.
  - exact (N2 ER).
Qed.

(* [comment removed for export] *)
Lemma rfp_not_tls a : the_tb <= a < the_tb + 4096 -> ~ (RERRNO <= a < RERRNO + 4) -> ~ FPT a.
Proof using LO MR sp st'. pin_using (fun (LO MR sp st' : unit) => tt). ceil_facts. msec_facts.
  intros Ha N2. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + destruct X as (rid & r & Hr & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_tlsF _ _ RF). pose proof (lr_lo_ge r). pose proof (round_up_pg_ge (r_len r)). lia.
    + destruct X as (b & gh & Hb & Hin). destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & _ & Sb0 & Sb1 & _).
      destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RF). pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len rb)). lia.
    + destruct X as (rid & r & v & Hr & _ & Hin & _). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len r)). lia.
  - destruct DR as (rid & r & Hr & _ & _ & Hin). destruct (WR _ _ Hr) as (_ & _ & _ & _ & RF). pose proof (rreserved_tlsF _ _ RF). pose proof (round_up_pg_ge (r_len r)). lia.
  - exact (N2 ER).
Qed.

Lemma rfp_not_image a : 0x22000 <= a < 0x56000 -> ~ ralloc_static a -> ~ (RERRNO <= a < RERRNO + 4) -> ~ FPT a.
Proof using LO MR TLSFACTS sp st'. pin_using (fun (LO MR TLSFACTS sp st' : unit) => tt). ceil_facts. msec_facts.
  intros Ha NS NE0. apply rfp_not_img; [exact Ha| |exact NE0]; intros X; fastfirst (first [ noevar_assumption |apply NS; unfold ralloc_static, RLIBC, RCTX, RMLOCK, RSSP_GUARD, RGOT_SSP in *; lia | exfalso; lia]).
Qed.

Lemma rfp_not_block blk' a : In blk' (lbrm LB0 blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FPT a.
Proof using BLKR C LO MR SHR TLSFACTS sp. pin_using (fun (BLKR C LO MR SHR TLSFACTS sp : unit) => tt). ceil_facts. msec_facts.
  intros Hb' Hab. pose proof MR as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). ceil_facts.
  pose proof Hb' as Hb0. unfold lbrm in Hb0. apply In_filter_iff in Hb0. destruct Hb0 as [HinL _].
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' HinL) as [(rg & Hrg & Krg & A16 & AEND & AL & UNK) HD _].
  destruct (UNK a Hab) as [h UNKa].
  destruct (WR _ _ Hrg) as (_ & _ & _ & RGC & RGF). pose proof (rreserved_disjoint _ _ RGF) as (?&?&?&?). pose proof (rreserved_tlsF _ _ RGF). ceil_facts.
  pose proof (lr_lo_group rg Krg) as LRG.
  intros [FP|[DR|ER]].
  - destruct FP as [[X|[X|X]]|[X|X]].
    + lia.
    + unfold RCTX in X. lia.
    + destruct X as (rid & r & Hr & NK & Hin).
      assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hrg in Hr; assert (r = rg) by congruence; subst; exact (NK Krg)).
      destruct (DJ _ _ _ _ Hr Hrg NE); lia.
    + destruct X as (b & gh & Hb & Hin). destruct (N.eq_dec (fst b) (fst (blk_slot blk'))) as [E|NE].
      * specialize (HD b gh Hb E). unfold IB in HD. lia.
      * destruct (rgroup_conc st b gh WF Hb) as (rb & Hrb & Cb & Krb & Sb0 & Sb1 & _).
        pose proof (lr_lo_group rb Krb). destruct (DJ _ _ _ _ Hrb Hrg NE); lia.
    + destruct X as (rid & r & v & Hr & Kr & Hin & HC). destruct (N.eq_dec rid (fst (blk_slot blk'))) as [->|NE].
      * rewrite Hrg in Hr. assert (r = rg) by congruence. subst r. rewrite UNKa in HC. discriminate.
      * pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - destruct DR as (rid & r & Hr & Hr' & Kr & Hin).
    destruct (BLKR blk' Hb') as [r' Hr'']. pose proof (SHR _ _ Hr'') as HrgS. rewrite Hrg in HrgS. assert (r' = rg) by congruence. subst r'.
    assert (NE : rid <> fst (blk_slot blk')) by (intros ->; rewrite Hr'' in Hr'; discriminate).
    pose proof (lr_lo_group r Kr). destruct (DJ _ _ _ _ Hr Hrg NE); lia.
  - lia.
Qed.

Lemma rheap_pres_free LB' : (forall b, In b LB' -> In b (lbrm LB0 blk)) -> rheap_pres LB' sp m m'.
Proof using BLKR C FPT LO LS MR PE SHR. pin_using (fun (BLKR C FPT LO LS MR PE SHR : unit) => tt). ceil_facts. msec_facts.
  intros HLB a Ha CA. apply PE; [exact Ha|].
  destruct CA as [CA|[[CA [NS NE0]]|[(blk' & Hb' & Hab)|[CA NE]]]].
  - apply rfp_not_high. exact CA.
  - apply rfp_not_image; assumption.
  - apply (rfp_not_block blk' a); [apply HLB; exact Hb'| exact Hab].
  - apply rfp_not_tls; assumption.
Qed.

Lemma rauxv_ok_free B : rauxv_ok m B -> sp <= B -> rauxv_ok m' B.
Proof using FPT LO LS MR PE TLSFACTS. pin_using (fun (FPT LO LS MR PE TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros AV HB. eapply rauxv_ok_pres_B; [exact AV | exact PE | |].
  - intros a Ha. apply rfp_not_high. lia.
  - intros a Ha. apply rfp_not_img; unfold RAUXV_CELL, RLIBC, RCTX in *; lia.
Qed.
End FP.

(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem rfree_spec_proof : rfree_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A n lo B errv
         HP Hin AV HB ST LO SLO ERR MI TP A0.
  destruct HP as (LB0 & PERM & MR & [BL AR] & REPL).
  set (st := ps_m s) in *.
  assert (Hin0 : In (p, A, n) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, n) Hin0) as BK.
  destruct BK as [(g & i & b & SL & HBg & FB & Ii & NFR & (off & O0 & OA & OS & OK & HK)) NG SZ].
  cbn [blk_addr blk_slot fst snd] in OA.
  (* [comment removed for export] *)
  assert (EOFF : off = snd p).
  { destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _ & _ & _ & CR).
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.Forall2_In_l _ _ _ _ CR Hin0) as (k & HkB & (C1 & C2 & C3 & C4)).
    cbn [blk_addr blk_slot blk_id fst snd] in C1, C3, C4. rewrite C1 in OA. rewrite OA in C3. unfold UNIT in C3. lia. }
  (* [comment removed for export] *)
  eapply (implM_evt usegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rfree_entry) fc None m (seg_rom usegs))).
  { unfold RFREE_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  replace (aadd (fst p) (UNIT * snd p)) with (aadd (blk_slot (p, A, n)) (UNIT * off)) by (rewrite EOFF; reflexivity).
  eapply (rraw_free_bridge s (aadd (blk_slot (p, A, n)) (UNIT * off)) m
            (fun st' s' ms' => rfree_end ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo st (lbrm LB0 (p, A, n)) m errv s st' s' ms'
                               /\ leaf_of m (free st (Some (aadd (blk_slot (p, A, n)) (UNIT * off)))) st')).
  - apply rimplT_reach.
    apply (rlibc_free_implT gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 lo LO TP ra sp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m s st (p, A, n) off errv C Hin0 O0 OA MR MI ST);
      [unfold RFREE_STACK in SLO; lia | exact ERR | exact A0].
  - intros st' s' ms'' [[-> FE] LEAF]. cbv beta.
    destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m' & -> & MI' & ST' & ERR' & MR' & PE & SHR & BLKR & EB & BRKR).
    pose proof (lb_remove_lbrm LB p A n (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    assert (SLO' : lo <= bv_unsigned sp) by (unfold RFREE_STACK in SLO; lia).
    unfold rfree_post. do 16 eexists. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|].
    split; [exact (rauxv_ok_free st st' lo (bv_unsigned sp) m m' MR LO SLO' PE B AV HB)|].
    split. { apply (rheap_pres_free st st' LB0 (p, A, n) lo (bv_unsigned sp) m m' C MR LO SLO' BLKR SHR PE).
             intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split; [rewrite ps_rest_set_m; reflexivity|].
    assert (REPL' : rw_cells usegs m' RMREPLACED [C4 (Z_to_bv 64 0)]).
    { eapply rpres_except_rw_cells; [exact PE| exact REPL|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha.
      pose proof the_tb_facts.
      eapply rfp_not_img; try eassumption; unfold RMREPLACED, RCTX in *; lia. }
    unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m.
    exists (lbrm LB0 (p, A, n)). split; [rewrite ELB; apply lbrm_perm; exact PERM|].
    split; [exact MR'|]. split; [| exact REPL']. split.
    + (* [comment removed for export] *) unfold brk_link in *. rewrite EB.
      destruct (c_brk (ctx st)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
      unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL.
    + (* [comment removed for export] *)
      destruct LEAF as (l0 & ans & l1 & FF).
      exact (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_free _ _ _ st LB0 (p, A, n) l0 l1 ans st' AR Hin0 ltac:(unfold blk_ptr; cbn [blk_slot blk_id fst snd]; rewrite <- EOFF; exact FF)).
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_free_spec.

(* [comment removed for export] *)
Module RF_realloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Malloc_fp. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocTreeB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B_reach OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_WSlot2__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_mm_syscalls. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_P__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_free_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.F_malloc_top.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_enframe. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_small. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RMalloc_ifaceP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_get_meta__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_free_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_reallocA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free_spec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_reallocA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_reallocB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_reallocC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mremap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_P__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free_spec.
From Stdlib Require Import Permutation.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_invR.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; ceil_facts; lia.


Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Lemma areach_set_tick {resv} st LB t : AREACH_from resv st LB -> (s_tick st <= t)%N -> AREACH_from resv (set_tick t st) LB.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) Ht. exists L, LS, BL.
  split; [apply INVL_set_tick; [exact Ht| exact INV]|]. split; [exact LIVE|]. split; [exact RESV|]. split; [exact SEC| exact CR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rrfinQ (m : mem) (st0 : mstate) (s : PState)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (blk : block) (bs : list byte) (n lo B : Z)
    (res : mstate * optr) (s' : PState) (msf : machine_state) : Prop :=
  exists (m' : mem) (errv' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    msf = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (oconc (fst res) (snd res))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rmrep (fst res) m' /\ brk_link_ps (fst res) s'
    /\ rheap_pres (lbrm LB blk) (bv_unsigned sp) m m'
    /\ rw_cells ssegs m' RMREPLACED [C4 (Z_to_bv 64 0)]
    /\ ps_m s' = ps_m s /\ ps_rest s' = ps_rest s
    /\ match snd res with
       | None => errv' = Z_to_bv 64 ENOMEM /\ rw_cells ssegs m' (blk_addr blk) [CB (Z.to_nat (blk_size blk)) bs]
       | Some q => rblock_range (conc (fst res) q) n
                   /\ exists junk, rw_cells ssegs m' (conc (fst res) q)
                        [CB (Z.to_nat (Z.min (blk_size blk) n)) (firstn (Z.to_nat (Z.min (blk_size blk) n)) bs); CB (Z.to_nat (n - Z.min (blk_size blk) n)) junk]
       end.

(* [comment removed for export] *)
Lemma bytes_at_firstn m a (bs0 : list byte) k : bytes_at ssegs m a bs0 -> bytes_at ssegs m a (firstn k bs0).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H. rewrite <- (firstn_skipn k bs0) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rw_cells_CB_prefix_agree m A n (J bs1 : list byte) :
  rw_cells ssegs m A [CB n J] -> bytes_at ssegs m A bs1 -> (length bs1 <= n)%nat ->
  rw_cells ssegs m A [CB (length bs1) bs1; CB (n - length bs1) (skipn (length bs1) J)].
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros [[Hwf HB] HW] H1 Hlen. cbn in Hwf. destruct Hwf as [HJ _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  split; [split|].
  - cbn. repeat split; try reflexivity. rewrite length_skipn. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact H1|].
    rewrite <- (firstn_skipn (length bs1) J) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
    rewrite length_firstn, Nat.min_l in HB by lia. exact HB.
  - cbn [cells_size csize] in HW |- *. replace (length bs1 + (n - length bs1 + 0))%nat with (n + 0)%nat by lia. exact HW.
Qed.

Lemma set_size_land31 p e n b st : set_size p e n (Z.land b 31) st = set_size p e n b st.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. unfold set_size. rewrite <- Z.land_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Definition rr_fallback_tree (st : mstate) (pf : aptr) (n : Z) : Malloc.M (mstate * optr) :=
  sbind (malloc st n) (fun x => let '(st2, q) := x in
    match q with
    | Some q0 => sbind (free st2 (Some pf)) (fun st3 => ret (st3, Some q0))
    | None => ret (st2, @None aptr)
    end).

(* [comment removed for export] *)
Definition rr_fb_mem (m : mem) (st0 : mstate) (sp tp : word) (LB : list block) (blk : block) (bs : list byte) (lo B : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 : word) (m1 : mem) : Prop :=
  mem_inv ssegs m1 /\ stk ssegs m1 lo (bv_unsigned sp + -64) /\ rmrep st0 m1 /\ rauxv_ok m1 B
  /\ rw_cells ssegs m1 RMREPLACED [C4 (Z_to_bv 64 0)]
  /\ rw_cells ssegs m1 (blk_addr blk) [CB (Z.to_nat (blk_size blk)) bs]
  /\ rheap_pres (lbrm LB blk) (bv_unsigned sp) m m1
  /\ (exists errv1 : word, rw_cells ssegs m1 (errno_addr tp) [C4 errv1])
  /\ rw_cells ssegs m1 (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6).

Definition rr_fallback_ok (m : mem) (st0 : mstate) (s : PState)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (blk : block) (off : Z) (bs : list byte) (n lo B : Z) : Prop :=
  forall (rax x0 x1 x2 y0 y1 a0' z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 x3 x4 x5 x6 : word) (m1 : mem),
    rr_fb_mem m st0 sp tp LB blk bs lo B ra s0 s1 s2 s3 s4 s5 s6 m1 ->
    bv_unsigned a0' = blk_addr blk ->
    rimplT m (rr_fallback_tree (set_tick (N.succ (s_tick st0)) st0) (aadd (blk_slot blk) (UNIT * off)) n) s
      (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 x1 x2 y0 y1 a0' (Z_to_bv 64 n) z2 z3 z4 z5 z6 z7
               (Z_to_bv 64 (blk_addr blk + blk_size blk)) y3 y4 y5 y6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
          F (Z_to_bv 64 0x1a4c4) fc None m1 (seg_rom ssegs)).

(* [comment removed for export] *)
Definition rbig63_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m m1 : mem) (s : PState) (LB : list block) (blk : block) (off : Z) (bs : list byte) (n lo B : Z)
         (g b : aptr) (ai : Z) (r : region) (i v3 rsv : Z) (t2 a0 a5 t3 t4 t5 t6 : word),
  let st0 := ps_m s in
  let st := set_tick (N.succ (s_tick st0)) st0 in
  let mr := get_meta_rec st0 g in
  let c0 := blk_slot blk in
  let pf := aadd c0 (UNIT * off) in
  let e := aadd (aadd b (UNIT + get_stride mr * Z.land v3 31)) (get_stride mr - IB) in
  let P := r_base r + snd pf in
  let E := r_base r + snd e in
  (* [comment removed for export] *)
  RAREACH st0 LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st0 c0 + UNIT * off -> brk_link_ps st0 s ->
  s_slots st0 !! c0 = Some (g, i) -> s_groups st0 !! b = Some (mkGhdr (Some g) ai) -> fst b = fst c0 ->
  s_regions st0 !! (fst b) = Some r -> r_kind r = RKGroup ->
  m_sizeclass mr = 63 -> m_last_idx mr = 0 -> 0 < m_maplen mr -> 0 <= i <= m_last_idx mr -> Z.land v3 31 = i ->
  cell_read (get_shadow st0 (fst pf)) (snd pf - 3) = Known v3 -> 0 <= v3 < 256 ->
  UNIT * off + blk_size blk <= get_stride mr - IB -> 0 <= blk_size blk ->
  MMAP_THRESHOLD <= n < 2^32 -> rsv = E - P - blk_size blk -> 0 <= rsv ->
  (* [comment removed for export] *)
  bv_unsigned sp <= B -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK -> tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 -> wmono ssegs m m1 ->
  rr_fb_mem m st0 sp tp LB blk bs lo B ra s0 s1 s2 s3 s4 s5 s6 m1 ->
  rr_fallback_ok m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk off bs n lo B ->
  rimplT m
    (guard 70 (m_sizeclass mr =? 63)
       (let base := snd pf - snd (aadd b (UNIT + get_stride mr * Z.land v3 31)) in
        let needed := round_up_pg (n + base + UNIT + IB) in
        let oldlen := m_maplen mr * 4096 in
        let rid := fst (aadd b (UNIT + get_stride mr * Z.land v3 31)) in
        if oldlen =? needed
        then ret (resize63 st rid needed pf n (Z.land v3 31), Some pf)
        else
         SVis (EMremap (conc st (rid, 0)) oldlen needed)
           (fun r0 : Z =>
              if negb (mremap_answer_ok st rid (conc st (rid, 0)) oldlen needed r0)
              then bad_answer (ret (st0, @None aptr))
              else if is_err r0 then rr_fallback_tree st pf n
              else ret (big_resize st g rid r0 needed pf n (Z.land v3 31), Some pf)))
       (ret (st0, @None aptr)))
    s
    (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (r_base r + snd c0)) t2 s0 (wz (conc st0 g))
             a0 (Z_to_bv 64 n) (wz (conc st0 b)) (Z_to_bv 64 (m_sizeclass mr)) (wz (meta_word mr)) a5 (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
             (Z_to_bv 64 (blk_addr blk + blk_size blk)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1a3dc) fc None m1 (seg_rom ssegs)).

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.
Hypothesis RBIG63 : rbig63_stmt.

(* [comment removed for export] *)
Definition rmalloc_implT_gen__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : mstate) (LB : list block) (n lo B : Z) (errv : word),
  rmrep st m -> brk_link_ps st s -> RAREACH st LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] -> mem_inv ssegs m -> tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplT m (malloc st n) s
         (fun res s' msf => rfinQ m st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo B res s' msf /\ leaf_of m (malloc st n) res)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s st LB n lo B errv : ltac2:(SecDiet.SzSec.tyM 'rmalloc_implT_gen__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmalloc_implT_gen__body : ltac2:(SecDiet.SzSec.bodyP 'rmalloc_implT_gen__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros MR BL AR AUXB SB ST CLO LO ERR MI TP HA N.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| ceil_facts; lia]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  apply (rimplT_reach m (malloc st n)). unfold malloc.
  eapply rimplT_bind.
  { exact (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)). }
  intros [st2 r] s' ms'' CQ. cbn [rcoreQ] in CQ.
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    ceil_facts.
    eapply rimplT_mono.
    { exact (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                MR2 TK2 UA2 MI2 ST2 ltac:(ceil_facts; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO). }
    intros [st' p'] s'' msf [-> EP]. unfold renf_post in EP.
    destruct EP as (st'_ & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF).
    inversion ER; subst st'_ p'. clear ER.
    destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    unfold rfinQ. cbn [fst snd oconc]. exists m', errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite (rerrno_addr tp TP). pose proof the_tb_facts.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)).
             intros a Ha [X|X]; subst lo_s hi_s; lia. }
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split; [exact MR'|]. split; [exact MRELf|].
    split. { unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2. }
    split; [exact PEf|]. split; [exact PSM|]. split; [exact PSF|].
    split. { unfold rblock_range; ceil_facts. rewrite EA. pose proof the_tb_facts.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    exists ujunk. exact UCH.
  - (* [comment removed for export] *)
    destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & EEN2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    cbv beta iota. apply rimplT_ret. apply evt_done.
    unfold rfinQ. cbn [fst snd oconc]. exists m1, errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split; [exact MR2|]. split; [exact MREL|]. split; [exact BL2|]. split; [exact PE2|]. split; [exact PSM|]. split; [exact PSF| exact EEN2].
Qed.
End Sz1.
Lemma rmalloc_implT_gen : ltac:(let t := eval cbv delta [rmalloc_implT_gen__stmt] in rmalloc_implT_gen__stmt in exact t).
Proof using AS_PRE RAS RBIG. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s st LB n lo B errv. ltac2:(SecDiet.SzSec.closeP 'rmalloc_implT_gen__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rrealloc_fallback__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (s : PState) (LB : list block) (blk : block) (off : Z) (bs : list byte) (n lo B : Z),
  let st0 := ps_m s in
  RAREACH st0 LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st0 (blk_slot blk) + UNIT * off ->
  brk_link_ps st0 s -> bv_unsigned sp <= B -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  tp = Z_to_bv 64 RATP -> 0 <= n < 2^32 ->
  rr_fallback_ok m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk off bs n lo B.
Section Sz2.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB blk off bs n lo B : ltac2:(SecDiet.SzSec.tyM 'rrealloc_fallback__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_fallback__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_fallback__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
  intros st0 AR Hin Hoff HA BL SB LO SLO TP N rax x0 x1 x2 y0 y1 a0' z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 x3 x4 x5 x6 m1 (MI1 & ST1 & MR1 & AUX1 & REPL1 & CH1 & HP1 & [errv1 ERR1] & FR1) HP0.
  unfold RREALLOC_STACK in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as LOv. ceil_facts.
  set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (ARt : RAREACH st LB) by (apply areach_set_tick; [exact AR| cbn; lia]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ ARt) as MFt.
  assert (MRt : rmrep st m1) by (apply rmrep_set_tick; exact MR1).
  assert (BLt : brk_link_ps st s) by exact BL.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as -> by (rewrite HA in OA; unfold UNIT in OA; lia). clear OA.
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as [(r & Hr & Kr & A16 & AEND & _ & _) _ _].
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *.
  pose proof MR1 as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  pose proof (rreserved_tlsF _ _ RF) as TLSr. pose proof (rreserved_disjoint1 _ _ RF ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as DRr.
  pose proof (rw_cells_bytes_at _ _ _ _ CH1) as BS1. cbn [cells_bytes cbytes] in BS1. rewrite app_nil_r in BS1.
  assert (LBS : length bs = Z.to_nat (blk_size blk)) by (destruct CH1 as [[Hwf _] _]; cbn in Hwf; exact (proj1 Hwf)).
  unfold rr_fallback_tree.
  (* [comment removed for export] *)
  apply rimplT_from_evt. step. step. step. step. apply evt_done.
  eapply rimplT_bind.
  { eapply (rmalloc_implT_gen (Z_to_bv 64 0x1a4d4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp _ _ _ (Z_to_bv 64 n) a0' (Z_to_bv 64 n) (Z_to_bv 64 n)
              _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m1 s st LB n lo B errv1 MRt BLt ARt AUX1);
      [rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| exact LO| rewrite unsigned_lit by lia; lia| exact ERR1| exact MI1| exact TP| reflexivity| exact N]. }
  intros [st2 q] s2' msf [FQ LEAF]. unfold rfinQ in FQ. cbn [fst snd] in FQ.
  destruct FQ as (m2 & errv2 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI2 & ST2 & ERR2 & AUX2 & MR2 & MREL & BL2 & PE2 & PSM & PSF & RES).
  rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in PE2 by lia.
  replace (ret_pc (Z_to_bv 64 0x1a4d4)) with (Z_to_bv 64 0x1a4d4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (KEEP2 : forall A cs, rw_cells ssegs m1 A cs -> bv_unsigned sp - 64 <= A -> rw_cells ssegs m2 A cs).
  { intros A cs H HA0. eapply rpres_except_rw_cells; [exact PE2| exact H|]. intros a Ha Hfp.
    destruct (rmalloc_fp_cases st st2 lo (bv_unsigned sp + -64) m1 m2 a MRt MR2 Hfp); ceil_facts; lia. }
  pose proof (KEEP2 _ _ FR1 ltac:(lia)) as FR2.
  assert (REPL2 : rw_cells ssegs m2 RMREPLACED [C4 (Z_to_bv 64 0)]).
  { eapply rpres_except_rw_cells; [exact PE2| exact REPL1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha Hfp.
    pose proof the_tb_facts.
    destruct (rmalloc_fp_image st st2 lo (bv_unsigned sp + -64) m1 m2 a MRt MR2 Hfp LO ltac:(unfold RMREPLACED, RCTX in Ha; lia)); unfold RMREPLACED, RCTX in *; lia. }
  pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp + -64) m1 m2 MFt MRt MR2 MREL PE2 LO ltac:(lia)) as HPf.
  assert (HP2 : rheap_pres (lbrm LB blk) (bv_unsigned sp) m m2).
  { eapply rheap_pres_trans; [exact HP1|]. eapply rheap_pres_weaken; [exact HPf| lia|]. intros b' Hb'. unfold lbrm in Hb'. apply In_filter_iff in Hb'. exact (proj1 Hb'). }
  assert (CH2 : rw_cells ssegs m2 (blk_addr blk) [CB (Z.to_nat (blk_size blk)) bs]).
  { eapply rheap_pres_rw_cells; [exact HPf| exact CH1|]. cbn [cells_size csize Nat.add]. right. right. left. exists blk. split; [exact Hin| lia]. }
  destruct q as [q|].
  - (* [comment removed for export] *)
    destruct RES as [BR [J JCH]]. cbn [oconc].
    set (Q := conc st2 q) in *.
    pose proof BR as (BQ0 & BQ16 & _ & BQC & BQI & BQT).
    (* [comment removed for export] *)
    destruct LEAF as (l0 & ans & l1 & FF). unfold lrun in FF.
    destruct (MallocTree.strel_follow _ _ _ (malloc_control pans_l pupd_l pans_l_range st n l0) ans (l1, (st2, Some q)) FF) as ([cst c] & FC & [Hcst Hpc]).
    cbn [fst snd] in Hcst, Hpc. fold (lrun l0 (malloc st n)) in FF.
    destruct c as [c|]; [| destruct Hpc]. destruct Hpc as [Efst [offq Eoffq]].
    assert (Eq : q = aadd c (UNIT * offq)) by (destruct q, c; unfold aadd; cbn in Efst, Eoffq |- *; subst; reflexivity).
    set (nb := ((c, offq), Q, n) : block).
    pose proof (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_some _ _ _ st LB n l0 l1 ans st2 q cst c offq ARt ltac:(lia) FF FC Eq) as AR2. fold Q in AR2. fold nb in AR2.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR2) as C2.
    assert (NEQc : c <> c0).
    { pose proof (ci_nodup _ _ C2) as ND. cbn [map nb blk_slot fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
      intros E. apply NI. rewrite E. subst c0. apply in_map. exact Hin. }
    assert (HEAP2 : RHEAP (set_m st2 s2') (nb :: LB) m2).
    { unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m. exists (nb :: LB). split; [apply Permutation.Permutation_refl|].
      split; [exact MR2|]. split; [| exact REPL2]. split; [apply (proj1 (brk_link_ps_iff st2 s2')); exact BL2| exact AR2]. }
    assert (DISJ : Q + n <= blk_addr blk \/ blk_addr blk + blk_size blk <= Q).
    { pose proof (RHEAP_blocks_disjoint_proof (set_m st2 s2') (nb :: LB) m2 nb blk HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hin)) as D.
      cbn [nb blk_addr blk_size blk_id fst snd] in D. apply D. intros E. apply NEQc. subst c0. unfold blk_slot. apply (f_equal fst) in E. cbn [fst] in E. exact E. }
    set (k1z := Z.min (blk_size blk) n). set (k1 := Z.to_nat k1z).
    assert (K1R : 0 <= k1z <= n /\ k1z <= blk_size blk) by (subst k1z; clear -N SZ; lia).
    assert (LK1 : length (firstn k1 bs) = k1) by (rewrite length_firstn, LBS; subst k1 k1z; clear -N SZ; lia).
    pose proof (bytes_at_firstn m2 (blk_addr blk) bs k1 ltac:(pose proof (rw_cells_bytes_at _ _ _ _ CH2) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X)) as SRC2.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB _ m2 Q [] (Z.to_nat n) J [] [k1; (Z.to_nat n - k1)%nat] JCH ltac:(cbn; subst k1 k1z; clear -N SZ; lia)) as JCH'.
    cbn [mk_CB_cells app] in JCH'. apply rw_cells_split2 in JCH'. destruct JCH' as [JA JB]. cbn [csize] in JB.
    (* [comment removed for export] *)
    assert (CALL : forall a1v a2v : word, bv_unsigned a2v = k1z ->
      evt ssegs (fun ms' => exists (x0' x1' x2' z1' z2' z3' z4' z5' z6' z7' x3' x4' x5' x6' : word) (m3 : mem),
          ms' = MS (mkR (Z_to_bv 64 0x1a4fc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0' x1' x2' (wz Q) a0' a0' z1' z2' z3' z4' z5' z6' z7'
                        (Z_to_bv 64 (blk_addr blk + blk_size blk)) y3 y4 y5 y6 s7 s8 s9 s10 s11 x3' x4' x5' x6')
                   F (Z_to_bv 64 rfree_entry) fc None m3 (seg_rom ssegs)
          /\ munch [(Q, Q + k1z)] m2 m3 /\ wmono ssegs m2 m3 /\ mem_inv ssegs m3
          /\ rw_cells ssegs m3 Q [CB k1 (firstn k1 bs)])
        (MS (mkR (Z_to_bv 64 0x1a4d4) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 n) a0' (wz Q) a1v a2v v3 v4 v5 v6 v7
                 (Z_to_bv 64 (blk_addr blk + blk_size blk)) y3 y4 y5 y6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x1a4e8) fc None m2 (seg_rom ssegs))).
    { intros a1v a2v HA2.
      (* [comment removed for export] *)
      step. step. step.
      eapply evt_cut.
      { eapply (memcpy_spec _ _ gp tp _ _ _ (wz Q) a0' (wz Q) a0' a2v _ _ _ _ _ _ y3 y4 y5 y6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 (firstn k1 bs) (firstn k1 J)).
        - rewrite HP0. exact SRC2.
        - rewrite HA2, LK1. reflexivity.
        - unfold wz. rewrite unsigned_lit by (ceil_facts; lia). rewrite HA2. subst k1. exact JA.
        - unfold wz. rewrite unsigned_lit by (ceil_facts; lia). rewrite HA2, HP0. clear -DISJ K1R. lia.
        - exact MI2. }
      intros ms' PM. unfold memcpy_post in PM.
      destruct PM as (x0' & x1' & x2' & z1' & z2' & z3' & z4' & z5' & z6' & z7' & x3' & x4' & x5' & x6' & m3 & -> & MU3 & WM3 & MI3 & DST3 & _).
      unfold wz in MU3, DST3. rewrite !unsigned_lit in MU3 by (ceil_facts; lia). rewrite unsigned_lit in DST3 by (ceil_facts; lia).
      rewrite HA2 in MU3, DST3.
      replace (ret_pc (Z_to_bv 64 0x1a4f4)) with (Z_to_bv 64 0x1a4f4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      (* [comment removed for export] *)
      step. step. apply evt_done. do 15 eexists. split; [reflexivity|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. subst k1. exact DST3. }
    eapply rimplT_evt.
    { (* [comment removed for export] *)
      step. if_cases K; zify_cond K. { exfalso. unfold wz in K. rewrite unsigned_lit in K by (ceil_facts; lia). clear -K BQ0. lia. }
      step. step. step. if_cases K2; zify_cond K2.
      - eapply CALL. rewrite unsigned_lit by lia. rewrite HP0 in K2. subst k1z. clear -K2 N SZ. lia.
      - step. eapply CALL. rewrite HP0 in K2 |- *. rewrite unsigned_lit by lia. subst k1z. clear -K2 N SZ. lia. }
    cbv beta. intros ms3 (x0' & x1' & x2' & z1' & z2' & z3' & z4' & z5' & z6' & z7' & x3' & x4' & x5' & x6' & m3 & -> & MU3 & WM3 & MI3 & DST3).
    (* [comment removed for export] *)
    assert (DJQ : forall A k, 0 <= k -> (A + k <= Q \/ Q + k1z <= A) -> disjoint_from [(Q, Q + k1z)] A k) by (intros A k Hk HA0; cbn; clear -HA0 Hk; lia).
    assert (HEAP3 : RHEAP (set_m st2 s2') (nb :: LB) m3).
    { eapply (RHEAP_frame_proof (set_m st2 s2') (nb :: LB) m2 m3); [exact HEAP2| exact MU3| exact WM3|].
      constructor; [| constructor]. right. right. left. exists nb. split; [left; reflexivity|]. cbn [nb blk_addr blk_size fst snd]. clear -K1R. lia. }
    assert (MR3 : rmrep st2 m3).
    { destruct HEAP3 as (LBx & _ & MRx & _). rewrite ps_m_set_m in MRx. exact MRx. }
    assert (ST3 : stk ssegs m3 lo (bv_unsigned sp + -64)).
    { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. apply DJQ; [clear -SLO LOv SPR; lia|]. right. ceil_facts. clear -BQC K1R LOv SLO. lia. }
    assert (ERR3 : rw_cells ssegs m3 (errno_addr tp) [C4 errv2]).
    { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. rewrite (rerrno_addr tp TP). apply DJQ; [cbn; lia|]. cbn. pose proof the_tb_facts. clear -H BQT K1R. lia. }
    assert (FR3 : rw_cells ssegs m3 (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6)).
    { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. apply DJQ; [cbn; lia|]. right. ceil_facts. clear -BQC K1R LOv SLO. lia. }
    assert (REPL3 : rw_cells ssegs m3 RMREPLACED [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact REPL2| exact MU3| exact WM3|]. apply DJQ; [cbn; lia|]. unfold RMREPLACED, RCTX. cbn. clear -BQI K1R. lia. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. ceil_facts.
      clear -BQC BQI K1R SB SLO LOv. lia. }
    assert (JB3 : rw_cells ssegs m3 (Q + Z.of_nat k1) [CB (Z.to_nat n - k1) (firstn (Z.to_nat n - k1) (skipn k1 J))]).
    { eapply rw_cells_transport; [exact JB| exact MU3| exact WM3|]. apply DJQ; [cbn; lia|]. right. subst k1. clear -K1R. lia. }
    assert (HP3 : rheap_pres (lbrm LB blk) (bv_unsigned sp) m2 m3).
    { intros x Hx Hcx. split; [| apply WM3]. apply MU3. rewrite wa_unsigned by lia. cbn. split; [| exact Logic.I].
      destruct Hcx as [X|[[X _]|[(b' & Hb' & Xb)|[X _]]]].
      - ceil_facts. clear -X BQC K1R LOv SLO. lia.
      - clear -X BQI K1R. lia.
      - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' NEb].
        destruct (RHEAP_blocks_disjoint_proof (set_m st2 s2') (nb :: LB) m2 nb b' HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb')) as [D|D].
        + cbn [nb blk_id fst]. intros E.
          pose proof (ci_nodup _ _ C2) as ND. cbn [map nb blk_slot fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
          apply (f_equal fst) in E. cbn [fst] in E. replace c with (blk_slot b') by (rewrite E; reflexivity). apply in_map. exact Hb'.
        + cbn [nb blk_addr blk_size fst snd] in D. clear -D Xb K1R. lia.
        + cbn [nb blk_addr blk_size fst snd] in D. clear -D Xb K1R. lia.
      - pose proof the_tb_facts. clear -X H BQT K1R. lia. }
    (* [comment removed for export] *)
    assert (HA2 : blk_addr blk = conc st2 c0 + UNIT * off).
    { pose proof (areach_blk_addr st0 LB blk AR Hin) as E0. pose proof (areach_blk_addr st2 (nb :: LB) blk AR2 ltac:(right; exact Hin)) as E2.
      fold c0 in E0, E2. rewrite HA in E0. replace off with (snd (blk_id blk)) by (unfold UNIT in E0; clear -E0; lia). exact E2. }
    (* [comment removed for export] *)
    eapply rimplT_bind.
    { apply (rlibc_free_implT gp tp (wz Q) a0' (Z_to_bv 64 (blk_addr blk + blk_size blk)) y3 y4 y5 y6 s7 s8 s9 s10 s11 F fc (nb :: LB) lo LO TP
               (Z_to_bv 64 0x1a4fc) (Z_to_bv 64 (bv_unsigned sp + -64)) x0' x1' x2' a0' z1' z2' z3' z4' z5' z6' z7' x3' x4' x5' x6' m3 s2' st2 blk off errv2
               C2 ltac:(right; exact Hin) Hoff HA2 MR3 MI3); [rewrite unsigned_lit by lia; exact ST3| rewrite unsigned_lit by lia; lia| exact ERR3| rewrite <- HP0; symmetry; apply Z_to_bv_bv_unsigned]. }
    intros st3 s3' msf [-> FE]. cbv beta.
    destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MI4 & ST4 & ERR4 & MR4 & PE4 & SHR & BLKR & EB & BRKR).
    rewrite !unsigned_lit in ST4 by lia. rewrite !unsigned_lit in PE4 by lia.
    replace (ret_pc (Z_to_bv 64 0x1a4fc)) with (Z_to_bv 64 0x1a4fc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (INnb : In nb (lbrm (nb :: LB) blk)).
    { unfold lbrm. apply In_filter_iff. split; [left; reflexivity|]. cbn [nb blk_slot fst]. fold c0. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.aptr_eqb_neq c c0 NEQc). reflexivity. }
    assert (SUBL : forall b', In b' (lbrm LB blk) -> In b' (lbrm (nb :: LB) blk)).
    { intros b' Hb'. unfold lbrm in Hb' |- *. apply In_filter_iff in Hb'. apply In_filter_iff. split; [right; exact (proj1 Hb')| exact (proj2 Hb')]. }
    assert (CQ3 : conc st3 q = Q).
    { subst Q. destruct (BLKR nb INnb) as [r' Hr']. cbn [nb blk_slot fst] in Hr'. pose proof (SHR _ _ Hr') as Hr2.
      rewrite Eq. rewrite (conc_region' st3 _ r') by (cbn [aadd fst]; exact Hr'). rewrite (conc_region' st2 _ r') by (cbn [aadd fst]; exact Hr2). reflexivity. }
    assert (KEEP4 : forall A cs, rw_cells ssegs m3 A cs ->
              (forall a, A <= a < A + Z.of_nat (cells_size cs) -> bv_unsigned sp + -64 <= a \/ Q <= a < Q + n) -> rw_cells ssegs m4 A cs).
    { intros A cs H HR. eapply rpres_except_rw_cells; [exact PE4| exact H|]. intros a Ha. destruct (HR a Ha) as [X|X].
      - eapply (rfp_not_high st2 st3 lo (bv_unsigned sp + -64) m3 MR3 LO ltac:(lia)). exact X.
      - eapply (rfp_not_block st2 st3 (nb :: LB) blk lo (bv_unsigned sp + -64) m3 C2 MR3 LO BLKR SHR nb a INnb). cbn [nb blk_addr blk_size fst snd]. exact X. }
    pose proof (KEEP4 _ _ FR3 ltac:(intros a Ha; left; lia)) as FR4.
    assert (REPL4 : rw_cells ssegs m4 RMREPLACED [C4 (Z_to_bv 64 0)]).
    { eapply rpres_except_rw_cells; [exact PE4| exact REPL3|]. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4. intros a Ha.
      pose proof the_tb_facts. eapply (rfp_not_img st2 st3 lo (bv_unsigned sp + -64) m3 MR3 LO); unfold RMREPLACED, RCTX in *; lia. }
    assert (CH4 : rw_cells ssegs m4 Q [CB k1 (firstn k1 bs); CB (Z.to_nat n - k1) (firstn (Z.to_nat n - k1) (skipn k1 J))]).
    { apply KEEP4.
      - apply rw_cells_join2; [exact DST3|]. cbn [csize]. exact JB3.
      - cbn [cells_size csize]. intros a Ha. right. subst k1 k1z. clear -Ha N SZ. lia. }
    assert (AUX4 : rauxv_ok m4 B) by (exact (rauxv_ok_free st2 st3 lo (bv_unsigned sp + -64) m3 m4 MR3 LO ltac:(lia) PE4 B AUX3 ltac:(lia))).
    assert (HP4 : rheap_pres (lbrm LB blk) (bv_unsigned sp) m3 m4).
    { eapply rheap_pres_weaken; [eapply (rheap_pres_free st2 st3 (nb :: LB) blk lo (bv_unsigned sp + -64) m3 m4 C2 MR3 LO ltac:(lia) BLKR SHR PE4); exact SUBL| lia| intros b' Hb'; exact Hb']. }
    (* [comment removed for export] *)
    apply rimplT_ret. step. step.
    eapply evt_mono.
    { eapply (rrealloc_epilogue _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m4 lo Q ra s0 s1 s2 s3 s4 s5 s6 (fun mm => mm = m4));
        [rewrite unsigned_lit by lia; exact ST4| rewrite unsigned_lit by lia; exact FR4| rewrite unsigned_lit by lia; lia| exact MI4| reflexivity]. }
    intros msf (e0 & e1 & e2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & e3 & e4 & e5 & e6 & m4' & -> & ->).
    rewrite unsigned_lit by lia. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    unfold rrfinQ. cbn [fst snd oconc]. rewrite CQ3. exists m4, errv2. do 14 eexists.
    split; [reflexivity|]. split; [exact MI4|].
    split. { replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat (cells_size (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6))) by (cbn; lia).
             eapply stk_release; [exact ST4| exact FR4| clear -SLO; lia]. }
    split; [exact ERR4|]. split; [exact AUX4|]. split; [exact MR4|].
    split. { unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
             unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL2. }
    split. { eapply rheap_pres_trans; [exact HP2|]. eapply rheap_pres_trans; [exact HP3| exact HP4]. }
    split; [exact REPL4|]. split; [exact PSM|]. split; [exact PSF|].
    split; [exact BR|].
    exists (firstn (Z.to_nat n - k1) (skipn k1 J)). subst k1 k1z.
    replace (Z.to_nat (n - Z.min (blk_size blk) n)) with (Z.to_nat n - Z.to_nat (Z.min (blk_size blk) n))%nat by (clear -N SZ; lia). exact CH4.
  - (* [comment removed for export] *)
    rename RES into EEN. cbv beta iota. apply rimplT_ret. cbn [oconc].
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. unfold wz. rewrite ?unsigned_lit by lia. reflexivity. }
    eapply evt_mono.
    { change (wz 0) with (Z_to_bv 64 0).
      eapply (rrealloc_epilogue _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m2 lo 0 ra s0 s1 s2 s3 s4 s5 s6 (fun mm => mm = m2));
        [rewrite unsigned_lit by lia; exact ST2| rewrite unsigned_lit by lia; exact FR2| rewrite unsigned_lit by lia; lia| exact MI2| reflexivity]. }
    intros msf (e0 & e1 & e2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & e3 & e4 & e5 & e6 & m2' & -> & ->).
    rewrite unsigned_lit by lia. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    unfold rrfinQ. cbn [fst snd oconc]. exists m2, errv2. do 14 eexists.
    split; [reflexivity|]. split; [exact MI2|].
    split. { replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat (cells_size (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6))) by (cbn; lia).
             eapply stk_release; [exact ST2| exact FR2| clear -SLO; lia]. }
    split; [exact ERR2|]. split; [exact AUX2|]. split; [exact MR2|]. split; [exact BL2|].
    split; [exact HP2|]. split; [exact REPL2|]. split; [exact PSM|]. split; [exact PSF|].
    split; [exact EEN| exact CH2].
Qed.
End Sz2.
Lemma rrealloc_fallback : ltac:(let t := eval cbv delta [rrealloc_fallback__stmt] in rrealloc_fallback__stmt in exact t).
Proof using AS_PRE RAS RBIG. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB blk off bs n lo B. ltac2:(SecDiet.SzSec.closeP 'rrealloc_fallback__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rrealloc_implT__stmt : Prop := forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (blk : block) (off : Z) (bs : list byte) (n lo B : Z) (errv : word),
  let st0 := ps_m s in
  RAREACH st0 LB -> CINV st0 LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st0 (blk_slot blk) + UNIT * off ->
  rmrep st0 m -> brk_link_ps st0 s -> mem_inv ssegs m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk ssegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 RATP ->
  rw_cells ssegs m (blk_addr blk) [CB (Z.to_nat (blk_size blk)) bs] ->
  rw_cells ssegs m RMREPLACED [C4 (Z_to_bv 64 0)] ->
  a0 = Z_to_bv 64 (blk_addr blk) -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplT m (realloc st0 (Some (aadd (blk_slot blk) (UNIT * off))) n) s
         (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom ssegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB blk off bs n lo B errv : ltac2:(SecDiet.SzSec.tyM 'rrealloc_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_implT__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG RBIG63. pin_using (fun (AS_PRE RAS RBIG RBIG63 : unit) => tt). ceil_facts. msec_facts.
  intros st0 AR C Hin Hoff HA MR BL MI AUXB SB ST LO SLO ERR TP CHUNK REPL A0 A1 N.
 unfold RREALLOC_STACK in SLO.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof MR as (WF & CX & GL & AR0 & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st0 pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st0 c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st0 g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rerrno_addr tp TP) as ETP.
  pose proof LO as LOv. ceil_facts.
  assert (SIM : (get_stride (get_meta_rec st0 g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st0 g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st0 g) * (i + 1) <= get_stride (get_meta_rec st0 g) * (m_last_idx (get_meta_rec st0 g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st0 g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st0 g) * i) in *. set (stq := get_stride (get_meta_rec st0 g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (ceil_facts; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x55000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  assert (Cb : conc st0 b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st0 m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at ssegs m (r_base r + snd q) [x] /\ rdv pans_mem m st0 q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st0 !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at ssegs m (r_base r + snd q) 1).
    { destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs1 & L & B1).
    destruct bs1 as [|x [|]]; try discriminate. exists x. split; [exact B1|].
    eapply (rrdv_cur m st0 m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B1]. }
  (* [comment removed for export] *)
  unfold realloc. replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  cbv zeta. set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (MRt : rmrep st m) by (apply rmrep_set_tick; exact MR).
  unfold get_meta. apply rimplT_guard. intros _.
  apply rimplT_rd16; [peek_same MRt| peek_same MRt|]. apply rimplT_rd8; [peek_same MRt|]. cbv zeta. apply rimplT_rd8; [peek_same MRt|].
  rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
  rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
  rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
  rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
  cbn [Z.eqb negb]. rewrite EB. unfold get_group. change (s_groups st) with (s_groups st0). rewrite Hgh. cbn [g_meta].
  apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
  change (s_areas st) with (s_areas st0).
  destruct (s_areas st0 !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
  apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
  change (get_meta_rec st g) with (get_meta_rec st0 g).
  unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
  apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
  rewrite V31 in G12, G13, G14, G16.
  set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st0 g) * Z.land v3 31)) (get_stride (get_meta_rec st0 g) - IB)).
  assert (Fe : fst e = fst b) by reflexivity.
  assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st0 g) * i + get_stride (get_meta_rec st0 g) - 4).
  { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
  pose proof (go_sc _ _ _ GO) as GSC.
  assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st0 b + UNIT + get_stride (get_meta_rec st0 g) * i + get_stride (get_meta_rec st0 g) - IB - k).
  { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
  assert (EQE0 : r_base r + snd e = conc st0 b + UNIT + get_stride (get_meta_rec st0 g) * i + get_stride (get_meta_rec st0 g) - IB).
  { rewrite Se, Cb. unfold UNIT, IB. lia. }
  assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
  { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
  assert (DIFF : snd e - snd pf = conc st0 b + UNIT + get_stride (get_meta_rec st0 g) * i + get_stride (get_meta_rec st0 g) - IB - (r_base r + snd pf)).
  { rewrite Se, Cb. unfold UNIT, IB. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  set (E := r_base r + snd e). set (P := r_base r + snd pf). set (C0 := r_base r + snd c0).
  set (mr := get_meta_rec st0 g) in *. change (get_meta_rec st g) with mr in *.
  assert (DECIDE : forall r32 : Z,
    (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ssegs m (E - 4) (le4 (wz r32)) /\ bytes_at ssegs m (E - 5) [b8 0]) ->
    (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= E - P ->
    bytes_at ssegs m (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
    bytes_at ssegs m E [b8 0] ->
    evt ssegs (fun ms' => exists (t2' t3' t4' : word) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2' s0 (wz (conc st0 g))
                      a0 a1 (wz (conc st0 b)) (Z_to_bv 64 (m_sizeclass mr)) (wz (meta_word mr)) (Z_to_bv 64 RSIZE_CLASSES)
                      (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5)))
                      s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                 F (Z_to_bv 64 0x1a320) fc None m1 (seg_rom ssegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ stk ssegs m1 lo (bv_unsigned sp + -64)
        /\ rw_cells ssegs m1 (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6)
        /\ rmrep st0 m1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom ssegs))).
  { intros r32 BIG RSVLE RB0r RE0.
    assert (RSV0 : 0 <= (if 160 <=? v3 then r32 else Z.shiftr v3 5)).
    { destruct (Z.leb_spec 160 v3) as [H160|H160]; [destruct (BIG H160) as (_ & X & _); clear -X; lia| apply Z.shiftr_nonneg; clear -V3R; lia]. }
    eapply evt_cut.
    { eapply (rrealloc_pro_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P n);
        [exact MI| exact ST| exact LO| lia| rewrite A0, HAp; apply unsigned_lit; lia| subst P; lia| rewrite A1; apply unsigned_lit; lia| exact N]. }
    intros ms1 (a2v & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (MR1 : rmrep st0 m1).
    { eapply rmrep_transport_high; [exact MR | exact MU1 | exact WM1 |]. intros l h [E1|[]]; inversion E1; subst; ceil_facts; lia. }
    lazymatch type of MU1 with munch ?W _ _ => assert (DJ1 : forall A k, A + k <= lo -> disjoint_from W A k) by (intros A k HAk; cbn; lia) end.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rrealloc_hdrA_spec ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                st0 pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi);
        first [exact MR1| exact MI1| exact Kr| exact AR1| exact G15| idtac].
      - rewrite Fp. exact Hr.
      - rewrite A0, HAp. apply unsigned_lit. lia.
      - exact P16m.
      - lia.
      - unfold UNIT in OFF. unfold pf. cbn [aadd snd]. lia.
      - exact PHI.
      - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
      - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
      - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
      - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
      - rewrite EB. exact Hgh.
      - reflexivity.
      - exact (go_slot _ _ _ GO).
      - destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. clear -A00 Hk. lia.
      - rewrite EB. exact (go_mem _ _ _ GO).
      - exact (go_avail _ _ _ GO).
      - exact (go_freed _ _ _ GO).
      - exact (proj2 (proj2 (proj2 (proj2 (ci_cx _ _ C))))).
      - subst mr. clear -LI. lia.
      - subst mr. rewrite (go_freeable _ _ _ GO). clear. lia.
      - subst mr. clear -GSC. lia.
      - subst mr. pose proof (go_maplen _ _ _ GO). clear -H. lia.
      - rewrite V31. exact G12.
      - rewrite V31. exact G13.
      - rewrite V31. exact G14.
      - intros Hsc. rewrite V31. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
        apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. subst mr. clear -G16a G16b. lia.
      - intros Hsc. subst mr. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st0 g)) 48); [exfalso; clear -Hsc H; lia|]. apply Z.eqb_eq in G16. exact G16.
      - intros Hml. subst mr. destruct (Z.eqb_spec (m_maplen (get_meta_rec st0 g)) 0); [exfalso; clear -Hml e0; lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
        unfold UNIT in G17.
        replace (m_maplen (get_meta_rec st0 g) * 4096) with (m_maplen (get_meta_rec st0 g) * 256 * 16) in G17 by (clear; lia).
        rewrite Z.div_mul in G17 by (clear; lia). clear -G17. lia.
      - subst mr. clear -GSC. lia. }
    intros ms2 (t2' & t3' & t4' & ->). rewrite EB.
    (* [comment removed for export] *)
    assert (EE : E = conc st0 b + 16 + get_stride mr * Z.land v3 31 + get_stride mr - 4).
    { subst E. rewrite EQE0, V31. unfold UNIT, IB. lia. }
    assert (EC0 : C0 = conc st0 b + 16 + get_stride mr * Z.land v3 31).
    { subst C0. rewrite Cb, Sc, V31. subst mr. lia. }
    rewrite EE, EC0.
    eapply evt_mono.
    { eapply (rrealloc_hdrB_walk ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp _ t2' s0 (wz (conc st0 g)) a0 a1 _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1
                P (conc st0 b) v3 (get_stride mr) r32).
      - rewrite A0, HAp. apply unsigned_lit. lia.
      - lia.
      - unfold UNIT in S16. subst mr. lia.
      - apply Z.mul_nonneg_nonneg; [unfold UNIT in S16; subst mr; lia| lia].
      - subst P. rewrite Cb, ?V31. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. subst mr. clear -SIL Sp Sc Hoff OS SZ S16 LI I SI0. unfold UNIT, IB in *. lia.
      - rewrite Cb, ?V31. pose proof (round_up_pg_ge (r_len r)) as RU. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. subst mr. clear -SIL SPAN RBC B0 RU SI0 S16 LI I. unfold UNIT, IB in *; ceil_facts. lia.
      - lia.
      - intros Hb3. destruct (BIG Hb3) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. rewrite <- EE. split;
          (eapply bytes_at_transport; [eassumption| exact MU1| apply DJ1; cbn; try rewrite length_le4; subst E; pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia]).
      - rewrite <- EE. exact RSVLE.
      - rewrite <- EE. eapply bytes_at_transport; [exact RB0r| exact MU1| apply DJ1; cbn; subst E P; pose proof (round_up_pg_ge (r_len r)) as RU; clear - RU RSV0 RSVLE ERNG RBC LO; ceil_facts; lia].
      - rewrite <- EE. eapply bytes_at_transport; [exact RE0| exact MU1| apply DJ1; cbn; subst E; pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia]. }
    intros ms3 (t2'' & t3'' & t4'' & ->). rewrite <- EE, <- EC0.
    exists t2'', t3'', t4'', m1. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1| exact MR1]. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (RDBt : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at ssegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq. destruct (RDB q Fq Hq) as (x & B1 & R1). exists x. split; [exact B1| exact R1]. }
  unfold get_nominal_size. apply rimplT_rd8; [peek_same MRt|]. cbv zeta.
  rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
  (* [comment removed for export] *)
  assert (CONT : forall r32 : Z,
    (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at ssegs m (E - 4) (le4 (wz r32)) /\ bytes_at ssegs m (E - 5) [b8 0]) ->
    (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= E - P ->
    bytes_at ssegs m (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
    bytes_at ssegs m E [b8 0] ->
    (if 160 <=? v3 then r32 else Z.shiftr v3 5) = E - P - blk_size blk ->
    rimplT m
      (if (n <=? snd e - snd pf) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1)
       then ret (havoc pf n (set_size pf e n (Z.land v3 31) st), Some pf)
       else if (48 <=? m_sizeclass mr) && (MMAP_THRESHOLD <=? n)
       then guard 70 (m_sizeclass mr =? 63)
              (let base := snd pf - snd (aadd b (UNIT + get_stride mr * Z.land v3 31)) in
               let needed := round_up_pg (n + base + UNIT + IB) in
               let oldlen := m_maplen mr * 4096 in
               let rid := fst (aadd b (UNIT + get_stride mr * Z.land v3 31)) in
               if oldlen =? needed then ret (resize63 st rid needed pf n (Z.land v3 31), Some pf)
               else SVis (EMremap (conc st (rid, 0)) oldlen needed) (fun r0 =>
                      if negb (mremap_answer_ok st rid (conc st (rid, 0)) oldlen needed r0) then bad_answer (ret (st0, @None aptr))
                      else if is_err r0 then
                        sbind (malloc st n) (fun x => let '(st2, q) := x in
                           match q with Some q0 => sbind (free st2 (Some pf)) (fun st3 => ret (st3, Some q0)) | None => ret (st2, None) end)
                      else ret (big_resize st g rid r0 needed pf n (Z.land v3 31), Some pf)))
              (ret (st0, None))
       else sbind (malloc st n) (fun x => let '(st2, q) := x in
               match q with Some q0 => sbind (free st2 (Some pf)) (fun st3 => ret (st3, Some q0)) | None => ret (st2, None) end))
      s (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom ssegs))).
  2:{
  destruct (areach_blk_frame st0 LB blk off g i AR Hin HA SL) as [FK3 FK5]. fold c0 in FK3, FK5.
  change (MI_Inv.MR st0 g) with mr in FK3, FK5.
  set (res := snd c0 + get_stride mr - IB - (snd c0 + UNIT * off) - blk_size blk) in *.
  assert (RES0 : 0 <= res) by (subst res; clear -OS Hoff; unfold UNIT, IB in *; lia).
  assert (ERES : E - P - blk_size blk = res) by (subst res E P; rewrite Se, Sp, Sc; unfold UNIT, IB; clear; lia).
  assert (V3E : v3 = i + 32 * Z.min res 5).
  { pose proof C3 as C3'. unfold pf in C3'. cbn [aadd fst snd] in C3'.
    replace (snd c0 + UNIT * off - 3) with (snd c0 + UNIT * off - 3) in C3' by reflexivity.
    rewrite FK3 in C3'. congruence. }
  assert (SR5E : Z.shiftr v3 5 = Z.min res 5) by (rewrite V3E; apply shiftr5_res; [subst mr; clear -I LI; lia| clear -RES0; lia]).
  assert (KE : forall d v, cell_read (get_shadow st0 (fst c0)) (snd c0 + get_stride mr - IB - d) = Known v ->
                          cell_read (get_shadow st (fst (aadd e (- d)))) (snd (aadd e (- d))) = Known v).
  { intros d v Hd. rewrite <- Hd. f_equal; [cbn [aadd fst]; rewrite Fe, FB; reflexivity| cbn [aadd snd]; rewrite Se, Sc; unfold UNIT, IB; clear; lia]. }
  apply rimplT_if; intros HR5.
  - (* [comment removed for export] *)
    apply Z.leb_le in HR5.
    apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
    apply rimplT_rd32; [peek_same MRt| peek_same MRt| peek_same MRt| peek_same MRt|].
    destruct (RDBt (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0.
    destruct (RDBt (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1.
    destruct (RDBt (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
    destruct (RDBt (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
    pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
    set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
    apply rimplT_guard; intros G21. apply Z.leb_le in G21.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
    apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
    apply rimplT_guard; intros G22. apply Z.leb_le in G22.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
    apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
    apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
    specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
    assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
    apply (CONT r32).
    + intros _. split; [exact G20|]. split; [lia|]. split.
      * subst E. rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
        replace (r_base r + snd e - 4) with (r_base r + snd (aadd e (-4))) by (cbn [aadd snd]; lia).
        apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
        apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
        -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
        -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
      * subst E. replace (r_base r + snd e - 5) with (r_base r + snd (aadd e (-5))) by (cbn [aadd snd]; lia). rewrite <- (byte_zero_list x5 G25). exact BX5.
    + rewrite H160. subst E P. lia.
    + rewrite H160. subst E. replace (r_base r + snd e - r32) with (r_base r + snd (aadd e (- r32))) by (cbn [aadd snd]; lia). rewrite <- (byte_zero_list xc G23). exact BXc.
    + subst E. rewrite <- (byte_zero_list xe G24). exact BXe.
    + rewrite H160, ERES. assert (R5 : 5 <= res) by (clear -HR5 SR5E; lia).
      destruct (FK5 R5) as (KB0 & KB1 & KB2 & KB3 & R32).
      rewrite (rdv_known m st (aadd e (-4)) (byte_of res 0)) in RX0 by (apply (KE 4); exact KB0).
      rewrite (rdv_known m st (aadd (aadd e (-4)) 1) (byte_of res 1)) in RX1
        by (rewrite <- (KE 3 _ KB1); f_equal; cbn [aadd snd]; clear; lia).
      rewrite (rdv_known m st (aadd (aadd e (-4)) 2) (byte_of res 2)) in RX2
        by (rewrite <- (KE 2 _ KB2); f_equal; cbn [aadd snd]; clear; lia).
      rewrite (rdv_known m st (aadd (aadd e (-4)) 3) (byte_of res 3)) in RX3
        by (rewrite <- (KE 1 _ KB3); f_equal; cbn [aadd snd]; clear; lia).
      subst r32. rewrite <- RX0, <- RX1, <- RX2, <- RX3. apply u32_bytes. clear -RES0 R32. lia.
  - (* [comment removed for export] *)
    apply Z.leb_gt in HR5.
    apply rimplT_guard; intros G22. apply Z.leb_le in G22.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
    apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
    apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
    specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
    assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
    apply (CONT 0).
    + intros H. exfalso. clear -H V160. lia.
    + rewrite H160. subst E P. lia.
    + rewrite H160. subst E. replace (r_base r + snd e - Z.shiftr v3 5) with (r_base r + snd (aadd e (- Z.shiftr v3 5))) by (cbn [aadd snd]; lia). rewrite <- (byte_zero_list xc G23). exact BXc.
    + subst E. rewrite <- (byte_zero_list xe G24). exact BXe.
    + rewrite H160, ERES. clear -HR5 SR5E RES0. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  intros r32 BIG RSVLE RB0r RE0 RSVEQ.
  pose proof (DECIDE r32 BIG RSVLE RB0r RE0) as MACH. clear DECIDE.
  assert (RSV0 : 0 <= (if 160 <=? v3 then r32 else Z.shiftr v3 5)).
  { destruct (Z.leb_spec 160 v3) as [H160|H160]; [destruct (BIG H160) as (_ & X & _); clear -X; lia| apply Z.shiftr_nonneg; clear -V3R; lia]. }
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (TKt : ticks_ok st) by (apply ticks_ok_set_tick; [cbn; lia| exact TK]).
  (* [comment removed for export] *)
  destruct (areach_blk_slot_clear st0 LB blk AR Hin) as (gm & bm & im & rm & offm & HOm & HIm & ESL & SLm & Hrm & Krm & EAm & OFm & SZm & FITm & GCLR & BCLR).
  fold c0 in ESL, SLm. rewrite SL in SLm. assert (gm = g /\ im = i) as [-> ->] by (split; congruence). clear SLm.
  assert (Ebm : fst bm = fst b) by (rewrite FB, ESL; reflexivity).
  rewrite Ebm, Hr in Hrm. assert (rm = r) as -> by congruence.
  assert (SS0 : sstart (MI_Inv.MR st0 g) i = snd c0) by (rewrite ESL; reflexivity).
  change (MI_Inv.MR st0 g) with mr in SS0, GCLR, BCLR, FITm, EAm, HIm.
  (* [comment removed for export] *)
  pose proof (rreserved_tlsF _ _ RF) as TLSr. pose proof (rreserved_disjoint _ _ RF) as (IMr1 & IMr2 & IMr3 & IMr4).
  pose proof (round_up_pg_ge (r_len r)) as RUr.
  set (SPANC := fun a => lo <= a < bv_unsigned sp \/ C0 - IB <= a < C0 + get_stride mr - IB).
  assert (SPAN_PRES : forall mx, rpres_except SPANC m mx -> rheap_pres (lbrm LB blk) (bv_unsigned sp) m mx).
  { intros mx PEx a Ha CA. apply PEx; [exact Ha|]. subst SPANC C0. cbv beta.
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
    destruct CA as [CA|[[CA NS]|[(blk' & Hb' & Hab)|[CA NE]]]].
    - clear -CA SLO LOv RBC SPAN Sc SIL SI0 B0. unfold UNIT, IB in *; ceil_facts. lia.
    - clear -CA LOv DRr RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts. lia.
    - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' NEQ].
      assert (NE' : blk_slot blk' <> blk_slot blk).
      { intros EQ. rewrite EQ in NEQ. rewrite aptr_eqb_refl in NEQ. cbn in NEQ. exact NEQ. }
      destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hin') as [(r' & Hr' & Kr' & A16' & AEND' & _) _ _].
      destruct (N.eq_dec (fst (blk_slot blk')) (fst bm)) as [EF|NF].
      + specialize (BCLR blk' Hin' NE' EF). rewrite SS0 in BCLR.
        assert (r' = r) as -> by (rewrite EF, Ebm, Hr in Hr'; congruence).
        clear -BCLR Hab AEND' LOv RBC SPAN Sc SIL SI0 B0 RUr. unfold UNIT, IB in *; ceil_facts. lia.
      + assert (NR : fst (blk_slot blk') <> fst b) by (rewrite <- Ebm; exact NF).
        pose proof (lr_lo_group r Kr). pose proof (lr_lo_group r' Kr'). pose proof (round_up_pg_ge (r_len r')).
        destruct (WR _ _ Hr') as (_ & _ & _ & RBC' & _).
        destruct (DJ _ _ _ _ Hr' Hr NR); clear -H H0 H1 H2 Hab A16' AEND' LOv RBC RBC' SPAN Sc SIL SI0 B0 RUr; unfold UNIT, IB in *; ceil_facts; lia.
    - pose proof the_tb_facts as TF. clear -CA NE TLSr LOv TF RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts. lia. }
  assert (SPAN_AUX : forall mx, rpres_except SPANC m mx -> rauxv_ok mx B).
  { intros mx PEx. eapply rauxv_ok_pres; [exact AUXB| exact PEx| |]; subst SPANC C0; cbv beta.
    - intros a Ha. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. clear -Ha SB SLO LOv RBC SPAN Sc SIL SI0 B0. unfold UNIT, IB in *; ceil_facts. lia.
    - intros a Ha. unfold RAUXV_CELL in Ha. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. clear -Ha LOv DRr RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts. lia. }
  assert (SPAN_ERR : forall mx, rpres_except SPANC m mx -> rw_cells ssegs mx (errno_addr tp) [C4 errv]).
  { intros mx PEx. eapply rpres_except_rw_cells; [exact PEx| exact ERR|]. rewrite ETP. change (Z.of_nat (cells_size [C4 errv])) with 4.
    intros a Ha. subst SPANC C0; cbv beta. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
    pose proof the_tb_facts as TF.
    clear -Ha TLSr LOv TF RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts.
    destruct TF as (TF1 & TF2 & TF3 & TF4). intros [X|X]; lia. }
  assert (SPAN_REPL : forall mx, rpres_except SPANC m mx -> rw_cells ssegs mx RMREPLACED [C4 (Z_to_bv 64 0)]).
  { intros mx PEx. eapply rpres_except_rw_cells; [exact PEx| exact REPL|]. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4.
    intros a Ha. subst SPANC C0; cbv beta. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold RMREPLACED, RCTX in Ha.
    clear -Ha LOv DRr RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts. intros [X|X]; lia. }
  destruct (WR _ _ Hr) as (_ & RBAL & _).
  assert (P16 : P mod 16 = 0).
  { subst P. pose proof P16m as X. unfold frozen in X. clear -X RBAL. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (rw_cells_bytes_at _ _ _ _ CHUNK) as BS0. cbn [cells_bytes cbytes] in BS0. rewrite app_nil_r in BS0.
  assert (LBS : length bs = Z.to_nat (blk_size blk)).
  { destruct CHUNK as [[Hwf _] _]. cbn in Hwf. exact (proj1 Hwf). }
  (* [comment removed for export] *)
  apply rimplT_if; intros HC1.
  - (* [comment removed for export] *)
    apply andb_prop in HC1 as [HC1 HC3]. apply andb_prop in HC1 as [HC1 HC2]. apply Z.leb_le in HC1. apply Z.ltb_lt in HC2. apply Z.leb_le in HC3.
    pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD in HC2 |- *; lia)) as (STC & _ & _).
    assert (SC48 : m_sizeclass mr < 48) by (clear -STC HC3 GSC; subst mr; lia).
    assert (STR31 : get_stride mr < 2^31).
    { pose proof (mf_gmeta _ _ MF g b (go_mem _ _ _ GO)) as FG. cbv zeta in FG. subst mr.
      destruct FG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S31 & _). apply S31. exact SC48. }
    apply rimplT_ret.
    eapply evt_cut; [exact MACH|]. intros ms1 (t2' & t3' & t4' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MR1).
    eapply evt_cut.
    { eapply (rrealloc_dec_small ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2' s0 (wz (conc st0 g)) a0 a1 (wz (conc st0 b)) (wz (meta_word mr))
                (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1 n (m_sizeclass mr) (E - P));
        [rewrite A1; apply unsigned_lit; lia| exact (conj (proj1 N) HC2)| subst E P; lia| | clear -GSC; subst mr; lia| exact MI1].
      subst E P. pose proof (round_up_pg_ge (r_len r)). ceil_facts. lia. }
    intros ms2 (t1' & t2'' & a2' & a4' & a5' & a7' & t3'' & t4'' & ->).
    replace (m_sizeclass mr <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; exact HC3).
    assert (MR1t : rmrep st m1) by (apply rmrep_set_tick; exact MR1).
    eapply evt_mono.
    { eapply (rrealloc_inplace_walk ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t1' t2'' s0 (wz (conc st0 g)) a0 a1 a2' (Z_to_bv 64 (m_sizeclass mr)) a4' a5' a7'
                (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5 t6 F fc
                m1 m1 lo st pf e r v3 n ra s0 s1 s2 s3 s4 s5 s6);
        first [exact MR1t| exact MI1| exact TKt| exact Kr| idtac].
      - rewrite unsigned_lit by lia. exact ST1.
      - rewrite unsigned_lit by lia. exact FR1.
      - exact LO.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. lia.
      - apply rpres_except_refl.
      - apply wmono_refl.
      - rewrite Fp. exact Hr.
      - rewrite Fe, Fp. reflexivity.
      - rewrite A0, HAp. apply unsigned_lit. lia.
      - rewrite A1. apply unsigned_lit. lia.
      - lia.
      - clear -HC1. lia.
      - rewrite Se, Sp, Sc. fold mr. clear -STR31 Hoff SI0. subst mr. lia.
      - clear -Sp Sc B0 SI0 Hoff. subst mr. lia.
      - exact (proj1 ERNG).
      - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
      - intros b' gh Hb' Hf'. rewrite Fp, <- Ebm in Hf'. destruct (GCLR b' gh Hb' Hf') as [X|X]; rewrite SS0 in X; [left| right]; rewrite ?Se, ?Sp, ?Sc in *; subst mr; clear -X Hoff SI0 Sc S16; unfold UNIT in *; lia. }
    intros msf POST. unfold rrret_post in POST.
    destruct POST as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & -> & QQ).
    destruct QQ as (MR' & TK' & MI' & ST' & FR' & PE' & WM').
    rewrite !unsigned_lit in ST', FR' by lia. rewrite unsigned_lit by lia.
    replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in * by lia. rewrite Z_to_bv_bv_unsigned.
    rewrite set_size_land31. set (st' := set_size pf e n v3 st) in *.
    pose proof (rmrep_havoc st' m' pf n MR' TK') as [MRh TKh].
    assert (RGh : s_regions (havoc pf n st') = s_regions st0) by (subst st' st; rewrite s_regions_havoc, s_regions_set_size; reflexivity).
    assert (Hrh : s_regions (havoc pf n st') !! (fst pf) = Some r) by (rewrite RGh, Fp; exact Hr).
    assert (CPh : conc (havoc pf n st') pf = P) by (rewrite (conc_region' _ pf r Hrh); reflexivity).
    assert (PEi : rpres_except SPANC m m').
    { eapply rpres_except_trans.
      - eapply rpres_except_of_munch; [exact MU1| exact WM1|]. intros a Ha NC. subst SPANC. cbv beta in NC. cbn [outside]. split; [|exact Logic.I]. clear -NC SLO. lia.
      - eapply rpres_except_mono; [exact PE'|]. intros a Ha. subst SPANC C0 P E. cbv beta. right.
        rewrite Se, Sp in Ha. rewrite Se, Sp in HC1. rewrite Sc in Ha, HC1 |- *. clear -Ha Hoff SI0 HC1 N. unfold UNIT, IB in *. lia. }
    unfold rrfinQ. cbn [fst snd oconc]. rewrite CPh. exists m', errv. do 14 eexists.
    split; [reflexivity|]. split; [exact MI'|].
    split. { replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat (cells_size (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6))) by (cbn; lia).
             eapply stk_release; [exact ST'| exact FR'| clear -SLO; lia]. }
    split; [exact (SPAN_ERR m' PEi)|]. split; [exact (SPAN_AUX m' PEi)|].
    split; [exact MRh|].
    split. { eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_malloc_big.brk_link_ps_ext; [| | exact BL].
             - subst st' st. unfold ctx. rewrite s_ctx_havoc, s_ctx_set_size. reflexivity.
             - intros rid boff _. unfold conc, get_region. rewrite RGh. reflexivity. }
    split; [exact (SPAN_PRES m' PEi)|]. split; [exact (SPAN_REPL m' PEi)|]. split; [reflexivity|]. split; [reflexivity|].
    split. { unfold rblock_range. subst P E. rewrite Se, Sp, Sc in HC1. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
             split; [clear -RB0 Sp Sc SI0 Hoff B0; lia|]. split; [exact P16|]. split; [clear -N; lia|].
             clear -HC1 RBC DRr TLSr SPAN Sp Sc SI0 SIL Hoff B0 RB0 N RUr. unfold UNIT, IB in *; ceil_facts. lia. }
    (* [comment removed for export] *)
    destruct (ruser_chunk (havoc pf n st') m' pf r n MRh Hrh Kr ltac:(clear -Sp Sc SI0 Hoff B0; lia) ltac:(clear -HC1 ERNG; lia) ltac:(clear -N; lia)) as (J & JCH).
    rewrite CPh in JCH.
    set (k1 := Z.to_nat (Z.min (blk_size blk) n)).
    assert (K1 : (k1 <= Z.to_nat n)%nat) by (subst k1; clear -N SZ; lia).
    assert (LK1 : length (firstn k1 bs) = k1) by (rewrite length_firstn, LBS; subst k1; clear -N SZ; lia).
    assert (BS1 : bytes_at ssegs m' P (firstn k1 bs)).
    { eapply rpres_except_bytes_at; [exact PE'| |].
      - eapply bytes_at_transport; [| exact MU1|].
        + eapply bytes_at_firstn. replace P with (blk_addr blk) by (subst P; exact HAp). exact BS0.
        + rewrite LK1. cbn. subst P k1. rewrite Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
          clear -Hoff SI0 N SZ OS SLO LOv RBC SPAN SIL B0. unfold UNIT, IB in *; ceil_facts. lia.
      - rewrite LK1. intros a Ha. subst P k1. cbv beta. clear -Ha HC1 Hoff N SZ. lia. }
    exists (skipn k1 J). pose proof (rw_cells_CB_prefix_agree m' P (Z.to_nat n) J (firstn k1 bs) JCH BS1 ltac:(rewrite LK1; exact K1)) as CH'.
    rewrite LK1 in CH'. replace (Z.to_nat (n - Z.min (blk_size blk) n)) with (Z.to_nat n - k1)%nat by (subst k1; clear -N SZ; lia). exact CH'.
  - (* [comment removed for export] *)
    assert (ERSV : E - (if 160 <=? v3 then r32 else Z.shiftr v3 5) = blk_addr blk + blk_size blk) by (rewrite RSVEQ, HAp; subst P; clear; lia).
    apply rimplT_if; intros HC4.
    + (* [comment removed for export] *)
      apply andb_prop in HC4 as [HC4a HC4b]. apply Z.leb_le in HC4a. apply Z.leb_le in HC4b.
      assert (SC63 : m_sizeclass mr = 63 /\ m_last_idx mr = 0 /\ 0 < m_maplen mr) by (clear -GSC HC4a; lia). destruct SC63 as (SC63 & LI0 & ML0).
      eapply rimplT_evt; [| intros msX HX; exact HX].
      eapply evt_cut; [exact MACH|]. intros ms1 (t2' & t3' & t4' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MR1).
      assert (PE1 : rpres_except SPANC m m1).
      { eapply rpres_except_of_munch; [exact MU1| exact WM1|]. intros a Ha NC. subst SPANC. cbv beta in NC. cbn [outside]. split; [|exact Logic.I]. clear -NC SLO. lia. }
      eapply evt_cut.
      { eapply (rrealloc_dec_big ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2' s0 (wz (conc st0 g)) a0 a1 (wz (conc st0 b)) (wz (meta_word mr))
                  (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1 n (m_sizeclass mr) (E - P));
          [rewrite A1; apply unsigned_lit; lia| clear -HC4b N; lia| subst E P; pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia| exact SC63]. }
      intros ms2 (t2'' & a5' & t3'' & ->).
      rewrite ERSV, A1. apply evt_done. subst C0.
      apply (RBIG63 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s LB blk off bs n lo B g b ai r i v3 (if 160 <=? v3 then r32 else Z.shiftr v3 5)
               t2'' a0 a5' t3'' t4' t5 t6 AR Hin Hoff HA BL SL Hgh FB Hr Kr SC63 LI0 ML0 I V31 C3 V3R OS SZ (conj HC4b (proj2 N)));
        [exact RSVEQ| exact RSV0| exact SB| exact LO| unfold RREALLOC_STACK; exact SLO| exact TP| exact A0| exact MU1| exact WM1| |].
      * split; [exact MI1|]. split; [exact ST1|]. split; [exact MR1|]. split; [exact (SPAN_AUX m1 PE1)|]. split; [exact (SPAN_REPL m1 PE1)|].
        split. { eapply rw_cells_transport; [exact CHUNK| exact MU1| exact WM1|]. cbn. split; [| exact Logic.I]. left.
                 clear -AEND RBC LOv SLO SZ. ceil_facts. lia. }
        split; [exact (SPAN_PRES m1 PE1)|]. split; [exists errv; exact (SPAN_ERR m1 PE1)| exact FR1].
      * exact (rrealloc_fallback ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB blk off bs n lo B AR Hin Hoff HA BL SB LO ltac:(unfold RREALLOC_STACK; lia) TP N).
    + (* [comment removed for export] *)
      eapply rimplT_evt; [| intros msX HX; exact HX].
      eapply evt_cut; [exact MACH|]. intros ms1 (t2' & t3' & t4' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MR1).
      assert (PE1 : rpres_except SPANC m m1).
      { eapply rpres_except_of_munch; [exact MU1| exact WM1|]. intros a Ha NC. subst SPANC. cbv beta in NC. cbn [outside]. split; [|exact Logic.I]. clear -NC SLO. lia. }
      eapply evt_cut.
      { eapply (rrealloc_dec_fb ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2' s0 (wz (conc st0 g)) a0 a1 (wz (conc st0 b)) (wz (meta_word mr))
                  (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1 n (m_sizeclass mr) (E - P));
          [rewrite A1; apply unsigned_lit; lia| lia| subst E P; pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia| clear -GSC; lia| clear -GSC; lia| exact MI1| | exact HC4].
        replace (snd e - snd pf) with (E - P) in HC1 by (subst E P; clear; lia). exact HC1. }
      intros ms2 (t1'' & t2'' & a2' & a4' & a5' & a7' & t3'' & t4'' & ->).
      rewrite ERSV. rewrite A1. apply evt_done.
      apply (rrealloc_fallback ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB blk off bs n lo B AR Hin Hoff HA BL SB LO ltac:(unfold RREALLOC_STACK; lia) TP N).
      * split; [exact MI1|]. split; [exact ST1|]. split; [exact MR1|]. split; [exact (SPAN_AUX m1 PE1)|]. split; [exact (SPAN_REPL m1 PE1)|].
        split. { eapply rw_cells_transport; [exact CHUNK| exact MU1| exact WM1|]. cbn. split; [| exact Logic.I]. left.
                 clear -AEND RBC LOv SLO SZ. ceil_facts. lia. }
        split; [exact (SPAN_PRES m1 PE1)|]. split; [exists errv; exact (SPAN_ERR m1 PE1)| exact FR1].
      * rewrite A0, HAp. apply unsigned_lit. lia.
Qed.
End Sz3.
Theorem rrealloc_implT : ltac:(let t := eval cbv delta [rrealloc_implT__stmt] in rrealloc_implT__stmt in exact t).
Proof using AS_PRE RAS RBIG RBIG63. intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB blk off bs n lo B errv. ltac2:(SecDiet.SzSec.closeP 'rrealloc_implT__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rrealloc_spec_proof__stmt : Prop := rrealloc_stmt.
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A sz n lo B bs errv : ltac2:(SecDiet.SzSec.tyM 'rrealloc_spec_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_spec_proof__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_spec_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG RBIG63. pin_using (fun (AS_PRE RAS RBIG RBIG63 : unit) => tt). ceil_facts. msec_facts.
  intros HP Hin AV SB ST LO SLO ERR MI TP CH A0 A1 N.
  destruct HP as (LB0 & PERM & MR & [BLK AR] & REPL).
  set (st := ps_m s) in *.
  assert (Hin0 : In (p, A, sz) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (areach_blk_addr st LB0 (p, A, sz) AR Hin0) as HA. unfold blk_addr, blk_slot, blk_id in HA. cbn [fst snd] in HA.
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  assert (O0 : 0 <= snd p).
  { pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, sz) Hin0) as [(g & i & b & _ & _ & _ & _ & _ & (off & O0 & OA & _)) _ _].
    unfold blk_addr, blk_slot in OA. cbn [fst snd] in OA. rewrite HA in OA. unfold UNIT in OA. lia. }
  (* [comment removed for export] *)
  eapply (implM_evt ssegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom ssegs))).
  { unfold RREALLOC_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (raw_realloc_bridge ssegs s (Some (aadd (fst p) (UNIT * snd p))) n m
            (fun res s' msf => rrfinQ m st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 (p, A, sz) bs n lo B res s' msf
                               /\ leaf_of m (realloc st (Some (aadd (fst p) (UNIT * snd p))) n) res)).
  - apply rimplT_reach.
    apply (rrealloc_implT ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 (p, A, sz) (snd p) bs n lo B errv
             AR C Hin0 O0 HA MR BL MI AV SB ST LO SLO ERR TP CH REPL A0 A1 N).
  - intros st' q s' msf [FQ LEAF]. cbv beta. unfold rrfinQ in FQ. cbn [fst snd] in FQ.
    destruct FQ as (m' & errv' & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI' & ST' & ERR' & AUX' & MR' & BL' & HPR & REPL' & PSM & PSR & RES).
    pose proof (lb_remove_lbrm LB p A sz (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    destruct LEAF as (l0 & ans & l1 & FF).
    pose proof (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_realloc _ _ _ st LB0 (p, A, sz) n l0 l1 ans st' q AR Hin0 ltac:(lia)
                  ltac:(unfold size_overflows; apply Z.leb_gt; lia) ltac:(unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.LEN_MAX, PGSZ; lia)
                  ltac:(unfold blk_ptr; cbn [blk_slot blk_id fst snd]; exact FF)) as AR'.
    unfold rrealloc_post. do 15 eexists. exists m', errv'. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split. { eapply rheap_pres_weaken; [exact HPR| lia|]. intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split; [rewrite ps_rest_set_m; exact PSR|].
    assert (BLs : brk_link (ps_m (set_m st' s')) (ps_brk (set_m st' s'))).
    { rewrite ps_m_set_m, ps_brk_set_m. apply (proj1 (brk_link_ps_iff st' s')). exact BL'. }
    destruct q as [q|].
    + destruct RES as [BR [junk UCH]]. destruct AR' as (c' & off' & Eq & Hoff' & _ & AR').
      exists c', off', (conc st' q).
      split; [exact Eq|]. split; [reflexivity|]. split; [rewrite ps_m_set_m; reflexivity|]. split; [exact BR|].
      split; [| exists junk; exact UCH].
      unfold RHEAP, RHEAPm. exists (((c', off'), conc st' q, n) :: lbrm LB0 (p, A, sz)).
      split; [rewrite ELB; apply perm_skip; apply lbrm_perm; exact PERM|].
      split; [rewrite ps_m_set_m; exact MR'|]. split; [| exact REPL']. split; [exact BLs|]. rewrite ps_m_set_m. exact AR'.
    + destruct RES as [EEN CHK].
      split; [reflexivity|]. split; [exact EEN|]. split; [| exact CHK].
      unfold RHEAP, RHEAPm. exists LB0. split; [exact PERM|].
      split; [rewrite ps_m_set_m; exact MR'|]. split; [| exact REPL']. split; [exact BLs|]. rewrite ps_m_set_m. exact AR'.
Qed.
End Sz4.
Theorem rrealloc_spec_proof : ltac:(let t := eval cbv delta [rrealloc_spec_proof__stmt] in rrealloc_spec_proof__stmt in exact t).
Proof using AS_PRE RAS RBIG RBIG63. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A sz n lo B bs errv. ltac2:(SecDiet.SzSec.closeP 'rrealloc_spec_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TOPLEVEL.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_enframe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocTreeB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B_reach OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.Malloc_fp.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Geom OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_WSlot2__Spec.MI_WMalloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Read OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocModel_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocKit_B3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_ntf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_free_C OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_enf OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_join OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_small OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_entry OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.F_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.F_malloc_top.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B3.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_get_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RPeek.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_fp.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_enframe.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_enf.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_entry.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_malloc_join.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_small.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RMalloc_ifaceP.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_get_meta__S3.RF_free_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free_spec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_reallocA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_reallocB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_reallocC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mremap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free_spec.
Import Stdlib.Sorting.Permutation.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_invR.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; ceil_facts; lia.


Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Lemma areach_set_tick {resv} st LB t : AREACH_from resv st LB -> (s_tick st <= t)%N -> AREACH_from resv (set_tick t st) LB.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros (L & LS & BL & INV & LIVE & RESV & SEC & CR) Ht. exists L, LS, BL.
  split; [apply INVL_set_tick; [exact Ht| exact INV]|]. split; [exact LIVE|]. split; [exact RESV|]. split; [exact SEC| exact CR].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rrfinQ (m : mem) (st0 : mstate) (s : PState)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (blk : block) (bs : list byte) (n lo B : Z)
    (res : mstate * optr) (s' : PState) (msf : machine_state) : Prop :=
  exists (m' : mem) (errv' t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    msf = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz (oconc (fst res) (snd res))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ rauxv_ok m' B
    /\ rmrep (fst res) m' /\ brk_link_ps (fst res) s'
    /\ rheap_pres (lbrm LB blk) (bv_unsigned sp) m m'
    /\ rw_cells usegs m' RMREPLACED [C4 (Z_to_bv 64 0)]
    /\ ps_m s' = ps_m s /\ ps_rest s' = ps_rest s
    /\ match snd res with
       | None => errv' = Z_to_bv 64 ENOMEM /\ rw_cells usegs m' (blk_addr blk) [CB (Z.to_nat (blk_size blk)) bs]
       | Some q => rblock_range (conc (fst res) q) n
                   /\ exists junk, rw_cells usegs m' (conc (fst res) q)
                        [CB (Z.to_nat (Z.min (blk_size blk) n)) (firstn (Z.to_nat (Z.min (blk_size blk) n)) bs); CB (Z.to_nat (n - Z.min (blk_size blk) n)) junk]
       end.

(* [comment removed for export] *)
Lemma bytes_at_firstn m a (bs0 : list byte) k : bytes_at usegs m a bs0 -> bytes_at usegs m a (firstn k bs0).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H. rewrite <- (firstn_skipn k bs0) in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rw_cells_CB_prefix_agree m A n (J bs1 : list byte) :
  rw_cells usegs m A [CB n J] -> bytes_at usegs m A bs1 -> (length bs1 <= n)%nat ->
  rw_cells usegs m A [CB (length bs1) bs1; CB (n - length bs1) (skipn (length bs1) J)].
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros [[Hwf HB] HW] H1 Hlen. cbn in Hwf. destruct Hwf as [HJ _].
  cbn [cells_bytes cbytes] in HB. rewrite app_nil_r in HB.
  split; [split|].
  - cbn. repeat split; try reflexivity. rewrite length_skipn. lia.
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. apply bytes_at_app. split; [exact H1|].
    rewrite <- (firstn_skipn (length bs1) J) in HB. apply bytes_at_app in HB. destruct HB as [_ HB].
    rewrite length_firstn, Nat.min_l in HB by lia. exact HB.
  - cbn [cells_size csize] in HW |- *. replace (length bs1 + (n - length bs1 + 0))%nat with (n + 0)%nat by lia. exact HW.
Qed.

Lemma set_size_land31 p e n b st : set_size p e n (Z.land b 31) st = set_size p e n b st.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. unfold set_size. rewrite <- Z.land_assoc. reflexivity. Qed.

(* [comment removed for export] *)
Definition rr_fallback_tree (st : mstate) (pf : aptr) (n : Z) : Malloc.M (mstate * optr) :=
  sbind (malloc st n) (fun x => let '(st2, q) := x in
    match q with
    | Some q0 => sbind (free st2 (Some pf)) (fun st3 => ret (st3, Some q0))
    | None => ret (st2, @None aptr)
    end).

(* [comment removed for export] *)
Definition rr_fb_mem (m : mem) (st0 : mstate) (sp tp : word) (LB : list block) (blk : block) (bs : list byte) (lo B : Z)
    (ra s0 s1 s2 s3 s4 s5 s6 : word) (m1 : mem) : Prop :=
  mem_inv usegs m1 /\ stk usegs m1 lo (bv_unsigned sp + -64) /\ rmrep st0 m1 /\ rauxv_ok m1 B
  /\ rw_cells usegs m1 RMREPLACED [C4 (Z_to_bv 64 0)]
  /\ rw_cells usegs m1 (blk_addr blk) [CB (Z.to_nat (blk_size blk)) bs]
  /\ rheap_pres (lbrm LB blk) (bv_unsigned sp) m m1
  /\ (exists errv1 : word, rw_cells usegs m1 (errno_addr tp) [C4 errv1])
  /\ rw_cells usegs m1 (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6).

Definition rr_fallback_ok (m : mem) (st0 : mstate) (s : PState)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (LB : list block) (blk : block) (off : Z) (bs : list byte) (n lo B : Z) : Prop :=
  forall (rax x0 x1 x2 y0 y1 a0' z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 x3 x4 x5 x6 : word) (m1 : mem),
    rr_fb_mem m st0 sp tp LB blk bs lo B ra s0 s1 s2 s3 s4 s5 s6 m1 ->
    bv_unsigned a0' = blk_addr blk ->
    rimplT m (rr_fallback_tree (set_tick (N.succ (s_tick st0)) st0) (aadd (blk_slot blk) (UNIT * off)) n) s
      (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 x1 x2 y0 y1 a0' (Z_to_bv 64 n) z2 z3 z4 z5 z6 z7
               (Z_to_bv 64 (blk_addr blk + blk_size blk)) y3 y4 y5 y6 s7 s8 s9 s10 s11 x3 x4 x5 x6)
          F (Z_to_bv 64 0x1ac84) fc None m1 (seg_rom usegs)).

(* [comment removed for export] *)
Definition rbig63_stmt : Prop :=
  forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
         (m m1 : mem) (s : PState) (LB : list block) (blk : block) (off : Z) (bs : list byte) (n lo B : Z)
         (g b : aptr) (ai : Z) (r : region) (i v3 rsv : Z) (t2 a0 a5 t3 t4 t5 t6 : word),
  let st0 := ps_m s in
  let st := set_tick (N.succ (s_tick st0)) st0 in
  let mr := get_meta_rec st0 g in
  let c0 := blk_slot blk in
  let pf := aadd c0 (UNIT * off) in
  let e := aadd (aadd b (UNIT + get_stride mr * Z.land v3 31)) (get_stride mr - IB) in
  let P := r_base r + snd pf in
  let E := r_base r + snd e in
  (* [comment removed for export] *)
  RAREACH st0 LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st0 c0 + UNIT * off -> brk_link_ps st0 s ->
  s_slots st0 !! c0 = Some (g, i) -> s_groups st0 !! b = Some (mkGhdr (Some g) ai) -> fst b = fst c0 ->
  s_regions st0 !! (fst b) = Some r -> r_kind r = RKGroup ->
  m_sizeclass mr = 63 -> m_last_idx mr = 0 -> 0 < m_maplen mr -> 0 <= i <= m_last_idx mr -> Z.land v3 31 = i ->
  cell_read (get_shadow st0 (fst pf)) (snd pf - 3) = Known v3 -> 0 <= v3 < 256 ->
  UNIT * off + blk_size blk <= get_stride mr - IB -> 0 <= blk_size blk ->
  MMAP_THRESHOLD <= n < 2^32 -> rsv = E - P - blk_size blk -> 0 <= rsv ->
  (* [comment removed for export] *)
  bv_unsigned sp <= B -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK -> tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 (blk_addr blk) ->
  munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 -> wmono usegs m m1 ->
  rr_fb_mem m st0 sp tp LB blk bs lo B ra s0 s1 s2 s3 s4 s5 s6 m1 ->
  rr_fallback_ok m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk off bs n lo B ->
  rimplT m
    (guard 70 (m_sizeclass mr =? 63)
       (let base := snd pf - snd (aadd b (UNIT + get_stride mr * Z.land v3 31)) in
        let needed := round_up_pg (n + base + UNIT + IB) in
        let oldlen := m_maplen mr * 4096 in
        let rid := fst (aadd b (UNIT + get_stride mr * Z.land v3 31)) in
        if oldlen =? needed
        then ret (resize63 st rid needed pf n (Z.land v3 31), Some pf)
        else
         SVis (EMremap (conc st (rid, 0)) oldlen needed)
           (fun r0 : Z =>
              if negb (mremap_answer_ok st rid (conc st (rid, 0)) oldlen needed r0)
              then bad_answer (ret (st0, @None aptr))
              else if is_err r0 then rr_fallback_tree st pf n
              else ret (big_resize st g rid r0 needed pf n (Z.land v3 31), Some pf)))
       (ret (st0, @None aptr)))
    s
    (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 (r_base r + snd c0)) t2 s0 (wz (conc st0 g))
             a0 (Z_to_bv 64 n) (wz (conc st0 b)) (Z_to_bv 64 (m_sizeclass mr)) (wz (meta_word mr)) a5 (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P))
             (Z_to_bv 64 (blk_addr blk + blk_size blk)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ab9c) fc None m1 (seg_rom usegs)).

Section TOPLEVEL.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis RAS : ralloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : forall st LB t sc n, RAREACH st LB -> RMFACTS st LB -> (s_tick st < t)%N -> 0 <= sc < 48 -> 0 <= n < 2^32 ->
  n + 4 <= 16 * size_class sc -> as_pre st (set_tick t st) sc n FUEL.
Hypothesis RBIG : rbig_stmt.
Hypothesis RBIG63 : rbig63_stmt.

(* [comment removed for export] *)
Definition rmalloc_implT_gen__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (st : mstate) (LB : list block) (n lo B : Z) (errv : word),
  rmrep st m -> brk_link_ps st s -> RAREACH st LB ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 8192 ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplT m (malloc st n) s
         (fun res s' msf => rfinQ m st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo B res s' msf /\ leaf_of m (malloc st n) res)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rmalloc_entry) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s st LB n lo B errv : ltac2:(SecDiet.SzSec.tyM 'rmalloc_implT_gen__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rmalloc_implT_gen__body : ltac2:(SecDiet.SzSec.bodyP 'rmalloc_implT_gen__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
 intros MR BL AR AUXB SB ST CLO LO ERR MI TP HA N.
  pose proof (bv_unsigned_in_range 64 sp) as SPR0.
  assert (AUX : rauxv_ok m (bv_unsigned sp)) by (eapply rauxv_ok_weaken; [exact AUXB| ceil_facts; lia]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  apply (rimplT_reach m (malloc st n)). unfold malloc.
  eapply rimplT_bind.
  { exact (rmalloc_core_implT as_pre as_inv RAS AS_PRE RBIG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
             m st LB s n lo errv (N.succ (s_tick st)) AR MF MR BL AUX ST CLO ltac:(lia) ERR MI TP HA N ltac:(lia)). }
  intros [st2 r] s' ms'' CQ. cbn [rcoreQ] in CQ.
  destruct r as [[g idx]|].
  - (* [comment removed for export] *)
    destruct CQ as (b & rg & m1 & errv1 & u0 & u1 & u2 & v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & s4' & u3 & u4 & u5 & u6 & ra' & -> &
                    MR2 & TK2 & UA2 & MI2 & ST2 & FR2 & ERR2 & AUX2 & PE2 & SPANFP & CTR2 & SO & EXPO & MREL & BL2 & PSM & PSF & PSO).
    pose proof SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0' NS NOGRP HDR0 Q16 SSL MSL AVr FRr FBr MPL SCr].
    pose proof (rregion_addr_facts st2 m1 (fst b) rg MR2 Hr) as (R4 & RAL & RC & RI1).
    assert (SK : 0 <= get_stride (get_meta_rec st2 g) * idx) by (apply Z.mul_nonneg_nonneg; lia).
    assert (SKL : get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) <= get_stride (get_meta_rec st2 g) * (m_last_idx (get_meta_rec st2 g) + 1)).
    { rewrite Z.mul_add_distr_l, Z.mul_1_r. apply Z.add_le_mono_r. apply Z.mul_le_mono_nonneg_l; lia. }
    set (stride := get_stride (get_meta_rec st2 g)) in *.
    set (lo_s := r_base rg + snd b + 16 + stride * idx - 4) in *.
    set (hi_s := r_base rg + snd b + 16 + stride * idx + stride - 4) in *.
    set (Cf := fun a => lo <= a < bv_unsigned sp \/ lo_s <= a < hi_s).
    ceil_facts.
    eapply rimplT_mono.
    { exact (renf_implT sp gp tp u0 u1 u2 v0 v1 v2 v3 v4 v5 v6 v7 s4' s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra' ra s0 s1 s2 s3 s4 F fc m m1 m1 s' st2 g b rg idx n lo Cf
                MR2 TK2 UA2 MI2 ST2 ltac:(ceil_facts; lia) ltac:(lia) FR2 (rpres_except_refl _ _)
                ltac:(intros a Ha; left; exact Ha) ltac:(intros a Ha; right; subst lo_s hi_s stride; exact Ha) CTR2 SO). }
    intros [st' p'] s'' msf [-> EP]. unfold renf_post in EP.
    destruct EP as (st'_ & p & w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & ER & -> & MI' & ST' & MR' & TK' & PE' & LEAF).
    inversion ER; subst st'_ p'. clear ER.
    destruct LEAF as (off & OFF0 & FIT & Ep & Est' & Ep2 & Eoff).
    assert (SE : strip st' = strip st2) by (rewrite Est', strip_havoc, strip_enframe_at; reflexivity).
    pose proof (strip_eq_proj _ _ SE) as (Ec & Er & En & Em & _ & _ & Esl & Es).
    assert (HrS : (s_regions st') !! (fst p) = Some rg) by (rewrite Er, Ep; cbn [fst]; exact Hr).
    assert (EA : conc st' p = r_base rg + snd b + 16 + stride * idx + 16 * off).
    { rewrite (conc_region' st' p rg HrS). rewrite Ep. cbn [snd]. subst stride. lia. }
    destruct (ruser_chunk st' m' p rg n MR' HrS Hk ltac:(rewrite Ep; cbn [snd]; lia) ltac:(rewrite Ep; cbn [snd]; subst stride; lia) ltac:(lia)) as (ujunk & UCH).
    assert (MRELf : mrel st st') by (eapply mrel_trans; [exact MREL|]; apply mrel_same; assumption).
    assert (PEf : rpres_except (rmalloc_fp st st' lo (bv_unsigned sp)) m m').
    { eapply rpres_except_mono.
      + eapply rpres_except_trans; [exact PE2|].
        eapply rpres_except_mono; [exact PE'|]. intros a [X|X]; [left; left; exact X| apply SPANFP; subst lo_s hi_s stride; exact X].
      + intros a Ha. eapply rmalloc_fp_mono; [|exact Ha]. intros rid r1 H1. exists r1. rewrite Er. repeat split; auto; lia. }
    unfold rfinQ. cbn [fst snd oconc]. exists m', errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI'|]. split; [exact ST'|].
    split. { eapply rpres_except_rw_cells; [exact PE'| exact ERR2|]. rewrite (rerrno_addr tp TP). pose proof the_tb_facts.
             change (Z.of_nat (cells_size [C4 errv1])) with 4. specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)).
             intros a Ha [X|X]; subst lo_s hi_s; lia. }
    split. { eapply (rauxv_ok_malloc_fp st st' lo (bv_unsigned sp) m m' m m' B); [exact MR| exact MR'| exact AUXB| exact PEf| exact CLO| exact SB]. }
    split; [exact MR'|]. split; [exact MRELf|].
    split. { unfold brk_link_ps in *. unfold ctx in *. rewrite Ec. unfold conc, get_region. rewrite Er. exact BL2. }
    split; [exact PEf|]. split; [exact PSM|]. split; [exact PSF|].
    split. { unfold rblock_range; ceil_facts. rewrite EA. pose proof the_tb_facts.
             split; [lia|]. split; [apply mod16_slot; [exact RAL| exact B16| exact SMOD| lia]|]. subst lo_s hi_s.
             specialize (RI1 ltac:(pose proof (round_up_pg_ge (r_len rg)); lia)). lia. }
    exists ujunk. exact UCH.
  - (* [comment removed for export] *)
    destruct CQ as (m1 & errv1 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> &
                    MR2 & TK2 & MI2 & ST2 & ERR2 & EEN2 & AUX2 & PE2 & MREL & BL2 & PSM & PSF & PSO).
    cbv beta iota. apply rimplT_ret. apply evt_done.
    unfold rfinQ. cbn [fst snd oconc]. exists m1, errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact ERR2|].
    split. { eapply (rauxv_ok_malloc_fp st st2 lo (bv_unsigned sp) m m1 m m1 B); [exact MR| exact MR2| exact AUXB| exact PE2| exact CLO| exact SB]. }
    split; [exact MR2|]. split; [exact MREL|]. split; [exact BL2|]. split; [exact PE2|]. split; [exact PSM|]. split; [exact PSF| exact EEN2].
Qed.
End Sz1.
Lemma rmalloc_implT_gen : ltac:(let t := eval cbv delta [rmalloc_implT_gen__stmt] in rmalloc_implT_gen__stmt in exact t).
Proof using AS_PRE RAS RBIG. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s st LB n lo B errv. ltac2:(SecDiet.SzSec.closeP 'rmalloc_implT_gen__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rrealloc_fallback__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (s : PState) (LB : list block) (blk : block) (off : Z) (bs : list byte) (n lo B : Z),
  let st0 := ps_m s in
  RAREACH st0 LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st0 (blk_slot blk) + UNIT * off ->
  brk_link_ps st0 s -> bv_unsigned sp <= B -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  tp = Z_to_bv 64 RATP -> 0 <= n < 2^32 ->
  rr_fallback_ok m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk off bs n lo B.
Section Sz2.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB blk off bs n lo B : ltac2:(SecDiet.SzSec.tyM 'rrealloc_fallback__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_fallback__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_fallback__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG. pin_using (fun (AS_PRE RAS RBIG : unit) => tt). ceil_facts. msec_facts.
 intros st0 AR Hin Hoff HA BL SB LO SLO TP N.
  intros rax x0 x1 x2 y0 y1 a0' z2 z3 z4 z5 z6 z7 y3 y4 y5 y6 x3 x4 x5 x6 m1 (MI1 & ST1 & MR1 & AUX1 & REPL1 & CH1 & HP1 & [errv1 ERR1] & FR1) HP0.
  unfold RREALLOC_STACK in SLO.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as LOv. ceil_facts.
  set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (ARt : RAREACH st LB) by (apply areach_set_tick; [exact AR| cbn; lia]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ ARt) as MFt.
  assert (MRt : rmrep st m1) by (apply rmrep_set_tick; exact MR1).
  assert (BLt : brk_link_ps st s) by exact BL.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as -> by (rewrite HA in OA; unfold UNIT in OA; lia). clear OA.
  destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as [(r & Hr & Kr & A16 & AEND & _ & _) _ _].
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *.
  pose proof MR1 as (WF & _). pose proof WF as (Hres & WR & DJ & WA & WG). destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  pose proof (rreserved_tlsF _ _ RF) as TLSr. pose proof (rreserved_disjoint1 _ _ RF ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as DRr.
  pose proof (rw_cells_bytes_at _ _ _ _ CH1) as BS1. cbn [cells_bytes cbytes] in BS1. rewrite app_nil_r in BS1.
  assert (LBS : length bs = Z.to_nat (blk_size blk)) by (destruct CH1 as [[Hwf _] _]; cbn in Hwf; exact (proj1 Hwf)).
  unfold rr_fallback_tree.
  (* [comment removed for export] *)
  apply rimplT_from_evt. step. step. step. step. apply evt_done.
  eapply rimplT_bind.
  { eapply (rmalloc_implT_gen (Z_to_bv 64 0x1ac94) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp _ _ _ (Z_to_bv 64 n) a0' (Z_to_bv 64 n) (Z_to_bv 64 n)
              _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m1 s st LB n lo B errv1 MRt BLt ARt AUX1);
      [rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; exact ST1| exact LO| rewrite unsigned_lit by lia; lia| exact ERR1| exact MI1| exact TP| reflexivity| exact N]. }
  intros [st2 q] s2' msf [FQ LEAF]. unfold rfinQ in FQ. cbn [fst snd] in FQ.
  destruct FQ as (m2 & errv2 & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI2 & ST2 & ERR2 & AUX2 & MR2 & MREL & BL2 & PE2 & PSM & PSF & RES).
  rewrite !unsigned_lit in ST2 by lia. rewrite !unsigned_lit in PE2 by lia.
  replace (ret_pc (Z_to_bv 64 0x1ac94)) with (Z_to_bv 64 0x1ac94) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (KEEP2 : forall A cs, rw_cells usegs m1 A cs -> bv_unsigned sp - 64 <= A -> rw_cells usegs m2 A cs).
  { intros A cs H HA0. eapply rpres_except_rw_cells; [exact PE2| exact H|]. intros a Ha Hfp.
    destruct (rmalloc_fp_cases st st2 lo (bv_unsigned sp + -64) m1 m2 a MRt MR2 Hfp); ceil_facts; lia. }
  pose proof (KEEP2 _ _ FR1 ltac:(lia)) as FR2.
  assert (REPL2 : rw_cells usegs m2 RMREPLACED [C4 (Z_to_bv 64 0)]).
  { eapply rpres_except_rw_cells; [exact PE2| exact REPL1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.to_nat Pos.iter_op]. intros a Ha Hfp.
    pose proof the_tb_facts.
    destruct (rmalloc_fp_image st st2 lo (bv_unsigned sp + -64) m1 m2 a MRt MR2 Hfp LO ltac:(unfold RMREPLACED, RCTX in Ha; lia)); unfold RMREPLACED, RCTX in *; lia. }
  pose proof (rheap_pres_of_fp st st2 LB lo (bv_unsigned sp + -64) m1 m2 MFt MRt MR2 MREL PE2 LO ltac:(lia)) as HPf.
  assert (HP2 : rheap_pres (lbrm LB blk) (bv_unsigned sp) m m2).
  { eapply rheap_pres_trans; [exact HP1|]. eapply rheap_pres_weaken; [exact HPf| lia|]. intros b' Hb'. unfold lbrm in Hb'. apply In_filter_iff in Hb'. exact (proj1 Hb'). }
  assert (CH2 : rw_cells usegs m2 (blk_addr blk) [CB (Z.to_nat (blk_size blk)) bs]).
  { eapply rheap_pres_rw_cells; [exact HPf| exact CH1|]. cbn [cells_size csize Nat.add]. right. right. left. exists blk. split; [exact Hin| lia]. }
  destruct q as [q|].
  - (* [comment removed for export] *)
    destruct RES as [BR [J JCH]]. cbn [oconc].
    set (Q := conc st2 q) in *.
    pose proof BR as (BQ0 & BQ16 & _ & BQC & BQI & BQT).
    (* [comment removed for export] *)
    destruct LEAF as (l0 & ans & l1 & FF). unfold lrun in FF.
    destruct (MallocTree.strel_follow _ _ _ (malloc_control pans_l pupd_l pans_l_range st n l0) ans (l1, (st2, Some q)) FF) as ([cst c] & FC & [Hcst Hpc]).
    cbn [fst snd] in Hcst, Hpc. fold (lrun l0 (malloc st n)) in FF.
    destruct c as [c|]; [| destruct Hpc]. destruct Hpc as [Efst [offq Eoffq]].
    assert (Eq : q = aadd c (UNIT * offq)) by (destruct q, c; unfold aadd; cbn in Efst, Eoffq |- *; subst; reflexivity).
    set (nb := ((c, offq), Q, n) : block).
    pose proof (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_malloc_some _ _ _ st LB n l0 l1 ans st2 q cst c offq ARt ltac:(lia) FF FC Eq) as AR2. fold Q in AR2. fold nb in AR2.
    pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR2) as C2.
    assert (NEQc : c <> c0).
    { pose proof (ci_nodup _ _ C2) as ND. cbn [map nb blk_slot fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _].
      intros E. apply NI. rewrite E. subst c0. apply in_map. exact Hin. }
    assert (HEAP2 : RHEAP (set_m st2 s2') (nb :: LB) m2).
    { unfold RHEAP, RHEAPm. rewrite ps_m_set_m, ps_brk_set_m. exists (nb :: LB). split; [apply Permutation.Permutation_refl|].
      split; [exact MR2|]. split; [| exact REPL2]. split; [apply (proj1 (brk_link_ps_iff st2 s2')); exact BL2| exact AR2]. }
    assert (DISJ : Q + n <= blk_addr blk \/ blk_addr blk + blk_size blk <= Q).
    { pose proof (RHEAP_blocks_disjoint_proof (set_m st2 s2') (nb :: LB) m2 nb blk HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hin)) as D.
      cbn [nb blk_addr blk_size blk_id fst snd] in D. apply D. intros E. apply NEQc. subst c0. unfold blk_slot. apply (f_equal fst) in E. cbn [fst] in E. exact E. }
    set (k1z := Z.min (blk_size blk) n). set (k1 := Z.to_nat k1z).
    assert (K1R : 0 <= k1z <= n /\ k1z <= blk_size blk) by (subst k1z; clear -N SZ; lia).
    assert (LK1 : length (firstn k1 bs) = k1) by (rewrite length_firstn, LBS; subst k1 k1z; clear -N SZ; lia).
    pose proof (bytes_at_firstn m2 (blk_addr blk) bs k1 ltac:(pose proof (rw_cells_bytes_at _ _ _ _ CH2) as X; cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X)) as SRC2.
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB _ m2 Q [] (Z.to_nat n) J [] [k1; (Z.to_nat n - k1)%nat] JCH ltac:(cbn; subst k1 k1z; clear -N SZ; lia)) as JCH'.
    cbn [mk_CB_cells app] in JCH'. apply rw_cells_split2 in JCH'. destruct JCH' as [JA JB]. cbn [csize] in JB.
    (* [comment removed for export] *)
    assert (CALL : forall a1v a2v : word, bv_unsigned a2v = k1z ->
      evt usegs (fun ms' => exists (x0' x1' x2' z1' z2' z3' z4' z5' z6' z7' x3' x4' x5' x6' : word) (m3 : mem),
          ms' = MS (mkR (Z_to_bv 64 0x1acbc) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0' x1' x2' (wz Q) a0' a0' z1' z2' z3' z4' z5' z6' z7'
                        (Z_to_bv 64 (blk_addr blk + blk_size blk)) y3 y4 y5 y6 s7 s8 s9 s10 s11 x3' x4' x5' x6')
                   F (Z_to_bv 64 rfree_entry) fc None m3 (seg_rom usegs)
          /\ munch [(Q, Q + k1z)] m2 m3 /\ wmono usegs m2 m3 /\ mem_inv usegs m3
          /\ rw_cells usegs m3 Q [CB k1 (firstn k1 bs)])
        (MS (mkR (Z_to_bv 64 0x1ac94) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp u0 u1 u2 (Z_to_bv 64 n) a0' (wz Q) a1v a2v v3 v4 v5 v6 v7
                 (Z_to_bv 64 (blk_addr blk + blk_size blk)) y3 y4 y5 y6 s7 s8 s9 s10 s11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x1aca8) fc None m2 (seg_rom usegs))).
    { intros a1v a2v HA2.
      (* [comment removed for export] *)
      step. step. step.
      eapply evt_cut.
      { eapply (memcpy_spec _ _ gp tp _ _ _ (wz Q) a0' (wz Q) a0' a2v _ _ _ _ _ _ y3 y4 y5 y6 s7 s8 s9 s10 s11 _ _ _ _ F fc m2 (firstn k1 bs) (firstn k1 J)).
        - rewrite HP0. exact SRC2.
        - rewrite HA2, LK1. reflexivity.
        - unfold wz. rewrite unsigned_lit by (ceil_facts; lia). rewrite HA2. subst k1. exact JA.
        - unfold wz. rewrite unsigned_lit by (ceil_facts; lia). rewrite HA2, HP0. clear -DISJ K1R. lia.
        - exact MI2. }
      intros ms' PM. unfold memcpy_post in PM.
      destruct PM as (x0' & x1' & x2' & z1' & z2' & z3' & z4' & z5' & z6' & z7' & x3' & x4' & x5' & x6' & m3 & -> & MU3 & WM3 & MI3 & DST3 & _).
      unfold wz in MU3, DST3. rewrite !unsigned_lit in MU3 by (ceil_facts; lia). rewrite unsigned_lit in DST3 by (ceil_facts; lia).
      rewrite HA2 in MU3, DST3.
      replace (ret_pc (Z_to_bv 64 0x1acb4)) with (Z_to_bv 64 0x1acb4) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      (* [comment removed for export] *)
      step. step. apply evt_done. do 15 eexists. split; [reflexivity|].
      split; [exact MU3|]. split; [exact WM3|]. split; [exact MI3|]. subst k1. exact DST3. }
    eapply rimplT_evt.
    { (* [comment removed for export] *)
      step. if_cases K; zify_cond K. { exfalso. unfold wz in K. rewrite unsigned_lit in K by (ceil_facts; lia). clear -K BQ0. lia. }
      step. step. step. if_cases K2; zify_cond K2.
      - eapply CALL. rewrite unsigned_lit by lia. rewrite HP0 in K2. subst k1z. clear -K2 N SZ. lia.
      - step. eapply CALL. rewrite HP0 in K2 |- *. rewrite unsigned_lit by lia. subst k1z. clear -K2 N SZ. lia. }
    cbv beta. intros ms3 (x0' & x1' & x2' & z1' & z2' & z3' & z4' & z5' & z6' & z7' & x3' & x4' & x5' & x6' & m3 & -> & MU3 & WM3 & MI3 & DST3).
    (* [comment removed for export] *)
    assert (DJQ : forall A k, 0 <= k -> (A + k <= Q \/ Q + k1z <= A) -> disjoint_from [(Q, Q + k1z)] A k) by (intros A k Hk HA0; cbn; clear -HA0 Hk; lia).
    assert (HEAP3 : RHEAP (set_m st2 s2') (nb :: LB) m3).
    { eapply (RHEAP_frame_proof (set_m st2 s2') (nb :: LB) m2 m3); [exact HEAP2| exact MU3| exact WM3|].
      constructor; [| constructor]. right. right. left. exists nb. split; [left; reflexivity|]. cbn [nb blk_addr blk_size fst snd]. clear -K1R. lia. }
    assert (MR3 : rmrep st2 m3).
    { destruct HEAP3 as (LBx & _ & MRx & _). rewrite ps_m_set_m in MRx. exact MRx. }
    assert (ST3 : stk usegs m3 lo (bv_unsigned sp + -64)).
    { eapply stk_transport_disjoint; [exact ST2| exact MU3| exact WM3|]. apply DJQ; [clear -SLO LOv SPR; lia|]. right. ceil_facts. clear -BQC K1R LOv SLO. lia. }
    assert (ERR3 : rw_cells usegs m3 (errno_addr tp) [C4 errv2]).
    { eapply rw_cells_transport; [exact ERR2| exact MU3| exact WM3|]. rewrite (rerrno_addr tp TP). apply DJQ; [cbn; lia|]. cbn. pose proof the_tb_facts. clear -H BQT K1R. lia. }
    assert (FR3 : rw_cells usegs m3 (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6)).
    { eapply rw_cells_transport; [exact FR2| exact MU3| exact WM3|]. apply DJQ; [cbn; lia|]. right. ceil_facts. clear -BQC K1R LOv SLO. lia. }
    assert (REPL3 : rw_cells usegs m3 RMREPLACED [C4 (Z_to_bv 64 0)]).
    { eapply rw_cells_transport; [exact REPL2| exact MU3| exact WM3|]. apply DJQ; [cbn; lia|]. unfold RMREPLACED, RCTX. cbn. clear -BQI K1R. lia. }
    assert (AUX3 : rauxv_ok m3 B).
    { eapply rauxv_ok_frame; [exact AUX2| exact MU3| exact WM3|]. constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. ceil_facts.
      clear -BQC BQI K1R SB SLO LOv. lia. }
    assert (JB3 : rw_cells usegs m3 (Q + Z.of_nat k1) [CB (Z.to_nat n - k1) (firstn (Z.to_nat n - k1) (skipn k1 J))]).
    { eapply rw_cells_transport; [exact JB| exact MU3| exact WM3|]. apply DJQ; [cbn; lia|]. right. subst k1. clear -K1R. lia. }
    assert (HP3 : rheap_pres (lbrm LB blk) (bv_unsigned sp) m2 m3).
    { intros x Hx Hcx. split; [| apply WM3]. apply MU3. rewrite wa_unsigned by lia. cbn. split; [| exact Logic.I].
      destruct Hcx as [X|[[X _]|[(b' & Hb' & Xb)|[X _]]]].
      - ceil_facts. clear -X BQC K1R LOv SLO. lia.
      - clear -X BQI K1R. lia.
      - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hb' NEb].
        destruct (RHEAP_blocks_disjoint_proof (set_m st2 s2') (nb :: LB) m2 nb b' HEAP2 ltac:(left; reflexivity) ltac:(right; exact Hb')) as [D|D].
        + cbn [nb blk_id fst]. intros E.
          pose proof (ci_nodup _ _ C2) as ND. cbn [map nb blk_slot fst] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI _]. apply NI.
          apply (f_equal fst) in E. cbn [fst] in E. replace c with (blk_slot b') by (rewrite E; reflexivity). apply in_map. exact Hb'.
        + cbn [nb blk_addr blk_size fst snd] in D. clear -D Xb K1R. lia.
        + cbn [nb blk_addr blk_size fst snd] in D. clear -D Xb K1R. lia.
      - pose proof the_tb_facts. clear -X H BQT K1R. lia. }
    (* [comment removed for export] *)
    assert (HA2 : blk_addr blk = conc st2 c0 + UNIT * off).
    { pose proof (areach_blk_addr st0 LB blk AR Hin) as E0. pose proof (areach_blk_addr st2 (nb :: LB) blk AR2 ltac:(right; exact Hin)) as E2.
      fold c0 in E0, E2. rewrite HA in E0. replace off with (snd (blk_id blk)) by (unfold UNIT in E0; clear -E0; lia). exact E2. }
    (* [comment removed for export] *)
    eapply rimplT_bind.
    { apply (rlibc_free_implT gp tp (wz Q) a0' (Z_to_bv 64 (blk_addr blk + blk_size blk)) y3 y4 y5 y6 s7 s8 s9 s10 s11 F fc (nb :: LB) lo LO TP
               (Z_to_bv 64 0x1acbc) (Z_to_bv 64 (bv_unsigned sp + -64)) x0' x1' x2' a0' z1' z2' z3' z4' z5' z6' z7' x3' x4' x5' x6' m3 s2' st2 blk off errv2
               C2 ltac:(right; exact Hin) Hoff HA2 MR3 MI3); [rewrite unsigned_lit by lia; exact ST3| rewrite unsigned_lit by lia; lia| exact ERR3| rewrite <- HP0; symmetry; apply Z_to_bv_bv_unsigned]. }
    intros st3 s3' msf [-> FE]. cbv beta.
    destruct FE as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & w14 & m4 & -> & MI4 & ST4 & ERR4 & MR4 & PE4 & SHR & BLKR & EB & BRKR).
    rewrite !unsigned_lit in ST4 by lia. rewrite !unsigned_lit in PE4 by lia.
    replace (ret_pc (Z_to_bv 64 0x1acbc)) with (Z_to_bv 64 0x1acbc) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    assert (INnb : In nb (lbrm (nb :: LB) blk)).
    { unfold lbrm. apply In_filter_iff. split; [left; reflexivity|]. cbn [nb blk_slot fst]. fold c0. rewrite (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit.aptr_eqb_neq c c0 NEQc). reflexivity. }
    assert (SUBL : forall b', In b' (lbrm LB blk) -> In b' (lbrm (nb :: LB) blk)).
    { intros b' Hb'. unfold lbrm in Hb' |- *. apply In_filter_iff in Hb'. apply In_filter_iff. split; [right; exact (proj1 Hb')| exact (proj2 Hb')]. }
    assert (CQ3 : conc st3 q = Q).
    { subst Q. destruct (BLKR nb INnb) as [r' Hr']. cbn [nb blk_slot fst] in Hr'. pose proof (SHR _ _ Hr') as Hr2.
      rewrite Eq. rewrite (conc_region' st3 _ r') by (cbn [aadd fst]; exact Hr'). rewrite (conc_region' st2 _ r') by (cbn [aadd fst]; exact Hr2). reflexivity. }
    assert (KEEP4 : forall A cs, rw_cells usegs m3 A cs ->
              (forall a, A <= a < A + Z.of_nat (cells_size cs) -> bv_unsigned sp + -64 <= a \/ Q <= a < Q + n) -> rw_cells usegs m4 A cs).
    { intros A cs H HR. eapply rpres_except_rw_cells; [exact PE4| exact H|]. intros a Ha. destruct (HR a Ha) as [X|X].
      - eapply (rfp_not_high st2 st3 lo (bv_unsigned sp + -64) m3 MR3 LO ltac:(lia)). exact X.
      - eapply (rfp_not_block st2 st3 (nb :: LB) blk lo (bv_unsigned sp + -64) m3 C2 MR3 LO BLKR SHR nb a INnb). cbn [nb blk_addr blk_size fst snd]. exact X. }
    pose proof (KEEP4 _ _ FR3 ltac:(intros a Ha; left; lia)) as FR4.
    assert (REPL4 : rw_cells usegs m4 RMREPLACED [C4 (Z_to_bv 64 0)]).
    { eapply rpres_except_rw_cells; [exact PE4| exact REPL3|]. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4. intros a Ha.
      pose proof the_tb_facts. eapply (rfp_not_img st2 st3 lo (bv_unsigned sp + -64) m3 MR3 LO); unfold RMREPLACED, RCTX in *; lia. }
    assert (CH4 : rw_cells usegs m4 Q [CB k1 (firstn k1 bs); CB (Z.to_nat n - k1) (firstn (Z.to_nat n - k1) (skipn k1 J))]).
    { apply KEEP4.
      - apply rw_cells_join2; [exact DST3|]. cbn [csize]. exact JB3.
      - cbn [cells_size csize]. intros a Ha. right. subst k1 k1z. clear -Ha N SZ. lia. }
    assert (AUX4 : rauxv_ok m4 B) by (exact (rauxv_ok_free st2 st3 lo (bv_unsigned sp + -64) m3 m4 MR3 LO ltac:(lia) PE4 B AUX3 ltac:(lia))).
    assert (HP4 : rheap_pres (lbrm LB blk) (bv_unsigned sp) m3 m4).
    { eapply rheap_pres_weaken; [eapply (rheap_pres_free st2 st3 (nb :: LB) blk lo (bv_unsigned sp + -64) m3 m4 C2 MR3 LO ltac:(lia) BLKR SHR PE4); exact SUBL| lia| intros b' Hb'; exact Hb']. }
    (* [comment removed for export] *)
    apply rimplT_ret. step. step.
    eapply evt_mono.
    { eapply (rrealloc_epilogue _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m4 lo Q ra s0 s1 s2 s3 s4 s5 s6 (fun mm => mm = m4));
        [rewrite unsigned_lit by lia; exact ST4| rewrite unsigned_lit by lia; exact FR4| rewrite unsigned_lit by lia; lia| exact MI4| reflexivity]. }
    intros msf (e0 & e1 & e2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & e3 & e4 & e5 & e6 & m4' & -> & ->).
    rewrite unsigned_lit by lia. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    unfold rrfinQ. cbn [fst snd oconc]. rewrite CQ3. exists m4, errv2. do 14 eexists.
    split; [reflexivity|]. split; [exact MI4|].
    split. { replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat (cells_size (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6))) by (cbn; lia).
             eapply stk_release; [exact ST4| exact FR4| clear -SLO; lia]. }
    split; [exact ERR4|]. split; [exact AUX4|]. split; [exact MR4|].
    split. { unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st2)) as [| |brid boff] eqn:HB0; [exact Logic.I| exact Logic.I|].
             unfold conc, get_region. rewrite (BRKR brid boff ltac:(first [exact HB0 | reflexivity])). exact BL2. }
    split. { eapply rheap_pres_trans; [exact HP2|]. eapply rheap_pres_trans; [exact HP3| exact HP4]. }
    split; [exact REPL4|]. split; [exact PSM|]. split; [exact PSF|].
    split; [exact BR|].
    exists (firstn (Z.to_nat n - k1) (skipn k1 J)). subst k1 k1z.
    replace (Z.to_nat (n - Z.min (blk_size blk) n)) with (Z.to_nat n - Z.to_nat (Z.min (blk_size blk) n))%nat by (clear -N SZ; lia). exact CH4.
  - (* [comment removed for export] *)
    rename RES into EEN. cbv beta iota. apply rimplT_ret. cbn [oconc].
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. unfold wz. rewrite ?unsigned_lit by lia. reflexivity. }
    eapply evt_mono.
    { change (wz 0) with (Z_to_bv 64 0).
      eapply (rrealloc_epilogue _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m2 lo 0 ra s0 s1 s2 s3 s4 s5 s6 (fun mm => mm = m2));
        [rewrite unsigned_lit by lia; exact ST2| rewrite unsigned_lit by lia; exact FR2| rewrite unsigned_lit by lia; lia| exact MI2| reflexivity]. }
    intros msf (e0 & e1 & e2 & f1 & f2 & f3 & f4 & f5 & f6 & f7 & e3 & e4 & e5 & e6 & m2' & -> & ->).
    rewrite unsigned_lit by lia. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    unfold rrfinQ. cbn [fst snd oconc]. exists m2, errv2. do 14 eexists.
    split; [reflexivity|]. split; [exact MI2|].
    split. { replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat (cells_size (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6))) by (cbn; lia).
             eapply stk_release; [exact ST2| exact FR2| clear -SLO; lia]. }
    split; [exact ERR2|]. split; [exact AUX2|]. split; [exact MR2|]. split; [exact BL2|].
    split; [exact HP2|]. split; [exact REPL2|]. split; [exact PSM|]. split; [exact PSF|].
    split; [exact EEN| exact CH2].
Qed.
End Sz2.
Lemma rrealloc_fallback : ltac:(let t := eval cbv delta [rrealloc_fallback__stmt] in rrealloc_fallback__stmt in exact t).
Proof using AS_PRE RAS RBIG. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB blk off bs n lo B. ltac2:(SecDiet.SzSec.closeP 'rrealloc_fallback__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition rrealloc_implT__stmt : Prop := forall (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PState) (LB : list block) (blk : block) (off : Z) (bs : list byte) (n lo B : Z) (errv : word),
  let st0 := ps_m s in
  RAREACH st0 LB -> CINV st0 LB -> In blk LB -> 0 <= off -> blk_addr blk = conc st0 (blk_slot blk) + UNIT * off ->
  rmrep st0 m -> brk_link_ps st0 s -> mem_inv usegs m ->
  rauxv_ok m B -> bv_unsigned sp <= B ->
  stk usegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - RREALLOC_STACK ->
  rw_cells usegs m (errno_addr tp) [C4 errv] -> tp = Z_to_bv 64 RATP ->
  rw_cells usegs m (blk_addr blk) [CB (Z.to_nat (blk_size blk)) bs] ->
  rw_cells usegs m RMREPLACED [C4 (Z_to_bv 64 0)] ->
  a0 = Z_to_bv 64 (blk_addr blk) -> a1 = Z_to_bv 64 n -> 0 <= n < 2^32 ->
  rimplT m (realloc st0 (Some (aadd (blk_slot blk) (UNIT * off))) n) s
         (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB blk off bs n lo B errv : ltac2:(SecDiet.SzSec.tyM 'rrealloc_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_implT__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_implT__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG RBIG63. pin_using (fun (AS_PRE RAS RBIG RBIG63 : unit) => tt). ceil_facts. msec_facts.
 intros st0 AR C Hin Hoff HA MR BL MI AUXB SB ST LO SLO ERR TP CHUNK REPL A0 A1 N. unfold RREALLOC_STACK in SLO.
  pose proof (ci_ticks _ _ C) as TK.
  pose proof (KINV_of_CINV _ _ C) as K0.
  pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) blk Hin) as BK.
  pose proof (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk Hin) as BC.
  destruct BK as [(g & i & b & SL & HB & FB & I & NFR & (off' & O0 & OA & OS & OK & HK)) NG SZ].
  assert (off' = off) as ->.
  { rewrite HA in OA. unfold UNIT in OA. lia. }
  clear OA.
  set (c0 := blk_slot blk) in *. set (pf := aadd c0 (UNIT * off)) in *.
  pose proof (ci_gmetas _ _ C b g HB) as GO.
  destruct (go_region _ _ _ GO) as (r & Hr & Kr & B0 & B16 & SPAN & TOP).
  pose proof MR as (WF & CX & GL & AR0 & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  destruct BC as [(r0 & Hr0 & _ & A16 & AEND & AL & UNK) HD BB].
  rewrite <- FB, Hr in Hr0. assert (r0 = r) by congruence. subst r0.
  destruct (ki_slts _ _ _ K0 _ _ _ SL) as (GMg & Ec & _). fold c0 in Ec.
  destruct HK as (v3 & lo8 & hi & C3 & V31 & C2 & C1 & OFF). fold c0 in C3, C2, C1, OFF.
  cbn [aadd fst snd] in C3, C2, C1, OFF.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (unfold pf; cbn; symmetry; exact FB).
  assert (Cp : conc st0 pf = r_base r + snd pf) by (apply conc_region'; rewrite Fp; exact Hr).
  assert (Cc : conc st0 c0 = r_base r + snd c0) by (apply conc_region'; rewrite <- FB; exact Hr).
  assert (Sp : snd pf = snd c0 + 16 * off) by (unfold pf, UNIT; cbn; lia).
  assert (HAp : blk_addr blk = r_base r + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Sc : snd c0 = snd b + 16 + get_stride (get_meta_rec st0 g) * i).
  { rewrite Ec. rewrite (slot_start'_mem _ b i (go_mem _ _ _ GO)). cbn. unfold UNIT. lia. }
  pose proof (go_stride _ _ _ GO) as [S16 SM]. pose proof (go_li _ _ _ GO) as LI.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (rerrno_addr tp TP) as ETP.
  pose proof LO as LOv. ceil_facts.
  assert (SIM : (get_stride (get_meta_rec st0 g) * i) mod 16 = 0).
  { unfold UNIT in SM. rewrite Z.mul_mod, SM, Z.mul_0_l by lia. reflexivity. }
  assert (SI0 : 0 <= get_stride (get_meta_rec st0 g) * i) by (apply Z.mul_nonneg_nonneg; unfold UNIT in S16; lia).
  assert (SIL : get_stride (get_meta_rec st0 g) * (i + 1) <= get_stride (get_meta_rec st0 g) * (m_last_idx (get_meta_rec st0 g) + 1)).
  { apply Z.mul_le_mono_nonneg_l; unfold UNIT in S16; lia. }
  unfold sstart_of in SPAN. rewrite (go_mem _ _ _ GO) in SPAN. cbn [default id snd] in SPAN.
  assert (P16m : snd pf mod 16 = 0).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st0 g) * i) in *. unfold UNIT, IB in *. clear - SIM B16 Hoff. Z.div_mod_to_equations. lia. }
  assert (PHI : snd pf + 16 <= round_up_pg (r_len r)).
  { rewrite Sp, Sc. set (si := get_stride (get_meta_rec st0 g) * i) in *. set (stq := get_stride (get_meta_rec st0 g)) in *.
    unfold UNIT, IB in *.
    assert (16 * off + 16 <= stq) by (clear - OS SZ SM Hoff S16; Z.div_mod_to_equations; lia).
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. fold si in SIL. lia. }
  assert (HAR : 0 <= r_base r + snd pf /\ r_base r + snd pf + 16 <= 2^64) by (ceil_facts; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (DRr : r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x56000 <= r_base r) by (apply (rreserved_disjoint1 _ _ RF); lia).
  clear SIM SM B16 RBAL AL. change (frozen (snd pf mod 16 = 0)) in P16m.
  assert (EB : aadd pf (- (UNIT * (lo8 + 256 * hi)) - UNIT) = b).
  { unfold aadd. apply injective_projections; cbn; [exact Fp| unfold UNIT in *; lia]. }
  destruct HB as [ai Hgh].
  assert (Cb : conc st0 b = r_base r + snd b) by (apply conc_region'; exact Hr).
  pose proof (shiftr5_range v3) as SR5.
  destruct (rmrep_shadow_read st0 m (fst c0) r (snd c0 + UNIT * off - 3) v3 MR ltac:(rewrite <- FB; exact Hr) Kr ltac:(unfold UNIT, IB in *; lia) C3) as [_ V3R].
  assert (RDB : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at usegs m (r_base r + snd q) [x] /\ rdv pans_mem m st0 q = bv_unsigned x).
  { intros q Fq Hq.
    assert (Hrq : s_regions st0 !! fst q = Some r) by (rewrite Fq; exact Hr).
    destruct (SH _ r Hr Kr) as [WRr _].
    assert (W1 : wr_at usegs m (r_base r + snd q) 1).
    { destruct WRr as (W0 & Wn & W). split; [lia|]. split; [pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia|].
      intros j Hj. replace (r_base r + snd q + j) with (r_base r + (snd q + j)) by lia. apply W. lia. }
    destruct (rwr_at_bytes_exist m _ 1 W1 ltac:(lia) ltac:(pose proof (round_up_pg_ge (r_len r)); lia)) as (bs1 & L & B1).
    destruct bs1 as [|x [|]]; try discriminate. exists x. split; [exact B1|].
    eapply (rrdv_cur m st0 m q r x MR Hrq Kr Hq); [intros; reflexivity| exact B1]. }
  (* [comment removed for export] *)
  unfold realloc. replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  cbv zeta. set (st := set_tick (N.succ (s_tick st0)) st0).
  assert (MRt : rmrep st m) by (apply rmrep_set_tick; exact MR).
  unfold get_meta. apply rimplT_guard. intros _.
  apply rimplT_rd16; [peek_same MRt| peek_same MRt|]. apply rimplT_rd8; [peek_same MRt|]. cbv zeta. apply rimplT_rd8; [peek_same MRt|].
  rewrite (rdv_known m st (aadd pf (-4)) 0) by (cbn [aadd fst snd]; replace (snd pf + -4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia); exact OK).
  rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
  rewrite (rdv_known m st (aadd pf (-2)) lo8) by (cbn [aadd fst snd]; replace (snd pf + -2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia); exact C2).
  rewrite (rdv_known m st (aadd (aadd pf (-2)) 1) hi) by (cbn [aadd fst snd]; replace (snd pf + -2 + 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia); exact C1).
  cbn [Z.eqb negb]. rewrite EB. unfold get_group. change (s_groups st) with (s_groups st0). rewrite Hgh. cbn [g_meta].
  apply rimplT_guard; intros G11. apply rimplT_guard; intros G12. apply rimplT_guard; intros G13. apply rimplT_guard; intros G14.
  change (s_areas st) with (s_areas st0).
  destruct (s_areas st0 !! area_of g) as [ar|] eqn:AR1; [| apply rimplT_guard; intros; discriminate].
  apply rimplT_guard; intros G15. apply rimplT_guard; intros G16. apply rimplT_guard; intros G17. cbv beta.
  change (get_meta_rec st g) with (get_meta_rec st0 g).
  unfold slot_start. rewrite (go_mem _ _ _ GO). cbv beta zeta.
  apply Z.eqb_eq in G15. apply Z.leb_le in G12. apply negb_true_iff in G13. apply negb_true_iff in G14.
  rewrite V31 in G12, G13, G14, G16.
  set (e := aadd (aadd b (UNIT + get_stride (get_meta_rec st0 g) * Z.land v3 31)) (get_stride (get_meta_rec st0 g) - IB)).
  assert (Fe : fst e = fst b) by reflexivity.
  assert (Se : snd e = snd b + 16 + get_stride (get_meta_rec st0 g) * i + get_stride (get_meta_rec st0 g) - 4).
  { unfold e. cbn [aadd snd]. rewrite V31. unfold UNIT, IB. lia. }
  pose proof (go_sc _ _ _ GO) as GSC.
  assert (EQE : forall k, r_base r + snd (aadd e (- k)) = conc st0 b + UNIT + get_stride (get_meta_rec st0 g) * i + get_stride (get_meta_rec st0 g) - IB - k).
  { intros k. cbn [aadd snd]. rewrite Se, Cb. unfold UNIT, IB. lia. }
  assert (EQE0 : r_base r + snd e = conc st0 b + UNIT + get_stride (get_meta_rec st0 g) * i + get_stride (get_meta_rec st0 g) - IB).
  { rewrite Se, Cb. unfold UNIT, IB. lia. }
  assert (ERNG : snd e + 1 <= round_up_pg (r_len r) /\ snd pf <= snd e /\ 16 <= snd e).
  { rewrite Se, Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold UNIT, IB in *. lia. }
  assert (DIFF : snd e - snd pf = conc st0 b + UNIT + get_stride (get_meta_rec st0 g) * i + get_stride (get_meta_rec st0 g) - IB - (r_base r + snd pf)).
  { rewrite Se, Cb. unfold UNIT, IB. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  set (E := r_base r + snd e). set (P := r_base r + snd pf). set (C0 := r_base r + snd c0).
  set (mr := get_meta_rec st0 g) in *. change (get_meta_rec st g) with mr in *.
  assert (DECIDE : forall r32 : Z,
    (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m (E - 4) (le4 (wz r32)) /\ bytes_at usegs m (E - 5) [b8 0]) ->
    (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= E - P ->
    bytes_at usegs m (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
    bytes_at usegs m E [b8 0] ->
    evt usegs (fun ms' => exists (t2' t3' t4' : word) (m1 : mem),
        ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2' s0 (wz (conc st0 g))
                      a0 a1 (wz (conc st0 b)) (Z_to_bv 64 (m_sizeclass mr)) (wz (meta_word mr)) (Z_to_bv 64 RSIZE_CLASSES)
                      (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5)))
                      s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6)
                 F (Z_to_bv 64 0x1aae0) fc None m1 (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ stk usegs m1 lo (bv_unsigned sp + -64)
        /\ rw_cells usegs m1 (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6)
        /\ rmrep st0 m1)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom usegs))).
  { intros r32 BIG RSVLE RB0r RE0.
    assert (RSV0 : 0 <= (if 160 <=? v3 then r32 else Z.shiftr v3 5)).
    { destruct (Z.leb_spec 160 v3) as [H160|H160]; [destruct (BIG H160) as (_ & X & _); clear -X; lia| apply Z.shiftr_nonneg; clear -V3R; lia]. }
    eapply evt_cut.
    { eapply (rrealloc_pro_walk ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo P n);
        [exact MI| exact ST| exact LO| lia| rewrite A0, HAp; apply unsigned_lit; lia| subst P; lia| rewrite A1; apply unsigned_lit; lia| exact N]. }
    intros ms1 (a2v & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1).
    assert (MR1 : rmrep st0 m1).
    { eapply rmrep_transport_high; [exact MR | exact MU1 | exact WM1 |]. intros l h [E1|[]]; inversion E1; subst; ceil_facts; lia. }
    lazymatch type of MU1 with munch ?W _ _ => assert (DJ1 : forall A k, A + k <= lo -> disjoint_from W A k) by (intros A k HAk; cbn; lia) end.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rrealloc_hdrA_spec ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 a0 a1 a2v a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
                st0 pf r g (mkGhdr (Some g) ai) ar v3 lo8 hi);
        first [exact MR1| exact MI1| exact Kr| exact AR1| exact G15| idtac].
      - rewrite Fp. exact Hr.
      - rewrite A0, HAp. apply unsigned_lit. lia.
      - exact P16m.
      - lia.
      - unfold UNIT in OFF. unfold pf. cbn [aadd snd]. lia.
      - exact PHI.
      - replace (snd pf - 4) with (snd c0 + UNIT * off - IB) by (unfold UNIT, IB in *; lia). unfold pf; cbn [aadd fst]. exact OK.
      - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
      - replace (snd pf - 2) with (snd c0 + UNIT * off - 2) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C2.
      - replace (snd pf - 1) with (snd c0 + UNIT * off - 1) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C1.
      - rewrite EB. exact Hgh.
      - reflexivity.
      - exact (go_slot _ _ _ GO).
      - destruct (go_slot _ _ _ GO) as (a & ara & k & Ha & Hk & ->). destruct (WA a ara Ha) as (rg0 & _ & A00 & _). cbn. unfold AREA_HDR, META_SIZE. clear -A00 Hk. lia.
      - rewrite EB. exact (go_mem _ _ _ GO).
      - exact (go_avail _ _ _ GO).
      - exact (go_freed _ _ _ GO).
      - exact (proj2 (proj2 (proj2 (proj2 (ci_cx _ _ C))))).
      - subst mr. clear -LI. lia.
      - subst mr. rewrite (go_freeable _ _ _ GO). clear. lia.
      - subst mr. clear -GSC. lia.
      - subst mr. pose proof (go_maplen _ _ _ GO). clear -H. lia.
      - rewrite V31. exact G12.
      - rewrite V31. exact G13.
      - rewrite V31. exact G14.
      - intros Hsc. rewrite V31. apply Z.ltb_lt in Hsc. rewrite Hsc in G16. apply andb_true_iff in G16. destruct G16 as [G16a G16b].
        apply Z.leb_le in G16a. apply Z.ltb_lt in G16b. subst mr. clear -G16a G16b. lia.
      - intros Hsc. subst mr. destruct (Z.ltb_spec (m_sizeclass (get_meta_rec st0 g)) 48); [exfalso; clear -Hsc H; lia|]. apply Z.eqb_eq in G16. exact G16.
      - intros Hml. subst mr. destruct (Z.eqb_spec (m_maplen (get_meta_rec st0 g)) 0); [exfalso; clear -Hml e0; lia|]. cbn [negb] in G17. apply Z.leb_le in G17.
        unfold UNIT in G17.
        replace (m_maplen (get_meta_rec st0 g) * 4096) with (m_maplen (get_meta_rec st0 g) * 256 * 16) in G17 by (clear; lia).
        rewrite Z.div_mul in G17 by (clear; lia). clear -G17. lia.
      - subst mr. clear -GSC. lia. }
    intros ms2 (t2' & t3' & t4' & ->). rewrite EB.
    (* [comment removed for export] *)
    assert (EE : E = conc st0 b + 16 + get_stride mr * Z.land v3 31 + get_stride mr - 4).
    { subst E. rewrite EQE0, V31. unfold UNIT, IB. lia. }
    assert (EC0 : C0 = conc st0 b + 16 + get_stride mr * Z.land v3 31).
    { subst C0. rewrite Cb, Sc, V31. subst mr. lia. }
    rewrite EE, EC0.
    eapply evt_mono.
    { eapply (rrealloc_hdrB_walk ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp _ t2' s0 (wz (conc st0 g)) a0 a1 _ _ _ s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1
                P (conc st0 b) v3 (get_stride mr) r32).
      - rewrite A0, HAp. apply unsigned_lit. lia.
      - lia.
      - unfold UNIT in S16. subst mr. lia.
      - apply Z.mul_nonneg_nonneg; [unfold UNIT in S16; subst mr; lia| lia].
      - subst P. rewrite Cb, ?V31. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. subst mr. clear -SIL Sp Sc Hoff OS SZ S16 LI I SI0. unfold UNIT, IB in *. lia.
      - rewrite Cb, ?V31. pose proof (round_up_pg_ge (r_len r)) as RU. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. subst mr. clear -SIL SPAN RBC B0 RU SI0 S16 LI I. unfold UNIT, IB in *; ceil_facts. lia.
      - lia.
      - intros Hb3. destruct (BIG Hb3) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. rewrite <- EE. split;
          (eapply bytes_at_transport; [eassumption| exact MU1| apply DJ1; cbn; try rewrite length_le4; subst E; pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia]).
      - rewrite <- EE. exact RSVLE.
      - rewrite <- EE. eapply bytes_at_transport; [exact RB0r| exact MU1| apply DJ1; cbn; subst E P; pose proof (round_up_pg_ge (r_len r)) as RU; clear - RU RSV0 RSVLE ERNG RBC LO; ceil_facts; lia].
      - rewrite <- EE. eapply bytes_at_transport; [exact RE0| exact MU1| apply DJ1; cbn; subst E; pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia]. }
    intros ms3 (t2'' & t3'' & t4'' & ->). rewrite <- EE, <- EC0.
    exists t2'', t3'', t4'', m1. split; [reflexivity|].
    split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|]. split; [exact FR1| exact MR1]. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (RDBt : forall q : aptr, fst q = fst b -> 0 <= snd q < round_up_pg (r_len r) ->
            exists x : byte, bytes_at usegs m (r_base r + snd q) [x] /\ rdv pans_mem m st q = bv_unsigned x).
  { intros q Fq Hq. destruct (RDB q Fq Hq) as (x & B1 & R1). exists x. split; [exact B1| exact R1]. }
  unfold get_nominal_size. apply rimplT_rd8; [peek_same MRt|]. cbv zeta.
  rewrite (rdv_known m st (aadd pf (-3)) v3) by (cbn [aadd fst snd]; replace (snd pf + -3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia); exact C3).
  (* [comment removed for export] *)
  assert (CONT : forall r32 : Z,
    (160 <= v3 -> Z.shiftr v3 5 = 5 /\ 5 <= r32 < 2^32 /\ bytes_at usegs m (E - 4) (le4 (wz r32)) /\ bytes_at usegs m (E - 5) [b8 0]) ->
    (if 160 <=? v3 then r32 else Z.shiftr v3 5) <= E - P ->
    bytes_at usegs m (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5)) [b8 0] ->
    bytes_at usegs m E [b8 0] ->
    (if 160 <=? v3 then r32 else Z.shiftr v3 5) = E - P - blk_size blk ->
    rimplT m
      (if (n <=? snd e - snd pf) && (n <? MMAP_THRESHOLD) && (m_sizeclass mr <=? size_to_class n + 1)
       then ret (havoc pf n (set_size pf e n (Z.land v3 31) st), Some pf)
       else if (48 <=? m_sizeclass mr) && (MMAP_THRESHOLD <=? n)
       then guard 70 (m_sizeclass mr =? 63)
              (let base := snd pf - snd (aadd b (UNIT + get_stride mr * Z.land v3 31)) in
               let needed := round_up_pg (n + base + UNIT + IB) in
               let oldlen := m_maplen mr * 4096 in
               let rid := fst (aadd b (UNIT + get_stride mr * Z.land v3 31)) in
               if oldlen =? needed then ret (resize63 st rid needed pf n (Z.land v3 31), Some pf)
               else SVis (EMremap (conc st (rid, 0)) oldlen needed) (fun r0 =>
                      if negb (mremap_answer_ok st rid (conc st (rid, 0)) oldlen needed r0) then bad_answer (ret (st0, @None aptr))
                      else if is_err r0 then
                        sbind (malloc st n) (fun x => let '(st2, q) := x in
                           match q with Some q0 => sbind (free st2 (Some pf)) (fun st3 => ret (st3, Some q0)) | None => ret (st2, None) end)
                      else ret (big_resize st g rid r0 needed pf n (Z.land v3 31), Some pf)))
              (ret (st0, None))
       else sbind (malloc st n) (fun x => let '(st2, q) := x in
               match q with Some q0 => sbind (free st2 (Some pf)) (fun st3 => ret (st3, Some q0)) | None => ret (st2, None) end))
      s (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom usegs))).
  2:{
  destruct (areach_blk_frame st0 LB blk off g i AR Hin HA SL) as [FK3 FK5]. fold c0 in FK3, FK5.
  change (MI_Inv.MR st0 g) with mr in FK3, FK5.
  set (res := snd c0 + get_stride mr - IB - (snd c0 + UNIT * off) - blk_size blk) in *.
  assert (RES0 : 0 <= res) by (subst res; clear -OS Hoff; unfold UNIT, IB in *; lia).
  assert (ERES : E - P - blk_size blk = res) by (subst res E P; rewrite Se, Sp, Sc; unfold UNIT, IB; clear; lia).
  assert (V3E : v3 = i + 32 * Z.min res 5).
  { pose proof C3 as C3'. unfold pf in C3'. cbn [aadd fst snd] in C3'.
    replace (snd c0 + UNIT * off - 3) with (snd c0 + UNIT * off - 3) in C3' by reflexivity.
    rewrite FK3 in C3'. congruence. }
  assert (SR5E : Z.shiftr v3 5 = Z.min res 5) by (rewrite V3E; apply shiftr5_res; [subst mr; clear -I LI; lia| clear -RES0; lia]).
  assert (KE : forall d v, cell_read (get_shadow st0 (fst c0)) (snd c0 + get_stride mr - IB - d) = Known v ->
                          cell_read (get_shadow st (fst (aadd e (- d)))) (snd (aadd e (- d))) = Known v).
  { intros d v Hd. rewrite <- Hd. f_equal; [cbn [aadd fst]; rewrite Fe, FB; reflexivity| cbn [aadd snd]; rewrite Se, Sc; unfold UNIT, IB; clear; lia]. }
  apply rimplT_if; intros HR5.
  - (* [comment removed for export] *)
    apply Z.leb_le in HR5.
    apply rimplT_guard; intros G20. apply Z.eqb_eq in G20.
    apply rimplT_rd32; [peek_same MRt| peek_same MRt| peek_same MRt| peek_same MRt|].
    destruct (RDBt (aadd e (-4)) Fe ltac:(cbn [aadd snd]; lia)) as (x0 & BX0 & RX0). rewrite RX0.
    destruct (RDBt (aadd (aadd e (-4)) 1) Fe ltac:(cbn [aadd snd]; lia)) as (x1 & BX1 & RX1). rewrite RX1.
    destruct (RDBt (aadd (aadd e (-4)) 2) Fe ltac:(cbn [aadd snd]; lia)) as (x2 & BX2 & RX2). rewrite RX2.
    destruct (RDBt (aadd (aadd e (-4)) 3) Fe ltac:(cbn [aadd snd]; lia)) as (x3 & BX3 & RX3). rewrite RX3.
    pose proof (bytes4_range x0 x1 x2 x3) as U32. pose proof (le4_of_bytes x0 x1 x2 x3) as LE4.
    set (r32 := bv_unsigned x0 + 256 * bv_unsigned x1 + 65536 * bv_unsigned x2 + 16777216 * bv_unsigned x3) in *.
    apply rimplT_guard; intros G21. apply Z.leb_le in G21.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt (aadd e (-5)) Fe ltac:(cbn [aadd snd]; lia)) as (x5 & BX5 & RX5). rewrite RX5.
    apply rimplT_guard; intros G25. apply Z.eqb_eq in G25.
    apply rimplT_guard; intros G22. apply Z.leb_le in G22.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt (aadd e (- r32)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
    apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
    apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
    specialize (SR5 V3R). pose proof (shiftr5_ge v3 V3R HR5) as V160.
    assert (H160 : (160 <=? v3) = true) by (apply Z.leb_le; exact V160).
    apply (CONT r32).
    + intros _. split; [exact G20|]. split; [lia|]. split.
      * subst E. rewrite LE4. change [x0; x1; x2; x3] with ([x0] ++ ([x1] ++ ([x2] ++ [x3]))).
        replace (r_base r + snd e - 4) with (r_base r + snd (aadd e (-4))) by (cbn [aadd snd]; lia).
        apply bytes_at_app. split; [exact BX0|]. apply bytes_at_app. split; [cbn [length Z.of_nat Pos.of_succ_nat]; cbn [aadd snd] in BX1 |- *; replace (r_base r + (snd e + -4) + 1) with (r_base r + (snd e + -4 + 1)) by lia; exact BX1|].
        apply bytes_at_app. split; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; cbn [aadd snd] in BX2, BX3 |- *.
        -- replace (r_base r + (snd e + -4) + 1 + 1) with (r_base r + (snd e + -4 + 2)) by lia. exact BX2.
        -- replace (r_base r + (snd e + -4) + 1 + 1 + 1) with (r_base r + (snd e + -4 + 3)) by lia. exact BX3.
      * subst E. replace (r_base r + snd e - 5) with (r_base r + snd (aadd e (-5))) by (cbn [aadd snd]; lia). rewrite <- (byte_zero_list x5 G25). exact BX5.
    + rewrite H160. subst E P. lia.
    + rewrite H160. subst E. replace (r_base r + snd e - r32) with (r_base r + snd (aadd e (- r32))) by (cbn [aadd snd]; lia). rewrite <- (byte_zero_list xc G23). exact BXc.
    + subst E. rewrite <- (byte_zero_list xe G24). exact BXe.
    + rewrite H160, ERES. assert (R5 : 5 <= res) by (clear -HR5 SR5E; lia).
      destruct (FK5 R5) as (KB0 & KB1 & KB2 & KB3 & R32).
      rewrite (rdv_known m st (aadd e (-4)) (byte_of res 0)) in RX0 by (apply (KE 4); exact KB0).
      rewrite (rdv_known m st (aadd (aadd e (-4)) 1) (byte_of res 1)) in RX1
        by (rewrite <- (KE 3 _ KB1); f_equal; cbn [aadd snd]; clear; lia).
      rewrite (rdv_known m st (aadd (aadd e (-4)) 2) (byte_of res 2)) in RX2
        by (rewrite <- (KE 2 _ KB2); f_equal; cbn [aadd snd]; clear; lia).
      rewrite (rdv_known m st (aadd (aadd e (-4)) 3) (byte_of res 3)) in RX3
        by (rewrite <- (KE 1 _ KB3); f_equal; cbn [aadd snd]; clear; lia).
      subst r32. rewrite <- RX0, <- RX1, <- RX2, <- RX3. apply u32_bytes. clear -RES0 R32. lia.
  - (* [comment removed for export] *)
    apply Z.leb_gt in HR5.
    apply rimplT_guard; intros G22. apply Z.leb_le in G22.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt (aadd e (- Z.shiftr v3 5)) Fe ltac:(cbn [aadd snd]; lia)) as (xc & BXc & RXc). rewrite RXc.
    apply rimplT_guard; intros G23. apply Z.eqb_eq in G23.
    apply rimplT_rd8; [peek_same MRt|]. destruct (RDBt e Fe ltac:(lia)) as (xe & BXe & RXe). rewrite RXe.
    apply rimplT_guard; intros G24. apply Z.eqb_eq in G24.
    specialize (SR5 V3R). pose proof (shiftr5_lt v3 V3R HR5) as V160.
    assert (H160 : (160 <=? v3) = false) by (apply Z.leb_gt; exact V160).
    apply (CONT 0).
    + intros H. exfalso. clear -H V160. lia.
    + rewrite H160. subst E P. lia.
    + rewrite H160. subst E. replace (r_base r + snd e - Z.shiftr v3 5) with (r_base r + snd (aadd e (- Z.shiftr v3 5))) by (cbn [aadd snd]; lia). rewrite <- (byte_zero_list xc G23). exact BXc.
    + subst E. rewrite <- (byte_zero_list xe G24). exact BXe.
    + rewrite H160, ERES. clear -HR5 SR5E RES0. lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  intros r32 BIG RSVLE RB0r RE0 RSVEQ.
  pose proof (DECIDE r32 BIG RSVLE RB0r RE0) as MACH. clear DECIDE.
  assert (RSV0 : 0 <= (if 160 <=? v3 then r32 else Z.shiftr v3 5)).
  { destruct (Z.leb_spec 160 v3) as [H160|H160]; [destruct (BIG H160) as (_ & X & _); clear -X; lia| apply Z.shiftr_nonneg; clear -V3R; lia]. }
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv2.areach_facts_proof _ _ AR) as MF.
  assert (TKt : ticks_ok st) by (apply ticks_ok_set_tick; [cbn; lia| exact TK]).
  (* [comment removed for export] *)
  destruct (areach_blk_slot_clear st0 LB blk AR Hin) as (gm & bm & im & rm & offm & HOm & HIm & ESL & SLm & Hrm & Krm & EAm & OFm & SZm & FITm & GCLR & BCLR).
  fold c0 in ESL, SLm. rewrite SL in SLm. assert (gm = g /\ im = i) as [-> ->] by (split; congruence). clear SLm.
  assert (Ebm : fst bm = fst b) by (rewrite FB, ESL; reflexivity).
  rewrite Ebm, Hr in Hrm. assert (rm = r) as -> by congruence.
  assert (SS0 : sstart (MI_Inv.MR st0 g) i = snd c0) by (rewrite ESL; reflexivity).
  change (MI_Inv.MR st0 g) with mr in SS0, GCLR, BCLR, FITm, EAm, HIm.
  (* [comment removed for export] *)
  pose proof (rreserved_tlsF _ _ RF) as TLSr. pose proof (rreserved_disjoint _ _ RF) as (IMr1 & IMr2 & IMr3 & IMr4).
  pose proof (round_up_pg_ge (r_len r)) as RUr.
  set (SPANC := fun a => lo <= a < bv_unsigned sp \/ C0 - IB <= a < C0 + get_stride mr - IB).
  assert (SPAN_PRES : forall mx, rpres_except SPANC m mx -> rheap_pres (lbrm LB blk) (bv_unsigned sp) m mx).
  { intros mx PEx a Ha CA. apply PEx; [exact Ha|]. subst SPANC C0. cbv beta.
    rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
    destruct CA as [CA|[[CA NS]|[(blk' & Hb' & Hab)|[CA NE]]]].
    - clear -CA SLO LOv RBC SPAN Sc SIL SI0 B0. unfold UNIT, IB in *; ceil_facts. lia.
    - clear -CA LOv DRr RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts. lia.
    - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' NEQ].
      assert (NE' : blk_slot blk' <> blk_slot blk).
      { intros EQ. rewrite EQ in NEQ. rewrite aptr_eqb_refl in NEQ. cbn in NEQ. exact NEQ. }
      destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hin') as [(r' & Hr' & Kr' & A16' & AEND' & _) _ _].
      destruct (N.eq_dec (fst (blk_slot blk')) (fst bm)) as [EF|NF].
      + specialize (BCLR blk' Hin' NE' EF). rewrite SS0 in BCLR.
        assert (r' = r) as -> by (rewrite EF, Ebm, Hr in Hr'; congruence).
        clear -BCLR Hab AEND' LOv RBC SPAN Sc SIL SI0 B0 RUr. unfold UNIT, IB in *; ceil_facts. lia.
      + assert (NR : fst (blk_slot blk') <> fst b) by (rewrite <- Ebm; exact NF).
        pose proof (lr_lo_group r Kr). pose proof (lr_lo_group r' Kr'). pose proof (round_up_pg_ge (r_len r')).
        destruct (WR _ _ Hr') as (_ & _ & _ & RBC' & _).
        destruct (DJ _ _ _ _ Hr' Hr NR); clear -H H0 H1 H2 Hab A16' AEND' LOv RBC RBC' SPAN Sc SIL SI0 B0 RUr; unfold UNIT, IB in *; ceil_facts; lia.
    - pose proof the_tb_facts as TF. clear -CA NE TLSr LOv TF RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts. lia. }
  assert (SPAN_AUX : forall mx, rpres_except SPANC m mx -> rauxv_ok mx B).
  { intros mx PEx. eapply rauxv_ok_pres; [exact AUXB| exact PEx| |]; subst SPANC C0; cbv beta.
    - intros a Ha. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. clear -Ha SB SLO LOv RBC SPAN Sc SIL SI0 B0. unfold UNIT, IB in *; ceil_facts. lia.
    - intros a Ha. unfold RAUXV_CELL in Ha. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. clear -Ha LOv DRr RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts. lia. }
  assert (SPAN_ERR : forall mx, rpres_except SPANC m mx -> rw_cells usegs mx (errno_addr tp) [C4 errv]).
  { intros mx PEx. eapply rpres_except_rw_cells; [exact PEx| exact ERR|]. rewrite ETP. change (Z.of_nat (cells_size [C4 errv])) with 4.
    intros a Ha. subst SPANC C0; cbv beta. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
    pose proof the_tb_facts as TF.
    clear -Ha TLSr LOv TF RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts.
    destruct TF as (TF1 & TF2 & TF3 & TF4). intros [X|X]; lia. }
  assert (SPAN_REPL : forall mx, rpres_except SPANC m mx -> rw_cells usegs mx RMREPLACED [C4 (Z_to_bv 64 0)]).
  { intros mx PEx. eapply rpres_except_rw_cells; [exact PEx| exact REPL|]. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4.
    intros a Ha. subst SPANC C0; cbv beta. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL. unfold RMREPLACED, RCTX in Ha.
    clear -Ha LOv DRr RUr SPAN Sc SIL SI0 B0 RB0. unfold UNIT, IB in *; ceil_facts. intros [X|X]; lia. }
  destruct (WR _ _ Hr) as (_ & RBAL & _).
  assert (P16 : P mod 16 = 0).
  { subst P. pose proof P16m as X. unfold frozen in X. clear -X RBAL. Z.div_mod_to_equations. lia. }
  (* [comment removed for export] *)
  pose proof (rw_cells_bytes_at _ _ _ _ CHUNK) as BS0. cbn [cells_bytes cbytes] in BS0. rewrite app_nil_r in BS0.
  assert (LBS : length bs = Z.to_nat (blk_size blk)).
  { destruct CHUNK as [[Hwf _] _]. cbn in Hwf. exact (proj1 Hwf). }
  (* [comment removed for export] *)
  apply rimplT_if; intros HC1.
  - (* [comment removed for export] *)
    apply andb_prop in HC1 as [HC1 HC3]. apply andb_prop in HC1 as [HC1 HC2]. apply Z.leb_le in HC1. apply Z.ltb_lt in HC2. apply Z.leb_le in HC3.
    pose proof (size_to_class_props n ltac:(unfold MMAP_THRESHOLD in HC2 |- *; lia)) as (STC & _ & _).
    assert (SC48 : m_sizeclass mr < 48) by (clear -STC HC3 GSC; subst mr; lia).
    assert (STR31 : get_stride mr < 2^31).
    { pose proof (mf_gmeta _ _ MF g b (go_mem _ _ _ GO)) as FG. cbv zeta in FG. subst mr.
      destruct FG as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S31 & _). apply S31. exact SC48. }
    apply rimplT_ret.
    eapply evt_cut; [exact MACH|]. intros ms1 (t2' & t3' & t4' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MR1).
    eapply evt_cut.
    { eapply (rrealloc_dec_small ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2' s0 (wz (conc st0 g)) a0 a1 (wz (conc st0 b)) (wz (meta_word mr))
                (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1 n (m_sizeclass mr) (E - P));
        [rewrite A1; apply unsigned_lit; lia| exact (conj (proj1 N) HC2)| subst E P; lia| | clear -GSC; subst mr; lia| exact MI1].
      subst E P. pose proof (round_up_pg_ge (r_len r)). ceil_facts. lia. }
    intros ms2 (t1' & t2'' & a2' & a4' & a5' & a7' & t3'' & t4'' & ->).
    replace (m_sizeclass mr <=? size_to_class n + 1) with true by (symmetry; apply Z.leb_le; exact HC3).
    assert (MR1t : rmrep st m1) by (apply rmrep_set_tick; exact MR1).
    eapply evt_mono.
    { eapply (rrealloc_inplace_walk ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t1' t2'' s0 (wz (conc st0 g)) a0 a1 a2' (Z_to_bv 64 (m_sizeclass mr)) a4' a5' a7'
                (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3'' t4'' t5 t6 F fc
                m1 m1 lo st pf e r v3 n ra s0 s1 s2 s3 s4 s5 s6);
        first [exact MR1t| exact MI1| exact TKt| exact Kr| idtac].
      - rewrite unsigned_lit by lia. exact ST1.
      - rewrite unsigned_lit by lia. exact FR1.
      - exact LO.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. lia.
      - apply rpres_except_refl.
      - apply wmono_refl.
      - rewrite Fp. exact Hr.
      - rewrite Fe, Fp. reflexivity.
      - rewrite A0, HAp. apply unsigned_lit. lia.
      - rewrite A1. apply unsigned_lit. lia.
      - lia.
      - clear -HC1. lia.
      - rewrite Se, Sp, Sc. fold mr. clear -STR31 Hoff SI0. subst mr. lia.
      - clear -Sp Sc B0 SI0 Hoff. subst mr. lia.
      - exact (proj1 ERNG).
      - replace (snd pf - 3) with (snd c0 + UNIT * off - 3) by (unfold UNIT in *; lia). unfold pf; cbn [aadd fst]. exact C3.
      - intros b' gh Hb' Hf'. rewrite Fp, <- Ebm in Hf'. destruct (GCLR b' gh Hb' Hf') as [X|X]; rewrite SS0 in X; [left| right]; rewrite ?Se, ?Sp, ?Sc in *; subst mr; clear -X Hoff SI0 Sc S16; unfold UNIT in *; lia. }
    intros msf POST. unfold rrret_post in POST.
    destruct POST as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & -> & QQ).
    destruct QQ as (MR' & TK' & MI' & ST' & FR' & PE' & WM').
    rewrite !unsigned_lit in ST', FR' by lia. rewrite unsigned_lit by lia.
    replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) in * by lia. rewrite Z_to_bv_bv_unsigned.
    rewrite set_size_land31. set (st' := set_size pf e n v3 st) in *.
    pose proof (rmrep_havoc st' m' pf n MR' TK') as [MRh TKh].
    assert (RGh : s_regions (havoc pf n st') = s_regions st0) by (subst st' st; rewrite s_regions_havoc, s_regions_set_size; reflexivity).
    assert (Hrh : s_regions (havoc pf n st') !! (fst pf) = Some r) by (rewrite RGh, Fp; exact Hr).
    assert (CPh : conc (havoc pf n st') pf = P) by (rewrite (conc_region' _ pf r Hrh); reflexivity).
    assert (PEi : rpres_except SPANC m m').
    { eapply rpres_except_trans.
      - eapply rpres_except_of_munch; [exact MU1| exact WM1|]. intros a Ha NC. subst SPANC. cbv beta in NC. cbn [outside]. split; [|exact Logic.I]. clear -NC SLO. lia.
      - eapply rpres_except_mono; [exact PE'|]. intros a Ha. subst SPANC C0 P E. cbv beta. right.
        rewrite Se, Sp in Ha. rewrite Se, Sp in HC1. rewrite Sc in Ha, HC1 |- *. clear -Ha Hoff SI0 HC1 N. unfold UNIT, IB in *. lia. }
    unfold rrfinQ. cbn [fst snd oconc]. rewrite CPh. exists m', errv. do 14 eexists.
    split; [reflexivity|]. split; [exact MI'|].
    split. { replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat (cells_size (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6))) by (cbn; lia).
             eapply stk_release; [exact ST'| exact FR'| clear -SLO; lia]. }
    split; [exact (SPAN_ERR m' PEi)|]. split; [exact (SPAN_AUX m' PEi)|].
    split; [exact MRh|].
    split. { eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_malloc_big.brk_link_ps_ext; [| | exact BL].
             - subst st' st. unfold ctx. rewrite s_ctx_havoc, s_ctx_set_size. reflexivity.
             - intros rid boff _. unfold conc, get_region. rewrite RGh. reflexivity. }
    split; [exact (SPAN_PRES m' PEi)|]. split; [exact (SPAN_REPL m' PEi)|]. split; [reflexivity|]. split; [reflexivity|].
    split. { unfold rblock_range. subst P E. rewrite Se, Sp, Sc in HC1. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
             split; [clear -RB0 Sp Sc SI0 Hoff B0; lia|]. split; [exact P16|]. split; [clear -N; lia|].
             clear -HC1 RBC DRr TLSr SPAN Sp Sc SI0 SIL Hoff B0 RB0 N RUr. unfold UNIT, IB in *; ceil_facts. lia. }
    (* [comment removed for export] *)
    destruct (ruser_chunk (havoc pf n st') m' pf r n MRh Hrh Kr ltac:(clear -Sp Sc SI0 Hoff B0; lia) ltac:(clear -HC1 ERNG; lia) ltac:(clear -N; lia)) as (J & JCH).
    rewrite CPh in JCH.
    set (k1 := Z.to_nat (Z.min (blk_size blk) n)).
    assert (K1 : (k1 <= Z.to_nat n)%nat) by (subst k1; clear -N SZ; lia).
    assert (LK1 : length (firstn k1 bs) = k1) by (rewrite length_firstn, LBS; subst k1; clear -N SZ; lia).
    assert (BS1 : bytes_at usegs m' P (firstn k1 bs)).
    { eapply rpres_except_bytes_at; [exact PE'| |].
      - eapply bytes_at_transport; [| exact MU1|].
        + eapply bytes_at_firstn. replace P with (blk_addr blk) by (subst P; exact HAp). exact BS0.
        + rewrite LK1. cbn. subst P k1. rewrite Sp, Sc. rewrite Z.mul_add_distr_l, Z.mul_1_r in SIL.
          clear -Hoff SI0 N SZ OS SLO LOv RBC SPAN SIL B0. unfold UNIT, IB in *; ceil_facts. lia.
      - rewrite LK1. intros a Ha. subst P k1. cbv beta. clear -Ha HC1 Hoff N SZ. lia. }
    exists (skipn k1 J). pose proof (rw_cells_CB_prefix_agree m' P (Z.to_nat n) J (firstn k1 bs) JCH BS1 ltac:(rewrite LK1; exact K1)) as CH'.
    rewrite LK1 in CH'. replace (Z.to_nat (n - Z.min (blk_size blk) n)) with (Z.to_nat n - k1)%nat by (subst k1; clear -N SZ; lia). exact CH'.
  - (* [comment removed for export] *)
    assert (ERSV : E - (if 160 <=? v3 then r32 else Z.shiftr v3 5) = blk_addr blk + blk_size blk) by (rewrite RSVEQ, HAp; subst P; clear; lia).
    apply rimplT_if; intros HC4.
    + (* [comment removed for export] *)
      apply andb_prop in HC4 as [HC4a HC4b]. apply Z.leb_le in HC4a. apply Z.leb_le in HC4b.
      assert (SC63 : m_sizeclass mr = 63 /\ m_last_idx mr = 0 /\ 0 < m_maplen mr) by (clear -GSC HC4a; lia). destruct SC63 as (SC63 & LI0 & ML0).
      eapply rimplT_evt; [| intros msX HX; exact HX].
      eapply evt_cut; [exact MACH|]. intros ms1 (t2' & t3' & t4' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MR1).
      assert (PE1 : rpres_except SPANC m m1).
      { eapply rpres_except_of_munch; [exact MU1| exact WM1|]. intros a Ha NC. subst SPANC. cbv beta in NC. cbn [outside]. split; [|exact Logic.I]. clear -NC SLO. lia. }
      eapply evt_cut.
      { eapply (rrealloc_dec_big ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2' s0 (wz (conc st0 g)) a0 a1 (wz (conc st0 b)) (wz (meta_word mr))
                  (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1 n (m_sizeclass mr) (E - P));
          [rewrite A1; apply unsigned_lit; lia| clear -HC4b N; lia| subst E P; pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia| exact SC63]. }
      intros ms2 (t2'' & a5' & t3'' & ->).
      rewrite ERSV, A1. apply evt_done. subst C0.
      apply (RBIG63 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s LB blk off bs n lo B g b ai r i v3 (if 160 <=? v3 then r32 else Z.shiftr v3 5)
               t2'' a0 a5' t3'' t4' t5 t6 AR Hin Hoff HA BL SL Hgh FB Hr Kr SC63 LI0 ML0 I V31 C3 V3R OS SZ (conj HC4b (proj2 N)));
        [exact RSVEQ| exact RSV0| exact SB| exact LO| unfold RREALLOC_STACK; exact SLO| exact TP| exact A0| exact MU1| exact WM1| |].
      * split; [exact MI1|]. split; [exact ST1|]. split; [exact MR1|]. split; [exact (SPAN_AUX m1 PE1)|]. split; [exact (SPAN_REPL m1 PE1)|].
        split. { eapply rw_cells_transport; [exact CHUNK| exact MU1| exact WM1|]. cbn. split; [| exact Logic.I]. left.
                 clear -AEND RBC LOv SLO SZ. ceil_facts. lia. }
        split; [exact (SPAN_PRES m1 PE1)|]. split; [exists errv; exact (SPAN_ERR m1 PE1)| exact FR1].
      * exact (rrealloc_fallback ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB blk off bs n lo B AR Hin Hoff HA BL SB LO ltac:(unfold RREALLOC_STACK; lia) TP N).
    + (* [comment removed for export] *)
      eapply rimplT_evt; [| intros msX HX; exact HX].
      eapply evt_cut; [exact MACH|]. intros ms1 (t2' & t3' & t4' & m1 & -> & MU1 & WM1 & MI1 & ST1 & FR1 & MR1).
      assert (PE1 : rpres_except SPANC m m1).
      { eapply rpres_except_of_munch; [exact MU1| exact WM1|]. intros a Ha NC. subst SPANC. cbv beta in NC. cbn [outside]. split; [|exact Logic.I]. clear -NC SLO. lia. }
      eapply evt_cut.
      { eapply (rrealloc_dec_fb ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) (Z_to_bv 64 C0) t2' s0 (wz (conc st0 g)) a0 a1 (wz (conc st0 b)) (wz (meta_word mr))
                  (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - (if 160 <=? v3 then r32 else Z.shiftr v3 5))) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5 t6 F fc m1 n (m_sizeclass mr) (E - P));
          [rewrite A1; apply unsigned_lit; lia| lia| subst E P; pose proof (round_up_pg_ge (r_len r)); ceil_facts; lia| clear -GSC; lia| clear -GSC; lia| exact MI1| | exact HC4].
        replace (snd e - snd pf) with (E - P) in HC1 by (subst E P; clear; lia). exact HC1. }
      intros ms2 (t1'' & t2'' & a2' & a4' & a5' & a7' & t3'' & t4'' & ->).
      rewrite ERSV. rewrite A1. apply evt_done.
      apply (rrealloc_fallback ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m s LB blk off bs n lo B AR Hin Hoff HA BL SB LO ltac:(unfold RREALLOC_STACK; lia) TP N).
      * split; [exact MI1|]. split; [exact ST1|]. split; [exact MR1|]. split; [exact (SPAN_AUX m1 PE1)|]. split; [exact (SPAN_REPL m1 PE1)|].
        split. { eapply rw_cells_transport; [exact CHUNK| exact MU1| exact WM1|]. cbn. split; [| exact Logic.I]. left.
                 clear -AEND RBC LOv SLO SZ. ceil_facts. lia. }
        split; [exact (SPAN_PRES m1 PE1)|]. split; [exists errv; exact (SPAN_ERR m1 PE1)| exact FR1].
      * rewrite A0, HAp. apply unsigned_lit. lia.
Qed.
End Sz3.
Theorem rrealloc_implT : ltac:(let t := eval cbv delta [rrealloc_implT__stmt] in rrealloc_implT__stmt in exact t).
Proof using AS_PRE RAS RBIG RBIG63. intros ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB blk off bs n lo B errv. ltac2:(SecDiet.SzSec.closeP 'rrealloc_implT__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rrealloc_spec_proof__stmt : Prop := rrealloc_stmt.
Section Sz4.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A sz n lo B bs errv : ltac2:(SecDiet.SzSec.tyM 'rrealloc_spec_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_spec_proof__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_spec_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using AS_PRE RAS RBIG RBIG63. pin_using (fun (AS_PRE RAS RBIG RBIG63 : unit) => tt). ceil_facts. msec_facts.
  intros HP Hin AV SB ST LO SLO ERR MI TP CH A0 A1 N.
  destruct HP as (LB0 & PERM & MR & [BLK AR] & REPL).
  set (st := ps_m s) in *.
  assert (Hin0 : In (p, A, sz) LB0) by (eapply Permutation_in; [apply Permutation_sym; exact PERM| exact Hin]).
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (areach_blk_addr st LB0 (p, A, sz) AR Hin0) as HA. unfold blk_addr, blk_slot, blk_id in HA. cbn [fst snd] in HA.
  pose proof (proj2 (brk_link_ps_iff st s) BLK) as BL.
  assert (O0 : 0 <= snd p).
  { pose proof (proj1 (List.Forall_forall _ _) (ci_blks _ _ C) (p, A, sz) Hin0) as [(g & i & b & _ & _ & _ & _ & _ & (off & O0 & OA & _)) _ _].
    unfold blk_addr, blk_slot in OA. cbn [fst snd] in OA. rewrite HA in OA. unfold UNIT in OA. lia. }
  (* [comment removed for export] *)
  eapply (implM_evt usegs _ _ _ (fun ms1 => ms1 = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                                  F (Z_to_bv 64 rrealloc_entry) fc None m (seg_rom usegs))).
  { unfold RREALLOC_SYM. step. apply evt_done. reflexivity. }
  cbv beta. intros ms' ->.
  eapply (raw_realloc_bridge usegs s (Some (aadd (fst p) (UNIT * snd p))) n m
            (fun res s' msf => rrfinQ m st s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB0 (p, A, sz) bs n lo B res s' msf
                               /\ leaf_of m (realloc st (Some (aadd (fst p) (UNIT * snd p))) n) res)).
  - apply rimplT_reach.
    apply (rrealloc_implT ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB0 (p, A, sz) (snd p) bs n lo B errv
             AR C Hin0 O0 HA MR BL MI AV SB ST LO SLO ERR TP CH REPL A0 A1 N).
  - intros st' q s' msf [FQ LEAF]. cbv beta. unfold rrfinQ in FQ. cbn [fst snd] in FQ.
    destruct FQ as (m' & errv' & u0 & u1 & u2 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & u3 & u4 & u5 & u6 & -> & MI' & ST' & ERR' & AUX' & MR' & BL' & HPR & REPL' & PSM & PSR & RES).
    pose proof (lb_remove_lbrm LB p A sz (NoDup_map_perm blk_slot LB0 LB PERM (ci_nodup _ _ C)) Hin) as ELB.
    destruct LEAF as (l0 & ans & l1 & FF).
    pose proof (@OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_realloc _ _ _ st LB0 (p, A, sz) n l0 l1 ans st' q AR Hin0 ltac:(lia)
                  ltac:(unfold size_overflows; apply Z.leb_gt; lia) ltac:(unfold OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.KInv.LEN_MAX, PGSZ; lia)
                  ltac:(unfold blk_ptr; cbn [blk_slot blk_id fst snd]; exact FF)) as AR'.
    unfold rrealloc_post. do 15 eexists. exists m', errv'. split; [reflexivity|].
    split; [exact MI'|]. split; [exact ST'|]. split; [exact ERR'|]. split; [exact AUX'|].
    split. { eapply rheap_pres_weaken; [exact HPR| lia|]. intros b' Hb'. rewrite ELB in Hb'. eapply In_lbrm_perm; [apply Permutation_sym; exact PERM| exact Hb']. }
    split; [rewrite ps_rest_set_m; exact PSR|].
    assert (BLs : brk_link (ps_m (set_m st' s')) (ps_brk (set_m st' s'))).
    { rewrite ps_m_set_m, ps_brk_set_m. apply (proj1 (brk_link_ps_iff st' s')). exact BL'. }
    destruct q as [q|].
    + destruct RES as [BR [junk UCH]]. destruct AR' as (c' & off' & Eq & Hoff' & _ & AR').
      exists c', off', (conc st' q).
      split; [exact Eq|]. split; [reflexivity|]. split; [rewrite ps_m_set_m; reflexivity|]. split; [exact BR|].
      split; [| exists junk; exact UCH].
      unfold RHEAP, RHEAPm. exists (((c', off'), conc st' q, n) :: lbrm LB0 (p, A, sz)).
      split; [rewrite ELB; apply perm_skip; apply lbrm_perm; exact PERM|].
      split; [rewrite ps_m_set_m; exact MR'|]. split; [| exact REPL']. split; [exact BLs|]. rewrite ps_m_set_m. exact AR'.
    + destruct RES as [EEN CHK].
      split; [reflexivity|]. split; [exact EEN|]. split; [| exact CHK].
      unfold RHEAP, RHEAPm. exists LB0. split; [exact PERM|].
      split; [rewrite ps_m_set_m; exact MR'|]. split; [| exact REPL']. split; [exact BLs|]. rewrite ps_m_set_m. exact AR'.
Qed.
End Sz4.
Theorem rrealloc_spec_proof : ltac:(let t := eval cbv delta [rrealloc_spec_proof__stmt] in rrealloc_spec_proof__stmt in exact t).
Proof using AS_PRE RAS RBIG RBIG63. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m s LB p A sz n lo B bs errv. ltac2:(SecDiet.SzSec.closeP 'rrealloc_spec_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TOPLEVEL.
End PORT.

End WithCeil.
End TwB.
End RF_realloc.

(* [comment removed for export] *)
Module RF_realloc63.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_free_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_reallocA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free_spec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_reallocA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_reallocB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_reallocC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mremap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_realloc63R.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_invR.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; ceil_facts; lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Definition rrip_Q63 (sp : word) (lo : Z) (st' : mstate) (m0 : mem) (raS s0S s1S s2S s3S s4S s5S s6S : word) (C : Z -> Prop) (m' : mem) : Prop :=
  rmrep st' m' /\ ticks_ok st' /\ mem_inv ssegs m' /\ stk ssegs m' lo (bv_unsigned sp)
  /\ rw_cells ssegs m' (bv_unsigned sp) (rrealloc_frame raS s0S s1S s2S s3S s4S s5S s6S)
  /\ rpres_except C m0 m' /\ wmono ssegs m0 m'.

(* [comment removed for export] *)
Lemma rrealloc_setsize63_walk : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : mem) (lo : Z) (st : mstate) (p e : aptr) (r : region) (b3 n : Z) (raS s0S s1S s2S s3S s4S s5S s6S : word) (C : Z -> Prop),
  let P := r_base r + snd p in
  let E := r_base r + snd e in
  let st' := set_size p e n b3 (wr8 e 0 st) in
  (forall a, a = P - 3 \/ P + n <= a < E + 1 -> C a) ->
  rmrep st m -> mem_inv ssegs m -> ticks_ok st ->
  stk ssegs m lo (bv_unsigned sp) -> rw_cells ssegs m (bv_unsigned sp) (rrealloc_frame raS s0S s1S s2S s3S s4S s5S s6S) ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  rpres_except C m0 m -> wmono ssegs m0 m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> fst e = fst p ->
  bv_unsigned a0 = P -> 0 <= n < 2^32 -> snd p + n <= snd e -> snd e - snd p - n < 2^31 -> 16 <= snd p ->
  snd e + 1 <= round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst p)) (snd p - 3) = Known b3 ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd b + 9 <= snd p - 3 \/ snd e + 1 <= snd b) ->
  evt ssegs (rrret_post sp gp tp s7 s8 s9 s10 s11 F fc raS s0S s1S s2S s3S s4S s5S s6S P (rrip_Q63 sp lo st' m0 raS s0S s1S s2S s3S s4S s5S s6S C))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (n + P)) a2 (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5 (Z_to_bv 64 (snd e - snd p - n)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a460) fc None m (seg_rom ssegs)).
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros until C. intros P E st' HCC MR0 MI TK0 ST FR LO SLO SPH PE00 WM0 Hr0 Hk Fe HP N0 LE AV P16 EHI HK30 HCLR0.
  (* [comment removed for export] *)
  pose proof MR0 as (WF0 & _ & _ & _ & _ & SH0). pose proof WF0 as (_ & WR0 & _).
  destruct (WR0 (fst p) r Hr0) as (B00 & _ & _ & BC0 & _). ceil_facts.
  assert (ELO : E + 1 <= lo) by (subst E; lia).
  destruct (SH0 (fst p) r Hr0 Hk) as [HWr0 _]. clear SH0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (SOK0 : store_ok ssegs mX (wa (E + 4 + -4)) 1 = true)
      by (replace (E + 4 + -4) with (r_base r + snd e) by (subst E; lia); apply (wr_at_store_ok ssegs mX _ _ (snd e) 1 HWr0); cbn; lia) end.
  step.
  pose proof (rmrep_wr8 st _ e 0 r MR0 TK0 ltac:(rewrite Fe; exact Hr0) Hk ltac:(lia)
                ltac:(intros b gh Hb Hfb; rewrite Fe in Hfb; destruct (HCLR0 b gh Hb Hfb); lia) ltac:(lia)) as MR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + snd e)) [b8 0])
      by (f_equal; try reflexivity; unfold wa; f_equal; subst E; lia) end.
  pose proof (munch_refl [(E, E + 1)]%Z m) as MUe. pose proof (wmono_refl ssegs m) as WMe.
  store_done.
  pose proof (ticks_ok_wr8 st e 0 TK0) as TK.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (PE0 : rpres_except C m0 mX)
      by (eapply rpres_except_trans; [exact PE00|]; apply (rpres_except_of_munch_cov _ _ _ _ MUe); [assumption| cbn [ivs_covered]; split; [intros x Hx; apply HCC; right; subst E P; lia| exact I]]) end.
  clear MUe.
  set (stw := wr8 e 0 st) in *.
  assert (Hr : s_regions stw !! fst p = Some r) by exact Hr0.
  assert (HK3 : cell_read (get_shadow stw (fst p)) (snd p - 3) = Known b3).
  { subst stw. rewrite <- Fe. rewrite (MallocRep.cell_read_wr8_other st e 0 (snd p - 3)) by lia. rewrite Fe. exact HK30. }
  assert (HCLR : forall b gh, s_groups stw !! b = Some gh -> fst b = fst p -> snd b + 9 <= snd p - 3 \/ snd e <= snd b).
  { intros b gh Hb Hfb. destruct (HCLR0 b gh Hb Hfb); lia. }
  clearbody stw. clear MR0 TK0 HK30 HCLR0 Hr0 PE00. rename stw into st0. rename st into stX. rename st0 into st.
  try clear WMe. try clear HWr0. try clear m. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m end.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct (rmrep_shadow_read st m (fst p) r (snd p - 3) b3 MR Hr Hk ltac:(lia) HK3) as [R3 B3].
  set (rsv := snd e - snd p - n) in *.
  assert (RSV : 0 <= rsv < 2^31) by (subst rsv; lia).
  unfold UNIT, IB in *; ceil_facts.
  assert (ER : 0 <= E /\ E + 1 <= 2^64) by (subst E; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (PR : 16 <= P /\ P + n <= E) by (subst P E; lia).
  assert (ERSV : E - (n + P) = rsv) by (subst E P rsv; lia).
  fold rsv.
  (* [comment removed for export] *)
  assert (TAIL : forall (a1v a2v a4v a6v : word) (c : Z) (st2 : mstate) (m2 : mem),
    bv_unsigned a1v = c -> 0 <= c < 8 ->
    st' = wr8 (aadd p (-3)) (Z.land b3 31 + Z.shiftl c 5) st2 ->
    rmrep st2 m2 -> ticks_ok st2 -> mem_inv ssegs m2 -> s_regions st2 = s_regions st -> s_groups st2 = s_groups st ->
    cell_read (get_shadow st2 (fst p)) (snd p - 3) = Known b3 ->
    stk ssegs m2 lo (bv_unsigned sp) -> rw_cells ssegs m2 (bv_unsigned sp) (rrealloc_frame raS s0S s1S s2S s3S s4S s5S s6S) ->
    rpres_except C m0 m2 -> wmono ssegs m0 m2 ->
    evt ssegs (rrret_post sp gp tp s7 s8 s9 s10 s11 F fc raS s0S s1S s2S s3S s4S s5S s6S P (rrip_Q63 sp lo st' m0 raS s0S s1S s2S s3S s4S s5S s6S C))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1v a2v (Z_to_bv 64 (E + 4)) a4v a5 a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a540) fc None m2 (seg_rom ssegs))).
  { intros a1v a2v a4v a6v c st2 m2 HC CR Est' MR2 TK2 MI2 RG2 GR2 HK3' ST2 FR2 PE2 WM2.
    destruct (rmrep_shadow_read st2 m2 (fst p) r (snd p - 3) b3 MR2 ltac:(rewrite RG2; exact Hr) Hk ltac:(lia) HK3') as [R3' _].
    replace (r_base r + (snd p - 3)) with (bv_unsigned a0 + -3) in R3' by lia.
    (* [comment removed for export] *)
    step. step. step. step.
    rewrite HC, ?(wz_unsigned b3), ?zxb_b8, ?(wz_unsigned b3) by lia.
    rewrite Z.shiftl_mul_pow2, ?(unsigned_lit (c * 2 ^ 5)) by lia. change (2 ^ 5) with 32.
    assert (L31 : 0 <= Z.land b3 31 < 32). { split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
    rewrite ?(unsigned_lit (Z.land b3 31)) by lia. rewrite lor_shl5_land31 by lia.
    set (V := Z.land b3 31 + Z.shiftl c 5) in *.
    assert (VR : 0 <= V < 256) by (subst V; rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
    (* [comment removed for export] *)
    pose proof MR2 as (_ & _ & _ & _ & _ & SH2). destruct (SH2 (fst p) r ltac:(rewrite RG2; exact Hr) Hk) as [HWr2 _]. clear SH2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (SOK : store_ok ssegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
        by (replace (bv_unsigned a0 + -3) with (r_base r + (snd p - 3)) by lia; apply (wr_at_store_ok ssegs mX _ _ (snd p - 3) 1 HWr2); cbn; lia) end.
    step.
    pose proof (rmrep_wr8 st2 _ (aadd p (-3)) V r MR2 TK2 ltac:(rewrite RG2; exact Hr) Hk ltac:(cbn; lia)
                  ltac:(intros b gh Hb Hfb; cbn [aadd fst snd] in Hfb |- *; rewrite GR2 in Hb; destruct (HCLR b gh Hb Hfb); lia) ltac:(lia)) as MR3.
    cbn [aadd snd] in MR3. rewrite <- Est' in MR3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
      replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (snd p + -3))) [b8 V])
        by (f_equal; [unfold wa; f_equal; lia| cbn; rewrite ?(unsigned_lit V) by lia; reflexivity]) end.
    pose proof (munch_refl [(P - 3, P - 2)]%Z m2) as MU3. pose proof (wmono_refl ssegs m2) as WMr.
    store_done.
    pose proof (ticks_ok_wr8 st2 (aadd p (-3)) V TK2) as TK3. rewrite <- Est' in TK3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (PE3 : rpres_except C m0 mX)
        by (eapply rpres_except_trans; [exact PE2|]; apply (rpres_except_of_munch_cov _ _ _ _ MU3); [exact WMr| cbn [ivs_covered]; split; [intros x Hx; apply HCC; left; lia| exact I]]) end.
    replace a0 with (Z_to_bv 64 P) by (rewrite <- HP; apply (Z_to_bv_bv_unsigned a0)).
    eapply rrealloc_epilogue; [eassumption| eassumption| exact SPH| assumption|].
    unfold rrip_Q63. split; [exact MR3|]. split; [exact TK3|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact PE3| assumption]. }
  (* [comment removed for export] *)
  pose proof (set_size_cases p e n b3 st) as SS. cbv zeta in SS. fold rsv in SS. fold st' in SS.
  step. if_cases K0; zify_cond K0; rewrite ?(unsigned_lit rsv) in K0 by lia.
  - (* [comment removed for export] *)
    rewrite K0 in SS. cbn [Z.eqb] in SS.
    step. step.
    eapply (TAIL _ _ _ _ 0 st m); try eassumption; try reflexivity; try lia. all: try (rewrite unsigned_lit by lia; reflexivity).
  - replace (rsv =? 0) with false in SS by (symmetry; apply Z.eqb_neq; exact K0).
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)), ERSV, swrap32_small by lia.
    step. rewrite ?(unsigned_lit rsv), swrap32_small by lia.
    step. replace (E + (0 - rsv)) with (r_base r + (snd e + - rsv)) by (subst E; lia).
    step.
    (* [comment removed for export] *)
    pose proof MR as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (SOK1 : store_ok ssegs mX (wa (r_base r + (snd e + - rsv) + 0)) 1 = true)
        by (replace (r_base r + (snd e + - rsv) + 0) with (r_base r + (snd e - rsv)) by lia; apply (wr_at_store_ok ssegs mX _ _ (snd e - rsv) 1 HWr); cbn; lia) end.
    step.
    pose proof (rmrep_wr8 st _ (aadd e (- rsv)) 0 r MR TK ltac:(cbn [aadd fst snd]; rewrite Fe; exact Hr) Hk ltac:(cbn; lia)
                  ltac:(intros b gh Hb Hfb; cbn [aadd fst snd] in Hfb |- *; rewrite Fe in Hfb; destruct (HCLR b gh Hb Hfb); lia) ltac:(lia)) as MR1.
    cbn [aadd snd] in MR1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
      replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (snd e + - rsv))) [b8 0])
        by (f_equal; try reflexivity; unfold wa; f_equal; lia) end.
    pose proof (munch_refl [(E - rsv, E)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WMa.
    store_done.
    pose proof (ticks_ok_wr8 st (aadd e (- rsv)) 0 TK) as TK1.
    set (st1 := wr8 (aadd e (- rsv)) 0 st) in *.
    assert (PEX : forall mX, munch [(E - rsv, E)]%Z m mX -> wmono ssegs m mX -> rpres_except C m0 mX).
    { intros mX MUX WMX. eapply rpres_except_trans; [exact PE0|]. apply (rpres_except_of_munch_cov _ _ _ _ MUX); [exact WMX|].
      cbn [ivs_covered]. split; [intros x Hx; apply HCC; right; subst E P rsv; lia| exact I]. }
    assert (RG1 : s_regions st1 = s_regions st) by reflexivity.
    assert (GR1 : s_groups st1 = s_groups st) by reflexivity.
    assert (HK3a : cell_read (get_shadow st1 (fst p)) (snd p - 3) = Known b3).
    { subst st1. rewrite <- Fe. change (fst e) with (fst (aadd e (- rsv))). rewrite (MallocRep.cell_read_wr8_other st (aadd e (- rsv)) 0 (snd p - 3)) by (cbn; lia).
      cbn [aadd fst]. rewrite Fe. exact HK3. }
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_of_Z in K5 by lia.
    + (* [comment removed for export] *)
      replace (5 <=? rsv) with false in SS by (symmetry; apply Z.leb_gt; lia).
      step.
      eapply (TAIL _ _ _ _ rsv st1); try eassumption; try lia; [rewrite unsigned_lit by lia; reflexivity| apply PEX; assumption].
    + (* [comment removed for export] *)
      replace (5 <=? rsv) with true in SS by (symmetry; apply Z.leb_le; lia).
      rewrite (wr8_wr32_comm st1 (aadd e (-5)) (aadd e (-4)) 0 rsv) in SS by (cbn; lia).
      (* [comment removed for export] *)
      pose proof MR1 as (_ & _ & _ & _ & _ & SHb). destruct (SHb (fst p) r Hr Hk) as [HWrb _]. clear SHb.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (SOK2 : store_ok ssegs mX (wa (E + 4 + -9)) 1 = true)
          by (replace (E + 4 + -9) with (r_base r + (snd e - 5)) by (subst E; lia); apply (wr_at_store_ok ssegs mX _ _ (snd e - 5) 1 HWrb); cbn; lia) end.
      step.
      pose proof (rmrep_wr8 st1 _ (aadd e (-5)) 0 r MR1 TK1 ltac:(cbn [aadd fst snd]; rewrite Fe; exact Hr) Hk ltac:(cbn; lia)
                    ltac:(intros b gh Hb Hfb; cbn [aadd fst snd] in Hfb |- *; rewrite Fe in Hfb; destruct (HCLR b gh Hb Hfb); lia) ltac:(lia)) as MR2.
      cbn [aadd snd] in MR2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
        replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (snd e + -5))) [b8 0])
          by (f_equal; try reflexivity; unfold wa; f_equal; subst E; lia) end.
      store_done.
      pose proof (ticks_ok_wr8 st1 (aadd e (-5)) 0 TK1) as TK2.
      set (st2 := wr8 (aadd e (-5)) 0 st1) in *.
      (* [comment removed for export] *)
      pose proof MR2 as (_ & _ & _ & _ & _ & SHc). destruct (SHc (fst p) r Hr Hk) as [HWrc _]. clear SHc.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (SOK3 : store_ok ssegs mX (wa (E + 4 + -8)) 4 = true)
          by (replace (E + 4 + -8) with (r_base r + (snd e - 4)) by (subst E; lia); apply (wr_at_store_ok ssegs mX _ _ (snd e - 4) 4 HWrc); cbn; lia) end.
      step.
      destruct (rmrep_wr32 st2 _ (aadd e (-4)) rsv r MR2 TK2 ltac:(cbn [aadd fst snd]; rewrite Fe; exact Hr) Hk ltac:(cbn; lia) ltac:(cbn; lia)
                    ltac:(intros b gh Hb Hfb; cbn [aadd fst snd] in Hfb |- *; rewrite Fe in Hfb; destruct (HCLR b gh Hb Hfb); lia) ltac:(lia)) as [MR3 TK3].
      cbn [aadd snd] in MR3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
        replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (snd e + -4))) (le4 (wz rsv)))
          by (f_equal; try reflexivity; unfold wa; f_equal; subst E; lia) end.
      store_done.
      (* [comment removed for export] *)
      step.
      eapply (TAIL _ _ _ _ 5 (wr32 (aadd e (-4)) rsv st2)); try eassumption; try lia.
      * rewrite unsigned_lit by lia. reflexivity.
      * subst st2 st1. unfold wr32. rewrite <- Fe.
        change (fst e) with (fst (aadd (aadd e (-4)) 3)). rewrite (MallocRep.cell_read_wr8_other _ (aadd (aadd e (-4)) 3) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd (aadd e (-4)) 3)) with (fst (aadd (aadd e (-4)) 2)). rewrite (MallocRep.cell_read_wr8_other _ (aadd (aadd e (-4)) 2) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd (aadd e (-4)) 2)) with (fst (aadd (aadd e (-4)) 1)). rewrite (MallocRep.cell_read_wr8_other _ (aadd (aadd e (-4)) 1) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd (aadd e (-4)) 1)) with (fst (aadd e (-4))). rewrite (MallocRep.cell_read_wr8_other _ (aadd e (-4)) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd e (-4))) with (fst (aadd e (-5))). rewrite (MallocRep.cell_read_wr8_other _ (aadd e (-5)) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd e (-5))) with (fst (aadd e (- rsv))). rewrite (MallocRep.cell_read_wr8_other _ (aadd e (- rsv)) _ (snd p - 3)) by (cbn; lia).
        cbn [aadd fst]. rewrite Fe. exact HK3.
      * apply PEX; assumption.
Qed.

Lemma land_low_pg x k : 0 <= x < 4096 -> 0 <= k -> Z.land x (4096 * k) = 0.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros Hx Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 12).
  - replace (4096 * k) with (k * 2^12) by lia. rewrite Z.mul_pow2_bits by lia. rewrite (Z.testbit_neg_r k (i - 12)) by lia. apply Bool.andb_false_r.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia|]. apply Z.lt_le_trans with 12; [| lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_low_pg x k : 0 <= x < 4096 -> 0 <= k -> Z.lor x (4096 * k) = x + 4096 * k.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros. rewrite <- Z.lxor_lor by (apply land_low_pg; lia). symmetry. apply Z.add_nocarry_lxor. apply land_low_pg; lia. Qed.

(* [comment removed for export] *)
Lemma rrealloc_big63_stores : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (G NB base needed n av fr w : Z) (prev next mem : word),
  let P' := NB + 16 + base in
  let E' := NB + needed - 4 in
  let w' := Z.land w 4095 + needed in
  rw_cells ssegs m G [C8 prev; C8 next; C8 mem; C4 (wz av); C4 (wz fr); C8 (wz w)] ->
  mem_inv ssegs m ->
  0 <= G -> G + 40 <= alloc_ceiling -> 0 < NB -> NB + needed <= alloc_ceiling -> 4096 <= needed < 2^48 -> needed mod 4096 = 0 ->
  0 <= base -> 0 <= n -> base + 16 + n + 4 <= needed < base + 16 + n + 4 + 4096 -> 0 <= w < 2^64 ->
  bv_unsigned s1 = G -> a2 = Z_to_bv 64 NB -> s3 = Z_to_bv 64 base -> s0 = Z_to_bv 64 needed -> s4 = Z_to_bv 64 4095 -> a1 = Z_to_bv 64 n ->
  evt ssegs (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P') (Z_to_bv 64 (n + P')) a2 (Z_to_bv 64 (E' + 4)) (Z_to_bv 64 E') (wz w')
                      (Z_to_bv 64 (E' - P' - n)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1a460) fc None m' (seg_rom ssegs)
        /\ munch [(G + 16, G + 24); (G + 32, G + 40)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
        /\ rw_cells ssegs m' G [C8 prev; C8 next; C8 (wz NB); C4 (wz av); C4 (wz fr); C8 (wz w')])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a434) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until mem. intros P' E' w' MM MI G0 GC NB0 NBC ND NAL B0 N0 FIT WR HS1 -> -> -> -> ->.
  ceil_facts.
  assert (W12 : 0 <= Z.land w 4095 < 4096).
  { split; [apply Z.land_nonneg; lia|]. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (WR' : 0 <= w' < 2^64) by (subst w'; lia).
  assert (LOR : Z.lor (Z.land w 4095) needed = w').
  { subst w'. replace needed with (4096 * (needed / 4096)) by (Z.div_mod_to_equations; lia). apply lor_low_pg; [exact W12| Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  pose proof MM as MM'. rewrite <- HS1 in MM'.
  step. step. step. step. step. step. step. step. step.
  rewrite (wz_unsigned w), (unsigned_lit (Z.land w 4095)), (unsigned_lit needed), LOR by lia.
  rewrite (unsigned_lit (NB + needed + -4)), (unsigned_lit (n + (NB + base + 16))), swrap32_small by lia.
  replace (NB + base + 16) with P' by (subst P'; lia). replace (NB + needed + -4) with E' by (subst E'; lia). replace (NB + needed) with (E' + 4) by (subst E'; lia).
  replace (E' - (n + P')) with (E' - P' - n) by lia.
  (* [comment removed for export] *)
  pose proof (munch_refl [(G + 16, G + 24); (G + 32, G + 40)]%Z m) as MU. pose proof (wmono_refl ssegs m) as WM.
  clear MM. step. step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  lazymatch goal with H : rw_cells ssegs _ (bv_unsigned s1) _ |- _ => rewrite HS1 in H; unfold wz; exact H end.
Qed.

Lemma land_pgmask x : 0 <= x < 2^64 -> Z.land x (2^64 - 4096) = x - x mod 4096.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hx.
  assert (E : Z.land x (2^64 - 4096) = Z.ldiff x (Z.ones 12)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
    change (2^64 - 4096) with (Z.ldiff (Z.ones 64) (Z.ones 12)). rewrite Z.ldiff_spec.
    destruct (Z.lt_ge_cases i 64).
    - rewrite (Z.ones_spec_low 64 i) by lia. reflexivity.
    - rewrite (Z.ones_spec_high 64 i) by lia. rewrite (Z.bits_above_log2 x i); [reflexivity| lia|].
      destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia]. }
  rewrite E, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

Lemma round_up_pg_alt y : round_up_pg y = (y + 4095) - (y + 4095) mod 4096.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition rr63A_post (ra sp gp tp t0 t1 t2 s1 a0 a2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n base needed oldlen : Z) : machine_state -> Prop :=
  fun ms' =>
    if oldlen =? needed then
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 needed) s1 a0 (Z_to_bv 64 n) a2 (Z_to_bv 64 (-4096)) (Z_to_bv 64 oldlen)
                    (Z_to_bv 64 (n + 4095 + base + 20)) a6 a7 s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1a42c) fc None m (seg_rom ssegs)
    else
      ms' = MS (mkR (Z_to_bv 64 0x1a420) sp gp tp t0 t1 t2 (Z_to_bv 64 needed) s1 a2 (Z_to_bv 64 oldlen) (Z_to_bv 64 needed) (Z_to_bv 64 1) (Z_to_bv 64 oldlen)
                    (Z_to_bv 64 (n + 4095 + base + 20)) a6 a7 s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) a0 (Z_to_bv 64 n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1a6b4) fc None m (seg_rom ssegs).

Lemma rrealloc_big63_head : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (P C0 n w last_idx freeable sc maplen : Z),
  let base := P - C0 in
  let needed := round_up_pg (n + base + 20) in
  bv_unsigned a0 = P -> t1 = Z_to_bv 64 C0 -> 0 <= C0 <= P -> P < alloc_ceiling -> 0 <= n < 2^32 ->
  w = last_idx + 32 * freeable + 64 * sc + 4096 * maplen -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  evt ssegs (rr63A_post ra sp gp tp t0 t1 t2 s1 a0 a2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n base needed (maplen * 4096))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 (wz w) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1a3dc) fc None m (seg_rom ssegs)).
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros until maplen. intros base needed HP -> C0R PC N Hw LI FR SC ML. ceil_facts.
  assert (WR : 0 <= w < 2^64) by (subst w; lia).
  assert (ND : needed = n + 4095 + base + 20 - (n + 4095 + base + 20) mod 4096) by (subst needed; rewrite round_up_pg_alt; lia).
  assert (OL : maplen * 4096 = w - w mod 4096) by (subst w; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  step. step. rewrite HP, (unsigned_lit C0) by lia. fold base.
  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4095 + base + 20)) by lia. change 18446744073709547520 with (2^64 - 4096). rewrite land_pgmask, <- ND by lia.
  step. rewrite (wz_unsigned w) by lia. change 18446744073709547520 with (2^64 - 4096). rewrite land_pgmask, <- OL by lia.
  (* [comment removed for export] *)
  assert (NDR : 0 <= needed < 2^64) by (rewrite ND; Z.div_mod_to_equations; lia).
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - unfold rr63A_post. replace (maplen * 4096 =? needed) with true by (symmetry; apply Z.eqb_eq; lia). apply evt_done. reflexivity.
  - unfold rr63A_post. replace (maplen * 4096 =? needed) with false by (symmetry; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. apply evt_done. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rimplT_mremap {R} o old on nn (k : Z -> Malloc.M R) s (P : mremap_ans -> machine_state -> Prop) Q ms :
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NMremap old on nn) (dec_mremap old on nn [] [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (mremap_val old a)) s Q ms') ->
  rimplT o (SVis (EMremap old on nn) k) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mremap_val old a /\ P a ms')); [exact Logic.I| |].
  - cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

Lemma havoc_upd_comm p n g f rid F st r :
  s_regions st !! rid = Some r ->
  havoc p n (upd_meta g f (upd_region rid F st)) = upd_meta g f (upd_region rid F (havoc p n st)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Hr. unfold upd_region, get_region. rewrite s_regions_havoc, Hr.
  unfold havoc. destruct (n <=? 0); [reflexivity|].
  unfold upd_shadow, upd_meta, put_meta, set_shadow, set_metas, set_regions, get_shadow, get_meta_rec. destruct st; cbn. reflexivity.
Qed.

Lemma ptrs_ctx_in_ext P st st' :
  ctx st' = ctx st -> s_metas st' = s_metas st -> s_areas st' = s_areas st -> s_groups st' = s_groups st ->
  ptrs_ctx_in P st -> ptrs_ctx_in P st'.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros EC EM EA EG H. unfold ptrs_ctx_in, active, get_meta_rec in *. rewrite EC, EM, EA, EG. exact H.
Qed.


End PORT.

End WithCeil.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_free_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free_spec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_reallocA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_reallocB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_reallocC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mremap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_realloc63R.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_invR.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; ceil_facts; lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

(* [comment removed for export] *)
Definition rrip_Q63 (sp : word) (lo : Z) (st' : mstate) (m0 : mem) (raS s0S s1S s2S s3S s4S s5S s6S : word) (C : Z -> Prop) (m' : mem) : Prop :=
  rmrep st' m' /\ ticks_ok st' /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
  /\ rw_cells usegs m' (bv_unsigned sp) (rrealloc_frame raS s0S s1S s2S s3S s4S s5S s6S)
  /\ rpres_except C m0 m' /\ wmono usegs m0 m'.

(* [comment removed for export] *)
Definition rrealloc_setsize63_walk__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc
    (m0 m : mem) (lo : Z) (st : mstate) (p e : aptr) (r : region) (b3 n : Z) (raS s0S s1S s2S s3S s4S s5S s6S : word) (C : Z -> Prop),
  let P := r_base r + snd p in
  let E := r_base r + snd e in
  let st' := set_size p e n b3 (wr8 e 0 st) in
  (forall a, a = P - 3 \/ P + n <= a < E + 1 -> C a) ->
  rmrep st m -> mem_inv usegs m -> ticks_ok st ->
  stk usegs m lo (bv_unsigned sp) -> rw_cells usegs m (bv_unsigned sp) (rrealloc_frame raS s0S s1S s2S s3S s4S s5S s6S) ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 64 <= 2^64 ->
  rpres_except C m0 m -> wmono usegs m0 m ->
  (s_regions st) !! (fst p) = Some r -> r_kind r = RKGroup -> fst e = fst p ->
  bv_unsigned a0 = P -> 0 <= n < 2^32 -> snd p + n <= snd e -> snd e - snd p - n < 2^31 -> 16 <= snd p ->
  snd e + 1 <= round_up_pg (r_len r) ->
  cell_read (get_shadow st (fst p)) (snd p - 3) = Known b3 ->
  (forall b gh, (s_groups st) !! b = Some gh -> fst b = fst p -> snd b + 9 <= snd p - 3 \/ snd e + 1 <= snd b) ->
  evt usegs (rrret_post sp gp tp s7 s8 s9 s10 s11 F fc raS s0S s1S s2S s3S s4S s5S s6S P (rrip_Q63 sp lo st' m0 raS s0S s1S s2S s3S s4S s5S s6S C))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (n + P)) a2 (Z_to_bv 64 (E + 4)) (Z_to_bv 64 E) a5 (Z_to_bv 64 (snd e - snd p - n)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ac20) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lo st p e r b3 n raS s0S s1S s2S s3S s4S s5S s6S C : ltac2:(SecDiet.SzSec.tyM 'rrealloc_setsize63_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_setsize63_walk__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_setsize63_walk__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
 intros P E st' HCC MR0 MI TK0 ST FR LO SLO SPH PE00 WM0 Hr0 Hk Fe HP N0 LE AV P16 EHI HK30 HCLR0.
  (* [comment removed for export] *)
  pose proof MR0 as (WF0 & _ & _ & _ & _ & SH0). pose proof WF0 as (_ & WR0 & _).
  destruct (WR0 (fst p) r Hr0) as (B00 & _ & _ & BC0 & _). ceil_facts.
  assert (ELO : E + 1 <= lo) by (subst E; lia).
  destruct (SH0 (fst p) r Hr0 Hk) as [HWr0 _]. clear SH0.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (SOK0 : store_ok usegs mX (wa (E + 4 + -4)) 1 = true)
      by (replace (E + 4 + -4) with (r_base r + snd e) by (subst E; lia); apply (wr_at_store_ok usegs mX _ _ (snd e) 1 HWr0); cbn; lia) end.
  step.
  pose proof (rmrep_wr8 st _ e 0 r MR0 TK0 ltac:(rewrite Fe; exact Hr0) Hk ltac:(lia)
                ltac:(intros b gh Hb Hfb; rewrite Fe in Hfb; destruct (HCLR0 b gh Hb Hfb); lia) ltac:(lia)) as MR.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + snd e)) [b8 0])
      by (f_equal; try reflexivity; unfold wa; f_equal; subst E; lia) end.
  pose proof (munch_refl [(E, E + 1)]%Z m) as MUe. pose proof (wmono_refl usegs m) as WMe.
  store_done.
  pose proof (ticks_ok_wr8 st e 0 TK0) as TK.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (PE0 : rpres_except C m0 mX)
      by (eapply rpres_except_trans; [exact PE00|]; apply (rpres_except_of_munch_cov _ _ _ _ MUe); [assumption| cbn [ivs_covered]; split; [intros x Hx; apply HCC; right; subst E P; lia| exact I]]) end.
  clear MUe.
  set (stw := wr8 e 0 st) in *.
  assert (Hr : s_regions stw !! fst p = Some r) by exact Hr0.
  assert (HK3 : cell_read (get_shadow stw (fst p)) (snd p - 3) = Known b3).
  { subst stw. rewrite <- Fe. rewrite (MallocRep.cell_read_wr8_other st e 0 (snd p - 3)) by lia. rewrite Fe. exact HK30. }
  assert (HCLR : forall b gh, s_groups stw !! b = Some gh -> fst b = fst p -> snd b + 9 <= snd p - 3 \/ snd e <= snd b).
  { intros b gh Hb Hfb. destruct (HCLR0 b gh Hb Hfb); lia. }
  clearbody stw. clear MR0 TK0 HK30 HCLR0 Hr0 PE00. rename stw into st0. rename st into stX. rename st0 into st.
  try clear WMe. try clear HWr0. try clear m. lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => rename mX into m end.
  pose proof MR as (WF & CX & GL & AR & GR & SH). pose proof WF as (Hres & WR & DISJ & WA & WG).
  destruct (WR (fst p) r Hr) as (B0 & BAL & L0 & BC & RFr).
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  destruct (rmrep_shadow_read st m (fst p) r (snd p - 3) b3 MR Hr Hk ltac:(lia) HK3) as [R3 B3].
  set (rsv := snd e - snd p - n) in *.
  assert (RSV : 0 <= rsv < 2^31) by (subst rsv; lia).
  unfold UNIT, IB in *; ceil_facts.
  assert (ER : 0 <= E /\ E + 1 <= 2^64) by (subst E; pose proof (round_up_pg_ge (r_len r)); lia).
  assert (PR : 16 <= P /\ P + n <= E) by (subst P E; lia).
  assert (ERSV : E - (n + P) = rsv) by (subst E P rsv; lia).
  fold rsv.
  (* [comment removed for export] *)
  assert (TAIL : forall (a1v a2v a4v a6v : word) (c : Z) (st2 : mstate) (m2 : mem),
    bv_unsigned a1v = c -> 0 <= c < 8 ->
    st' = wr8 (aadd p (-3)) (Z.land b3 31 + Z.shiftl c 5) st2 ->
    rmrep st2 m2 -> ticks_ok st2 -> mem_inv usegs m2 -> s_regions st2 = s_regions st -> s_groups st2 = s_groups st ->
    cell_read (get_shadow st2 (fst p)) (snd p - 3) = Known b3 ->
    stk usegs m2 lo (bv_unsigned sp) -> rw_cells usegs m2 (bv_unsigned sp) (rrealloc_frame raS s0S s1S s2S s3S s4S s5S s6S) ->
    rpres_except C m0 m2 -> wmono usegs m0 m2 ->
    evt usegs (rrret_post sp gp tp s7 s8 s9 s10 s11 F fc raS s0S s1S s2S s3S s4S s5S s6S P (rrip_Q63 sp lo st' m0 raS s0S s1S s2S s3S s4S s5S s6S C))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1v a2v (Z_to_bv 64 (E + 4)) a4v a5 a6v a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ad00) fc None m2 (seg_rom usegs))).
  { intros a1v a2v a4v a6v c st2 m2 HC CR Est' MR2 TK2 MI2 RG2 GR2 HK3' ST2 FR2 PE2 WM2.
    destruct (rmrep_shadow_read st2 m2 (fst p) r (snd p - 3) b3 MR2 ltac:(rewrite RG2; exact Hr) Hk ltac:(lia) HK3') as [R3' _].
    replace (r_base r + (snd p - 3)) with (bv_unsigned a0 + -3) in R3' by lia.
    (* [comment removed for export] *)
    step. step. step. step.
    rewrite HC, ?(wz_unsigned b3), ?zxb_b8, ?(wz_unsigned b3) by lia.
    rewrite Z.shiftl_mul_pow2, ?(unsigned_lit (c * 2 ^ 5)) by lia. change (2 ^ 5) with 32.
    assert (L31 : 0 <= Z.land b3 31 < 32). { split; [apply Z.land_nonneg; lia|]. change 31 with (Z.ones 5). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
    rewrite ?(unsigned_lit (Z.land b3 31)) by lia. rewrite lor_shl5_land31 by lia.
    set (V := Z.land b3 31 + Z.shiftl c 5) in *.
    assert (VR : 0 <= V < 256) by (subst V; rewrite Z.shiftl_mul_pow2 by lia; change (2^5) with 32; lia).
    (* [comment removed for export] *)
    pose proof MR2 as (_ & _ & _ & _ & _ & SH2). destruct (SH2 (fst p) r ltac:(rewrite RG2; exact Hr) Hk) as [HWr2 _]. clear SH2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (SOK : store_ok usegs mX (wa (bv_unsigned a0 + -3)) 1 = true)
        by (replace (bv_unsigned a0 + -3) with (r_base r + (snd p - 3)) by lia; apply (wr_at_store_ok usegs mX _ _ (snd p - 3) 1 HWr2); cbn; lia) end.
    step.
    pose proof (rmrep_wr8 st2 _ (aadd p (-3)) V r MR2 TK2 ltac:(rewrite RG2; exact Hr) Hk ltac:(cbn; lia)
                  ltac:(intros b gh Hb Hfb; cbn [aadd fst snd] in Hfb |- *; rewrite GR2 in Hb; destruct (HCLR b gh Hb Hfb); lia) ltac:(lia)) as MR3.
    cbn [aadd snd] in MR3. rewrite <- Est' in MR3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
      replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (snd p + -3))) [b8 V])
        by (f_equal; [unfold wa; f_equal; lia| cbn; rewrite ?(unsigned_lit V) by lia; reflexivity]) end.
    pose proof (munch_refl [(P - 3, P - 2)]%Z m2) as MU3. pose proof (wmono_refl usegs m2) as WMr.
    store_done.
    pose proof (ticks_ok_wr8 st2 (aadd p (-3)) V TK2) as TK3. rewrite <- Est' in TK3.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (PE3 : rpres_except C m0 mX)
        by (eapply rpres_except_trans; [exact PE2|]; apply (rpres_except_of_munch_cov _ _ _ _ MU3); [exact WMr| cbn [ivs_covered]; split; [intros x Hx; apply HCC; left; lia| exact I]]) end.
    replace a0 with (Z_to_bv 64 P) by (rewrite <- HP; apply (Z_to_bv_bv_unsigned a0)).
    eapply rrealloc_epilogue; [eassumption| eassumption| exact SPH| assumption|].
    unfold rrip_Q63. split; [exact MR3|]. split; [exact TK3|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [exact PE3| assumption]. }
  (* [comment removed for export] *)
  pose proof (set_size_cases p e n b3 st) as SS. cbv zeta in SS. fold rsv in SS. fold st' in SS.
  step. if_cases K0; zify_cond K0; rewrite ?(unsigned_lit rsv) in K0 by lia.
  - (* [comment removed for export] *)
    rewrite K0 in SS. cbn [Z.eqb] in SS.
    step. step.
    eapply (TAIL _ _ _ _ 0 st m); try eassumption; try reflexivity; try lia. all: try (rewrite unsigned_lit by lia; reflexivity).
  - replace (rsv =? 0) with false in SS by (symmetry; apply Z.eqb_neq; exact K0).
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit E), (unsigned_lit (n + P)), ERSV, swrap32_small by lia.
    step. rewrite ?(unsigned_lit rsv), swrap32_small by lia.
    step. replace (E + (0 - rsv)) with (r_base r + (snd e + - rsv)) by (subst E; lia).
    step.
    (* [comment removed for export] *)
    pose proof MR as (_ & _ & _ & _ & _ & SH1). destruct (SH1 (fst p) r Hr Hk) as [HWr _]. clear SH1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (SOK1 : store_ok usegs mX (wa (r_base r + (snd e + - rsv) + 0)) 1 = true)
        by (replace (r_base r + (snd e + - rsv) + 0) with (r_base r + (snd e - rsv)) by lia; apply (wr_at_store_ok usegs mX _ _ (snd e - rsv) 1 HWr); cbn; lia) end.
    step.
    pose proof (rmrep_wr8 st _ (aadd e (- rsv)) 0 r MR TK ltac:(cbn [aadd fst snd]; rewrite Fe; exact Hr) Hk ltac:(cbn; lia)
                  ltac:(intros b gh Hb Hfb; cbn [aadd fst snd] in Hfb |- *; rewrite Fe in Hfb; destruct (HCLR b gh Hb Hfb); lia) ltac:(lia)) as MR1.
    cbn [aadd snd] in MR1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
      replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (snd e + - rsv))) [b8 0])
        by (f_equal; try reflexivity; unfold wa; f_equal; lia) end.
    pose proof (munch_refl [(E - rsv, E)]%Z m) as MU. pose proof (wmono_refl usegs m) as WMa.
    store_done.
    pose proof (ticks_ok_wr8 st (aadd e (- rsv)) 0 TK) as TK1.
    set (st1 := wr8 (aadd e (- rsv)) 0 st) in *.
    assert (PEX : forall mX, munch [(E - rsv, E)]%Z m mX -> wmono usegs m mX -> rpres_except C m0 mX).
    { intros mX MUX WMX. eapply rpres_except_trans; [exact PE0|]. apply (rpres_except_of_munch_cov _ _ _ _ MUX); [exact WMX|].
      cbn [ivs_covered]. split; [intros x Hx; apply HCC; right; subst E P rsv; lia| exact I]. }
    assert (RG1 : s_regions st1 = s_regions st) by reflexivity.
    assert (GR1 : s_groups st1 = s_groups st) by reflexivity.
    assert (HK3a : cell_read (get_shadow st1 (fst p)) (snd p - 3) = Known b3).
    { subst st1. rewrite <- Fe. change (fst e) with (fst (aadd e (- rsv))). rewrite (MallocRep.cell_read_wr8_other st (aadd e (- rsv)) 0 (snd p - 3)) by (cbn; lia).
      cbn [aadd fst]. rewrite Fe. exact HK3. }
    (* [comment removed for export] *)
    step. if_cases K5; zify_cond K5; rewrite ?signed_of_Z in K5 by lia.
    + (* [comment removed for export] *)
      replace (5 <=? rsv) with false in SS by (symmetry; apply Z.leb_gt; lia).
      step.
      eapply (TAIL _ _ _ _ rsv st1); try eassumption; try lia; [rewrite unsigned_lit by lia; reflexivity| apply PEX; assumption].
    + (* [comment removed for export] *)
      replace (5 <=? rsv) with true in SS by (symmetry; apply Z.leb_le; lia).
      rewrite (wr8_wr32_comm st1 (aadd e (-5)) (aadd e (-4)) 0 rsv) in SS by (cbn; lia).
      (* [comment removed for export] *)
      pose proof MR1 as (_ & _ & _ & _ & _ & SHb). destruct (SHb (fst p) r Hr Hk) as [HWrb _]. clear SHb.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (SOK2 : store_ok usegs mX (wa (E + 4 + -9)) 1 = true)
          by (replace (E + 4 + -9) with (r_base r + (snd e - 5)) by (subst E; lia); apply (wr_at_store_ok usegs mX _ _ (snd e - 5) 1 HWrb); cbn; lia) end.
      step.
      pose proof (rmrep_wr8 st1 _ (aadd e (-5)) 0 r MR1 TK1 ltac:(cbn [aadd fst snd]; rewrite Fe; exact Hr) Hk ltac:(cbn; lia)
                    ltac:(intros b gh Hb Hfb; cbn [aadd fst snd] in Hfb |- *; rewrite Fe in Hfb; destruct (HCLR b gh Hb Hfb); lia) ltac:(lia)) as MR2.
      cbn [aadd snd] in MR2.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
        replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (snd e + -5))) [b8 0])
          by (f_equal; try reflexivity; unfold wa; f_equal; subst E; lia) end.
      store_done.
      pose proof (ticks_ok_wr8 st1 (aadd e (-5)) 0 TK1) as TK2.
      set (st2 := wr8 (aadd e (-5)) 0 st1) in *.
      (* [comment removed for export] *)
      pose proof MR2 as (_ & _ & _ & _ & _ & SHc). destruct (SHc (fst p) r Hr Hk) as [HWrc _]. clear SHc.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
        assert (SOK3 : store_ok usegs mX (wa (E + 4 + -8)) 4 = true)
          by (replace (E + 4 + -8) with (r_base r + (snd e - 4)) by (subst E; lia); apply (wr_at_store_ok usegs mX _ _ (snd e - 4) 4 HWrc); cbn; lia) end.
      step.
      destruct (rmrep_wr32 st2 _ (aadd e (-4)) rsv r MR2 TK2 ltac:(cbn [aadd fst snd]; rewrite Fe; exact Hr) Hk ltac:(cbn; lia) ltac:(cbn; lia)
                    ltac:(intros b gh Hb Hfb; cbn [aadd fst snd] in Hfb |- *; rewrite Fe in Hfb; destruct (HCLR b gh Hb Hfb); lia) ltac:(lia)) as [MR3 TK3].
      cbn [aadd snd] in MR3.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
        replace (write_to_mem mX a bs) with (write_to_mem mX (wa (r_base r + (snd e + -4))) (le4 (wz rsv)))
          by (f_equal; try reflexivity; unfold wa; f_equal; subst E; lia) end.
      store_done.
      (* [comment removed for export] *)
      step.
      eapply (TAIL _ _ _ _ 5 (wr32 (aadd e (-4)) rsv st2)); try eassumption; try lia.
      * rewrite unsigned_lit by lia. reflexivity.
      * subst st2 st1. unfold wr32. rewrite <- Fe.
        change (fst e) with (fst (aadd (aadd e (-4)) 3)). rewrite (MallocRep.cell_read_wr8_other _ (aadd (aadd e (-4)) 3) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd (aadd e (-4)) 3)) with (fst (aadd (aadd e (-4)) 2)). rewrite (MallocRep.cell_read_wr8_other _ (aadd (aadd e (-4)) 2) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd (aadd e (-4)) 2)) with (fst (aadd (aadd e (-4)) 1)). rewrite (MallocRep.cell_read_wr8_other _ (aadd (aadd e (-4)) 1) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd (aadd e (-4)) 1)) with (fst (aadd e (-4))). rewrite (MallocRep.cell_read_wr8_other _ (aadd e (-4)) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd e (-4))) with (fst (aadd e (-5))). rewrite (MallocRep.cell_read_wr8_other _ (aadd e (-5)) _ (snd p - 3)) by (cbn; lia).
        change (fst (aadd e (-5))) with (fst (aadd e (- rsv))). rewrite (MallocRep.cell_read_wr8_other _ (aadd e (- rsv)) _ (snd p - 3)) by (cbn; lia).
        cbn [aadd fst]. rewrite Fe. exact HK3.
      * apply PEX; assumption.
Qed.
End Sz1.
Lemma rrealloc_setsize63_walk : ltac:(let t := eval cbv delta [rrealloc_setsize63_walk__stmt] in rrealloc_setsize63_walk__stmt in exact t).
Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a5 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0 m lo st p e r b3 n raS s0S s1S s2S s3S s4S s5S s6S C. ltac2:(SecDiet.SzSec.closeP 'rrealloc_setsize63_walk__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Lemma land_low_pg x k : 0 <= x < 4096 -> 0 <= k -> Z.land x (4096 * k) = 0.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts.
  intros Hx Hk. apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
  destruct (Z.lt_ge_cases i 12).
  - replace (4096 * k) with (k * 2^12) by lia. rewrite Z.mul_pow2_bits by lia. rewrite (Z.testbit_neg_r k (i - 12)) by lia. apply Bool.andb_false_r.
  - destruct (Z.eq_dec x 0) as [->|NZ]; [rewrite Z.bits_0; reflexivity|].
    rewrite (Z.bits_above_log2 x i); [reflexivity| lia|]. apply Z.lt_le_trans with 12; [| lia]. apply Z.log2_lt_pow2; lia.
Qed.
Lemma lor_low_pg x k : 0 <= x < 4096 -> 0 <= k -> Z.lor x (4096 * k) = x + 4096 * k.
Proof using MSECV TB. pin_using (fun (MSECV TB : unit) => tt). ceil_facts. msec_facts. intros. rewrite <- Z.lxor_lor by (apply land_low_pg; lia). symmetry. apply Z.add_nocarry_lxor. apply land_low_pg; lia. Qed.

(* [comment removed for export] *)
Definition rrealloc_big63_stores__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (G NB base needed n av fr w : Z) (prev next mem : word),
  let P' := NB + 16 + base in
  let E' := NB + needed - 4 in
  let w' := Z.land w 4095 + needed in
  rw_cells usegs m G [C8 prev; C8 next; C8 mem; C4 (wz av); C4 (wz fr); C8 (wz w)] ->
  mem_inv usegs m ->
  0 <= G -> G + 40 <= alloc_ceiling -> 0 < NB -> NB + needed <= alloc_ceiling -> 4096 <= needed < 2^48 -> needed mod 4096 = 0 ->
  0 <= base -> 0 <= n -> base + 16 + n + 4 <= needed < base + 16 + n + 4 + 4096 -> 0 <= w < 2^64 ->
  bv_unsigned s1 = G -> a2 = Z_to_bv 64 NB -> s3 = Z_to_bv 64 base -> s0 = Z_to_bv 64 needed -> s4 = Z_to_bv 64 4095 -> a1 = Z_to_bv 64 n ->
  evt usegs (fun ms' => exists m',
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P') (Z_to_bv 64 (n + P')) a2 (Z_to_bv 64 (E' + 4)) (Z_to_bv 64 E') (wz w')
                      (Z_to_bv 64 (E' - P' - n)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1ac20) fc None m' (seg_rom usegs)
        /\ munch [(G + 16, G + 24); (G + 32, G + 40)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
        /\ rw_cells usegs m' G [C8 prev; C8 next; C8 (wz NB); C4 (wz av); C4 (wz fr); C8 (wz w')])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1abf4) fc None m (seg_rom usegs)).
Section Sz2.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m G NB base needed n av fr w prev next mem : ltac2:(SecDiet.SzSec.tyM 'rrealloc_big63_stores__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_big63_stores__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_big63_stores__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros P' E' w' MM MI G0 GC NB0 NBC ND NAL B0 N0 FIT WR HS1 -> -> -> -> ->.
  ceil_facts.
  assert (W12 : 0 <= Z.land w 4095 < 4096).
  { split; [apply Z.land_nonneg; lia|]. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  assert (WR' : 0 <= w' < 2^64) by (subst w'; lia).
  assert (LOR : Z.lor (Z.land w 4095) needed = w').
  { subst w'. replace needed with (4096 * (needed / 4096)) by (Z.div_mod_to_equations; lia). apply lor_low_pg; [exact W12| Z.div_mod_to_equations; lia]. }
  (* [comment removed for export] *)
  pose proof MM as MM'. rewrite <- HS1 in MM'.
  step. step. step. step. step. step. step. step. step.
  rewrite (wz_unsigned w), (unsigned_lit (Z.land w 4095)), (unsigned_lit needed), LOR by lia.
  rewrite (unsigned_lit (NB + needed + -4)), (unsigned_lit (n + (NB + base + 16))), swrap32_small by lia.
  replace (NB + base + 16) with P' by (subst P'; lia). replace (NB + needed + -4) with E' by (subst E'; lia). replace (NB + needed) with (E' + 4) by (subst E'; lia).
  replace (E' - (n + P')) with (E' - P' - n) by lia.
  (* [comment removed for export] *)
  pose proof (munch_refl [(G + 16, G + 24); (G + 32, G + 40)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  clear MM. step. step.
  apply evt_done. eexists. split; [reflexivity|].
  split; [eassumption|]. split; [eassumption|]. split; [eassumption|].
  lazymatch goal with H : rw_cells usegs _ (bv_unsigned s1) _ |- _ => rewrite HS1 in H; unfold wz; exact H end.
Qed.
End Sz2.
Lemma rrealloc_big63_stores : ltac:(let t := eval cbv delta [rrealloc_big63_stores__stmt] in rrealloc_big63_stores__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m G NB base needed n av fr w prev next mem. ltac2:(SecDiet.SzSec.closeP 'rrealloc_big63_stores__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Lemma land_pgmask x : 0 <= x < 2^64 -> Z.land x (2^64 - 4096) = x - x mod 4096.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  intros Hx.
  assert (E : Z.land x (2^64 - 4096) = Z.ldiff x (Z.ones 12)).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.ldiff_spec.
    change (2^64 - 4096) with (Z.ldiff (Z.ones 64) (Z.ones 12)). rewrite Z.ldiff_spec.
    destruct (Z.lt_ge_cases i 64).
    - rewrite (Z.ones_spec_low 64 i) by lia. reflexivity.
    - rewrite (Z.ones_spec_high 64 i) by lia. rewrite (Z.bits_above_log2 x i); [reflexivity| lia|].
      destruct (Z.eq_dec x 0) as [->|]; [cbn; lia|]. apply Z.lt_le_trans with 64; [apply Z.log2_lt_pow2; lia| lia]. }
  rewrite E, Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia. change (2^12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

Lemma round_up_pg_alt y : round_up_pg y = (y + 4095) - (y + 4095) mod 4096.
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
  unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Definition rr63A_post (ra sp gp tp t0 t1 t2 s1 a0 a2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (P n base needed oldlen : Z) : machine_state -> Prop :=
  fun ms' =>
    if oldlen =? needed then
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 needed) s1 a0 (Z_to_bv 64 n) a2 (Z_to_bv 64 (-4096)) (Z_to_bv 64 oldlen)
                    (Z_to_bv 64 (n + 4095 + base + 20)) a6 a7 s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1abec) fc None m (seg_rom usegs)
    else
      ms' = MS (mkR (Z_to_bv 64 0x1abe0) sp gp tp t0 t1 t2 (Z_to_bv 64 needed) s1 a2 (Z_to_bv 64 oldlen) (Z_to_bv 64 needed) (Z_to_bv 64 1) (Z_to_bv 64 oldlen)
                    (Z_to_bv 64 (n + 4095 + base + 20)) a6 a7 s2 (Z_to_bv 64 base) (Z_to_bv 64 4095) a0 (Z_to_bv 64 n) s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 0x1ae74) fc None m (seg_rom usegs).

Definition rrealloc_big63_head__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (m : mem)
    (P C0 n w last_idx freeable sc maplen : Z),
  let base := P - C0 in
  let needed := round_up_pg (n + base + 20) in
  bv_unsigned a0 = P -> t1 = Z_to_bv 64 C0 -> 0 <= C0 <= P -> P < alloc_ceiling -> 0 <= n < 2^32 ->
  w = last_idx + 32 * freeable + 64 * sc + 4096 * maplen -> 0 <= last_idx < 32 -> 0 <= freeable < 2 -> 0 <= sc < 64 -> 0 <= maplen < 2^40 ->
  evt usegs (rr63A_post ra sp gp tp t0 t1 t2 s1 a0 a2 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P n base needed (maplen * 4096))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 (wz w) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ab9c) fc None m (seg_rom usegs)).
Section Sz3.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P C0 n w last_idx freeable sc maplen : ltac2:(SecDiet.SzSec.tyM 'rrealloc_big63_head__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rrealloc_big63_head__body : ltac2:(SecDiet.SzSec.bodyP 'rrealloc_big63_head__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using MSECV TLSFACTS. pin_using (fun (MSECV TLSFACTS : unit) => tt). ceil_facts. msec_facts.
 intros base needed HP -> C0R PC N Hw LI FR SC ML. ceil_facts.
  assert (WR : 0 <= w < 2^64) by (subst w; lia).
  assert (ND : needed = n + 4095 + base + 20 - (n + 4095 + base + 20) mod 4096) by (subst needed; rewrite round_up_pg_alt; lia).
  assert (OL : maplen * 4096 = w - w mod 4096) by (subst w; Z.div_mod_to_equations; lia).
  (* [comment removed for export] *)
  step. step. rewrite HP, (unsigned_lit C0) by lia. fold base.
  step. step. step. step. step. step.
  rewrite (unsigned_lit (n + 4095 + base + 20)) by lia. change 18446744073709547520 with (2^64 - 4096). rewrite land_pgmask, <- ND by lia.
  step. rewrite (wz_unsigned w) by lia. change 18446744073709547520 with (2^64 - 4096). rewrite land_pgmask, <- OL by lia.
  (* [comment removed for export] *)
  assert (NDR : 0 <= needed < 2^64) by (rewrite ND; Z.div_mod_to_equations; lia).
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - unfold rr63A_post. replace (maplen * 4096 =? needed) with true by (symmetry; apply Z.eqb_eq; lia). apply evt_done. reflexivity.
  - unfold rr63A_post. replace (maplen * 4096 =? needed) with false by (symmetry; apply Z.eqb_neq; lia).
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. apply evt_done. reflexivity.
Qed.
End Sz3.
Lemma rrealloc_big63_head : ltac:(let t := eval cbv delta [rrealloc_big63_head__stmt] in rrealloc_big63_head__stmt in exact t).
Proof using MSECV TLSFACTS. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P C0 n w last_idx freeable sc maplen. ltac2:(SecDiet.SzSec.closeP 'rrealloc_big63_head__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rimplT_mremap {R} o old on nn (k : Z -> Malloc.M R) s (P : mremap_ans -> machine_state -> Prop) Q ms :
  impl usegs (at_node usegs) (npeek usegs) (enode (NMremap old on nn) (dec_mremap old on nn [] [])) (epost P) ms ->
  (forall a ms', P a ms' -> rimplT o (k (mremap_val old a)) s Q ms') ->
  rimplT o (SVis (EMremap old on nn) k) s Q ms.
Proof using MSECV. pin_using (fun (MSECV : unit) => tt). ceil_facts. msec_facts.
  intros H K. eapply (rimplT_vis o _ k s (fun z s' ms' => s' = s /\ exists a, z = mremap_val old a /\ P a ms')); [exact Logic.I| |].
  - cbn [ev_step]. eapply rimplM_msys_ret; [exact H|]. intros a ms' HP. apply evt_done. split; [reflexivity|]. exists a; auto.
  - intros z s' ms' (-> & a & -> & HP). exact (K a ms' HP).
Qed.

Lemma havoc_upd_comm p n g f rid F st r :
  s_regions st !! rid = Some r ->
  havoc p n (upd_meta g f (upd_region rid F st)) = upd_meta g f (upd_region rid F (havoc p n st)).
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros Hr. unfold upd_region, get_region. rewrite s_regions_havoc, Hr.
  unfold havoc. destruct (n <=? 0); [reflexivity|].
  unfold upd_shadow, upd_meta, put_meta, set_shadow, set_metas, set_regions, get_shadow, get_meta_rec. destruct st; cbn. reflexivity.
Qed.

Lemma ptrs_ctx_in_ext P st st' :
  ctx st' = ctx st -> s_metas st' = s_metas st -> s_areas st' = s_areas st -> s_groups st' = s_groups st ->
  ptrs_ctx_in P st -> ptrs_ctx_in P st'.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts.
  intros EC EM EA EG H. unfold ptrs_ctx_in, active, get_meta_rec in *. rewrite EC, EM, EA, EG. exact H.
Qed.


End PORT.

End WithCeil.
End TwB.
End RF_realloc63.

(* [comment removed for export] *)
Module RF_realloc63T.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Image ZBridge SysStep Arr ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import SFModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_malloc_free__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_A__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocKit_A2__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocHINV. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_P__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_free_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocKit_A. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_free_K__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_mm_syscalls__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_reallocA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free_spec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_reallocA OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_reallocB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_reallocC OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mremap OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_realloc63R OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc63 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_realloc63M.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require STree Malloc. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KInv__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MallocCtrl Monad. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Inv. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Fuel__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Ledger__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require KStep__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require MI_Realloc2__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_invR.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_inv__MA.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; ceil_facts; lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma pw_conc_ext (st st' : mstate) p : (forall q, conc st' q = conc st q) -> pw st' p = pw st p.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros H. destruct p as [q|]; unfold pw, oconc; [rewrite H|]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rbig63_proof__stmt : Prop := rbig63_stmt.
Section Sz1.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s LB blk off bs n lo B g b ai r i v3 rsv t2 a0 a5 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'rbig63_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rbig63_proof__body : ltac2:(SecDiet.SzSec.bodyP 'rbig63_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st0 st mr c0 pf e P E AR Hin Hoff HA BL SL Hgh FB Hr Kr SC63 LI0 ML0 I V31 C3 V3R OS SZ N RSVE RSV0 SB LO SLO TP A0 MU1 WM1 (MI1 & ST1 & MR1 & AUX1 & REPL1 & CH1 & HP1 & [errv1 ERR1] & FR1) FBOK.
  unfold RREALLOC_STACK in SLO. unfold MMAP_THRESHOLD in N.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as LOv. ceil_facts. pose proof the_tb_facts as TBF.
  assert (I0 : i = 0) by lia. assert (V0 : Z.land v3 31 = 0) by lia.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (ci_gmetas _ _ C b g ltac:(exists ai; exact Hgh)) as GO.
  destruct (go_region _ _ _ GO) as (r_ & Hr_ & _ & B0 & _ & SPAN & TOP). rewrite Hr in Hr_. assert (r_ = r) as -> by congruence.
  destruct (TOP ltac:(change (get_meta_rec st0 g) with mr; lia)) as [Sb OLDLEN]. change (get_meta_rec st0 g) with mr in OLDLEN, SPAN.
  pose proof (go_mem _ _ _ GO) as Hmem. change (get_meta_rec st0 g) with mr in Hmem.
  pose proof (go_slot _ _ _ GO) as MSg. pose proof (go_maplen _ _ _ GO) as MLR. change (get_meta_rec st0 g) with mr in MLR.
  pose proof (go_freeable _ _ _ GO) as FRB. change (get_meta_rec st0 g) with mr in FRB.
  pose proof (go_avail _ _ _ GO) as AVR. pose proof (go_freed _ _ _ GO) as FDR. change (get_meta_rec st0 g) with mr in AVR, FDR.
  assert (STR : get_stride mr = m_maplen mr * 4096 - 16).
  { unfold get_stride. rewrite LI0. replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  pose proof MR1 as (WF & CX & GL & ARR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  set (old := r_base r) in *. set (on := round_up_pg (r_len r)) in *.
  assert (EP : P = old + snd pf) by reflexivity. assert (EE : E = old + snd e) by reflexivity.
  assert (EOLD : old = r_base r) by reflexivity. assert (EON : on = round_up_pg (r_len r)) by reflexivity.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (subst pf c0; cbn; symmetry; exact FB).
  assert (Sc : snd c0 = 16).
  { destruct (ki_slts _ _ _ (KINV_of_CINV _ _ C) _ _ _ SL) as (_ & Ec & _). fold c0 in Ec. rewrite Ec, (slot_start'_mem _ b i Hmem). cbn. rewrite Sb, I0. unfold UNIT. lia. }
  assert (Sp : snd pf = 16 + 16 * off) by (subst pf; cbn; rewrite Sc; unfold UNIT; lia).
  assert (Se : snd e = on - 4) by (subst e; cbn [aadd snd]; rewrite V0, STR, Sb, OLDLEN; unfold UNIT, IB; lia).
  assert (Cc : conc st0 c0 = old + 16) by (rewrite (conc_region' st0 c0 r) by (rewrite <- FB; exact Hr); rewrite Sc; reflexivity).
  assert (HAp : blk_addr blk = old + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Cb : conc st0 b = old) by (rewrite (conc_region' st0 b r Hr), Sb; subst old; lia).
  assert (ON4096 : 4096 <= on) by (subst on; rewrite <- OLDLEN; lia).
  pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as DRr. pose proof (rreserved_tlsU _ _ RF) as TLSr.
  (* [comment removed for export] *)
  apply rimplT_guard; intros _.
  cbv zeta. cbn [aadd fst snd]. rewrite V0, Z.mul_0_r, Z.add_0_r.
  set (needed := round_up_pg (n + (snd pf - (snd b + UNIT)) + UNIT + IB)).
  assert (END : needed = round_up_pg (n + (P - (old + 16)) + 20)) by (subst needed P; rewrite Sb; unfold UNIT, IB; f_equal; lia).
  pose proof (round_up_pg_alt (n + (P - (old + 16)) + 20)) as NDv. rewrite <- END in NDv.
  assert (NDR : n + (P - (old + 16)) + 20 <= needed < n + (P - (old + 16)) + 20 + 4096) by (rewrite NDv; Z.div_mod_to_equations; (keep_hyps CEILV TB n b r r0 H0; lia)).
  assert (NDAL : needed mod 4096 = 0) by (rewrite NDv; Z.div_mod_to_equations; (keep_hyps CEILV TB n b r r1 q r0 q0 H H0 H4; lia)).
  assert (ND4 : 4096 <= needed) by (first [clear -NDR N EP Sp Hoff CEILF__ CEILM__ CEILP__ | clear -NDR N EP Sp Hoff]; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CB0 : conc st (fst b, 0) = old) by (rewrite (conc_region' _ (fst b, 0) r) by (cbn [fst]; exact Hr); cbn [snd]; subst old; lia).
  rewrite CB0.
  pose proof (rmeta_slot_bounds st0 m1 g MR1 MSg) as (G0 & GC & GIMG & _ & _).
  set (G := conc st0 g) in *.
  pose proof (rmrep_meta_chunk st0 m1 g MR1 MSg) as MM1. fold G mr in MM1. unfold meta_cells in MM1. rewrite Hmem in MM1.
  change (pw st0 (Some b)) with (wz (conc st0 b)) in MM1.
  pose proof (go_li _ _ _ GO) as GLI. pose proof (go_sc _ _ _ GO) as GSC. change (get_meta_rec st0 g) with mr in GLI, GSC.
  assert (WRD : 0 <= meta_word mr < 2^64) by (unfold meta_word; lia).
  assert (WLO : Z.land (meta_word mr) 4095 = m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. unfold meta_word. rewrite SC63, LI0, FRB. Z.div_mod_to_equations. (keep_hyps CEILV TB n g b r q r0 H H0; lia). }
  pose proof (ci_ticks _ _ C) as TK0. assert (TKt : ticks_ok st) by (apply ticks_ok_set_tick; [cbn; lia| exact TK0]).
  assert (MRt : rmrep st m1) by (apply rmrep_set_tick; exact MR1).
  (* [comment removed for export] *)
  assert (GPR : s_metas st0 !! g = Some mr).
  { destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _). pose proof INV as (_ & _ & _ & _ & IG & _ & _).
    pose proof (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG g b ai Hgh)) as GP. subst mr. unfold get_meta_rec.
    destruct (s_metas st0 !! g) as [mr0|]; [reflexivity| exfalso; apply GP; reflexivity]. }
  (* [comment removed for export] *)
  destruct (areach_blk_slot_clear st0 LB blk AR Hin) as (gm & bm & im & rm & offm & HOm & HIm & ESL & SLm & Hrm & Krm & EAm & OFm & SZm & FITm & GCLR & BCLR).
  fold c0 in ESL, SLm. rewrite SL in SLm. assert (gm = g /\ im = i) as [-> ->] by (split; congruence). clear SLm.
  assert (Ebm : fst bm = fst b) by (rewrite FB, ESL; reflexivity).
  rewrite Ebm, Hr in Hrm. assert (rm = r) as -> by congruence.
  assert (SS0 : sstart (MI_Inv.MR st0 g) i = snd c0) by (rewrite ESL; reflexivity). change (MI_Inv.MR st0 g) with mr in SS0, GCLR, BCLR.
  assert (ONLYG : forall b' gh, s_groups st0 !! b' = Some gh -> fst b' = fst b -> b' = b).
  { intros b' gh Hb' Hf'. pose proof (GCLR b' gh Hb' ltac:(rewrite Ebm; exact Hf')) as X. rewrite SS0, Sc, STR, OLDLEN in X.
    destruct (WG b' gh Hb') as (rb & Hrb & _ & B0' & B16' & _). rewrite Hf', Hr in Hrb. assert (rb = r) as -> by congruence. fold on in B16'.
    destruct b' as [b'1 b'2]. destruct b as [b1 b2]. cbn [fst snd] in *. subst b'1. f_equal. unfold UNIT in X. (keep_hyps CEILV TB off n g r b1 b2 bm b'2 Sb X B0' B16'; lia). }
  pose proof (rmem_only st0 LB (fst b) b g ai C Hgh ONLYG) as MEMG.
  pose proof (rptrs_ctx_norid st0 LB 0 (fst b) r m1 (KINV_of_CINV _ _ C) MR1 Hr Kr (ci_mp _ _ C)) as PTX0.
  (* [comment removed for export] *)
  pose proof MSg as (ag & arg & kg & Hag & Hkg & Eg).
  destruct (rarea_conc st0 ag arg WF Hag) as (rag & Hrag & Cag & Sag0 & Sag1 & SagL & NKg & RBg0 & RBgA & RBgC).
  destruct (WR _ _ Hrag) as (_ & _ & _ & _ & RFg). pose proof (rreserved_tlsU _ _ RFg) as GTLS. pose proof (round_up_pg_ge (r_len rag)) as RUg.
  assert (EG : G = conc st0 ag + AREA_HDR + META_SIZE * kg) by (subst G; rewrite Eg, conc_aadd by (rewrite Hrag; eauto); lia).
  (* [comment removed for export] *)
  assert (LBS : length bs = Z.to_nat (blk_size blk)) by (destruct CH1 as [[Hwf _] _]; cbn in Hwf; exact (proj1 Hwf)).
  pose proof (rw_cells_bytes_at _ _ _ _ CH1) as BS1. cbn [cells_bytes cbytes] in BS1. rewrite app_nil_r in BS1.
  set (k1 := Z.to_nat (Z.min (blk_size blk) n)).
  assert (K1R : Z.of_nat k1 <= n /\ Z.of_nat k1 <= blk_size blk /\ (k1 <= Z.to_nat n)%nat) by (subst k1; first [clear -N SZ CEILF__ CEILM__ CEILP__ | clear -N SZ]; lia).
  assert (LK1 : length (firstn k1 bs) = k1) by (rewrite length_firstn, LBS; subst k1; first [clear -N SZ CEILF__ CEILM__ CEILP__ | clear -N SZ]; lia).
  assert (EK1 : k1 = Z.to_nat (Z.min (blk_size blk) n)) by reflexivity. clearbody k1.
  (* [comment removed for export] *)
  set (FP := fun nb a => lo <= a < bv_unsigned sp \/ old <= a < old + on \/ nb <= a < nb + needed \/ G + 16 <= a < G + 40).
  assert (FINAL : forall (nb : Z) (stF : mstate) (rF : region) (m' : mem) (x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
    rmrep stF m' -> mem_inv ssegs m' -> stk ssegs m' lo (bv_unsigned sp + -64) ->
    rw_cells ssegs m' (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6) ->
    s_regions stF !! (fst b) = Some rF -> r_base rF = nb -> r_kind rF = RKGroup -> needed <= round_up_pg (r_len rF) ->
    ctx stF = ctx st0 -> (forall q, fst q <> fst b -> conc stF q = conc st0 q) ->
    rpres_except (FP nb) m1 m' ->
    bytes_at ssegs m' (nb + snd pf) (firstn k1 bs) ->
    0 < nb -> nb mod 4096 = 0 -> nb + needed <= alloc_ceiling -> ranges_free ref_reserved nb needed = true ->
    (forall rid' r', s_regions st0 !! rid' = Some r' -> rid' <> fst b -> nb + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb) ->
    rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B (stF, Some pf) s
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) + 64)) gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 (nb + snd pf)) y1 y2 y3 y4 y5 y6 y7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6) F (ret_pc ra) fc None m' (seg_rom ssegs))).
  { intros nb stF rF m' x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 MRF MIF STF FRF RGF RBF KF NDF CTF CNF PEF BSF NB0 NBAL NBC RFN DJN.
    rewrite unsigned_lit by lia. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    pose proof (rreserved_disjoint1 _ _ RFN ltac:(lia)) as NIMG. pose proof (rreserved_tlsU _ _ RFN) as NTLS. pose proof (rreserved_disjoint _ _ RFN) as (_ & _ & NI3 & NI4).
    pose proof (rreserved_disjoint _ _ RF) as (_ & _ & OI3 & OI4).
    assert (CPF : conc stF pf = nb + snd pf) by (rewrite (conc_region' stF pf rF) by (rewrite Fp; exact RGF); rewrite RBF; reflexivity).
    (* [comment removed for export] *)
    assert (NFP_hi : forall a, bv_unsigned sp <= a -> ~ FP nb a).
    { intros a Ha. subst FP; cbv beta. first [clear -Ha RBC NBC GC LOv SLO CEILF__ CEILM__ CEILP__ | clear -Ha RBC NBC GC LOv SLO]. ceil_facts. intros [X|[X|[X|X]]]; lia. }
    assert (NFP_img : forall a, 0x22000 <= a < 0x55000 -> ~ FP nb a).
    { intros a Ha. subst FP; cbv beta. first [clear -Ha DRr NIMG GIMG LOv SLO ON4096 ND4 CEILF__ CEILM__ CEILP__ | clear -Ha DRr NIMG GIMG LOv SLO ON4096 ND4]. intros [X|[X|[X|X]]]; lia. }
    assert (NFP_tls : forall a, the_tb <= a < the_tb + 4096 -> ~ FP nb a).
    { intros a Ha. subst FP; cbv beta. rewrite EG, Cag. first [clear -Ha TLSr NTLS GTLS TBF LOv SLO Sag0 Sag1 Hkg RUg CEILF__ CEILM__ CEILP__ | clear -Ha TLSr NTLS GTLS TBF LOv SLO Sag0 Sag1 Hkg RUg]. unfold AREA_HDR, META_SIZE, NSLOTS in *; ceil_facts. intros [X|[X|[X|X]]]; lia. }
    assert (NFP_blk : forall blk' a, In blk' (lbrm LB blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FP nb a).
    { intros blk' a Hb' Hab. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' NEQ].
      assert (NE' : blk_slot blk' <> blk_slot blk) by (intros EQ; rewrite EQ, aptr_eqb_refl in NEQ; cbn in NEQ; exact NEQ).
      destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hin') as [(r' & Hr' & Kr' & A16' & AEND' & _) _ _].
      subst FP; cbv beta. rewrite EG, Cag.
      destruct (N.eq_dec (fst (blk_slot blk')) (fst b)) as [EF|NF].
      - specialize (BCLR blk' Hin' NE' ltac:(rewrite Ebm; exact EF)). rewrite SS0, Sc, STR, OLDLEN in BCLR.
        rewrite EF, Hr in Hr'. assert (r' = r) as -> by congruence. fold old in A16', AEND', BCLR. fold on in A16', AEND'.
        first [clear -BCLR Hab A16' AEND' CEILF__ CEILM__ CEILP__ | clear -BCLR Hab A16' AEND']. unfold UNIT, IB in *. intros _. lia.
      - pose proof (lr_lo_group r Kr) as LR. pose proof (lr_lo_group r' Kr') as LR'. pose proof (round_up_pg_ge (r_len r')) as RU'.
        destruct (WR _ _ Hr') as (RB0' & _ & _ & RBC' & _).
        assert (NEa : fst (blk_slot blk') <> fst ag) by (intros E2; rewrite E2, Hrag in Hr'; assert (r' = rag) as -> by congruence; exact (NKg Kr')).
        pose proof (rarea_lr_lo st0 ag arg rag WF Hag Hrag) as LLg.
        destruct (DJ _ _ _ _ Hr' Hr NF) as [D1|D1]; destruct (DJN _ _ Hr' NF) as [D2|D2]; destruct (DJ _ _ _ _ Hr' Hrag NEa) as [D3|D3];
          first [clear -Hab A16' AEND' LR LR' RU' RB0' RBC' LLg D1 D2 D3 LOv SLO Sag0 Sag1 Hkg RUg CEILF__ CEILM__ CEILP__ | clear -Hab A16' AEND' LR LR' RU' RB0' RBC' LLg D1 D2 D3 LOv SLO Sag0 Sag1 Hkg RUg]; unfold AREA_HDR, META_SIZE, NSLOTS in *; ceil_facts; intros [X|[X|[X|X]]]; lia. }
    unfold rrfinQ. cbn [fst snd oconc]. rewrite CPF. exists m', errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MIF|].
    split. { replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat (cells_size (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6))) by (cbn; lia).
             eapply stk_release; [exact STF| exact FRF| first [clear -SLO CEILF__ CEILM__ CEILP__ | clear -SLO]; lia]. }
    split. { eapply rpres_except_rw_cells; [exact PEF| exact ERR1|]. rewrite (rerrno_addr tp TP). change (Z.of_nat (cells_size [C4 errv1])) with 4.
             intros a Ha. apply NFP_tls. first [clear -Ha TBF CEILF__ CEILM__ CEILP__ | clear -Ha TBF]. lia. }
    split. { eapply rauxv_ok_pres; [exact AUX1| exact PEF| intros a Ha; apply NFP_hi; first [clear -Ha SB CEILF__ CEILM__ CEILP__ | clear -Ha SB]; lia| intros a Ha; apply NFP_img; unfold RAUXV_CELL in Ha; first [clear -Ha CEILF__ CEILM__ CEILP__ | clear -Ha]; lia]. }
    split; [exact MRF|].
    split. { eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_malloc_big.brk_link_ps_ext; [| | exact BL].
             - rewrite CTF. reflexivity.
             - intros brid boff HB. apply CNF. cbn [fst]. intros E2. destruct (ci_bk _ _ C brid boff HB) as (rb & Hrb & Kb). rewrite E2, Hr in Hrb.
               assert (rb = r) as -> by congruence. rewrite Kr in Kb. discriminate. }
    split. { eapply rheap_pres_trans; [exact HP1|]. intros a Ha CA. apply PEF; [exact Ha|].
             destruct CA as [CA|[[CA NS]|[(blk' & Hb' & Hab)|[CA NE]]]]; [apply NFP_hi; exact CA| apply NFP_img; exact CA| exact (NFP_blk blk' a Hb' Hab)| apply NFP_tls; exact CA]. }
    split. { eapply rpres_except_rw_cells; [exact PEF| exact REPL1|]. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4. intros a Ha. apply NFP_img. unfold RMREPLACED, RCTX in Ha. first [clear -Ha CEILF__ CEILM__ CEILP__ | clear -Ha]. lia. }
    split; [reflexivity|]. split; [reflexivity|].
    split. { unfold rblock_range. split; [first [clear -NB0 Sp Hoff CEILF__ CEILM__ CEILP__ | clear -NB0 Sp Hoff]; lia|]. split; [rewrite Sp; first [clear -NBAL Hoff CEILF__ CEILM__ CEILP__ | clear -NBAL Hoff]; Z.div_mod_to_equations; lia|]. split; [first [clear -N CEILF__ CEILM__ CEILP__ | clear -N]; lia|].
             first [clear -NBC NIMG NTLS NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NBC NIMG NTLS NDR EP Sp Hoff N]. ceil_facts. lia. }
    destruct (ruser_chunk stF m' pf rF n MRF ltac:(rewrite Fp; exact RGF) KF ltac:(first [clear -Sp Hoff CEILF__ CEILM__ CEILP__ | clear -Sp Hoff]; lia) ltac:(first [clear -NDF NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDF NDR EP Sp Hoff N]; lia) ltac:(first [clear -N CEILF__ CEILM__ CEILP__ | clear -N]; lia)) as (J & JCH).
    rewrite CPF in JCH. exists (skipn k1 J).
    pose proof (rw_cells_CB_prefix_agree m' (nb + snd pf) (Z.to_nat n) J (firstn k1 bs) JCH BSF ltac:(rewrite LK1; exact (proj2 (proj2 K1R)))) as CH'.
    rewrite LK1 in CH'. replace (Z.to_nat (n - Z.min (blk_size blk) n)) with (Z.to_nat n - k1)%nat by (rewrite EK1; first [clear -N SZ CEILF__ CEILM__ CEILP__ | clear -N SZ]; lia). rewrite <- EK1. exact CH'. }
  (* [comment removed for export] *)
  set (stH := havoc pf (needed - snd pf) st).
  destruct (rmrep_havoc st m1 pf (needed - snd pf) MRt TKt) as [MRH TKH]. fold stH in MRH, TKH.
  assert (RGH : s_regions stH = s_regions st0) by (subst stH; rewrite s_regions_havoc; reflexivity).
  assert (CGH : forall q, conc stH q = conc st0 q) by (intros q; unfold conc, get_region; rewrite RGH; reflexivity).
  assert (HAVT : forall u hl, r_hav (get_shadow st (fst pf)) !! u = Some hl -> hl_ticks hl (s_tick st)).
  { intros u hl Hu ch Hch. exact (proj1 (sh_ticks_of_ticks_ok st (fst pf) TKt) u hl ch Hu Hch). }
  assert (HK3H : cell_read (get_shadow stH (fst pf)) (snd pf - 3) = Known v3).
  { subst stH. rewrite (cell_read_havoc_out pf (needed - snd pf) st ltac:(rewrite Sp; clear; Z.div_mod_to_equations; (keep_hyps off q r H H0; lia)) ltac:((keep_hyps CEILV blk bs n g b r bm ag rag k1 N NDR; lia)) HAVT (fst pf, snd pf - 3)) by (cbn [fst snd]; (keep_hyps CEILV blk bs n g b r bm ag rag k1; lia)).
    cbn [fst snd]. exact C3. }
  assert (NOKH : forall o v, snd pf <= o < needed -> cell_read (get_shadow stH (fst b)) o = Known v -> False).
  { intros o v Ho Hc. subst stH.
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _). pose proof INV as (_ & _ & _ & _ & _ & _ & ISH).
    destruct (cell_read_havoc_in pf (needed - snd pf) st ltac:(rewrite Sp; clear; Z.div_mod_to_equations; lia) ltac:(lia) HAVT (fst b, o) ltac:(cbn [fst]; symmetry; exact Fp) ltac:(cbn [snd]; lia)) as [h Hh].
    - intros v' tk Hc'. cbn [snd] in Hc'. change (s_tick st) with (N.succ (s_tick st0)).
      change (get_shadow st (fst pf)) with (get_shadow st0 (fst pf)) in Hc'. unfold get_shadow in Hc'.
      destruct (s_shadow st0 !! fst pf) as [sh|] eqn:Esh; [| cbn in Hc'; rewrite lookup_empty in Hc'; discriminate].
      cbn in Hc'. pose proof (proj1 (ish_ticks _ _ ISH (fst pf) sh Esh) o v' tk Hc') as [_ T]. first [clear -T CEILF__ CEILM__ CEILP__ | clear -T]. lia.
    - cbn [fst snd] in Hh. rewrite Hh in Hc. discriminate. }
  assert (PTXH : ptrs_ctx_in (fun x => x <> fst b) stH).
  { eapply ptrs_ctx_in_ext; [| | | | exact PTX0]; subst stH st; unfold ctx; rewrite ?s_ctx_havoc, ?s_metas_havoc, ?s_areas_havoc, ?s_groups_havoc; reflexivity. }
  assert (HghH : s_groups stH !! b = Some (mkGhdr (Some g) ai)) by (subst stH; rewrite s_groups_havoc; exact Hgh).
  assert (ONLYGH : forall b' gh, s_groups stH !! b' = Some gh -> fst b' = fst b -> b' = b) by (subst stH; rewrite s_groups_havoc; exact ONLYG).
  assert (MEMGH : forall q b'', m_mem (get_meta_rec stH q) = Some b'' -> fst b'' = fst b -> q = g).
  { intros q b'' H1 H2. apply (MEMG q b''); [| exact H2]. subst stH. unfold get_meta_rec in H1 |- *. rewrite s_metas_havoc in H1. exact H1. }
  assert (MSgH : meta_slot stH g) by (unfold meta_slot; subst stH; rewrite s_areas_havoc; exact MSg).
  assert (HmemH : m_mem (get_meta_rec stH g) = Some b) by (subst stH; unfold get_meta_rec; rewrite s_metas_havoc; exact Hmem).
  assert (GRH : get_meta_rec stH g = mr) by (subst stH mr; unfold get_meta_rec; rewrite s_metas_havoc; reflexivity).
  (* [comment removed for export] *)
  assert (SUCC : forall (nb : Z) (mA : mem) (x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
    0 < nb -> nb mod 4096 = 0 -> nb + needed <= alloc_ceiling -> ranges_free ref_reserved nb needed = true ->
    (forall rid' r', s_regions st0 !! rid' = Some r' -> rid' <> fst b -> nb + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb) ->
    mem_inv ssegs mA -> stk ssegs mA lo (bv_unsigned sp + -64) ->
    rw_cells ssegs mA (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6) ->
    rw_cells ssegs mA G [C8 (pw st0 (m_prev mr)); C8 (pw st0 (m_next mr)); C8 (wz (conc st0 b)); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))] ->
    rpres_except (FP nb) m1 mA ->
    (forall A k, 0 <= A -> 0 <= k -> (A + k <= old \/ old + on <= A) -> (A + k <= nb \/ nb + needed <= A) -> A + k <= alloc_ceiling -> agree_on m1 mA A k) ->
    (forall o, 0 <= o < Z.min on needed - 4 -> mA (wa (nb + o)) = m1 (wa (old + o))) ->
    wr_at ssegs mA nb needed ->
    rimplT m (ret (big_resize st g (fst b) nb needed pf n 0, Some pf)) s
      (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
      (MS (mkR (Z_to_bv 64 0x1a420) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 x1 x2 (Z_to_bv 64 needed) (wz G) (Z_to_bv 64 nb) y1 y2 y3 y4 y5 y6 y7
               (Z_to_bv 64 (blk_addr blk + blk_size blk)) (Z_to_bv 64 (P - (old + 16))) (Z_to_bv 64 4095) a0 (Z_to_bv 64 n) s7 s8 s9 s10 s11 x3 x4 x5 x6)
          F (Z_to_bv 64 0x1a420) fc None mA (seg_rom ssegs))).
  { intros nb mA x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 NB0 NBAL NBC RFN DJN MIA STA FRA MMA PEA AGA CPY WRN.
    pose proof (rreserved_disjoint1 _ _ RFN ltac:(lia)) as NIMG.
    apply rimplT_ret.
    (* [comment removed for export] *)
    step. step. step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by (ceil_facts; lia). ceil_facts. first [clear -K NBC ND4 CEILF__ CEILM__ CEILP__ | clear -K NBC ND4]. lia. }
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rrealloc_big63_stores _ _ gp tp _ _ _ _ (wz G) _ _ (Z_to_bv 64 nb) _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc mA
                G nb (P - (old + 16)) needed n (m_avail mr) (m_freed mr) (meta_word mr));
        [exact MMA| exact MIA| (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb G0; lia)| ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb GC; lia)| exact NB0| exact NBC| ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb CEILM__ ND4 NB0 NBC; lia)| exact NDAL
        | first [clear -EP Sp Hoff CEILF__ CEILM__ CEILP__ | clear -EP Sp Hoff]; (keep_hyps CEILV off r Hoff Sp; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb N; lia)| first [clear -NDR CEILF__ CEILM__ CEILP__ | clear -NDR]; (keep_hyps CEILV n b r NDR; lia)| exact WRD| apply wz_unsigned; ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb CEILM__ G0 GC; lia)| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    intros msB (m3 & -> & MU3 & WM3 & MI3 & MC3). rewrite WLO in MC3.
    (* [comment removed for export] *)
    destruct (rl_rmrep stH m1 mA m3 g b pf ai r nb needed G MRH TKH ltac:(rewrite RGH; exact Hr) Kr HghH Sb ONLYGH MEMGH MSgH ltac:(rewrite CGH; reflexivity) HmemH PTXH Fp
                ltac:(subst on; rewrite <- OLDLEN; rewrite STR in OS; first [clear -Sp Hoff OS NDR EP N SZ CEILF__ CEILM__ CEILP__ | clear -Sp Hoff OS NDR EP N SZ]; unfold UNIT, IB in *; lia) NOKH
                ltac:(exact ON4096 || (first [clear -ON4096 CEILF__ CEILM__ CEILP__ | clear -ON4096]; lia)) NB0 NBAL ND4 NDAL NBC RFN ltac:(rewrite RGH; exact DJN))
      as [MRR TKR].
    - intros A k HA0 K0 DO DN AC. exact (AGA A k HA0 K0 DO DN AC).
    - intros o Ho. apply CPY. subst on. rewrite <- OLDLEN. rewrite STR in OS. first [clear -Ho Sp Hoff OS NDR EP N SZ OLDLEN CEILF__ CEILM__ CEILP__ | clear -Ho Sp Hoff OS NDR EP N SZ OLDLEN]. unfold UNIT, IB in *. lia.
    - exact WRN.
    - exact MU3.
    - exact WM3.
    - rewrite GRH. rewrite !(pw_conc_ext st0 stH _ CGH).
      replace (meta_word (m_set_maplen (needed / 4096) mr)) with (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + needed); [exact MC3|].
      assert (E4 : 4096 * (needed / 4096) = needed) by (first [clear -NDAL ND4 CEILF__ CEILM__ CEILP__ | clear -NDAL ND4]; Z.div_mod_to_equations; lia).
      unfold meta_word, m_set_maplen. cbn [m_last_idx m_freeable m_sizeclass m_maplen].
      change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
      rewrite Z.mod_small by (ceil_facts; first [clear -NBC ND4 NB0 CEILF__ CEILM__ CEILP__ | clear -NBC ND4 NB0]; Z.div_mod_to_equations; lia). first [clear -E4 CEILF__ CEILM__ CEILP__ | clear -E4]; lia.
    - (* [comment removed for export] *)
      set (st2R := upd_meta g (m_set_maplen (needed / 4096)) (upd_region (fst b) (fun rg => mkRegion (r_kind rg) nb needed) stH)) in *.
      set (rN := mkRegion (r_kind r) nb needed).
      assert (HrN : s_regions st2R !! fst pf = Some rN) by (rewrite Fp; subst st2R rN; apply (rl_lookup_new stH g b r nb needed); rewrite RGH; exact Hr).
      replace (nb + 16 + (P - (old + 16))) with (r_base rN + snd pf) by (cbn [r_base rN]; first [clear -EP CEILF__ CEILM__ CEILP__ | clear -EP]; lia).
      replace (Z_to_bv 64 (nb + needed - 4 + 4)) with (Z_to_bv 64 (r_base rN + snd (fst b, needed - 4) + 4)) by (cbn [snd r_base rN]; f_equal; lia).
      replace (Z_to_bv 64 (nb + needed - 4 - (r_base rN + snd pf) - n)) with (Z_to_bv 64 (snd (fst b, needed - 4) - snd pf - n)) by (cbn [snd r_base rN]; f_equal; lia).
      replace (Z_to_bv 64 (nb + needed - 4)) with (Z_to_bv 64 (r_base rN + snd (fst b, needed - 4))) by (cbn [snd r_base rN]; f_equal; lia).
      unfold big_resize, resize63. change IB with 4.
      rewrite (havoc_upd_comm pf (needed - snd pf) g _ (fst b) _ st r Hr). fold stH. fold st2R.
      replace (set_size pf (fst b, needed - 4) n 0 (wr8 (fst b, needed - 4) 0 st2R))
         with (set_size pf (fst b, needed - 4) n (Z.land v3 31) (wr8 (fst b, needed - 4) 0 st2R)) by (rewrite V0; reflexivity).
      rewrite set_size_land31.
      eapply evt_mono.
      { eapply (rrealloc_setsize63_walk _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 lo st2R pf (fst b, needed - 4) rN v3 n
                  ra s0 s1 s2 s3 s4 s5 s6 (fun a => a = r_base rN + snd pf - 3 \/ r_base rN + snd pf + n <= a < r_base rN + snd (fst b, needed - 4) + 1));
          first [exact MRR| exact MI3| exact TKR| exact HrN| idtac].
        - intros a Ha. exact Ha.
        - rewrite unsigned_lit by lia. eapply stk_transport_disjoint; [exact STA| exact MU3| exact WM3|]. cbn. ceil_facts. first [clear -GC LOv SLO CEILF__ CEILM__ CEILP__ | clear -GC LOv SLO]; lia.
        - rewrite unsigned_lit by lia. eapply rw_cells_transport; [exact FRA| exact MU3| exact WM3|]. cbn. ceil_facts. first [clear -GC LOv SLO CEILF__ CEILM__ CEILP__ | clear -GC LOv SLO]; lia.
        - exact LO.
        - rewrite unsigned_lit by lia. first [clear -SLO CEILF__ CEILM__ CEILP__ | clear -SLO]; lia.
        - rewrite unsigned_lit by lia. first [clear -SPR CEILF__ CEILM__ CEILP__ | clear -SPR]; lia.
        - apply rpres_except_refl.
        - apply wmono_refl.
        - exact Kr.
        - cbn [fst]. symmetry. exact Fp.
        - cbn [r_base rN]. rewrite unsigned_lit by (ceil_facts; first [clear -NBC NB0 Sp Hoff NDR EP N CEILF__ CEILM__ CEILP__ | clear -NBC NB0 Sp Hoff NDR EP N]; lia). reflexivity.
        - lia.
        - cbn [snd]. first [clear -NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDR EP Sp Hoff N]. lia.
        - cbn [snd]. first [clear -NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDR EP Sp Hoff N]. lia.
        - first [clear -Sp Hoff CEILF__ CEILM__ CEILP__ | clear -Sp Hoff]; lia.
        - cbn [snd r_len rN]. rewrite (round_up_pg_id' needed NDAL). lia.
        - subst st2R. rewrite (rl_shadow stH g b r nb needed) by (rewrite RGH; exact Hr). exact HK3H.
        - intros b' gh Hb' Hf'. subst st2R. rewrite (rl_groups stH g b r nb needed) in Hb' by (rewrite RGH; exact Hr).
          pose proof (ONLYGH b' gh Hb' ltac:(rewrite Hf', Fp; reflexivity)) as ->. left. rewrite Sb. first [clear -Sp Hoff CEILF__ CEILM__ CEILP__ | clear -Sp Hoff]; lia. }
      intros msf POST. unfold rrret_post in POST.
      destruct POST as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & -> & (MRF & TKF & MIF & STF & FRF & PEl & WMl)).
      rewrite !unsigned_lit in STF, FRF by (keep_hyps CEILV sp blk bs n lo g b r bm ag rag k1 nb CEILF__ SLO SPR LOv; lia).
      cbn [r_base rN].
      eapply (FINAL nb _ rN m'); try eassumption; try reflexivity.
      + unfold set_size. destruct (5 <=? _); destruct (negb _); rewrite ?s_regions_wr8, ?s_regions_wr32, ?s_regions_wr8; rewrite <- Fp; exact HrN.
      + cbn [r_len rN]. rewrite (round_up_pg_id' needed NDAL). lia.
      + assert (CT2 : ctx st2R = ctx st0).
        { subst st2R. rewrite (rl_ctx stH g b r nb needed) by (rewrite RGH; exact Hr). subst stH st. unfold ctx. rewrite s_ctx_havoc. reflexivity. }
        rewrite <- CT2. unfold set_size. destruct (5 <=? _); destruct (negb _); unfold ctx; rewrite ?s_ctx_wr8, ?s_ctx_wr32, ?s_ctx_wr8; reflexivity.
      + intros q Hq. unfold conc at 1, get_region. rewrite s_regions_set_size, s_regions_wr8. subst st2R. fold (get_region (upd_meta g (m_set_maplen (needed / 4096)) (upd_region (fst b) (λ rg : region, {| r_kind := r_kind rg; r_base := nb; r_len := needed |}) stH)) (fst q)).
        fold (conc (upd_meta g (m_set_maplen (needed / 4096)) (upd_region (fst b) (λ rg : region, {| r_kind := r_kind rg; r_base := nb; r_len := needed |}) stH)) q).
        rewrite (rl_conc stH g b r nb needed ltac:(rewrite RGH; exact Hr) q Hq). apply CGH.
      + (* [comment removed for export] *)
        eapply rpres_except_trans; [exact PEA|]. eapply rpres_except_trans.
        * eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. subst FP. cbv beta in NC. cbn [outside].
          repeat split; try exact Logic.I; first [clear -NC CEILF__ CEILM__ CEILP__ | clear -NC]; lia.
        * eapply rpres_except_mono; [exact PEl|]. intros a Ha. subst FP. cbv beta. right. right. left. cbn [snd] in Ha.
          cbn [snd r_base rN] in Ha. first [clear -Ha EP Sp Hoff NDR N CEILF__ CEILM__ CEILP__ | clear -Ha EP Sp Hoff NDR N]. lia.
      + (* [comment removed for export] *)
        eapply rpres_except_bytes_at; [exact PEl| |].
        * assert (BSA : bytes_at ssegs mA (nb + snd pf) (firstn k1 bs)).
          { pose proof (bytes_at_firstn m1 (blk_addr blk) bs k1 BS1) as X. rewrite HAp in X. destruct X as (X0 & X1 & X2). rewrite LK1 in X1.
            split; [first [clear -NB0 Sp Hoff CEILF__ CEILM__ CEILP__ | clear -NB0 Sp Hoff]; lia|]. split; [rewrite LK1; ceil_facts; first [clear -NBC K1R NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NBC K1R NDR EP Sp Hoff N]; lia|].
            intros ii Hii. rewrite LK1 in Hii. rewrite <- (X2 ii ltac:(rewrite LK1; exact Hii)). unfold mrd.
            replace (nb + snd pf + Z.of_nat ii) with (nb + (snd pf + Z.of_nat ii)) by lia. replace (old + snd pf + Z.of_nat ii) with (old + (snd pf + Z.of_nat ii)) by lia.
            rewrite (CPY (snd pf + Z.of_nat ii)) by (subst on; rewrite <- OLDLEN; rewrite STR in OS; first [clear -Hii K1R Sp Hoff OS NDR EP N SZ CEILF__ CEILM__ CEILP__ | clear -Hii K1R Sp Hoff OS NDR EP N SZ]; unfold UNIT, IB in *; lia).
            destruct (m1 (wa (old + (snd pf + Z.of_nat ii)))); [reflexivity|].
            rewrite !ref_seg_rom_none by (rewrite wa_unsigned by (ceil_facts; (keep_hyps CEILV blk off bs n g b r bm ag rag k1 nb ii CEILM__ Hoff Sp NDR EK1 NB0 NBC Hii rsv RSVE RSV0 RB0 RBC Se; lia)); rewrite STR in OS; unfold UNIT, IB in *; ceil_facts; first [clear -Hii K1R Sp Hoff OS NDR EP N SZ NIMG DRr OLDLEN EON EOLD STR NBC RBC NB0 RB0 CEILF__ CEILM__ CEILP__ | clear -Hii K1R Sp Hoff OS NDR EP N SZ NIMG DRr OLDLEN EON EOLD STR NBC RBC NB0 RB0]; clearbody old on; (keep_hyps CEILV blk off n b old k1 nb ii Hoff N Sp NDR NB0 NIMG on OS OLDLEN DRr K1R Hii; lia)). reflexivity. }
          eapply bytes_at_transport; [exact BSA| exact MU3|]. rewrite LK1. cbn. rewrite EG, Cag.
          pose proof (rarea_lr_lo st0 ag arg rag WF Hag Hrag) as LLg.
          assert (NEa : fst ag <> fst b) by (intros E2; rewrite E2, Hr in Hrag; assert (rag = r) as -> by congruence; exact (NKg Kr)).
          destruct (DJN _ _ Hrag NEa) as [D2|D2]; first [clear -D2 K1R Hkg Sag0 Sag1 RUg Sp Sc Hoff LLg NDR EP N CEILF__ CEILM__ CEILP__ | clear -D2 K1R Hkg Sag0 Sag1 RUg Sp Sc Hoff LLg NDR EP N]; unfold AREA_HDR, META_SIZE, NSLOTS, UNIT in *; (split; [| split; [| exact Logic.I]]).
          all: try clearbody old; try clearbody on. all: first [lia| match goal with |- ?gg => idtac "LIAFAIL" gg end; try match reverse goal with HH : ?T |- _ => idtac HH ":" T; fail end; fail].
        * rewrite LK1. intros a Ha. cbn [snd r_base rN]. first [clear -Ha K1R CEILF__ CEILM__ CEILP__ | clear -Ha K1R]. lia. }
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { eapply (rrealloc_big63_head ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) _ t2 s0 (wz G) a0 (wz (conc st0 b)) (Z_to_bv 64 (m_sizeclass mr)) a5
              (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (blk_addr blk + blk_size blk)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
              P (old + 16) n (meta_word mr) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr));
      [rewrite A0, HAp; subst P; apply unsigned_lit; (keep_hyps CEILV blk off bs n g b r rsv bm ag rag k1 CEILM__ Hoff RSVE RSV0 RB0 RBC Sp Se SZm; lia)| rewrite Sc; reflexivity| subst P; (keep_hyps CEILV blk off bs n g b r bm ag rag k1 Hoff RB0 Sp; lia)| subst P; rewrite STR in OS; subst on; unfold UNIT, IB in *; ceil_facts; (keep_hyps CEILV blk bs n g b r rsv bm ag rag k1 RSVE RSV0 RBC Se SZm; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 N; lia)| reflexivity
      | (keep_hyps CEILV blk bs n g b r bm ag rag k1 LI0; lia)| (keep_hyps CEILV blk off bs n g b r bm ag rag k1 FRB; lia)| (keep_hyps CEILV blk off bs n g b r bm ag rag k1 SC63; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 MLR; lia)]. }
  intros msA HDA. unfold rr63A_post in HDA. rewrite <- END in HDA.
  apply rimplT_if; intros EQN; rewrite EQN in HDA; subst msA.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in EQN.
    apply rimplT_ret.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite Cb in K. unfold wz in K. rewrite ?unsigned_lit in K by (ceil_facts; lia). ceil_facts. lia. }
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rrealloc_big63_stores _ _ gp tp _ _ _ _ (wz G) _ _ (wz (conc st0 b)) _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m1
                G old (P - (old + 16)) needed n (m_avail mr) (m_freed mr) (meta_word mr));
        [exact MM1| exact MI1| (keep_hyps CEILV blk bs n g b r bm ag rag k1 G0; lia)| ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 GC; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 RB0; lia)| rewrite <- EQN, OLDLEN; subst old on; exact RBC| ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 CEILM__ OLDLEN RB0 RBC ND4 EQN; lia)| exact NDAL
        | subst P; (keep_hyps CEILV blk off bs n g b r bm ag rag k1 Hoff Sp; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 N; lia)| first [clear -NDR CEILF__ CEILM__ CEILP__ | clear -NDR]; (keep_hyps CEILV n b r NDR; lia)| exact WRD| apply wz_unsigned; ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 CEILM__ G0 GC; lia)| rewrite Cb; reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    intros msB (m2 & -> & MU2 & WM2 & MI2 & MC2).
    rewrite WLO in MC2. replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + needed) with (meta_word mr) in MC2 by (unfold meta_word; lia).
    assert (MRH2 : rmrep stH m2).
    { pose proof (rmrep_put_meta_frame stH m1 m2 g mr MRH ltac:(unfold meta_slot; subst stH; rewrite s_areas_havoc; exact MSg)
                    ltac:(rewrite CGH; fold G; eapply munch_weaken; [| exact MU2]; intros y Hy; unfold META_SIZE in Hy; cbn in Hy |- *; repeat split; try exact Logic.I; (keep_hyps CEILV TB blk bs n g b r bm ag rag k1 y Hy; lia)) WM2
                    ltac:(rewrite CGH; fold G; unfold meta_cells; rewrite Hmem; rewrite !(pw_conc_ext st0 stH _ CGH);
                          change (pw st0 (Some b)) with (wz (conc st0 b)); rewrite Cb; exact MC2)) as X.
      rewrite (put_meta_same stH g mr) in X; [exact X|]. subst stH st. rewrite s_metas_havoc. exact GPR. }
    (* [comment removed for export] *)
    replace (old + 16 + (P - (old + 16))) with P by lia.
    replace (Z_to_bv 64 (old + needed - 4 + 4)) with (Z_to_bv 64 (r_base r + snd (fst b, needed - 4) + 4)) by (cbn [snd]; f_equal; subst old; lia).
    replace (Z_to_bv 64 (old + needed - 4 - P - n)) with (Z_to_bv 64 (snd (fst b, needed - 4) - snd pf - n)) by (cbn [snd]; f_equal; subst old P; lia).
    replace (Z_to_bv 64 (old + needed - 4)) with (Z_to_bv 64 (r_base r + snd (fst b, needed - 4))) by (cbn [snd]; f_equal; subst old; lia).
    eapply evt_mono.
    { eapply (rrealloc_setsize63_walk _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m2 m2 lo stH pf (fst b, needed - 4) r v3 n
                ra s0 s1 s2 s3 s4 s5 s6 (fun a => a = P - 3 \/ P + n <= a < r_base r + snd (fst b, needed - 4) + 1));
        first [exact MRH2| exact MI2| exact TKH| exact Kr| idtac].
      - intros a Ha. exact Ha.
      - rewrite unsigned_lit by lia. eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn. ceil_facts. (keep_hyps CEILV sp blk off bs n lo g b r bm ag rag k1 LOv GC; lia).
      - rewrite unsigned_lit by lia. eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. ceil_facts. (keep_hyps CEILV sp blk off bs n lo g b r bm ag rag k1 SLO LOv GC; lia).
      - exact LO.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. lia.
      - apply rpres_except_refl.
      - apply wmono_refl.
      - rewrite RGH, Fp. exact Hr.
      - cbn [fst]. symmetry. exact Fp.
      - rewrite unsigned_lit by (subst P; ceil_facts; (keep_hyps CEILV blk off bs n g b r rsv bm ag rag k1 CEILM__ Hoff RSVE RSV0 RB0 RBC Sp Se SZm; lia)). reflexivity.
      - lia.
      - cbn [snd]. first [clear -NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDR EP Sp Hoff N]. lia.
      - cbn [snd]. first [clear -NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDR EP Sp Hoff N]. lia.
      - lia.
      - cbn [snd]. subst on. lia.
      - subst stH. rewrite (cell_read_havoc_out pf (needed - snd pf) st ltac:(rewrite Sp; clear; Z.div_mod_to_equations; (keep_hyps off q r H H0; lia)) ltac:((keep_hyps CEILV blk off bs n g b r bm ag rag k1 N NDR; lia)) HAVT (fst pf, snd pf - 3)) by (cbn [fst snd]; (keep_hyps CEILV blk bs n g b r bm ag rag k1; lia)).
        cbn [fst snd]. exact C3.
      - intros b' gh Hb' Hf'. subst stH. rewrite s_groups_havoc in Hb'. change (s_groups st) with (s_groups st0) in Hb'.
        pose proof (ONLYG b' gh Hb' ltac:(rewrite Hf', Fp; reflexivity)) as ->. left. rewrite Sb. lia. }
    intros msf POST. unfold rrret_post in POST.
    destruct POST as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & (MRF & TKF & MIF & STF & FRF & PEl & WMl)).
    rewrite !unsigned_lit in STF, FRF by (keep_hyps CEILV sp blk bs n lo g b r bm ag rag k1 CEILF__ SLO SPR LOv; lia).
    (* [comment removed for export] *)
    unfold resize63. change IB with 4.
    replace (set_size pf (fst b, needed - 4) n 0 (wr8 (fst b, needed - 4) 0 (havoc pf (needed - snd pf) st)))
       with (set_size pf (fst b, needed - 4) n (Z.land v3 31) (wr8 (fst b, needed - 4) 0 stH)) by (rewrite V0; reflexivity).
    rewrite set_size_land31.
    replace (r_base r + snd pf) with (old + snd pf) by reflexivity.
    eapply (FINAL old _ r m'); try eassumption; try reflexivity.
    + unfold set_size. destruct (5 <=? _); destruct (negb _); subst stH st; rewrite ?s_regions_wr8, ?s_regions_wr32, ?s_regions_wr8, ?s_regions_havoc; cbn [s_regions set_tick]; exact Hr.
    + rewrite <- EQN, OLDLEN. subst on. lia.
    + unfold set_size. destruct (5 <=? _); destruct (negb _); subst stH st; unfold ctx; rewrite ?s_ctx_wr8, ?s_ctx_wr32, ?s_ctx_wr8, ?s_ctx_havoc; reflexivity.
    + intros q _. unfold conc, get_region. rewrite s_regions_set_size, s_regions_wr8. subst stH. rewrite s_regions_havoc. reflexivity.
    + (* [comment removed for export] *)
      eapply rpres_except_trans.
      * eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. subst FP. cbv beta in NC. cbn [outside].
        repeat split; try exact Logic.I; first [clear -NC CEILF__ CEILM__ CEILP__ | clear -NC]; lia.
      * eapply rpres_except_mono; [exact PEl|]. intros a Ha. subst FP. cbv beta. right. left. subst old on. rewrite <- OLDLEN, EQN. cbn [snd] in Ha.
        first [clear -Ha EP Sp Hoff NDR N CEILF__ CEILM__ CEILP__ | clear -Ha EP Sp Hoff NDR N]. lia.
    + (* [comment removed for export] *)
      eapply rpres_except_bytes_at; [exact PEl| |].
      * eapply bytes_at_transport; [| exact MU2|].
        -- eapply bytes_at_firstn. rewrite <- HAp. exact BS1.
        -- rewrite LK1. cbn. rewrite EG, Cag.
           assert (NEr : fst b <> fst ag) by (intros E2; rewrite E2 in Hr; rewrite Hr in Hrag; assert (rag = r) as -> by congruence; exact (NKg Kr)).
           pose proof (lr_lo_group r Kr) as LR. pose proof (rarea_lr_lo st0 ag arg rag WF Hag Hrag) as LLg.
           rewrite STR in OS. destruct (DJ _ _ _ _ Hr Hrag NEr) as [D1|D1]; first [clear -D1 K1R RBgC Hkg Sag0 Sag1 RUg Sp Sc Hoff RB0 B0 LR LLg HAp OS EP OLDLEN EOLD EON CEILF__ CEILM__ CEILP__ | clear -D1 K1R RBgC Hkg Sag0 Sag1 RUg Sp Sc Hoff RB0 B0 LR LLg HAp OS EP OLDLEN EOLD EON]; unfold AREA_HDR, META_SIZE, UNIT, IB, NSLOTS in *; ceil_facts;
             (split; [| split; [| exact Logic.I]]).
           all: clearbody old on; lia.
      * rewrite LK1. intros a Ha. cbn [snd]. first [clear -Ha K1R EP EOLD CEILF__ CEILM__ CEILP__ | clear -Ha K1R EP EOLD]. clearbody old. lia.
    + rewrite <- EQN, OLDLEN. exact RBC.
    + rewrite <- EQN, OLDLEN. exact RF.
    + intros rid' r' Hr' NE'. pose proof (lr_lo_group r Kr). rewrite <- EQN, OLDLEN. subst old on. destruct (DJ _ _ _ _ Hr' Hr NE'); [right| left]; lia.
  - (* [comment removed for export] *)
    apply Z.eqb_neq in EQN.
    pose proof GL as (G1 & G2 & G3 & G4 & G5).
    assert (ERRlo : errno_addr tp + 4 <= lo) by (rewrite (rerrno_addr tp TP); first [clear -TBF LOv CEILF__ CEILM__ CEILP__ | clear -TBF LOv]; lia).
    eapply rimplT_mremap.
    { rewrite <- Cb. eapply (rmremap_spec _ _ gp tp _ _ _ _ _ (wz (conc st0 b)) _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m1
               (conc st0 b) (m_maplen mr * 4096) needed [] errv1 lo);
        first [exact MI1| exact G4| exact G5| reflexivity| idtac]; rewrite ?Cb; ceil_facts.
      - rewrite unsigned_lit by lia. exact ST1.
      - exact ERR1.
      - exact RB0.
      - exact RBAL.
      - first [clear -ML0 CEILF__ CEILM__ CEILP__ | clear -ML0]; lia.
      - clear; Z.div_mod_to_equations; lia.
      - rewrite STR in OS. first [clear -ND4 NDR N EP Sp Hoff OS OLDLEN RBC EOLD EON RB0 SZ CEILF__ CEILM__ CEILP__ | clear -ND4 NDR N EP Sp Hoff OS OLDLEN RBC EOLD EON RB0 SZ]; clearbody old on P pf needed; unfold UNIT, IB in *; ceil_facts; lia.
      - exact NDAL.
      - exact EQN.
      - rewrite OLDLEN. ceil_facts. first [clear -RBC CEILF__ CEILM__ CEILP__ | clear -RBC]. lia.
      - rewrite OLDLEN. exact DRr.
      - rewrite unsigned_lit by lia. first [clear -SLO CEILF__ CEILM__ CEILP__ | clear -SLO]; lia.
      - first [clear -LOv CEILF__ CEILM__ CEILP__ | clear -LOv]. lia.
      - rewrite unsigned_lit by lia. left. first [clear -ERRlo SLO CEILF__ CEILM__ CEILP__ | clear -ERRlo SLO]; lia.
      - rewrite TP, RATP_unsigned. first [clear -TBF CEILF__ CEILM__ CEILP__ | clear -TBF]; lia.
      - rewrite (rerrno_addr tp TP). first [clear -TBF CEILF__ CEILM__ CEILP__ | clear -TBF]; lia. }
    intros x msX [FX PO]. cbv beta. unfold rmremap_facts in FX.
    (* [comment removed for export] *)
    apply rimplT_if; intros OKA; [apply rimplT_undef|]. apply Bool.negb_false_iff in OKA.
    apply rimplT_if; intros ISERR.
    + (* [comment removed for export] *)
      destruct x as [er|  |na]; cbn [mremap_val mremap_ret] in ISERR, PO |- *.
      2:{ exfalso. unfold is_err, TWO64 in ISERR. apply Z.ltb_lt in ISERR. fold old in ISERR. first [clear -ISERR RBC ON4096 CEILF__ CEILM__ CEILP__ | clear -ISERR RBC ON4096]. ceil_facts. lia. }
      2:{ exfalso. destruct FX as (_ & AOK & _ & _). pose proof (mmap_addr_ok_true _ _ _ AOK) as ((_ & _ & AC) & _).
          rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith.mmap_len_of_aligned in AC by lia. ceil_facts.
          unfold is_err, TWO64 in ISERR. apply Z.ltb_lt in ISERR. first [clear -ISERR AC ND4 CEILF__ CEILM__ CEILP__ | clear -ISERR AC ND4]. lia. }
      destruct (PO Logic.I) as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & MI2 & ST2 & MU2 & WM2 & ERR2 & He).
      cbn [mremap_mem] in MI2, ST2 |- *.
      rewrite !unsigned_lit in ST2, MU2 by (keep_hyps CEILV sp blk bs n lo g b r bm ag rag k1 CEILF__ SLO SPR LOv; lia).
      replace (ret_pc (Z_to_bv 64 0x1a420)) with (Z_to_bv 64 0x1a420) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      (* [comment removed for export] *)
      apply rimplT_from_evt. step. step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      apply evt_done.
      assert (MR2 : rmrep st0 m2).
      { eapply (rmrep_transport_unowned st0 m1 m2 _ MR1 MU2 WM2).
        pose proof (rerrno_addr tp TP) as ETP.
        intros lo' hi' a [E1|[E1|[]]] Ha RFt; inversion E1; subst; destruct (rrepfoot_where2 st0 m1 a MR1 RFt) as [A1 A2];
          rewrite ?ETP in Ha; first [clear -Ha A1 A2 LOv SLO TBF CEILF__ CEILM__ CEILP__ | clear -Ha A1 A2 LOv SLO TBF]; unfold RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; ceil_facts; lia. }
      apply (FBOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2).
      * split; [exact MI2|]. split; [exact ST2|]. split; [exact MR2|].
        split. { eapply rauxv_ok_frame; [exact AUX1| exact MU2| exact WM2|]. rewrite (rerrno_addr tp TP). unfold RAUXV_CELL.
                 constructor; [cbn; first [clear -SLO SB LOv CEILF__ CEILM__ CEILP__ | clear -SLO SB LOv]; lia|]. constructor; [cbn; first [clear -TBF SB LOv SLO CEILF__ CEILM__ CEILP__ | clear -TBF SB LOv SLO]; lia| constructor]. }
        split. { eapply rw_cells_transport; [exact REPL1| exact MU2| exact WM2|]. rewrite (rerrno_addr tp TP). unfold RMREPLACED, RCTX. cbn. first [clear -TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -TBF LOv SLO]. lia. }
        split. { eapply rw_cells_transport; [exact CH1| exact MU2| exact WM2|]. rewrite (rerrno_addr tp TP). cbn. rewrite HAp.
                 rewrite STR in OS. first [clear -TBF LOv SLO TLSr OS Sp Hoff RBC OLDLEN EOLD EON SZ CEILF__ CEILM__ CEILP__ | clear -TBF LOv SLO TLSr OS Sp Hoff RBC OLDLEN EOLD EON SZ]. unfold UNIT, IB in *; ceil_facts. clearbody old on. lia. }
        split. { eapply rheap_pres_trans; [exact HP1|]. intros a Ha CA. split; [| apply WM2]. apply MU2. rewrite wa_unsigned by lia. rewrite (rerrno_addr tp TP). cbn.
                 destruct CA as [CA|[[CA [NS NE0]]|[(blk' & Hb' & Hab)|[CA NE]]]].
                 - first [clear -CA TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -CA TBF LOv SLO]. repeat split; try exact Logic.I; lia.
                 - first [clear -CA NE0 TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -CA NE0 TBF LOv SLO]. repeat split; try exact Logic.I; lia.
                 - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' _].
                   destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hin') as [(r' & Hr' & Kr' & A16' & AEND' & _) _ _].
                   destruct (WR _ _ Hr') as (_ & _ & _ & RBC' & RF'). pose proof (rreserved_tlsU _ _ RF'). pose proof (round_up_pg_ge (r_len r')).
                   first [clear -Hab A16' AEND' RBC' H H0 TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -Hab A16' AEND' RBC' H H0 TBF LOv SLO]. ceil_facts. repeat split; try exact Logic.I; lia.
                 - first [clear -CA NE TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -CA NE TBF LOv SLO]. repeat split; try exact Logic.I; lia. }
        split; [eexists; exact ERR2|].
        eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. rewrite (rerrno_addr tp TP). cbn. first [clear -TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -TBF LOv SLO]. lia.
      * rewrite A0, HAp. apply unsigned_lit. rewrite STR in OS. first [clear -OS Sp Hoff RBC OLDLEN RB0 EOLD EON SZ CEILF__ CEILM__ CEILP__ | clear -OS Sp Hoff RBC OLDLEN RB0 EOLD EON SZ]. clearbody old on. unfold UNIT, IB in *; ceil_facts. lia.
    + (* [comment removed for export] *)
      rewrite Cb in FX, PO. rewrite OLDLEN in FX, PO, OKA, EQN.
      pose proof (rarea_lr_lo st0 ag arg rag WF Hag Hrag) as LLg.
      assert (NEa : fst ag <> fst b) by (intros E2; rewrite E2, Hr in Hrag; assert (rag = r) as -> by congruence; exact (NKg Kr)).
      assert (GOLD : G + 40 <= old \/ old + on <= G).
      { destruct (DJ _ _ _ _ Hrag Hr NEa) as [D1|D1]; rewrite ?(lr_lo_group r Kr) in D1; rewrite EG, Cag; subst old on; first [clear -D1 LLg Hkg Sag0 Sag1 CEILF__ CEILM__ CEILP__ | clear -D1 LLg Hkg Sag0 Sag1]; unfold AREA_HDR, META_SIZE, NSLOTS in *; lia. }
      pose proof (SH _ _ Hr Kr) as [WRo _]. fold old in WRo. fold on in WRo.
      (* [comment removed for export] *)
      assert (KER : exists nb, mremap_val old x = nb /\ mremap_ret old x = Z_to_bv 64 nb
         /\ match x with MrErr _ => False | MrSame => nb = old | MrMoved a => nb = a /\ on < needed /\ (old + on <= a \/ a + needed <= old) end
         /\ 0 < nb /\ nb mod 4096 = 0 /\ nb + needed <= alloc_ceiling /\ ranges_free ref_reserved nb needed = true
         /\ (forall rid' r', s_regions st0 !! rid' = Some r' -> rid' <> fst b -> nb + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb)).
      { destruct (mremap_ok_cases st (fst b) old on needed (mremap_val old x) OKA ISERR) as [[Ez INP]|(NEz & Z0 & ZAL & ZC & ZRF)].
        - destruct x as [er| |na]; cbn [mremap_val] in Ez.
          + exfalso. cbn [mremap_val] in ISERR. rewrite (is_err_neg_errno er FX) in ISERR. discriminate.
          + exists old. cbn [mremap_val mremap_ret]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
            split; [exact RB0|]. split; [exact RBAL|].
            assert (GE : on <= needed -> old + needed <= alloc_ceiling /\ ranges_free (live_ranges_wo st (fst b)) (old + on) (needed - on) = true).
            { intros GE. destruct INP as [LE|X]; [exfalso; first [clear -LE GE EQN CEILF__ CEILM__ CEILP__ | clear -LE GE EQN]; lia| exact X]. }
            destruct (Z_lt_dec needed on) as [LT|NLT].
            * split; [first [clear -LT RBC CEILF__ CEILM__ CEILP__ | clear -LT RBC]; lia|]. split; [eapply (ranges_free_sub _ old on); [exact RF| lia| first [clear -LT CEILF__ CEILM__ CEILP__ | clear -LT]; lia| first [clear -ND4 CEILF__ CEILM__ CEILP__ | clear -ND4]; lia]|].
              intros rid' r' Hr' NE'. destruct (DJ _ _ _ _ Hr' Hr NE') as [D1|D1]; rewrite ?(lr_lo_group r Kr) in D1; subst old on; first [clear -D1 LT CEILF__ CEILM__ CEILP__ | clear -D1 LT]; lia.
            * destruct (GE ltac:(first [clear -NLT CEILF__ CEILM__ CEILP__ | clear -NLT]; lia)) as [CE RFW].
              split; [exact CE|]. split.
              { replace needed with (on + (needed - on)) by lia. apply ranges_free_app_pos; [apply ref_reserved_pos| first [clear -ON4096 CEILF__ CEILM__ CEILP__ | clear -ON4096]; lia| first [clear -NLT CEILF__ CEILM__ CEILP__ | clear -NLT]; lia| exact RF|].
                apply ranges_free_intro. intros b0 k0 HI. apply (ranges_free_In _ _ _ _ _ RFW). unfold live_ranges_wo. apply in_or_app. left.
                change (s_reserved st) with (s_reserved st0). rewrite Hres. exact HI. }
              intros rid' r' Hr' NE'. destruct (DJ _ _ _ _ Hr' Hr NE') as [D1|D1]; rewrite ?(lr_lo_group r Kr) in D1.
              { right. subst old on. first [clear -D1 CEILF__ CEILM__ CEILP__ | clear -D1]. lia. }
              pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc3.ranges_free_regions_wo st (fst b) _ _ rid' r' RFW Hr' NE') as D2.
              destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _). pose proof INV as (IR & _).
              pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc3.region_live_range_pos _ st0 L rid' r' IR Hr') as P2.
              unfold region_live_range in D2, P2. unfold lr_lo in D1 |- *. unfold PGSZ in D2, P2.
              destruct (r_kind r'); cbn in D1, D2, P2; cbn; subst old on; first [clear -D1 D2 P2 NLT CEILF__ CEILM__ CEILP__ | clear -D1 D2 P2 NLT]; lia.
          + exfalso. exact (proj2 (proj2 (proj2 FX)) Ez).
        - destruct x as [er| |na]; cbn [mremap_val] in NEz, Z0, ZAL, ZC, ZRF.
          + exfalso. cbn [mremap_val] in ISERR. rewrite (is_err_neg_errno er FX) in ISERR. discriminate.
          + exfalso. apply NEz. reflexivity.
          + assert (DJA : forall rid' r', s_regions st0 !! rid' = Some r' -> na + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= na).
            { intros rid' r' Hr'. pose proof (In_live_ranges st rid' r' Hr') as HI. unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
              destruct (r_kind r'); (pose proof (ranges_free_In _ _ _ _ _ ZRF HI) as D; first [clear -D CEILF__ CEILM__ CEILP__ | clear -D]; lia). }
            exists na. cbn [mremap_ret]. split; [reflexivity|]. split; [reflexivity|].
            split. { split; [reflexivity|]. split; [exact (proj1 FX)|]. pose proof (DJA _ _ Hr) as D. rewrite (lr_lo_group r Kr) in D. subst old on. first [clear -D CEILF__ CEILM__ CEILP__ | clear -D]. lia. }
            split; [exact Z0|]. split; [exact ZAL|]. split; [exact ZC|]. split.
            { apply ranges_free_intro. intros b0 k0 HI. apply (ranges_free_In _ _ _ _ _ ZRF). unfold live_ranges. apply in_or_app. left.
              change (s_reserved st) with (s_reserved st0). rewrite Hres. exact HI. }
            intros rid' r' Hr' _. exact (DJA _ _ Hr'). }
      destruct KER as (nb & EVAL & ERET & HX & NB0 & NBAL & NBC & RFN & DJN).
      rewrite EVAL.
      assert (NIMG : nb + needed <= 0x10000 \/ 0x55000 <= nb) by (apply (rreserved_disjoint1 _ _ RFN); first [clear -ND4 CEILF__ CEILM__ CEILP__ | clear -ND4]; lia).
      assert (GNEW : G + 40 <= nb \/ nb + needed <= G).
      { destruct (DJN _ _ Hrag NEa) as [D1|D1]; rewrite EG, Cag; first [clear -D1 LLg Hkg Sag0 Sag1 CEILF__ CEILM__ CEILP__ | clear -D1 LLg Hkg Sag0 Sag1]; unfold AREA_HDR, META_SIZE, NSLOTS in *; lia. }
      assert (IMGC : match x with MrErr _ => True | MrSame => img_clear old on needed | MrMoved a => img_clear a on needed end).
      { unfold img_clear. destruct x as [er| |na]; [exact Logic.I| rewrite <- HX| destruct HX as (Ena & _); rewrite <- Ena]; first [clear -NIMG CEILF__ CEILM__ CEILP__ | clear -NIMG]; lia. }
      destruct (PO IMGC) as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & MIA & STA & REST).
      rewrite !unsigned_lit in STA, REST by (keep_hyps CEILV sp blk bs n lo g b r bm ag rag k1 nb CEILF__ SLO SPR LOv; lia).
      assert (MW : munch [(bv_unsigned sp + -64 - 112, bv_unsigned sp + -64)] m1 m2 /\ wmono ssegs m1 m2).
      { destruct x as [er| |na]; [destruct HX| exact (conj (proj1 REST) (proj1 (proj2 REST)))| exact (conj (proj1 REST) (proj1 (proj2 REST)))]. }
      clear REST. destruct MW as [MU2 WM2].
      rewrite ERET. replace (ret_pc (Z_to_bv 64 0x1a420)) with (Z_to_bv 64 0x1a420) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      set (mA := mremap_mem old on needed x m2) in *.
      destruct (mremap_mem_facts m2 old on needed x nb RB0 ltac:(first [clear -ON4096 CEILF__ CEILM__ CEILP__ | clear -ON4096]; lia) ltac:(first [clear -ND4 CEILF__ CEILM__ CEILP__ | clear -ND4]; lia) RBC NB0 NBC HX) as (OUT & PRE & TL). fold mA in OUT, PRE, TL.
      assert (M12 : forall a, 0 <= a < 2^64 -> (a < bv_unsigned sp - 176 \/ bv_unsigned sp - 64 <= a) -> m2 (wa a) = m1 (wa a)).
      { intros a Ha Ho. apply MU2. rewrite wa_unsigned by exact Ha. cbn [outside]. split; [first [clear -Ho CEILF__ CEILM__ CEILP__ | clear -Ho]; lia| exact Logic.I]. }
      assert (WR2 : wr_at ssegs m2 old on).
      { destruct WRo as (W0 & W1 & W2). split; [exact W0|]. split; [exact W1|]. intros ii Hii. apply WM2. apply W2. exact Hii. }
      pose proof (mremap_mem_wr_at m2 old on needed x nb RB0 ltac:(first [clear -ON4096 CEILF__ CEILM__ CEILP__ | clear -ON4096]; lia) ltac:(first [clear -ND4 CEILF__ CEILM__ CEILP__ | clear -ND4]; lia) RBC NB0 NBC HX DRr NIMG WR2) as WRN. fold mA in WRN.
      assert (FR2 : rw_cells ssegs m2 (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6)).
      { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. split; [clear; lia| exact Logic.I]. }
      assert (MM2 : rw_cells ssegs m2 G [C8 (pw st0 (m_prev mr)); C8 (pw st0 (m_next mr)); C8 (wz (conc st0 b)); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))]).
      { eapply rw_cells_transport; [exact MM1| exact MU2| exact WM2|]. cbn. split; [first [clear -GC LOv SLO CEILF__ CEILM__ CEILP__ | clear -GC LOv SLO]; lia| exact Logic.I]. }
      apply (SUCC nb mA x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 NB0 NBAL NBC RFN DJN MIA STA).
      * eapply rrw_cells_agree'; [exact FR2|]. intros a Ha. cbn in Ha. apply OUT; ceil_facts; first [clear -Ha SPR LOv SLO RBC NBC CEILF__ CEILM__ CEILP__ | clear -Ha SPR LOv SLO RBC NBC]; lia.
      * eapply rrw_cells_agree'; [exact MM2|]. intros a Ha. cbn in Ha. apply OUT; ceil_facts; first [clear -Ha GC G0 GOLD GNEW CEILF__ CEILM__ CEILP__ | clear -Ha GC G0 GOLD GNEW]; lia.
      * apply rpres_except_of_eq. intros a Ha NC. subst FP. cbv beta in NC.
        rewrite (OUT a Ha) by (first [clear -NC Ha CEILF__ CEILM__ CEILP__ | clear -NC Ha]; lia). apply M12; [exact Ha| first [clear -NC Ha LOv SLO CEILF__ CEILM__ CEILP__ | clear -NC Ha LOv SLO]; lia].
      * intros A k HA0 HK DO DN AC a Ha. ceil_facts.
        rewrite (OUT a) by (first [clear -Ha HA0 HK DO DN AC CEILF__ CEILM__ CEILP__ | clear -Ha HA0 HK DO DN AC]; lia). apply M12; first [clear -Ha HA0 AC LOv SLO CEILF__ CEILM__ CEILP__ | clear -Ha HA0 AC LOv SLO]; lia.
      * intros o Ho. rewrite (PRE o) by (first [clear -Ho CEILF__ CEILM__ CEILP__ | clear -Ho]; lia). ceil_facts. apply M12; first [clear -Ho RBC RB0 LOv SLO CEILF__ CEILM__ CEILP__ | clear -Ho RBC RB0 LOv SLO]; lia.
      * exact WRN.
Qed.
End Sz1.
Theorem rbig63_proof : ltac:(let t := eval cbv delta [rbig63_proof__stmt] in rbig63_proof__stmt in exact t).
Proof using Type. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s LB blk off bs n lo B g b ai r i v3 rsv t2 a0 a5 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'rbig63_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

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
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Image OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ZBridge OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.SFModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_malloc_free__MA.F_malloc_fast OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.F_free_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocKit_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A3 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocBlocks OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocHINV OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.MallocFacts_A OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_B OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.MallocFacts_Bpres OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocKit_A2__MA.MallocKit_A2 OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_A__MA.Malloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_P__MA.F_free OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.F_free_K.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocRep.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocKit_A.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocKit_B.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMallocKit_B2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RMallocKit_A2.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mm_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_free_spec.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_reallocA.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RF_reallocB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_reallocC.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_mremap.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free_K__S3.RF_realloc63R.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc63.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_mm_syscalls__S3.RF_realloc63M.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.STree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Malloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.KInv__Spec.MallocRe OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MallocCtrl OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.ProgFull OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Inv OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Kit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Fuel__Spec.MI_Shadow OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Ledger__Spec.MI_Ledger.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_invR.
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac ulia := unfold UNIT, IB in *; ceil_facts; lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Lemma pw_conc_ext (st st' : mstate) p : (forall q, conc st' q = conc st q) -> pw st' p = pw st p.
Proof using CEILV MSECV. pin_using (fun (CEILV MSECV : unit) => tt). ceil_facts. msec_facts. intros H. destruct p as [q|]; unfold pw, oconc; [rewrite H|]; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rbig63_proof__stmt : Prop := rbig63_stmt.
Section Sz1.
Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s LB blk off bs n lo B g b ai r i v3 rsv t2 a0 a5 t3 t4 t5 t6 : ltac2:(SecDiet.SzSec.tyM 'rbig63_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
Lemma rbig63_proof__body : ltac2:(SecDiet.SzSec.bodyP 'rbig63_proof__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  intros st0 st mr c0 pf e P E AR Hin Hoff HA BL SL Hgh FB Hr Kr SC63 LI0 ML0 I V31 C3 V3R OS SZ N RSVE RSV0 SB LO SLO TP A0 MU1 WM1
         (MI1 & ST1 & MR1 & AUX1 & REPL1 & CH1 & HP1 & [errv1 ERR1] & FR1) FBOK.
  unfold RREALLOC_STACK in SLO. unfold MMAP_THRESHOLD in N.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof LO as LOv. ceil_facts. pose proof the_tb_facts as TBF.
  assert (I0 : i = 0) by lia. assert (V0 : Z.land v3 31 = 0) by lia.
  pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv3.areach_cinv_proof _ _ AR) as C.
  pose proof (ci_gmetas _ _ C b g ltac:(exists ai; exact Hgh)) as GO.
  destruct (go_region _ _ _ GO) as (r_ & Hr_ & _ & B0 & _ & SPAN & TOP). rewrite Hr in Hr_. assert (r_ = r) as -> by congruence.
  destruct (TOP ltac:(change (get_meta_rec st0 g) with mr; lia)) as [Sb OLDLEN]. change (get_meta_rec st0 g) with mr in OLDLEN, SPAN.
  pose proof (go_mem _ _ _ GO) as Hmem. change (get_meta_rec st0 g) with mr in Hmem.
  pose proof (go_slot _ _ _ GO) as MSg. pose proof (go_maplen _ _ _ GO) as MLR. change (get_meta_rec st0 g) with mr in MLR.
  pose proof (go_freeable _ _ _ GO) as FRB. change (get_meta_rec st0 g) with mr in FRB.
  pose proof (go_avail _ _ _ GO) as AVR. pose proof (go_freed _ _ _ GO) as FDR. change (get_meta_rec st0 g) with mr in AVR, FDR.
  assert (STR : get_stride mr = m_maplen mr * 4096 - 16).
  { unfold get_stride. rewrite LI0. replace (m_maplen mr =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity. }
  pose proof MR1 as (WF & CX & GL & ARR & GR & SH). pose proof WF as (Hres & WR & DJ & WA & WG).
  destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & RF).
  set (old := r_base r) in *. set (on := round_up_pg (r_len r)) in *.
  assert (EP : P = old + snd pf) by reflexivity. assert (EE : E = old + snd e) by reflexivity.
  assert (EOLD : old = r_base r) by reflexivity. assert (EON : on = round_up_pg (r_len r)) by reflexivity.
  (* [comment removed for export] *)
  assert (Fp : fst pf = fst b) by (subst pf c0; cbn; symmetry; exact FB).
  assert (Sc : snd c0 = 16).
  { destruct (ki_slts _ _ _ (KINV_of_CINV _ _ C) _ _ _ SL) as (_ & Ec & _). fold c0 in Ec. rewrite Ec, (slot_start'_mem _ b i Hmem). cbn. rewrite Sb, I0. unfold UNIT. lia. }
  assert (Sp : snd pf = 16 + 16 * off) by (subst pf; cbn; rewrite Sc; unfold UNIT; lia).
  assert (Se : snd e = on - 4) by (subst e; cbn [aadd snd]; rewrite V0, STR, Sb, OLDLEN; unfold UNIT, IB; lia).
  assert (Cc : conc st0 c0 = old + 16) by (rewrite (conc_region' st0 c0 r) by (rewrite <- FB; exact Hr); rewrite Sc; reflexivity).
  assert (HAp : blk_addr blk = old + snd pf) by (rewrite HA, Cc, Sp; unfold UNIT; lia).
  assert (Cb : conc st0 b = old) by (rewrite (conc_region' st0 b r Hr), Sb; subst old; lia).
  assert (ON4096 : 4096 <= on) by (subst on; rewrite <- OLDLEN; lia).
  pose proof (rreserved_disjoint1 _ _ RF ltac:(lia)) as DRr. pose proof (rreserved_tlsU _ _ RF) as TLSr.
  (* [comment removed for export] *)
  apply rimplT_guard; intros _.
  cbv zeta. cbn [aadd fst snd]. rewrite V0, Z.mul_0_r, Z.add_0_r.
  set (needed := round_up_pg (n + (snd pf - (snd b + UNIT)) + UNIT + IB)).
  assert (END : needed = round_up_pg (n + (P - (old + 16)) + 20)) by (subst needed P; rewrite Sb; unfold UNIT, IB; f_equal; lia).
  pose proof (round_up_pg_alt (n + (P - (old + 16)) + 20)) as NDv. rewrite <- END in NDv.
  assert (NDR : n + (P - (old + 16)) + 20 <= needed < n + (P - (old + 16)) + 20 + 4096) by (rewrite NDv; Z.div_mod_to_equations; lia).
  assert (NDAL : needed mod 4096 = 0) by (rewrite NDv; Z.div_mod_to_equations; (keep_hyps CEILV TB n b r r1 q r0 q0 H H0 H4; lia)).
  assert (ND4 : 4096 <= needed) by (first [clear -NDR N EP Sp Hoff CEILF__ CEILM__ CEILP__ | clear -NDR N EP Sp Hoff]; lia).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  assert (CB0 : conc st (fst b, 0) = old) by (rewrite (conc_region' _ (fst b, 0) r) by (cbn [fst]; exact Hr); cbn [snd]; subst old; lia).
  rewrite CB0.
  pose proof (rmeta_slot_bounds st0 m1 g MR1 MSg) as (G0 & GC & GIMG & _ & _).
  set (G := conc st0 g) in *.
  pose proof (rmrep_meta_chunk st0 m1 g MR1 MSg) as MM1. fold G mr in MM1. unfold meta_cells in MM1. rewrite Hmem in MM1.
  change (pw st0 (Some b)) with (wz (conc st0 b)) in MM1.
  pose proof (go_li _ _ _ GO) as GLI. pose proof (go_sc _ _ _ GO) as GSC. change (get_meta_rec st0 g) with mr in GLI, GSC.
  assert (WRD : 0 <= meta_word mr < 2^64) by (unfold meta_word; lia).
  assert (WLO : Z.land (meta_word mr) 4095 = m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr).
  { change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. unfold meta_word. rewrite SC63, LI0, FRB. Z.div_mod_to_equations. (keep_hyps CEILV TB n g b r q r0 H H0; lia). }
  pose proof (ci_ticks _ _ C) as TK0. assert (TKt : ticks_ok st) by (apply ticks_ok_set_tick; [cbn; lia| exact TK0]).
  assert (MRt : rmrep st m1) by (apply rmrep_set_tick; exact MR1).
  (* [comment removed for export] *)
  assert (GPR : s_metas st0 !! g = Some mr).
  { destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _). pose proof INV as (_ & _ & _ & _ & IG & _ & _).
    pose proof (g_present _ _ _ _ _ _ (ig_ok _ _ _ IG g b ai Hgh)) as GP. subst mr. unfold get_meta_rec.
    destruct (s_metas st0 !! g) as [mr0|]; [reflexivity| exfalso; apply GP; reflexivity]. }
  (* [comment removed for export] *)
  destruct (areach_blk_slot_clear st0 LB blk AR Hin) as (gm & bm & im & rm & offm & HOm & HIm & ESL & SLm & Hrm & Krm & EAm & OFm & SZm & FITm & GCLR & BCLR).
  fold c0 in ESL, SLm. rewrite SL in SLm. assert (gm = g /\ im = i) as [-> ->] by (split; congruence). clear SLm.
  assert (Ebm : fst bm = fst b) by (rewrite FB, ESL; reflexivity).
  rewrite Ebm, Hr in Hrm. assert (rm = r) as -> by congruence.
  assert (SS0 : sstart (MI_Inv.MR st0 g) i = snd c0) by (rewrite ESL; reflexivity). change (MI_Inv.MR st0 g) with mr in SS0, GCLR, BCLR.
  assert (ONLYG : forall b' gh, s_groups st0 !! b' = Some gh -> fst b' = fst b -> b' = b).
  { intros b' gh Hb' Hf'. pose proof (GCLR b' gh Hb' ltac:(rewrite Ebm; exact Hf')) as X. rewrite SS0, Sc, STR, OLDLEN in X.
    destruct (WG b' gh Hb') as (rb & Hrb & _ & B0' & B16' & _). rewrite Hf', Hr in Hrb. assert (rb = r) as -> by congruence. fold on in B16'.
    destruct b' as [b'1 b'2]. destruct b as [b1 b2]. cbn [fst snd] in *. subst b'1. f_equal. unfold UNIT in X. (keep_hyps CEILV TB off n g r b1 b2 bm b'2 Sb X B0' B16'; lia). }
  pose proof (rmem_only st0 LB (fst b) b g ai C Hgh ONLYG) as MEMG.
  pose proof (rptrs_ctx_norid st0 LB 0 (fst b) r m1 (KINV_of_CINV _ _ C) MR1 Hr Kr (ci_mp _ _ C)) as PTX0.
  (* [comment removed for export] *)
  pose proof MSg as (ag & arg & kg & Hag & Hkg & Eg).
  destruct (rarea_conc st0 ag arg WF Hag) as (rag & Hrag & Cag & Sag0 & Sag1 & SagL & NKg & RBg0 & RBgA & RBgC).
  destruct (WR _ _ Hrag) as (_ & _ & _ & _ & RFg). pose proof (rreserved_tlsU _ _ RFg) as GTLS. pose proof (round_up_pg_ge (r_len rag)) as RUg.
  assert (EG : G = conc st0 ag + AREA_HDR + META_SIZE * kg) by (subst G; rewrite Eg, conc_aadd by (rewrite Hrag; eauto); lia).
  (* [comment removed for export] *)
  assert (LBS : length bs = Z.to_nat (blk_size blk)) by (destruct CH1 as [[Hwf _] _]; cbn in Hwf; exact (proj1 Hwf)).
  pose proof (rw_cells_bytes_at _ _ _ _ CH1) as BS1. cbn [cells_bytes cbytes] in BS1. rewrite app_nil_r in BS1.
  set (k1 := Z.to_nat (Z.min (blk_size blk) n)).
  assert (K1R : Z.of_nat k1 <= n /\ Z.of_nat k1 <= blk_size blk /\ (k1 <= Z.to_nat n)%nat) by (subst k1; first [clear -N SZ CEILF__ CEILM__ CEILP__ | clear -N SZ]; lia).
  assert (LK1 : length (firstn k1 bs) = k1) by (rewrite length_firstn, LBS; subst k1; first [clear -N SZ CEILF__ CEILM__ CEILP__ | clear -N SZ]; lia).
  assert (EK1 : k1 = Z.to_nat (Z.min (blk_size blk) n)) by reflexivity. clearbody k1.
  (* [comment removed for export] *)
  set (FP := fun nb a => lo <= a < bv_unsigned sp \/ old <= a < old + on \/ nb <= a < nb + needed \/ G + 16 <= a < G + 40).
  assert (FINAL : forall (nb : Z) (stF : mstate) (rF : region) (m' : mem) (x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
    rmrep stF m' -> mem_inv usegs m' -> stk usegs m' lo (bv_unsigned sp + -64) ->
    rw_cells usegs m' (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6) ->
    s_regions stF !! (fst b) = Some rF -> r_base rF = nb -> r_kind rF = RKGroup -> needed <= round_up_pg (r_len rF) ->
    ctx stF = ctx st0 -> (forall q, fst q <> fst b -> conc stF q = conc st0 q) ->
    rpres_except (FP nb) m1 m' ->
    bytes_at usegs m' (nb + snd pf) (firstn k1 bs) ->
    0 < nb -> nb mod 4096 = 0 -> nb + needed <= alloc_ceiling -> ranges_free ref_reserved nb needed = true ->
    (forall rid' r', s_regions st0 !! rid' = Some r' -> rid' <> fst b -> nb + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb) ->
    rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B (stF, Some pf) s
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -64)) + 64)) gp tp x0 x1 x2 s0 s1 (Z_to_bv 64 (nb + snd pf)) y1 y2 y3 y4 y5 y6 y7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x3 x4 x5 x6) F (ret_pc ra) fc None m' (seg_rom usegs))).
  { intros nb stF rF m' x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 MRF MIF STF FRF RGF RBF KF NDF CTF CNF PEF BSF NB0 NBAL NBC RFN DJN.
    rewrite unsigned_lit by lia. replace (bv_unsigned sp + -64 + 64) with (bv_unsigned sp) by lia. rewrite Z_to_bv_bv_unsigned.
    pose proof (rreserved_disjoint1 _ _ RFN ltac:(lia)) as NIMG. pose proof (rreserved_tlsU _ _ RFN) as NTLS. pose proof (rreserved_disjoint _ _ RFN) as (_ & _ & NI3 & NI4).
    pose proof (rreserved_disjoint _ _ RF) as (_ & _ & OI3 & OI4).
    assert (CPF : conc stF pf = nb + snd pf) by (rewrite (conc_region' stF pf rF) by (rewrite Fp; exact RGF); rewrite RBF; reflexivity).
    (* [comment removed for export] *)
    assert (NFP_hi : forall a, bv_unsigned sp <= a -> ~ FP nb a).
    { intros a Ha. subst FP; cbv beta. first [clear -Ha RBC NBC GC LOv SLO CEILF__ CEILM__ CEILP__ | clear -Ha RBC NBC GC LOv SLO]. ceil_facts. intros [X|[X|[X|X]]]; lia. }
    assert (NFP_img : forall a, 0x22000 <= a < 0x56000 -> ~ FP nb a).
    { intros a Ha. subst FP; cbv beta. first [clear -Ha DRr NIMG GIMG LOv SLO ON4096 ND4 CEILF__ CEILM__ CEILP__ | clear -Ha DRr NIMG GIMG LOv SLO ON4096 ND4]. intros [X|[X|[X|X]]]; lia. }
    assert (NFP_tls : forall a, the_tb <= a < the_tb + 4096 -> ~ FP nb a).
    { intros a Ha. subst FP; cbv beta. rewrite EG, Cag. first [clear -Ha TLSr NTLS GTLS TBF LOv SLO Sag0 Sag1 Hkg RUg CEILF__ CEILM__ CEILP__ | clear -Ha TLSr NTLS GTLS TBF LOv SLO Sag0 Sag1 Hkg RUg]. unfold AREA_HDR, META_SIZE, NSLOTS in *; ceil_facts. intros [X|[X|[X|X]]]; lia. }
    assert (NFP_blk : forall blk' a, In blk' (lbrm LB blk) -> blk_addr blk' <= a < blk_addr blk' + blk_size blk' -> ~ FP nb a).
    { intros blk' a Hb' Hab. unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' NEQ].
      assert (NE' : blk_slot blk' <> blk_slot blk) by (intros EQ; rewrite EQ, aptr_eqb_refl in NEQ; cbn in NEQ; exact NEQ).
      destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hin') as [(r' & Hr' & Kr' & A16' & AEND' & _) _ _].
      subst FP; cbv beta. rewrite EG, Cag.
      destruct (N.eq_dec (fst (blk_slot blk')) (fst b)) as [EF|NF].
      - specialize (BCLR blk' Hin' NE' ltac:(rewrite Ebm; exact EF)). rewrite SS0, Sc, STR, OLDLEN in BCLR.
        rewrite EF, Hr in Hr'. assert (r' = r) as -> by congruence. fold old in A16', AEND', BCLR. fold on in A16', AEND'.
        first [clear -BCLR Hab A16' AEND' CEILF__ CEILM__ CEILP__ | clear -BCLR Hab A16' AEND']. unfold UNIT, IB in *. intros _. lia.
      - pose proof (lr_lo_group r Kr) as LR. pose proof (lr_lo_group r' Kr') as LR'. pose proof (round_up_pg_ge (r_len r')) as RU'.
        destruct (WR _ _ Hr') as (RB0' & _ & _ & RBC' & _).
        assert (NEa : fst (blk_slot blk') <> fst ag) by (intros E2; rewrite E2, Hrag in Hr'; assert (r' = rag) as -> by congruence; exact (NKg Kr')).
        pose proof (rarea_lr_lo st0 ag arg rag WF Hag Hrag) as LLg.
        destruct (DJ _ _ _ _ Hr' Hr NF) as [D1|D1]; destruct (DJN _ _ Hr' NF) as [D2|D2]; destruct (DJ _ _ _ _ Hr' Hrag NEa) as [D3|D3];
          first [clear -Hab A16' AEND' LR LR' RU' RB0' RBC' LLg D1 D2 D3 LOv SLO Sag0 Sag1 Hkg RUg CEILF__ CEILM__ CEILP__ | clear -Hab A16' AEND' LR LR' RU' RB0' RBC' LLg D1 D2 D3 LOv SLO Sag0 Sag1 Hkg RUg]; unfold AREA_HDR, META_SIZE, NSLOTS in *; ceil_facts; intros [X|[X|[X|X]]]; lia. }
    unfold rrfinQ. cbn [fst snd oconc]. rewrite CPF. exists m', errv1. do 14 eexists.
    split; [reflexivity|]. split; [exact MIF|].
    split. { replace (bv_unsigned sp) with (bv_unsigned sp + -64 + Z.of_nat (cells_size (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6))) by (cbn; lia).
             eapply stk_release; [exact STF| exact FRF| first [clear -SLO CEILF__ CEILM__ CEILP__ | clear -SLO]; lia]. }
    split. { eapply rpres_except_rw_cells; [exact PEF| exact ERR1|]. rewrite (rerrno_addr tp TP). change (Z.of_nat (cells_size [C4 errv1])) with 4.
             intros a Ha. apply NFP_tls. first [clear -Ha TBF CEILF__ CEILM__ CEILP__ | clear -Ha TBF]. lia. }
    split. { eapply rauxv_ok_pres; [exact AUX1| exact PEF| intros a Ha; apply NFP_hi; first [clear -Ha SB CEILF__ CEILM__ CEILP__ | clear -Ha SB]; lia| intros a Ha; apply NFP_img; unfold RAUXV_CELL in Ha; first [clear -Ha CEILF__ CEILM__ CEILP__ | clear -Ha]; lia]. }
    split; [exact MRF|].
    split. { eapply OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.F_malloc_big.brk_link_ps_ext; [| | exact BL].
             - rewrite CTF. reflexivity.
             - intros brid boff HB. apply CNF. cbn [fst]. intros E2. destruct (ci_bk _ _ C brid boff HB) as (rb & Hrb & Kb). rewrite E2, Hr in Hrb.
               assert (rb = r) as -> by congruence. rewrite Kr in Kb. discriminate. }
    split. { eapply rheap_pres_trans; [exact HP1|]. intros a Ha CA. apply PEF; [exact Ha|].
             destruct CA as [CA|[[CA NS]|[(blk' & Hb' & Hab)|[CA NE]]]]; [apply NFP_hi; exact CA| apply NFP_img; exact CA| exact (NFP_blk blk' a Hb' Hab)| apply NFP_tls; exact CA]. }
    split. { eapply rpres_except_rw_cells; [exact PEF| exact REPL1|]. change (Z.of_nat (cells_size [C4 (Z_to_bv 64 0)])) with 4. intros a Ha. apply NFP_img. unfold RMREPLACED, RCTX in Ha. first [clear -Ha CEILF__ CEILM__ CEILP__ | clear -Ha]. lia. }
    split; [reflexivity|]. split; [reflexivity|].
    split. { unfold rblock_range. split; [first [clear -NB0 Sp Hoff CEILF__ CEILM__ CEILP__ | clear -NB0 Sp Hoff]; lia|]. split; [rewrite Sp; first [clear -NBAL Hoff CEILF__ CEILM__ CEILP__ | clear -NBAL Hoff]; Z.div_mod_to_equations; lia|]. split; [first [clear -N CEILF__ CEILM__ CEILP__ | clear -N]; lia|].
             first [clear -NBC NIMG NTLS NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NBC NIMG NTLS NDR EP Sp Hoff N]. ceil_facts. lia. }
    destruct (ruser_chunk stF m' pf rF n MRF ltac:(rewrite Fp; exact RGF) KF ltac:(first [clear -Sp Hoff CEILF__ CEILM__ CEILP__ | clear -Sp Hoff]; lia) ltac:(first [clear -NDF NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDF NDR EP Sp Hoff N]; lia) ltac:(first [clear -N CEILF__ CEILM__ CEILP__ | clear -N]; lia)) as (J & JCH).
    rewrite CPF in JCH. exists (skipn k1 J).
    pose proof (rw_cells_CB_prefix_agree m' (nb + snd pf) (Z.to_nat n) J (firstn k1 bs) JCH BSF ltac:(rewrite LK1; exact (proj2 (proj2 K1R)))) as CH'.
    rewrite LK1 in CH'. replace (Z.to_nat (n - Z.min (blk_size blk) n)) with (Z.to_nat n - k1)%nat by (rewrite EK1; first [clear -N SZ CEILF__ CEILM__ CEILP__ | clear -N SZ]; lia). rewrite <- EK1. exact CH'. }
  (* [comment removed for export] *)
  set (stH := havoc pf (needed - snd pf) st).
  destruct (rmrep_havoc st m1 pf (needed - snd pf) MRt TKt) as [MRH TKH]. fold stH in MRH, TKH.
  assert (RGH : s_regions stH = s_regions st0) by (subst stH; rewrite s_regions_havoc; reflexivity).
  assert (CGH : forall q, conc stH q = conc st0 q) by (intros q; unfold conc, get_region; rewrite RGH; reflexivity).
  assert (HAVT : forall u hl, r_hav (get_shadow st (fst pf)) !! u = Some hl -> hl_ticks hl (s_tick st)).
  { intros u hl Hu ch Hch. exact (proj1 (sh_ticks_of_ticks_ok st (fst pf) TKt) u hl ch Hu Hch). }
  assert (HK3H : cell_read (get_shadow stH (fst pf)) (snd pf - 3) = Known v3).
  { subst stH. rewrite (cell_read_havoc_out pf (needed - snd pf) st ltac:(rewrite Sp; clear; Z.div_mod_to_equations; (keep_hyps off q r H H0; lia)) ltac:((keep_hyps CEILV blk bs n g b r bm ag rag k1 N NDR; lia)) HAVT (fst pf, snd pf - 3)) by (cbn [fst snd]; (keep_hyps CEILV blk bs n g b r bm ag rag k1; lia)).
    cbn [fst snd]. exact C3. }
  assert (NOKH : forall o v, snd pf <= o < needed -> cell_read (get_shadow stH (fst b)) o = Known v -> False).
  { intros o v Ho Hc. subst stH.
    destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _). pose proof INV as (_ & _ & _ & _ & _ & _ & ISH).
    destruct (cell_read_havoc_in pf (needed - snd pf) st ltac:(rewrite Sp; clear; Z.div_mod_to_equations; lia) ltac:(lia) HAVT (fst b, o) ltac:(cbn [fst]; symmetry; exact Fp) ltac:(cbn [snd]; lia)) as [h Hh].
    - intros v' tk Hc'. cbn [snd] in Hc'. change (s_tick st) with (N.succ (s_tick st0)).
      change (get_shadow st (fst pf)) with (get_shadow st0 (fst pf)) in Hc'. unfold get_shadow in Hc'.
      destruct (s_shadow st0 !! fst pf) as [sh|] eqn:Esh; [| cbn in Hc'; rewrite lookup_empty in Hc'; discriminate].
      cbn in Hc'. pose proof (proj1 (ish_ticks _ _ ISH (fst pf) sh Esh) o v' tk Hc') as [_ T]. first [clear -T CEILF__ CEILM__ CEILP__ | clear -T]. lia.
    - cbn [fst snd] in Hh. rewrite Hh in Hc. discriminate. }
  assert (PTXH : ptrs_ctx_in (fun x => x <> fst b) stH).
  { eapply ptrs_ctx_in_ext; [| | | | exact PTX0]; subst stH st; unfold ctx; rewrite ?s_ctx_havoc, ?s_metas_havoc, ?s_areas_havoc, ?s_groups_havoc; reflexivity. }
  assert (HghH : s_groups stH !! b = Some (mkGhdr (Some g) ai)) by (subst stH; rewrite s_groups_havoc; exact Hgh).
  assert (ONLYGH : forall b' gh, s_groups stH !! b' = Some gh -> fst b' = fst b -> b' = b) by (subst stH; rewrite s_groups_havoc; exact ONLYG).
  assert (MEMGH : forall q b'', m_mem (get_meta_rec stH q) = Some b'' -> fst b'' = fst b -> q = g).
  { intros q b'' H1 H2. apply (MEMG q b''); [| exact H2]. subst stH. unfold get_meta_rec in H1 |- *. rewrite s_metas_havoc in H1. exact H1. }
  assert (MSgH : meta_slot stH g) by (unfold meta_slot; subst stH; rewrite s_areas_havoc; exact MSg).
  assert (HmemH : m_mem (get_meta_rec stH g) = Some b) by (subst stH; unfold get_meta_rec; rewrite s_metas_havoc; exact Hmem).
  assert (GRH : get_meta_rec stH g = mr) by (subst stH mr; unfold get_meta_rec; rewrite s_metas_havoc; reflexivity).
  (* [comment removed for export] *)
  assert (SUCC : forall (nb : Z) (mA : mem) (x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 : word),
    0 < nb -> nb mod 4096 = 0 -> nb + needed <= alloc_ceiling -> ranges_free ref_reserved nb needed = true ->
    (forall rid' r', s_regions st0 !! rid' = Some r' -> rid' <> fst b -> nb + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb) ->
    mem_inv usegs mA -> stk usegs mA lo (bv_unsigned sp + -64) ->
    rw_cells usegs mA (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6) ->
    rw_cells usegs mA G [C8 (pw st0 (m_prev mr)); C8 (pw st0 (m_next mr)); C8 (wz (conc st0 b)); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))] ->
    rpres_except (FP nb) m1 mA ->
    (forall A k, 0 <= A -> 0 <= k -> (A + k <= old \/ old + on <= A) -> (A + k <= nb \/ nb + needed <= A) -> A + k <= alloc_ceiling -> agree_on m1 mA A k) ->
    (forall o, 0 <= o < Z.min on needed - 4 -> mA (wa (nb + o)) = m1 (wa (old + o))) ->
    wr_at usegs mA nb needed ->
    rimplT m (ret (big_resize st g (fst b) nb needed pf n 0, Some pf)) s
      (fun res s' msf => rrfinQ m st0 s ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB blk bs n lo B res s' msf)
      (MS (mkR (Z_to_bv 64 0x1abe0) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp x0 x1 x2 (Z_to_bv 64 needed) (wz G) (Z_to_bv 64 nb) y1 y2 y3 y4 y5 y6 y7
               (Z_to_bv 64 (blk_addr blk + blk_size blk)) (Z_to_bv 64 (P - (old + 16))) (Z_to_bv 64 4095) a0 (Z_to_bv 64 n) s7 s8 s9 s10 s11 x3 x4 x5 x6)
          F (Z_to_bv 64 0x1abe0) fc None mA (seg_rom usegs))).
  { intros nb mA x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 NB0 NBAL NBC RFN DJN MIA STA FRA MMA PEA AGA CPY WRN.
    pose proof (rreserved_disjoint1 _ _ RFN ltac:(lia)) as NIMG.
    apply rimplT_ret.
    (* [comment removed for export] *)
    step. step. step. step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by (ceil_facts; lia). ceil_facts. first [clear -K NBC ND4 CEILF__ CEILM__ CEILP__ | clear -K NBC ND4]. lia. }
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rrealloc_big63_stores _ _ gp tp _ _ _ _ (wz G) _ _ (Z_to_bv 64 nb) _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc mA
                G nb (P - (old + 16)) needed n (m_avail mr) (m_freed mr) (meta_word mr));
        [exact MMA| exact MIA| (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb G0; lia)| ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb GC; lia)| exact NB0| exact NBC| ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb CEILM__ ND4 NB0 NBC; lia)| exact NDAL
        | first [clear -EP Sp Hoff CEILF__ CEILM__ CEILP__ | clear -EP Sp Hoff]; (keep_hyps CEILV off r Hoff Sp; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb N; lia)| first [clear -NDR CEILF__ CEILM__ CEILP__ | clear -NDR]; (keep_hyps CEILV n b r NDR; lia)| exact WRD| apply wz_unsigned; ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 nb CEILM__ G0 GC; lia)| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    intros msB (m3 & -> & MU3 & WM3 & MI3 & MC3). rewrite WLO in MC3.
    (* [comment removed for export] *)
    destruct (rl_rmrep stH m1 mA m3 g b pf ai r nb needed G MRH TKH ltac:(rewrite RGH; exact Hr) Kr HghH Sb ONLYGH MEMGH MSgH ltac:(rewrite CGH; reflexivity) HmemH PTXH Fp
                ltac:(subst on; rewrite <- OLDLEN; rewrite STR in OS; first [clear -Sp Hoff OS NDR EP N SZ CEILF__ CEILM__ CEILP__ | clear -Sp Hoff OS NDR EP N SZ]; unfold UNIT, IB in *; lia) NOKH
                ltac:(exact ON4096 || (first [clear -ON4096 CEILF__ CEILM__ CEILP__ | clear -ON4096]; lia)) NB0 NBAL ND4 NDAL NBC RFN ltac:(rewrite RGH; exact DJN))
      as [MRR TKR].
    - intros A k HA0 K0 DO DN AC. exact (AGA A k HA0 K0 DO DN AC).
    - intros o Ho. apply CPY. subst on. rewrite <- OLDLEN. rewrite STR in OS. first [clear -Ho Sp Hoff OS NDR EP N SZ OLDLEN CEILF__ CEILM__ CEILP__ | clear -Ho Sp Hoff OS NDR EP N SZ OLDLEN]. unfold UNIT, IB in *. lia.
    - exact WRN.
    - exact MU3.
    - exact WM3.
    - rewrite GRH. rewrite !(pw_conc_ext st0 stH _ CGH).
      replace (meta_word (m_set_maplen (needed / 4096) mr)) with (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + needed); [exact MC3|].
      assert (E4 : 4096 * (needed / 4096) = needed) by (first [clear -NDAL ND4 CEILF__ CEILM__ CEILP__ | clear -NDAL ND4]; Z.div_mod_to_equations; lia).
      unfold meta_word, m_set_maplen. cbn [m_last_idx m_freeable m_sizeclass m_maplen].
      change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
      rewrite Z.mod_small by (ceil_facts; first [clear -NBC ND4 NB0 CEILF__ CEILM__ CEILP__ | clear -NBC ND4 NB0]; Z.div_mod_to_equations; lia). first [clear -E4 CEILF__ CEILM__ CEILP__ | clear -E4]; lia.
    - (* [comment removed for export] *)
      set (st2R := upd_meta g (m_set_maplen (needed / 4096)) (upd_region (fst b) (fun rg => mkRegion (r_kind rg) nb needed) stH)) in *.
      set (rN := mkRegion (r_kind r) nb needed).
      assert (HrN : s_regions st2R !! fst pf = Some rN) by (rewrite Fp; subst st2R rN; apply (rl_lookup_new stH g b r nb needed); rewrite RGH; exact Hr).
      replace (nb + 16 + (P - (old + 16))) with (r_base rN + snd pf) by (cbn [r_base rN]; first [clear -EP CEILF__ CEILM__ CEILP__ | clear -EP]; lia).
      replace (Z_to_bv 64 (nb + needed - 4 + 4)) with (Z_to_bv 64 (r_base rN + snd (fst b, needed - 4) + 4)) by (cbn [snd r_base rN]; f_equal; lia).
      replace (Z_to_bv 64 (nb + needed - 4 - (r_base rN + snd pf) - n)) with (Z_to_bv 64 (snd (fst b, needed - 4) - snd pf - n)) by (cbn [snd r_base rN]; f_equal; lia).
      replace (Z_to_bv 64 (nb + needed - 4)) with (Z_to_bv 64 (r_base rN + snd (fst b, needed - 4))) by (cbn [snd r_base rN]; f_equal; lia).
      unfold big_resize, resize63. change IB with 4.
      rewrite (havoc_upd_comm pf (needed - snd pf) g _ (fst b) _ st r Hr). fold stH. fold st2R.
      replace (set_size pf (fst b, needed - 4) n 0 (wr8 (fst b, needed - 4) 0 st2R))
         with (set_size pf (fst b, needed - 4) n (Z.land v3 31) (wr8 (fst b, needed - 4) 0 st2R)) by (rewrite V0; reflexivity).
      rewrite set_size_land31.
      eapply evt_mono.
      { eapply (rrealloc_setsize63_walk _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m3 m3 lo st2R pf (fst b, needed - 4) rN v3 n
                  ra s0 s1 s2 s3 s4 s5 s6 (fun a => a = r_base rN + snd pf - 3 \/ r_base rN + snd pf + n <= a < r_base rN + snd (fst b, needed - 4) + 1));
          first [exact MRR| exact MI3| exact TKR| exact HrN| idtac].
        - intros a Ha. exact Ha.
        - rewrite unsigned_lit by lia. eapply stk_transport_disjoint; [exact STA| exact MU3| exact WM3|]. cbn. ceil_facts. first [clear -GC LOv SLO CEILF__ CEILM__ CEILP__ | clear -GC LOv SLO]; lia.
        - rewrite unsigned_lit by lia. eapply rw_cells_transport; [exact FRA| exact MU3| exact WM3|]. cbn. ceil_facts. first [clear -GC LOv SLO CEILF__ CEILM__ CEILP__ | clear -GC LOv SLO]; lia.
        - exact LO.
        - rewrite unsigned_lit by lia. first [clear -SLO CEILF__ CEILM__ CEILP__ | clear -SLO]; lia.
        - rewrite unsigned_lit by lia. first [clear -SPR CEILF__ CEILM__ CEILP__ | clear -SPR]; lia.
        - apply rpres_except_refl.
        - apply wmono_refl.
        - exact Kr.
        - cbn [fst]. symmetry. exact Fp.
        - cbn [r_base rN]. rewrite unsigned_lit by (ceil_facts; first [clear -NBC NB0 Sp Hoff NDR EP N CEILF__ CEILM__ CEILP__ | clear -NBC NB0 Sp Hoff NDR EP N]; lia). reflexivity.
        - lia.
        - cbn [snd]. first [clear -NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDR EP Sp Hoff N]. lia.
        - cbn [snd]. first [clear -NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDR EP Sp Hoff N]. lia.
        - first [clear -Sp Hoff CEILF__ CEILM__ CEILP__ | clear -Sp Hoff]; lia.
        - cbn [snd r_len rN]. rewrite (round_up_pg_id' needed NDAL). lia.
        - subst st2R. rewrite (rl_shadow stH g b r nb needed) by (rewrite RGH; exact Hr). exact HK3H.
        - intros b' gh Hb' Hf'. subst st2R. rewrite (rl_groups stH g b r nb needed) in Hb' by (rewrite RGH; exact Hr).
          pose proof (ONLYGH b' gh Hb' ltac:(rewrite Hf', Fp; reflexivity)) as ->. left. rewrite Sb. first [clear -Sp Hoff CEILF__ CEILM__ CEILP__ | clear -Sp Hoff]; lia. }
      intros msf POST. unfold rrret_post in POST.
      destruct POST as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m' & -> & (MRF & TKF & MIF & STF & FRF & PEl & WMl)).
      rewrite !unsigned_lit in STF, FRF by (keep_hyps CEILV sp blk bs n lo g b r bm ag rag k1 nb CEILF__ SLO SPR LOv; lia).
      cbn [r_base rN].
      eapply (FINAL nb _ rN m'); try eassumption; try reflexivity.
      + unfold set_size. destruct (5 <=? _); destruct (negb _); rewrite ?s_regions_wr8, ?s_regions_wr32, ?s_regions_wr8; rewrite <- Fp; exact HrN.
      + cbn [r_len rN]. rewrite (round_up_pg_id' needed NDAL). lia.
      + assert (CT2 : ctx st2R = ctx st0).
        { subst st2R. rewrite (rl_ctx stH g b r nb needed) by (rewrite RGH; exact Hr). subst stH st. unfold ctx. rewrite s_ctx_havoc. reflexivity. }
        rewrite <- CT2. unfold set_size. destruct (5 <=? _); destruct (negb _); unfold ctx; rewrite ?s_ctx_wr8, ?s_ctx_wr32, ?s_ctx_wr8; reflexivity.
      + intros q Hq. unfold conc at 1, get_region. rewrite s_regions_set_size, s_regions_wr8. subst st2R. fold (get_region (upd_meta g (m_set_maplen (needed / 4096)) (upd_region (fst b) (λ rg : region, {| r_kind := r_kind rg; r_base := nb; r_len := needed |}) stH)) (fst q)).
        fold (conc (upd_meta g (m_set_maplen (needed / 4096)) (upd_region (fst b) (λ rg : region, {| r_kind := r_kind rg; r_base := nb; r_len := needed |}) stH)) q).
        rewrite (rl_conc stH g b r nb needed ltac:(rewrite RGH; exact Hr) q Hq). apply CGH.
      + (* [comment removed for export] *)
        eapply rpres_except_trans; [exact PEA|]. eapply rpres_except_trans.
        * eapply rpres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. subst FP. cbv beta in NC. cbn [outside].
          repeat split; try exact Logic.I; first [clear -NC CEILF__ CEILM__ CEILP__ | clear -NC]; lia.
        * eapply rpres_except_mono; [exact PEl|]. intros a Ha. subst FP. cbv beta. right. right. left. cbn [snd] in Ha.
          cbn [snd r_base rN] in Ha. first [clear -Ha EP Sp Hoff NDR N CEILF__ CEILM__ CEILP__ | clear -Ha EP Sp Hoff NDR N]. lia.
      + (* [comment removed for export] *)
        eapply rpres_except_bytes_at; [exact PEl| |].
        * assert (BSA : bytes_at usegs mA (nb + snd pf) (firstn k1 bs)).
          { pose proof (bytes_at_firstn m1 (blk_addr blk) bs k1 BS1) as X. rewrite HAp in X. destruct X as (X0 & X1 & X2). rewrite LK1 in X1.
            split; [first [clear -NB0 Sp Hoff CEILF__ CEILM__ CEILP__ | clear -NB0 Sp Hoff]; lia|]. split; [rewrite LK1; ceil_facts; first [clear -NBC K1R NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NBC K1R NDR EP Sp Hoff N]; lia|].
            intros ii Hii. rewrite LK1 in Hii. rewrite <- (X2 ii ltac:(rewrite LK1; exact Hii)). unfold mrd.
            replace (nb + snd pf + Z.of_nat ii) with (nb + (snd pf + Z.of_nat ii)) by lia. replace (old + snd pf + Z.of_nat ii) with (old + (snd pf + Z.of_nat ii)) by lia.
            rewrite (CPY (snd pf + Z.of_nat ii)) by (subst on; rewrite <- OLDLEN; rewrite STR in OS; first [clear -Hii K1R Sp Hoff OS NDR EP N SZ CEILF__ CEILM__ CEILP__ | clear -Hii K1R Sp Hoff OS NDR EP N SZ]; unfold UNIT, IB in *; lia).
            destruct (m1 (wa (old + (snd pf + Z.of_nat ii)))); [reflexivity|].
            rewrite !ref_seg_rom_none by (rewrite wa_unsigned by (ceil_facts; (keep_hyps CEILV blk off bs n g b r bm ag rag k1 nb ii CEILM__ Hoff Sp NDR EK1 NB0 NBC Hii rsv RSVE RSV0 RB0 RBC Se; lia)); rewrite STR in OS; unfold UNIT, IB in *; ceil_facts; first [clear -Hii K1R Sp Hoff OS NDR EP N SZ NIMG DRr OLDLEN EON EOLD STR NBC RBC NB0 RB0 CEILF__ CEILM__ CEILP__ | clear -Hii K1R Sp Hoff OS NDR EP N SZ NIMG DRr OLDLEN EON EOLD STR NBC RBC NB0 RB0]; clearbody old on; (keep_hyps CEILV blk off n b old k1 nb ii Hoff N Sp NDR NB0 NIMG on OS OLDLEN DRr K1R Hii; lia)). reflexivity. }
          eapply bytes_at_transport; [exact BSA| exact MU3|]. rewrite LK1. cbn. rewrite EG, Cag.
          pose proof (rarea_lr_lo st0 ag arg rag WF Hag Hrag) as LLg.
          assert (NEa : fst ag <> fst b) by (intros E2; rewrite E2, Hr in Hrag; assert (rag = r) as -> by congruence; exact (NKg Kr)).
          destruct (DJN _ _ Hrag NEa) as [D2|D2]; first [clear -D2 K1R Hkg Sag0 Sag1 RUg Sp Sc Hoff LLg NDR EP N CEILF__ CEILM__ CEILP__ | clear -D2 K1R Hkg Sag0 Sag1 RUg Sp Sc Hoff LLg NDR EP N]; unfold AREA_HDR, META_SIZE, NSLOTS, UNIT in *; (split; [| split; [| exact Logic.I]]).
          all: try clearbody old; try clearbody on. all: first [lia| match goal with |- ?gg => idtac "LIAFAIL" gg end; try match reverse goal with HH : ?T |- _ => idtac HH ":" T; fail end; fail].
        * rewrite LK1. intros a Ha. cbn [snd r_base rN]. first [clear -Ha K1R CEILF__ CEILM__ CEILP__ | clear -Ha K1R]. lia. }
  (* [comment removed for export] *)
  eapply rimplT_evt.
  { eapply (rrealloc_big63_head ra (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp (Z_to_bv 64 E) _ t2 s0 (wz G) a0 (wz (conc st0 b)) (Z_to_bv 64 (m_sizeclass mr)) a5
              (Z_to_bv 64 (E + 4)) (Z_to_bv 64 (E - P)) (Z_to_bv 64 (blk_addr blk + blk_size blk)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
              P (old + 16) n (meta_word mr) (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr));
      [rewrite A0, HAp; subst P; apply unsigned_lit; (keep_hyps CEILV blk off bs n g b r rsv bm ag rag k1 CEILM__ Hoff RSVE RSV0 RB0 RBC Sp Se SZm; lia)| rewrite Sc; reflexivity| subst P; (keep_hyps CEILV blk off bs n g b r bm ag rag k1 Hoff RB0 Sp; lia)| subst P; rewrite STR in OS; subst on; unfold UNIT, IB in *; ceil_facts; (keep_hyps CEILV blk bs n g b r rsv bm ag rag k1 RSVE RSV0 RBC Se SZm; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 N; lia)| reflexivity
      | (keep_hyps CEILV blk bs n g b r bm ag rag k1 LI0; lia)| (keep_hyps CEILV blk off bs n g b r bm ag rag k1 FRB; lia)| (keep_hyps CEILV blk off bs n g b r bm ag rag k1 SC63; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 MLR; lia)]. }
  intros msA HDA. unfold rr63A_post in HDA. rewrite <- END in HDA.
  apply rimplT_if; intros EQN; rewrite EQN in HDA; subst msA.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in EQN.
    apply rimplT_ret.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite Cb in K. unfold wz in K. rewrite ?unsigned_lit in K by (ceil_facts; lia). ceil_facts. lia. }
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (rrealloc_big63_stores _ _ gp tp _ _ _ _ (wz G) _ _ (wz (conc st0 b)) _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m1
                G old (P - (old + 16)) needed n (m_avail mr) (m_freed mr) (meta_word mr));
        [exact MM1| exact MI1| (keep_hyps CEILV blk bs n g b r bm ag rag k1 G0; lia)| ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 GC; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 RB0; lia)| rewrite <- EQN, OLDLEN; subst old on; exact RBC| ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 CEILM__ OLDLEN RB0 RBC ND4 EQN; lia)| exact NDAL
        | subst P; (keep_hyps CEILV blk off bs n g b r bm ag rag k1 Hoff Sp; lia)| (keep_hyps CEILV blk bs n g b r bm ag rag k1 N; lia)| first [clear -NDR CEILF__ CEILM__ CEILP__ | clear -NDR]; (keep_hyps CEILV n b r NDR; lia)| exact WRD| apply wz_unsigned; ceil_facts; (keep_hyps CEILV blk bs n g b r bm ag rag k1 CEILM__ G0 GC; lia)| rewrite Cb; reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
    intros msB (m2 & -> & MU2 & WM2 & MI2 & MC2).
    rewrite WLO in MC2. replace (m_last_idx mr + 32 * m_freeable mr + 64 * m_sizeclass mr + needed) with (meta_word mr) in MC2 by (unfold meta_word; lia).
    assert (MRH2 : rmrep stH m2).
    { pose proof (rmrep_put_meta_frame stH m1 m2 g mr MRH ltac:(unfold meta_slot; subst stH; rewrite s_areas_havoc; exact MSg)
                    ltac:(rewrite CGH; fold G; eapply munch_weaken; [| exact MU2]; intros y Hy; unfold META_SIZE in Hy; cbn in Hy |- *; repeat split; try exact Logic.I; (keep_hyps CEILV TB blk bs n g b r bm ag rag k1 y Hy; lia)) WM2
                    ltac:(rewrite CGH; fold G; unfold meta_cells; rewrite Hmem; rewrite !(pw_conc_ext st0 stH _ CGH);
                          change (pw st0 (Some b)) with (wz (conc st0 b)); rewrite Cb; exact MC2)) as X.
      rewrite (put_meta_same stH g mr) in X; [exact X|]. subst stH st. rewrite s_metas_havoc. exact GPR. }
    (* [comment removed for export] *)
    replace (old + 16 + (P - (old + 16))) with P by lia.
    replace (Z_to_bv 64 (old + needed - 4 + 4)) with (Z_to_bv 64 (r_base r + snd (fst b, needed - 4) + 4)) by (cbn [snd]; f_equal; subst old; lia).
    replace (Z_to_bv 64 (old + needed - 4 - P - n)) with (Z_to_bv 64 (snd (fst b, needed - 4) - snd pf - n)) by (cbn [snd]; f_equal; subst old P; lia).
    replace (Z_to_bv 64 (old + needed - 4)) with (Z_to_bv 64 (r_base r + snd (fst b, needed - 4))) by (cbn [snd]; f_equal; subst old; lia).
    eapply evt_mono.
    { eapply (rrealloc_setsize63_walk _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m2 m2 lo stH pf (fst b, needed - 4) r v3 n
                ra s0 s1 s2 s3 s4 s5 s6 (fun a => a = P - 3 \/ P + n <= a < r_base r + snd (fst b, needed - 4) + 1));
        first [exact MRH2| exact MI2| exact TKH| exact Kr| idtac].
      - intros a Ha. exact Ha.
      - rewrite unsigned_lit by lia. eapply stk_transport_disjoint; [exact ST1| exact MU2| exact WM2|]. cbn. ceil_facts. (keep_hyps CEILV sp blk off bs n lo g b r bm ag rag k1 LOv GC; lia).
      - rewrite unsigned_lit by lia. eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. ceil_facts. (keep_hyps CEILV sp blk off bs n lo g b r bm ag rag k1 SLO LOv GC; lia).
      - exact LO.
      - rewrite unsigned_lit by lia. lia.
      - rewrite unsigned_lit by lia. lia.
      - apply rpres_except_refl.
      - apply wmono_refl.
      - rewrite RGH, Fp. exact Hr.
      - cbn [fst]. symmetry. exact Fp.
      - rewrite unsigned_lit by (subst P; ceil_facts; (keep_hyps CEILV blk off bs n g b r rsv bm ag rag k1 CEILM__ Hoff RSVE RSV0 RB0 RBC Sp Se SZm; lia)). reflexivity.
      - lia.
      - cbn [snd]. first [clear -NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDR EP Sp Hoff N]. lia.
      - cbn [snd]. first [clear -NDR EP Sp Hoff N CEILF__ CEILM__ CEILP__ | clear -NDR EP Sp Hoff N]. lia.
      - lia.
      - cbn [snd]. subst on. lia.
      - subst stH. rewrite (cell_read_havoc_out pf (needed - snd pf) st ltac:(rewrite Sp; clear; Z.div_mod_to_equations; (keep_hyps off q r H H0; lia)) ltac:((keep_hyps CEILV blk off bs n g b r bm ag rag k1 N NDR; lia)) HAVT (fst pf, snd pf - 3)) by (cbn [fst snd]; (keep_hyps CEILV blk bs n g b r bm ag rag k1; lia)).
        cbn [fst snd]. exact C3.
      - intros b' gh Hb' Hf'. subst stH. rewrite s_groups_havoc in Hb'. change (s_groups st) with (s_groups st0) in Hb'.
        pose proof (ONLYG b' gh Hb' ltac:(rewrite Hf', Fp; reflexivity)) as ->. left. rewrite Sb. lia. }
    intros msf POST. unfold rrret_post in POST.
    destruct POST as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m' & -> & (MRF & TKF & MIF & STF & FRF & PEl & WMl)).
    rewrite !unsigned_lit in STF, FRF by (keep_hyps CEILV sp blk bs n lo g b r bm ag rag k1 CEILF__ SLO SPR LOv; lia).
    (* [comment removed for export] *)
    unfold resize63. change IB with 4.
    replace (set_size pf (fst b, needed - 4) n 0 (wr8 (fst b, needed - 4) 0 (havoc pf (needed - snd pf) st)))
       with (set_size pf (fst b, needed - 4) n (Z.land v3 31) (wr8 (fst b, needed - 4) 0 stH)) by (rewrite V0; reflexivity).
    rewrite set_size_land31.
    replace (r_base r + snd pf) with (old + snd pf) by reflexivity.
    eapply (FINAL old _ r m'); try eassumption; try reflexivity.
    + unfold set_size. destruct (5 <=? _); destruct (negb _); subst stH st; rewrite ?s_regions_wr8, ?s_regions_wr32, ?s_regions_wr8, ?s_regions_havoc; cbn [s_regions set_tick]; exact Hr.
    + rewrite <- EQN, OLDLEN. subst on. lia.
    + unfold set_size. destruct (5 <=? _); destruct (negb _); subst stH st; unfold ctx; rewrite ?s_ctx_wr8, ?s_ctx_wr32, ?s_ctx_wr8, ?s_ctx_havoc; reflexivity.
    + intros q _. unfold conc, get_region. rewrite s_regions_set_size, s_regions_wr8. subst stH. rewrite s_regions_havoc. reflexivity.
    + (* [comment removed for export] *)
      eapply rpres_except_trans.
      * eapply rpres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. subst FP. cbv beta in NC. cbn [outside].
        repeat split; try exact Logic.I; first [clear -NC CEILF__ CEILM__ CEILP__ | clear -NC]; lia.
      * eapply rpres_except_mono; [exact PEl|]. intros a Ha. subst FP. cbv beta. right. left. subst old on. rewrite <- OLDLEN, EQN. cbn [snd] in Ha.
        first [clear -Ha EP Sp Hoff NDR N CEILF__ CEILM__ CEILP__ | clear -Ha EP Sp Hoff NDR N]. lia.
    + (* [comment removed for export] *)
      eapply rpres_except_bytes_at; [exact PEl| |].
      * eapply bytes_at_transport; [| exact MU2|].
        -- eapply bytes_at_firstn. rewrite <- HAp. exact BS1.
        -- rewrite LK1. cbn. rewrite EG, Cag.
           assert (NEr : fst b <> fst ag) by (intros E2; rewrite E2 in Hr; rewrite Hr in Hrag; assert (rag = r) as -> by congruence; exact (NKg Kr)).
           pose proof (lr_lo_group r Kr) as LR. pose proof (rarea_lr_lo st0 ag arg rag WF Hag Hrag) as LLg.
           rewrite STR in OS. destruct (DJ _ _ _ _ Hr Hrag NEr) as [D1|D1]; first [clear -D1 K1R RBgC Hkg Sag0 Sag1 RUg Sp Sc Hoff RB0 B0 LR LLg HAp OS EP OLDLEN EOLD EON CEILF__ CEILM__ CEILP__ | clear -D1 K1R RBgC Hkg Sag0 Sag1 RUg Sp Sc Hoff RB0 B0 LR LLg HAp OS EP OLDLEN EOLD EON]; unfold AREA_HDR, META_SIZE, UNIT, IB, NSLOTS in *; ceil_facts;
             (split; [| split; [| exact Logic.I]]).
           all: clearbody old on; lia.
      * rewrite LK1. intros a Ha. cbn [snd]. first [clear -Ha K1R EP EOLD CEILF__ CEILM__ CEILP__ | clear -Ha K1R EP EOLD]. clearbody old. lia.
    + rewrite <- EQN, OLDLEN. exact RBC.
    + rewrite <- EQN, OLDLEN. exact RF.
    + intros rid' r' Hr' NE'. pose proof (lr_lo_group r Kr). rewrite <- EQN, OLDLEN. subst old on. destruct (DJ _ _ _ _ Hr' Hr NE'); [right| left]; lia.
  - (* [comment removed for export] *)
    apply Z.eqb_neq in EQN.
    pose proof GL as (G1 & G2 & G3 & G4 & G5).
    assert (ERRlo : errno_addr tp + 4 <= lo) by (rewrite (rerrno_addr tp TP); first [clear -TBF LOv CEILF__ CEILM__ CEILP__ | clear -TBF LOv]; lia).
    eapply rimplT_mremap.
    { rewrite <- Cb. eapply (rmremap_spec _ _ gp tp _ _ _ _ _ (wz (conc st0 b)) _ _ _ _ _ _ _ _ _ _ _ _ s7 s8 s9 s10 s11 _ _ _ _ F fc m1
               (conc st0 b) (m_maplen mr * 4096) needed [] errv1 lo);
        first [exact MI1| exact G4| exact G5| reflexivity| idtac]; rewrite ?Cb; ceil_facts.
      - rewrite unsigned_lit by lia. exact ST1.
      - exact ERR1.
      - exact RB0.
      - exact RBAL.
      - first [clear -ML0 CEILF__ CEILM__ CEILP__ | clear -ML0]; lia.
      - clear; Z.div_mod_to_equations; lia.
      - rewrite STR in OS. first [clear -ND4 NDR N EP Sp Hoff OS OLDLEN RBC EOLD EON RB0 SZ CEILF__ CEILM__ CEILP__ | clear -ND4 NDR N EP Sp Hoff OS OLDLEN RBC EOLD EON RB0 SZ]; clearbody old on P pf needed; unfold UNIT, IB in *; ceil_facts; lia.
      - exact NDAL.
      - exact EQN.
      - rewrite OLDLEN. ceil_facts. first [clear -RBC CEILF__ CEILM__ CEILP__ | clear -RBC]. lia.
      - rewrite OLDLEN. exact DRr.
      - rewrite unsigned_lit by lia. first [clear -SLO CEILF__ CEILM__ CEILP__ | clear -SLO]; lia.
      - first [clear -LOv CEILF__ CEILM__ CEILP__ | clear -LOv]. lia.
      - rewrite unsigned_lit by lia. left. first [clear -ERRlo SLO CEILF__ CEILM__ CEILP__ | clear -ERRlo SLO]; lia.
      - rewrite TP, RATP_unsigned. first [clear -TBF CEILF__ CEILM__ CEILP__ | clear -TBF]; lia.
      - rewrite (rerrno_addr tp TP). first [clear -TBF CEILF__ CEILM__ CEILP__ | clear -TBF]; lia. }
    intros x msX [FX PO]. cbv beta. unfold rmremap_facts in FX.
    (* [comment removed for export] *)
    apply rimplT_if; intros OKA; [apply rimplT_undef|]. apply Bool.negb_false_iff in OKA.
    apply rimplT_if; intros ISERR.
    + (* [comment removed for export] *)
      destruct x as [er|  |na]; cbn [mremap_val mremap_ret] in ISERR, PO |- *.
      2:{ exfalso. unfold is_err, TWO64 in ISERR. apply Z.ltb_lt in ISERR. fold old in ISERR. first [clear -ISERR RBC ON4096 CEILF__ CEILM__ CEILP__ | clear -ISERR RBC ON4096]. ceil_facts. lia. }
      2:{ exfalso. destruct FX as (_ & AOK & _ & _). pose proof (mmap_addr_ok_true _ _ _ AOK) as ((_ & _ & AC) & _).
          rewrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.KArith.mmap_len_of_aligned in AC by lia. ceil_facts.
          unfold is_err, TWO64 in ISERR. apply Z.ltb_lt in ISERR. first [clear -ISERR AC ND4 CEILF__ CEILM__ CEILP__ | clear -ISERR AC ND4]. lia. }
      destruct (PO Logic.I) as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & MI2 & ST2 & MU2 & WM2 & ERR2 & He).
      cbn [mremap_mem] in MI2, ST2 |- *.
      rewrite !unsigned_lit in ST2, MU2 by (keep_hyps CEILV sp blk bs n lo g b r bm ag rag k1 CEILF__ SLO SPR LOv; lia).
      replace (ret_pc (Z_to_bv 64 0x1abe0)) with (Z_to_bv 64 0x1abe0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      (* [comment removed for export] *)
      apply rimplT_from_evt. step. step. step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
      apply evt_done.
      assert (MR2 : rmrep st0 m2).
      { eapply (rmrep_transport_unowned st0 m1 m2 _ MR1 MU2 WM2).
        pose proof (rerrno_addr tp TP) as ETP.
        intros lo' hi' a [E1|[E1|[]]] Ha RFt; inversion E1; subst; destruct (rrepfoot_where2 st0 m1 a MR1 RFt) as [A1 A2];
          rewrite ?ETP in Ha; first [clear -Ha A1 A2 LOv SLO TBF CEILF__ CEILM__ CEILP__ | clear -Ha A1 A2 LOv SLO TBF]; unfold RCTX, RMLOCK, RLIBC, RGOT_SSP, RSSP_GUARD in *; ceil_facts; lia. }
      apply (FBOK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m2).
      * split; [exact MI2|]. split; [exact ST2|]. split; [exact MR2|].
        split. { eapply rauxv_ok_frame; [exact AUX1| exact MU2| exact WM2|]. rewrite (rerrno_addr tp TP). unfold RAUXV_CELL.
                 constructor; [cbn; first [clear -SLO SB LOv CEILF__ CEILM__ CEILP__ | clear -SLO SB LOv]; lia|]. constructor; [cbn; first [clear -TBF SB LOv SLO CEILF__ CEILM__ CEILP__ | clear -TBF SB LOv SLO]; lia| constructor]. }
        split. { eapply rw_cells_transport; [exact REPL1| exact MU2| exact WM2|]. rewrite (rerrno_addr tp TP). unfold RMREPLACED, RCTX. cbn. first [clear -TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -TBF LOv SLO]. lia. }
        split. { eapply rw_cells_transport; [exact CH1| exact MU2| exact WM2|]. rewrite (rerrno_addr tp TP). cbn. rewrite HAp.
                 rewrite STR in OS. first [clear -TBF LOv SLO TLSr OS Sp Hoff RBC OLDLEN EOLD EON SZ CEILF__ CEILM__ CEILP__ | clear -TBF LOv SLO TLSr OS Sp Hoff RBC OLDLEN EOLD EON SZ]. unfold UNIT, IB in *; ceil_facts. clearbody old on. lia. }
        split. { eapply rheap_pres_trans; [exact HP1|]. intros a Ha CA. split; [| apply WM2]. apply MU2. rewrite wa_unsigned by lia. rewrite (rerrno_addr tp TP). cbn.
                 destruct CA as [CA|[[CA [NS NE0]]|[(blk' & Hb' & Hab)|[CA NE]]]].
                 - first [clear -CA TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -CA TBF LOv SLO]. repeat split; try exact Logic.I; lia.
                 - first [clear -CA NE0 TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -CA NE0 TBF LOv SLO]. repeat split; try exact Logic.I; lia.
                 - unfold lbrm in Hb'. apply In_filter_iff in Hb'. destruct Hb' as [Hin' _].
                   destruct (proj1 (List.Forall_forall _ _) (ci_bclr _ _ C) blk' Hin') as [(r' & Hr' & Kr' & A16' & AEND' & _) _ _].
                   destruct (WR _ _ Hr') as (_ & _ & _ & RBC' & RF'). pose proof (rreserved_tlsU _ _ RF'). pose proof (round_up_pg_ge (r_len r')).
                   first [clear -Hab A16' AEND' RBC' H H0 TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -Hab A16' AEND' RBC' H H0 TBF LOv SLO]. ceil_facts. repeat split; try exact Logic.I; lia.
                 - first [clear -CA NE TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -CA NE TBF LOv SLO]. repeat split; try exact Logic.I; lia. }
        split; [eexists; exact ERR2|].
        eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. rewrite (rerrno_addr tp TP). cbn. first [clear -TBF LOv SLO CEILF__ CEILM__ CEILP__ | clear -TBF LOv SLO]. lia.
      * rewrite A0, HAp. apply unsigned_lit. rewrite STR in OS. first [clear -OS Sp Hoff RBC OLDLEN RB0 EOLD EON SZ CEILF__ CEILM__ CEILP__ | clear -OS Sp Hoff RBC OLDLEN RB0 EOLD EON SZ]. clearbody old on. unfold UNIT, IB in *; ceil_facts. lia.
    + (* [comment removed for export] *)
      rewrite Cb in FX, PO. rewrite OLDLEN in FX, PO, OKA, EQN.
      pose proof (rarea_lr_lo st0 ag arg rag WF Hag Hrag) as LLg.
      assert (NEa : fst ag <> fst b) by (intros E2; rewrite E2, Hr in Hrag; assert (rag = r) as -> by congruence; exact (NKg Kr)).
      assert (GOLD : G + 40 <= old \/ old + on <= G).
      { destruct (DJ _ _ _ _ Hrag Hr NEa) as [D1|D1]; rewrite ?(lr_lo_group r Kr) in D1; rewrite EG, Cag; subst old on; first [clear -D1 LLg Hkg Sag0 Sag1 CEILF__ CEILM__ CEILP__ | clear -D1 LLg Hkg Sag0 Sag1]; unfold AREA_HDR, META_SIZE, NSLOTS in *; lia. }
      pose proof (SH _ _ Hr Kr) as [WRo _]. fold old in WRo. fold on in WRo.
      (* [comment removed for export] *)
      assert (KER : exists nb, mremap_val old x = nb /\ mremap_ret old x = Z_to_bv 64 nb
         /\ match x with MrErr _ => False | MrSame => nb = old | MrMoved a => nb = a /\ on < needed /\ (old + on <= a \/ a + needed <= old) end
         /\ 0 < nb /\ nb mod 4096 = 0 /\ nb + needed <= alloc_ceiling /\ ranges_free ref_reserved nb needed = true
         /\ (forall rid' r', s_regions st0 !! rid' = Some r' -> rid' <> fst b -> nb + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= nb)).
      { destruct (mremap_ok_cases st (fst b) old on needed (mremap_val old x) OKA ISERR) as [[Ez INP]|(NEz & Z0 & ZAL & ZC & ZRF)].
        - destruct x as [er| |na]; cbn [mremap_val] in Ez.
          + exfalso. cbn [mremap_val] in ISERR. rewrite (is_err_neg_errno er FX) in ISERR. discriminate.
          + exists old. cbn [mremap_val mremap_ret]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
            split; [exact RB0|]. split; [exact RBAL|].
            assert (GE : on <= needed -> old + needed <= alloc_ceiling /\ ranges_free (live_ranges_wo st (fst b)) (old + on) (needed - on) = true).
            { intros GE. destruct INP as [LE|X]; [exfalso; first [clear -LE GE EQN CEILF__ CEILM__ CEILP__ | clear -LE GE EQN]; lia| exact X]. }
            destruct (Z_lt_dec needed on) as [LT|NLT].
            * split; [first [clear -LT RBC CEILF__ CEILM__ CEILP__ | clear -LT RBC]; lia|]. split; [eapply (ranges_free_sub _ old on); [exact RF| lia| first [clear -LT CEILF__ CEILM__ CEILP__ | clear -LT]; lia| first [clear -ND4 CEILF__ CEILM__ CEILP__ | clear -ND4]; lia]|].
              intros rid' r' Hr' NE'. destruct (DJ _ _ _ _ Hr' Hr NE') as [D1|D1]; rewrite ?(lr_lo_group r Kr) in D1; subst old on; first [clear -D1 LT CEILF__ CEILM__ CEILP__ | clear -D1 LT]; lia.
            * destruct (GE ltac:(first [clear -NLT CEILF__ CEILM__ CEILP__ | clear -NLT]; lia)) as [CE RFW].
              split; [exact CE|]. split.
              { replace needed with (on + (needed - on)) by lia. apply ranges_free_app_pos; [apply ref_reserved_pos| first [clear -ON4096 CEILF__ CEILM__ CEILP__ | clear -ON4096]; lia| first [clear -NLT CEILF__ CEILM__ CEILP__ | clear -NLT]; lia| exact RF|].
                apply ranges_free_intro. intros b0 k0 HI. apply (ranges_free_In _ _ _ _ _ RFW). unfold live_ranges_wo. apply in_or_app. left.
                change (s_reserved st) with (s_reserved st0). rewrite Hres. exact HI. }
              intros rid' r' Hr' NE'. destruct (DJ _ _ _ _ Hr' Hr NE') as [D1|D1]; rewrite ?(lr_lo_group r Kr) in D1.
              { right. subst old on. first [clear -D1 CEILF__ CEILM__ CEILP__ | clear -D1]. lia. }
              pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc3.ranges_free_regions_wo st (fst b) _ _ rid' r' RFW Hr' NE') as D2.
              destruct (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_inv__MA.MallocFacts_inv.areach_inv _ _ _ AR) as (L & LS & BLl & INV & _). pose proof INV as (IR & _).
              pose proof (OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.MI_Realloc2__Spec.MI_Realloc3.region_live_range_pos _ st0 L rid' r' IR Hr') as P2.
              unfold region_live_range in D2, P2. unfold lr_lo in D1 |- *. unfold PGSZ in D2, P2.
              destruct (r_kind r'); cbn in D1, D2, P2; cbn; subst old on; first [clear -D1 D2 P2 NLT CEILF__ CEILM__ CEILP__ | clear -D1 D2 P2 NLT]; lia.
          + exfalso. exact (proj2 (proj2 (proj2 FX)) Ez).
        - destruct x as [er| |na]; cbn [mremap_val] in NEz, Z0, ZAL, ZC, ZRF.
          + exfalso. cbn [mremap_val] in ISERR. rewrite (is_err_neg_errno er FX) in ISERR. discriminate.
          + exfalso. apply NEz. reflexivity.
          + assert (DJA : forall rid' r', s_regions st0 !! rid' = Some r' -> na + needed <= lr_lo r' \/ r_base r' + round_up_pg (r_len r') <= na).
            { intros rid' r' Hr'. pose proof (In_live_ranges st rid' r' Hr') as HI. unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
              destruct (r_kind r'); (pose proof (ranges_free_In _ _ _ _ _ ZRF HI) as D; first [clear -D CEILF__ CEILM__ CEILP__ | clear -D]; lia). }
            exists na. cbn [mremap_ret]. split; [reflexivity|]. split; [reflexivity|].
            split. { split; [reflexivity|]. split; [exact (proj1 FX)|]. pose proof (DJA _ _ Hr) as D. rewrite (lr_lo_group r Kr) in D. subst old on. first [clear -D CEILF__ CEILM__ CEILP__ | clear -D]. lia. }
            split; [exact Z0|]. split; [exact ZAL|]. split; [exact ZC|]. split.
            { apply ranges_free_intro. intros b0 k0 HI. apply (ranges_free_In _ _ _ _ _ ZRF). unfold live_ranges. apply in_or_app. left.
              change (s_reserved st) with (s_reserved st0). rewrite Hres. exact HI. }
            intros rid' r' Hr' _. exact (DJA _ _ Hr'). }
      destruct KER as (nb & EVAL & ERET & HX & NB0 & NBAL & NBC & RFN & DJN).
      rewrite EVAL.
      assert (NIMG : nb + needed <= 0x10000 \/ 0x56000 <= nb) by (apply (rreserved_disjoint1 _ _ RFN); first [clear -ND4 CEILF__ CEILM__ CEILP__ | clear -ND4]; lia).
      assert (GNEW : G + 40 <= nb \/ nb + needed <= G).
      { destruct (DJN _ _ Hrag NEa) as [D1|D1]; rewrite EG, Cag; first [clear -D1 LLg Hkg Sag0 Sag1 CEILF__ CEILM__ CEILP__ | clear -D1 LLg Hkg Sag0 Sag1]; unfold AREA_HDR, META_SIZE, NSLOTS in *; lia. }
      assert (IMGC : match x with MrErr _ => True | MrSame => img_clear old on needed | MrMoved a => img_clear a on needed end).
      { unfold img_clear. destruct x as [er| |na]; [exact Logic.I| rewrite <- HX| destruct HX as (Ena & _); rewrite <- Ena]; first [clear -NIMG CEILF__ CEILM__ CEILP__ | clear -NIMG]; lia. }
      destruct (PO IMGC) as (x0 & x1 & x2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & x3 & x4 & x5 & x6 & m2 & -> & MIA & STA & REST).
      rewrite !unsigned_lit in STA, REST by (keep_hyps CEILV sp blk bs n lo g b r bm ag rag k1 nb CEILF__ SLO SPR LOv; lia).
      assert (MW : munch [(bv_unsigned sp + -64 - 112, bv_unsigned sp + -64)] m1 m2 /\ wmono usegs m1 m2).
      { destruct x as [er| |na]; [destruct HX| exact (conj (proj1 REST) (proj1 (proj2 REST)))| exact (conj (proj1 REST) (proj1 (proj2 REST)))]. }
      clear REST. destruct MW as [MU2 WM2].
      rewrite ERET. replace (ret_pc (Z_to_bv 64 0x1abe0)) with (Z_to_bv 64 0x1abe0) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      set (mA := mremap_mem old on needed x m2) in *.
      destruct (mremap_mem_facts m2 old on needed x nb RB0 ltac:(first [clear -ON4096 CEILF__ CEILM__ CEILP__ | clear -ON4096]; lia) ltac:(first [clear -ND4 CEILF__ CEILM__ CEILP__ | clear -ND4]; lia) RBC NB0 NBC HX) as (OUT & PRE & TL). fold mA in OUT, PRE, TL.
      assert (M12 : forall a, 0 <= a < 2^64 -> (a < bv_unsigned sp - 176 \/ bv_unsigned sp - 64 <= a) -> m2 (wa a) = m1 (wa a)).
      { intros a Ha Ho. apply MU2. rewrite wa_unsigned by exact Ha. cbn [outside]. split; [first [clear -Ho CEILF__ CEILM__ CEILP__ | clear -Ho]; lia| exact Logic.I]. }
      assert (WR2 : wr_at usegs m2 old on).
      { destruct WRo as (W0 & W1 & W2). split; [exact W0|]. split; [exact W1|]. intros ii Hii. apply WM2. apply W2. exact Hii. }
      pose proof (mremap_mem_wr_at m2 old on needed x nb RB0 ltac:(first [clear -ON4096 CEILF__ CEILM__ CEILP__ | clear -ON4096]; lia) ltac:(first [clear -ND4 CEILF__ CEILM__ CEILP__ | clear -ND4]; lia) RBC NB0 NBC HX DRr NIMG WR2) as WRN. fold mA in WRN.
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -64) (rrealloc_frame ra s0 s1 s2 s3 s4 s5 s6)).
      { eapply rw_cells_transport; [exact FR1| exact MU2| exact WM2|]. cbn. split; [clear; lia| exact Logic.I]. }
      assert (MM2 : rw_cells usegs m2 G [C8 (pw st0 (m_prev mr)); C8 (pw st0 (m_next mr)); C8 (wz (conc st0 b)); C4 (wz (m_avail mr)); C4 (wz (m_freed mr)); C8 (wz (meta_word mr))]).
      { eapply rw_cells_transport; [exact MM1| exact MU2| exact WM2|]. cbn. split; [first [clear -GC LOv SLO CEILF__ CEILM__ CEILP__ | clear -GC LOv SLO]; lia| exact Logic.I]. }
      apply (SUCC nb mA x0 x1 x2 y1 y2 y3 y4 y5 y6 y7 x3 x4 x5 x6 NB0 NBAL NBC RFN DJN MIA STA).
      * eapply rrw_cells_agree'; [exact FR2|]. intros a Ha. cbn in Ha. apply OUT; ceil_facts; first [clear -Ha SPR LOv SLO RBC NBC CEILF__ CEILM__ CEILP__ | clear -Ha SPR LOv SLO RBC NBC]; lia.
      * eapply rrw_cells_agree'; [exact MM2|]. intros a Ha. cbn in Ha. apply OUT; ceil_facts; first [clear -Ha GC G0 GOLD GNEW CEILF__ CEILM__ CEILP__ | clear -Ha GC G0 GOLD GNEW]; lia.
      * apply rpres_except_of_eq. intros a Ha NC. subst FP. cbv beta in NC.
        rewrite (OUT a Ha) by (first [clear -NC Ha CEILF__ CEILM__ CEILP__ | clear -NC Ha]; lia). apply M12; [exact Ha| first [clear -NC Ha LOv SLO CEILF__ CEILM__ CEILP__ | clear -NC Ha LOv SLO]; lia].
      * intros A k HA0 HK DO DN AC a Ha. ceil_facts.
        rewrite (OUT a) by (first [clear -Ha HA0 HK DO DN AC CEILF__ CEILM__ CEILP__ | clear -Ha HA0 HK DO DN AC]; lia). apply M12; first [clear -Ha HA0 AC LOv SLO CEILF__ CEILM__ CEILP__ | clear -Ha HA0 AC LOv SLO]; lia.
      * intros o Ho. rewrite (PRE o) by (first [clear -Ho CEILF__ CEILM__ CEILP__ | clear -Ho]; lia). ceil_facts. apply M12; first [clear -Ho RBC RB0 LOv SLO CEILF__ CEILM__ CEILP__ | clear -Ho RBC RB0 LOv SLO]; lia.
      * exact WRN.
Qed.
End Sz1.
Theorem rbig63_proof : ltac:(let t := eval cbv delta [rbig63_proof__stmt] in rbig63_proof__stmt in exact t).
Proof using Type. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m m1 s LB blk off bs n lo B g b ai r i v3 rsv t2 a0 a5 t3 t4 t5 t6. ltac2:(SecDiet.SzSec.closeP 'rbig63_proof__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

End PORT.

End WithCeil.
End TwB.
End RF_realloc63T.

(* [comment removed for export] *)
Module RF_calloc_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_slot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_P__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_meta. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_slot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_P__S3.RF_am_P OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_calloc.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).
Theorem rcalloc_spec : rcalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  exact (rcalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.
End PORT.

End WithCeil.

(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_slot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_P__S3.RF_am_P.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_calloc.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).
Theorem rcalloc_spec : rcalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  exact (rcalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.
End PORT.

End WithCeil.
End TwB.
End RF_calloc_spec.

(* [comment removed for export] *)
Module RF_malloc_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_slot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_P__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_meta. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_slot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_P__S3.RF_am_P OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_meta.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Theorem rmalloc_spec : rmalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

End PORT.

End WithCeil.

(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_slot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_P__S3.RF_am_P.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_meta.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.

Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).

Theorem rmalloc_spec : rmalloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  exact (rmalloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big)).
Qed.

End PORT.

End WithCeil.
End TwB.
End RF_malloc_spec.

(* [comment removed for export] *)
Module RF_realloc_spec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require AllocBridge__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import TlsBase.
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocTree. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocFacts_Bpres__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require MallocBlocks__MA. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require F_am_F__MA. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMallocRep__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_malloc_entry__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_A__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RMalloc_ifaceP__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_slot. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_am_P__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require RF_alloc_meta. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_slot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_P__S3.RF_am_P OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_meta OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc63T.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require Import MSecret.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Ceiling.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).
Theorem rrealloc_spec : rrealloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  exact (rrealloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big) rbig63_proof).
Qed.
End PORT.

End WithCeil.

(* [comment removed for export] *)

From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA Require TlsBaseU.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.AllocBridge__Spec.AllocBridge.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.TlsBaseU.
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocTree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocFacts_Bpres__MA.ASlot_I OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MallocBlocks__MA.MallocFacts_AM OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.F_am_F__MA.MallocFacts_AMP.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMallocRep__S3.RMallocTree.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RMalloc_ifaceB.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RAllocSlot_iface.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_A__S3.RF_malloc_core.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_top.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_malloc_entry__S3.RASlot_I.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_slot.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RMalloc_ifaceP__S3.RF_malloc_big.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_am_P__S3.RF_am_P.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_alloc_meta.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.RF_free__S3.RF_realloc63T.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.MA.MSecret.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Ceiling.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Section WithCeil.
Context {CEILV : CEIL} {MSECV : MSEC}.
Section PORT.
Context {PState : Type} {AS : AllocSt PState} {TB : TlsBase}.
Let TLSFACTS := the_tb_facts (TB:=TB).
Theorem rrealloc_spec : rrealloc_stmt.
Proof using Type. pin_using tt. ceil_facts. msec_facts.
  exact (rrealloc_spec_proof ras_pre2 as_inv2 ralloc_slot_spec ras_pre2_intro (rbig_spec ram_pre ralloc_meta_spec ramp_big) rbig63_proof).
Qed.
End PORT.

End WithCeil.
End TwB.
End RF_realloc_spec.
