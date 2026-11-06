(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_entry F_malloc_enframe MallocTree MallocFacts_A MallocHINV MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp MallocKit_A2 AllocSlot_iface Malloc_iface.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocNat MallocFacts_AS MallocKit_A3 ASlot_W0 ASlot_W9 ASlot_W18 ASlot_I.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_ASlot_M0 () : Init.string Init.list := ["Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.m_mem"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.m_freeable"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.m_maplen"; "OSSVerify.KrLib.Heap.MallocTree.mem"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "OSSVerify.KrLib.Heap.MallocTree.leaf_of"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.Heap.Malloc.alloc_meta"; "OSSVerify.KrLib.Heap.MallocNat.kS"; "OSSVerify.KrLib.Heap.MallocNat.bS"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.pair"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "links_only"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "OSSVerify.KrLib.Heap.ASlot_I.ENTRY_REL"; "OSSVerify.KrLib.Heap.MallocTree.am_rel"; "Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "stdpp.numbers.Z.eq_dec"; "stdpp.countable.Z_countable"; "OSSVerify.KrLib.Heap.Malloc.r_cells"; "Stdlib.NArith.BinNat.N.le"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "Stdlib.NArith.BinNat.N.lt"; "OSSVerify.KrLib.Heap.ASlot_I.ALLC"; "OSSVerify.KrLib.Heap.Malloc.set_tick"; "OSSVerify.KrLib.Heap.Malloc_fp.unk_agree"; "OSSVerify.KrLib.Heap.Malloc.region"; "OSSVerify.KrLib.Heap.Malloc.rkind"; "OSSVerify.KrLib.Heap.Malloc.r_kind"; "OSSVerify.KrLib.Heap.Malloc.RKGroup"; "OSSVerify.KrLib.Heap.Malloc.s_regions"; "Corelib.Init.Logic.iff"; "stdpp.base.is_Some"; "OSSVerify.KrLib.Heap.Malloc.ghdr"; "stdpp.decidable.prod_eq_dec"; "stdpp.countable.prod_countable"; "OSSVerify.KrLib.Heap.Malloc.s_groups"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.Malloc.r_len"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "OSSVerify.KrLib.Heap.Malloc.Unknown"; "Corelib.Init.Logic.not"; "OSSVerify.KrLib.Heap.Malloc_fp.grp_hdr_cov"; "stdpp.bitvector.definitions.bv"; "OSSVerify.KrLib.Lib.Mem.wa"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.r_base"; "OSSVerify.KrLib.Heap.ASlot_W18.as_fm_st"; "OSSVerify.KrLib.Heap.Malloc.area"; "OSSVerify.KrLib.Heap.Malloc.s_areas"; "OSSVerify.KrLib.Heap.Malloc.s_slots"; "OSSVerify.KrLib.Heap.Malloc.s_next_rid"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.Malloc.s_reserved"; "OSSVerify.KrLib.Heap.Malloc.active"; "OSSVerify.KrLib.Heap.Malloc.usage"; "OSSVerify.KrLib.Heap.Malloc.brkstate"; "OSSVerify.KrLib.Heap.Malloc.c_brk"; "OSSVerify.KrLib.Heap.Malloc.ctx"; "OSSVerify.KrLib.Heap.Malloc.c_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.bounces"; "OSSVerify.KrLib.Heap.Malloc.unmap_seq"; "OSSVerify.KrLib.Heap.Malloc.c_seq"].


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition links_only (r r' : meta) : Prop := ltac2:(CDefT.buildp (gd_tbl_ASlot_M0 ()) "(0.(1.$2.(3.O1.)(3.O2.))(0.(1.$4.(5.O1.)(5.O2.))(0.(1.$4.(6.O1.)(6.O2.))(0.(1.$4.(7.O1.)(7.O2.))(0.(1.$4.(8.O1.)(8.O2.))(0.(1.$4.(9.O1.)(9.O2.))(1.$4.(:.O1.)(:.O2.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leaf_of_ret_inv {R} o (r r' : R) : leaf_of o (SRet r) r' -> r' = r.
Proof. (intros dd_H; ddestruct dd_H as (ans & o' & H)). rewrite mrun_ret in H. cbn in H. destruct ans; inversion H; reflexivity. Qed.

Lemma leaf_of_vis_inv {R} o e (k : Z -> Malloc.M R) r :
  leaf_of o (SVis e k) r ->
  match e with
  | EUndef _ => False
  | EPeek p c h => leaf_of o (k (pans_mem o p c h)) r
  | _ => exists z, leaf_of o (k z) r
  end.
Proof.
  (intros dd_H; ddestruct dd_H as (ans & o' & H)).
  destruct e; try (rewrite mrun_vis in H by exact I; cbn [follow] in H; destruct ans as [|a ans]; [discriminate|]; exists a; dexists ans, o'; exact H).
  - rewrite mrun_peek in H. dexists ans, o'. exact H.
  - rewrite mrun_vis in H by exact I. cbn [follow] in H. destruct ans; discriminate.
Qed.

Lemma leaf_of_bad {R} o (bail : Malloc.M R) r : leaf_of o (bad_answer bail) r -> False.
Proof. intros H. exact (leaf_of_vis_inv o _ _ r H). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition LO (st st' : mstate) : Prop := forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).

Lemma LO_refl st : LO st st.
Proof. intros q. repeat split; reflexivity. Qed.
Lemma LO_trans st1 st2 st3 : LO st1 st2 -> LO st2 st3 -> LO st1 st3.
Proof.
  intros A B q. ddestruct (A q) as (A1&A2&A3&A4&A5&A6&A7). ddestruct (B q) as (B1&B2&B3&B4&B5&B6&B7).
  repeat split; congruence.
Qed.
Lemma LO_same st st' : (forall q, get_meta_rec st' q = get_meta_rec st q) -> LO st st'.
Proof. intros H q. rewrite H. apply LO_refl. Qed.

Lemma LO_upd_links st m f :
  (forall r, links_only r (f r)) -> LO st (upd_meta m f st).
Proof.
  intros Hf q. unfold upd_meta. destruct (decide (q = m)) as [->|NE].
  - rewrite get_meta_rec_put_same. apply Hf.
  - rewrite get_meta_rec_put_other by exact NE. apply LO_refl.
Qed.


Lemma rec_set_head h v st q : get_meta_rec (set_head h v st) q = get_meta_rec st q.
Proof. destruct h; reflexivity. Qed.

Ltac lo_peel :=
  first [ apply LO_refl
        | apply LO_same; intros ?; reflexivity
        | eapply LO_trans; [| apply LO_upd_links; intros ?; repeat split; reflexivity]; lo_peel
        | eapply LO_trans; [| apply LO_same; intros ?; apply rec_set_head]; lo_peel ].

Lemma LO_dequeue h m st : LO st (dequeue h m st).
Proof.
  unfold dequeue. cbv zeta.
  destruct (negb (optr_eqb (m_next (get_meta_rec st m)) (Some m)));
  destruct (m_prev (get_meta_rec st m)) as [pv|]; destruct (m_next (get_meta_rec st m)) as [nx|];
  try destruct (optr_eqb _ (Some m)); lo_peel.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AML.
Context {R : Type}.
Variable o : mem.
Variable Φ : R -> Prop.

Definition KOK (st : mstate) (k : mstate -> optr -> Malloc.M R) : Prop :=
  forall st2 mo r, LO st st2 -> leaf_of o (k st2 mo) r -> Φ r.
Definition BOK (bail : Malloc.M R) : Prop := forall r, leaf_of o bail r -> Φ r.

#[using="Type"] Lemma KOK_LO st st1 k : LO st st1 -> KOK st k -> KOK st1 k.
Proof. intros L K st2 mo r L2 H. apply (K st2 mo r); [eapply LO_trans; [exact L| exact L2]| exact H]. Qed.

#[using="Type"] Lemma am_take_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (am_take st k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_take in H.
  destruct (c_avail_meta (ctx st)) as [m|].
  - eapply K; [| exact H]. lo_peel.
  - destruct (leaf_of_vis_inv o _ _ r H).
Qed.

#[using="Type"] Lemma am_carve_leaves st p k bail r : KOK st k -> BOK bail -> leaf_of o (am_carve st p k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_carve in H. cbv zeta in H.
  eapply am_take_leaves; [| exact B| exact H].
  eapply KOK_LO; [| exact K]. apply LO_same. intros q.
  destruct (c_meta_area_tail _); reflexivity.
Qed.

#[using="Type"] Lemma am_finish_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_finish st nu k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_finish in H.
  destruct (c_avail_meta_areas (ctx st)) as [p|]; [| destruct (leaf_of_vis_inv o _ _ r H)].
  cbv zeta in H.
  destruct (if negb (snd p mod PGSZ =? 0) then false else nu).
  - destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
    destruct (negb (mprotect_answer_ok z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct ((z =? 0) || (z =? TWO64 - ENOSYS)).
    + eapply am_carve_leaves; [exact K| exact B| exact Hz].
    + exact (K _ _ _ (LO_refl st) Hz).
  - eapply am_carve_leaves; [exact K| exact B| exact H].
Qed.

#[using="Type"] Lemma am_after_brk_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_after_brk st nu k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_after_brk in H.
  destruct (c_avail_meta_area_count (ctx st) =? 0).
  - destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
    destruct (negb (mmap_answer_ok _ _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct (is_err z); [exact (K _ _ _ (LO_refl st) Hz)|].
    destruct (new_region RKMeta z _ st) as [st1 rid] eqn:E.
    eapply am_finish_leaves; [| exact B| exact Hz].
    eapply KOK_LO; [| exact K]. apply LO_same. intros q.
    replace st1 with (fst (new_region RKMeta z (Z.shiftl 2 (c_meta_alloc_shift (ctx st)) * PGSZ) st)) by (rewrite E; reflexivity). reflexivity.
  - eapply am_finish_leaves; [exact K| exact B| exact H].
Qed.

#[using="Type"] Lemma alloc_meta_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (alloc_meta st k bail) r -> Φ r.
Proof.
  intros K B H. unfold alloc_meta in H.
  set (stI := if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st) in H.
  assert (LI : LO st stI) by (apply LO_same; intros q; subst stI; destruct (c_init_done (ctx st) =? 0); reflexivity).
  pose proof (KOK_LO st stI k LI K) as KI.
  destruct (c_free_meta_head (ctx stI)) as [m|].
  { exact (KI _ _ _ (LO_dequeue LFree m stI) H). }
  destruct (negb (c_avail_meta_count (ctx stI) =? 0)); [eapply am_take_leaves; [exact KI| exact B| exact H]|].
  destruct ((c_avail_meta_area_count (ctx stI) =? 0) && _); [| eapply am_after_brk_leaves; [exact KI| exact B| exact H]].
  destruct (c_brk (ctx stI)) as [| |rid off].
  - (* [comment removed for export] *)
    destruct (leaf_of_vis_inv o _ _ r H) as [cur Hc]. cbv beta in Hc.
    destruct (negb (brk0_answer_ok cur)); [destruct (leaf_of_bad o _ _ Hc)|].
    destruct (leaf_of_vis_inv o _ _ r Hc) as [z Hz]. cbv beta in Hz.
    destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct (negb (z =? _)).
    + eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
    + destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
      destruct (leaf_of_vis_inv o _ _ r Hz) as [w Hw]. cbv beta in Hw.
      destruct (negb (mmap_fixed_answer_ok _ w)); [destruct (leaf_of_bad o _ _ Hw)|].
      destruct (new_region RKBrk _ _ stI) as [st1 rid1] eqn:E.
      eapply am_after_brk_leaves; [| exact B| exact Hw]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
      replace st1 with (fst (new_region RKBrk (round_up_pg cur) (2 * PGSZ) stI)) by (rewrite E; reflexivity). reflexivity.
  - (* [comment removed for export] *) eapply am_after_brk_leaves; [exact KI| exact B| exact H].
  - (* [comment removed for export] *)
    destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
    destruct (negb (brk_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct (negb (z =? _)).
    + eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q; reflexivity.
    + destruct (negb (brk_pages_ok _ _ _)); [destruct (leaf_of_bad o _ _ Hz)|].
      eapply am_after_brk_leaves; [| exact B| exact Hz]. eapply KOK_LO; [| exact KI]. apply LO_same; intros q.
      unfold upd_region. destruct (get_region stI rid); reflexivity.
Qed.
End AML.

Lemma am_leaf_links_only : ltac2:(CDefT.buildp (gd_tbl_ASlot_M0 ()) "Po,$;.Pst,$<.Pst',$<.Pmo,$2.P,(=.(>.(?.$<.$2.))R4.(10.(>.(?.$<.$2.))R3.(11.$<.$2.)(12.(?.$<.$2.)))(13.(?.$<.$2.)(14.$<.$2.R2.R1.)))Pq,$15.(16.(17.R5.R1.)(17.R4.R1.))")
(* [comment removed for export] *).
Proof.
  intros o st st' mo H.
  refine (alloc_meta_leaves o (fun r => match r with Some (stX, _) => LO st stX | None => True end) st kS bS (Some (st', mo)) _ _ H).
  - intros st2 mo2 r L HL. apply leaf_of_ret_inv in HL. subst r. exact L.
  - intros r HL. apply leaf_of_ret_inv in HL. subst r. exact I.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ER_refl_tick st0 t : ENTRY_REL st0 (set_tick t st0).
Proof.
  constructor; try reflexivity; try (intros; tauto).
  - split; [intros rid r H; exists r; cbn; repeat split; auto; lia| cbn; lia| reflexivity].
Qed.

Lemma ER_ta st0 st sc st1 : ENTRY_REL st0 st -> ta_rel sc st st1 -> ENTRY_REL st0 st1.
Proof.
  intros E T. destruct E as [ES EG EGR EM EME EGE EB EA].
  constructor.
  - rewrite (tr_shadow _ _ _ T). exact ES.
  - intros b. rewrite <- (EG b). destruct (tr_groups _ _ _ T b) as [A B].
    split; intros [x Hx]; [destruct (A (ex_intro _ x Hx)) as [y Hy]| destruct (B (ex_intro _ x Hx)) as [y Hy]]; rewrite Hy; eexists; reflexivity.
  - intros rid r Hk. rewrite (tr_regions _ _ _ T). apply EGR. exact Hk.
  - destruct EM as [R1 N1 S1]. split; [| rewrite (tr_next _ _ _ T); exact N1| rewrite (tr_reserved _ _ _ T); exact S1].
    intros rid r Hr. rewrite (tr_regions _ _ _ T). exact (R1 rid r Hr).
  - intros q. destruct (tr_geom _ _ _ T q) as (M & _). rewrite M. apply EME.
  - intros q Hq. ddestruct (EGE q Hq) as (A1 & A2 & A3). destruct (tr_geom _ _ _ T q) as (M & L & F & S & P). rewrite L, S. repeat split; try assumption.
    unfold get_stride. rewrite L, S, P. exact A1.
  - intros q i Hi Hb. apply (EB q i Hi). apply (tr_bits _ _ _ T q i Hi). exact Hb.
  - intros a Ha. rewrite (tr_areas _ _ _ T). apply EA. exact Ha.
Qed.

Lemma ER_am st0 st st1 m o : ltac2:(CDefT.buildp (gd_tbl_ASlot_M0 ()) "P,(18.O5.O4.)P,(19.O4.O3.(13.$15.O2.))P,(=.(>.(?.$<.$2.))O1.(10.(>.(?.$<.$2.))O4.(11.$<.$2.)(12.(?.$<.$2.)))(13.(?.$<.(>.$15.))(14.$<.(>.$15.)O3.(13.$15.O2.))))(18.O5.O3.)")
(* [comment removed for export] *).
Proof.
  intros E A L. destruct E as [ES EG EGR EM EME EGE EB EA].
  pose proof (am_leaf_links_only o st st1 (Some m) L) as LO.
  constructor.
  - rewrite (amr_shadow _ _ _ A). exact ES.
  - intros b. rewrite <- (EG b). rewrite (amr_groups _ _ _ A). tauto.
  - intros rid r Hk. rewrite <- (EGR rid r Hk). split; intros Hr.
    + destruct ((s_regions st) !! rid) as [r0|] eqn:E0.
      * destruct (amr_regions _ _ _ A rid r0 E0) as (r' & Hr' & K' & _ & _ & G'). rewrite Hr in Hr'. inversion Hr'; subst r'.
        rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      * exfalso. exact (amr_new _ _ _ A rid r Hr E0 Hk).
    + destruct (amr_regions _ _ _ A rid r Hr) as (r' & Hr' & K' & _ & _ & G'). rewrite Hr'. f_equal. apply G'. exact Hk.
  - destruct EM as [R1 N1 S1]. split.
    + intros rid r Hr. ddestruct (R1 rid r Hr) as (r1 & H1 & K1 & B1 & L1).
      destruct (amr_regions _ _ _ A rid r1 H1) as (r2 & H2 & K2 & B2 & L2 & _). exists r2. repeat split; try congruence. lia.
    + pose proof (amr_next_rid _ _ _ A). lia.
    + rewrite (amr_reserved _ _ _ A). exact S1.
  - intros q. destruct (LO q) as (M & _). rewrite M. apply EME.
  - intros q Hq. ddestruct (EGE q Hq) as (A1 & A2 & A3). ddestruct (LO q) as (M & AV & FR & L2 & F & S & P). rewrite L2, S. repeat split; try assumption.
    unfold get_stride. rewrite L2, S, P. exact A1.
  - intros q i Hi Hb. apply (EB q i Hi). ddestruct (LO q) as (_ & AV & FR & _). rewrite <- AV, <- FR. exact Hb.
  - intros a Ha. apply (amr_areas _ _ _ A). apply EA. exact Ha.
Qed.

Lemma ticks_ok_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros ES ET [T1 T2]. split; rewrite ES, ET; assumption. Qed.

(* [comment removed for export] *)
Lemma ALLC_tick st0 t : ltac2:(CDefT.buildp (gd_tbl_ASlot_M0 ()) "P,Prid,$1:.Psh,$1;.Po,$4.Pv,$4.Ptk,$1:.P,(1.(>.$1;.)(1<.$1:.$1;.(1=.$1:.$1>.$1?.$1;.)(20.$1:.$1>.$1?.$1;.)R5.(21.O2.))(13.$1;.R4.))P,(1.(>.(?.$4.$1:.))(1<.$4.(?.$4.$1:.)(1=.$4.$22.$23.(?.$4.$1:.))(20.$4.$22.$23.(?.$4.$1:.))R4.(24.R5.))(13.(?.$4.$1:.)(14.$4.$1:.R3.R2.)))(25.R3.(26.O2.))P,(27.(26.O2.)O1.)(28.(29.O1.O2.))")
(* [comment removed for export] *).
Proof. intros H Ht rid sh o v tk Hs Hc. cbn. pose proof (H rid sh o v tk Hs Hc). lia. Qed.

Lemma ALLC_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ALLC st -> ALLC st1.
Proof. intros ES ET H rid sh o v tk Hs Hc. rewrite ET. rewrite ES in Hs. exact (H rid sh o v tk Hs Hc). Qed.

Lemma ALLC_ta st sc st1 : ta_rel sc st st1 -> ALLC st -> ALLC st1.
Proof. intros T. apply ALLC_same; [apply (tr_shadow _ _ _ T)| apply (tr_tick _ _ _ T)]. Qed.

Lemma ALLC_am st st1 mo : am_rel st st1 mo -> ALLC st -> ALLC st1.
Proof. intros A. apply ALLC_same; [apply (amr_shadow _ _ _ A)| apply (amr_tick _ _ _ A)]. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sc_mono_fn (a : Z) : bool := forallb (fun b => (size_class a <? size_class b)) (zseq (a + 1) (47 - a)).
Lemma sc_mono_check : forallb sc_mono_fn (zseq 0 48) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma size_class_mono a b : 0 <= a -> a < b < 48 -> size_class a < size_class b.
Proof.
  intros Ha Hb. pose proof (forallb_zseq sc_mono_fn 0 48 a sc_mono_check ltac:(lia) ltac:(lia)) as X. unfold sc_mono_fn in X.
  pose proof (forallb_zseq _ (a + 1) (47 - a) b X ltac:(lia) ltac:(lia)) as Y. apply Z.ltb_lt in Y. exact Y.
Qed.


(* [comment removed for export] *)
Definition nest_fn (q : Z) : bool := let j := stc_q q in (0 <=? j) && (j <=? 26) && (q + 1 <=? size_class j).
Lemma nest_check : forallb nest_fn (zseq 1 127) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma nest_class_props q : 1 <= q <= 127 ->
  0 <= stc_q q <= 26 /\ q + 1 <= size_class (stc_q q).
Proof.
  intros Hq. pose proof (forallb_zseq nest_fn 1 127 q nest_check ltac:(lia) ltac:(lia)) as X. unfold nest_fn in X. cbv zeta in X.
  rewrite !Bool.andb_true_iff in X. destruct X as [[A B] C]. apply Z.leb_le in A. apply Z.leb_le in B. apply Z.leb_le in C. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPER.
Variables (st0 st : mstate) (m : mem).
Hypothesis MR : mrep st m.
Hypothesis ER : ENTRY_REL st0 st.


End FPER.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma unk_agree_xfer o stA mA stB mB : ltac2:(CDefT.buildp (gd_tbl_ASlot_M0 ()) "P,(2:.O4.O5.O3.)P,(1.(1=.$1:.$1>.$1?.$1;.)(21.O2.)(21.O4.))P,Prid,$1:.Pr,$2;.P,(1.$2<.(2=.R1.)$2>.)P,(1.(>.$2;.)(1<.$1:.$2;.(1=.$1:.$1>.$1?.$2;.)(20.$1:.$1>.$1?.$2;.)R3.(2?.O2.))(13.$2;.R2.))(1.(>.$2;.)(1<.$1:.$2;.(1=.$1:.$1>.$1?.$2;.)(20.$1:.$1>.$1?.$2;.)R4.(2?.O4.))(13.$2;.R3.))P,Pb,$15.(30.(31.$32.(1<.$15.$32.(1=.$15.(33.$1:.$1>.$4.$22.)(34.$1:.$1>.$1?.$4.$22.$23.)$32.)(20.$15.(33.$1:.$1>.$4.$22.)(34.$1:.$1>.$1?.$4.$22.$23.)$32.)R1.(35.O2.)))(31.$32.(1<.$15.$32.(1=.$15.(33.$1:.$1>.$4.$22.)(34.$1:.$1>.$1?.$4.$22.$23.)$32.)(20.$15.(33.$1:.$1>.$4.$22.)(34.$1:.$1>.$1?.$4.$22.$23.)$32.)R1.(35.O4.))))P,Prid,$1:.Pr,$2;.Poff,$4.Ph,$4.P,(1.(>.$2;.)(1<.$1:.$2;.(1=.$1:.$1>.$1?.$2;.)(20.$1:.$1>.$1?.$2;.)R4.(2?.O4.))(13.$2;.R3.))P,(1.$2<.(2=.R4.)$2>.)P,(0.(36.=R4.)(37.R4.(38.(39.R5.))))P,(1.$3:.(3;.(3<.O4.R7.)R5.)(3=.R4.))P,(3>.(3?.O4.R8.R6.))(1.(>.(40.&8.))A1.O1.(41.(42.(43.R8.)R7.))A1.O3.(41.(42.(43.R8.)R7.)))(2:.O2.O5.O1.)")
(* [comment removed for export] *).
Proof.
  intros UA ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow stA rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov stA rid off).
  { (intros dd_H; ddestruct dd_H as (bq & gh & Hbq & Hf & Hoff)). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. dexists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

(* [comment removed for export] *)
Lemma fm_proj st g : ltac2:(CDefT.buildp (gd_tbl_ASlot_M0 ()) "Zst',$<.(44.O2.O1.)(0.(1.(1=.$1:.$1>.$1?.$2;.)(2?.R1.)(2?.O2.))(0.(1.(1=.$1:.$1>.$1?.$1;.)(21.R1.)(21.O2.))(0.(1.(1=.$15.(33.$1:.$1>.$4.$22.)(34.$1:.$1>.$1?.$4.$22.$23.)$32.)(35.R1.)(35.O2.))(0.(1.(1=.$15.(33.$1:.$1>.$4.$22.)(34.$1:.$1>.$1?.$4.$22.$23.)$45.)(46.R1.)(46.O2.))(0.(1.(1=.$15.(33.$1:.$1>.$4.$22.)(34.$1:.$1>.$1?.$4.$22.$23.)(?.$15.$4.))(47.R1.)(47.O2.))(0.(1.$1:.(26.R1.)(26.O2.))(0.(1.$1:.(48.R1.)(48.O2.))(0.(1.(49.(?.$4.$4.))(4:.R1.)(4:.O2.))(0.Pc,$4.(1.$2.(4;.R2.R1.)(4;.O2.R1.))(0.Pi,$4.(1.$4.(4<.R2.R1.)(4<.O2.R1.))(0.(1.$4=.(4>.(4?.R1.))(4>.(4?.O2.)))(0.(1.$4.(50.(4?.R1.))(50.(4?.O2.)))(0.Pi,$4.(1.$4.(51.R2.R1.)(51.O2.R1.))(0.Pi,$4.(1.$4.(52.R2.R1.)(52.O2.R1.))(1.$4.(53.(4?.R1.))(53.(4?.O2.)))))))))))))))))")
(* [comment removed for export] *).
Proof.
  unfold as_fm_st, as_queue_st, as_fm_link, as_fm_single. cbn [get_head].
  destruct (c_free_meta_head (ctx (put_meta g meta0 st))) as [h|].
  - cbv zeta. destruct (m_prev (get_meta_rec (put_meta g meta0 st) h)) as [p|]; repeat split; reflexivity.
  - repeat split; reflexivity.
Qed.
