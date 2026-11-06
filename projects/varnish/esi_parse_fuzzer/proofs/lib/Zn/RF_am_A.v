(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MTree Mallx0z RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.F_ntf_B OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import MRep MRepAux MTree Mallkgx Mall17y RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition am_took (st : mstate) (q : aptr) (cnt : Z) : mstate :=
  upd_meta q clr_links (upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
Definition am_fp (st : mstate) (lo sp : Z) (a : Z) : Prop :=
  lo <= a < sp
  \/ CTX <= a < CTX + 928
  \/ exists rid r, (s_regions st) !! rid = Some r /\ r_kind r <> RKGroup /\ lr_lo r <= a < r_base r + round_up_pg (r_len r).

Lemma am_fp_alloc_fp st lo sp a : am_fp st lo sp a -> alloc_fp (fun k => k <> RKGroup) st lo sp a.
Proof. unfold am_fp, alloc_fp. tauto. Qed.
Lemma am_fp_stack st lo sp a : lo <= a < sp -> am_fp st lo sp a.
Proof. intros; left; assumption. Qed.
Lemma am_fp_ctx st lo sp a : CTX <= a < CTX + 928 -> am_fp st lo sp a.
Proof. intros; right; left; assumption. Qed.
Lemma am_fp_region st lo sp a rid r : (s_regions st) !! rid = Some r -> r_kind r <> RKGroup ->
  lr_lo r <= a < r_base r + round_up_pg (r_len r) -> am_fp st lo sp a.
Proof. intros; right; right. exists rid, r. auto. Qed.
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma am_fp_not_errno st lo sp a : am_fp st lo sp a -> regions_wf st -> alloc_ceiling <= lo ->
  ~ (errno_addr (Z_to_bv 64 0x424f8) <= a < errno_addr (Z_to_bv 64 0x424f8) + 4).
Proof.
  (intros [H|[H|(rid & r & Hr & _ & H)]]; (first [ intro dR_12; dand3 dR_12 as _ WR _ | intros (_ & WR & _) ]); intros LO); (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX in *; rewrite ?unsigned_lit by lia; try lia.
  (first [ pose proof ((WR _ _ Hr)) as dR_1; dand5 dR_1 as _ _ _ RBC RF | destruct (WR _ _ Hr) as (_ & _ & _ & RBC & RF) ]). (first [ pose proof ((reserved_disjoint _ _ RF)) as dR_2; dand4 dR_2 as _ _ D23 D2 | destruct (reserved_disjoint _ _ RF) as (_ & _ & D23 & D2) ]).
  pose proof (lr_lo_ge r). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
Qed.
Lemma am_fp_meta : forall st m lo sp q a, mrep st m -> meta_slot st q ->
  conc st q <= a < conc st q + 40 -> am_fp st lo sp a.
Proof.
  (intros st m lo sp q a MR; (first [ intro dR_13; dex3 dR_13 as ar arr k; dand3 dR_13 as Har Hk Eq | intro dR_13; dand6 dR_13 as ar arr k Har Hk Eq | intros (ar & arr & k & Har & Hk & Eq) ]); intros Ha). pose proof MR as (WF & _).
  (first [ pose proof ((area_conc st ar arr WF Har)) as dR_3; dex1 dR_3 as ra; dand9 dR_3 as Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | pose proof ((area_conc st ar arr WF Har)) as dR_3; dand10 dR_3 as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | destruct (area_conc st ar arr WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]).
  assert (HG : conc st q = conc st ar + (AREA_HDR + META_SIZE * k)) by (rewrite Eq, conc_aadd by (rewrite Hra; eauto); reflexivity).
  pose proof (area_lr_lo st ar arr ra WF Har Hra).
  unfold AREA_HDR, META_SIZE, NSLOTS in *.
  eapply am_fp_region; [exact Hra | exact NK | lia].
Qed.
(* [comment removed for export] *)
Lemma am_fp_area : forall st m lo sp ak ar a, mrep st m -> (s_areas st) !! ak = Some ar ->
  conc st ak <= a < conc st ak + 4096 -> am_fp st lo sp a.
Proof.
  intros st m lo sp ak ar a MR Har Ha. pose proof MR as (WF & _).
  (first [ pose proof ((area_conc st ak ar WF Har)) as dR_4; dex1 dR_4 as ra; dand9 dR_4 as Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | pose proof ((area_conc st ak ar WF Har)) as dR_4; dand10 dR_4 as ra Hra Ca Sa0 Sa1 SaL NK RB0 RBAL RBC | destruct (area_conc st ak ar WF Har) as (ra & Hra & Ca & Sa0 & Sa1 & SaL & NK & RB0 & RBAL & RBC) ]).
  pose proof (area_lr_lo st ak ar ra WF Har Hra).
  eapply am_fp_region; [exact Hra | exact NK | lia].
Qed.
Lemma am_fp_same st st' lo sp a : s_regions st' = s_regions st -> am_fp st' lo sp a <-> am_fp st lo sp a.
Proof. intros ER. unfold am_fp. rewrite ER. tauto. Qed.

(* [comment removed for export] *)
Definition am_ret_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (stF : mstate) (m : word -> option byte) (st' : mstate) (rv : word) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 rv a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ pres_except (am_fp stF lo (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ mrep st' m'.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ram_frame (junk : list byte) (s4 s3 s2 s1 s0 ra : word) : list cell :=
  [CB 8 junk; C8 (wz run_guard); C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_tail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo : Z) (st : mstate) (q : aptr),
  mrep st m -> mem_inv rsegs m -> meta_slot st q ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (am_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (upd_meta q clr_links st) (Z_to_bv 64 (conc st q)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23c90) fc None m (seg_rom rsegs)).
Proof.
  intros until q. intros MR MI MSq FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (first [ pose proof ((meta_slot_bounds st _ q MR MSq)) as dR_5; dand5 dR_5 as GB0 GB1 GB2 GB4 _ | pose proof (meta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _) ]).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (conc st q, conc st q + 40)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof (MR) as dR_6; dand4 dR_6 as _ _ (_ & _ & _ & _ & GUARD) _ | pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _) ]).
  meta_chunk MR MSq CH.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold SSP_GUARD, ram_frame in *.
  meta_open (conc st q) MUq WMq.
  (* [comment removed for export] *)
  st1. st1.
  meta_close MR MSq MUq WMq CH (put_meta q (clr_links (get_meta_rec st q)) st) MR2.
  rewrite <- upd_meta_put in MR2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z mX) as MUs; pose proof (wmono_refl rsegs mX) as WMs end.
  (* [comment removed for export] *)
  st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : mrep (upd_meta q clr_links st) mX)
      by (eapply mrep_transport_high; [exact MR2 | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]) end.
  clear MUs WMs.
  release_frame FR ST (bv_unsigned sp).
  apply (pres_except_of_munch_cov (am_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
  2:{ cbn [ivs_covered]. split; [|split; [|exact I]].
      - intros x Hx. apply am_fp_stack. lia.
      - intros x Hx. eapply am_fp_meta; [exact MR | exact MSq | lia]. }
  apply evt_done. unfold am_ret_post. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact MR3.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_b0 : forall (sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m : word -> option byte) (junk : list byte) (lo cnt : Z) (st : mstate) (q : aptr),
  mrep st m -> mem_inv rsegs m -> meta_slot st q -> 0 <= cnt < 2^64 ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (am_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m (am_took st q cnt) (Z_to_bv 64 (conc st q)))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (conc st q)) (Z_to_bv 64 cnt) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23c84) fc None m (seg_rom rsegs)).
Proof.
  intros until q. intros MR MI MSq HC FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (first [ pose proof ((meta_slot_bounds st _ q MR MSq)) as dR_7; dand5 dR_7 as GB0 GB1 GB2 GB4 _ | pose proof (meta_slot_bounds st _ q MR MSq) as (GB0 & GB1 & GB2 & GB4 & _) ]).
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp); (CTX, CTX + 928)]%Z m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof (MR) as dR_8; dand3 dR_8 as WF (C1 & _) _ | pose proof MR as (WF & (C1 & _) & _) ]). unfold ctx_head_cells in C1.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK in *.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    pose proof (munch_refl [(CTX + 24, CTX + 40)]%Z mX) as MUc; pose proof (wmono_refl rsegs mX) as WMc end.
  unfold CTX in MUc.
  (* [comment removed for export] *)
  st1. st1. st1.
  set (st1 := upd_ctx (fun c => set_avail_meta (Some (aadd q META_SIZE)) (set_avail_meta_count cnt c)) st).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR1 : mrep st1 mX) end.
  { eapply (mrep_ctx_frameW st st1 _ _ _ MR MUc WMc); try reflexivity.
    - intros lo' hi' [E|[]]; inversion E; subst. unfold CTX. lia.
    - left. unfold ctx_head_cells, CTX. cbn [ctx st1 upd_ctx s_ctx set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
            c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
      unfold pw at 2. cbn [oconc]. change (conc st1 (aadd q META_SIZE)) with (conc st (aadd q META_SIZE)).
      rewrite (conc_aadd st q META_SIZE) by ((first [ dex3 MSq as a ar k; dand3 MSq as Ha Hk -> | dand6 MSq as a ar k Ha Hk -> | destruct MSq as (a & ar & k & Ha & Hk & ->) ]); cbn; pose proof MR as (WF' & _);
          (first [ pose proof ((area_conc st a ar WF' Ha)) as dR_10; dex1 dR_10 as ra; destruct dR_10 as [Hra _] | pose proof ((area_conc st a ar WF' Ha)) as dR_10; dand3 dR_10 as ra Hra _ | destruct (area_conc st a ar WF' Ha) as (ra & Hra & _) ]); rewrite Hra; eauto).
      unfold META_SIZE, wz. exact C1.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold CTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold CTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold CTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold CTX. lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst. unfold CTX. lia. }
  clear MUc WMc C1.
  change (conc st q) with (conc st1 q).
  eapply evt_mono.
  { eapply (am_tail sp gp tp _ _ _ s0 s1 _ _ _ _ _ _ _ _ s4 s5 s6 s7 s8 s9 s10 s11 _ _ _ _ x1 raw s0o s1o s2o s3o s4o F fc _ junk lo st1 q);
      [exact MR1 | assumption | exact MSq | exact FR | exact ST | (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia | lia]. }
  intros ms' RP. unfold am_ret_post in RP |- *.
  (first [ dex15 RP as v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 m'; dand6 RP as -> PE' WM' MI' ST' MR' | dand21 RP as v0 v1 v2 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 v14 m' -> PE' WM' MI' ST' MR' | destruct RP as (v0 & v1 & v2 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & v14 & m' & -> & PE' & WM' & MI' & ST' & MR') ]).
  do 15 eexists. split; [reflexivity|].
  split.
  { apply (pres_except_of_munch_cov (am_fp st lo (bv_unsigned sp))) in MU; [|exact WM|].
    - eapply pres_except_trans; [exact MU|]. eapply pres_except_mono; [exact PE'|]. intros a Ha. apply (proj1 (am_fp_same st st1 lo _ a eq_refl)). exact Ha.
    - cbn [ivs_covered]. split; [|split; [|exact I]].
      + intros x Hx. apply am_fp_stack. lia.
      + intros x Hx. apply am_fp_ctx. unfold CTX. lia. }
  split; [eapply wmono_trans; [exact WM| exact WM']|]. split; [exact MI'|]. split; [exact ST'|]. exact MR'.
Qed.

End CEIL.
