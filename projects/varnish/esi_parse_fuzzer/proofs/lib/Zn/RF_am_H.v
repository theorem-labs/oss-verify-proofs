(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MTree Mallx0z RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Mall17y RF_am_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_am_G.

Module RF_am_F.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MTree Mallx0z RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Mall17y RF_am_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_am_G.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.F_ntf_B OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A.RF_am_K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_G.RF_am_C.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree Mallkgx Mall17y RF_mk75 RF_ntf_A RF_am_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_am_G.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A.RF_am_K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_G.RF_am_C.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.

Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
Lemma carve_st_regions st p : s_regions (carve_st st p) = s_regions st.
Proof.
  unfold carve_st. cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail].
  destruct (c_meta_area_tail (s_ctx st)); reflexivity.
Qed.
Definition mp_strict (a : range_ans) : Prop := match a with RgErr e => e <> 38 | RgDone b => b = true end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma dec_mprotect_rw_weaken A L rsp a : dec_mprotect_rw A L rsp = Some a -> dec_mprotect A L rsp = Some a /\ mp_strict a.
Proof.
  unfold dec_mprotect_rw. destruct (dec_mprotect A L rsp) as [[e|b]|]; [| | discriminate].
  - destruct (Z.eqb_spec e ENOSYS); [discriminate|]. intros H; inversion H; subst. split; [reflexivity|]. cbn. unfold ENOSYS in *. exact n.
  - destruct b; [| discriminate]. intros H; inversion H; subst. split; reflexivity.
Qed.
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma am_disp_fin : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (p : aptr) (r : region),
  mrep st m -> c_avail_meta_area_count (ctx st) <> 0 -> 0 <= c_avail_meta_area_count (ctx st) < 2^64 ->
  c_avail_meta_areas (ctx st) = Some p -> (s_regions st) !! (fst p) = Some r -> pgal (snd p) -> 0 <= snd p -> snd p + 4096 <= round_up_pg (r_len r) ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st p)) (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23cc4) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b24) fc None m (seg_rom rsegs)).
Proof.
  intros until r. intros MR CNT CR AMA Hr SAL S0 S1.
  (first [ pose proof (MR) as dR_1; dand3 dR_1 as WF (C1 & _) _ | pose proof MR as (WF & (C1 & _) & _) ]). unfold ctx_head_cells in C1. rewrite AMA in C1.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  (first [ pose proof (WF) as dR_2; dand3 dR_2 as _ WR _ | pose proof WF as (_ & WR & _) ]). (first [ pose proof ((WR _ _ Hr)) as dR_3; dand5 dR_3 as RB0 RBAL RL0 RBC _ | destruct (WR _ _ Hr) as (RB0 & RBAL & RL0 & RBC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (conc_region' st p r Hr) as Cp. pose proof (round_up_pg_ge (r_len r)) as RU.
  assert (AL : Z.land (conc st p) 4095 = 0).
  { rewrite Cp. unfold pgal in SAL. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    clear - RBAL SAL S0 RB0. Z.div_mod_to_equations. lia. }
  assert (AL' : Z.land 4095 (conc st p) = 0) by (rewrite Z.land_comm; exact AL).
  assert (PB : 0 <= conc st p < 2^64) by lia.
  clear RBAL RU RBC RL0 WR.
  unfold CTX, MLOCK, SSP_GUARD in *.
  (* [comment removed for export] *)
  st1. st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 (c_avail_meta_area_count (ctx st))) (Z_to_bv 64 0)) = true)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Bool.negb_true_iff; apply Z.eqb_neq; exact CNT).
  rewrite CF.
  (* [comment removed for export] *)
  st1. apply Bool.negb_true_iff in CF. rewrite CF. clear CF.
  st1. st1.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 0)) with true. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_to_mprotect : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (P : Z),
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x23cd4) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P)
                                   (Z_to_bv 64 P) (Z_to_bv 64 4096) (Z_to_bv 64 3) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 mprotect_entry) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 P) a0 a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23cc4) fc None m (seg_rom rsegs)).
Proof.
  intros.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  apply evt_done. unfold mprotect_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_mp_ok0 : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte),
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23c34) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23cd4) fc None m (seg_rom rsegs)).
Proof.
  intros.
  st1. rewrite bv_eqb_refl. cbv iota.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_mp_fail : forall (sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 raw s0o s1o s2o s3o s4o : word) F fc
    (m0 m : word -> option byte) (junk : list byte) (lo e : Z) (st : mstate),
  mrep st m -> mem_inv rsegs m -> tp = Z_to_bv 64 0x424f8 ->
  rw_cells rsegs m (errno_addr tp) [C4 (Z_to_bv 64 e)] -> 1 <= e <= 4095 -> e <> 38 ->
  pres_except (am_fp st lo (bv_unsigned sp)) m0 m -> wmono rsegs m0 m ->
  rw_cells rsegs m (bv_unsigned sp + -64) (ram_frame junk s4o s3o s2o s1o s0o raw) ->
  stk rsegs m lo (bv_unsigned sp + -64) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 64 ->
  evt rsegs (fun ms' => am_ret_post raw sp gp tp s0o s1o s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 F fc lo st m0 st (Z_to_bv 64 0) ms'
                        /\ rw_cells rsegs (ms_mem ms') (errno_addr tp) [C4 (Z_to_bv 64 e)])
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23cd4) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MI TP ERR ER E38 PE0 WM0 FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (first [ pose proof (MR) as dR_4; dand4 dR_4 as _ _ (_ & _ & _ & _ & GUARD) _ | pose proof MR as (_ & _ & (_ & _ & _ & _ & GUARD) & _) ]).
  subst tp. rewrite (unsigned_lit 0x424f8) in * by lia. change (271608 + -164) with 271444 in *.
  change (Z_to_bv 64 e) with (wz e) in ERR.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK, SSP_GUARD, ram_frame in *.
  (* [comment removed for export] *)
  st1. change (bv_eqb (Z_to_bv 64 (-1)) (Z_to_bv 64 0)) with false. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  (* [comment removed for export] *)
  st1. rewrite sx32_wz by lia. st1. st1.
  assert (CF : bv_eqb (wz e) (Z_to_bv 64 38) = false)
    by (unfold bv_eqb, wz; rewrite !unsigned_lit by lia; apply Z.eqb_neq; exact E38).
  rewrite CF; clear CF.
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  st1. st1. st1. st1. st1. st1. st1. st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MRX : mrep st mX) end.
  { eapply mrep_transport_high; [exact MR| exact MU| exact WM|]. intros l h [E|[]]; inversion E; subst; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia. }
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. split.
  - unfold am_ret_post. do 15 eexists. split; [reflexivity|].
    split.
    { eapply pres_except_trans; [exact PE0|].
      apply (pres_except_of_munch_cov (am_fp st lo (bv_unsigned sp))) in MU; [exact MU|exact WM|].
      cbn [ivs_covered]. split; [|exact I]. intros x Hx. apply am_fp_stack. lia. }
    split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [assumption|]. split; [exact ST|]. exact MRX.
  - cbn [ms_mem]. change (wz e) with (Z_to_bv 64 e) in ERR. exact ERR.
Qed.

End CEIL.
End RF_am_F.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_am_G.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.F_ntf_B OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A.RF_am_K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_G.RF_am_C OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_H.RF_am_F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_G.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require KLink.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree Mallkgx Mall17y RF_mk75 RF_ntf_A RF_am_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_am_G.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_am_G.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A.RF_am_K OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_G.RF_am_C OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_H.RF_am_F OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_am_G.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u F_mm4hw MRep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaLt.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaLt.lia_tuned.
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

Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_neg_aligned cur : 0 < cur < 2^64 -> cur mod 4096 = 0 -> Z.land (bv_unsigned (Z_to_bv 64 (0 + - cur))) 4095 = 0.
Proof.
  intros H AL. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  replace ((0 + - cur) mod 2^64) with ((2^52 - cur / 4096) * 4096) by (Z.div_mod_to_equations; lia).
  change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. change (2^12) with 4096. apply Z.mod_mul. lia.
Qed.
Lemma brk_new_pages_aligned cur n : 0 <= cur -> 0 < n -> cur mod 4096 = 0 -> n mod 4096 = 0 ->
  brk_new_pages cur (cur + n) = Some (cur, n).
Proof.
  intros C0 N0 CA NA. unfold brk_new_pages. rewrite <- !KLink.round_up_pg_eq.
  rewrite !KLink.round_up_pg_aligned by (auto; rewrite Z.add_mod, CA, NA by lia; reflexivity).
  replace (cur <? cur + n) with true by (symmetry; apply Z.ltb_lt; lia). f_equal. f_equal. lia.
Qed.
Definition fx_rel (A : Z) (a : fixed_ans) (r : word) (u : bool) : Prop :=
  match a with
  | FxKept e => errno_of r = Some e /\ u = false
  | FxDone => r = Z_to_bv 64 A /\ u = true
  | FxLost e => errno_of r = Some e /\ u = true
  end.
Lemma dec_mmap_fixed_shape A L rsp a : dec_mmap_fixed A L rsp = Some a -> exists r u, fx_rel A a r u /\ rsp = fixed_shape A L r u.
Proof.
  unfold dec_mmap_fixed, fixed_shape. destruct rsp as [r ws zs us cps cis].
  destruct ws; [| discriminate]. destruct zs; [| discriminate]. destruct us as [|[ua un] us].
  - destruct cps; [| discriminate]. destruct cis; [| discriminate].
    destruct (errno_of r) eqn:E; [| discriminate]. intros H; inversion H; subst. exists r, false. cbn. rewrite E. auto.
  - destruct us; [| discriminate]. destruct cps; [| discriminate]. destruct cis; [| discriminate].
    destruct (bv_eqb ua (Z_to_bv 64 A) && bv_eqb un (Z_to_bv 64 (mmap_len L))) eqn:E; [| discriminate].
    apply andb_prop in E. destruct E as [E1 E2]. apply Fs.bv_eqb_eq in E1. apply Fs.bv_eqb_eq in E2. subst ua un.
    destruct (errno_of r) eqn:E.
    + intros H; inversion H; subst. exists r, true. cbn. rewrite E. auto.
    + destruct (bv_eqb r (Z_to_bv 64 A)) eqn:E3; [| discriminate]. apply Fs.bv_eqb_eq in E3. intros H; inversion H; subst. exists (Z_to_bv 64 A), true. cbn. auto.
Qed.
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma am_disp_untried : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate),
  mrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkUntried ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b60) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b24) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR CNT BRK.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold CTX, MLOCK, SSP_GUARD in *. change (403456 + 912) with 404368 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  change (bv_eqb (Z_to_bv 64 0) (Z_to_bv 64 (-1))) with false. cbv iota.
  st1. rewrite bv_eqb_refl. cbv iota.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma am_disp_live : forall (sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) F fc
    (m : word -> option byte) (st : mstate) (rid : N) (off : Z),
  mrep st m -> c_avail_meta_area_count (ctx st) = 0 -> c_brk (ctx st) = BrkLive rid off ->
  0 < conc st (rid, off) -> conc st (rid, off) + 4096 < 2^64 ->
  evt rsegs (fun ms' => ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (conc st (rid, off) + 4096))
                                   (Z_to_bv 64 (conc st (rid, off) + 4096)) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                             F (Z_to_bv 64 0x23b48) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b24) fc None m (seg_rom rsegs)).
Proof.
  intros until off. intros MR CNT BRK C0 C1b.
  pose proof MR as (WF & (C1 & _ & _ & _ & _ & C6) & _). unfold ctx_head_cells in C1. rewrite CNT in C1.
  unfold ctx_tail_cells, brk_word in C6. rewrite BRK in C6.
  unfold pw in C1. cbn [oconc] in C1. unfold wz in C1, C6.
  unfold CTX, MLOCK, SSP_GUARD in *. change (403456 + 912) with 404368 in C6.
  (* [comment removed for export] *)
  st1. st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  (* [comment removed for export] *)
  st1. st1. st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 (-1)) = false)
    by (unfold bv_eqb; rewrite (unsigned_lit (conc st (rid, off))) by lia; change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1)%Z; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 (conc st (rid, off))) (Z_to_bv 64 0) = false)
    by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1. st1. st1.
  apply evt_done. reflexivity.
Qed.

End CEIL.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section BRKNODES.

Variables (x1 sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
          (m : word -> option byte).

Definition brk_res (cur req : Z) (a : brk_ans) : Z := match a with BrkGrown => req | BrkSame => cur end.
Definition brk_mem (cur req : Z) (a : brk_ans) : word -> option byte :=
  match a with
  | BrkGrown => match brk_new_pages cur req with Some (lo, n) => apply_zeros m [(wa lo, Z_to_bv 64 n)] | None => m end
  | BrkSame => m
  end.
Definition brk_regs (a0 : word) : _ :=
  mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma am_brk0_node :
  impl rsegs (at_node rsegs) (enode (NBrk 0) dec_brk0)
       (epost (fun r ms' => ms' = MS (brk_regs (Z_to_bv 64 r)) F (Z_to_bv 64 0x23b64) fc None m (seg_rom rsegs) /\ 0 <= r < 2^64))
       (MS (brk_regs (Z_to_bv 64 0)) F (Z_to_bv 64 0x23b60) fc None m (seg_rom rsegs)).
Proof.
  unfold brk_regs. apply impl_enode. step_ecall. split. { at_node_solve. }
  intros rsp r Hdec. apply dec_brk0_Some in Hdec. destruct Hdec as [-> Hr]. unfold eff0.
  rewrite nret_MSsvc, mkR_set_a0, apply_mem_none, lit_add_lit. replace (0x23b60 + 4)%Z with 0x23b64%Z by reflexivity.
  apply evt_done. split; [reflexivity| exact Hr].
Qed.

(* [comment removed for export] *)
Lemma am_brk_node_at (pc : Z) :
  (pc = 0x23b48 \/ pc = 0x23b84) -> forall cur req, req <> 0 ->
  impl rsegs (at_node rsegs) (enode (NBrk req) (dec_brk cur req))
       (epost (fun a ms' => ms' = MS (brk_regs (Z_to_bv 64 (brk_res cur req a))) F (Z_to_bv 64 (pc + 4)) fc None (brk_mem cur req a) (seg_rom rsegs)))
       (MS (brk_regs (Z_to_bv 64 req)) F (Z_to_bv 64 pc) fc None m (seg_rom rsegs)).
Proof.
  intros Hpc cur req NZ. unfold brk_regs.
  destruct Hpc as [-> | ->]; (apply impl_enode; step_ecall; split; [at_node_solve|]);
    intros rsp a Hdec; apply dec_brk_Some in Hdec; (destruct a; rewrite Hdec; unfold eff0, brk_res, brk_mem, zeros_of;
      rewrite nret_MSsvc, mkR_set_a0, lit_add_lit;
      [ destruct (brk_new_pages cur req) as [[lo n]|]; [rewrite apply_mem_zeros | rewrite apply_mem_none]
      | rewrite apply_mem_none ];
      apply evt_done; reflexivity).
Qed.
End BRKNODES.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_bu_mid : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur < 2^64 -> cur mod 4096 = 0 ->
  rw_cells rsegs m (CTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a2' m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) a2' a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x23b84) fc None m' (seg_rom rsegs)
        /\ munch [(CTX + 920, CTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' (CTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 cur) (Z_to_bv 64 4095) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b64) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros CR CAL TC MI.
  pose proof (munch_refl [(CTX + 920, CTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (land_neg_aligned cur CR CAL) as AL.
  assert (AL' : Z.land 4095 (bv_unsigned (Z_to_bv 64 (0 + - cur))) = 0) by (rewrite Z.land_comm; exact AL).
  change (cur mod 4096 = 0) with (pgal cur) in CAL.
  unfold CTX, MLOCK, SSP_GUARD in *. change (403456 + 912) with 404368 in TC. change (403456 + 920) with 404376 in MU. change (403456 + 928) with 404384 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?AL, ?AL'. st1. st1.
  replace (0 + cur) with cur by lia.
  (* [comment removed for export] *)
  st1. st1. st1. st1.
  replace (8192 + cur) with (cur + 8192) by lia.
  apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact TC.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_bu_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word) (q0 : byte) (q1 : list byte) F fc
    (m : word -> option byte) (cur : Z),
  0 < cur -> cur + 8192 < 2^64 ->
  rw_cells rsegs m (CTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] ->
  evt rsegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x23ba8) sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192))
                                   (Z_to_bv 64 cur) (Z_to_bv 64 4096) (Z_to_bv 64 0) (Z_to_bv 64 50) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 (Z_to_bv 64 214)
                                   (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (Z_to_bv 64 mmap_entry) fc None m (seg_rom rsegs))
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 (cur + 8192)) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b88) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros C0 C1b TC.
  unfold CTX, MLOCK, SSP_GUARD in *. change (403456 + 912) with 404368 in TC.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbn [negb]. cbv iota.
  st1. st1. st1. st1. st1. st1. st1.
  apply evt_done. unfold mmap_entry. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma am_b_store : forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells rsegs m CTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells rsegs m (CTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) a0 a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x23c34) fc None m' (seg_rom rsegs)
        /\ munch [(CTX + 40, CTX + 48); (CTX + 920, CTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' CTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells rsegs m' (CTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23ba8) fc None m (seg_rom rsegs)).
Proof.
  intros until nw. intros NW HC TC MI.
  pose proof (munch_refl [(CTX + 40, CTX + 48); (CTX + 920, CTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold CTX, MLOCK, SSP_GUARD in *. change (403456 + 912) with 404368 in TC.
  change (403456 + 40) with 403496 in MU. change (403456 + 48) with 403504 in MU. change (403456 + 920) with 404376 in MU. change (403456 + 928) with 404384 in MU.
  (* [comment removed for export] *)
  st1. st1. rewrite ?(unsigned_lit nw) by lia. replace (nw + - (4096)) with (nw - 4096) by lia. st1. change (Z.shiftr 4096 12) with 1. st1. st1.
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact HC| exact TC].
Qed.

(* [comment removed for export] *)
Lemma am_bl_ok : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 : word) (q0 : byte) (q1 : list byte) (q2 : word) F fc (m : word -> option byte) (nw : Z),
  0 <= nw < 2^64 ->
  rw_cells rsegs m CTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 w6; C8 w7; C8 w8; C8 w9; C8 w10] ->
  rw_cells rsegs m (CTX + 912) [C1 q0; CB 7 q1; C8 q2] -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 1) (Z_to_bv 64 (nw - 4096)) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x23c34) fc None m' (seg_rom rsegs)
        /\ munch [(CTX + 40, CTX + 48); (CTX + 920, CTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ rw_cells rsegs m' CTX [C8 w0; C4 w1; C4 w2; C8 w3; C8 w4; C8 w5; C8 (Z_to_bv 64 1); C8 w7; C8 w8; C8 w9; C8 w10]
        /\ rw_cells rsegs m' (CTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 nw)])
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 nw) (Z_to_bv 64 nw) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b4c) fc None m (seg_rom rsegs)).
Proof.
  intros until nw. intros NW HC TC MI.
  (* [comment removed for export] *)
  st1. rewrite bv_eqb_refl. cbv iota.
  eapply (am_b_store sp gp tp t0 t1 t2 _ a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 q0 q1 q2 F fc m nw NW HC TC MI).
Qed.

(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma am_brk_dead : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) (q2 : word) F fc (m0 m : word -> option byte) (st : mstate),
  mrep st m0 -> munch [(CTX + 920, CTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 ->
  rw_cells rsegs m (CTX + 912) [C1 q0; CB 7 q1; C8 q2] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 a7
                      (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23bd4) fc None m' (seg_rom rsegs)
        /\ munch [(CTX + 920, CTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ mrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23bbc) fc None m (seg_rom rsegs)).
Proof.
  intros until st. intros MR MU0 WM0 CNT TC -> -> MI.
  pose proof MR as (WF & (C1 & _) & _). unfold ctx_head_cells in C1. rewrite CNT in C1. unfold pw in C1. cbn [oconc] in C1. unfold wz in C1.
  lazymatch type of C1 with rw_cells _ _ _ ?cs =>
    assert (C1' : rw_cells rsegs m CTX cs)
      by (eapply Mallkgx.rw_cells_agree; [exact C1| | exact WM0]; cbn [cells_size csize Nat.add]; intros y Hy; apply MU0;
          rewrite wa_unsigned by (unfold CTX in *; lia); unfold CTX in *; cbn; lia) end.
  clear C1.
  pose proof (munch_refl [(CTX + 920, CTX + 928)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  unfold CTX, MLOCK, SSP_GUARD in *. change (403456 + 912) with 404368 in TC.
  change (403456 + 920) with 404376 in MU, MU0. change (403456 + 928) with 404384 in MU, MU0.
  (* [comment removed for export] *)
  st1. st1. st1. st1. rewrite bv_eqb_refl. cbv iota.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) => assert (MR' : mrep (upd_ctx (set_brk BrkDead) st) mX) end.
  { eapply (mrep_ctx_frameW st _ m0 _ [(CTX + 920, CTX + 928)]%Z MR); try reflexivity.
    - unfold CTX. first [exact MU0 | eapply munch_trans; [exact MU0| exact MU]].
    - first [exact WM0 | eapply wmono_trans; [exact WM0| exact WM]].
    - intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.
    - right. split; [reflexivity|]. intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia.
    - left. unfold ctx_tail_cells, brk_word, CTX. cbn [ctx upd_ctx s_ctx set_brk c_brk c_seq]. change (403456 + 912) with 404368.
      replace (wz (2 ^ 64 - 1)) with (Z_to_bv 64 (-1)) by (apply Z_to_bv_eqm; reflexivity).
      lazymatch goal with H : rw_cells rsegs ?mX 404368 _ |- _ => exact H end. }
  apply evt_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact MR'.
Qed.

(* [comment removed for export] *)
Lemma am_bl_fail : forall (sp gp tp t0 t1 t2 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    F fc (m : word -> option byte) (st : mstate) (old : Z),
  mrep st m -> c_avail_meta_area_count (ctx st) = 0 -> 0 < old -> old + 4096 < 2^64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23bd4) fc None m' (seg_rom rsegs)
        /\ munch [(CTX + 920, CTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ mrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (old + 4096)) (Z_to_bv 64 old) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b4c) fc None m (seg_rom rsegs)).
Proof.
  intros until old. intros MR CNT O0 O1 MI.
  pose proof MR as (WF & (_ & _ & _ & _ & _ & C6) & _). unfold ctx_tail_cells in C6.
  (* [comment removed for export] *)
  st1.
  assert (CF : bv_eqb (Z_to_bv 64 old) (Z_to_bv 64 (old + 4096)) = false) by (unfold bv_eqb; rewrite !unsigned_lit by lia; apply Z.eqb_neq; lia).
  rewrite CF; clear CF.
  st1.
  eapply (am_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m m st MR (munch_refl _ m) (wmono_refl rsegs m) CNT C6 eq_refl eq_refl MI).
Qed.

(* [comment removed for export] *)
Lemma am_bu_fail : forall (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (q0 : byte) (q1 : list byte) F fc (m0 m : word -> option byte) (st : mstate) (cur : Z),
  mrep st m0 -> munch [(CTX + 920, CTX + 928)]%Z m0 m -> wmono rsegs m0 m ->
  c_avail_meta_area_count (ctx st) = 0 -> 0 < cur -> cur < 2^64 ->
  rw_cells rsegs m (CTX + 912) [C1 q0; CB 7 q1; C8 (Z_to_bv 64 cur)] -> q0 = b8 (c_seq (ctx st)) -> q1 = zeros 7 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists m',
        ms' = MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 0) (Z_to_bv 64 (-1)) a2 a3 a4 a5 a6 (Z_to_bv 64 214)
                      (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23bd4) fc None m' (seg_rom rsegs)
        /\ munch [(CTX + 920, CTX + 928)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
        /\ mrep (upd_ctx (set_brk BrkDead) st) m')
      (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 4096) (Z_to_bv 64 (cur + 8192)) (Z_to_bv 64 cur) a1 a2 a3 a4 a5 a6 (Z_to_bv 64 214)
               (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 MLOCK) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x23b88) fc None m (seg_rom rsegs)).
Proof.
  intros until cur. intros MR MU0 WM0 CNT C0 C1b TC -> -> MI.
  (* [comment removed for export] *)
  st1.
  assert (CF : negb (bv_eqb (Z_to_bv 64 cur) (Z_to_bv 64 (cur + 8192))) = true).
  { apply Bool.negb_true_iff. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
    apply Z.eqb_neq. rewrite (Z.mod_small cur) by lia. Z.div_mod_to_equations. lia. }
  rewrite CF; clear CF.
  eapply (am_brk_dead sp gp tp t0 t1 t2 _ _ _ _ a2 a3 a4 a5 a6 _ s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 _ _ _ F fc m0 m st MR MU0 WM0 CNT TC eq_refl eq_refl MI).
Qed.

End CEIL2.
