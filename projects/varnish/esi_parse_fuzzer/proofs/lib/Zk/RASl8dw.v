(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlh4s RASlot_I.

Module RASl99y.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RAlllfc RASlot_I Malluin RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallx0z.F_ntf_B.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep MRepAux.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac mem_side := cbn; first [ (let E := fresh "E" in intros E; discriminate E) | solve [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [ exact I | reflexivity ] ] | solve [ repeat first [ left; reflexivity | right ] ] | tauto ].
Local Ltac mem_hyp Hr := cbn in Hr; first [ solve [ repeat (destruct Hr as [Hr|Hr]; [discriminate Hr|]); first [ discriminate Hr | destruct Hr ] ] | intuition discriminate ].
(* [comment removed for export] *)

Definition as_fm_link (st0 : mstate) (g head : aptr) : mstate :=
  let hprev := m_prev (get_meta_rec st0 head) in
  let st1 := upd_meta g (fun r => m_set_prev hprev (m_set_next (Some head) r)) st0 in
  let st2 := match hprev with Some pv => upd_meta pv (m_set_next (Some g)) st1 | None => st1 end in
  upd_meta head (m_set_prev (Some g)) st2.
Definition as_fm_single (st0 : mstate) (h : lhead) (g : aptr) : mstate :=
  set_head h (Some g) (upd_meta g (fun r => m_set_prev (Some g) (m_set_next (Some g) r)) st0).
Definition as_queue_st (h : lhead) (g : aptr) (st0 : mstate) : mstate :=
  match get_head st0 h with
  | Some head => as_fm_link st0 g head
  | None => as_fm_single st0 h g
  end.
Lemma as_queue_eq : forall R h g st0 (k : mstate -> Malloc.M R) (bail : Malloc.M R),
  m_next (get_meta_rec st0 g) = None -> m_prev (get_meta_rec st0 g) = None ->
  queue h g st0 k bail = k (as_queue_st h g st0).
Proof.
  intros R h g st0 k bail Hn Hp. unfold queue, guard. rewrite Hn, Hp. cbn [optr_eqb].
  unfold as_queue_st, as_fm_link, as_fm_single. destruct (get_head st0 h); reflexivity.
Qed.
Definition as_fm_st (st : mstate) (g : aptr) : mstate := as_queue_st LFree g (put_meta g meta0 st).
Lemma as_free_meta_eq : forall R st g (k : mstate -> Malloc.M R) (bail : Malloc.M R), free_meta g st k bail = k (as_fm_st st g).
Proof.
  intros. unfold free_meta, as_fm_st. apply as_queue_eq; rewrite get_meta_rec_put_same; reflexivity.
Qed.
Lemma outside_In W x lo hi : outside W x -> In (lo, hi) W -> ~ (lo <= x < hi).
Proof.
  induction W as [|[a b] W IH]; cbn; intros HO HI; [destruct HI|].
  destruct HI as [E|HI]; [inversion E; subst; tauto|]. apply IH; tauto.
Qed.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma mrep_set_free_head : forall st m v,
  mrep st m ->
  mrep (upd_ctx (set_free_meta_head v) st) (write_to_mem m (wa (CTX + 16)) (le8 (pw st v))).
Proof.
  intros st m v MR. (first [ pose proof (MR) as dR_1; dand3 dR_1 as _ (X1 & X2 & X3 & X4 & X5 & X6) _ | pose proof MR as (_ & (X1 & X2 & X3 & X4 & X5 & X6) & _) ]).
  pose proof (length_le8 (pw st v)) as L8.
  pose proof (munch_write [(CTX + 16, CTX + 24)] m m (CTX + 16) (le8 (pw st v)) (munch_refl _ m)
                ltac:(unfold CTX; lia) ltac:(rewrite L8; unfold CTX; lia) ltac:(rewrite L8; cbn [inside]; lia)) as MU.
  pose proof (wmono_write rsegs m m (wa (CTX + 16)) (le8 (pw st v)) (wmono_refl rsegs m)) as WM.
  eapply (mrep_ctx_frameW st (upd_ctx (set_free_meta_head v) st) m _ _ MR MU WM); try reflexivity.
  - intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia.
  - left.
    pose proof (rw_cells_write rsegs m CTX (ctx_head_cells st) 16 (C8 (pw st (c_free_meta_head (ctx st)))) (C8 (pw st v)) X1 eq_refl eq_refl I) as W.
    cbn [cbytes cell_upd ctx_head_cells Nat.eqb Z.of_nat Pos.of_succ_nat Pos.succ] in W.
    unfold ctx_head_cells, ctx in *. cbn [s_ctx upd_ctx set_free_meta_head c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
      c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
    exact W.
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
  - right. split; [reflexivity| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
  - right. split; [| intros lo hi [E|[]]; inversion E; subst; unfold CTX; lia].
    unfold ctx_tail_cells, brk_word, ctx. cbn [s_ctx upd_ctx set_free_meta_head c_seq c_brk]. reflexivity.
Qed.

Lemma mrep_extW : forall stX stY m,
  mrep stX m ->
  s_regions stY = s_regions stX -> ctx stY = ctx stX -> (forall q, get_meta_rec stY q = get_meta_rec stX q) ->
  s_areas stY = s_areas stX -> s_groups stY = s_groups stX -> (forall rid, get_shadow stY rid = get_shadow stX rid) ->
  s_reserved stY = s_reserved stX ->
  mrep stY m.
Proof.
  (intros stX stY m; (first [ intro dR_14; dand6 dR_14 as WF CX GL AR GR SH | intros (WF & CX & GL & AR & GR & SH) ]); intros ER EC EM EA EG ES ERs).
  assert (Hconc : forall q, conc stY q = conc stX q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - unfold regions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - eapply mrep_ctx_ext; [exact EC| exact Hconc| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply area_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply group_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply shadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

End CEIL.

(* [comment removed for export] *)
Ltac rraw_store_finishF A bs' FR MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, CTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame rsegs mX _ _ A bs') in FR; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [cells_size csize Nat.add]; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [inside]; lia];
    apply (wmono_write rsegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv rsegs mX |- _ =>
      apply (mem_inv_store rsegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, CTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.

Section FAILM.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (mt : aptr).
Let G := conc st mt.
Hypothesis MST : meta_slot st mt.
(* [comment removed for export] *)
Hypothesis FL : forall h, c_free_meta_head (ctx st) = Some h ->
  meta_slot st h /\ h <> mt /\ exists p, m_prev (get_meta_rec st h) = Some p /\ meta_slot st p /\ p <> mt.

Definition failW (spv : Z) : list (Z * Z) :=
  (spv - 144, spv) :: (G, G + 40) :: (CTX + 16, CTX + 24)
  :: match c_free_meta_head (ctx st) with
     | Some h => (conc st h, conc st h + 40)
                 :: match m_prev (get_meta_rec st h) with Some p => [(conc st p, conc st p + 40)] | None => [] end
     | None => []
     end.

(* [comment removed for export] *)
#[using="FL MST"] Lemma rfailm1_walk :
  forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
  mrep st m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  alloc_ceiling <= bv_unsigned sp - 144 ->
  evt rsegs (fun ms' => exists (a1' s6' : word) m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24524) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) (ta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
      /\ munch (failW (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep (as_fm_st st mt) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2411c) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (first [ pose proof ((meta_slot_bounds st m mt MR MST)) as dR_2; dand5 dR_2 as Gpos GC GI G4 _ | pose proof (meta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI, G4.
  unfold failW. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK, ta_frame in *.
  (* [comment removed for export] *)
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt rsegs (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) (pw st (c_free_meta_head (ctx st))) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 402520) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24178) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ mrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 402520) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2411c) fc None m (seg_rom rsegs))).
  { intros W HW1 HW2.
    (first [ pose proof (MR) as dR_3; dand3 dR_3 as _ (CX1 & _) _ | pose proof MR as (_ & (CX1 & _) & _) ]). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold CTX in CX1.
    mchunk MR MST CH. fold G in CH.
    (* [comment removed for export] *)
    lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : mrep st mX) by (eapply mrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]) end.
    clear MUs.
    meta_open G MUb WMb.
    (* [comment removed for export] *)
    step. st1. step. st1. step. st1. step. st1. step. st1.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : mrep (put_meta mt meta0 st) mX);
      [ eapply mrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| mem_side]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; mem_side| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  - (* [comment removed for export] *)
    (first [ pose proof ((FL h eq_refl)) as dR_4; dand6 dR_4 as MSh NEh p HP MSp NEp | destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp) ]). rewrite HP.
    (first [ pose proof ((meta_slot_bounds st m h MR MSh)) as dR_5; dand5 dR_5 as Hpos HC' HI _ _ | pose proof (meta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _) ]).
    (first [ pose proof ((meta_slot_bounds st m p MR MSp)) as dR_6; dand5 dR_6 as Ppos PC PI _ _ | pose proof (meta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _) ]).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (402528 + 16, 402528 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); mem_side|]. cbv beta.
    (intros ms'; (first [ intro dR_15; dex2 dR_15 as m1 junk'; dand6 dR_15 as -> FR1 MU WM1 MI1 MR0 | intro dR_15; dand8 dR_15 as m1 junk' -> FR1 MU WM1 MI1 MR0 | intros (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0) ])). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    mchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    meta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : mrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply mrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    (* [comment removed for export] *)
    mchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    (* [comment removed for export] *)
    mchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    meta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : mrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply mrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    (* [comment removed for export] *)
    mchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    meta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : mrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply mrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    (* [comment removed for export] *)
    mchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    (* [comment removed for export] *)
    mchunk MR3 MSh3 CH.
    meta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : mrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply mrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    (* [comment removed for export] *)
    step.
    apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
    eapply (mrep_extW _ _ _ MR4); try reflexivity.
    intros q. unfold st3, st2, st1, st0, upd_meta.
    destruct (decide (q = h)) as [->|NQh].
    { rewrite !get_meta_rec_put_same. f_equal.
      destruct (decide (h = p)) as [<-|NHp].
      - rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
      - rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
    destruct (decide (q = p)) as [->|NQp].
    { rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
  - (* [comment removed for export] *)
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (402528 + 16, 402528 + 24)]%Z); mem_side|]. cbv beta.
    (intros ms'; (first [ intro dR_16; dex2 dR_16 as m1 junk'; dand6 dR_16 as -> FR1 MU WM1 MI1 MR0 | intro dR_16; dand8 dR_16 as m1 junk' -> FR1 MU WM1 MI1 MR0 | intros (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0) ])). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    mchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    meta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : mrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply mrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    (* [comment removed for export] *)
    step.
    (first [ pose proof (MR1) as dR_7; dand3 dR_7 as _ (CX1 & _) _ | pose proof MR1 as (_ & (CX1 & _) & _) ]). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold CTX in CX1.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (402520 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (mrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold CTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (402528 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. do 4 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (mrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
(* [comment removed for export] *)
#[using="FL MST"] Lemma rfailm2_walk :
  forall (sp gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
         (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc m junk,
  mrep st m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  alloc_ceiling <= bv_unsigned sp - 144 ->
  evt rsegs (fun ms' => exists (s6' : word) m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6' s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24524) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) (ta_frame junk' s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav)
      /\ munch (failW (bv_unsigned sp)) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep (as_fm_st st mt) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2449c) fc None m (seg_rom rsegs)).
Proof.
  intros until junk. intros MR MI FR SPC.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (first [ pose proof ((meta_slot_bounds st m mt MR MST)) as dR_8; dand5 dR_8 as Gpos GC GI G4 _ | pose proof (meta_slot_bounds st m mt MR MST) as (Gpos & GC & GI & G4 & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). fold G in Gpos, GC, GI, G4.
  unfold failW. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK, ta_frame in *.
  (* [comment removed for export] *)
  assert (PRE : forall W, In (bv_unsigned sp - 144, bv_unsigned sp) W -> In (G, G + 40) W ->
    evt rsegs (fun ms' => exists m' junk',
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) (pw st (c_free_meta_head (ctx st))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 402520) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x244f4) fc None m' (seg_rom rsegs)
      /\ rw_cells rsegs m' (bv_unsigned sp + -144) ([CB 48 junk'; C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav])
      /\ munch W m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ mrep (put_meta mt meta0 st) m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 (Z_to_bv 64 G) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 402520) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2449c) fc None m (seg_rom rsegs))).
  { intros W HW1 HW2.
    (first [ pose proof (MR) as dR_9; dand3 dR_9 as _ (CX1 & _) _ | pose proof MR as (_ & (CX1 & _) & _) ]). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold CTX in CX1.
    mchunk MR MST CH. fold G in CH.
    (* [comment removed for export] *)
    lazymatch type of CH with rw_cells rsegs m G [?c0; ?c1; ?c2; C4 ?av; C4 ?fr; ?c5] =>
      assert (CH' : rw_cells rsegs m G [c0; c1; c2; CB 8 (le4 av ++ le4 fr); c5]);
      [ eapply rw_cells_congr; [| | | exact CH]; [cbn [cells_bytes cbytes]; rewrite <- !app_assoc; reflexivity| reflexivity| cbn [cells_wf cell_wf]; rewrite length_app, !length_le4; tauto]
      | clear CH ] end.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40)]%Z m) as MUa.
    pose proof (munch_refl [(bv_unsigned sp - 144, bv_unsigned sp)]%Z m) as MUs.
    (* [comment removed for export] *)
    st1. st1. st1. st1. st1.
    lazymatch goal with WMs : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MRs : mrep st mX) by (eapply mrep_transport_high; [exact MR | exact MUs | exact WMs | intros l h [E|[]]; inversion E; subst; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]) end.
    clear MUs.
    meta_open G MUb WMb.
    (* [comment removed for export] *)
    step. st1. step. st1. step. st1. step. st1. step. st1.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    step.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR0 : mrep (put_meta mt meta0 st) mX);
      [ eapply mrep_put_meta_frame; [exact MRs| exact MST| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [cbn [cells_bytes cbytes]; reflexivity| reflexivity| mem_side]
      | clear H MUb WMb ] end.
    lazymatch goal with H : rw_cells rsegs ?mX (bv_unsigned sp + -144) (CB 8 ?j8 :: _) |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (FR' : rw_cells rsegs mX (bv_unsigned sp + -144)
        ([CB 48 (j8 ++ cells_bytes [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)]); C8 (wz run_guard); C8 s9v; C8 s8v; C8 s7v; C8 s6v; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav]));
      [ destruct H as [[WF BA] WR]; cbn [cells_wf cell_wf] in WF; destruct WF as [L8 WF'];
        split; [split; [cbn [cells_wf cell_wf]; rewrite length_app, L8; mem_side| cbn [cells_bytes cbytes] in BA |- *; rewrite <- !app_assoc; exact BA]
              | cbn [cells_size csize] in WR |- *; exact WR]
      | clear H ] end.
    apply evt_done. do 2 eexists. split; [reflexivity|]. split; [exact FR'|].
    split. { eapply munch_weaken; [| exact MUa]. intros y Hy. cbn. split; [| split; [|exact I]]; eapply (outside_In _ y); eauto. }
    split; [assumption|]. split; [assumption| exact MR0]. }
  destruct (c_free_meta_head (ctx st)) as [h|] eqn:FH.
  - (* [comment removed for export] *)
    (first [ pose proof ((FL h eq_refl)) as dR_10; dand6 dR_10 as MSh NEh p HP MSp NEp | destruct (FL h eq_refl) as (MSh & NEh & p & HP & MSp & NEp) ]). rewrite HP.
    (first [ pose proof ((meta_slot_bounds st m h MR MSh)) as dR_11; dand5 dR_11 as Hpos HC' HI _ _ | pose proof (meta_slot_bounds st m h MR MSh) as (Hpos & HC' & HI & _ & _) ]).
    (first [ pose proof ((meta_slot_bounds st m p MR MSp)) as dR_12; dand5 dR_12 as Ppos PC PI _ _ | pose proof (meta_slot_bounds st m p MR MSp) as (Ppos & PC & PI & _ & _) ]).
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (402528 + 16, 402528 + 24); (conc st h, conc st h + 40); (conc st p, conc st p + 40)]%Z); mem_side|]. cbv beta.
    (intros ms'; (first [ intro dR_17; dex2 dR_17 as m1 junk'; dand6 dR_17 as -> FR1 MU WM1 MI1 MR0 | intro dR_17; dand8 dR_17 as m1 junk' -> FR1 MU WM1 MI1 MR0 | intros (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0) ])). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    assert (MSh0 : meta_slot st0 h) by (apply meta_slot_put_meta; exact MSh).
    assert (MSp0 : meta_slot st0 p) by (apply meta_slot_put_meta; exact MSp).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. lia. } clear K.
    (* [comment removed for export] *)
    mchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    meta_open G MUa WMa.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : mrep (put_meta mt (mkMeta None (Some h) None 0 0 0 0 0 0) st0) mX);
      [ eapply mrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 h) with (conc st h); reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    assert (MSm1 : meta_slot st1 mt) by (apply meta_slot_put_meta; exact MSm0).
    assert (MSh1 : meta_slot st1 h) by (apply meta_slot_put_meta; exact MSh0).
    assert (MSp1 : meta_slot st1 p) by (apply meta_slot_put_meta; exact MSp0).
    (* [comment removed for export] *)
    mchunk MR1 MSh1 CH. unfold st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    rewrite HP in CH. cbn [oconc] in CH.
    step. clear CH.
    (* [comment removed for export] *)
    mchunk MR1 MSm1 CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. change (meta_word _) with 0 in CH.
    change (conc st0 mt) with G in CH. change (conc st mt) with G in CH.
    meta_open G MUb WMb.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR2 : mrep (put_meta mt (mkMeta (Some p) (Some h) None 0 0 0 0 0 0) st1) mX);
      [ eapply mrep_put_meta_frame; [exact MR1| exact MSm1| exact MUb| exact WMb|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; reflexivity
      | clear MUb WMb H ] end.
    set (st2 := put_meta mt _ st1) in MR2.
    assert (MSm2 : meta_slot st2 mt) by (apply meta_slot_put_meta; exact MSm1).
    assert (MSh2 : meta_slot st2 h) by (apply meta_slot_put_meta; exact MSh1).
    assert (MSp2 : meta_slot st2 p) by (apply meta_slot_put_meta; exact MSp1).
    (* [comment removed for export] *)
    mchunk MR2 MSp2 CH. unfold st2, st1, st0 in CH. rewrite !get_meta_rec_put_other in CH by (congruence).
    meta_open (conc st p) MUc WMc.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st p) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR3 : mrep (put_meta p (m_set_next (Some mt) (get_meta_rec st p)) st2) mX);
      [ eapply mrep_put_meta_frame; [exact MR2| exact MSp2| exact MUc| exact WMc|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_next oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st2 mt) with G; reflexivity
      | clear MUc WMc H ] end.
    set (st3 := put_meta p _ st2) in MR3.
    assert (MSm3 : meta_slot st3 mt) by (apply meta_slot_put_meta; exact MSm2).
    assert (MSh3 : meta_slot st3 h) by (apply meta_slot_put_meta; exact MSh2).
    (* [comment removed for export] *)
    mchunk MR3 MSm3 CH. unfold st3 in CH. rewrite get_meta_rec_put_other in CH by (intros E; exact (NEp (eq_sym E))).
    unfold st2 in CH. rewrite get_meta_rec_put_same in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH.
    change (conc st mt) with G in CH.
    step. clear CH.
    (* [comment removed for export] *)
    step.
    mchunk MR3 MSh3 CH.
    meta_open (conc st h) MUd WMd.
    st1.
    lazymatch goal with H : rw_cells rsegs ?mX (conc st h) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR4 : mrep (put_meta h (m_set_prev (Some mt) (get_meta_rec st3 h)) st3) mX);
      [ eapply mrep_put_meta_frame; [exact MR3| exact MSh3| exact MUd| exact WMd|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_prev oconc meta_word m_last_idx m_freeable m_sizeclass m_maplen];
        change (conc st3 mt) with G; reflexivity
      | clear MUd WMd H ] end.
    (* [comment removed for export] *)
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_link. rewrite get_meta_rec_put_other by congruence. rewrite HP. cbv zeta.
    eapply (mrep_extW _ _ _ MR4); try reflexivity.
    intros q. unfold st3, st2, st1, st0, upd_meta.
    destruct (decide (q = h)) as [->|NQh].
    { rewrite !get_meta_rec_put_same. f_equal.
      destruct (decide (h = p)) as [<-|NHp].
      - rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity.
      - rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ h _ q) by congruence.
    destruct (decide (q = p)) as [->|NQp].
    { rewrite !get_meta_rec_put_same. f_equal. rewrite !get_meta_rec_put_other by congruence. reflexivity. }
    rewrite !(get_meta_rec_put_other _ p _ q) by congruence.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
  - (* [comment removed for export] *)
    eapply evt_cut; [apply (PRE [(bv_unsigned sp - 144, bv_unsigned sp); (G, G + 40); (402528 + 16, 402528 + 24)]%Z); mem_side|]. cbv beta.
    (intros ms'; (first [ intro dR_18; dex2 dR_18 as m1 junk'; dand6 dR_18 as -> FR1 MU WM1 MI1 MR0 | intro dR_18; dand8 dR_18 as m1 junk' -> FR1 MU WM1 MI1 MR0 | intros (m1 & junk' & -> & FR1 & MU & WM1 & MI1 & MR0) ])). clear PRE WM.
    set (st0 := put_meta mt meta0 st) in *.
    assert (MSm0 : meta_slot st0 mt) by (apply meta_slot_put_meta; exact MST).
    unfold pw. cbn [oconc]. unfold wz.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. } clear K.
    (* [comment removed for export] *)
    mchunk MR0 MSm0 CH. rewrite meta_word_meta0 in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc meta0] in CH.
    change (conc st mt) with G in CH.
    meta_open G MUa WMa.
    st1. st1.
    lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      assert (MR1 : mrep (put_meta mt (mkMeta (Some mt) (Some mt) None 0 0 0 0 0 0) st0) mX);
      [ eapply mrep_put_meta_frame; [exact MR0| exact MSm0| exact MUa| exact WMa|];
        eapply rw_cells_congr; [| | | exact H]; [| reflexivity| mem_side];
        unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed oconc]; change (conc st0 mt) with G; reflexivity
      | clear MUa WMa H ] end.
    set (st1 := put_meta mt _ st0) in MR1.
    (* [comment removed for export] *)
    step.
    (first [ pose proof (MR1) as dR_13; dand3 dR_13 as _ (CX1 & _) _ | pose proof MR1 as (_ & (CX1 & _) & _) ]). unfold ctx_head_cells in CX1. cbv zeta in CX1. unfold CTX in CX1.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 16 (C8 (pw st1 (c_free_meta_head (ctx st1)))) 8 (Z_to_bv 64 (402520 + 24)) CX1 eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK. clear CX1.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (mrep_set_free_head st1 mX (Some mt) MR1) as MR2; unfold CTX in MR2 end.
    unfold pw in MR2. cbn [oconc] in MR2. change (conc st1 mt) with G in MR2.
    rraw_store_finishF (402528 + 16) (le8 (wz G)) FR1 MU WM1 SOK.
    (* [comment removed for export] *)
    step.
    apply evt_done. do 3 eexists. split; [reflexivity|]. split; [exact FR1|].
    split; [exact MU|]. split; [exact WM1|]. split; [assumption|].
    unfold as_fm_st, as_queue_st. cbn [get_head]. change (ctx (put_meta mt meta0 st)) with (ctx st). rewrite FH.
    unfold as_fm_single. cbn [set_head].
    eapply (mrep_extW _ _ _ MR2); try reflexivity.
    intros q. unfold st1, st0, upd_meta. rewrite !rec_upd_ctx.
    destruct (decide (q = mt)) as [->|NQm].
    { rewrite !get_meta_rec_put_same. reflexivity. }
    rewrite !(get_meta_rec_put_other _ mt _ q) by congruence. reflexivity.
Qed.
End FAILM.
End RASl99y.

Module RASldlz.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RAlllfc RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep MRepAux RF_m8yt RAlllfc Malllim.

Definition links_only (r r' : meta) : Prop :=
  m_mem r' = m_mem r /\ m_avail r' = m_avail r /\ m_freed r' = m_freed r
  /\ m_last_idx r' = m_last_idx r /\ m_freeable r' = m_freeable r /\ m_sizeclass r' = m_sizeclass r /\ m_maplen r' = m_maplen r.
Lemma leaf_of_ret_inv {R} o (r r' : R) : leaf_of o (SRet r) r' -> r' = r.
Proof. ((first [ intro dR_39; dex2 dR_39 as ans o'; rename dR_39 into H | intro dR_39; dand3 dR_39 as ans o' H | intros (ans & o' & H) ])). rewrite mrun_ret in H. cbn in H. destruct ans; inversion H; reflexivity. Qed.
Definition LO (st st' : mstate) : Prop := forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).
Lemma LO_refl st : LO st st.
Proof. intros q. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.
Lemma LO_trans st1 st2 st3 : LO st1 st2 -> LO st2 st3 -> LO st1 st3.
Proof.
  intros A B q. (first [ pose proof ((A q)) as dR_1; dand7 dR_1 as A1 A2 A3 A4 A5 A6 A7 | destruct (A q) as (A1&A2&A3&A4&A5&A6&A7) ]). (first [ pose proof ((B q)) as dR_2; dand7 dR_2 as B1 B2 B3 B4 B5 B6 B7 | destruct (B q) as (B1&B2&B3&B4&B5&B6&B7) ]).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence.
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
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rec_set_head h v st q : get_meta_rec (set_head h v st) q = get_meta_rec st q.
Proof. destruct h; reflexivity. Qed.
Ltac lo_peel :=
  first [ apply LO_refl
        | apply LO_same; intros ?; reflexivity
        | eapply LO_trans; [| apply LO_upd_links; intros ?; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity]; lo_peel
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
Lemma ER_refl_tick st0 t : ENTRY_REL st0 (set_tick t st0).
Proof.
  constructor; try reflexivity; try (intros; tauto).
  - split; [intros rid r H; exists r; cbn; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia| cbn; lia| reflexivity].
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
  - intros q Hq. (first [ pose proof ((EGE q Hq)) as dR_3; dand3 dR_3 as A1 A2 A3 | destruct (EGE q Hq) as (A1 & A2 & A3) ]). (first [ pose proof ((tr_geom _ _ _ T q)) as dR_4; dand5 dR_4 as M L F S P | destruct (tr_geom _ _ _ T q) as (M & L & F & S & P) ]). rewrite L, S. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption.
    unfold get_stride. rewrite L, S, P. exact A1.
  - intros q i Hi Hb. apply (EB q i Hi). apply (tr_bits _ _ _ T q i Hi). exact Hb.
  - intros a Ha. rewrite (tr_areas _ _ _ T). apply EA. exact Ha.
Qed.
Lemma ticks_ok_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros ES ET [T1 T2]. split; rewrite ES, ET; assumption. Qed.
Lemma ALLC_tick st0 t :
  (forall rid sh o v tk, (s_shadow st0) !! rid = Some sh -> (r_cells sh) !! o = Some (v, tk) -> (tk <= s_tick st0)%N) ->
  (s_tick st0 < t)%N -> ALLC (set_tick t st0).
Proof. intros H Ht rid sh o v tk Hs Hc. cbn. pose proof (H rid sh o v tk Hs Hc). lia. Qed.
Lemma ALLC_same st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ALLC st -> ALLC st1.
Proof. intros ES ET H rid sh o v tk Hs Hc. rewrite ET. rewrite ES in Hs. exact (H rid sh o v tk Hs Hc). Qed.
Lemma ALLC_ta st sc st1 : ta_rel sc st st1 -> ALLC st -> ALLC st1.
Proof. intros T. apply ALLC_same; [apply (tr_shadow _ _ _ T)| apply (tr_tick _ _ _ T)]. Qed.
Lemma ALLC_am st st1 mo : am_rel st st1 mo -> ALLC st -> ALLC st1.
Proof. intros A. apply ALLC_same; [apply (amr_shadow _ _ _ A)| apply (amr_tick _ _ _ A)]. Qed.
Lemma unk_agree_xfer o stA mA stB mB :
  unk_agree stA o mA ->
  s_shadow stB = s_shadow stA ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stB) !! rid = Some r -> (s_regions stA) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stB) !! b) <-> is_Some ((s_groups stA) !! b)) ->
  (forall rid r off h, (s_regions stA) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow stA rid) off = Unknown h -> ~ grp_hdr_cov stA rid off -> mB (wa (r_base r + off)) = mA (wa (r_base r + off))) ->
  unk_agree stB o mB.
Proof.
  intros UA ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow stA rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov stA rid off).
  { ((first [ intro dR_40; dex2 dR_40 as bq gh; dand3 dR_40 as Hbq Hf Hoff | intro dR_40; dand5 dR_40 as bq gh Hbq Hf Hoff | intros (bq & gh & Hbq & Hf & Hoff) ])). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.
Lemma fm_proj st g :
  let st' := as_fm_st st g in
  s_regions st' = s_regions st /\ s_shadow st' = s_shadow st /\ s_groups st' = s_groups st /\ s_areas st' = s_areas st
  /\ s_slots st' = s_slots st /\ s_tick st' = s_tick st /\ s_next_rid st' = s_next_rid st /\ s_reserved st' = s_reserved st
  /\ (forall c, active st' c = active st c) /\ (forall i, usage st' i = usage st i)
  /\ c_brk (ctx st') = c_brk (ctx st) /\ c_mmap_counter (ctx st') = c_mmap_counter (ctx st)
  /\ (forall i, bounces st' i = bounces st i) /\ (forall i, unmap_seq st' i = unmap_seq st i) /\ c_seq (ctx st') = c_seq (ctx st).
Proof.
  unfold as_fm_st, as_queue_st, as_fm_link, as_fm_single. cbn [get_head].
  destruct (c_free_meta_head (ctx (put_meta g meta0 st))) as [h|].
  - cbv zeta. destruct (m_prev (get_meta_rec (put_meta g meta0 st) h)) as [p|]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  - OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
Qed.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma leaf_of_vis_inv {R} o e (k : Z -> Malloc.M R) r :
  leaf_of o (SVis e k) r ->
  match e with
  | EUndef _ => False
  | EPeek p c h => leaf_of o (k (pans_mem o p c h)) r
  | _ => exists z, leaf_of o (k z) r
  end.
Proof.
  ((first [ intro dR_41; dex2 dR_41 as ans o'; rename dR_41 into H | intro dR_41; dand3 dR_41 as ans o' H | intros (ans & o' & H) ])).
  destruct e; try (rewrite mrun_vis in H by exact I; cbn [follow] in H; destruct ans as [|a ans]; [discriminate|]; exists a; exists ans, o'; exact H).
  - rewrite mrun_peek in H. exists ans, o'. exact H.
  - rewrite mrun_vis in H by exact I. cbn [follow] in H. destruct ans; discriminate.
Qed.
Lemma leaf_of_bad {R} o (bail : Malloc.M R) r : leaf_of o (bad_answer bail) r -> False.
Proof. intros H. exact (leaf_of_vis_inv o _ _ r H). Qed.
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
Lemma gmf_of_facts st LB sc g :
  ISTF st LB -> lmem st g -> m_sizeclass (get_meta_rec st g) = sc -> 0 <= sc < 48 -> gmf st sc g.
Proof.
  (intros F; (first [ intro dR_42; dand3 dR_42 as MEM NX PV | intros (MEM & NX & PV) ]); intros GSC SCR). assert (SC48 : m_sizeclass (get_meta_rec st g) < 48) by lia.
  pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF. pose proof (isf_ghdr _ _ F) as GU.
  destruct (m_mem (get_meta_rec st g)) as [b|] eqn:Hmem; [|congruence].
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  (first [ dand9 FG as MSL AVr FRr LI FB SCr ML0 (ai & Hgh & AI & AVAI) _ | destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh & AI & AVAI) & _) ]).
  (first [ pose proof ((lf_mw _ (isf_lf _ _ F) g)) as dR_6; dand3 dR_6 as MW _ _ | pose proof (lf_mw _ (isf_lf _ _ F) g) as (MW & _ & _) ]). change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MW.
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  constructor.
  - exact MSL.
  - exact AVr.
  - exact FRr.
  - exact MW.
  - exact SC48.
  - exact GSC.
  - exists b, (mkGhdr (Some g) ai). split; [exact Hmem|]. split; [exact Hgh|]. split; [reflexivity|]. split; [cbn; lia|]. split.
    + intros S0. cbn. pose proof (lf_sc0_full _ LF g b (mkGhdr (Some g) ai)) as X.
      change (get_meta_rec (strip st) g) with (get_meta_rec st g) in X. change (s_groups (strip st)) with (s_groups st) in X.
      exact (X Hmem Hgh S0).
    + intros o Ho. exact (GU b _ o Hgh Ho).
  - intros i Hi Hb. (first [ pose proof ((FM g b Hmem)) as dR_7; dand3 dR_7 as F1 F2 _ | destruct (FM g b Hmem) as (F1 & F2 & _) ]). exact (F2 i Hi Hb).
  - intros i Hi Hb. (first [ pose proof ((FM g b Hmem)) as dR_8; dand3 dR_8 as F1 F2 _ | destruct (FM g b Hmem) as (F1 & F2 & _) ]). exact (F1 i Hi Hb).
  - destruct (m_next (get_meta_rec st g)) as [n|] eqn:En; [|congruence]. destruct (m_prev (get_meta_rec st g)) as [p|] eqn:Ep; [|congruence].
    exists n, p. split; reflexivity.
Qed.

Lemma taf_of_facts st LB sc : ISTF st LB -> 0 <= sc < 48 -> taf st sc.
Proof.
  intros F SC. pose proof (isf_mf _ _ F) as MF. pose proof (isf_lf _ _ F) as LF.
  (first [ pose proof ((lf_lists _ LF)) as dR_9; dand3 dR_9 as L1 L2 L3 | pose proof (lf_lists _ LF) as (L1 & L2 & L3) ]).
  change (fact_active (strip st)) with (fact_active st).
  pose proof (mf_active _ _ MF) as FA. change (fact_active (strip st)) with (fact_active st) in FA.
  pose proof (lf_links _ LF) as LK.
  constructor.
  - intros g Hg. (first [ pose proof ((FA sc g Hg)) as dR_10; dand3 dR_10 as _ GSC _ | destruct (FA sc g Hg) as (_ & GSC & _) ]). pose proof (L1 sc g Hg) as LM.
    change (lmem (strip st) g) with (lmem st g) in LM.
    split; [| exact GSC]. eapply gmf_of_facts; [exact F| exact LM| exact GSC| exact SC].
  - intros g n GM Hn. (first [ pose proof ((gmf_grp _ _ _ GM)) as dR_11; dex2 dR_11 as b gh; destruct dR_11 as [Hmem _] | pose proof ((gmf_grp _ _ _ GM)) as dR_11; dand4 dR_11 as b gh Hmem _ | destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _) ]).
    destruct (L2 g n ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hn) as [LMn SCn].
    change (lmem (strip st) n) with (lmem st n) in LMn. change (get_meta_rec (strip st) n) with (get_meta_rec st n) in SCn.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCn.
    split; [eapply gmf_of_facts; [exact F| exact LMn| rewrite SCn; exact (gmf_cls _ _ _ GM)| exact SC]|].
    split; [exact SCn|].
    (first [ pose proof ((gmf_links _ _ _ GM)) as dR_12; dex2 dR_12 as n' p'; destruct dR_12 as [En Ep] | pose proof ((gmf_links _ _ _ GM)) as dR_12; dand4 dR_12 as n' p' En Ep | destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep) ]).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [LKn _].
    exact (LKn n Hn).
  - intros g p GM Hp. (first [ pose proof ((gmf_grp _ _ _ GM)) as dR_13; dex2 dR_13 as b gh; destruct dR_13 as [Hmem _] | pose proof ((gmf_grp _ _ _ GM)) as dR_13; dand4 dR_13 as b gh Hmem _ | destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & _) ]).
    destruct (L3 g p ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); rewrite Hmem; discriminate) Hp) as [LMp SCp].
    change (lmem (strip st) p) with (lmem st p) in LMp. change (get_meta_rec (strip st) p) with (get_meta_rec st p) in SCp.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SCp.
    split; [eapply gmf_of_facts; [exact F| exact LMp| rewrite SCp; exact (gmf_cls _ _ _ GM)| exact SC]|].
    (first [ pose proof ((gmf_links _ _ _ GM)) as dR_14; dex2 dR_14 as n' p'; destruct dR_14 as [En Ep] | pose proof ((gmf_links _ _ _ GM)) as dR_14; dand4 dR_14 as n' p' En Ep | destruct (gmf_links _ _ _ GM) as (n' & p' & En & Ep) ]).
    destruct (LK g ltac:(split; [rewrite Hmem; discriminate| split; [rewrite En| rewrite Ep]; discriminate])) as [_ LKp].
    exact (LKp p Hp).
  - (first [ pose proof ((mf_ctx _ _ MF)) as dR_15; dand6 dR_15 as _ _ _ _ B _ | pose proof (mf_ctx _ _ MF) as (_ & _ & _ & _ & B & _) ]). intros i. exact (B i).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPER.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st0 st : mstate) (m : mem).
Hypothesis MR : mrep st m.
Hypothesis ER : ENTRY_REL st0 st.

Lemma st0_region rid r : (s_regions st0) !! rid = Some r ->
  0 <= r_base r /\ r_base r + round_up_pg (r_len r) <= alloc_ceiling
  /\ (r_base r + round_up_pg (r_len r) <= 0x10000 \/ 0x17000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x17000 \/ 0x30000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x30000 \/ 0x31000 <= r_base r)
  /\ (r_base r + round_up_pg (r_len r) <= 0x31000 \/ 0x63000 <= r_base r).
Proof.
  intros Hr. (first [ pose proof ((mrel_regions _ _ (er_mrel _ _ ER) rid r Hr)) as dR_16; dex1 dR_16 as r'; dand4 dR_16 as Hr' K' B' L' | pose proof ((mrel_regions _ _ (er_mrel _ _ ER) rid r Hr)) as dR_16; dand5 dR_16 as r' Hr' K' B' L' | destruct (mrel_regions _ _ (er_mrel _ _ ER) rid r Hr) as (r' & Hr' & K' & B' & L') ]).
  pose proof MR as (WF & _). (first [ pose proof (WF) as dR_17; dand3 dR_17 as _ WR _ | pose proof WF as (_ & WR & _) ]).
  (first [ pose proof ((WR rid r' Hr')) as dR_18; dand5 dR_18 as RB0 RBAL RL0 RBC RF | destruct (WR rid r' Hr') as (RB0 & RBAL & RL0 & RBC & RF) ]). (first [ pose proof ((reserved_disjoint _ _ RF)) as dR_19; dand4 dR_19 as D1 D2 D3 D4 | pose proof (reserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4) ]).
  pose proof (round_up_pg_mono _ _ L'). pose proof (round_up_pg_ge (r_len r)). rewrite B' in *. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
Qed.

Lemma malloc_fp_cases_ER stE mE lo sp a :
  mrep stE mE -> malloc_fp st0 stE lo sp a -> lo <= a < sp \/ a < alloc_ceiling.
Proof.
  intros (WF2 & _) H. (first [ pose proof (WF2) as dR_20; dand3 dR_20 as _ WR2 _ | pose proof WF2 as (_ & WR2 & _) ]).
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC _]]]]].
  - left; exact H.
  - right. rewrite unsigned_lit in H by lia. lia.
  - right. unfold CTX in H. lia.
  - right. (first [ pose proof ((WR2 rid r Hr)) as dR_21; dand5 dR_21 as _ _ _ RC _ | destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - right. (first [ pose proof ((WR2 rid r Hr)) as dR_22; dand5 dR_22 as _ _ _ RC _ | destruct (WR2 rid r Hr) as (_ & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - right. (first [ pose proof ((st0_region (fst b) r Hr)) as dR_23; dand3 dR_23 as _ RC _ | destruct (st0_region (fst b) r Hr) as (_ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - right. (first [ pose proof ((st0_region (fst b) r Hr)) as dR_24; dand3 dR_24 as _ RC _ | destruct (st0_region (fst b) r Hr) as (_ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - right. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
Qed.

Lemma malloc_fp_image_ER stE mE lo sp a :
  mrep stE mE -> malloc_fp st0 stE lo sp a -> alloc_ceiling <= lo ->
  0x10000 <= a < 0x63000 -> CTX <= a < CTX + 928 \/ 0x420b4 <= a < 0x420b8.
Proof.
  intros (WF2 & _) H CLO HA. (first [ pose proof (WF2) as dR_25; dand3 dR_25 as _ WR2 _ | pose proof WF2 as (_ & WR2 & _) ]). pose proof MR as ((RS1 & _) & _).
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  destruct H as [[H|[H|[H|(rid & r & Hr & _ & Ha)]]]|[(rid & r & Hr & _ & Ha)|[(g & b & r & i & _ & Hr & _ & _ & _ & Ha & _)|[(b & gh & r & _ & Hr & _ & Ha & _)|[FC FR]]]]].
  - exfalso. lia.
  - right. rewrite unsigned_lit in H by lia. lia.
  - left. exact H.
  - exfalso. (first [ pose proof ((WR2 rid r Hr)) as dR_26; dand5 dR_26 as _ _ _ _ RF | destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF) ]). (first [ pose proof ((reserved_disjoint _ _ RF)) as dR_27; dand4 dR_27 as D1 D2 D3 D4 | pose proof (reserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4) ]). pose proof (lr_lo_ge r). lia.
  - exfalso. (first [ pose proof ((WR2 rid r Hr)) as dR_28; dand5 dR_28 as _ _ _ _ RF | destruct (WR2 rid r Hr) as (_ & _ & _ & _ & RF) ]). (first [ pose proof ((reserved_disjoint _ _ RF)) as dR_29; dand4 dR_29 as D1 D2 D3 D4 | pose proof (reserved_disjoint _ _ RF) as (D1 & D2 & D3 & D4) ]). pose proof (lr_lo_ge r). lia.
  - exfalso. (first [ pose proof ((st0_region (fst b) r Hr)) as dR_30; dand6 dR_30 as _ _ W1 W2 W3 W4 | destruct (st0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4) ]). lia.
  - exfalso. (first [ pose proof ((st0_region (fst b) r Hr)) as dR_31; dand6 dR_31 as _ _ W1 W2 W3 W4 | destruct (st0_region (fst b) r Hr) as (_ & _ & W1 & W2 & W3 & W4) ]). lia.
  - exfalso. pose proof (fresh_image (Clg:=Clg) st0 a (conj FC FR) ltac:(rewrite <- (mrel_reserved _ _ (er_mrel _ _ ER)); exact RS1)). lia.
Qed.

Lemma auxv_okd_malloc_fp_ER stE mE lo sp m1 m' B :
  mrep stE mE -> auxv_okd (c_init_done (ctx st0)) m1 B -> pres_except (malloc_fp st0 stE lo sp) m1 m' ->
  alloc_ceiling <= lo -> sp <= B -> auxv_okd (c_init_done (ctx st0)) m' B.
Proof.
  intros MRE AUX PE CLO SB. eapply auxv_okd_pres; [exact AUX| exact PE| |].
  - intros a Ha Hfp. destruct (malloc_fp_cases_ER stE mE lo sp a MRE Hfp); [lia|].
    destruct AUX as [HH _]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - intros a Ha Hfp. unfold AUXV_CELL in Ha.
    destruct (malloc_fp_image_ER stE mE lo sp a MRE Hfp CLO ltac:(lia)) as [X|X]; unfold CTX in X; lia.
Qed.

Lemma frame_keep_ER stE mE lo sp m1 m' A cs :
  mrep stE mE -> pres_except (malloc_fp st0 stE lo sp) m1 m' -> rw_cells rsegs m1 A cs ->
  sp <= A -> alloc_ceiling <= A -> rw_cells rsegs m' A cs.
Proof.
  intros MRE PE H HA HC. eapply pres_except_rw_cells; [exact PE| exact H|].
  intros a Ha Hfp. destruct (malloc_fp_cases_ER stE mE lo sp a MRE Hfp); lia.
Qed.
End FPER.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AML.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Context {R : Type}.
Variable o : mem.
Variable Φ : R -> Prop.

Definition KOK (st : mstate) (k : mstate -> optr -> Malloc.M R) : Prop :=
  forall st2 mo r, LO st st2 -> leaf_of o (k st2 mo) r -> Φ r.
Definition BOK (bail : Malloc.M R) : Prop := forall r, leaf_of o bail r -> Φ r.
Lemma KOK_LO st st1 k : LO st st1 -> KOK st k -> KOK st1 k.
Proof. intros L K st2 mo r L2 H. apply (K st2 mo r); [eapply LO_trans; [exact L| exact L2]| exact H]. Qed.
Lemma am_take_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (am_take st k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_take in H.
  destruct (c_avail_meta (ctx st)) as [m|].
  - eapply K; [| exact H]. lo_peel.
  - destruct (leaf_of_vis_inv o _ _ r H).
Qed.
Lemma am_carve_leaves st p k bail r : KOK st k -> BOK bail -> leaf_of o (am_carve st p k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_carve in H. cbv zeta in H.
  eapply am_take_leaves; [| exact B| exact H].
  eapply KOK_LO; [| exact K]. apply LO_same. intros q.
  destruct (c_meta_area_tail _); reflexivity.
Qed.
Lemma am_finish_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_finish st nu k bail) r -> Φ r.
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
Lemma am_after_brk_leaves st nu k bail r : KOK st k -> BOK bail -> leaf_of o (am_after_brk st nu k bail) r -> Φ r.
Proof.
  intros K B H. unfold am_after_brk in H.
  destruct (c_avail_meta_area_count (ctx st) =? 0).
  - destruct (leaf_of_vis_inv o _ _ r H) as [z Hz]. cbv beta in Hz.
    destruct (negb (mmap_answer_ok _ _ z)); [destruct (leaf_of_bad o _ _ Hz)|].
    destruct (is_err z); [exact (K _ _ _ (LO_refl st) Hz)|].
    destruct (new_region RKMeta z _ st) as [st1 rid] eqn:E.
    eapply am_finish_leaves; [| exact B| exact Hz].
    eapply KOK_LO; [| exact K]. apply LO_same. intros q.
    replace st1 with (fst (new_region RKMeta z (Z.shiftl 2 (c_meta_alloc_shift (ctx st)) * PGSZ) st)) by (rewrite E; reflexivity). reflexivity.
  - eapply am_finish_leaves; [exact K| exact B| exact H].
Qed.
Lemma alloc_meta_leaves st k bail r : KOK st k -> BOK bail -> leaf_of o (alloc_meta st k bail) r -> Φ r.
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

Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma am_leaf_links_only : forall o st st' mo,
  leaf_of o (alloc_meta st kS bS) (Some (st', mo)) ->
  forall q, links_only (get_meta_rec st q) (get_meta_rec st' q).
Proof.
  intros o st st' mo H.
  refine (alloc_meta_leaves o (fun r => match r with Some (stX, _) => LO st stX | None => True end) st kS bS (Some (st', mo)) _ _ H).
  - intros st2 mo2 r L HL. apply leaf_of_ret_inv in HL. subst r. exact L.
  - intros r HL. apply leaf_of_ret_inv in HL. subst r. exact I.
Qed.
Lemma ER_am st0 st st1 m o : ENTRY_REL st0 st -> am_rel st st1 (Some m) ->
  leaf_of o (alloc_meta st kS bS) (Some (st1, Some m)) -> ENTRY_REL st0 st1.
Proof.
  intros E A L. destruct E as [ES EG EGR EM EME EGE EB EA].
  pose proof (am_leaf_links_only o st st1 (Some m) L) as LO.
  constructor.
  - rewrite (amr_shadow _ _ _ A). exact ES.
  - intros b. rewrite <- (EG b). rewrite (amr_groups _ _ _ A). tauto.
  - intros rid r Hk. rewrite <- (EGR rid r Hk). split; intros Hr.
    + destruct ((s_regions st) !! rid) as [r0|] eqn:E0.
      * (first [ pose proof ((amr_regions _ _ _ A rid r0 E0)) as dR_32; dex1 dR_32 as r'; dand5 dR_32 as Hr' K' _ _ G' | pose proof ((amr_regions _ _ _ A rid r0 E0)) as dR_32; dand6 dR_32 as r' Hr' K' _ _ G' | destruct (amr_regions _ _ _ A rid r0 E0) as (r' & Hr' & K' & _ & _ & G') ]). rewrite Hr in Hr'. inversion Hr'; subst r'.
        rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      * exfalso. exact (amr_new _ _ _ A rid r Hr E0 Hk).
    + (first [ pose proof ((amr_regions _ _ _ A rid r Hr)) as dR_33; dex1 dR_33 as r'; dand5 dR_33 as Hr' K' _ _ G' | pose proof ((amr_regions _ _ _ A rid r Hr)) as dR_33; dand6 dR_33 as r' Hr' K' _ _ G' | destruct (amr_regions _ _ _ A rid r Hr) as (r' & Hr' & K' & _ & _ & G') ]). rewrite Hr'. f_equal. apply G'. exact Hk.
  - destruct EM as [R1 N1 S1]. split.
    + intros rid r Hr. (first [ pose proof ((R1 rid r Hr)) as dR_34; dex1 dR_34 as r1; dand4 dR_34 as H1 K1 B1 L1 | pose proof ((R1 rid r Hr)) as dR_34; dand5 dR_34 as r1 H1 K1 B1 L1 | destruct (R1 rid r Hr) as (r1 & H1 & K1 & B1 & L1) ]).
      (first [ pose proof ((amr_regions _ _ _ A rid r1 H1)) as dR_35; dex1 dR_35 as r2; dand5 dR_35 as H2 K2 B2 L2 _ | pose proof ((amr_regions _ _ _ A rid r1 H1)) as dR_35; dand6 dR_35 as r2 H2 K2 B2 L2 _ | destruct (amr_regions _ _ _ A rid r1 H1) as (r2 & H2 & K2 & B2 & L2 & _) ]). exists r2. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try congruence. lia.
    + pose proof (amr_next_rid _ _ _ A). lia.
    + rewrite (amr_reserved _ _ _ A). exact S1.
  - intros q. destruct (LO q) as (M & _). rewrite M. apply EME.
  - intros q Hq. (first [ pose proof ((EGE q Hq)) as dR_36; dand3 dR_36 as A1 A2 A3 | destruct (EGE q Hq) as (A1 & A2 & A3) ]). (first [ pose proof ((LO q)) as dR_37; dand7 dR_37 as M AV FR L2 F S P | destruct (LO q) as (M & AV & FR & L2 & F & S & P) ]). rewrite L2, S. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; try assumption.
    unfold get_stride. rewrite L2, S, P. exact A1.
  - intros q i Hi Hb. apply (EB q i Hi). (first [ pose proof ((LO q)) as dR_38; dand4 dR_38 as _ AV FR _ | destruct (LO q) as (_ & AV & FR & _) ]). rewrite <- AV, <- FR. exact Hb.
  - intros a Ha. apply (amr_areas _ _ _ A). apply EA. exact Ha.
Qed.

End CEIL.
End RASldlz.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RAlllfc RASlot_I RASlh4s.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASl8dw.RASldlz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module RASlico.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Malls02 Mallmv3 RF_m8yt RAlllfc RASlot_I Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.RASlwvv.RASlh1b.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep.

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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition nest_frame (j gm cnt size sc : Z) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz j); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
Section AG1.

Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

(* [comment removed for export] *)
#[using="SC"] Lemma rag_entry_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (t1_regs sc (Z_to_bv 64 0x23ebc) sp gp tp t0 t1 t2 s1 (Z_to_bv 64 (SIZE_CLASSES + sc * 2)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 (sc * 2))
                   (wz (size_class sc)) (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 alloc_meta_entry) fc None m (seg_rom rsegs))
    (MS (t1_regs sc ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23ea4) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI. unfold t1_regs, alloc_meta_entry, SIZE_CLASSES, CTX, MLOCK, SSP_GUARD in *.
  pose proof (size_class_range sc SC) as SZR.
  step. rewrite ?(unsigned_lit sc), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. step. step. step.
  pose proof (size_classes_read m sc MI SC) as SCRD. unfold SIZE_CLASSES in SCRD.
  replace (85160 + 2 * sc) with (85160 + sc * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  step. apply evt_done. reflexivity.
Qed.
End AG1.


(* [comment removed for export] *)
Lemma ag_ret_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (gm : Z),
  0 <= gm < 2^64 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 gm) (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if gm =? 0 then 0x24524 else 0x23ec8)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 gm) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23ebc) fc None m (seg_rom rsegs)).
Proof.
  intros until gm. intros GR MI.
  step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - subst gm. cbn [Z.eqb]. apply evt_done. reflexivity.
  - replace (gm =? 0) with false by (symmetry; apply Z.eqb_neq; exact K). apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section STC.

Variables (szc cnt : Z).
Hypothesis SZC : 1 <= szc <= 8191.
Hypothesis CR : 1 <= cnt <= 32.
Hypothesis SMALL : szc * 16 * cnt + 16 <= 2048.
Let n' := szc * 16 * cnt + 12.
Let j := size_to_class n'.

#[using="SMALL CR SZC"] Lemma stc_q_eq : j = stc_q (szc * cnt).
Proof.
  unfold j, n'. rewrite size_to_class_q by nia. f_equal. Z.div_mod_to_equations. nia.
Qed.


(* [comment removed for export] *)
#[using="SMALL CR SZC"] Lemma nest_call_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc m,
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a2' a3' a4',
      ms' = MS (mkR (Z_to_bv 64 0x240a4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2' a3' a4' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 alloc_slot_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 (wz (szc * 16 * cnt)) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x23fd4) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI.
  assert (PR : 16 <= szc * 16 * cnt <= 2032) by nia.
  set (q := szc * cnt). assert (QR : 1 <= q <= 127) by (subst q; nia).
  pose proof stc_q_eq as STC. fold q in STC.
  unfold SIZE_CLASSES, alloc_slot_entry in *.
  (* [comment removed for export] *)
  assert (CALL : forall (a0' a2' a3' : word) (jv : Z), jv = j ->
    evt rsegs (fun ms' => exists a2'' a3'' a4'',
      ms' = MS (mkR (Z_to_bv 64 0x240a4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 85160) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 146628) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (wz n') a2' a3' (Z_to_bv 64 jv) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 85160) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24098) fc None m (seg_rom rsegs))).
  { intros a0' a2' a3' jv ->.
    pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & _).
    step. rewrite SysStep.sextw_small by lia. step. step.
    apply evt_done. do 3 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (szc * 16 * cnt)) by lia. fold n'. change (Z_to_bv 64 n') with (wz n').
  step. step. rewrite (wz_unsigned (szc * 16 * cnt)), Z.shiftr_div_pow2 by lia. change (2 ^ 4) with 16.
  replace (szc * 16 * cnt / 16) with q by (subst q; Z.div_mod_to_equations; nia).
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?(wz_unsigned n'), ?unsigned_lit in K by (unfold n'; lia).
  - (* [comment removed for export] *)
    apply CALL. rewrite STC. unfold stc_q. replace (q <? 10) with true by (symmetry; apply Z.ltb_lt; unfold n' in K; Z.div_mod_to_equations; nia). reflexivity.
  - (* [comment removed for export] *)
    assert (Q10 : 10 <= q) by (unfold n' in K; nia).
    step. rewrite ?(unsigned_lit q) by lia. set (x := q + 1) in *. assert (XR : 11 <= x < 8192) by lia.
    destruct (clz_pow_eq x XR) as [PW RV4].
    (* [comment removed for export] *)
    step.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    pose proof (shiftr_small 13 x 1 ltac:(lia) ltac:(lia)) as R1. pose proof (shiftr_small 13 x 2 ltac:(lia) ltac:(lia)) as R2.
    step. rewrite (unsigned_lit (Z.shiftr x 2)), (unsigned_lit x) by lia.
    set (v1 := Z.lor (Z.shiftr x 2) x). assert (RX : 0 <= x < 2 ^ 13) by lia. pose proof (lor_small 13 _ _ ltac:(lia) R2 RX) as RV1. fold v1 in RV1.
    step. rewrite (unsigned_lit x), srliw_small by lia.
    step. rewrite (unsigned_lit v1), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (v2 := Z.lor v1 (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) RV1 R1) as RV2. fold v2 in RV2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit v2), srliw_small by lia. pose proof (shiftr_small 13 v2 2 RV2 ltac:(lia)) as R3.
    step. rewrite (unsigned_lit (Z.shiftr v2 2)), (unsigned_lit (Z.shiftr x 1)) by lia.
    set (w2 := Z.lor (Z.shiftr v2 2) (Z.shiftr x 1)). pose proof (lor_small 13 _ _ ltac:(lia) R3 R1) as RW2. fold w2 in RW2.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w2) by lia. pose proof (shiftr_small 13 w2 4 RW2 ltac:(lia)) as R4.
    step. rewrite (unsigned_lit (Z.shiftr w2 4)), (unsigned_lit w2) by lia.
    set (w3 := Z.lor (Z.shiftr w2 4) w2). pose proof (lor_small 13 _ _ ltac:(lia) R4 RW2) as RW3. fold w3 in RW3.
    (* [comment removed for export] *)
    step. rewrite (unsigned_lit w3) by lia. pose proof (shiftr_small 13 w3 8 RW3 ltac:(lia)) as R5.
    step. rewrite (unsigned_lit (Z.shiftr w3 8)), (unsigned_lit w3) by lia.
    set (w4 := Z.lor (Z.shiftr w3 8) w3). pose proof (lor_small 13 _ _ ltac:(lia) R5 RW3) as RW4. fold w4 in RW4.
    assert (EW4 : w4 = rclz_v4 x) by reflexivity.
    (* [comment removed for export] *)
    step. step. step.
    rewrite (unsigned_lit w4), Z.shiftl_mul_pow2 by lia. rewrite (unsigned_lit (w4 * 2 ^ 33)) by lia.
    replace ((w4 * 2 ^ 33) ≫ 49) with 0 by (rewrite Z.shiftr_div_pow2 by lia; symmetry; apply Z.div_small; lia).
    rewrite (unsigned_lit 0), Z.lor_0_l by lia.
    (* [comment removed for export] *)
    step. step. rewrite (unsigned_lit w4) by lia.
    step. rewrite (unsigned_lit (w4 + 1)) by lia. rewrite (unsigned_lit (Z.lxor w4 18446744073709551615)) by (rewrite zb_lxor_ones by lia; lia).
    change (Z.land (w4 + 1) (Z.lxor w4 18446744073709551615)) with (clz_pow x). rewrite PW.
    set (k := Z.log2 x) in *.
    pose proof (size_to_class_props n' ltac:(unfold n', MMAP_THRESHOLD; lia)) as (SCRj & SFIT & LG).
    assert (K13 : 3 <= k <= 12).
    { unfold n' in LG. replace ((szc * 16 * cnt + 12 + 3) / 16) with q in LG by (subst q; Z.div_mod_to_equations; nia). subst k x. lia. }
    assert (P2 : 0 < 2 ^ k < 2 ^ 13) by (split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]).
    assert (EK : k = Z.log2 x) by reflexivity. clearbody k. clear PW RV4 EW4 RW4 R5 RW3 R4 RW2 R3 RV2 RV1 R1 R2. subst w4 w3 w2 v2 v1.
    assert (EX : x = q + 1) by reflexivity. clearbody x.
    (* [comment removed for export] *)
    step. step. step.
    step. rewrite (unsigned_lit (2 ^ k)) by lia. change 125613361 with rDB32.
    step. rewrite (mul_srliw27 k) by lia.
    pose proof (rdbi_range k) as DR.
    step. rewrite ?(unsigned_lit (rdbi k)) by lia.
    pose proof (rdebruijn_read m k MI ltac:(lia)) as DBR. unfold DEBRUIJN in DBR.
    step. rewrite ?zxb_b8 by lia. clear DBR.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned k), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. rewrite (unsigned_lit (k * 4)), lxor_4k_124 by lia.
    set (i := 4 * k - 4). assert (IR : 8 <= i <= 44) by lia.
    replace (124 - 4 * k) with (120 - i) by lia.
    assert (STQ : j = (let i1 := if size_class (i + 1) <? x then i + 2 else i in if size_class i1 <? x then i1 + 1 else i1)).
    { rewrite STC. unfold stc_q. replace (q <? 10) with false by (symmetry; apply Z.ltb_ge; lia). rewrite <- EX, <- EK. reflexivity. }
    assert (IEV : Z.even i = true) by (subst i; rewrite Z.even_sub, Z.even_mul; reflexivity).
    clearbody i. clear EK.
    pose proof (size_class_range (i + 1) ltac:(lia)) as SR1.
    step. step. rewrite (unsigned_lit (120 - i)) by lia. replace (121 + - (120 - i)) with (i + 1) by lia.
    step. rewrite (unsigned_lit (i + 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
    step. replace (85160 + (i + 1) * 2) with (85160 + 2 * (i + 1)) by lia.
    pose proof (size_classes_read m (i + 1) MI ltac:(lia)) as RS1. unfold SIZE_CLASSES in RS1.
    step. rewrite ?zx16_wz by lia. clear RS1.
    (* [comment removed for export] *)
    assert (J1 : forall (i1 c : Z),
      i1 = (if size_class (i + 1) <? x then i + 2 else i) -> c = i1 - i + 120 ->
      evt rsegs (fun ms' => exists a2'' a3'' a4'',
        ms' = MS (mkR (Z_to_bv 64 0x240a4) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 j) (wz n') a2'' a3'' a4'' a5 a6 a7 (Z_to_bv 64 j) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 85160) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 146628) fc None m (seg_rom rsegs))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (120 - i)) (wz n') (Z_to_bv 64 c) (Z_to_bv 64 85128) (Z_to_bv 64 q) a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 (Z_to_bv 64 85160) s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2407c) fc None m (seg_rom rsegs))).
    { intros i1 c Hi1 Hc.
      assert (I1R : 8 <= i1 <= 46 /\ Z.even i1 = true).
      { subst i1. destruct (size_class (i + 1) <? x); (split; [lia|]); rewrite ?Z.even_add, ?IEV; reflexivity. }
      destruct I1R as [I1R I1E].
      pose proof (size_class_range i1 ltac:(lia)) as SR2.
      (* [comment removed for export] *)
      step. rewrite ?(unsigned_lit c), ?(unsigned_lit (120 - i)) by lia. replace (c + - (120 - i)) with i1 by lia.
      step. rewrite (unsigned_lit i1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
      step. replace (85160 + i1 * 2) with (85160 + 2 * i1) by lia.
      pose proof (size_classes_read m i1 MI ltac:(lia)) as RS2. unfold SIZE_CLASSES in RS2.
      step. rewrite ?zx16_wz by lia. clear RS2.
      (* [comment removed for export] *)
      step. rewrite v_sltu_b2z, (unsigned_lit q), (wz_unsigned (size_class i1)) by lia.
      step. step.
      destruct (Z.ltb_spec q (size_class i1)) as [LT|GE]; cbn [Z.b2z].
      * rewrite (unsigned_lit 1), (unsigned_lit i1) by lia. change (Z.lxor 1 1) with 0. rewrite (unsigned_lit 0), Z.lor_0_r by lia.
        apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
      * rewrite (unsigned_lit 0), (unsigned_lit i1) by lia. change (Z.lxor 0 1) with 1. rewrite (unsigned_lit 1), (lor_even_1 i1 ltac:(lia) I1E) by lia.
        apply CALL. rewrite STQ. cbv zeta. rewrite <- Hi1.
        replace (size_class i1 <? x) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
    step. if_cases K3; zify_cond K3; rewrite ?(unsigned_lit q), ?(wz_unsigned (size_class (i + 1))) in K3 by lia.
    + (* [comment removed for export] *)
      step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with false by (symmetry; apply Z.ltb_ge; lia). lia.
    + (* [comment removed for export] *)
      step. step. eapply J1; [reflexivity|]. replace (size_class (i + 1) <? x) with true by (symmetry; apply Z.ltb_lt; lia). lia.
Qed.
End STC.

(* [comment removed for export] *)
Lemma nest_ret_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (idx : Z),
  -1 <= idx < 32 -> mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 (if idx =? -1 then 0x2411c else 0x240a8)) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x240a4) fc None m (seg_rom rsegs)).
Proof.
  intros until idx. intros IR MI.
  step. if_cases K; zify_cond K.
  - replace (idx =? -1) with true.
    2:{ symmetry. apply Z.eqb_eq. destruct (Z.eq_dec idx (-1)) as [E|NE]; [exact E|]. exfalso.
        (* [comment removed for export] *)
        revert K. Z.div_mod_to_equations. lia. }
    apply evt_done. reflexivity.
  - replace (idx =? -1) with false.
    2:{ symmetry. apply Z.eqb_neq. intros ->. revert K. Z.div_mod_to_equations. lia. }
    apply evt_done. reflexivity.
Qed.
End RASlico.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import F_sy88u MRep MRepAux RF_m8yt RAlllfc RF_mx3o Malllim.

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
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
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
(* [comment removed for export] *)

Section TASLOT.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st0 st stX : mstate) (LB : list block) (sc req : Z) (g : aptr) (k : Z).
Let mr := get_meta_rec stX g.
Let msk := m_avail mr.
Let st' := upd_meta g (m_set_avail (msk - lowbit msk)) stX.
Hypothesis F : ISTF st LB.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis TR : ta_rel sc st stX.
Hypothesis HA : active stX sc = Some g.
Hypothesis GM : gmf st sc g.
Hypothesis MSK : 0 < msk < 2^32.
Hypothesis K0 : 0 <= k < 32.
Hypothesis LBK : lowbit msk = 2 ^ k.

#[using="LBK"] Lemma rec_st' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr.
Proof. unfold st'. rewrite get_meta_rec_upd_same. rewrite LBK. reflexivity. Qed.

#[using="LBK K0 MSK GM TR FIT RQ SC ER F sc LB"] Lemma ta_slot_ok : exists b r,
  m_mem (get_meta_rec st g) = Some b /\ (s_regions st) !! (fst b) = Some r /\ (s_regions st') !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ slot_ok st' g b r k req
  /\ get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)
  /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k - 4 <= a
               < r_base r + snd b + 16 + get_stride (get_meta_rec st' g) * k + get_stride (get_meta_rec st' g) - 4 ->
        free_slot_addr st0 a).
Proof.
  pose proof (isf_mf _ _ F) as MF.
  pose proof (gmf_cls _ _ _ GM) as GSC.
  (first [ pose proof ((gmf_grp _ _ _ GM)) as dR_1; dex2 dR_1 as b gh; dand6 dR_1 as Hmem Hgh GMETA AIR SC0 UNK | pose proof ((gmf_grp _ _ _ GM)) as dR_1; dand8 dR_1 as b gh Hmem Hgh GMETA AIR SC0 UNK | destruct (gmf_grp _ _ _ GM) as (b & gh & Hmem & Hgh & GMETA & AIR & SC0 & UNK) ]).
  pose proof (mf_gmeta _ _ MF) as FG. change (fact_gmeta (strip st)) with (fact_gmeta st) in FG.
  specialize (FG g b Hmem). cbv zeta in FG.
  (first [ dand14 FG as MSL AVr FRr LI FB SCr ML0 (ai & Hgh' & AI & AVAI) (r & Hr & Hk & B0 & B16 & SPAN) S16 SMOD S31 UND S20 | destruct FG as (MSL & AVr & FRr & LI & FB & SCr & ML0 & (ai & Hgh' & AI & AVAI) & (r & Hr & Hk & B0 & B16 & SPAN) & S16 & SMOD & S31 & UND & S20) ]).
  (* [comment removed for export] *)
  (first [ pose proof ((tr_geom _ _ _ TR g)) as dR_3; dand5 dR_3 as EM REL EF ES EP | destruct (tr_geom _ _ _ TR g) as (EM & REL & EF & ES & EP) ]).
  assert (STX : get_stride mr = get_stride (get_meta_rec st g)) by (unfold get_stride, mr; rewrite REL, ES, EP; reflexivity).
  assert (E' : get_meta_rec st' g = m_set_avail (msk - 2 ^ k) mr) by apply rec_st'.
  assert (ST' : get_stride (get_meta_rec st' g) = get_stride (get_meta_rec st g)).
  { rewrite E', <- STX. unfold get_stride. cbn [m_last_idx m_maplen m_sizeclass m_set_avail]. reflexivity. }
  (* [comment removed for export] *)
  assert (TBk : Z.testbit msk k = true) by (apply lowbit_testbit; [lia| exact LBK]).
  assert (TBst : Z.testbit (m_avail (get_meta_rec st g)) k || Z.testbit (m_freed (get_meta_rec st g)) k = true).
  { apply (tr_bits _ _ _ TR g k ltac:(lia)). unfold msk, mr in TBk. rewrite TBk. reflexivity. }
  pose proof (mf_masks _ _ MF) as FM. change (fact_masks (strip st)) with (fact_masks st) in FM.
  (first [ pose proof ((FM g b Hmem)) as dR_4; dand3 dR_4 as FM1 FM2 _ | destruct (FM g b Hmem) as (FM1 & FM2 & _) ]).
  assert (KLI : k <= m_last_idx (get_meta_rec st g)).
  { destruct (Z.testbit (m_avail (get_meta_rec st g)) k) eqn:Ta; [exact (FM1 k ltac:(lia) Ta)|].
    cbn in TBst. exact (FM2 k ltac:(lia) TBst). }
  assert (GSC48 : m_sizeclass (get_meta_rec st g) < 48) by (rewrite GSC; lia).
  destruct SCr as [[GS0 MPL]|[E63 _]]; [|lia].
  pose proof (mf_free_clear _ _ MF g b k Hmem ltac:(lia) ltac:(destruct (Z.testbit (m_avail (get_meta_rec (strip st) g)) k) eqn:Ta; [left; reflexivity| right; change (get_meta_rec (strip st) g) with (get_meta_rec st g) in Ta |- *; rewrite Ta in TBst; exact TBst])) as FC.
  cbv zeta in FC. destruct FC as [NOGRP _].
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in NOGRP. change (s_groups (strip st)) with (s_groups st) in NOGRP.
  unfold sstart_of in NOGRP. rewrite Hmem in NOGRP. cbn [default from_option id snd] in NOGRP. unfold UNIT, IB in NOGRP.
  pose proof (mf_hdr0 _ _ MF g b k Hmem ltac:(lia)) as K4.
  unfold sstart_of in K4. rewrite Hmem in K4. cbn [default from_option id fst snd] in K4. unfold IB, UNIT in K4.
  unfold sstart_of in SPAN. rewrite Hmem in SPAN. cbn [default from_option id snd] in SPAN. unfold UNIT, IB in SPAN.
  assert (SFIT : 16 * size_class sc <= get_stride (get_meta_rec st g)).
  { pose proof (lf_bit_stride _ (isf_lf _ _ F) g b k) as HS.
    change (get_meta_rec (strip st) g) with (get_meta_rec st g) in HS. rewrite GSC in HS. unfold UNIT in HS.
    exact (HS Hmem ltac:(lia) TBst ltac:(lia)). }
  pose proof (mf_maplen _ _ MF g b Hmem) as MPL40. change (get_meta_rec (strip st) g) with (get_meta_rec st g) in MPL40.
  pose proof (mf_slots_complete _ _ MF g b k Hmem ltac:(change (get_meta_rec (strip st) g) with (get_meta_rec st g); lia)) as SSL.
  change (get_meta_rec (strip st) g) with (get_meta_rec st g) in SSL. change (s_slots (strip st)) with (s_slots st) in SSL.
  unfold sstart_of in SSL. rewrite Hmem in SSL. cbn [default from_option id snd] in SSL. unfold UNIT in SSL.
  destruct (tr_mrange _ _ _ TR g AVr FRr) as [AVX FRX].
  assert (P2k : 0 < 2 ^ k <= msk).
  { split; [apply Z.pow_pos_nonneg; lia|]. (first [ pose proof ((lowbit_pow2 msk ltac:(lia))) as dR_5; dex1 dR_5 as k'; dand3 dR_5 as _ EE LE' | pose proof ((lowbit_pow2 msk ltac:(lia))) as dR_5; dand4 dR_5 as k' _ EE LE' | destruct (lowbit_pow2 msk ltac:(lia)) as (k' & _ & EE & LE') ]). unfold lowbit in LBK. rewrite LBK in EE. rewrite EE. exact LE'. }
  exists b, r.
  split; [exact Hmem|]. split; [exact Hr|].
  split; [unfold st'; cbn; rewrite (tr_regions _ _ _ TR); exact Hr|]. split; [exact Hk|].
  split; [| split; [exact ST'|]].
  - (first [ pose proof ((gmf_mw _ _ _ GM)) as dR_6; dand4 dR_6 as MW1 MW2 MW3 MW4 | pose proof (gmf_mw _ _ _ GM) as (MW1 & MW2 & MW3 & MW4) ]).
    assert (ST2 : get_stride (m_set_avail (msk - 2 ^ k) mr) = get_stride (get_meta_rec st g)) by (rewrite <- E'; exact ST').
    constructor; rewrite ?E'; rewrite ?ST2; cbn [m_mem m_avail m_freed m_last_idx m_freeable m_sizeclass m_maplen m_set_avail];
      rewrite ?ST2; fold mr; rewrite ?EM, ?REL, ?EF, ?ES, ?EP, ?STX.
    + exact Hmem.
    + unfold st'. cbn. rewrite (tr_regions _ _ _ TR). exact Hr.
    + exact Hk.
    + exact B0.
    + exact B16.
    + lia.
    + lia.
    + exact SPAN.
    + unfold UNIT in S16. lia.
    + unfold UNIT in SMOD. exact SMOD.
    + lia.
    + exact RQ.
    + lia.
    + intros b' gh0 Hb' Hf'. unfold st' in Hb'. cbn in Hb'.
      (first [ pose proof ((tr_gmeta _ _ _ TR b' gh0 Hb')) as dR_7; dex1 dR_7 as gh1; destruct dR_7 as [Hb1 _] | pose proof ((tr_gmeta _ _ _ TR b' gh0 Hb')) as dR_7; dand3 dR_7 as gh1 Hb1 _ | destruct (tr_gmeta _ _ _ TR b' gh0 Hb') as (gh1 & Hb1 & _) ]). exact (NOGRP b' gh1 Hb1 Hf').
    + unfold st'. unfold get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). exact K4.
    + intros off O0 OF.
      assert (get_stride (get_meta_rec st g) * k + 16 * off < get_stride (get_meta_rec st g) * (k + 1)) by lia.
      assert (get_stride (get_meta_rec st g) * (k + 1) <= get_stride (get_meta_rec st g) * (m_last_idx (get_meta_rec st g) + 1)) by (apply Z.mul_le_mono_nonneg_l; lia).
      specialize (S20 GSC48). apply Z.div_lt_upper_bound; lia.
    + unfold st'. cbn. rewrite (tr_slots _ _ _ TR). exact SSL.
    + unfold st'. apply meta_slot_put_meta. eapply meta_slot_same_areas; [| exact MSL]. apply (tr_areas _ _ _ TR).
    + unfold msk, mr in *. lia.
    + unfold mr. lia.
    + lia.
    + lia.
    + left. lia.
  - intros a Ha. rewrite ST' in Ha.
    destruct ER as [ES0 EG0 EGR0 EM0 EME0 EGE0 EB0 EA0].
    assert (Hmem0 : m_mem (get_meta_rec st0 g) = Some b) by (rewrite <- EME0; exact Hmem).
    (first [ pose proof ((EGE0 g ltac:(rewrite Hmem0; discriminate))) as dR_8; dand3 dR_8 as GS0' GL0' GC0' | destruct (EGE0 g ltac:(rewrite Hmem0; discriminate)) as (GS0' & GL0' & GC0') ]).
    exists g, b, r, k. split; [exact Hmem0|]. split; [apply (proj1 (EGR0 (fst b) r Hk)); exact Hr|]. split; [exact Hk|]. split; [lia|].
    split; [| unfold sstart_of; rewrite Hmem0; cbn [default from_option id snd]; unfold UNIT, IB; rewrite <- GS0'].
    + pose proof (EB0 g k ltac:(lia) TBst) as TB0. destruct (Z.testbit (m_avail (get_meta_rec st0 g)) k); [left; reflexivity| right; exact TB0].
    + assert (get_stride (get_meta_rec st g) * k + get_stride (get_meta_rec st g) <= get_stride (get_meta_rec st g) * m_last_idx (get_meta_rec st g) + get_stride (get_meta_rec st g))
        by (apply Z.add_le_mono_r; apply Z.mul_le_mono_nonneg_l; lia).
      assert (0 <= get_stride (get_meta_rec st g) * k) by (apply Z.mul_nonneg_nonneg; lia).
      lia.
Qed.
End TASLOT.


(* [comment removed for export] *)
(* [comment removed for export] *)

Section LEVEL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Context {R : Type}.
Variables (f : nat) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R) (o : mem) (s : PState) (Q : R -> PState -> machine_state -> Prop).
Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (st0 st : mstate) (LB : list block) (lo sc req : Z) (errv : word).
Hypothesis AR : AREACH st0 LB.
Hypothesis IS : IST st0 st.
Hypothesis ER : ENTRY_REL st0 st.
Hypothesis AC : ALLC st.
Hypothesis SC : 0 <= sc < 48.
Hypothesis RQ : 0 <= req < 2^32.
Hypothesis FIT : req + 4 <= 16 * size_class sc.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis UA : unk_agree st o m.
Hypothesis BL : brk_link_ps st s.
Hypothesis AUX : auxv_okd (c_init_done (ctx st0)) m (bv_unsigned sp).
Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
Hypothesis CLO : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - AS_STACK sc.
Hypothesis ERR : rw_cells rsegs m (errno_addr tp) [C4 errv].
Hypothesis MI : mem_inv rsegs m.
Hypothesis TP : tp = Z_to_bv 64 PTP.
Hypothesis A0 : a0 = Z_to_bv 64 sc.
Hypothesis A1 : a1 = Z_to_bv 64 req.
Hypothesis HK : forall st1 idx s' ms',
  as_post2 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc o m st0 st s lo sc req st1 idx s' ms' ->
  implT o (k st1 idx) s' Q ms'.
Let F0 : ISTF st LB := Mall8ro.ist_facts_proof st0 LB st AR IS.

#[using="HK TP ERR errv req sc lo st st0 m fc F s11 s10 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 gp sp ra Q s o k R Rr Clg"] Lemma errno_lit : errno_addr tp = 0x420b4.
Proof. subst tp. unfold PTP. rewrite unsigned_lit by lia. reflexivity. Qed.

#[using="F0 HK TP ERR LO CLO AUX BL UA TK MR FIT RQ SC AC ER IS AR errv LB st0"] Lemma hk1_ok : forall stX g3 msk kk m' (t0' t1' a1' a2' a3' a4' a5' a6' a7' : word),
  ta_rel sc st stX -> active stX sc = Some g3 -> gmf st sc g3 ->
  msk = m_avail (get_meta_rec stX g3) -> 0 < msk < 2^32 -> lowbit msk = 2 ^ kk -> 0 <= kk < 32 ->
  mrep (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
  pres_except (ta_fp st lo (bv_unsigned sp)) m m' ->
  implT o (as_k full_lay f sc req k bail (upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) (lowbit msk)) s Q
    (MS (mkR ra sp gp tp t0' t1' t2 s0 s1 (wz kk) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (ret_pc ra) fc None m' (seg_rom rsegs)).
Proof.
  intros until a7'. intros TR HA GM MSK MR0 LBK KK MR' MI' ST' PE.
  unfold as_k. replace (lowbit msk =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite LBK; pose proof (Z.pow_pos_nonneg 2 kk); lia).
  cbn [negb]. rewrite LBK at 2. rewrite ctz32_pow2 by lia.
  pose proof errno_lit as EA. pose proof (AS_STACK_ge sc) as ASG.
  pose proof (isf_mf _ _ F0) as MF.
  set (st' := upd_meta g3 (m_set_avail (msk - lowbit msk)) stX) in *.
  subst msk.
  (first [ pose proof ((ta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)) as dR_9; dex2 dR_9 as b r; dand7 dR_9 as Hmem Hr Hr' Hk SO STR FSA | pose proof ((ta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)) as dR_9; dand9 dR_9 as b r Hmem Hr Hr' Hk SO STR FSA | destruct (ta_slot_ok st0 st stX LB sc req g3 kk F0 ER SC ltac:(lia) FIT TR GM MR0 KK LBK)
    as (b & r & Hmem & Hr & Hr' & Hk & SO & STR & FSA) ]).
  fold st' in Hr', SO, STR, FSA.
  (* [comment removed for export] *)
  pose proof MR as (WF & _). (first [ pose proof (WF) as dR_10; dand5 dR_10 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
  assert (REGX : s_regions st' = s_regions st) by (unfold st'; cbn; apply (tr_regions _ _ _ TR)).
  assert (CONCX : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite REGX; reflexivity).
  (* [comment removed for export] *)
  assert (FPC : forall a, ta_fp st lo (bv_unsigned sp) a -> malloc_fp st0 st' lo (bv_unsigned sp) a).
  { intros a [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - left. left. exact X.
    - left. right. right. left. exact X.
    - left. do 3 right. (first [ pose proof ((meta_chunk_facts st m q MR MSq)) as dR_11; dand7 dR_11 as _ _ _ _ _ _ (rid0 & r0 & H0 & K0 & L0 & H0') | destruct (meta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')) ]).
      exists rid0, r0. rewrite REGX. split; [exact H0|]. split; [exact K0|]. lia.
    - do 3 right. left. (first [ pose proof ((group_conc st bq gh WF Hbq)) as dR_12; dex1 dR_12 as rb; dand7 dR_12 as Hrb Cb Kb B0 B16' M16 _ | pose proof ((group_conc st bq gh WF Hbq)) as dR_12; dand8 dR_12 as rb Hrb Cb Kb B0 B16' M16 _ | destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _) ]).
      destruct ER as [_ EG EGR _ _ _ _ _].
      destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
      exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
      pose proof (round_up_pg_ge (r_len rb)). rewrite Cb in Xq. lia. }
  assert (PE' : pres_except (malloc_fp st0 st' lo (bv_unsigned sp)) m m') by (eapply pres_except_mono; [exact PE| exact FPC]).
  (* [comment removed for export] *)
  assert (NIMG : forall a, 0x10000 <= a < 0x63000 -> ~ (CTX <= a < CTX + 928) -> ~ ta_fp st lo (bv_unsigned sp) a).
  { intros a Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
    - exact (Hc X).
    - (first [ pose proof ((meta_slot_bounds st m q MR MSq)) as dR_13; dand4 dR_13 as _ _ GI _ | destruct (meta_slot_bounds st m q MR MSq) as (_ & _ & GI & _) ]). lia.
    - (first [ pose proof ((group_conc st bq gh WF Hbq)) as dR_14; dex1 dR_14 as rb; dand6 dR_14 as Hrb Cb Kb B0 BE _ | pose proof ((group_conc st bq gh WF Hbq)) as dR_14; dand7 dR_14 as rb Hrb Cb Kb B0 BE _ | destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _) ]). (first [ pose proof ((rregion_facts st m (fst bq) rb MR Hrb)) as dR_15; dand5 dR_15 as _ _ _ RI1 RI2 | destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2) ]).
      pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia. }
  apply HK. unfold as_post2.
  exists t0', t1', t2, a1', a2', a3', a4', a5', a6', a7', t3, t4, t5, t6, m', errv.
  split; [reflexivity|].
  split; [exact MI'|]. split; [exact ST'|].
  split. { eapply pres_except_rw_cells; [exact PE| exact ERR|]. rewrite EA. cbn. intros a Ha. apply NIMG; [lia| unfold CTX; lia]. }
  split. { eapply auxv_okd_pres; [exact AUX| exact PE| |].
           - intros a Ha X. destruct X as [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
             + lia. + unfold CTX in X. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
             + (first [ pose proof ((meta_slot_bounds st m q MR MSq)) as dR_16; dand3 dR_16 as _ GC _ | destruct (meta_slot_bounds st m q MR MSq) as (_ & GC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
             + (first [ pose proof ((group_conc st bq gh WF Hbq)) as dR_17; dex1 dR_17 as rb; dand8 dR_17 as Hrb Cb Kb B0 BE M16 RB0 RC | pose proof ((group_conc st bq gh WF Hbq)) as dR_17; dand9 dR_17 as rb Hrb Cb Kb B0 BE M16 RB0 RC | destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
           - intros a Ha. apply NIMG; unfold AUXV_CELL, CTX in *; lia. }
  split; [exact MR'|].
  split. { unfold st'. apply ticks_ok_upd_meta. eapply ticks_ok_same; [| | exact TK]; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)]. }
  split. { (* [comment removed for export] *)
    intros rid rr off h Hrr Kr Ho Hc NG. rewrite REGX in Hrr.
    assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h).
    { revert Hc. unfold st', get_shadow. cbn. rewrite (tr_shadow _ _ _ TR). intros Hc; exact Hc. }
    assert (NG0 : ~ grp_hdr_cov st rid off).
    { ((first [ intro dR_25; dex2 dR_25 as bq gh; dand3 dR_25 as Hbq Hf Hoff | intro dR_25; dand5 dR_25 as bq gh Hbq Hf Hoff | intros (bq & gh & Hbq & Hf & Hoff) ])). apply NG. destruct (tr_groups _ _ _ TR bq) as [_ B2].
      destruct (B2 (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. unfold st'. cbn. auto. }
    rewrite <- (UA rid rr off h Hrr Kr Ho Hc0 NG0).
    refine (proj1 (PE (r_base rr + off) _ _)).
    { (first [ pose proof ((WR _ _ Hrr)) as dR_18; dand5 dR_18 as R0 _ _ RC _ | destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _) ]). pose proof (round_up_pg_ge (r_len rr)). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
    intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
    - (first [ pose proof ((WR _ _ Hrr)) as dR_19; dand5 dR_19 as R0 _ _ RC _ | destruct (WR _ _ Hrr) as (R0 & _ & _ & RC & _) ]). lia.
    - (first [ pose proof ((rregion_facts st m rid rr MR Hrr)) as dR_20; dand5 dR_20 as _ _ _ RI1 RI2 | destruct (rregion_facts st m rid rr MR Hrr) as (_ & _ & _ & RI1 & RI2) ]). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold CTX in X. lia.
    - (first [ pose proof ((meta_chunk_facts st m q MR MSq)) as dR_21; dand7 dR_21 as _ _ _ _ _ GRG _ | destruct (meta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _) ]). destruct (GRG rid rr Hrr Kr); lia.
    - (first [ pose proof ((group_conc st bq gh WF Hbq)) as dR_22; dex1 dR_22 as rb; dand7 dR_22 as Hrb Cb Kb B0 B16' M16 _ | pose proof ((group_conc st bq gh WF Hbq)) as dR_22; dand8 dR_22 as rb Hrb Cb Kb B0 B16' M16 _ | destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _) ]).
      destruct (N.eq_dec (fst bq) rid) as [E|NE].
      + apply NG0. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hrr in Hrb. inversion Hrb; subst rb. lia.
      + pose proof (lr_lo_group rr Kr). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hrr NE); lia. }
  split; [exact PE'|].
  split. { split; [| unfold st'; cbn; rewrite (tr_next _ _ _ TR); lia| unfold st'; cbn; apply (tr_reserved _ _ _ TR)].
           intros rid rr Hrr. exists rr. rewrite REGX. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. lia. }
  split. { unfold brk_link_ps in *. unfold st', ctx in *. cbn. (first [ pose proof ((tr_ctx _ _ _ TR)) as dR_23; dand15 dR_23 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ CB' | destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB') ]).
           unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONCX. exact BL. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split. { (* [comment removed for export] *) constructor.
    - intros c Hc. unfold st'. rewrite active_upd_meta. apply (tr_active _ _ _ TR). lia.
    - intros a Ha. unfold st'. cbn. rewrite (tr_areas _ _ _ TR). exact Ha.
    - unfold st'. cbn. apply (tr_tick _ _ _ TR).
    - intros _ rid S len _ o' v t Ho Hc. unfold st', get_shadow in Hc. cbn in Hc. rewrite (tr_shadow _ _ _ TR) in Hc.
      unfold st'. cbn. rewrite (tr_tick _ _ _ TR).
      destruct ((s_shadow st) !! rid) as [sh|] eqn:Esh; [| cbn in Hc; rewrite lookup_empty in Hc; discriminate].
      exact (AC rid sh o' v t Esh Hc).
    - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate. }
  split. { unfold st', ctx. cbn. (first [ pose proof ((tr_ctx _ _ _ TR)) as dR_24; dand4 dR_24 as _ _ CC _ | destruct (tr_ctx _ _ _ TR) as (_&_&CC&_) ]). unfold ctx in CC. rewrite CC.
           pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
  right. split; [lia|]. exists g3, b, r.
  split; [unfold st'; rewrite active_upd_meta; exact HA|]. split; [exact SO|]. split.
  - intros a Ha. do 2 right. left. apply FSA. exact Ha.
  - intros E0. exfalso. destruct ER as [_ _ EGR _ _ _ _ _]. pose proof (proj1 (EGR (fst b) r Hk) Hr) as X. rewrite E0 in X. rewrite lookup_empty in X. discriminate.
Qed.
End LEVEL.