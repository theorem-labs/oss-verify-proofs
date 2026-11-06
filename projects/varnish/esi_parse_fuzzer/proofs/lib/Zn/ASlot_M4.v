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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_sy88u MRep MRepAux MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_mm4hw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_mm4hw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallkgx Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3 Malls02 RAlllfc RF_mx3o Malllim RF_muly.

Module RF_m79e.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Mall5lv Mallj6y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall5lv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mdx7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_m8yt RF_mdx7 RF_muly Malleon.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o.RF_mcaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mdx7.RF_m8qy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mdx7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malleon.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y RF_mk75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3 RF_egfy.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RF_mx3o.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc RF_m8yt RF_mx3o SlotMisc RF_mdx7 Malls02 RF_muly.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o.RF_mcaj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.SlotMisc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mdx7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_muly.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep MRepAux F_mm4hw RAlllfc.
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

Lemma unk_agree_transfer st st' o m m' :
  unk_agree st o m ->
  (forall rid r, (s_regions st') !! rid = Some r -> r_kind r = RKGroup ->
     ((s_regions st) !! rid = Some r /\ get_shadow st' rid = get_shadow st rid /\
       (forall off, grp_hdr_cov st rid off -> grp_hdr_cov st' rid off) /\
       (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st rid) off = Unknown h ->
          ~ grp_hdr_cov st' rid off -> m' (wa (r_base r + off)) = m (wa (r_base r + off))))
     \/ (forall off h, 0 <= off < round_up_pg (r_len r) -> cell_read (get_shadow st' rid) off = Unknown h -> grp_hdr_cov st' rid off)) ->
  unk_agree st' o m'.
Proof.
  intros UA H rid r off h Hr Hk Ho Hc NG.
  destruct (H rid r Hr Hk) as [(Hr0 & ES & GM & AG)|NEW].
  - rewrite ES in Hc. rewrite (AG off h Ho Hc NG). apply (UA rid r off h Hr0 Hk Ho Hc). intros X. apply NG, GM, X.
  - exfalso. apply NG. eapply NEW; eauto.
Qed.
Lemma grp_hdr_cov_same st st' rid off : s_groups st' = s_groups st -> grp_hdr_cov st rid off -> grp_hdr_cov st' rid off.
Proof. (intros EG; (first [ intro dR_45; dex2 dR_45 as b gh; dand3 dR_45 as Hb E R | intro dR_45; dand5 dR_45 as b gh Hb E R | intros (b & gh & Hb & E & R) ])). exists b, gh. rewrite EG. auto. Qed.
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma brk_link_ps_ext st st' s :
  c_brk (ctx st') = c_brk (ctx st) ->
  (forall rid off, c_brk (ctx st) = BrkLive rid off -> conc st' (rid, off) = conc st (rid, off)) ->
  brk_link_ps st s -> brk_link_ps st' s.
Proof.
  intros EB EC BL. unfold brk_link_ps in *. rewrite EB. destruct (c_brk (ctx st)) as [| |rid off] eqn:E; auto.
  rewrite (EC rid off eq_refl). exact BL.
Qed.

End CEIL.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.


(* [comment removed for export] *)
Definition big_final (st3 : mstate) (g : aptr) (rid : N) (n : Z) : mstate :=
  let needed := n + IB + UNIT in
  let st4 := upd_meta g (fun mr =>
               m_set_freed 0 (m_set_avail 0 (m_set_maplen ((needed + 4095) / 4096)
               (m_set_sizeclass 63 (m_set_freeable 1 (m_set_last_idx 0 (m_set_mem (Some (rid, 0)) mr))))))) st3 in
  let st5 := put_group (rid, 0) (Some g) (group_active_idx st4 (rid, 0)) (lh_hdr full_lay st4 (rid, 0)) in
  let st6 := add_slots g (rid, 0) (get_stride (get_meta_rec st5 g)) 1 st5 in
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st6.
Section CEIL2.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma malloc_core_big_eq st1 n : MMAP_THRESHOLD <= n < 2^32 ->
  malloc_core full_lay st1 n =
    SVis (EMmap 0 (n + IB + UNIT) PROT_RW (MAP_PRIVATE + MAP_ANON)) (fun r =>
      if negb (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) r) then bad_answer (ret (st1, @None (aptr * Z))) else
      if is_err r then ret (st1, None) else
      let '(st2, rid) := new_region RKGroup r (n + IB + UNIT) st1 in
      alloc_meta (step_seq st2) (fun st3 go =>
        match go with
        | None => SVis (EMunmap r (n + IB + UNIT)) (fun ru => if munmap_answer_ok ru then ret (drop_region rid st3, @None (aptr * Z)) else bad_answer (ret (st1, None)))
        | Some g => ret (big_final st3 g rid n, Some (g, 0))
        end) (ret (st1, None))).
Proof.
  intros Hn. unfold malloc_core.
  replace (size_overflows n) with false by (symmetry; unfold size_overflows; apply Z.leb_gt; lia).
  replace (MMAP_THRESHOLD <=? n) with true by (symmetry; apply Z.leb_le; lia).
  reflexivity.
Qed.
Lemma munmap_answer_ok_range a : match a with RgErr e => 1 <= e <= 4095 | RgDone _ => True end -> munmap_answer_ok (range_val a) = true.
Proof.
  destruct a as [e|b]; cbn [range_val]; intros He.
  - unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
    replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia).
    destruct (2 ^ 64 - e =? 0); reflexivity.
  - reflexivity.
Qed.
Lemma mmap_answer_ok_err live len e : 1 <= e <= 4095 -> mmap_answer_ok live len (neg_errno e) = true /\ is_err (neg_errno e) = true.
Proof.
  intros He. unfold mmap_answer_ok, is_errno_form, is_err, neg_errno, TWO64. split.
  - replace (2 ^ 64 - 4095 <=? 2 ^ 64 - e) with true by (symmetry; apply Z.leb_le; lia).
    replace (2 ^ 64 - e <? 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - apply Z.ltb_lt. lia.
Qed.
Lemma mmap_answer_ok_addr live len xa : 0 <= len ->
  mmap_addr_ok len [] xa = true -> mmap_answer_ok live len xa = true ->
  0 < xa /\ xa mod 4096 = 0 /\ xa + round_up_pg len <= alloc_ceiling /\ ranges_free live xa (round_up_pg len) = true /\ is_err xa = false.
Proof.
  intros L0 A B. pose proof (round_up_pg_ge len) as RG. unfold mmap_addr_ok in A. rewrite !Bool.andb_true_iff in A. destruct A as [[[A1 A2] A3] _].
  apply Z.eqb_eq in A1. apply Z.ltb_lt in A2. apply Z.leb_le in A3. rewrite mmap_len_round_up in A3.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). change page_size with 4096 in A1.
  unfold mmap_answer_ok in B. apply Bool.orb_prop in B.
  assert (NE : is_errno_form xa = false).
  { unfold is_errno_form, TWO64. replace (2 ^ 64 - 4095 <=? xa) with false by (symmetry; apply Z.leb_gt; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia). reflexivity. }
  destruct B as [B|B]; [rewrite NE in B; discriminate|].
  rewrite !Bool.andb_true_iff in B. destruct B as [[[_ _] _] B4].
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. unfold is_err, TWO64. apply Z.ltb_ge. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
Qed.
Lemma munch_of_pointwise (lo hi : Z) (m m' : mem) :
  0 <= lo -> hi <= 2^64 ->
  (forall a, 0 <= a < 2^64 -> (a < lo \/ hi <= a) -> m' (wa a) = m (wa a)) -> munch [(lo, hi)] m m'.
Proof.
  intros H0 H1 AG x Hx. cbn in Hx. pose proof (bv_unsigned_in_range 64 x) as R. change (bv_modulus 64) with (2^64) in R.
  rewrite <- (wa_unsigned_id x). apply AG; lia.
Qed.
Lemma cell_read_hh0 st rid off : (s_shadow st) !! rid = None -> 0 <= off ->
  cell_read (get_shadow (hdr_havoc (rid, 0) st) rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
  intros SH Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow fst snd].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty. change (0 / 16) with 0.
  destruct (Z.eq_dec (off / 16) 0) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
    replace (off mod 16) with off by (Z.div_mod_to_equations; lia). destruct (off <? 12); reflexivity.
  - rewrite lookup_insert_ne by congruence. rewrite lookup_empty. cbn.
    replace (off <? 12) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia). reflexivity.
Qed.
Lemma round_up_pg_4115 n : 0 <= n -> round_up_pg (n + IB + UNIT) = (n + 4115) / 4096 * 4096.
Proof. intros Hn. unfold IB, UNIT. rewrite round_up_pg_eq. Z.div_mod_to_equations. lia. Qed.
Lemma mrep_ext : forall st st' m,
  mrep st m ->
  s_regions st' = s_regions st -> ctx st' = ctx st -> (forall q, get_meta_rec st' q = get_meta_rec st q) ->
  s_areas st' = s_areas st -> s_groups st' = s_groups st -> (forall rid, get_shadow st' rid = get_shadow st rid) ->
  s_reserved st' = s_reserved st ->
  mrep st' m.
Proof.
  (intros st st' m; (first [ intro dR_46; dand6 dR_46 as WF CX GL AR GR SH | intros (WF & CX & GL & AR & GR & SH) ]); intros ER EC EM EA EG ES ERs).
  assert (Hconc : forall q, conc st' q = conc st q) by (intros q; unfold conc, get_region; rewrite ER; reflexivity).
  split; [|split; [|split; [exact GL|split; [|split]]]].
  - unfold regions_wf. rewrite ER, EA, EG, ERs. exact WF.
  - eapply mrep_ctx_ext; [exact EC| exact Hconc| exact CX].
  - intros a ar Ha. rewrite EA in Ha. eapply area_rep_ext; [exact Hconc| intros; apply EM| exact (AR a ar Ha)].
  - intros b gh Hb. rewrite EG in Hb. eapply group_rep_ext; [exact Hconc| exact (GR b gh Hb)].
  - intros rid r Hr Hk. rewrite ER in Hr. eapply shadow_rep_ext; [apply ES| exact (SH rid r Hr Hk)].
Qed.

End CEIL2.

Section FINAL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st3 : mstate) (g : aptr) (rid : N) (xa n c : Z).
Hypothesis G0 : get_meta_rec st3 g = meta0.
Hypothesis GN : (s_groups st3) !! (rid, 0) = None.
Hypothesis HC : c_mmap_counter (ctx st3) = c.
Hypothesis NR : 0 <= n < 2^32.
Hypothesis RR : (s_regions st3) !! rid = Some (mkRegion RKGroup xa (n + IB + UNIT)).

Let stF := big_final st3 g rid n.
Let stM := big_st st3 g rid n (u32 (c + 1)).

#[using="G0"] Lemma bf_meta : get_meta_rec stF g = big_meta rid n.
Proof.
  unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. cbn [default from_option id].
  rewrite G0. reflexivity.
Qed.

Lemma bf_meta_other q : q <> g -> get_meta_rec stF q = get_meta_rec st3 q.
Proof.
  intros NE. unfold stF, big_final, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma bm_meta : get_meta_rec stM g = big_meta rid n.
Proof. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_eq. reflexivity. Qed.
Lemma bm_meta_other q : q <> g -> get_meta_rec stM q = get_meta_rec st3 q.
Proof.
  intros NE. unfold stM, big_st, get_meta_rec. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite lookup_insert_ne by congruence. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="GN"] Lemma bf_groups : s_groups stF = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land]. unfold group_active_idx, get_group. cbn -[Z.add Z.mul Z.div Z.land].
  rewrite GN. reflexivity.
Qed.
Lemma bm_groups : s_groups stM = <[(rid, 0) := mkGhdr (Some g) 0]> (s_groups st3).
Proof. reflexivity. Qed.
(* [comment removed for export] *)
Lemma bf_shadow_other q : q <> rid -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF, big_final, get_shadow. cbn -[Z.add Z.mul Z.div Z.land]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.
#[using="HC"] Lemma bf_ctx : ctx stF = ctx stM.
Proof. unfold stF, stM, big_final, big_st, ctx. cbn -[Z.add Z.mul Z.div Z.land u32]. unfold ctx in HC. rewrite HC. reflexivity. Qed.
#[using="stM HC"] Lemma bf_counter : c_mmap_counter (ctx stF) = u32 (c + 1).
Proof. rewrite bf_ctx. reflexivity. Qed.

#[using="HC GN G0"] Lemma mrep_big_final m : mrep stM m -> mrep stF m.
Proof.
  intros MR. eapply (mrep_ext stM stF m MR); try reflexivity.
  - exact bf_ctx.
  - intros q. destruct (decide (q = g)) as [->|NE]; [rewrite bf_meta, bm_meta; reflexivity| rewrite bf_meta_other, bm_meta_other by exact NE; reflexivity].
  - rewrite bf_groups, bm_groups. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="NR"] Lemma bf_stride : get_stride (big_meta rid n) = big_ml n * 4096 - 16.
Proof.
  unfold get_stride, big_meta. cbn [m_last_idx m_maplen]. rewrite big_ml_eq by lia.
  replace ((n + 4115) / 4096 =? 0) with false by (symmetry; apply Z.eqb_neq; Z.div_mod_to_equations; lia).
  cbn. rewrite <- big_ml_eq by lia. unfold UNIT. reflexivity.
Qed.

Lemma bf_slots : s_slots stF = <[(rid, 16) := (g, 0)]> (s_slots st3).
Proof.
  unfold stF, big_final. cbn -[Z.add Z.mul Z.div Z.land get_stride get_meta_rec Z.sub].
  unfold aadd. cbn [fst snd]. rewrite Z.mul_0_r, Z.add_0_r. reflexivity.
Qed.
End FINAL.


(* [comment removed for export] *)
Section CEIL3.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma rrepfoot_where2 st m a : mrep st m -> repfoot st a ->
  a < alloc_ceiling /\ (CTX <= a < CTX + 928 \/ MLOCK <= a < MLOCK + 4 \/ LIBC <= a < LIBC + 0x38 \/ GOT_SSP <= a < GOT_SSP + 8 \/ SSP_GUARD <= a < SSP_GUARD + 8 \/ a < 0x10000 \/ 0x64000 <= a).
Proof.
  intros MR RF. pose proof MR as (WF & _). (first [ pose proof (WF) as dR_1; dand3 dR_1 as _ WR _ | pose proof WF as (_ & WR & _) ]).
  destruct RF as [R1|[R2|[R3|[R4|[(ak & ar & Hak & Rak)|[(b & gh & Hb & Rb)|[(q & rq & v & Hq & Kq & Rq & Cq)|[R8|R9]]]]]]]];
    (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK, LIBC, NEED_LOCKS, PAGE_SIZE_A, GOT_SSP, SSP_GUARD in *.
  - lia. - lia. - lia. - lia.
  - (first [ pose proof ((area_conc st ak ar WF Hak)) as dR_2; dex1 dR_2 as ra; dand9 dR_2 as Hra Ca Sa0 Sa1 _ NK RB0 RBAL RBC | pose proof ((area_conc st ak ar WF Hak)) as dR_2; dand10 dR_2 as ra Hra Ca Sa0 Sa1 _ NK RB0 RBAL RBC | destruct (area_conc st ak ar WF Hak) as (ra & Hra & Ca & Sa0 & Sa1 & _ & NK & RB0 & RBAL & RBC) ]).
    (first [ pose proof ((WR _ _ Hra)) as dR_3; dand5 dR_3 as _ _ _ _ RFa | destruct (WR _ _ Hra) as (_ & _ & _ & _ & RFa) ]). pose proof (reserved_disjoint1 _ _ RFa) as D. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    pose proof (round_up_pg_ge (r_len ra)). lia.
  - (first [ pose proof ((group_conc st b gh WF Hb)) as dR_4; dex1 dR_4 as rb; dand8 dR_4 as Hrb Cb Kb Sb0 Sb1 _ RB0 RBC | pose proof ((group_conc st b gh WF Hb)) as dR_4; dand9 dR_4 as rb Hrb Cb Kb Sb0 Sb1 _ RB0 RBC | destruct (group_conc st b gh WF Hb) as (rb & Hrb & Cb & Kb & Sb0 & Sb1 & _ & RB0 & RBC) ]).
    (first [ pose proof ((WR _ _ Hrb)) as dR_5; dand5 dR_5 as _ _ _ _ RFb | destruct (WR _ _ Hrb) as (_ & _ & _ & _ & RFb) ]). pose proof (reserved_disjoint1 _ _ RFb) as D. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
    pose proof (round_up_pg_ge (r_len rb)). lia.
  - (first [ pose proof ((WR _ _ Hq)) as dR_6; dand5 dR_6 as _ _ _ RC RFq | destruct (WR _ _ Hq) as (_ & _ & _ & RC & RFq) ]). pose proof (reserved_disjoint1 _ _ RFq) as D. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - lia. - lia.
Qed.

(* [comment removed for export] *)
Lemma wrapper_munch_keeps st m m' (spv lo : Z) :
  mrep st m -> munch [(spv - 80, spv); (0x42454, 0x42454 + 4)] m m' -> wmono rsegs m m' -> alloc_ceiling <= spv - 80 ->
  mrep st m'.
Proof.
  intros MR MU WM HS. eapply (mrep_transport_unowned st m m' _ MR MU WM).
  intros lo' hi' a [E|[E|[]]] Ha RF; inversion E; subst; destruct (rrepfoot_where2 st m a MR RF) as [A B]; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK, LIBC, GOT_SSP, SSP_GUARD in *; lia.
Qed.

Lemma pres_except_of_munch_nw C W m m' :
  munch W m m' -> (forall a, 0 <= a < 2^64 -> ~ C a -> outside W a) -> pres_except C m m'.
Proof.
  intros MU HW a Ha Hc. assert (E : m' (wa a) = m (wa a)) by (apply MU; rewrite wa_unsigned by lia; apply HW; assumption).
  split; [exact E|]. unfold wview. rewrite E. auto.
Qed.

(* [comment removed for export] *)
Lemma fp_below_ceiling K st3 stx m lo spv a :
  mrep st3 m -> spv <= a -> alloc_ceiling <= a -> ~ (alloc_fp K st3 lo spv a \/ fresh_addr stx a).
Proof.
  intros MR H1 H2 [[X|[X|[X|(q & rq & Hq & _ & Xa)]]]|[X _]]; try lia.
  - rewrite unsigned_lit in X by lia. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX in *. lia.
  - pose proof MR as (WF & _). (first [ pose proof (WF) as dR_7; dand3 dR_7 as _ WR _ | pose proof WF as (_ & WR & _) ]). (first [ pose proof ((WR q rq Hq)) as dR_8; dand5 dR_8 as _ _ _ RC _ | destruct (WR q rq Hq) as (_ & _ & _ & RC & _) ]). lia.
Qed.

Lemma big_stride n rid : 0 <= n < 2^32 -> get_stride (big_meta rid n) = round_up_pg (n + IB + UNIT) - 16.
Proof. intros Hn. rewrite bf_stride, big_ml_eq, round_up_pg_4115 by lia. reflexivity. Qed.

Lemma rregion_facts_hi : forall st m rid r,
  mrep st m -> (s_regions st) !! rid = Some r ->
  r_base r + round_up_pg (r_len r) <= 0x31000 \/ 0x64000 <= r_base r.   (* [comment removed for export] *)
Proof.
  intros st m rid r (WF & _) Hr. (first [ pose proof (WF) as dR_9; dand3 dR_9 as _ WR _ | pose proof WF as (_ & WR & _) ]).
  (first [ pose proof ((WR rid r Hr)) as dR_10; dand5 dR_10 as RB0 RBAL RL0 RBC RFr | destruct (WR rid r Hr) as (RB0 & RBAL & RL0 & RBC & RFr) ]).
  (first [ pose proof ((reserved_disjoint _ _ RFr)) as dR_11; dand4 dR_11 as _ _ _ D | destruct (reserved_disjoint _ _ RFr) as (_ & _ & _ & D) ]). exact D.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AMP_BIG (am_pre : mstate -> Prop) : Prop :=
  forall st LB t xa n, AREACH st LB -> MMAP_THRESHOLD <= n < 2^32 ->
  mmap_answer_ok (live_ranges (set_tick t st)) (n + IB + UNIT) xa = true -> is_err xa = false ->
  am_pre (step_seq (fst (new_region RKGroup xa (n + IB + UNIT) (set_tick t st)))).


Lemma ramp_big : AMP_BIG (am_pre_g p0_reserved).
Proof.
  intros st LB t xa n AR NR VOK ISE. unfold am_pre_g. apply AMpre_big_call; [exact (Mall8ro.areach_ampre_proof _ _ AR)|].
  unfold IB, UNIT, MMAP_THRESHOLD in *. lia.
Qed.

End CEIL3.

Section BIG.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_BIG am_pre.

#[using="AMP AM am_pre"] Lemma big_spec : big_stmt.
Proof.
  pose proof AMP as AMPB. unfold AMP_BIG in AMPB.
  intros o m0 st LB s ra sp gp tp s5 s6 s7 s8 s9 s10 s11 s0v s1v s2v s3v s4v F fc n lo t m1 errv t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2r s3r s4r t3 t4 t5 t6 ra' st1.
  intros AR MF MR0 TP CLO LO NR BL MR1 TK1 UA1 MI1 ST1 FR1 ERR1 AUX1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  unfold AM_STACK in LO. unfold MMAP_THRESHOLD in NR.
  rewrite (malloc_core_big_eq st1 n) by (unfold MMAP_THRESHOLD; lia).
  (* [comment removed for export] *)
  iprefixT. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). subst tp. unfold PTP in ERR1. rewrite unsigned_lit in ERR1 by lia.
  unfold MLOCK.
  step. step. step. step. step. step. step. step. step.
  apply evt_done.
  set (sp' := Z_to_bv 64 (bv_unsigned sp + -48)).
  assert (SP' : bv_unsigned sp' = bv_unsigned sp + -48) by (subst sp'; apply unsigned_lit; lia).
  eapply implT_mmap_rw.
  { eapply (rmmap_anon_spec false) with (lo := lo) (avoid := []);
    [ rewrite SP'; exact ST1 | unfold PTP; rewrite unsigned_lit by lia; exact ERR1 | exact MI1 | reflexivity | unfold IB, UNIT; f_equal; lia
    | reflexivity | reflexivity | reflexivity | reflexivity | unfold IB, UNIT; lia | rewrite SP'; lia | (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
    | rewrite SP'; unfold PTP; rewrite unsigned_lit by lia; lia | unfold PTP; rewrite unsigned_lit by lia; lia ]. }
  intros ans ms' PO.
  assert (FRAME : forall m2, munch [(bv_unsigned sp' - 80, bv_unsigned sp'); (271608 + -164, 271608 + -164 + 4)] m1 m2 -> wmono rsegs m1 m2 ->
            rw_cells rsegs m2 (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra] /\ mrep st1 m2 /\ auxv_okd (c_init_done (ctx st)) m2 (bv_unsigned sp)
            /\ pres_except (malloc_fp st st1 lo (bv_unsigned sp)) m0 m2 /\ unk_agree st1 o m2).
  { intros m2 MU WM. rewrite SP' in MU. split; [|split; [|split; [|split]]].
    - eapply rw_cells_transport; [exact FR1| exact MU| exact WM| cbn; lia].
    - eapply (wrapper_munch_keeps st1 m1 m2 (bv_unsigned sp + -48) lo MR1); [| exact WM| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia].
      eapply munch_weaken; [|exact MU]. intros y; cbn; lia.
    - eapply auxv_okd_frame; [exact AUX1| exact MU| exact WM|]. unfold AUXV_CELL.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor.
    - eapply pres_except_trans; [exact PE1|]. eapply pres_except_of_munch; [exact MU| exact WM|].
      intros a Ha NC. cbn. split; [|split; [|exact I]]; intros HX; apply NC; left; [left; lia| right; left]. rewrite unsigned_lit by lia. lia.
    - eapply unk_agree_munch; [exact UA1| exact MU| |].
      + intros rid r Hr Hk. (first [ pose proof ((rregion_facts st1 m1 rid r MR1 Hr)) as dR_12; dand4 dR_12 as R1 _ R2 _ | pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _) ]). pose proof (rregion_facts_hi st1 m1 rid r MR1 Hr) as R3. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). cbn. lia.
      + intros rid r Hr. (first [ pose proof ((rregion_facts st1 m1 rid r MR1 Hr)) as dR_13; dand4 dR_13 as R1 _ R2 _ | pose proof (rregion_facts st1 m1 rid r MR1 Hr) as (R1 & _ & R2 & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
  destruct ans as [e|xa].
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (first [ dex15 PO as v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 m2; dand7 PO as -> MU2 WM2 MI2 ST2 ERR2 He | dand22 PO as v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 m2 -> MU2 WM2 MI2 ST2 ERR2 He | destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & He) ]).
    cbn [mmap_val]. destruct (mmap_answer_ok_err (live_ranges st1) (n + IB + UNIT) e He) as [-> ->]. cbn [negb].
    apply implT_ret.
    unfold PTP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
    (first [ pose proof ((FRAME m2 MU2 WM2)) as dR_15; dand5 dR_15 as FR2 MR2 AUX2 PE2 UA2 | destruct (FRAME m2 MU2 WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2) ]).
    replace (ret_pc (Z_to_bv 64 0x23d8c)) with (Z_to_bv 64 0x23d8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    eapply evt_cut. { eapply big_fail1_walk; [exact FR2| exact ST2| lia| lia]. }
    intros ms'' [-> ST3]. apply evt_done. cbn [coreQ].
    exists m2, (Z_to_bv 64 (F_mm4hw.mmap_fix_errno e)). do 14 eexists. split; [reflexivity|].
    split; [exact MR2|]. split; [exact TK1|]. split; [exact MI2|]. split; [exact ST3|].
    split; [unfold PTP; rewrite unsigned_lit by lia; exact ERR2|]. split; [exact AUX2|]. split; [exact PE2|].
    split; [apply mrel_same; reflexivity|]. split; [exact BL|]. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  - (* [comment removed for export] *)
    cbn [rmmap_anon_post] in PO.
    (first [ dex15 PO as v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 m2; dand7 PO as -> MU2 WM2 MI2 ST2 ERR2 AOK | dand22 PO as v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 v12 v13 m2 -> MU2 WM2 MI2 ST2 ERR2 AOK | destruct PO as (v0 & v1 & v2 & v3 & v4 & v5 & v6 & v7 & v8 & v9 & v10 & v11 & v12 & v13 & m2 & -> & MU2 & WM2 & MI2 & ST2 & ERR2 & AOK) ]).
    cbn [mmap_val].
    destruct (mmap_answer_ok (live_ranges st1) (n + IB + UNIT) xa) eqn:VOK.
    2:{ cbn [negb]. apply implT_undef. }
    cbn [negb].
    (first [ pose proof ((mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK)) as dR_17; dand5 dR_17 as X0 XA XC XRF ISE | destruct (mmap_answer_ok_addr (live_ranges st1) (n + IB + UNIT) xa ltac:(unfold IB, UNIT; lia) AOK VOK) as (X0 & XA & XC & XRF & ISE) ]). rewrite ISE.
    unfold PTP in MU2, ERR2. rewrite unsigned_lit in MU2 by lia. rewrite SP' in ST2. rewrite unsigned_lit in ERR2 by lia.
    (first [ pose proof ((FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2)) as dR_18; dand5 dR_18 as FR2 MR2 AUX2 PE2 UA2 | destruct (FRAME m2 ltac:(eapply munch_weaken; [|exact MU2]; intros y; cbn; lia) WM2) as (FR2 & MR2 & AUX2 & PE2 & UA2) ]).
    (* [comment removed for export] *)
    unfold new_region.
    set (rid := s_next_rid st1). set (st2 := set_next_rid (N.succ rid) (set_regions (<[rid:={| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}]> (s_regions st1)) st1)).
    assert (Est2 : st2 = fst (new_region RKGroup xa (n + IB + UNIT) st1)) by reflexivity.
    pose proof (mf_ptrs _ _ MF) as [PT0 FRESH0].
    assert (PT1 : ptrs_in (fun r => r <> rid) st1).
    { eapply ptrs_in_mono; [|exact PT0]. intros r Hr. cbn in Hr. subst rid. unfold st1. cbn. intros ->. lia. }
    destruct (FRESH0 rid ltac:(subst rid; unfold st1; cbn; lia)) as [FRr FRs].
    set (L := mmap_len (n + IB + UNIT)).
    assert (EL : L = round_up_pg (n + IB + UNIT)) by apply mmap_len_round_up.
    pose proof (round_up_pg_ge (n + IB + UNIT)) as LG. rewrite <- EL in LG, XC, XRF.
    unfold F_mm4hw.mmap_raw in ST2 |- *. cbn [negb] in ST2 |- *. fold L. fold L in ST2.
    assert (ELm : mmap_len (n + IB + UNIT) = L) by reflexivity. clearbody L. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). unfold IB, UNIT in LG.
    set (mz := apply_zeros m2 [(wa xa, Z_to_bv 64 L)]).
    assert (ZO : forall a, 0 <= a < 2^64 -> (a < xa \/ xa + L <= a) -> mz (wa a) = m2 (wa a)).
    { intros a Ha Ho. unfold mz. apply (zeros_outside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (ZI : forall a, xa <= a < xa + L -> mz (wa a) = Some (b8 0)).
    { intros a Ha. unfold mz. apply (zeros_inside m2 xa L); rewrite ?wa_unsigned by lia; lia. }
    assert (MRz : mrep st2 mz).
    { rewrite Est2. eapply (mrep_new_region (Clg:=Clg) (Rr:=Rr) st1 m2 mz xa (n + IB + UNIT) RKGroup MR2 PT1 FRs X0 XA ltac:(unfold IB, UNIT; lia));
        rewrite <- ?EL; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); exact XC| exact XRF| exact ZO| intros _; exact ZI]. }
    fold mz in ST2 |- *.
    (* [comment removed for export] *)
    pose proof MR1 as (WF1 & _). (first [ pose proof (WF1) as dR_19; dand3 dR_19 as RS1 WR1 _ | pose proof WF1 as (RS1 & WR1 & _) ]).
    assert (XI : xa + L <= 0x10000 \/ 0x64000 <= xa).
    { assert (RFimg : ranges_free p0_reserved xa L = true).
      { apply ranges_free_intro. intros b k HI. apply (ranges_free_In _ _ _ _ _ XRF). unfold live_ranges. apply in_or_app. left. rewrite RS1. exact HI. }
      apply (reserved_disjoint1 _ _ RFimg). lia. }
    assert (MIz : mem_inv rsegs mz).
    { unfold mz. apply (mem_inv_zeros rsegs m2 xa L); try lia; [exact MI2|]. intros w Hw. apply p0_ro_addr_false. lia. }
    assert (FRz : rw_cells rsegs mz (bv_unsigned sp + -48) [C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 ra]).
    { eapply rw_cells_agree; [exact FR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (TKz : ticks_ok st2) by (rewrite Est2; exact TK1).
    assert (UAz : unk_agree st2 o mz).
    { eapply (unk_agree_transfer st1 st2 o m2 mz UA2). intros q r Hq Hk.
      rewrite Est2 in Hq. destruct (nr_lookup_inv st1 xa (n + IB + UNIT) RKGroup q r Hq) as [[-> ->]|[NE Hq1]].
      - right. intros off h Ho Hc. exfalso. rewrite Est2 in Hc. rewrite (nr_shadow st1 xa (n + IB + UNIT) RKGroup) in Hc.
        unfold get_shadow in Hc. rewrite FRs in Hc. cbn [default from_option id] in Hc. rewrite cell_read_shadow0 in Hc. discriminate.
      - left. split; [exact Hq1|]. split; [rewrite Est2; apply nr_shadow|]. split; [intros off X; exact X|].
        intros off h Ho Hc NG. (first [ pose proof ((WR1 q r Hq1)) as dR_20; dand5 dR_20 as B0 _ _ BC _ | destruct (WR1 q r Hq1) as (B0 & _ & _ & BC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
        pose proof (nr_old_disjoint st1 xa (n + IB + UNIT) ltac:(rewrite <- EL; exact XRF) q r Hq1) as D.
        pose proof (lr_lo_group r Hk). rewrite <- EL in D. apply ZO; lia. }
    (* [comment removed for export] *)
    iprefixT.
    replace (ret_pc (Z_to_bv 64 0x23d8c)) with (Z_to_bv 64 0x23d8c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    pose proof (mf_ctx _ _ MF) as FC. (first [ dand6 FC as FC1 FC2 FC3 FC4 FC5 FC6 | destruct FC as (FC1 & FC2 & FC3 & FC4 & FC5 & FC6) ]).
    change (ctx (strip st)) with (ctx st) in FC1, FC2, FC3, FC4.
    eapply evt_cut.
    { eapply (big_seq_walk sp gp (Z_to_bv 64 271608)) with (st := st2) (lo := lo);
        [exact MRz| rewrite Est2; exact FC4| rewrite unsigned_lit by lia; lia| exact FRz| exact ST2| lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| exact MIz]. }
    (intros ms1; (first [ intro dR_47; dex3 dR_47 as wa0 wa1 m3; dand7 dR_47 as -> MU3 WM3 MI3 ST3 FR3 MR3 | intro dR_47; dand10 dR_47 as wa0 wa1 m3 -> MU3 WM3 MI3 ST3 FR3 MR3 | intros (wa0 & wa1 & m3 & -> & MU3 & WM3 & MI3 & ST3 & FR3 & MR3) ])).
    apply evt_done.
    (* [comment removed for export] *)
    assert (MUz : munch [(xa, xa + L)] m2 mz) by (apply munch_of_pointwise; [lia| lia| exact ZO]).
    assert (WMz : wmono rsegs m2 mz) by (intros w Hw; unfold mz; apply (wview_zeros_mono rsegs m2 xa L); try lia; exact Hw).
    assert (AUXz : auxv_okd (c_init_done (ctx st)) mz (bv_unsigned sp)).
    { eapply auxv_okd_frame; [exact AUX2| exact MUz| exact WMz|]. unfold AUXV_CELL. constructor; [cbn; lia| constructor]. }
    assert (AUX3 : auxv_okd (c_init_done (ctx st)) m3 (bv_unsigned sp)).
    { eapply auxv_okd_frame; [exact AUXz| exact MU3| exact WM3|]. unfold AUXV_CELL, CTX.
      constructor; [cbn; lia|]. constructor; [cbn; lia|]. constructor. }
    assert (ERRz : rw_cells rsegs mz (271608 + -164) [C4 errv]).
    { eapply rw_cells_agree; [exact ERR2|]. intros a Ha. cbn in Ha. apply ZO; lia. }
    assert (ERR3 : rw_cells rsegs m3 (271608 + -164) [C4 errv]).
    { eapply rw_cells_transport; [exact ERRz| exact MU3| exact WM3|]. unfold CTX. cbn. lia. }
    assert (Hconc2 : forall q, fst q <> rid -> conc st2 q = conc st1 q) by (intros q Hq; rewrite Est2; apply nr_conc; exact Hq).
    assert (BL2 : brk_link_ps (step_seq st2) s).
    { eapply (brk_link_ps_ext st1); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| | exact BL].
      intros rb ob Hb. transitivity (conc st2 (rb, ob)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      apply Hconc2. cbn. (first [ dand8 PT1 as _ _ _ _ _ _ P7 _ | destruct PT1 as (_ & _ & _ & _ & _ & _ & P7 & _) ]). rewrite Hb in P7. exact P7. }
    assert (TK2' : ticks_ok (step_seq st2)) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); exact TKz).
    eapply (AM (c_init_done (ctx st))).
    { apply (AMPB st LB t xa n AR); [unfold MMAP_THRESHOLD; lia| exact VOK| exact ISE]. }
    { exact MR3. }
    { exact TK2'. }
    { exact BL2. }
    { rewrite SP'. eapply auxv_okd_weaken; [exact AUX3| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. }
    { intros H0. rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); rewrite Est2; cbn; exact H0. }
    { rewrite SP'. exact ST3. }
    { (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia. }
    { rewrite SP'. unfold AM_STACK. lia. }
    { unfold PTP. rewrite unsigned_lit by lia. exact ERR3. }
    { exact MI3. }
    { reflexivity. }
    intros st3 mo s' ms' PO3 BL3.
    (first [ dex16 PO3 as u0 u1 u2 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 m4 errv4; dand12 PO3 as -> MI4 ST4 ERR4 AUX4 PE4 MR4 TK4 PSM PSF PSO REL | dand28 PO3 as u0 u1 u2 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 m4 errv4 -> MI4 ST4 ERR4 AUX4 PE4 MR4 TK4 PSM PSF PSO REL | destruct PO3 as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m4 & errv4 & -> & MI4 & ST4 & ERR4 & AUX4 & PE4 & MR4 & TK4 & PSM & PSF & PSO & REL) ]).
    rewrite SP' in ST4, AUX4, PE4. unfold PTP in ERR4. rewrite unsigned_lit in ERR4 by lia.
    replace (ret_pc (Z_to_bv 64 0x23e80)) with (Z_to_bv 64 0x23e80) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
    (* [comment removed for export] *)
    lazymatch type of FR3 with rw_cells _ _ _ ?cs => assert (FR4 : rw_cells rsegs m4 (bv_unsigned sp + -48) cs) end.
    { eapply pres_except_rw_cells; [exact PE4| exact FR3|]. intros a Ha. cbn in Ha. eapply (fp_below_ceiling _ st3 _ m4); [exact MR4| lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. }
    assert (RR2 : s_regions (step_seq st2) !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { rewrite step_seq_eq. destruct (c_seq (ctx st2) =? 255); (rewrite Est2; apply nr_lookup_new). }
    assert (RR3 : s_regions st3 !! rid = Some {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}).
    { (first [ pose proof ((amr_regions _ _ _ REL rid _ RR2)) as dR_24; dex1 dR_24 as r'; dand5 dR_24 as Hr' K' B' L' G' | pose proof ((amr_regions _ _ _ REL rid _ RR2)) as dR_24; dand6 dR_24 as r' Hr' K' B' L' G' | destruct (amr_regions _ _ _ REL rid _ RR2) as (r' & Hr' & K' & B' & L' & G') ]). rewrite Hr'. f_equal. apply G'. reflexivity. }
    assert (PT2 : ptrs_in (fun q => q <> rid) (step_seq st2)) by (apply ptrs_in_step_seq; rewrite Est2; apply ptrs_in_new_region; exact PT1).
    assert (PT3 : ptrs_in (fun q => q <> rid) st3).
    { apply (amr_ptrs _ _ _ REL); [|exact PT2]. intros q rq Hq Hk ->. rewrite RR3 in Hq. inversion Hq; subst. apply Hk. reflexivity. }
    (first [ pose proof (MR4) as dR_25; dand4 dR_25 as WF4 _ (ML4 & _) _ | pose proof MR4 as (WF4 & _ & (ML4 & _) & _) ]). (first [ pose proof (WF4) as dR_26; dand4 dR_26 as RS4 WR4 DJ4 _ | pose proof WF4 as (RS4 & WR4 & DJ4 & _) ]).
    assert (RS3 : s_reserved st3 = p0_reserved) by exact RS4.
    (* [comment removed for export] *)
    assert (PE14 : forall stF, s_reserved stF = s_reserved st ->
              (forall a, alloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> malloc_fp st stF lo (bv_unsigned sp) a) ->
              pres_except (malloc_fp st stF lo (bv_unsigned sp)) m1 m4).
    { intros stF RSF HFP.
      eapply pres_except_trans. { eapply pres_except_of_munch; [exact MU2| exact WM2|]. intros a Ha NC. cbn. split; [|exact I]. intros X; apply NC; left; left; lia. }
      eapply pres_except_trans. { eapply pres_except_of_munch; [exact MUz| exact WMz|]. intros a Ha NC. cbn. split; [|exact I]. intros X. apply NC.
        do 4 right. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      eapply pres_except_trans. { eapply pres_except_of_munch; [exact MU3| exact WM3|]. intros a Ha NC. cbn. unfold CTX in *.
        split; [|split; [|exact I]]; intros X; apply NC; left; [right; right; left; unfold CTX; lia| right; right; left; unfold CTX; lia]. }
      eapply pres_except_mono; [exact PE4|]. intros a [X|X]; [apply (HFP a X)|].
      do 4 right. eapply (fresh_addr_anti st (step_seq st2)); [| |exact X].
      { transitivity (s_reserved st2); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity| rewrite Est2; reflexivity]. }
      intros q rq Hq. exists rq. split; [|OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto; lia].
      transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
      rewrite Est2, nr_lookup_old; [exact Hq|]. intros ->. unfold st1 in Hq. cbn in Hq. fold rid in FRr. unfold st1 in FRr. cbn in FRr. rewrite FRr in Hq. discriminate. }
    destruct mo as [g|].
    + (* [comment removed for export] *)
      apply implT_ret.
      destruct (amr_result _ _ _ REL g eq_refl) as [G0 MSL].
      (first [ pose proof ((meta_chunk_facts st3 m4 g MR4 MSL)) as dR_27; dand7 dR_27 as _ Gpos GC GI1 GI2 GRG (ridg & rg & Hrg & Krg & GLg & GHg) | pose proof (meta_chunk_facts st3 m4 g MR4 MSL) as (_ & Gpos & GC & GI1 & GI2 & GRG & (ridg & rg & Hrg & Krg & GLg & GHg)) ]).
      set (G := conc st3 g) in *.
      assert (HG : bv_unsigned (pw st3 (Some g)) = G) by (unfold pw, oconc; fold G; apply wz_unsigned; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia).
      assert (GN3 : forall off, (s_groups st3) !! (rid, off) = None).
      { intros off. destruct ((s_groups st3) !! (rid, off)) as [gh|] eqn:E; [|reflexivity].
        (first [ dand10 PT3 as _ _ _ _ _ _ _ _ _ P10 | destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & P10) ]). destruct (P10 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (AN3 : forall off, (s_areas st3) !! (rid, off) = None).
      { intros off. destruct ((s_areas st3) !! (rid, off)) as [ar|] eqn:E; [|reflexivity].
        (first [ dand10 PT3 as _ _ _ _ _ _ _ _ P9 _ | destruct PT3 as (_ & _ & _ & _ & _ & _ & _ & _ & P9 & _) ]). destruct (P9 _ _ E) as [X _]. exfalso. apply X. reflexivity. }
      assert (SHN3 : (s_shadow st3) !! rid = None).
      { rewrite (amr_shadow _ _ _ REL). transitivity (s_shadow st2 !! rid); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. exact FRs. }
      assert (HC3 : c_mmap_counter (ctx st3) = c_mmap_counter (ctx st)).
      { rewrite (amr_counter _ _ _ REL). transitivity (c_mmap_counter (ctx st2)); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
        rewrite Est2. reflexivity. }
      eapply evt_cut.
      { eapply (big_succ_walk (Clg:=Clg) (Rr:=Rr) st3 m4 g rid xa n (c_mmap_counter (ctx st)) lo MR4 TK4 G0 MSL RR3 GN3 AN3 SHN3 HC3 FC1 ltac:(unfold MMAP_THRESHOLD; lia) ltac:((let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia) sp gp (Z_to_bv 64 271608));
          [exact HG| exact FR4| exact ST4| lia| exact MI4]. }
      (intros ms5; (first [ intro dR_48; dex3 dR_48 as a0' a1' m7; dand8 dR_48 as -> MU7 WM7 MI7 ST7 FR7 MR7 TK7 | intro dR_48; dand11 dR_48 as a0' a1' m7 -> MU7 WM7 MI7 ST7 FR7 MR7 TK7 | intros (a0' & a1' & m7 & -> & MU7 & WM7 & MI7 & ST7 & FR7 & MR7 & TK7) ])).
      apply evt_done. cbn [coreQ].
      set (stF := big_final st3 g rid n).
      rewrite (bf_counter st3 g rid n (c_mmap_counter (ctx st)) HC3).
      change (pw st3 (Some g)) with (pw stF (Some g)).
      exists (rid, 0), {| r_kind := RKGroup; r_base := xa; r_len := n + IB + UNIT |}, m7, errv4. do 17 eexists.
      split; [reflexivity|].
      assert (MRF : mrep stF m7) by (apply (mrep_big_final st3 g rid n _ G0 (GN3 0) HC3); exact MR7).
      split; [exact MRF|].
      split; [exact TK7|].
      assert (STRIDE : get_stride (big_meta rid n) = L - 16) by (rewrite big_stride by lia; rewrite <- EL; reflexivity).
      assert (NL : forall q rq, (s_regions st3) !! q = Some rq -> q <> rid -> xa + L <= lr_lo rq \/ r_base rq + round_up_pg (r_len rq) <= xa).
      { intros q rq Hq NE. destruct (DJ4 q rq rid _ Hq RR3 NE) as [D|D]; cbn [r_base r_len lr_lo r_kind] in D; rewrite <- ?EL in D; [|lia]. pose proof (lr_lo_ge rq). lia. }
      split.
      { (* [comment removed for export] *)
        assert (UA3 : unk_agree (step_seq st2) o m3).
        { eapply (unk_agree_transfer st2 (step_seq st2) o mz m3 UAz). intros q r Hq Hk. left.
          assert (Hq2 : s_regions st2 !! q = Some r) by (revert Hq; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); intros Hq; exact Hq).
          split; [exact Hq2|]. split; [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
          intros off h Ho Hc NG. pose proof MRz as (WFz & _). (first [ pose proof (WFz) as dR_30; dand3 dR_30 as _ WRz _ | pose proof WFz as (_ & WRz & _) ]).
          (first [ pose proof ((WRz q r Hq2)) as dR_31; dand5 dR_31 as B0 _ _ BC RFq | destruct (WRz q r Hq2) as (B0 & _ & _ & BC & RFq) ]). (first [ pose proof ((reserved_disjoint _ _ RFq)) as dR_32; dand4 dR_32 as _ _ _ D | pose proof (reserved_disjoint _ _ RFq) as (_ & _ & _ & D) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
          apply MU3. rewrite wa_unsigned by lia. cbn. unfold CTX. lia. }
        assert (UA4 : unk_agree st3 o m4).
        { eapply (unk_agree_transfer (step_seq st2) st3 o m3 m4 UA3). intros q r Hq Hk. left.
          assert (Hq2 : s_regions (step_seq st2) !! q = Some r).
          { destruct ((s_regions (step_seq st2)) !! q) as [r2|] eqn:E.
            - (first [ pose proof ((amr_regions _ _ _ REL q r2 E)) as dR_33; dex1 dR_33 as r'; dand5 dR_33 as Hr' K' _ _ G' | pose proof ((amr_regions _ _ _ REL q r2 E)) as dR_33; dand6 dR_33 as r' Hr' K' _ _ G' | destruct (amr_regions _ _ _ REL q r2 E) as (r' & Hr' & K' & _ & _ & G') ]). rewrite Hq in Hr'. inversion Hr'; subst r'. f_equal. symmetry. apply G'. rewrite <- K'. exact Hk.
            - exfalso. exact (amr_new _ _ _ REL q r Hq E Hk). }
          split; [exact Hq2|]. split; [unfold get_shadow; rewrite (amr_shadow _ _ _ REL); reflexivity|].
          split; [intros off X; eapply grp_hdr_cov_same; [|exact X]; exact (amr_groups _ _ _ REL)|].
          intros off h Ho Hc NG. (first [ pose proof ((WR4 q r Hq)) as dR_34; dand5 dR_34 as B0 _ _ BC RFq | destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
          refine (proj1 (PE4 (r_base r + off) ltac:(lia) _)).
          intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
          - lia.
          - rewrite unsigned_lit in X by lia. (first [ pose proof ((reserved_disjoint _ _ RFq)) as dR_35; dand4 dR_35 as _ _ _ D | pose proof (reserved_disjoint _ _ RFq) as (_ & _ & _ & D) ]). lia.
          - unfold CTX in X. (first [ pose proof ((reserved_disjoint _ _ RFq)) as dR_36; dand4 dR_36 as _ _ _ D | pose proof (reserved_disjoint _ _ RFq) as (_ & _ & _ & D) ]). lia.
          - assert (NE : q2 <> q) by (intros ->; rewrite Hq in Hq'; inversion Hq'; subst; apply Kq2; exact Hk).
            pose proof (lr_lo_group r Hk). destruct (DJ4 q2 rq2 q r Hq' Hq NE); lia.
          - pose proof (fresh_live_region (step_seq st2) (r_base r + off) q r X Hq2) as Y. pose proof (lr_lo_group r Hk). lia. }
        eapply (unk_agree_transfer st3 stF o m4 m7 UA4). intros q r Hq Hk. change (s_regions stF) with (s_regions st3) in Hq.
        destruct (N.eq_dec q rid) as [->|NE].
        - right. rewrite RR3 in Hq. inversion Hq; subst r. cbn [r_len]. intros off h Ho Hc.
          change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid) in Hc.
          rewrite cell_read_hh0 in Hc by (exact SHN3 || lia). destruct (off <? 12) eqn:T; [|discriminate]. apply Z.ltb_lt in T.
          exists (rid, 0), (mkGhdr (Some g) 0). split; [|cbn; lia]. unfold stF. rewrite (bf_groups st3 g rid n (GN3 0)). apply lookup_insert_eq.
        - left. split; [exact Hq|]. split; [apply bf_shadow_other; exact NE|].
          split. { (intros off; (first [ intro dR_49; dex2 dR_49 as b gh; dand3 dR_49 as Hb Hf Ho | intro dR_49; dand5 dR_49 as b gh Hb Hf Ho | intros (b & gh & Hb & Hf & Ho) ])). exists b, gh. split; [|auto]. unfold stF. rewrite (bf_groups st3 g rid n (GN3 0)).
                   rewrite lookup_insert_ne; [exact Hb|]. intros <-. cbn in Hf. congruence. }
          intros off h Ho Hc NG. (first [ pose proof ((WR4 q r Hq)) as dR_37; dand5 dR_37 as B0 _ _ BC RFq | destruct (WR4 q r Hq) as (B0 & _ & _ & BC & RFq) ]). (first [ pose proof ((reserved_disjoint _ _ RFq)) as dR_38; dand4 dR_38 as _ _ _ D | pose proof (reserved_disjoint _ _ RFq) as (_ & _ & _ & D) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
          pose proof (NL q r Hq NE). pose proof (lr_lo_group r Hk). pose proof (GRG q r Hq Hk).
          apply MU7; rewrite wa_unsigned by lia; cbn; unfold CTX; lia. }
      split; [exact MI7|]. split; [exact ST7|]. split; [exact FR7|].
      assert (ERR8 : rw_cells rsegs m7 (271608 + -164) [C4 errv4]).
      { eapply rw_cells_transport; [exact ERR4| exact MU7| exact WM7|]. cbn. unfold CTX. lia. }
      split; [unfold PTP; rewrite unsigned_lit by lia; exact ERR8|].
      assert (HFPF : forall a, alloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> malloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [exact Hq| split; [exact Kq| exact Xa]]. }
      assert (PE18 : pres_except (malloc_fp st stF lo (bv_unsigned sp)) m1 m7).
      { eapply pres_except_trans. { apply (PE14 stF); [change (s_reserved stF) with (s_reserved st3); rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply pres_except_trans.
        { eapply pres_except_of_munch; [exact MU7| exact WM7|]. intros a Ha NC. cbn. split; [|split; [|split; [|exact I]]]; intros X; apply NC.
          - left. right; right; right. exists ridg, rg. split; [exact Hrg|]. split; [exact Krg|]. lia.
          - do 4 right. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia].
          - left. right; right; left. unfold CTX in *. lia. }
        apply pres_except_refl. }
      split. { eapply (auxv_okd_malloc_fp st stF lo (bv_unsigned sp) m0 m7 m1 m7); [exact MR0| exact MRF| exact AUX1| exact PE18| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, nr_lookup_old by exact NE. exact Hq. }
          (first [ pose proof ((amr_regions _ _ _ REL q rq Hq2)) as dR_39; dex1 dR_39 as r'; dand5 dR_39 as Hr' K' B' L' _ | pose proof ((amr_regions _ _ _ REL q rq Hq2)) as dR_39; dand6 dR_39 as r' Hr' K' B' L' _ | destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _) ]).
          exists r'. split; [|OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto]. exact Hr'.
        - change (s_next_rid stF) with (s_next_rid st3). pose proof (amr_next_rid _ _ _ REL) as NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - change (s_reserved stF) with (s_reserved st3). rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply pres_except_trans; [| exact PE18]. eapply pres_except_mono; [exact PE1|]. intros a Ha.
               eapply malloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      rewrite (bf_meta st3 g rid n G0). rewrite STRIDE. cbn [fst snd r_base r_len].
      split. { intros a Ha. do 4 right. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      split. { unfold u32. Z.div_mod_to_equations. lia. }
      assert (ML1 : 32 <= big_ml n < 2^40) by (rewrite big_ml_eq by lia; Z.div_mod_to_equations; lia).
      pose proof (round_up_pg_4115 n ltac:(lia)) as RU. rewrite <- EL in RU.
      assert (LUB : L <= n + 4115) by (rewrite RU; Z.div_mod_to_equations; lia).
      rewrite <- big_ml_eq in RU by lia.
      split.
      { (* [comment removed for export] *) constructor; rewrite ?(bf_meta st3 g rid n G0), ?STRIDE; cbn [m_mem m_last_idx m_avail m_freed m_freeable m_maplen m_sizeclass big_meta fst snd r_kind r_len].
        - reflexivity.
        - exact RR3.
        - reflexivity.
        - lia.
        - reflexivity.
        - lia.
        - lia.
        - rewrite <- EL. lia.
        - lia.
        - rewrite RU. Z.div_mod_to_equations. lia.
        - lia.
        - lia.
        - lia.
        - intros b' gh Hb' Hf. unfold stF in Hb'. rewrite (bf_groups st3 g rid n (GN3 0)) in Hb'.
          destruct (decide (b' = (rid, 0))) as [->|NEb]; [cbn; lia|].
          rewrite lookup_insert_ne in Hb' by congruence. destruct b' as [b1 b2]. cbn in Hf. subst b1. rewrite GN3 in Hb'. discriminate.
        - change (get_shadow stF rid) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
          rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + 16 + (L - 16) * 0 - 4 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        - intros off Ho Hfit. Z.div_mod_to_equations. lia.
        - unfold stF. rewrite bf_slots. replace (0 + 16 + (L - 16) * 0) with 16 by lia. apply lookup_insert_eq.
        - exact MSL.
        - lia.
        - lia.
        - lia.
        - lia.
        - right. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia. }
      split. { intros _. unfold RF_egfy.rdv. change (get_shadow stF (fst (rid, 0))) with (get_shadow (hdr_havoc (rid, 0) (put_meta g (big_metaA rid) st3)) rid).
               cbn [fst snd]. rewrite cell_read_hh0; [| exact SHN3| lia]. replace (0 + (16 + (L - 16) * 0) + -3 <? 12) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      split. { left. unfold MMAP_THRESHOLD in *. lia. }
      split; [exact MRELF|].
      split. { eapply (brk_link_ps_ext st3); [reflexivity| intros; reflexivity| exact BL3]. }
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
    + (* [comment removed for export] *)
      cbn [pw oconc].
      iprefixT.
      eapply evt_cut.
      { apply big_fail2a_walk. exact ML4. }
      intros ms2 ->. apply evt_done.
      eapply implT_munmap.
      { eapply (rmunmap_spec) with (A := xa) (L := n + IB + UNIT) (lo := lo);
          [ rewrite unsigned_lit by lia; exact ST4 | rewrite unsigned_lit by lia; exact ERR4 | exact MI4 | reflexivity | unfold IB, UNIT; f_equal; lia
          | lia | rewrite ELm; lia | unfold IB, UNIT; lia | rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; rewrite unsigned_lit by lia; lia | rewrite ELm; left; (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia
          | rewrite ELm, unsigned_lit by lia; lia | rewrite unsigned_lit by lia; lia ]. }
      intros ans2 ms3 PM. unfold rmunmap_post in PM.
      (first [ dex15 PM as z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m6; dand7 PM as -> MU6 WM6 MI6 ST6 ERR6 He6 | dand22 PM as z0 z1 z2 z3 z4 z5 z6 z7 z8 z9 z10 z11 z12 z13 m6 -> MU6 WM6 MI6 ST6 ERR6 He6 | destruct PM as (z0 & z1 & z2 & z3 & z4 & z5 & z6 & z7 & z8 & z9 & z10 & z11 & z12 & z13 & m6 & -> & MU6 & WM6 & MI6 & ST6 & ERR6 & He6) ]).
      rewrite (munmap_answer_ok_range ans2 He6). apply implT_ret.
      rewrite ELm in MU6. rewrite !unsigned_lit in MU6 by lia. rewrite unsigned_lit in ST6 by lia. rewrite unsigned_lit in ERR6 by lia.
      replace (ret_pc (Z_to_bv 64 0x23f58)) with (Z_to_bv 64 0x23f58) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
      lazymatch type of FR4 with rw_cells _ _ _ ?cs => assert (FR6 : rw_cells rsegs m6 (bv_unsigned sp + -48) cs) end.
      { eapply rw_cells_agree; [exact FR4|]. intros a Ha. cbn in Ha. apply MU6. rewrite wa_unsigned by lia. cbn. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia. }
      eapply evt_cut. { eapply big_fail2b_walk; [exact FR6| exact ST6| lia| lia]. }
      intros ms4 [-> ST7]. apply evt_done. cbn [coreQ].
      set (stF := drop_region rid st3).
      assert (MRF : mrep stF m6).
      { eapply (mrep_drop_region st3 m4 m6 rid _ MR4 RR3 PT3). intros a Ha Hout Hin. cbn [r_base r_len lr_lo r_kind] in Hout.
        rewrite <- EL in Hout.
        assert (A1 : a < alloc_ceiling /\ (a + 1 <= 271608 + -164 \/ 271608 + -164 + 4 <= a) /\ (a < xa \/ xa + L <= a)).
        { destruct Hin as [X|[X|[X|[X|(q & rq & Hq & Xa)]]]];
            [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold MLOCK in *; lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold LIBC in *; lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold GOT_SSP in *; lia| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold SSP_GUARD in *; lia|].
          (first [ pose proof ((WR4 q rq Hq)) as dR_41; dand5 dR_41 as _ _ _ RC RFq | destruct (WR4 q rq Hq) as (_ & _ & _ & RC & RFq) ]). (first [ pose proof ((reserved_disjoint _ _ RFq)) as dR_42; dand4 dR_42 as _ _ _ D | pose proof (reserved_disjoint _ _ RFq) as (_ & _ & _ & D) ]). pose proof (lr_lo_ge rq).
          split; [lia|]. split; [lia|].
          destruct (N.eq_dec q rid) as [->|NE]; [rewrite RR3 in Hq; inversion Hq; subst; cbn [lr_lo r_kind r_base r_len] in Xa; lia|].
          destruct (DJ4 q rq rid _ Hq RR3 NE) as [D2|D2]; cbn [r_base r_len lr_lo r_kind] in D2; rewrite <- ?EL in D2; lia. }
        (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
        apply MU6; rewrite wa_unsigned by lia; cbn; lia. }
      assert (HFPF : forall a, alloc_fp (fun k => k <> RKGroup) st3 lo (bv_unsigned sp + -48) a -> malloc_fp st stF lo (bv_unsigned sp) a).
      { intros a [X|[X|[X|(q & rq & Hq & Kq & Xa)]]]; left; [left; lia| right; left; exact X| right; right; left; exact X|].
        right; right; right. exists q, rq. split; [|split; [exact Kq|exact Xa]].
        unfold stF. rewrite dr_lookup_old; [exact Hq|]. intros ->. rewrite RR3 in Hq. inversion Hq; subst. apply Kq. reflexivity. }
      assert (PE16 : pres_except (malloc_fp st stF lo (bv_unsigned sp)) m1 m6).
      { eapply pres_except_trans. { apply (PE14 stF); [unfold stF, drop_region; cbn [s_reserved set_shadow set_regions]; rewrite RS3; symmetry; exact (mf_reserved _ _ MF)| exact HFPF]. }
        eapply pres_except_of_munch_nw; [exact MU6|]. intros a Ha NC. cbn.
        split; [|split; [|split; [|exact I]]]; intros X; apply NC; [left; left; lia| left; right; left; rewrite unsigned_lit by lia; lia|].
        do 4 right. split; [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia|]. eapply (ranges_free_sub _ xa L); [exact XRF| lia| lia| lia]. }
      exists m6, (F_mm4hw.rg_errno ans2 errv4). do 14 eexists. split; [reflexivity|].
      split; [exact MRF|]. split; [apply ticks_ok_drop_region; exact TK4|]. split; [exact MI6|]. split; [exact ST7|].
      split; [unfold PTP; rewrite unsigned_lit by lia; exact ERR6|].
      split. { eapply (auxv_okd_malloc_fp st stF lo (bv_unsigned sp) m0 m6 m1 m6); [exact MR0| exact MRF| exact AUX1| exact PE16| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| lia]. }
      assert (MRELF : mrel st stF).
      { split.
        - intros q rq Hq.
          assert (NE : q <> rid). { intros ->. unfold st1 in FRr. cbn in FRr. fold rid in FRr. change (s_regions (set_tick t st)) with (s_regions st) in FRr. rewrite FRr in Hq. discriminate. }
          assert (Hq2 : s_regions (step_seq st2) !! q = Some rq).
          { transitivity (s_regions st2 !! q); [rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity|].
            rewrite Est2, nr_lookup_old by exact NE. exact Hq. }
          (first [ pose proof ((amr_regions _ _ _ REL q rq Hq2)) as dR_43; dex1 dR_43 as r'; dand5 dR_43 as Hr' K' B' L' _ | pose proof ((amr_regions _ _ _ REL q rq Hq2)) as dR_43; dand6 dR_43 as r' Hr' K' B' L' _ | destruct (amr_regions _ _ _ REL q rq Hq2) as (r' & Hr' & K' & B' & L' & _) ]).
          exists r'. split; [|OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto]. unfold stF. rewrite dr_lookup_old by exact NE. exact Hr'.
        - unfold stF, drop_region. cbn [s_next_rid set_shadow set_regions]. pose proof (amr_next_rid _ _ _ REL) as NX.
          change (s_next_rid (step_seq st2)) with (s_next_rid (step_seq st2)) in NX.
          assert (E2 : s_next_rid (step_seq st2) = N.succ rid) by (rewrite step_seq_eq; destruct (c_seq (ctx st2) =? 255); reflexivity).
          rewrite E2 in NX. subst rid. unfold st1 in NX. cbn in NX. change (s_next_rid st) with (s_next_rid st) in NX. lia.
        - unfold stF, drop_region. cbn [s_reserved set_shadow set_regions]. rewrite RS3. symmetry. exact (mf_reserved _ _ MF). }
      split. { eapply pres_except_trans; [| exact PE16]. eapply pres_except_mono; [exact PE1|]. intros a Ha.
               eapply malloc_fp_mono; [apply (mrel_regions _ _ MRELF)| exact Ha]. }
      split; [exact MRELF|].
      split.
      { eapply (brk_link_ps_ext st3); [reflexivity| | exact BL3]. intros rb ob Hb. unfold stF. apply dr_conc. cbn.
        (first [ dand8 PT3 as _ _ _ _ _ _ P7 _ | destruct PT3 as (_ & _ & _ & _ & _ & _ & P7 & _) ]). rewrite Hb in P7. exact P7. }
      OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
Qed.
End BIG.
End RF_m79e.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RF_m79e.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj Malluin ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.

Module RASl0ja.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y RF_mk75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RAlllfc RASlot_I Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep MRepAux Malllim.
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

Lemma med_cnt_range i : 0 <= i < 4 -> 20 <= med_cnt i <= 32 /\ med_cnt i mod 4 = 0.
Proof.
  intros Hi. assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; [change (med_cnt 0) with 28| change (med_cnt 1) with 24| change (med_cnt 2) with 20| change (med_cnt 3) with 32]; (split; [lia| reflexivity]).
Qed.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma small_cnt_range sc i : 0 <= sc < 9 -> 0 <= i < 3 -> 4 <= small_cnt sc i <= 31.
Proof.
  intros Hsc Hi.
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
  unfold small_cnt. rewrite !Nat2Z.id.
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [cbn [nth small_cnt_tab]; lia|]); lia |]). lia.
Qed.
Lemma halve_even_range F : forall cnt u, 1 <= cnt -> 1 <= halve_even F cnt u <= cnt.
Proof.
  induction F as [|F IH]; intros cnt u Hc; cbn [halve_even]; [lia|].
  destruct (Z.even cnt && (u <? 4 * cnt)) eqn:E; [|lia].
  apply andb_prop in E. destruct E as [E _]. rewrite even_of_land1 in E. apply Z.eqb_eq in E. rewrite land1_mod2 in E.
  rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) u ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.
Lemma halve_big_range F : forall cnt sz, 0 <= cnt -> 0 <= halve_big F cnt sz <= cnt.
Proof.
  induction F as [|F IH]; intros cnt sz Hc; cbn [halve_big]; [lia|].
  destruct (_ <=? _); [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  pose proof (IH (cnt / 2) sz ltac:(Z.div_mod_to_equations; lia)). Z.div_mod_to_equations. lia.
Qed.
Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof.
  split; [apply Z.land_nonneg; right; lia|].
  apply Z.ldiff_le; [lia|]. apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.land_spec, Z.bits_0.
  destruct (Z.testbit x n), (Z.testbit 3 n); reflexivity.
Qed.
Definition small_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes rsegs SMALL_CNT 27 with Some bs => bs | None => [] end).
Definition rmed_cnt_bytes : list byte :=
  Eval vm_compute in (match image_bytes rsegs MED_CNT 4 with Some bs => bs | None => [] end).

Lemma small_cnt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m SMALL_CNT [CB 27 small_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold SMALL_CNT; lia | unfold SMALL_CNT; cbn; lia]. Qed.
Lemma rmed_cnt_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m MED_CNT [CB 4 rmed_cnt_bytes].
Proof. intros m MI. apply (ro_cells_image rsegs m); [exact MI | vm_compute; reflexivity | unfold MED_CNT; lia | unfold MED_CNT; cbn; lia]. Qed.

Lemma small_cnt_read : forall m sc i, mem_inv rsegs m -> 0 <= sc < 9 -> 0 <= i < 3 ->
  ov_read_bytes rsegs m (wa (SMALL_CNT + 3 * sc + i)) 1 = Some [b8 (small_cnt sc i)].
Proof.
  intros m sc i MI Hsc Hi.
  destruct (small_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  replace (SMALL_CNT + 3 * sc + i) with (SMALL_CNT + (3 * sc + i)) by lia.
  rewrite (bytes_at_read rsegs m SMALL_CNT small_cnt_bytes (3 * sc + i) 1 B) by (cbn; lia).
  assert (Hs : exists n, sc = Z.of_nat n /\ (n < 9)%nat) by (exists (Z.to_nat sc); lia). destruct Hs as (n & -> & Hn).
  assert (Hi' : exists k, i = Z.of_nat k /\ (k < 3)%nat) by (exists (Z.to_nat i); lia). destruct Hi' as (k & -> & Hk).
  replace (Z.to_nat (3 * Z.of_nat n + Z.of_nat k)) with (3 * n + k)%nat by lia.
  unfold small_cnt. rewrite !Nat2Z.id.
  Ltac solve_bytes := vm_compute; f_equal; repeat first [ reflexivity | apply f_equal2; [apply bv_eq; reflexivity|] ].
  do 9 (destruct n as [|n]; [do 3 (destruct k as [|k]; [solve_bytes|]); lia |]). lia.
Qed.

Lemma rmed_cnt_read : forall m i, mem_inv rsegs m -> 0 <= i < 4 ->
  ov_read_bytes rsegs m (wa (MED_CNT + i)) 1 = Some [b8 (med_cnt i)].
Proof.
  intros m i MI Hi.
  destruct (rmed_cnt_ro m MI) as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite (bytes_at_read rsegs m MED_CNT rmed_cnt_bytes i 1 B) by (cbn; lia).
  assert (C : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
  destruct C as [->|[->|[->| ->]]]; (vm_compute; f_equal; f_equal; apply bv_eq; reflexivity).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section HALVE.

Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
Definition cnt_regs (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz usage) (wz 4096) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
#[using="SZ"] Lemma halve_big_walk : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  0 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a2' a3',
      ms' = MS (cnt_regs ra sp gp tp t0 t1 t2 s0 s1 a2' a3' a4 a5 a6 a7 s2 (wz (halve_big F cnt size)) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x24308) fc None m (seg_rom rsegs))
    (MS (cnt_regs ra sp gp tp t0 t1 t2 s0 s1 (wz cnt) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x242f4) fc None m (seg_rom rsegs)).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 MI; unfold cnt_regs.
  - cbn [halve_big]. change (2 ^ Z.of_nat 0) with 1 in CR.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia. replace (size * cnt) with 0 by lia.
    step. step. step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia; [exfalso; cbn in K; lia|].
    apply evt_done. do 2 eexists. replace cnt with 0 by lia. reflexivity.
  - cbn [halve_big]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia.
    assert (PR : 0 <= size * cnt <= 2^18 * 32) by nia.
    step. step. rewrite (wz_unsigned cnt), (wz_unsigned size) by lia.
    step. rewrite (unsigned_lit (size * cnt)) by lia.
    step. rewrite (wz_unsigned cnt) by lia.
    step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (rewrite Z.shiftr_div_pow2 by lia; Z.div_mod_to_equations; lia).
    + (* [comment removed for export] *)
      rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with true by (symmetry; apply Z.leb_le; unfold UNIT; Z.div_mod_to_equations; lia).
      rewrite (RF_m8yt.srliw_small cnt 1) by lia. change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
      apply IH; [|rewrite Z.shiftr_div_pow2 by lia; change (2^1) with 2; Z.div_mod_to_equations; lia| exact MI].
      rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2. Z.div_mod_to_equations. lia.
    + rewrite Z.shiftr_div_pow2 in K by lia.
      replace (65536 * UNIT <=? size * cnt) with false by (symmetry; apply Z.leb_gt; unfold UNIT; Z.div_mod_to_equations; lia).
      apply evt_done. do 2 eexists. reflexivity.
Qed.
End HALVE.
Lemma land2_half_parity cnt : 0 <= cnt -> Z.even (cnt / 2) = (Z.land cnt 2 =? 0).
Proof.
  intros H.
  assert (E : Z.land cnt 2 = (if Z.testbit cnt 1 then 2 else 0)).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec.
    destruct (Z.eq_dec n 1) as [->|NE].
    - change (Z.testbit 2 1) with true. rewrite andb_true_r. destruct (Z.testbit cnt 1); reflexivity.
    - replace (Z.testbit 2 n) with false by (symmetry; change 2 with (2^1); rewrite Z.pow2_bits_eqb by lia; apply Z.eqb_neq; lia).
      rewrite andb_false_r. destruct (Z.testbit cnt 1); [| rewrite Z.bits_0; reflexivity]. symmetry. change 2 with (2^1). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_neq. lia. }
  rewrite E. change 1 with (Z.succ 0) at 1. rewrite <- Z.div2_bits, Z.bit0_odd by lia.
  rewrite <- Z.negb_odd. destruct (Z.odd (cnt / 2)); reflexivity.
Qed.

Section HALVE2.

Variables (usage size : Z).
Hypothesis UR : 0 <= usage < 2^60.
Hypothesis SZ : 16 <= size < 2^18.

(* [comment removed for export] *)
#[using="UR"] Lemma rhalve_even_loop : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  2 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> Z.even cnt = true -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a3' a4',
      ms' = MS (cnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x242f4) fc None m (seg_rom rsegs))
    (MS (cnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x242cc) fc None m (seg_rom rsegs)).
Proof.
  induction F as [|F IH]; intros until m; intros CR C32 EV MI; unfold cnt_regs.
  - change (2 ^ Z.of_nat 0) with 1 in CR. exfalso. lia.
  - cbn [halve_even]. rewrite Nat2Z.inj_succ, Z.pow_succ_r in CR by lia. rewrite EV. cbn [andb].
    assert (EVm : cnt mod 2 = 0) by (rewrite even_of_land1 in EV; apply Z.eqb_eq in EV; rewrite <- land1_mod2; exact EV).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4. rewrite swrap32_small by lia.
    step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
    + (* [comment removed for export] *)
      replace (usage <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia).
      step. apply evt_done. do 2 eexists. reflexivity.
    + replace (usage <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      (* [comment removed for export] *)
      step. rewrite (wz_unsigned cnt) by lia. rewrite (RF_m8yt.srliw_small cnt 1) by lia.
      step. rewrite (wz_unsigned cnt) by lia. step.
      assert (HS : Z.shiftr cnt 1 = cnt / 2) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
      pose proof (land_upper cnt 2 ltac:(lia) ltac:(lia)) as L2.
      (* [comment removed for export] *)
      step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      * (* [comment removed for export] *)
        assert (EV2 : Z.even (Z.shiftr cnt 1) = true) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_eq; exact K2).
        assert (C2 : 2 <= Z.shiftr cnt 1 <= 16).
        { rewrite HS in EV2 |- *. destruct (Z.eq_dec (cnt / 2) 1) as [E1|]; [rewrite E1 in EV2; discriminate| Z.div_mod_to_equations; lia]. }
        change (Z_to_bv 64 (Z.shiftr cnt 1)) with (wz (Z.shiftr cnt 1)).
        apply IH; [rewrite HS in C2 |- *; Z.div_mod_to_equations; lia| lia| exact EV2| exact MI].
      * (* [comment removed for export] *)
        step.
        assert (OD : Z.even (Z.shiftr cnt 1) = false) by (rewrite HS, land2_half_parity by lia; apply Z.eqb_neq; exact K2).
        replace (halve_even F (Z.shiftr cnt 1) usage) with (Z.shiftr cnt 1) by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
        apply evt_done. do 2 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="UR"] Lemma halve_even_walk : forall (F : nat) (cnt : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  1 <= cnt < 2 ^ Z.of_nat F -> cnt <= 32 -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a3' a4',
      ms' = MS (cnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 (wz (halve_even F cnt usage)) a3' a4' a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x242f4) fc None m (seg_rom rsegs))
    (MS (cnt_regs usage size ra sp gp tp t0 t1 t2 s0 s1 a2 (wz cnt) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x242c4) fc None m (seg_rom rsegs)).
Proof.
  intros until m; intros CR C32 MI; unfold cnt_regs.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned cnt) by lia.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by (pose proof (land_upper cnt 1 ltac:(lia) ltac:(lia)); lia).
  - (* [comment removed for export] *)
    assert (OD : Z.even cnt = false) by (rewrite even_of_land1; apply Z.eqb_neq; exact K).
    replace (halve_even F cnt usage) with cnt by (destruct F; cbn [halve_even]; rewrite ?OD; reflexivity).
    step. step. apply evt_done. do 2 eexists. reflexivity.
  - assert (EV : Z.even cnt = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact K).
    destruct (Z.eq_dec cnt 1) as [->|NE1]; [discriminate|].
    apply rhalve_even_loop; [lia| lia| exact EV| exact MI].
Qed.
End HALVE2.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section COUNT.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m : mem) (sc : Z).
Hypothesis MR : mrep st m.
Hypothesis SC : 0 <= sc < 48.
Hypothesis UR : 0 <= usage st sc < 2^60.
Let u := usage st sc.
Let size := size_class sc * UNIT.
Let cnt0 := if sc <? 9 then small_cnt_pick sc u else halve_big 8%nat (halve_even 8%nat (med_cnt (Z.land sc 3)) u) size.

#[using="SC"] Lemma cnt0_range : 0 <= cnt0 <= 32.
Proof.
  unfold cnt0. destruct (Z.ltb_spec sc 9).
  - unfold small_cnt_pick. pose proof (small_cnt_range sc). destruct (negb _); [|destruct (negb _)]; (split; [|]; [pose proof (H0 0)| ]); try lia;
      first [pose proof (H0 0 ltac:(lia) ltac:(lia)); lia | pose proof (H0 1 ltac:(lia) ltac:(lia)); lia | pose proof (H0 2 ltac:(lia) ltac:(lia)); lia].
  - pose proof (land3_range sc). pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MC _].
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)).
    pose proof (halve_big_range 8 (halve_even 8 (med_cnt (Z.land sc 3)) u) size ltac:(lia)). lia.
Qed.

#[using="UR SC MR Rr Clg"] Lemma count_walk :
  forall (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5 s10 s11 t3 t4 t5 t6 x1 gmw rqw : word) Fr fc,
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists a2' a3' a4',
      ms' = MS (cnt_regs u size x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a2' a3' a4' a5 a6 a7 rqw (wz cnt0) (Z_to_bv 64 SSP_GUARD) s5 (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 0x24308) fc None m (seg_rom rsegs))
    (MS (mkR x1 sp gp tp t0 t1 t2 (Z_to_bv 64 sc) gmw a0 a1 a2 a3 a4 a5 a6 a7 rqw (Z_to_bv 64 (sc * 2)) (Z_to_bv 64 SSP_GUARD) s5 (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc))
             (wz (size_class sc)) (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x24268) fc None m (seg_rom rsegs)).
Proof.
  intros until fc. intros MI.
  pose proof (size_class_range sc SC) as SZR.
  pose proof MR as (_ & _ & (_ & _ & PGS & _) & _). unfold wz in PGS.
  pose proof cnt0_range as C0R.
  unfold cnt_regs, CTX, MLOCK, SSP_GUARD, SIZE_CLASSES, PAGE_SIZE_A, SMALL_CNT, MED_CNT in *.
  (* [comment removed for export] *)
  pose proof (mrep_usage_read st m sc (wa (403456 + 464 + 8 * sc)) MR SC eq_refl) as RDU. fold u in RDU.
  step. clear RDU.
  (* [comment removed for export] *)
  step. step. step. step. rewrite (wz_unsigned (size_class sc)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  fold UNIT. change (size_class sc * 16) with size. change (Z_to_bv 64 size) with (wz size). change (Z_to_bv 64 4096) with (wz 4096). change (Z_to_bv 64 u) with (wz u).
  (* [comment removed for export] *)
  step. if_cases K; unfold bv_lts in K; rewrite !signed_wz_small in K by lia.
  - (* [comment removed for export] *)
    apply Z.ltb_lt in K. unfold cnt0. replace (sc <? 9) with false by (symmetry; apply Z.ltb_ge; lia).
    pose proof (land3_range sc) as L3. pose proof (med_cnt_range (Z.land sc 3) ltac:(lia)) as [MCR _].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (rmed_cnt_read m (Z.land sc 3) MI ltac:(lia)) as RDM. unfold MED_CNT in RDM.
    step. clear RDM. rewrite zxb_b8 by lia.
    (* [comment removed for export] *)
    eapply evt_cut.
    { eapply (halve_even_walk u size UR 8%nat (med_cnt (Z.land sc 3))); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. intros ms' (a3' & a4' & ->). unfold cnt_regs.
    pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) u ltac:(lia)) as HER.
    eapply evt_mono.
    { eapply (halve_big_walk u size ltac:(unfold size, UNIT; lia) 8%nat); [change (2 ^ Z.of_nat 8) with 256; lia| lia| exact MI]. }
    cbv beta. intros ms' (a2'' & a3'' & ->). unfold cnt_regs. do 3 eexists. reflexivity.
  - (* [comment removed for export] *)
    assert (SC9 : sc < 9) by (destruct (Z.lt_ge_cases 8 sc) as [H|H]; [exfalso; apply Bool.not_true_iff_false in K; apply K; apply Z.ltb_lt; exact H| lia]).
    unfold cnt0. replace (sc <? 9) with true by (symmetry; apply Z.ltb_lt; lia). unfold small_cnt_pick.
    pose proof (small_cnt_range sc 0 ltac:(lia) ltac:(lia)) as R0. pose proof (small_cnt_range sc 1 ltac:(lia) ltac:(lia)) as R1. pose proof (small_cnt_range sc 2 ltac:(lia) ltac:(lia)) as R2.
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit (sc * 2)), ?(unsigned_lit sc) by lia. step. step. step.
    pose proof (small_cnt_read m sc 0 MI ltac:(lia) ltac:(lia)) as RD0. unfold SMALL_CNT in RD0.
    replace (wa (85256 + 3 * sc + 0)) with (Z_to_bv 64 (85256 + (sc * 2 + sc))) in RD0 by (unfold wa; f_equal; lia).
    step. clear RD0. rewrite zxb_b8 by lia.
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned (small_cnt sc 0)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K0; zify_cond K0; rewrite ?wz_unsigned, ?unsigned_lit in K0 by lia.
    { replace (u <? 4 * small_cnt sc 0) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
    replace (u <? 4 * small_cnt sc 0) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    (* [comment removed for export] *)
    pose proof (small_cnt_read m sc 1 MI ltac:(lia) ltac:(lia)) as RD1. unfold SMALL_CNT in RD1.
    replace (wa (85256 + 3 * sc + 1)) with (Z_to_bv 64 (85256 + (sc * 2 + sc) + 1)) in RD1 by (unfold wa; f_equal; lia).
    step. clear RD1. rewrite zxb_b8 by lia.
    step. rewrite (wz_unsigned (small_cnt sc 1)), Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    step. if_cases K1; zify_cond K1; rewrite ?wz_unsigned, ?unsigned_lit in K1 by lia.
    { replace (u <? 4 * small_cnt sc 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [negb]. apply evt_done. do 3 eexists. reflexivity. }
    replace (u <? 4 * small_cnt sc 1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb].
    (* [comment removed for export] *)
    pose proof (small_cnt_read m sc 2 MI ltac:(lia) ltac:(lia)) as RD2. unfold SMALL_CNT in RD2.
    replace (wa (85256 + 3 * sc + 2)) with (Z_to_bv 64 (85256 + (sc * 2 + sc) + 2)) in RD2 by (unfold wa; f_equal; lia).
    step. clear RD2. rewrite zxb_b8 by lia. step.
    apply evt_done. do 3 eexists. reflexivity.
Qed.
End COUNT.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section CNT2.

Variables (u size cnt0 : Z).
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis C0 : 0 <= cnt0 <= 32.
Let cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0.
Let big := PGSZ / 2 <? size * cnt1 + UNIT.

#[using="C0"] Lemma cnt1_range : 0 <= cnt1 <= 32.
Proof. unfold cnt1. destruct (_ && _); lia. Qed.
#[using="C0 SZ"] Lemma cnt2_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) Fr fc m,
  mem_inv rsegs m ->
  evt rsegs (fun ms' =>
      ms' = MS (cnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 (wz (size + 16)) (wz 2048) (wz (size * cnt1)) (wz (size * cnt1 + 16)) a6 a7 s2 (wz cnt1) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
              Fr (Z_to_bv 64 (if big then 0x24330 else 0x24374)) fc None m (seg_rom rsegs))
    (MS (cnt_regs u size ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 (wz cnt0) s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6)
        Fr (Z_to_bv 64 0x24308) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MI. unfold cnt_regs.
  assert (PR : 0 <= size * cnt0 <= 2^18 * 32) by nia.
  pose proof cnt1_range as C1R. fold cnt1 in C1R.
  assert (PR1 : 0 <= size * cnt1 <= 2^18 * 32) by nia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned size) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftr 4096 1) with 2048.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?wz_unsigned, ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    assert (E1 : cnt1 = cnt0) by (unfold cnt1; replace (cnt0 =? 1) with false by (symmetry; apply Z.eqb_neq; exact K); reflexivity).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned size), (wz_unsigned cnt0) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; rewrite E1; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; rewrite E1; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB, E1. apply evt_done. reflexivity.
  - (* [comment removed for export] *)
    step. rewrite ?unsigned_lit by lia. step. step.
    assert (E1 : cnt1 = (if 2048 <? size + 16 then 1 else 2)).
    { unfold cnt1. rewrite K. cbn [Z.eqb]. unfold UNIT, PGSZ. change (4096 / 2) with 2048.
      destruct (Z.ltb_spec 2048 (size + 16)); [replace (size * 1 + 16 <=? 2048) with false by (symmetry; apply Z.leb_gt; lia)| replace (size * 1 + 16 <=? 2048) with true by (symmetry; apply Z.leb_le; lia)]; reflexivity. }
    assert (EV : Z_to_bv 64 (bv_swrap 32 (2 - bv_unsigned (v_sltu (Z_to_bv 64 2048) (Z_to_bv 64 (size + 16))))) = wz cnt1).
    { rewrite E1. unfold v_sltu, c_ltu, bv_ltu. rewrite !unsigned_lit by lia.
      destruct (Z.ltb_spec 2048 (size + 16)); rewrite unsigned_lit by lia; reflexivity. }
    rewrite EV. clear EV.
    assert (C1R' : 1 <= cnt1 <= 2) by (rewrite E1; destruct (2048 <? size + 16); lia).
    (* [comment removed for export] *)
    step. rewrite (wz_unsigned size), (wz_unsigned cnt1) by lia. step. rewrite ?unsigned_lit by lia.
    step. if_cases K3; zify_cond K3; rewrite ?wz_unsigned, ?unsigned_lit in K3 by lia.
    + assert (EB : big = false) by (unfold big; apply Z.ltb_ge; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
    + assert (EB : big = true) by (unfold big; apply Z.ltb_lt; unfold UNIT, PGSZ; cbn; lia).
      rewrite EB. apply evt_done. reflexivity.
Qed.
End CNT2.
End RASl0ja.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.

Module RASlanm.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z RF_muly.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_muly.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RAlllfc RASlot_I Malluin RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlh1b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep.

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
Lemma signed_lit_small z : -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros Hz. rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^64).
  destruct (Z.ltb_spec (z mod 2^64) (2^63)); Z.div_mod_to_equations; lia.
Qed.
(* [comment removed for export] *)

Section SEQ.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (sc : Z).
Hypothesis SC : 0 <= sc < 48.

Definition seqW : list (Z * Z) := [(CTX + 848, CTX + 913)]%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="SC"] Lemma bounce_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
  mrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x245e4) fc None m' (seg_rom rsegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch seqW m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ mrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24330) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MR SEQ BR USR MI.
  pose proof (munch_refl seqW m) as MU. pose proof (wmono_refl rsegs m) as WM. unfold seqW in MU.
  unfold CTX, MLOCK in *.
  (* [comment removed for export] *)
  assert (EXIT : forall stX mX (t0v t1v a3v a5v a6v a7v : word),
    mrep stX mX -> stX = account_bounce sc st -> mem_inv rsegs mX -> a3v = Z_to_bv 64 (Z.b2z (is_bouncing sc st)) ->
    munch [(403456 + 848, 403456 + 913)]%Z m mX -> wmono rsegs m mX ->
    evt rsegs (fun ms' => exists (t0' t1' a3' a5' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 a5' (wz (c_seq (ctx st))) a7' s2 s3 s4 s5 (Z_to_bv 64 403448) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x245e4) fc None m' (seg_rom rsegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch [(403456 + 848, 403456 + 913)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ mrep (account_bounce sc st) m')
    (MS (mkR ra sp gp tp t0v t1v t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3v a4 a5v a6v a7v s2 s3 s4 s5 (Z_to_bv 64 403448) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x245e0) fc None mX (seg_rom rsegs))).
  { intros stX mX t0v t1v a3v a5v a6v a7v MRX EX MIX -> MUX WMX.
    pose proof (mrep_seq_read stX mX (wa (403456 + 912)) MRX eq_refl) as RDS.
    replace (wa (403456 + 912)) with (Z_to_bv 64 (403448 + 920)) in RDS by (unfold wa; f_equal; lia).
    assert (SQX : c_seq (ctx stX) = c_seq (ctx st)).
    { rewrite EX. unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
      destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
    rewrite SQX in RDS.
    step. rewrite ?zxb_b8 by lia. clear RDS.
    apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MUX|]. split; [exact WMX|]. split; [exact MIX| rewrite <- EX; exact MRX]. }
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step.
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  { (* [comment removed for export] *)
    assert (HO : sc_in_seq_range sc = false).
    { unfold sc_in_seq_range. destruct (Z.lt_ge_cases sc 7) as [L7|G7].
      - replace (7 <=? sc) with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      - rewrite swrap32_small in K by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite ?Z.land_ones, ?Z.mod_small in K by lia.
        replace (sc <? 39) with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
    step. step.
    eapply EXIT; [exact MR| | exact MI| | exact MU| exact WM].
    - unfold account_bounce. rewrite HO. reflexivity.
    - unfold is_bouncing. rewrite HO. reflexivity. }
  rewrite swrap32_small in K |- * by lia. change 18446744073709551615 with (Z.ones 64) in K. rewrite ?Z.land_ones in K by lia.
  destruct (Z.lt_ge_cases sc 7) as [L7|G7].
  { exfalso. clear -K L7 SC. Z.div_mod_to_equations. lia. }
  rewrite Z.mod_small in K by lia.
  assert (IN : sc_in_seq_range sc = true) by (unfold sc_in_seq_range; rewrite (proj2 (Z.leb_le 7 sc)), (proj2 (Z.ltb_lt sc 39)) by lia; reflexivity).
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (sc + -7)) by lia.
  pose proof (mrep_bounces_read (Clg:=Clg) (Rr:=Rr) st m (sc - 7) (wa (403456 + 880 + (sc - 7))) MR ltac:(lia) eq_refl) as RDB.
  replace (wa (403456 + 880 + (sc - 7))) with (Z_to_bv 64 (403448 + (sc + -7) + 888)) in RDB by (unfold wa; f_equal; lia).
  pose proof (BR (sc - 7)) as BR7. pose proof (USR (sc - 7)) as USR7.
  step. rewrite ?zxb_b8 by lia. clear RDB.
  (first [ pose proof (MR) as dR_1; dand3 dR_1 as _ (_ & _ & _ & US & _) _ | pose proof MR as (_ & (_ & _ & _ & US & _) & _) ]).
  pose proof (u8arr_read rsegs m _ (unmap_seqs st) (sc - 7) _ (Z_to_bv 64 (403448 + (sc + -7) + 856)) US (unmap_seqs_nth st (sc - 7) ltac:(lia)) ltac:(lia)
                ltac:(unfold wa, CTX; f_equal; lia)) as RDU. clear US.
  step. rewrite ?zxb_b8 by lia. clear RDU.
  (* [comment removed for export] *)
  step. step.
  set (nos := 100 <=? bounces st (sc - 7)).
  assert (NOSE : is_bouncing sc st = nos) by (unfold is_bouncing; rewrite IN; reflexivity).
  assert (A3 : Z_to_bv 64 (Z.lxor (bv_unsigned (v_sltiu (wz (bounces st (sc - 7))) 100)) 1) = Z_to_bv 64 (Z.b2z (is_bouncing sc st))).
  { rewrite NOSE. unfold v_sltiu, c_ltu, bv_ltu, nos. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    change (bv_wrap 64 100) with 100.
    destruct (Z.ltb_spec (bounces st (sc - 7)) 100); destruct (Z.leb_spec 100 (bounces st (sc - 7))); try lia; reflexivity. }
  rewrite A3. clear A3.
  assert (AB : account_bounce sc st =
    (if negb (unmap_seq st (sc - 7) =? 0) && (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10)
     then if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st
     else st)) by (unfold account_bounce; rewrite IN; reflexivity).
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (unmap_seq st (sc - 7))) in K1 by lia.
  { eapply EXIT; [exact MR| | exact MI| reflexivity| exact MU| exact WM]. rewrite AB, K1. reflexivity. }
  (* [comment removed for export] *)
  pose proof (mrep_seq_read st m (wa (403456 + 912)) MR eq_refl) as RDS.
  replace (wa (403456 + 912)) with (Z_to_bv 64 (403448 + 920)) in RDS by (unfold wa; f_equal; lia).
  step. rewrite ?zxb_b8 by lia. clear RDS.
  step. rewrite (wz_unsigned (c_seq (ctx st))), (wz_unsigned (unmap_seq st (sc - 7))) by lia.
  step. step. if_cases K2; unfold bv_lts in K2; rewrite !signed_lit_small in K2 by lia.
  { (* [comment removed for export] *)
    apply Z.ltb_lt in K2.
    apply evt_done. do 6 eexists. split; [reflexivity|]. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact MI|].
    rewrite AB. replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with false by (symmetry; apply Z.ltb_ge; lia).
    rewrite Bool.andb_false_r. exact MR. }
  apply Z.ltb_ge in K2.
  assert (AB2 : account_bounce sc st =
    (if bounces st (sc - 7) + 1 <? 100 then set_bounce (sc - 7) (bounces st (sc - 7) + 1) st else set_bounce (sc - 7) 150 st)).
  { rewrite AB. replace (unmap_seq st (sc - 7) =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    replace (c_seq (ctx st) - unmap_seq st (sc - 7) <? 10) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  clear AB K1 K2.
  (first [ pose proof (MR) as dR_2; dand3 dR_2 as _ (_ & _ & _ & _ & BA & _) _ | pose proof MR as (_ & (_ & _ & _ & _ & BA & _) & _) ]).
  pose proof (u8arr_store_ok rsegs _ _ (bouncess st) (sc - 7) (Z_to_bv 64 (403448 + (sc + -7) + 888)) BA
                ltac:(rewrite bouncess_length; lia) ltac:(unfold wa, CTX; f_equal; lia)) as SOK. clear BA.
  (* [comment removed for export] *)
  step. step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned (bounces st (sc - 7))), ?unsigned_lit in K3 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned (bounces st (sc - 7))) by lia.
    st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (mrep_set_bounce (Clg:=Clg) (Rr:=Rr) st mX (sc - 7) (bounces st (sc - 7) + 1) MR ltac:(lia)) as MR2; unfold CTX in MR2 end.
    raw_store_finish0 (403456 + 880 + (sc - 7)) [b8 (bounces st (sc - 7) + 1)] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. step. st1. rewrite (le1_lit 150) by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (mrep_set_bounce (Clg:=Clg) (Rr:=Rr) st mX (sc - 7) 150 MR ltac:(lia)) as MR2; unfold CTX in MR2 end.
    raw_store_finish0 (403456 + 880 + (sc - 7)) [b8 150] MU WM SOK.
    eapply EXIT; [exact MR2| | assumption| reflexivity| exact MU| exact WM].
    rewrite AB2. replace (bounces st (sc - 7) + 1 <? 100) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma rseq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m0 m : mem),
  mrep st m -> 0 <= c_seq (ctx st) < 256 -> mem_inv rsegs m ->
  munch seqW m0 m -> wmono rsegs m0 m ->
  evt rsegs (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24610) fc None m' (seg_rom rsegs)
      /\ munch seqW m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ mrep (step_seq st) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 (wz (c_seq (ctx st))) a7 s2 s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x245e4) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MR SEQ MI MU WM. unfold seqW in *.
  set (q := c_seq (ctx st)) in *.
  (first [ pose proof (MR) as dR_3; dand3 dR_3 as _ (_ & _ & _ & US & _ & C6) _ | pose proof MR as (_ & (_ & _ & _ & US & _ & C6) & _) ]).
  unfold CTX, MLOCK in *. unfold ctx_tail_cells in C6.
  replace (403456 + 912) with 404368 in C6 by reflexivity. replace (403456 + 848) with 404304 in US by reflexivity.
  (* [comment removed for export] *)
  assert (TL : forall (mj : mem) (stj : mstate) (ns : Z),
    0 <= ns < 256 -> mrep stj mj -> ctx_tail_cells stj = ctx_tail_cells st -> mem_inv rsegs mj ->
    munch [(403456 + 848, 403456 + 913)]%Z m0 mj -> wmono rsegs m0 mj ->
    evt rsegs (fun ms' => exists (a6' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 31) a6' a7 s2 s3 s4 s5 (Z_to_bv 64 403448) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24610) fc None m' (seg_rom rsegs)
      /\ munch [(403456 + 848, 403456 + 913)]%Z m0 m' /\ wmono rsegs m0 m' /\ mem_inv rsegs m' /\ mrep (upd_ctx (set_seq ns) stj) m')
      (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 (Z_to_bv 64 255) (Z_to_bv 64 ns) a7 s2 s3 s4 s5 (Z_to_bv 64 403448) s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x24608) fc None mj (seg_rom rsegs))).
  { intros mj stj ns NS MRj CTj MIj MUj WMj.
    (first [ pose proof (MRj) as dR_4; dand3 dR_4 as _ (_ & _ & _ & _ & _ & C6j) _ | pose proof MRj as (_ & (_ & _ & _ & _ & _ & C6j) & _) ]). rewrite CTj in C6j. unfold ctx_tail_cells in C6j. unfold CTX in C6j.
    replace (403456 + 912) with 404368 in C6j by reflexivity.
    pose proof (rw_cells_store_ok_at rsegs _ _ _ 0 (C1 (b8 (c_seq (ctx st)))) 1 (Z_to_bv 64 (403448 + 920)) C6j eq_refl eq_refl
                  ltac:(unfold wa; f_equal; lia)) as SOK.
    clear C6j.
    (* [comment removed for export] *)
    step. st1.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
      pose proof (mrep_set_seq stj mX ns MRj NS) as MR1; unfold CTX in MR1 end.
    raw_store_finish0 (403456 + 912) [b8 ns] MUj WMj SOK.
    apply evt_done. do 2 eexists. split; [reflexivity|].
    split; [exact MUj|]. split; [exact WMj|]. split; [assumption| exact MR1]. }
  (* [comment removed for export] *)
  step. step. if_cases K2; zify_cond K2; rewrite ?(wz_unsigned q), ?unsigned_lit in K2 by lia.
  - (* [comment removed for export] *)
    step. rewrite (wz_unsigned q) by lia.
    eapply evt_mono; [eapply (TL m st (q + 1)); [lia| exact MR| reflexivity| exact MI| exact MU| exact WM]|].
    intros ms' PO. rewrite (step_seq_eq st). fold q. replace (q =? 255) with false by (symmetry; apply Z.eqb_neq; lia). exact PO.
  - (* [comment removed for export] *)
    pose proof (rw_cells_of_u8arr rsegs _ _ _ US) as USC. rewrite unmap_seqs_length in USC. clear US C6.
    pose proof (munch_refl [(403456 + 848, 403456 + 880)]%Z m) as MUz. pose proof (wmono_refl rsegs m) as WMz.
    step. fix_lit_store. step. fix_lit_store. step. fix_lit_store. step. fix_lit_store.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (UZ : u8arr rsegs mX 404304 (zeros 32));
    [ apply (u8arr_of_rw_cells rsegs mX 404304 32);
      lazymatch goal with H : rw_cells rsegs mX 404304 _ |- _ =>
        apply (rw_cells_congr rsegs mX 404304 [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] [CB 32 (zeros 32)]); [reflexivity| reflexivity| cbn; split; [reflexivity| exact I]| exact H] end |] end.
    set (stz := upd_ctx (fun c => set_unmap_seq_map ∅ c) st).
    (first [ pose proof (MR) as dR_5; dand3 dR_5 as _ (_ & _ & _ & _ & _ & C6) _ | pose proof MR as (_ & (_ & _ & _ & _ & _ & C6) & _) ]). unfold ctx_tail_cells, CTX in C6.
    lazymatch goal with MUc : munch _ m ?mX, WMc : wmono rsegs m ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MRz : mrep stz mX);
    [ eapply (mrep_ctx_frameW st stz _ mX _ MR MUc WMc); try reflexivity;
      [ intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia]
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia]
      | left; unfold stz; rewrite unmap_seqs_empty; unfold CTX; exact UZ
      | right; split; [reflexivity| intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia]
      | right; split; [| intros lo' hi' [E|[]]; inversion E; subst; unfold CTX; lia];
        unfold ctx_tail_cells, brk_word, ctx, stz; cbn [s_ctx upd_ctx c_seq c_brk set_unmap_seq_map]; reflexivity ]
    | clear MUc WMc ] end.
    (* [comment removed for export] *)
    step. step.
    lazymatch goal with MUc : munch _ m0 ?mX, WMc : wmono rsegs m0 ?mX, MIc : mem_inv rsegs ?mX |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
      eapply evt_mono; [eapply (TL mX stz 1); [lia| exact MRz| reflexivity| exact MIc| exact MUc| exact WMc]|] end.
    intros ms' PO. rewrite (step_seq_eq st). fold q. rewrite K2. cbn [Z.eqb Pos.eqb]. exact PO.
Qed.
(* [comment removed for export] *)
#[using="SC"] Lemma mm_seq_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) (m : mem),
  mrep st m -> 0 <= c_seq (ctx st) < 256 -> (forall i, 0 <= bounces st i < 256) -> (forall i, 0 <= unmap_seq st i < 256) ->
  mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (t0' t1' a3' a6' a7' : word) m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3' a4 (Z_to_bv 64 31) a6' a7' s2 s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24610) fc None m' (seg_rom rsegs)
      /\ a3' = Z_to_bv 64 (Z.b2z (is_bouncing sc st))
      /\ munch seqW m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ mrep (step_seq (account_bounce sc st)) m')
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24330) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MR SEQ BR USR MI.
  eapply evt_cut; [eapply bounce_walk; eassumption|].
  cbv beta. (intros ms'; (first [ intro dR_6; dex6 dR_6 as t0' t1' a3' a5' a7' m'; dand6 dR_6 as -> A3 MU WM MI' MR' | intro dR_6; dand12 dR_6 as t0' t1' a3' a5' a7' m' -> A3 MU WM MI' MR' | intros (t0' & t1' & a3' & a5' & a7' & m' & -> & A3 & MU & WM & MI' & MR') ])).
  assert (SEQ' : c_seq (ctx (account_bounce sc st)) = c_seq (ctx st)).
  { unfold account_bounce. destruct (sc_in_seq_range sc); [|reflexivity].
    destruct (negb _ && _); [|reflexivity]. destruct (_ <? 100); reflexivity. }
  rewrite <- SEQ'.
  eapply evt_mono; [eapply (rseq_walk _ _ _ _ t0' t1'); [exact MR'| rewrite SEQ'; exact SEQ| exact MI'| exact MU| exact WM]|].
  cbv beta. (intros ms''; (first [ intro dR_7; dex2 dR_7 as a6'' m''; dand5 dR_7 as -> MU'' WM'' MI'' MR'' | intro dR_7; dand7 dR_7 as a6'' m'' -> MU'' WM'' MI'' MR'' | intros (a6'' & m'' & -> & MU'' & WM'' & MI'' & MR'') ])).
  do 6 eexists. split; [reflexivity|]. subst a3'.
  repeat (split; [first [reflexivity| assumption]|]). exact MR''.
Qed.
End SEQ.
End RASlanm.


Module RASlx4x.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASl0ja OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlanm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RAlllfc RASlot_I Malluin.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASl0ja.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)

Ltac bool_hyp b K := destruct b; cbn in K; first [reflexivity | discriminate | congruence | (exfalso; apply K; reflexivity)].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Definition mm_usage1 (st1 : mstate) (sc usage0 : Z) : Z :=
  if (Z.even sc) && (sc <? 32) then usage0 + usage st1 (sc + 1) else usage0.
Definition mm_cnt_red (sc size cnt usage1 : Z) (nosmall : bool) : Z :=
  if (usage1 <? 4 * cnt) && negb nosmall then
    if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
    else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
    else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
    else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
    else cnt
  else cnt.
Definition mm_small (size req usage1 cnt needed : Z) : Z * Z :=
  let req := round_up_pg (req + IB + UNIT) in
  if (req <? size + UNIT) || ((4 * PGSZ <=? req) && (usage1 <? 2 * cnt)) then (1, req) else (cnt, needed).
Definition mm_final (size req usage1 cnt : Z) (nosmall : bool) : Z * Z :=
  let needed := round_up_pg (size * cnt + UNIT) in
  if negb nosmall && (cnt <=? 7) then mm_small size req usage1 cnt needed else (cnt, needed).
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma land_4095_word z : Z.land (bv_unsigned (Z_to_bv 64 z)) 4095 = Z.land z 4095.
Proof.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2^52 * 2^12).
  change 4095 with (Z.ones 12). rewrite !Z.land_ones by lia.
  apply Z.mod_mod_divide. exists (2^52). reflexivity.
Qed.
Lemma land3_range x : 0 <= Z.land x 3 <= 3.
Proof. change (Z.land x 3) with (Z.land x (Z.ones 2)). rewrite Z.land_ones by lia. pose proof (Z.mod_pos_bound x (2^2) ltac:(lia)). lia. Qed.
Lemma land_4095_range y : 0 <= Z.land y 4095 < 4096.
Proof. change 4095 with (Z.ones 12). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. Qed.
Lemma round_up_pg_alt x : Z.land (- x) 4095 + x = round_up_pg x.
Proof. unfold round_up_pg. change (PGSZ - 1) with 4095. lia. Qed.
Lemma round_up_pg_range x : 0 <= x -> x <= round_up_pg x < x + 4096.
Proof. intros. unfold round_up_pg. change (PGSZ - 1) with 4095. pose proof (land_4095_range (- x)). lia. Qed.

Section MMC.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (sc size req : Z) (nos : bool).
Hypothesis SC : 0 <= sc < 48.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis RQ : 0 <= req < 2^32.

(* [comment removed for export] *)
Definition mmc_post (ra sp gp tp t1 t2 s0 s1 s2 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem)
    (res : Z * Z) : machine_state -> Prop :=
  fun ms' => exists (t0' a0' a1' a2' a3' a4' a5' a6' a7' : word),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 (wz (snd res)) s4 s5 s6 s7 s8 (wz (fst res)) s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x246f4) fc None m (seg_rom rsegs).

(* [comment removed for export] *)
#[using="RQ SZ"] Lemma rj2c_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a4 a5 a6 a7 s3 s4 s5 s6 s7 s10 s11 t3 t4 t5 t6 : word) F fc m (c1 u1 : Z),
  1 <= c1 <= 32 -> 0 <= u1 < 2^61 ->
  evt rsegs (mmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 s6 s7 (wz size) s10 s11 t3 t4 t5 t6 F fc m
               (mm_final size req u1 c1 nos))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) a4 a5 a6 a7
             (Z_to_bv 64 req) s3 s4 s5 s6 s7 (wz size) (wz c1) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24698) fc None m (seg_rom rsegs)).
Proof.
  intros until u1. intros CR UR.
  assert (SCR : 16 <= size * c1 < 2^24) by nia.
  pose proof (zb_b2z_range nos) as NR.
  unfold mmc_post.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned size), (wz_unsigned c1) by lia.
  step. step. step. step. step. step.
  rewrite !land_4095_word. rewrite ?(unsigned_lit (size * c1)) by lia.
  replace (-16 + - (size * c1)) with (- (size * c1 + 16)) by lia.
  set (nd0 := round_up_pg (size * c1 + 16)).
  pose proof (round_up_pg_alt (size * c1 + 16)) as RU. pose proof (round_up_pg_range (size * c1 + 16) ltac:(lia)) as RUR.
  replace (size * c1 + Z.land (- (size * c1 + 16)) 4095 + 16) with nd0 by lia.
  fold nd0 in RUR.
  assert (EF : mm_final size req u1 c1 nos = (if negb nos && (c1 <=? 7) then mm_small size req u1 c1 nd0 else (c1, nd0))).
  { unfold mm_final, UNIT. reflexivity. }
  (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
  { (* [comment removed for export] *)
    apply evt_done. rewrite EF. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]). cbn [negb andb fst snd].
    do 9 eexists. reflexivity. }
  replace nos with false in EF |- * by (destruct nos; cbn in KN; [lia| reflexivity]). cbn [negb andb] in EF.
  (* [comment removed for export] *)
  step. step. if_cases K7; zify_cond K7; rewrite ?(wz_unsigned c1), ?unsigned_lit in K7 by lia.
  { (* [comment removed for export] *)
    apply evt_done. rewrite EF. replace (c1 <=? 7) with false by (symmetry; apply Z.leb_gt; lia). cbn [fst snd].
    do 9 eexists. reflexivity. }
  replace (c1 <=? 7) with true in EF by (symmetry; apply Z.leb_le; lia).
  (* [comment removed for export] *)
  step. step. step. step. step.
  rewrite (Z.land_comm 4095), land_4095_word. rewrite ?(unsigned_lit req) by lia.
  replace (-20 + - req) with (- (req + 20)) by lia.
  set (rq' := round_up_pg (req + 20)).
  pose proof (round_up_pg_alt (req + 20)) as RU2. pose proof (round_up_pg_range (req + 20) ltac:(lia)) as RUR2.
  replace (req + Z.land (- (req + 20)) 4095 + 20) with rq' by lia. fold rq' in RUR2.
  assert (ES : mm_small size req u1 c1 nd0 = (if (rq' <? size + 16) || ((4 * PGSZ <=? rq') && (u1 <? 2 * c1)) then (1, rq') else (c1, nd0))).
  { unfold mm_small, IB, UNIT. replace (req + 4 + 16) with (req + 20) by lia. reflexivity. }
  rewrite ES in EF. clear ES. unfold PGSZ in EF. 
  (* [comment removed for export] *)
  step. if_cases K1; zify_cond K1; rewrite ?(wz_unsigned (size + 16)), ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    replace (rq' <? size + 16) with false in EF by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in EF.
    step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
    step. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    + (* [comment removed for export] *)
      apply evt_done. rewrite EF. replace (4 * 4096 <=? rq') with false by (symmetry; apply Z.leb_gt; lia). cbn [andb fst snd].
      do 9 eexists. reflexivity.
    + replace (4 * 4096 <=? rq') with true in EF by (symmetry; apply Z.leb_le; lia). cbn [andb] in EF.
      (* [comment removed for export] *)
      step. rewrite (wz_unsigned c1), Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2. rewrite swrap32_small by lia.
      step. if_cases K3; zify_cond K3; rewrite ?(wz_unsigned u1), ?unsigned_lit in K3 by lia.
      * (* [comment removed for export] *)
        step. step. step.
        apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with true by (symmetry; apply Z.ltb_lt; lia). cbn [fst snd].
        do 9 eexists. reflexivity.
      * apply evt_done. rewrite EF. replace (u1 <? 2 * c1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [fst snd].
        do 9 eexists. reflexivity.
  - (* [comment removed for export] *)
    replace (rq' <? size + 16) with true in EF by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in EF.
    step. step. step.
    apply evt_done. rewrite EF. cbn [fst snd]. do 9 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
#[using="SZ SC"] Lemma rred_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a5 a6 a7 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc m (cnt u1 : Z),
  1 <= cnt <= 32 -> 0 <= u1 < 2^61 ->
  evt rsegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
      ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
                   (Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24698) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5 a6 a7
             (Z_to_bv 64 req) (wz cnt) s4 s5 s6 s7 (wz size) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24624) fc None m (seg_rom rsegs)).
Proof.
  intros until u1. intros CR UR.
  assert (SCR : 16 <= size * cnt < 2^24) by nia.
  pose proof (zb_b2z_range nos) as NR. pose proof (land3_range sc) as L3.
  (* [comment removed for export] *)
  assert (J28 : forall (a5' a6' a7' t0' s9' : word) (c : Z), c = mm_cnt_red sc size cnt u1 nos ->
    evt rsegs (fun ms' => exists (a5' a6' a7' t0' s3' : word),
      ms' = MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
                   (Z_to_bv 64 req) s3' s4 s5 s6 s7 (wz size) (wz (mm_cnt_red sc size cnt u1 nos)) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24698) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0' t1 t2 (Z_to_bv 64 sc) s1 (wz u1) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) a5' a6' a7'
             (Z_to_bv 64 req) (wz c) s4 s5 s6 s7 (wz size) s9' s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24694) fc None m (seg_rom rsegs))).
  { intros a5' a6' a7' t0' s9' c ->. step. apply evt_done. do 5 eexists. reflexivity. }
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned cnt), Z.shiftl_mul_pow2, swrap32_small by lia. change (2 ^ 2) with 4.
  step. if_cases KU; zify_cond KU; rewrite ?(wz_unsigned u1), ?unsigned_lit in KU by lia.
  { eapply J28. unfold mm_cnt_red. replace (u1 <? 4 * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  (* [comment removed for export] *)
  step. if_cases KN; zify_cond KN; rewrite ?unsigned_lit in KN by lia.
  { eapply J28. unfold mm_cnt_red. replace nos with true by (destruct nos; cbn in KN; [reflexivity| lia]).
    rewrite Bool.andb_false_r. reflexivity. }
  assert (EN : nos = false) by (destruct nos; cbn in KN; [lia| reflexivity]).
  assert (ER : mm_cnt_red sc size cnt u1 nos =
    (if (Z.land sc 3 =? 1) && (8 * PGSZ <? size * cnt) then 2
     else if (Z.land sc 3 =? 2) && (4 * PGSZ <? size * cnt) then 3
     else if (Z.land sc 3 =? 0) && (8 * PGSZ <? size * cnt) then 3
     else if (Z.land sc 3 =? 0) && (2 * PGSZ <? size * cnt) then 5
     else cnt)).
  { unfold mm_cnt_red. rewrite EN. replace (u1 <? 4 * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity. }
  unfold PGSZ in ER.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia. step. step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 3) with 32768.
  step. if_cases KA; zify_cond KA; rewrite ?unsigned_lit in KA by lia.
  - (* [comment removed for export] *)
    replace (Z.land sc 3 =? 1) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
    step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia.
    + (* [comment removed for export] *)
      replace (Z.land sc 3 =? 2) with false in ER by (symmetry; apply Z.eqb_neq; lia). cbn [andb] in ER.
      (* [comment removed for export] *)
      step. step. step.
      step. if_cases KC; zify_cond KC.
      * (* [comment removed for export] *)
        rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
        destruct (Z.ltb_spec (Z.land sc 3) 1) as [A1|A1]; destruct (Z.ltb_spec 32768 (size * cnt)) as [LT|GE]; cbn [Z.b2z Z.land] in KC; try (exfalso; apply KC; reflexivity); [].
        assert (E0 : Z.land sc 3 = 0) by lia.
        step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [exfalso; lia|].
        step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [| exfalso; lia].
        apply evt_done. rewrite ER, E0. cbn [Z.eqb andb]. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
        do 5 eexists. reflexivity.
      * (* [comment removed for export] *)
        assert (NC : ~ (Z.land sc 3 = 0 /\ 32768 < size * cnt)).
        { intros [E0 LT]. rewrite ?(wz_unsigned (size * cnt)) in KC by lia.
          replace (Z.land sc 3 <? 1) with true in KC by (symmetry; apply Z.ltb_lt; lia).
          replace (32768 <? size * cnt) with true in KC by (symmetry; apply Z.ltb_lt; lia). change (Z.land (Z.b2z true) (Z.b2z true)) with 1 in KC. lia. }
        clear KC. step. step.
        step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia.
        { (* [comment removed for export] *)
          apply evt_done. rewrite ER. replace (Z.land sc 3 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb].
          do 5 eexists. reflexivity. }
        rewrite KD in ER |- *. cbn [Z.eqb andb] in ER.
        replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia).
        (* [comment removed for export] *)
        step. if_cases KE; zify_cond KE; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KE by lia; [exfalso; lia|].
        step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 1) with 8192.
        step. if_cases KQ; zify_cond KQ; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KQ by lia.
        -- eapply J28. rewrite ER. replace (2 * 4096 <? size * cnt) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
        -- step. eapply (J28 _ _ _ _ _ 5). rewrite ER. replace (2 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
    + (* [comment removed for export] *)
      rewrite KB in ER |- *. cbn [Z.eqb andb] in ER.
      step. rewrite (wz_unsigned 4096) by lia. change (Z.shiftl 4096 2) with 16384.
      step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
      * (* [comment removed for export] *)
        replace (4 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
        step. step. step.
        step. if_cases KG; zify_cond KG.
        { exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
        clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
        apply evt_done. rewrite ER. do 5 eexists. reflexivity.
      * (* [comment removed for export] *)
        step. step. apply evt_done. rewrite ER. replace (4 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
        do 5 eexists. reflexivity.
  - (* [comment removed for export] *)
    rewrite KA in ER |- *. cbn [Z.eqb andb] in ER.
    step. if_cases KC; zify_cond KC; rewrite ?(wz_unsigned (size * cnt)), ?unsigned_lit in KC by lia.
    + (* [comment removed for export] *)
      replace (8 * 4096 <? size * cnt) with false in ER by (symmetry; apply Z.ltb_ge; lia). cbn [andb] in ER.
      step. step. if_cases KB; zify_cond KB; rewrite ?unsigned_lit in KB by lia; [| exfalso; lia].
      step. step. step.
      step. if_cases KG; zify_cond KG.
      { exfalso. apply KG. cbn. first [reflexivity | destruct (32768 <? _); reflexivity]. }
      clear KG. step. step. step. if_cases KD; zify_cond KD; rewrite ?unsigned_lit in KD by lia; [| exfalso; lia].
      apply evt_done. rewrite ER. do 5 eexists. reflexivity.
    + (* [comment removed for export] *)
      step. step. apply evt_done. rewrite ER. replace (8 * 4096 <? size * cnt) with true by (symmetry; apply Z.ltb_lt; lia).
      do 5 eexists. reflexivity.
Qed.
(* [comment removed for export] *)
#[using="SC"] Lemma rusage1_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a1 a2 a3 a4 a6 a7 s2 s3 s4 s5 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (u0 : Z),
  mrep st m -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
  evt rsegs (fun ms' => exists (a5' : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz (mm_usage1 st sc u0)) a1 a2 a3 a4 a5' a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (MLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x24624) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) a1 a2 a3 a4 (Z_to_bv 64 31) a6 a7 s2 s3 s4 s5 s6 (Z_to_bv 64 (MLOCK + 8 * sc)) s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24610) fc None m (seg_rom rsegs)).
Proof.
  intros until u0. intros MR UR USR. unfold MLOCK, CTX in *.
  pose proof (land_upper sc 1 ltac:(lia) ltac:(lia)) as L1R.
  (* [comment removed for export] *)
  step. if_cases K; unfold bv_lts in K; rewrite !signed_lit_small in K by lia.
  { apply Z.ltb_lt in K. apply evt_done. unfold mm_usage1. replace (sc <? 32) with false by (symmetry; apply Z.ltb_ge; lia). rewrite Bool.andb_false_r.
    eexists. reflexivity. }
  apply Z.ltb_ge in K.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit sc) by lia.
  step. if_cases KO; zify_cond KO; rewrite ?(unsigned_lit (Z.land sc 1)) in KO by lia.
  { (* [comment removed for export] *)
    assert (ODD : Z.even sc = false).
    { rewrite even_of_land1. apply Z.eqb_neq. exact KO. }
    apply evt_done. unfold mm_usage1. rewrite ODD. cbn [andb]. eexists. reflexivity. }
  assert (EV : Z.even sc = true) by (rewrite even_of_land1; apply Z.eqb_eq; exact KO).
  (* [comment removed for export] *)
  pose proof (mrep_usage_read (Clg:=Clg) (Rr:=Rr) st m (sc + 1) (wa (403456 + 464 + 8 * (sc + 1))) MR ltac:(lia) eq_refl) as RDU.
  replace (wa (403456 + 464 + 8 * (sc + 1))) with (Z_to_bv 64 (403448 + 8 * sc + 480)) in RDU by (unfold wa; f_equal; lia).
  pose proof (USR (sc + 1)) as U1R.
  step. clear RDU. step. rewrite (wz_unsigned (usage st (sc + 1))), (wz_unsigned u0) by lia.
  apply evt_done. unfold mm_usage1. rewrite EV. replace (sc <? 32) with true by (symmetry; apply Z.ltb_lt; lia). cbn [andb].
  eexists. unfold wz. rewrite (Z.add_comm (usage st (sc + 1)) u0). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="RQ SZ SC"] Lemma mmc_walk :
  forall (ra sp gp tp t0 t1 t2 s1 a6 a7 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word) F fc (st : mstate) m (cnt u0 : Z),
  mrep st m -> 1 <= cnt <= 32 -> 0 <= u0 < 2^60 -> (forall i, 0 <= usage st i < 2^60) ->
  evt rsegs (mmc_post ra sp gp tp t1 t2 (Z_to_bv 64 sc) s1 (Z_to_bv 64 req) s4 s5 (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) (wz size) s10 s11 t3 t4 t5 t6 F fc m
               (mm_final size req (mm_usage1 st sc u0) (mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos) nos))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) s1 (wz u0) (wz 4096) (wz (size + 16)) (Z_to_bv 64 (Z.b2z nos)) (wz (size * cnt)) (Z_to_bv 64 31) a6 a7
             (Z_to_bv 64 req) (wz cnt) s4 s5 (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) (wz size) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24610) fc None m (seg_rom rsegs)).
Proof.
  intros until u0. intros MR CR UR USR.
  assert (U1R : 0 <= mm_usage1 st sc u0 < 2^61).
  { unfold mm_usage1. pose proof (USR (sc + 1)). destruct (_ && _); lia. }
  eapply evt_cut. { eapply (rusage1_walk _ _ _ _ t0 t1 t2 s1); [exact MR| exact UR| exact USR]. }
  cbv beta. intros ms' (a5' & ->).
  eapply evt_cut. { eapply (rred_walk _ _ _ _ t0 t1 t2 s1); [exact CR| exact U1R]. }
  cbv beta. intros ms'' (a5'' & a6'' & a7'' & t0'' & s3'' & ->).
  assert (CRR : 1 <= mm_cnt_red sc size cnt (mm_usage1 st sc u0) nos <= 32).
  { unfold mm_cnt_red. destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia. }
  eapply evt_mono. { eapply rj2c_walk; [exact CRR| exact U1R]. }
  cbv beta. unfold mmc_post. intros ms3 (t0x & a0' & a1' & a2' & a3' & a4' & a5x & a6x & a7x & ->).
  do 9 eexists. reflexivity.
Qed.
End MMC.
End RASlx4x.


Module RASl8jf.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y RF_mk75.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RF_egfy RAlllfc RASlot_I Malluin RF_ntf_A RF_muly.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mk75 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_muly OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlh1b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.F_ntf_B.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep MRepAux F_mm4hw RF_muly.

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
Definition mm_frame (nd gm cnt size sc : Z) (j8 : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [C8 (wz nd); C8 (Z_to_bv 64 gm); C8 (wz cnt); C8 (wz size); C8 (Z_to_bv 64 (sc + 58)); CB 8 j8; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma divu_word a b : 0 <= a < 2^64 -> 0 < b < 2^64 -> mul_div M_DIVU (Z_to_bv 64 a) (wz b) = Z_to_bv 64 (a / b).
Proof.
  intros Ha Hb. unfold mul_div. rewrite (wz_unsigned b) by lia. replace (b =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  apply bv_eq. rewrite bv_divu_unsigned, (wz_unsigned b), unsigned_lit, Z_to_bv_unsigned by lia.
  unfold bv_wrap. change (bv_modulus 64) with (2^64). symmetry. apply Z.mod_small.
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.
Lemma mm_call_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' =>
      ms' = MS (mkR (Z_to_bv 64 0x24714) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) s3 (Z_to_bv 64 3) (Z_to_bv 64 34) (Z_to_bv 64 (-1)) (Z_to_bv 64 0) a6 a7
                   (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 mmap_entry) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x246f4) fc None m (seg_rom rsegs)).
Proof.
  intros. unfold mmap_entry.
  step. step. step. step. step. step. step. step.
  apply evt_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mm_ret_fail_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc m,
  evt rsegs (fun ms' =>
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2483c) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (-1)) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (-1)) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24714) fc None m (seg_rom rsegs)).
Proof.
  intros. step. if_cases K; zify_cond K. 2:{ exfalso. apply K. reflexivity. }
  apply evt_done. reflexivity.
Qed.

Section MMOK.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st2 : mstate) (sc cnt size nd xa c : Z) (mt : aptr).
Let G := conc st2 mt.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SZ : 16 <= size < 2^18.
Hypothesis ND : 16 <= nd < 2^40.
Hypothesis NDA : nd mod 4096 = 0.
Hypothesis XA : 0 < xa.
Hypothesis XA2 : xa + nd <= alloc_ceiling.
Hypothesis MST : meta_slot st2 mt.
Hypothesis REC : get_meta_rec st2 mt = meta0.
Hypothesis HC : c_mmap_counter (ctx st2) = c.
Hypothesis CR : 0 <= c < 2^32.

(* [comment removed for export] *)
Definition mm_ai : Z :=
  let ai := (4096 - UNIT) / size - 1 in
  let ai := if cnt - 1 <? ai then cnt - 1 else ai in
  if ai <? 0 then 0 else ai.
Definition mm_st4 : mstate :=
  upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2).
#[using="SZ CNT G mt nd st2"] Lemma mm_ai_range : 0 <= mm_ai <= cnt - 1.
Proof.
  unfold mm_ai, UNIT. change (4096 - 16) with 4080.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)).
  destruct (Z.ltb_spec (cnt - 1) (4080 / size - 1)); [destruct (Z.ltb_spec (cnt - 1) 0)| destruct (Z.ltb_spec (4080 / size - 1) 0)]; lia.
Qed.
#[using="CR HC REC MST XA2 XA NDA ND SZ CNT SC"] Lemma mm_ret_ok_walk :
  forall (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s4 s5 s7 s10 s11 t3 t4 t5 t6 : word) F fc m,
  mrep st2 m -> mem_inv rsegs m ->
  evt rsegs (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 mm_ai) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 MLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2476c) fc None m' (seg_rom rsegs)
      /\ munch [(G, G + 40); (CTX + 12, CTX + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep mm_st4 m' /\ c_mmap_counter (ctx mm_st4) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 MLOCK) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24714) fc None m (seg_rom rsegs)).
Proof.
  intros until m. intros MR MI.
  pose proof (munch_refl [(G, G + 40); (CTX + 12, CTX + 16)]%Z m) as MU. pose proof (wmono_refl rsegs m) as WM.
  pose proof (meta_slot_bounds st2 m mt MR MST) as (Gpos & GC & GI & G4 & _). fold G in Gpos, GC, GI, G4.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold CTX, MLOCK in *.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia. { exfalso. change (bv_unsigned (Z_to_bv 64 (-1))) with (2^64 - 1) in K. lia. }
  clear K.
  (* [comment removed for export] *)
  step.
  mchunk MR MST CH. fold G in CH. rewrite REC in CH. cbn [m_prev m_next m_mem m_avail m_freed oconc] in CH. rewrite meta_word_meta0 in CH.
  meta_open G MUa WMa.
  step.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned nd) by lia. rewrite land_m4096 by lia. rewrite NDA, Z.sub_0_r.
  step. step. step. change (bv_swrap 32 (4096 + -16)) with 4080.
  rewrite (divu_word 4080 size) by lia.
  pose proof (Z.div_pos 4080 size ltac:(lia) ltac:(lia)) as D0. pose proof (Z.div_le_upper_bound 4080 size 255 ltac:(lia) ltac:(lia)) as D1.
  set (d := 4080 / size) in *.
  (* [comment removed for export] *)
  pose proof MR as (_ & (CX1 & _) & _). unfold ctx_head_cells in CX1. rewrite HC in CX1. unfold CTX in CX1.
  step. rewrite (sx32_wz_sxv c) by lia.
  (* [comment removed for export] *)
  step. step. step. cbn [Z.shiftl Z.shiftr]. rewrite ?unsigned_lit by lia. rewrite ?Z.lor_0_l.
  step. rewrite (wz_unsigned (sxv c)) by (apply sxv_range).
  (* [comment removed for export] *)
  assert (ND12 : Z.shiftr nd 12 = nd / 4096) by (rewrite Z.shiftr_div_pow2 by lia; reflexivity).
  assert (EWD : meta_word (m_set_maplen (Z.shiftr nd 12) meta0) = nd).
  { unfold meta_word, m_set_maplen, meta0. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite ND12.
    change (2 ^ 52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia. rewrite Z.mod_small by (Z.div_mod_to_equations; lia).
    Z.div_mod_to_equations. lia. }
  step.
  lazymatch goal with H : rw_cells rsegs ?mX G _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR3 : mrep (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) mX);
    [ unfold upd_meta; rewrite REC; eapply mrep_put_meta_frame; [exact MR| exact MST| exact MUa| exact WMa|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells; rewrite EWD; unfold pw; cbn [m_prev m_next m_mem m_avail m_freed oconc m_set_maplen meta0]; reflexivity
    | clear MUa WMa H ] end.
  set (st3 := upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2) in *.
  (* [comment removed for export] *)
  pose proof (rw_cells_store_ok_at rsegs _ _ _ 12 (C4 (wz c)) 4 (Z_to_bv 64 (403448 + 20)) CX1 eq_refl eq_refl ltac:(unfold wa; f_equal; lia)) as SOK.
  clear CX1.
  st1.
  rewrite le4_swrap_succ by lia.
  assert (VR : 0 <= u32 (c + 1) < 2^32) by (unfold u32; Z.div_mod_to_equations; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_set_mmap_counter st3 mX (u32 (c + 1)) MR3 VR) as MR4; unfold CTX in MR4 end.
  clear MR3.
  raw_store_finish0 (403456 + 12) (le4 (wz (u32 (c + 1)))) MU WM SOK.
  assert (E4 : mm_st4 = upd_ctx (set_mmap_counter (u32 (c + 1))) st3).
  { unfold mm_st4, st3, upd_ctx. change (ctx (upd_meta mt (m_set_maplen (Z.shiftr nd 12)) st2)) with (ctx st2). rewrite HC. reflexivity. }
  rewrite <- E4 in MR4.
  assert (C4' : c_mmap_counter (ctx mm_st4) = u32 (c + 1)) by (rewrite E4; reflexivity).
  (* [comment removed for export] *)
  step. step.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
  assert (J : forall (a2v : word) (mn : Z), mn = (if cnt <? d then cnt else d) -> a2v = Z_to_bv 64 mn ->
    evt rsegs (fun ms' => exists (a3' a4' : word) m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G)
                   (Z_to_bv 64 xa) (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 mm_ai) a3' a4' a5 a6 a7
                   (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 403448) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2476c) fc None m' (seg_rom rsegs)
      /\ munch [(G, G + 40); (403456 + 12, 403456 + 16)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
      /\ mrep mm_st4 m' /\ c_mmap_counter (ctx mm_st4) = u32 (c + 1))
    (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 sc) (Z_to_bv 64 G) (Z_to_bv 64 xa) (Z_to_bv 64 d) a2v (Z_to_bv 64 nd) (Z_to_bv 64 (bv_swrap 32 c + 1)) a5 a6 a7
             (Z_to_bv 64 (-1)) (wz nd) s4 s5 (Z_to_bv 64 403448) s7 (wz size) (wz cnt) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24758) fc None mX (seg_rom rsegs))) end.
  { intros a2v mn Hmn ->.
    assert (MNR : 0 <= mn <= cnt /\ mn <= d) by (rewrite Hmn; destruct (Z.ltb_spec cnt d); lia).
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit mn) by lia. step. step. step. step.
    replace (cnt + -1) with (cnt - 1) by lia.
    assert (AI : mm_ai = (if mn =? 0 then 0 else mn - 1)).
    { unfold mm_ai. change (4096 - UNIT) with 4080. fold d. rewrite Hmn.
      destruct (Z.ltb_spec cnt d) as [LT|GE].
      - replace (cnt - 1 <? d - 1) with true by (symmetry; apply Z.ltb_lt; lia).
        replace (cnt - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
        replace (cnt =? 0) with false by (symmetry; apply Z.eqb_neq; lia). reflexivity.
      - replace (cnt - 1 <? d - 1) with false by (symmetry; apply Z.ltb_ge; lia).
        destruct (Z.eqb_spec d 0) as [E0|NE0].
        + rewrite E0. reflexivity.
        + replace (d - 1 <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    assert (EA2 : Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltu (Z_to_bv 64 mn) (Z_to_bv 64 (mn + -1))) + -1))) (bv_unsigned (Z_to_bv 64 (mn + -1))))
                  = Z_to_bv 64 mm_ai).
    { rewrite AI. unfold v_sltu, c_ltu, bv_ltu. rewrite (unsigned_lit mn) by lia.
      destruct (Z.eqb_spec mn 0) as [E0|NE0].
      - rewrite E0. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with (2^64 - 1). cbn [Z.ltb]. reflexivity.
      - rewrite (unsigned_lit (mn + -1)) by lia. replace (mn <? mn + -1) with false by (symmetry; apply Z.ltb_ge; lia).
        change (bv_unsigned (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 0) + -1))) with (Z.ones 64). rewrite Z.land_comm, Z.land_ones_low; [f_equal; lia| lia|].
        destruct (Z.eq_dec (mn + -1) 0) as [->|]; [cbn; lia|]. apply Z.log2_lt_pow2; lia. }
    rewrite EA2.
    apply evt_done. do 3 eexists. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR4| exact C4']. }
  if_cases K1; zify_cond K1; rewrite ?(wz_unsigned cnt), ?unsigned_lit in K1 by lia.
  - (* [comment removed for export] *)
    eapply J; [reflexivity|]. replace (cnt <? d) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
  - (* [comment removed for export] *)
    step. eapply J; [reflexivity|]. replace (cnt <? d) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
End MMOK.
End RASl8jf.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.

Module RASlts3.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlot_I.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
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
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma ras_ret0 : forall (sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 x1 : word)
    (s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav : word) F fc (m : word -> option byte) (junk : list byte) (st' : mstate) (lo : Z),
  mrep st' m -> mem_inv rsegs m ->
  rw_cells rsegs m (bv_unsigned sp + -144) (ta_frame junk s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v rav) ->
  stk rsegs m lo (bv_unsigned sp + -144) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 144 ->
  evt rsegs (fun ms' => exists (a1' a2' : word),
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v a0 a1' a2' a3 a4 a5 a6 a7 s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3 t4 t5 t6)
              F (ret_pc rav) fc None m (seg_rom rsegs)
      /\ stk rsegs m lo (bv_unsigned sp))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 (Z_to_bv 64 SSP_GUARD) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x248c4) fc None m (seg_rom rsegs)).
Proof.
  intros until lo. intros MR' MI FR ST LO LOLE.
  pose proof (bv_unsigned_in_range _ sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof MR' as (_ & _ & (_ & _ & _ & _ & GUARD) & _).
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); unfold SSP_GUARD, ta_frame in *.
  (* [comment removed for export] *)
  step. step. step. if_cases K; zify_cond K. { exfalso. apply K. reflexivity. }
  (* [comment removed for export] *)
  step. step. step. step. step. step. step. step. step. step. step. step. step.
  release_frame FR ST (bv_unsigned sp).
  apply evt_done. do 2 eexists. split; [reflexivity| exact ST].
Qed.

End CEIL.
End RASlts3.

Module RASljm5.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlh4s RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24.RASlico OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlts3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require InitMono.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_sy88u MRep MRepAux RF_m8yt RAlllfc RF_mx3o Malllim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_mx3o OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malllim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.ASlot_W8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.ASlooxi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24.RASlico OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.

Definition epi_frame (jj : list byte) (s4v s3v s2v s1v s0v rav : word) : list cell :=
  [CB 48 jj; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav].
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

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

Variable am_pre : mstate -> Prop.
Hypothesis AM : alloc_meta_stmt am_pre.
Hypothesis AMP : AMP_AS am_pre.

(* [comment removed for export] *)
Definition rag_regs (x1 t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s3' s8' s9' t3' t4' t5' t6' : word) :=
  mkR x1 (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) s1' a0' a1' a2' a3' a4' a5' a6' a7' a1 s3'
      (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (CTX + 80 + 8 * sc)) (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc)) s8' s9' s10 s11 t3' t4' t5' t6'.
Definition rFRM (junk : list byte) := ta_frame junk s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 ra.

(* [comment removed for export] *)
Definition HAG_stmt : Prop :=
  forall st1 st2 mm m3 s' (errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (junk : list byte) oo,
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) ->
  IST st0 st2 -> ENTRY_REL st0 st2 -> ALLC st2 ->
  am_rel st1 st2 (Some mm) -> get_meta_rec st2 mm = meta0 -> meta_slot st2 mm ->
  mrep st2 m3 -> ticks_ok st2 -> unk_agree st2 o m3 -> mem_inv rsegs m3 -> stk rsegs m3 lo (bv_unsigned sp + -144) ->
  rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk) ->
  rw_cells rsegs m3 (errno_addr tp) [C4 errv'] -> auxv_okd (c_init_done (ctx st0)) m3 (bv_unsigned sp) ->
  pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m3 ->
  brk_link_ps st2 s' -> ps_m s' = ps_m s -> ps_fa s' = ps_fa s -> ps_so s' = ps_so s ->
  implT o (ag_body f sc req k bail st2 mm) s' Q
    (MS (rag_regs (Z_to_bv 64 0x2425c) t0' t1' t2' (Z_to_bv 64 (conc st2 mm)) (Z_to_bv 64 (-1)) a1' a2' a3' a4' a5' a6' a7'
                  (Z_to_bv 64 (sc * 2)) (wz (size_class sc)) (Z_to_bv 64 SIZE_CLASSES) t3' t4' t5' t6')
        F (Z_to_bv 64 0x24268) fc None m3 (seg_rom rsegs)).
Hypothesis HAG : HAG_stmt.

Lemma errno_lit2 : errno_addr tp = 0x42454.
Proof. rewrite TP. unfold PTP. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma conc_meta_stable stE q : mrel st stE -> meta_slot st q -> conc stE q = conc st q.
Proof.
  (intros REL; (first [ intro dR_32; dex3 dR_32 as ar arr kk; dand3 dR_32 as Ha Hk -> | intro dR_32; dand6 dR_32 as ar arr kk Ha Hk -> | intros (ar & arr & kk & Ha & Hk & ->) ])). pose proof MR as (WF & _). (first [ pose proof (WF) as dR_1; dand5 dR_1 as _ _ _ WA _ | pose proof WF as (_ & _ & _ & WA & _) ]).
  (first [ pose proof ((WA ar arr Ha)) as dR_2; dex1 dR_2 as r; destruct dR_2 as [Hr _] | pose proof ((WA ar arr Ha)) as dR_2; dand3 dR_2 as r Hr _ | destruct (WA ar arr Ha) as (r & Hr & _) ]). (first [ pose proof ((mrel_regions _ _ REL _ _ Hr)) as dR_3; dex1 dR_3 as r'; dand4 dR_3 as Hr' _ B' _ | pose proof ((mrel_regions _ _ REL _ _ Hr)) as dR_3; dand5 dR_3 as r' Hr' _ B' _ | destruct (mrel_regions _ _ REL _ _ Hr) as (r' & Hr' & _ & B' & _) ]).
  unfold aadd. cbn [fst snd]. rewrite (conc_region stE (fst ar) _ r' Hr'), (conc_region st (fst ar) _ r Hr). lia.
Qed.

(* [comment removed for export] *)
Lemma ta_fp_malloc_fp stE mE a :
  mrep stE mE -> mrel st stE -> (forall q, meta_slot st q -> meta_slot stE q) ->
  ta_fp st lo (bv_unsigned sp) a -> malloc_fp st0 stE lo (bv_unsigned sp) a.
Proof.
  intros MRE REL AREAS [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - left. left. exact X.
  - left. right. right. left. exact X.
  - left. do 3 right.
    pose proof (AREAS q MSq) as MSq'.
    (first [ pose proof ((meta_chunk_facts stE mE q MRE MSq')) as dR_4; dand7 dR_4 as _ _ _ _ _ _ (rid0 & r0 & H0 & K0 & L0 & H0') | destruct (meta_chunk_facts stE mE q MRE MSq') as (_ & _ & _ & _ & _ & _ & (rid0 & r0 & H0 & K0 & L0 & H0')) ]).
    exists rid0, r0. split; [exact H0|]. split; [exact K0|].
    rewrite (conc_meta_stable stE q REL MSq) in L0, H0'. lia.
  - do 3 right. left. pose proof MR as (WF & _).
    (first [ pose proof ((group_conc st bq gh WF Hbq)) as dR_5; dex1 dR_5 as rb; dand7 dR_5 as Hrb Cb Kb B0 B16' M16 _ | pose proof ((group_conc st bq gh WF Hbq)) as dR_5; dand8 dR_5 as rb Hrb Cb Kb B0 B16' M16 _ | destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _) ]).
    destruct ER as [_ EG EGR _ _ _ _ _].
    destruct (proj1 (EG bq) (ex_intro _ gh Hbq)) as [gh0 Hbq0].
    exists bq, gh0, rb. split; [exact Hbq0|]. split; [apply (proj1 (EGR _ _ Kb)); exact Hrb|]. split; [exact Kb|].
    rewrite Cb in Xq. lia.
Qed.

(* [comment removed for export] *)
Lemma ta_fp_not_image a : 0x10000 <= a < 0x64000 -> ~ (CTX <= a < CTX + 928) -> ~ ta_fp st lo (bv_unsigned sp) a.
Proof.
  intros Ha Hc [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
  - exact (Hc X).
  - (first [ pose proof ((meta_slot_bounds st m q MR MSq)) as dR_6; dand4 dR_6 as _ _ GI _ | destruct (meta_slot_bounds st m q MR MSq) as (_ & _ & GI & _) ]). lia.
  - pose proof MR as (WF & _). (first [ pose proof ((group_conc st bq gh WF Hbq)) as dR_7; dex1 dR_7 as rb; dand6 dR_7 as Hrb Cb Kb B0 BE _ | pose proof ((group_conc st bq gh WF Hbq)) as dR_7; dand7 dR_7 as rb Hrb Cb Kb B0 BE _ | destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & _) ]).
    (first [ pose proof ((rregion_facts st m (fst bq) rb MR Hrb)) as dR_8; dand5 dR_8 as _ _ _ RI1 RI2 | destruct (rregion_facts st m (fst bq) rb MR Hrb) as (_ & _ & _ & RI1 & RI2) ]).
    pose proof (round_up_pg_ge (r_len rb)). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma ta_fp_not_high a : bv_unsigned sp <= a -> ~ ta_fp st lo (bv_unsigned sp) a.
Proof.
  pose proof (AS_STACK_ge sc) as ASG. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  intros Ha [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - unfold CTX in X. lia.
  - (first [ pose proof ((meta_slot_bounds st m q MR MSq)) as dR_9; dand3 dR_9 as _ GC _ | destruct (meta_slot_bounds st m q MR MSq) as (_ & GC & _) ]). lia.
  - pose proof MR as (WF & _). (first [ pose proof ((group_conc st bq gh WF Hbq)) as dR_10; dex1 dR_10 as rb; dand8 dR_10 as Hrb Cb Kb B0 BE M16 RB0 RC | pose proof ((group_conc st bq gh WF Hbq)) as dR_10; dand9 dR_10 as rb Hrb Cb Kb B0 BE M16 RB0 RC | destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & BE & M16 & RB0 & RC) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv). lia.
Qed.

(* [comment removed for export] *)
Lemma unk_agree_keep stE mE :
  s_shadow stE = s_shadow st ->
  (forall rid r, r_kind r = RKGroup -> (s_regions stE) !! rid = Some r -> (s_regions st) !! rid = Some r) ->
  (forall b, is_Some ((s_groups stE) !! b) <-> is_Some ((s_groups st) !! b)) ->
  (forall rid r off h, (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) ->
      cell_read (get_shadow st rid) off = Unknown h -> ~ grp_hdr_cov st rid off -> mE (wa (r_base r + off)) = m (wa (r_base r + off))) ->
  unk_agree stE o mE.
Proof.
  intros ES ERG EG AG rid r off h Hr Hk Ho Hc NG.
  pose proof (ERG rid r Hk Hr) as Hr0.
  assert (Hc0 : cell_read (get_shadow st rid) off = Unknown h) by (revert Hc; unfold get_shadow; rewrite ES; intros X; exact X).
  assert (NG0 : ~ grp_hdr_cov st rid off).
  { ((first [ intro dR_33; dex2 dR_33 as bq gh; dand3 dR_33 as Hbq Hf Hoff | intro dR_33; dand5 dR_33 as bq gh Hbq Hf Hoff | intros (bq & gh & Hbq & Hf & Hoff) ])). apply NG. destruct (proj2 (EG bq) (ex_intro _ gh Hbq)) as [gh1 Hbq1]. exists bq, gh1. auto. }
  rewrite (AG rid r off h Hr0 Hk Ho Hc0 NG0). exact (UA rid r off h Hr0 Hk Ho Hc0 NG0).
Qed.

(* [comment removed for export] *)
Lemma ta_fp_not_inband rid r off :
  (s_regions st) !! rid = Some r -> r_kind r = RKGroup -> 0 <= off < round_up_pg (r_len r) -> ~ grp_hdr_cov st rid off ->
  ~ ta_fp st lo (bv_unsigned sp) (r_base r + off).
Proof.
  intros Hr Hk Ho NG. pose proof MR as (WF & _). (first [ pose proof (WF) as dR_11; dand4 dR_11 as _ WR DJ _ | pose proof WF as (_ & WR & DJ & _) ]).
  (first [ pose proof ((WR _ _ Hr)) as dR_12; dand5 dR_12 as R0 _ _ RC _ | destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  intros [X|[X|[(q & MSq & Xq)|(bq & gh & Hbq & Xq)]]].
  - lia.
  - (first [ pose proof ((rregion_facts st m rid r MR Hr)) as dR_13; dand5 dR_13 as _ _ _ RI1 RI2 | destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2) ]). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold CTX in X. lia.
  - (first [ pose proof ((meta_chunk_facts st m q MR MSq)) as dR_14; dand7 dR_14 as _ _ _ _ _ GRG _ | destruct (meta_chunk_facts st m q MR MSq) as (_ & _ & _ & _ & _ & GRG & _) ]). destruct (GRG rid r Hr Hk); lia.
  - (first [ pose proof ((group_conc st bq gh WF Hbq)) as dR_15; dex1 dR_15 as rb; dand7 dR_15 as Hrb Cb Kb B0 B16' M16 _ | pose proof ((group_conc st bq gh WF Hbq)) as dR_15; dand8 dR_15 as rb Hrb Cb Kb B0 B16' M16 _ | destruct (group_conc st bq gh WF Hbq) as (rb & Hrb & Cb & Kb & B0 & B16' & M16 & _) ]).
    destruct (N.eq_dec (fst bq) rid) as [E|NE].
    + apply NG. exists bq, gh. split; [exact Hbq|]. split; [exact E|]. rewrite E, Hr in Hrb. inversion Hrb; subst rb. lia.
    + pose proof (lr_lo_group r Hk). pose proof (lr_lo_group rb Kb). destruct (DJ _ _ _ _ Hrb Hr NE); lia.
Qed.

Lemma ag_phase : forall st1 m1 (t0' t1' a0' a1' a2' a3' a4' a5' a6' a7' : word) (junk : list byte),
  ta_fail sc st st1 -> ta_rel sc st st1 -> active st1 sc = None ->
  mrep st1 m1 -> mem_inv rsegs m1 -> rw_cells rsegs m1 (bv_unsigned sp + -144) (rFRM junk) -> stk rsegs m1 lo (bv_unsigned sp + -144) ->
  pres_except (ta_fp st lo (bv_unsigned sp)) m m1 ->
  implT o (as_grp full_lay f sc req k bail st1) s Q
    (MS (rag_regs ra t0' t1' t2 s1 a0' a1' a2' a3' a4' a5' a6' a7' s3 s8 s9 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24244) fc None m1 (seg_rom rsegs)).
Proof.
  intros until junk. intros TF TR ACT0 MR1 MI1 FR1 ST1 PE1.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  pose proof (AS_STACK_ge sc) as ASG. pose proof CLO as CLO'. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof errno_lit2 as EA.
  pose proof (isf_mf _ _ F0) as MF. pose proof MR as (WF & _). (first [ pose proof (WF) as dR_16; dand5 dR_16 as RS WR DJ WA WG | pose proof WF as (RS & WR & DJ & WA & WG) ]).
  rewrite (as_grp_eq f sc req k bail st1).
  iprefixT. unfold rag_regs.
  eapply evt_cut. { eapply (rag_entry_walk sc SC). exact MI1. }
  cbv beta. intros ms' ->. apply evt_done. unfold t1_regs.
  (* [comment removed for export] *)
  assert (REG1 : s_regions st1 = s_regions st) by apply (tr_regions _ _ _ TR).
  assert (TK1 : ticks_ok st1) by (eapply ticks_ok_same; [apply (tr_shadow _ _ _ TR)| apply (tr_tick _ _ _ TR)| exact TK]).
  assert (CONC1 : forall q, conc st1 q = conc st q) by (intros q; unfold conc, get_region; rewrite REG1; reflexivity).
  assert (BL1 : brk_link_ps st1 s).
  { unfold brk_link_ps in *. unfold ctx in *. (first [ pose proof ((tr_ctx _ _ _ TR)) as dR_17; dand15 dR_17 as _ _ _ _ _ _ _ _ _ _ _ _ _ _ CB' | destruct (tr_ctx _ _ _ TR) as (_&_&_&_&_&_&_&_&_&_&_&_&_&_&CB') ]).
    unfold ctx in CB'. rewrite CB'. destruct (c_brk (s_ctx st)) as [| |rid off]; auto. rewrite CONC1. exact BL. }
  assert (AUX2 : auxv_okd (c_init_done (ctx st0)) m1 (bv_unsigned sp + -144)).
  { apply (auxv_okd_weaken (c_init_done (ctx st0)) m1 (bv_unsigned sp)); [| (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia]. eapply auxv_okd_pres; [exact AUX| exact PE1| |].
    - intros a Ha. apply ta_fp_not_high. exact Ha.
    - intros a Ha. apply ta_fp_not_image; unfold AUXV_CELL, CTX in *; lia. }
  assert (ERR2 : rw_cells rsegs m1 (errno_addr tp) [C4 errv]).
  { eapply pres_except_rw_cells; [exact PE1| exact ERR|]. rewrite EA. cbn. intros a Ha. apply ta_fp_not_image; [lia| unfold CTX; lia]. }
  assert (DI1 : c_init_done (ctx st0) <> 0 -> c_init_done (ctx st1) <> 0).
  { intros H0. (first [ pose proof ((tr_ctx _ _ _ TR)) as dR_18; dand3 dR_18 as _ EI _ | destruct (tr_ctx _ _ _ TR) as (_ & EI & _) ]). rewrite EI. exact (InitMono.ist_init_done st0 LB st AR IS H0). }
  eapply (ralloc_meta_stmtL am_pre AM) with (lo := lo) (d := c_init_done (ctx st0));
    [ exact (AMP st0 LB st sc st1 AR IS SC TF) | exact MR1 | exact TK1 | exact BL1 | rewrite unsigned_lit by lia; exact AUX2 | exact DI1
    | rewrite unsigned_lit by lia; exact ST1 | exact CLO
    | rewrite unsigned_lit by lia; unfold AM_STACK; lia | exact ERR2 | exact MI1 | exact TP |].
  intros st2 mo s' ms' PO BL2 LF.
  (first [ dex16 PO as u0 u1 u2 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 m3 errv3; dand12 PO as -> MI3 ST3 ERR3 AUX3 PE3 MR3 TK3 PSM PSF PSO REL | dand28 PO as u0 u1 u2 w1 w2 w3 w4 w5 w6 w7 u3 u4 u5 u6 m3 errv3 -> MI3 ST3 ERR3 AUX3 PE3 MR3 TK3 PSM PSF PSO REL | destruct PO as (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m3 & errv3 & -> & MI3 & ST3 & ERR3 & AUX3 & PE3 & MR3 & TK3 & PSM & PSF & PSO & REL) ]).
  rewrite unsigned_lit in ST3, AUX3, PE3 by lia.
  replace (ret_pc (Z_to_bv 64 0x2425c)) with (Z_to_bv 64 0x2425c) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  pose proof MR3 as (WF3 & _). (first [ pose proof (WF3) as dR_20; dand4 dR_20 as RS3 WR3 DJ3 _ | pose proof WF3 as (RS3 & WR3 & DJ3 & _) ]).
  (* [comment removed for export] *)
  assert (OUT3 : forall a, bv_unsigned sp - 144 <= a \/ (0x10000 <= a < 0x64000 /\ ~ (CTX <= a < CTX + 928) /\ ~ (0x42454 <= a < 0x42458)) ->
            ~ (alloc_fp (fun k => k <> RKGroup) st2 lo (bv_unsigned sp + -144) a \/ fresh_addr st1 a)).
  { intros a Ha [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
    - lia.
    - rewrite unsigned_lit in X by lia. lia.
    - unfold CTX in *. lia.
    - (first [ pose proof ((WR3 _ _ Hq')) as dR_21; dand5 dR_21 as B0 _ _ BC RF' | destruct (WR3 _ _ Hq') as (B0 & _ & _ & BC & RF') ]). pose proof (lr_lo_ge rq2). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      (first [ pose proof ((reserved_disjoint _ _ RF')) as dR_22; dand4 dR_22 as D1 D2 D3 D4 | pose proof (reserved_disjoint _ _ RF') as (D1 & D2 & D3 & D4) ]). pose proof (round_up_pg_ge (r_len rq2)). lia.
    - destruct X as [XC XF]. (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      pose proof (fresh_image (Clg:=Clg) st1 a (conj XC XF) ltac:(rewrite (tr_reserved _ _ _ TR); exact RS)). lia. }
  assert (FR3 : rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM junk)).
  { eapply pres_except_rw_cells; [exact PE3| exact FR1|]. intros a Ha. apply OUT3. left. unfold rFRM, ta_frame in Ha. cbn in Ha. lia. }
  (* [comment removed for export] *)
  assert (REL02 : mrel st st2).
  { split; [| rewrite <- (tr_next _ _ _ TR); apply (amr_next_rid _ _ _ REL)| rewrite (amr_reserved _ _ _ REL); apply (tr_reserved _ _ _ TR)].
    intros rid r Hr. rewrite <- REG1 in Hr. (first [ pose proof ((amr_regions _ _ _ REL rid r Hr)) as dR_23; dex1 dR_23 as r'; dand5 dR_23 as H' K' B' L' _ | pose proof ((amr_regions _ _ _ REL rid r Hr)) as dR_23; dand6 dR_23 as r' H' K' B' L' _ | destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & B' & L' & _) ]). exists r'. auto. }
  assert (AREAS2 : forall q, meta_slot st q -> meta_slot st2 q).
  { (intros q; (first [ intro dR_34; dex3 dR_34 as ar arr kk; dand3 dR_34 as Ha Hk E | intro dR_34; dand6 dR_34 as ar arr kk Ha Hk E | intros (ar & arr & kk & Ha & Hk & E) ])). destruct (amr_areas _ _ _ REL ar ltac:(rewrite (tr_areas _ _ _ TR), Ha; eexists; reflexivity)) as [arr' Ha'].
    exists ar, arr', kk. auto. }
  assert (PE03 : pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m3).
  { eapply pres_except_trans.
    - eapply pres_except_mono; [exact PE1|]. intros a Ha. eapply (ta_fp_malloc_fp st2 m3); [exact MR3| exact REL02| exact AREAS2| exact Ha].
    - eapply pres_except_mono; [exact PE3|]. intros a [[X|[X|[X|X]]]|X].
      + left. left. lia. + left. right. left. exact X. + left. right. right. left. exact X. + left. right. right. right. exact X.
      + do 4 right. eapply (fresh_addr_anti st0 st1); [| | exact X].
        * rewrite (tr_reserved _ _ _ TR). destruct ER as [_ _ _ EM _ _ _ _]. apply (mrel_reserved _ _ EM).
        * intros rid r Hr. destruct ER as [_ _ _ EM _ _ _ _]. (first [ pose proof ((mrel_regions _ _ EM rid r Hr)) as dR_24; dex1 dR_24 as r'; dand4 dR_24 as H' K' B' L' | pose proof ((mrel_regions _ _ EM rid r Hr)) as dR_24; dand5 dR_24 as r' H' K' B' L' | destruct (mrel_regions _ _ EM rid r Hr) as (r' & H' & K' & B' & L') ]). exists r'. rewrite REG1. auto. }
  (* [comment removed for export] *)
  assert (UA3 : unk_agree st2 o m3).
  { eapply (unk_agree_keep st2 m3).
    - rewrite (amr_shadow _ _ _ REL). apply (tr_shadow _ _ _ TR).
    - intros rid r Hk Hr. rewrite <- REG1. destruct ((s_regions st1) !! rid) as [r0|] eqn:E0.
      + (first [ pose proof ((amr_regions _ _ _ REL rid r0 E0)) as dR_25; dex1 dR_25 as r'; dand5 dR_25 as H' K' _ _ G' | pose proof ((amr_regions _ _ _ REL rid r0 E0)) as dR_25; dand6 dR_25 as r' H' K' _ _ G' | destruct (amr_regions _ _ _ REL rid r0 E0) as (r' & H' & K' & _ & _ & G') ]). rewrite Hr in H'. inversion H'; subst r'. rewrite (G' ltac:(rewrite <- K'; exact Hk)). reflexivity.
      + exfalso. exact (amr_new _ _ _ REL rid r Hr E0 Hk).
    - intros b. rewrite (amr_groups _ _ _ REL). apply (tr_groups _ _ _ TR).
    - intros rid r off h Hr Hk Ho Hc NG.
      (first [ pose proof ((WR _ _ Hr)) as dR_26; dand5 dR_26 as R0 _ _ RC _ | destruct (WR _ _ Hr) as (R0 & _ & _ & RC & _) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
      transitivity (m1 (wa (r_base r + off))).
      + refine (proj1 (PE3 (r_base r + off) ltac:(lia) _)). intros [[X|[X|[X|(q2 & rq2 & Hq' & Kq2 & Xa)]]]|X].
        * lia.
        * rewrite unsigned_lit in X by lia. (first [ pose proof ((rregion_facts st m rid r MR Hr)) as dR_27; dand5 dR_27 as _ _ _ RI1 RI2 | destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2) ]).
          specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). lia.
        * (first [ pose proof ((rregion_facts st m rid r MR Hr)) as dR_28; dand5 dR_28 as _ _ _ RI1 RI2 | destruct (rregion_facts st m rid r MR Hr) as (_ & _ & _ & RI1 & RI2) ]). specialize (RI1 ltac:(lia)). specialize (RI2 ltac:(lia)). unfold CTX in X. lia.
        * assert (Hr2 : (s_regions st2) !! rid = Some r).
          { rewrite <- REG1 in Hr. (first [ pose proof ((amr_regions _ _ _ REL rid r Hr)) as dR_29; dex1 dR_29 as r'; dand5 dR_29 as H' K' _ _ G' | pose proof ((amr_regions _ _ _ REL rid r Hr)) as dR_29; dand6 dR_29 as r' H' K' _ _ G' | destruct (amr_regions _ _ _ REL rid r Hr) as (r' & H' & K' & _ & _ & G') ]). rewrite H'. f_equal. apply G'. exact Hk. }
          assert (NE : q2 <> rid) by (intros ->; rewrite Hr2 in Hq'; inversion Hq'; subst; exact (Kq2 Hk)).
          pose proof (lr_lo_group r Hk). destruct (DJ3 _ _ _ _ Hq' Hr2 NE); lia.
        * rewrite <- REG1 in Hr. pose proof (fresh_live_region st1 _ rid r X Hr) as Y. pose proof (lr_lo_group r Hk). lia.
      + refine (proj1 (PE1 (r_base r + off) ltac:(lia) _)). apply (ta_fp_not_inband rid r off Hr Hk Ho NG). }
  destruct mo as [mm|].
  - (* [comment removed for export] *)
    destruct (amr_result _ _ _ REL mm eq_refl) as [G0 MSL].
    (first [ pose proof ((meta_slot_bounds st2 m3 mm MR3 MSL)) as dR_30; dand3 dR_30 as Gpos GC _ | pose proof (meta_slot_bounds st2 m3 mm MR3 MSL) as (Gpos & GC & _) ]).
    iprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply ag_ret_walk with (gm := conc st2 mm); [(let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv); lia| exact MI3]. }
    cbv beta. intros ms' ->. replace (conc st2 mm =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    apply evt_done.
    eapply (HAG st1 st2 mm m3 s'); try eassumption.
    + eapply ist_am; [exact IS| exact SC| exact TF| exact LF].
    + eapply ER_am; [eapply ER_ta; [exact ER| exact TR]| exact REL| exact LF].
    + eapply ALLC_am; [exact REL|]. eapply ALLC_ta; [exact TR| exact AC].
    + eapply (auxv_okd_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia].
  - (* [comment removed for export] *)
    cbn iota.
    iprefixT. eapply evt_cut.
    { unfold pw. cbn [oconc]. unfold wz. eapply ag_ret_walk with (gm := 0); [lia| exact MI3]. }
    cbv beta. intros ms' ->. cbn [Z.eqb].
    eapply evt_cut. { unfold rFRM in FR3. eapply (ras_ret0 sp gp tp); [exact MR3| exact MI3| exact FR3| exact ST3| exact CLO| lia]. }
    cbv beta. (intros ms'; (first [ intro dR_35; dex2 dR_35 as a1x a2x; destruct dR_35 as [-> ST4] | intro dR_35; dand4 dR_35 as a1x a2x -> ST4 | intros (a1x & a2x & -> & ST4) ])). apply evt_done.
    apply HK. unfold as_post2.
    do 14 eexists. exists m3, errv3. split; [reflexivity|].
    split; [exact MI3|]. split; [exact ST4|]. split; [exact ERR3|].
    split. { eapply (auxv_okd_malloc_fp_ER st0 st m MR ER st2 m3); [exact MR3| exact AUX| exact PE03| exact CLO| lia]. }
    split; [exact MR3|]. split; [exact TK3|]. split; [exact UA3|]. split; [exact PE03|].
    split; [exact REL02|]. split; [exact BL2|]. split; [exact PSM|]. split; [exact PSF|]. split; [exact PSO|].
    split. { constructor.
      - intros c Hc. rewrite (amr_active _ _ _ REL). apply (tr_active _ _ _ TR). lia.
      - intros a Ha. apply (amr_areas _ _ _ REL). rewrite (tr_areas _ _ _ TR). exact Ha.
      - rewrite (amr_tick _ _ _ REL). apply (tr_tick _ _ _ TR).
      - intros H; exfalso; lia.
      - intros _ H; exfalso; lia. }
    split. { rewrite (amr_counter _ _ _ REL). unfold ctx. (first [ pose proof ((tr_ctx _ _ _ TR)) as dR_31; dand4 dR_31 as _ _ CC _ | destruct (tr_ctx _ _ _ TR) as (_&_&CC&_) ]). unfold ctx in CC. rewrite CC.
             pose proof (mf_ctx _ _ MF) as (X & _). exact X. }
    left. reflexivity.
Qed.
End LEVEL.
End RASljm5.


Module RASlxag.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASl0ja OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RAlllfc RASlot_I.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASl8dw.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlh1b OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASl0ja OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASljm5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall8ro.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import F_sy88u MRep MRepAux RAlllfc Malllim.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Lemma halve_big_pos F : forall cnt sz, 1 <= cnt -> 0 <= sz < 2^18 -> 1 <= halve_big F cnt sz.
Proof.
  induction F as [|F IH]; intros cnt sz Hc Hs; cbn [halve_big]; [lia|].
  destruct (Z.leb_spec (65536 * UNIT) (sz * cnt)) as [LE|GT]; [|lia].
  apply IH; [|lia]. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 1) with 2. unfold UNIT in LE.
  assert (2 <= cnt) by nia. Z.div_mod_to_equations. lia.
Qed.

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

(* [comment removed for export] *)
Definition ag_ctx (st1 st2 : mstate) (mm : aptr) (m3 : mem) (s' : PState) (errv' : word) (junk : list byte) (oo : mem) : Prop :=
  ta_fail sc st st1 /\ ta_rel sc st st1 /\ active st1 sc = None /\
  leaf_of oo (alloc_meta st1 kS bS) (Some (st2, Some mm)) /\
  IST st0 st2 /\ ENTRY_REL st0 st2 /\ ALLC st2 /\
  am_rel st1 st2 (Some mm) /\ get_meta_rec st2 mm = meta0 /\ meta_slot st2 mm /\
  mrep st2 m3 /\ ticks_ok st2 /\ unk_agree st2 o m3 /\ mem_inv rsegs m3 /\ stk rsegs m3 lo (bv_unsigned sp + -144) /\
  rw_cells rsegs m3 (bv_unsigned sp + -144) (rFRM ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 junk) /\
  rw_cells rsegs m3 (errno_addr tp) [C4 errv'] /\ auxv_okd (c_init_done (ctx st0)) m3 (bv_unsigned sp) /\
  pres_except (malloc_fp st0 st2 lo (bv_unsigned sp)) m m3 /\
  brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s.

(* [comment removed for export] *)
Definition rcnt_state (pc : Z) (st2 : mstate) (mm : aptr) (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word) (m3 : mem) : machine_state :=
  MS (mkR (Z_to_bv 64 0x2425c) (Z_to_bv 64 (bv_unsigned sp + -144)) gp tp t0' t1' t2' (Z_to_bv 64 sc) (Z_to_bv 64 (conc st2 mm))
          (wz (usage st2 sc)) (wz 4096) (wz (size_class sc * UNIT + 16)) (wz 2048) (wz (size_class sc * UNIT * cnt1)) (wz (size_class sc * UNIT * cnt1 + 16)) a6' a7'
          a1 (wz cnt1) (Z_to_bv 64 SSP_GUARD) (Z_to_bv 64 (CTX + 80 + 8 * sc)) (Z_to_bv 64 MLOCK) (Z_to_bv 64 (MLOCK + 8 * sc))
          (wz (size_class sc * UNIT)) (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3' t4' t5' t6')
     F (Z_to_bv 64 pc) fc None m3 (seg_rom rsegs).

Definition HMM_stmt : Prop :=
  forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
  ag_ctx st1 st2 mm m3 s' errv' junk oo ->
  1 <= cnt1 <= 32 -> 2048 < size_class sc * UNIT * cnt1 + UNIT ->
  implT o (ag_mmap sc req k bail st2 mm cnt1) s' Q (rcnt_state 0x24330 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Definition HNEST_stmt : Prop :=
  forall st1 st2 mm m3 s' errv' junk oo (cnt1 : Z) (t0' t1' t2' a6' a7' t3' t4' t5' t6' : word),
  ag_ctx st1 st2 mm m3 s' errv' junk oo ->
  1 <= cnt1 <= 32 -> size_class sc * UNIT * cnt1 + UNIT <= 2048 ->
  implT o (ag_nest f sc k bail st2 mm cnt1) s' Q (rcnt_state 0x24374 st2 mm cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' m3).

Hypothesis HMM : HMM_stmt.
Hypothesis HNEST : HNEST_stmt.

Lemma hag_ok : HAG_stmt f k bail o s Q ra sp gp tp s0 s1 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m st0 st lo sc req.
Proof.
  intros st1 st2 mm m3 s' errv' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' junk oo.
  intros TF TR ACT0 LF IS2 ER2 AC2 REL G0 MSL MR3 TK3 UA3 MI3 ST3 FR3 ERR3 AUX3 PE03 BL2 PSM PSF PSO.
  assert (CTXT : ag_ctx st1 st2 mm m3 s' errv' junk oo) by (repeat (split; [assumption|]); assumption).
  pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2^64) in SPR.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  pose proof (Mall8ro.ist_facts_proof st0 LB st2 AR IS2) as F2. pose proof (isf_mf _ _ F2) as MF2.
  pose proof (mf_usage _ _ MF2 sc) as UR. change (usage (strip st2) sc) with (usage st2 sc) in UR.
  pose proof (size_class_range sc SC) as SZR.
  rewrite (ag_body_eq f sc req k bail st2 mm).
  iprefixT. unfold rag_regs.
  eapply evt_cut.
  { eapply (count_walk st2 m3 sc MR3 SC UR). exact MI3. }
  cbv beta. intros ms' (a2'' & a3'' & a4'' & ->).
  set (size := size_class sc * UNIT).
  set (cnt0 := if sc <? 9 then small_cnt_pick sc (usage st2 sc) else halve_big 8 (halve_even 8 (med_cnt (Z.land sc 3)) (usage st2 sc)) size).
  assert (C0R : 1 <= cnt0 <= 32).
  { pose proof (cnt0_range st2 sc SC) as X. change (1 <= cnt0 <= 32). split; [| apply X].
    subst cnt0. destruct (Z.ltb_spec sc 9).
    - unfold small_cnt_pick. pose proof (small_cnt_range sc 0). pose proof (small_cnt_range sc 1). pose proof (small_cnt_range sc 2).
      destruct (negb _); [lia|]. destruct (negb _); lia.
    - apply halve_big_pos; [| subst size; unfold UNIT; lia]. pose proof (med_cnt_range (Z.land sc 3) ltac:(pose proof (land3_range sc); lia)) as [MC _].
      pose proof (halve_even_range 8 (med_cnt (Z.land sc 3)) (usage st2 sc) ltac:(lia)). lia. }
  eapply evt_cut.
  { eapply (cnt2_walk (usage st2 sc) size cnt0); [subst size; unfold UNIT; lia| lia| exact MI3]. }
  cbv beta. intros ms' ->. unfold cnt_regs.
  set (cnt1 := if (cnt0 =? 1) && (size * cnt0 + UNIT <=? PGSZ / 2) then 2 else cnt0) in *.
  assert (C1R : 1 <= cnt1 <= 32) by (subst cnt1; destruct (_ && _); lia).
  assert (EC : ag_cnt1 sc st2 = cnt1).
  { unfold ag_cnt1. subst cnt1 cnt0 size. rewrite (Z.mul_comm UNIT (size_class sc)). reflexivity. }
  rewrite EC. replace (UNIT * size_class sc * cnt1) with (size * cnt1) by (subst size; lia).
  apply evt_done.
  destruct (Z.ltb_spec (PGSZ / 2) (size * cnt1 + UNIT)) as [BIG|SMALLc].
  - pose proof (HMM st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in BIG; cbn in BIG; subst size; lia)) as X.
    unfold rcnt_state in X. subst size. unfold UNIT in X |- *. replace (size_class sc * 16 * cnt1 + 16) with (size_class sc * 16 * cnt1 + 16) in X by lia. exact X.
  - pose proof (HNEST st1 st2 mm m3 s' errv' junk oo cnt1 t0' t1' t2' a6' a7' t3' t4' t5' t6' CTXT C1R ltac:(unfold PGSZ in SMALLc; cbn in SMALLc; subst size; lia)) as X.
    unfold rcnt_state in X. subst size. unfold UNIT in X |- *. exact X.
Qed.
End LEVEL.
End RASlxag.


Module ASlojxo.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_sy88u MRep MRepAux MRepAux MRepAux RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallkgx Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallmv3 Malls02.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malluin RASlh4s RASla24.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RF_m79e.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma pos_iter_slots' (m p : aptr) (stride : Z) : forall n tb,
  0 < stride ->
  let F := fun acc : Z * gmap aptr (aptr * Z) => let (i, t) := acc in (i + 1, <[aadd p (UNIT + stride * i) := (m, i)]> t) in
  fst (Pos.iter F (0, tb) n) = Z.pos n
  /\ (snd (Pos.iter F (0, tb) n)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (snd (Pos.iter F (0, tb) n)) !! q <> None -> tb !! q <> None \/ exists i, 0 <= i < Z.pos n /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros n tb HS F. induction n as [|n IH] using Pos.peano_ind.
  - cbn [Pos.iter]. unfold F. rewrite Z.mul_0_r, Z.add_0_r. split; [reflexivity|]. split; [apply lookup_insert_eq|].
    intros q Hq. destruct (decide (q = aadd p UNIT)) as [->|NE]; [right; exists 0; rewrite Z.mul_0_r, Z.add_0_r; split; [lia| reflexivity]|].
    left. rewrite lookup_insert_ne in Hq by congruence. exact Hq.
  - rewrite Pos.iter_succ. (first [ dand3 IH as I1 I2 I3 | destruct IH as (I1 & I2 & I3) ]). fold F. destruct (Pos.iter F (0, tb) n) as [i t] eqn:EP. cbn [fst snd] in I1, I2, I3 |- *.
    unfold F at 1. unfold F at 1. unfold F at 1. cbn [fst snd]. subst i.
    split; [lia|]. split.
    + rewrite lookup_insert_ne; [exact I2|]. unfold aadd. intros E. apply (f_equal snd) in E. cbn in E. unfold UNIT in E. nia.
    + intros q Hq. destruct (decide (q = aadd p (UNIT + stride * Z.pos n))) as [->|NE].
      * right. exists (Z.pos n). split; [lia| reflexivity].
      * rewrite lookup_insert_ne in Hq by congruence. destruct (I3 q Hq) as [X|(i & Hi & ->)]; [left; exact X| right; exists i; split; [lia| reflexivity]].
Qed.

Lemma add_slots_first' m p stride c st : 1 <= c -> 0 < stride ->
  (s_slots (add_slots m p stride c st)) !! (aadd p UNIT) = Some (m, 0)
  /\ (forall q, (s_slots (add_slots m p stride c st)) !! q <> None -> (s_slots st) !! q <> None \/ exists i, 0 <= i < c /\ q = aadd p (UNIT + stride * i)).
Proof.
  intros Hc HS. unfold add_slots. cbn [s_slots set_slots].
  destruct c as [|n|n]; [lia| |lia]. cbn [Z.iter].
  (first [ pose proof ((pos_iter_slots' m p stride n (s_slots st) HS)) as dR_2; dand3 dR_2 as _ A B | destruct (pos_iter_slots' m p stride n (s_slots st) HS) as (_ & A & B) ]). split; [exact A| exact B].
Qed.

Lemma mask_upto_range' k : 0 <= k <= 31 -> 1 <= mask_upto k < 2^32 /\ 2^k <= mask_upto k.
Proof.
  intros Hkk. unfold mask_upto. rewrite Z.pow_add_r by lia. change (2^1) with 2.
  assert (1 <= 2^k) by (change 1 with (2^0); apply Z.pow_le_mono_r; lia).
  assert (2^k <= 2^31) by (apply Z.pow_le_mono_r; lia).
  change (2^32) with (2 * 2^31). lia.
Qed.

(* [comment removed for export] *)
Lemma put_meta_wr8_comm mt r q v st : put_meta mt r (wr8 q v st) = wr8 q v (put_meta mt r st).
Proof. destruct st; reflexivity. Qed.
Lemma put_meta_zero_hdrs_comm mt r p size : forall k i st,
  put_meta mt r (zero_hdrs p size i k st) = zero_hdrs p size i k (put_meta mt r st).
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH, put_meta_wr8_comm. reflexivity. Qed.
Lemma rec_zero_hdrs p size q : forall k i st, get_meta_rec (zero_hdrs p size i k st) q = get_meta_rec st q.
Proof. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|]. rewrite IH. destruct st; reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SMG.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (stT : mstate) (sc cnt ai ml : Z) (mt p : aptr).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 0 <= ml.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis P0 : 0 <= snd p.

Definition sm_rec : meta :=
  mkMeta (Some mt) (Some mt) (Some p) (mask_upto ai - 1) (mask_upto (cnt - 1) - mask_upto ai) (cnt - 1) 1 sc ml.

Lemma smg_proj :
  s_regions stF = s_regions stT /\ s_shadow stF = s_shadow (hdr_havoc p stT)
  /\ s_groups stF = <[p := mkGhdr (Some mt) (Z.land ai 31)]> (s_groups stT)
  /\ s_areas stF = s_areas stT /\ s_tick stF = s_tick stT /\ s_next_rid stF = s_next_rid stT /\ s_reserved stF = s_reserved stT
  /\ c_brk (ctx stF) = c_brk (ctx stT) /\ c_mmap_counter (ctx stF) = c_mmap_counter (ctx stT)
  /\ c_free_meta_head (ctx stF) = c_free_meta_head (ctx stT).
Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

Lemma smg_rec_mt : get_meta_rec stF mt = sm_rec.
Proof.
  unfold stF. rewrite (st_model_eq_rec stT sc cnt ai ml mt p SC CNT REC P0).
  unfold stFin, stE. rewrite rec_set_active, get_meta_rec_put_same. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma smg_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof.
  unfold stF, st_model. cbv zeta. rewrite active_set_active. destruct (c =? sc); [reflexivity|].
  rewrite !active_upd_meta. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma smg_stride : get_stride sm_rec = if (cnt =? 1) && negb (ml =? 0) then ml * 4096 - 16 else 16 * size_class sc.
Proof.
  unfold get_stride, sm_rec. cbn [m_last_idx m_maplen m_sizeclass].
  replace (cnt - 1 =? 0) with (cnt =? 1) by (destruct (Z.eqb_spec cnt 1); destruct (Z.eqb_spec (cnt - 1) 0); try reflexivity; lia).
  unfold UNIT. reflexivity.
Qed.

Lemma smg_slot0 : 0 < get_stride sm_rec -> (s_slots stF) !! (fst p, snd p + 16) = Some (mt, 0).
Proof.
  intros HS. unfold stF, st_model. cbv zeta.
  match goal with |- s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ ?X))) !! _ = _ =>
    change (s_slots (set_active _ _ (upd_meta _ _ (upd_meta _ _ X)))) with (s_slots X) end.
  match goal with |- s_slots (add_slots mt p ?s cnt ?X) !! _ = _ =>
    replace s with (get_stride sm_rec) end.
  2:{ unfold upd_meta. rewrite rec_put_group, get_meta_rec_put_same, rec_set_usage, rec_hdr_havoc, REC. unfold get_stride, sm_rec.
      cbn [m_last_idx m_maplen m_sizeclass m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      replace (Z.land (cnt - 1) 31) with (cnt - 1) by (change 31 with (Z.ones 5); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
      replace (Z.land sc 63) with sc by (change 63 with (Z.ones 6); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
      reflexivity. }
  change (fst p, snd p + 16) with (aadd p UNIT).
  apply (proj1 (add_slots_first' mt p (get_stride sm_rec) cnt _ ltac:(lia) HS)).
Qed.

Lemma smg_shadow_other q : q <> fst p -> get_shadow stF q = get_shadow stT q.
Proof.
  intros NE. unfold get_shadow. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma smg_shadow_p :
  get_shadow stF (fst p) = mkShadow (r_cells (get_shadow stT (fst p)))
                             (<[snd p / 16 := hav_add 12 (s_tick stT) (default [] ((r_hav (get_shadow stT (fst p))) !! (snd p / 16)))]> (r_hav (get_shadow stT (fst p))))
                             (r_havp (get_shadow stT (fst p))).
Proof.
  unfold get_shadow at 1. rewrite (proj1 (proj2 smg_proj)). unfold hdr_havoc, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. reflexivity.
Qed.

Lemma smg_group_p : (s_groups stF) !! p = Some (mkGhdr (Some mt) (Z.land ai 31)).
Proof. rewrite (proj1 (proj2 (proj2 smg_proj))). apply lookup_insert_eq. Qed.

Lemma smg_groups_inv b' gh : (s_groups stF) !! b' = Some gh -> (b' = p /\ gh = mkGhdr (Some mt) (Z.land ai 31)) \/ (b' <> p /\ (s_groups stT) !! b' = Some gh).
Proof.
  rewrite (proj1 (proj2 (proj2 smg_proj))). intros H. destruct (decide (b' = p)) as [->|NE].
  - left. rewrite lookup_insert_eq in H. inversion H. auto.
  - right. rewrite lookup_insert_ne in H by congruence. auto.
Qed.

Lemma smg_groups_old b' gh : (s_groups stT) !! p = None -> (s_groups stT) !! b' = Some gh -> (s_groups stF) !! b' = Some gh.
Proof.
  intros GN H. rewrite (proj1 (proj2 (proj2 smg_proj))). rewrite lookup_insert_ne; [exact H|]. intros ->. rewrite GN in H. discriminate.
Qed.

Lemma smg_grp_hdr_cov off : snd p <= off < snd p + 12 -> grp_hdr_cov stF (fst p) off.
Proof. intros Ho. exists p, (mkGhdr (Some mt) (Z.land ai 31)). split; [exact smg_group_p|]. split; [reflexivity| lia]. Qed.

Lemma smg_grp_hdr_cov_old q off : (s_groups stT) !! p = None -> grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. (intros GN; (first [ intro dR_5; dex2 dR_5 as b' gh; dand3 dR_5 as Hb Hf Ho | intro dR_5; dand5 dR_5 as b' gh Hb Hf Ho | intros (b' & gh & Hb & Hf & Ho) ])). exists b', gh. split; [apply smg_groups_old; assumption| auto]. Qed.

Lemma smg_conc q : conc stF q = conc stT q.
Proof. unfold conc, get_region. rewrite (proj1 smg_proj). reflexivity. Qed.

Lemma smg_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. split; intros H; (eapply meta_slot_same_areas; [| exact H]); rewrite (proj1 (proj2 (proj2 (proj2 smg_proj)))); reflexivity. Qed.

(* [comment removed for export] *)
Lemma smg_ret_span rid' S len :
  (exists g b, active stF sc = Some g /\ m_mem (get_meta_rec stF g) = Some b /\ rid' = fst b
     /\ S = snd b + 16 + get_stride (get_meta_rec stF g) * 0 /\ len = get_stride (get_meta_rec stF g) - 4) ->
  rid' = fst p /\ S = snd p + 16 /\ len = get_stride sm_rec - 4.
Proof.
  ((first [ intro dR_6; dex2 dR_6 as g b; dand5 dR_6 as HA HM -> -> -> | intro dR_6; dand7 dR_6 as g b HA HM -> -> -> | intros (g & b & HA & HM & -> & -> & ->) ])). rewrite smg_active, Z.eqb_refl in HA. inversion HA; subst g.
  rewrite smg_rec_mt in HM |- *. cbn in HM. inversion HM; subst b. split; [reflexivity| split; [lia| reflexivity]].
Qed.
End SMG.

Lemma Zle_1_nonneg' x : 1 <= x < 2^28 -> 0 <= x /\ True.
Proof. intros H. split; [lia| exact I]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SM.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (stT : mstate) (sc cnt ai ml : Z) (mt : aptr) (rid : N) (r0 : region).
Let p : aptr := (rid, 0).
Let stF := st_model stT sc cnt ai mt p.
Hypothesis SC : 0 <= sc < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis AI : 0 <= ai <= cnt - 1.
Hypothesis ML : 1 <= ml < 2^28.
Hypothesis REC : get_meta_rec stT mt = mkMeta None None None 0 0 0 0 0 ml.
Hypothesis HrT : (s_regions stT) !! rid = Some r0.
Hypothesis Hk0 : r_kind r0 = RKGroup.
Hypothesis SHT : (s_shadow stT) !! rid = None.
Hypothesis GNT : forall off, (s_groups stT) !! (rid, off) = None.

Let P0 : 0 <= snd p := Z.le_refl 0.
Let ML0 : 0 <= ml := proj1 (Zle_1_nonneg' ml ML).


Lemma sm_proj :
  s_regions stF = s_regions stT /\ s_shadow stF = s_shadow (hdr_havoc p stT)
  /\ s_groups stF = <[p := mkGhdr (Some mt) (Z.land ai 31)]> (s_groups stT)
  /\ s_areas stF = s_areas stT /\ s_tick stF = s_tick stT /\ s_next_rid stF = s_next_rid stT /\ s_reserved stF = s_reserved stT
  /\ c_brk (ctx stF) = c_brk (ctx stT) /\ c_mmap_counter (ctx stF) = c_mmap_counter (ctx stT)
  /\ c_free_meta_head (ctx stF) = c_free_meta_head (ctx stT).
Proof. exact (smg_proj stT sc cnt ai mt p). Qed.

Lemma sm_rec_mt : get_meta_rec stF mt = sm_rec sc cnt ai ml mt p.
Proof. apply (smg_rec_mt stT sc cnt ai ml mt p); assumption. Qed.

Lemma sm_active c : active stF c = if c =? sc then Some mt else active stT c.
Proof. exact (smg_active stT sc cnt ai mt p c). Qed.

Lemma sm_ml_nz : (ml =? 0) = false.
Proof. apply Z.eqb_neq. lia. Qed.

Lemma sm_stride : get_stride (sm_rec sc cnt ai ml mt p) = if cnt =? 1 then ml * 4096 - 16 else 16 * size_class sc.
Proof. rewrite (smg_stride sc cnt ai ml mt p) by assumption. rewrite sm_ml_nz, andb_true_r. reflexivity. Qed.

Lemma sm_slot0 : 0 < get_stride (sm_rec sc cnt ai ml mt p) -> (s_slots stF) !! (rid, 16) = Some (mt, 0).
Proof. intros HS. apply (smg_slot0 stT sc cnt ai ml mt p); assumption. Qed.

(* [comment removed for export] *)
Lemma sm_cell_read off : 0 <= off -> cell_read (get_shadow stF rid) off = if off <? 12 then Unknown 0 else Known 0.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  intros Ho. unfold get_shadow. rewrite (proj1 (proj2 sm_proj)). fold (get_shadow (hdr_havoc p stT) rid).
  apply cell_read_hh0; [exact SHT| exact Ho].
Qed.

Lemma sm_cells_none off : (r_cells (get_shadow stF rid)) !! off = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_cells]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_hav_none off : 16 <= off -> (r_hav (get_shadow stF rid)) !! (off / 16) = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. intros Ho. change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_hav]. unfold p. cbn [fst snd]. change (0 / 16) with 0.
  rewrite lookup_insert_ne by (Z.div_mod_to_equations; lia). unfold get_shadow. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_havp_none k : (r_havp (get_shadow stF rid)) !! k = None.
Proof.
  clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT.
  change rid with (fst p). rewrite (smg_shadow_p stT sc cnt ai mt p). cbn [r_havp]. unfold p, get_shadow. cbn [fst]. rewrite SHT. cbn. apply lookup_empty.
Qed.

Lemma sm_shadow_other q : q <> rid -> get_shadow stF q = get_shadow stT q.
Proof. intros NE. exact (smg_shadow_other stT sc cnt ai mt p q NE). Qed.

Lemma sm_groups_rid off gh : (s_groups stF) !! (rid, off) = Some gh -> off = 0 /\ gh = mkGhdr (Some mt) (Z.land ai 31).
Proof.
  intros H. destruct (smg_groups_inv stT sc cnt ai mt p _ _ H) as [[E ->]|[NE H']].
  - unfold p in E. inversion E. auto.
  - rewrite GNT in H'. discriminate.
Qed.

Lemma sm_grp_hdr_cov off : 0 <= off < 12 -> grp_hdr_cov stF rid off.
Proof. clear ML0 P0 CNT AI ML REC HrT Hk0 GNT SHT. intros Ho. apply (smg_grp_hdr_cov stT sc cnt ai mt p SC off). cbn. lia. Qed.

Lemma sm_grp_hdr_cov_old q off : grp_hdr_cov stT q off -> grp_hdr_cov stF q off.
Proof. intros H. exact (smg_grp_hdr_cov_old stT sc cnt ai mt p P0 q off (GNT 0) H). Qed.

Lemma sm_conc q : conc stF q = conc stT q.
Proof. exact (smg_conc stT sc cnt ai mt p q). Qed.

Lemma sm_meta_slot q : meta_slot stT q <-> meta_slot stF q.
Proof. exact (smg_meta_slot stT sc cnt ai mt p q). Qed.

Lemma sm_rdv o : rdv pans_mem o stF (rid, 13) = 0.
Proof. clear ML0 P0 SC CNT AI ML REC HrT Hk0 GNT. unfold rdv. cbn [fst snd]. rewrite sm_cell_read by lia. reflexivity. Qed.

Lemma sm_stride_mod16 : get_stride (get_meta_rec stF mt) mod 16 = 0.
Proof.
  rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1).
  - replace (ml * 4096 - 16) with ((256 * ml - 1) * 16) by lia. apply Z_mod_mult.
  - rewrite Z.mul_comm. apply Z_mod_mult.
Qed.

(* [comment removed for export] *)
Lemma sm_slot_ok (req nd : Z) :
  0 <= req < 2^32 -> req + 4 <= 16 * size_class sc ->
  r_len r0 = nd -> nd = 4096 * ml -> req + 20 <= nd -> 16 * size_class sc < 2^18 ->
  (cnt = 1 /\ nd < req + 20 + 4096 \/ 16 * size_class sc * cnt + 16 <= nd /\ nd < 16 * size_class sc * cnt + 16 + 4096) ->
  meta_slot stT mt ->
  slot_ok stF mt p r0 0 req
  /\ get_stride (get_meta_rec stF mt) = (if cnt =? 1 then nd - 16 else 16 * size_class sc)
  /\ 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) <= nd.
Proof.
  intros RQ FIT LEN EML NDR SZ NDC MS.
  pose proof (size_class_range sc SC) as SZR.
  assert (RU : round_up_pg nd = nd).
  { rewrite EML. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
    replace (- (4096 * ml)) with ((- ml) * 4096) by lia. rewrite Z_mod_mult. lia. }
  assert (STR : get_stride (get_meta_rec stF mt) = if cnt =? 1 then nd - 16 else 16 * size_class sc).
  { rewrite sm_rec_mt, sm_stride. destruct (cnt =? 1); lia. }
  assert (S20 : 16 <= get_stride (get_meta_rec stF mt) /\ 16 + get_stride (get_meta_rec stF mt) * cnt <= nd
               /\ req + 4 <= get_stride (get_meta_rec stF mt) /\ get_stride (get_meta_rec stF mt) - 4 - req < 2^31
               /\ (forall off, 16 * off + req + 4 <= get_stride (get_meta_rec stF mt) -> off < 65536)).
  { rewrite STR. destruct (Z.eqb_spec cnt 1) as [E1|NE1].
    - rewrite E1. destruct NDC as [[_ X]|[X1 X2]]; (split; [lia|]; split; [lia|]; split; [lia|]; split; [lia|]; intros off Hoff; lia).
    - destruct NDC as [[X _]|[X1 X2]]; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. intros off Hoff. lia. }
  (first [ dand5 S20 as G20 GSP GFIT G31 G18 | destruct S20 as (G20 & GSP & GFIT & G31 & G18) ]).
  pose proof (mask_upto_range' ai ltac:(lia)) as [A1 A2]. pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  assert (AM : mask_upto ai <= mask_upto (cnt - 1)) by (unfold mask_upto; apply Z.sub_le_mono_r; apply Z.pow_le_mono_r; lia).
  split; [| split; [exact STR| split; [exact G20| nia]]].
  constructor.
  - rewrite sm_rec_mt. reflexivity.
  - rewrite (proj1 sm_proj). exact HrT.
  - exact Hk0.
  - unfold p. cbn [snd]. lia.
  - reflexivity.
  - rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - replace (m_last_idx (get_meta_rec stF mt)) with (cnt - 1) by (rewrite sm_rec_mt; reflexivity).
    rewrite LEN, RU. unfold p. cbn [snd]. replace (cnt - 1 + 1) with cnt by lia. lia.
  - exact G20.
  - apply sm_stride_mod16.
  - exact G31.
  - lia.
  - exact GFIT.
  - intros b' gh Hb' Hf. destruct b' as [b1 b2]. unfold p in Hf. cbn in Hf. subst b1. destruct (sm_groups_rid _ _ Hb') as [-> _]. unfold p. cbn [snd]. left. lia.
  - unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0 - 4) with 12 by lia. rewrite sm_cell_read by lia. reflexivity.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. apply G18. exact OF.
  - unfold p. cbn [fst snd]. replace (0 + 16 + get_stride (get_meta_rec stF mt) * 0) with 16 by lia. apply sm_slot0. rewrite <- sm_rec_mt. lia.
  - apply (proj1 (sm_meta_slot mt)). exact MS.
  - rewrite sm_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite sm_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

Lemma sm_ret_span rid' S len :
  (exists g b, active stF sc = Some g /\ m_mem (get_meta_rec stF g) = Some b /\ rid' = fst b
     /\ S = snd b + 16 + get_stride (get_meta_rec stF g) * 0 /\ len = get_stride (get_meta_rec stF g) - 4) ->
  rid' = rid /\ S = 16.
Proof.
  intros H. (first [ pose proof ((smg_ret_span stT sc cnt ai ml mt p SC CNT REC P0 rid' S len H)) as dR_4; dand3 dR_4 as -> -> _ | destruct (smg_ret_span stT sc cnt ai ml mt p SC CNT REC P0 rid' S len H) as (-> & -> & _) ]). unfold p. cbn. split; reflexivity.
Qed.
End SM.
End ASlojxo.

Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.ASlooxi OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASl0ja OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlanm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlx4x OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASl8jf OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASl99y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASl8dw.RASldlz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASljm5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlxag OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.ASlojxo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall8ro.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.

Module RASlku2.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import ImgU.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRepAux MRepAux RF_m8yt RF_egfy MTree Mallwlb.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallkgx Malls02 Malluin Mallkgx Mall17y Mallx0z.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_m8yt OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallx0z.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mall9rj ASlot_W0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RAlllfc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlot_I RASla24.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj.Malli5q OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall9rj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_W0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc.ASlot_W1 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require MRep MRepAux MTree W_ge3a6 Mallkgx Mall1es Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malls02 Mallmv3 RF_egfy RAlllfc RASlot_I Malluin RF_ntf_A.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASlwvv.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.W_ge3a6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallkgx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall1es OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mall17y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RAlllfc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlot_I OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_ntf_A OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlz6s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlwvv.RASlh1b.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_sy88u MRep MRepAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24.RASlico.

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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dieta54.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dieta54.dlia.
(* [comment removed for export] *)

Section ENF.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Variables (st : mstate) (m1 o : mem) (g b : aptr) (r : region) (idx j : Z).
Let mr := get_meta_rec st g.
Let stride := get_stride mr.
Let B := conc st b.
Let P := B + 16 + stride * idx.
Let N := UNIT * size_class j - IB.
Hypothesis MR : mrep st m1.
Hypothesis UA : unk_agree st o m1.
Hypothesis J : 0 <= j < 48.
Hypothesis HA : active st j = Some g.
Hypothesis MSL : meta_slot st g.
Hypothesis MW : mw_ok mr.
Hypothesis SCg : m_sizeclass mr = j.
Hypothesis STR : stride = UNIT * size_class j.
Hypothesis SO : slot_ok st g b r idx N.
Hypothesis TK : ticks_ok st.

(* [comment removed for export] *)
#[using="SO"] Lemma enf_facts : m_mem mr = Some b /\ (s_regions st) !! (fst b) = Some r /\ r_kind r = RKGroup /\ 0 <= snd b /\ snd b mod 16 = 0
  /\ 0 <= idx <= m_last_idx mr /\ m_last_idx mr < 32
  /\ snd b + 16 + stride * (m_last_idx mr + 1) <= round_up_pg (r_len r) /\ 16 <= stride /\ stride mod 16 = 0
  /\ (forall b' gh, (s_groups st) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= snd b + 16 + stride * idx - 4 \/ snd b + 16 + stride * idx + stride - 4 <= snd b')
  /\ cell_read (get_shadow st (fst b)) (snd b + 16 + stride * idx - 4) = Known 0
  /\ (forall off, 0 <= off -> 16 * off + N + 4 <= stride -> (stride * idx + 16 * off) / 16 < 65536).
Proof.
  destruct SO as [Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD S31 N0 NS NOGRP HDR0 Q16 SSL MSL' AVr FRr FBr MPL SCr].
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16 |- *.
  repeat (split; [assumption|]). exact Q16.
Qed.
Definition enf0_st : mstate :=
  wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
    (wr8 (fst b, snd b + (16 + stride * idx) + -3) idx
      (wr16 (fst b, snd b + (16 + stride * idx) + -2) ((snd b + (16 + stride * idx) - (snd b + 16)) / 16) st)).
#[using="SO STR P B r"] Lemma enf0_st_eq : fst (enframe_at st g idx N 0) = enf0_st /\ snd (enframe_at st g idx N 0) = (fst b, snd b + (16 + stride * idx)).
Proof.
  pose proof enf_facts as (Hmem & _).
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  unfold enframe_at. change (get_meta_rec st g) with mr. rewrite Hmem. cbn [default from_option id]. fold stride.
  change (negb (0 =? 0)) with false. cbv iota beta. unfold aadd. cbn [fst snd].
  unfold set_size. cbn [fst snd].
  replace (snd b + (UNIT + stride * idx) + (stride - IB) - (snd b + (UNIT + stride * idx)) - N) with 0 by (unfold UNIT, IB; lia).
  cbn [Z.eqb negb Z.leb]. unfold enf0_st, UNIT. split; reflexivity.
Qed.
#[using="N P B stride mr j idx b g st"] Lemma meta_word_mod4096 r0 : mw_ok r0 -> meta_word r0 mod 4096 = meta_word (m_set_maplen 0 r0).
Proof.
  ((first [ intro dR_17; dand4 dR_17 as LI FB SC ML | intros (LI & FB & SC & ML) ])). unfold meta_word. cbn [m_last_idx m_freeable m_sizeclass m_maplen m_set_maplen].
  rewrite Z.land_0_l. Z.div_mod_to_equations. lia.
Qed.
(* [comment removed for export] *)
Definition pp : aptr := (fst b, snd b + (16 + stride * idx)).
#[using="TK SO STR SCg MW MSL HA J UA MR N r o"] Lemma rnenf_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s7 s8 s10 s11 t3 t4 t5 t6 : word) F fc,
  0 <= c_mmap_counter (ctx st) < 2^32 -> mem_inv rsegs m1 ->
  evt rsegs (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) m',
      ms' = MS (mkR (Z_to_bv 64 0x24474) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 P) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 (SIZE_CLASSES + j * 2)) s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3' t4' t5' t6')
              F (Z_to_bv 64 0x24474) fc None m' (seg_rom rsegs)
      /\ munch [(P - 3, P)]%Z m1 m' /\ wmono rsegs m1 m' /\ mem_inv rsegs m'
      /\ mrep enf0_st m' /\ ticks_ok enf0_st)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 idx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 j) s3 s4 s5 (Z_to_bv 64 MLOCK) s7 s8 (Z_to_bv 64 SIZE_CLASSES) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24448) fc None m1 (seg_rom rsegs)).
Proof.
  intros until fc. intros CTR MI.
  (first [ pose proof (enf_facts) as dR_1; dand13 dR_1 as Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16 | pose proof enf_facts as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16) ]).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  pose proof (size_class_range j J) as SZR.
  assert (STN : stride = N + 4) by (rewrite STR; unfold N, UNIT, IB; lia).
  assert (NR : 12 <= N < 2^18) by (unfold N, UNIT, IB; lia).
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  (first [ pose proof ((slot_facts (Clg:=Clg) (Rr:=Rr) st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)) as dR_2; dex3 dR_2 as x3 x2 x1; dand10 dR_2 as WRs Y E3 E2 E1 CB R4 PEND RC RI1 | pose proof ((slot_facts (Clg:=Clg) (Rr:=Rr) st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)) as dR_2; dand13 dR_2 as x3 x2 x1 WRs Y E3 E2 E1 CB R4 PEND RC RI1 | destruct (slot_facts (Clg:=Clg) (Rr:=Rr) st m1 o g b r idx MR UA Hr Hk B0 ltac:(lia) SPAN1 S16 B16 SMOD HDR0)
    as (x3 & x2 & x1 & WRs & Y & E3 & E2 & E1 & CB & R4 & PEND & RC & RI1) ]).
  fold mr in WRs, Y, E3, E2, E1, PEND. fold stride in WRs, Y, E3, E2, E1, PEND. fold B in CB, Y, WRs, PEND. 
  (first [ pose proof ((meta_chunk_facts st m1 g MR MSL)) as dR_3; dand7 dR_3 as MM G0 GC GI1 GI2 GDJ GRG | pose proof (meta_chunk_facts st m1 g MR MSL) as (MM & G0 & GC & GI1 & GI2 & GDJ & GRG) ]).
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  set (G := conc st g) in *.
  pose proof (GDJ (fst b) r Hr Hk) as GR.
  change (get_meta_rec st g) with mr in MM. unfold meta_cells in MM. rewrite Hmem in MM.
  unfold pw at 3 in MM. cbn [oconc] in MM. unfold meta_word in MM. fold B in MM.
  pose proof (byte_range x3) as X3. pose proof (byte_range x2) as X2. pose proof (byte_range x1) as X1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  pose proof (bytes_at_read rsegs m1 _ _ 0 1 Y ltac:(lia) ltac:(cbn; lia)) as RD4. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD4.
  pose proof (bytes_at_read rsegs m1 _ _ 1 1 Y ltac:(lia) ltac:(cbn; lia)) as RD3. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD3.
  pose proof (bytes_at_read rsegs m1 _ _ 2 2 Y ltac:(lia) ltac:(cbn; lia)) as RD2. cbv [take drop Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in RD2.
  rewrite Z.add_0_r in RD4.
  replace (B + 16 + stride * idx - 4 + 1) with (B + 16 + stride * idx - 3) in RD3 by lia.
  replace (B + 16 + stride * idx - 4 + 2) with (B + 16 + stride * idx - 2) in RD2 by lia.
  rewrite <- (le2_lohi (bv_unsigned x2) (bv_unsigned x1)) in RD2 by lia.
  pose proof MW as (LI0 & FB0 & SCR0 & ML0).
  pose proof MR as (WF' & CX & GL & _). destruct CX as (CH & _). unfold ctx_head_cells in CH.
  unfold SIZE_CLASSES, MLOCK, CTX in *.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
  step. rewrite ?(unsigned_lit j), ?Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  step. step.
  (* [comment removed for export] *)
  pose proof (size_classes_read m1 j MI J) as SCRD. unfold SIZE_CLASSES in SCRD.
  replace (85160 + 2 * j) with (85160 + j * 2) in SCRD by lia.
  step. rewrite zx16_wz by lia. clear SCRD.
  (* [comment removed for export] *)
  pose proof (mrep_active_read st m1 j (wa (403456 + 80 + 8 * j)) MR J eq_refl) as RDA. rewrite HA in RDA. unfold pw in RDA. cbn [oconc] in RDA. unfold wz in RDA. fold G in RDA.
  replace (wa (403456 + 80 + 8 * j)) with (Z_to_bv 64 (403448 + j * 8 + 88)) in RDA by (unfold wa; f_equal; lia).
  step. clear RDA.
  (* [comment removed for export] *)
  step. rewrite sx32_wz_sxv by lia.
  (* [comment removed for export] *)
  step. rewrite (wz_unsigned (size_class j)), Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
  step.
  (* [comment removed for export] *)
  step.
  eapply evt_mono.
  { eapply (enframe_walk (Z_to_bv 64 0x24474) sp gp tp _ _ _ s0 s1 _ _ _ _ _ s3 s4 s5 _ s7 s8 _ s10 s11 _ _ _ _ (Z_to_bv 64 G) _
              (pw st (m_prev mr)) (pw st (m_next mr)) F fc m1 B stride N idx (c_mmap_counter (ctx st)) (m_avail mr) (m_freed mr)
              (m_last_idx mr) (m_freeable mr) (m_sizeclass mr) (m_maplen mr) (bv_unsigned x3) (bv_unsigned x2 + 256 * bv_unsigned x1)).
    all: lazymatch goal with
         | |- rw_cells _ _ (bv_unsigned _) _ => rewrite (unsigned_lit G) by lia; exact MM
         | |- mem_inv _ _ => exact MI
         | |- wr_at _ _ _ _ => exact WRs
         | |- ov_read_bytes _ _ _ 2 = _ => exact RD2
         | |- ov_read_bytes _ _ _ _ = Some [b8 0] => exact RD4
         | |- ov_read_bytes _ _ _ _ = _ => exact RD3
         | |- bv_unsigned (Z_to_bv 64 _) = _ => rewrite unsigned_lit by lia; unfold N, UNIT, IB; lia
         | |- _ => idtac end.
    all: try (rewrite (unsigned_lit G) by lia).
    all: try lia.
    - subst stride. unfold get_stride, UNIT. reflexivity.
    - intros off' O1 O2. pose proof (Q16 off' O1 O2). lia.
    - exact (so_maplen _ _ _ _ _ _ SO). }
  (* [comment removed for export] *)
  intros ms' PO. cbv beta in PO. unfold en3_post in PO.
  (first [ dex15 PO as w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m'; dand3 PO as -> EM MI' | dand18 PO as w0 w1 w2 y1 y2 y3 y4 y5 y6 y7 w3 w4 w5 w6 m' -> EM MI' | destruct PO as (w0 & w1 & w2 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & w3 & w4 & w5 & w6 & m' & -> & EM & MI') ]).
  set (off0 := if bv_unsigned x3 =? 0 then Z.land (c_mmap_counter (ctx st)) 255 else Z.land (bv_unsigned x2 + 256 * bv_unsigned x1 + 1) 255) in EM |- *.
  assert (OFF0 : 0 <= off0 < 256).
  { subst off0. destruct (bv_unsigned x3 =? 0).
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
    - split; [apply Z.land_nonneg; lia|]. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia. }
  replace ((stride - 4 - N) / 16) with 0 in EM |- * by (rewrite STN; replace (N + 4 - 4 - N) with 0 by lia; reflexivity).
  pose proof (fold_off_le_slack off0 0 OFF0 ltac:(lia)) as OFF.
  replace (fold_off off0 0) with 0 in EM |- * by lia.
  rewrite Z.mul_0_r, Z.add_0_r in EM |- *.
  replace (ret_pc (Z_to_bv 64 0x24474)) with (Z_to_bv 64 0x24474) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]).
  (* [comment removed for export] *)
  assert (S31n : stride - 4 - N < 2^31) by lia.
  assert (SPAN2 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)) by (rewrite Z.mul_add_distr_l, Z.mul_1_r; exact SPAN1).
  assert (T1 : 0 <= idx < 32) by lia. assert (T3 : 16 * 0 + N + 4 <= stride) by lia. assert (T0 : 0 <= 0) by lia. assert (TN : 0 <= N) by lia.
  assert (T4 : (stride * idx + 16 * 0) / 16 < 65536) by (apply (Q16 0); lia).
  (first [ pose proof ((enframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)) as dR_5; dand5 dR_5 as MRr TKr CONCr FSTr SNDr | destruct (enframe_mrep st m1 g b r idx N 0 MR TK Hmem Hr Hk B0 T1 SPAN2 S16 S31n NOGRP T0 TN T3 T4)
    as (MRr & TKr & CONCr & FSTr & SNDr) ]). clear T1 T3 T0 TN T4.
  rewrite Z.mul_0_r, Z.add_0_r in MRr.
  change (conc st b) with B in MRr. change (get_stride (get_meta_rec st g)) with stride in MRr.
  fold P in MRr, EM. rewrite <- EM in MRr.
  destruct enf0_st_eq as [E1st _]. fold N in E1st. rewrite E1st in MRr, TKr.
  (* [comment removed for export] *)
  assert (EM' : m' = write_to_mem (write_to_mem (write_to_mem m1 (wa (P - 3)) [b8 idx]) (wa (P - 2)) (le2 (wz ((P - B - 16) / 16)))) (wa (P - 3)) [b8 (Z.land idx 31 + Z.shiftl 0 5)]).
  { rewrite EM. unfold enframe_tail_mem, enframe_off_mem. cbn [Z.eqb].
    replace (P + stride - 4 - P - N) with 0 by lia. cbn [Z.eqb Z.leb]. reflexivity. }
  assert (MU : munch [(P - 3, P)]%Z m1 m').
  { rewrite EM'. apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [| lia| cbn; lia| cbn; lia].
    apply munch_write; [apply munch_refl| lia| cbn; lia| cbn; lia]. }
  assert (WM : wmono rsegs m1 m').
  { rewrite EM'. apply wmono_write. apply wmono_write. apply wmono_write. apply wmono_refl. }
  do 14 eexists. exists m'.
  split; [unfold P, G; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI'|]. split; [exact MRr| exact TKr].
Qed.
#[using="N P B stride mr j idx b g st"] Lemma lor_192 a : 0 <= a < 32 -> Z.lor a 192 = a + 192.
Proof. intros Ha. change 192 with (3 * 2 ^ 6). rewrite (lor_small_shl 3 6 a) by lia. lia. Qed.

(* [comment removed for export] *)
#[using="TK SO J MR N j r m1"] Lemma enfD_walk :
  forall (ra sp gp tp t0 t1 t2 s0 a1 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) F fc (mt : aptr) (cnt : Z) mC,
  meta_slot st mt -> mw_ok (get_meta_rec st mt) -> 1 <= cnt <= 32 ->
  mrep enf0_st mC -> ticks_ok enf0_st -> mem_inv rsegs mC ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 (P + 12)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2449c) fc None m' (seg_rom rsegs)
      /\ munch [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC m' /\ wmono rsegs mC m' /\ mem_inv rsegs m'
      /\ mrep (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) enf0_st)) m'
      /\ ticks_ok (wr8 (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192)
                 (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) enf0_st)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 (Z_to_bv 64 (conc st mt)) (Z_to_bv 64 P) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x24474) fc None mC (seg_rom rsegs)).
Proof.
  intros until mC. intros MST MWT CR MRC TKC MIC.
  (first [ pose proof (enf_facts) as dR_6; dand13 dR_6 as Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16 | pose proof enf_facts as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16) ]).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  (first [ pose proof ((rregion_facts st m1 (fst b) r MR Hr)) as dR_7; dand5 dR_7 as R4 RAL RC RI1 RI2 | pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  set (st0' := enf0_st) in *.
  assert (MST0 : meta_slot st0' mt) by (eapply meta_slot_same_areas; [| exact MST]; reflexivity).
  (first [ pose proof ((meta_slot_bounds st0' mC mt MRC MST0)) as dR_8; dand5 dR_8 as Tpos TC TI _ _ | pose proof (meta_slot_bounds st0' mC mt MRC MST0) as (Tpos & TC & TI & _ & _) ]).
  change (conc st0' mt) with (conc st mt) in Tpos, TC, TI.
  (first [ pose proof ((meta_chunk_facts st0' mC mt MRC MST0)) as dR_9; dand7 dR_9 as _ _ _ _ _ GDJ _ | pose proof (meta_chunk_facts st0' mC mt MRC MST0) as (_ & _ & _ & _ & _ & GDJ & _) ]).
  assert (RG0 : s_regions st0' = s_regions st) by (unfold st0', enf0_st, wr16; rewrite !s_regions_wr8; reflexivity).
  assert (GR0 : s_groups st0' = s_groups st) by (unfold st0', enf0_st, wr16; rewrite !s_groups_wr8; reflexivity).
  rewrite RG0 in GDJ. pose proof (GDJ (fst b) r Hr Hk) as TDJ. change (conc st0' mt) with (conc st mt) in TDJ.
  pose proof (munch_refl [(conc st mt, conc st mt + 40); (P - 3, P - 2)]%Z mC) as MU. pose proof (wmono_refl rsegs mC) as WM.
  (first [ pose proof (MWT) as dR_10; dand4 dR_10 as LI0 FB0 SCR0 ML0 | pose proof MWT as (LI0 & FB0 & SCR0 & ML0) ]). pose proof (meta_word_range _ MWT) as MWR.
  (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  (* [comment removed for export] *)
  mchunk MRC MST0 CH. change (conc st0' mt) with (conc st mt) in CH. change (get_meta_rec st0' mt) with (get_meta_rec st mt) in CH.
  meta_open (conc st mt) MUt WMt.
  step.
  (* [comment removed for export] *)
  step. step. rewrite ?(unsigned_lit (meta_word (get_meta_rec st mt))) by lia.
  set (w := meta_word (get_meta_rec st mt)) in *.
  rewrite (Z_to_bv_unsigned 64 (Z.shiftl w 52)). unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite (zb_shl_shr w 52) by lia. change (2 ^ (64 - 52)) with 4096.
  rewrite (meta_word_mod4096 _ MWT).
  step.
  lazymatch goal with H : rw_cells rsegs ?mX (conc st mt) _ |- evt _ _ (MS _ _ _ _ _ ?mX _) =>
    assert (MR5 : mrep (put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') mX);
    [ eapply mrep_put_meta_frame; [exact MRC| exact MST0| exact MUt| exact WMt|];
      eapply rw_cells_congr; [| | | exact H]; [| reflexivity| cbn; tauto];
      unfold meta_cells, pw; cbn [m_prev m_next m_mem m_avail m_freed m_set_maplen oconc]; reflexivity
    | clear MUt WMt H ] end.
  set (st5 := put_meta mt (m_set_maplen 0 (get_meta_rec st mt)) st0') in *.
  assert (TK5 : ticks_ok st5) by (exact (ticks_ok_upd_meta st0' mt (fun _ => m_set_maplen 0 (get_meta_rec st mt)) TKC)).
  (* [comment removed for export] *)
  pose proof (land31_range idx) as L31.
  assert (K3 : cell_read (get_shadow st5 (fst b)) (snd b + (16 + stride * idx) + -3) = Known (Z.land idx 31)).
  { change (get_shadow st5 (fst b)) with (get_shadow st0' (fst b)). unfold st0', enf0_st.
    rewrite (cell_read_wr8_same (wr8 _ _ (wr16 _ _ st)) (fst b, snd b + (16 + stride * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5));
      [| apply ticks_ok_wr8, ticks_ok_wr16; exact TK | change (Z.shiftl 0 5) with 0; lia].
    change (Z.shiftl 0 5) with 0. rewrite Z.add_0_r. reflexivity. }
  destruct (mrep_shadow_read (Clg:=Clg) (Rr:=Rr) st5 _ (fst b) r (snd b + (16 + stride * idx) + -3) (Z.land idx 31) MR5 Hr Hk ltac:(lia) K3) as [RDK _].
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in RDK
    by (unfold wa; f_equal; unfold P; lia).
  step. rewrite zxb_b8 by lia. clear RDK. rewrite ?(unsigned_lit P) by (unfold P; lia).
  (* [comment removed for export] *)
  step. rewrite (unsigned_lit cnt), swrap32_small by lia.
  step. rewrite (wz_unsigned (Z.land idx 31)) by lia. rewrite <- (Z.land_assoc idx 31 31). change (Z.land 31 31) with 31.
  step. rewrite ?(unsigned_lit (Z.land idx 31)) by lia.
  (* [comment removed for export] *)
  (first [ pose proof (MR5) as dR_11; dand6 dR_11 as _ _ _ _ _ SH5 | pose proof MR5 as (_ & _ & _ & _ & _ & SH5) ]). destruct (SH5 (fst b) r Hr Hk) as [WR5 _]. clear SH5.
  pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + -3) 1 WR5 ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + -3))) with (Z_to_bv 64 (P + -3)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  assert (RG5 : s_regions st5 = s_regions st) by (unfold st5; exact RG0).
  assert (GR5 : s_groups st5 = s_groups st) by (unfold st5; exact GR0).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_wr8 st5 mX (fst b, snd b + (16 + stride * idx) + -3) (Z.lor (Z.land idx 31) 192) r MR5 TK5) as MR6 end.
  cbn [fst snd] in MR6. rewrite RG5, GR5 in MR6.
  assert (LOR : 0 <= Z.lor (Z.land idx 31) 192 < 256) by (rewrite lor_192 by lia; lia).
  specialize (MR6 Hr Hk ltac:(lia) ltac:(intros b' gh' Hb' Hf'; destruct (NOGRP b' gh' Hb' Hf'); lia) ltac:(lia)).
  replace (r_base r + (snd b + (16 + stride * idx) + -3)) with (P - 3) in MR6 by (unfold P; lia).
  rewrite <- (lor_192 (Z.land idx 31)) by lia.
  raw_store_finish0 (P - 3) [b8 (Z.lor (Z.land idx 31) 192)] MU WM SOK.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit P) by (unfold P; lia).
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [exact MR6| apply ticks_ok_wr8; exact TK5].
Qed.
(* [comment removed for export] *)
#[using="SO STR MR N j r m1"] Lemma zero_loop_walk : forall k (i szc cnt : Z) stz mC0 mC
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s9 s10 s11 t3 t4 t5 t6 : word) F fc,
  Z.of_nat k = cnt + 1 - i -> 0 <= i <= cnt -> 1 <= szc -> 0 <= cnt < 4096 -> 16 + 16 * szc * cnt <= stride ->
  s_regions stz = s_regions st -> s_groups stz = s_groups st ->
  mrep stz mC -> ticks_ok stz -> mem_inv rsegs mC ->
  munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 mC -> wmono rsegs mC0 mC ->
  evt rsegs (fun ms' => exists m',
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt - 1)) (Z_to_bv 64 (cnt - 1)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) (Z_to_bv 64 cnt) s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x2476c) fc None m' (seg_rom rsegs)
      /\ munch [(P + 12, P + 12 + 16 * szc * cnt + 1)]%Z mC0 m' /\ wmono rsegs mC0 m' /\ mem_inv rsegs m'
      /\ mrep (zero_hdrs pp (16 * szc) i k stz) m' /\ ticks_ok (zero_hdrs pp (16 * szc) i k stz)
      /\ s_regions (zero_hdrs pp (16 * szc) i k stz) = s_regions st /\ s_groups (zero_hdrs pp (16 * szc) i k stz) = s_groups st
      /\ (forall x, (forall j, i <= j <= cnt -> bv_unsigned x <> P + 12 + 16 * szc * j) -> m' x = mC x))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (cnt + 1 - i)) (Z_to_bv 64 (P + 12 + 16 * szc * i)) a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 cnt) s4 s5 s6 s7 (Z_to_bv 64 (16 * szc)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2449c) fc None mC (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros until fc; intros HK HI SZC CNT FIT RGz GRz MRz TKz MIz MU WM.
  { exfalso. lia. }
  (first [ pose proof (enf_facts) as dR_12; dand13 dR_12 as Hmem Hr Hk B0 B16 IDX LI32 SPAN S16 SMOD NOGRP HDR0 Q16 | pose proof enf_facts as (Hmem & Hr & Hk & B0 & B16 & IDX & LI32 & SPAN & S16 & SMOD & NOGRP & HDR0 & Q16) ]).
  fold mr in Hmem, IDX, LI32, SPAN, S16, SMOD, NOGRP, HDR0, Q16. fold stride in SPAN, S16, SMOD, NOGRP, HDR0, Q16.
  assert (SPAN1 : snd b + 16 + stride * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact SPAN]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  assert (SK : 0 <= stride * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SZI : 0 <= 16 * szc * i <= 16 * szc * cnt) by (split; [apply Z.mul_nonneg_nonneg; lia| apply Z.mul_le_mono_nonneg_l; lia]).
  (first [ pose proof ((rregion_facts st m1 (fst b) r MR Hr)) as dR_13; dand5 dR_13 as R4 RAL RC RI1 RI2 | pose proof (rregion_facts st m1 (fst b) r MR Hr) as (R4 & RAL & RC & RI1 & RI2) ]). (let acv := fresh "ACV" in pose proof alloc_ceiling_val as acv).
  assert (CB : B = r_base r + snd b) by (unfold B; apply conc_region'; exact Hr).
  (* [comment removed for export] *)
  assert (Hr' : (s_regions stz) !! (fst b) = Some r) by (rewrite RGz; exact Hr).
  (first [ pose proof (MRz) as dR_14; dand6 dR_14 as WFz _ _ _ _ SHz | pose proof MRz as (WFz & _ & _ & _ & _ & SHz) ]). destruct (SHz (fst b) r Hr' Hk) as [WRz _]. clear SHz.
  pose proof (wr_at_store_ok rsegs _ _ _ (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)) 1 WRz ltac:(lia) ltac:(lia)) as SOK.
  replace (wa (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4)))) with (Z_to_bv 64 (P + 12 + 16 * szc * i)) in SOK
    by (unfold wa; f_equal; unfold P; lia).
  st1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX _ _) _) =>
    pose proof (mrep_wr8 stz mX (aadd pp (UNIT + i * (16 * szc) - 4)) 0 r MRz TKz) as MR2 end.
  unfold aadd, pp, UNIT in MR2. cbn [fst snd] in MR2. fold mr in MR2. fold stride in MR2. rewrite GRz in MR2.
  specialize (MR2 Hr' Hk ltac:(lia)).
  assert (NOG : forall b0 gh, (s_groups st) !! b0 = Some gh -> fst b0 = fst b ->
            ~ snd b0 <= snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4) < snd b0 + 9).
  { intros b0 gh Hb0 Hf0 CONTRA. pose proof MR as (WF & _). (first [ pose proof (WF) as dR_15; dand5 dR_15 as _ _ _ _ GWF | pose proof WF as (_ & _ & _ & _ & GWF) ]).
    (first [ pose proof ((GWF b0 gh Hb0)) as dR_16; dex1 dR_16 as r0; dand5 dR_16 as _ _ _ _ M16 | pose proof ((GWF b0 gh Hb0)) as dR_16; dand6 dR_16 as r0 _ _ _ _ M16 | destruct (GWF b0 gh Hb0) as (r0 & _ & _ & _ & _ & M16) ]).
    destruct (NOGRP b0 gh Hb0 Hf0) as [LE|GE]; [lia|].
    assert (E0 : snd b0 = 16 * (snd b0 / 16)) by (pose proof (Z.div_mod (snd b0) 16 ltac:(lia)); lia).
    assert (E1 : snd b = 16 * (snd b / 16)) by (pose proof (Z.div_mod (snd b) 16 ltac:(lia)); lia).
    assert (E2 : stride = 16 * (stride / 16)) by (pose proof (Z.div_mod stride 16 ltac:(lia)); lia).
    clear M16 B16 SMOD. try clear ACV. try clear RC R4 RAL RI1 RI2. (* [comment removed for export] *) nia. }
  specialize (MR2 NOG ltac:(lia)). clear NOG.
  replace (r_base r + (snd b + (16 + stride * idx) + (16 + i * (16 * szc) - 4))) with (P + 12 + 16 * szc * i) in MR2 by (unfold P; lia).
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0])
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa; f_equal; lia);
    assert (PW0 : forall u, 0 <= u < 2^64 -> u <> P + 12 + 16 * szc * i -> write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0] (wa u) = mX (wa u));
    [ intros u Hu Hux;
      rewrite write_to_mem_spec by (cbn; lia); rewrite wa_unsigned by lia; cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity;
      destruct (Z.leb_spec0 (P + 12 + 16 * szc * i) u); destruct (Z.ltb_spec0 u (P + 12 + 16 * szc * i + 1)); cbn [andb]; try reflexivity;
      exfalso; lia
    | apply (munch_write _ _ mX (P + 12 + 16 * szc * i) [b8 0]) in MU; [| lia | cbn [length]; replace (Z.of_nat 1) with 1 by reflexivity; lia | cbn [length inside]; replace (Z.of_nat 1) with 1 by reflexivity; lia];
      apply (wmono_write rsegs _ mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in WM;
      lazymatch goal with HI : mem_inv rsegs mX |- _ =>
        apply (mem_inv_store rsegs mX (wa (P + 12 + 16 * szc * i)) [b8 0]) in HI;
        [| first [ exact SOK | replace (wa (P + 12 + 16 * szc * i)) with a by (unfold wa; f_equal; lia); exact SOK ] ]
      end;
      clear SOK;
      let m' := fresh "m" in remember (write_to_mem mX (wa (P + 12 + 16 * szc * i)) [b8 0]) as m' eqn:Em'; clear Em' ]
  end.
  (* [comment removed for export] *)
  step. rewrite ?(unsigned_lit (cnt + 1 - i)) by lia.
  step. rewrite ?unsigned_lit by lia.
  (* [comment removed for export] *)
  step. if_cases K; zify_cond K; rewrite ?unsigned_lit in K by lia.
  - (* [comment removed for export] *)
    replace (cnt + 1 - i + -1) with (cnt + 1 - (i + 1)) by lia.
    replace (P + 12 + 16 * szc * i + 16 * szc) with (P + 12 + 16 * szc * (i + 1)) by lia.
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    eapply evt_mono.
    { (eapply (IH (i + 1) szc cnt);
      [ lia | lia | exact SZC | exact CNT | exact FIT
      | rewrite s_regions_wr8; exact RGz
      | rewrite s_groups_wr8; exact GRz
      | exact MR2
      | apply ticks_ok_wr8; exact TKz
      | assumption | exact MU | exact WM ]). }
    cbv beta. (intros ms'; (first [ intro dR_18; dex1 dR_18 as m'; dand9 dR_18 as -> X1 X2 X3 X4 X5 X6 X7 PW | intro dR_18; dand10 dR_18 as m' -> X1 X2 X3 X4 X5 X6 X7 PW | intros (m' & -> & X1 & X2 & X3 & X4 & X5 & X6 & X7 & PW) ])).
    eexists. split; [reflexivity|]. split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|].
    split; [exact X6|]. split; [exact X7|].
    intros x Hx. rewrite (PW x) by (intros jj Hjj; apply Hx; lia).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
  - (* [comment removed for export] *)
    assert (Ei : i = cnt) by lia. destruct k; [| exfalso; lia].
    (* [comment removed for export] *)
    step. rewrite ?(unsigned_lit cnt) by lia. replace (cnt + -1) with (cnt - 1) by lia. step. step. step.
    apply evt_done. eexists. split; [reflexivity|].
    cbn [zero_hdrs]. unfold aadd, pp, UNIT. cbn [fst snd]. fold mr. fold stride.
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact MR2|]. split; [apply ticks_ok_wr8; exact TKz|].
    split; [rewrite s_regions_wr8; exact RGz|]. split; [rewrite s_groups_wr8; exact GRz|].
    intros x Hx. pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2^64) in XR.
    rewrite <- (Z_to_bv_bv_unsigned x). unfold wa in PW0. apply PW0; [lia|]. apply Hx. lia.
Qed.
End ENF.
End RASlku2.

Module ASlo1am.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Tac Image ZBridge SysStep Bytes Walk.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes Decode Arr.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Image OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.SysStep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Walk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Decode OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Arr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require F_sy88u MRep MRepAux MRepAux MRepAux RF_egfy MTree Mallwlb Mallj6y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.F_sy88u OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRep OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MRepAux OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RF_egfy OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.MTree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallwlb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallj6y OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3.Mallm24.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Import Mallkgx Mall17y.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import STree Malloc Mall7vg Monad MProg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Mallmv3 Malls02.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Mallmv3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malls02 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RF_m79e.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require Malluin RASlh4s.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn Require RASla24.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.Malluin OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASlh4s OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.RASlku2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.RASla24 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zn.ASlot_M4.ASlojxo.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
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
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cells_wr8_other st q v o : o <> snd q ->
  (r_cells (get_shadow (wr8 q v st) (fst q))) !! o = (r_cells (get_shadow st (fst q))) !! o.
Proof. intros NE. rewrite get_shadow_wr8_same. cbn [r_cells]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

(* [comment removed for export] *)

Lemma hav_wr8 st q v : r_hav (get_shadow (wr8 q v st) (fst q)) = r_hav (get_shadow st (fst q))
  /\ r_havp (get_shadow (wr8 q v st) (fst q)) = r_havp (get_shadow st (fst q)).
Proof. rewrite get_shadow_wr8_same. split; reflexivity. Qed.

Lemma cells_wr8_other' st rid off v o : o <> off ->
  (r_cells (get_shadow (wr8 (rid, off) v st) rid)) !! o = (r_cells (get_shadow st rid)) !! o.
Proof. intros NE. exact (cells_wr8_other st (rid, off) v o NE). Qed.

Lemma hav_wr8_any st q v rid : r_hav (get_shadow (wr8 q v st) rid) = r_hav (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj1 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma havp_wr8_any st q v rid : r_havp (get_shadow (wr8 q v st) rid) = r_havp (get_shadow st rid).
Proof. destruct (N.eq_dec rid (fst q)) as [->|NE]; [apply (proj2 (hav_wr8 st q v))| rewrite get_shadow_wr8_other by exact NE; reflexivity]. Qed.

Lemma shadow_put_meta st m r rid : get_shadow (put_meta m r st) rid = get_shadow st rid.
Proof. reflexivity. Qed.

Lemma cell_read_wr8_other' st rid off v o : o <> off ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) o = cell_read (get_shadow st rid) o.
Proof. intros NE. exact (cell_read_wr8_other st (rid, off) v o NE). Qed.

Lemma cell_read_wr8_same' st rid off v : ticks_ok st -> 0 <= v < 256 ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known v.
Proof. intros TK Hv. exact (cell_read_wr8_same st (rid, off) v TK Hv). Qed.

Lemma cell_read_wr8_same_land st rid off v : ticks_ok st ->
  cell_read (get_shadow (wr8 (rid, off) v st) rid) off = Known (Z.land v 255).
Proof.
  intros TK. replace (wr8 (rid, off) v st) with (wr8 (rid, off) (Z.land v 255) st).
  - apply cell_read_wr8_same'; [exact TK|]. pose proof (Z.land_nonneg v 255). split; [lia|].
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. apply Z.mod_pos_bound. lia.
  - unfold wr8. cbn [fst snd]. rewrite <- Z.land_assoc. change (Z.land 255 255) with 255. reflexivity.
Qed.

Lemma ticks_ok_same2 st st1 : s_shadow st1 = s_shadow st -> s_tick st1 = s_tick st -> ticks_ok st -> ticks_ok st1.
Proof. intros HS HT [T1 T2]. split; rewrite HS, HT; assumption. Qed.

Section ZH.
Variables (p : aptr) (s : Z).

Lemma zh_proj : forall k i st,
  let st' := zero_hdrs p s i k st in
  s_regions st' = s_regions st /\ s_groups st' = s_groups st /\ s_areas st' = s_areas st
  /\ s_tick st' = s_tick st /\ s_next_rid st' = s_next_rid st /\ s_reserved st' = s_reserved st
  /\ s_ctx st' = s_ctx st /\ s_slots st' = s_slots st /\ s_metas st' = s_metas st.
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity|].
  (first [ pose proof ((IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st))) as dR_1; dand9 dR_1 as A1 A2 A3 A4 A5 A6 A7 A8 A9 | destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9) ]).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8, A9. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
Qed.

Lemma zh_shadow_other q : q <> fst p -> forall k i st, get_shadow (zero_hdrs p s i k st) q = get_shadow st q.
Proof.
  intros NE. induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH. apply get_shadow_wr8_other. exact NE.
Qed.

Lemma zh_hav : forall k i st,
  r_hav (get_shadow (zero_hdrs p s i k st) (fst p)) = r_hav (get_shadow st (fst p))
  /\ r_havp (get_shadow (zero_hdrs p s i k st) (fst p)) = r_havp (get_shadow st (fst p)).
Proof.
  induction k as [|k IH]; intros i st; cbn [zero_hdrs]; [split; reflexivity|].
  destruct (IH (i + 1) (wr8 (aadd p (UNIT + i * s - 4)) 0 st)) as [A B]. rewrite A, B.
  pose proof (hav_wr8 st (aadd p (UNIT + i * s - 4)) 0) as [C D]. cbn [fst aadd] in C, D. rewrite C, D. split; reflexivity.
Qed.

Lemma zh_cells_other o : forall k i st,
  (forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
  (r_cells (get_shadow (zero_hdrs p s i k st) (fst p))) !! o = (r_cells (get_shadow st (fst p))) !! o.
Proof.
  induction k as [|k IH]; intros i st Ho; cbn [zero_hdrs]; [reflexivity|].
  rewrite IH by (intros j Hj; apply Ho; lia).
  pose proof (cells_wr8_other st (aadd p (UNIT + i * s - 4)) 0 o) as C. cbn [fst snd aadd] in C. apply C. specialize (Ho i ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)

Lemma zh_cell_read_other o : forall k i st,
  (forall j, i <= j < i + Z.of_nat k -> o <> snd p + UNIT + j * s - 4) ->
  cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) o = cell_read (get_shadow st (fst p)) o.
Proof.
  intros k i st Ho. unfold cell_read. rewrite (zh_cells_other o k i st Ho).
  destruct (zh_hav k i st) as [A B]. rewrite A, B. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma zh_cell_read_at : 0 < s -> forall k i st j, ticks_ok st -> i <= j < i + Z.of_nat k ->
  cell_read (get_shadow (zero_hdrs p s i k st) (fst p)) (snd p + UNIT + j * s - 4) = Known 0.
Proof.
  intros HS. induction k as [|k IH]; intros i st j TK Hj; cbn [zero_hdrs]; [lia|].
  destruct (Z.eq_dec j i) as [->|NE].
  - rewrite zh_cell_read_other by (intros j' Hj'; nia).
    pose proof (cell_read_wr8_same st (aadd p (UNIT + i * s - 4)) 0 TK ltac:(lia)) as C. cbn [fst snd aadd] in C.
    replace (snd p + UNIT + i * s - 4) with (snd p + (UNIT + i * s - 4)) by lia. exact C.
  - apply IH; [apply ticks_ok_wr8; exact TK| lia].
Qed.
End ZH.

(* [comment removed for export] *)
Lemma existsb_filter_gt12 (l : list (Z * N)) (f : Z * N -> bool) :
  (forall ch, f ch = true -> 12 < fst ch) ->
  existsb f (filter (fun ch : Z * N => Is_true (12 <? fst ch)) l) = existsb f l.
Proof.
  intros Hf. induction l as [|ch l IH]; [reflexivity|].
  rewrite filter_cons. destruct (decide _) as [D|D]; cbn [existsb]; rewrite IH; [reflexivity|].
  destruct (f ch) eqn:E; [|reflexivity]. exfalso. apply D. apply Is_true_true_2. apply Z.ltb_lt. exact (Hf ch E).
Qed.

Lemma stale_hav_add_ge hl bb T t : 12 <= bb -> stale (hav_add 12 T hl) bb t = stale hl bb t.
Proof.
  intros Hb. unfold hav_add, stale. cbn [existsb fst snd].
  replace (bb <? 12) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb orb].
  apply existsb_filter_gt12. intros [cov t'] H. cbn in H |- *. apply andb_prop in H. destruct H as [H _]. apply Z.ltb_lt in H. lia.
Qed.

Lemma cell_read_hdr_havoc_other st b o :
  snd b mod 16 = 0 -> ~ (snd b <= o < snd b + 12) ->
  cell_read (get_shadow (hdr_havoc b st) (fst b)) o = cell_read (get_shadow st (fst b)) o.
Proof.
  intros B16 Ho. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id].
  unfold cell_read. cbn [r_cells r_hav r_havp].
  destruct (Z.eq_dec (o / 16) (snd b / 16)) as [E|NE].
  - rewrite E, lookup_insert_eq. cbn [default from_option id].
    assert (HM : 12 <= o mod 16) by (Z.div_mod_to_equations; lia).
    fold (get_shadow st (fst b)).
    destruct (r_cells (get_shadow st (fst b)) !! o) as [[v t]|]; rewrite stale_hav_add_ge by exact HM; reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma hav_hdr_havoc_other st b u : u <> snd b / 16 ->
  (r_hav (get_shadow (hdr_havoc b st) (fst b))) !! u = (r_hav (get_shadow st (fst b))) !! u.
Proof.
  intros NE. unfold hdr_havoc, upd_shadow. unfold get_shadow at 1. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id r_hav]. rewrite lookup_insert_ne by congruence. reflexivity.
Qed.

Lemma cells_hdr_havoc st b : r_cells (get_shadow (hdr_havoc b st) (fst b)) = r_cells (get_shadow st (fst b))
  /\ r_havp (get_shadow (hdr_havoc b st) (fst b)) = r_havp (get_shadow st (fst b)).
Proof.
  unfold hdr_havoc, upd_shadow. split; rewrite (get_shadow_unfold (set_shadow _ _)); cbn [s_shadow set_shadow]; rewrite lookup_insert_eq; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section NEST.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Variables (st3 : mstate) (g b : aptr) (r : region) (idx jn sc cnt : Z) (mm : aptr).
Let strideg := get_stride (get_meta_rec st3 g).
Let szc := size_class sc.
Let X := snd b + (16 + strideg * idx).
Let p : aptr := (fst b, X).
Let N := UNIT * size_class jn - IB.

Definition nt_stW : mstate :=
  wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.lor (Z.land idx 31) 192)
      (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)).
Definition nt_stT : mstate := zero_hdrs p (16 * szc) 0 (Z.to_nat (cnt + 1)) nt_stW.

Hypothesis SC : 0 <= sc < 48.
Hypothesis J : 0 <= jn < 48.
Hypothesis CNT : 1 <= cnt <= 32.
Hypothesis SO : slot_ok st3 g b r idx N.
Hypothesis STR : strideg = UNIT * size_class jn.
Hypothesis FITN : 16 * szc * cnt + 16 <= UNIT * size_class jn.
Hypothesis G0 : get_meta_rec st3 mm = meta0.
Hypothesis MSmm : meta_slot st3 mm.
Hypothesis TK3 : ticks_ok st3.
Hypothesis FRESH3 : forall o v t, X <= o < X + strideg - 4 ->
  (r_cells (get_shadow st3 (fst b))) !! o = Some (v, t) -> (t < s_tick st3)%N.

(* [comment removed for export] *)

#[using="SC"] Lemma szc_range : 1 <= szc <= 8191.
Proof. unfold szc. apply size_class_range. exact SC. Qed.

#[using="STR SO N r"] Lemma nest_model_eq :
  upd_meta mm (m_set_maplen 0) (nest_layout st3 g idx jn (UNIT * size_class sc) cnt) = nt_stT.
Proof.
  unfold nest_layout. destruct (enf0_st_eq st3 g b r idx jn STR SO) as [E1 E2].
  rewrite (surjective_pairing (enframe_at st3 g idx (UNIT * size_class jn - IB) 0)), E1, E2.
  unfold upd_meta. rewrite rec_zero_hdrs.
  change (get_meta_rec (wr8 _ _ (enf0_st st3 g b idx)) mm) with (get_meta_rec st3 mm).
  rewrite put_meta_zero_hdrs_comm, put_meta_wr8_comm.
  unfold nt_stT, nt_stW, p, X, strideg, szc, aadd, UNIT. cbn [fst snd]. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ntW_proj :
  s_regions nt_stW = s_regions st3 /\ s_groups nt_stW = s_groups st3 /\ s_areas nt_stW = s_areas st3
  /\ s_tick nt_stW = s_tick st3 /\ s_next_rid nt_stW = s_next_rid st3 /\ s_reserved nt_stW = s_reserved st3
  /\ s_ctx nt_stW = s_ctx st3 /\ s_slots nt_stW = s_slots st3.
Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

Lemma ntT_proj :
  s_regions nt_stT = s_regions st3 /\ s_groups nt_stT = s_groups st3 /\ s_areas nt_stT = s_areas st3
  /\ s_tick nt_stT = s_tick st3 /\ s_next_rid nt_stT = s_next_rid st3 /\ s_reserved nt_stT = s_reserved st3
  /\ s_ctx nt_stT = s_ctx st3 /\ s_slots nt_stT = s_slots st3.
Proof.
  unfold nt_stT. (first [ pose proof ((zh_proj p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW)) as dR_2; dand9 dR_2 as A1 A2 A3 A4 A5 A6 A7 A8 _ | destruct (zh_proj p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & _) ]).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8. exact ntW_proj.
Qed.

#[using="G0"] Lemma ntT_rec q : get_meta_rec nt_stT q = if decide (q = mm) then mkMeta None None None 0 0 0 0 0 0 else get_meta_rec st3 q.
Proof.
  unfold nt_stT. rewrite rec_zero_hdrs. unfold nt_stW.
  change (get_meta_rec (wr8 _ _ (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx))) q)
    with (get_meta_rec (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q).
  destruct (decide (q = mm)) as [->|NE].
  - rewrite get_meta_rec_put_same, G0. reflexivity.
  - rewrite get_meta_rec_put_other by exact NE. reflexivity.
Qed.

Lemma ntT_active c : active nt_stT c = active st3 c.
Proof. unfold active, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

Lemma ntT_usage i : usage nt_stT i = usage st3 i.
Proof. unfold usage, ctx. rewrite (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). reflexivity. Qed.

Lemma ntT_ctx : ctx nt_stT = ctx st3.
Proof. unfold ctx. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 ntT_proj))))))). Qed.

Lemma ntT_conc q : conc nt_stT q = conc st3 q.
Proof. unfold conc, get_region. rewrite (proj1 ntT_proj). reflexivity. Qed.

Lemma ntT_shadow_other q : q <> fst b -> get_shadow nt_stT q = get_shadow st3 q.
Proof.
  intros NE. unfold nt_stT. rewrite (zh_shadow_other p (16 * szc) q NE). unfold nt_stW.
  rewrite get_shadow_wr8_other by exact NE.
  change (get_shadow (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (enf0_st st3 g b idx)) q) with (get_shadow (enf0_st st3 g b idx) q).
  unfold enf0_st, wr16. rewrite !get_shadow_wr8_other by exact NE. reflexivity.
Qed.

Lemma ntW_hav :
  r_hav (get_shadow nt_stW (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stW (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold nt_stW, enf0_st, wr16.
  split; repeat first [rewrite hav_wr8_any | rewrite havp_wr8_any | rewrite shadow_put_meta]; reflexivity.
Qed.

Lemma ntT_hav :
  r_hav (get_shadow nt_stT (fst b)) = r_hav (get_shadow st3 (fst b)) /\ r_havp (get_shadow nt_stT (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold nt_stT. destruct (zh_hav p (16 * szc) (Z.to_nat (cnt + 1)) 0 nt_stW) as [A B]. unfold p in A, B. cbn [fst] in A, B.
  rewrite A, B. exact ntW_hav.
Qed.

(* [comment removed for export] *)
Definition nt_written (o : Z) : Prop :=
  o = X - 3 \/ o = X - 2 \/ o = X - 1 \/ exists j, 0 <= j <= cnt /\ o = X + 12 + j * (16 * szc).

#[using="J SC N szc sc jn"] Lemma ntW_cells_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
  (r_cells (get_shadow nt_stW (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros N3 N2 N1. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  rewrite cells_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite !cells_wr8_other' by lia. reflexivity.
Qed.

#[using="J SC N szc sc jn"] Lemma ntW_cell_read_other o : o <> X - 3 -> o <> X - 2 -> o <> X - 1 ->
  cell_read (get_shadow nt_stW (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros N3 N2 N1. unfold cell_read. rewrite (ntW_cells_other o N3 N2 N1). destruct ntW_hav as [A B]. rewrite A, B. reflexivity.
Qed.

#[using="CNT J SC N jn"] Lemma ntT_cells_other o : ~ nt_written o ->
  (r_cells (get_shadow nt_stT (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros NW. unfold nt_stT. change (fst b) with (fst p) at 1.
  rewrite zh_cells_other.
  2:{ intros j Hj E. apply NW. right; right; right. exists j. split; [lia|]. unfold p, UNIT in E. cbn [snd] in E. lia. }
  unfold p. cbn [fst]. apply ntW_cells_other; intros E; apply NW; [left| right; left| right; right; left]; exact E.
Qed.

#[using="CNT J SC N jn"] Lemma ntT_cell_read_other o : ~ nt_written o ->
  cell_read (get_shadow nt_stT (fst b)) o = cell_read (get_shadow st3 (fst b)) o.
Proof.
  intros NW. unfold cell_read. rewrite (ntT_cells_other o NW). destruct ntT_hav as [A B]. rewrite A, B. reflexivity.
Qed.

#[using="TK3"] Lemma ntW_ticks_ok : ticks_ok nt_stW.
Proof.
  unfold nt_stW. apply ticks_ok_wr8.
  assert (TE : ticks_ok (enf0_st st3 g b idx)) by (unfold enf0_st, wr16; repeat apply ticks_ok_wr8; exact TK3).
  eapply ticks_ok_same2; [| | exact TE]; reflexivity.
Qed.

#[using="TK3 CNT J SC N jn"] Lemma ntT_cell_read_zero j : 0 <= j <= cnt ->
  cell_read (get_shadow nt_stT (fst b)) (X + 12 + j * (16 * szc)) = Known 0.
Proof.
  intros Hj. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  replace (X + 12 + j * (16 * szc)) with (snd p + UNIT + j * (16 * szc) - 4) by (unfold p, UNIT; cbn; lia).
  apply zh_cell_read_at; [lia| exact ntW_ticks_ok| lia].
Qed.

#[using="TK3 CNT J SC N jn"] Lemma ntT_cell_read_hdr k : 1 <= k <= 3 -> exists v, cell_read (get_shadow nt_stT (fst b)) (X - k) = Known v.
Proof.
  intros Hk. pose proof szc_range as SZR. unfold nt_stT. change (fst b) with (fst p).
  rewrite zh_cell_read_other by (intros j Hj; unfold p, UNIT; cbn; nia).
  unfold p. cbn [fst]. unfold X in *. unfold nt_stW, enf0_st, wr16, aadd. cbn [fst snd]. fold strideg.
  assert (T1 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)) by (apply ticks_ok_wr8; exact TK3).
  assert (T2 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
                          (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))) by (apply ticks_ok_wr8; exact T1).
  assert (T3 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))) by (apply ticks_ok_wr8; exact T2).
  assert (T4 : ticks_ok (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3))))) by (apply ticks_ok_wr8; exact T3).
  assert (T5 : ticks_ok (put_meta mm (m_set_maplen 0 (get_meta_rec st3 mm)) (wr8 (fst b, snd b + (16 + strideg * idx) + -3) (Z.land idx 31 + Z.shiftl 0 5)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -3) idx
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2 + 1) (Z.shiftr ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) 8)
             (wr8 (fst b, snd b + (16 + strideg * idx) + -2) ((snd b + (16 + strideg * idx) - (snd b + 16)) / 16) st3)))))) by (eapply ticks_ok_same2; [| | exact T4]; reflexivity).
  destruct (Z.eq_dec k 3) as [->|N3].
  { eexists. replace (snd b + (16 + strideg * idx) - 3) with (snd b + (16 + strideg * idx) + -3) by lia. apply cell_read_wr8_same_land. exact T5. }
  rewrite cell_read_wr8_other' by lia. rewrite shadow_put_meta.
  rewrite 2 cell_read_wr8_other' by lia.
  destruct (Z.eq_dec k 1) as [->|N1].
  { eexists. replace (snd b + (16 + strideg * idx) - 1) with (snd b + (16 + strideg * idx) + -2 + 1) by lia. apply cell_read_wr8_same_land. exact T1. }
  assert (k = 2) by lia. subst k.
  rewrite cell_read_wr8_other' by lia.
  eexists. replace (snd b + (16 + strideg * idx) - 2) with (snd b + (16 + strideg * idx) + -2) by lia. apply cell_read_wr8_same_land. exact TK3.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
#[using="SO J SC N szc sc jn"] Lemma slot_geom :
  m_mem (get_meta_rec st3 g) = Some b /\ (s_regions st3) !! (fst b) = Some r /\ r_kind r = RKGroup
  /\ 0 <= snd b /\ snd b mod 16 = 0 /\ 0 <= idx /\ 16 <= strideg /\ strideg mod 16 = 0
  /\ X + strideg <= round_up_pg (r_len r) /\ 0 <= strideg * idx
  /\ (forall b' gh, (s_groups st3) !! b' = Some gh -> fst b' = fst b -> snd b' + 9 <= X - 4 \/ X + strideg - 4 <= snd b').
Proof.
  destruct SO as [Smem Sreg Skind Sb0 Sb16 Sidx Sli Sspan Ss16 Ssmod _ _ _ Snogrp _ _ _ _ _ _ _ _ _].
  fold strideg in Sspan, Ss16, Ssmod, Snogrp.
  assert (SK : 0 <= strideg * idx) by (apply Z.mul_nonneg_nonneg; lia).
  assert (SPAN1 : snd b + 16 + strideg * (idx + 1) <= round_up_pg (r_len r)).
  { eapply Z.le_trans; [|exact Sspan]. apply Z.add_le_mono_l. apply Z.mul_le_mono_nonneg_l; lia. }
  rewrite Z.mul_add_distr_l, Z.mul_1_r in SPAN1.
  repeat (split; [first [assumption | unfold X; lia] |]).
  intros b' gh Hb' Hf. unfold X. destruct (Snogrp b' gh Hb' Hf); lia.
Qed.

#[using="SO J SC N szc sc jn r"] Lemma X_mod16 : X mod 16 = 0.
Proof.
  (first [ dand9 slot_geom as _ _ _ B0 B16 IDX S16 SMOD _ | destruct slot_geom as (_ & _ & _ & B0 & B16 & IDX & S16 & SMOD & _) ]).
  unfold X. rewrite Z.add_assoc, <- Z.add_mod_idemp_l, <- (Z.add_mod_idemp_l (snd b)), B16 by lia. cbn [Z.add].
  rewrite <- Z.mul_mod_idemp_l, SMOD by lia. reflexivity.
Qed.

#[using="FRESH3 MSmm G0 SO CNT J SC N jn"] Lemma nt_tail_hyps :
  meta_slot nt_stT mm
  /\ get_meta_rec nt_stT mm = mkMeta None None None 0 0 0 0 0 0
  /\ (s_regions nt_stT) !! (fst p) = Some r
  /\ 0 <= snd p /\ snd p mod 16 = 0 /\ snd p + 16 <= round_up_pg (r_len r)
  /\ (s_groups nt_stT) !! p = None
  /\ (forall b' gh, (s_groups nt_stT) !! b' = Some gh -> fst b' = fst p -> snd b' + 9 <= snd p \/ snd p + 9 <= snd b')
  /\ (forall o v t, snd p <= o < snd p + 12 -> (r_cells (get_shadow nt_stT (fst p))) !! o = Some (v, t) -> (t < s_tick nt_stT)%N)
  /\ s_tick nt_stT = s_tick st3.
Proof.
  (first [ dand11 slot_geom as Smem Sreg Skind B0 B16 IDX S16 SMOD SPAN SK NOG | destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG) ]).
  (first [ dand5 ntT_proj as PR PG PA PT _ | destruct ntT_proj as (PR & PG & PA & PT & _) ]).
  split. { eapply meta_slot_same_areas; [| exact MSmm]. rewrite PA. reflexivity. }
  split. { rewrite ntT_rec. destruct (decide (mm = mm)); [reflexivity| congruence]. }
  split. { rewrite PR. exact Sreg. }
  split. { unfold p, X. cbn. lia. }
  split. { exact X_mod16. }
  split. { unfold p. cbn [snd]. lia. }
  split. { rewrite PG. destruct ((s_groups st3) !! p) as [gh|] eqn:E; [|reflexivity]. exfalso.
           destruct (NOG p gh E eq_refl); unfold p in *; cbn in *; lia. }
  split. { intros b' gh Hb' Hf. rewrite PG in Hb'. unfold p in Hf |- *. cbn in Hf |- *. destruct (NOG b' gh Hb' Hf); lia. }
  split. { intros o v t Ho Hc. rewrite PT. unfold p in Ho, Hc. cbn [fst snd] in Ho, Hc.
           rewrite ntT_cells_other in Hc. 2:{ pose proof szc_range. intros [E|[E|[E|(j & Hj & E)]]]; nia. }
           eapply FRESH3; [| exact Hc]. lia. }
  exact PT.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Let stF := st_model nt_stT sc cnt (cnt - 1) mm p.

#[using="FRESH3 MSmm G0 SO CNT J SC N jn r"] Lemma ntF_rec_mt : get_meta_rec stF mm = sm_rec sc cnt (cnt - 1) 0 mm p.
Proof.
  apply smg_rec_mt; [exact SC| exact CNT| apply (proj1 (proj2 nt_tail_hyps))| apply (proj1 (proj2 (proj2 (proj2 nt_tail_hyps))))].
Qed.

#[using="FRESH3 MSmm G0 SO CNT J SC N jn r"] Lemma ntF_stride : get_stride (get_meta_rec stF mm) = 16 * szc.
Proof. rewrite ntF_rec_mt, smg_stride by (exact SC || exact CNT). rewrite andb_false_r. reflexivity. Qed.

Lemma ntF_shadow_eq : s_shadow stF = s_shadow (hdr_havoc p nt_stT).
Proof. exact (proj1 (proj2 (smg_proj nt_stT sc cnt (cnt - 1) mm p))). Qed.

#[using="SO J SC N jn r"] Lemma ntF_cell_read_other o : ~ (X <= o < X + 12) ->
  cell_read (get_shadow stF (fst b)) o = cell_read (get_shadow nt_stT (fst b)) o.
Proof.
  intros Ho. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). apply cell_read_hdr_havoc_other; [exact X_mod16| exact Ho].
Qed.

Lemma ntF_cells o : (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow nt_stT (fst b))) !! o.
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p). rewrite (proj1 (cells_hdr_havoc nt_stT p)). reflexivity.
Qed.

Lemma ntF_havp : r_havp (get_shadow stF (fst b)) = r_havp (get_shadow st3 (fst b)).
Proof.
  unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite (proj2 (cells_hdr_havoc nt_stT p)). unfold p. cbn [fst]. apply (proj2 ntT_hav).
Qed.

Lemma ntF_hav u : u <> X / 16 -> (r_hav (get_shadow stF (fst b))) !! u = (r_hav (get_shadow st3 (fst b))) !! u.
Proof.
  intros NE. unfold get_shadow at 1. rewrite ntF_shadow_eq. fold (get_shadow (hdr_havoc p nt_stT) (fst b)).
  change (fst b) with (fst p) at 1. rewrite hav_hdr_havoc_other by exact NE. unfold p. cbn [fst]. rewrite (proj1 ntT_hav). reflexivity.
Qed.

(* [comment removed for export] *)
#[using="FRESH3 TK3 MSmm G0 FITN STR SO CNT J SC N jn"] Lemma nt_slot_ok (req : Z) : 0 <= req -> req + 4 <= 16 * szc -> slot_ok stF mm p r 0 req.
Proof.
  intros RQ FIT. pose proof szc_range as SZR.
  (first [ dand11 slot_geom as Smem Sreg Skind B0 B16 IDX S16 SMOD SPAN SK NOG | destruct slot_geom as (Smem & Sreg & Skind & B0 & B16 & IDX & S16 & SMOD & SPAN & SK & NOG) ]).
  (first [ dand10 nt_tail_hyps as TMS TREC TREG TP0 TP16 TPEND TGN TNOG TOLD TTK | destruct nt_tail_hyps as (TMS & TREC & TREG & TP0 & TP16 & TPEND & TGN & TNOG & TOLD & TTK) ]).
  pose proof ntF_stride as STF.
  pose proof (mask_upto_range' (cnt - 1) ltac:(lia)) as [C1 C2].
  (first [ pose proof ((smg_proj nt_stT sc cnt (cnt - 1) mm p)) as dR_8; dand5 dR_8 as PF1 PF2 PF3 PF4 _ | destruct (smg_proj nt_stT sc cnt (cnt - 1) mm p) as (PF1 & PF2 & PF3 & PF4 & _) ]). fold stF in PF1, PF2, PF3, PF4.
  (first [ dand5 ntT_proj as PR PG PA PT _ | destruct ntT_proj as (PR & PG & PA & PT & _) ]).
  constructor; rewrite ?STF.
  - rewrite ntF_rec_mt. reflexivity.
  - rewrite PF1, PR. exact Sreg.
  - exact Skind.
  - exact TP0.
  - exact TP16.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_last_idx sm_rec snd]. replace (cnt - 1 + 1) with cnt by lia. unfold p, X. cbn [snd]. unfold X in SPAN. nia.
  - lia.
  - rewrite Z.mul_comm. apply Z_mod_mult.
  - lia.
  - exact RQ.
  - exact FIT.
  - intros b' gh Hb' Hf. destruct (smg_groups_inv nt_stT sc cnt (cnt - 1) mm p b' gh Hb') as [[-> _]|[NE Hb3]].
    + left. unfold p. cbn [snd]. lia.
    + rewrite PG in Hb3. unfold p in Hf |- *. cbn [fst snd] in Hf |- *. destruct (NOG b' gh Hb3 Hf) as [H|H]; [left; lia| right]. clear - H FITN STR CNT SZR; nia.   (* [comment removed for export] *)
  - unfold p at 1 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0 - 4) with (X + 12) by lia.
    rewrite ntF_cell_read_other by lia. replace (X + 12) with (X + 12 + 0 * (16 * szc)) by lia. apply ntT_cell_read_zero. lia.
  - intros off O0 OF. rewrite Z.mul_0_r, Z.add_0_l. rewrite Z.mul_comm, Z_div_mult by lia. lia.
  - unfold p at 2. cbn [fst snd]. replace (X + 16 + 16 * szc * 0) with (snd p + 16) by (unfold p; cbn; lia). change (fst b) with (fst p).
    apply (smg_slot0 nt_stT sc cnt (cnt - 1) 0 mm p SC CNT TREC). rewrite <- ntF_rec_mt, STF. lia.
  - apply (proj1 (smg_meta_slot nt_stT sc cnt (cnt - 1) mm p mm)). exact TMS.
  - rewrite ntF_rec_mt. cbn [m_avail sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freed sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_freeable sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_maplen sm_rec]. lia.
  - rewrite ntF_rec_mt. cbn [m_sizeclass sm_rec]. lia.
Qed.

(* [comment removed for export] *)
#[using="CNT J SC N jn"] Lemma ntF_span_cells o : X + 16 <= o < X + 16 + 16 * szc - 4 ->
  (r_cells (get_shadow stF (fst b))) !! o = (r_cells (get_shadow st3 (fst b))) !! o.
Proof.
  intros Ho. pose proof szc_range. rewrite ntF_cells. apply ntT_cells_other.
  intros [E|[E|[E|(j & Hj & E)]]]; try lia. assert (j = 0 \/ 1 <= j) as [->|J1] by lia; nia.
Qed.

#[using="SO J SC N jn r"] Lemma ntF_span_hav o : X + 16 <= o -> (r_hav (get_shadow stF (fst b))) !! (o / 16) = (r_hav (get_shadow st3 (fst b))) !! (o / 16).
Proof. intros Ho. apply ntF_hav. pose proof X_mod16. Z.div_mod_to_equations. lia. Qed.

(* [comment removed for export] *)
#[using="SO CNT J SC N jn r"] Lemma ntF_rdv13 o :
  (r_cells (get_shadow st3 (fst b))) !! (X + 13) = None ->
  (r_hav (get_shadow st3 (fst b))) !! ((X + 13) / 16) = None ->
  (r_havp (get_shadow st3 (fst b))) !! ((X + 13) / 4096) = None ->
  rdv pans_mem o stF (fst b, X + 13) = 0.
Proof.
  intros HC HH HP. pose proof szc_range. unfold rdv. cbn [fst snd]. rewrite ntF_cell_read_other by lia.
  rewrite ntT_cell_read_other. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; nia. }
  unfold cell_read. rewrite HC, HH, HP. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="TK3 SO CNT J SC N jn r"] Lemma ntF_unknown off h : 0 <= off ->
  cell_read (get_shadow stF (fst b)) off = Unknown h ->
  grp_hdr_cov stF (fst b) off
  \/ (cell_read (get_shadow st3 (fst b)) off = Unknown h /\ ~ (X - 3 <= off < X) /\ ~ (exists j, 0 <= j <= cnt /\ off = X + 12 + j * (16 * szc))).
Proof.
  intros Ho Hc. pose proof szc_range as SZR.
  destruct (Z_lt_le_dec off X) as [L|GE]; [| destruct (Z_lt_le_dec off (X + 12)) as [L2|GE2]].
  2:{ left. change (fst b) with (fst p). apply smg_grp_hdr_cov; [exact SC|]. unfold p. cbn [snd]. lia. }
  all: right; rewrite ntF_cell_read_other in Hc by lia.
  - destruct (Z_lt_le_dec off (X - 3)) as [L3|GE3].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; first [lia | nia]. }
      split; [exact Hc|]. split; [lia|]. ((first [ intro dR_10; dex1 dR_10 as j; destruct dR_10 as [Hj E] | intro dR_10; dand3 dR_10 as j Hj E | intros (j & Hj & E) ])). nia.
    + exfalso. destruct (ntT_cell_read_hdr (X - off) ltac:(lia)) as [v Hv]. replace (X - (X - off)) with off in Hv by lia. rewrite Hv in Hc. discriminate.
  - destruct (Z.eq_dec ((off - X - 12) mod (16 * szc)) 0) as [M0|M1];
      [destruct (Z_lt_le_dec cnt ((off - X - 12) / (16 * szc))) as [QB|QS]|].
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia. }
      split; [exact Hc|]. split; [lia|]. ((first [ intro dR_11; dex1 dR_11 as j; destruct dR_11 as [Hj E] | intro dR_11; dand3 dR_11 as j Hj E | intros (j & Hj & E) ])).
      assert (j = (off - X - 12) / (16 * szc)) by (subst off; replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia; rewrite Z_div_mult by lia; reflexivity). lia.
    + exfalso. pose proof (Z.div_mod (off - X - 12) (16 * szc) ltac:(lia)) as DM. rewrite M0, Z.add_0_r in DM.
      pose proof (Z.div_pos (off - X - 12) (16 * szc) ltac:(lia) ltac:(lia)) as QP.
      pose proof (ntT_cell_read_zero ((off - X - 12) / (16 * szc)) ltac:(lia)) as Hz.
      replace (X + 12 + (off - X - 12) / (16 * szc) * (16 * szc)) with off in Hz by lia. rewrite Hz in Hc. discriminate.
    + rewrite ntT_cell_read_other in Hc. 2:{ intros [E|[E|[E|(j & Hj & E)]]]; try lia.
        apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult. }
      split; [exact Hc|]. split; [lia|]. ((first [ intro dR_12; dex1 dR_12 as j; destruct dR_12 as [Hj E] | intro dR_12; dand3 dR_12 as j Hj E | intros (j & Hj & E) ])).
      apply M1. subst off. replace (X + 12 + j * (16 * szc) - X - 12) with (j * (16 * szc)) by lia. apply Z_mod_mult.
Qed.

Lemma ntF_shadow_other q : q <> fst b -> get_shadow stF q = get_shadow st3 q.
Proof.
  intros NE. unfold stF. rewrite (smg_shadow_other nt_stT sc cnt (cnt - 1) mm p q) by exact NE. apply ntT_shadow_other. exact NE.
Qed.
End NEST.
End ASlo1am.

   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section MMEQ.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)
Context {R : Type}.
Variables (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

Definition mm_after (st2 : mstate) (m : aptr) (c nd : Z) : Z -> Malloc.M R :=
  let size := UNIT * size_class sc in
  let st1 := step_seq (account_bounce sc st2) in
  fun r =>
        if negb (mmap_answer_ok (live_ranges st1) nd r) then bad_answer bail else
        if is_err r then free_meta m st1 (fun st2 => as_kq sc k bail st2 None) bail
        else
          let '(st2, rid) := new_region RKGroup r nd st1 in
          let st3 := upd_meta m (m_set_maplen (Z.shiftr nd 12)) st2 in
          let st4 := upd_ctx (fun c => set_mmap_counter (u32 (c_mmap_counter c + 1)) c) st3 in
          let ai := (4096 - UNIT) / size - 1 in
          let ai := if c - 1 <? ai then c - 1 else ai in
          let ai := if ai <? 0 then 0 else ai in
          ag_tail full_lay st4 sc m (rid, 0) c ai (as_kq sc k bail).

Lemma ag_mmap_eq st2 m cnt :
  ag_mmap sc req k bail st2 m cnt =
  (let '(c, nd) := mm_final (UNIT * size_class sc) req (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc))
                              (mm_cnt_red sc (UNIT * size_class sc) cnt (mm_usage1 (step_seq (account_bounce sc st2)) sc (usage st2 sc)) (is_bouncing sc st2))
                              (is_bouncing sc st2) in
   SVis (EMmap 0 nd PROT_RW (MAP_PRIVATE + MAP_ANON)) (mm_after st2 m c nd)).
Proof. reflexivity. Qed.
End MMEQ.

Section TAILEQ.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).
Lemma ag_tail_kq_eq stT mm p c ai :
  m_next (get_meta_rec stT mm) = None -> m_prev (get_meta_rec stT mm) = None -> active stT sc = None ->
  ag_tail full_lay stT sc mm p c ai (as_kq sc k bail) = k (st_model stT sc c ai mm p) 0.
Proof.
  intros HN HP HA. unfold ag_tail, as_kq. cbv zeta. cbn [lh_hdr full_lay].
  rewrite as_queue_eq.
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_next m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HN. }
  2:{ unfold upd_meta, add_slots. rewrite get_meta_rec_put_same. cbn [m_prev m_set_avail].
      rewrite rec_set_slots, rec_put_group, get_meta_rec_put_same. cbn [m_next m_prev m_set_sizeclass m_set_freeable m_set_last_idx m_set_mem m_set_freed m_set_avail].
      rewrite rec_set_usage, rec_hdr_havoc. exact HP. }
  unfold as_queue_st. cbn [get_head].
  match goal with |- context [active ?X sc] => replace (active X sc) with (active stT sc) by reflexivity end.
  rewrite HA. unfold as_fm_single, st_model. cbn [set_head]. reflexivity.
Qed.
End TAILEQ.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mm_cnt_red_range sc size cnt u1 nos : 1 <= cnt <= 32 -> 1 <= mm_cnt_red sc size cnt u1 nos <= 32.
Proof.
  intros H. unfold mm_cnt_red.
  destruct (_ && _); [|lia]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); [lia|]. destruct (_ && _); lia.
Qed.

Lemma round_up_pg_props x : 0 <= x -> x <= round_up_pg x < x + 4096 /\ round_up_pg x mod 4096 = 0.
Proof.
  intros Hx. unfold round_up_pg. change (PGSZ - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096.
  Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma mm_final_props size req u1 cnt nos c nd :
  1 <= cnt <= 32 -> 16 <= size -> 0 <= req -> req + 4 <= size ->
  mm_final size req u1 cnt nos = (c, nd) ->
  1 <= c <= cnt /\ nd mod 4096 = 0 /\ req + 20 <= nd
  /\ (c = 1 /\ nd = round_up_pg (req + 20) \/ size * c + 16 <= nd /\ nd = round_up_pg (size * c + 16)).
Proof.
  intros HC HS HR HF E. unfold mm_final, mm_small in E. cbv zeta in E.
  pose proof (round_up_pg_props (req + 20) ltac:(lia)) as [R1 R2].
  pose proof (round_up_pg_props (size * cnt + 16) ltac:(nia)) as [N1 N2].
  change (req + IB + UNIT) with (req + 4 + 16) in E. replace (req + 4 + 16) with (req + 20) in E by lia.
  change (size * cnt + UNIT) with (size * cnt + 16) in E.
  destruct (negb nos && (cnt <=? 7)).
  - destruct (Z.ltb_spec (round_up_pg (req + 20)) (size + UNIT)) as [L|G]; cbn [orb] in E.
    + inversion E; subst. unfold UNIT in L. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
    + destruct ((4 * PGSZ <=? round_up_pg (req + 20)) && (u1 <? 2 * cnt)).
      * inversion E; subst. unfold UNIT in G. split; [lia|]. split; [lia|]. split; [lia|]. left; auto.
      * inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
  - inversion E; subst. split; [lia|]. split; [lia|]. split; [nia|]. right; split; [nia| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling} {Rr : RunRandom}.  (* [comment removed for export] *)

Lemma stS_shape sc st2 : exists f, step_seq (account_bounce sc st2) = upd_ctx f st2
  /\ forall c, c_active (f c) = c_active c /\ c_usage (f c) = c_usage c /\ c_brk (f c) = c_brk c
     /\ c_mmap_counter (f c) = c_mmap_counter c /\ c_free_meta_head (f c) = c_free_meta_head c
     /\ c_avail_meta (f c) = c_avail_meta c /\ c_secret (f c) = c_secret c /\ c_init_done (f c) = c_init_done c
     /\ c_avail_meta_count (f c) = c_avail_meta_count c /\ c_avail_meta_area_count (f c) = c_avail_meta_area_count c
     /\ c_meta_alloc_shift (f c) = c_meta_alloc_shift c /\ c_meta_area_head (f c) = c_meta_area_head c
     /\ c_meta_area_tail (f c) = c_meta_area_tail c /\ c_avail_meta_areas (f c) = c_avail_meta_areas c.
Proof.
  assert (AB : exists g, account_bounce sc st2 = upd_ctx g st2 /\ forall c, g c = c \/ exists v, g c = set_bounces_map (<[sc - 7 := v]> (c_bounces c)) c).
  { unfold account_bounce, set_bounce.
    destruct (sc_in_seq_range sc); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (negb _ && _); [| exists (fun c => c); split; [destruct st2; reflexivity| intros; left; reflexivity]].
    destruct (_ <? 100); (eexists; split; [reflexivity| intros c; right; eexists; reflexivity]). }
  destruct AB as (g & EG & HG).
  rewrite step_seq_eq. rewrite EG.
  destruct (c_seq (ctx (upd_ctx g st2)) =? 255).
  - exists (fun c => set_seq 1 (set_unmap_seq_map ∅ (g c))). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
  - exists (fun c => set_seq (c_seq (g c) + 1) (g c)). split; [destruct st2; reflexivity|].
    intros c. destruct (HG c) as [E|[v E]]; rewrite E; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity.
Qed.

End CEIL.

(* [comment removed for export] *)
