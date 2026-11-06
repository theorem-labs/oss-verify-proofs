(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith NArith List Lia Bool.
From stdpp Require gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup QWxq_c1 Lib.GwApply Qfw3_c1 Q9A7 QlEo_c1 Q5Rg QnDM_c1 Q2qa Qy5Y Q4J3 QytA QJE4 Qnxq QZAi QUZl Q7S0 Ql2m QGeV Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 Qy5Y.Mq1 Q4J3.Mq1 QytA QJE4.Mq4 Qnxq.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section TA.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R).

Definition ta_avz (st3 : mstate) (m3 : aptr) : QUZl.M R :=
activate_group m3 st3 (fun st4 mask =>
guard 40 (negb (mask =? 0)) (
ta_fin (decay_bounces (m_sizeclass (get_meta_rec st4 m3)) st4) m3 mask k) bail) bail.

Definition ta_act (st2 : mstate) (m2 : aptr) (mask : Z) : QUZl.M R :=
let mr2 := get_meta_rec st2 m2 in
let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
let '(st3, m3) :=
if Z.land mask (mask_upto gai) =? 0 then
if negb (optr_eqb (m_next mr2) (Some m2)) then
match m_next mr2 with
| Some mn => (set_active sc (Some mn) st2, mn)
| None => (st2, m2)
end
else
let cnt := gai + 2 in
let size := size_class (m_sizeclass mr2) * UNIT in
let span := UNIT + size * cnt in
let cnt := span_loop 300%nat cnt span size in
let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
match m_mem mr2 with
| Some g => (set_group_active_idx g (cnt - 1) st2, m2)
| None => (st2, m2)
end
else (st2, m2) in
ta_avz st3 m3.

Definition ta_m (st1 : mstate) (m1 : aptr) : QUZl.M R :=
let mask := m_freed (get_meta_rec st1 m1) in
let '(st2, m2, mask) :=
let mr := get_meta_rec st1 m1 in
if (mask =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0) then
match m_next mr with
| Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn))
| None => (st1, m1, mask)
end
else (st1, m1, mask) in
ta_act st2 m2 mask.

#[using="Type"] Lemma try_avail_eq st :
try_avail sc st k bail =
match active st sc with
| None => k st 0
| Some m =>
if negb (m_avail (get_meta_rec st m) =? 0) then ta_fin st m (m_avail (get_meta_rec st m)) k else
let step1 : option (mstate * aptr) :=
if m_freed (get_meta_rec st m) =? 0 then
let st1 := dequeue (LActive sc) m st in
match active st1 sc with None => None | Some m1 => Some (st1, m1) end
else
match m_next (get_meta_rec st m) with
| Some m1 => Some (set_active sc (Some m1) st, m1)
| None => None
end in
match step1 with
| None => if m_freed (get_meta_rec st m) =? 0 then k (dequeue (LActive sc) m st) 0
else SVis (EUndef UBadPtr) (fun _ => bail)
| Some (st1, m1) => ta_m st1 m1
end
end.
Proof. reflexivity. Qed.
End TA.

Section AS.
Context {R : Type}.
Variables (lay : layout_hook) (f : nat) (sc req : Z) (k : mstate -> Z -> QUZl.M R) (bail : QUZl.M R).

Definition as_grp (st1 : mstate) : QUZl.M R :=
alloc_group R lay (alloc_slot lay f) st1 sc req (fun st2 go =>
match go with
| None => k st2 (-1)
| Some g =>
let st3 := upd_meta g (fun r => m_set_avail (m_avail r - 1) r) st2 in
queue (LActive sc) g st3 (fun st4 => k st4 0) bail
end) bail.

Definition as_k (st1 : mstate) (first : Z) : QUZl.M R :=
if negb (first =? 0) then k st1 (ctz32 first) else as_grp st1.

#[using="Type"] Lemma alloc_slot_S st : alloc_slot lay (S f) st sc req k bail = try_avail sc st as_k bail.
Proof. reflexivity. Qed.
End AS.

Fixpoint span_exit (fuel : nat) (span size : Z) : bool :=
match fuel with
| O => false
| S f => if Z.lxor span (span + size - 1) <? 4096 then span_exit f (span + size) size else true
end.

Definition span_fn (sc cnt : Z) : bool :=
span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16).
Definition span_chk (sc : Z) : bool := forallb (span_fn sc) (zseq 2 32).

#[using="Type"] Lemma span_chk_true : forallb span_chk (zseq 1 47) = true.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma span_fn_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 -> span_fn sc cnt = true.
Proof.
intros Hsc Hc.
pose proof (forallb_zseq span_chk 1 47 sc span_chk_true ltac:(lia) ltac:(lia)) as X. unfold span_chk in X.
exact (forallb_zseq (span_fn sc) 2 32 cnt X ltac:(lia) ltac:(lia)).
Qed.

#[using="Type"] Lemma span_exit_ok sc cnt : 1 <= sc < 48 -> 2 <= cnt <= 33 ->
span_exit 300 (16 + size_class sc * 16 * cnt) (size_class sc * 16) = true.
Proof. intros Hsc Hc. exact (span_fn_ok sc cnt Hsc Hc). Qed.

End RC__1.
End Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 Q4J3.Mq2.
Import QJE4.Mq0 QJE4.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pgal (z : Z) : Prop := z mod 4096 = 0.

#[using="Type"] Lemma carve_st_some st p tl ar :
c_meta_area_tail (ctx st) = Some tl -> (s_areas st) !! tl = Some ar -> (s_areas st) !! p = None ->
carve_st st p =
let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
let st2 := set_areas (<[tl := mkArea (a_check ar) (Some p) (a_nslots ar)]> (s_areas st1)) st1 in
let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
intros HT Har Hp. assert (NE : tl <> p) by (intros ->; rewrite Hp in Har; discriminate).
unfold carve_st.
cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
cbn [s_areas upd_ctx set_areas]. rewrite Har. rewrite lookup_insert_ne by exact NE. rewrite Hp. reflexivity.
Qed.

#[using="Type"] Lemma carve_st_none st p :
c_meta_area_tail (ctx st) = None -> (s_areas st) !! p = None ->
carve_st st p =
let st1 := upd_ctx (fun c => set_avail_meta_areas (Some (aadd p 4096)) (set_avail_meta_area_count (c_avail_meta_area_count c - 1) c)) st in
let st2 := upd_ctx (set_meta_area_head (Some p)) st1 in
let stC := upd_ctx (set_meta_area_tail (Some p)) st2 in
set_areas (<[p := mkArea (c_secret (ctx st2)) None NSLOTS]> (s_areas stC)) stC.
Proof.
intros HT Hp. unfold carve_st.
cbn [ctx upd_ctx s_ctx set_avail_meta_areas set_avail_meta_area_count c_meta_area_tail]. rewrite HT.
cbn [s_areas upd_ctx set_areas]. rewrite Hp. reflexivity.
Qed.

End RC__1.
End Mq1.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 Q4J3.Mq2 QJE4.Mq3.
Import QJE4.Mq0.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Ltac ctx_cells_cbn :=
cbn [ctx set_head upd_ctx s_ctx set_free_meta_head set_avail_meta set_avail_meta_count c_secret c_init_done c_mmap_counter c_free_meta_head c_avail_meta
c_avail_meta_count c_avail_meta_area_count c_meta_alloc_shift c_meta_area_head c_meta_area_tail c_avail_meta_areas].
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma am_take_eq {R} st (k : mstate -> optr -> M R) bail q :
c_avail_meta (ctx st) = Some q ->
am_take st k bail = k (am_took st q (c_avail_meta_count (ctx st) - 1)) (Some q).
Proof. intros H. unfold am_take. rewrite H. reflexivity. Qed.

End RC__1.
End Mq2.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.

Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq3 Q4J3.Mq2.
Import QJE4.Mq0 QJE4.Mq1.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac showregs := lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "REGS" R "PC" pc "MEM" m end.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition am_init_st (st : mstate) : mstate :=
if c_init_done (ctx st) =? 0 then upd_ctx (fun c => set_init_done 1 (set_secret (s_secret st) c)) st else st.

End RC__1.
End Mq3.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA.
Import QZAi.Mq2 QUZl Q7S0.Mq0.
Import Qy5Y.Mq6 Q4J3.Mq4 QPjm.Mq0 Q4J3.Mq2 QJE4.Mq3.
Import QPjm.Mq3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope bv_scope.
Open Scope Z_scope.

End Mq4.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QYTG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq5.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup QWxq_c1.Mq0 OSSVerify.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge Qfw3_c1.Mq2 Q9A7.Mq1 QlEo_c1.Mq0 QWxq_c1.Mq1 Q5Rg.Mq0 Q5Rg.
Import QnDM_c1.Mq0 Q2qa.Mq1 QytA QJE4.Mq4.
Import QZAi.Mq2 QUZl Q7S0.Mq0 Ql2m.Mq3 QGeV.

Import Qy5Y.Mq5.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PEXT.
Variables (st st' : mstate) (P : N -> Prop).
Hypothesis HP : ptrs_in P st.
Hypothesis Hconc : forall q, P (fst q) -> conc st' q = conc st q.
Hypothesis Hctx : ctx st' = ctx st.
Hypothesis Hmetas : s_metas st' = s_metas st.

#[using="Hconc"] Lemma pw_extP p : optr_in P p -> pw st' p = pw st p.
Proof. destruct p as [q|]; cbn; intros H; unfold pw, oconc; [rewrite Hconc by exact H|]; reflexivity. Qed.

#[using="Hmetas"] Lemma get_meta_rec_extP g : get_meta_rec st' g = get_meta_rec st g.
Proof. unfold get_meta_rec. rewrite Hmetas. reflexivity. Qed.

#[using="P HP Hconc"] Lemma meta_cells_extP g : meta_cells st' (get_meta_rec st g) = meta_cells st (get_meta_rec st g).
Proof.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & H8 & _). destruct (H8 g) as (X1 & X2 & X3).
unfold meta_cells. rewrite !pw_extP by assumption. reflexivity.
Qed.

End PEXT.

Definition agree_on (m m' : mem) (A n : Z) : Prop :=
forall a, A <= a < A + n -> m' (wa a) = m (wa a).

#[using="Type"] Lemma agree_on_sub m m' A n A' n' : agree_on m m' A n -> A <= A' -> A' + n' <= A + n -> agree_on m m' A' n'.
Proof. intros AG H1 H2 a Ha. apply AG. lia. Qed.

#[using="Type"] Lemma mmap_len_round_up l : mmap_len l = round_up_pg l.
Proof. unfold mmap_len. symmetry. apply QYTG.Mq0.round_up_pg_eq. Qed.

#[using="Type"] Lemma round_up_pg_mod x : round_up_pg x mod 4096 = 0.
Proof. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. Z.div_mod_to_equations. lia. Qed.

#[using="Type"] Lemma cell_read_shadow0 o : cell_read shadow0 o = Known 0.
Proof. unfold cell_read, shadow0. cbn. rewrite !lookup_empty. reflexivity. Qed.

Section NEWREGION.
Variables (st : mstate) (m m' : mem) (x len : Z) (k : rkind).
Let rid := s_next_rid st.
Let L := round_up_pg len.
Let r0 := mkRegion k x len.
Let st' := fst (new_region k x len st).

Hypothesis PT : ptrs_in (fun r => r <> rid) st.
Hypothesis FRr : (s_regions st) !! rid = None.
Hypothesis FRs : (s_shadow st) !! rid = None.
Hypothesis X0 : 0 < x.
Hypothesis XA : x mod 4096 = 0.
Hypothesis LEN : 0 <= len.
Hypothesis XC : x + L <= alloc_ceiling.
Hypothesis RF : ranges_free (live_ranges st) x L = true.

Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < x \/ x + L <= a) -> m' (wa a) = m (wa a).
Hypothesis ZF : k = RKGroup -> forall a, x <= a < x + L -> m' (wa a) = Some (b8 0).

#[using="Type"] Lemma nr_regions : s_regions st' = <[rid := r0]> (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma nr_lookup_new : (s_regions st') !! rid = Some r0.
Proof. rewrite nr_regions. apply lookup_insert_eq. Qed.
#[using="r0"] Lemma nr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite nr_regions. rewrite lookup_insert_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma nr_lookup_inv q r : (s_regions st') !! q = Some r -> (q = rid /\ r = r0) \/ (q <> rid /\ (s_regions st) !! q = Some r).
Proof.
intros H. destruct (N.eq_dec q rid) as [->|NE].
- left. rewrite nr_lookup_new in H. inversion H. auto.
- right. rewrite nr_lookup_old in H by exact NE. auto.
Qed.
#[using="r0"] Lemma nr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite nr_lookup_old by assumption. reflexivity. Qed.
#[using="r0"] Lemma nr_conc_new off : conc st' (rid, off) = x + off.
Proof. unfold conc, get_region. cbn [fst snd]. rewrite nr_lookup_new. reflexivity. Qed.
#[using="Type"] Lemma nr_shadow q : get_shadow st' q = get_shadow st q.
Proof. reflexivity. Qed.
#[using="RC__ st m' rid L ZF"] Lemma nr_lr_lo_new : x <= lr_lo r0.
Proof. unfold lr_lo, r0. cbn. destruct k; lia. Qed.

#[using="RC__ rid RF"] Lemma nr_old_disjoint q r : (s_regions st) !! q = Some r ->
x + L <= lr_lo r \/ r_base r + round_up_pg (r_len r) <= x.
Proof.
intros Hr. pose proof (In_live_ranges st q r Hr) as HI.
unfold region_live_range in HI. unfold lr_lo. unfold PGSZ in HI.
destruct (r_kind r); (pose proof (ranges_free_In _ _ _ _ _ RF HI); lia).
Qed.

#[using="Type"] Lemma ticks_ok_new_region : ticks_ok st -> ticks_ok st'.
Proof. intros H. exact H. Qed.

#[using="Type"] Lemma ptrs_in_new_region (P : N -> Prop) : ptrs_in P st -> ptrs_in P st'.
Proof. intros H. exact H. Qed.
End NEWREGION.

Section DROPREGION.
Variables (st : mstate) (m m' : mem) (rid : N) (r : region).
Let st' := drop_region rid st.

Hypothesis Hr : (s_regions st) !! rid = Some r.
Hypothesis PT : ptrs_in (fun q => q <> rid) st.
Hypothesis AG : forall a, 0 <= a < 2^64 -> (a < lr_lo r \/ r_base r + round_up_pg (r_len r) <= a) ->
(MLOCK <= a < MLOCK + 4 \/ LIBC <= a < LIBC + 0x408 \/ exists q rq, (s_regions st) !! q = Some rq /\ lr_lo rq <= a < r_base rq + round_up_pg (r_len rq)) ->
m' (wa a) = m (wa a).

#[using="Type"] Lemma dr_regions : s_regions st' = delete rid (s_regions st).
Proof. reflexivity. Qed.
#[using="Type"] Lemma dr_lookup_inv q rq : (s_regions st') !! q = Some rq -> q <> rid /\ (s_regions st) !! q = Some rq.
Proof.
intros H. rewrite dr_regions in H. destruct (N.eq_dec q rid) as [->|NE].
- rewrite lookup_delete_eq in H. discriminate.
- rewrite lookup_delete_ne in H by congruence. auto.
Qed.
#[using="Type"] Lemma dr_lookup_old q : q <> rid -> (s_regions st') !! q = (s_regions st) !! q.
Proof. intros. rewrite dr_regions. rewrite lookup_delete_ne by congruence. reflexivity. Qed.
#[using="Type"] Lemma dr_conc q : fst q <> rid -> conc st' q = conc st q.
Proof. intros. unfold conc, get_region. rewrite dr_lookup_old by assumption. reflexivity. Qed.
#[using="Type"] Lemma dr_shadow q : q <> rid -> get_shadow st' q = get_shadow st q.
Proof. intros. unfold get_shadow. unfold st', drop_region. cbn [s_shadow set_shadow set_regions]. rewrite lookup_delete_ne by congruence. reflexivity. Qed.

#[using="Type"] Lemma ticks_ok_drop_region : ticks_ok st -> ticks_ok st'.
Proof.
intros [T1 T2]. split.
- intros q sh u hl ch Hq Hu Hin. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T1 q sh u hl ch Hq Hu Hin).
- intros q sh pg t Hq Hp. unfold st', drop_region in Hq. cbn [s_shadow set_shadow set_regions] in Hq.
destruct (N.eq_dec q rid) as [->|NE]; [rewrite lookup_delete_eq in Hq; discriminate|].
rewrite lookup_delete_ne in Hq by congruence. exact (T2 q sh pg t Hq Hp).
Qed.
End DROPREGION.

#[using="Type"] Lemma ptrs_in_set_tick P st t : ptrs_in P st -> ptrs_in P (set_tick t st).
Proof. intros H; exact H. Qed.
#[using="Type"] Lemma ptrs_in_upd_ctx_scalar P st f :
(forall c, c_free_meta_head (f c) = c_free_meta_head c) -> (forall c, c_avail_meta (f c) = c_avail_meta c) ->
(forall c, c_meta_area_head (f c) = c_meta_area_head c) -> (forall c, c_meta_area_tail (f c) = c_meta_area_tail c) ->
(forall c, c_avail_meta_areas (f c) = c_avail_meta_areas c) -> (forall c, c_active (f c) = c_active c) ->
(forall c, c_brk (f c) = c_brk c) ->
ptrs_in P st -> ptrs_in P (upd_ctx f st).
Proof.
intros E1 E2 E3 E4 E5 E6 E7 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx upd_ctx s_metas s_areas s_groups] in *.
rewrite E1, E2, E3, E4, E5, E6, E7.
split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
split; [exact H6|]. split; [exact H7|]. split; [|split; [exact H9| exact H10]].
intros g. exact (H8 g).
Qed.
#[using="Type"] Lemma ptrs_in_step_seq P st : ptrs_in P st -> ptrs_in P (step_seq st).
Proof. intros H. unfold step_seq. destruct (c_seq (ctx st) =? 255); (apply ptrs_in_upd_ctx_scalar; [..|exact H]; reflexivity). Qed.
#[using="Type"] Lemma ptrs_in_put_meta P st g mr :
optr_in P (m_prev mr) -> optr_in P (m_next mr) -> optr_in P (m_mem mr) ->
ptrs_in P st -> ptrs_in P (put_meta g mr st).
Proof.
intros Q1 Q2 Q3 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx put_meta set_metas s_metas s_areas s_groups] in *.
split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
split; [|auto]. intros g'. unfold get_meta_rec. cbn [s_metas put_meta set_metas].
destruct (decide (g' = g)) as [->|NE].
- rewrite lookup_insert_eq. cbn. auto.
- rewrite lookup_insert_ne by congruence. apply H8.
Qed.
#[using="Type"] Lemma ptrs_in_put_group P st b mo ai :
P (fst b) -> optr_in P mo -> ptrs_in P st -> ptrs_in P (put_group b mo ai st).
Proof.
intros Q1 Q2 (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10).
unfold ptrs_in, ctx, active in *. cbn [s_ctx put_group set_groups s_metas s_areas s_groups get_meta_rec] in *.
split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|]. split; [auto|].
split; [exact H8|]. split; [exact H9|].
intros b' gh Hb'. destruct (decide (b' = b)) as [->|NE].
- rewrite lookup_insert_eq in Hb'. inversion Hb'; subst. cbn. auto.
- rewrite lookup_insert_ne in Hb' by congruence. exact (H10 b' gh Hb').
Qed.
#[using="Type"] Lemma ptrs_in_hdr_havoc P st b : ptrs_in P st -> ptrs_in P (hdr_havoc b st).
Proof. intros H; exact H. Qed.
#[using="Type"] Lemma ptrs_in_set_slots P st v : ptrs_in P st -> ptrs_in P (set_slots v st).
Proof. intros H; exact H. Qed.

End RC__1.
End Mq5.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q9A7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q9A7.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q2qa.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q2qa.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPjm.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPjm. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QJE4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJE4.
Import ListNotations. Unset Keyed Unification.
Local Open Scope Z_scope.

From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac flia ::= flia_fast. Local Ltac mkr__flia_1 := flia_fast.
Local Ltac unfold_sf_in H ::= unfold_sf_in_recast H. Local Ltac mkr__unfold_sf_in_2 H := unfold_sf_in_recast H.
Local Ltac blia ::= blia_fast. Local Ltac mkr__blia_3 := blia_fast.

Local Ltac step ::= step_fast. Local Ltac mkr__step_4 := step_fast.
Local Ltac zsimp ::= zsimp_fast. Local Ltac mkr__zsimp_5 := zsimp_fast.

Definition f128_div_entry := 0x11338%Z.

Section Model.
Variables a_lo a_hi b_lo b_hi : Z.
Let aExp := shr64 (shl64 a_hi 1) 49.
Let bExp := shr64 (shl64 b_hi 1) 49.
Let signHi := shl64 (shr64 (Z.lxor b_hi a_hi) 63) 63.
Let aSigHi := Z.land a_hi MASK48.
Let bSigHi := Z.land b_hi MASK48.
Let aAbsHi := Z.land a_hi ABS_HI.
Let bAbsHi := Z.land b_hi ABS_HI.

Definition FD_p2b (aSigHi1 aLo1 scale1 : Z) : Z :=
let '(bSigHi1, bLo1, scale2) :=
if shr64 bAbsHi 48 =? 0 then
let '(nhi, nlo, nclz) := norm_denormal bSigHi b_lo in (nhi, nlo, (scale1 + nclz) - 16)
else (bSigHi, b_lo, scale1) in
div_core signHi aExp bExp aSigHi1 aLo1 bSigHi1 bLo1 scale2.

Definition FD_p2 : Z :=
let '(aSigHi1, aLo1, scale1) :=
if shr64 aAbsHi 48 =? 0 then
let '(nhi, nlo, nclz) := norm_denormal aSigHi a_lo in (nhi, nlo, 16 - nclz)
else (aSigHi, a_lo, 0) in
FD_p2b aSigHi1 aLo1 scale1.

Definition FD_inf : Z :=
if Z.lor (Z.lxor aAbsHi INF_HI) a_lo =? 0 then
(if negb (Z.lor b_lo (Z.lxor bAbsHi INF_HI) =? 0) then mk128 (Z.lor signHi INF_HI) 0 else mk128 QNAN_HI 0)
else if Z.lor b_lo (Z.lxor bAbsHi INF_HI) =? 0 then mk128 signHi 0
else if Z.lor a_lo aAbsHi =? 0 then
(if negb (Z.lor b_lo bAbsHi =? 0) then mk128 signHi 0 else mk128 QNAN_HI 0)
else if Z.lor b_lo bAbsHi =? 0 then mk128 (Z.lor signHi INF_HI) 0
else FD_p2.

Definition FD_b : Z :=
let bIsNaN := if bAbsHi =? INF_HI then negb (b_lo =? 0) else negb (bAbsHi <? INF_HI) in
if bIsNaN then mk128 (Z.lor b_hi QUIET_HI) b_lo else FD_inf.

Definition FD_a : Z :=
let aIsNaN := if aAbsHi =? INF_HI then negb (a_lo =? 0) else negb (aAbsHi <? INF_HI) in
if aIsNaN then mk128 (Z.lor a_hi QUIET_HI) a_lo else FD_b.

Definition FD_0b : Z :=
let bExpM := add64 bExp 0xffffffffffff8001 in
if bExpM <=? 0xffffffffffff8001 then FD_a
else div_core signHi aExp bExp aSigHi a_lo bSigHi b_lo 0.
Definition f128_div_w : Z :=
let aExpM := add64 aExp 0xffffffffffff8001 in
if aExpM <? 0xffffffffffff8002 then FD_a else FD_0b.
End Model.

Lemma f128_div_words : forall a_lo a_hi b_lo b_hi,
0 <= a_lo < 2^64 -> 0 <= a_hi < 2^64 -> 0 <= b_lo < 2^64 -> 0 <= b_hi < 2^64 ->
f128_div (mk128 a_hi a_lo) (mk128 b_hi b_lo) = f128_div_w a_lo a_hi b_lo b_hi.
Proof.
intros. unfold f128_div, f128_div_w, FD_0b. rewrite !lo64_mk128, !hi64_mk128 by lia. cbv zeta.
destruct (_ <? _); destruct (_ <=? _); reflexivity.
Qed.

Section Walk.
Variables (sp a0 a1 a2 a3 : word).

Definition savedD (s6 s5 s4 s3 s2 s1 s0 ra : word) : list cell :=
[C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

End Walk.

