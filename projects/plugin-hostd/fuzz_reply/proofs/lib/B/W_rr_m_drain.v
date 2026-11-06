(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: hop 1 (DRAIN) of the MATCH segment of the IMAGE-B walk of fuzz_reply's
   relay_remove (lib/B/W_rr_match_cx.v hop_drain_stmt): RRM i 0x842d8 -> RRG i 0x842f8.
   Proves no function (kind: segment lemma of the W6 image-B walk).  Image A's MATCH has no DRAIN hop file
   (a working branch has W_rr_m_ge / _free / _cpy only), so this one is written from B's objdump with
   k3's drain-call form (lib/A/W_rig_top.v top_p1) for the call.

   B's run (0x842d8 .. 0x842f4, nine instructions; a0 = &g_src[i] = SA from RRM, never reloaded here):
     842d8  addi a1,a0,4             &s->eof
     842dc  srli a2,a1,3             the shadow pointer, computed in the segment (image A carried it)
     842e0  add  a2,a2,s2
     842e4  lb   a2,0(a2)            the shadow byte of the slot's first granule: 0 (the table block is addressable)
     842e8  bnez a2,843f0            the ASan slow path 0x843f0 .. 0x84400: NOT reached (the runner decides it)
     842ec  lw   a1,4(a0)            s->eof
     842f0  bnez a1,842f8            eof <> 0: no drain, straight to RRG
     842f4  jal  83278 <drain>       eof = 0: drain (SA) through DRAIN (dr_spec), ra = 0x842f8 = RRG
   No UBSan trap edge lies in this hop (the entry pointer's checks are in the scan before it and in GE after it).

   The budget RRG's rmbud carries: drain charges dr_cost and leaves the key run and the two frees, so
   rtr cx = rmtrD ++ rmtrK ++ rmtrF (W_rr_match_cx.v rm_tr_split) splits the room.  C3 (the peak form; the image-A
   twin's W_rr_m_drain.v route): dr_spec's peak premise at the call is W_tr_peak.v tr_peak_prefix of RHELD's peak over
   rtr cx; blocks_bytes after the call is bounded in the NET form through W_rr_m_dbytes.v rm_dr_bytes (k3's
   dr_bytes, blocks_bytes S' <= blocks_bytes S + tr_net (dr_tr ..)), whose model premises come from rm_dr_inv_of;
   rmbud's peak over the rest then follows by W_tr_peak.v tr_peak_app.  The tr_alloc helpers the sum form needed
   (the key run's nonnegative allocations, rmd_keys_alloc_nonneg and its chain) are gone. *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 in the room form (the image-A twin's conversion, a Theorem Labs lane
   f4cd818e98d lib/A/W_rr_m_drain.v): hop DRAIN over ANY allocator relation ARx, in place (Section c is
   W_rr_match_cx.v's generic block, verbatim); rr_m_drain : hop_drain_stmt B PST ARx MT RP MMAX RG.  The laws, the
   journal and its lemmas are their _x twins (the head set Hp after each state, RLIVE's journal at RR_STK_x), drain
   is called at dr_spec_x (DRAIN_STK_x) through W_rr_m_kit.v rm_gx_callS, and the shadow fact of the eof field is
   range_addressable_of_block_hp0_x under HP0.  The room round, RRG's two new conjuncts:
   - eof <> 0: rtr = key run ++ frees (rm_tr_split, no drain), so rmbud's rp_RM is RHELD's; the count
     cnt_ok_pk RP gse_pk by cnt_ok_pk_mono from RHELD's rr_pk count (gse_pk = 4 <= tr_peakP + 4).
   - eof = 0: drain at kr' = Z.to_nat (tr_cost MT_rk (key run ++ frees)) + kr.  Its rp_RM premise is RHELD's split
     exactly (rm_tr_cost_app_m, Z2Nat over the nonnegative MT_rk costs, rmd_rk_nonneg); its count premise
     (dr_pk = drain's peak + 2) by cnt_ok_pk_mono from RHELD's (W_tr_cnt.v tr_peakP_app).  After the call
     rmbud's rp_RM is dr_post_x's, and RRG's count is RHELD's moved by drain's count growth (W_rr_m_dcnt.v
     rmc_dr_cnt_peak over dr_post_x's two Permutations), within the trace's peak.
   Image B against the image-A twin: the slot's 8-alignment at drain's call is HSA8 (computed here from the table
   block's 16-alignment; A: rmd_sa_align over alx_blocks); the MT_rk costs are nonnegative by rmd_rk_nonneg (each
   charge of MT_rk is 1; A: rmd_nn_meas MT_rk rmd_rk_laws over its request-size facts); the call helper is the kit's
   rm_gx_callS, whose continuation carries the head set (A: W_gestures_end.gse_callS_x and HP0 at the return); the
   unused KR (g_rng outside g_s kept across drain) is dropped. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
relay_remove_b_c relay_remove_b_aux drain_b_c relay_instance_gone_b_lem RelayModel send_line_b_c RelayRunT.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_relay_remove_cx W_rr_match_cx W_rr_m_kit W_rr_m_dbytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require W_tr_cnt W_rr_m_dcnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_tr_peak.
(* route R (the Section wR below) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ------------------------------------------------------------------ the key run's charges are not negative *)
(* the meter's charges (the allocator charges a realloc per growth and a free per key): with ameter_laws every charge
   of a non-negative request is non-negative; send_line's growth requests are (g_nout + n) * 2 with 0 <= g_nout and
   0 <= n <= the bytes left (W_contract.v sl_cost_run) *)
Lemma rmd_sl_cost_run_nonneg : forall MT f mx no cap rem, ameter_laws MT -> 0 <= mx -> 0 <= no -> 0 <= rem ->
  0 <= sl_cost_run MT f mx no cap rem.
Proof.
intros MT f. induction f as [|f IH]; intros mx no cap rem MLAW Hmx Hno Hrem; cbn [sl_cost_run]; [lia|].
destruct (Z.leb_spec rem 0) as [Hr|Hr]; [lia|].
set (n := if negb (mx =? 0) && (mx <? rem) then mx else rem).
assert (Hn : 0 <= n <= rem).
{ unfold n. destruct (negb (mx =? 0) && (mx <? rem)) eqn:E; [|lia].
  apply andb_prop in E as [_ E]. apply Z.ltb_lt in E. lia. }
pose proof (mo_free_nonneg MT MLAW) as MF.
destruct (cap <? no + n).
- pose proof (mo_malloc_nonneg MT MLAW ((no + n) * 2) ltac:(lia)) as MM.
  pose proof (IH mx (no + n) ((no + n) * 2) (rem - n) MLAW Hmx ltac:(lia) ltac:(lia)). lia.
- apply IH; [exact MLAW | lia | lia | lia].
Qed.
Lemma rmd_sl_run_cost : forall MT f mx no cap rem j o,
  tr_cost MT (fst (send_line_b_c.sl_run f mx no cap rem j o)) = sl_cost_run MT f mx no cap rem.
Proof.
intros MT f. induction f as [|f IH]; intros mx no cap rem j o; cbn [send_line_b_c.sl_run sl_cost_run]; [reflexivity|].
destruct (rem <=? 0); [reflexivity|].
destruct (cap <? no + _); [|apply IH].
cbn [fst]. change (tr_cost MT (?a :: ?t)) with (tr_cost MT ([a] ++ t)).
rewrite (rm_tr_cost_app MT), IH.
destruct (cap =? 0); unfold tr_cost at 1; cbn [fold_right]; lia.
Qed.
Lemma rmd_sl_tr_cost : forall MT live mx no cap len j o,
  tr_cost MT (send_line_b_c.send_line_tr live mx no cap len j o) =
  if live then sl_cost_run MT (Z.to_nat len) mx no cap len else 0.
Proof.
intros MT live mx no cap len j o. unfold send_line_b_c.send_line_tr. destruct live; [|reflexivity].
apply rmd_sl_run_cost.
Qed.
Lemma rmd_ge_tr_cost_nonneg : forall MT live mx no cap xl j o, ameter_laws MT -> 0 <= mx -> 0 <= no -> 0 <= xl ->
  0 <= tr_cost MT (gesture_end_b_c.gesture_end_tr live mx no cap xl j o).
Proof.
intros MT live mx no cap xl j o MLAW Hmx Hno Hxl. unfold gesture_end_b_c.gesture_end_tr. cbv zeta.
rewrite (rm_tr_cost_app MT), !rmd_sl_tr_cost. destruct live; [|lia].
pose proof (rmd_sl_cost_run_nonneg MT (Z.to_nat xl) mx no cap xl MLAW Hmx Hno Hxl).
pose proof (rmd_sl_cost_run_nonneg MT (Z.to_nat 5) mx (no + xl)
  (send_line_b_c.send_line_cap true mx no cap xl) 5 MLAW Hmx ltac:(lia) ltac:(lia)).
lia.
Qed.
Lemma rmd_keys_cost_nonneg : forall MT xks live mx no cap j o, ameter_laws MT -> 0 <= mx -> 0 <= no ->
  Forall (fun p => 0 <= fst p) xks ->
  0 <= tr_cost MT (fst (keys_end_run live mx no cap xks j o)).
Proof.
intros MT xks. induction xks as [|[xl ka] r IH]; intros live mx no cap j o MLAW Hmx Hno HF;
  cbn [keys_end_run]; [cbn; unfold tr_cost; cbn [fold_right]; lia|].
apply Forall_cons_iff in HF as [Hxl HF]. cbn [fst] in Hxl.
cbv zeta. cbn [fst].
change (tr_cost MT (?a ++ ?b :: ?t)) with (tr_cost MT (a ++ [b] ++ t)).
rewrite !(rm_tr_cost_app MT).
pose proof (mo_free_nonneg MT MLAW) as MF.
pose proof (rmd_ge_tr_cost_nonneg MT live mx no cap xl j o MLAW Hmx Hno Hxl).
pose proof (IH live mx (no + xl + 5) (gesture_end_b_c.gesture_end_cap live mx no cap xl)
  (j + RelayRunT.nret YO0i.sptr (gesture_end_b_c.gesture_end_tr live mx no cap xl j o))%nat
  (gesture_end_b_c.gesture_end_out live mx no cap xl j o) MLAW Hmx ltac:(lia) HF).
assert (HR : tr_cost MT [RelayRunT.RFree (xl + 1) ka] = mo_free MT) by (unfold tr_cost; cbn [fold_right]; lia).
lia.
Qed.
(* ------------------------------------------------------------------ block lists *)
(* concat (map f _) respects a permutation of the list *)
Lemma rmd_perm_concat : forall {X : Type} (f : X -> list (Z * Z)) l1 l2, Permutation l1 l2 ->
  Permutation (concat (map f l1)) (concat (map f l2)).
Proof.
intros X f l1 l2 H. induction H; cbn [map concat].
- apply perm_nil.
- apply Permutation_app_head. exact IHPermutation.
- rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
- eapply perm_trans; eassumption.
Qed.
(* the table's blocks, with entry i's first *)
Lemma rmd_blks_split : forall (es : list rentry) (i : nat), (i < length es)%nat ->
  Permutation (concat (map aentry_blks es))
    (aentry_blks (nth i es relay_remove_b_c.no_entry) ++
     concat (map aentry_blks (relay_remove_b_c.remove_at i es))).
Proof.
intros es i Hi.
exact (rmd_perm_concat aentry_blks es _ (rm_remove_perm es i relay_remove_b_c.no_entry Hi)).
Qed.
(* the other entries' blocks move past the source's and the output's *)
Lemma rmd_perm_rot : forall (OB SR OU R : list (Z * Z)),
  Permutation (OB ++ SR ++ OU ++ R) (SR ++ OU ++ (OB ++ R)).
Proof.
intros OB SR OU R.
replace (SR ++ OU ++ (OB ++ R)) with ((SR ++ OU) ++ OB ++ R) by (rewrite <- !app_assoc; reflexivity).
replace (OB ++ SR ++ OU ++ R) with (OB ++ (SR ++ OU) ++ R) by (rewrite <- !app_assoc; reflexivity).
apply Permutation_app_swap_app.
Qed.
(* a block moves from after three parts to the front *)
Lemma rmd_perm_cons3 : forall {X : Type} (a : X) A SR OU R,
  Permutation (A ++ SR ++ OU ++ a :: R) (a :: A ++ SR ++ OU ++ R).
Proof. intros X a A SR OU R. rewrite !app_assoc. apply Permutation_sym, Permutation_middle. Qed.
(* a member of the first three parts is a member of the four *)
Lemma rmd_in3 : forall {X : Type} (x : X) l1 l2 l3 l4, In x (l1 ++ l2 ++ l3) -> In x (l1 ++ l2 ++ l3 ++ l4).
Proof. intros X x l1 l2 l3 l4 H. rewrite !app_assoc in *. apply in_or_app. left. exact H. Qed.
(* the count of a drain-form block list: drain's three parts, then the rest (the image-A twin's, verbatim) *)
Lemma rmd_acnt3 : forall (P : Z -> bool) (A B C R : list (Z * Z)),
  ReplyCnt.acnt P (A ++ B ++ C ++ R) = (ReplyCnt.acnt P (A ++ B ++ C) + ReplyCnt.acnt P R)%nat.
Proof. intros P A B C R. rewrite !app_assoc. apply ReplyCnt.acnt_app. Qed.
(* the counting meter MT_rk (W_contract_x.v) charges 1 per call, so a trace's cost at it is never negative (image B's
   form of the image-A twin's rmd_nn_meas MT_rk rmd_rk_laws, which needs no request-size fact here) *)
Lemma rmd_rk_nonneg : forall {P : Type} (t : list (RelayRunT.rev P)), 0 <= tr_cost MT_rk t.
Proof.
intros P t. unfold tr_cost. induction t as [|ev t IH]; cbn [fold_right]; [lia|].
lazymatch type of IH with 0 <= ?r => generalize r IH end. intros r Hr.
destruct ev; cbn [mo_malloc mo_free MT_rk]; lia.
Qed.


(* ------------------------------------------------------------------ the slot's eof field *)
(* a run over the read-only slot region leaves the memory as it was (W_rr_scan.v rrs_mem) *)
Ltac rmd_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

(* env_agree survives the fresh atoms a run introduces (k3's tp_env_agree_ewset, lib/A/W_rig_top.v:460) *)
Lemma rmd_env_agree_ewset : forall R E n w, env_agree 32 R E -> (32 <= n)%nat -> env_agree 32 R (ewset E n w).
Proof. intros R E n w [HA HD] Hn. split; [|exact HD]. intros k Hk. rewrite ew_ewset_other by lia. apply HA. exact Hk. Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* entry e's eof field: the 4 bytes at SA + 4 (k3's tp_entry_eof) *)
Lemma rmd_eof_cell : forall M SA e, garr8 SEGS M SA (bzs (entry_bytes e)) -> (re_eof e = 0 \/ re_eof e = 1) ->
val_mem SEGS M (SA + 4) 4 (re_eof e).
Proof.
intros M SA e Hg He. unfold entry_bytes, bzs in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [_ Hg]. apply garr8_app in Hg as [Hg _].
rewrite length_map, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le4 in Hg.
replace (SA + Z.of_nat 4) with (SA + 4) in Hg by lia.
apply rm_garr8_le; [|cbn; lia].
unfold OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le4 in Hg.
rewrite unsigned_lit_small in Hg by lia. exact Hg.
Qed.

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the free interceptor's caller-context table (one table for free and free(NULL); image B's closed singleton row) *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (image B's top, W_wake_x.v's form), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC); ASMP / ASF / FFL are the class-0
   fake frame's laws (image B's relay_remove takes none: wake does, W_wake_x.v) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src (the abstract placement does not fix them against the objects; PB_fr on
   AsanUbsan discharges both by vm_compute, as the image-A twin's HH59 / HH60) *)
Hypothesis HH53 : VAL (A_HI 53) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH54 : VAL (A_HI 54) = rg_src RG + RR_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are unowned image bytes (the image-A twin's HRGP / HRGI, verbatim) *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime: rom_view survives the calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs;
   image B meets it at wake's return (W_wake_c_x.v wk_post_x's seat fact S' = set_fs f S) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (image B calls free's interceptor directly, WS_free) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls: drain, gestures_end (the kit's _x specs) and wake (W_wake_c_x.v) *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x8435c with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* B only: wake, tail-called at 0x843e8 (image A inlines it); W_relay_remove.v builds it by W_wake_x.v pb_wake_x *)
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (the image-A twin's PSTR / PSTG, verbatim). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.

Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).

(* ------------------------------------------------------------------ the held array (the image-A twin's) *)
(* an entry's held array: no pointer, or a block of nonzero size (aentry_ok's held-array clause, 8 <= re_kh) *)
Lemma rmd_held_ok : forall ly S W mem e, aentry_ok B ly S W mem e -> re_hp e = 0 \/ re_kh e <> 0.
Proof.
intros ly S W mem e (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HK & _).
destruct HK as [(Hz & _) | (_ & _ & _ & H8 & _)]; [left; exact Hz | right; lia].
Qed.

(* ------------------------------------------------------------------ what the entry and the stream give *)
Lemma rmd_entry : forall cx i, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat ->
  aentry_ok B (rxly cx) (rxS cx) (rxW cx) (rxmem cx) (rnth cx i).
Proof.
intros cx i HB Hi. destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & HR & _).
destruct HR as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HF & _). rewrite Forall_forall in HF. apply HF. apply nth_In. exact Hi.
Qed.
Lemma rmd_nozero : forall (U : list byte), ~ In (Z_to_bv 8 0) U -> RelayModel.nozero (bzs U).
Proof.
intros U HU. unfold RelayModel.nozero, bzs. apply Forall_map. apply Forall_forall. intros b Hb Hz. apply HU.
replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. unfold bz in Hz. rewrite Hz. reflexivity.
Qed.
(* g_nout after drain is the stream's (the A twin's rgl_fin_no, through relay_remove_b_aux.rma_fin_no) *)
Lemma rmd_fin_no : forall cx i lv, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat -> re_fd (rnth cx i) = rxFD cx ->
  rmopen cx i = true ->
  drain_b_c.ds_no (drain_b_c.drain_fin lv (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) =
  rmno cx + dr_tot (rxh cx).
Proof.
intros cx i lv HB Hi Hfd Ho.
pose proof (rmd_entry cx i HB Hi) as (Eeof & Eskip & _ & _ & _ & Ecap & EU1 & EU2 & EU3 & _).
assert (Ee0 : re_eof (rnth cx i) = 0) by (unfold rmopen in Ho; apply Z.eqb_eq; exact Ho).
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDS & _).
destruct (HDS i Hi Hfd Ee0) as (_ & HAS & _ & _ & HSO & HUW & _).
pose proof HAS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HPEND & _ & _ & _ & _ & HOFF & _).
unfold dr_tot, dr_lines. apply relay_remove_b_aux.rma_fin_no.
- unfold RelayModel.J1, hs_state. cbn [RelayModel.ls_k RelayModel.ls_w].
  split; [rewrite HSO; reflexivity|].
  split; [intros Hs; apply HUW; destruct Eskip as [E|E]; [exact E | rewrite E in Hs; discriminate]|].
  split; [unfold bzs; rewrite length_map; apply Nat2Z.inj_le; rewrite EU1;
    change (Z.of_nat RelayModel.LINE_LIMIT) with 6000; unfold APARTIAL in EU2; exact EU2|].
  apply rmd_nozero. exact EU3.
- unfold relay_remove_b_aux.rma_pok, drain_b_c.drain_init. cbn [drain_b_c.ds_off drain_b_c.ds_pend].
  destruct HOFF as [(Hr & Ho0) | (r & rs & Hr & Ho0)]; rewrite Hr; cbn [map].
  + split; [lia | exact I].
  + split; [lia|]. split; [unfold bzs; rewrite length_map; lia|].
    pose proof HPEND as (_ & _ & _ & _ & _ & _ & _ & _ & HF). rewrite Hr in HF. apply Forall_cons_iff in HF as [_ HF].
    apply Forall_map. eapply Forall_impl; [|exact HF]. intros r' (_ & _ & _ & H4).
    unfold bzs. rewrite length_map. apply H4. reflexivity.
- lia.
Qed.
(* the key run of rr_tr is charged nothing negative *)
Lemma rmd_trK_cost_nonneg : forall cx i, RBASE B ARx MT RP MMAX RG cx -> (i < length (rxes cx))%nat ->
  re_fd (rnth cx i) = rxFD cx -> 0 <= tr_cost MT (rmtrK cx i).
Proof.
intros cx i HB Hi Hfd. unfold rmtrK.
pose proof HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HOUT & _).
pose proof (rm_aout_facts B RG (rxly cx) (rxS cx) (rxW cx) (rxmem cx) _ _ _ _ _ _ HOUT) as (Hmx & HnoO & _).
apply rmd_keys_cost_nonneg; [exact MLAW | lia | |].
- unfold rms, dr_fin. destruct (rmopen cx i) eqn:Eo.
  + rewrite (rmd_fin_no cx i _ HB Hi Hfd Eo). unfold rmno, dr_tot. lia.
  + unfold drain_b_c.drain_init. cbn [drain_b_c.ds_no]. unfold rmno. lia.
- apply Forall_map. apply Forall_forall. intros x _. cbn [fst]. lia.
Qed.

(* ------------------------------------------------------------------ the seat at 0x842d8 *)
(* a0 (atom 10) = SA, s2 (18) = the shadow offset, atom 33 = the eof field's value; the region over the slot's
   eof field is read only, and the shadow entry over the slot's first granule takes the check's fast path. *)
Definition RMD_PHI : Z := 140737479966720.
Definition BxD : sv := SOff 18 0.
Definition rmd_regions : smem :=
[ YP09.mkRegion (Some 10%nat) 4 8 0 0 [YP09.mkChunk 4 (CVal 4 (SOff 32 0))] ].
Definition rmd_facts : facts :=
mkFacts [ (10%nat, mkAF 4096 RMD_PHI 3); (18%nat, mkAF SB SB 0); (32%nat, mkAF 0 1 0) ] [] [].
Definition ss_rmd : sstate := mkSS A_rr_match sr_atoms rmd_regions None rmd_facts.
Definition rmd_SH : list shent := [ mkSHE 10 0 8 ].
Definition rmd_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition rmd_extra (eof : Z) : list word := map (Z_to_bv 64) [eof].
(* the registers the hop does not write before the call (a1 and a2 it does) *)
Definition RMD_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 10; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the callee-saved ones among them (a0 is not kept by a call): what RMHD reads *)
Definition RMD_HELD : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

(* ------------------------------------------------------------------ what a callee keeps (lib/B/W_rr_m_ge.v's rgl_*
   helpers, verbatim but renamed; BRmGe's B adaptation of the A twin's) *)
Definition rmd_in (bl : list (Z * Z)) (a : Z) : Prop := exists p n, In (p, n) bl /\ p <= a < p + req_size n.
Lemma rmd_in_blk : forall bl p n len a, In (p, n) bl -> 0 <= n -> len <= n -> p <= a < p + len -> rmd_in bl a.
Proof.
intros bl p n len a Hin Hn Hl Ha. exists p, n. split; [exact Hin|]. pose proof (req_size_pos n Hn) as [_ Hr]. lia.
Qed.
Lemma rmd_in_app_l : forall l1 l2 a, rmd_in l1 a -> rmd_in (l1 ++ l2) a.
Proof. intros l1 l2 a (p & n & H & Ha). exists p, n. split; [apply in_or_app; left; exact H | exact Ha]. Qed.
Lemma rmd_in_app_r : forall l1 l2 a, rmd_in l2 a -> rmd_in (l1 ++ l2) a.
Proof. intros l1 l2 a (p & n & H & Ha). exists p, n. split; [apply in_or_app; right; exact H | exact Ha]. Qed.
Lemma rmd_len_bzs : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma rmd_key_ptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
induction ks as [|k ks IH]; [reflexivity|].
unfold key_ptrs in *. cbn [map concat].
rewrite length_app, IH, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
Lemma rmd_fp_aentry : forall ly S W mem e, aentry_ok B ly S W mem e ->
  forall r a, In r (aentry_fp e) -> fst r <= a < snd r -> rmd_in (aentry_blks e) a.
Proof.
intros ly S W mem e (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15) r a Hr Ha.
rewrite Forall_forall in K15. unfold aentry_fp in Hr. unfold aentry_blks.
apply in_app_or in Hr as [Hr | Hr].
- destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hr|].
  destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
  destruct Hr as [<- | []]. cbn [gfp fst snd] in Ha. apply rmd_in_app_l.
  rewrite rmd_len_bzs, length_app, Nat2Z.inj_add, Hj, K7 in Ha.
  apply (rmd_in_blk _ (re_buf e) (re_cap e) (re_cap e) a); [left; reflexivity | lia | lia | lia].
- apply rmd_in_app_r. destruct Hr as [<- | Hr].
  + cbn [gfp fst snd] in Ha. rewrite rmd_len_bzs, rmd_key_ptrs_len in Ha.
    destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
    { rewrite Hks in Ha. cbn [length] in Ha. lia. }
    unfold re_nheld in Hk1. apply rmd_in_app_l.
    assert (Ez : (re_hp e =? 0) = false) by (apply Z.eqb_neq; exact Hz). rewrite Ez.
    apply (rmd_in_blk _ (re_hp e) (re_kh e) (Z.of_nat (8 * length (re_keys e))) a); [left; reflexivity | lia | lia | lia].
  + apply in_map_iff in Hr as (k & <- & Hk). cbn [gfp fst snd] in Ha. apply rmd_in_app_r.
    destruct (K15 k Hk) as (M1 & _). rewrite rmd_len_bzs, length_app in Ha. cbn [length] in Ha.
    apply (rmd_in_blk _ (key_addr k) (Z.of_nat (length (key_text k)) + 1) (Z.of_nat (length (key_text k)) + 1) a);
      [|lia|lia|lia].
    apply (in_map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1))). exact Hk.
Qed.
Lemma rmd_keep_blk : forall Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k p n a,
  gx_ok SEGS B Gc ->
  ajournal_gx_x (SK := SK) SEGS B PST ARx Gc 0 [] STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k ->
  ARx ly1 S1 Hp1 W1 m1 md1 ->
  In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> ~ inFP FP1 a ->
  abyte_kept W1 m1 W2 m2 a.
Proof.
intros Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k p n a HGc HJ HAR1 Hin1 Hin2 Ha Hf.
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_x; exact HJ).
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 Hin1) as (_ & Hp4096 & Hpceil & _).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
split.
- replace a with (p + (a - p)) by lia.
  rewrite (F2 p n (a - p) Hin1 Hin2 ltac:(lia) ltac:(replace (p + (a - p)) with a by lia; exact Hf)).
  apply (aview_gagree SEGS Gc _ _ _ _ Hag). apply inGb_false.
  rewrite unsigned_lit_small by (pose proof (req_size_pos n) as Hq; lia).
  intros HGa. destruct (HGc _ HGa) as [Himg _].
  apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (p + (a - p)) HAR1 Hin1); [lia | exact Himg].
- intros _. destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 p n HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _).
  apply (apresent_writable SEGS). exact (proj1 (Hpres a Ha)).
Qed.
Lemma rmd_notfp : forall ly S Hp W m md bl p n a, ARx ly S Hp W m md -> In (p, n) (ablocks B ly S) ->
  p <= a < p + req_size n -> (forall b, In b bl -> In b (ablocks B ly S) /\ b <> (p, n)) -> ~ inFP (ablocks_fp bl) a.
Proof.
intros ly S Hp W m md bl p n a HAR Hin Ha Hbl Hf. apply inFP_ablocks_fp_inv in Hf as (q & k & Hq & Hqa).
destruct (Hbl _ Hq) as [Hq1 Hne].
pose proof (sep_blocks_x SEGS B ARx LAWS ly S Hp W m md q k p n HAR Hq1 Hin Hne) as D. unfold zdisjoint in D. cbn [fst snd] in D. lia.
Qed.
Lemma rmd_nd_app : forall (l1 l2 : list (Z * Z)) x, List.NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
Proof.
intros l1 l2 x ND H1 H2. apply in_split in H1 as (p & q & ->). rewrite <- app_assoc in ND. cbn [app] in ND.
apply NoDup_remove_2 in ND. apply ND. apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.
Lemma rmd_abk_trans : forall (W W1 W2 : world SEGS) m m1 m2 a,
  abyte_kept W m W1 m1 a -> abyte_kept W1 m1 W2 m2 a -> abyte_kept W m W2 m2 a.
Proof. intros W W1 W2 m m1 m2 a (A1 & B1) (A2 & B2). split; [rewrite A2; exact A1 | intros Hw; exact (B2 (B1 Hw))]. Qed.
(* NoDup of a suffix, and a member of three parts against a fourth *)
Lemma rmd_nodup_r : forall (l1 l2 : list (Z * Z)), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof. induction l1 as [|x l1 IH]; intros l2 H; [exact H|]. apply IH. inversion H; assumption. Qed.
Lemma rmd_nd_app3 : forall (l1 l2 l3 l4 : list (Z * Z)) x, List.NoDup (l1 ++ l2 ++ l3 ++ l4) ->
  In x (l1 ++ l2 ++ l3) -> In x l4 -> False.
Proof.
intros l1 l2 l3 l4 x ND H1 H2.
replace (l1 ++ l2 ++ l3 ++ l4) with ((l1 ++ l2 ++ l3) ++ l4) in ND by (rewrite <- !app_assoc; reflexivity).
exact (rmd_nd_app _ _ x ND H1 H2).
Qed.

Lemma rmd_held_kept : forall r, In r RMD_HELD -> In r RMD_KEPT.
Proof. intros r Hr. unfold RMD_HELD in Hr. unfold RMD_KEPT. cbn [In] in Hr |- *. tauto. Qed.
(* the registers 21 .. 27 are all in RMD_HELD (the binder clause of rregs_base) *)
Lemma rmd_kept_hi : forall r : bv 5, 21 <= bv_unsigned r <= 27 -> In r RMD_HELD.
Proof.
intros r Hr.
assert (EK : forall k : bv 5, bv_unsigned r = bv_unsigned k -> In k RMD_HELD -> In r RMD_HELD)
  by (intros k Hk HI; replace r with k by (symmetry; apply bv_eq; exact Hk); exact HI).
assert (HD : bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/
             bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
destruct HD as [HD|[HD|[HD|[HD|[HD|[HD|HD]]]]]];
  [ apply (EK 21%bv) | apply (EK 22%bv) | apply (EK 23%bv) | apply (EK 24%bv) | apply (EK 25%bv)
  | apply (EK 26%bv) | apply (EK 27%bv) ];
  solve [ rewrite HD; vm_compute; reflexivity
        | unfold RMD_HELD; cbn [In]; repeat (first [left; reflexivity | right]) ].
Qed.
(* RMHD moves to any register map that keeps RMD_KEPT *)
Lemma rmd_rmhd_kept : forall cx i (regsA regsB : bvmap 5 word),
  RMHD RG cx i regsA -> (forall r, In r RMD_HELD -> getr regsB r = getr regsA r) -> RMHD RG cx i regsB.
Proof.
intros cx i regsA regsB (HRH & H19 & HFD & Hi & Hfd) HK.
destruct HRH as ((Hsp & H3 & H4 & Hhi) & H8 & H9 & H18 & H20).
split; [|split; [rewrite (HK 19%bv) by (cbv; tauto); exact H19 |
         split; [exact HFD | split; [exact Hi | exact Hfd]]]].
split; [|split; [rewrite (HK 8%bv) by (cbv; tauto); exact H8 |
         split; [rewrite (HK 9%bv) by (cbv; tauto); exact H9 |
         split; [rewrite (HK 18%bv) by (cbv; tauto); exact H18 |
                 rewrite (HK 20%bv) by (cbv; tauto); exact H20]]]].
split; [unfold spZ; rewrite (HK 2%bv) by (cbv; tauto); exact Hsp|].
split; [rewrite (HK 3%bv) by (cbv; tauto); exact H3|].
split; [rewrite (HK 4%bv) by (cbv; tauto); exact H4|].
intros r Hr. rewrite (HK r (rmd_kept_hi r Hr)). exact (Hhi r Hr).
Qed.

(* ---- ROUTE R (a Theorem Labs lane's route-R lift crew, group G8b-relayrm-B; G4's form, lib/B/W_bx_reset_x.v): hop DRAIN at
   a world relation R.  Drain's post reaches its world through R (DRAIN_R, W_contract_xR.v dr_spec_xR), so the walk is
   an SRrG walk: the runs and the branch are their G / R forms (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG, W_kit.v
   paj_branch_xR), the call is SRrG_bind over W_rr_m_kit.v rm_gx_callS_xR, and the journal lemmas are their _xR twins
   (W_journal_x.v ajournal_gx_AR_xR, W_relay_remove_cx.v rr_lift_DR_xR, W_rr_m_kit.v rr_img_kept_xR /
   rr_live_call_xR).  Every other token, and each proof, is the strict text's.  At R := wle the twin is the strict
   statement by conversion (W_rr_match_cx.v hop_drain_stmt_wle, W_contract_xR.v dr_spec_x_wle), so the strict
   rr_m_drain below is rr_m_drain_xR at wle.
   Census rows -> twins: :292 AFREE -> AFREE_R, :296 DRAIN -> DRAIN_R, :297 GSE -> GSE_R, :299 AFREEN -> AFREEN_R,
   :440 rmd_keep_blk -> rmd_keep_blk_xR, :523 rr_m_drain -> rr_m_drain_xR. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the R free rules' call-boundary premise RO (the free rules below are stated over it) *)
Variable RO : (word -> option byte) -> Prop.
(* :292 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :296 DRAIN, :297 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :299 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* :440 rmd_keep_blk at R *)
Lemma rmd_keep_blk_xR : forall Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k p n a,
  gx_ok SEGS B Gc ->
  ajournal_gx_xR (SK := SK) SEGS B PST ARx R Gc 0 [] STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 [] ly2 S2 Hp2 W2 m2 md2 k ->
  ARx ly1 S1 Hp1 W1 m1 md1 ->
  In (p, n) (ablocks B ly1 S1) -> In (p, n) (ablocks B ly2 S2) -> p <= a < p + req_size n -> ~ inFP FP1 a ->
  abyte_kept W1 m1 W2 m2 a.
Proof.
intros Gc STK1 sp1 FP1 ly1 S1 Hp1 W1 m1 md1 ly2 S2 Hp2 W2 m2 md2 k p n a HGc HJ HAR1 Hin1 Hin2 Ha Hf.
assert (HAR2 : ARx ly2 S2 Hp2 W2 m2 md2) by (eapply ajournal_gx_AR_xR; exact HJ).
pose proof asan_consts as (C1 & _).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 p n HAR1 Hin1) as (_ & Hp4096 & Hpceil & _).
destruct HJ as (_ & _ & (memS & HJi & Hag) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
split.
- replace a with (p + (a - p)) by lia.
  rewrite (F2 p n (a - p) Hin1 Hin2 ltac:(lia) ltac:(replace (p + (a - p)) with a by lia; exact Hf)).
  apply (aview_gagree SEGS Gc _ _ _ _ Hag). apply inGb_false.
  rewrite unsigned_lit_small by (pose proof (req_size_pos n) as Hq; lia).
  intros HGa. destruct (HGc _ HGa) as [Himg _].
  apply (blk_img_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 md1 p n (p + (a - p)) HAR1 Hin1); [lia | exact Himg].
- intros _. destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 m2 md2 p n HAR2 Hin2) as (_ & _ & _ & _ & Hpres & _).
  apply (apresent_writable SEGS). exact (proj1 (Hpres a Ha)).
Qed.

(* :523 rr_m_drain at R *)
Theorem rr_m_drain_xR : hop_drain_stmt_xR B PST ARx R MT RP MMAX RG.
Proof.
unfold hop_drain_stmt_xR. intros cx i W1 c1 HB HM KG.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HM as (regs1 & ly1 & S1 & Hp1 & m1 & md1 & k1 & -> & HRH & H10 & H19 & HFD0 & Hi & Hfd & HH).
pose proof HH as (HLV & HREL & HOUT & HPERM & HGS & HSRC & HMO & HBB & HRM0 & HCNT0).
pose proof HLV as (HJ & HROM & HAPK & HSV & HLK & HWK).
pose proof HRH as (HRB & H8 & H9 & H18 & H20).
assert (HMD : RMHD RG cx i regs1)
  by (split; [exact HRH | split; [exact H19 | split; [exact HFD0 | split; [exact Hi | exact Hfd]]]]).
pose proof HRB as (Hsp & H3 & H4 & Hhi).
pose proof HB as (HPRE & H32 & HCNT & RGP & Ha0 & HFDr & HLOCK0 & HWAKE0 & HREL0 & HOUT0 & HROM0 & HSRC0 & HPERM0 &
  HTRM & HLIVE & HMOK & HRMB & HCNTB).
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof HPRE as (HAR0 & Hret & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
fold (rsp0 cx) in Hal16, Hslo, Hshi, Htop, Hbot, Hpres.
assert (HAR : ARx ly1 S1 Hp1 W1 m1 md1) by (eapply ajournal_gx_AR_xR; exact HJ).
(* ---- the table and the entry ---- *)
pose proof HREL as (TSv & TSw & TNv & TNw & TCv & TCw & TLen & TIn & (tail & Ttl & Tlen & Tg) & TOK & TND).
destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE HAR TIn) as (HP16 & HP4096 & HPceil & HPia & Hpres2 & _).
change (req_size ATABLE) with 896 in HPceil, HPia, Hpres2.
assert (Hpads : Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) (rxes cx))
  by (eapply Forall_impl; [|exact TOK]; intros e (_ & _ & Q1 & Q2 & _); split; assumption).
assert (HEOK : aentry_ok B ly1 S1 W1 m1 (rnth cx i))
  by (rewrite Forall_forall in TOK; apply TOK; apply nth_In; exact Hi).
assert (Heof01 : re_eof (rnth cx i) = 0 \/ re_eof (rnth cx i) = 1) by exact (proj1 HEOK).
assert (ESA : rmSA cx i = rxG0 cx + 56 * Z.of_nat i) by reflexivity.
assert (HSAr : rxG0 cx <= rmSA cx i /\ rmSA cx i + AENT <= rxG0 cx + ATABLE)
  by (unfold rmSA, AENT, ATABLE; lia).
assert (HSA8 : rmSA cx i mod 8 = 0).
{ rewrite ESA. pose proof (Z.div_mod (rxG0 cx) 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D. rewrite D.
  replace (16 * (rxG0 cx / 16) + 56 * Z.of_nat i) with ((2 * (rxG0 cx / 16) + 7 * Z.of_nat i) * 8) by ring.
  apply Z_mod_mult. }
(* the table's 896 bytes, split at slot i, and the slot's 56 *)
pose proof Tg as TgS.
rewrite (rm_concat_split entry_bytes (rxes cx) relay_remove_b_c.no_entry i Hi) in TgS.
pose proof (rm_tpre_len B ARx MT RP MMAX RG cx i HB ltac:(lia)) as LPRE.
assert (LPRN : Z.of_nat (length (concat (map entry_bytes (firstn i (rxes cx))))) = AENT * Z.of_nat i) by exact LPRE.
assert (LPON : Z.of_nat (length (concat (map entry_bytes (skipn (S i) (rxes cx))))) =
  AENT * (Z.of_nat (length (rxes cx)) - Z.of_nat i - 1)) by exact (rm_tpost_len B ARx MT RP MMAX RG cx i HB Hi).
pose proof (Nat2Z.is_nonneg (length tail)) as HTL0.
pose proof (rm_tpost_len B ARx MT RP MMAX RG cx i HB Hi) as LPOS.
assert (HSL : garr8 SEGS (arm W1 m1) (rmSA cx i) (bzs (entry_bytes (rnth cx i)))).
{ pose proof TgS as Tx. unfold bzs in Tx. rewrite !map_app in Tx.
  apply garr8_app in Tx as [Tx _]. apply garr8_app in Tx as [_ Tx]. apply garr8_app in Tx as [Tx _].
  rewrite length_map in Tx.
  replace (rxG0 cx + Z.of_nat (length (concat (map entry_bytes (firstn i (rxes cx)))))) with (rmSA cx i) in Tx
    by (rewrite LPRN; unfold rmSA; reflexivity).
  exact Tx. }
assert (MEOF : val_mem SEGS (arm W1 m1) (rmSA cx i + 4) 4 (re_eof (rnth cx i)))
  by exact (rmd_eof_cell (arm W1 m1) _ _ HSL Heof01).
assert (HSAW : awr W1 m1 (rmSA cx i) AENT).
{ intros k Hk. unfold arm. apply (apresent_writable SEGS).
  exact (proj1 (Hpres2 (rmSA cx i + k) ltac:(unfold rmSA, AENT in *; lia))). }
(* ---- the seat ---- *)
remember (Eimg (Ereg regs1 (rmd_extra (re_eof (rnth cx i))))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs1 (rmd_extra (re_eof (rnth cx i)))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EEo : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs1 rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E10 : ew E 10 = Z_to_bv 64 (rmSA cx i)) by (rewrite (EEo 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EEo 18%nat 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 (re_eof (rnth cx i)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs1 _ 0)).
assert (UB10 : base_val E (Some 10%nat) = rmSA cx i)
by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; unfold rmSA, AENT in *; lia).
assert (HS : st_ok_pi SEGS VAL E ss_rmd (restrict (w_H W1) (mkst regs1 (Z_to_bv 64 (BASE + A_rr_match)) m1 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_rmd. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold rmd_regions. apply Forall_cons; [|apply Forall_nil].
  unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
  rewrite UB10. split; [unfold rmSA, AENT in *; lia|]. split; [unfold rmSA, AENT in *; lia|].
  split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_nil].
  apply (chunk_ok_val SEGS E _ (rmSA cx i) 4 4 (SOff 32 0) (re_eof (rnth cx i)));
  [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
  exact MEOF.
- cbn [pairwise_disjoint all_disjoint]. repeat split.
- split; [|split; [exact I | exact I]].
  cbn [rmd_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E10, E18, E32, !unsigned_lit_small by (unfold SHADOW_OFF, rmSA, AENT in *; lia).
  change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold RMD_PHI, SB, SHADOW_OFF in *.
  repeat match goal with |- _ /\ _ => split end; try lia; try exact I. }
clear HE.
assert (HBx : U E BxD = SHADOW_OFF)
by (unfold BxD; rewrite (U_atom E 18 SHADOW_OFF E18) by (unfold SHADOW_OFF; lia); reflexivity).
assert (SHOK : sh_ok SEGS BxD rmd_SH E (mrestrict (w_H W1) m1)).
{ constructor; [|constructor].
  eapply shent_ok_of_range.
  + apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly1 S1 Hp1 W1 m1 md1 (rxG0 cx) ATABLE (rmSA cx i) 8
      HAR TIn);
    [unfold rmSA, AENT in *; lia | change (req_size ATABLE) with 896; unfold rmSA, AENT in *; lia].
  + exact HBx.
  + rewrite (U_atom E 10 _ E10) by (unfold rmSA, AENT in *; lia). reflexivity.
  + lia.
  + lia.
  + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, rmSA, AENT in *. lia. }
unfold cfg_at. change (w64 (BASE + A_rr_match)) with (Z_to_bv 64 (BASE + A_rr_match)).
(* 0x842d8 .. 0x842e8: the eof field's shadow check (fast path), then the eof load, to the test 0x842f0 *)
paj_run_tok_x RUNG HS HJ SHOK rmd_Bspan.
{ apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
rmd_mem Em1.
(* 0x842f0 bnez a1: eof <> 0 (no drain) or eof = 0 (drain) *)
psrr_branch_tok RUNG BRR HS SHOK rmd_Bspan.
- (* eof <> 0: 0x842f8 = RRG with nothing changed *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?EE _) _ = _ =>
    assert (EE32 : ew EE 32 = Z_to_bv 64 (re_eof (rnth cx i))) by (rewrite !ew_ewset_other by lia; exact E32);
    rewrite (branch_ne_U EE), (U_atom EE 32 _ EE32), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia) end.
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Eo : rmopen cx i = false) by (unfold rmopen; apply Z.eqb_neq; exact Hc).
  paj_run_to_tok_x RUNTOG HS HJ SHOK rmd_Bspan (AF_fr_relay_remove + 0xfc).
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rmd_mem Em2.
  lazymatch type of HS with st_ok_pi _ _ ?EE _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs1 (rmd_extra (re_eof (rnth cx i)))) EE)
      by (do 2 (apply rmd_env_agree_ewset; [|lia]); exact HAE) end.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RMD_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as HK;
    cbn [ms_regs restrict] in HK;
    pmkst HS; rewrite Em2, Em1 in HJ |- *; apply KG; unfold RRG_xR;
    eexists (ms_regs ms'), ly1, S1, Hp1, m1, _, k1 end.
  exists (rnth cx i), (rxh cx), 0, [], (rxout cx), 0.
  split; [reflexivity|].
  split; [exact (rmd_rmhd_kept cx i regs1 _ HMD (fun r Hr => HK r (rmd_held_kept r Hr)))|].
  split; [split; [exact HJ | split; [exact HROM | split; [exact HAPK | split; [exact HSV | exact (conj HLK HWK)]]]]|].
  split; [unfold rmdrel; rewrite Eo; reflexivity|].
  split; [exact HEOK|].
  split; [exact (rm_tbl_rel B ARx MT RP MMAX RG LAWS cx i ly1 S1 Hp1 W1 m1 md1 HB Hi HAR HREL)|].
  split.
  { unfold rmc1, rmO1, rmcap1. unfold rmlive. rewrite Eo. cbn [andb].
    exact HOUT. }
  split.
  { eapply perm_trans; [exact HPERM|]. apply perm_skip.
    rewrite (rm_drains cx i (rm_base_nodup B ARx MT RP MMAX RG cx HB) HFD0 Hi Hfd), Eo.
    unfold rmsrc, rmcap1, rmOB. unfold rmlive. rewrite Eo. cbn [andb app].
    eapply perm_trans; [apply Permutation_app_tail; exact (rmd_blks_split (rxes cx) i Hi)|].
    rewrite <- app_assoc. apply Permutation_app_head. apply Permutation_refl. }
  split; [intros a Ha _; exact (HGS a Ha)|].
  (* the budget: nothing charged, the key run and the frees left; the room round: no drain, so the rest of the
     trace is the whole trace and rmbud's rp_RM is RHELD's *)
  pose proof (rm_tr_split cx i (rm_base_nodup B ARx MT RP MMAX RG cx HB) HFD0 Hi Hfd) as TS.
  split.
  { split; [exact HMO|].
    split.
    { rewrite TS. unfold rmtrD. rewrite Eo. cbn [app]. lia. }
    split.
    { pose proof (rm_tr_max_app (rmtrD cx i) (rmtrK cx i ++ rmtrF cx i)) as HX.
      rewrite <- TS in HX.
      pose proof (rm_tr_max_nonneg (rmtrD cx i)). lia. }
    split.
    { rewrite TS in HBB. unfold rmtrD in HBB. rewrite Eo in HBB. cbn [app] in HBB. exact HBB. }
    rewrite TS in HRM0. unfold rmtrD in HRM0. rewrite Eo in HRM0. cbn [app] in HRM0. exact HRM0. }
  (* gestures_end's count premise: its constant peak 4 is under RHELD's rr_pk = tr_peakP + 4 *)
  apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) gse_pk (ablocks B ly1 S1) (ablocks B ly1 S1)); [|exact HCNT0].
  intros P. unfold gse_pk, rr_pk. cbv beta. lia.
- (* eof = 0: the call to drain at 0x842f4 *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?EE _) _ = _ =>
    assert (EE32 : ew EE 32 = Z_to_bv 64 (re_eof (rnth cx i))) by (rewrite !ew_ewset_other by lia; exact E32);
    rewrite (branch_ne_U EE), (U_atom EE 32 _ EE32), U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia) end.
  apply negb_false_iff, Z.eqb_eq in Hc.
  assert (Eo : rmopen cx i = true) by (unfold rmopen; apply Z.eqb_eq; exact Hc).
  assert (Heof : re_eof (rnth cx i) = 0) by exact Hc.
  destruct (HSRC i Hi Hfd Heof) as (Hj4 & HAS & HOTH & Hhfd & Hskip & HUW & HPS26 & HEC26 & HNH26).
  paj_run_to_tok_x RUNTOG HS HJ SHOK rmd_Bspan AF_fr_drain.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  rmd_mem Em2.
  lazymatch type of HS with st_ok_pi _ _ ?EE _ _ =>
    assert (HAE2 : env_agree 32 (Ereg regs1 (rmd_extra (re_eof (rnth cx i)))) EE)
      by (do 2 (apply rmd_env_agree_ewset; [|lia]); exact HAE) end.
  pmkst HS. rewrite Em2, Em1.
  prreg HS (1%bv : bv 5) QRA. prreg HS (10%bv : bv 5) QA0.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?ms') =>
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs1 _ RMD_KEPT HS HAE2 ltac:(vm_compute; reflexivity)) as HK end.
  cbn [ms_regs restrict] in HK.
  rewrite Em2, Em1 in HJ.
  assert (QSP : spZ (ms_regs ms0) = rsp0 cx - RR_FRAME)
    by (unfold spZ; rewrite (HK 2%bv) by (cbv; tauto); fold (spZ regs1); exact Hsp).
  assert (QS0 : getr (ms_regs ms0) 8 = w64 (rxFD cx)) by (rewrite (HK 8%bv) by (cbv; tauto); exact H8).
  assert (QRA4 : 4096 <= bv_unsigned (getr (ms_regs ms0) 1)).
  { rewrite QRA. rewrite unsigned_lit_small by lia. lia. }
  assert (QSA : getr (ms_regs ms0) 10 = w64 (rmSA cx i)).
  { rewrite QA0, E10. reflexivity. }
  (* drain's budget premises, from rr_tr's split *)
  pose proof (rm_base_nodup B ARx MT RP MMAX RG cx HB) as HND.
  pose proof (rm_tr_split cx i HND HFD0 Hi Hfd) as HTR.
  assert (EDR : rmtrD cx i = dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
    by (unfold rmtrD; rewrite Eo; reflexivity).
  assert (HTMAX : tr_max (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) < MMAX).
  { pose proof (rm_tr_max_app (rmtrD cx i) (rmtrK cx i ++ rmtrF cx i)) as HX.
    rewrite <- HTR in HX. rewrite <- EDR.
    pose proof (rm_tr_max_nonneg (rmtrK cx i ++ rmtrF cx i)). lia. }
  (* dr_spec's peak premise: drain's trace is the prefix of the rest of rr_tr (W_tr_peak.v tr_peak_prefix) *)
  assert (HBB2 : blocks_bytes S1 + tr_peak (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
                 <= LIVE_MAX).
  { rewrite HTR in HBB. rewrite <- EDR.
    pose proof (tr_peak_prefix (rmtrD cx i) (rmtrK cx i ++ rmtrF cx i)) as PP. lia. }
  assert (HMOK2 : mo_ok MT S1 (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))).
  { apply (mo_ok_step MT MLAW (rxS cx) S1 0 _); [|exact HMO].
    apply (mo_ok_le MT MLAW (rxS cx) _ _ HMOK).
    unfold dr_cost. rewrite HTR, !rm_tr_cost_app, <- EDR. unfold rmtrD in HTR |- *.
    pose proof (mo_free_nonneg MT MLAW) as MF.
    assert (HKC : 0 <= tr_cost MT (rmtrK cx i)) by exact (rmd_trK_cost_nonneg cx i HB Hi Hfd).
    assert (HFC : tr_cost MT (rmtrF cx i) = mo_free MT + mo_free MT)
      by (unfold rmtrF, tr_cost; cbn [fold_right]; lia). lia. }
  (* the Permutation drain asks for, and the one it gives back *)
  assert (HPD : Permutation (ablocks B ly1 S1)
    ((rxG0 cx, ATABLE) :: aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx) ++
     (rmOB cx i ++ rxrest cx))).
  { eapply perm_trans; [exact HPERM|]. apply perm_skip.
    rewrite (rm_drains cx i HND HFD0 Hi Hfd), Eo.
    eapply perm_trans; [apply Permutation_app_tail; exact (rmd_blks_split (rxes cx) i Hi)|].
    rewrite <- app_assoc. apply Permutation_app_head. apply rmd_perm_rot. }
  (* the room round at drain's call: drain gets kr' = what the key run and the two frees charge, plus kr; its room
     premise is RHELD's split exactly (the counting meter's costs are nonnegative), its count premise (drain's peak
     plus 2) is under RHELD's (the request trace's peak plus 4) *)
  pose proof (rmd_rk_nonneg (rmtrK cx i ++ rmtrF cx i)) as TCk.
  pose proof (rmd_rk_nonneg (dr_tr (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))) as CNk.
  assert (HRMdr : rp_RM RP S1 (Z.to_nat (dr_cost MT_rk (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) +
    (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx))).
  { apply (RMM_of RP S1 _ (Z.to_nat (tr_cost MT_rk (rtr cx)) + rxkr cx)); [|exact HRM0].
    rewrite HTR, (rm_tr_cost_app_m MT_rk (rmtrD cx i) (rmtrK cx i ++ rmtrF cx i)), EDR.
    unfold dr_cost. lia. }
  assert (HCNTd : cnt_ok_pk RP (dr_pk (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) (ablocks B ly1 S1)).
  { apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) _ (ablocks B ly1 S1) (ablocks B ly1 S1)); [|exact HCNT0].
    intros P. unfold dr_pk, rr_pk. cbv beta. rewrite HTR, EDR, W_tr_cnt.tr_peakP_app. lia. }
  (* the call: drain (&g_src[i]) through DRAIN, its journal lifted to G_RR *)
  lazymatch type of HJ with ajournal_gx_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mdx _ =>
    set (mdc := mdx) in * end.
  eapply (SRrG_bind SEGS R R_trans).
  { eapply (rm_gx_callS_xR B PST ARx LAWS R R_trans (G_RR B RG) W1 (ms_regs ms0) m1 _ RR_STK_x (rsp0 cx) (rFP cx)
      (rxly cx) (rxS cx) (rxHp cx) (rxW cx) (rxmem cx) (rxmd cx) [] ly1 S1 Hp1 mdc k1 DRAIN_STK_x
      (dr_fp (rmSA cx i) (rnth cx i) (rxh cx) (rxcap cx) (rxout cx)) (-48)
      (getr (ms_regs ms0) 1) []
      (fun ly2 S2 Hp2 W2 regs2 mem2 md2 => exists k2 (e2 : rentry) (h2 : hsrc) (out2 ev2 : Z) (LB : list byte) rest,
        ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (rsp0 cx - RR_FRAME)
          (dr_fp (rmSA cx i) (rnth cx i) (rxh cx) (rxcap cx) (rxout cx)) ly1 S1 Hp1 W1 m1 mdc []
          ly2 S2 Hp2 W2 mem2 md2 k2 /\
        apres_kept B W1 m1 W2 mem2 /\
        mo_le MT S1 S2 (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)) /\
        rp_RM RP S2 (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx) /\
        Permutation (ablocks B ly1 S1)
          (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx) ++ rest) /\
        Permutation (ablocks B ly2 S2)
          (aentry_blks e2 ++ asrc_blks h2 ++
           aout_blks (if dr_live (rxc cx) (rxh cx)
                      then drain_b_c.ds_ocap (dr_fin (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
                      else rxcap cx) out2 ++ rest) /\
        garr8 SEGS (arm W2 mem2) (rmSA cx i) (bzs (entry_bytes e2)) /\ awr W2 mem2 (rmSA cx i) AENT /\
        aentry_ok B ly2 S2 W2 mem2 e2 /\
        dr_rel (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx) e2 h2 LB /\
        asrc_at B ly2 S2 W2 mem2 (rmHA RG cx) h2 /\
        (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ (rmHA RG cx <= a < rmHA RG cx + ASRC) ->
           abyte_kept W1 m1 W2 mem2 a) /\
        aout_at B RG ly2 S2 W2 mem2 (dr_ctl (rxc cx) (rxh cx) ev2)
          (if dr_live (rxc cx) (rxh cx) then rxO cx ++ LB else rxO cx) (rxmx cx)
          (if dr_live (rxc cx) (rxh cx) then rmno cx + dr_tot (rxh cx) else rmno cx)
          (if dr_live (rxc cx) (rxh cx)
           then drain_b_c.ds_ocap (dr_fin (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx))
           else rxcap cx) out2)
      HG HJ).
  - rewrite QSP. unfold RR_FRAME. lia.
  - reflexivity.
  - lia.
  - apply Z.leb_le. vm_compute. reflexivity.
  - unfold RR_STK_x, RR_STK, DRAIN_STK_x, DRAIN_STK, SL_STK, RR_FRAME, DRAIN_FRAME, SL_FRAME, ASTACK. lia.
  - rewrite (HK 3%bv) by (cbv; tauto). rewrite H3. exact Hgp.
  - rewrite (HK 4%bv) by (cbv; tauto). rewrite H4. exact Htp.
  - reflexivity.
  - rewrite QRA. apply ret_ok_codeptr_v; [lia | reflexivity].
  - exact QRA4.
  - replace (rsp0 cx + -48) with (rsp0 cx - RR_FRAME) by (unfold RR_FRAME; lia).
    rewrite (rr_s0Z_fd B ARx MT RP MMAX RG cx (ms_regs ms0) HB HFD0 QS0).
    exact (rr_achain_fd B ARx MT RP MMAX RG cx ly1 (aview SEGS (w_H W1) m1) (rsp0 cx - RR_FRAME) HB HFD0).
  - (* drain's contract at its entry *)
    intros HPRE1. eapply SRrG_mono.
    { (* dr_spec_x's entry alignment rmSA cx i mod 8 = 0: a slot of the 16-aligned table (HSA8 above; the image-A
         twin: rmd_sa_align, W_drain_sa.v dr_sa_align_slot over alx_blocks); the room round: kr', HRMdr, HCNTd *)
      exact (DRAIN_R W1 ly1 S1 Hp1 (ms_regs ms0) m1 mdc [] (rxG0 cx) (rmSA cx i) (rnth cx i) (rxj cx) (rxh cx)
        (rxc cx) (rxO cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) HPRE1 QSA TIn (proj1 HSAr) (proj2 HSAr) HSA8
        HSL HSAW HEOK Hj4 HAS HOTH Hhfd Hskip HUW HOUT HROM (ex_intro _ _ HPD) HPS26 HEC26 HNH26 HTMAX HBB2 HMOK2
        (Z.to_nat (tr_cost MT_rk (rmtrK cx i ++ rmtrF cx i)) + rxkr cx)%nat HRMdr HCNTd). }
    cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k2 & e2 & h2 & out2 & ev2 & LB & rest & -> & HJ2 &
      HPR2 & HAK2 & HM2 & HRM2 & HPm1 & HPm2 & Tg2 & Taw2 & Tok2 & R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 &
      R11 & HAS2 & HKS & R12 & R13 & R14 & R15 & R16 & R17 & R18 & R19 & R20 & R21 & R22 & R23 & R24 & R25 & R26 & RSU &
      RLB & HOU2).
    exists ly2, S2, Hp2, regs2, mem2, md2, k2. split; [reflexivity|].
    split; [eapply rr_lift_DR_xR; exact HJ2|]. split; [exact HPR2|].
    exists k2, e2, h2, out2, ev2, LB, rest.
    split; [rewrite <- QSP; exact HJ2|]. split; [exact HAK2|]. split; [exact HM2|]. split; [exact HRM2|].
    split; [exact HPm1|]. split; [exact HPm2|].
    split; [exact Tg2|]. split; [exact Taw2|]. split; [exact Tok2|].
    split.
    { unfold dr_rel. cbv zeta.
      split; [exact R1|]. split; [exact R2|]. split; [exact R3|]. split; [exact R4|]. split; [exact R5|].
      split; [exact R6|]. split; [exact R7|]. split; [exact R8|]. split; [exact R10|]. split; [exact R11|].
      split; [exact R12|]. split; [exact R13|]. split; [exact R14|]. split; [exact R15|]. split; [exact R16|].
      split; [exact R17|]. split; [exact R18|]. split; [exact R19|]. split; [exact R20|]. split; [exact R21|].
      split; [exact R22|]. split; [exact R23|]. split; [exact R24|]. split; [exact R25|]. split; [exact R26|].
      split; [exact RSU | exact RLB]. }
    split; [exact HAS2|]. split; [exact HKS|]. exact HOU2.
  - (* drain's footprint: the slot and the blocks of its entry, source and output *)
    intros a (r & Hr & Hra). destruct Hr as [<- | Hr].
    + cbn [fst snd] in Hra. left. split.
      * unfold rFP, rr_fp. replace a with (rxG0 cx + (a - rxG0 cx)) by lia.
        apply (inFP_ablocks_fp _ (rxG0 cx) ATABLE);
          [left; reflexivity | change (req_size ATABLE) with 896; unfold rmSA, AENT in *; lia].
      * exists (rxG0 cx), ATABLE. split; [exact TIn | change (req_size ATABLE) with 896; unfold rmSA, AENT in *; lia].
    + assert (Ha' : inFP (ablocks_fp (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++
                      aout_blks (rxcap cx) (rxout cx))) a) by (exists r; split; assumption).
      apply inFP_ablocks_fp_inv in Ha' as (p & n & Hpn & Hpa). left.
      assert (Hin1 : In (p, n) (ablocks B ly1 S1)).
      { apply (Permutation_in _ (Permutation_sym HPD)). right. pose proof Hpn as Hq.
        apply in_app_or in Hq as [Hq | Hq]; [apply in_or_app; left; exact Hq|].
        apply in_or_app; right. apply in_app_or in Hq as [Hq | Hq]; [apply in_or_app; left; exact Hq|].
        apply in_or_app; right. apply in_or_app; left; exact Hq. }
      split; [|exists p, n; split; [exact Hin1 | exact Hpa]].
      unfold rFP, rr_fp. replace a with (p + (a - p)) by lia. apply (inFP_ablocks_fp _ p n); [|lia].
      right. rewrite (rm_drains cx i HND HFD0 Hi Hfd), Eo.
      apply in_app_or in Hpn as [Hpn | Hpn].
      * apply in_or_app. left. apply in_concat. exists (aentry_blks (rnth cx i)).
        split; [apply in_map; apply nth_In; exact Hi | exact Hpn].
      * apply in_or_app. right. exact Hpn. }
  cbv beta. intros W2 c3 Hwle (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & kk & -> & HJ3 & HJc & HPR2 &
    (k2 & e2 & h2 & out2 & ev2 & LB & rest & HJd & HAK2 & HM2 & HRM2 & HPm1 & HPm2 & Tg2 & Taw2 & Tok2 & HDREL & HAS2 &
     HKS & HOU2)).
  (* ---- back at 0x842f8: what the call kept, then RRG ---- *)
  set (FPD := dr_fp (rmSA cx i) (rnth cx i) (rxh cx) (rxcap cx) (rxout cx)) in *.
  assert (HGDR : gx_ok SEGS B (G_DR B RG)) by exact (gx_ok_sub SEGS B _ _ (rr_G_DR_RR B RG) HG).
  assert (HARc : ARx ly1 S1 Hp1 W1 m1 mdc) by (eapply ajournal_gx_AR_xR; exact HJ).
  assert (HAR2 : ARx ly2 S2 Hp2 W2 mem2 md2) by (eapply ajournal_gx_AR_xR; exact HJd).
  assert (HFP0 : Forall (fun r => 0 < fst r) FPD).
  { unfold FPD, dr_fp. constructor; [cbn [fst]; unfold rmSA, AENT in *; lia|].
    apply Forall_forall. intros r Hr. unfold ablocks_fp in Hr. apply in_map_iff in Hr as ([p n] & <- & Hpn). cbn [fst].
    assert (Hin : In (p, n) (ablocks B ly1 S1)) by (apply (Permutation_in _ (Permutation_sym HPm1)); exact (rmd_in3 _ _ _ _ _ Hpn)).
    destruct (alx_blocks _ _ _ LAWS ly1 S1 Hp1 W1 m1 mdc p n HARc Hin) as (_ & Hp & _). lia. }
  assert (KIMG : forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
    ~ (as_errno B <= a < as_errno B + 4) -> ~ Exists (in_zr a) PST -> ~ inG (G_DR B RG) a -> abyte_kept W1 m1 W2 mem2 a).
  { intros a I1 I2 I3 Iq I4. exact (rr_img_kept_xR B PST ARx RG R (G_DR B RG) DRAIN_STK_x (rsp0 cx - RR_FRAME) FPD
      ly1 S1 Hp1 W1 m1 mdc [] ly2 S2 Hp2 W2 mem2 md2 k2 a (fun x H => H) HJd HFP0 HAK2 I1 I2 I3 Iq I4). }
  assert (KC : forall a, rg_src RG <= a < rg_src RG + 8 \/ rg_nsrc RG <= a < rg_nsrc RG + 4 \/
                         rg_capsrc RG <= a < rg_capsrc RG + 4 -> abyte_kept W1 m1 W2 mem2 a).
  { intros a Ha.
    assert (HI : in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)).
    { destruct Ha as [Ha | [Ha | Ha]].
      - apply RGIMG. unfold rg_rng. tauto.
      - apply RGIMG. unfold rg_rng. tauto.
      - destruct (HRGI a ltac:(tauto)) as [I1 I2]. split; [exact I1|]. split; [exact I2|].
        exact (rr_capsrc_nerr B RG HRGP a ltac:(tauto)). }
    (* g_src, g_nsrc and g_capsrc are rr_gcells' third to fifth cells, so off PST (PSTG; the image-A twin's) *)
    assert (Iq : ~ Exists (in_zr a) PST).
    { apply PSTG. unfold rr_gcells. do 2 apply Exists_cons_tl.
      destruct Ha as [Ha|[Ha|Ha]]; [apply Exists_cons_hd | apply Exists_cons_tl, Exists_cons_hd |
        do 2 apply Exists_cons_tl; apply Exists_cons_hd]; cbn [fst snd]; lia. }
    destruct HI as (I1 & I2 & I3). apply (KIMG a I1 I2 I3 Iq). apply (rr_nG_DR B RG HRGP a). tauto. }
  (* the table block and the other entries lie in drain's `rest` *)
  assert (HTrest : Permutation ((rxG0 cx, ATABLE) :: rmOB cx i ++ rxrest cx) rest).
  { apply (Permutation_app_inv_l (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx))).
    rewrite <- !app_assoc.
    eapply perm_trans; [apply rmd_perm_cons3|].
    eapply perm_trans; [apply Permutation_sym; exact HPD | exact HPm1]. }
  assert (T2 : In (rxG0 cx, ATABLE) (ablocks B ly2 S2)).
  { apply (Permutation_in _ (Permutation_sym HPm2)). apply in_or_app. right. apply in_or_app. right.
    apply in_or_app. right. apply (Permutation_in _ HTrest). left. reflexivity. }
  assert (ND2 : List.NoDup (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx) ++ rest))
    by (apply (Permutation_NoDup HPm1); exact (rm_ablocks_nodup B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 mdc HARc)).
  (* every byte of a block of `rest` is kept: it is live before and after and outside drain's footprint *)
  pose proof (rmd_nodup_r _ _ (rmd_nodup_r _ _ (rmd_nodup_r _ _ ND2))) as NDrest.
  assert (NDr : List.NoDup ((rxG0 cx, ATABLE) :: rmOB cx i ++ rxrest cx))
    by exact (Permutation_NoDup (Permutation_sym HTrest) NDrest).
  assert (KREST : forall p n a, In (p, n) (rmOB cx i ++ rxrest cx) -> p <= a < p + req_size n ->
    abyte_kept W1 m1 W2 mem2 a).
  { intros p n a Hp0 Ha.
    assert (Hp : In (p, n) rest) by (apply (Permutation_in _ HTrest); right; exact Hp0).
    assert (I1 : In (p, n) (ablocks B ly1 S1)).
    { apply (Permutation_in _ (Permutation_sym HPm1)). apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hp. }
    assert (I2 : In (p, n) (ablocks B ly2 S2)).
    { apply (Permutation_in _ (Permutation_sym HPm2)). apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. exact Hp. }
    apply (rmd_keep_blk_xR (G_DR B RG) DRAIN_STK_x (rsp0 cx - RR_FRAME) FPD ly1 S1 Hp1 W1 m1 mdc ly2 S2 Hp2 W2 mem2 md2 k2
      p n a
      HGDR HJd HARc I1 I2 Ha).
    intros (r & Hr & Hra). unfold FPD, dr_fp in Hr. destruct Hr as [<- | Hr].
    - (* the slot: inside the table block, which is not (p, n) *)
      assert (Hne : (rxG0 cx, ATABLE) <> (p, n)).
      { intros Eq. pose proof NDr as NDr'. apply List.NoDup_cons_iff in NDr' as [Hni _]. apply Hni.
        rewrite Eq. exact Hp0. }
      pose proof (sep_blocks_x SEGS B ARx LAWS ly1 S1 Hp1 W1 m1 mdc (rxG0 cx) ATABLE p n HARc TIn I1 Hne) as D.
      unfold zdisjoint in D. cbn [fst snd] in D, Hra. change (req_size ATABLE) with 896 in D.
      unfold rmSA, AENT in *. lia.
    - assert (Hbl : forall b, In b (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ->
        In b (ablocks B ly1 S1) /\ b <> (p, n)).
      { intros b Hb. split.
        - apply (Permutation_in _ (Permutation_sym HPm1)). exact (rmd_in3 _ _ _ _ _ Hb).
        - intros ->. exact (rmd_nd_app3 _ _ _ _ (p, n) ND2 Hb Hp). }
      exact (rmd_notfp ly1 S1 Hp1 W1 m1 mdc _ p n a HARc I1 Ha Hbl (ex_intro _ r (conj Hr Hra))). }
  assert (KTAB : forall a, rxG0 cx <= a < rxG0 cx + ATABLE -> ~ (rmSA cx i <= a < rmSA cx i + AENT) ->
    abyte_kept W1 m1 W2 mem2 a).
  { intros a Ha Hs.
    assert (Har : rxG0 cx <= a < rxG0 cx + req_size ATABLE) by (change (req_size ATABLE) with 896; unfold ATABLE in Ha; lia).
    apply (rmd_keep_blk_xR (G_DR B RG) DRAIN_STK_x (rsp0 cx - RR_FRAME) FPD ly1 S1 Hp1 W1 m1 mdc ly2 S2 Hp2 W2 mem2 md2 k2
      (rxG0 cx) ATABLE a HGDR HJd HARc TIn T2 Har).
    intros (r & Hr & Hra). unfold FPD, dr_fp in Hr. destruct Hr as [<- | Hr].
    - cbn [fst snd] in Hra. clear - Hra Hs. unfold AENT in *. lia.
    - assert (Hbl : forall b, In b (aentry_blks (rnth cx i) ++ asrc_blks (rxh cx) ++ aout_blks (rxcap cx) (rxout cx)) ->
        In b (ablocks B ly1 S1) /\ b <> (rxG0 cx, ATABLE)).
      { intros b Hb. split.
        - apply (Permutation_in _ (Permutation_sym HPm1)). exact (rmd_in3 _ _ _ _ _ Hb).
        - intros ->. pose proof (rm_ablocks_nodup B ARx LAWS BLKN ly1 S1 Hp1 W1 m1 mdc HARc) as NDa.
          apply (Permutation_NoDup HPm1) in NDa.
          exact (rmd_nd_app3 _ _ _ _ (rxG0 cx, ATABLE) NDa Hb (Permutation_in _ HTrest ltac:(left; reflexivity))). }
      exact (rmd_notfp ly1 S1 Hp1 W1 m1 mdc _ (rxG0 cx) ATABLE a HARc TIn Har Hbl (ex_intro _ r (conj Hr Hra))). }
  (* the lines drain relayed: their count is the stream's *)
  assert (HLBlen : Z.of_nat (length LB) = dr_tot (rxh cx)).
  { pose proof HDREL as HD'. unfold dr_rel in HD'. cbv zeta in HD'.
    destruct HD' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     _ & _ & HW).
    unfold dr_tot. rewrite <- HW. unfold bzs. rewrite length_map. reflexivity. }
  (* g_capout's facts and drain's model premises, for the net bytes and the count after drain *)
  pose proof (rm_aout_facts B RG ly1 S1 W1 m1 _ _ _ _ _ _ HOUT) as (Hmx0 & _ & Hcap0).
  assert (Hcap1 : 0 <= rxcap cx) by (destruct Hcap0 as [(Hc0 & _) | (Hc0 & _)]; lia).
  pose proof (rm_dr_inv_of B RG ly1 S1 W1 m1 (rnth cx i) (rxh cx) (rxj cx) (rmno cx) (rxcap cx) HEOK
    (HSRC i Hi Hfd Heof)) as (IV & ER).
  (* RRG *)
  apply KG. unfold RRG_xR.
  exists regs2, ly2, S2, Hp2, mem2, md2, (k1 + kk), e2, h2, ev2, LB, out2,
    (dr_cost MT (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rnth cx i) (rxh cx)).
  split; [unfold cfg_at, A_rr_ge, AF_fr_relay_remove; rewrite QRA; reflexivity|].
  (* the registers: the callee preserved every one RMHD names *)
  assert (HR2 : forall r, In r RMD_HELD -> getr regs2 r = getr regs1 r).
  { intros r Hr. rewrite <- (HK r (rmd_held_kept r Hr)). rewrite <- (Z_to_bv_bv_unsigned _ r). apply HPR2.
    unfold RMD_HELD in Hr. cbn [In] in Hr.
    repeat (destruct Hr as [<- | Hr];
      [lazymatch goal with |- acallee_saved (bv_unsigned ?b) => let v := eval vm_compute in (bv_unsigned b) in
         change (bv_unsigned b) with v end; unfold acallee_saved; lia|]).
    destruct Hr. }
  split; [exact (rmd_rmhd_kept cx i regs1 regs2 HMD HR2)|].
  (* RLIVE across the call *)
  split.
  { apply (rr_live_call_xR B PST ARx MT RP MMAX RG LAWS HRGP HROMO PSTR PSTG R cx ly1 S1 Hp1 W1 m1 mdc k1 (G_DR B RG)
      DRAIN_STK_x FPD ly2 S2 Hp2 W2 mem2 md2 k2 (k1 + kk) HB); [| exact HGDR | intros a Ha; exact Ha | | exact HJd |
      exact HFP0 | exact HAK2 | exact HJ3].
    - split; [exact HJ | split; [exact HROM | split; [exact HAPK | split; [exact HSV | exact (conj HLK HWK)]]]].
    - split; [apply Z.leb_le; vm_compute; reflexivity | lia]. }
  (* drain's relation and the harness source after *)
  split; [unfold rmdrel; rewrite Eo; exact (conj HDREL HAS2)|].
  split; [exact Tok2|].
  (* the table with slot i = entry_bytes e2 *)
  split.
  { pose proof Tok2 as (_ & _ & EP1 & EP2 & _).
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; left; cbn in Hx; lia | exact TSv]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; left; lia | exact TSw]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; right; left; cbn in Hx; lia | exact TNv]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; right; left; lia | exact TNw]|].
    split; [apply (akept_vm W1 m1); [intros x Hx; apply KC; right; right; cbn in Hx; lia | exact TCv]|].
    split; [apply (akept_awr W1 m1); [intros x Hx; apply KC; right; right; lia | exact TCw]|].
    split; [exact T2|].
    split; [rewrite (rm_eb_len e2 EP1 EP2); reflexivity|].
    split.
    { exists tail. split; [exact Ttl|].
      pose proof (rm_eb_len e2 EP1 EP2) as LE2.
      destruct (proj1 (Forall_forall _ _) (rm_pads B ARx MT RP MMAX RG cx HB) _
        (nth_In (rxes cx) relay_remove_b_c.no_entry Hi)) as [P1 P2].
      pose proof (rm_eb_len (rnth cx i) P1 P2) as LE1. unfold rnth in LE1.
      pose proof TgS as Tx. unfold bzs in Tx, Tg2 |- *. rewrite !map_app in Tx |- *.
      apply garr8_app in Tx as [Tx TxT]. apply garr8_app in Tx as [TxA Tx]. apply garr8_app in Tx as [_ TxB].
      rewrite ?length_map, ?length_app, ?length_map in TxT, TxB |- *.
      rewrite ?LE1, ?LE2 in TxT, TxB |- *.
      rewrite ?LPRN in TxA, TxB, TxT |- *.
      apply garr8_app. split.
      - apply (akept_garr8 W1 m1); [|exact TxA]. intros x Hx. rewrite ?length_map in Hx.
        apply KTAB; clear - Hx HSAr Hi Ttl HTL0 LPRN LPON LPRE LPOS LE1 LE2; unfold rmSA, AENT, ATABLE, rN in *; lia.
      - apply garr8_app. split.
        + lazymatch goal with |- garr8 _ _ ?bG _ =>
            replace bG with (rmSA cx i) by (clear - LPRE; rewrite ?length_map; unfold rmSA; lia) end.
          exact Tg2.
        + apply garr8_app. split.
          * lazymatch goal with |- garr8 _ _ ?bG _ =>
              replace bG with (rxG0 cx + AENT * Z.of_nat i + 56) by (clear - LPRE LE2; rewrite ?length_app, ?length_map, ?length_app; unfold AENT in *; lia) end.
            lazymatch type of TxB with garr8 _ _ ?bT _ =>
              replace bT with (rxG0 cx + AENT * Z.of_nat i + 56) in TxB by (clear - LPRN LE1; rewrite ?length_app, ?length_map, ?length_app; unfold AENT in *; lia) end.
            apply (akept_garr8 W1 m1); [|exact TxB]. intros x Hx. rewrite ?length_map in Hx.
            apply KTAB; clear - Hx HSAr Hi Ttl HTL0 LPRN LPON LPRE LPOS LE1 LE2; unfold rmSA, AENT, ATABLE, rN in *; lia.
          * lazymatch goal with |- garr8 _ _ ?bG _ =>
              replace bG with (rxG0 cx + AENT * Z.of_nat i + 56 + AENT * (Z.of_nat (length (rxes cx)) - Z.of_nat i - 1)) by (clear - LPRE LE2 LPOS; rewrite ?length_app, ?length_map, ?length_app; unfold AENT in *; lia) end.
            lazymatch type of TxT with garr8 _ _ ?bT _ =>
              replace bT with (rxG0 cx + AENT * Z.of_nat i + 56 + AENT * (Z.of_nat (length (rxes cx)) - Z.of_nat i - 1)) in TxT by (clear - LPRN LE1 LPON; rewrite ?length_app, ?length_map, ?length_app; unfold AENT in *; lia) end.
            apply (akept_garr8 W1 m1); [|exact TxT]. intros x Hx. rewrite ?length_map in Hx.
            apply KTAB; clear - Hx HSAr Hi Ttl HTL0 LPRN LPON LPRE LPOS LE1 LE2; unfold rmSA, AENT, ATABLE, rN in *; lia. }
    split; [exact Taw2|].
    rewrite Forall_forall. intros e He. rewrite Forall_forall in TOK.
    assert (HINE : In (nth i (rxes cx) relay_remove_b_c.no_entry) (rxes cx) \/ True) by (left; apply nth_In; exact Hi).
    assert (HEB : forall b, In b (aentry_blks e) -> In b (rmOB cx i ++ rxrest cx)).
    { intros b Hb. apply in_or_app. left.
      unfold rmOB. apply in_concat. exists (aentry_blks e). split; [apply in_map; exact He | exact Hb]. }
    assert (HOKe : aentry_ok B ly1 S1 W1 m1 e).
    { apply TOK. apply (Permutation_in _ (Permutation_sym (rm_remove_perm (rxes cx) i relay_remove_b_c.no_entry Hi))).
      right. exact He. }
    apply (aentry_ok_kept B ly1 S1 W1 m1 ly2 S2 W2 mem2 e HOKe).
    - intros r Hr a Ha. destruct (rmd_fp_aentry ly1 S1 W1 m1 e HOKe r a Hr Ha) as (p & n & Hpn & Hpa).
      exact (KREST p n a (HEB _ Hpn) Hpa).
    - intros b Hb. apply (Permutation_in _ (Permutation_sym HPm2)). apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. right. apply (Permutation_in _ HTrest). right. exact (HEB _ Hb). }
  (* the stream after drain *)
  split.
  { unfold rmc1, rmO1, rmcap1. unfold rmlive. rewrite Eo. cbn [andb].
    destruct (dr_live (rxc cx) (rxh cx)) eqn:Ed.
    - replace (Z.of_nat (length (rxO cx ++ LB))) with (rmno cx + dr_tot (rxh cx))
        by (rewrite length_app, Nat2Z.inj_add, HLBlen; unfold rmno; lia).
      exact HOU2.
    - replace (Z.of_nat (length (rxO cx))) with (rmno cx) by reflexivity. exact HOU2. }
  (* the blocks *)
  split.
  { eapply perm_trans; [exact HPm2|].
    eapply perm_trans; [apply Permutation_app_head; apply Permutation_app_head; apply Permutation_app_head;
      apply Permutation_sym; exact HTrest|].
    unfold rmsrc, rmcap1. unfold rmlive. rewrite Eo. cbn [andb].
    eapply perm_trans; [apply rmd_perm_cons3|]. apply perm_skip.
    apply Permutation_app_head. apply Permutation_sym. apply rmd_perm_rot. }
  (* g_s outside drain's slot *)
  split.
  { intros a Ha Hj. rewrite (rm_drains cx i HND HFD0 Hi Hfd), Eo in Hj.
    exact (rmd_abk_trans (rxW cx) W1 W2 (rxmem cx) m1 mem2 a (HGS a Ha) (HKS a Ha (Hj eq_refl))). }
  (* the budget: drain charged dr_cost; the key run and the two frees are left (the room round: dr_post_x's rp_RM at
     kr', the room of the rest) *)
  split.
  { split; [rewrite <- (Z.add_0_l (dr_cost MT _ _ _ _ _ _)); exact (mle_station MT (rxS cx) S1 S2 0 _ MLAW HMO HM2)|].
    split.
    { unfold dr_cost. rewrite HTR, !(rm_tr_cost_app MT). rewrite <- EDR. lia. }
    split.
    { pose proof (rm_tr_max_app (rmtrD cx i) (rmtrK cx i ++ rmtrF cx i)) as HX.
      rewrite <- HTR in HX. pose proof (rm_tr_max_nonneg (rmtrD cx i)). lia. }
    split.
    { pose proof (rm_dr_bytes B ly1 S1 W1 m1 ly2 S2 (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) out2
        (rnth cx i) (rxh cx) e2 h2 LB rest (rmHA RG cx) HEOK HAS Hcap1 Hmx0 ltac:(unfold rmno; lia) IV ER
        HPm1 HPm2 HDREL) as HBY.
      (* the peak of the rest, from the peak of rr_tr (W_tr_peak.v tr_peak_app) and drain's net change *)
      rewrite HTR, tr_peak_app in HBB. rewrite <- EDR in HBY. lia. }
    exact HRM2. }
  (* the room round: gestures_end's count premise at the return state.  Drain moves the count of its own blocks (the
     entry's, the source's, g_out's) by at most its trace's count peak (W_rr_m_dcnt.v), and that peak is within the
     request trace's (W_tr_cnt.v tr_peakP_app), whose rr_pk = peak + 4 RHELD's count fact carries;
     gse_pk is 4. *)
  apply (cnt_ok_pk_mono RP (rr_pk (rtr cx)) gse_pk (ablocks B ly1 S1) (ablocks B ly2 S2)); [|exact HCNT0].
  intros P. unfold gse_pk, rr_pk. cbv beta.
  pose proof (W_rr_m_dcnt.rmc_dr_cnt_peak (rxc cx) (rxmx cx) (rmno cx) (rxcap cx) (rxout cx) out2 (rnth cx i) (rxh cx)
    e2 h2 LB P IV ER (rmd_held_ok _ _ _ _ _ HEOK) (rmd_held_ok _ _ _ _ _ Tok2) Hcap1 HDREL) as DC. cbv zeta in DC.
  rewrite (ReplyCnt.acnt_perm P _ _ HPm2), (ReplyCnt.acnt_perm P _ _ HPm1),
    (rmd_acnt3 P (aentry_blks e2)), (rmd_acnt3 P (aentry_blks (rnth cx i))).
  rewrite HTR, EDR, W_tr_cnt.tr_peakP_app.
  lia.
Qed.

End wR.
(* the strict text below is the R section's at R := wle (route R's rule: one walk text): DRAIN_R at wle is DRAIN, and
   the three laws hold for wle *)
Ltac wle_inst := first [ eassumption | exact DRAIN | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

Theorem rr_m_drain : hop_drain_stmt B PST ARx MT RP MMAX RG.
Proof. rewrite hop_drain_stmt_wle. eapply (rr_m_drain_xR (@wle SEGS)); wle_inst. Qed.

End c.
End b.
End a.
