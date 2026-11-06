(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumWalk.v, with its module paths and module names changed; 262 of its 282 lines of code are new or changed and 24 lines of the source are left out. *)
(* fuzz_preset, harness fix #102 (pins A' asan 1be0f53d96cb9d6c, B' asan-ubsan d663f82d7f488d30): the IMAGE-FREE half
   of the tx_put walks that concerns tx_put's ONE allocator call, the direct call of the realloc wrapper through noted()
   (merged fuzz_preset.c :394; A' 0x84dac, B' 0x85298), shared by the A' and B' walks.
   Text proved: ttx_put_specX of lib/A/PRH_FnTx.v, whose GROW run event is an entry premise guarded by f0 = 0 and
   cap0 < len0 + n + 1, and whose post's position conjunct after a grow is keyed on that event.
   rule 24: proves no function (kind: shared lemmas)
   (a text twin and tx_put's call-site lemmas; the walks of tx_put cite it).

   THE TWIN TEXT. THE LIVE COUNTS: room_live_cf S' after the realloc needs YGcfRoomLive.RL_realloc_step /
   room_live_realloc_null_keep, whose live-count premises follow from iface_room_pos only through the run-position
   counts lib/Spec/PresetRoomCounts.v counts_of_room_pos_ok / _rl. This image-free file takes them as ONE named entry
   premise, tp_live, over the leaf lib/Spec/PresetLiveBounds.v: counts_of_room_pos_ok's conclusion and
   counts_of_room_pos_rl's strict class-24 bound; the instances close it from the text's own iface_room_pos premise
   (TxPut102A_Inst.v / TxPut102B_Top.v tp_live_of_pos). ttx_put_specX_ev is ttx_put_specX VERBATIM with exactly this
   premise inserted after the iface_room_pos premise (its post written by name, PRH_FnTx.txpP_Q);
   ttx_put_specX_of_ev / ttx_put_specX_of_pos state that it gives the text wherever tp_live holds.

   THE CALL-SITE LEMMAS (section x below; image-free, at the cf instance ARx := ARcf pa_segs B /\ xs_placed_cf,
   QM := QMm_cf, RL := prh_room_live_a8, so room_live_cf is YGcfRoomLive.room_live_cf, written so): each hypothesis is a
   piece of the conclusion of the realloc rule (cap0 > 0: YGcallRx.aj_realloc_x and its forms over R and with the
   memnorm keep, YGcallRkKeep.aj_realloc_at_x_cfR_keep) or of the realloc(NULL, n) rule (cap0 = 0:
   YGcallRxKeep.aj_realloc_null_at_x_keep; its tree is ReallocP.realloc_null_tree_with), or a fact the walk holds at
   the call.
   1. tp_RMX (the rule's RMX, YGcallRcf.realloc_model_law_x_cf at headroom 0, universe_ok from ARcf), tp_RQ_of_live,
      tp_QM_of_live (the rule's RQ / QM at the call from room_live_cf).
   2. tp_room_live_after / tp_room_live_after0: room_live_cf after the call (YGcfRoomLive.RL_realloc_step /
      room_live_realloc_null_keep, its live-count premises being tp_live's three conjuncts).
   3. tp_pos_after_grow / tp_pos_after_grow0 (granted), tp_pos_after_null / tp_pos_after_null0 (refused): the run
      position after the call (PresetRoomPosKeep.v's room_pos_keep_realloc / _realloc0 / _realloc_null /
      _realloc0_null), the event premise in the text's own `if cap0 =? 0` spelling.
   4. tp_trace_universe: a chain for chain_pre at the call and its trace in the universe, from prhtx_trace and
      prh_univ_closure, for a call with s0 = t and ra = pi_ret_tx_realloc.
   5. tp_refused_at: the NULL arm's prhtx_refused_at (YGcallRcf.realloc_x_null_post_cf).
   6. tp_grow_blocks / tp_grow_blocks0: the success arm's block surgery gives prhtx_grow and the live-byte bound.
   7. tp_hp_remove: the ghost set after a success is unchanged when the old buffer is no harness head.
   The pure chain lemmas tpc_rdword_some / tpc_chain_ex_n / tpc_chain_of_present / tpc_aview_byte are copied from
   lib/A/Prog/S10TxKit.v (sha256 be44a1ec83f3; internal record), s10_* renamed tpc_*. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YG0dcf YGcfRoomLive.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger TxModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnTx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetLiveBounds PresetRun PresetReqAt.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require
  YG00cf YG01cf YG0ncf YGcallx YGcallcf ReallocP YGcallRx YGcallRcf YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YCbqGwild.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcfRehidePost.
Import ListNotations.
Local Open Scope Z_scope.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.

(* the live counts YGcfRoomLive's realloc keeps need at the call (= PresetRoomCounts.counts_of_room_pos_ok's
   conclusion and counts_of_room_pos_rl's class-24 bound, strict) *)
Definition tp_live (S : astate) : Prop :=
  YGcfRoomLive.rl_sec_ok (PresetLiveBounds.LSEC + PresetLiveBounds.DRV) S /\
  YGcfRoomLive.rl_b24_ok (PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1) S /\
  YGcfRoomLive.ccnt24 S < PresetLiveBounds.L24 + PresetLiveBounds.DRV + 1.

(* ttx_put_specX (PRH_FnTx.v) VERBATIM, with tp_live S after the iface_room_pos premise: the re-hiding move's form
   (SRr' segs RZ_cf, the post's journal at wle' segs RZ_cf) and the run-length premise (length rp_os <= 4); the post
   is the text's own, written by its name PRH_FnTx.txpP_Q (txpP_Q_check: it IS the text's post) *)
Definition ttx_put_specX_ev (CTX0 : list (list Z)) : Prop :=
  forall (rp_sm : list Z -> Z * Z) (rp_x : list Z) (rp_os : list (option nat * option nat * option nat))
    (rp_i : nat) (rp_H0 : list Z) (rp_hist : list YG00.chunk),
  forall ly S Hp W regs mem md ch (dw t s n b0 len0 cap0 f0 own : Z) (txt src : list Z) Lam peak cnt fail ran most,
  fpre B ARx STK_tx_put ly S Hp W regs mem md ch -> prh_univ_closure B CTX0 ->
  room_live_cf S -> PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
  tp_live S ->
  (length rp_os <= 4)%nat ->
  (f0 = 0 -> YCbqGwild.wild_room (as_universe B) [] (length (prhtx_evs len0 cap0 [n])) (st_depot S)) ->
  (f0 = 0 -> PRH_Base.prh_cons_from rp_sm rp_x rp_os rp_i (length (prhtx_evs len0 cap0 [n]))) ->
  getr regs 10 = w64 t -> getr regs 11 = w64 s -> getr regs 12 = w64 n ->
  fwin ly W regs mem dw -> prhtx_place ly S W regs mem dw t -> prhtx_trace B ly W mem t ->
  prhtx_rec W mem t b0 len0 cap0 f0 -> prhtx_inv B Lam ly S W mem b0 len0 cap0 txt ->
  src_rd W mem s src -> Z.of_nat (length src) = n -> prhtx_kept B Lam ly S s n ->
  (forall a, s <= a < s + n -> ~ (t <= a < t + 28) /\ ~ (b0 <= a < b0 + cap0)) ->
  len0 + n + 1 <= 2 ^ 28 ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (f0 = 0 -> cap0 < len0 + n + 1 -> nth_error (PresetRun.hruns rp_sm rp_x rp_os) rp_i =
     Some (if cap0 =? 0 then PresetReqAt.HMal (2 * (len0 + n + 1)) else PresetReqAt.HRe cap0 (2 * (len0 + n + 1)))) ->
  blocks_bytes S - cap0 + LIVE_tx <= LIVE_MAX -> 2 * (len0 + n + 1) < cf_malloc_max ->
  SRr' segs YGcfRehidePost.RZ_cf W (cfg_at segs (pa_sigma AS_tx_put) regs mem md)
    (fpostWbmR B ARx SK (wle' segs YGcfRehidePost.RZ_cf) (wbudget_if f0 [] (length (prhtx_evs len0 cap0 [n])))
      STK_tx_put dw (prhtx_fp t b0 cap0) regs ly S Hp W mem md
      (txpP_Q B rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp regs dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt fail
         ran most)).

(* the twin gives the text wherever tp_live holds *)
Lemma ttx_put_specX_of_ev : forall CTX0,
  (forall S, tp_live S) ->
  ttx_put_specX_ev CTX0 -> ttx_put_specX B ARx SK CTX0.
Proof.
intros CTX0 HL H. unfold ttx_put_specX. intros.
eapply H; eauto.
Qed.

(* the same, when the live counts follow from the run position at the text's entry state (PresetCfnA/B's
   counts_of_room_pos_ok / _rl at the instance) *)
Lemma ttx_put_specX_of_pos : forall CTX0,
  (forall sm x os i H0 hist S, PresetRoomPos.iface_room_pos sm x os i H0 hist S -> tp_live S) ->
  ttx_put_specX_ev CTX0 -> ttx_put_specX B ARx SK CTX0.
Proof.
intros CTX0 HL H. unfold ttx_put_specX.
intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s n b0 len0 cap0 f0 own txt src Lam peak cnt
  fail ran most H1 H2 H3 H4.
exact (H rp_sm rp_x rp_os rp_i rp_H0 rp_hist ly S Hp W regs mem md ch dw t s n b0 len0 cap0 f0 own txt src Lam peak
  cnt fail ran most H1 H2 H3 H4 (HL _ _ _ _ _ _ _ H4)).
Qed.

End c.

(* ============================================================================================================ *)
(* THE CALL-SITE LEMMAS of tx_put's realloc call (header 1-7). Image-free. *)

(* ---- pure: a frame-pointer chain exists wherever the words it reads are present (S10TxKit.v blob 82107d1db1cc
   s10_rdword_some / s10_chain_ex_n / s10_chain_of_present / s10_aview_byte, verbatim but for the names) ---- *)
Lemma tpc_rdword_some : forall (rd : reader) a,
  (forall i, 0 <= i < 8 -> rd (a + i) <> None) ->
  (forall x v, rd x = Some v -> 0 <= v < 256) ->
  exists v, rdword rd a = Some v /\ 0 <= v.
Proof.
intros rd a Hp Hb. unfold rdword.
assert (H0 : rd a <> None) by (replace a with (a + 0) by lia; apply Hp; lia).
destruct (rd a) as [b0|] eqn:E0; [|exfalso; exact (H0 eq_refl)].
destruct (rd (a + 1)) as [b1|] eqn:E1; [|exfalso; exact (Hp 1 ltac:(lia) E1)].
destruct (rd (a + 2)) as [b2|] eqn:E2; [|exfalso; exact (Hp 2 ltac:(lia) E2)].
destruct (rd (a + 3)) as [b3|] eqn:E3; [|exfalso; exact (Hp 3 ltac:(lia) E3)].
destruct (rd (a + 4)) as [b4|] eqn:E4; [|exfalso; exact (Hp 4 ltac:(lia) E4)].
destruct (rd (a + 5)) as [b5|] eqn:E5; [|exfalso; exact (Hp 5 ltac:(lia) E5)].
destruct (rd (a + 6)) as [b6|] eqn:E6; [|exfalso; exact (Hp 6 ltac:(lia) E6)].
destruct (rd (a + 7)) as [b7|] eqn:E7; [|exfalso; exact (Hp 7 ltac:(lia) E7)].
eexists. split; [reflexivity|].
pose proof (Hb _ _ E0). pose proof (Hb _ _ E1). pose proof (Hb _ _ E2). pose proof (Hb _ _ E3).
pose proof (Hb _ _ E4). pose proof (Hb _ _ E5). pose proof (Hb _ _ E6). pose proof (Hb _ _ E7). lia.
Qed.

Lemma tpc_chain_ex_n : forall (rd : reader) (top : Z),
  (forall x v, rd x = Some v -> 0 <= v < 256) ->
  forall (n : nat) (bp : Z), top - bp <= Z.of_nat n -> bp < top -> bp mod 8 = 0 ->
  (forall a, bp - 16 <= a < top -> rd a <> None) ->
  exists ch, fpchain (rdword rd) bp top ch.
Proof.
intros rd top Hb n. induction n as [|n IH]; intros bp Hn Hbt Hal Hpres.
- exfalso. lia.
- destruct (tpc_rdword_some rd (bp - 8) ltac:(intros i Hi; apply Hpres; lia) Hb) as (ra & Hra & Hra0).
  destruct (Z_lt_ge_dec ra 4096) as [Hlt | Hge].
  + exists []. cbn [fpchain]. exists ra. split; [exact Hra | lia].
  + destruct (tpc_rdword_some rd (bp - 16) ltac:(intros i Hi; apply Hpres; lia) Hb) as (nfp & Hnfp & Hnfp0).
    destruct (bad_next bp top nfp) eqn:Ebn.
    * exists [(bp, ra, nfp)]. cbn [fpchain]. rewrite Ebn.
      split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra|]. split; [exact Hnfp|]. split; [lia | reflexivity].
    * unfold bad_next in Ebn.
      apply orb_false_iff in Ebn as [Ebn E3]. apply orb_false_iff in Ebn as [E1 E2].
      apply Z.leb_gt in E1. apply Z.leb_gt in E2. apply negb_false_iff in E3. apply Z.eqb_eq in E3.
      destruct (IH nfp ltac:(lia) ltac:(lia) E3 ltac:(intros a Ha; apply Hpres; lia)) as (ch & Hch).
      exists ((bp, ra, nfp) :: ch). cbn [fpchain]. unfold bad_next.
      rewrite (proj2 (Z.leb_gt nfp bp) E1), (proj2 (Z.leb_gt (top - 16) nfp) E2).
      rewrite (proj2 (Z.eqb_eq (nfp mod 8) 0) E3). cbn [orb negb].
      split; [reflexivity|]. split; [exact Hal|]. split; [exact Hra|]. split; [exact Hnfp|]. split; [lia | exact Hch].
Qed.

Lemma tpc_chain_of_present : forall (rd : reader) (top bp : Z),
  (forall x v, rd x = Some v -> 0 <= v < 256) -> bp < top -> bp mod 8 = 0 ->
  (forall a, bp - 16 <= a < top -> rd a <> None) ->
  exists ch, fpchain (rdword rd) bp top ch.
Proof.
intros rd top bp Hb Hbt Hal Hpres.
apply (tpc_chain_ex_n rd top Hb (Z.to_nat (top - bp)) bp ltac:(lia) Hbt Hal Hpres).
Qed.

Lemma tpc_aview_byte : forall (sg : list Segment) (H : word -> bool) mem x v, aview sg H mem x = Some v -> 0 <= v < 256.
Proof.
intros sg H mem x v E. unfold aview in E.
destruct (mbyte sg (mrestrict H mem) x) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as <-. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Import YG00cf YG01cf YG0ncf YG0dcf YGcallx YGcallcf ReallocP YGcallRx YGcallRcf YGcfRoomKeep.

Section x. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation segs := pa_segs.
Variable B : asyms.
(* the cf instance's relation of the generic rules (YGcallcf.v's ARxs; FuzzReallocB.v's ARcfx) *)
#[local] Abbreviation ARcfx := (fun ly S Hp W mem md => ARcf segs B ly S Hp W mem md /\ xs_placed_cf ly S).

(* ---- 1. the rule's RMX, RQ and QM at the call ---- *)
(* RMX (YGcallRx.v's realloc model law) at RQ := qtight /\ ROOM_cf_k RK_realloc: YGcallRcf.realloc_model_law_x_cf at
   headroom 0, its universe_ok from ARcf at any state (YGcallcf.universe_ok_of_ARcf) *)
Lemma tp_RMX : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md ->
  realloc_model_law_x B (fun s _ _ => qtight s /\ ROOM_cf_k s RK_realloc)
    malloc_cf cf_malloc_max free_cf (Wf_cf (as_universe B)).
Proof.
intros ly S Hp W mem md HAR s p n_old n tr HW (HQ & HRk) Hin Hn Hl Htr.
exact (realloc_model_law_x_cf B 0 (universe_ok_of_ARcf segs B ly S Hp W mem md HAR) s p n_old n tr HW
  (conj HQ HRk) Hin Hn Hl Htr).
Qed.

(* RQ at the call from room_live_cf (YGcfRoomLive.room_live_room_k) *)
Lemma tp_RQ_of_live : forall S, YGcfRoomLive.room_live_cf S -> qtight S -> qtight S /\ ROOM_cf_k S RK_realloc.
Proof. intros S HL HQ. exact (conj HQ (YGcfRoomLive.room_live_room_k S HL)). Qed.

(* QM at the call from ARcf, qtight, room_live_cf and the hull admission (YGcallcf.QM_cf_of_room,
   YGcfRoomLive.room_live_room) *)
Lemma tp_QM_of_live : forall ly S Hp W mem md, ARcf segs B ly S Hp W mem md -> qtight S ->
  YGcfRoomLive.room_live_cf S -> cf_hull_ok S -> QM_cf S.
Proof.
intros ly S Hp W mem md HAR HQ HL HO.
exact (QM_cf_of_room segs B ly S Hp W mem md HAR HQ (YGcfRoomLive.room_live_room S HL) HO).
Qed.

(* ---- 2. room_live_cf after the call ---- *)
(* cap0 > 0: the realloc tree (YGcfRoomLive.RL_realloc_step at Lsec := LSEC + DRV, L24 := L24 + DRV + 1), at the
   call's admission (the batch-kit text's wild room, through YCbqGwild.ajournal_xw_admits at the call) *)
Lemma tp_room_live_after : forall ly S Hp W regs mem md ch p r tr trc q S2,
  YGcfRoomLive.room_live_cf S -> tp_live S ->
  acall_pre_x segs B ARcfx (QMm_cf segs B) ly S Hp W regs mem md ch -> admits (as_universe B) tr S ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX ->
  apath (realloc_tree_with malloc_cf free_cf p r tr S) trc (q, S2) -> YGcfRoomLive.room_live_cf S2.
Proof.
intros ly S Hp W regs mem md ch p r tr trc q S2 HL (L1 & L2 & L3) HPRE Hadm Hr Hl Hap.
exact (YGcfRoomLive.RL_realloc_step segs B ly S Hp W regs mem md ch _ _ p r tr trc (q, S2)
  (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE) Hadm Hr Hl L1 L2 L3 HL Hap).
Qed.

(* cap0 = 0: realloc(NULL, r) (YGcfRoomLive.room_live_realloc_null_keep) *)
Lemma tp_room_live_after0 : forall ly S Hp W regs mem md ch r tr trc q S2,
  YGcfRoomLive.room_live_cf S -> tp_live S ->
  acall_pre_x segs B ARcfx (QMm_cf segs B) ly S Hp W regs mem md ch ->
  apath (realloc_null_tree_with malloc_cf free_cf r tr S) trc (q, S2) -> YGcfRoomLive.room_live_cf S2.
Proof.
intros ly S Hp W regs mem md ch r tr trc q S2 HL (L1 & L2 & _) HPRE Hap.
destruct (YGcfRoomLive.rl_of_acall_pre_cf segs B ly S Hp W regs mem md ch
  (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE)) as (HW & _ & HQ).
exact (YGcfRoomLive.room_live_realloc_null_keep _ _ _ r tr S trc q S2 HW HQ L1 L2 HL Hap).
Qed.

(* ---- 3. the run position after the call ---- *)
(* cap0 > 0, granted: the run's event is HRe cap0 r (PresetRoomPosKeep.room_pos_keep_realloc at the call's
   admission, the trace being wild in the kit's text) *)
Lemma tp_pos_after_grow : forall sm x os i H0 hist ly S Hp W regs mem md ch p b0 cap0 r tr trc q S2,
  acall_pre_x segs B ARcfx (QMm_cf segs B) ly S Hp W regs mem md ch -> YGcfRoomLive.room_live_cf S ->
  0 < cap0 -> sptr_addr B ly p = b0 -> b0 <> 0 -> In (p, cap0) (blocks S) ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> admits (as_universe B) tr S ->
  apath (realloc_tree_with malloc_cf free_cf p r tr S) trc (q, S2) -> q <> PNull ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  nth_error (PresetRun.hruns sm x os) i =
    Some (if cap0 =? 0 then PresetReqAt.HMal r else PresetReqAt.HRe cap0 r) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (Datatypes.S i) H0 hist' S2.
Proof.
intros sm x os i H0 hist ly S Hp W regs mem md ch p b0 cap0 r tr trc q S2 HPRE HL Hc Ep Hb0 Hin Hr Hl Htr Hap Hq
  Hpos He.
assert (Hpn : p <> PNull) by (intros ->; apply Hb0; rewrite <- Ep; reflexivity).
rewrite (proj2 (Z.eqb_neq cap0 0) ltac:(lia)) in He.
exact (PresetRoomPosKeep.room_pos_keep_realloc segs B ly S Hp W regs mem md ch sm x os i H0 hist p cap0 r tr trc q S2
  (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE) (YGcfRoomLive.room_live_room_k S HL) Hr Hl Htr Hin Hpn
  Hap Hq Hpos He).
Qed.

(* cap0 = 0, granted: the run's event is HMal r (PresetRoomPosKeep.room_pos_keep_realloc0) *)
Lemma tp_pos_after_grow0 : forall sm x os i H0 hist ly S Hp W regs mem md ch cap0 r tr trc q S2,
  acall_pre_x segs B ARcfx (QMm_cf segs B) ly S Hp W regs mem md ch -> cap0 = 0 ->
  0 <= r < cf_malloc_max -> blocks_bytes S + r <= LIVE_MAX -> admits (as_universe B) tr S ->
  apath (realloc_null_tree_with malloc_cf free_cf r tr S) trc (q, S2) -> q <> PNull ->
  PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
  nth_error (PresetRun.hruns sm x os) i =
    Some (if cap0 =? 0 then PresetReqAt.HMal r else PresetReqAt.HRe cap0 r) ->
  exists hist', PresetRoomPos.iface_room_pos sm x os (Datatypes.S i) H0 hist' S2.
Proof.
intros sm x os i H0 hist ly S Hp W regs mem md ch cap0 r tr trc q S2 HPRE -> Hr Hl Htr Hap Hq Hpos He.
cbn [Z.eqb] in He. exists hist.
exact (PresetRoomPosKeep.room_pos_keep_realloc0 segs B ly S Hp W regs mem md ch sm x os i H0 hist r tr trc q S2
  (acall_pre_x_xs_cf segs B ly S Hp W regs mem md ch HPRE) Hr Hl Htr Hap Hq Hpos He).
Qed.

(* ---- 4. the realloc call's trace: a chain chain_pre accepts at the call, and its trace in the universe in the
   engine's own form inU (the batch-kit prhtx_trace). The call state regsT holds s0 = t (the record, on the real stack at or
   above alloc_ceiling) and ra = pi_ret_tx_realloc; its view agrees with the entry view on [t - 16, ly_top ly) outside
   the record and has the record's bytes. Three cases of chain_pre: frame0_ok false ([pc0], the closure's entry
   clause); bad_next (the empty chain, the closure's literal-site clause at F_tx_put / RT_realloc); else the chain
   fpchain reads from t, whose trace prhtx_trace gives (unwind_of_chain reads only the tuples' return addresses, so
   the first tuple's sp is immaterial). A fixed trace is inU under universe_ok (YG01.admits_fix's first half). ---- *)
Lemma tpc_inU_fix : forall U t, universe_ok U -> In t (u_fix U) -> inU U t.
Proof. intros U t (_ & HF & _) H. split; [exact (proj1 (Forall_forall _ _) HF t H) | left; exact H]. Qed.
Lemma tp_trace_universe : forall CTX0 ly W mem t lyc (Wc : world segs) (memc : word -> option byte) regsT,
  universe_ok (as_universe B) ->
  prhtx_trace B ly W mem t -> prh_univ_closure B CTX0 ->
  pi_ret_sites F_tx_put RT_realloc = [pi_ret_tx_realloc] ->
  YM05.alloc_ceiling <= t -> s0Z regsT = t -> raZ regsT = pi_ret_tx_realloc -> 4096 <= raZ regsT ->
  spZ regsT + 16 <= t -> ly_top lyc = ly_top ly ->
  (forall a, t - 16 <= a < ly_top ly -> ~ (t <= a < t + 28) ->
     aview segs (w_H Wc) memc a = aview segs (w_H W) mem a) ->
  (forall a, t <= a < t + 28 -> aview segs (w_H Wc) memc a <> None) ->
  exists ch, chain_pre lyc (aview segs (w_H Wc) memc) regsT ch /\
    inU (as_universe B) (call_trace lyc cf_pc_realloc_ra0 regsT ch).
Proof.
intros CTX0 ly W mem t lyc Wc memc regsT HUok HTR HU Hsites Hceil Hs0 Hra Hra4 Hsp Htop Hagree Hrec.
assert (Hlit : inU (as_universe B) (prh_trace cf_pc_realloc_ra0 pi_ret_tx_realloc [])).
{ apply tpc_inU_fix; [exact HUok|].
  apply (prh_univ_closure_lit B CTX0 F_tx_put RT_realloc pi_ret_tx_realloc HU). rewrite Hsites. left. reflexivity. }
assert (H0 : inU (as_universe B) [cf_pc_realloc_ra0]) by exact (tpc_inU_fix _ _ HUok (proj1 HU RT_realloc)).
unfold chain_pre, call_trace.
destruct (frame0_ok lyc regsT) eqn:Ef.
2: { exists []. split; [split; [exact Hra4 | reflexivity] | exact H0]. }
destruct (bad_next (spZ regsT) (ly_top lyc) (s0Z regsT)) eqn:Eb.
- exists []. split; [split; [exact Hra4 | reflexivity]|].
  unfold unwind_of_chain. cbn [flat_map]. rewrite Hra. exact Hlit.
- rewrite Hs0 in Eb |- *.
  unfold bad_next in Eb. apply orb_false_iff in Eb as [Eb E3]. apply orb_false_iff in Eb as [E1 E2].
  apply Z.leb_gt in E1. apply Z.leb_gt in E2. apply negb_false_iff in E3. apply Z.eqb_eq in E3.
  destruct (HTR Hceil) as (Hpres & Huniv).
  assert (Hrp : forall a, t - 16 <= a < ly_top lyc -> aview segs (w_H Wc) memc a <> None).
  { intros a Ha.
    destruct (Z_le_gt_dec t a) as [Ht1 | Ht1]; [destruct (Z_lt_ge_dec a (t + 28)) as [Ht2 | Ht2]|].
    - exact (Hrec a ltac:(lia)).
    - rewrite (Hagree a ltac:(lia) ltac:(lia)). exact (Hpres a ltac:(lia)).
    - rewrite (Hagree a ltac:(lia) ltac:(lia)). exact (Hpres a ltac:(lia)). }
  destruct (tpc_chain_of_present (aview segs (w_H Wc) memc) (ly_top lyc) t (tpc_aview_byte segs (w_H Wc) memc)
    ltac:(lia) E3 Hrp) as (ch & Hch).
  exists ch. split; [split; [exact Hra4 | split; [lia | exact Hch]]|].
  rewrite Htop in Hch.
  pose proof (Huniv (aview segs (w_H Wc) memc) ch Hagree Hch) as HI.
  unfold unwind_of_chain in HI |- *. cbn [flat_map] in HI |- *. rewrite Hra. exact HI.
Qed.

(* ---- 6. the success arm's blocks: prhtx_grow and the live-byte bound. ly S is the entry state, lyc Sc the call's
   (tx_put frees and allocates nothing before the call, so the walk gives their equal ablocks) ---- *)
(* cap0 > 0: aj_realloc_x's surgery l1 ++ (b0, cap0) :: l2 -> l1 ++ l2 ++ [(res, n)] *)
Lemma tp_grow_blocks : forall ly S lyc Sc ly2 S2 b0 cap0 res n l1 l2,
  ablocks B lyc Sc = ablocks B ly S -> 0 < cap0 -> cap0 < n ->
  ablocks B lyc Sc = l1 ++ (b0, cap0) :: l2 -> ablocks B ly2 S2 = l1 ++ l2 ++ [(res, n)] ->
  prhtx_grow B ly S ly2 S2 b0 cap0 res n /\ blocks_bytes S2 <= blocks_bytes S + n - cap0.
Proof.
intros ly S lyc Sc ly2 S2 b0 cap0 res n l1 l2 Eab Hc Hn E1 E2.
split.
- right. split; [exact Hn|]. exists l1, l2.
  split; [right; split; [exact Hc | rewrite <- Eab; exact E1]|].
  rewrite E2, app_assoc. apply Permutation_sym, Permutation_cons_append.
- rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), <- Eab, E1, E2.
  rewrite !bsum_app, !bsum_cons. cbn [snd bsum fold_right]. lia.
Qed.

(* cap0 = 0: realloc(NULL, n)'s append ablocks S2 = ablocks Sc ++ [(res, n)] *)
Lemma tp_grow_blocks0 : forall ly S lyc Sc ly2 S2 b0 cap0 res n,
  ablocks B lyc Sc = ablocks B ly S -> cap0 = 0 -> 0 < n ->
  ablocks B ly2 S2 = ablocks B lyc Sc ++ [(res, n)] ->
  prhtx_grow B ly S ly2 S2 b0 cap0 res n /\ blocks_bytes S2 <= blocks_bytes S + n - cap0.
Proof.
intros ly S lyc Sc ly2 S2 b0 cap0 res n Eab Hc Hn E2.
split.
- right. split; [lia|]. exists (ablocks B ly S), [].
  split; [left; split; [exact Hc | rewrite app_nil_r; reflexivity]|].
  rewrite E2, Eab, app_nil_r. apply Permutation_sym, Permutation_cons_append.
- rewrite (blocks_bytes_bsum B ly2 S2), (blocks_bytes_bsum B ly S), <- Eab, E2.
  rewrite !bsum_app. cbn [snd bsum fold_right]. lia.
Qed.

(* ---- 7. the ghost set after a success: remove b0 Hp = Hp when b0 is no harness block's head (prhtx_inv's last
   conjunct), since Hp is exactly the heads of Lam (PRH_Base.prh_ledger_heads) ---- *)
Lemma tp_hp_remove : forall ly S Hp W mem Lam peak cnt fail ran most own b0,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a k, In (a, k) Lam -> a - cf_head <> b0) -> remove Z.eq_dec b0 Hp = Hp.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own b0 LG Hne.
apply notin_remove. intros Hin.
pose proof (Permutation_in _ (prh_ledger_heads B ly S Hp W mem Lam peak cnt fail ran most own LG) Hin) as Hm.
apply in_map_iff in Hm as ([a k] & Ea & Hak). cbn [fst] in Ea. exact (Hne a k Hak Ea).
Qed.

End x.
