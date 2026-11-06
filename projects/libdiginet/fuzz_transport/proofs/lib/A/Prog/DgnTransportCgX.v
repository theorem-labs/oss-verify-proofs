(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the runtime site contracts of fuzz_reply's ASan program walks that the donor's
   runtime vocabulary (Reusable/YG0d.v, from proofs/cgif/cgif_file_fuzzer/lib/YG0d.v) does not name, in its shape. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/W_sites.v, with its module paths and module names changed; 818 of its 926 lines of code are new or changed and 345 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/TransportGCg.v, with its module paths and module names changed; 579 of its 683 lines of code are new or changed and 822 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/io_recv_seg_m.v, with its module paths and module names changed; 164 of its 228 lines of code are new or changed and 619 lines of the source are left out. *)
(* DgnTransportCgX: two walk lemmas over lib/A/Prog/DgnTransportCg.v trans_src_ok that the kit file does not carry.
   - trans_src_ok_acall_gr_ge0 / trans_src_ok_acall_gr: trans_src_ok_acall_g_ge0 / trans_src_ok_acall_g with the
     callee's gx_kept over ALL of G_HARNESS (lib/A/Prog/TransportGCg.v) replaced by the range's own G bytes kept. A
     G-form callee that writes G (as m_rx and m_tick do) gives no gx_kept; a caller whose range has no byte in what
     the callee writes (e.g. no byte of G at all) proves the weaker premise.
   - trans_src_ok_amem: trans_src_ok of a range of any length, the empty one included, bounds it and places it in
     application memory (trans_src_ok_rd and trans_src_ok_place ask 0 < n; a memcpy of length 0 still needs these
     facts of its source).
   Each 0 < n lemma of the same name without _ge0 is its instance, as in DgnTransportCg.v. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require TransportG W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg.
Import ListNotations.
Open Scope Z_scope.

Section cgx. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.

(* Across a G-form callee (acall_kept_g G_HARNESS at the call state, E its written range, [slo, shi) its stack
   window), for a range empty or not: a heap block by the block clause, a side-stack frame by the frame clause, a G
   byte by the premise on the range's G bytes, the machine stack by the clause at or above alloc_ceiling, a
   TRANS_RO_RD byte by the image clause (it lies below G_HARNESS_LO); the frames' shadow bytes by the frame clause (E
   misses the shadow band); then trans_src_ok_kept_ge0. *)
Lemma trans_src_ok_acall_gr_ge0 : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  TransportGCg.acall_kept_g segs B TransportG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, q <= a < q + n -> W_journalG.inG TransportG.G_HARNESS a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 <= n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    (K1 & K2 & K3 & K4 & _) HGK HnE HnEs Hoff Hs Hn.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (KS : forall cid pos s, In (cid, pos) (frames Sc) ->
     in_zr s (shadow_addr (frame_addr lyc cid pos), fs_frame_bytes cid / 8) ->
     aview segs (w_H W2) mem2 s = aview segs (w_H W) memc s).
  { intros cid pos s Hin Hs'. apply (K4 cid pos s Hin (or_intror Hs')). apply HnEs.
    destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
    pose proof (fs_frame_bytes_nonneg cid) as Hfs.
    pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
    assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
    pose proof (Z.div_pos (frame_addr lyc cid pos) 8 ltac:(lia) ltac:(lia)).
    unfold in_zr in Hs'. cbn [fst snd] in Hs'.
    unfold shadow_addr, SHADOW_OFF, kLowMemEnd, kHighShadowEnd in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  assert (KV : forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { intros a Ha. destruct Hs as [(bA & nA & Hin & B1 & B2) | (HL & _)].
    - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & _ & _ & _ & _ & _ & Hn0).
      pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
      replace a with (bA + (a - bA)) by lia.
      apply (K2 bA nA (a - bA) Hin ltac:(lia)). replace (bA + (a - bA)) with a by lia. exact (HnE a Ha).
    - destruct HL as [(cid & pos & Hin & F1 & F2) | [(HG & _) | [(S1 & S3) | (HR & _)]]].
      + apply (K4 cid pos a Hin); [left; unfold in_zr, frame_rng; cbn [fst snd]; lia | exact (HnE a Ha)].
      + exact (HGK a Ha (HG a Ha)).
      + destruct (trans_stk_bounds B lyc Sc W memc mdc HAR) as [T1 T2]. apply K1; lia.
      + pose proof (HR a Ha) as Ra. destruct (trans_ro_rd_scoped B HRU HRE a Ra) as [Ho He].
        apply (K3 a (trans_ro_img a Ra)); [|exact Ho | exact He].
        intro Ga. pose proof (inG_G_HARNESS_hull a Ga) as Gh. pose proof (trans_ro_rd_bounds a Ra) as Rb.
        unfold TransportG.G_HARNESS_LO in Gh. lia. }
  split; [|exact KV].
  exact (trans_src_ok_kept_ge0 B LAWS lyc Sc W memc mdc ly2 S2 W2 mem2 md2 q n HAR HAR2 Hperm Hfr Hfa Elo Ehi KV KS
           Hs Hn).
Qed.
Lemma trans_src_ok_acall_gr : AR_laws segs B -> trans_ro_rd_unowned B -> trans_rom_no_errno B ->
  forall lyc Sc (W : world segs) memc mdc ly2 S2 (W2 : world segs) mem2 md2 slo shi (E : Z -> Prop) q n,
  @AR rc segs B lyc Sc W memc mdc -> @AR rc segs B ly2 S2 W2 mem2 md2 ->
  Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) -> frames S2 = frames Sc ->
  (forall cid pos, frame_addr ly2 cid pos = frame_addr lyc cid pos) ->
  ly_stk_lo ly2 = ly_stk_lo lyc -> ly_stk_hi ly2 = ly_stk_hi lyc ->
  TransportGCg.acall_kept_g segs B TransportG.G_HARNESS lyc Sc W memc W2 mem2 slo shi E ->
  (forall a, q <= a < q + n -> W_journalG.inG TransportG.G_HARNESS a ->
     aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
  (forall a, q <= a < q + n -> ~ E a) -> (forall a, kLowMemEnd <= a < kHighShadowEnd -> ~ E a) ->
  (q + n <= slo \/ shi <= q) ->
  trans_src_ok B lyc Sc W memc q n -> 0 < n ->
  trans_src_ok B ly2 S2 W2 mem2 q n /\
  (forall a, q <= a < q + n -> aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
Proof.
  intros LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2 Hperm Hfr Hfa Elo Ehi
    HK HGK HnE HnEs Hoff Hs Hn.
  exact (trans_src_ok_acall_gr_ge0 LAWS HRU HRE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 slo shi E q n HAR HAR2
           Hperm Hfr Hfa Elo Ehi HK HGK HnE HnEs Hoff Hs (Z.lt_le_incl _ _ Hn)).
Qed.

(* Bounds and application memory for a range of any length: a heap block by al_blocks and YCbq.v
   amem_range_of_block; every other case carries decode_rd_ok. *)
Lemma trans_src_ok_amem : AR_laws segs B -> forall lyc Sc (W : world segs) memc mdc q n,
  @AR rc segs B lyc Sc W memc mdc -> trans_src_ok B lyc Sc W memc q n ->
  0 <= q /\ q + n <= 2 ^ 63 /\ amem_range q n.
Proof.
  intros LAWS lyc Sc W memc mdc q n HAR Hs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  destruct Hs as [(bA & nA & Hin & H1 & H2) | (_ & (_ & _ & _ & Ham & H0 & H63))].
  - destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bA nA HAR Hin) as (_ & H4096 & Hce & _ & _ & _ & Hn0).
    pose proof (req_size_pos nA (proj1 Hn0)) as [_ Hreq].
    split; [lia | split; [lia |]].
    exact (amem_range_of_block segs B LAWS lyc Sc W memc mdc bA nA q n HAR Hin H1 ltac:(lia)).
  - split; [exact H0 | split; [exact H63 | exact Ham]].
Qed.
End cgx.

(* trans_sh_any from the record's shadow cells, for a range whose 64-byte hull holds constant shadow bytes that are
   not 0 (a read-only global's partial payload granule, the 0xf9 redzone granules after it), where
   DgnTransportCg.v trans_sh_any_zshadow, which asks the whole hull inside one zero-shadow range, does not apply.
   - trans_sh_cell g v: the shadow byte of the granule at g reads v at every AR state. trans_sh_cell_const gives it
     for a constant cell of the record (a row of as_const, re-read at every AR state by YG0n.v ARm am_const), and
     trans_sh_cell_zshadow for a granule of a zero-shadow range of the record (DgnTransportCg.v decode_zshadow_rd).
   - trans_sh_cells cs: trans_sh_cell of every (granule, value) row of the list cs; built row by row
     (trans_sh_cells_nil / _cons), by concatenation (_app), from one record clause over a list of granules with
     one value (_const: e.g. lib/A/Prog/LLVMFuzzerTestOneInput_cg.v trans_llvmf_cells' 0xf9 clause over
     TRANS_LLVMF_F9, taken whole) and from a zero-shadow range (_zshadow over trans_zgran, its granules with 0).
   - trans_cs_cover cs q n: a closed check (vm_compute at numerals) that every granule of the 64-byte hull of
     [q, q + n) has a row in cs and that every byte x of [q, q + n) is addressable by the row v of its granule
     (YG0v.v saddr_ok x v: v = 0, or x mod 8 < v < 8).
   - trans_sh_any_cells: from trans_sh_cells cs and trans_cs_cover cs q n = true, trans_sh_any of [q, q + n). Its
     reader form, trans_vrow_ra, is DgnTransportCg.v trans_zrow_ra_ge0 with each hull granule's shadow byte only
     visible and each byte of the range addressable at its granule's value. *)
Section shc. Context {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Variable B : asyms.

Definition trans_sh_cell (g v : Z) : Prop :=
  forall ly S (W : world segs) mem md, @AR rc segs B ly S W mem md ->
    aview segs (w_H W) mem (shadow_addr g) = Some v.

(* A constant shadow cell of the record: the one byte of the cell z1 at the granule's shadow byte is v. *)
Lemma trans_sh_cell_const (g v : Z) :
  (forall ly, In (z1 (ANum (FCells.shadow_addr g)) v) (as_const B ly)) -> 0 <= v < 256 -> trans_sh_cell g v.
Proof.
  intros HC Hv ly S W mem md (M & _).
  pose proof (proj1 (Forall_forall _ _) (am_const _ _ _ _ M) _ (HC ly)) as Hh.
  unfold cell_holds in Hh. cbn [z1 c1 c_at c_val c_w aeval] in Hh.
  specialize (Hh 0%nat ltac:(lia)).
  replace (FCells.shadow_addr g + Z.of_nat 0) with (shadow_addr g) in Hh
    by (unfold FCells.shadow_addr, FCells.ASAN_K, shadow_addr, SHADOW_OFF; lia).
  rewrite Hh. f_equal. unfold le_byte.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  rewrite (Z.mod_small v (2 ^ 8)) by (change (2 ^ 8) with 256; lia).
  apply Z.mod_small. exact Hv.
Qed.

(* A granule of a zero-shadow range of the record. *)
Lemma trans_sh_cell_zshadow (lo hi g : Z) :
  decode_zshadow_at B lo hi -> g mod 8 = 0 -> lo <= g -> g + 8 <= hi -> trans_sh_cell g 0.
Proof.
  intros HZ Hg H1 H2 ly S W mem md HAR.
  replace (shadow_addr g) with (FCells.shadow_addr g)
    by (unfold FCells.shadow_addr, FCells.ASAN_K, shadow_addr, SHADOW_OFF; lia).
  exact (decode_zshadow_rd B ly S W mem md lo hi g HAR Hg H1 H2 HZ).
Qed.

Definition trans_sh_cells (cs : list (Z * Z)) : Prop := forall c, In c cs -> trans_sh_cell (fst c) (snd c).

Lemma trans_sh_cells_nil : trans_sh_cells [].
Proof. intros c Hc. destruct Hc. Qed.

Lemma trans_sh_cells_cons (g v : Z) (cs : list (Z * Z)) :
  trans_sh_cell g v -> trans_sh_cells cs -> trans_sh_cells ((g, v) :: cs).
Proof. intros H1 H2 c [<-|Hc]; [exact H1 | exact (H2 c Hc)]. Qed.

Lemma trans_sh_cells_app (cs1 cs2 : list (Z * Z)) :
  trans_sh_cells cs1 -> trans_sh_cells cs2 -> trans_sh_cells (cs1 ++ cs2).
Proof. intros H1 H2 c Hc. apply in_app_or in Hc as [Hc|Hc]; [exact (H1 c Hc) | exact (H2 c Hc)]. Qed.

(* One record clause that gives the value v at the shadow byte of each granule of L. *)
Lemma trans_sh_cells_const (L : list Z) (v : Z) :
  (forall ly a, In a L -> In (z1 (ANum (FCells.shadow_addr a)) v) (as_const B ly)) -> 0 <= v < 256 ->
  trans_sh_cells (map (fun a => (a, v)) L).
Proof.
  intros HC Hv c Hc. apply in_map_iff in Hc as (a & <- & Ha). cbn [fst snd].
  exact (trans_sh_cell_const a v (fun ly => HC ly a Ha) Hv).
Qed.

(* The granules of [lo, hi), each with shadow 0. *)
Definition trans_zgran (lo hi : Z) : list (Z * Z) :=
  map (fun i => (lo + 8 * Z.of_nat i, 0)) (seq 0 (Z.to_nat ((hi - lo) / 8))).

Lemma trans_sh_cells_zshadow (lo hi : Z) :
  decode_zshadow_at B lo hi -> lo mod 8 = 0 -> trans_sh_cells (trans_zgran lo hi).
Proof.
  intros HZ Hlo c Hc. unfold trans_zgran in Hc. apply in_map_iff in Hc as (i & <- & Hi).
  apply in_seq in Hi. cbn [fst snd].
  assert (Hd : Z.of_nat i < (hi - lo) / 8) by lia.
  pose proof (Z.mul_div_le (hi - lo) 8 ltac:(lia)) as Hm.
  apply (trans_sh_cell_zshadow lo hi); [exact HZ | | lia | lia].
  replace (lo + 8 * Z.of_nat i) with (lo + Z.of_nat i * 8) by ring. rewrite Z_mod_plus_full. exact Hlo.
Qed.

(* The row of granule g in cs (the first one), and the closed check of a range [q, q + n) against cs. *)
Definition trans_cs_find (cs : list (Z * Z)) (g : Z) : option Z :=
  match find (fun c => Z.eqb (fst c) g) cs with Some c => Some (snd c) | None => None end.
Definition trans_saddr_b (x v : Z) : bool := (v =? 0) || ((x mod 8 <? v) && (v <? 8)).
Definition trans_cs_cover (cs : list (Z * Z)) (q n : Z) : bool :=
  forallb (fun i => match trans_cs_find cs (q / 64 * 64 + 8 * Z.of_nat i) with Some _ => true | None => false end)
    (seq 0 (Z.to_nat (((q + n - 1) / 64 * 64 + 64 - q / 64 * 64) / 8))) &&
  forallb (fun i => match trans_cs_find cs ((q + Z.of_nat i) / 8 * 8) with
                    | Some v => trans_saddr_b (q + Z.of_nat i) v
                    | None => false
                    end)
    (seq 0 (Z.to_nat n)).

Lemma trans_cs_find_cell (cs : list (Z * Z)) (g v : Z) :
  trans_sh_cells cs -> trans_cs_find cs g = Some v -> trans_sh_cell g v.
Proof.
  intros HC Hf. unfold trans_cs_find in Hf.
  destruct (find (fun c => fst c =? g) cs) as [c|] eqn:E; [|discriminate Hf].
  injection Hf as <-. apply find_some in E as [Hin Heq]. cbv beta in Heq. apply Z.eqb_eq in Heq. rewrite <- Heq.
  exact (HC c Hin).
Qed.

(* The reader form: each granule of [lo, hi) has a visible shadow byte and each byte of [q, q + n) is addressable at
   its granule's shadow byte; the range's 64-byte blocks lie in [lo, hi). *)
Lemma trans_vrow_ra (rd : Z -> option Z) (lo hi q n : Z) :
  (forall T, T mod 8 = 0 -> lo <= T -> T + 8 <= hi -> rd (shadow_addr T) <> None) ->
  (forall x, q <= x < q + n -> exists s, rd (shadow_addr (x / 8 * 8)) = Some s /\ saddr_ok x s) ->
  lo <= q / 64 * 64 -> (q + n - 1) / 64 * 64 + 64 <= hi ->
  range_addressable rd SHADOW_OFF q n /\ shadow_hull_vis rd q n.
Proof.
  intros HV HA Hlo Hhi.
  pose proof (Z.div_mod q 64 ltac:(lia)). pose proof (Z.mod_pos_bound q 64 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(lia)).
  split.
  - intros x Hx. destruct (HA x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    replace (shadow_of_addr SHADOW_OFF x) with (shadow_addr (x / 8 * 8))
      by (unfold shadow_of_addr, shadow_addr; rewrite Z.div_mul by lia; reflexivity).
    exact Hs.
  - intros s Hs.
    assert (ES : shadow_addr ((s - SHADOW_OFF) * 8) = s) by (unfold shadow_addr; rewrite Z.div_mul by lia; lia).
    rewrite <- ES. apply HV; [apply Z_mod_mult | |].
    all: unfold shadow_addr, SHADOW_OFF in Hs |- *.
    all: pose proof (Z.div_mod q 8 ltac:(lia)); pose proof (Z.mod_pos_bound q 8 ltac:(lia));
      pose proof (Z.div_mod (q + n - 1) 8 ltac:(lia)); pose proof (Z.mod_pos_bound (q + n - 1) 8 ltac:(lia));
      pose proof (Z.div_mod (2147450880 + q / 8) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (2147450880 + q / 8) 8 ltac:(lia));
      pose proof (Z.div_mod (2147450880 + (q + n - 1) / 8) 8 ltac:(lia));
      pose proof (Z.mod_pos_bound (2147450880 + (q + n - 1) / 8) 8 ltac:(lia)); lia.
Qed.

(* trans_sh_any of a range, empty or not, from the shadow cells cs of the record that cover its 64-byte hull. *)
Lemma trans_sh_any_cells (cs : list (Z * Z)) (q n : Z) :
  trans_sh_cells cs -> trans_cs_cover cs q n = true -> trans_sh_any B q n.
Proof.
  intros HC Hcov ly S W mem md HAR.
  unfold trans_cs_cover in Hcov. apply andb_true_iff in Hcov as [HG HX].
  rewrite forallb_forall in HG, HX. cbv beta in HG, HX.
  pose proof (Z.div_mod q 64 ltac:(lia)). pose proof (Z.mod_pos_bound q 64 ltac:(lia)).
  pose proof (Z.div_mod (q + n - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (q + n - 1) 64 ltac:(lia)).
  apply (trans_vrow_ra _ (q / 64 * 64) ((q + n - 1) / 64 * 64 + 64) q n); [| | lia | lia].
  - intros T HT HT1 HT2.
    pose proof (Z.div_mod T 8 ltac:(lia)).
    pose proof (Z.div_mod (T - q / 64 * 64) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (T - q / 64 * 64) 8 ltac:(lia)).
    pose proof (Z.div_mod ((q + n - 1) / 64 * 64 + 64 - q / 64 * 64) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound ((q + n - 1) / 64 * 64 + 64 - q / 64 * 64) 8 ltac:(lia)).
    assert (Hd : 0 <= (T - q / 64 * 64) / 8 < ((q + n - 1) / 64 * 64 + 64 - q / 64 * 64) / 8) by lia.
    assert (ET : q / 64 * 64 + 8 * Z.of_nat (Z.to_nat ((T - q / 64 * 64) / 8)) = T)
      by (rewrite Z2Nat.id by lia; lia).
    pose proof (HG (Z.to_nat ((T - q / 64 * 64) / 8)) ltac:(apply in_seq; lia)) as HGi.
    rewrite ET in HGi.
    revert HGi. destruct (trans_cs_find cs T) as [v|] eqn:Ef; intro HGi; [|discriminate HGi].
    rewrite (trans_cs_find_cell cs T v HC Ef ly S W mem md HAR). discriminate.
  - intros x Hx.
    pose proof (HX (Z.to_nat (x - q)) ltac:(apply in_seq; lia)) as HXi.
    rewrite Z2Nat.id in HXi by lia. replace (q + (x - q)) with x in HXi by lia.
    revert HXi. destruct (trans_cs_find cs (x / 8 * 8)) as [v|] eqn:Ef; intro HXi; [|discriminate HXi].
    exists v. split; [exact (trans_cs_find_cell cs (x / 8 * 8) v HC Ef ly S W mem md HAR)|].
    unfold trans_saddr_b in HXi. unfold saddr_ok.
    apply orb_true_iff in HXi as [Hb|Hb]; [left; apply Z.eqb_eq in Hb; exact Hb | right].
    apply andb_true_iff in Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1. apply Z.ltb_lt in Hb2. lia.
Qed.
End shc.
