(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/B/Prog/PItems_entry.v, with its module paths and module names changed; 2668 of its 2786 lines of code are new or changed and 1447 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S7a_put.v, with its module paths and module names changed; 1917 of its 1994 lines of code are new or changed and 2709 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/A/FSW_put_grow_tail.v, with its module paths, module names and numbers changed; 2 of its 286 lines of code are new or changed and 1710 lines of the source are left out. *)
(* fs WRITER walk, image B (fs.asan-ubsan): put's GROW arm, second half, the piece pgt_src_after: the source range
   [s, s + n) when fuzz_realloc returns to put (resume pc 542080 = 0x84580), over lib/B/FSW_put_grow_tail.v's Section
   data (copied below, same order).
   B FACTS this piece uses (it runs no code; it reasons on blocks and memory only):
   - B's image is [0x10000, 0x5fd000) (lib/B/FSW_put.v:182 fsw_pf_in_img); every FS_RO_STRS literal, its NUL included,
     lies in it (:193 fsw_pf_ro_strs_img); the read-only image lies below the shadow (:202 fsw_pf_roP_low).
   - put's frame on B is 112 bytes (the call's sp is spZ regs - 112, HMF). The proof needs only 112 <= STK_put, which it
     computes; no STK value is pinned.
   - Of fs_img_facts' cstr_ok (lib/A/FSH_Gen.v) it reads the byte list, range_addressable and shadow_hull_vis over
     length l + 1 only, never the alloc_ceiling bound (`+ 8` on c33a9d6a7d4, `+ 1` on a9edd281227): built green on both.
   TAKEN FROM: lib/A/FSW_put_grow_tail.v:1606-1825 (pgt_src_after) at a working branch 860b2fb1188,
   statement and proof text unchanged but the STK bound (A: 4208 <= STK_put). B kit: lib/B/FSW_put.v:182, :193, :202,
   :230 fsw_pf_ush_out, :239 fsw_pf_ra_raw, :248 fsw_pf_hull_raw, :258 fsw_pf_blk_disj, :273 fsw_pf_heads_out,
   :285 fsw_pf_img_out, :302 fsw_pf_unp; lib/B/FSW_rd.v:566 fsw_roP_img, :602 arodata_kept; lib/B/FSW_K.v:89 fsw_ARU,
   :123 fsw_sp, :549 mbyte_below, :575 arodata_below; lib/B/FSW_put_grow_tail.v:213 pgt_pstat_img, :218 pgt_pstat_not_ro,
   :232 pgt_same_start.
   rule 24: proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YG0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require FSW_rd.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSupoison FSupoisonU FSupoisonStack FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
YB1v YB1w FSH_Base FSH_Rt FSPstat FSH_Fn_writer FSH_Fn_alloc FSW_K FSW_K3 FSW_ret FSW_put FSW_put_grow FSW_put_grow_model FSW_put_grow_tail.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterApp.
From OSSVerify.omx_clap_core.fuzz_state.images Require AsanUbsan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section pgt. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
(* S0's shadow-base cells (lib/B/FSH_Base.v FsShadowSyms), the one interceptor contract the granted path calls
   (__asan_memcpy, lib/B/FSH_Rt.v FsRt's fr_memcpy field, as lib/B/FSW_put.v takes it) and the image facts *)
Hypothesis HSS : FsShadowSyms B.
Hypothesis RT_memcpy : FSupoisonU.aintrin_realizesU tfibsegs B OCpy PC_memcpy.
Hypothesis IMG : fs_img_facts tfibsegs B.
(* THE CALLEE: fuzz_realloc's ASan contract, a statement only (lib/B/FSH_Fn_alloc.v, by path from dda8331bd25:
   CTX-free with its `cnt <> fail ->` room guards), discharged at composition. *)
Hypothesis HREALLOC : fuzz_realloc_spec tfibsegs B.

(* ---- put_spec's data, on the grow arm (failed = 0, cap < len + n + 1) ---- *)
Variables (ly : alayout) (S : astate) (U : list (Z * Z)) (W : world tfibsegs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ch : list (Z * Z * Z)) (ot o s n buf cap : Z) (text bs : list Z)
  (live peak cnt fail : Z).
Hypothesis HPRE : fpreU tfibsegs B STK_put ly S U W regs mem md ch.
Hypothesis FH : fs_heads B ly S U.
Hypothesis HHEAD : cap <> 0 -> In (buf - HEAD, HEAD) U.
Hypothesis G10 : getr regs 10 = w64 o.
Hypothesis G11 : getr regs 11 = w64 s.
Hypothesis G12 : getr regs 12 = w64 n.
Hypothesis HOUT : wout_ok B tfibsegs ly S W mem o buf cap 0 text.
Hypothesis HGLOB : fs_glob tfibsegs W mem live peak cnt fail.
Hypothesis Hspo : spZ regs <= o.
Hypothesis Hoot : o + 32 <= ot.
Hypothesis Hot16 : ot mod 16 = 0.
Hypothesis Hottop : ot <= ly_top ly.
Hypothesis HCHN :
  o = spZ regs + 8 /\ raZ regs < alloc_ceiling \/
  spZ regs + 16 <= o /\ exists ra nfp, rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 8) = Some ra /\
    rdword (aview tfibsegs (w_H W) (unpoison U mem)) (o - 16) = Some nfp /\ (ra < 4096 \/ nfp < alloc_ceiling).
Hypothesis HPRESENT : forall a, spZ regs <= a < ot -> apresent (w_H W) mem a.
Hypothesis HZS : zbytes_at tfibsegs W mem s bs.
Hypothesis HSK : wsrc_kept B tfibsegs ly S U W mem buf s bs.
Hypothesis Hlen : Z.of_nat (length bs) = n.
Hypothesis Hbok : WriterSpec.bytes_ok bs.
Hypothesis HSRC : 0 <= s /\ s + n <= alloc_ceiling.
Hypothesis Hsdisj : s + n <= o \/ ot <= s.
Hypothesis HWM : Z.of_nat (length text) + n + 1 <= WMAX.
Hypothesis HCAP : cap <= WMAX.
Hypothesis HCL : cap <= live.
Hypothesis HBUD : wbudget_pre S cap cnt live (WriterApp.put1 (WriterApp.mkW 0 text cap cnt fail []) bs).
Hypothesis HGROW : cap < Z.of_nat (length text) + n + 1.

(* ---- the first half's hand-over, at the call of fuzz_realloc (lib/B/FSW_put_grow_run.v fsw_pg_to_call's
   continuation; A's Theorem Labs lane interface) ---- *)
Variables (E' : env) (ms' : machine_state) (mdc : Model) (c : Z).
Hypothesis HS : st_ok tfibsegs E' fsw_pg_ssc (restrict (w_H W) ms').
Hypothesis HJ : ajournal tfibsegs B (STK_put + (ot - spZ regs)) ot (FS_PSTAT_FP ++ wbuf_fp buf cap)
  ly S W (unpoison U mem) md [] ly S W (unpoison U (ms_mem ms')) mdc 0.
Hypothesis HARU : ARU tfibsegs B ly S U W (ms_mem ms') mdc.
Hypothesis HMF : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 112 <= a < spZ regs) ->
  ms_mem ms' (Z_to_bv 64 a) = mem (Z_to_bv 64 a).
Hypothesis HPRK : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms') a.
Hypothesis HEA : YP06.env_agree 36
  (Ereg regs (fs_extraT ++ [Z_to_bv 64 buf; Z_to_bv 64 (Z.of_nat (length text)); Z_to_bv 64 cap])) E'.
Hypothesis HE36 : ew E' 36 = Z_to_bv 64 c.
Hypothesis Hcnew : c = WriterSpec.newcap cap (Z.of_nat (length text) + n + 1).
Hypothesis Hc4096 : 4096 <= c.
Hypothesis HcW : c <= WMAX.
Hypothesis Hcneed : Z.of_nat (length text) + n + 1 <= c.

(* the source range after fuzz_realloc, from wsrc_kept: in a live block other than the old buffer (its bytes off the
   callee's footprint FP1, kept by the callee journal; its user bytes hold no head after the call), or a prefix of a
   read-only literal (fs_img_facts' cstr_ok, read on the memory after the call through FSW_rd.arodata_kept); and it
   avoids every block the call created *)
Lemma pgt_src_after : forall FP1 kc ly2 S2 U2 W2 mem2 md2,
  ajournal tfibsegs B STK_fuzz_realloc (spZ (ms_regs ms')) FP1 ly S W (unpoison U (ms_mem ms')) mdc []
    ly2 S2 W2 (unpoison U2 mem2) md2 kc ->
  ARU tfibsegs B ly2 S2 U2 W2 mem2 md2 -> fs_heads B ly2 S2 U2 ->
  (forall a, inFP FP1 a -> inFP FS_PSTAT_FP a \/ (cap <> 0 /\ buf - HEAD <= a < buf + cap)) ->
  (forall p k, In (p, k) (ablocks B ly S) -> p <> buf - HEAD -> In (p, k) (ablocks B ly2 S2)) ->
  (forall r, In r U2 -> In r U \/ exists m, In (fst r, m) (ablocks B ly2 S2) /\ ~ In (fst r, m) (ablocks B ly S) /\
     snd r = HEAD /\ HEAD <= req_size m) ->
  zbytes_at tfibsegs W2 mem2 s bs /\
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF s n /\
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W2) mem2) s n) /\ amem_range s n /\
  (forall i, 0 <= i < n ->
     mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)) /\
  (forall q m, In (q, m) (ablocks B ly2 S2) -> ~ In (q, m) (ablocks B ly S) -> 0 < m ->
     forall x, s <= x < s + n -> ~ (q <= x < q + req_size m)).
Proof.
intros FP1 kc ly2 S2 U2 W2 mem2 md2 HJc HARU2 FH2 HFP1 HBK HU2.
pose proof (AR_laws_ok tfibsegs B) as LAWS.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (fsw_sp B STK_put ly S U W regs mem md ch (proj1 HPRE)) as (Hal16 & Hspc & Hsp47 & _).
assert (HSTK : 112 <= STK_put) by (vm_compute; discriminate).
pose proof HPRE as (HPREU & HRO).
pose proof HPREU as (HAP & HUOK & HUPO).
pose proof HAP as (HAR & _).
pose proof HSRC as (Hs0 & Hsn).
pose proof HOUT as (_ & _ & _ & _ & Hbuf64 & Hcap64 & _ & _ & _ & _ & _ & _ & Hcase).
pose proof HJc as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
assert (SB : same_below mem (ms_mem ms') alloc_ceiling) by (intros x Hx; apply HMF; lia).
(* the old buffer, a block of the entry when cap <> 0 *)
assert (OLDB : cap <> 0 -> In (buf - HEAD, cap + HEAD) (ablocks B ly S) /\ 0 < cap).
{ intros Hc0. destruct Hcase as [(E0 & _) | (_ & (Hin & _ & Hcp & _) & _)]; [lia | split; [exact Hin | exact Hcp]]. }
(* a byte of a block live at both ends, off FP1, is the entry's *)
assert (BK : forall p k i, In (p, k) (ablocks B ly S) -> In (p, k) (ablocks B ly2 S2) -> 0 <= i < req_size k ->
  ~ inFP FP1 (p + i) ->
  mbyte tfibsegs (mrestrict (w_H W2) mem2) (p + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (p + i)).
{ intros p k i H1 H2 Hi Hnf.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p k HAR H1) as (_ & Hp4096 & Hpc & Hpapp & _).
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Hpapp.
  rewrite <- (mbyte_below (w_H W) mem (ms_mem ms') alloc_ceiling (p + i) SB) by lia.
  apply (mbyte_of_aview tfibsegs).
  rewrite <- (aview_at tfibsegs (w_H W2) (unpoison U2 mem2) mem2 (p + i))
    by (apply (fsw_pf_unp B ly2 S2 U2 W2 mem2 md2 (p + i) HARU2); unfold SHADOW_OFF; lia).
  rewrite <- (aview_at tfibsegs (w_H W) (unpoison U (ms_mem ms')) (ms_mem ms') (p + i))
    by (apply (fsw_pf_unp B ly S U W (ms_mem ms') mdc (p + i) HARU); unfold SHADOW_OFF; lia).
  exact (F2 p k i H1 H2 Hi Hnf). }
(* a byte of a block of the entry other than the old buffer is off FP1 *)
assert (OFF : forall p k i, In (p, k) (ablocks B ly S) -> p <> buf - HEAD -> 0 <= i < req_size k -> ~ inFP FP1 (p + i)).
{ intros p k i H1 Hp Hi Hf. destruct (HFP1 _ Hf) as [Hps | (Hc0 & Hb)].
  - apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md p k (p + i) HAR H1); [lia | exact (pgt_pstat_img _ Hps)].
  - destruct (OLDB Hc0) as (Hin & Hcp).
    pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
    destruct (fsw_pf_blk_disj B ly S W (unpoison U mem) md p k (buf - HEAD) (cap + HEAD) HAR H1 Hin Hp) as [D|D];
      unfold HEAD in *; lia. }
(* a block of the entry other than the old buffer is disjoint from every block the call created *)
assert (NEWD : forall p k q m, In (p, k) (ablocks B ly S) -> p <> buf - HEAD -> 0 < k ->
  In (q, m) (ablocks B ly2 S2) -> ~ In (q, m) (ablocks B ly S) -> 0 < m ->
  p + req_size k <= q \/ q + req_size m <= p).
{ intros p k q m H1 Hp Hk H2 H3 Hm.
  pose proof (HBK p k H1 Hp) as H1'.
  destruct (Z.eq_dec p q) as [<- | Hne].
  - exfalso. apply H3. rewrite <- (pgt_same_start B ly2 S2 W2 (unpoison U2 mem2) md2 p k m HAR2 H1' H2 Hk Hm).
    exact H1.
  - exact (fsw_pf_blk_disj B ly2 S2 W2 (unpoison U2 mem2) md2 p k q m HAR2 H1' H2 Hne). }
destruct HSK as [[Hbs Ham] | [(p & k & Hpb & Hrb & Hps & Hpk) | [(p & k & Hpb & Hin2 & Hps & Hpk & HU) | (l & Hl & Hll)]]].
- (* nothing is read *)
  subst bs. cbn [length Z.of_nat] in Hlen. subst n.
  split; [unfold zbytes_at; apply garr8_nil|]. split; [apply range_addressable_nil; lia|].
  split; [lia|]. split; [exact Ham|]. split; [intros i Hi; lia|]. intros q m _ _ _ x Hx; lia.
- (* the user bytes of another reader block *)
  rewrite Hlen in Hpk. pose proof Hrb as (Hin2 & Hp16 & Hk0 & _).
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (p - HEAD) (k + HEAD) HAR Hin2)
    as (_ & Hp4096 & Hpceil & Hpapp & _).
  assert (RQ : req_size (k + HEAD) = k + HEAD) by (unfold req_size, HEAD; destruct (Z.eqb_spec (k + 16) 0); lia).
  rewrite RQ in Hpceil, Hpapp. unfold in_app, kLowShadowBeg, ASAN_CEIL, HEAD in Hpapp. unfold HEAD in Hpceil, Hp4096.
  assert (Hpn : p - HEAD <> buf - HEAD) by (unfold HEAD; lia).
  pose proof (HBK _ _ Hin2 Hpn) as Hin2'.
  assert (KS : forall i, 0 <= i < n ->
    mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)).
  { intros i Hi. replace (s + i) with (p - HEAD + (s + i - (p - HEAD))) by lia.
    apply (BK (p - HEAD) (k + HEAD)); [exact Hin2 | exact Hin2' | rewrite RQ; unfold HEAD; lia |].
    apply (OFF (p - HEAD) (k + HEAD)); [exact Hin2 | exact Hpn | rewrite RQ; unfold HEAD; lia]. }
  assert (OUT : forall x, s <= x < s + n -> in_ush U2 (shadow_addr x) = false).
  { intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU2))); [lia|].
    exact (fsw_pf_heads_out B ly2 S2 U2 W2 (unpoison U2 mem2) md2 p k x HAR2 FH2 Hin2' Hk0 ltac:(lia)). }
  split.
  { unfold zbytes_at in HZS |- *. apply (garr8_frame tfibsegs _ _ s bs HZS).
    intros a Ha. rewrite Hlen in Ha. replace a with (s + (a - s)) by lia. apply KS. lia. }
  split.
  { apply (fsw_pf_ra_raw (w_H W2) U2 mem2 s n); [lia | lia | exact OUT |].
    apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 (p - HEAD) (k + HEAD) s n
      HAR2 Hin2'); rewrite ?RQ; unfold HEAD; lia. }
  split.
  { intros Hn1. apply (fsw_pf_hull_raw W2 U2 mem2 s n (proj2 (proj2 HARU2))); [lia | lia |].
    apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 (p - HEAD) (k + HEAD) s n
      HAR2 Hin2'); rewrite ?RQ; unfold HEAD; lia. }
  split; [unfold amem_range; lia|]. split; [exact KS|].
  intros q m Hq Hnq Hm0 x Hx Hxq.
  destruct (NEWD (p - HEAD) (k + HEAD) q m Hin2 Hpn ltac:(unfold HEAD; lia) Hq Hnq Hm0) as [D|D];
    rewrite ?RQ in D; unfold HEAD in *; lia.
- (* any other live block, the range avoiding every head of U *)
  rewrite Hlen in Hpk, HU.
  destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md p k HAR Hin2) as (_ & Hp4096 & Hpceil & Hpapp & _ & _ & HkM).
  pose proof (req_size_pos k ltac:(lia)) as (RQ1 & RQ2).
  unfold in_app, kLowShadowBeg, ASAN_CEIL in Hpapp.
  pose proof (HBK _ _ Hin2 Hpb) as Hin2'.
  destruct (Z.eq_dec n 0) as [Hn0 | Hn0].
  + (* nothing is read: every clause is vacuous but the range's own facts *)
    rewrite Hn0. split.
    { unfold zbytes_at. destruct bs as [|b0 bs']; [apply garr8_nil | cbn [length] in Hlen; lia]. }
    split; [apply range_addressable_nil; lia|]. split; [lia|]. split; [unfold amem_range; lia|].
    split; [intros i Hi; lia|]. intros q m _ _ _ x Hx; lia.
  + assert (Hk0 : 0 < k) by (destruct (Z.eq_dec k 0) as [E0|E0]; [subst k; unfold req_size in Hpk; cbn in Hpk; lia | lia]).
    assert (KS : forall i, 0 <= i < n ->
      mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)).
    { intros i Hi. replace (s + i) with (p + (s + i - p)) by lia.
      apply (BK p k); [exact Hin2 | exact Hin2' | lia |].
      apply (OFF p k); [exact Hin2 | exact Hpb | lia]. }
    assert (OUT : forall x, s <= x < s + n -> in_ush U2 (shadow_addr x) = false).
    { intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU2))); [lia|].
      intros r Hr Hxr. destruct (HU2 r Hr) as [HrU | (m & Hm2 & Hm1 & Hsr & HmR)].
      - destruct (HU r HrU); lia.
      - assert (Hm0 : 0 < m) by (destruct (Z.eq_dec m 0) as [E|E]; [subst m; unfold req_size in HmR; cbn in HmR;
                                                                     unfold HEAD in HmR; lia | ];
                                 destruct (al_blocks _ _ LAWS ly2 S2 W2 (unpoison U2 mem2) md2 _ m HAR2 Hm2)
                                   as (_ & _ & _ & _ & _ & _ & HmM); lia).
        pose proof (req_size_pos m ltac:(lia)) as (Rm1 & Rm2).
        destruct (NEWD p k (fst r) m Hin2 Hpb Hk0 Hm2 Hm1 Hm0) as [D|D]; rewrite Hsr in Hxr; unfold HEAD in *; lia. }
    split.
    { unfold zbytes_at in HZS |- *. apply (garr8_frame tfibsegs _ _ s bs HZS).
      intros a Ha. rewrite Hlen in Ha. replace a with (s + (a - s)) by lia. apply KS. lia. }
    split.
    { apply (fsw_pf_ra_raw (w_H W2) U2 mem2 s n); [lia | lia | exact OUT |].
      apply (range_addressable_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 p k s n HAR2 Hin2'); lia. }
    split.
    { intros Hn1. apply (fsw_pf_hull_raw W2 U2 mem2 s n (proj2 (proj2 HARU2))); [lia | lia |].
      apply (shadow_hull_vis_of_block tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 p k s n HAR2 Hin2'); lia. }
    split; [unfold amem_range; lia|]. split; [exact KS|].
    intros q m Hq Hnq Hm0 x Hx Hxq.
    destruct (NEWD p k q m Hin2 Hpb Hk0 Hq Hnq Hm0) as [D|D]; lia.
- (* a prefix of a read-only literal: fs_img_facts' cstr_ok at the entry and on the memory after the call *)
  destruct (fsw_pf_ro_strs_img s l Hl) as (Hl0 & Hl1).
  assert (Hnl : n <= Z.of_nat (length l) + 1).
  { pose proof (proj1 (Nat2Z.inj_le _ _) Hll) as H'. rewrite Nat2Z.inj_succ in H'. lia. }
  pose proof IMG as (_ & IMG2).
  assert (HARU0 : ARU tfibsegs B ly S U W mem md) by exact (fsw_ARU B STK_put ly S U W regs mem md ch HPREU).
  (* the read-only view at the entry, on the unpoisoned memory *)
  assert (HRO' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (unpoison U mem))).
  { intros a Ha Hno Hne. pose proof (fsw_pf_roP_low a Ha) as Ha'.
    rewrite (aview_at tfibsegs (w_H W) (unpoison U mem) mem a); [exact (HRO a Ha Hno Hne)|].
    apply (fsw_pf_unp B ly S U W mem md a HARU0); unfold SHADOW_OFF in *; lia. }
  (* ... at the call, and after it (FSW_rd.arodata_kept: FP1 is closed and holds no read-only byte) *)
  assert (HROc : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W) (ms_mem ms')))
    by exact (arodata_below B W mem (ms_mem ms') SB HRO).
  assert (Hcl : ~ YI16.sink_open_fp FP1).
  { intros (r & Hr & H0). destruct (HFP1 0 (ex_intro _ r (conj Hr H0))) as [Hps | (Hc0 & Hb)].
    - destruct Hps as (r' & Hr' & H0'). unfold FS_PSTAT_FP in Hr'.
      destruct Hr' as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in H0'; lia.
    - destruct (OLDB Hc0) as (Hin & _).
      destruct (al_blocks _ _ LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) HAR Hin) as (_ & Hb4096 & _).
      unfold HEAD in *. lia. }
  assert (Hro1 : forall a, in_roP tfibsegs FS_RLO FS_RHI a -> ~ inFP FP1 a).
  { intros a Ha Hf. destruct (HFP1 a Hf) as [Hps | (Hc0 & Hb)].
    - exact (pgt_pstat_not_ro a Ha Hps).
    - destruct (OLDB Hc0) as (Hin & Hcp).
      pose proof (req_size_pos (cap + HEAD) ltac:(unfold HEAD; lia)) as (_ & RQ).
      apply (blk_img tfibsegs B LAWS ly S W (unpoison U mem) md (buf - HEAD) (cap + HEAD) a HAR Hin);
        [unfold HEAD in *; lia | exact (FSW_rd.fsw_roP_img a Ha)]. }
  assert (HRO2 : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) mem2))
    by exact (FSW_rd.arodata_kept B STK_fuzz_realloc (spZ (ms_regs ms')) FP1 ly S U W (ms_mem ms') mdc ly2 S2 U2 W2
                mem2 md2 kc HJc HARU (proj1 (proj2 HARU2)) (proj2 (proj2 HARU2)) Hcl Hro1 HROc).
  assert (HRO2' : arodata_okP tfibsegs FS_RLO FS_RHI B (aview tfibsegs (w_H W2) (unpoison U2 mem2))).
  { intros a Ha Hno Hne. pose proof (fsw_pf_roP_low a Ha) as Ha'.
    rewrite (aview_at tfibsegs (w_H W2) (unpoison U2 mem2) mem2 a); [exact (HRO2 a Ha Hno Hne)|].
    apply (fsw_pf_unp B ly2 S2 U2 W2 mem2 md2 a HARU2); unfold SHADOW_OFF in *; lia. }
  destruct (IMG2 ly S W (unpoison U mem) md HAR HRO') as (_ & _ & HSTRS & _).
  destruct (proj1 (Forall_forall _ _) HSTRS (s, l) Hl) as (Hcs & _). cbn [fst snd] in Hcs.
  destruct Hcs as ((Hga & _) & _ & _ & _ & Hamr & _ & _ & _).
  destruct (IMG2 ly2 S2 W2 (unpoison U2 mem2) md2 HAR2 HRO2') as (_ & _ & HSTRS2 & _).
  destruct (proj1 (Forall_forall _ _) HSTRS2 (s, l) Hl) as (Hcs2 & _). cbn [fst snd] in Hcs2.
  destruct Hcs2 as ((Hga2 & _) & _ & _ & _ & _ & HRA2 & HHULL2 & _).
  (* the image bytes are no user-poisoned shadow byte, at either end *)
  assert (RAWE : forall x, 0x10000 <= x < 0x5fd000 ->
    mbyte tfibsegs (mrestrict (w_H W) (unpoison U mem)) x = mbyte tfibsegs (mrestrict (w_H W) mem) x).
  { intros x Hx. unfold mbyte, mrestrict.
    rewrite (fsw_pf_unp B ly S U W mem md x HARU0) by (unfold SHADOW_OFF; lia). reflexivity. }
  assert (RAW2 : forall x, 0x10000 <= x < 0x5fd000 ->
    mbyte tfibsegs (mrestrict (w_H W2) (unpoison U2 mem2)) x = mbyte tfibsegs (mrestrict (w_H W2) mem2) x).
  { intros x Hx. unfold mbyte, mrestrict.
    rewrite (fsw_pf_unp B ly2 S2 U2 W2 mem2 md2 x HARU2) by (unfold SHADOW_OFF; lia). reflexivity. }
  assert (KS : forall i, 0 <= i < n ->
    mbyte tfibsegs (mrestrict (w_H W2) mem2) (s + i) = mbyte tfibsegs (mrestrict (w_H W) mem) (s + i)).
  { intros i Hi.
    assert (Hil : (Z.to_nat i < length (l ++ [0%Z]))%nat) by (rewrite length_app; cbn [length]; lia).
    destruct (Hga (Z.to_nat i) Hil) as (V1 & _). destruct (Hga2 (Z.to_nat i) Hil) as (V2 & _).
    specialize (V1 0%nat ltac:(lia)). specialize (V2 0%nat ltac:(lia)).
    replace (s + Z.of_nat (Z.to_nat i) + Z.of_nat 0) with (s + i) in V1, V2 by lia.
    rewrite <- (RAWE (s + i)) by lia. rewrite <- (RAW2 (s + i)) by lia. rewrite V1, V2. reflexivity. }
  assert (OUT : forall x, s <= x < s + n -> in_ush U2 (shadow_addr x) = false).
  { intros x Hx. apply (fsw_pf_ush_out B ly2 S2 U2 x (proj1 (proj2 HARU2))); [lia|].
    apply (fsw_pf_img_out B ly2 S2 U2 W2 (unpoison U2 mem2) md2 x HAR2 (proj1 (proj2 HARU2))).
    apply fsw_pf_in_img. lia. }
  split.
  { unfold zbytes_at in HZS |- *. apply (garr8_frame tfibsegs _ _ s bs HZS).
    intros a Ha. rewrite Hlen in Ha. replace a with (s + (a - s)) by lia. apply KS. lia. }
  split.
  { apply (fsw_pf_ra_raw (w_H W2) U2 mem2 s n); [lia | lia | exact OUT |].
    eapply range_addressable_sub; [exact HRA2 | lia | lia]. }
  split.
  { intros Hn1. apply (fsw_pf_hull_raw W2 U2 mem2 s n (proj2 (proj2 HARU2))); [lia | lia |].
    intros t Ht. apply HHULL2. unfold shadow_addr in *. lia. }
  split; [unfold amem_range in *; lia|]. split; [exact KS|].
  intros q m Hq _ _ x Hx Hxq.
  apply (blk_img tfibsegs B LAWS ly2 S2 W2 (unpoison U2 mem2) md2 q m x HAR2 Hq); [lia|].
  apply fsw_pf_in_img. lia.
Qed.


End pgt.
