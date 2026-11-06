(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: the ARx-GENERIC twin of lib/B/W_drain_cx.v, the shared context of image B's drain walk family
   (step 2), the image-B twin of lib/A/W_drain_cx_x.v (sha256 8d1e9699d0e9; internal record: the file at 3d17f490d56 (sha256 edfd77859c8e; internal record), the
   bridges of a Theorem Labs lane's 301e00df93c4 and sep_blocks_perm_x of 35e3f98858e), stated against lib/B/W_drain_cx.v.
   W_drain_cx.v is NOT edited: this file sits beside it, and every walk that cites W_drain_cx.v builds unchanged.
   - Each AR-stated definition or lemma NAME of W_drain_cx.v has its twin NAME_x here, in W_drain_cx.v's Section
     nesting, over a Section relation `ARx` (its third argument the ghost list Hp), the laws
     `LAWS : AR_laws_x SEGS B ARx hl` (YCbqG.v) and the placement parameter PST of the journal
     W_journal_x.ajournal_gx_x. PST and ARx follow B among the Section variables, so a twin's arguments are the
     original's with PST ARx after B (ARx alone where PST is unused).
   - The entry context record dcx is W_drain_cx.v's, unchanged: the entry's ghost list Hp is an argument right after
     cx (dPOST_x, DBASE_x, DMEM_x, the cut predicates and every segment statement), the pre is YCbqG.afn_pre_x at Hp,
     the post W_contract_x.dr_post_x at Hp. A cut's own ghost list Hp1 follows S1: in DMEM_x / LCORE_x / DLC_x as an
     argument, in the cut predicates DI_x .. DGS_x as an existential right after S1, and in dr_epi_stmt_x as a binder
     after S1.
   - The Section hypotheses are their twins: the allocator rules W_journal_x.<rule>_c_x (AREALLOC, AFREE, ASTRNDUP,
     at B's caller-context tables CTX_R / CTX_F / CTX_S, as W_drain_cx.v's _c rules; the call-site facts HCTX_* are
     W_drain_cx.v's, at B's own offsets), the sites W_sites_x.<site>_x (AERRNO, AMEMMOVE, ASTRRCHR, ASTRNCMP,
     ASTRCMP, and the two runtime contracts aintrin_realizes_x / amemchr_realizesM_x), the specs W_contract_x's
     (ASTRLEN, SLSPEC, LPSPEC), ALLOC_TAIL over ARx (Hp after S), and dlit_at_x over W_contract_x.ashp_x. The other
     hypotheses name no AR and are W_drain_cx.v's text (B's indices and image band: A_OBJ 18 / 19 / 20 / 21 / 30,
     IMG_TOP, HSD, HERRAL).
   - ALLOC_TAIL stays a Section hypothesis, as in the base text; over ARx it is a theorem of the laws: alloc_tail_x
     (Section t) proves it from AR_laws_x's field alx_blocks_tail, whose range is the same granule tail.
   - No fact is read out of AR's own conjuncts here: amem_range_near_block reads the law al_blocks, whose twin is
     alx_blocks.
   - The AR-free names of W_drain_cx.v are CITED, not copied: the pcs A_drain .. A_dr_epi, DR_SAVED, DR_SAVE_OFF,
     DR_SCAN_END, DCEIL, IMG_TOP, amem_range_of_in_app, amem_range_img, dinband, aentry_okx and its two lemmas, dcx
     and its projections, dHA dsp0 dSTR dPS dlive dFP dfin dtrc dcost ds0, dlater dbud danext dapush dlfut dsfut
     drfut dpfut, dctl dr_saved dr_frame, DLINK DSAME DHIST dW dvirt drlp dskp drlq dlrun dlno dloc dlH dlka dbound
     dline RSTART, dregs_top, dregs_line.
   - The cut predicates are W_drain_cx.v's texts (B's registers, frame slots and dinband conjuncts), with DMEM ->
     DMEM_x, LCORE / DLC -> LCORE_x / DLC_x, dbud -> dbud_x and the cut's Hp1; DBASE_x is DBASE (with its
     `dxSA cx mod 8 = 0`, dr_spec's premise on both images) and dr_spec_x's room premises.
   - The BRIDGES (Section br) take ARx := W_journal_x.ARi (cgif's AR, Hp ignored) and PST := []: dlit_at_x and dbud_x
     are W_drain_cx.v's there, and from `LX : AR_laws_x SEGS B ARi 0` the lemma twins amem_range_near_block_x and
     alloc_tail_x give W_drain_cx.v's amem_range_near_block and its ALLOC_TAIL hypothesis at AR.  The base, the cuts,
     the post and the epilogue's journal carry DRAIN_STK_x (W_contract_x.v, DRAIN_STK + 128, a Theorem Labs lane 2026-10-30;
     measured on image B as on A: the strndup interceptor's frame is 2032 + 128 bytes before its inner malloc) where
     W_drain_cx.v's carry DRAIN_STK, so they have no bridge to W_drain_cx.v; the AR walks keep their own proofs.
     (a Theorem Labs lane's A cut 7e440345053, mirrored.)
   - THE ROOM ROUND: the rules and the callee specs take the room parameter RP (W_journal_x.roomp, a Section variable
     after MT); the entry carries the budget kr of dr_spec_x (dPOST_x, DBASE_x, every cut predicate and every segment
     statement take it right after Hp); DBASE_x is dr_spec_x's premises (tr_peak, the room
     `rp_RM RP S (dr_cost MT_rk .. + kr)` and the count block at dr_pk); the cut predicates carry dbud_x:
     W_drain_cx.v's dbud, the room at the cut's state with MT_rk's count of the requests still owed on top of kr, and
     the live counts plus dr_pk's shape over those requests (their tr_peakP + 2).  The Section states the budget law
     RMM over RP.  The bridges take RP := RP_AR, where the room and the counts are trivially true.
   No statement difference is forced by ARx: no premise or conclusion is added or dropped, only Hp threaded (the stack
   width DRAIN_STK_x is a Theorem Labs lane's ruling for the strndup frame, not ARx's). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Setoid.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep gestures_end_b_c RelayModel RelayKeys.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require
send_line_c send_line_b_c RelayRunT RelayRunF ListTr drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_drain_model.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_rep W_journal W_sites W_contract W_frame W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Rt Require Import ConstsViewDef MemchrDef.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG FCiface.
(* the count names (tr_peakP, used by dbud_x): lib/B/ReplyCnt.v, before the kit so that the kit's names come last *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_drain_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR.
(* YGcallx.v's sep_blocks_pos_x, for sep_blocks_perm_x (Section t); Require without Import *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YGcallx.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* W_drain_cx.v:266, the plain model's trace type *)
#[local] Abbreviation dtrace := (list (RelayRunT.rev YO0i.sptr)).

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.

(* ---- W_drain_cx.v:320 ALLOC_TAIL over ARx, a theorem of the laws (AR_laws_x field alx_blocks_tail): the range
   p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 is the field's
   p + req_size n <= a < (p + req_size n + 7) / 8 * 8. ---- *)
Section t.
Variable segs : list Segment.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx hl.
Lemma alloc_tail_x : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview segs (w_H W) mem a <> None.
Proof.
intros ly S Hp W mem md p n a HAR Hin Ha.
apply (alx_blocks_tail _ _ _ LAWS ly S Hp W mem md p n a HAR Hin).
assert (E : (p + req_size n + 7) / 8 * 8 = p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8).
{ replace (p + req_size n + 7) with (p + req_size n - 1 + 1 * 8) by lia.
  rewrite Z.div_add by lia. pose proof (Z.div_mod (p + req_size n - 1) 8 ltac:(lia)). lia. }
rewrite E. lia.
Qed.
(* DR_x: YCbq.v:2584 sep_blocks_perm over ARx (the drain walks cite it over AR), W_relay_add.v:575
   ra_sep_blocks_perm_x's proof from YGcallx.v's sep_blocks_pos_x *)
Lemma sep_blocks_perm_x : forall ly S Hp W mem md x y l,
ARx ly S Hp W mem md -> Permutation (ablocks B ly S) (x :: y :: l) ->
zdisjoint (block_rng x) (block_rng y).
Proof.
intros ly S Hp W mem md x y l HAR HP.
assert (Hx : In x (ablocks B ly S)) by (eapply Permutation_in; [apply Permutation_sym; exact HP | left; reflexivity]).
apply in_split in Hx as (a1 & a2 & E1).
assert (HP2 : Permutation (a1 ++ a2) (y :: l)).
{ apply Permutation_sym. apply (@Permutation_cons_app_inv _ _ a1 a2 x). rewrite <- E1. apply Permutation_sym. exact HP. }
assert (Hy : In y (a1 ++ a2)) by (eapply Permutation_in; [apply Permutation_sym; exact HP2 | left; reflexivity]).
apply in_app_or in Hy as [Hy | Hy]; apply in_split in Hy as (b1 & b2 & E2).
- pose proof (YGcallx.sep_blocks_pos_x segs B ARx LAWS ly S Hp W mem md y x b1 b2 a2 HAR
    ltac:(rewrite E1, E2, <- app_assoc; reflexivity)) as Hd.
  unfold zdisjoint in *. lia.
- exact (YGcallx.sep_blocks_pos_x segs B ARx LAWS ly S Hp W mem md x y a1 b1 b2 HAR ltac:(rewrite E1, E2; reflexivity)).
Qed.
End t.

Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Abbreviation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Abbreviation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Abbreviation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
Context {hl : Z}.
(* the instance's laws *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
(* W_drain_cx.v:305-310, AR-free *)
Hypothesis HG : gx_ok SEGS B (G_DR B RG).
Hypothesis HGR : forall a, inG (G_DR B RG) a -> ~ in_rom SEGS a.
Hypothesis HROMO : rom_out SEGS B (G_DR B RG).
Hypothesis HGO : gx_ok SEGS B [(rg_client RG, 4); (rg_send_dead RG, 1); (rg_send_max RG, 8)].
Hypothesis MTL : ameter_laws MT.
Hypothesis TL : PALib B.
(* W_drain_cx.v:311-319, the runtime entries over ARx (W_sites_x.v's sites and its two runtime contracts,
   W_contract_x.v's astrlen_realizes_x) *)
Hypothesis AERRNO : aerrno_realizes_x B ARx (SIGMA WS_errno_location).
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
Hypothesis AMEMCHR : amemchr_realizesM_x SEGS B ARx 0x10350 0x10370 (SIGMA WS_memchr).
Hypothesis HCROM : forall a, 0x10350 <= a < 0x10370 -> in_rom SEGS a.
Hypothesis ASTRRCHR : astrrchr_realizes_x B ARx (SIGMA WS_strrchr).
Hypothesis ASTRNCMP : astrncmp_realizes_x B ARx (SIGMA WS_strncmp).
Hypothesis ASTRCMP : astrcmp_realizes_x B ARx (SIGMA WS_strcmp).
Hypothesis ASTRLEN : astrlen_realizes_x B ARx (SIGMA WS_strlen).
(* W_drain_cx.v:320 ALLOC_TAIL over ARx (Hp after S); alloc_tail_x proves it from LAWS *)
Hypothesis ALLOC_TAIL : forall ly S Hp W mem md p n a,
ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
(* W_drain_cx.v:324-325, the callees' specs over ARx (W_contract_x.v), at RP *)
Hypothesis SLSPEC : sl_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_send_line).
Hypothesis LPSPEC : lp_spec_g_x B PST ARx MT RP MMAX (BASE + AF_fr_list_push).
(* The room round's budget law in a callee-spec Section (RMM, budget monotonicity; at every instance
   RM ignores the budget, so the law is trivial there).  The walk needs it: MT_rk charges a malloc / strndup request of
   dr_cost 2 (mo_malloc + mo_free) where its rule consumes 1, and dr_post_x's `rp_RM RP S' kr` drops what is left. *)
Hypothesis RMM : forall S k k', (k' <= k)%nat -> rp_RM RP S k -> rp_RM RP S k'.
(* W_drain_cx.v:326-331, AR-free *)
Hypothesis HERRNO : as_errno B = as_tp B - 164.
Hypothesis HERRZ : azs B (as_errno B) 4.
Hypothesis HERRW : forall i, 0 <= i < 4 -> writable_at SEGS (fun _ => None) (as_errno B + i).
Hypothesis HERRAL : as_errno B mod 4 = 0.
Hypothesis HGSZ : azs B (rg_s RG) (4 * ASRC).
Hypothesis HVS : VAL (A_OBJ 19) = rg_s RG.
(* W_drain_cx.v:332 dlit_at, its shadow conjunct W_contract_x.v's ashp_x (A's W_drain_cx_x.v:172-176 text) *)
Definition dlit_at_x (i : nat) (l : list Z) : Prop :=
(forall k, (k < length l)%nat ->
   seg_rom SEGS (Z_to_bv 64 (VAL (A_OBJ i) + Z.of_nat k)) = option_map (Z_to_bv 8) (nth_error l k)) /\
(forall x, VAL (A_OBJ i) <= x < VAL (A_OBJ i) + Z.of_nat (length l) -> YG0d.in_rom SEGS x) /\
ashp_x ARx (VAL (A_OBJ i)) (Z.of_nat (length l)).
(* W_drain_cx.v:337-339, image B's literal objects A_OBJ 18 / 20 / 21 (A: 21 / 23 / 24) *)
Hypothesis HLIT5 : dlit_at_x 18 (K_GESTURE ++ [0]).
Hypothesis HLIT6 : dlit_at_x 20 (W_BEGIN ++ [0]).
Hypothesis HLIT7 : dlit_at_x 21 (W_END ++ [0]).
(* W_drain_cx.v:340-353, AR-free *)
Hypothesis HRGD : zpairwise_disjoint
[(VAL (A_OBJ 0), VAL (A_OBJ 0) + 8); (VAL (A_OBJ 30), VAL (A_OBJ 30) + 8);
 (rg_s RG, rg_s RG + 4 * ASRC);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_send_dead RG, rg_send_dead RG + 1);
 (rg_send_max RG, rg_send_max RG + 8); (rg_nout RG, rg_nout RG + 8);
 (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (as_errno B, as_errno B + 4);
 (VAL (A_OBJ 18), VAL (A_OBJ 18) + 14); (VAL (A_OBJ 20), VAL (A_OBJ 20) + 6); (VAL (A_OBJ 21), VAL (A_OBJ 21) + 4)].
Hypothesis HGSB : 0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0.
Hypothesis HMMAX : 0 < MMAX <= 2 ^ 30.
Hypothesis HV9 : VAL (A_OBJ 9) = rg_client RG.
Hypothesis HSD : 0x10000 <= rg_send_dead RG /\ rg_send_dead RG + 1 <= IMG_TOP.
Hypothesis HSM : 0x10000 <= rg_send_max RG /\ rg_send_max RG + 8 <= IMG_TOP.
(* W_drain_cx.v:354-362, the allocator's site rules over the generic journal (W_journal_x.v Section hc, the _c twins
   with the caller-context tables), at RP; the call-site facts at image B's own offsets *)
Variables CTX_R CTX_F CTX_S : list (list Z).
Hypothesis AREALLOC : arealloc_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_R (SIGMA WS_realloc).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_F.
Hypothesis ASTRNDUP : astrndup_cf_rule_c_x SEGS B PST ARx MT MMAX RP CTX_S (SIGMA WS_strndup).
Hypothesis HCTX_re1 : In [BASE + AF_fr_drain + 0x19c] CTX_R.
Hypothesis HCTX_re2 : In [BASE + AF_fr_drain + 0x974] CTX_R.
Hypothesis HCTX_fr2 : In [BASE + AF_fr_drain + 0xa58] CTX_F.
Hypothesis HCTX_sd : In [BASE + AF_fr_drain + 0x994] CTX_S.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.

(* W_drain_cx.v:370 amem_range_near_block, from the blocks law alx_blocks *)
Lemma amem_range_near_block_x : forall ly S Hp W mem md q n a,
ARx ly S Hp W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a <= q + req_size n -> amem_range a 8.
Proof.
intros ly S Hp W mem md q n a HAR Hin H1 H2.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md q n HAR Hin) as (_ & H4096 & Hceil & Hap & _).
pose proof (@ASAN_CEIL_range rc) as (Hc & _).
destruct Hap as (Ha0 & [HL | [HH1 HH2]]);
unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *;
[left; lia | right; lia].
Qed.


(* W_drain_cx.v:447 DBASE, with dr_spec_x's room premises at the entry's budget kr *)
Definition DBASE_x (cx : dcx) (Hp : list Z) (kr : nat) : Prop :=
afn_pre_x SEGS B ARx DRAIN_STK_x (dxly cx) (dxS cx) Hp (dxW cx) (dxregs cx) (dxmem cx) (dxmd cx) (dxch cx) /\
getr (dxregs cx) 10 = w64 (dxSA cx) /\
In (dxG cx, ATABLE) (ablocks B (dxly cx) (dxS cx)) /\
dxG cx <= dxSA cx /\ dxSA cx + AENT <= dxG cx + ATABLE /\
dxSA cx mod 8 = 0 /\
garr8 SEGS (arm (dxW cx) (dxmem cx)) (dxSA cx) (bzs (entry_bytes (dxe cx))) /\
awr (dxW cx) (dxmem cx) (dxSA cx) AENT /\
aentry_ok B (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxe cx) /\
(dxj cx < 4)%nat /\
asrc_at B (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dHA RG cx) (dxh cx) /\
aothers_at RG (dxW cx) (dxmem cx) (dxj cx) (re_fd (dxe cx)) /\
hs_fd (dxh cx) = re_fd (dxe cx) /\ re_skip (dxe cx) = hs_overlong (dxh cx) /\
(re_skip (dxe cx) = 0 -> bzs (re_U (dxe cx)) = bzs (hs_W (dxh cx))) /\
aout_at B RG (dxly cx) (dxS cx) (dxW cx) (dxmem cx) (dxc cx) (dxO cx) (dxmx cx) (dxno cx) (dxcap cx) (dxout cx) /\
rom_view SEGS (dxW cx) (dxmem cx) /\
Permutation (ablocks B (dxly cx) (dxS cx))
  ((dxG cx, ATABLE) :: aentry_blks (dxe cx) ++ asrc_blks (dxh cx) ++ aout_blks (dxcap cx) (dxout cx) ++ dxrest cx) /\
Z.of_nat (length (pending_stream (dxh cx))) < 2 ^ 26 /\
hl_cap (hs_expected (dxh cx)) < 2 ^ 26 /\
re_nheld (dxe cx) + Z.of_nat (length (pending_stream (dxh cx))) < 2 ^ 26 /\
tr_max (dtrc cx) < MMAX /\
blocks_bytes (dxS cx) + tr_peak (dtrc cx) <= LIVE_MAX /\
mo_ok MT (dxS cx) (dcost MT cx) /\
rp_RM RP (dxS cx) (Z.to_nat (dcost MT_rk cx) + kr) /\
cnt_ok_pk RP (dr_pk (dxc cx) (dxmx cx) (dxno cx) (dxcap cx) (dxe cx) (dxh cx)) (ablocks B (dxly cx) (dxS cx)).

(* W_drain_cx.v:481 dbud, with the room the requests still owed need (the trace specs' form of W_contract_x.v): the
   room invariant at the cut's allocator state with MT_rk's count of those requests on top of the entry's kr, and the
   live counts plus dr_pk's shape over those requests under the bounds: their own peak count tr_peakP plus 2, the
   largest premise constant of an inner callee (send_line's sl_pk, list_push's lp_peak <= 2; W_contract_x.v dr_pk).
   At the entry (tl = dtrc cx) it is DBASE_x's dr_pk premise, by conversion. *)
Definition dbud_x (cx : dcx) (kr : nat) (ly1 : alayout) (S1 : astate) (spent : Z) (tl : dtrace) : Prop :=
dbud MT MMAX cx S1 spent tl /\
rp_RM RP S1 (Z.to_nat (tr_cost MT_rk tl) + kr) /\
cnt_ok_pk RP (fun P => (Z.to_nat (tr_peakP P tl) + 2)%nat) (ablocks B ly1 S1).



(* ---- The eight cut predicates (W_drain_cx.v:669-854), the cut's ghost list Hp1 an existential after S1. ---- *)










(* ---- The segment statements (W_drain_cx.v:856-929), over the entry's ghost list Hp and budget kr. ---- *)











(* ---- The compositions (W_drain_cx.v:931-955). ---- *)






(* ==== route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) section 0; wave-2 commit (1) form): the R twins of this section's carrier.  Each
   X_xR is X_x with ajournal_gx_x -> ajournal_gx_xR .. R, SRr SEGS -> SRrG SEGS R, dr_post_x -> dr_post_xR .. R,
   dr_spec_x -> dr_spec_xR .. R and each twinned carrier name -> its R twin; the strict text is untouched.
   DBASE_x and dbud_x name no journal and no step relation, so they have no twin (the twins use them). ==== *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.

(* R twin of dPOST_x *)
Definition dPOST_xR (cx : dcx) (Hp : list Z) (kr : nat) : world SEGS -> config -> Prop :=
dr_post_xR B PST ARx R MT RP RG (dxregs cx) (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx)
  (dxSA cx) (dHA RG cx) (dxe cx) (dxh cx) (dxc cx) (dxO cx) (dxmx cx) (dxno cx) (dxcap cx) (dxout cx) kr.

(* R twin of DMEM_x *)
Definition DMEM_xR (cx : dcx) (Hp : list Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) (e1 : rentry) (h1 : hsrc) (s1 : drain_b_c.dstate) (out1 ev1 : Z)
(sent : list (list Z)) (LB1 : list byte) : Prop :=
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 /\
rom_view SEGS W1 m1 /\ apres_kept B (dxW cx) (dxmem cx) W1 m1 /\ frames S1 = frames (dxS cx) /\
dr_frame RG cx W1 m1 /\
garr8 SEGS (arm W1 m1) (dxSA cx) (bzs (entry_bytes e1)) /\ awr W1 m1 (dxSA cx) AENT /\
aentry_okx B ly1 S1 W1 m1 e1 /\
asrc_at B ly1 S1 W1 m1 (dHA RG cx) h1 /\
aothers_at RG W1 m1 (dxj cx) (re_fd (dxe cx)) /\
(forall x, rg_s RG <= x < rg_s RG + 4 * ASRC -> ~ (dHA RG cx <= x < dHA RG cx + ASRC) ->
   abyte_kept (dxW cx) (dxmem cx) W1 m1 x) /\
aout_at B RG ly1 S1 W1 m1 (dctl cx (Z.of_nat (length (with_nul sent))) ev1)
  (if dlive cx then dxO cx ++ LB1 else dxO cx) (dxmx cx)
  (if dlive cx then drain_b_c.ds_no s1 else dxno cx) (drain_b_c.ds_ocap s1) out1 /\
(dlive cx = false -> out1 = dxout cx /\ drain_b_c.ds_ocap s1 = dxcap cx) /\
Permutation (ablocks B ly1 S1)
  ((dxG cx, ATABLE) :: aentry_blks e1 ++ asrc_blks h1 ++ aout_blks (drain_b_c.ds_ocap s1) out1 ++ dxrest cx).

(* R twin of LCORE_x *)
Definition LCORE_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (sent kl : list (list Z))
(H : list (list Z)) (ka no oc nk : Z) (sk : bool)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
let sv := dvirt cx s1 sk H ka no oc in
DMEM_xR cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 sv out1 ev1 sent LB1 /\
DLINK sv e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx sv (D ++ ddata s1) (D ++ ddata s1) sent kl h1 LB1 nk /\
RSTART cx s1 D /\ dbud_x cx kr ly1 S1 spent tl.

(* ---- The eight cut predicates (W_drain_cx.v:669-854), the cut's ghost list Hp1 an existential after S1. ---- *)

(* R twin of DI_x *)
Definition DI_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config)
: Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_top) regs1 m1 md1 /\
dregs_top RG cx regs1 /\
DMEM_xR cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
(re_cap e1 <> 0 -> dinband (re_buf e1) (re_cap e1)) /\
DLINK s1 e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) /\
dlater cx s1 jb a tl /\ dbud_x cx kr ly1 S1 spent tl.

(* R twin of DEND_x *)
Definition DEND_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_end) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 21 = w64 (dxSA cx) /\ getr regs1 23 = w64 (dHA RG cx) /\
getr regs1 19 = w64 (SHADOW_OFF + 12 * Z.of_nat (dxj cx)) /\
dr_frame RG cx W1 m1 /\
DMEM_xR cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
DLINK s1 e1 h1 /\ DSAME cx e1 h1 /\
DHIST cx s1 D D (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
J1 (drain_b_c.ds_u s1) (drain_b_c.ds_skip s1) (drain_b_c.ds_ref s1) /\
drain_b_c.ds_pend s1 = [] /\ drain_b_c.ds_eintr s1 = false /\ 4096 <= drain_b_c.ds_cap s1 - ulen s1 /\
dlater cx s1 jb a tl /\ dbud_x cx kr ly1 S1 spent tl.

(* R twin of DRB_x *)
Definition DRB_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (W1 : world SEGS)
(c1 : config)
: Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a v rs tl p0 r0 rs0,
c1 = cfg_at SEGS (BASE + A_dr_feed) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 8 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 18 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 23 = w64 (dHA RG cx) /\
getr regs1 15 = w64 (dnum s1) /\ getr regs1 21 = w64 (dnum s1 - Z.of_nat k) /\
getr regs1 27 = w64 p0 /\ getr regs1 19 = w64 (p0 + Z.of_nat k) /\ getr regs1 24 = w64 (p0 + Z.of_nat k) /\
getr regs1 6 = w64 (fst r0) /\ getr regs1 20 = w64 1 /\
getr regs1 16 = w64 (shadow_addr (dHA RG cx + 40)) /\ getr regs1 17 = w64 (shadow_addr (dHA RG cx + 48)) /\
getr regs1 22 = w64 (shadow_addr (dHA RG cx + 56)) /\
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 24) 8 (dHA RG cx + 56) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 (dHA RG cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 160) 8 (dHA RG cx + 64) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (shadow_addr (dHA RG cx + 16)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 168) 8 (shadow_addr (dHA RG cx + 32)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (dnum s1) /\
hl_recs (hs_pending h1) = r0 :: rs0 /\ p0 = fst r0 + drain_b_c.ds_off s1 /\
dinband (fst r0) (Z.of_nat (length (snd r0)) + 1) /\ fst r0 <= p0 /\
(Z.of_nat k < dnum s1)%Z /\ 0 < dnum s1 /\
bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
DMEM_xR cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DSAME cx e1 h1 /\
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (firstn k (ddata s1)) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1)))) /\
hl_cap (hs_expected h1) =
  pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (lines (drain_b_c.ds_ref s1) (firstn k (ddata s1))) /\
DHIST cx s1 D (D ++ firstn k (ddata s1)) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
RSTART cx s1 D /\
dpfut cx s1 k jb a v rs tl /\ dbud_x cx kr ly1 S1 spent tl.

(* R twin of DE_x *)
Definition DE_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a tl,
c1 = cfg_at SEGS (BASE + A_dr_fed) regs1 m1 md1 /\
spZ regs1 = dsp0 cx - DRAIN_FRAME /\
getr regs1 3 = getr (dxregs cx) 3 /\ getr regs1 4 = getr (dxregs cx) 4 /\
getr regs1 8 = w64 (rg_s RG) /\ getr regs1 9 = w64 (rg_s RG / 8) /\
getr regs1 18 = w64 ((rg_s RG + 4) / 8) /\ getr regs1 23 = w64 (dHA RG cx) /\
getr regs1 15 = w64 (dnum s1) /\
dr_frame RG cx W1 m1 /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 96) 8 (dHA RG cx + 16) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 112) 8 (shadow_addr (dHA RG cx + 16)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 168) 8 (shadow_addr (dHA RG cx + 32)) /\
val_mem SEGS (arm W1 m1) (dsp0 cx - DRAIN_FRAME + 192) 8 (dnum s1) /\
0 < dnum s1 /\ bzs (firstn (Z.to_nat (dnum s1)) (re_junk e1)) = ddata s1 /\
DMEM_xR cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 (lines (dSTR cx) D) LB1 /\
~ In (Z_to_bv 8 0) (re_U e1) /\ re_used e1 <= APARTIAL /\
dinband (re_buf e1) (re_cap e1) /\
DSAME cx e1 h1 /\
re_cap e1 = drain_b_c.ds_cap s1 /\ bzs (re_U e1) = drain_b_c.ds_u s1 /\
re_skip e1 = (if drain_b_c.ds_skip s1 then 1 else 0) /\
drain_b_c.keys_texts (re_keys e1) = drain_b_c.ds_H s1 /\ drain_b_c.ent_ka e1 = drain_b_c.ds_ka s1 /\
hs_eintr h1 = 0 /\
map (fun r => bzs (snd r)) (hl_recs (hs_pending h1)) = drain_b_c.ds_pend s1 /\
hs_off h1 = drain_b_c.ds_off s1 /\
hs_state h1 = feed (drain_b_c.ds_ref s1) (ddata s1) /\
hl_n (hs_expected h1) = drain_b_c.ds_en s1 + Z.of_nat (length (dref s1)) /\
hl_cap (hs_expected h1) = pcapm (drain_b_c.ds_en s1) (drain_b_c.ds_ecap s1) (dref s1) /\
DHIST cx s1 D (D ++ ddata s1) (lines (dSTR cx) D) (lines (dSTR cx) D) h1 LB1 0 /\
RSTART cx s1 D /\
drfut cx s1 jb a tl /\ dbud_x cx kr ly1 S1 spent tl.

(* R twin of DLC_x *)
Definition DLC_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE_xR cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p) (dlno s1 p) (dloc cx s1 p) (Z.of_nat (length (drlq s1 p))) (dskp s1 p)
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.

(* R twin of DLL_x *)
Definition DLL_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_line) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 26 = w64 DR_SCAN_END /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 (re_buf e1) /\
getr regs1 25 = w64 (Z.of_nat (length (dW s1) - p)) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
DLC_xR cx Hp kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

(* R twin of DLN_x *)
Definition DLN_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p : nat)
(W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_next) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat p - 1) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\ (0 < p)%nat /\
DLC_xR cx Hp kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

(* R twin of DLR_x *)
Definition DLR_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p : nat)
(W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl,
c1 = cfg_at SEGS (BASE + A_dr_rest) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 26 = w64 DR_SCAN_END /\
getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 25 = w64 (Z.of_nat (length (dW s1) - p)) /\
getr regs1 19 = w64 (re_buf e1) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
dbound s1 p /\ (forall i, (p <= i)%nat -> nth_error (dW s1) i <> Some 0) /\
DLC_xR cx Hp kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dlfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlno s1 p) (dloc cx s1 p) (dlH cx s1 p) (dlka cx s1 p)
  (drlq s1 p) jb o ha ks tl.

(* R twin of DGS_x *)
Definition DGS_xR (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS)
(c1 : config) : Prop :=
exists regs1 ly1 S1 Hp1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent jb a o ha ks tl (kd : gkind) (jj : nat) (bg : Z),
c1 = cfg_at SEGS (BASE + A_dr_seen) regs1 m1 md1 /\
dregs_line RG cx regs1 W1 m1 /\
getr regs1 23 = w64 (re_buf e1 + Z.of_nat q) /\ getr regs1 24 = w64 (re_buf e1 + Z.of_nat p) /\
getr regs1 19 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj) /\
getr regs1 26 = w64 (re_buf e1 + Z.of_nat p + Z.of_nat jj + 1) /\
getr regs1 25 = w64 bg /\
0 <= bg < 2 ^ 64 /\ (bg = 0 <-> kd = GBegin) /\
dinband (re_buf e1) (re_cap e1) /\ 0 < re_cap e1 /\
gesture (dline s1 p q) = Some (kd, firstn jj (dline s1 p q)) /\ (13 < jj < q - p)%nat /\
dbound s1 p /\ (p <= q < length (dW s1))%nat /\ nth_error (dW s1) q = Some 0 /\
(forall i, (p <= i < q)%nat -> nth_error (dW s1) i <> Some 0) /\
dskp s1 p = false /\ (q - p <= LINE_LIMIT)%nat /\
LCORE_xR cx Hp kr s1 D (lines (dSTR cx) D ++ drlp s1 p ++ [dline s1 p q]) (lines (dSTR cx) D ++ drlp s1 p)
  (dlH cx s1 p) (dlka cx s1 p)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (Z.of_nat (S (length (drlq s1 (S q))))) false
  ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl /\
dsfut cx (dnext (dlive cx) (dxmx cx) s1) a (dlH cx s1 p) (dlka cx s1 p) (dline s1 p q)
  (dlno s1 p + Z.of_nat (length (dline s1 p q)) + 1)
  (send_line_b_c.send_line_cap (dlive cx) (dxmx cx) (dlno s1 p) (dloc cx s1 p)
     (Z.of_nat (length (dline s1 p q)) + 1))
  (drlq s1 (S q)) jb o ha ks tl.

(* ---- The segment statements (W_drain_cx.v:856-929), over the entry's ghost list Hp and budget kr. ---- *)

(* R twin of dr_pro_stmt_x *)
Definition dr_pro_stmt_xR : Prop :=
forall cx Hp kr,
DBASE_x cx Hp kr ->
(forall W2 c2, DI_xR cx Hp kr (ds0 cx) [] W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R (dxW cx) (cfg_at SEGS A_drainP (dxregs cx) (dxmem cx) (dxmd cx)) (dPOST_xR cx Hp kr).

(* R twin of dr_top_stmt_x *)
Definition dr_top_stmt_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASE_x cx Hp kr -> DI_xR cx Hp kr s1 D W1 c1 ->
(drain_b_c.ds_eintr s1 = true -> forall W2 c2, DI_xR cx Hp kr (dclr (dgrow s1)) D W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
(forall W2 c2, DEND_xR cx Hp kr (dgrow s1) D W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
(forall W2 c2, DRB_xR cx Hp kr (dgrow s1) D 0 W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_feed_stmt_x *)
Definition dr_feed_stmt_xR : Prop :=
forall cx Hp kr s1 D k W1 c1,
DBASE_x cx Hp kr -> DRB_xR cx Hp kr s1 D k W1 c1 ->
(forall W2 c2, DRB_xR cx Hp kr s1 D (S k) W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
(forall W2 c2, DE_xR cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_drop_stmt_x *)
Definition dr_drop_stmt_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASE_x cx Hp kr -> DE_xR cx Hp kr s1 D W1 c1 ->
(forall q W2 c2, DLL_xR cx Hp kr s1 D 0 q W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
(forall W2 c2, DLR_xR cx Hp kr s1 D 0 W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_linea_stmt_x *)
Definition dr_linea_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x cx Hp kr -> DLL_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR cx Hp kr s1 D (S q) W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
(forall W2 c2, DGS_xR cx Hp kr s1 D p q W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_gs_stmt_x *)
Definition dr_gs_stmt_xR : Prop :=
forall cx Hp kr s1 D p q W1 c1,
DBASE_x cx Hp kr -> DGS_xR cx Hp kr s1 D p q W1 c1 ->
(forall W2 c2, DLN_xR cx Hp kr s1 D (S q) W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_next_stmt_x *)
Definition dr_next_stmt_xR : Prop :=
forall cx Hp kr s1 D p W1 c1,
DBASE_x cx Hp kr -> DLN_xR cx Hp kr s1 D p W1 c1 ->
(forall q W2 c2, DLL_xR cx Hp kr s1 D p q W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
(forall W2 c2, DLR_xR cx Hp kr s1 D p W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_rest_stmt_x *)
Definition dr_rest_stmt_xR : Prop :=
forall cx Hp kr s1 D p W1 c1,
DBASE_x cx Hp kr -> DLR_xR cx Hp kr s1 D p W1 c1 ->
(forall W2 c2, DI_xR cx Hp kr (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_epi_stmt_x *)
Definition dr_epi_stmt_xR : Prop :=
forall cx Hp ly1 S1 Hp1 W1 m1 md1 k1 regs1 (Q : world SEGS -> config -> Prop),
@ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
  (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m1 md1 k1 ->
spZ regs1 = dsp0 cx - DRAIN_FRAME ->
getr regs1 3 = getr (dxregs cx) 3 -> getr regs1 4 = getr (dxregs cx) 4 ->
YK0s.ret_ok (getr (dxregs cx) 1) ->
dr_saved W1 m1 (dsp0 cx - DRAIN_FRAME) (dxregs cx) ->
(forall regs' m' md', aregs_preserved (dxregs cx) regs' ->
   (forall x, arm W1 m' x = arm W1 m1 x) ->
   @ajournal_gx_xR _ SK SEGS B PST ARx R (G_DR B RG) 0 [] DRAIN_STK_x (dsp0 cx) (dFP cx)
     (dxly cx) (dxS cx) Hp (dxW cx) (dxmem cx) (dxmd cx) [] ly1 S1 Hp1 W1 m' md' k1 ->
   Q W1 (mkCfg (mkst regs' (getr (dxregs cx) 1) m' (seg_rom SEGS)) md')) ->
SRrG SEGS R W1 (cfg_at SEGS (BASE + A_dr_epi) regs1 m1 md1) Q.

(* R twin of dr_end_concl_x *)
Definition dr_end_concl_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASE_x cx Hp kr -> DEND_xR cx Hp kr s1 D W1 c1 ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_end_stmt_x *)
Definition dr_end_stmt_xR : Prop := dr_epi_stmt_xR -> dr_end_concl_xR.

(* ---- The compositions (W_drain_cx.v:931-955). ---- *)

(* R twin of dr_feeds_concl_x *)
Definition dr_feeds_concl_xR : Prop :=
forall cx Hp kr s1 D k W1 c1,
DBASE_x cx Hp kr -> DRB_xR cx Hp kr s1 D k W1 c1 ->
(forall W2 c2, DE_xR cx Hp kr s1 D W2 c2 -> SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_feeds_stmt_x *)
Definition dr_feeds_stmt_xR : Prop := dr_feed_stmt_xR -> dr_feeds_concl_xR.

(* R twin of dr_lines_concl_x *)
Definition dr_lines_concl_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASE_x cx Hp kr ->
((exists p q, DLL_xR cx Hp kr s1 D p q W1 c1) \/ (exists p, DLN_xR cx Hp kr s1 D p W1 c1) \/
 (exists p, DLR_xR cx Hp kr s1 D p W1 c1)) ->
(forall W2 c2, DI_xR cx Hp kr (dnext (dlive cx) (dxmx cx) s1) (D ++ ddata s1) W2 c2 ->
   SRrG SEGS R W2 c2 (dPOST_xR cx Hp kr)) ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_lines_stmt_x *)
Definition dr_lines_stmt_xR : Prop :=
dr_linea_stmt_xR -> dr_gs_stmt_xR -> dr_next_stmt_xR -> dr_rest_stmt_xR -> dr_lines_concl_xR.

(* R twin of dr_outer_concl_x *)
Definition dr_outer_concl_xR : Prop :=
forall cx Hp kr s1 D W1 c1,
DBASE_x cx Hp kr -> DI_xR cx Hp kr s1 D W1 c1 ->
SRrG SEGS R W1 c1 (dPOST_xR cx Hp kr).

(* R twin of dr_outer_stmt_x *)
Definition dr_outer_stmt_xR : Prop :=
dr_top_stmt_xR -> dr_feeds_concl_xR -> dr_drop_stmt_xR -> dr_lines_concl_xR -> dr_end_concl_xR -> dr_outer_concl_xR.

(* R twin of dr_all_stmt_x *)
Definition dr_all_stmt_xR : Prop :=
dr_pro_stmt_xR -> dr_outer_concl_xR -> dr_spec_xR B PST ARx R MT RP MMAX RG A_drainP.

End wR.
(* ---- The entry context: W_drain_cx.v's dcx, with the entry's ghost list Hp beside it. ---- *)
(* W_drain_cx.v:443 dPOST, at the entry's budget kr *)
Definition dPOST_x (cx : dcx) (Hp : list Z) (kr : nat) : world SEGS -> config -> Prop :=
dPOST_xR (@wle SEGS) cx Hp kr.
(* ---- The memory core of every cut (W_drain_cx.v:566 DMEM), the cut's ghost list Hp1 after S1. ---- *)
Definition DMEM_x (cx : dcx) (Hp : list Z) (ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS)
(m1 : word -> option byte) (md1 : Model) (k1 : Z) (e1 : rentry) (h1 : hsrc) (s1 : drain_b_c.dstate) (out1 ev1 : Z)
(sent : list (list Z)) (LB1 : list byte) : Prop :=
DMEM_xR (@wle SEGS) cx Hp ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 s1 out1 ev1 sent LB1.
(* W_drain_cx.v:650 LCORE *)
Definition LCORE_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (sent kl : list (list Z))
(H : list (list Z)) (ka no oc nk : Z) (sk : bool)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
LCORE_xR (@wle SEGS) cx Hp kr s1 D sent kl H ka no oc nk sk ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
(* W_drain_cx.v:669 DI *)
Definition DI_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS) (c1 : config)
: Prop :=
DI_xR (@wle SEGS) cx Hp kr s1 D W1 c1.
(* W_drain_cx.v:681 DEND *)
Definition DEND_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
DEND_xR (@wle SEGS) cx Hp kr s1 D W1 c1.
(* W_drain_cx.v:697 DRB *)
Definition DRB_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (k : nat) (W1 : world SEGS)
(c1 : config)
: Prop :=
DRB_xR (@wle SEGS) cx Hp kr s1 D k W1 c1.
(* W_drain_cx.v:738 DE *)
Definition DE_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (W1 : world SEGS)
(c1 : config) : Prop :=
DE_xR (@wle SEGS) cx Hp kr s1 D W1 c1.
(* W_drain_cx.v:778 DLC *)
Definition DLC_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p : nat)
(ly1 : alayout) (S1 : astate) (Hp1 : list Z) (W1 : world SEGS) (m1 : word -> option byte) (md1 : Model) (k1 : Z)
(e1 : rentry) (h1 : hsrc) (out1 ev1 : Z) (LB1 : list byte) (spent : Z) (tl : dtrace) : Prop :=
DLC_xR (@wle SEGS) cx Hp kr s1 D p ly1 S1 Hp1 W1 m1 md1 k1 e1 h1 out1 ev1 LB1 spent tl.
(* W_drain_cx.v:785 DLL *)
Definition DLL_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS)
(c1 : config) : Prop :=
DLL_xR (@wle SEGS) cx Hp kr s1 D p q W1 c1.
(* W_drain_cx.v:801 DLN *)
Definition DLN_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p : nat)
(W1 : world SEGS)
(c1 : config) : Prop :=
DLN_xR (@wle SEGS) cx Hp kr s1 D p W1 c1.
(* W_drain_cx.v:813 DLR *)
Definition DLR_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p : nat)
(W1 : world SEGS)
(c1 : config) : Prop :=
DLR_xR (@wle SEGS) cx Hp kr s1 D p W1 c1.
(* W_drain_cx.v:828 DGS *)
Definition DGS_x (cx : dcx) (Hp : list Z) (kr : nat) (s1 : drain_b_c.dstate) (D : list Z) (p q : nat)
(W1 : world SEGS)
(c1 : config) : Prop :=
DGS_xR (@wle SEGS) cx Hp kr s1 D p q W1 c1.
(* W_drain_cx.v:856 dr_pro_stmt *)
Definition dr_pro_stmt_x : Prop :=
dr_pro_stmt_xR (@wle SEGS).
(* W_drain_cx.v:862 dr_top_stmt *)
Definition dr_top_stmt_x : Prop :=
dr_top_stmt_xR (@wle SEGS).
(* W_drain_cx.v:870 dr_feed_stmt *)
Definition dr_feed_stmt_x : Prop :=
dr_feed_stmt_xR (@wle SEGS).
(* W_drain_cx.v:877 dr_drop_stmt *)
Definition dr_drop_stmt_x : Prop :=
dr_drop_stmt_xR (@wle SEGS).
(* W_drain_cx.v:884 dr_linea_stmt *)
Definition dr_linea_stmt_x : Prop :=
dr_linea_stmt_xR (@wle SEGS).
(* W_drain_cx.v:891 dr_gs_stmt *)
Definition dr_gs_stmt_x : Prop :=
dr_gs_stmt_xR (@wle SEGS).
(* W_drain_cx.v:897 dr_next_stmt *)
Definition dr_next_stmt_x : Prop :=
dr_next_stmt_xR (@wle SEGS).
(* W_drain_cx.v:904 dr_rest_stmt *)
Definition dr_rest_stmt_x : Prop :=
dr_rest_stmt_xR (@wle SEGS).
(* W_drain_cx.v:910 dr_epi_stmt: the journal at the entry's Hp and the epilogue's Hp1, which it keeps *)
Definition dr_epi_stmt_x : Prop :=
dr_epi_stmt_xR (@wle SEGS).
(* W_drain_cx.v:925 dr_end_concl, :929 dr_end_stmt *)
Definition dr_end_concl_x : Prop :=
dr_end_concl_xR (@wle SEGS).
Definition dr_end_stmt_x : Prop :=
dr_end_stmt_xR (@wle SEGS).
(* W_drain_cx.v:931 dr_feeds_concl, :936 dr_feeds_stmt *)
Definition dr_feeds_concl_x : Prop :=
dr_feeds_concl_xR (@wle SEGS).
Definition dr_feeds_stmt_x : Prop :=
dr_feeds_stmt_xR (@wle SEGS).
(* W_drain_cx.v:938 dr_lines_concl, :944 dr_lines_stmt *)
Definition dr_lines_concl_x : Prop :=
dr_lines_concl_xR (@wle SEGS).
Definition dr_lines_stmt_x : Prop :=
dr_lines_stmt_xR (@wle SEGS).
(* W_drain_cx.v:947 dr_outer_concl, :951 dr_outer_stmt *)
Definition dr_outer_concl_x : Prop :=
dr_outer_concl_xR (@wle SEGS).
Definition dr_outer_stmt_x : Prop :=
dr_outer_stmt_xR (@wle SEGS).
(* W_drain_cx.v:954 dr_all_stmt: the prologue and the outer loop's conclusion give W_contract_x.v's dr_spec_x *)
Definition dr_all_stmt_x : Prop :=
dr_all_stmt_xR (@wle SEGS).

End c.
End b.
End a.

(* THE BRIDGES. At ARx := W_journal_x.ARi (cgif's AR, Hp ignored), PST := [] and RP := RP_AR (W_journal_x.v: no room,
   no count): the definitions of this file that name no stack width are W_drain_cx.v's (dlit_at_x, dbud_x), and from
   the laws at that instance (LX) the lemma twins give W_drain_cx.v's statements.  (DRAIN_STK_x, a Theorem Labs lane
   2026-10-30: the generic base, cuts, post and epilogue journal carry DRAIN_STK + 128 where W_drain_cx.v's carry
   DRAIN_STK, so their bridges to W_drain_cx.v and the statement bridges built on them, here and in the former Section
   br0, no longer hold and are gone; the AR walks keep their own proofs.) *)
Section br.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Context {PI : PAImg fr_prog_listing}.
#[local] Abbreviation SEGS := (@pa_segs _ fr_prog_listing PI).
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable RG : rep_globals.
#[local] Abbreviation ARI := (ARi SEGS B).

Lemma dlit_at_x_AR : forall i l, dlit_at_x ARI i l <-> dlit_at B i l.
Proof. intros i l. unfold dlit_at_x, dlit_at. rewrite ashp_x_AR. reflexivity. Qed.
(* dbud_x is dbud at RP_AR *)
Lemma dbud_x_AR : forall cx kr ly1 S1 spent tl,
dbud_x B MT RP_AR MMAX cx kr ly1 S1 spent tl <-> dbud MT MMAX cx S1 spent tl.
Proof.
intros cx kr ly1 S1 spent tl. unfold dbud_x. split; [intros (H & _); exact H|].
intros H. split; [exact H|]. split; [exact (rp_RM_AR _ _)|].
apply cnt_ok_pk_AR. cbv beta. rewrite tr_peakP_false. cbn. lia.
Qed.

(* the lemma twins at that instance give W_drain_cx.v's statements *)
Hypothesis LX : AR_laws_x SEGS B ARI 0.
(* W_drain_cx.v:320 ALLOC_TAIL, the hypothesis, at AR *)
Lemma alloc_tail_AR : forall ly S W mem md p n a,
AR SEGS B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p + req_size n - 1 < a < p + req_size n - 1 - (p + req_size n - 1) mod 8 + 8 ->
aview SEGS (w_H W) mem a <> None.
Proof. intros ly S W mem md p n a. exact (alloc_tail_x SEGS B ARI LX ly S [] W mem md p n a). Qed.
(* W_drain_cx.v:370 amem_range_near_block, with its HGSB premise *)
Lemma amem_range_near_block_AR :
0x10000 <= rg_s RG /\ rg_s RG + 4 * ASRC <= IMG_TOP /\ rg_s RG mod 8 = 0 ->
forall ly S W mem md q n a,
AR SEGS B ly S W mem md -> In (q, n) (ablocks B ly S) -> q <= a -> a <= q + req_size n -> amem_range a 8.
Proof.
intros HGSB ly S W mem md q n a. exact (amem_range_near_block_x B ARI RG LX HGSB ly S [] W mem md q n a).
Qed.
End br.
