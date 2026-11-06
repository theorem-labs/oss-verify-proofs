(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YC1f.v for libreac/fuzz_boxreg's program walk (as fuzz_identity's lib/A/Prog/IdentPaLib.v, ea5560a967b, carries it): module paths changed; the names are bsym's (the wrappers' free and malloc entries are BS___interceptor_trampoline_free and BS___interceptor_trampoline_malloc); the shadow GOT slot is object 1 (0x98eb8) and the shadow cell object 12 (0xa0f78) of BoxAddr.v; blk_off_imgP states fuzz_boxreg.asan's image range as Reusable/YImgTop.v's [IMG_LO, IMG_TOP) in place of cgif's off_img. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_boxreg/lib/A/Prog/BoxPaLib.v, with its module paths and module names changed; 370 of its 404 lines of code are new or changed and 459 lines of the source are left out. *)
(* fuzz_preset, image A' (the #102 asan image, pinned 1be0f53d96cb9d6c, unstripped twin bff8519bbe3ea0e4): the walk
   of check_reject_clean (merged fuzz_preset.c:538-555, signature unchanged) against the tcheck_reject_clean_specX
   (lib/A/PRH_FnCheck.v:537, blob 9ecd8eb167c6 = the kit of record f97c8b2f046b's; the text block is byte-identical
   to decff67d721f's PRH_FnCheck.v:479, blob 4cb899514e6c, which this walk was first proved against at 6ed04b809892).
   rule 24: proves function check_reject_clean (ported: h-hpreset-7's Wcheck_reject_clean.v,
   origin/cold/h-hpreset-7-walk-s9-got-rob 9a0674f0b5f2, old pin 0x82060; no #102 copy exists).
   The #102 body (A' 0x82110 = Crc102Syms.A102_check_reject_clean, 20 instructions, frame 16; listing
   h-hreply-s5-rf's check_reject_clean.fuzz_preset.asan102.s) is the donor's
   instruction for instruction, moved by +0xb0; only the pc-relative fields differ. Its arms; every abort arm is the
   shared tail at pi_abort F_check_reject_clean = 0x82158 (`jal __asan_handle_no_return`, then `jal abort`):
     0x8211c `beqz a0`              the 64-bit a0 (rc, an int, sign-extended) is 0                 -> abort
     0x82138 `jal bcmp (a1, &empty, 56)` then 0x8213c `bnez a0`
                                    the 56 bytes at doc differ from the read-only static `empty`     -> abort
     0x82140 `jal fuzz_alloc_live` then 0x82144 `bne a0, s0` (s0 = live_before, kept across the call)
                                    the live byte count differs from live_before                     -> abort
     else 0x82148-0x82154: reload ra / s0, return.
   The text's premises rc <> 0, doc's 56 bytes zero, live_before = lsum Lam are the negations of the three tests, in
   the bytes' order, so each abort arm is refuted and the walk returns with nothing changed but its frame.
   WHAT THE #102 KIT CHANGED against the donor's text, and how the walk meets it:
   - fpre has a fourth conjunct, raZ regs < YM05.alloc_ceiling: read at entry, and given to fuzz_alloc_live from the
     jal's own return site (Crc102Syms.RA102_check_reject_clean_1); and (kit f97c8b2f046b, FRM0-ENTRY) a fifth,
     frm_zero of the entry float state: the walk runs no float instruction, so fuzz_alloc_live is entered at the
     caller's own float state and gets the caller's conjunct unchanged;
   - the post is fpostm (PRH_Base.v fQmn): the memory stays normal. The runs carry it by YGcallMxmn.v's
     memnorm_frame_of (Crc102Kit.v c102_run), the bcmp call by the m-form row abcmp_realizes_xm (aj_bcmp_at_xm),
     the fuzz_alloc_live call by its own m-form text;
   - prh_ledger has thirteen arguments (most / own): threaded, and kept below the ceiling (c102_ledger_keep);
   - the post states S' = S: fuzz_alloc_live's text gives it.
   Generic over the listing instance PA (image facts: Crc102Kit.v's c102_img, discharged at PI_prog_A in
   Crc102InstA.v) and over ARx (AR_laws_x). Callees as Section hypotheses: the bcmp row abcmp_realizes_xm
   (Reusable/YGcallMxmn.v:280) at the wrapper, and the tfuzz_alloc_live_specX (PRH_FnAlloc.v:137).
   Numerals: 16 / 56 / 8208 (LENGTH: frame, struct pj, frame + 2 * ESTACK), 2 ^ 31 / 2 ^ 47 / 2 ^ 64 (LENGTH: bounds),
   2147450880 (DERIVED: SHADOW_OFF, in the shadow-index bounds), 32 / 48 (DERIVED: the symbolic engine's atom counts
   at the two calls). Every ADDRESS is Crc102Syms.v's (generated). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG YCbqGcall.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import FCiface YGcallMx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YP0b YPsym YC4aP YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YAkMemnorm YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v PRH_Base PRH_Img PRH_FnAlloc PRH_FnCheck.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PresetRodata.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import Crc102Syms Crc102Kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---- the live harness bytes are below YM05.alloc_ceiling (Wcheck_reject_clean.v :59-100, unchanged): Lam's allocator
   blocks are distinct, pairwise disjoint and lie in [4096, YM05.alloc_ceiling) (YCbqG's blocks law), so their sizes sum
   to less than YM05.alloc_ceiling. check_reject_clean keeps live_before in s0 across its call of fuzz_alloc_live, and
   the callee's entry chain (afn_pre_x's achain) needs that value below YM05.alloc_ceiling (achain_low). ---- *)
Definition c102_bl (c : Z) (ak : Z * Z) : Z * Z := (fst ak - c, req_size (snd ak + c)).
Fixpoint c102_ssum (l : list (Z * Z)) : Z := match l with [] => 0 | x :: r => snd x + c102_ssum r end.
Lemma c102_ssum_filter : forall (f : Z * Z -> bool) l,
  c102_ssum l = c102_ssum (List.filter f l) + c102_ssum (List.filter (fun x => negb (f x)) l).
Proof.
intros f l. induction l as [|x r IH]; [reflexivity|]. cbn [List.filter c102_ssum].
destruct (f x); cbn [negb c102_ssum]; lia.
Qed.
(* disjoint intervals inside [lo, hi) have total length at most hi - lo *)
Lemma c102_disjoint_sum : forall (n : nat) (l : list (Z * Z)) lo hi, (length l <= n)%nat ->
  (forall x, In x l -> lo <= fst x /\ fst x + snd x <= hi /\ 0 <= snd x) ->
  (forall x y, In x l -> In y l -> x <> y -> zdisjoint x y) -> List.NoDup l -> lo <= hi ->
  c102_ssum l <= hi - lo.
Proof.
induction n as [|n IH]; intros l lo hi Hn Hin Hd Hnd Hlh.
- destruct l; [cbn; lia | cbn in Hn; lia].
- destruct l as [|x r]; [cbn; lia|]. cbn [c102_ssum].
  apply List.NoDup_cons_iff in Hnd as [Hx Hnd].
  destruct (Hin x (or_introl eq_refl)) as (Hx1 & Hx2 & Hx3).
  rewrite (c102_ssum_filter (fun y => fst y + snd y <=? fst x) r).
  assert (Hl : c102_ssum (List.filter (fun y => fst y + snd y <=? fst x) r) <= fst x - lo).
  { apply IH; [cbn in Hn; pose proof (List.filter_length_le (fun y => fst y + snd y <=? fst x) r); lia | | | | lia].
    - intros y Hy. apply List.filter_In in Hy as [Hy Hy']. apply Z.leb_le in Hy'.
      destruct (Hin y (or_intror Hy)) as (Hy1 & Hy2 & Hy3). lia.
    - intros y z Hy Hz Hyz. apply List.filter_In in Hy as [Hy _]. apply List.filter_In in Hz as [Hz _].
      exact (Hd y z (or_intror Hy) (or_intror Hz) Hyz).
    - apply List.NoDup_filter. exact Hnd. }
  assert (Hr : c102_ssum (List.filter (fun y => negb (fst y + snd y <=? fst x)) r) <= hi - (fst x + snd x)).
  { apply IH; [cbn in Hn; pose proof (List.filter_length_le (fun y => negb (fst y + snd y <=? fst x)) r); lia | | | | lia].
    - intros y Hy. apply List.filter_In in Hy as [Hy Hy']. apply negb_true_iff, Z.leb_gt in Hy'.
      destruct (Hin y (or_intror Hy)) as (Hy1 & Hy2 & Hy3).
      assert (Hne : x <> y) by (intros <-; exact (Hx Hy)).
      destruct (Hd x y (or_introl eq_refl) (or_intror Hy) Hne) as [H|H]; lia.
    - intros y z Hy Hz Hyz. apply List.filter_In in Hy as [Hy _]. apply List.filter_In in Hz as [Hz _].
      exact (Hd y z (or_intror Hy) (or_intror Hz) Hyz).
    - apply List.NoDup_filter. exact Hnd. }
  lia.
Qed.

(* a zero-shadow range of whole granules is addressable byte by byte *)
Lemma c102_ra_of_zs : forall (rd : Z -> option Z) a n, a mod 8 = 0 -> 0 <= n ->
  zero_shadow rd SHADOW_OFF a n -> n mod 8 = 0 -> range_addressable rd SHADOW_OFF a n.
Proof.
intros rd a n Ha Hn Hz Hn8 x Hx. exists 0. split; [|left; reflexivity].
assert (Ea : a = 8 * (a / 8)) by (pose proof (Z.div_mod a 8 ltac:(lia)); lia).
assert (En : n = 8 * (n / 8)) by (pose proof (Z.div_mod n 8 ltac:(lia)); lia).
assert (Hd : x / 8 = a / 8 + (x - a) / 8).
{ assert (Hx' : x = (a / 8) * 8 + (x - a)) by lia. rewrite Hx' at 1. rewrite Z.div_add_l by lia. reflexivity. }
unfold shadow_of_addr. rewrite Hd, Z.add_assoc. apply Hz. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

Section W. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {cp : CfParams}.
Context {L : ptable asym} {PA : PAImg L}.
Context {RL : PrhRoomLive}.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world pa_segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
(* the allocator's laws (YCbqG.v AR_laws_x; at ARcf /\ xs_placed_cf, YGcallcf.v AR_laws_x_xs of h-mani-a8's
   YG0lawscf.v AR_laws_ok_cf) *)
Hypothesis LAWS : AR_laws_x pa_segs B ARx cf_head.
(* the image facts (Crc102Kit.v; PROVED at PI_prog_A by Crc102InstA.v c102_img_A) *)
Hypothesis IMG : c102_img PA.
(* CALLEE: the bcmp row with the memnorm keep (Reusable/YGcallMxmn.v:265 abcmp_realizes_xm) at the listing's
   __wrap_bcmp; owner: the bcmp realizer's lane, c-libc-stdio (its po_memcmp_cf row with the nested bcmp row,
   Reusable/YGcallCmp.v:3-6) *)
Hypothesis BCMP : YGcallMxmn.abcmp_realizes_xm pa_segs B ARx (pa_sigma AS___wrap_bcmp).
(* CALLEE: K0's text of fuzz_alloc_live (PRH_FnAlloc.v:71; its A' walk is h-w6rep-2's relocation) *)
Hypothesis LIVE : tfuzz_alloc_live_specX (PI := prh_img_A) B ARx SK.
(* `static const struct pj empty` (A' 0x20fc0, 56 bytes; the Check part's C-RO): asyms facts of the image, each PROVED at
   image A's asyms TfibB in Crc102InstA.v (over the generated AF0m.v tables): one whole range of as_zero_shadow, no
   runtime-owned static, not errno; and its shadow hull is mapped in every allocator state (Crc102InstA.v, from
   a Theorem Labs lane's tfib_img_shadow_vis_cf under ARx -> ARcf) *)
Hypothesis EMPTY_ZS : In (A102_crc_empty, 56) (as_zero_shadow B).
Hypothesis EMPTY_B : forall i, 0 <= i < 56 ->
  ~ Exists (in_zr (A102_crc_empty + i)) (as_owned_static B) /\ ~ (as_errno B <= A102_crc_empty + i < as_errno B + 4).
Hypothesis EMPTY_HULL : forall ly S Hp (W : world pa_segs) mem md, ARx ly S Hp W mem md ->
  shadow_hull_vis (aview pa_segs (w_H W) mem) A102_crc_empty 56.
Let HSL : forall a, in_img pa_segs a -> 0 <= a < kLowMemEnd := pa_segs_low.
Let HWX : wx_segs_nowrap pa_segs := pa_wx.

Lemma c102_lsum_below : forall ly S Hp W mem md Lam peak cnt fail ran most own,
  ARx ly S Hp W mem md -> prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own ->
  Ledger.lsum Lam < YM05.alloc_ceiling.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own HAR HL.
pose proof (prh_ledger_nodup (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as HN.
pose proof (prh_ledger_blocks (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL) as HF.
clear HL.
pose proof asan_consts as (C1 & _). pose proof (@cf_head_nonneg cp) as Hc0.
assert (HFl : forall a k, In (a, k) Lam -> 0 <= k /\ In (a - cf_head, k + cf_head) (ablocks B ly S)).
{ intros a k Hin. pose proof (proj1 (Forall_forall _ _) HF (a, k) Hin) as (Hk & Hb & _). cbn [fst snd] in *. auto. }
assert (Hreq : forall z, 0 <= z -> z <= req_size z /\ 1 <= req_size z) by (intros z Hz; unfold req_size; destruct (Z.eqb_spec z 0); lia).
assert (Hs : Ledger.lsum Lam <= c102_ssum (map (c102_bl cf_head) Lam)).
{ clear HN HF. induction Lam as [|[a k] r IH]; [cbn; lia|]. cbn [Ledger.lsum map c102_ssum].
  destruct (HFl a k (or_introl eq_refl)) as [Hk _]. cbn [c102_bl fst snd].
  assert (Hkc : 0 <= k + cf_head) by lia.
  pose proof (Hreq (k + cf_head) Hkc) as [R1 _].
  assert (IH' : Ledger.lsum r <= c102_ssum (map (c102_bl cf_head) r)) by (apply IH; intros a' k' H'; apply HFl; right; exact H'). lia. }
assert (Hb : c102_ssum (map (c102_bl cf_head) Lam) <= YM05.alloc_ceiling - 4096).
{ apply (c102_disjoint_sum (length (map (c102_bl cf_head) Lam))); [lia | | | | lia].
  - intros x Hx. apply in_map_iff in Hx as ([a k] & <- & Hin). destruct (HFl a k Hin) as [Hk Hblk].
    destruct (alx_blocks pa_segs B ARx LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & H4096 & Hcl & _).
    assert (Hkc : 0 <= k + cf_head) by lia. pose proof (Hreq (k + cf_head) Hkc) as [_ R2]. cbn [c102_bl fst snd]. lia.
  - intros x y Hx Hy Hxy. apply in_map_iff in Hx as ([a k] & <- & Hin). apply in_map_iff in Hy as ([a' k'] & <- & Hin').
    destruct (HFl a k Hin) as [_ Hb1]. destruct (HFl a' k' Hin') as [_ Hb2]. cbn [c102_bl fst snd].
    eapply (sep_blocks_x pa_segs B ARx LAWS ly S Hp W mem md); [exact HAR | exact Hb1 | exact Hb2 |].
    intros E. injection E as E1 E2. apply Hxy. assert (Ea : a = a') by lia. assert (Ek : k = k') by lia. subst a' k'. reflexivity.
  - apply NoDup_ListNoDup in HN. clear -HN.
    induction Lam as [|[a k] r IH]; cbn [map]; [constructor|]. cbn [map fst] in HN.
    apply List.NoDup_cons_iff in HN as [Hn HN]. constructor; [|exact (IH HN)].
    intros Hin. apply in_map_iff in Hin as ([a' k'] & E & Hin'). cbn [c102_bl fst snd] in E. injection E as E1 _.
    apply Hn. apply in_map_iff. exists (a', k'). split; [cbn; lia | exact Hin']. }
lia.
Qed.

(* shadow facts read below YM05.alloc_ceiling survive memory that agrees below it *)
Lemma c102_ra_below : forall (rd rd' : reader), (forall a, 0 <= a < YM05.alloc_ceiling -> rd' a = rd a) ->
  forall x n, 0 <= x -> x + n <= 2 ^ 47 ->
  range_addressable rd SHADOW_OFF x n -> range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' Hrd x n Hx Hxn Hra y Hy. destruct (Hra y Hy) as (s & Hs & Hok). exists s. split; [|exact Hok].
pose proof asan_consts as (C1 & _). rewrite Hrd; [exact Hs|]. unfold shadow_of_addr, SHADOW_OFF.
pose proof (Z.div_pos y 8 ltac:(lia) ltac:(lia)). assert (y / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia). lia.
Qed.
Lemma c102_hull_below : forall (rd rd' : reader), (forall a, 0 <= a < YM05.alloc_ceiling -> rd' a = rd a) ->
  forall x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' Hrd x n Hx Hn Hxn Hh s Hs. pose proof asan_consts as (C1 & _). rewrite Hrd; [exact (Hh s Hs)|].
unfold shadow_addr, SHADOW_OFF in Hs.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert ((x + n - 1) / 8 <= 2 ^ 44) by (apply Z.div_le_upper_bound; lia).
assert ((2147450880 + (x + n - 1) / 8) / 8 <= 2 ^ 42) by (apply Z.div_le_upper_bound; lia).
pose proof (Z.div_pos (2147450880 + x / 8) 8 ltac:(lia) ltac:(lia)). lia.
Qed.
Lemma c102_aview_below : forall (W : world pa_segs) (m m' : word -> option byte),
  (forall a, 0 <= a < YM05.alloc_ceiling -> mbyte pa_segs (mrestrict (w_H W) m') a = mbyte pa_segs (mrestrict (w_H W) m) a) ->
  forall a, 0 <= a < YM05.alloc_ceiling -> aview pa_segs (w_H W) m' a = aview pa_segs (w_H W) m a.
Proof. intros W m m' H a Ha. unfold aview. rewrite (H a Ha). reflexivity. Qed.

Lemma c102_lsum_nonneg : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own -> 0 <= Ledger.lsum Lam.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own HL.
exact (proj1 (proj1 (prh_ledger_bounds (PI := prh_img_A) B ly S Hp W mem Lam peak cnt fail ran most own HL))).
Qed.

Theorem check_reject_clean_holds102 : tcheck_reject_clean_specX (PI := prh_img_A) B ARx SK.
Proof.
intros ly S Hp W regs mem md ch rcv doc live Lam peak cnt fail ran most own [HPRE [HRO [HSH [HRAe HFRM]]]]
  H10 Hrc Hrc0 H11 Hdoc H12 Hlive HL.
pose proof (ci_crc _ IMG) as TBL.
pose proof BCMP as BCMP'. rewrite (ci_e_bcmp _ IMG) in BCMP'.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof (c102_sp _ _ _ _ _ _ _ _ _ _ _ _ HPRE) as (Hal16 & Hceil & H47 & HS0).
pose proof asan_consts as (C1 & _).
assert (FS : STK_check_reject_clean (PI := prh_img_A) = 16 + 2 * ESTACK) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (Hceil' : YM05.alloc_ceiling + 8208 <= spZ regs) by (rewrite FS, HES in Hceil; lia).
pose proof (c102_entry pa_segs B ARx _ 16 ly S Hp W regs mem md ch A102_check_reject_clean HPRE
  ltac:(rewrite FS; unfold ESTACK; lia) ltac:(vm_compute; reflexivity)) as HS.
pose proof (ajournal_x_init (SK := SK) pa_segs B (prh_pst (PI := prh_img_A)) ARx _ [] ly S Hp W regs mem md ch HPRE) as HJ.
set (E := Ereg regs []) in HS.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (subst E; rewrite (ew_Ereg_nat regs [] 2 2%bv eq_refl); reflexivity).
assert (Ereg_at : forall (n : nat) (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn; subst E; exact (ew_Ereg_nat regs [] n r Hn)).
pose proof Hdoc as (Hdb & Hd4096 & Hdc & Hdam & Hdra & Hdhv).
cbn [length repeat] in Hdc, Hdam, Hdra, Hdhv. change (Z.of_nat 56) with 56 in Hdc, Hdam, Hdra, Hdhv.
unfold cfg_at. rewrite (ci_e_crc _ IMG). change (w64 A102_check_reject_clean) with (Z_to_bv 64 A102_check_reject_clean).
unfold fpostm, fpost.
(* the memnorm keep, threaded from entry: Hmn : memnorm mem -> memnorm (the current memory) *)
assert (Hmn : YAkMemnorm.memnorm pa_segs mem -> YAkMemnorm.memnorm pa_segs mem) by (exact (fun H => H)).
c102_run TBL HS HJ Hmn.
{ awr_ok_tac. exact Usp. }
(* ---- 0x8211c beqz a0: rc = 0 is the first abort ---- *)
c102_branch tbl_crc102 HS.
{ intros Hc HS. exfalso. rewrite branch_eq_U, U_SLit in Hc. change (zcanon 0) with 0 in Hc. apply Z.eqb_eq in Hc.
  rewrite U_SOff, (Ereg_at 10%nat 10%bv eq_refl), H10, Z.add_0_r in Hc. unfold w64 in Hc.
  rewrite Z_to_bv_unsigned in Hc. unfold zcanon, M64, bv_wrap in Hc. change (bv_modulus 64) with (2 ^ 64) in Hc.
  rewrite Zmod_mod in Hc. apply Z.mod_divide in Hc; [|lia]. destruct Hc as [q Hq]. lia. }
intros Hc HS.
c102_run TBL HS HJ Hmn.
{ awr_ok_tac. exact Usp. }
(* ---- 0x82138 jal bcmp (doc, &empty, 56): the bcmp interceptor reads both windows ---- *)
assert (WB : forall rs, (forall r, In r rs -> YP09.r_base r = Some 2%nat /\ -16 <= YP09.r_wlo r /\ YP09.r_whi r <= 0) ->
  forall a, in_wrange E rs a -> YM05.alloc_ceiling <= a).
{ intros rs Hrs a (r & Hin & Ha). destruct (Hrs r Hin) as (Hb & Hw1 & Hw2). rewrite Hb in Ha. cbn [base_val] in Ha.
  rewrite Usp in Ha. rewrite FS in Hceil. unfold ESTACK in Hceil. lia. }
assert (HB0 : forall a, 0 <= a < YM05.alloc_ceiling -> mbyte pa_segs (mrestrict (w_H W) (ms_mem ms0)) a = mbyte pa_segs (mrestrict (w_H W) mem) a).
{ intros a Ha.
  match goal with H : frame_of _ ?rs2 (mrestrict _ (ms_mem ?m1)) (mrestrict _ (ms_mem ms0)) |- _ =>
    rewrite (c102_frame_below pa_segs E rs2 (w_H W) (ms_mem m1) (ms_mem ms0) H) by
      (first [exact Ha | apply WB; intros r Hin; cbn in Hin; destruct Hin as [<-|[]]; cbn; split; [reflexivity|lia]]) end.
  match goal with H : frame_of _ ?rs1 (mrestrict _ mem) (mrestrict _ (ms_mem ?m1)) |- _ =>
    exact (c102_frame_below pa_segs E rs1 (w_H W) mem (ms_mem m1) H
      ltac:(apply WB; intros r Hin; cbn in Hin; destruct Hin as [<-|[]]; cbn; split; [reflexivity|lia]) a Ha) end. }
pose proof (c102_aview_below W mem (ms_mem ms0) HB0) as AV0.
assert (Ddoc : forall i, 0 <= i < 56 -> aview pa_segs (w_H W) mem (doc + i) = Some 0).
{ intros i Hi. destruct (Hdb (Z.to_nat i) ltac:(rewrite repeat_length; lia)) as [Hv _].
  rewrite nth_repeat in Hv. specialize (Hv 0%nat ltac:(lia)). rewrite Z2Nat.id in Hv by lia. rewrite Z.add_0_r in Hv.
  unfold aview. rewrite Hv. reflexivity. }
assert (Demp : forall i, 0 <= i < 56 -> aview pa_segs (w_H W) mem (A102_crc_empty + i) = Some 0).
{ intros i Hi. destruct (ci_empty _ IMG i Hi) as [Hro Hrom]. destruct (EMPTY_B i Hi) as [Ho He].
  rewrite (HRO _ Hro Ho He), Hrom. reflexivity. }
assert (Hshape : ms0 = mkst (ms_regs ms0) (Z_to_bv 64 A102_wrap_bcmp) (ms_mem ms0) (seg_rom pa_segs))
  by exact (st_ok_restrict_mkst pa_segs (w_H W) E _ ms0 HS eq_refl).
rreg HS (10%bv : bv 5) R10. rreg HS (11%bv : bv 5) R11. rreg HS (12%bv : bv 5) R12. rreg HS (1%bv : bv 5) R1.
rreg HS (2%bv : bv 5) R2. rreg HS (3%bv : bv 5) R3. rreg HS (4%bv : bv 5) R4.
assert (E10 : getr (ms_regs ms0) 10 = w64 doc) by (rewrite R10, (Ereg_at 11%nat 11%bv eq_refl); exact H11).
assert (E11 : getr (ms_regs ms0) 11 = w64 A102_crc_empty) by (rewrite R11; reflexivity).
assert (E12 : getr (ms_regs ms0) 12 = w64 56) by (rewrite R12; reflexivity).
assert (E1 : getr (ms_regs ms0) 1 = Z_to_bv 64 RA102_check_reject_clean_0) by (rewrite R1; reflexivity).
assert (Esp : spZ (ms_regs ms0) = spZ regs + -16).
{ unfold spZ. rewrite R2, Usp. assert (Hc' : YM05.alloc_ceiling + 16 + 8192 <= spZ regs) by (rewrite FS in Hceil; unfold ESTACK in Hceil; lia).
  rewrite unsigned_lit_small by lia. reflexivity. }
assert (E3 : getr (ms_regs ms0) 3 = w64 (as_gp B)) by (rewrite R3, (Ereg_at 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : getr (ms_regs ms0) 4 = w64 (as_tp B)) by (rewrite R4, (Ereg_at 4%nat 4%bv eq_refl); exact Htp).
pose proof HJ as (HARc & _).
pose proof (EMPTY_HULL _ _ _ _ _ _ HARc) as Ehv.
pose proof (alx_zshadow pa_segs B ARx LAWS _ _ _ _ _ _ (A102_crc_empty, 56) HARc
  ltac:(unfold zero_shadow_ranges; right; exact EMPTY_ZS)) as Hz0.
pose proof (c102_ra_of_zs _ A102_crc_empty 56 ltac:(unfold A102_crc_empty; reflexivity) ltac:(lia) Hz0 eq_refl) as Era.
rewrite Hshape at 1.
assert (Pbud : 2 * ESTACK - -16 <= STK_check_reject_clean (PI := prh_img_A)) by (rewrite FS, HES; lia).
assert (Praw : YK0s.ret_ok (Z_to_bv 64 RA102_check_reject_clean_0)).
{ apply ret_ok_even. rewrite unsigned_lit_small by (unfold RA102_check_reject_clean_0; lia). reflexivity. }
assert (Psx : src_ok pa_segs W (ms_regs ms0) (ms_mem ms0) doc 56).
{ intros a Ha. rewrite AV0 by lia. rewrite Esp. split; [|rewrite HES; lia].
  replace a with (doc + (a - doc)) by lia. rewrite Ddoc by lia. discriminate. }
assert (Psy : src_ok pa_segs W (ms_regs ms0) (ms_mem ms0) A102_crc_empty 56).
{ intros a Ha. assert (0 <= a < YM05.alloc_ceiling) by (unfold A102_crc_empty in *; lia). rewrite AV0 by lia. rewrite Esp.
  split; [|rewrite HES; unfold A102_crc_empty in *; lia].
  replace a with (A102_crc_empty + (a - A102_crc_empty)) by lia. rewrite Demp by lia. discriminate. }
assert (Pwx : forall a, doc <= a < doc + 56 -> ~ (spZ regs + -16 - 2 * ESTACK <= a < spZ regs + -16)) by (intros a Ha; rewrite HES; lia).
assert (Pwy : forall a, A102_crc_empty <= a < A102_crc_empty + 56 -> ~ (spZ regs + -16 - 2 * ESTACK <= a < spZ regs + -16))
  by (intros a Ha; rewrite HES; unfold A102_crc_empty in *; lia).
assert (Pamy : amem_range A102_crc_empty 56) by (unfold amem_range, A102_crc_empty, kLowMemEnd; lia).
assert (Prax : range_addressable (aview pa_segs (w_H W) (ms_mem ms0)) SHADOW_OFF doc 56)
  by (apply (c102_ra_below _ _ AV0); [lia | lia | exact Hdra]).
assert (Phx : 0 < 56 -> shadow_hull_vis (aview pa_segs (w_H W) (ms_mem ms0)) doc 56)
  by (intros _; apply (c102_hull_below _ _ AV0); [lia | lia | lia | exact (Hdhv ltac:(lia))]).
eapply SRr_bind.
{ exact (YGcallMxmn.aj_bcmp_at_xm (SK := SK) pa_segs B (prh_pst (PI := prh_img_A)) ARx LAWS HSL A102_wrap_bcmp BCMP'
    W (ms_regs ms0) (ms_mem ms0)
    _ (spZ regs) [] ly S Hp W mem md [] ly S Hp _ 0 doc A102_crc_empty 56 (-16) (Z_to_bv 64 RA102_check_reject_clean_0) HJ
    E10 E11 E12 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold A102_crc_empty; lia) ltac:(unfold A102_crc_empty; lia)
    Esp eq_refl ltac:(lia) Pbud E3 E4 E1 Praw Psx Psy Pwx Pwy Hdam Pamy Prax Phx Era (fun _ => Ehv)). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP2 & Hv & Hcmp & Hfr2 & Hpres2 & HMN2).
assert (Hv0 : v = w64 0).
{ apply Hcmp. intros i Hi. rewrite !AV0 by (unfold A102_crc_empty; lia). rewrite Ddoc, Demp by lia. reflexivity. }
(* the memnorm keep across the call: the row's keep after the run's *)
pose proof (fun H => HMN2 (Hmn H)) as Hmn2. clear Hmn. rename Hmn2 into Hmn.
(* ---- back at 0x8213c: the symbolic state resumes (st_ok_after_call: the caller-saved registers are fresh atoms,
   the frame region is kept: bcmp writes only its own window below sp - 16) ---- *)
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresJ2 & _).
lazymatch type of HS with st_ok _ _ ?ss _ =>
  assert (HKR : Forall (region_kept pa_segs E (ms_mem (restrict (w_H W) ms0)) (mrestrict (w_H W) mem2)) (ss_mem ss)) end.
{ cbn [ss_mem restrict ms_mem]. constructor; [|constructor]. split.
  - intros a Ha. cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi] in Ha. rewrite Usp in Ha.
    apply mbyte_of_aview. apply Hfr2; [lia|]. rewrite HES. lia.
  - intros a Ha _. cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Ha. rewrite Usp in Ha.
    apply apresent_writable. apply HpresJ2. rewrite FS, HES. lia. }
lazymatch type of HS with st_ok _ _ ?ss _ =>
  pose proof (st_ok_after_call pa_segs 32 E ss (restrict (w_H W) ms0) regs2 (mrestrict (w_H W) mem2) (ss_mem ss)
    RA102_check_reject_clean_0 HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP2 r Hr)) HKR) as HS2;
  let ss2 := eval vm_compute in (ss_after_call ss (ss_mem ss) 32 RA102_check_reject_clean_0) in
  change (ss_after_call ss (ss_mem ss) 32 RA102_check_reject_clean_0) with ss2 in HS2 end.
change (mkst regs2 (Z_to_bv 64 RA102_check_reject_clean_0) (mrestrict (w_H W) mem2) (seg_rom pa_segs)) with
  (restrict (w_H W) (mkst regs2 (Z_to_bv 64 RA102_check_reject_clean_0) mem2 (seg_rom pa_segs))) in HS2.
clear HS HKR.
assert (Usp2 : bv_unsigned (ew (havoc E 32 (map (getr regs2) CLOB)) 2) = spZ regs) by (rewrite ew_havoc_old by lia; exact Usp).
c102_run TBL HS2 HJ2 Hmn.
{ awr_ok_tac. exact Usp2. }
set (EE := havoc E 32 (map (getr regs2) CLOB)) in *.
assert (HB1 : forall a, 0 <= a < YM05.alloc_ceiling -> mbyte pa_segs (mrestrict (w_H W) (ms_mem ms1)) a = mbyte pa_segs (mrestrict (w_H W) mem) a).
{ intros a Ha. rewrite <- (HB0 a Ha).
  match goal with H : frame_of _ ?rs3 (mrestrict _ mem2) (mrestrict _ (ms_mem ms1)) |- _ =>
    rewrite (c102_frame_below pa_segs EE rs3 (w_H W) mem2 (ms_mem ms1) H) by
      (first [exact Ha | intros x (r & Hin & Hx); cbn in Hin; destruct Hin as [<-|[]];
        cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite Usp2 in Hx; lia]) end.
  apply mbyte_of_aview. apply Hfr2; [lia|]. rewrite HES. lia. }
(* ---- 0x8213c bnez a0: a doc not all zero is the second abort ---- *)
assert (U36 : U EE (SOff 36 0) = 0).
{ rewrite U_SOff. change (ew EE 36) with (getr regs2 10). rewrite Hv, Hv0. reflexivity. }
c102_branch tbl_crc102 HS2.
{ intros Hc2 HS2. exfalso. rewrite branch_ne_U, U36, U_SLit in Hc2. discriminate Hc2. }
intros Hc2 HS2.
c102_run TBL HS2 HJ2 Hmn.
{ awr_ok_tac. exact Usp2. }
(* ---- 0x82140 jal fuzz_alloc_live, through its text (aj_call_x) ---- *)
assert (HB2 : forall a, 0 <= a < YM05.alloc_ceiling -> mbyte pa_segs (mrestrict (w_H W) (ms_mem ms2)) a = mbyte pa_segs (mrestrict (w_H W) mem) a).
{ intros a Ha. rewrite <- (HB1 a Ha).
  match goal with H : frame_of _ ?rs4 (mrestrict _ (ms_mem ms1)) (mrestrict _ (ms_mem ms2)) |- _ =>
    exact (c102_frame_below pa_segs EE rs4 (w_H W) (ms_mem ms1) (ms_mem ms2) H
      ltac:(intros x (r & Hin & Hx); cbn in Hin; destruct Hin as [<-|[]];
        cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite Usp2 in Hx; lia) a Ha) end. }
pose proof (c102_aview_below W mem (ms_mem ms2) HB2) as AV2.
assert (HROc : arodata_okP pa_segs pa_relro_lo pa_relro_hi B (aview pa_segs (w_H W) (ms_mem ms2))).
{ intros a Hro Ho He. assert (Hi : in_img pa_segs a)
    by (destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (pa_relro_img a Hr)]).
  pose proof (HSL a Hi) as Hlo. unfold kLowMemEnd in Hlo. rewrite AV2 by lia. exact (HRO a Hro Ho He). }
assert (HLc : prh_ledger (PI := prh_img_A) B ly S Hp W (ms_mem ms2) Lam peak cnt fail ran most own)
  by exact (c102_ledger_keep B ARx LAWS ly S Hp W mem md (ms_mem ms2) Lam peak cnt fail ran most own HAR HL HB2).
pose proof (c102_lsum_below ly S Hp W mem md Lam peak cnt fail ran most own HAR HL) as Hlt.
pose proof (c102_lsum_nonneg _ _ _ _ _ _ _ _ _ _ _ _ HL) as Hl0.
rreg HS2 (1%bv : bv 5) Q1. rreg HS2 (2%bv : bv 5) Q2. rreg HS2 (3%bv : bv 5) Q3. rreg HS2 (4%bv : bv 5) Q4. rreg HS2 (8%bv : bv 5) Q8.
assert (Rsp : getr (ms_regs ms2) 2 = sv_denot EE (SOff 2 (-16))).
{ apply bv_eq. rewrite Q2, denot_SOff, Usp2. rewrite unsigned_lit_small by lia. symmetry. apply zcanon_id. unfold M64. lia. }
assert (Rgp : getr (ms_regs ms2) 3 = w64 (as_gp B)).
{ rewrite Q3. subst EE. rewrite ew_havoc_old by lia. rewrite (Ereg_at 3%nat 3%bv eq_refl). exact Hgp. }
assert (Rtp : getr (ms_regs ms2) 4 = w64 (as_tp B)).
{ rewrite Q4. subst EE. rewrite ew_havoc_old by lia. rewrite (Ereg_at 4%nat 4%bv eq_refl). exact Htp. }
assert (Rs0 : getr (ms_regs ms2) 8 = w64 live).
{ rewrite Q8. subst EE. rewrite ew_havoc_old by lia. rewrite (Ereg_at 12%nat 12%bv eq_refl). exact H12. }
assert (Ra1 : getr (ms_regs ms2) 1 = Z_to_bv 64 RA102_check_reject_clean_1) by (rewrite Q1; reflexivity).
assert (Praw1 : YK0s.ret_ok (Z_to_bv 64 RA102_check_reject_clean_1)).
{ apply ret_ok_even. rewrite unsigned_lit_small by (unfold RA102_check_reject_clean_1; lia). reflexivity. }
assert (Hach : achain ly (aview pa_segs (w_H W) (ms_mem ms2)) (spZ regs + -16) (s0Z (ms_regs ms2)) []).
{ apply achain_low. unfold s0Z. rewrite Rs0. unfold w64. rewrite unsigned_lit_small by lia. lia. }
(* the callee's sp is 16 below ours: the kit pre's stack-top conjunct (PRH_Base fpre) for fuzz_alloc_live *)
assert (HSHc : spZ (ms_regs ms2) + 64 <= ly_stk_hi ly).
{ assert (E16 : spZ (ms_regs ms2) = spZ regs + -16).
  { unfold spZ at 1. rewrite Rsp, denot_SOff, Usp2. unfold zcanon, M64. apply Z.mod_small. lia. }
  rewrite E16. lia. }
(* the callee's return address is the jal's return site, below the ceiling: the kit pre's fourth conjunct *)
assert (HRAc : raZ (ms_regs ms2) < YM05.alloc_ceiling).
{ unfold raZ. rewrite Ra1. rewrite unsigned_lit_small by (unfold RA102_check_reject_clean_1; lia).
  unfold RA102_check_reject_clean_1. lia. }
lazymatch type of HS2 with st_ok _ _ ?ss3 _ =>
eapply SRr_bind;
[ apply (aj_call_x (SK := SK) pa_segs B (prh_pst (PI := prh_img_A)) ARx LAWS HSL W EE ss3 ms2 _ (spZ regs) [] ly S Hp W mem md [] ly S Hp _ 0
    (STK_fuzz_alloc_live (PI := prh_img_A)) [] (-16) (ew EE 2) (Z_to_bv 64 RA102_check_reject_clean_1) []
    (fun ly' S' Hp' W' regs' mem' md' =>
       ((room_live_cf S -> room_live_cf S') /\ getr regs' 10 = w64 (Ledger.lsum Lam) /\ Hp' = Hp /\ S' = S /\
        ablocks B ly' S' = ablocks B ly S /\ prh_ledger (PI := prh_img_A) B ly' S' Hp' W' mem' Lam peak cnt fail ran most own) /\
       (YAkMemnorm.memnorm pa_segs (ms_mem ms2) -> YAkMemnorm.memnorm pa_segs mem'))
    HS2 eq_refl HJ2
    Rsp eq_refl Usp2 eq_refl ltac:(lia) ltac:(cbn; lia) ltac:(cbn; rewrite FS, HES; lia) Rgp Rtp Ra1 Praw1
    ltac:(rewrite unsigned_lit_small by (unfold RA102_check_reject_clean_1; lia); unfold RA102_check_reject_clean_1; lia) Hach);
  [ intros HPc;
    pose proof (LIVE ly S Hp W (ms_regs ms2) (ms_mem ms2) _ [] Lam peak cnt fail ran most own
      (conj HPc (conj HROc (conj HSHc (conj HRAc HFRM)))) HLc) as HLV;
    unfold cfg_at, fpostm, fpost, fQmn in HLV; rewrite (ci_e_live _ IMG) in HLV; exact HLV
  | intros a Ha; exfalso; exact (inFP_nil a Ha) ]
| ] end.
cbv beta. intros W3 c3 Hle3 (ly2 & S2 & Hp2 & regs3 & mem3 & md3 & k1 & -> & HJ3 & HJ1 & HP3 &
  ((Hrk & Hres & EHp & ES2 & Ebl & HL3) & HMN3)).
pose proof (fun H => HMN3 (Hmn H)) as Hmn3. clear Hmn. rename Hmn3 into Hmn.
(* ---- back at 0x82144: the frame region is kept by the callee's journal inside the caller's (region_kept_stack_sub_x) ---- *)
lazymatch type of HS2 with st_ok _ _ ?ss3 _ =>
  assert (HKR3 : Forall (region_kept pa_segs EE (ms_mem (restrict (w_H W) ms2)) (mrestrict (w_H W3) mem3)) (ss_mem ss3)) end.
{ cbn [ss_mem restrict ms_mem]. constructor; [|constructor].
  eapply (region_kept_stack_sub_x (SK := SK) pa_segs B (prh_pst (PI := prh_img_A)) ARx EE _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k1 2%nat
    (-16) 0 (-16) 0 _ (spZ regs) _ _ _ _ _ _ _ _ _ _ _ HJ1 HJ3 Usp2); lia. }
lazymatch type of HS2 with st_ok _ _ ?ss3 _ =>
  pose proof (st_ok_after_call pa_segs 48 EE ss3 (restrict (w_H W) ms2) regs3 (mrestrict (w_H W3) mem3) (ss_mem ss3)
    RA102_check_reject_clean_1 HS2 eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
    ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) (submem_refl _) eq_refl
    ltac:(intros r Hr; exact (HP3 r Hr)) HKR3) as HS3;
  let ss4 := eval vm_compute in (ss_after_call ss3 (ss_mem ss3) 48 RA102_check_reject_clean_1) in
  change (ss_after_call ss3 (ss_mem ss3) 48 RA102_check_reject_clean_1) with ss4 in HS3 end.
change (mkst regs3 (Z_to_bv 64 RA102_check_reject_clean_1) (mrestrict (w_H W3) mem3) (seg_rom pa_segs)) with
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 RA102_check_reject_clean_1) mem3 (seg_rom pa_segs))) in HS3.
clear HS2 HKR3.
set (EF := havoc EE 48 (map (getr regs3) CLOB)) in *.
assert (Usp4 : bv_unsigned (ew EF 2) = spZ regs) by (subst EF; rewrite ew_havoc_old by lia; exact Usp2).
pose proof (@alloc_ceiling_val rc) as [_ Hac].
(* ---- 0x82144 bne a0, s0: fuzz_alloc_live () != live_before is the third abort ---- *)
assert (UA : U EF (SOff 52 0) = Ledger.lsum Lam).
{ apply (U_atom EF 52 (Ledger.lsum Lam)); [change (ew EF 52) with (getr regs3 10); exact Hres | lia]. }
assert (UL : U EF (SOff 12 0) = Ledger.lsum Lam).
{ apply (U_atom EF 12 (Ledger.lsum Lam)); [|lia]. subst EF. rewrite ew_havoc_old by lia. subst EE. rewrite ew_havoc_old by lia.
  rewrite (Ereg_at 12%nat 12%bv eq_refl), H12, Hlive. reflexivity. }
c102_branch tbl_crc102 HS3.
{ intros Hc3 HS3. exfalso. rewrite branch_ne_U, UA, UL, Z.eqb_refl in Hc3. discriminate Hc3. }
intros Hc3 HS3.
pose proof HJ3 as (HAR3 & _).
c102_run TBL HS3 HJ3 Hmn.
{ awr_ok_tac. exact Usp4. }
(* ---- 0x82154 ret ---- *)
rreg HS3 (1%bv : bv 5) R1'.
lazymatch type of HS3 with st_ok _ _ _ (restrict _ ?msx) =>
  assert (HBF : forall a, 0 <= a < YM05.alloc_ceiling ->
    mbyte pa_segs (mrestrict (w_H W3) (ms_mem msx)) a = mbyte pa_segs (mrestrict (w_H W3) mem3) a);
  [ intros a Ha;
    match goal with H : frame_of _ ?rs4 (mrestrict _ mem3) (mrestrict _ (ms_mem msx)) |- _ =>
      exact (c102_frame_below pa_segs EF rs4 (w_H W3) mem3 (ms_mem msx) H
        ltac:(intros x (r & Hin & Hx); cbn in Hin; destruct Hin as [<-|[]];
          cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi] in Hx; rewrite Usp4 in Hx; lia) a Ha) end
  | ];
  eapply (SRr_ret_at pa_segs tbl_crc102 TBL HWX W3 EF _ _ _ _ HS3); [reflexivity | vm_compute; reflexivity |];
  intros matF;
  assert (E1r : ew EF 1 = getr regs 1)
    by (subst EF; rewrite ew_havoc_old by lia; subst EE; rewrite ew_havoc_old by lia; exact (Ereg_at 1%nat 1%bv eq_refl));
  assert (Hpc : v_jalr (getr (ms_regs msx) 1) 0 = getr regs 1) by (rewrite R1', ?c102_SOff0, E1r; exact Hra);
  rewrite Hpc; unfold apost_base_x;
  match goal with |- context [mkCfg _ ?mdx] => exists ly2, S2, Hp2, (ms_regs msx), (ms_mem msx), mdx, (0 + k1) end;
  split; [reflexivity|];
  split; [apply (ajournal_x_materialize pa_segs B _ ARx LAWS HSL); exact HJ3|];
  split; [eapply (aregs_preserved_of_st_ok pa_segs (w_H W3) EF _ msx regs [] HS3);
    [ apply env_agree_havoc_ge; [lia|]; apply env_agree_havoc_ge; [lia|]; apply env_agree_refl | vm_compute; reflexivity ]|];
  unfold fQmn; cbv beta;
  split; [|exact Hmn];
  split; [exact EHp|]; split; [exact ES2|]; split; [exact Ebl|]; split; [exact Hrk|];
  exact (c102_ledger_keep B ARx LAWS ly2 S2 Hp2 W3 mem3 md3 (ms_mem msx) Lam peak cnt fail ran most own HAR3 HL3 HBF)
end.
Qed.
End W.
