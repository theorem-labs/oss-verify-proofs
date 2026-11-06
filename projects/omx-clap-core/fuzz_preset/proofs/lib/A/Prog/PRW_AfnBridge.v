(* fuzz_preset, program part: afn_spec_cf_of_text, the ONE generic bridge from a contract text to the program
   interface's callee contract (a Theorem Labs lane's ruling, 2026-10-29: "ONE generic bridge over the cf instance in the
   FCapiCf / PresetD2pAPf layer"), and the alloc.c accessor entries of LLVMFuzzerTestOneInput's callee record. It lives
   in lib/A/Prog, not in the kit: afn_spec_cf is the cf INSTANCE's vocabulary and no lib/Reusable file may Require
   lib/A.
   rule 24: no function proved. The accessor citations below cite h-w6rep-2's Qed walks; this file proves only the
   adapter and its instances.
   BUILT AGAINST (#102, pins A' asan 1be0f53d): the interface of record lib/A/PresetCfnA.v blob 245f68e4e777 (since revised),
   the #102 kit tip as it stood on the integration head
   (lib/A/PRH_Base.v fdb45545469b, PRH_FnAlloc.v 740f4d11d144, both since revised), a Theorem Labs lane's A' accessor walks lib/A/Prog/PwAllocSurf.v
   428e59506566 (p102-allocsurf f5123281fbe2, on int102), h-mani-a8's lib/A/FCapiCf.v e29123ff8116.
   THE #102 RE-CUT (from origin/cold/h-pre-b1-bridgea-mn 0c8e1ed21bd3, the iface-mn port; every change is forced by
   one of the five interface / kit changes below, and no statement is weakened):
   (a) prh_ledger has 13 arguments: the two #102 cells g_most / g_own_ran_out (prh_ledger_most / prh_ledger_own). The
       accessor tuple prwA_led carries them as most / own, and every prh_ledger site carries the SAME most / own from
       the pre to the post (the accessor texts leave both cells alone).
   (b) the accessor texts' posts are the m-form fpostm (the memnorm keep) and their Q states S' = S: prwA_Q_* are the
       texts' Q verbatim (so they gain S' = S); the conversion lemmas forget the keep (prw_fpostm_forget) and state
       fpost as before.
   (c) the kit's fpre has five conjuncts (afn_pre_x, the read-only view, the stack-top gap, raZ regs <
       alloc_ceiling, frm_zero of the entry fcsr): prw_text's premise is all five. The record carries the raZ bound
       (prw_fi_pre, as before) and afn_spec_cf supplies frm_zero, so the bridge passes both instead of dropping them.
   (d) afn_spec_cf no longer takes `blocks_bytes S + LIVE_LIB <= LIVE_MAX` (PresetCfnA.v header item (12)): the bridge
       introduces one premise fewer.
   (e) THE SLOT'S CALLEE RECORD (D1, 17:34Z): preset_callee_contracts' fields are the texts themselves, at
       iface_ARx (ARcf /\ xs_placed_cf at CfParams_preset), prh_room_live_a8 and preset_sink_head, for the 16 callees
       of LLVMFuzzerTestOneInput on the #102 pins; the old fields `afn_spec_cf A_<f> F_<f>` left the slot. So
       pcc_<f>_of_walk now states the field pcc_<f> (as the B' sibling's pcc_check_reject_clean_of_walk,
       lib/AU/Prog/PRW_AfnBridgeBProg.v on origin/cold/h-rw-pre-7-bp-halts), and the old afn_spec_cf entries are kept,
       renamed afn_<f>_of_walk (the name afn_fuzz_alloc_fail_of_walk already had).
   THE 16-CALLEE SET AND THIS FILE: of the record's seven accessor fields, this file gives the four whose walks are in
   PwAllocSurf.v (pcc_fuzz_alloc_live, _count, _peak_reset, _peak). fuzz_alloc_fail is not a callee of
   LLVMFuzzerTestOneInput (no field); its afn_spec_cf entry at its listing entry stays. pcc_stack_malloc_of_fcapi is
   the cf form FCapiCf gives; the #102 field pcc_stack_malloc is the memnorm-keeping cfm form
   (astack_malloc_realizes_cfm), which FCapiCf does not state, so that entry is NOT the #102 field.
   PST_unowned (PwAllocSurf.v Section T, PST_ok's B half) is PROVED in lib/A/Prog/PwPstUnowned.v (pst_unowned_A from
   AF0m.TfibSyms B, pst_unowned_TfibB at AD2l.TfibB). That file Requires THIS one (it instantiates the entries below),
   so this file keeps PST_unowned as a Section hypothesis and consumers cite PwPstUnowned.v's closed entries.
   THE RECORD ROUTE (h-hpreset-7 approved): the walks are at ARx := ARcf /\ xs_placed_cf (PwAllocSurf.v ARc, which is
   the interface's iface_ARx at PA := PI_prog_A by conversion), the afn_spec_cf contract at ARcf alone. ARx is POSITIVE
   in afn_pre_x and in ajournal_x (YCbqG.v), so the adapter needs only `XP ly S` at entry and returns `XP ly' S'` at
   exit; it carries them in the record, as fi_pre's FIRST conjunct and fi_post's FIRST conjunct. The caller supplies
   XP = xs_placed_cf from its own invariant.
   THE SCHEMA: a text at entry pc with frame bound STK and footprint FP is `prw_text pc STK FP X P Q`: for every tuple
   x : X of its logical variables, the kit's fpre and its own premises P x give SRr to apost_base_x with its post
   Q x. Its record is prw_fn STK ctx fr bud FP X P Q, with fi_pre = XP /\ gap /\ raZ bound /\ (exists x, P x) and
   fi_post = XP' /\ (exists x, P x at entry /\ Q x). ctx, fr and bud are the record's; a text that does not read them
   (every accessor) is adapted at any value, so they are parameters.
   THE INTERFACE PREMISES THE ADAPTER DROPS (the text is stronger): the context membership, the frames bound and
   LIB_ROOM. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YI16 YM05 YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0b YPsym YC4aP YP08 YL0b.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YG0ncf YG0dcf YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0lawscf YGcallcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
AB1v Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnAlloc CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require AF0m PresetCfnA FCapiCf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import PwAllocSurf.
Import ListNotations.
Local Open Scope Z_scope.

(* the interface's fi_fp / fi_pre / fi_post types (PresetCfnA.v fn_iface; fi_fp reads the callee's entry memory) *)
Definition prw_fp_t : Type := bvmap 5 word -> (word -> option byte) -> alayout -> astate -> list (Z * Z).
Definition prw_pre_t : Type :=
  alayout -> astate -> list Z -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Definition prw_post_t : Type :=
  bvmap 5 word -> alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model ->
  alayout -> astate -> list Z -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

(* ==== 1. the record of a text, carrying the state conjunct XP ==== *)
Section r. Context {rc : YM05.RunCeil}.
Variable XP : alayout -> astate -> Prop.
(* fi_pre carries THREE facts the interface does not supply: the state conjunct XP (xs_placed_cf, the walks' ARx), the
   kit's stack-top gap `spZ regs + 64 <= ly_stk_hi ly` (fpre's third conjunct, h-rw-pre-5's pj_write counter-case
   sp0 = ly_stk_hi), and `raZ regs < YM05.alloc_ceiling` (fpre's fourth conjunct, from h-rw-pre-5's two put-family
   measurements). The last is what makes the put family's CASE 2 (o = spZ regs + 8, where [o - 16] is the callee's own
   saved ra) closable at all, and it is closable only if the bound is visible in the record the walk unpacks - so it
   goes HERE as well as in fpre. h-pre-b1's PRW_AfnBridgeB.v mirrors all three; the two bridges must not drift. *)
Definition prw_fi_pre (X : Type) (P : X -> prw_pre_t) : prw_pre_t :=
  fun ly S Hp W regs mem md =>
  XP ly S /\ spZ regs + 64 <= ly_stk_hi ly /\ raZ regs < YM05.alloc_ceiling /\
  exists x : X, P x ly S Hp W regs mem md.
Definition prw_fi_post (X : Type) (P : X -> prw_pre_t) (Q : X -> prw_post_t) : prw_post_t :=
  fun regs ly S Hp W mem md ly' S' Hp' W' regs' mem' md' =>
  XP ly' S' /\
  exists x : X, P x ly S Hp W regs mem md /\ Q x regs ly S Hp W mem md ly' S' Hp' W' regs' mem' md'.
Definition prw_fn (STK : Z) (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z)
  (FP : prw_fp_t) (X : Type) (P : X -> prw_pre_t) (Q : X -> prw_post_t)
  : PresetCfnA.fn_iface :=
  PresetCfnA.MkFn STK ctx fr bud FP (prw_fi_pre X P) (prw_fi_post X P Q).
End r.

(* ==== 2. the generic bridge ==== *)
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {L : ptable asym} {PA : PAImg L}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation segs := tfibsegs.
Variable B : asyms.
Variable XP : alayout -> astate -> Prop.

(* the walks' allocator relation: the interface's ARcf with XP *)
Definition prw_ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop :=
  fun ly S Hp W mem md => ARcf (cp := CP) segs B ly S Hp W mem md /\ XP ly S.

(* THE SCHEMA OF A TEXT (the kit's fpre / fpost at PST := prh_pst, the image's sink head); its footprint is read at
   the entry registers and memory, as the interface's fi_fp is. The premise is the kit's fpre (PRH_Base.v :588-610),
   all five conjuncts, nested as fpre nests them. *)
Definition prw_text (pc STK : Z) (FP : prw_fp_t) (X : Type)
  (P : X -> prw_pre_t) (Q : X -> prw_post_t) : Prop :=
  forall ly S Hp (W : world segs) regs mem md ch (x : X),
  afn_pre_x segs B prw_ARx STK ly S Hp W regs mem md ch /\
  (PRH_Base.arodata_okP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) B (aview segs (w_H W) mem) /\
   spZ regs + 64 <= ly_stk_hi ly /\ raZ regs < YM05.alloc_ceiling /\ YK0o.frm_zero (@YK11.fp_csr fx)) ->
  P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs pc regs mem md)
    (apost_base_x (SK := PresetCfnA.preset_sink_head) segs B (@PRH_Base.prh_pst PresetCfnA.preset_prh_img) prw_ARx
       STK (FP regs mem ly S) regs ly S Hp W mem md (Q x regs ly S Hp W mem md)).

(* THE BRIDGE: a text in the schema discharges the interface's callee contract for its record *)
Lemma afn_spec_cf_of_text : forall pc STK ctx fr bud FP (X : Type) (P : X -> prw_pre_t) (Q : X -> prw_post_t),
  prw_text pc STK FP X P Q ->
  PresetCfnA.afn_spec_cf (L := L) (PA := PA) B pc (prw_fn XP STK ctx fr bud FP X P Q).
Proof.
intros pc STK ctx fr bud FP X P Q T.
unfold PresetCfnA.afn_spec_cf, prw_fn.
cbn [PresetCfnA.fi_stk PresetCfnA.fi_ctx PresetCfnA.fi_frames PresetCfnA.fi_budget PresetCfnA.fi_fp
  PresetCfnA.fi_pre PresetCfnA.fi_post].
intros ly S Hp W regs mem md ch Hpre _ _ Haro _ [HX [HG [Hra [x Hx]]]] Hfz.
unfold PresetCfnA.afn_pre_cf, afn_pre_x in Hpre.
destruct Hpre as [HAR Hrest].
assert (Hpre' : afn_pre_x segs B prw_ARx STK ly S Hp W regs mem md ch).
{ unfold afn_pre_x, prw_ARx. exact (conj (conj HAR HX) Hrest). }
eapply SRr_mono; [exact (T ly S Hp W regs mem md ch x (conj Hpre' (conj Haro (conj HG (conj Hra Hfz)))) Hx) |].
intros W' c' _ Hpost.
(* the interface's callee post is the float form: this text leaves the float state alone, so
   YCbqG.apost_base_x_F gives it from the plain form at the entry rounding mode 0 (Hfz). h-pre-b1's twin,
   PRW_AfnBridgeB.v:158 at cold/h-pre-b1-bridgeb 8b9c82bcf459, does the same; the two must not drift. *)
unfold PresetCfnA.apost_base_cfF. apply YCbqG.apost_base_x_F; [exact Hfz |].
unfold apost_base_x, ajournal_x in *.
destruct Hpost as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hj & Hr & HQ).
destruct Hj as [[HAR' HX'] Hj].
exists ly', S', Hp', regs', mem', md', k.
split; [exact Hc |]. split; [exact (conj HAR' Hj) |]. split; [exact Hr |].
unfold prw_fi_post. split; [exact HX' |]. exists x. split; [exact Hx | exact HQ].
Qed.
End b.

(* ==== 3. the five accessor texts in the schema: their tuples, premises and posts, VERBATIM from this tree's
   lib/A/PRH_FnAlloc.v :110-163, over the same section context, and one conversion lemma each (destructure the tuple,
   apply the text, forget the memnorm keep of its m-form post) ==== *)
(* the ledger's values, in prh_ledger's order: Lam, peak, cnt, fail, ran, most, own *)
Definition prwA_led : Type := (list (Z * Z) * Z * Z * Z * Z * Z * Z)%type.

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}.
Context {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.

Definition prwA_P (x : prwA_led) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own.
Definition prwA_P_fail (y : prwA_led * Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  let '(x, k) := y in prwA_P x ly S Hp W regs mem md /\ getr regs 10 = w64 k /\ 0 <= k < 2 ^ 64.

Definition prwA_Q_live (x : prwA_led) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (ly' : alayout) (S' : astate) (Hp' : list Z)
  (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in
  (room_live_cf S -> room_live_cf S') /\
  getr regs' 10 = w64 (Ledger.lsum Lam) /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Definition prwA_Q_peak (x : prwA_led) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (ly' : alayout) (S' : astate) (Hp' : list Z)
  (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in
  (room_live_cf S -> room_live_cf S') /\
  getr regs' 10 = w64 peak /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Definition prwA_Q_peak_reset (x : prwA_led) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (ly' : alayout) (S' : astate) (Hp' : list Z)
  (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in
  (room_live_cf S -> room_live_cf S') /\
  Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger B ly' S' Hp' W' mem' Lam (Ledger.lsum Lam) cnt fail ran most own.
Definition prwA_Q_count (x : prwA_led) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (ly' : alayout) (S' : astate) (Hp' : list Z)
  (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in
  (room_live_cf S -> room_live_cf S') /\
  getr regs' 10 = w64 cnt /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own.
Definition prwA_Q_fail (y : prwA_led * Z) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model) (ly' : alayout) (S' : astate) (Hp' : list Z)
  (W' : world segs) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) : Prop :=
  let '((Lam, peak, cnt, fail, ran, most, own), k) := y in
  (room_live_cf S -> room_live_cf S') /\
  Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
  prh_ledger B ly' S' Hp' W' mem' Lam peak cnt (if k <? SIZE_MAXZ - cnt then cnt + k else SIZE_MAXZ) ran most own.

(* the m-form post (fpostm: the post's Q with the memnorm keep, PRH_Base.v fQmn) gives the plain one *)
Lemma prw_fpostm_forget : forall ARx SK STK FP regs ly S Hp (W : world segs) mem md Q c,
  SRr segs W c (fpostm B ARx SK STK FP regs ly S Hp W mem md Q) ->
  SRr segs W c (fpost B ARx SK STK FP regs ly S Hp W mem md Q).
Proof.
intros ARx SK STK FP regs ly S Hp W mem md Q c H.
eapply SRr_mono; [exact H |]. intros W' c' _ Hpost.
unfold fpostm, fpost, fQmn, apost_base_x in *.
destruct Hpost as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hj & Hr & [HQ _]).
exists ly', S', Hp', regs', mem', md', k. exact (conj Hc (conj Hj (conj Hr HQ))).
Qed.

Lemma prwA_live_text : forall ARx SK, tfuzz_alloc_live_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwA_led),
  fpre B ARx STK_fuzz_alloc_live ly S Hp W regs mem md ch -> prwA_P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_live) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_live [] regs ly S Hp W mem md (prwA_Q_live x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[Lam peak] cnt] fail] ran] most] own] H1 H2.
apply prw_fpostm_forget. exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran most own H1 H2).
Qed.
Lemma prwA_peak_text : forall ARx SK, tfuzz_alloc_peak_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwA_led),
  fpre B ARx STK_fuzz_alloc_peak ly S Hp W regs mem md ch -> prwA_P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_peak) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_peak [] regs ly S Hp W mem md (prwA_Q_peak x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[Lam peak] cnt] fail] ran] most] own] H1 H2.
apply prw_fpostm_forget. exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran most own H1 H2).
Qed.
Lemma prwA_peak_reset_text : forall ARx SK, tfuzz_alloc_peak_reset_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwA_led),
  fpre B ARx STK_fuzz_alloc_peak_reset ly S Hp W regs mem md ch -> prwA_P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_peak_reset) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_peak_reset [] regs ly S Hp W mem md
       (prwA_Q_peak_reset x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[Lam peak] cnt] fail] ran] most] own] H1 H2.
apply prw_fpostm_forget. exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran most own H1 H2).
Qed.
Lemma prwA_count_text : forall ARx SK, tfuzz_alloc_count_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwA_led),
  fpre B ARx STK_fuzz_alloc_count ly S Hp W regs mem md ch -> prwA_P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_count) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_count [] regs ly S Hp W mem md (prwA_Q_count x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[Lam peak] cnt] fail] ran] most] own] H1 H2.
apply prw_fpostm_forget. exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran most own H1 H2).
Qed.
Lemma prwA_fail_text : forall ARx SK, tfuzz_alloc_fail_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (y : prwA_led * Z),
  fpre B ARx STK_fuzz_alloc_fail ly S Hp W regs mem md ch -> prwA_P_fail y ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_fail) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_fail [] regs ly S Hp W mem md (prwA_Q_fail y regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[[Lam peak] cnt] fail] ran] most] own] k] H1 [H2 [H3 H4]].
apply prw_fpostm_forget. exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran k most own H1 H2 H3 H4).
Qed.
End q.

(* ==== 4. the instances at image A': PA := PI_prog_A, PI := prh_img_A (= the interface's preset_prh_img), preset's
   CfParams, the interface's sink head, XP := xs_placed_cf. ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg}.
Context {RL : PrhRoomLive}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PIA := prh_img_A.
#[local] Abbreviation SEGS := (@pa_segs _ A_prog_listing PI_prog_A).
#[local] Abbreviation SIGMA := (@pa_sigma _ A_prog_listing PI_prog_A).
#[local] Abbreviation SKA := PresetCfnA.preset_sink_head.
#[local] Abbreviation RLX := (@prh_room_live_a8 CfParams_preset).
#[local] Abbreviation XPc := (fun (ly : alayout) (S : astate) => xs_placed_cf ly S).
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* the interface's ARx (PresetCfnA.v iface_ARx: ARcf /\ xs_placed_cf at CfParams_preset) at the A' listing *)
#[local] Abbreviation ARi := (PresetCfnA.iface_ARx (L := A_prog_listing) (PA := PI_prog_A) B).
(* PST_ok's B half (PwAllocSurf.v Section T). PROVED in lib/A/Prog/PwPstUnowned.v (pst_unowned_A, pst_unowned_TfibB),
   which Requires this file and closes the entries that take it at B := AD2l.TfibB (see the header) *)
Hypothesis PST_unowned : forall a, Exists (in_zr a) (@prh_pst PIA) -> ~ Exists (in_zr a) (as_owned_static B).

(* ---- 4a. the #102 slot's fields (PresetCfnA.v preset_callee_contracts): the text at iface_ARx, prh_room_live_a8
   and preset_sink_head, each the walk of PwAllocSurf.v (whose ARc IS iface_ARx at PI_prog_A, by conversion). After
   the section, each holds at every float state, as the field asks. ---- *)
Theorem pcc_fuzz_alloc_live_of_walk :
  @PRH_FnAlloc.tfuzz_alloc_live_specX fx rc CP PresetCfnA.preset_prh_img RLX A_prog_listing PI_prog_A B ARi SKA.
Proof. exact (fuzz_alloc_live_holds (SK := SKA) B). Qed.

Theorem pcc_fuzz_alloc_count_of_walk :
  @PRH_FnAlloc.tfuzz_alloc_count_specX fx rc CP PresetCfnA.preset_prh_img RLX A_prog_listing PI_prog_A B ARi SKA.
Proof. exact (fuzz_alloc_count_holds (SK := SKA) B). Qed.

Theorem pcc_fuzz_alloc_peak_reset_of_walk :
  @PRH_FnAlloc.tfuzz_alloc_peak_reset_specX fx rc CP PresetCfnA.preset_prh_img RLX A_prog_listing PI_prog_A B ARi
    SKA.
Proof. exact (fuzz_alloc_peak_reset_holds (SK := SKA) B PST_unowned). Qed.

Theorem pcc_fuzz_alloc_peak_of_walk :
  @PRH_FnAlloc.tfuzz_alloc_peak_specX fx rc CP PresetCfnA.preset_prh_img RLX A_prog_listing PI_prog_A B ARi SKA.
Proof. exact (fuzz_alloc_peak_holds (SK := SKA) B). Qed.

(* ---- 4b. the afn_spec_cf entries (the pre-#102 slot's field form), through the generic bridge, at any room-live
   instance RL ---- *)
#[local] Abbreviation nofp :=
  (fun (_ : bvmap 5 word) (_ : word -> option byte) (_ : alayout) (_ : astate) => @nil (Z * Z)).

(* the records (ctx, fr, bud: the record's, any value) *)
Definition prwA_F_live (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) : PresetCfnA.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_live (PI := PIA)) ctx fr bud nofp prwA_led
    (prwA_P (cp := CP) (PI := PIA) (PA := PI_prog_A) B) (prwA_Q_live (cp := CP) (PI := PIA) (PA := PI_prog_A) B).
Definition prwA_F_peak (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) : PresetCfnA.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_peak (PI := PIA)) ctx fr bud nofp prwA_led
    (prwA_P (cp := CP) (PI := PIA) (PA := PI_prog_A) B) (prwA_Q_peak (cp := CP) (PI := PIA) (PA := PI_prog_A) B).
Definition prwA_F_peak_reset (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) : PresetCfnA.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_peak_reset (PI := PIA)) ctx fr bud nofp prwA_led
    (prwA_P (cp := CP) (PI := PIA) (PA := PI_prog_A) B)
    (prwA_Q_peak_reset (cp := CP) (PI := PIA) (PA := PI_prog_A) B).
Definition prwA_F_count (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) : PresetCfnA.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_count (PI := PIA)) ctx fr bud nofp prwA_led
    (prwA_P (cp := CP) (PI := PIA) (PA := PI_prog_A) B) (prwA_Q_count (cp := CP) (PI := PIA) (PA := PI_prog_A) B).
Definition prwA_F_fail (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) : PresetCfnA.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_fail (PI := PIA)) ctx fr bud nofp (prwA_led * Z)
    (prwA_P_fail (cp := CP) (PI := PIA) (PA := PI_prog_A) B)
    (prwA_Q_fail (cp := CP) (PI := PIA) (PA := PI_prog_A) B).

(* the interface's entries are the listing's (#102: generated names, pa_sigma of the listing class; the instance is
   passed explicitly, never inferred) *)
Lemma prwA_pc_live : PresetCfnA.A_fuzz_alloc_live (L := A_prog_listing) (PA := PI_prog_A) = SIGMA AS_fuzz_alloc_live.
Proof. vm_compute. reflexivity. Qed.
Lemma prwA_pc_peak : PresetCfnA.A_fuzz_alloc_peak (L := A_prog_listing) (PA := PI_prog_A) = SIGMA AS_fuzz_alloc_peak.
Proof. vm_compute. reflexivity. Qed.
Lemma prwA_pc_peak_reset :
  PresetCfnA.A_fuzz_alloc_peak_reset (L := A_prog_listing) (PA := PI_prog_A) = SIGMA AS_fuzz_alloc_peak_reset.
Proof. vm_compute. reflexivity. Qed.
Lemma prwA_pc_count :
  PresetCfnA.A_fuzz_alloc_count (L := A_prog_listing) (PA := PI_prog_A) = SIGMA AS_fuzz_alloc_count.
Proof. vm_compute. reflexivity. Qed.

Theorem afn_fuzz_alloc_live_of_walk : forall ctx fr bud,
  PresetCfnA.afn_spec_cf (L := A_prog_listing) (PA := PI_prog_A) B
    (PresetCfnA.A_fuzz_alloc_live (L := A_prog_listing) (PA := PI_prog_A)) (prwA_F_live ctx fr bud).
Proof.
intros ctx fr bud. rewrite prwA_pc_live. unfold prwA_F_live.
apply (afn_spec_cf_of_text (L := A_prog_listing) (PA := PI_prog_A) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwA_live_text (cp := CP) (PI := PIA) (PA := PI_prog_A) B ARc SKA
  (fuzz_alloc_live_holds_rl (RL := RL) (SK := SKA) B) ly S Hp W regs mem md ch x H1 H2).
Qed.

Theorem afn_fuzz_alloc_peak_of_walk : forall ctx fr bud,
  PresetCfnA.afn_spec_cf (L := A_prog_listing) (PA := PI_prog_A) B
    (PresetCfnA.A_fuzz_alloc_peak (L := A_prog_listing) (PA := PI_prog_A)) (prwA_F_peak ctx fr bud).
Proof.
intros ctx fr bud. rewrite prwA_pc_peak. unfold prwA_F_peak.
apply (afn_spec_cf_of_text (L := A_prog_listing) (PA := PI_prog_A) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwA_peak_text (cp := CP) (PI := PIA) (PA := PI_prog_A) B ARc SKA
  (fuzz_alloc_peak_holds_rl (RL := RL) (SK := SKA) B) ly S Hp W regs mem md ch x H1 H2).
Qed.

Theorem afn_fuzz_alloc_peak_reset_of_walk : forall ctx fr bud,
  PresetCfnA.afn_spec_cf (L := A_prog_listing) (PA := PI_prog_A) B
    (PresetCfnA.A_fuzz_alloc_peak_reset (L := A_prog_listing) (PA := PI_prog_A)) (prwA_F_peak_reset ctx fr bud).
Proof.
intros ctx fr bud. rewrite prwA_pc_peak_reset. unfold prwA_F_peak_reset.
apply (afn_spec_cf_of_text (L := A_prog_listing) (PA := PI_prog_A) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwA_peak_reset_text (cp := CP) (PI := PIA) (PA := PI_prog_A) B ARc SKA
  (fuzz_alloc_peak_reset_holds_rl (RL := RL) (SK := SKA) B PST_unowned) ly S Hp W regs mem md ch x H1 H2).
Qed.

Theorem afn_fuzz_alloc_count_of_walk : forall ctx fr bud,
  PresetCfnA.afn_spec_cf (L := A_prog_listing) (PA := PI_prog_A) B
    (PresetCfnA.A_fuzz_alloc_count (L := A_prog_listing) (PA := PI_prog_A)) (prwA_F_count ctx fr bud).
Proof.
intros ctx fr bud. rewrite prwA_pc_count. unfold prwA_F_count.
apply (afn_spec_cf_of_text (L := A_prog_listing) (PA := PI_prog_A) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwA_count_text (cp := CP) (PI := PIA) (PA := PI_prog_A) B ARc SKA
  (fuzz_alloc_count_holds_rl (RL := RL) (SK := SKA) B) ly S Hp W regs mem md ch x H1 H2).
Qed.

(* fuzz_alloc_fail: no record entry (it is not a callee of LLVMFuzzerTestOneInput on the #102 pins, PresetCfnA.v
   section 1); the same bridge at its listing entry *)
Theorem afn_fuzz_alloc_fail_of_walk : forall ctx fr bud,
  PresetCfnA.afn_spec_cf (L := A_prog_listing) (PA := PI_prog_A) B (SIGMA AS_fuzz_alloc_fail)
    (prwA_F_fail ctx fr bud).
Proof.
intros ctx fr bud. unfold prwA_F_fail.
apply (afn_spec_cf_of_text (L := A_prog_listing) (PA := PI_prog_A) B XPc).
intros ly S Hp W regs mem md ch y H1 H2.
exact (prwA_fail_text (cp := CP) (PI := PIA) (PA := PI_prog_A) B ARc SKA
  (fuzz_alloc_fail_holds_rl (RL := RL) (SK := SKA) B PST_unowned) ly S Hp W regs mem md ch y H1 H2).
Qed.

(* ==== 5. the stack-malloc row from h-mani-a8's FCapiCf.preset_aa_stack_malloc_cf, in the cf form it states: the
   allocator laws are a8's AR_laws_ok_cf (YG0lawscf.v), the class set is [0; 1; 3] by computation; TfibSyms B (the
   image's symbol facts of B) stays a premise, as in FCapiCf. NOT the #102 field pcc_stack_malloc, which asks the
   memnorm-keeping astack_malloc_realizes_cfm (PresetCfnA.v section 6) ---- *)
Theorem pcc_stack_malloc_of_fcapi : AF0m.TfibSyms B ->
  forall cid, In cid (@cf_fs_classes CP) -> astack_malloc_realizes_cf (fx := fx) (rc := rc) (cp := CP) tfibsegs B cid.
Proof.
intros TB cid Hc.
assert (E : @cf_fs_classes CP = [0; 1; 3]) by reflexivity.
rewrite E in Hc.
exact (FCapiCf.preset_aa_stack_malloc_cf (cp := CP) B (AR_laws_ok_cf (cp := CP) tfibsegs B) TB cid Hc).
Qed.
End w.
