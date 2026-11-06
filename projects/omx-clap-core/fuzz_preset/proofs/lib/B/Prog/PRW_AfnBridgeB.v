(* fuzz_preset, program part, image B' (asan-ubsan, #102 pin d663f82d7f48, unstripped twin c90d4fa54d43):
   afn_spec_cf_of_text, the ONE generic bridge from a kit contract text to the program interface's callee contract
   afn_spec_cf (a Theorem Labs lane's ruling, 2026-10-29: "ONE generic bridge over the cf instance in the FCapiCf /
   PresetD2pAPf layer"), and the #102 callee-record fields that this file's walks discharge. It lives in lib/B/Prog,
   not in the kit: afn_spec_cf is the cf INSTANCE's vocabulary and no lib/Reusable file may Require lib/A or lib/AU.
   rule 24: no function proved. The accessor citations below cite the Qed walks of lib/B/Prog/PwAllocSurfB.v; this
   file proves only the adapter and its instances.
   RELOCATED AND RE-FIT 2026-10-29 from the old-pin file (a working branch 5f6a2b85e1b9, blob de6140b5ae50,
   image f8f98a95). This file names no address: its entries are pa_sigma of PI_prog_B, checked against the
   interface's by vm_compute (a wrong-image constant fails there), so the relocation is the image under it. The
   re-fit is to two texts of this tree:
   - THE KIT OF RECORD f97c8b2f046b (lib/A/PRH_Base.v blob fdb45545469b, lib/A/PRH_FnAlloc.v blob 740f4d11d144,
     lib/A/PRH_FnCheck.v blob 9ecd8eb167c6). (i) fpre (PRH_Base.v :588-610) has FIVE conjuncts: afn_pre_x, the
     read-only view, the stack gap, `raZ regs < YM05.alloc_ceiling` and FRM0-ENTRY's `frm_zero (fp_csr fx)`. So
     prw_text takes all five, and afn_spec_cf_of_text passes the record's raZ bound and afn_spec_cf's own frm_zero
     premise (this closes the old file's EXPECTED ROW (c)). (ii) The ledger carries #102's two cells as fields
     (prh_ledger .. ran most own), so prwB_led is a 7-tuple (a 9-tuple for check_bounded_alloc). (iii) Every text
     posts the m-form fpostm (PRH_Base.v :900-903, fpost at fQmn mem Q: Q and the memnorm keep), and states S' = S.
     So each record's post is the text's `fQmn mem Q` VERBATIM, and a conversion lemma is still one `exact`.
   - THE INTERFACE OF RECORD iface-102 (lib/AU/PresetCfnB.v blob 316b293c8f23). (i) afn_spec_cf (:899-910) no longer
     takes `blocks_bytes S + LIVE_LIB <= LIVE_MAX` (its header item (12)), so the adapter introduces one premise
     fewer. (ii) Its callee record preset_callee_contracts (:950-992) holds the kit's texts THEMSELVES at iface_ARx
     (:942-945; D1, owner 17:34Z), not afn_spec_cf over fn_iface records. So section 6 states the four record fields
     that PwAllocSurfB's walks discharge (pcc_fuzz_alloc_live, _count, _peak_reset, _peak; :976-983) in the record's
     own words, at every float state. Those are the entries the composition cites; the afn_spec_cf entries of
     section 4 are the same walks in the schema, for a consumer of afn_spec_cf.
   PST_unowned (PwAllocSurfB.v Section T, PST_ok's B half) is PROVED in lib/B/Prog/PwPstUnownedB.v: pst_unowned_B
   from YF0m.TfibSyms B (ts_owned and a computation over the 93 rows of Tfib_owned_static and prh_pst's seven cells),
   and pst_unowned_TfibB with no premise. THE CYCLE: that file Requires THIS one (it instantiates the entries below
   that take PST_unowned), so this file keeps PST_unowned as a Section hypothesis and CONSUMERS CITE the closed
   entries of PwPstUnownedB.v section 2 at B := YD2l.TfibB.
   THE RECORD ROUTE (a Theorem Labs lane approved): the walks are at ARx := ARcf /\ xs_placed_cf (PwAllocSurfB.v ARc, like
   FuzzMallocB / FuzzFreeB / FuzzStrdupB), afn_spec_cf at ARcf alone. ARx is POSITIVE in afn_pre_x and in ajournal_x
   (YCbqG.v :192, :202), so the adapter needs only `XP ly S` at entry and returns `XP ly' S'` at exit; it carries them
   in the record, as fi_pre's FIRST conjunct and fi_post's FIRST conjunct, and the interface is unchanged. The caller
   supplies XP = xs_placed_cf from its own invariant (preset_lib_pre_x / _post_x carry it, PresetCfnB.v :817, :875).
   The #102 record's iface_ARx IS ARc (ARcf /\ xs_placed_cf at pa_segs), so section 6 needs no adapter.
   THE SCHEMA: a text at entry pc with frame bound STK and footprint FP is `prw_text pc STK FP X P Q`: for every tuple
   x : X of its logical variables, the kit's fpre (its five conjuncts) and its own premises P x give SRr to
   apost_base_x with its post Q x. Its record is prw_fn STK ctx fr bud FP X P Q, with fi_pre = XP /\ the stack gap /\
   the raZ bound /\ (exists x, P x) and fi_post = XP' /\ (exists x, P x at entry /\ Q x). ctx, fr and bud are the
   record's; a text that does not read them (every accessor) is adapted at any value, so they are parameters.
   THE AGREED ROWS (a Theorem Labs lane's rulings):
   (a) DW, the run's data words (kit PRH_Base.v prh_univ_closure). Every record takes DW : list Z after ctx fr bud,
       and every entry takes DW as a plain binder: the top instantiates it per run. The accessor texts read no data
       word, so their records ignore it; a text that reads one puts it in its premises, the schema unchanged.
   (b) fpre's stack gap `spZ regs + 64 <= ly_stk_hi ly` (a Theorem Labs lane's pj_write counter-case sp0 = ly_stk_hi).
       afn_spec_cf does NOT supply it, so the RECORD carries it, as fi_pre's conjunct next to XP (the caller's frame
       lies above the callee's entry sp).
   (c) fpre's `raZ regs < YM05.alloc_ceiling`: afn_spec_cf does not supply it either, so the RECORD carries it
       (Section r takes {rc} for it) and afn_spec_cf_of_text passes it to the text. fpre's fifth conjunct, frm_zero
       of the entry fcsr, IS afn_spec_cf's last premise, so the record does not carry it.
   THE INTERFACE PREMISES THE ADAPTER DROPS (the text is stronger): the context membership, the frames bound and
   LIB_ROOM.
   INSTANCES: section 4, the four accessors of the #102 callee set that PwAllocSurfB walks (fuzz_alloc_live, _count,
   _peak_reset, _peak) at the interface's entries (PresetCfnB.v :743-746), plus fuzz_alloc_fail at its listing entry
   (no record entry: it is not a callee of LLVMFuzzerTestOneInput, PresetCfnB.v :220-243), all at the generic
   room-live class {RL} as the texts state it (PwAllocSurfB's _rl theorems), and check_bounded_alloc at the
   interface's entry from the kit's text at ARc, a PREMISE of that one entry: its walk, a Theorem Labs lane's
   lib/B/Prog/CheckBoundedAllocB.v (check_bounded_alloc_holds_B), is not in this tree; on #102 the record's
   pcc_check_bounded_alloc field is that text itself, so the walk discharges the field with no bridge. Section 5,
   pcc_stack_malloc_of_fcapi from a Theorem Labs lane's FCapiCfB.preset_aa_stack_malloc_cf_B (lib/AU/FCapiCfB.v blob
   d336a6a6da04): the CF form astack_malloc_realizes_cf; the #102 record's pcc_stack_malloc field (:989-990) is the
   MEMNORM-KEEPING astack_malloc_realizes_cfm, which the cf form does not give (its supplier is a Theorem Labs lane's
   frame-class lane, lib/AU/FCm01xm.v, not in this tree). Section 6, the four #102 record fields at
   RL := prh_room_live_a8 (PwAllocSurfB's tops).
   NOT HERE, of the #102 callee set: fuzz_alloc_most, fuzz_alloc_ran_out and fuzz_alloc_ran_out_reset (no walk in
   these files; a Theorem Labs lane's lib/B/Prog/FuzzAllocAccB102.v walks the two ran_out ones on B'), and the program
   callees other than check_bounded_alloc. *)
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
(* frm_zero (the kit's fpre fifth conjunct, afn_spec_cf's last premise); used qualified *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B Require Import PRH_ImgB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_FnAlloc PRH_FnCheck CfParamsPreset.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YF0m.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require PresetCfnB FCapiCfB.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.B.Prog Require Import PwAllocSurfB.
Import ListNotations.
Local Open Scope Z_scope.

(* the interface's fi_fp / fi_pre / fi_post types (PresetCfnB.v :690-693; fi_fp reads the callee's entry memory) *)
Definition prw_fp_t : Type := bvmap 5 word -> (word -> option byte) -> alayout -> astate -> list (Z * Z).
Definition prw_pre_t : Type :=
  alayout -> astate -> list Z -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.
Definition prw_post_t : Type :=
  bvmap 5 word -> alayout -> astate -> list Z -> world tfibsegs -> (word -> option byte) -> Model ->
  alayout -> astate -> list Z -> world tfibsegs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop.

(* ==== 1. the record of a text, carrying the state conjunct XP, the stack gap and the raZ bound ==== *)
Section r. Context {rc : YM05.RunCeil}.
Variable XP : alayout -> astate -> Prop.
(* fi_pre carries THREE facts afn_spec_cf does not supply: the state conjunct XP (xs_placed_cf, the walks' ARx), the
   kit's stack-top gap `spZ regs + 64 <= ly_stk_hi ly`, and `raZ regs < YM05.alloc_ceiling` (fpre's fourth conjunct,
   from a Theorem Labs lane's two put-family measurements: it makes the put family's CASE 2, o = spZ regs + 8 with [o - 16] the
   callee's own saved ra, closable, and only if the bound is visible in the record the walk unpacks) *)
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
  : PresetCfnB.fn_iface :=
  PresetCfnB.MkFn STK ctx fr bud FP (prw_fi_pre X P) (prw_fi_post X P Q).
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
   the entry registers and memory, as the interface's fi_fp is. The premise is the kit f97's fpre, its five conjuncts in
   its order (PRH_Base.v :588-610), so a text's fpre is this premise by conversion at PA := PI_prog_B *)
Definition prw_text (pc STK : Z) (FP : prw_fp_t) (X : Type)
  (P : X -> prw_pre_t) (Q : X -> prw_post_t) : Prop :=
  forall ly S Hp (W : world segs) regs mem md ch (x : X),
  afn_pre_x segs B prw_ARx STK ly S Hp W regs mem md ch /\
  PRH_Base.arodata_okP segs (@pa_relro_lo rc L PA) (@pa_relro_hi rc L PA) B (aview segs (w_H W) mem) /\
  spZ regs + 64 <= ly_stk_hi ly /\ raZ regs < YM05.alloc_ceiling /\ YK0o.frm_zero (@YK11.fp_csr fx) ->
  P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs pc regs mem md)
    (apost_base_x (SK := PresetCfnB.preset_sink_head) segs B (@PRH_Base.prh_pst PresetCfnB.preset_prh_img) prw_ARx
       STK (FP regs mem ly S) regs ly S Hp W mem md (Q x regs ly S Hp W mem md)).

(* THE BRIDGE: a text in the schema discharges the interface's callee contract for its record *)
Lemma afn_spec_cf_of_text : forall pc STK ctx fr bud FP (X : Type) (P : X -> prw_pre_t) (Q : X -> prw_post_t),
  prw_text pc STK FP X P Q ->
  PresetCfnB.afn_spec_cf (L := L) (PA := PA) B pc (prw_fn XP STK ctx fr bud FP X P Q).
Proof.
intros pc STK ctx fr bud FP X P Q T.
unfold PresetCfnB.afn_spec_cf, prw_fn.
cbn [PresetCfnB.fi_stk PresetCfnB.fi_ctx PresetCfnB.fi_frames PresetCfnB.fi_budget PresetCfnB.fi_fp
  PresetCfnB.fi_pre PresetCfnB.fi_post].
(* #102's afn_spec_cf: the pre, the context, the frames bound, the read-only view, LIB_ROOM, fi_pre, frm_zero *)
intros ly S Hp W regs mem md ch Hpre _ _ Haro _ [HX [Hsp [Hra [x Hx]]]] Hfz.
unfold PresetCfnB.afn_pre_cf, afn_pre_x in Hpre.
destruct Hpre as [HAR Hrest].
assert (Hpre' : afn_pre_x segs B prw_ARx STK ly S Hp W regs mem md ch).
{ unfold afn_pre_x, prw_ARx. exact (conj (conj HAR HX) Hrest). }
eapply SRr_mono; [exact (T ly S Hp W regs mem md ch x (conj Hpre' (conj Haro (conj Hsp (conj Hra Hfz)))) Hx) |].
intros W' c' _ Hpost.
(* the interface's callee post is the float form (PresetCfnB header item (9)): this text leaves the float state alone,
   so YCbqG.apost_base_x_F gives it from the plain form at the entry rounding mode 0 (Hfz) *)
unfold PresetCfnB.apost_base_cfF. apply YCbqG.apost_base_x_F; [exact Hfz |].
unfold apost_base_x, ajournal_x in *.
destruct Hpost as (ly' & S' & Hp' & regs' & mem' & md' & k & Hc & Hj & Hr & HQ).
destruct Hj as [[HAR' HX'] Hj].
exists ly', S', Hp', regs', mem', md', k.
split; [exact Hc |]. split; [exact (conj HAR' Hj) |]. split; [exact Hr |].
unfold prw_fi_post. split; [exact HX' |]. exists x. split; [exact Hx | exact HQ].
Qed.
End b.

(* ==== 3. the five accessor texts in the schema: their tuples, premises and posts, VERBATIM from this tree's
   lib/A/PRH_FnAlloc.v :109-163 (the kit f97: the ledger's most / own fields, the m-form post fpostm = fpost at fQmn mem Q,
   S' = S), over the same section context, and one conversion lemma each (destructure the tuple, apply the text) ==== *)
Definition prwB_led : Type := (list (Z * Z) * Z * Z * Z * Z * Z * Z)%type.

Section q. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.

Definition prwB_P (x : prwB_led) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) : Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own.
Definition prwB_P_fail (y : prwB_led * Z) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  let '(x, k) := y in prwB_P x ly S Hp W regs mem md /\ getr regs 10 = w64 k /\ 0 <= k < 2 ^ 64.

Definition prwB_Q_live (x : prwB_led) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in
  fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
    (room_live_cf S -> room_live_cf S') /\
    getr regs' 10 = w64 (Ledger.lsum Lam) /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
    prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own).
Definition prwB_Q_peak (x : prwB_led) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in
  fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
    (room_live_cf S -> room_live_cf S') /\
    getr regs' 10 = w64 peak /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
    prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own).
Definition prwB_Q_peak_reset (x : prwB_led) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in
  fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
    (room_live_cf S -> room_live_cf S') /\
    Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
    prh_ledger B ly' S' Hp' W' mem' Lam (Ledger.lsum Lam) cnt fail ran most own).
Definition prwB_Q_count (x : prwB_led) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  let '(Lam, peak, cnt, fail, ran, most, own) := x in
  fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
    (room_live_cf S -> room_live_cf S') /\
    getr regs' 10 = w64 cnt /\ Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
    prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own).
Definition prwB_Q_fail (y : prwB_led * Z) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  let '((Lam, peak, cnt, fail, ran, most, own), k) := y in
  fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
    (room_live_cf S -> room_live_cf S') /\
    Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\
    prh_ledger B ly' S' Hp' W' mem' Lam peak cnt (if k <? SIZE_MAXZ - cnt then cnt + k else SIZE_MAXZ) ran most own).

Lemma prwB_live_text : forall ARx SK, tfuzz_alloc_live_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwB_led),
  fpre B ARx STK_fuzz_alloc_live ly S Hp W regs mem md ch -> prwB_P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_live) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_live [] regs ly S Hp W mem md (prwB_Q_live x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[Lam peak] cnt] fail] ran] most] own] H1 H2.
exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran most own H1 H2).
Qed.
Lemma prwB_peak_text : forall ARx SK, tfuzz_alloc_peak_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwB_led),
  fpre B ARx STK_fuzz_alloc_peak ly S Hp W regs mem md ch -> prwB_P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_peak) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_peak [] regs ly S Hp W mem md (prwB_Q_peak x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[Lam peak] cnt] fail] ran] most] own] H1 H2.
exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran most own H1 H2).
Qed.
Lemma prwB_peak_reset_text : forall ARx SK, tfuzz_alloc_peak_reset_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwB_led),
  fpre B ARx STK_fuzz_alloc_peak_reset ly S Hp W regs mem md ch -> prwB_P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_peak_reset) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_peak_reset [] regs ly S Hp W mem md
       (prwB_Q_peak_reset x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[Lam peak] cnt] fail] ran] most] own] H1 H2.
exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran most own H1 H2).
Qed.
Lemma prwB_count_text : forall ARx SK, tfuzz_alloc_count_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwB_led),
  fpre B ARx STK_fuzz_alloc_count ly S Hp W regs mem md ch -> prwB_P x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_count) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_count [] regs ly S Hp W mem md (prwB_Q_count x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[Lam peak] cnt] fail] ran] most] own] H1 H2.
exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran most own H1 H2).
Qed.
Lemma prwB_fail_text : forall ARx SK, tfuzz_alloc_fail_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (y : prwB_led * Z),
  fpre B ARx STK_fuzz_alloc_fail ly S Hp W regs mem md ch -> prwB_P_fail y ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_fuzz_alloc_fail) regs mem md)
    (fpost B ARx SK STK_fuzz_alloc_fail [] regs ly S Hp W mem md (prwB_Q_fail y regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[[Lam peak] cnt] fail] ran] most] own] k] H1 [H2 [H3 H4]].
(* the text binds k before most own (PRH_FnAlloc.v :155) *)
exact (T ly S Hp W regs mem md ch Lam peak cnt fail ran k most own H1 H2 H3 H4).
Qed.

(* check_bounded_alloc's text (PRH_FnCheck.v :523-532, blob 9ecd8eb167c6): its tuple, premises and post, VERBATIM *)
Definition prwB_cba : Type := (Z * Z * list (Z * Z) * Z * Z * Z * Z * Z * Z)%type.
Definition prwB_P_cba (x : prwB_cba) (ly : alayout) (S : astate) (Hp : list Z) (W : world segs)
  (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) : Prop :=
  let '(held, size, Lam, peak, cnt, fail, ran, most, own) := x in
  getr regs 10 = w64 held /\ getr regs 11 = w64 size /\
  0 <= held < 2 ^ 64 /\ 0 <= size <= 2 ^ 40 /\ held <= PJ_ALLOC_BOUND size /\
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own.
Definition prwB_Q_cba (x : prwB_cba) (regs : bvmap 5 word) (ly : alayout) (S : astate) (Hp : list Z)
  (W : world segs) (mem : word -> option byte) (md : Model)
  : alayout -> astate -> list Z -> world segs -> bvmap 5 word -> (word -> option byte) -> Model -> Prop :=
  let '(held, size, Lam, peak, cnt, fail, ran, most, own) := x in
  fQmn mem (fun ly' S' Hp' W' regs' mem' md' =>
    Hp' = Hp /\ S' = S /\ ablocks B ly' S' = ablocks B ly S /\ (room_live_cf S -> room_live_cf S') /\
    prh_ledger B ly' S' Hp' W' mem' Lam peak cnt fail ran most own).
Lemma prwB_cba_text : forall ARx SK, tcheck_bounded_alloc_specX B ARx SK ->
  forall ly S Hp (W : world segs) regs mem md ch (x : prwB_cba),
  fpre B ARx STK_check_bounded_alloc ly S Hp W regs mem md ch -> prwB_P_cba x ly S Hp W regs mem md ->
  SRr segs W (cfg_at segs (pa_sigma AS_check_bounded_alloc) regs mem md)
    (fpost B ARx SK STK_check_bounded_alloc [] regs ly S Hp W mem md (prwB_Q_cba x regs ly S Hp W mem md)).
Proof.
intros ARx SK T ly S Hp W regs mem md ch [[[[[[[[held size] Lam] peak] cnt] fail] ran] most] own]
  H1 [H2 [H3 [H4 [H5 [H6 H7]]]]].
exact (T ly S Hp W regs mem md ch held size Lam peak cnt fail ran most own H1 H2 H3 H4 H5 H6 H7).
Qed.
End q.

(* ==== 4. the instances at image B': PA := PI_prog_B, PI := prh_img_B (= the interface's preset_prh_img), preset's
   CfParams, the interface's sink head, XP := xs_placed_cf. Each record entry is the bridge applied to the walk's
   Qed theorem; the entry address is the interface's (PresetCfnB.v :731-747), equal to the listing's by computation
   (a wrong-image constant would fail here, not pass). ---- *)
Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {RL : PrhRoomLive}.
#[local] Abbreviation CP := CfParams_preset.
#[local] Abbreviation PIA := prh_img_B.
#[local] Abbreviation SEGS := (@pa_segs _ B_prog_listing PI_prog_B).
#[local] Abbreviation SIGMA := (@pa_sigma _ B_prog_listing PI_prog_B).
#[local] Abbreviation SKA := PresetCfnB.preset_sink_head.
#[local] Abbreviation XPc := (fun (ly : alayout) (S : astate) => xs_placed_cf ly S).
Variable B : asyms.
#[local] Abbreviation ARc := (fun ly S Hp W mem md => ARcf (cp := CP) SEGS B ly S Hp W mem md /\ xs_placed_cf ly S).
(* PST_ok's B half (PwAllocSurfB.v Section T). PROVED in lib/B/Prog/PwPstUnownedB.v (pst_unowned_B, pst_unowned_TfibB),
   which Requires this file and closes the entries that take it at B := YD2l.TfibB (see the header) *)
Hypothesis PST_unowned : forall a, Exists (in_zr a) (@prh_pst PIA) -> ~ Exists (in_zr a) (as_owned_static B).

#[local] Abbreviation nofp :=
  (fun (_ : bvmap 5 word) (_ : word -> option byte) (_ : alayout) (_ : astate) => @nil (Z * Z)).

(* the records (ctx, fr, bud: the record's, any value; DW: the run's data words, read by no accessor text) *)
Definition prwB_F_live (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) (DW : list Z) : PresetCfnB.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_live (PI := PIA)) ctx fr bud nofp prwB_led
    (prwB_P (cp := CP) (PI := PIA) (PA := PI_prog_B) B) (prwB_Q_live (cp := CP) (PI := PIA) (PA := PI_prog_B) B).
Definition prwB_F_peak (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) (DW : list Z) : PresetCfnB.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_peak (PI := PIA)) ctx fr bud nofp prwB_led
    (prwB_P (cp := CP) (PI := PIA) (PA := PI_prog_B) B) (prwB_Q_peak (cp := CP) (PI := PIA) (PA := PI_prog_B) B).
Definition prwB_F_peak_reset (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) (DW : list Z)
  : PresetCfnB.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_peak_reset (PI := PIA)) ctx fr bud nofp prwB_led
    (prwB_P (cp := CP) (PI := PIA) (PA := PI_prog_B) B)
    (prwB_Q_peak_reset (cp := CP) (PI := PIA) (PA := PI_prog_B) B).
Definition prwB_F_count (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) (DW : list Z) : PresetCfnB.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_count (PI := PIA)) ctx fr bud nofp prwB_led
    (prwB_P (cp := CP) (PI := PIA) (PA := PI_prog_B) B) (prwB_Q_count (cp := CP) (PI := PIA) (PA := PI_prog_B) B).
Definition prwB_F_fail (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) (DW : list Z) : PresetCfnB.fn_iface :=
  prw_fn XPc (STK_fuzz_alloc_fail (PI := PIA)) ctx fr bud nofp (prwB_led * Z)
    (prwB_P_fail (cp := CP) (PI := PIA) (PA := PI_prog_B) B)
    (prwB_Q_fail (cp := CP) (PI := PIA) (PA := PI_prog_B) B).

(* the interface's typed entries equal the listing's (by computation) *)
Lemma prwB_pc_live : PresetCfnB.A_fuzz_alloc_live = SIGMA AS_fuzz_alloc_live.
Proof. vm_compute. reflexivity. Qed.
Lemma prwB_pc_peak : PresetCfnB.A_fuzz_alloc_peak = SIGMA AS_fuzz_alloc_peak.
Proof. vm_compute. reflexivity. Qed.
Lemma prwB_pc_peak_reset : PresetCfnB.A_fuzz_alloc_peak_reset = SIGMA AS_fuzz_alloc_peak_reset.
Proof. vm_compute. reflexivity. Qed.
Lemma prwB_pc_count : PresetCfnB.A_fuzz_alloc_count = SIGMA AS_fuzz_alloc_count.
Proof. vm_compute. reflexivity. Qed.

(* the four #102 callees among the accessors that PwAllocSurfB walks, in the schema, from the Qed walks at the
   generic room-live class (PwAllocSurfB's _rl theorems) *)
Theorem pcc_fuzz_alloc_live_of_walk : forall ctx fr bud (DW : list Z),
  PresetCfnB.afn_spec_cf (L := B_prog_listing) (PA := PI_prog_B) B PresetCfnB.A_fuzz_alloc_live
    (prwB_F_live ctx fr bud DW).
Proof.
intros ctx fr bud DW. rewrite prwB_pc_live. unfold prwB_F_live.
apply (afn_spec_cf_of_text (L := B_prog_listing) (PA := PI_prog_B) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwB_live_text (cp := CP) (PI := PIA) (PA := PI_prog_B) B ARc SKA
  (fuzz_alloc_live_holds_rl (SK := SKA) B) ly S Hp W regs mem md ch x H1 H2).
Qed.

Theorem pcc_fuzz_alloc_peak_of_walk : forall ctx fr bud (DW : list Z),
  PresetCfnB.afn_spec_cf (L := B_prog_listing) (PA := PI_prog_B) B PresetCfnB.A_fuzz_alloc_peak
    (prwB_F_peak ctx fr bud DW).
Proof.
intros ctx fr bud DW. rewrite prwB_pc_peak. unfold prwB_F_peak.
apply (afn_spec_cf_of_text (L := B_prog_listing) (PA := PI_prog_B) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwB_peak_text (cp := CP) (PI := PIA) (PA := PI_prog_B) B ARc SKA
  (fuzz_alloc_peak_holds_rl (SK := SKA) B) ly S Hp W regs mem md ch x H1 H2).
Qed.

Theorem pcc_fuzz_alloc_peak_reset_of_walk : forall ctx fr bud (DW : list Z),
  PresetCfnB.afn_spec_cf (L := B_prog_listing) (PA := PI_prog_B) B PresetCfnB.A_fuzz_alloc_peak_reset
    (prwB_F_peak_reset ctx fr bud DW).
Proof.
intros ctx fr bud DW. rewrite prwB_pc_peak_reset. unfold prwB_F_peak_reset.
apply (afn_spec_cf_of_text (L := B_prog_listing) (PA := PI_prog_B) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwB_peak_reset_text (cp := CP) (PI := PIA) (PA := PI_prog_B) B ARc SKA
  (fuzz_alloc_peak_reset_holds_rl (SK := SKA) B PST_unowned) ly S Hp W regs mem md ch x H1 H2).
Qed.

Theorem pcc_fuzz_alloc_count_of_walk : forall ctx fr bud (DW : list Z),
  PresetCfnB.afn_spec_cf (L := B_prog_listing) (PA := PI_prog_B) B PresetCfnB.A_fuzz_alloc_count
    (prwB_F_count ctx fr bud DW).
Proof.
intros ctx fr bud DW. rewrite prwB_pc_count. unfold prwB_F_count.
apply (afn_spec_cf_of_text (L := B_prog_listing) (PA := PI_prog_B) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwB_count_text (cp := CP) (PI := PIA) (PA := PI_prog_B) B ARc SKA
  (fuzz_alloc_count_holds_rl (SK := SKA) B) ly S Hp W regs mem md ch x H1 H2).
Qed.

(* fuzz_alloc_fail: no record entry (it is not a callee of LLVMFuzzerTestOneInput, PresetCfnB.v :220-243); the same
   bridge at its listing entry *)
Theorem afn_fuzz_alloc_fail_of_walk : forall ctx fr bud (DW : list Z),
  PresetCfnB.afn_spec_cf (L := B_prog_listing) (PA := PI_prog_B) B (SIGMA AS_fuzz_alloc_fail)
    (prwB_F_fail ctx fr bud DW).
Proof.
intros ctx fr bud DW. unfold prwB_F_fail.
apply (afn_spec_cf_of_text (L := B_prog_listing) (PA := PI_prog_B) B XPc).
intros ly S Hp W regs mem md ch y H1 H2.
exact (prwB_fail_text (cp := CP) (PI := PIA) (PA := PI_prog_B) B ARc SKA
  (fuzz_alloc_fail_holds_rl (SK := SKA) B PST_unowned) ly S Hp W regs mem md ch y H1 H2).
Qed.

(* ---- check_bounded_alloc: the bridge at the interface's entry from the kit's text at ARx := ARc (premise T_cba). Its
   walk, a Theorem Labs lane's CheckBoundedAllocB.check_bounded_alloc_holds_B (the kit's text at any ARx with the engine laws
   LAWS : AR_laws_x SEGS B ARx HL; at ARc from a8's AR_laws_ok_cf lifted by YGcallcf.v's AR_laws_x_xs, exactly as
   PwAllocSurfB.v Section T discharges the accessors' LAWS), is not in this tree; a consumer passes it ---- *)
Definition prwB_F_check_bounded_alloc (ctx : list (list Z)) (fr : Z) (bud : bvmap 5 word -> Z) (DW : list Z)
  : PresetCfnB.fn_iface :=
  prw_fn XPc (STK_check_bounded_alloc (PI := PIA)) ctx fr bud nofp prwB_cba
    (prwB_P_cba (cp := CP) (PI := PIA) (PA := PI_prog_B) B)
    (prwB_Q_cba (cp := CP) (PI := PIA) (PA := PI_prog_B) B).
Lemma prwB_pc_check_bounded_alloc : PresetCfnB.A_check_bounded_alloc = SIGMA AS_check_bounded_alloc.
Proof. vm_compute. reflexivity. Qed.

Theorem pcc_check_bounded_alloc_of_text :
  tcheck_bounded_alloc_specX (cp := CP) (PI := PIA) (PA := PI_prog_B) B ARc SKA ->
  forall ctx fr bud (DW : list Z),
  PresetCfnB.afn_spec_cf (L := B_prog_listing) (PA := PI_prog_B) B PresetCfnB.A_check_bounded_alloc
    (prwB_F_check_bounded_alloc ctx fr bud DW).
Proof.
intros T_cba ctx fr bud DW. rewrite prwB_pc_check_bounded_alloc. unfold prwB_F_check_bounded_alloc.
apply (afn_spec_cf_of_text (L := B_prog_listing) (PA := PI_prog_B) B XPc).
intros ly S Hp W regs mem md ch x H1 H2.
exact (prwB_cba_text (cp := CP) (PI := PIA) (PA := PI_prog_B) B ARc SKA T_cba ly S Hp W regs mem md ch x H1 H2).
Qed.

(* ==== 5. pcc_stack_malloc in the CF form, from a Theorem Labs lane's FCapiCfB.preset_aa_stack_malloc_cf_B: the allocator laws
   are a8's AR_laws_ok_cf (YG0lawscf.v), the class set is [0; 1; 3] by computation; TfibSyms B (the image's symbol
   facts of B) stays a premise, as in FCapiCfB. NOT the #102 record's field (PresetCfnB.v :989-990, the memnorm-keeping
   astack_malloc_realizes_cfm; astack_malloc_realizes_cfm_cf goes only from cfm to cf) ---- *)
Theorem pcc_stack_malloc_of_fcapi : YF0m.TfibSyms B ->
  forall cid, In cid (@cf_fs_classes CP) ->
  astack_malloc_realizes_cf (fx := fx) (rc := rc) (ci := ci) (cp := CP) tfibsegs B cid.
Proof.
intros TB cid Hc.
assert (E : @cf_fs_classes CP = [0; 1; 3]) by reflexivity.
rewrite E in Hc.
exact (FCapiCfB.preset_aa_stack_malloc_cf_B (cp := CP) B (AR_laws_ok_cf (cp := CP) tfibsegs B) TB cid Hc).
Qed.

(* ==== 6. THE #102 CALLEE RECORD's fields for the four accessors this file's walks discharge (PresetCfnB.v
   preset_callee_contracts :976-983, D1): the kit's texts themselves at every float state fy, at the record's
   PI := preset_prh_img (= prh_img_B), RL := prh_room_live_a8, ARx := iface_ARx (:942-945, = ARc by conversion),
   SK := preset_sink_head. Each is PwAllocSurfB.v's top at fx := fy; peak_reset takes PST_unowned (closed at
   B := YD2l.TfibB in PwPstUnownedB.v). ==== *)
Theorem pcc102_fuzz_alloc_live_of_walk : forall fy : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_live_specX fy rc CP PresetCfnB.preset_prh_img (@prh_room_live_a8 CP)
    B_prog_listing PI_prog_B B (PresetCfnB.iface_ARx (L := B_prog_listing) (PA := PI_prog_B) B) SKA.
Proof. intros fy. exact (fuzz_alloc_live_holds (fx := fy) (rc := rc) (SK := SKA) B). Qed.

Theorem pcc102_fuzz_alloc_count_of_walk : forall fy : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_count_specX fy rc CP PresetCfnB.preset_prh_img (@prh_room_live_a8 CP)
    B_prog_listing PI_prog_B B (PresetCfnB.iface_ARx (L := B_prog_listing) (PA := PI_prog_B) B) SKA.
Proof. intros fy. exact (fuzz_alloc_count_holds (fx := fy) (rc := rc) (SK := SKA) B). Qed.

Theorem pcc102_fuzz_alloc_peak_reset_of_walk : forall fy : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_peak_reset_specX fy rc CP PresetCfnB.preset_prh_img (@prh_room_live_a8 CP)
    B_prog_listing PI_prog_B B (PresetCfnB.iface_ARx (L := B_prog_listing) (PA := PI_prog_B) B) SKA.
Proof. intros fy. exact (fuzz_alloc_peak_reset_holds (fx := fy) (rc := rc) (SK := SKA) B PST_unowned). Qed.

Theorem pcc102_fuzz_alloc_peak_of_walk : forall fy : YK11.FPState,
  @PRH_FnAlloc.tfuzz_alloc_peak_specX fy rc CP PresetCfnB.preset_prh_img (@prh_room_live_a8 CP)
    B_prog_listing PI_prog_B B (PresetCfnB.iface_ARx (L := B_prog_listing) (PA := PI_prog_B) B) SKA.
Proof. intros fy. exact (fuzz_alloc_peak_holds (fx := fy) (rc := rc) (SK := SKA) B). Qed.
End w.
