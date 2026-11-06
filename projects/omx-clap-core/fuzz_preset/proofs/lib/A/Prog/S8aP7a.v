(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/Prog/S8aNumE.v, with its module paths and module names changed; 2503 of its 2694 lines of code are new or changed and 1724 lines of the source are left out. *)
(* fuzz_preset, slice S8a EX-VALUE, image A' (asan #102, pin 1be0f53d, unstripped twin bff8519b): sub-lane S8aP7a of piece 7
   (ev_item_step) of the walk of ex_value (A' 0x832a4), in the srealizes / SRr form, against the cut interface of
   lib/A/Prog/S8aItems.v (S8aP7). Hand: h-walk-ctrl's S8aP7a.
   - p7a TRANSPORT KIT: ev_mid across a straight stretch (p7a_mid_frame, FRAME's ev_mid_frame widened) and across a
     caller-window call (p7a_mid_call); both general, used by segment 2 and by S8aP7's segment 4.
   - SEGMENT 2 (ev7_seg2_A, S8aItems.v ev7_seg2_stmt): C_KID 0x83878 -> C_KEY 0x839a0 on the object path, or the
     refusal join 0x83b54 -> P_EXIT 0x83d48.
   Section hypotheses: LAWS, WS, PSTI (S8aItemsWalk.v's header, copied verbatim; HSH derived from LAWS), STR (S8b),
   SCMP, BLKAM8 (each with its owner below). SCMP: STAND-IN, owner c-libc-stdio. HYPOTHESIS CHANGE (stronger:
   adds the memnorm keep; arodata_okP form). Supplier ps_strcmp_xrom_A @ c-libc-stdio-presetstr-ro 45e489ec67c7; its
   YGcallMxmn cites PresetRodata.arodata_okP, and so does the engine of record here (s1b bb085d091bbe, YGcallMxmn blob
   b47cf7942c3d, which Requires lib/Spec/PresetRodata.v 4eb7e95e7e93 and has no local copy): one arodata_okP home.
   HFHULL and HSTK64 are DELETED (the S8a memnorm interface's contract item 4): p7a_frame_hull / p7a_stk64 derive them
   from LAWS (AR_laws_x field 18, as S8aEntry.v's eve_frame_hull / eve_stk64). ROM is DELETED: its one use was the
   rom_view premise of the strcmp row, and the xrom row takes ev_pre's arodata_okP instead. BLK32 is DELETED: its one
   use (keys[n]'s kx + 1 < 2 ^ 32) is the kit's pj_cstrR conjunct (PRH_Reader.v:113). No ADDRESS literal:
   addresses are pa_sigma / pa_val of PAImg_prog.v; each block's numerals are classified in its comment.
   MEMNORM (S8aIface.v: ev_pre's and ev_mid's last conjunct `YAkMemnorm.memnorm segs mem`, walkkit old-pin
   be60d536d2af): kept across every runner segment by YC1fPx's `*_inv` runners (P := YAkMemnorm.memnorm SEGS, laws
   YSRrMemnorm.srr_inv_laws_memnorm_k), across the ex_string call by tex_string_specX's fpostWm keep and across the
   strcmp call by YGcallMxmn.aj_strcmp_at_xrom's keep; p7a_mid_frame and p7a_mid_call take it at the new memory. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn
YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YK0o YCbqG.
(* the caller-window call rule is Reusable/YCbqGcallW.v's aj_call_xW (walkkit b77223726823's engine set) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop YGcfNames YG0dcf YGcallMx FCiface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog PRH_Base PRH_Img PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YCbqGcallW YGcallHull.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface S8aItems.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aModel.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require S8aWs.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YGcallMxmn YAkMemnorm YSRrMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.
(* the walk is at image A's PrhImg (frames, statics), as at its listing *)
#[local] Existing Instance prh_img_A.
#[local] Notation PI := prh_img_A.
#[local] Notation PA := (@PI_prog_A rc).
#[local] Notation PL := (PL_prog_A).
#[local] Notation SEGS := (@pa_segs _ A_prog_listing PA).
#[local] Notation VAL := (@pa_val _ A_prog_listing PA).
#[local] Notation SIGMA := (@pa_sigma _ A_prog_listing PA).
#[local] Notation BASE := (@pa_val _ A_prog_listing PA A_TEXT).
#[local] Notation PST := (prh_pst (PI := PI)).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
Context {RL : PrhRoomLive}.
(* the kit's allocator laws at ARx, at the harness head length cf_head (YCbqG.v journal 83da015952be; at ARx := ARcf
   this is YGcallcf.v's AR_laws_x_cf) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx cf_head.
(* the shared whitespace loop, PROVED (no longer a stand-in): WalkS8a's S8aWs.ev_ws_loop (ws-rawframe 91e4dffbfb7),
   whose only Section hypothesis is LAWS *)
Lemma WS : ev_ws_loop_spec_FIX (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (S8aWs.ev_ws_loop B ARx SK LAWS). Qed.
(* HSH is DERIVED (c-omx-hpreset 10:43Z): ev_hshadow_law is AR_laws_x's field alx_hshadow at hl := cf_head (journal
   83da015952be, YCbqG.v:163); S8aItems.v ev_hshadow_of_laws *)
Lemma HSH : ev_hshadow_law (L := A_prog_listing) (PA := PA) B ARx.
Proof. exact (ev_hshadow_of_laws B ARx LAWS). Qed.
(* STAND-IN: a Theorem Labs lane, the image binding of PrhImg: alloc.c's statics (prh_pst) are image bytes (true at prh_img_A: PRH_Img.v,
   below kLowMemEnd by pa_segs_low, so apart from the stack); without it a generic PrhImg could put them in `struct ex` *)
Hypothesis PSTI : forall z, Exists (in_zr z) PST -> in_img SEGS z.

(* ======== LOCAL KIT (EvItems) ======== *)

(* The CALL of a caller-window callee: YCbqGcallW.v aj_call_xW / aj_call_xWF over YCbqG's fp_sub_x, instantiated at the
   piece's float state. *)
Let ev_segs_low : forall a, in_img SEGS a -> 0 <= a < kLowMemEnd := @pa_segs_low _ A_prog_listing PA.




(* ======== END LOCAL KIT ======== *)

(* STAND-IN: slice S8b (h-hpreset-7-walk-S8b), K0's ex_string text, at every float state: the call runs at the piece's
   float state fxc, and tex_string_specX's cfg_at / fpostW are built at its implicit one *)
Hypothesis STR : forall fxc : YK11.FPState,
  tex_string_specX (fx := fxc) (cp := cp) (L := A_prog_listing) (PA := PA) B ARx SK.
(* STAND-IN, owner c-libc-stdio. HYPOTHESIS CHANGE (stronger: adds the memnorm keep; arodata_okP form). Supplier
   ps_strcmp_xrom_A @ c-libc-stdio-presetstr-ro 45e489ec67c7; it and the engine of record (s1b bb085d091bbe, YGcallMxmn
   blob b47cf7942c3d) both cite PresetRodata.arodata_okP (lib/Spec/PresetRodata.v 4eb7e95e7e93): one home. The strcmp
   row (YGcallMxmn.v astrcmp_realizes_xrom) at __wrap_strcmp, at every float state, at ev_pre's read-only bounds
   (fpre's arodata_okP, PRH_Base.v, converted by S8aItems.aro_prh_to_mxmn) *)
Hypothesis SCMP : forall fxc : YK11.FPState, YGcallMxmn.astrcmp_realizes_xrom (fx := fxc) SEGS B ARx (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) (SIGMA AS___wrap_strcmp).
(* (the chain stand-in CHA is gone at iface 67f35bb5f4bb: ev_pre's prhex_ch_apart conjunct gives it) *)
(* (HFHULL / HSTK64, the fake-frame and real-stack shadow hulls of a tree root after the `jal ex_string`, are DERIVED
   from LAWS since the S8a memnorm interface: p7a_frame_hull / p7a_stk64 below. ROM is gone with the strcmp row's
   rom_view premise. BLK32 (a live block is shorter than 2 ^ 32, for keys[n]'s kx + 1 < 2 ^ 32) is gone: the kit's
   pj_cstrR carries `Z.of_nat (length s) + 1 < 2 ^ 32` itself, PRH_Reader.v:113.) *)
(* STAND-IN, owner h-mani-a8 / c-omx-alloc, S8aNumE.v CUTFIX_blk_amem8 verbatim (origin/cold/h-s8a-number-sweep
   1fdf0c60bc6a :576-577; the other lanes' text lib/B/Prog/ExvB_Stmt.v eh_blk_amem8): a live block is a region of the string
   rows' amem_range8. The strcmp row (YGcallMxmn.v astrcmp_realizes_xrom, as YGcallMx.v astrcmp_realizes_x) asks amem_range8 for
   keys[n] and the scratch; no AR_laws_x field gives it (alx_blocks gives in_app only). At the preset instance:
   block_amem_range8_cf (h-mani-a8, YGcfBlockRange.v). *)
Hypothesis BLKAM8 : forall ly S Hp W mem md p n,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> YGcallMx.amem_range8 p (req_size n).

(* ======== p7a TRANSPORT KIT ========
   ev_mid (S8aIface.v:169) across what piece 7's segment 2 does between its cuts:
   - p7a_mid_frame: a stretch at one allocator state whose changed bytes Wr lie in [S1 - 2 ESTACK, S1 + 152) or in
     the written cells of `struct ex`. It is lane FRAME's ev_mid_frame (S8aItemsWalk.v at 638cd0ea026, :304-436)
     with two changes: the stack part of Wr is widened from [S1, S1 + 152) to [S1 - 2 ESTACK, S1 + 152) (the strcmp
     call writes its window [S1 - 2 ESTACK, S1); that window lies in [sp0 - STK, sp0), which the tree's footprint
     misses, and above alloc_ceiling + ESTACK, by p7a_stk), and the frame premise is stated over aview (what a
     runtime call's text gives) instead of the raw restricted memory.
   - p7a_mid_call: a caller-window CALL (YCbqGcallW.v aj_call_xW / aj_call_xWF): the allocator state moves; the
     caller's journal is extended over the call, the callee's journal and its extension clause keep every byte ev_mid
     reads (blocks: its block clause; frames and their shadow: its frame clause; the stack at or above S1: its
     window clause or its stack clause), the shadow and presence facts come from the laws at the new state.
   The helpers p7a_stk / p7a_vm / p7a_av / p7a_garr8 / p7a_cstr / p7a_hdr / p7a_items_frame / p7a_mems_frame /
   p7a_nodeR_frame / p7a_sh_lt / p7a_ra / p7a_hull / p7a_rdword / p7a_bounds are FRAME's evf_* / ev_bounds (same sha,
   :104-301), the tree transport restated over a pointwise byte-and-writability premise (a call keeps writability
   only where it keeps the byte; FRAME's mem_grows is a property of one allocator state).
   Numerals (no ADDRESS): LENGTH 8 (a word's bytes; the shadow granule), 56 (a pj_value node), 256 and 32 (the
   prologue's `addi sp, sp, -256` and `andi sp, sp, -32`), 152 (the body's locals), 152 and 248 (EV_SAVED's lowest
   and highest offset), 8192 (= 2 ESTACK, the strcmp row's window), 3 (ESTACKs below the save area: p7a_stk), 2
   (the factor of 2 ESTACK; the radix of a shift), 16, 20, 32, 36 and 40 (struct ex: depth, differs, its size),
   4096 (the page every block and
   fake frame is above), 0 .. 7 (byte indices of a word), 1 (the frame class), 64 (fs_frame_bytes 0); DERIVED 287 =
   256 + 31 and 288 = 256 + 32 (the body's sp below the entry sp), 128 = fs_frame_bytes 1; WORD 44 and 47 and 64
   (exponents of the shadow span 2 ^ 44, the address-space bound 2 ^ 47 and the word range 2 ^ 64). *)

(* plain lia (S8aDisp.v's zl): the imported `lia` prunes hypotheses and can fail on goals over record projections *)
Ltac p7a_zl := Zify.zify; xlia zchecker.

(* ex_value's stack allowance at image A covers its save area plus three ESTACK (the strtod row is four) *)
Lemma p7a_stk : forall n, 3 * ESTACK + 288 <= STK_ex_value n.
Proof. intros n. unfold STK_ex_value. vm_compute (zmaxl _). vm_compute (pi_frame _). unfold ESTACK. lia. Qed.

(* ---- byte transports ---- *)
Lemma p7a_vm : forall (m m' : word -> option byte) a n v,
  (forall z, a <= z < a + Z.of_nat n -> mbyte SEGS m' z = mbyte SEGS m z) ->
  val_mem SEGS m a n v -> val_mem SEGS m' a n v.
Proof. intros m m' a n v E H k Hk. rewrite E by lia. exact (H k Hk). Qed.

Lemma p7a_av : forall H (m m' : word -> option byte) z,
  mbyte SEGS (mrestrict H m') z = mbyte SEGS (mrestrict H m) z -> aview SEGS H m' z = aview SEGS H m z.
Proof. intros H m m' z E. unfold aview. rewrite E. reflexivity. Qed.

Lemma p7a_garr8 : forall (m m' : word -> option byte) a l,
  (forall z, a <= z < a + Z.of_nat (length l) -> mbyte SEGS m' z = mbyte SEGS m z) ->
  garr8 SEGS m a l -> garr8 SEGS m' a l.
Proof.
intros m m' a l E H j Hj. destruct (H j Hj) as [Hv Hb]. split; [|exact Hb].
apply (p7a_vm m m'); [|exact Hv]. intros z Hz. apply E. lia.
Qed.

(* aview equality gives mbyte equality of the restricted memories (YCbq.v mbyte_of_aview) *)
Lemma p7a_vm_av : forall H H' (m m' : word -> option byte) a n v,
  (forall z, a <= z < a + Z.of_nat n -> aview SEGS H' m' z = aview SEGS H m z) ->
  val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v E. apply p7a_vm. intros z Hz. exact (mbyte_of_aview SEGS H H' m m' z (E z Hz)).
Qed.

Lemma p7a_garr_av : forall H H' (m m' : word -> option byte) a l,
  (forall z, a <= z < a + Z.of_nat (length l) -> aview SEGS H' m' z = aview SEGS H m z) ->
  garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H' m') a l.
Proof.
intros H H' m m' a l E. apply p7a_garr8. intros z Hz. exact (mbyte_of_aview SEGS H H' m m' z (E z Hz)).
Qed.

(* a writable byte off the image is present; aview equality carries presence, hence writability *)
Lemma p7a_wr_present : forall H (m : word -> option byte) z, 0 <= z < 2 ^ 64 -> ~ in_img SEGS z ->
  writable_at SEGS (mrestrict H m) z -> apresent H m z.
Proof.
intros H m z Hz Hni Hw. unfold writable_at, wview, mrestrict in Hw. unfold apresent.
assert (Hseg : find_segment SEGS (bv_unsigned (Z_to_bv 64 z)) 1 = None).
{ destruct (find_segment SEGS (bv_unsigned (Z_to_bv 64 z)) 1) as [seg|] eqn:Ef; [|reflexivity].
  exfalso. apply Hni. destruct (find_segment_hit _ _ _ _ Ef) as (Hin & Hlo & Hhi).
  rewrite unsigned_lit_small in Hlo, Hhi by lia. exists seg. split; [exact Hin|lia]. }
destruct (H (Z_to_bv 64 z)).
- rewrite Hseg in Hw. exfalso. apply Hw. reflexivity.
- split; [reflexivity|]. destruct (m (Z_to_bv 64 z)) as [b|].
  + exists b. reflexivity.
  + rewrite Hseg in Hw. exfalso. apply Hw. reflexivity.
Qed.

Lemma p7a_wr_av : forall H H' (m m' : word -> option byte) z, 0 <= z < 2 ^ 64 -> ~ in_img SEGS z ->
  aview SEGS H' m' z = aview SEGS H m z -> writable_at SEGS (mrestrict H m) z -> writable_at SEGS (mrestrict H' m') z.
Proof.
intros H H' m m' z Hz Hni E Hw. apply (apresent_writable SEGS).
exact (apresent_transfer SEGS H H' m m' z Hz Hni E (p7a_wr_present H m z Hz Hni Hw)).
Qed.

(* ---- the reader's tree: pj_nodeR is kept when its node bytes and its lblk blocks keep their value and their
   writability (P2) ---- *)
Definition p7a_P2 (m m' : word -> option byte) (z : Z) : Prop :=
  mbyte SEGS m' z = mbyte SEGS m z /\ (writable_at SEGS m z -> writable_at SEGS m' z).

Lemma p7a_cstr : forall (m m' : word -> option byte) lblk a k s,
  (forall z, a <= z < a + k -> p7a_P2 m m' z) ->
  PRH_Reader.pj_cstrR SEGS m lblk a k s -> PRH_Reader.pj_cstrR SEGS m' lblk a k s.
Proof.
intros m m' lblk a k s E (Hl & Hk & Hf & Hc & Hg). split; [exact Hl|]. split; [exact Hk|]. split; [exact Hf|].
split; [exact Hc|].
apply (p7a_garr8 m m'); [|exact Hg]. intros z Hz. apply E. rewrite length_app in Hz. cbn [length] in Hz. lia.
Qed.

Lemma p7a_hdr : forall (m m' : word -> option byte) p ty num str kids keys n cap,
  (forall z, p <= z < p + 56 -> p7a_P2 m m' z) ->
  PRH_Reader.pj_hdrR SEGS m p ty num str kids keys n cap -> PRH_Reader.pj_hdrR SEGS m' p ty num str kids keys n cap.
Proof.
intros m m' p ty num str kids keys n cap E
  ((Hal & Hrw) & (T0 & T1) & (N0 & N1) & (S0 & S1) & (K0 & K1) & (Y0 & Y1) & (C0 & C1) & (P0 & P1)).
assert (EV : forall b e, p <= b -> b + e <= p + 56 -> forall z, b <= z < b + e -> mbyte SEGS m' z = mbyte SEGS m z)
  by (intros b e Hb He z Hz; exact (proj1 (E z ltac:(lia)))).
split; [split; [exact Hal|intros x Hx; exact (proj2 (E x Hx) (Hrw x Hx))]|].
split; [split; [exact T0|apply (p7a_vm m m'); [apply (EV p 4); lia|exact T1]]|].
split; [split; [exact N0|apply (p7a_vm m m'); [apply (EV (p + 8) 8); lia|exact N1]]|].
split; [split; [exact S0|apply (p7a_vm m m'); [apply (EV (p + 16) 8); lia|exact S1]]|].
split; [split; [exact K0|apply (p7a_vm m m'); [apply (EV (p + 24) 8); lia|exact K1]]|].
split; [split; [exact Y0|apply (p7a_vm m m'); [apply (EV (p + 32) 8); lia|exact Y1]]|].
split; [split; [exact C0|apply (p7a_vm m m'); [apply (EV (p + 40) 8); lia|exact C1]]|].
split; [exact P0|apply (p7a_vm m m'); [apply (EV (p + 48) 8); lia|exact P1]].
Qed.

Definition p7a_nodeP (m m' : word -> option byte) (lblk : Z -> Z -> Prop) (t : PjTree.jv) : Prop :=
  forall p D, PRH_Reader.pj_nodeR SEGS m lblk p t D ->
  (forall z, (p <= z < p + 56 \/ exists b k, In (b, k) D /\ lblk b k /\ b <= z < b + k) -> p7a_P2 m m' z) ->
  PRH_Reader.pj_nodeR SEGS m' lblk p t D.

Lemma p7a_items_frame : forall (m m' : word -> option byte) lblk (items : list PjTree.jv),
  Forall (p7a_nodeP m m' lblk) items ->
  forall a Di, PRH_Reader.pj_itemsR (PRH_Reader.pj_nodeR SEGS m lblk) a items Di ->
  (forall z, a <= z < a + 56 * Z.of_nat (length items) -> p7a_P2 m m' z) ->
  (forall z, (exists b k, In (b, k) Di /\ lblk b k /\ b <= z < b + k) -> p7a_P2 m m' z) ->
  PRH_Reader.pj_itemsR (PRH_Reader.pj_nodeR SEGS m' lblk) a items Di.
Proof.
intros m m' lblk items IH. induction IH as [|u r Hu Hr IHr]; intros a Di H E1 E2;
  cbn [PRH_Reader.pj_itemsR] in H |- *.
- exact H.
- destruct H as (D1 & D2 & ED & H1 & H2). exists D1, D2. split; [exact ED|]. split.
  + apply (Hu a D1 H1). intros z [Hz|(b & k & Hin & Hl & Hz)].
    * apply E1. cbn [length]. lia.
    * apply E2. exists b, k. split; [rewrite ED; apply in_or_app; left; exact Hin|]. split; [exact Hl|exact Hz].
  + apply (IHr (a + 56) D2 H2).
    * intros z Hz. apply E1. cbn [length]. lia.
    * intros z (b & k & Hin & Hl & Hz). apply E2. exists b, k.
      split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

Lemma p7a_mems_frame : forall (m m' : word -> option byte) lblk (members : list (list Z * PjTree.jv)),
  Forall (fun mm => p7a_nodeP m m' lblk (snd mm)) members ->
  forall a ka Di, PRH_Reader.pj_memsR SEGS m lblk (PRH_Reader.pj_nodeR SEGS m lblk) a ka members Di ->
  (forall z, a <= z < a + 56 * Z.of_nat (length members) -> p7a_P2 m m' z) ->
  (forall z, ka <= z < ka + 8 * Z.of_nat (length members) -> p7a_P2 m m' z) ->
  (forall z, (exists b k, In (b, k) Di /\ lblk b k /\ b <= z < b + k) -> p7a_P2 m m' z) ->
  PRH_Reader.pj_memsR SEGS m' lblk (PRH_Reader.pj_nodeR SEGS m' lblk) a ka members Di.
Proof.
intros m m' lblk members IH. induction IH as [|mm r Hu Hr IHr]; intros a ka Di H E1 E2 E3.
- cbn [PRH_Reader.pj_memsR] in H |- *. exact H.
- destruct mm as [nm u]. cbn [PRH_Reader.pj_memsR snd] in H, Hu |- *.
  destruct H as (x & k & D1 & D2 & ED & (Hx0 & Hx) & Hc & H1 & H2).
  exists x, k, D1, D2. split; [exact ED|].
  split; [split; [exact Hx0|apply (p7a_vm m m'); [intros z Hz; apply E2; cbn [length]; lia|exact Hx]]|].
  split.
  { apply (p7a_cstr m m'); [|exact Hc]. intros z Hz. apply E3. exists x, k.
    split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz]. }
  split.
  + apply (Hu a D1 H1). intros z [Hz|(b & kk & Hin & Hl & Hz)].
    * apply E1. cbn [length]. lia.
    * apply E3. exists b, kk. split; [rewrite ED; right; apply in_or_app; left; exact Hin|].
      split; [exact Hl|exact Hz].
  + apply (IHr (a + 56) (ka + 8) D2 H2).
    * intros z Hz. apply E1. cbn [length]. lia.
    * intros z Hz. apply E2. cbn [length]. lia.
    * intros z (b & kk & Hin & Hl & Hz). apply E3. exists b, kk.
      split; [rewrite ED; right; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

Lemma p7a_nodeR_frame : forall (m m' : word -> option byte) lblk t, p7a_nodeP m m' lblk t.
Proof.
intros m m' lblk t.
induction t as [| | | txt bits | s | items IH | members IH] using PjTree.jv_ind'; unfold p7a_nodeP; intros p D H E;
  cbn [PRH_Reader.pj_nodeR] in H |- *;
  destruct H as (ND & AP & num & str & kids & keys & n & cap & HH & R);
  (split; [exact ND|]); (split; [exact AP|]);
  exists num, str, kids, keys, n, cap;
  (split; [apply (p7a_hdr m m'); [intros z Hz; apply E; left; exact Hz|exact HH]|]).
- exact R.
- exact R.
- exact R.
- destruct R as (R1 & R2 & R3 & R4 & R5 & kk & Hc & ED).
  do 5 (split; [assumption|]). exists kk. split; [|exact ED].
  apply (p7a_cstr m m'); [|exact Hc]. intros z Hz. apply E. right. exists str, kk.
  split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz].
- destruct R as (R2 & R3 & R4 & R5 & kk & Hc & ED).
  do 4 (split; [assumption|]). exists kk. split; [|exact ED].
  apply (p7a_cstr m m'); [|exact Hc]. intros z Hz. apply E. right. exists str, kk.
  split; [rewrite ED; left; reflexivity|]. split; [exact (proj1 Hc)|exact Hz].
- destruct R as (R1 & R2 & R3 & R4 & R5 & Di & ED & HI).
  do 5 (split; [assumption|]). exists Di. split; [exact ED|].
  apply (p7a_items_frame m m' lblk items IH kids Di HI).
  + intros z Hz. apply E. right. destruct R5 as [(Hc0 & _)|(Hc0 & Hl)]; [lia|].
    exists kids, (56 * cap). split; [|split; [exact Hl|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  + intros z (b & kk & Hin & Hl & Hz). apply E. right. exists b, kk.
    split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
- destruct R as (R1 & R2 & R3 & R4 & Di & ED & HM).
  do 4 (split; [assumption|]). exists Di. split; [exact ED|].
  apply (p7a_mems_frame m m' lblk members IH kids keys Di HM).
  + intros z Hz. apply E. right. destruct R4 as [(Hc0 & _)|(Hc0 & Hl & Hl2)]; [lia|].
    exists kids, (56 * cap). split; [|split; [exact Hl|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity.
  + intros z Hz. apply E. right. destruct R4 as [(Hc0 & _)|(Hc0 & Hl & Hl2)]; [lia|].
    exists keys, (8 * cap). split; [|split; [exact Hl2|lia]].
    rewrite ED. replace (cap =? 0) with false by (symmetry; apply Z.eqb_neq; lia). right. left. reflexivity.
  + intros z (b & kk & Hin & Hl & Hz). apply E. right. exists b, kk.
    split; [rewrite ED; apply in_or_app; right; exact Hin|]. split; [exact Hl|exact Hz].
Qed.

(* ---- shadow reads ---- *)
Lemma p7a_sh_lt : forall x, 0 <= x < 2 ^ 47 -> 0 <= shadow_addr x /\ shadow_addr x + 8 <= alloc_ceiling.
Proof.
intros x Hx. pose proof asan_consts as ((C1 & _) & _).
pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D2.
unfold shadow_addr, SHADOW_OFF. lia.
Qed.

(* a shadow byte of an address below 2 ^ 47 lies in no application range (in_app: below kLowShadowBeg or at or above
   kHighMemBeg = SHADOW_OFF + 2 ^ 44) *)
Lemma p7a_sh_app : forall x lo len, 0 <= x < 2 ^ 47 -> in_app lo len -> ~ (lo <= shadow_addr x < lo + len).
Proof.
intros x lo len Hx Ha. pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as D2.
unfold in_app, kLowShadowBeg, kHighMemBeg in Ha. unfold shadow_addr, SHADOW_OFF. lia.
Qed.

Lemma p7a_ra : forall (rd rd' : Z -> option Z) x n, 0 <= x -> x + n <= 2 ^ 47 ->
  (forall s, 0 <= s < alloc_ceiling -> rd' s = rd s) ->
  range_addressable rd SHADOW_OFF x n -> range_addressable rd' SHADOW_OFF x n.
Proof.
intros rd rd' x n Hx Hxn E H. apply (range_addressable_agree rd rd' SHADOW_OFF x n); [|exact H].
intros y Hy. destruct (p7a_sh_lt y ltac:(lia)) as [A0 A1]. apply E.
unfold shadow_of_addr. unfold shadow_addr in A0, A1. lia.
Qed.

Lemma p7a_hull : forall (rd rd' : Z -> option Z) x n, 0 <= x -> 0 < n -> x + n <= 2 ^ 47 ->
  (forall s, 0 <= s < alloc_ceiling -> rd' s = rd s) ->
  shadow_hull_vis rd x n -> shadow_hull_vis rd' x n.
Proof.
intros rd rd' x n Hx Hn Hxn E H s Hs.
destruct (p7a_sh_lt x ltac:(lia)) as [A0 _]. destruct (p7a_sh_lt (x + n - 1) ltac:(lia)) as [_ A1].
pose proof (Z.div_mod (shadow_addr x) 8 ltac:(lia)) as D0.
pose proof (Z.mod_pos_bound (shadow_addr x) 8 ltac:(lia)) as M0.
pose proof (Z.div_mod (shadow_addr (x + n - 1)) 8 ltac:(lia)) as D1.
pose proof (Z.mod_pos_bound (shadow_addr (x + n - 1)) 8 ltac:(lia)) as M1.
rewrite E by lia. exact (H s Hs).
Qed.

(* the strcmp row's tail premise (YGcallMx.v astrcmp_realizes_x: `x + k < a < x + k - (x + k) mod 8 + 8`), i.e. the bytes
   after a NUL at g up to the END OF g's GRANULE, are present when g lies in a live block [p, E): below E by alx_blocks'
   presence, in [E, (E + 7) / 8 * 8) by alx_blocks_tail (AR_laws_x field 15). Replaces the stand-in HULL
   (ev_hull_present_law), which claimed presence on [p, E - E mod 8 + 8): when E mod 8 = 0 that is the granule PAST
   the block, false in the model (a Theorem Labs lane's internal file HSMAP-DESIGN.md §2(b)-(c)): the granule of E is not the granule of the
   block's last byte E - 1. *)
Lemma p7a_tail_present : forall ly S Hp W mem md p n g a,
  ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> p <= g < p + req_size n ->
  g < a < g - g mod 8 + 8 -> aview SEGS (w_H W) mem a <> None.
Proof.
intros ly S Hp W mem md p n g a HAR Hin Hg Ha.
destruct (Z_lt_le_dec a (p + req_size n)) as [Hlt | Hge].
- destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p n HAR Hin) as (_ & _ & _ & _ & Hpres & _).
  exact (aview_some_of_apresent SEGS _ _ _ (proj1 (Hpres a ltac:(lia)))).
- apply (alx_blocks_tail _ _ _ LAWS ly S Hp W mem md p n a HAR Hin).
  pose proof (Z.div_mod g 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound g 8 ltac:(lia)) as M1.
  pose proof (Z.div_mod (p + req_size n + 7) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound (p + req_size n + 7) 8 ltac:(lia)) as M2.
  lia.
Qed.

(* the string rows' region premise over a sub-range that ends by the range's end *)
Lemma p7a_am8_sub : forall p n x m, YGcallMx.amem_range8 p n -> p <= x -> x + m <= p + n -> YGcallMx.amem_range8 x m.
Proof. unfold YGcallMx.amem_range8. intros. lia. Qed.

(* the shadow hull of a sub-range is inside the hull of the range *)
Lemma p7a_hull_sub : forall (rd : Z -> option Z) p mm d n, shadow_hull_vis rd p mm -> p <= d -> d + n <= p + mm ->
  0 < n -> shadow_hull_vis rd d n.
Proof.
intros rd p mm d n H Hpd Hdn Hn s Hs. apply H.
assert (M : forall x y, x <= y -> shadow_addr x / 8 * 8 <= shadow_addr y / 8 * 8).
{ intros x y Hxy. unfold shadow_addr. apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.div_le_mono; [lia|].
  apply Z.add_le_mono_l. apply Z.div_le_mono; lia. }
pose proof (M p d Hpd). pose proof (M (d + n - 1) (p + mm - 1) ltac:(lia)). lia.
Qed.

Lemma p7a_rdword : forall (rd rd' : Z -> option Z) a,
  (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a E. pose proof (E 0 ltac:(lia)) as E0. rewrite Z.add_0_r in E0. unfold rdword.
rewrite E0, (E 1), (E 2), (E 3), (E 4), (E 5), (E 6), (E 7) by lia. reflexivity.
Qed.

(* a frame that holds a 56-byte node has a whole number of granules *)
Lemma p7a_fs8 : forall c, 56 <= fs_frame_bytes c -> fs_frame_bytes c mod 8 = 0.
Proof.
intros c H. unfold fs_frame_bytes in *. destruct (Z.le_gt_cases 0 c) as [Hc|Hc].
- rewrite Z.shiftl_mul_pow2 by lia. replace (64 * 2 ^ c) with ((8 * 2 ^ c) * 8) by lia. apply Z.mod_mul. lia.
- exfalso. assert (En : c = - (- c)) by lia. remember (- c) as n eqn:Hn. rewrite En in H.
  rewrite Z.shiftl_div_pow2 in H by lia. rewrite ?Z.opp_involutive in H.
  assert (H2 : 2 <= 2 ^ n).
  { replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
  assert (H3 : 64 / 2 ^ n <= 64 / 2) by (apply Z.div_le_compat_l; lia).
  change (64 / 2) with 32 in H3. pose proof (Z.le_trans _ _ _ H H3) as H5. apply H5. reflexivity.
Qed.

(* the shadow byte of an address of a granule-aligned range is a byte of the range's shadow *)
Lemma p7a_sh_in : forall fa fs x, fa mod 8 = 0 -> fs mod 8 = 0 -> fa <= x < fa + fs ->
  fa / 8 <= x / 8 < fa / 8 + fs / 8.
Proof.
intros fa fs x Ha Hs Hx. pose proof (Z.div_mod fa 8 ltac:(lia)) as Da. pose proof (Z.div_mod fs 8 ltac:(lia)) as Ds.
rewrite Ha, Z.add_0_r in Da. rewrite Hs, Z.add_0_r in Ds.
split; [apply Z.div_le_mono; lia|].
apply Z.div_lt_upper_bound; [lia|]. rewrite Z.mul_add_distr_l. rewrite <- Da, <- Ds. lia.
Qed.

(* ---- the two hull facts this file took as HFHULL / HSTK64 until the S8a memnorm interface (contract item 4), DERIVED
   from AR_laws_x field 18 (alx_layout_ok) as S8aEntry.v does (eve_granule_64 / eve_stk64 / eve_fs_cid /
   eve_frame_hull, copied: S8aEntry is not Required): the real stack's top is 64-aligned (YCbqG.v stk_aligned_x); a live
   fake frame of 56 bytes or more is 64-aligned (layout_ok's lo_F_al: ly_F page aligned; every term of fs_frame_off is
   a multiple of 64 for a class cid >= 0), so its shadow hull is exactly its own fs_frame_bytes cid / 8 shadow bytes,
   present by field 3 (alx_frames).
   Numerals: 2147450880 (WORD: SHADOW_OFF), 268431360 (DERIVED: SHADOW_OFF / 8), 8 (LENGTH: the granule), 64 (LENGTH:
   fs_frame_bytes 0, the fake frames' alignment, eight granules), 4096 (LENGTH: a page), 576 and 16384 (DERIVED:
   kFakeFramesOff and a class's frame span, over 64), 1048576 (DERIVED: 1 << kStackSizeLog), 63 (LENGTH: 64 - 1),
   56 (LENGTH: a pj_value node), 2 and 32 (the radix of a shift; 64 / 2). ---- *)
Lemma p7a_granule_64 : forall x, shadow_addr x / 8 * 8 = SHADOW_OFF + x / 64 * 8.
Proof.
intro x. unfold shadow_addr, SHADOW_OFF.
replace (2147450880 + x / 8) with (268431360 * 8 + x / 8) by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_div by lia. change (8 * 8) with 64. lia.
Qed.
Lemma p7a_stk64 : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> ly_stk_hi ly mod 64 = 0.
Proof. intros ly S Hp W mem md HAR. exact (proj2 (stk_aligned_x SEGS B ARx LAWS ly S Hp W mem md HAR)). Qed.
Lemma p7a_fs_cid : forall c, 56 <= fs_frame_bytes c -> 0 <= c.
Proof.
intros c H. unfold fs_frame_bytes in *. destruct (Z.le_gt_cases 0 c) as [Hc|Hc]; [exact Hc|].
exfalso. assert (En : c = - (- c)) by lia. remember (- c) as n eqn:Hn. rewrite En in H.
rewrite Z.shiftl_div_pow2 in H by lia. rewrite ?Z.opp_involutive in H.
assert (H2 : 2 <= 2 ^ n).
{ replace 2 with (2 ^ 1) at 1 by reflexivity. apply Z.pow_le_mono_r; lia. }
assert (H3 : 64 / 2 ^ n <= 64 / 2) by (apply Z.div_le_compat_l; lia).
change (64 / 2) with 32 in H3. pose proof (Z.le_trans _ _ _ H H3) as H5. apply H5. reflexivity.
Qed.
Lemma p7a_frame_hull : forall ly S Hp (W : world SEGS) mem md cid pos,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> 56 <= fs_frame_bytes cid ->
  shadow_hull_vis (aview SEGS (w_H W) mem) (frame_addr ly cid pos) (fs_frame_bytes cid).
Proof.
intros ly S Hp W mem md cid pos HAR Hin H56.
destruct (alx_frames SEGS B ARx LAWS ly S Hp W mem md cid pos HAR Hin) as (_ & _ & _ & HSP).
pose proof (lo_F_al _ (alx_layout_ok SEGS B ARx LAWS ly S Hp W mem md HAR)) as HF. unfold page_aligned in HF.
pose proof (p7a_fs_cid cid H56) as Hc.
pose proof (Z.pow_pos_nonneg 2 cid ltac:(lia) Hc) as Ht0.
assert (Hfs : fs_frame_bytes cid = 64 * 2 ^ cid) by (unfold fs_frame_bytes; rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
assert (Hfa : frame_addr ly cid pos = 64 * (ly_F ly / 4096 * 64 + 576 + cid * 16384 + pos * 2 ^ cid)).
{ unfold frame_addr, fs_frame_off, kFakeFramesOff, kStackSizeLog. change (Z.shiftl 1 20) with 1048576. rewrite Hfs.
  pose proof (Z.div_mod (ly_F ly) 4096 ltac:(lia)) as D. rewrite HF, Z.add_0_r in D.
  set (fq := ly_F ly / 4096) in D |- *. rewrite D. ring. }
set (u := ly_F ly / 4096 * 64 + 576 + cid * 16384 + pos * 2 ^ cid) in Hfa.
set (t := 2 ^ cid) in *.
assert (Hsh : shadow_addr (frame_addr ly cid pos) = SHADOW_OFF + u * 8).
{ unfold shadow_addr. rewrite Hfa. replace (64 * u) with ((u * 8) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
assert (Hf8 : fs_frame_bytes cid / 8 = t * 8).
{ rewrite Hfs. replace (64 * t) with ((t * 8) * 8) by ring. rewrite Z.div_mul by lia. reflexivity. }
intros s Hs. rewrite !p7a_granule_64 in Hs. rewrite Hfa, Hfs in Hs.
replace (64 * u) with (u * 64) in Hs by ring. rewrite Z.div_mul in Hs by lia.
replace (u * 64 + 64 * t - 1) with ((u + t - 1) * 64 + 63) in Hs by ring.
rewrite Z.div_add_l in Hs by lia. change (63 / 64) with 0 in Hs.
destruct (HSP (s - shadow_addr (frame_addr ly cid pos)) ltac:(rewrite Hf8, Hsh; lia)) as [Hps _].
replace (shadow_addr (frame_addr ly cid pos) + (s - shadow_addr (frame_addr ly cid pos))) with s in Hps by lia.
exact (aview_some_of_apresent SEGS _ _ _ Hps).
Qed.

(* a live block's sub-range outside its hidden head has a visible shadow hull (the laws at that state) *)
Lemma p7a_inblk_hull : forall ly S Hp W mem md Lam peak cnt fail ran most own a len, ARx ly S Hp W mem md ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prhex_inblk B ly S Hp a len -> 0 < len ->
  shadow_hull_vis (aview SEGS (w_H W) mem) a len.
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own a len HAR HLED (b & m & Hin & Hba & Hab & Hhd) Hlen.
assert (Hrq : m <= req_size m) by (unfold req_size; destruct (Z.eqb_spec m 0); lia).
pose proof (@cf_head_nonneg cp) as Hh0.
destruct (in_dec Z.eq_dec b Hp) as [Hb | Hb].
- specialize (Hhd Hb). destruct (HSH ly S Hp W mem md b m HAR Hin Hb) as [_ Hhv].
  apply (p7a_hull_sub _ (b + cf_head) (req_size m - cf_head)); [apply Hhv; lia|lia|lia|lia].
- destruct (alx_shadow _ _ _ LAWS ly S Hp W mem md b m HAR Hin
    (ev_hp_apart B ARx LAWS ly S Hp W mem md Lam peak cnt fail ran most own b m HAR HLED Hin Hb)) as [_ Hhv].
  apply (p7a_hull_sub _ b (req_size m)); [exact Hhv|lia|lia|lia].
Qed.

(* ---- the frame arithmetic (FRAME's ev_bounds) ---- *)
Lemma p7a_bounds : forall (a : ev_act), ev_pre (fx := fx) B ARx a ->
  alloc_ceiling <= ea_sp0 a - ea_STK a /\ ea_sp0 a - ea_STK a <= ea_S1 a /\ ea_S1 a + 152 <= ea_sp0 a /\
  ea_S1 a mod 32 = 0 /\ ea_sp0 a <= ea_q a /\ ea_q a + 40 <= ea_sp0 a + ea_d a /\ ea_sp0 a + ea_d a <= 2 ^ 47 /\
  ea_q a mod 8 = 0 /\ 0 <= ea_d a.
Proof.
intros a HPRE.
destruct HPRE as (((_ & _ & _ & _ & _ & HSTK & _) & _) & _ & _ & _ & _ & _ & HQ8 & _ & HSQ & HQD & HFW & _).
destruct HSTK as (_ & _ & HCEIL & HLO & _ & H47 & _ & _ & HTOPHI).
destruct HFW as (HD0 & _ & HDTOP & _).
change (spZ (ea_regs a)) with (ea_sp0 a) in *.
pose proof (p7a_stk (ea_n a)) as HK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HK. unfold ESTACK in HK.
assert (ESA : ea_SA a = ea_sp0 a - 256) by reflexivity.
pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)) as HM.
assert (ES1 : ea_S1 a = ea_SA a - ea_SA a mod 32) by reflexivity.
assert (ES1' : ea_S1 a = ea_SA a / 32 * 32) by (pose proof (Z.div_mod (ea_SA a) 32 ltac:(lia)); lia).
split; [lia|]. split; [lia|]. split; [lia|]. split; [rewrite ES1'; apply Z.mod_mul; lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [exact HQ8|exact HD0].
Qed.

(* ---- the reader's tree at a node of the activation's tree, across a straight stretch: its footprint misses the
   stretch's stack writes ([sp0 - STK, sp0), by ev_pre) and `struct ex`; its blocks are the ledger's, below
   S1 - 2 ESTACK. A node byte keeps its value and lies off the image, so it keeps its writability too. ---- *)
Lemma p7a_tree_frame : forall (a : ev_act) ly S Hp W mem md k p dep dl mem' (Wr : Z -> Prop) p0 t0 D0,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ Wr z -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  (forall z, Wr z -> ea_S1 a - 2 * ESTACK <= z < ea_S1 a + 152 \/ ea_q a <= z < ea_q a + 8 \/
     ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36) ->
  prhex_tree ly S (ea_Lam a) W (ea_regs a) mem p0 t0 D0 ->
  (forall z, PRH_Reader.pj_footR p0 D0 z -> ~ (ea_q a <= z < ea_q a + 40) /\ ~ (ea_sp0 a - ea_STK a <= z < ea_sp0 a)) ->
  prhex_tree ly S (ea_Lam a) W (ea_regs a) mem' p0 t0 D0.
Proof.
intros a ly S Hp W mem md k p dep dl mem' Wr p0 t0 D0 HPRE HMID AV HWR (HN & HH & HRA & HHV) FOOT.
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & _ & BQ & BQD & B47 & _ & BD0).
pose proof (p7a_stk (ea_n a)) as HK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HK. unfold ESTACK in HK, HWR.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5).
assert (ESA : ea_SA a = ea_sp0 a - 256) by reflexivity.
assert (HS1 : ea_sp0 a - 287 <= ea_S1 a /\ ea_S1 a <= ea_SA a).
{ unfold ea_S1. pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)). lia. }
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HPRE as (((_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & H47 & _) & _) & _) & _).
pose proof HMID as (HJ & _ & _ & _ & HLED & _).
pose proof HJ as (HAR & HLY & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EHI & _).
assert (LOWA : forall s, 0 <= s < alloc_ceiling -> aview SEGS (w_H W) mem' s = aview SEGS (w_H W) mem s).
{ intros s Hs. apply AV; [lia|]. intros Hw. destruct (HWR s Hw) as [H1|[H1|[H1|H1]]]; lia. }
(* a byte of a ledger block: below alloc_ceiling, in a harness block *)
assert (LAMK : forall b kk z, In (b, kk) (ea_Lam a) -> b <= z < b + kk ->
   aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
{ intros b kk z Hin Hz. destruct HLED as (_ & _ & HHB & _).
  destruct (proj1 (Forall_forall _ _) HHB (b, kk) Hin) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
  assert (Hrq : kk + cf_head <= req_size (kk + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (b - cf_head) (kk + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
  split; [apply LOWA; lia|].
  split; [apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md (b - cf_head) (kk + cf_head) z HAR Hblk); lia|lia]. }
(* a byte of the root node, by its home *)
assert (ROOT : forall z, p0 <= z < p0 + 56 ->
   aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
{ intros z Hz. destruct (FOOT z (or_introl Hz)) as (Hq & Hs).
  assert (Hn : ~ Wr z) by (intros Hw; destruct (HWR z Hw) as [H1|[H1|[H1|H1]]]; [apply Hs; lia|apply Hq; lia..]).
  destruct HH as [(b & mm & Hin & H1 & H2)|[(cid & pos & Hin & H1 & H2)|(H1 & H2)]].
  - destruct (LAMK b mm z Hin ltac:(lia)) as (_ & NI & Rz). split; [apply AV; [exact Rz|exact Hn]|]. split; assumption.
  - destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Fa & Fc & _).
    split; [apply AV; [lia|exact Hn]|].
    split; [apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos z HAR Hin); lia|lia].
  - change (spZ (ea_regs a)) with (ea_sp0 a) in H1. rewrite EHI in H2.
    split; [apply AV; [lia|exact Hn]|].
    split; [intros Him; pose proof (ev_segs_low z Him) as Hlo; unfold kLowMemEnd in Hlo; lia|lia]. }
assert (VB : 0 <= p0 /\ p0 + 56 <= 2 ^ 47).
{ destruct (ROOT p0 ltac:(lia)) as (_ & _ & R0). destruct (ROOT (p0 + 55) ltac:(lia)) as (_ & _ & R55).
  destruct HH as [(b & mm & Hin & H1 & H2)|[(cid & pos & Hin & H1 & H2)|(H1 & H2)]].
  - split; [lia|].
    destruct HLED as (_ & _ & HHB & _).
    destruct (proj1 (Forall_forall _ _) HHB (b, mm) Hin) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
    assert (Hrq : mm + cf_head <= req_size (mm + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (mm + cf_head) 0); lia).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (b - cf_head) (mm + cf_head) HAR Hblk) as (_ & _ & Hc & _). lia.
  - destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (F0 & F1 & _). lia.
  - rewrite EHI in H2. change (spZ (ea_regs a)) with (ea_sp0 a) in H1. lia. }
split; [|split; [exact HH|split; [apply (p7a_ra (aview SEGS (w_H W) mem)); [lia|lia|exact LOWA|exact HRA] |
  apply (p7a_hull (aview SEGS (w_H W) mem)); [lia|lia|lia|exact LOWA|exact HHV]]]].
apply (p7a_nodeR_frame (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') (prh_lin (ea_Lam a)) _ _ _ HN).
intros z Hz'.
assert (FKz : aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
{ destruct Hz' as [Hz|(b & kk & Hin & Hl & Hz)]; [exact (ROOT z Hz)|exact (LAMK b kk z Hl Hz)]. }
destruct FKz as (AVz & NIz & Rz). split.
- exact (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem' z AVz).
- exact (p7a_wr_av (w_H W) (w_H W) mem mem' z Rz NIz AVz).
Qed.

(* ---- the reader's tree across a caller-window call: its footprint misses the callee's FP (inside the activation's:
   the scratch and `struct ex`); a node byte is kept by the callee's block clause (a ledger block), its frame clause
   (a fake frame) or its window / stack clause (the real stack at or above S1); the root's shadow comes from the laws
   at the new state (a ledger block, the real stack) or from the frame clause's shadow part (a fake frame) ---- *)
Lemma p7a_tree_call : forall (a : ev_act) ly S Hp W mem md k p dep dl
    STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 p0 t0 D0,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  ajournal_x (SK := SK) SEGS B PST ARx (STK1 + e1) (ea_S1 a + e1) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall z, ea_S1 a <= z < ea_S1 a + e1 -> ~ inFP FP1 z -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z) ->
  (forall z, inFP FP1 z -> inFP (ea_FP a) z) ->
  Hp2 = Hp -> ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) ->
  prhex_tree ly S (ea_Lam a) W (ea_regs a) mem p0 t0 D0 ->
  (forall z, PRH_Reader.pj_footR p0 D0 z ->
     ~ (ea_scr a <= z < ea_scr a + ea_len a + 1) /\ ~ (ea_q a <= z < ea_q a + 40)) ->
  prhex_tree ly2 S2 (ea_Lam a) W2 (ea_regs a) mem2 p0 t0 D0.
Proof.
intros a ly S Hp W mem md k p dep dl STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 p0 t0 D0
  HPRE HMID HAR2 HJC HX HFP1 EHP EAB HLED2 (HN & HH & HRA & HHV) FOOT.
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & _ & BQ & BQD & B47 & _ & BD0).
pose proof (p7a_stk (ea_n a)) as HK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HK. unfold ESTACK in HK.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5).
assert (ESA : ea_SA a = ea_sp0 a - 256) by reflexivity.
assert (HS1 : ea_sp0 a - 287 <= ea_S1 a /\ ea_S1 a <= ea_SA a).
{ unfold ea_S1. pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)). lia. }
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINS & _).
destruct HFP as ((_ & _ & _ & _ & _ & (_ & _ & HCEIL0 & HLO0 & _ & H47 & _) & _) & _).
change (spZ (ea_regs a)) with (ea_sp0 a) in HLO0.
pose proof HMID as (HJ & _ & _ & HABL & HLED & _).
pose proof HJ as (HAR & HLY & _).
pose proof HJC as (_ & HLYC & _ & _ & _ & HFRC & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & ELO & EHI & _).
pose proof HLYC as (_ & _ & _ & _ & _ & ELFC & _ & _ & _ & ELOC & EHIC & _).
assert (NFP : forall z, ~ (ea_scr a <= z < ea_scr a + ea_len a + 1) -> ~ (ea_q a <= z < ea_q a + 40) ->
  ~ inFP FP1 z).
{ intros z H1 H2 Hin. destruct (HFP1 z Hin) as (r & Hr & Hz). unfold ea_FP in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hz; lia. }
assert (KSTK : forall z, ea_S1 a <= z < 2 ^ 64 -> ~ inFP FP1 z ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
{ intros z Hz Hn. destruct (Z_lt_le_dec z (ea_S1 a + e1)) as [Hl|Hl]; [apply HX; [lia|exact Hn]|].
  apply F1; lia. }
assert (KBLK : forall b m z, In (b, m) (ablocks B ly S) -> b <= z < b + req_size m -> ~ inFP FP1 z ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
{ intros b m z Hin Hz Hn. replace z with (b + (z - b)) by lia.
  apply (F2 b m (z - b)); [exact Hin|rewrite EAB; exact Hin|lia|replace (b + (z - b)) with z by lia; exact Hn]. }
pose proof HINS as (bs & ms & Hbs & Hbs1 & Hbs2 & _). rewrite <- HABL in Hbs.
assert (Rs : ms <= req_size ms) by (unfold req_size; destruct (Z.eqb_spec ms 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md bs ms HAR Hbs) as (_ & Hs4096 & Hsc & Hsapp & _).
(* a byte of a ledger block *)
assert (LAMK : forall b kk z, In (b, kk) (ea_Lam a) -> b <= z < b + kk -> ~ inFP FP1 z ->
   aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
{ intros b kk z Hin Hz Hn. destruct HLED as (_ & _ & HHB & _).
  destruct (proj1 (Forall_forall _ _) HHB (b, kk) Hin) as (Hk0 & Hblk & _). cbn [fst snd] in Hk0, Hblk.
  assert (Hrq : kk + cf_head <= req_size (kk + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
  destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (b - cf_head) (kk + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
  split; [apply (KBLK (b - cf_head) (kk + cf_head) z Hblk); [lia|exact Hn]|].
  split; [apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md (b - cf_head) (kk + cf_head) z HAR Hblk); lia|lia]. }
(* a byte of the root node, by its home *)
assert (ROOT : forall z, p0 <= z < p0 + 56 ->
   aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
{ intros z Hz. destruct (FOOT z (or_introl Hz)) as (Hsc' & Hq).
  assert (Hn : ~ inFP FP1 z) by (apply NFP; assumption).
  destruct HH as [(b & mm & Hin & H1 & H2)|[(cid & pos & Hin & H1 & H2)|(H1 & H2)]].
  - apply (LAMK b mm z Hin); [lia|exact Hn].
  - destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Fa & Fc & _).
    split; [eapply F4; [exact Hin|left; unfold frame_rng, in_zr; cbn [fst snd]; lia|exact Hn]|].
    split; [apply (frm_img_x SEGS B ARx LAWS ly S Hp W mem md cid pos z HAR Hin); lia|lia].
  - change (spZ (ea_regs a)) with (ea_sp0 a) in H1. rewrite EHI in H2.
    split; [apply KSTK; [lia|exact Hn]|].
    split; [intros Him; pose proof (ev_segs_low z Him) as Hlo; unfold kLowMemEnd in Hlo; lia|lia]. }
(* the footprint the reader's node reads *)
assert (FK : forall z, (p0 <= z < p0 + 56 \/
     exists b kk, In (b, kk) D0 /\ prh_lin (ea_Lam a) b kk /\ b <= z < b + kk) ->
   aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z /\ ~ in_img SEGS z /\ 0 <= z < 2 ^ 64).
{ intros z [Hz|(b & kk & Hin & Hl & Hz)]; [exact (ROOT z Hz)|].
  assert (Hf : PRH_Reader.pj_footR p0 D0 z).
  { right. exists (b, kk). split; [exact Hin|]. unfold PRH_Reader.pj_holdsR. cbn [fst snd]. lia. }
  destruct (FOOT z Hf) as (Hsc' & Hq).
  apply (LAMK b kk z Hl); [lia|apply NFP; assumption]. }
split.
{ apply (p7a_nodeR_frame (mrestrict (w_H W) mem) (mrestrict (w_H W2) mem2) (prh_lin (ea_Lam a)) _ _ _ HN).
  intros z Hz. destruct (FK z Hz) as (AVz & NIz & Rz). split.
  - exact (mbyte_of_aview SEGS (w_H W) (w_H W2) mem mem2 z AVz).
  - exact (p7a_wr_av (w_H W) (w_H W2) mem mem2 z Rz NIz AVz). }
split.
{ destruct HH as [Hl|[(cid & pos & Hin & H1 & H2)|(H1 & H2)]]; [left; exact Hl| |].
  - right. left. exists cid, pos. split; [rewrite HFRC; exact Hin|].
    assert (EF : frame_addr ly2 cid pos = frame_addr ly cid pos) by (unfold frame_addr; rewrite ELFC; reflexivity).
    rewrite EF. split; assumption.
  - right. right. split; [exact H1|rewrite EHIC; exact H2]. }
(* the root's shadow and shadow hull at the new state *)
destruct HH as [(b & mm & Hin & H1 & H2)|[(cid & pos & Hin & H1 & H2)|(H1 & H2)]].
- split; [exact (proj1 (ev_lam_shadow B ARx LAWS HSH ly2 S2 Hp2 W2 mem2 md2 (ea_Lam a) (ea_peak a) (ea_cnt a)
    (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) b mm p0 56 HAR2 HLED2 Hin H1 H2 ltac:(lia)))|].
  exact (ev_lam_hull B ARx LAWS HSH ly2 S2 Hp2 W2 mem2 md2 (ea_Lam a) (ea_peak a) (ea_cnt a)
    (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) b mm p0 56 HAR2 HLED2 Hin H1 H2 ltac:(lia)).
- assert (HIN2 : In (cid, pos) (frames S2)) by (rewrite HFRC; exact Hin).
  assert (EF2 : frame_addr ly2 cid pos = frame_addr ly cid pos) by (unfold frame_addr; rewrite ELFC; reflexivity).
  split; cycle 1.
  { apply (p7a_hull_sub _ (frame_addr ly cid pos) (fs_frame_bytes cid) p0 56); [|lia|lia|lia].
    rewrite <- EF2. exact (p7a_frame_hull ly2 S2 Hp2 W2 mem2 md2 cid pos HAR2 HIN2 ltac:(lia)). }
  destruct (alx_frames _ _ _ LAWS ly S Hp W mem md cid pos HAR Hin) as (Fal & _ & _ & _).
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (Fa & Fc & _).
  pose proof (p7a_fs8 cid ltac:(lia)) as F8.
  set (fa := frame_addr ly cid pos) in *. set (fs := fs_frame_bytes cid) in *.
  assert (Hfa8 : fa mod 8 = 0).
  { pose proof (Z.div_mod fa 32 ltac:(lia)) as D. rewrite Fal, Z.add_0_r in D. rewrite D.
    replace (32 * (fa / 32)) with (fa / 32 * 4 * 8) by lia. apply Z.mod_mul. lia. }
  apply (range_addressable_agree (aview SEGS (w_H W) mem) (aview SEGS (w_H W2) mem2) SHADOW_OFF p0 56);
    [|exact HRA].
  intros x Hx. unfold shadow_of_addr.
  pose proof (p7a_sh_in fa fs x Hfa8 F8 ltac:(lia)) as Hsx.
  eapply F4; [exact Hin|right; unfold in_zr; cbn [fst snd]; fold fa fs; unfold shadow_addr; lia|].
  apply NFP.
  + intros Hs. apply (p7a_sh_app x bs (req_size ms)); [lia|exact Hsapp|unfold shadow_addr; lia].
  + intros Hq. destruct (p7a_sh_lt x ltac:(lia)) as [_ Hlt]. unfold shadow_addr in Hlt. lia.
- change (spZ (ea_regs a)) with (ea_sp0 a) in H1.
  split.
  + intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    apply (alx_zshadow_byte _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 x HAR2).
    rewrite ELOC, EHIC, ELO. lia.
  + pose proof (p7a_stk64 ly2 S2 Hp2 W2 mem2 md2 HAR2) as H64. rewrite EHIC in H64.
    apply (stack_hull_vis_x_rng SEGS B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 p0 56 HAR2); rewrite ?ELOC, ?EHIC, ?ELO.
    * pose proof (Z.div_mod p0 64 ltac:(lia)). pose proof (Z.mod_pos_bound p0 64 ltac:(lia)). lia.
    * pose proof (Z.div_mod (p0 + 56 - 1) 64 ltac:(lia)). pose proof (Z.mod_pos_bound (p0 + 56 - 1) 64 ltac:(lia)).
      pose proof (Z.div_mod (ly_stk_hi ly) 64 ltac:(lia)). rewrite H64 in *. lia.
Qed.

(* ---- the straight-stretch transport (FRAME's ev_mid_frame, Wr widened, frame premise over aview; with the S8a
   memnorm interface, the memory's normality at the new memory as its last premise, as S8aItemsWalk.ev_mid_frame) ---- *)
Lemma p7a_mid_frame : forall (a : ev_act) ly S Hp W mem md k p dep dl mem' md' p' dep' dl' (Wr : Z -> Prop),
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ Wr z -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  (forall z, Wr z -> ea_S1 a - 2 * ESTACK <= z < ea_S1 a + 152 \/ ea_q a <= z < ea_q a + 8 \/
     ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36) ->
  prhex_cur W mem' (ea_q a) p' (ea_x0 a + ea_len a) dep' (ea_scr a) dl' ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_mid B ARx SK a ly S Hp W mem' md' k p' dep' dl'.
Proof.
intros a ly S Hp W mem md k p dep dl mem' md' p' dep' dl' Wr HPRE HMID HJ' AV GROW HWR HCUR' HMN'.
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & _ & BQ & BQD & B47 & _ & BD0).
pose proof (p7a_stk (ea_n a)) as HK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HK. unfold ESTACK in HK, HWR.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5).
assert (ESA : ea_SA a = ea_sp0 a - 256) by reflexivity.
assert (HS1 : ea_sp0 a - 287 <= ea_S1 a /\ ea_S1 a <= ea_SA a).
{ unfold ea_S1. pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)). lia. }
pose proof HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTR0 & _).
destruct HFP as ((_ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & H47 & _) & _) & _).
pose proof HMID as (HJ & HWIN & HHP & HABL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HROOM & HRPOS & _).
pose proof HJ as (HAR & HLY & _ & _ & _ & HFR & _).
(* a byte of the word range outside Wr is kept *)
assert (KEEP : forall z, 0 <= z < 2 ^ 64 -> ~ Wr z ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz Hn. exact (mbyte_of_aview SEGS (w_H W) (w_H W) mem mem' z (AV z Hz Hn)). }
(* below S1 - 2 ESTACK (at least alloc_ceiling + ESTACK), nothing is in Wr *)
assert (LOW : forall z, 0 <= z < ea_S1 a - 8192 ->
  mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz. apply KEEP; [lia|]. intros Hw. destruct (HWR z Hw) as [H1|[H1|[H1|H1]]]; lia. }
assert (LOWA : forall s, 0 <= s < alloc_ceiling -> aview SEGS (w_H W) mem' s = aview SEGS (w_H W) mem s).
{ intros s Hs. apply p7a_av. apply LOW. lia. }
(* the q parts of Wr are in FP *)
assert (EFP : forall z, ea_q a <= z < ea_q a + 8 \/ ea_q a + 16 <= z < ea_q a + 20 \/
  ea_q a + 32 <= z < ea_q a + 36 -> inFP (ea_FP a) z).
{ intros z [Hz|[Hz|Hz]]; unfold inFP, ea_FP.
  - exists (ea_q a, ea_q a + 8). split; [right; left; reflexivity|cbn [fst snd]; lia].
  - exists (ea_q a + 16, ea_q a + 20). split; [right; right; left; reflexivity|cbn [fst snd]; lia].
  - exists (ea_q a + 32, ea_q a + 36). split; [right; right; right; left; reflexivity|cbn [fst snd]; lia]. }
unfold ev_mid.
split; [exact HJ'|].
(* the caller window outside FP *)
split.
{ intros z Hz Hnf. etransitivity; [|exact (HWIN z Hz Hnf)]. apply AV; [lia|].
  intros Hw. destruct (HWR z Hw) as [H1|H1]; [lia|exact (Hnf (EFP z H1))]. }
split; [exact HHP|]. split; [exact HABL|].
(* the ledger: the statics (image bytes) and the block heads (below alloc_ceiling) *)
split.
{ destruct HLED as (HGL & HND & HHB & HPM).
  assert (PSTL : forall z, Exists (in_zr z) PST ->
    mbyte SEGS (mrestrict (w_H W) mem') z = mbyte SEGS (mrestrict (w_H W) mem) z).
  { intros z Hz. destruct (@pa_segs_low _ A_prog_listing PA z (PSTI z Hz)) as [Z0 Z1]. apply LOW.
    unfold kLowMemEnd in Z1. lia. }
  destruct HGL as (V1 & V2 & V3 & V4 & V5 & (V6 & V6r) & (V7 & V7r) & VR).
  split; [|split; [exact HND|split; [|exact HPM]]].
  - split; [apply (p7a_vm (mrestrict (w_H W) mem)); [|exact V1]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    split; [apply (p7a_vm (mrestrict (w_H W) mem)); [|exact V2]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    split; [apply (p7a_vm (mrestrict (w_H W) mem)); [|exact V3]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    split; [apply (p7a_vm (mrestrict (w_H W) mem)); [|exact V4]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia|].
    split; [apply (p7a_vm (mrestrict (w_H W) mem)); [|exact V5]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd; unfold in_zr;
      cbn [fst snd]; lia|].
    (* #102: g_most / g_own_ran_out, prh_pst's cells 6 and 7 (PRH_Base.v 3004a98fe2d9 prh_most / prh_own) *)
    split; [split; [apply (p7a_vm (mrestrict (w_H W) mem)); [|exact V6]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_hd;
      unfold in_zr; cbn [fst snd]; lia | exact V6r]|].
    split; [split; [apply (p7a_vm (mrestrict (w_H W) mem)); [|exact V7]; intros z Hz; apply PSTL; unfold prh_pst;
      apply Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl, Exists_cons_tl,
      Exists_cons_hd; unfold in_zr; cbn [fst snd]; lia | exact V7r]|].
    exact VR.
  - rewrite Forall_forall in HHB |- *. intros [a1 k1] Hin.
    destruct (HHB (a1, k1) Hin) as (Hk0 & Hblk & Hhp & Hal & Hv). cbn [fst snd] in Hk0, Hblk, Hhp, Hal, Hv |- *.
    split; [exact Hk0|]. split; [exact Hblk|]. split; [exact Hhp|]. split; [exact Hal|].
    pose proof (@cf_head_nonneg cp) as Hh0.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md (a1 - cf_head) (k1 + cf_head) HAR Hblk) as (_ & H4096 & Hc & _).
    assert (Hrq : 1 <= req_size (k1 + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k1 + cf_head) 0); lia).
    apply (p7a_vm (mrestrict (w_H W) mem)); [|exact Hv]. intros z Hz. apply LOW. lia. }
split; [exact HCUR'|].
(* the text: below alloc_ceiling *)
split.
{ destruct HSRC as (HBY & H4 & HCE & HAM & HRA & HHU).
  split; [apply (p7a_garr8 (mrestrict (w_H W) mem)); [intros z Hz; apply LOW; lia|exact HBY]|].
  split; [exact H4|]. split; [exact HCE|]. split; [exact HAM|].
  split; [apply (p7a_ra (aview SEGS (w_H W) mem)); [lia|lia|exact LOWA|exact HRA]|].
  intros Hl. apply (p7a_hull (aview SEGS (w_H W) mem)); [lia|exact Hl|lia|exact LOWA|exact (HHU Hl)]. }
(* the scratch: below alloc_ceiling; writability grows *)
split.
{ destruct HWD as (HD0 & HDC & HAM & HWW & HRA & HHU).
  split; [exact HD0|]. split; [exact HDC|]. split; [exact HAM|].
  split; [intros z Hz; destruct (HWW z Hz) as (Hw & Ho & Hs);
    split; [exact (writable_at_grows SEGS _ _ z GROW Hw)|split; [exact Ho|exact Hs]]|].
  split; [apply (p7a_ra (aview SEGS (w_H W) mem)); [lia|lia|exact LOWA|exact HRA]|].
  intros Hl. apply (p7a_hull (aview SEGS (w_H W) mem)); [lia|exact Hl|lia|exact LOWA|exact (HHU Hl)]. }
(* the tree: its footprint misses Wr (ev_pre), its blocks are the ledger's *)
split.
{ destruct HTR0 as [Hv0|(_ & _ & FOOT)]; [left; exact Hv0|].
  destruct HTREE as [Hv0|HT]; [left; exact Hv0|]. right.
  apply (p7a_tree_frame a ly S Hp W mem md k p dep dl mem' Wr _ _ _ HPRE HMID AV HWR HT).
  intros z Hz. destruct (FOOT z (proj2 (ev_foot_R _ _ _) Hz)) as (_ & Hq & Hs & _).
  change (spZ (ea_regs a)) with (ea_sp0 a) in Hs. split; assumption. }
(* the save area [SA + 152, sp0): above the locals, below q *)
split.
{ unfold ev_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros orr Hin.
  assert (Hb : 152 <= fst orr <= 248).
  { unfold EV_SAVED in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst]; lia|]). destruct Hin. }
  apply (p7a_vm (mrestrict (w_H W) mem)); [|exact (HSAV orr Hin)].
  intros z Hz. apply KEEP; [lia|]. intros Hw. destruct (HWR z Hw) as [H1|[H1|[H1|H1]]]; lia. }
(* the own frame's flag word: inside a live fake frame, below alloc_ceiling; the room and run-position conjuncts: S
   unchanged; memnorm at the new memory (HMN') *)
split; [|split; [exact HROOM|split; [exact HRPOS|exact HMN']]].
{ assert (HIN : In (1, ea_pos a) (frames S)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HIN) as (F0 & F1 & _).
  assert (EF : frame_addr ly 1 (ea_pos a) = ea_fr a).
  { destruct HLY as (_ & _ & _ & _ & _ & ELF & _). unfold ea_fr, frame_addr. rewrite ELF. reflexivity. }
  rewrite EF in F0, F1. assert (FB : fs_frame_bytes 1 = 128) by reflexivity.
  rewrite <- HFLAG. apply p7a_rdword. intros i Hi. apply LOWA. lia. }
Qed.

(* ---- the caller-window CALL transport (with the S8a memnorm interface: memnorm at the call's end memory, the callee's
   keep, as its last premise) ---- *)
Lemma p7a_mid_call : forall (a : ev_act) ly S Hp W mem md k p dep dl
    STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 p' dep' dl',
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  (* the caller's journal, extended over the call (aj_call_xW / aj_call_xWF's first journal) *)
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
  (* the callee's own journal and the call's extension clause *)
  ajournal_x (SK := SK) SEGS B PST ARx (STK1 + e1) (ea_S1 a + e1) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall z, ea_S1 a <= z < ea_S1 a + e1 -> ~ inFP FP1 z -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z) ->
  (forall z, inFP FP1 z -> inFP (ea_FP a) z) ->
  ea_sp0 a + ea_d a <= ea_S1 a + e1 ->
  (* the callee's text: the harness blocks and the ledger *)
  Hp2 = Hp -> ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) ->
  (* the callee's text: the non-primary room (walkkit b77223726823) and its hull use (S8aIface's ev_mid pairs it with
     the room; composed by hull_used_app), and the run position (S8aIface's ev_mid keeps
     iface_room_pos from the activation's state; the callee's text gives its own keep, or S2 = S) *)
  (room_live_cf S -> room_live_cf S2) ->
  PresetHullBudget.hull_used S S2 [] ->
  (forall rp_sm rp_x rp_os rp_i rp_H0 rp_hist,
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S ->
     PresetRoomPos.iface_room_pos rp_sm rp_x rp_os rp_i rp_H0 rp_hist S2) ->
  prhex_cur W2 mem2 (ea_q a) p' (ea_x0 a + ea_len a) dep' (ea_scr a) dl' ->
  YAkMemnorm.memnorm SEGS mem2 ->
  ev_mid B ARx SK a ly2 S2 Hp2 W2 mem2 md2 (k + k1) p' dep' dl'.
Proof.
intros a ly S Hp W mem md k p dep dl STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 p' dep' dl'
  HPRE HMID HJ2 HJC HX HFP1 HE1 EHP EAB HLED2 HRL2 HHU2 HRP2 HCUR' HMN2.
assert (HRM1 : room_live_cf (ea_S a) -> room_live_cf S) by (eapply ev_mid_room; exact HMID).
assert (HHU1 : PresetHullBudget.hull_used (ea_S a) S nil) by (eapply ev_mid_hull; exact HMID).
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & _ & BQ & BQD & B47 & _ & BD0).
pose proof (p7a_stk (ea_n a)) as HK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HK. unfold ESTACK in HK.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5).
assert (ESA : ea_SA a = ea_sp0 a - 256) by reflexivity.
assert (HS1 : ea_sp0 a - 287 <= ea_S1 a /\ ea_S1 a <= ea_SA a).
{ unfold ea_S1. pose proof (Z.mod_pos_bound (ea_SA a) 32 ltac:(lia)). lia. }
pose proof (@cf_head_nonneg cp) as Hh0.
pose proof HPRE as (HFP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HINX & _ & _ & _ & _ & _ & _ & HINS & HSEPX & HSEPQ &
  HTR0 & _).
destruct HFP as ((_ & _ & _ & _ & _ & (_ & _ & HCEIL0 & HLO0 & _ & H47 & _) & _) & _).
change (spZ (ea_regs a)) with (ea_sp0 a) in HLO0.
pose proof HMID as (HJ & HWIN & HHP & HABL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HROOM & HRPOS & _).
pose proof HJ as (HAR & HLY & _ & _ & _ & HFR & _).
pose proof HJ2 as (HAR2 & _).
pose proof HJC as (_ & HLYC & _ & _ & _ & HFRC & _ & _ & F1 & F2 & F3 & F4 & _).
pose proof HLY as (_ & _ & _ & _ & _ & ELF & _ & _ & _ & ELO & EHI & _).
pose proof HLYC as (_ & _ & _ & _ & _ & ELFC & _ & _ & _ & ELOC & EHIC & _).
(* the callee's footprint lies in the activation's: away from it means off the scratch and off `struct ex` *)
assert (NFP : forall z, ~ (ea_scr a <= z < ea_scr a + ea_len a + 1) -> ~ (ea_q a <= z < ea_q a + 40) ->
  ~ inFP FP1 z).
{ intros z H1 H2 Hin. destruct (HFP1 z Hin) as (r & Hr & Hz). unfold ea_FP in Hr.
  destruct Hr as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Hz; lia. }
(* the stack at or above S1: the call's window clause, above it the callee's stack clause *)
assert (KSTK : forall z, ea_S1 a <= z < 2 ^ 64 -> ~ inFP FP1 z ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
{ intros z Hz Hn. destruct (Z_lt_le_dec z (ea_S1 a + e1)) as [Hl|Hl]; [apply HX; [lia|exact Hn]|].
  apply F1; lia. }
(* a block live at both states: the callee's block clause *)
assert (KBLK : forall b m z, In (b, m) (ablocks B ly S) -> b <= z < b + req_size m -> ~ inFP FP1 z ->
  aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
{ intros b m z Hin Hz Hn. replace z with (b + (z - b)) by lia.
  apply (F2 b m (z - b)); [exact Hin|rewrite EAB; exact Hin|lia|replace (b + (z - b)) with z by lia; exact Hn]. }
(* the text's and the scratch's blocks *)
(* (the text's block exists only for a non-empty text: ev_pre's (0 < len -> prhex_inblk ..), iface 67f35bb5f4bb) *)
pose proof HINS as (bs & ms & Hbs & Hbs1 & Hbs2 & _). rewrite <- HABL in Hbs.
assert (Rs : ms <= req_size ms) by (unfold req_size; destruct (Z.eqb_spec ms 0); lia).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md bs ms HAR Hbs) as (_ & Hs4096 & Hsc & Hsapp & _).
assert (INB2 : forall x n, prhex_inblk B (ea_ly a) (ea_S a) (ea_Hp a) x n -> prhex_inblk B ly2 S2 Hp2 x n).
{ unfold prhex_inblk. rewrite EAB, HABL, EHP, HHP. tauto. }
unfold ev_mid.
split; [exact HJ2|].
(* the caller window outside FP *)
split.
{ intros z Hz Hnf. rewrite <- (HWIN z Hz Hnf). apply KSTK; [lia|]. intros Hin. exact (Hnf (HFP1 z Hin)). }
split; [rewrite EHP; exact HHP|].
split; [rewrite EAB; exact HABL|].
split; [exact HLED2|].
split; [exact HCUR'|].
(* the text: its block, its shadow and hull from the laws at the new state *)
split.
{ destruct HSRC as (HBY & H4 & HCE & HAM & HRA & HHU). unfold ea_len in *.
  split.
  { apply (p7a_garr_av (w_H W) (w_H W2) mem mem2); [|exact HBY].
    intros z Hz. destruct (HINX ltac:(lia)) as (bx & mx & Hbx & Hbx1 & Hbx2 & _). rewrite <- HABL in Hbx.
    assert (Rx : mx <= req_size mx) by (unfold req_size; destruct (Z.eqb_spec mx 0); lia).
    apply (KBLK bx mx z Hbx); [lia|]. apply NFP; lia. }
  split; [exact H4|]. split; [exact HCE|]. split; [exact HAM|].
  split.
  { destruct (Z_lt_le_dec 0 (Z.of_nat (length (ea_x a)))) as [Hl|Hl]; [|apply range_addressable_nil; lia].
    eapply (ev_inblk_shadow_FIX B ARx LAWS HSH); [exact HAR2|exact HLED2|apply INB2; exact (HINX Hl)|lia]. }
  intros Hl. eapply p7a_inblk_hull; [exact HAR2|exact HLED2|apply INB2; exact (HINX Hl)|exact Hl]. }
(* the scratch: present in its block at the new state *)
split.
{ destruct HWD as (HD0 & HDC & HAM & HWW & HRA & HHU).
  destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 bs ms HAR2 ltac:(rewrite EAB; exact Hbs))
    as (_ & _ & _ & _ & Hpr2 & _).
  split; [exact HD0|]. split; [exact HDC|]. split; [exact HAM|].
  split.
  { intros z Hz. destruct (HWW z Hz) as (_ & _ & Hs). destruct (Hpr2 z ltac:(lia)) as [Hp2z Ho2].
    split; [exact (apresent_writable SEGS _ _ _ Hp2z)|]. split; [exact Ho2|exact Hs]. }
  split; [eapply (ev_inblk_shadow_FIX B ARx LAWS HSH); [exact HAR2|exact HLED2|apply INB2; exact HINS|unfold ea_len; lia]|].
  intros Hl. eapply p7a_inblk_hull; [exact HAR2|exact HLED2|apply INB2; exact HINS|exact Hl]. }
(* the tree *)
split.
{ destruct HTR0 as [Hv0|(_ & _ & FOOT)]; [left; exact Hv0|].
  destruct HTREE as [Hv0|HT]; [left; exact Hv0|]. right.
  apply (p7a_tree_call a ly S Hp W mem md k p dep dl STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ _
    HPRE HMID HAR2 HJC HX HFP1 EHP EAB HLED2 HT).
  intros z Hz. destruct (FOOT z (proj2 (ev_foot_R _ _ _) Hz)) as (Hsc' & Hq & _). split; assumption. }
(* the save area: inside the call's window, off its footprint *)
split.
{ unfold ev_saved in HSAV |- *. rewrite Forall_forall in HSAV |- *. intros orr Hin.
  assert (Hb : 152 <= fst orr <= 248).
  { unfold EV_SAVED in Hin. repeat (destruct Hin as [<-|Hin]; [cbn [fst]; lia|]). destruct Hin. }
  destruct HWD as (_ & HDC & _).
  apply (p7a_vm_av (w_H W) (w_H W2) mem mem2); [|exact (HSAV orr Hin)].
  intros z Hz. apply KSTK; [lia|]. apply NFP; lia. }
(* the own frame's flag word: a frame of the call's state, off the scratch's block; the room and the hull use (the
   pair) and the run position through the callee's; memnorm at mem2 (HMN2) *)
split; [|split; [split; [intros HR0; exact (HRL2 (HRM1 HR0)) |
  exact (PresetHullBudget.hull_used_app _ _ _ nil nil HHU1 HHU2)] | split; [intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist HR0;
  exact (HRP2 _ _ _ _ _ _ (HRPOS _ _ _ _ _ _ HR0))|exact HMN2]]].
{ assert (HIN1 : In (1, ea_pos a) (frames S)) by (rewrite HFR; left; reflexivity).
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HIN1) as (F0 & Fc & _).
  assert (EF : frame_addr ly 1 (ea_pos a) = ea_fr a) by (unfold ea_fr, frame_addr; rewrite ELF; reflexivity).
  pose proof (sep_block_frame_x _ _ _ LAWS ly S Hp W mem md bs ms 1 (ea_pos a) HAR Hbs HIN1) as Hdj.
  unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. rewrite EF in F0, Fc, Hdj.
  assert (FB : fs_frame_bytes 1 = 128) by reflexivity. rewrite FB in Fc, Hdj.
  rewrite <- HFLAG. apply p7a_rdword. intros i Hi. rewrite FB.
  eapply F4; [exact HIN1|left; unfold frame_rng, in_zr; cbn [fst snd]; rewrite EF, FB; lia|].
  apply NFP; lia. }
Qed.

(* ---- the kid's tree (ev_kid_ok) across a stretch and across a call: its footprint is inside the activation's ---- *)
Lemma p7a_v'_nz : forall (a : ev_act) o, ev_v' (ea_v a) o (ea_t a) <> 0 -> ea_v a <> 0.
Proof. intros a o H Hv. apply H. unfold ev_v'. rewrite Hv. destruct (ev_tv 0 o (ea_t a)); reflexivity. Qed.

Lemma p7a_kid_frame : forall (a : ev_act) ly S Hp W mem md k p dep dl mem' (Wr : Z -> Prop) o n kid,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ Wr z -> aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  (forall z, Wr z -> ea_S1 a - 2 * ESTACK <= z < ea_S1 a + 152 \/ ea_q a <= z < ea_q a + 8 \/
     ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36) ->
  ev_kid_ok a ly S W mem o n kid -> ev_kid_ok a ly S W mem' o n kid.
Proof.
intros a ly S Hp W mem md k p dep dl mem' Wr o n kid HPRE HMID AV HWR [Hk|(Hv' & Hn & H1 & H2 & H3 & Dk & HT & Hinc & Hfoot)];
  [left; exact Hk|right].
do 5 (split; [assumption|]). exists Dk. split; [|split; [exact Hinc|exact Hfoot]].
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTR0 & _).
destruct HTR0 as [Hv0|(_ & _ & FOOT)]; [exfalso; exact (p7a_v'_nz a o Hv' Hv0)|].
apply (p7a_tree_frame a ly S Hp W mem md k p dep dl mem' Wr _ _ _ HPRE HMID AV HWR HT).
intros z Hz. destruct (FOOT z (proj2 (ev_foot_R _ _ _) (Hfoot z Hz))) as (_ & Hq & Hs & _).
change (spZ (ea_regs a)) with (ea_sp0 a) in Hs. split; assumption.
Qed.

Lemma p7a_kid_call : forall (a : ev_act) ly S Hp W mem md k p dep dl
    STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 o n kid,
  ev_pre (fx := fx) B ARx a ->
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ARx ly2 S2 Hp2 W2 mem2 md2 ->
  ajournal_x (SK := SK) SEGS B PST ARx (STK1 + e1) (ea_S1 a + e1) FP1 ly S Hp W mem md [] ly2 S2 Hp2 W2 mem2 md2 k1 ->
  (forall z, ea_S1 a <= z < ea_S1 a + e1 -> ~ inFP FP1 z -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z) ->
  (forall z, inFP FP1 z -> inFP (ea_FP a) z) ->
  Hp2 = Hp -> ablocks B ly2 S2 = ablocks B ly S ->
  prh_ledger B ly2 S2 Hp2 W2 mem2 (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a) ->
  ev_kid_ok a ly S W mem o n kid -> ev_kid_ok a ly2 S2 W2 mem2 o n kid.
Proof.
intros a ly S Hp W mem md k p dep dl STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 o n kid
  HPRE HMID HAR2 HJC HX HFP1 EHP EAB HLED2 [Hk|(Hv' & Hn & H1 & H2 & H3 & Dk & HT & Hinc & Hfoot)];
  [left; exact Hk|right].
do 5 (split; [assumption|]). exists Dk. split; [|split; [exact Hinc|exact Hfoot]].
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HTR0 & _).
destruct HTR0 as [Hv0|(_ & _ & FOOT)]; [exfalso; exact (p7a_v'_nz a o Hv' Hv0)|].
apply (p7a_tree_call a ly S Hp W mem md k p dep dl STK1 e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ _
  HPRE HMID HAR2 HJC HX HFP1 EHP EAB HLED2 HT).
intros z Hz. destruct (FOOT z (proj2 (ev_foot_R _ _ _) (Hfoot z Hz))) as (Hsc & Hq & _). split; assumption.
Qed.

(* ======== p7a CALL KIT: what a mid-body caller-window call of the activation needs (after S8aItemsWalk.v
   0939d966f14 :1746-1899, ev7_bytes8 / ev7_rdword / ev7_saved_offs / ev7_mod8_of16 / ev7_chain_call / ev7_CN /
   ev7_pres_get / ev7_regs_pres / ev7_s1_lo / ev7_mod16 / ev7_mod16', copied: S8aItemsWalk Requires this file).
   Numerals: 256, 8, 16, 32 (LENGTH: byte radix, word, alignments), 248 / 240 (LENGTH: EV_SAVED's ra and s0 slots),
   272 (LENGTH: 256 + 16), 152 (LENGTH: the save area's lowest slot). ======== *)
Lemma p7a_bytes8 : forall v, 0 <= v < 2 ^ 64 ->
  YG0f.le_byte v 8 0 + 256 * (YG0f.le_byte v 8 1 + 256 * (YG0f.le_byte v 8 2 + 256 * (YG0f.le_byte v 8 3 +
    256 * (YG0f.le_byte v 8 4 + 256 * (YG0f.le_byte v 8 5 + 256 * (YG0f.le_byte v 8 6 + 256 * YG0f.le_byte v 8 7)))))) = v.
Proof.
intros v Hv. unfold YG0f.le_byte.
replace (v mod 2 ^ (8 * Z.of_nat 8)) with v by (symmetry; apply Z.mod_small; cbn; lia).
rewrite !Z.shiftr_div_pow2 by (cbn; lia).
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 2) with 16.
change (8 * Z.of_nat 3) with 24. change (8 * Z.of_nat 4) with 32. change (8 * Z.of_nat 5) with 40.
change (8 * Z.of_nat 6) with 48. change (8 * Z.of_nat 7) with 56.
rewrite Z.pow_0_r, Z.div_1_r.
set (y1 := v / 256). set (y2 := y1 / 256). set (y3 := y2 / 256). set (y4 := y3 / 256).
set (y5 := y4 / 256). set (y6 := y5 / 256). set (y7 := y6 / 256).
assert (E8 : v / 2 ^ 8 = y1) by reflexivity.
assert (E16 : v / 2 ^ 16 = y2) by (unfold y2, y1; rewrite Z.div_div by lia; reflexivity).
assert (E24 : v / 2 ^ 24 = y3) by (unfold y3; rewrite <- E16, Z.div_div by lia; reflexivity).
assert (E32 : v / 2 ^ 32 = y4) by (unfold y4; rewrite <- E24, Z.div_div by lia; reflexivity).
assert (E40 : v / 2 ^ 40 = y5) by (unfold y5; rewrite <- E32, Z.div_div by lia; reflexivity).
assert (E48 : v / 2 ^ 48 = y6) by (unfold y6; rewrite <- E40, Z.div_div by lia; reflexivity).
assert (E56 : v / 2 ^ 56 = y7) by (unfold y7; rewrite <- E48, Z.div_div by lia; reflexivity).
rewrite E8, E16, E24, E32, E40, E48, E56.
assert (Hy7 : 0 <= y7 < 256) by (rewrite <- E56; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite (Z.mod_small y7 256) by exact Hy7.
pose proof (Z.div_mod v 256 ltac:(lia)) as D0. pose proof (Z.div_mod y1 256 ltac:(lia)) as D1.
pose proof (Z.div_mod y2 256 ltac:(lia)) as D2. pose proof (Z.div_mod y3 256 ltac:(lia)) as D3.
pose proof (Z.div_mod y4 256 ltac:(lia)) as D4. pose proof (Z.div_mod y5 256 ltac:(lia)) as D5.
pose proof (Z.div_mod y6 256 ltac:(lia)) as D6.
fold y1 in D0. fold y2 in D1. fold y3 in D2. fold y4 in D3. fold y5 in D4. fold y6 in D5. fold y7 in D6.
lia.
Qed.

Lemma p7a_rdword_of : forall (H : word -> bool) mem a v,
  val_mem SEGS (mrestrict H mem) a 8 v -> 0 <= v < 2 ^ 64 -> rdword (aview SEGS H mem) a = Some v.
Proof.
intros H mem a v Hv Hr.
assert (Bk : forall k, (k < 8)%nat -> aview SEGS H mem (a + Z.of_nat k) = Some (YG0f.le_byte v 8 k)).
{ intros k Hk. unfold aview. rewrite (Hv k Hk). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. unfold YG0f.le_byte. apply Z.mod_mod. lia. }
unfold rdword.
rewrite <- (Z.add_0_r a) at 1. change 0 with (Z.of_nat 0) at 1. rewrite (Bk 0%nat) by lia.
change 1 with (Z.of_nat 1). rewrite (Bk 1%nat) by lia. change 2 with (Z.of_nat 2) at 1. rewrite (Bk 2%nat) by lia.
change 3 with (Z.of_nat 3). rewrite (Bk 3%nat) by lia. change 4 with (Z.of_nat 4). rewrite (Bk 4%nat) by lia.
change 5 with (Z.of_nat 5). rewrite (Bk 5%nat) by lia. change 6 with (Z.of_nat 6). rewrite (Bk 6%nat) by lia.
change 7 with (Z.of_nat 7). rewrite (Bk 7%nat) by lia.
f_equal. exact (p7a_bytes8 v Hr).
Qed.

Lemma p7a_saved_offs : forall o r, In (o, r) EV_SAVED -> 152 <= o <= 248.
Proof. intros o r H. cbv [EV_SAVED In] in H. repeat (destruct H as [H | H]; [injection H as <- <-; lia |]). destruct H. Qed.

Lemma p7a_mod8_of16 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof.
intros x H. pose proof (Z.div_mod x 16 ltac:(lia)) as D. rewrite H in D.
replace x with ((2 * (x / 16)) * 8) by lia. apply Z.mod_mul. lia.
Qed.

(* the chain at a mid-body call of the activation (sp = S1, s0 = sp0): ex_value's own record on top of the entry
   chain, for any reader that agrees with the current memory off struct ex (S8aItemsWalk.v ev7_chain_call) *)
Lemma p7a_chain_call : forall (a : ev_act) ly S Hp W mem md k p dep dl,
  ev_pre (fx := fx) B ARx a -> ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  forall rd'' : reader, (forall x, ~ (ea_q a <= x < ea_q a + 40) -> rd'' x = aview SEGS (w_H W) mem x) ->
  achain ly rd'' (ea_S1 a) (ea_sp0 a) ((ea_sp0 a, raZ (ea_regs a), s0Z (ea_regs a)) :: ea_ch a).
Proof.
intros a ly S Hp W mem md k p dep dl Hpre HM rd'' Hrd.
destruct (p7a_bounds a Hpre) as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9).
pose proof Hpre as HP. unfold ev_pre in HP. cbv zeta in HP.
destruct HP as ((HAF & _) & _ & _ & _ & _ & _ & _ & HCHA & Hspq & Hqd & Hfw & _ & _ & _ & _ & _ & _ & _ & Hwd0 & _).
pose proof HAF as (_ & _ & Hra4 & _ & _ & Hstk & _).
pose proof Hstk as (Hsp16 & _ & _ & _ & _ & H47 & _ & _ & Htop).
pose proof Hfw as (Hd0 & _ & Hdtop & _).
pose proof Hwd0 as (_ & Hwdc & _).
destruct HM as (HJ & HWin & _ & _ & _ & _ & _ & _ & _ & HSav & _).
pose proof HJ as (_ & Hly & _ & _ & _ & _ & _ & _ & HStk & _).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _).
pose proof asan_consts as ((C1 & C1') & _).
assert (Esp : spZ (ea_regs a) = ea_sp0 a) by reflexivity.
set (rd' := fun x => if (x <? ea_sp0 a) || (2 ^ 64 <=? x) then aview SEGS (w_H (ea_W a)) (ea_mem a) x else rd'' x).
assert (Hch0 : achain (ea_ly a) rd' (ea_sp0 a) (s0Z (ea_regs a)) (ea_ch a)).
{ rewrite <- Esp. apply (HCHA rd'). intros x Hx. unfold rd'.
  destruct ((x <? ea_sp0 a) || (2 ^ 64 <=? x)) eqn:Ex; [reflexivity|].
  apply orb_false_iff in Ex as [Ex1 Ex2]. apply Z.ltb_ge in Ex1. apply Z.leb_gt in Ex2.
  rewrite (Hrd x Hx).
  destruct (Z_lt_le_dec x (ea_sp0 a + ea_d a)) as [Hin | Hout].
  - apply HWin; [lia|]. unfold ea_FP. rewrite !inFP_cons. intros [Hf | [Hf | [Hf | [Hf | Hf]]]];
      [unfold ea_len in *; lia | lia | lia | lia | exact (inFP_nil _ Hf)].
  - apply HStk; [lia | lia]. }
assert (Hch1 : achain (ea_ly a) rd'' (ea_sp0 a) (s0Z (ea_regs a)) (ea_ch a)).
{ apply (achain_kept (ea_ly a) rd' rd'' (ea_sp0 a) (s0Z (ea_regs a)) (ea_ch a) (ea_sp0 a) Hch0 ltac:(lia) ltac:(lia)).
  intros x Hx. unfold rd'. replace ((x <? ea_sp0 a) || (2 ^ 64 <=? x)) with false; [reflexivity|].
  symmetry. apply orb_false_iff. split; [apply Z.ltb_ge | apply Z.leb_gt]; lia. }
apply (achain_ly_top (ea_ly a) ly) in Hch1; [|exact Etop].
assert (Hsave : forall o r, In (o, r) EV_SAVED ->
  rdword rd'' (ea_SA a + o) = Some (bv_unsigned (getr (ea_regs a) (Z_to_bv 5 r)))).
{ intros o r Hor. pose proof (proj1 (Forall_forall _ _) HSav (o, r) Hor) as Hv. cbn [fst snd] in Hv.
  pose proof (p7a_saved_offs o r Hor) as Ho.
  rewrite (rdword_ext (aview SEGS (w_H W) mem) rd''); [|intros kk Hkk; apply Hrd; unfold ea_SA in *; lia].
  apply (p7a_rdword_of (w_H W) mem _ _ Hv).
  pose proof (bv_unsigned_in_range 64 (getr (ea_regs a) (Z_to_bv 5 r))) as Hr. unfold bv_modulus in Hr. cbn [Z.of_N] in Hr.
  exact Hr. }
pose proof (Hsave 248 1 ltac:(cbv; tauto)) as Hw8. pose proof (Hsave 240 8 ltac:(cbv; tauto)) as Hw16.
replace (ea_SA a + 248) with (ea_sp0 a - 8) in Hw8 by (unfold ea_SA; lia).
replace (ea_SA a + 240) with (ea_sp0 a - 16) in Hw16 by (unfold ea_SA; lia).
apply (achain_push ly rd'' rd'' (ea_sp0 a) (s0Z (ea_regs a)) (raZ (ea_regs a)) (ea_ch a) (ea_S1 a) Hch1).
- rewrite Etop. lia.
- intros x _. reflexivity.
- exact Hw8.
- exact Hw16.
- exact Hra4.
- lia.
- exact (p7a_mod8_of16 _ Hsp16).
- rewrite Etop. lia.
- lia.
Qed.

Lemma p7a_pres_get : forall regs regs2, aregs_preserved regs regs2 ->
  forall r : bv 5, acallee_saved (bv_unsigned r) -> getr regs2 r = getr regs r.
Proof. intros regs regs2 H r Hr. rewrite <- (Z_to_bv_bv_unsigned _ r). exact (H _ Hr). Qed.

Lemma p7a_s1_lo : forall (a : ev_act), ea_sp0 a mod 16 = 0 -> ea_sp0 a - 272 <= ea_S1 a.
Proof.
intros a H16. unfold ea_S1, ea_SA.
set (x := ea_sp0 a - 256).
pose proof (Z.div_mod x 32 ltac:(lia)) as D32. pose proof (Z.mod_pos_bound x 32 ltac:(lia)) as M32.
assert (Hx16 : x mod 16 = 0) by (unfold x; rewrite Zminus_mod, H16; reflexivity).
pose proof (Z.div_mod x 16 ltac:(lia)) as D16. rewrite Hx16 in D16.
lia.
Qed.

Lemma p7a_mod16 : forall x y z, x mod 32 = 0 -> y mod 16 = 0 -> z mod 16 = 0 -> (x - (y + z)) mod 16 = 0.
Proof.
intros x y z Hx Hy Hz.
pose proof (Z.div_mod x 32 ltac:(lia)) as Dx. pose proof (Z.div_mod y 16 ltac:(lia)) as Dy.
pose proof (Z.div_mod z 16 ltac:(lia)) as Dz. rewrite Hx in Dx. rewrite Hy in Dy. rewrite Hz in Dz.
replace (x - (y + z)) with ((2 * (x / 32) - y / 16 - z / 16) * 16) by lia. apply Z.mod_mul. lia.
Qed.

Lemma p7a_mod16' : forall x y z, x mod 32 = 0 -> y mod 16 = 0 -> z mod 16 = 0 -> (y + z - x) mod 16 = 0.
Proof.
intros x y z Hx Hy Hz.
pose proof (Z.div_mod x 32 ltac:(lia)) as Dx. pose proof (Z.div_mod y 16 ltac:(lia)) as Dy.
pose proof (Z.div_mod z 16 ltac:(lia)) as Dz. rewrite Hx in Dx. rewrite Hy in Dy. rewrite Hz in Dz.
replace (y + z - x) with ((y / 16 + z / 16 - 2 * (x / 32)) * 16) by lia. apply Z.mod_mul. lia.
Qed.

(* ex_string's stack need (160, LENGTH: FR ex_string 144 + ex_hex4 16) fits ex_value's allowance below the body's sp *)
Lemma p7a_stks : forall n, STK_ex_string + 288 <= STK_ex_value n.
Proof.
intros n. assert (Hs : STK_ex_string = 160) by (vm_compute; reflexivity). rewrite Hs.
unfold STK_ex_value. vm_compute (zmaxl _). vm_compute (pi_frame _). lia.
Qed.

(* no static of PST is read-only at image A (S8aItemsWalk.v ev7_pst_rw_chk / ev7_pst_not_ro, copied) *)
Definition p7a_rdisj (lo hi b w : Z) : bool := (b + w <=? lo) || (hi <=? b).
Definition p7a_pst_rw_chk : bool :=
  forallb (fun r : Z * Z =>
    forallb (fun s => seg_writable s ||
       p7a_rdisj (Z.of_N (seg_base s)) (Z.of_N (seg_base s) + Z.of_N (seg_size s)) (fst r) (snd r)) SEGS &&
    p7a_rdisj (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) (fst r) (snd r)) PST.

Lemma p7a_pst_rw_ok : p7a_pst_rw_chk = true.
Proof. vm_compute. reflexivity. Qed.

Lemma p7a_pst_not_ro : forall a, in_roP SEGS (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) a ->
  ~ Exists (in_zr a) PST.
Proof.
intros a Hro Hex. apply Exists_exists in Hex as (r & Hin & Hr). unfold in_zr in Hr.
pose proof p7a_pst_rw_ok as Hc. unfold p7a_pst_rw_chk in Hc. rewrite forallb_forall in Hc.
specialize (Hc r Hin). apply andb_prop in Hc as [Hs Hrel]. rewrite forallb_forall in Hs.
unfold p7a_rdisj in *.
destruct Hro as [(s & Hsin & Hw & Hsr) | Hrr].
- specialize (Hs s Hsin). rewrite Hw in Hs. cbn [orb] in Hs.
  apply orb_prop in Hs as [Hs | Hs]; apply Z.leb_le in Hs; lia.
- apply orb_prop in Hrel as [H1 | H1]; apply Z.leb_le in H1; lia.
Qed.


(* ======== SEGMENT 2 (ev7_seg2_A): C_KID 0x83878 -> C_KEY 0x839a0, object path, with the refusal join ========
   (A addresses in this comment are for the reader; the proof names them by offset from ex_value's entry.)
   Model glue first (pure), then the cuts internal to the segment, then the runs. *)

(* ---- pure ---- *)
Lemma p7a_skipn_cons : forall (x : list Z) i, (i < length x)%nat -> skipn i x = nth i x 0 :: skipn (S i) x.
Proof.
intros x. induction x as [|b x IH]; intros i Hi; [cbn in Hi; lia|]. destruct i as [|i]; [reflexivity|].
cbn [skipn nth]. apply IH. cbn in Hi. lia.
Qed.

Lemma p7a_scan_lt : forall xs c, PjGrammar.scan xs = Some c -> (c < length xs)%nat.
Proof.
assert (H : forall m xs c, (length xs <= m)%nat -> PjGrammar.scan xs = Some c -> (c < length xs)%nat).
{ induction m as [|m IH]; intros xs c Hl Hs.
  - destruct xs; [discriminate|cbn in Hl; lia].
  - destruct xs as [|b r]; [discriminate|]. cbn [PjGrammar.scan] in Hs. cbn [length] in Hl |- *.
    destruct (b =? 34); [injection Hs as <-; lia|].
    destruct (b =? 92).
    + destruct r as [|b2 r2]; [discriminate|].
      destruct (PjGrammar.scan r2) as [q|] eqn:E; cbn [option_map] in Hs; [|discriminate].
      injection Hs as <-. cbn [length] in Hl |- *. pose proof (IH r2 q ltac:(lia) E). lia.
    + destruct (PjGrammar.scan r) as [q|] eqn:E; cbn [option_map] in Hs; [|discriminate].
      injection Hs as <-. pose proof (IH r q ltac:(lia) E). lia. }
intros xs c. exact (H (length xs) xs c (Nat.le_refl _)).
Qed.

(* the object's name read from the loop head's cursor i, the first non-blank byte at i' *)
Lemma p7a_name_at : forall (x : list Z) i i', skipn i' x = PjGrammar.skip (skipn i x) -> (i' < length x)%nat ->
  ev_run0 (PjGrammar.jr_name true (skipn i x)) =
  if nth i' x 0 =? 34 then
    match ev_run0 (PjGrammar.jr_string (skipn (S i') x)) with
    | Some (s, r) => match PjGrammar.skip r with c :: r1 => if c =? 58 then Some (s, r1) else None | [] => None end
    | None => None
    end
  else None.
Proof. intros x i i' Hs Hl. rewrite ev_jr_name_obj, <- Hs, (p7a_skipn_cons x i' Hl). reflexivity. Qed.

Lemma p7a_name_end : forall (x : list Z) i i', skipn i' x = PjGrammar.skip (skipn i x) -> (length x <= i')%nat ->
  ev_run0 (PjGrammar.jr_name true (skipn i x)) = None.
Proof. intros x i i' Hs Hl. rewrite ev_jr_name_obj, <- Hs, (skipn_all2 x Hl). reflexivity. Qed.

Lemma p7a_L_none : forall d n cap acc y, ev_run0 (PjGrammar.jr_name true y) = None ->
  ev_L d true n cap acc y = None.
Proof. intros d n cap acc y H. rewrite evp_L_step, H. reflexivity. Qed.

(* the key read: the string's closing quote at i' + 1 + c, in->p just past it *)
Lemma p7a_key_read : forall (x : list Z) i i' s rest c,
  skipn i' x = PjGrammar.skip (skipn i x) -> (i' < length x)%nat -> nth i' x 0 = 34 ->
  ev_run0 (PjGrammar.jr_string (skipn (S i') x)) = Some (s, rest) ->
  PjGrammar.scan (skipn (S i') x) = Some c -> rest = skipn (S c) (skipn (S i') x) ->
  ev_run0 (PjGrammar.jr_name true (skipn i x)) =
    match PjGrammar.skip (skipn (i' + c + 2) x) with c0 :: r1 => if c0 =? 58 then Some (s, r1) else None | [] => None end /\
  (i' + c + 2 <= length x)%nat.
Proof.
intros x i i' s rest c Hs Hl H34 Hjs Hsc Hr.
pose proof (p7a_scan_lt _ _ Hsc) as Hc. rewrite length_skipn in Hc.
split; [|lia].
rewrite (p7a_name_at x i i' Hs Hl), H34, Z.eqb_refl, Hjs, Hr, skipn_skipn.
replace (S c + S i')%nat with (i' + c + 2)%nat by lia. reflexivity.
Qed.

(* in->differs at C_KEY *)
Lemma p7a_dl_key0 : forall (a : ev_act) n nm dln dl1,
  (ev_v' (ea_v a) true (ea_t a) = 0 \/ (length (ev_kids (ea_t a)) <= n)%nat) ->
  ev_dl_kid a true n dln dl1 -> ev_dl_key a true n nm dln dl1.
Proof.
intros a n nm dln dl1 Hk (H01 & Hiff). split; [exact H01|]. rewrite Hiff.
destruct Hk as [Hv|Hl].
- split; intros [H|(H1 & H2)]; [left; exact H|exfalso; exact (H1 Hv)|left; exact H|exfalso; exact (H1 Hv)].
- split; intros [H|(H1 & H2)]; [left; exact H|right; split; [exact H1|left; exact Hl]|left; exact H|].
  right. split; [exact H1|exact Hl].
Qed.

Lemma p7a_dl_key_eq : forall (a : ev_act) n nm dln dl1,
  (n < length (ev_kids (ea_t a)))%nat -> fst (nth n (ev_kids (ea_t a)) ([], PjTree.JNull)) = nm ->
  ev_dl_kid a true n dln dl1 -> ev_dl_key a true n nm dln dl1.
Proof.
intros a n nm dln dl1 Hn Hnm (H01 & Hiff). split; [exact H01|]. rewrite Hiff.
split; intros [H|(H1 & H2)]; [left; exact H|lia|left; exact H|].
destruct H2 as [H2|(_ & H2)]; [lia|exfalso; exact (H2 Hnm)].
Qed.

Lemma p7a_dl_key_ne : forall (a : ev_act) n nm dln,
  ev_v' (ea_v a) true (ea_t a) <> 0 -> fst (nth n (ev_kids (ea_t a)) ([], PjTree.JNull)) <> nm ->
  ev_dl_key a true n nm dln 1.
Proof.
intros a n nm dln Hv Hne. split; [right; reflexivity|].
split; [intros _; right; split; [exact Hv|right; split; [reflexivity|exact Hne]]|intros _; reflexivity].
Qed.

(* ---- the refusal join's end (0x83b54 -> P_EXIT): s6 = the frame, s11 = -1, the reading refused ---- *)
Lemma p7a_exit_of : forall (a : ev_act) fxc W regs mem md ly S Hp k p dep' dl',
  ev_fx (fx := fx) fxc ->
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + p) dep' dl' -> ev_regs a regs ->
  getr regs 22 = w64 (ea_fr a) -> getr regs 27 = w64 (-1) ->
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = None ->
  0 <= p <= ea_len a -> ea_dep a <= dep' <= 33 -> (dl' = 0 \/ dl' = 1) ->
  ev_to_exit (fx := fx) B ARx SK a W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs EV_EXIT mem md).
Proof.
intros a fxc W regs mem md ly S Hp k p dep' dl' HFX HM HR H22 H27 HV Hp0 Hd Hdl.
exists fxc, regs, mem, md, ly, S, Hp, k, (-1), p, dep', dl'.
split; [reflexivity|]. split; [exact HFX|].
split; [exact HM|]. split; [exact HR|]. split; [exact H22|]. split; [exact H27|].
unfold ev_out. split; [exact Hdl|]. rewrite HV. split; [reflexivity|]. split; [exact Hp0|exact Hd].
Qed.

(* ---- the segment's carriers: the registers and the stack locals it keeps from C_KID to C_KEY ---- *)
Definition p7a_car (a : @ev_act rc A_prog_listing PA) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (n : nat) (kid : Z) : Prop :=
  ev_regs a regs /\
  getr regs 20 = w64 (shadow_addr (ea_q a + 8)) /\ getr regs 21 = w64 123 /\
  getr regs 22 = w64 EV_WSMASK /\ getr regs 27 = w64 32 /\ getr regs 23 = w64 (if kid =? 0 then 1 else 0) /\
  ev_spills a W mem true (ev_v' (ea_v a) true (ea_t a)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 96) 8 kid /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 104) 8 (ev_v' (ea_v a) true (ea_t a)) /\
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 120) 8 (Z.of_nat n).

Definition P7A_KEPT : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Lemma p7a_car_keep : forall a W regs mem n kid W' regs' mem',
  p7a_car a W regs mem n kid ->
  (forall r, In r P7A_KEPT -> getr regs' r = getr regs r) ->
  (forall z, ea_S1 a + 24 <= z < ea_S1 a + 128 -> aview SEGS (w_H W') mem' z = aview SEGS (w_H W) mem z) ->
  p7a_car a W' regs' mem' n kid.
Proof.
intros a W regs mem n kid W' regs' mem' (HR & H20 & H21 & H22 & H27 & H23 & HSP & V96 & V104 & V120) HK HM.
assert (VM : forall off v, 24 <= off -> off + 8 <= 128 ->
  val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + off) 8 v -> val_mem SEGS (mrestrict (w_H W') mem') (ea_S1 a + off) 8 v).
{ intros off v H1 H2. apply p7a_vm_av. intros z Hz. apply HM. lia. }
destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
destruct HSP as (S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
unfold p7a_car, ev_regs, ev_spills.
rewrite !HK by (cbv; tauto).
repeat split; try assumption; apply VM; try lia; assumption.
Qed.

(* the items' facts the segment carries unchanged *)
Definition p7a_item (a : @ev_act rc A_prog_listing PA) (n cap : nat) (acc : list (list Z * PjTree.jv)) (i : nat)
  (dln : Z) : Prop :=
  0 <= ea_dep a <= 31 /\ (n <= i)%nat /\ (i <= length (ea_x a))%nat /\ n = length acc /\
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) =
    ev_L (Nat.succ (Z.to_nat (ea_dep a))) true n cap acc (skipn i (ea_x a)) /\
  ev_dl (ea_dl a) (ea_v a) true (ea_t a) acc dln.

(* C_KEY from the carriers and the facts *)
Lemma p7a_key_of : forall a W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2,
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i1) (ea_dep a + 1) dl2 ->
  p7a_car a W regs mem n kid -> p7a_item a n cap acc i dln -> (i <= i1 <= length (ea_x a))%nat ->
  ev_run0 (PjGrammar.jr_name true (skipn i (ea_x a))) =
    match PjGrammar.skip (skipn i1 (ea_x a)) with c :: r1 => if c =? 58 then Some (nm, r1) else None | [] => None end ->
  ev_kid_ok a ly S W mem true n kid -> ev_dl_key a true n nm dln dl2 ->
  ev_at_key B ARx SK a W regs mem md ly S Hp k true n cap acc i i1 nm dln kid dl2.
Proof.
intros a W regs mem md ly S Hp k n cap acc i i1 nm dln kid dl2 HM
  (HR & H20 & H21 & H22 & H27 & H23 & HSP & V96 & V104 & V120) (Hd & Hni & Hil & Hna & HL & Hdl) Hi1 HN HK HD.
unfold ev_at_key. cbv zeta.
split; [reflexivity|]. split; [exact HM|]. split; [exact HR|]. split; [exact H20|]. split; [exact H21|].
split; [exact H22|]. split; [exact H27|]. split; [exact H23|]. split; [exact HSP|]. split; [exact V96|].
split; [exact V104|]. split; [exact V120|]. split; [exact Hd|]. split; [exact Hni|]. split; [lia|]. split; [lia|].
split; [exact Hna|]. split; [exact HL|]. split; [exact HN|]. split; [exact HK|]. split; [exact HD|exact Hdl].
Qed.

(* ---- the engine's view (helpers after lane NEXT's S8aItemsWalk.v at cb3bf00de8c :144-341, its ev8 lemmas) ----
   Numerals: 7364 (DERIVED: ex_value's listing offset, slot 1841 * 4 of bff8519b); atom indices 9-38 (DERIVED: the
   RISC-V ABI registers and Ereg's extra atoms from 32); 8, 1, 4 (LENGTH: access sizes); 3 (LENGTH: the granule
   shift); 5 (LENGTH: s1's 32-alignment as a log); 2 ^ 44, 2 ^ 47, 2 ^ 64, 4096, 64, 40 (DERIVED / LENGTH: shadow
   span, user-space top, word range, page floor, a margin, struct ex); 123, 34 (WORD: the opening brace, the quote);
   18446744073709551615 (WORD: -1 as a word). *)
Definition p7a_k (off : Z) : Z := 7364 + off.
Lemma p7a_pc : forall off, SIGMA AS_ex_value + off = BASE + p7a_k off.
Proof. intros off. assert (E : SIGMA AS_ex_value = BASE + 7364) by (vm_compute; reflexivity). unfold p7a_k. lia. Qed.

Lemma p7a_byte_eq : forall v (n k : nat), (k < n)%nat -> (n <= 8)%nat ->
  Z_to_bv 8 (YG0f.le_byte v n k) = byte_of_word (Z_to_bv 64 v) (Z.of_nat k).
Proof.
intros v n k Hk Hn. unfold byte_of_word. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with (2 ^ 8). change (bv_modulus 64) with (2 ^ 64). unfold YG0f.le_byte.
apply Z.bits_inj'. intros j Hj. change 256 with (2 ^ 8).
destruct (Z.lt_ge_cases j 8) as [E|E].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite !Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma p7a_chunk_of_val : forall E m base off (w : N) e v, (w <= 8)%N -> sv_denot E e = Z_to_bv 64 v ->
  val_mem SEGS m (base + off) (N.to_nat w) v -> YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)).
Proof.
intros E m base off w e v Hw He Hv i Hi. unfold YP09.c_len, YP09.cv_len in Hi. cbn [YP09.c_val YP09.c_off] in *.
exists (byte_of_word (sv_denot E e) i). split; [reflexivity|].
pose proof (Hv (Z.to_nat i) ltac:(lia)) as H. rewrite Z2Nat.id in H by lia. rewrite H.
f_equal. rewrite He. replace i with (Z.of_nat (Z.to_nat i)) at 2 by lia. apply p7a_byte_eq; lia.
Qed.
Lemma p7a_val_of_chunk : forall E m base off (w : N) e, (w <= 8)%N ->
  YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal w e)) ->
  val_mem SEGS m (base + off) (N.to_nat w) (bv_unsigned (sv_denot E e)).
Proof.
intros E m base off w e Hw Hc k Hk.
destruct (Hc (Z.of_nat k) ltac:(unfold YP09.c_len, YP09.cv_len; cbn [YP09.c_val]; lia)) as (b & Hb & Hm).
cbn [YP09.cbyte YP09.c_val YP09.c_off] in Hb, Hm. injection Hb as <-. rewrite Hm. f_equal.
pose proof (p7a_byte_eq (bv_unsigned (sv_denot E e)) (N.to_nat w) k Hk ltac:(lia)) as Hb.
rewrite Z_to_bv_bv_unsigned in Hb. symmetry. exact Hb.
Qed.
Lemma p7a_denot0 : forall E n v, ew E n = Z_to_bv 64 v -> sv_denot E (SOff n 0) = Z_to_bv 64 v.
Proof. intros E n v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma p7a_r0 : forall r : bv 5, bv_unsigned r <> 0 -> r <> 0%bv.
Proof. intros r H E. apply H. rewrite E. reflexivity. Qed.
Lemma p7a_vm1 : forall (H : word -> bool) mem z, aview SEGS H mem z = Some 0 -> val_mem SEGS (mrestrict H mem) z 1 0.
Proof.
intros H mem z E k Hk. assert (k = 0%nat) by lia. subst k. cbn [Z.of_nat]. rewrite Z.add_0_r.
unfold aview in E. destruct (mbyte SEGS (mrestrict H mem) z) as [b|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. rewrite E. reflexivity.
Qed.
Lemma p7a_ro_frame : forall E rs (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hin & Hr). rewrite forallb_forall in Hro.
specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.
Definition p7a_E (regs : bvmap 5 word) (xs : list Z) : env :=
  @Eimg _ A_prog_listing PA (Ereg regs (map (Z_to_bv 64) xs)).
Lemma p7a_ewr : forall regs xs (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r ->
  ew (p7a_E regs xs) n = getr regs r.
Proof. intros regs xs n r Hn Hr. unfold p7a_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_nat regs _ n r Hr). Qed.
Lemma p7a_ewx : forall regs xs j, (32 + j < A_TEXT)%nat -> ew (p7a_E regs xs) (32 + j) = Z_to_bv 64 (nth j xs 0).
Proof.
intros regs xs j Hj. unfold p7a_E. rewrite Eimg_low by exact Hj. rewrite ew_Ereg_extra.
change (Z_to_bv 64 0) with ((fun z => Z_to_bv 64 z) 0). rewrite map_nth. reflexivity.
Qed.
Lemma p7a_agree : forall regs xs, env_agree 32 (Ereg regs (map (Z_to_bv 64) xs)) (p7a_E regs xs).
Proof. intros. unfold p7a_E. split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]. Qed.
Lemma p7a_env : forall regs xs, img_env VAL A_LIM (p7a_E regs xs).
Proof. intros. unfold p7a_E. apply Eimg_env. Qed.
Lemma p7a_regs_ok : forall regs xs, regs_ok (p7a_E regs xs) sr_atoms regs.
Proof. intros. unfold p7a_E. apply regs_ok_Eimg_Ereg. Qed.
Lemma p7a_cfg_eq : forall (fxc : YK11.FPState) regs off mem md,
  ev_cfg (L := A_prog_listing) (PA := PA) fxc regs off mem md =
  mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k off)) mem (YK11.seg_rom SEGS)) md.
Proof. intros. unfold ev_cfg, ev_pc. rewrite p7a_pc. reflexivity. Qed.
Ltac p7a_awr_ro :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.

(* ---- the symbolic state at C_KID (0x83878): s5 = '{' pinned; atoms 32 = in->p = x0 + i, 33 = in->end = x0 + len;
   regions: the kid spill s1 + 96 (written by `sd a1,96(s1)`), in->p / in->end, the shadow bytes of q + 8 (s4) and
   of q (s10) ---- *)
Definition p7a_Bx : sv := SOff 24 0.
Definition p7a_Bspan : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
Definition p7a_fa_bx : nat * afact := (24%nat, mkAF SHADOW_OFF SHADOW_OFF 0).
Definition p7a_fa_s1 : nat * afact := (9%nat, mkAF kHighMemBeg (2 ^ 47) 5).
Definition p7a_fa_q : nat * afact := (19%nat, mkAF kHighMemBeg (2 ^ 47 - 40) 3).
Definition p7a_ss1 : sstate :=
  mkSS (p7a_k EV_KID) (sr_set sr_atoms 21%bv (SLit 123))
    [ YP09.mkRegion (Some 9%nat) 96 104 96 104 [];
      YP09.mkRegion (Some 19%nat) 0 16 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 8 (SOff 33 0))];
      YP09.mkRegion (Some 20%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))];
      YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))] ]
    None (mkFacts [p7a_fa_bx; p7a_fa_s1; p7a_fa_q; (32%nat, mkAF 4096 (2 ^ 47 - 64) 0);
                   (33%nat, mkAF 4096 (2 ^ 47 - 64) 0)] [] []).

Lemma p7a_st1 : forall (fxc : YK11.FPState) regs mem (W : world SEGS) (xi xe q s1 : Z),
  getr regs 9 = w64 s1 -> getr regs 19 = w64 q -> getr regs 20 = w64 (shadow_addr (q + 8)) ->
  getr regs 26 = w64 (shadow_addr q) -> getr regs 24 = w64 SHADOW_OFF -> getr regs 21 = w64 123 ->
  val_mem SEGS (mrestrict (w_H W) mem) q 8 xi -> val_mem SEGS (mrestrict (w_H W) mem) (q + 8) 8 xe ->
  val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr (q + 8)) 1 0 ->
  val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr q) 1 0 ->
  (forall z, s1 + 96 <= z < s1 + 104 -> writable_at SEGS (mrestrict (w_H W) mem) z) ->
  kHighMemBeg <= s1 -> s1 + 152 <= q -> q + 40 <= 2 ^ 47 -> s1 mod 32 = 0 -> q mod 8 = 0 ->
  4096 <= xi <= 2 ^ 47 - 64 -> 4096 <= xe <= 2 ^ 47 - 64 ->
  st_ok_pi (fx := fxc) SEGS VAL (p7a_E regs [xi; xe]) p7a_ss1
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k EV_KID)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W xi xe q s1 H9 H19 H20 H26 H24 H21 Vp Ve Vs8 Vs0 Wst Hs1 Hsq Hq47 Hs32 Hq8 Hxi Hxe.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5). pose proof Hs1 as Hs1v. unfold kHighMemBeg in Hs1v.
set (E := p7a_E regs [xi; xe]).
assert (ER : forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros; apply p7a_ewr; assumption).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (rewrite (ER 9%nat 9%bv) by (lia || reflexivity); exact H9).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (rewrite (ER 19%nat 19%bv) by (lia || reflexivity); exact H19).
assert (E20 : ew E 20 = Z_to_bv 64 (shadow_addr (q + 8))) by (rewrite (ER 20%nat 20%bv) by (lia || reflexivity); exact H20).
assert (E26 : ew E 26 = Z_to_bv 64 (shadow_addr q)) by (rewrite (ER 26%nat 26%bv) by (lia || reflexivity); exact H26).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (rewrite (ER 24%nat 24%bv) by (lia || reflexivity); exact H24).
assert (E32 : ew E 32 = Z_to_bv 64 xi) by (exact (p7a_ewx regs [xi; xe] 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 xe) by (exact (p7a_ewx regs [xi; xe] 1 ltac:(unfold A_TEXT; lia))).
assert (Hsh : SHADOW_OFF <= shadow_addr q /\ shadow_addr (q + 8) = shadow_addr q + 1 /\ shadow_addr q + 2 <= kHighMemBeg).
{ pose proof Hs1 as Hs1'. unfold kHighMemBeg in Hs1'.
  unfold shadow_addr. pose proof (Z.div_mod q 8 ltac:(lia)) as D. rewrite Hq8, Z.add_0_r in D.
  replace (q + 8) with ((q / 8 + 1) * 8) by lia. rewrite Z.div_mul by lia.
  assert (q / 8 < 2 ^ 44 - 1) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF, kHighMemBeg. lia. }
destruct Hsh as (Hsh0 & Hsh8 & Hsh2). unfold SHADOW_OFF, kHighMemBeg in Hsh0, Hsh2.
rewrite restrict_mkst_fx. unfold p7a_ss1.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply regs_ok_pin; [apply p7a_regs_ok|apply p7a_r0; vm_compute; discriminate|cbn [sv_denot]; exact H21].
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [lia|]. split; [lia|]. split; [intros z Hz; apply Wst; lia|constructor].
  + rewrite E19, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor; [|constructor]].
    * apply (p7a_chunk_of_val E _ q 0 8 (SOff 32 0) xi); [lia|exact (p7a_denot0 E 32 xi E32)|rewrite Z.add_0_r; exact Vp].
    * apply (p7a_chunk_of_val E _ q 8 8 (SOff 33 0) xe); [lia|exact (p7a_denot0 E 33 xe E33)|exact Ve].
  + rewrite E20, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ (shadow_addr (q + 8)) 0 1 (SLit 0) 0); [lia|reflexivity|rewrite Z.add_0_r; exact Vs8].
  + rewrite E26, unsigned_lit_small by (unfold kHighMemBeg in *; lia).
    split; [lia|]. split; [unfold kHighMemBeg in *; lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ (shadow_addr q) 0 1 (SLit 0) 0); [lia|reflexivity|rewrite Z.add_0_r; exact Vs0].
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, E19, E20, E26, !unsigned_lit_small by (unfold kHighMemBeg in *; lia).
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. unfold kHighMemBeg in *. repeat split; lia.
- split; [|split; [exact I | exact I]].
  cbn [f_atoms atoms_ok]. unfold p7a_fa_bx, p7a_fa_s1, p7a_fa_q, afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E24, E9, E19, E32, E33, !unsigned_lit_small by (unfold SHADOW_OFF, kHighMemBeg in *; lia).
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* ---- run plumbing: a run's write ranges, the chunks of its final state ---- *)
Lemma p7a_frame_slot : forall E rs (m m' : word -> option byte) lo hi, frame_of E rs m m' ->
  (forall z, YP09.in_wrange E rs z -> lo <= z < hi) -> forall x, ~ (lo <= bv_unsigned x < hi) -> m' x = m x.
Proof. intros E rs m m' lo hi HF Hw x Hx. apply HF. intros H. exact (Hx (Hw _ H)). Qed.
Lemma p7a_av_of_raw : forall (W : world SEGS) (m m' : word -> option byte) (P : Z -> Prop),
  (forall x : word, ~ P (bv_unsigned x) -> mrestrict (w_H W) m' x = mrestrict (w_H W) m x) ->
  forall z, 0 <= z < 2 ^ 64 -> ~ P z -> aview SEGS (w_H W) m' z = aview SEGS (w_H W) m z.
Proof.
intros W m m' P H z Hz Hn. apply aview_eq_of. apply H. rewrite unsigned_lit_small by lia. exact Hn.
Qed.
Lemma p7a_chunk_of_st : forall (fxc : YK11.FPState) E ss (ms : machine_state) (W : world SEGS) i r jj off (w : N) e,
  st_ok_pi (fx := fxc) SEGS VAL E ss (restrict (w_H W) ms) ->
  nth_error (ss_mem ss) i = Some r -> nth_error (YP09.r_chunks r) jj = Some (YP09.mkChunk off (CVal w e)) ->
  (w <= 8)%N ->
  val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (base_val E (YP09.r_base r) + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e)).
Proof.
intros fxc E ss ms W i r jj off w e HS Hr Hc Hw.
pose proof (st_ok_mem_ok SEGS E (abs_ss VAL ss) (restrict (w_H W) ms) HS) as (_ & Hall & _).
pose proof (proj1 (Forall_forall _ _) Hall r (nth_error_In _ i Hr)) as Hro.
destruct Hro as (_ & _ & _ & Hch).
pose proof (proj1 (Forall_forall _ _) Hch _ (nth_error_In _ jj Hc)) as Hck.
cbn [ms_mem restrict] in Hck |- *.
exact (p7a_val_of_chunk E _ _ off w e Hw Hck).
Qed.
Lemma p7a_cur_keep : forall (W W' : world SEGS) mem mem' q p e dep scr dl,
  prhex_cur W mem q p e dep scr dl ->
  (forall z, q <= z < q + 40 -> aview SEGS (w_H W') mem' z = aview SEGS (w_H W) mem z) ->
  prhex_cur W' mem' q p e dep scr dl.
Proof.
intros W W' mem mem' q p e dep scr dl (Q1 & Q2 & Q3 & Q4 & Q5) HK.
split; [apply p7a_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q1]|].
split; [apply p7a_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q2]|].
split; [apply p7a_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q3]|].
split; [apply p7a_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q4]|].
apply p7a_vm_av with (H := w_H W) (m := mem); [intros z Hz; apply HK; cbn in Hz; lia|exact Q5].
Qed.

(* ---- the cut 0x838f0 (offset 0x64c, the inlined ex_ws's exit) and the segment's post ---- *)
Definition p7a_Q (a : @ev_act rc A_prog_listing PA) (n cap : nat) (acc : list (list Z * PjTree.jv)) (i : nat)
  (dln kid : Z) : world SEGS -> config -> Prop :=
  fun W' c' => ev_to_exit (fx := fx) B ARx SK a W' c' \/
    exists fx' regs' mem' md' ly' S' Hp' k' i1 nm dl2,
      c' = ev_cfg (L := A_prog_listing) (PA := PA) fx' regs' EV_KEY mem' md' /\ ev_fx (fx := fx) fx' /\
      ev_at_key B ARx SK a W' regs' mem' md' ly' S' Hp' k' true n cap acc i i1 nm dln kid dl2.

Definition p7a_at_x (a : @ev_act rc A_prog_listing PA) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (n cap : nat)
  (acc : list (list Z * PjTree.jv)) (i i' : nat) (dln kid dl1 : Z) : Prop :=
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + Z.of_nat i') (ea_dep a + 1) dl1 /\
  p7a_car a W regs mem n kid /\ getr regs 11 = w64 (ea_x0 a + ea_len a) /\
  (i <= i' <= length (ea_x a))%nat /\ skipn i' (ea_x a) = PjGrammar.skip (skipn i (ea_x a)) /\
  p7a_item a n cap acc i dln /\ ev_kid_ok a ly S W mem true n kid /\ ev_dl_kid a true n dln dl1.

Definition p7a_x_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k n cap acc i i' dln kid dl1,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  p7a_at_x a W regs mem md ly S Hp k n cap acc i i' dln kid dl1 ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs 0x64c mem md) (p7a_Q a n cap acc i dln kid).

(* what run 1 (0x83878 -> 0x8389c -> 0x838f0 or 0x838a4) leaves: only the kid spill s1 + 96 written; memnorm at the
   run's end memory (the _inv runner's) *)
Lemma p7a_r1_post : forall a W regs mem md ly S Hp k n cap acc i dln kid dl1 regs' mem' md',
  ev_pre (fx := fx) B ARx a ->
  ev_at_kid B ARx SK a W regs mem md ly S Hp k true n cap acc i dln kid dl1 ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem' md' k ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ (ea_S1 a + 96 <= z < ea_S1 a + 104) ->
     aview SEGS (w_H W) mem' z = aview SEGS (w_H W) mem z) ->
  mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem') ->
  val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + 96) 8 kid ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
  getr regs' 21 = w64 123 ->
  YAkMemnorm.memnorm SEGS mem' ->
  ev_mid B ARx SK a ly S Hp W mem' md' k (ea_x0 a + Z.of_nat i) (ea_dep a + 1) dl1 /\
  p7a_car a W regs' mem' n kid /\ ev_kid_ok a ly S W mem' true n kid /\ p7a_item a n cap acc i dln /\
  ev_dl_kid a true n dln dl1.
Proof.
intros a W regs mem md ly S Hp k n cap acc i dln kid dl1 regs' mem' md' HPRE HK HJ' AV GROW V96 HKR H21' HMN'.
destruct HK as (HM & HR & H20 & H21 & H22 & H27 & H11 & H23 & HSP & V104 & V120 & Hd & Hni & Hil & Hna & HL & HKO &
  HDK & HDL).
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & _ & BQ & BQD & B47 & _ & BD0).
pose proof asan_consts as ((C1 & C2) & _).
assert (HWR : forall z, ea_S1 a + 96 <= z < ea_S1 a + 104 -> ea_S1 a - 2 * ESTACK <= z < ea_S1 a + 152 \/
  ea_q a <= z < ea_q a + 8 \/ ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36)
  by (intros z Hz; left; unfold ESTACK; lia).
split.
{ apply (p7a_mid_frame a ly S Hp W mem md k _ _ _ mem' md' _ _ _ (fun z => ea_S1 a + 96 <= z < ea_S1 a + 104)
    HPRE HM HJ' AV GROW HWR); [|exact HMN'].
  pose proof HM as (_ & _ & _ & _ & _ & HCUR & _).
  apply (p7a_cur_keep W W mem mem' _ _ _ _ _ _ HCUR). intros z Hz. apply AV; lia. }
split.
{ destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
  destruct HSP as (S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
  assert (VM : forall off v, (24 <= off /\ off + 8 <= 96) \/ (104 <= off /\ off + 8 <= 128) ->
    val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + off) 8 v ->
    val_mem SEGS (mrestrict (w_H W) mem') (ea_S1 a + off) 8 v).
  { intros off v Ho. apply p7a_vm_av. intros z Hz. apply AV; lia. }
  unfold p7a_car, ev_regs, ev_spills.
  split; [repeat split; (rewrite HKR by (cbv; tauto); assumption)|].
  split; [rewrite HKR by (cbv; tauto); exact H20|]. split; [exact H21'|].
  split; [rewrite HKR by (cbv; tauto); exact H22|]. split; [rewrite HKR by (cbv; tauto); exact H27|].
  split; [rewrite HKR by (cbv; tauto); exact H23|].
  split; [repeat split; (apply VM; [lia|assumption])|].
  split; [exact V96|]. split; [apply VM; [lia|exact V104]|apply VM; [lia|exact V120]]. }
split; [exact (p7a_kid_frame a ly S Hp W mem md k _ _ _ mem' _ true n kid HPRE HM AV HWR HKO)|].
split; [|exact HDK]. exact (conj Hd (conj Hni (conj Hil (conj Hna (conj HL HDL))))).
Qed.

(* a register of a run's final state, as its symbolic value *)
Ltac p7a_get HS r H :=
  lazymatch type of HS with st_ok_pi _ _ ?E' ?ss (restrict ?Hh ?ms) =>
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in
    pose proof (st_ok_pi_restrict_reg Hh E' ss ms r HS) as H;
    change (sr_get (ss_regs ss) r) with e in H; cbn [ms_regs restrict] in H end.
(* the write ranges of a run whose only writable region is s1's window [lo, hi) (atom 9, value s1) *)
Ltac p7a_slot9 E9 :=
  let z := fresh "z" in let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros z (r & Hin & Hr); vm_compute in Hin;
  repeat (destruct Hin as [<- | Hin]; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    try (rewrite E9, unsigned_lit_small in Hr by (unfold kHighMemBeg in *; lia)); lia|]);
  destruct Hin.
(* the write premise of a run whose only writable region (the first) is s1's window *)
Ltac p7a_awr9 E9 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 9%nat);
  [ reflexivity
  | rewrite E9, unsigned_lit_small by (unfold kHighMemBeg in *; lia); reflexivity
  | intros z Hz; cbn [YP09.r_wlo YP09.r_whi] in Hz; left; lia
  | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ].

Lemma p7a_kept_ws : forall r, In r P7A_KEPT -> r <> 10%bv /\ r <> 12%bv /\ r <> 13%bv /\ r <> 14%bv.
Proof.
intros r Hr. cbv [P7A_KEPT In] in Hr.
repeat (destruct Hr as [<-|Hr]; [repeat split; intros E; apply (f_equal (@bv_unsigned 5)) in E; vm_compute in E;
  discriminate|]).
destruct Hr.
Qed.

Ltac p7a_bvne := let Hne := fresh "Hne" in
  intros Hne; apply (f_equal (@bv_unsigned 5)) in Hne; vm_compute in Hne; discriminate.

(* the goal at a run's stop, after pmkst, as ev_cfg at offset off *)
Lemma p7a_cfg_eq' : forall (fxc : YK11.FPState) regs off mem md n, n = p7a_k off ->
  mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + n)) mem (YK11.seg_rom SEGS)) md =
  ev_cfg (L := A_prog_listing) (PA := PA) fxc regs off mem md.
Proof. intros fxc regs off mem md n ->. symmetry. apply p7a_cfg_eq. Qed.
Ltac p7a_cfg_to off :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst ?r (Z_to_bv 64 (_ + ?n)) ?m _; cfg_model := ?d |} _ =>
    rewrite (p7a_cfg_eq' _ r off m d n ltac:(vm_compute; reflexivity)) end.

(* the end of run 1's second stretch: the frame (only s1 + 96 written, over both stretches), the kept registers, s5,
   a1, the kid spill; the goal's machine state in mkst form. HF / HFr / HG are the stretch's run facts. *)
Ltac p7a_r1_end a regs xs HS HF HFr HG HM1 HG1 E9 E11 E33 :=
  let HM2 := fresh "HM2" in let Hgrow := fresh "Hgrow" in let Hav := fresh "Hav" in let HKR := fresh "HKR" in
  let N21 := fresh "N21" in let N11 := fresh "N11" in let V96 := fresh "V96" in
  pose proof (p7a_frame_slot _ _ _ _ (ea_S1 a + 96) (ea_S1 a + 104) HFr ltac:(p7a_slot9 E9)) as HM2;
  pose proof (mem_grows_trans _ _ _ HG1 HG) as Hgrow;
  pose proof (p7a_av_of_raw _ _ _ (fun z => ea_S1 a + 96 <= z < ea_S1 a + 104)
    (fun x Hx => eq_trans (HM2 x Hx) (HM1 x Hx))) as Hav;
  clear HF HFr HG HM2;
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv HS
    (p7a_agree regs xs) ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR;
  p7a_get HS (21%bv : bv 5) N21; p7a_get HS (11%bv : bv 5) N11; rewrite (p7a_denot0 _ 33 _ E33) in N11;
  pose proof (p7a_chunk_of_st _ _ _ _ _ 0%nat _ 0%nat 96 8%N (SOff 11 0) HS eq_refl eq_refl ltac:(lia)) as V96;
  cbn [YP09.r_base base_val N.to_nat Pos.to_nat] in V96;
  rewrite E9, (p7a_denot0 _ 11 _ E11), !unsigned_lit_small in V96 by lia;
  pmkst HS.

(* ---- RUN 1: C_KID 0x83878 -> 0x8389c (`bgeu a2,a1`): the text ended (-> 0x838f0) or into the inlined ex_ws
   (-> 0x838a4, the Section hypothesis WS, -> 0x838f0). Checks: 0x8387c `bne s5,a0` not taken (s5 = 123, the
   object path), 0x83884 / 0x83890 the shadow bytes of q + 8 / q read 0 (alx_zshadow_byte: `struct ex` on the real
   stack); the ex_ws loop's own arms 0x838cc / 0x838e8 are WS's. ---- *)
Lemma p7a_seg2_of_x : p7a_x_spec -> ev7_seg2_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof.
intros HX a fxc W regs mem md ly S Hp k n cap acc i dln kid dl1 HPRE HFX HK.
change (SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs EV_KID mem md) (p7a_Q a n cap acc i dln kid)).
pose proof HK as (HM & HR & H20 & H21 & H22 & H27 & H11 & H23 & HSP & V104 & V120 & Hd & Hni & Hil & Hna & HL & HKO &
  HDK & HDL).
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & S1al & BQ & BQD & B47 & Qal & BD0).
pose proof asan_consts as ((C1 & C2) & _).
pose proof (p7a_stk (ea_n a)) as HSTK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HSTK. unfold ESTACK in HSTK.
pose proof HM as (HJ & HWIN & HHP & HABL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HROOM & HRPOS & HMN).
pose proof HCUR as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HSRC as (_ & Hx4096 & Hxc & _).
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES & _).
destruct (ev_q_stack B ARx SK a ly S Hp W mem md k _ _ _ HPRE HM) as [Hqlo Hqhi].
assert (Vs0 : val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr (ea_q a)) 1 0).
{ apply p7a_vm1. exact (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md (ea_q a) HAR ltac:(lia)). }
assert (Vs8 : val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr (ea_q a + 8)) 1 0).
{ apply p7a_vm1. exact (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md (ea_q a + 8) HAR ltac:(lia)). }
assert (Wst : forall z, ea_S1 a + 96 <= z < ea_S1 a + 104 -> writable_at SEGS (mrestrict (w_H W) mem) z).
{ intros z Hz. apply (apresent_writable SEGS). apply HPRES. lia. }
assert (Hkid : 0 <= kid < 2 ^ 64).
{ destruct HKO as [(-> & _)|(_ & _ & Hk1 & Hk2 & _)]; lia. }
unfold ea_len in *. set (len := Z.of_nat (length (ea_x a))) in *.
set (xs := [ea_x0 a + Z.of_nat i; ea_x0 a + len]).
pose proof (p7a_st1 fxc regs mem W (ea_x0 a + Z.of_nat i) (ea_x0 a + len) (ea_q a) (ea_S1 a)
  R9 R19 H20 R26 R24 H21 Q1 Q2 Vs8 Vs0 Wst ltac:(unfold kHighMemBeg; lia) ltac:(lia) ltac:(lia) S1al Qal
  ltac:(lia) ltac:(lia)) as HS.
fold xs in HS.
set (E := p7a_E regs xs) in *.
assert (HEI : img_env VAL A_LIM E) by apply p7a_env.
assert (SHOK : sh_ok SEGS p7a_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E9 : ew E 9 = Z_to_bv 64 (ea_S1 a)) by (exact (eq_trans (p7a_ewr regs xs 9%nat 9%bv ltac:(lia) eq_refl) R9)).
assert (E32 : ew E 32 = Z_to_bv 64 (ea_x0 a + Z.of_nat i)) by (exact (p7a_ewx regs xs 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 (ea_x0 a + len)) by (exact (p7a_ewx regs xs 1 ltac:(unfold A_TEXT; lia))).
assert (E11 : ew E 11 = Z_to_bv 64 kid) by (exact (eq_trans (p7a_ewr regs xs 11%nat 11%bv ltac:(lia) eq_refl) H11)).
rewrite p7a_cfg_eq.
pose (RUN := paj_run_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
pose (RUNI := paj_run_x_inv (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := paj_run_to_x_inv (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
(* memnorm (HMN, ev_mid's last conjunct) is kept by the _inv runners to each run's end memory *)
paj_run_tok_x_inv RUNI HS HJ SHOK HMN p7a_Bspan; [p7a_awr9 E9|].
pose proof (p7a_frame_slot _ _ _ _ (ea_S1 a + 96) (ea_S1 a + 104) HFr ltac:(p7a_slot9 E9)) as HM1.
rename HG into HG1. clear HF HFr.
psrr_branch_tok RUN BR HS SHOK p7a_Bspan.
all: rewrite branch_geu_U, (U_atom _ 32 _ E32), (U_atom _ 33 _ E33) in Hc by lia.
- (* in->p >= in->end: the text has ended, i = len; to 0x838f0 *)
  apply negb_true_iff, Z.ltb_ge in Hc.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7a_Bspan (p7a_k 0x64c); [p7a_awr9 E9|].
  p7a_r1_end a regs xs HS HF HFr HG HM1 HG1 E9 E11 E33.
  p7a_cfg_to 0x64c.
  apply (HX a fxc W _ _ _ ly S Hp k n cap acc i i dln kid dl1 HPRE HFX).
  destruct (p7a_r1_post a W regs mem md ly S Hp k n cap acc i dln kid dl1 _ _ _ HPRE HK HJ Hav Hgrow V96 HKR N21 HMN)
    as (HM' & HC' & HKO' & HIT & HDK').
  split; [exact HM'|]. split; [exact HC'|]. split; [exact N11|]. split; [lia|].
  split; [rewrite (skipn_all2 (ea_x a)) by lia; reflexivity|]. split; [exact HIT|]. split; [exact HKO'|exact HDK'].
- (* in->p < in->end: `mv a0,a2` (0x838a0), into the inlined ex_ws at 0x838a4 *)
  apply negb_false_iff, Z.ltb_lt in Hc.
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7a_Bspan (p7a_k 0x600); [p7a_awr9 E9|].
  p7a_r1_end a regs xs HS HF HFr HG HM1 HG1 E9 E11 E33.
  p7a_get HS (10%bv : bv 5) N10. rewrite (p7a_denot0 E 32 _ E32) in N10.
  p7a_get HS (12%bv : bv 5) N12. rewrite (p7a_denot0 E 32 _ E32) in N12.
  p7a_cfg_to 0x600.
  destruct (p7a_r1_post a W regs mem md ly S Hp k n cap acc i dln kid dl1 _ _ _ HPRE HK HJ Hav Hgrow V96 HKR N21 HMN)
    as (HM' & HC' & HKO' & HIT & HDK').
  pose proof HC' as (HR' & _ & _ & H22' & H27' & _).
  eapply SRr_bind.
  { exact (WS 0x600 0x64c ltac:(left; reflexivity) a fxc W _ _ _ ly S Hp k i (ea_dep a + 1) dl1 HPRE HFX HM' HR'
      N10 N12 N11 H27' H22' ltac:(lia)). }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & i2 & -> & HM2' & Hii & Hsk & R10 & R12 & HK2 & HFR2).
  apply (HX a fxc W regs2 mem2 md2 ly S Hp k n cap acc i i2 dln kid dl1 HPRE HFX).
  assert (AV2 : forall z, 0 <= z < 2 ^ 64 -> ~ (ea_q a <= z < ea_q a + 8) ->
    aview SEGS (w_H W) mem2 z = aview SEGS (w_H W) _ z)
    by exact (p7a_av_of_raw W _ mem2 (fun z => ea_q a <= z < ea_q a + 8) HFR2).
  assert (HWR2 : forall z, ea_q a <= z < ea_q a + 8 -> ea_S1 a - 2 * ESTACK <= z < ea_S1 a + 152 \/
    ea_q a <= z < ea_q a + 8 \/ ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36)
    by (intros z Hz; right; left; exact Hz).
  split; [exact HM2'|].
  split.
  { apply (p7a_car_keep a W _ _ n kid W regs2 mem2 HC').
    - intros r Hr. destruct (p7a_kept_ws r Hr) as (N1 & N2 & N3 & N4). exact (HK2 r N1 N2 N3 N4).
    - intros z Hz. apply AV2; lia. }
  split; [rewrite (HK2 11%bv) by p7a_bvne; exact N11|].
  split; [exact Hii|]. split; [exact Hsk|]. split; [exact HIT|].
  split; [exact (p7a_kid_frame a ly S Hp W _ _ k _ _ _ mem2 _ true n kid HPRE HM' AV2 HWR2 HKO')|exact HDK'].
Qed.

(* ---- the cut 0x83924 (offset 0x680), just after `jal ex_string` returns: the string's outcome in a0 ---- *)
Definition p7a_at_s (a : @ev_act rc A_prog_listing PA) (W : world SEGS) (regs : bvmap 5 word)
  (mem : word -> option byte) (md : Model) (ly : alayout) (S : astate) (Hp : list Z) (k : Z) (n cap : nat)
  (acc : list (list Z * PjTree.jv)) (i i' : nat) (dln kid dl1 p' : Z) : Prop :=
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + p') (ea_dep a + 1) dl1 /\
  p7a_car a W regs mem n kid /\
  (i <= i' < length (ea_x a))%nat /\ skipn i' (ea_x a) = PjGrammar.skip (skipn i (ea_x a)) /\
  nth i' (ea_x a) 0 = 34 /\
  p7a_item a n cap acc i dln /\ ev_kid_ok a ly S W mem true n kid /\ ev_dl_kid a true n dln dl1 /\
  match ev_run0 (PjGrammar.jr_string (skipn (Datatypes.S i') (ea_x a))) with
  | None => getr regs 10 = w64 (-1) /\ p' = Z.of_nat i'
  | Some (s, rest) => getr regs 10 = w64 0 /\
      (exists c, PjGrammar.scan (skipn (Datatypes.S i') (ea_x a)) = Some c /\
         rest = skipn (Datatypes.S c) (skipn (Datatypes.S i') (ea_x a)) /\ p' = Z.of_nat i' + Z.of_nat c + 2) /\
      bytes_at W mem (ea_scr a) (s ++ [0])
  end.

Definition p7a_s_spec : Prop :=
  forall a fxc W regs mem md ly S Hp k n cap acc i i' dln kid dl1 p',
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  p7a_at_s a W regs mem md ly S Hp k n cap acc i i' dln kid dl1 p' ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs 0x680 mem md) (p7a_Q a n cap acc i dln kid).

(* ---- the symbolic states at 0x838f0 (0x64c): s1's frame spill (the refusal join reads it), in->p (atom 32), the
   shadow byte of q; with a byte left, the byte at in->p (atom 33). ---- *)
Definition p7a_rS1x : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 18 0))].
Definition p7a_rQp : YP09.region := YP09.mkRegion (Some 19%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))].
Definition p7a_rSq : YP09.region := YP09.mkRegion (Some 26%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SLit 0))].
Definition p7a_rTx : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition p7a_fa_p : nat * afact := (32%nat, mkAF 4096 (2 ^ 47 - 64) 0).
Definition p7a_GX : facts := mkFacts [p7a_fa_bx; p7a_fa_s1; p7a_fa_q; p7a_fa_p] [] [].
Definition p7a_ssXe : sstate := mkSS (p7a_k 0x64c) sr_atoms [p7a_rS1x; p7a_rQp; p7a_rSq] None p7a_GX.
Definition p7a_ssXb : sstate :=
  add_atom (mkSS (p7a_k 0x64c) sr_atoms (p7a_rTx :: [p7a_rS1x; p7a_rQp; p7a_rSq]) None p7a_GX) 33 (mkAF 0 255 0).

Lemma p7a_stXe : forall (fxc : YK11.FPState) regs mem (W : world SEGS) (xp c q s1 fr : Z),
  getr regs 9 = w64 s1 -> getr regs 19 = w64 q -> getr regs 26 = w64 (shadow_addr q) ->
  getr regs 24 = w64 SHADOW_OFF -> getr regs 18 = w64 fr ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 24) 8 fr -> val_mem SEGS (mrestrict (w_H W) mem) q 8 xp ->
  val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr q) 1 0 ->
  kHighMemBeg <= s1 -> s1 + 152 <= q -> q + 40 <= 2 ^ 47 -> s1 mod 32 = 0 -> q mod 8 = 0 ->
  4096 <= xp <= 2 ^ 47 - 64 ->
  st_ok_pi (fx := fxc) SEGS VAL (p7a_E regs [xp; c]) p7a_ssXe
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k 0x64c)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W xp c q s1 fr H9 H19 H26 H24 H18 Vf Vp Vs0 Hs1 Hsq Hq47 Hs32 Hq8 Hxp.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5). pose proof Hs1 as Hs1v. unfold kHighMemBeg in Hs1v.
set (E := p7a_E regs [xp; c]).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (exact (eq_trans (p7a_ewr regs _ 9%nat 9%bv ltac:(lia) eq_refl) H9)).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (exact (eq_trans (p7a_ewr regs _ 19%nat 19%bv ltac:(lia) eq_refl) H19)).
assert (E26 : ew E 26 = Z_to_bv 64 (shadow_addr q)) by (exact (eq_trans (p7a_ewr regs _ 26%nat 26%bv ltac:(lia) eq_refl) H26)).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (exact (eq_trans (p7a_ewr regs _ 24%nat 24%bv ltac:(lia) eq_refl) H24)).
assert (E18 : ew E 18 = Z_to_bv 64 fr) by (exact (eq_trans (p7a_ewr regs _ 18%nat 18%bv ltac:(lia) eq_refl) H18)).
assert (E32 : ew E 32 = Z_to_bv 64 xp) by (exact (p7a_ewx regs [xp; c] 0 ltac:(unfold A_TEXT; lia))).
assert (Hsh : SHADOW_OFF <= shadow_addr q /\ shadow_addr q + 2 <= kHighMemBeg).
{ unfold shadow_addr. pose proof (Z.div_mod q 8 ltac:(lia)) as D. rewrite Hq8, Z.add_0_r in D.
  assert (q / 8 < 2 ^ 44 - 1) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF, kHighMemBeg. lia. }
destruct Hsh as (Hsh0 & Hsh2). unfold SHADOW_OFF, kHighMemBeg in Hsh0, Hsh2.
rewrite restrict_mkst_fx. unfold p7a_ssXe, p7a_rS1x, p7a_rQp, p7a_rSq.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply p7a_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ s1 24 8 (SOff 18 0) fr); [lia|exact (p7a_denot0 E 18 fr E18)|exact Vf].
  + rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ q 0 8 (SOff 32 0) xp); [lia|exact (p7a_denot0 E 32 xp E32)|rewrite Z.add_0_r; exact Vp].
  + rewrite E26, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ (shadow_addr q) 0 1 (SLit 0) 0); [lia|reflexivity|rewrite Z.add_0_r; exact Vs0].
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, E19, E26, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I | exact I]].
  unfold p7a_GX, p7a_fa_bx, p7a_fa_s1, p7a_fa_q, p7a_fa_p. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E24, E9, E19, E32, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF, kHighMemBeg. repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

Lemma p7a_stXb : forall (fxc : YK11.FPState) regs mem (W : world SEGS) (xp c q s1 fr : Z),
  getr regs 9 = w64 s1 -> getr regs 19 = w64 q -> getr regs 26 = w64 (shadow_addr q) ->
  getr regs 24 = w64 SHADOW_OFF -> getr regs 18 = w64 fr ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 24) 8 fr -> val_mem SEGS (mrestrict (w_H W) mem) q 8 xp ->
  val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr q) 1 0 -> val_mem SEGS (mrestrict (w_H W) mem) xp 1 c ->
  kHighMemBeg <= s1 -> s1 + 152 <= q -> q + 40 <= 2 ^ 47 -> s1 mod 32 = 0 -> q mod 8 = 0 ->
  4096 <= xp <= 2 ^ 47 - 64 -> 0 <= c <= 255 -> xp + 1 <= s1 -> (xp + 1 <= kLowMemEnd \/ kHighMemBeg <= xp) ->
  st_ok_pi (fx := fxc) SEGS VAL (p7a_E regs [xp; c]) p7a_ssXb
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k 0x64c)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W xp c q s1 fr H9 H19 H26 H24 H18 Vf Vp Vs0 Vc Hs1 Hsq Hq47 Hs32 Hq8 Hxp Hc Hxs Happ.
pose proof (p7a_stXe fxc regs mem W xp c q s1 fr H9 H19 H26 H24 H18 Vf Vp Vs0 Hs1 Hsq Hq47 Hs32 Hq8 Hxp) as HS.
pose proof asan_consts as ((C1 & C2) & _ & _ & _ & C5). pose proof Hs1 as Hs1v. unfold kHighMemBeg in Hs1v.
set (E := p7a_E regs [xp; c]) in *.
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (exact (eq_trans (p7a_ewr regs _ 9%nat 9%bv ltac:(lia) eq_refl) H9)).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (exact (eq_trans (p7a_ewr regs _ 19%nat 19%bv ltac:(lia) eq_refl) H19)).
assert (E26 : ew E 26 = Z_to_bv 64 (shadow_addr q)) by (exact (eq_trans (p7a_ewr regs _ 26%nat 26%bv ltac:(lia) eq_refl) H26)).
assert (E32 : ew E 32 = Z_to_bv 64 xp) by (exact (p7a_ewx regs [xp; c] 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 c) by (exact (p7a_ewx regs [xp; c] 1 ltac:(unfold A_TEXT; lia))).
assert (Hsh : SHADOW_OFF <= shadow_addr q /\ shadow_addr q + 2 <= kHighMemBeg).
{ unfold shadow_addr. pose proof (Z.div_mod q 8 ltac:(lia)) as D. rewrite Hq8, Z.add_0_r in D.
  assert (q / 8 < 2 ^ 44 - 1) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos q 8 ltac:(lia) ltac:(lia)).
  unfold SHADOW_OFF, kHighMemBeg. lia. }
destruct Hsh as (Hsh0 & Hsh2). unfold SHADOW_OFF, kHighMemBeg, kLowMemEnd in Hsh0, Hsh2, Happ.
unfold p7a_ssXb. apply st_ok_pi_add_fact.
- refine (st_ok_pi_add_region E p7a_ssXe _ p7a_rTx HS eq_refl _ _).
  + unfold region_ok, p7a_rTx. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val restrict ms_mem].
    rewrite E32, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ xp 0 1 (SOff 33 0) c); [lia|exact (p7a_denot0 E 33 c E33)|rewrite Z.add_0_r; exact Vc].
  + apply all_disjoint_of_extents. unfold extent_of_region, p7a_ssXe, p7a_rS1x, p7a_rQp, p7a_rSq, p7a_rTx.
    cbn [ss_mem map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite E9, E19, E26, E32, !unsigned_lit_small by lia.
    cbn [zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E33, unsigned_lit_small by lia.
  rewrite Z.pow_0_r, Z.mod_1_r. lia.
Qed.

(* the text byte's shadow check (0x8390c, with its partial-granule arm 0x83b1c-0x83b24): ev_mid's src_rd keeps the text
   addressable (S8aItemsWalk.v ev8_ob_txt at atom 32) *)
Lemma p7a_ob_txt : forall a ly S Hp W mem md k p dep dl E xp,
  ev_mid B ARx SK a ly S Hp W mem md k p dep dl ->
  ew E 24 = Z_to_bv 64 SHADOW_OFF -> ew E 32 = Z_to_bv 64 xp -> ea_x0 a <= xp < ea_x0 a + ea_len a ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) mem)) (U E p7a_Bx) (U E (SOff 32 0)) 1.
Proof.
intros a ly S Hp W mem md k p dep dl E xp HM H24 H32 Hx.
pose proof HM as (_ & _ & _ & _ & _ & _ & (_ & H4 & Hc & _ & HRA & _) & _).
pose proof asan_consts as ((C1 & C1') & _).
change (Z.of_nat (length (ea_x a))) with (ea_len a) in *.
unfold p7a_Bx. rewrite (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
rewrite (U_atom E 32 xp H32) by lia.
rewrite <- aview_rd_of. intros x Hx'. apply HRA. lia.
Qed.

(* ex_string's entry, as an offset from ex_value's (0xd90, LENGTH: 0x84034 - 0x832a4 on the bff8519b listing) *)
Lemma p7a_str_pc : SIGMA AS_ex_string = BASE + p7a_k 0xd90.
Proof. vm_compute. reflexivity. Qed.

Lemma p7a_ro_mem : forall E rs (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> m' = m.
Proof.
intros E rs m m' Hro HF. apply FunctionalExtensionality.functional_extensionality. intros x.
exact (p7a_ro_frame E rs m m' Hro HF x).
Qed.

(* the end of a refusal arm (0x83b54: `ld s6,24(s1)`, `li s11,-1`, `j 0x83d48`): P_EXIT with the memory as it was *)
Lemma p7a_exit_goal : forall a fxc W regs regs' mem md md' ly S Hp k p dep' dl' n cap acc i dln kid,
  ev_fx (fx := fx) fxc ->
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + p) dep' dl' ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem md' k ->
  ev_regs a regs -> (forall r, In r [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv -> getr regs' r = getr regs r) ->
  getr regs' 22 = w64 (ea_fr a) -> getr regs' 27 = w64 (-1) ->
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = None ->
  0 <= p <= ea_len a -> ea_dep a <= dep' <= 33 -> (dl' = 0 \/ dl' = 1) ->
  SRr SEGS W (ev_cfg (L := A_prog_listing) (PA := PA) fxc regs' EV_EXIT mem md') (p7a_Q a n cap acc i dln kid).
Proof.
intros a fxc W regs regs' mem md md' ly S Hp k p dep' dl' n cap acc i dln kid HFX HM HJ' HR HK H22 H27 HV Hp0 Hd Hdl.
apply SRr_ret. left.
apply (p7a_exit_of a fxc W regs' mem md' ly S Hp k p dep' dl' HFX); try assumption.
- destruct HM as (_ & HMr). exact (conj HJ' HMr).
- destruct HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26). unfold ev_regs.
  rewrite !HK by (cbv; tauto). repeat split; assumption.
Qed.

Lemma p7a_wm1 : w64 (-1) = Z_to_bv 64 18446744073709551615.
Proof. apply bv_eq. unfold w64. rewrite !Z_to_bv_unsigned. reflexivity. Qed.

(* after a read-only stretch: the memory is still mem *)
Ltac p7a_ro_step Hm :=
  lazymatch goal with HF : frame_of _ _ (ms_mem ?m0) (ms_mem ?m1) |- _ =>
    let H := fresh "Hmr" in
    assert (H : ms_mem m1 = ms_mem m0) by (eapply p7a_ro_mem; [|exact HF]; vm_compute; reflexivity);
    rewrite Hm in H; clear Hm; rename H into Hm
  end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.
(* the same after a first read-only stretch from the memory m *)
Ltac p7a_ro_first m Hm :=
  lazymatch goal with HF : frame_of _ _ m (ms_mem ?m1) |- _ =>
    assert (Hm : ms_mem m1 = m) by (eapply p7a_ro_mem; [|exact HF]; vm_compute; reflexivity)
  end;
  repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.

(* the refusal arm's stop at P_EXIT, after a read-only run: Hm is the memory equation of the run's start *)
Ltac p7a_exit_fin a fxc regs xs HS HJ HM HR HFX Hm E18 :=
  let HKR := fresh "HKR" in let N22 := fresh "N22" in let N27 := fresh "N27" in
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 24; 25; 26]%bv HS
    ltac:(env_agree_chain (p7a_agree regs xs)) ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR;
  prreg HS (22%bv : bv 5) N22; prreg HS (27%bv : bv 5) N27;
  rewrite E18 in N22;
  pmkst HS; p7a_cfg_to EV_EXIT; rewrite Hm in HJ |- *;
  eapply (p7a_exit_goal a fxc _ regs _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HFX HM HJ HR HKR N22
    ltac:(rewrite N27, p7a_wm1; reflexivity)).

Lemma p7a_x_of : p7a_s_spec -> p7a_x_spec.
Proof.
intros HSS a fxc W regs mem md ly S Hp k n cap acc i i' dln kid dl1 HPRE HFX HXa.
pose proof HXa as (HM & HC & H11 & Hii & Hsk & HIT & HKO & HDK).
pose proof HC as (HR & H20 & H21 & H22 & H27 & H23 & HSP & V96 & V104 & V120).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HSP as (S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
pose proof HM as (HJ & HWIN & HHP & HABL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HROOM & HRPOS & HMN).
pose proof HCUR as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof HSRC as (HBY & Hx4096 & Hxc & HAM & HRA & HHU).
pose proof HIT as (Hd & Hni & Hil & Hna & HL & Hdl).
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & S1al & BQ & BQD & B47 & Qal & BD0).
pose proof HPRE as HP. unfold ev_pre in HP. cbv zeta in HP.
destruct HP as ((HAF & HARO & _) & Hfrm0 & Hcnt0 & HE10 & HE11 & HCur0 & Hq8 & HCHA0 & Hspq & Hqd & Hfw & Hsrc0 & Hinb0
  & Hlen0 & Hi00 & Hdep0 & Hdepn0 & Hdl00 & Hwd0 & Hinb20 & Hd10 & Hd20 & Htree0 & Hled0 & _).
pose proof HAF as (HAR0 & _ & Hra4 & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hsp16 & _).
pose proof Hfw as (Hd0 & Hd16 & Hdtop & _).
pose proof asan_consts as ((C1 & C2) & _).
pose proof (p7a_stk (ea_n a)) as HSTK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HSTK. unfold ESTACK in HSTK.
pose proof (p7a_stks (ea_n a)) as HSTKS. change (STK_ex_value (ea_n a)) with (ea_STK a) in HSTKS.
pose proof (p7a_s1_lo a Hsp16) as HS1lo.
pose proof HJ as (HAR & _).
destruct (ev_q_stack B ARx SK a ly S Hp W mem md k _ _ _ HPRE HM) as [Hqlo Hqhi].
assert (Vs0 : val_mem SEGS (mrestrict (w_H W) mem) (shadow_addr (ea_q a)) 1 0).
{ apply p7a_vm1. exact (alx_zshadow_byte _ _ _ LAWS ly S Hp W mem md (ea_q a) HAR ltac:(lia)). }
unfold ea_len in *. set (len := Z.of_nat (length (ea_x a))) in *.
assert (Hfr : 0 <= ea_fr a < 2 ^ 64).
{ assert (HIN : In (1, ea_pos a) (frames S)).
  { pose proof HJ as (_ & _ & _ & _ & _ & HFR & _). rewrite HFR. left. reflexivity. }
  destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR HIN) as (F0 & F1 & _).
  pose proof HJ as (_ & HLY & _). pose proof HLY as (_ & _ & _ & _ & _ & ELF & _).
  assert (EF : frame_addr ly 1 (ea_pos a) = ea_fr a) by (unfold ea_fr, frame_addr; rewrite ELF; reflexivity).
  rewrite EF in F0, F1. assert (FB : fs_frame_bytes 1 = 128) by reflexivity. rewrite FB in F1. lia. }
assert (HV0 : ev_run0 (PjGrammar.jr_name true (skipn i (ea_x a))) = None ->
  prhex_V (ea_dep a) (skipn (Z.to_nat (ea_i0 a)) (ea_x a)) = None).
{ intros Hn. rewrite HL. apply p7a_L_none. exact Hn. }
rewrite p7a_cfg_eq.
pose (RUN := paj_run_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
pose (RUNI := paj_run_x_inv (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := paj_run_to_x_inv (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
(* the runs up to the call are read-only: HMNr carries memnorm through the _inv runners, HMN stays at mem *)
pose proof HMN as HMNr.
destruct (Nat.lt_ge_cases i' (length (ea_x a))) as [Hlt | Hge].
- (* a byte left *)
  set (c := nth i' (ea_x a) 0).
  destruct (HBY i' Hlt) as (Vc & Hc255). fold c in Vc, Hc255.
  set (xs := [ea_x0 a + Z.of_nat i'; c]).
  pose proof (p7a_stXb fxc regs mem W (ea_x0 a + Z.of_nat i') c (ea_q a) (ea_S1 a) (ea_fr a)
    R9 R19 R26 R24 R18 S24 Q1 Vs0 Vc ltac:(unfold kHighMemBeg; lia) ltac:(lia) ltac:(lia) S1al Qal
    ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold amem_range, kLowMemEnd, kHighMemBeg in *; lia)) as HS.
  fold xs in HS.
  set (E := p7a_E regs xs) in *.
  assert (HEI : img_env VAL A_LIM E) by apply p7a_env.
  assert (SHOK : sh_ok SEGS p7a_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (exact (eq_trans (p7a_ewr regs xs 24%nat 24%bv ltac:(lia) eq_refl) R24)).
  assert (E11 : ew E 11 = Z_to_bv 64 (ea_x0 a + len)) by (exact (eq_trans (p7a_ewr regs xs 11%nat 11%bv ltac:(lia) eq_refl) H11)).
  assert (E18 : ew E 18 = Z_to_bv 64 (ea_fr a)) by (exact (eq_trans (p7a_ewr regs xs 18%nat 18%bv ltac:(lia) eq_refl) R18)).
  assert (E19 : ew E 19 = Z_to_bv 64 (ea_q a)) by (exact (eq_trans (p7a_ewr regs xs 19%nat 19%bv ltac:(lia) eq_refl) R19)).
  assert (E32 : ew E 32 = Z_to_bv 64 (ea_x0 a + Z.of_nat i')) by (exact (p7a_ewx regs xs 0 ltac:(unfold A_TEXT; lia))).
  assert (E33 : ew E 33 = Z_to_bv 64 c) by (exact (p7a_ewx regs xs 1 ltac:(unfold A_TEXT; lia))).
  paj_run_tok_x_inv RUNI HS HJ SHOK HMNr p7a_Bspan; [p7a_awr_ro|].
  assert (Hm1 : ms_mem ms = mem) by (eapply p7a_ro_mem; [|exact HF]; vm_compute; reflexivity). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK p7a_Bspan.
  all: rewrite branch_geu_U, (U_atom _ 32 _ E32), (U_atom _ 11 _ E11) in Hc by lia.
  + apply negb_true_iff, Z.ltb_ge in Hc. exfalso. lia.
  + apply negb_false_iff, Z.ltb_lt in Hc. rename Hc into Hplt.
    (* 0x83900-0x83918: the text byte's shadow check (obligation), `lbu`, `li a1,34`, the `bne` *)
    paj_run_tok_x_inv RUNI HS HJ SHOK HMNr p7a_Bspan;
      [rewrite Hm1; exact (p7a_ob_txt a ly S Hp W mem md k _ _ _ E _ HM E24 E32 ltac:(unfold ea_len; fold len; lia)) | p7a_awr_ro |].
    p7a_ro_step Hm1.
    psrr_branch_tok RUN BR HS SHOK p7a_Bspan.
    all: rewrite branch_ne_U, U_SLit in Hc; change (zcanon 34) with 34 in Hc;
      match type of Hc with context [U ?E' (SOff 33 0)] =>
        let Hx := fresh "Hx" in assert (Hx : ew E' 33 = Z_to_bv 64 c) by (cbn [ew ewset Nat.eqb extK]; exact E33);
        rewrite (U_atom E' 33 c Hx) in Hc by lia; clear Hx end.
    * (* not a quote: the refusal join *)
      apply negb_true_iff, Z.eqb_neq in Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMNr p7a_Bspan (p7a_k EV_EXIT); [p7a_awr_ro|].
      p7a_ro_step Hm1. p7a_exit_fin a fxc regs xs HS HJ HM HR HFX Hm1 E18.
      -- apply HV0. rewrite (p7a_name_at (ea_x a) i i' Hsk Hlt). fold c. rewrite (proj2 (Z.eqb_neq c 34) Hc). reflexivity.
      -- unfold ea_len; fold len; lia.
      -- lia.
      -- exact (proj1 HDK).
    * (* a quote: `mv a0,s3; jal ex_string` *)
      apply negb_false_iff, Z.eqb_eq in Hc.
      paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMNr p7a_Bspan (p7a_k 0xd90); [p7a_awr_ro|].
      p7a_ro_step Hm1.
      (* at ex_string's entry (0x84034): a0 = q, ra = 0x83924; the memory as it was *)
      pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ P7A_KEPT HS
        ltac:(env_agree_chain (p7a_agree regs xs)) ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
      prreg HS (10%bv : bv 5) N10. prreg HS (1%bv : bv 5) N1. rewrite E19 in N10.
      pmkst HS. rewrite Hm1 in HJ |- *.
      lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst ?r _ _ _; cfg_model := ?d |} _ =>
        set (regsc := r) in *; set (mdX := d) in * end.
      pose proof (conj HJ (proj2 HM) : ev_mid B ARx SK a ly S Hp W mem mdX k (ea_x0 a + Z.of_nat i') (ea_dep a + 1) dl1)
        as HMX.
      assert (GSP : spZ regsc = ea_S1 a).
      { unfold spZ. rewrite (HKR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
      assert (GS0 : s0Z regsc = ea_sp0 a).
      { unfold s0Z. rewrite (HKR 8%bv ltac:(cbv; tauto)), R8. unfold w64. apply unsigned_lit_small. lia. }
      assert (Hs160 : STK_ex_string = 160) by (vm_compute; reflexivity).
      set (o1 := ea_S1 a - (ea_sp0 a + ea_d a)).
      set (e1 := ea_sp0 a + ea_d a - ea_S1 a).
      set (ch1 := (ea_sp0 a, raZ (ea_regs a), s0Z (ea_regs a)) :: ea_ch a).
      set (FP1 := [(ea_scr a, ea_scr a + len + 1); (ea_q a, ea_q a + 8)]).
      pose proof HWD as (HD0 & HDC & HAM' & HWW & HRA' & HHU').
      assert (HFP1 : forall z, inFP FP1 z -> inFP (ea_FP a) z).
      { intros z Hz. unfold FP1, ea_FP in *. unfold ea_len. fold len. rewrite !inFP_cons in Hz |- *.
        destruct Hz as [Hz|[Hz|Hz]]; [left; exact Hz|right; left; exact Hz|destruct (inFP_nil _ Hz)]. }
      assert (GRA : getr regsc 1 = Z_to_bv 64 (BASE + p7a_k 0x680)) by (rewrite N1; reflexivity).
      eapply SRr_bind.
      { eapply (@aj_call_xW fxc rc SK SEGS B PST ARx cf_head LAWS ev_segs_low W regsc mem (SIGMA AS_ex_string)
          (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a)
          [(1, ea_pos a)] ly S Hp _ k STK_ex_string e1 FP1 o1 (Z_to_bv 64 (BASE + p7a_k 0x680)) ch1 _ HJ).
        - unfold o1. rewrite GSP. lia.
        - unfold o1. exact (p7a_mod16 _ _ _ S1al Hsp16 Hd16).
        - unfold o1. lia.
        - lia.
        - unfold o1. lia.
        - unfold e1. lia.
        - unfold e1. exact (p7a_mod16' _ _ _ S1al Hsp16 Hd16).
        - unfold o1, e1. lia.
        - rewrite (HKR 3%bv ltac:(cbv; tauto)), R3. exact Hgp0.
        - rewrite (HKR 4%bv ltac:(cbv; tauto)), R4. exact Htp0.
        - rewrite N1. reflexivity.
        - apply (ret_ok_codeptr_v (PI := PA)); [unfold p7a_k; lia | reflexivity].
        - apply Z.leb_le. vm_compute. reflexivity.
        - unfold o1. replace (ea_sp0 a + ea_d a + (ea_S1 a - (ea_sp0 a + ea_d a))) with (ea_S1 a) by lia.
          rewrite GS0. exact (p7a_chain_call a ly S Hp W mem _ k _ _ _ HPRE HMX (aview SEGS (w_H W) mem) (fun x _ => eq_refl)).
        - intros HPRE' HWIN'.
          eapply (STR fxc ly S Hp W regsc mem _ ch1 (ea_q a) (ea_x0 a) (Z.of_nat i') (ea_scr a) e1 (ea_x a)
            (ea_Lam a) (ea_peak a) (ea_cnt a) (ea_fail a) (ea_ran a) (ea_most a) (ea_own a)).
          + split; [exact HPRE'|]. split.
            { eapply ev_aro_kept; [exact HJ | | exact p7a_pst_not_ro | exact HARO].
              apply ev_fp_closed. unfold ea_FP.
              assert (Hscr : 4096 <= ea_scr a).
              { destruct Hinb20 as (b0 & m0 & Hbm & Hb0 & _ & _).
                destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ b0 m0 HAR0 Hbm) as (_ & H4096 & _). lia. }
              repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil. }
            (* PRH_Base.fpre's two conjuncts added at walkkit old-pin be60d536d2af: the callee's sp is the body's S1, 64
               or more below the stack's top (S1 + 152 <= sp0 <= q, q + 40 <= ly_stk_hi: ev_bounds, ev_q_stack); its ra
               is the jal's return pc, a listing literal below the ceiling's least value *)
            split; [rewrite GSP; lia|].
            split.
            { unfold raZ. rewrite GRA.
              apply (Z.lt_le_trans _ 0x7fff7f800000); [apply Z.ltb_lt; vm_compute; reflexivity | exact C1]. }
            (* FRM0-ENTRY (kit f97c8b2f046b, PRH_Base.v fdb45545469b: fpre's last conjunct): the rounding mode at
               ex_string's entry is the caller's, frm 0 by ev_fx *)
            exact (proj1 HFX).
          + exact N10.
          + exact Q1.
          + exact Q2.
          + exact Q4.
          + exact Qal.
          + rewrite GSP. lia.
          + rewrite GSP. unfold e1. lia.
          + exact HWIN'.
          + exact HSRC.
          + (* the text is not empty: a quote is read at x0 + i' < x0 + len *)
            unfold prhex_inblk in *. rewrite HABL, HHP. apply Hinb0. unfold ea_len in *. lia.
          + exact Hlen0.
          + lia.
          + split; [exact HD0|]. split; [exact HDC|]. split; [exact HAM'|].
            split; [|split; [exact HRA' | exact HHU']].
            intros z Hz. destruct (HWW z Hz) as (Hw1 & Hw2 & _). split; [exact Hw1|]. split; [exact Hw2|].
            rewrite GSP. lia.
          + unfold prhex_inblk in *. rewrite HABL, HHP. exact Hinb20.
          + exact Hd10.
          + exact Hd20.
          + exact HLED.
        - intros z Hz. left. exact (HFP1 z Hz). }
      (* ---- ex_string returned: 0x83924 ---- *)
      (* tex_string_specX's post is fpostWm (walkkit old-pin): its Q, with S' = S after Hp' = Hp, and the memnorm keep *)
      cbv beta. intros W2 c2 _ (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & k1 & -> & HJ2 & HJ1 & HX & HPres & HK).
      cbv beta delta [fQmn] in HK. destruct HK as ((HRL2 & EHP & ES2 & EAB & HLED2 & HMT) & HKEEP).
      rewrite <- p7a_cfg_eq.
      assert (ES1 : ea_sp0 a + ea_d a + o1 + e1 = ea_S1 a + e1) by (unfold o1; lia).
      rewrite ES1 in HJ1.
      assert (HX' : forall z, ea_S1 a <= z < ea_S1 a + e1 -> ~ inFP FP1 z ->
        aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
      { intros z Hz Hn. apply HX; [unfold o1; lia | exact Hn]. }
      pose proof HJ2 as (HAR2 & _).
      assert (HKS : forall z, ea_S1 a + 24 <= z < ea_S1 a + 152 -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
      { intros z Hz. apply HX'; [unfold e1; lia|]. unfold FP1. rewrite !inFP_cons.
        intros [Hf|[Hf|Hf]]; [lia|lia|destruct (inFP_nil _ Hf)]. }
      assert (HKQ : forall z, ea_q a + 8 <= z < ea_q a + 40 -> aview SEGS (w_H W2) mem2 z = aview SEGS (w_H W) mem z).
      { intros z Hz. apply HX'; [unfold e1; lia|]. unfold FP1. rewrite !inFP_cons.
        intros [Hf|[Hf|Hf]]; [lia|lia|destruct (inFP_nil _ Hf)]. }
      assert (HC2 : p7a_car a W2 regs2 mem2 n kid).
      { apply (p7a_car_keep a W regs mem n kid W2 regs2 mem2 HC).
        - intros r Hr. rewrite (p7a_pres_get _ _ HPres r).
          + exact (HKR r Hr).
          + cbv [P7A_KEPT In] in Hr.
            repeat (destruct Hr as [<-|Hr]; [unfold acallee_saved; vm_compute (bv_unsigned _); lia|]). destruct Hr.
        - intros z Hz. apply HKS. lia. }
      pose proof (p7a_kid_call a ly S Hp W mem mdX k _ _ _ STK_ex_string e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 true n kid
        HPRE HMX HAR2 HJ1 HX' HFP1 EHP EAB HLED2 HKO) as HKO2.
      assert (HQ2 : val_mem SEGS (mrestrict (w_H W2) mem2) (ea_q a + 8) 8 (ea_x0 a + len) /\
        val_mem SEGS (mrestrict (w_H W2) mem2) (ea_q a + 16) 4 (ea_dep a + 1) /\
        val_mem SEGS (mrestrict (w_H W2) mem2) (ea_q a + 24) 8 (ea_scr a) /\
        val_mem SEGS (mrestrict (w_H W2) mem2) (ea_q a + 32) 4 dl1).
      { split; [|split; [|split]]; (apply (p7a_vm_av (w_H W) (w_H W2) mem mem2); [intros z Hz; apply HKQ; cbn in Hz; lia|]);
          assumption. }
      destruct HQ2 as (Q2' & Q3' & Q4' & Q5').
      cbv beta zeta in HMT. rewrite Nat2Z.id in HMT. change (Nat.succ i') with (Datatypes.S i') in HMT.
      destruct (fst (fst (PjGrammar.jr_string (skipn (Datatypes.S i') (ea_x a)) []))) as [[sn rest]|] eqn:EJS.
      -- destruct HMT as (R10 & (cc & Hsc & Hrest & Vq) & Hbytes).
         apply (HSS a fxc W2 regs2 mem2 md2 ly2 S2 Hp2 (k + k1) n cap acc i i' dln kid dl1
           (Z.of_nat i' + Z.of_nat cc + 2) HPRE HFX).
         unfold p7a_at_s, ev_run0. rewrite EJS.
         split.
         { apply (p7a_mid_call a ly S Hp W mem mdX k _ _ _ STK_ex_string e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ _
             HPRE HMX HJ2 HJ1 HX' HFP1 ltac:(unfold e1; lia) EHP EAB HLED2 HRL2
             ltac:(rewrite ES2; apply PresetHullBudget.hull_used_refl)
             ltac:(intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist HR0; rewrite ES2; exact HR0)); [|exact (HKEEP HMN)].
           split; [replace (ea_x0 a + (Z.of_nat i' + Z.of_nat cc + 2)) with (ea_x0 a + Z.of_nat i' + Z.of_nat cc + 2)
             by lia; exact Vq|].
           split; [exact Q2'|]. split; [exact Q3'|]. split; [exact Q4'|exact Q5']. }
         split; [exact HC2|]. split; [lia|]. split; [exact Hsk|]. split; [exact Hc|].
         split; [exact HIT|]. split; [exact HKO2|]. split; [exact HDK|].
         split; [exact R10|]. split; [|exact Hbytes].
         exists cc. split; [exact Hsc|]. split; [exact Hrest|reflexivity].
      -- destruct HMT as (R10 & Hsame).
         apply (HSS a fxc W2 regs2 mem2 md2 ly2 S2 Hp2 (k + k1) n cap acc i i' dln kid dl1 (Z.of_nat i') HPRE HFX).
         unfold p7a_at_s, ev_run0. rewrite EJS.
         split.
         { apply (p7a_mid_call a ly S Hp W mem mdX k _ _ _ STK_ex_string e1 FP1 ly2 S2 Hp2 W2 mem2 md2 k1 _ _ _
             HPRE HMX HJ2 HJ1 HX' HFP1 ltac:(unfold e1; lia) EHP EAB HLED2 HRL2
             ltac:(rewrite ES2; apply PresetHullBudget.hull_used_refl)
             ltac:(intros rp_sm rp_x rp_os rp_i rp_H0 rp_hist HR0; rewrite ES2; exact HR0)); [|exact (HKEEP HMN)].
           split; [apply (p7a_vm_av (w_H W) (w_H W2) mem mem2); [intros z Hz; apply Hsame; cbn in Hz; lia | exact Q1]|].
           split; [exact Q2'|]. split; [exact Q3'|]. split; [exact Q4'|exact Q5']. }
         split; [exact HC2|]. split; [lia|]. split; [exact Hsk|]. split; [exact Hc|].
         split; [exact HIT|]. split; [exact HKO2|]. split; [exact HDK|].
         split; [exact R10|reflexivity].
- (* the text has ended: the refusal join *)
  set (xs := [ea_x0 a + Z.of_nat i'; 0]).
  pose proof (p7a_stXe fxc regs mem W (ea_x0 a + Z.of_nat i') 0 (ea_q a) (ea_S1 a) (ea_fr a)
    R9 R19 R26 R24 R18 S24 Q1 Vs0 ltac:(unfold kHighMemBeg; lia) ltac:(lia) ltac:(lia) S1al Qal ltac:(lia)) as HS.
  fold xs in HS.
  set (E := p7a_E regs xs) in *.
  assert (HEI : img_env VAL A_LIM E) by apply p7a_env.
  assert (SHOK : sh_ok SEGS p7a_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (E11 : ew E 11 = Z_to_bv 64 (ea_x0 a + len)) by (exact (eq_trans (p7a_ewr regs xs 11%nat 11%bv ltac:(lia) eq_refl) H11)).
  assert (E18 : ew E 18 = Z_to_bv 64 (ea_fr a)) by (exact (eq_trans (p7a_ewr regs xs 18%nat 18%bv ltac:(lia) eq_refl) R18)).
  assert (E32 : ew E 32 = Z_to_bv 64 (ea_x0 a + Z.of_nat i')) by (exact (p7a_ewx regs xs 0 ltac:(unfold A_TEXT; lia))).
  paj_run_tok_x_inv RUNI HS HJ SHOK HMNr p7a_Bspan; [p7a_awr_ro|].
  assert (Hm1 : ms_mem ms = mem) by (eapply p7a_ro_mem; [|exact HF]; vm_compute; reflexivity). clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK p7a_Bspan.
  all: rewrite branch_geu_U, (U_atom _ 32 _ E32), (U_atom _ 11 _ E11) in Hc by lia.
  + apply negb_true_iff, Z.ltb_ge in Hc.
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMNr p7a_Bspan (p7a_k EV_EXIT); [p7a_awr_ro|].
    p7a_ro_step Hm1. p7a_exit_fin a fxc regs xs HS HJ HM HR HFX Hm1 E18.
    * apply HV0. exact (p7a_name_end (ea_x a) i i' Hsk Hge).
    * unfold ea_len; fold len; lia.
    * lia.
    * exact (proj1 HDK).
  + apply negb_false_iff, Z.ltb_lt in Hc. exfalso. lia.
Qed.

(* ---- the cut 0x83924 (0x680): states. a0 is the string's outcome (pinned), s7 the kid-NULL flag (pinned). ---- *)
Definition p7a_ssSf : sstate :=
  mkSS (p7a_k 0x680) (sr_set sr_atoms 10%bv (SLit 18446744073709551615)) [p7a_rS1x] None (mkFacts [p7a_fa_s1] [] []).
Definition p7a_ssSn : sstate :=
  mkSS (p7a_k 0x680) (sr_set (sr_set sr_atoms 10%bv (SLit 0)) 23%bv (SLit 1)) [] None (mkFacts [] [] []).

Lemma p7a_stSf : forall (fxc : YK11.FPState) regs mem (W : world SEGS) (s1 fr : Z),
  getr regs 10 = w64 (-1) -> getr regs 9 = w64 s1 -> getr regs 18 = w64 fr ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 24) 8 fr ->
  kHighMemBeg <= s1 -> s1 + 152 <= 2 ^ 47 -> s1 mod 32 = 0 ->
  st_ok_pi (fx := fxc) SEGS VAL (p7a_E regs []) p7a_ssSf
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k 0x680)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W s1 fr H10 H9 H18 Vf Hs1 Hs47 Hs32.
pose proof Hs1 as Hs1v. unfold kHighMemBeg in Hs1v.
set (E := p7a_E regs []).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (exact (eq_trans (p7a_ewr regs _ 9%nat 9%bv ltac:(lia) eq_refl) H9)).
assert (E18 : ew E 18 = Z_to_bv 64 fr) by (exact (eq_trans (p7a_ewr regs _ 18%nat 18%bv ltac:(lia) eq_refl) H18)).
rewrite restrict_mkst_fx. unfold p7a_ssSf, p7a_rS1x.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply regs_ok_pin; [apply p7a_regs_ok|apply p7a_r0; vm_compute; discriminate|].
  cbn [sv_denot]. rewrite H10. exact p7a_wm1.
- vm_compute. reflexivity.
- constructor; [|constructor]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
  constructor; [|constructor].
  apply (p7a_chunk_of_val E _ s1 24 8 (SOff 18 0) fr); [lia|exact (p7a_denot0 E 18 fr E18)|exact Vf].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  unfold p7a_fa_s1. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E9, !unsigned_lit_small by lia. change (2 ^ 5) with 32.
  unfold kHighMemBeg. repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

Lemma p7a_stSn : forall (fxc : YK11.FPState) regs mem (W : world SEGS),
  getr regs 10 = w64 0 -> getr regs 23 = w64 1 ->
  st_ok_pi (fx := fxc) SEGS VAL (p7a_E regs []) p7a_ssSn
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k 0x680)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W H10 H23.
rewrite restrict_mkst_fx. unfold p7a_ssSn.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply regs_ok_pin; [apply regs_ok_pin; [apply p7a_regs_ok|apply p7a_r0; vm_compute; discriminate|]|
    apply p7a_r0; vm_compute; discriminate|].
  + cbn [sv_denot]. exact H10.
  + cbn [sv_denot]. exact H23.
- vm_compute. reflexivity.
- constructor.
- exact I.
- split; [exact I|split; [exact I | exact I]].
Qed.

(* p7a_car across a stretch that keeps every register but pins s7 *)
Lemma p7a_car_keep23 : forall a W regs mem n kid W' regs' mem',
  p7a_car a W regs mem n kid ->
  (forall r, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r) ->
  getr regs' 23 = getr regs 23 ->
  (forall z, ea_S1 a + 24 <= z < ea_S1 a + 128 -> aview SEGS (w_H W') mem' z = aview SEGS (w_H W) mem z) ->
  p7a_car a W' regs' mem' n kid.
Proof.
intros a W regs mem n kid W' regs' mem' HC HK H23 HM. apply (p7a_car_keep a W regs mem n kid W' regs' mem' HC); [|exact HM].
intros r Hr. cbv [P7A_KEPT In] in Hr.
repeat (destruct Hr as [<-|Hr]; [first [exact H23 | apply HK; cbv; tauto]|]). destruct Hr.
Qed.

(* the kid path's state at 0x83924: s1's spills of q + 24 (s1 + 32), v' + 32 (s1 + 40, atom 32) and n (s1 + 120, atom
   33); v->keys at v' + 32 (atom 34); &keys[n] (atom 35, the alias of keys + (n << 3)) holding keys[n] (atom 36);
   in->scratch at q + 24 (atom 37) *)
Definition p7a_rK1 : YP09.region := YP09.mkRegion (Some 9%nat) 32 128 0 0
  [YP09.mkChunk 32 (CVal 8 (SOff 19 24)); YP09.mkChunk 40 (CVal 8 (SOff 32 0)); YP09.mkChunk 120 (CVal 8 (SOff 33 0))].
Definition p7a_rK2 : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 34 0))].
Definition p7a_rK3 : YP09.region := YP09.mkRegion (Some 35%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))].
Definition p7a_rK4 : YP09.region := YP09.mkRegion (Some 19%nat) 24 32 0 0 [YP09.mkChunk 24 (CVal 8 (SOff 37 0))].
Definition p7a_aliasK : sv * sv := (SAlu ALU_ADD (SAlu ALU_SLL (SOff 33 0) (SLit 3)) (SOff 34 0), SOff 35 0).
Definition p7a_GK : facts := mkFacts [p7a_fa_bx; p7a_fa_s1; p7a_fa_q; (32%nat, mkAF 4096 (2 ^ 47 - 24) 3);
  (35%nat, mkAF 4096 (2 ^ 47 - 64) 3)] [] [p7a_aliasK].
Definition p7a_ssSk : sstate :=
  mkSS (p7a_k 0x680) (sr_set (sr_set sr_atoms 10%bv (SLit 0)) 23%bv (SLit 0)) [p7a_rK1; p7a_rK2; p7a_rK3; p7a_rK4] None
    p7a_GK.

Lemma p7a_denot_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof.
intros E n v c H Hv Hvc. apply bv_eq. rewrite denot_SOff, H. rewrite !unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.

Lemma p7a_stSk : forall (fxc : YK11.FPState) regs mem (W : world SEGS) (vk nn keys kn x scr q s1 : Z),
  getr regs 10 = w64 0 -> getr regs 23 = w64 0 -> getr regs 9 = w64 s1 -> getr regs 19 = w64 q ->
  getr regs 24 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 32) 8 (q + 24) -> val_mem SEGS (mrestrict (w_H W) mem) (s1 + 40) 8 vk ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 120) 8 nn -> val_mem SEGS (mrestrict (w_H W) mem) vk 8 keys ->
  val_mem SEGS (mrestrict (w_H W) mem) kn 8 x -> val_mem SEGS (mrestrict (w_H W) mem) (q + 24) 8 scr ->
  kHighMemBeg <= s1 -> s1 + 152 <= q -> q + 40 <= 2 ^ 47 -> s1 mod 32 = 0 -> q mod 8 = 0 ->
  4096 <= vk <= 2 ^ 47 - 24 -> vk mod 8 = 0 -> 4096 <= kn <= 2 ^ 47 - 64 -> kn mod 8 = 0 ->
  kn = keys + 8 * nn -> 0 <= nn -> 0 <= keys -> 0 <= x < 2 ^ 64 -> 0 <= scr < 2 ^ 64 ->
  (vk + 8 <= s1 + 32 \/ s1 + 128 <= vk) -> (vk + 8 <= q + 24 \/ q + 32 <= vk) -> kn + 8 <= s1 + 32 ->
  kn + 8 <= q + 24 -> (vk + 8 <= kn \/ kn + 8 <= vk) ->
  st_ok_pi (fx := fxc) SEGS VAL (p7a_E regs [vk; nn; keys; kn; x; scr]) p7a_ssSk
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k 0x680)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W vk nn keys kn x scr q s1 H10 H23 H9 H19 H24 V32 V40 V120 Vk Vx Vs Hs1 Hsq Hq47 Hs32 Hq8
  Hvk Hvk8 Hkn Hkn8 Ekn Hnn Hkeys Hx Hscr D1 D2 D3 D4 D5.
pose proof Hs1 as Hs1v. unfold kHighMemBeg in Hs1v.
set (E := p7a_E regs [vk; nn; keys; kn; x; scr]).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (exact (eq_trans (p7a_ewr regs _ 9%nat 9%bv ltac:(lia) eq_refl) H9)).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (exact (eq_trans (p7a_ewr regs _ 19%nat 19%bv ltac:(lia) eq_refl) H19)).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (exact (eq_trans (p7a_ewr regs _ 24%nat 24%bv ltac:(lia) eq_refl) H24)).
assert (E32 : ew E 32 = Z_to_bv 64 vk) by (exact (p7a_ewx regs _ 0 ltac:(unfold A_TEXT; lia))).
assert (E33 : ew E 33 = Z_to_bv 64 nn) by (exact (p7a_ewx regs _ 1 ltac:(unfold A_TEXT; lia))).
assert (E34 : ew E 34 = Z_to_bv 64 keys) by (exact (p7a_ewx regs _ 2 ltac:(unfold A_TEXT; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 kn) by (exact (p7a_ewx regs _ 3 ltac:(unfold A_TEXT; lia))).
assert (E36 : ew E 36 = Z_to_bv 64 x) by (exact (p7a_ewx regs _ 4 ltac:(unfold A_TEXT; lia))).
assert (E37 : ew E 37 = Z_to_bv 64 scr) by (exact (p7a_ewx regs _ 5 ltac:(unfold A_TEXT; lia))).
rewrite restrict_mkst_fx. unfold p7a_ssSk, p7a_rK1, p7a_rK2, p7a_rK3, p7a_rK4.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply regs_ok_pin; [apply regs_ok_pin; [apply p7a_regs_ok|apply p7a_r0; vm_compute; discriminate|]|
    apply p7a_r0; vm_compute; discriminate|].
  + cbn [sv_denot]. exact H10.
  + cbn [sv_denot]. exact H23.
- vm_compute. reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  + rewrite E9, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor; [|constructor; [|constructor]]].
    * apply (p7a_chunk_of_val E _ s1 32 8 (SOff 19 24) (q + 24)); [lia|exact (p7a_denot_off E 19 q 24 E19 ltac:(lia) ltac:(lia))|exact V32].
    * apply (p7a_chunk_of_val E _ s1 40 8 (SOff 32 0) vk); [lia|exact (p7a_denot0 E 32 vk E32)|exact V40].
    * apply (p7a_chunk_of_val E _ s1 120 8 (SOff 33 0) nn); [lia|exact (p7a_denot0 E 33 nn E33)|exact V120].
  + rewrite E32, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ vk 0 8 (SOff 34 0) keys); [lia|exact (p7a_denot0 E 34 keys E34)|rewrite Z.add_0_r; exact Vk].
  + rewrite E35, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ kn 0 8 (SOff 36 0) x); [lia|exact (p7a_denot0 E 36 x E36)|rewrite Z.add_0_r; exact Vx].
  + rewrite E19, unsigned_lit_small by lia.
    split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
    constructor; [|constructor].
    apply (p7a_chunk_of_val E _ q 24 8 (SOff 37 0) scr); [lia|exact (p7a_denot0 E 37 scr E37)|exact Vs].
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
  rewrite E9, E19, E32, E35, !unsigned_lit_small by lia.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; [exact I|]].
  + unfold p7a_GK, p7a_fa_bx, p7a_fa_s1, p7a_fa_q. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E24, E9, E19, E32, E35, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, kHighMemBeg. repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
  + unfold p7a_GK, p7a_aliasK. cbn [f_alias alias_ok]. split; [|exact I].
    apply U_inj. rewrite !U_SAlu, U_SLit.
    rewrite (U_atom E 33 nn E33) by lia. rewrite (U_atom E 34 keys E34) by lia. rewrite (U_atom E 35 kn E35) by lia.
    cbn [zalu_raw]. rewrite (zcanon_id 3) by (unfold M64; lia). change (Z.land 3 63) with 3.
    rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3) with 8.
    rewrite (zcanon_id (nn * 8)) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ---- the strcmp call's premises (after S8aNumE.v b930551f458a :383-498, eve_* and evE_rom, restated) ---- *)
Lemma p7a_garr8_aview : forall (H : word -> bool) m p l j, garr8 SEGS (mrestrict H m) p l -> (j < length l)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some (nth j l 0).
Proof.
intros H m p l j Hg Hj. unfold aview. rewrite (garr8_mbyte SEGS _ p l j Hg Hj). cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256.
apply Z.mod_small. exact (proj2 (Hg j Hj)).
Qed.
Lemma p7a_first_byte : forall (W : world SEGS) m p l, garr8 SEGS (mrestrict (w_H W) m) p (l ++ [0]) ->
  Forall (fun c => c <> 0) l -> first_byte SEGS W m p (Z.of_nat (length l) + 1) 0 (Z.of_nat (length l)).
Proof.
intros W m p l Hg Hnz. split; [lia|]. split.
- intros i Hi. exists (nth (Z.to_nat i) l 0). split.
  + replace (p + i) with (p + Z.of_nat (Z.to_nat i)) by lia.
    rewrite (p7a_garr8_aview (w_H W) m p (l ++ [0]) (Z.to_nat i) Hg) by (rewrite length_app; cbn; lia).
    rewrite app_nth1 by lia. reflexivity.
  + apply (proj1 (Forall_forall _ _) Hnz). apply nth_In. lia.
- intros _. rewrite (p7a_garr8_aview (w_H W) m p (l ++ [0]) (length l) Hg) by (rewrite length_app; cbn; lia).
  rewrite app_nth2 by lia. rewrite Nat.sub_diag. reflexivity.
Qed.
Lemma p7a_src_ok : forall (W : world SEGS) regs m p l, garr8 SEGS (mrestrict (w_H W) m) p l ->
  (forall a, p <= a < p + Z.of_nat (length l) -> ~ (spZ regs - ESTACK <= a < spZ regs)) ->
  src_ok SEGS W regs m p (Z.of_nat (length l)).
Proof.
intros W regs m p l Hg Hw a Ha. split; [|exact (Hw a Ha)].
replace a with (p + Z.of_nat (Z.to_nat (a - p))) by lia.
rewrite (p7a_garr8_aview (w_H W) m p l (Z.to_nat (a - p)) Hg) by lia. discriminate.
Qed.
Lemma p7a_amem_of_app : forall lo len, in_app lo len -> amem_range lo len.
Proof.
intros lo len H. pose proof alloc_ceiling_value as [C1 C2].
unfold in_app, amem_range, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL in *. lia.
Qed.
Lemma p7a_grows_of_pres : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' HP x Hx. unfold mrestrict in *.
destruct (H x) eqn:Hh; [exfalso; apply Hx; reflexivity|].
destruct (m x) as [b|] eqn:Hm; [|exfalso; apply Hx; reflexivity].
assert (Ha : apresent H m (bv_unsigned x)).
{ unfold apresent. rewrite Z_to_bv_bv_unsigned. split; [exact Hh|exists b; exact Hm]. }
destruct (HP _ Ha) as (_ & b' & Hb'). rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.
Lemma p7a_garr_forall : forall m a l, garr8 SEGS m a l -> Forall (fun b => 0 <= b < 256) l.
Proof.
intros m a l H. apply Forall_forall. intros b Hb. destruct (In_nth l b 0 Hb) as (j & Hj & <-). exact (proj2 (H j Hj)).
Qed.
Lemma p7a_forall_skipn : forall (P : Z -> Prop) l j, Forall P l -> Forall P (skipn j l).
Proof.
intros P l. induction l as [|b l IH]; intros [|j] H; cbn; [exact H|exact H|exact H|].
inversion H; subst. apply IH. assumption.
Qed.
Lemma p7a_ob_atom : forall (W : world SEGS) mem E n x len, ew E 24 = Z_to_bv 64 SHADOW_OFF -> ew E n = Z_to_bv 64 x ->
  0 <= x < 2 ^ 64 -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF x len ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) mem)) (U E p7a_Bx) (U E (SOff n 0)) len.
Proof.
intros W mem E n x len H24 Hn Hx HR. pose proof asan_consts as ((C1 & C1') & _).
unfold p7a_Bx. rewrite (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
rewrite (U_atom E n x Hn) by lia. rewrite <- aview_rd_of. exact HR.
Qed.
Lemma p7a_ob_off : forall (W : world SEGS) mem E n x c len, ew E 24 = Z_to_bv 64 SHADOW_OFF -> ew E n = Z_to_bv 64 x ->
  0 <= x < 2 ^ 64 -> 0 <= x + c < 2 ^ 64 -> range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (x + c) len ->
  range_addressable (rd_of SEGS (mrestrict (w_H W) mem)) (U E p7a_Bx) (U E (SOff n c)) len.
Proof.
intros W mem E n x c len H24 Hn Hx Hxc HR.
unfold p7a_Bx. rewrite (U_atom E 24 SHADOW_OFF H24) by (unfold SHADOW_OFF; lia).
rewrite (U_atom_off E n x c Hn Hx Hxc). rewrite <- aview_rd_of. exact HR.
Qed.
Lemma p7a_names_eq : forall (H : word -> bool) m x y l1 l2,
  garr8 SEGS (mrestrict H m) x (l1 ++ [0]) -> garr8 SEGS (mrestrict H m) y (l2 ++ [0]) ->
  Z.of_nat (length l1) = Z.of_nat (length l2) ->
  (forall i, 0 <= i < Z.of_nat (length l1) -> aview SEGS H m (x + i) = aview SEGS H m (y + i)) -> l1 = l2.
Proof.
intros H m x y l1 l2 G1 G2 Hl Hb. apply (nth_ext l1 l2 0 0); [lia|].
intros j Hj. specialize (Hb (Z.of_nat j) ltac:(lia)).
rewrite (p7a_garr8_aview H m x (l1 ++ [0]) j G1) in Hb by (rewrite length_app; cbn; lia).
rewrite (p7a_garr8_aview H m y (l2 ++ [0]) j G2) in Hb by (rewrite length_app; cbn; lia).
rewrite !app_nth1 in Hb by lia. injection Hb as Hb. exact Hb.
Qed.
Lemma p7a_names_same : forall (H : word -> bool) m x y l,
  garr8 SEGS (mrestrict H m) x (l ++ [0]) -> garr8 SEGS (mrestrict H m) y (l ++ [0]) ->
  forall i, 0 <= i < Z.of_nat (length l) -> aview SEGS H m (x + i) = aview SEGS H m (y + i).
Proof.
intros H m x y l G1 G2 i Hi. replace i with (Z.of_nat (Z.to_nat i)) by lia.
rewrite (p7a_garr8_aview H m x (l ++ [0]) (Z.to_nat i) G1) by (rewrite length_app; cbn; lia).
rewrite (p7a_garr8_aview H m y (l ++ [0]) (Z.to_nat i) G2) by (rewrite length_app; cbn; lia). reflexivity.
Qed.
(* the 8-byte granule floor is monotone (Zify's division equations are off in this file) *)
Lemma p7a_floor8 : forall u w, u <= w -> u - u mod 8 <= w - w mod 8.
Proof.
intros u w H. pose proof (Z.div_mod u 8 ltac:(lia)). pose proof (Z.div_mod w 8 ltac:(lia)).
assert (u / 8 <= w / 8) by (apply Z.div_le_mono; lia). lia.
Qed.
(* ev_pre's read-only view (fpre's arodata_okP, PRH_Base.v) at a state of the piece, in the xrom strcmp row's spelling
   PresetRodata.arodata_okP (S8aItems.v ev_aro_kept: the journal's image clause; aro_prh_to_mxmn: PRH_Base's body to
   the leaf's, by conversion). It replaces p7a_rom (rom_view from ROM), which the strcmp row of walkkit b77223726823
   needed. STATEMENT CHANGE forced by the engine of record: its YGcallMxmn.v (b47cf7942c3d) no longer defines
   YGcallMxmn.arodata_okP, which this conclusion named; the new name is the one astrcmp_realizes_xrom now asks. *)
Lemma p7a_aro : forall a ly S Hp W mem md k,
  ev_pre (fx := fx) B ARx a ->
  ajournal_x (SK := SK) SEGS B PST ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a) (ea_FP a)
    (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem md k ->
  PresetRodata.arodata_okP SEGS (@pa_relro_lo _ A_prog_listing PA) (@pa_relro_hi _ A_prog_listing PA) B
    (aview SEGS (w_H W) mem).
Proof.
intros a ly S Hp W mem md k HPRE HJ.
pose proof HPRE as H. unfold ev_pre in H. cbv zeta in H.
destruct H as ((HFPRE & HROD & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hinb2 & _).
assert (Hscr : 4096 <= ea_scr a).
{ destruct Hinb2 as (b0 & m0 & Hbm & Hb0 & _ & _). pose proof HFPRE as (HAR0 & _).
  destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ b0 m0 HAR0 Hbm) as (_ & H4096 & _). lia. }
apply S8aItems.aro_prh_to_mxmn.
eapply ev_aro_kept; [exact HJ | | exact p7a_pst_not_ro | exact HROD].
apply ev_fp_closed. unfold ea_FP.
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & _ & BQ & _). pose proof asan_consts as ((C1 & C2) & _).
repeat (apply Forall_cons; [cbn [fst]; lia|]). apply Forall_nil.
Qed.

(* ---- the cut 0x83980 (0x6dc), just after the strcmp: a0 = its result (atom 10); s1's spill of q + 32 (s1 + 88). The
   not-taken arm adds in->differs' cell as a write window (p7a_rC2). ---- *)
Definition p7a_rC1 : YP09.region := YP09.mkRegion (Some 9%nat) 88 96 0 0 [YP09.mkChunk 88 (CVal 8 (SOff 19 32))].
Definition p7a_rC2 : YP09.region := YP09.mkRegion (Some 19%nat) 32 36 32 36 [].
Definition p7a_ssC : sstate :=
  mkSS (p7a_k 0x6dc) sr_atoms [p7a_rC1] None (mkFacts [p7a_fa_bx; p7a_fa_s1; p7a_fa_q] [] []).

Lemma p7a_stC : forall (fxc : YK11.FPState) regs mem (W : world SEGS) (q s1 : Z),
  getr regs 9 = w64 s1 -> getr regs 19 = w64 q -> getr regs 24 = w64 SHADOW_OFF ->
  val_mem SEGS (mrestrict (w_H W) mem) (s1 + 88) 8 (q + 32) ->
  kHighMemBeg <= s1 -> s1 + 152 <= q -> q + 40 <= 2 ^ 47 -> s1 mod 32 = 0 -> q mod 8 = 0 ->
  st_ok_pi (fx := fxc) SEGS VAL (p7a_E regs []) p7a_ssC
    (restrict (w_H W) (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k 0x6dc)) mem (YK11.seg_rom SEGS))).
Proof.
intros fxc regs mem W q s1 H9 H19 H24 V88 Hs1 Hsq Hq47 Hs32 Hq8.
pose proof Hs1 as Hs1v. unfold kHighMemBeg in Hs1v.
set (E := p7a_E regs []).
assert (E9 : ew E 9 = Z_to_bv 64 s1) by (exact (eq_trans (p7a_ewr regs _ 9%nat 9%bv ltac:(lia) eq_refl) H9)).
assert (E19 : ew E 19 = Z_to_bv 64 q) by (exact (eq_trans (p7a_ewr regs _ 19%nat 19%bv ltac:(lia) eq_refl) H19)).
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (exact (eq_trans (p7a_ewr regs _ 24%nat 24%bv ltac:(lia) eq_refl) H24)).
rewrite restrict_mkst_fx. unfold p7a_ssC, p7a_rC1.
apply (pa_entry_st_ok_full (fx := fxc) (PI := PA)).
- apply p7a_regs_ok.
- vm_compute. reflexivity.
- constructor; [|constructor]; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros z Hz; lia|].
  constructor; [|constructor].
  apply (p7a_chunk_of_val E _ s1 88 8 (SOff 19 32) (q + 32)); [lia|exact (p7a_denot_off E 19 q 32 E19 ltac:(lia) ltac:(lia))|exact V88].
- cbn [pairwise_disjoint all_disjoint]. exact (conj I I).
- split; [|split; [exact I | exact I]].
  unfold p7a_fa_bx, p7a_fa_s1, p7a_fa_q. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite E24, E9, E19, !unsigned_lit_small by (unfold SHADOW_OFF; lia).
  change (2 ^ 5) with 32. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
  unfold SHADOW_OFF, kHighMemBeg. repeat match goal with |- _ /\ _ => split end; try exact I; try lia.
Qed.

(* the write premise of a run whose only writable region is in->differs' cell (atom 19, window q + 32 .. q + 36) *)
Ltac p7a_awr19 E19 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0' ?fp ?b0 ?bc ?ly' ?own' =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0' fp b0 bc ly' own') end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 19%nat);
  [ reflexivity
  | rewrite E19, unsigned_lit_small by (unfold kHighMemBeg in *; lia); reflexivity
  | intros z Hz; cbn [YP09.r_wlo YP09.r_whi] in Hz; left; lia
  | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ].

(* ---- the kid path from 0x83924: v->keys[n] against the scratch by strcmp (0x8397c), then in->differs ---- *)
Lemma p7a_kid_path : forall a fxc W regs mem md ly S Hp k n cap acc i i' dln kid dl1 nm rest cc,
  ev_pre (fx := fx) B ARx a -> ev_fx (fx := fx) fxc ->
  ev_mid B ARx SK a ly S Hp W mem md k (ea_x0 a + (Z.of_nat i' + Z.of_nat cc + 2)) (ea_dep a + 1) dl1 ->
  p7a_car a W regs mem n kid -> getr regs 10 = w64 0 -> kid <> 0 ->
  (i <= i' < length (ea_x a))%nat -> skipn i' (ea_x a) = PjGrammar.skip (skipn i (ea_x a)) ->
  nth i' (ea_x a) 0 = 34 -> p7a_item a n cap acc i dln -> ev_kid_ok a ly S W mem true n kid ->
  ev_dl_kid a true n dln dl1 ->
  ev_run0 (PjGrammar.jr_string (skipn (Datatypes.S i') (ea_x a))) = Some (nm, rest) ->
  PjGrammar.scan (skipn (Datatypes.S i') (ea_x a)) = Some cc ->
  rest = skipn (Datatypes.S cc) (skipn (Datatypes.S i') (ea_x a)) ->
  bytes_at W mem (ea_scr a) (nm ++ [0]) ->
  SRr SEGS W (mkCfg (@YK11.mkst fxc regs (Z_to_bv 64 (BASE + p7a_k 0x680)) mem (YK11.seg_rom SEGS)) md)
    (p7a_Q a n cap acc i dln kid).
Proof.
intros a fxc W regs mem md ly S Hp k n cap acc i i' dln kid dl1 nm rest cc HPRE HFX HM HC R10 Hk0 Hii' Hsk H34 HIT
  HKO HDK EJS Hsc Hrest Hbytes.
pose proof HKO as HKO0.
pose proof HC as (HR & H20 & H21 & H22 & H27 & H23 & HSP & V96 & V104 & V120).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HSP as (S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
pose proof HM as (HJ & HWIN & HHP & HABL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HROOM & HRPOS & HMN).
pose proof HCUR as (Q1 & Q2 & Q3 & Q4 & Q5).
pose proof HSRC as (HBY & Hx4096 & Hxc & HAM & HRA & HHU).
pose proof HWD as (HD0 & HDC & HAMs & HWW & HRAs & HHUs).
pose proof HIT as (Hd & Hni & Hil & Hna & HL & Hdl).
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & S1al & BQ & BQD & B47 & Qal & BD0).
pose proof HPRE as HP. unfold ev_pre in HP. cbv zeta in HP.
destruct HP as ((HAF & HARO & _) & Hfrm0 & Hcnt0 & HE10 & HE11 & HCur0 & Hq8 & HCHA0 & Hspq & Hqd & Hfw & Hsrc0 & Hinb0
  & Hlen0 & Hi00 & Hdep0 & Hdepn0 & Hdl00 & Hwd0 & Hinb20 & Hd10 & Hd20 & Htree0 & Hled0 & _).
pose proof HAF as (HAR0 & _ & Hra4 & Hgp0 & Htp0 & Hstk0 & _).
pose proof Hstk0 as (Hsp16 & _ & _ & _ & _ & H47 & _).
pose proof Hfw as (Hd0 & Hd16 & Hdtop & _).
pose proof asan_consts as ((C1 & C2) & _).
pose proof (p7a_stk (ea_n a)) as HSTK. change (STK_ex_value (ea_n a)) with (ea_STK a) in HSTK. unfold ESTACK in HSTK.
pose proof (p7a_s1_lo a Hsp16) as HS1lo.
pose proof HJ as (HAR & HLY & _).
pose proof HLY as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & EHI & _).
pose proof (@cf_head_nonneg cp) as Hh0.
unfold ea_len in *. set (len := Z.of_nat (length (ea_x a))) in *.
pose proof (p7a_key_read (ea_x a) i i' nm rest cc Hsk ltac:(lia) H34 EJS Hsc Hrest) as (HN & Hi1).
rewrite (proj2 (Z.eqb_neq kid 0) Hk0) in H23.
destruct HKO as [(Hk0' & _)|(Hv' & Hnl & Hk4 & Hkc & Hkam & Dk & HKT & Hinc & Hfoot)]; [exfalso; exact (Hk0 Hk0')|].
assert (Hv0 : ea_v a <> 0) by exact (p7a_v'_nz a true Hv').
assert (EV' : ev_v' (ea_v a) true (ea_t a) = ea_v a).
{ unfold ev_v' in Hv' |- *. destruct (ev_tv (ea_v a) true (ea_t a)); [reflexivity|exfalso; apply Hv'; reflexivity]. }
assert (Htg : PjTree.tag (ea_t a) = 6).
{ unfold ev_v', ev_tv in Hv'. destruct (ea_v a =? 0) eqn:E0; [apply Z.eqb_eq in E0; contradiction|].
  cbn [orb] in Hv'. destruct (PjTree.tag (ea_t a) =? 6) eqn:E6; [apply Z.eqb_eq in E6; exact E6|exfalso; apply Hv'; reflexivity]. }
destruct HTREE as [Hv00|(HN0 & HH & HRAv & HHVv)]; [exfalso; exact (Hv0 Hv00)|].
destruct Htree0 as [Hv00|(_ & HD0' & FOOT)]; [exfalso; exact (Hv0 Hv00)|].
(* the string's facts *)
destruct (S8aModel.ex_string_rest _ _ _ EJS) as (c2 & Hsc2 & _ & Hc2l & Hlnm & Hbnm).
rewrite Hsc in Hsc2. injection Hsc2 as <-.
rewrite length_skipn in Hc2l.
assert (Hnz2 : Forall (fun b => 0 < b < 256) nm) by (apply Hbnm; apply p7a_forall_skipn; exact (p7a_garr_forall _ _ _ HBY)).
assert (Hnzy : Forall (fun c => c <> 0) nm) by (eapply Forall_impl; [|exact Hnz2]; intros b Hb; cbv beta in Hb; lia).
(* the object's tree: keys[n] *)
assert (HJO : exists ms, ea_t a = PjTree.JObj ms).
{ revert Htg. destruct (ea_t a) eqn:Et; cbn; intros Htg; try discriminate. eexists; reflexivity. }
destruct HJO as (ms & Et).
pose proof HN0 as HN0'. rewrite Et in HN0'.
assert (Hnl' : (n < length ms)%nat) by (rewrite Et in Hnl; exact Hnl).
destruct (ev_obj_kid _ _ _ _ _ n HN0' Hnl') as (kids & keys & cap' & x & kk & Dk' & Hkids & Hkeys & Hcap0 & Hcapl &
  Hlk & Hlky & HinK & HinKy & Hx & Hcs & HinX & _ & _).
set (nmt := fst (nth n ms ([], PjTree.JNull))) in *.
destruct Hkeys as (Hkeys64 & Vkeys). destruct Hx as (Hx64 & Vx).
(* the kit's pj_cstrR (PRH_Reader.v:110-113, walkkit old-pin): the string's 2 ^ 32 bound, then pj_cbytesR (its byte
   range, its bytes) *)
destruct Hcs as (HlinX & Hkk & Hk32 & Hnzx & Gx).
assert (Hnzx' : Forall (fun c => c <> 0) nmt) by (eapply Forall_impl; [|exact Hnzx]; intros b Hb; cbv beta in Hb; lia).
destruct (ev_node_hdr _ _ _ _ _ HN0) as (num & str & kids0 & keys0 & n0 & cap0 & _ & _ & Hv8).
pose proof HN0' as HN0a. cbn [PRH_Reader.pj_nodeR] in HN0a.
destruct HN0a as (_ & AP & _).
(* the ledger blocks of v->keys and of keys[n] *)
pose proof HLED as (_ & _ & HHB & _).
destruct (proj1 (Forall_forall _ _) HHB (keys, 8 * cap') Hlky) as (Hk8 & Hblkk & Hhpk & Halk & _).
cbn [fst snd] in Hk8, Hblkk, Hhpk, Halk.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hblkk) as (_ & K4096 & Kc & Kapp & _).
assert (Rk : req_size (8 * cap' + cf_head) = 8 * cap' + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (8 * cap' + cf_head) 0); lia).
rewrite Rk in Kc, Kapp.
destruct (proj1 (Forall_forall _ _) HHB (x, kk) HlinX) as (Hkx0 & Hblkx & Hhpx & Halx & _).
cbn [fst snd] in Hkx0, Hblkx, Hhpx, Halx.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hblkx) as (_ & X4096 & Xc & Xapp & _).
assert (Rx : req_size (kk + cf_head) = kk + cf_head)
  by (unfold req_size; destruct (Z.eqb_spec (kk + cf_head) 0); lia).
rewrite Rx in Xc, Xapp.
set (kn := keys + 8 * Z.of_nat n).
assert (Hkn8 : kn mod 8 = 0).
{ unfold kn. pose proof (Z.div_mod keys 16 ltac:(lia)) as D. rewrite Halk, Z.add_0_r in D.
  replace (keys + 8 * Z.of_nat n) with ((2 * (keys / 16) + Z.of_nat n) * 8) by lia. apply Z.mod_mul. lia. }
(* the node's home: 4096 <= v, v + 56 <= 2 ^ 47, below the stack or above sp0 *)
assert (VB : 4096 <= ea_v a /\ ea_v a + 56 <= 2 ^ 47 /\ (ea_v a + 56 <= alloc_ceiling \/ ea_sp0 a <= ea_v a)).
{ destruct HH as [(b & mm & Hin & H1 & H2)|[(cid & pos & Hin & H1 & H2)|(H1 & H2)]].
  - destruct (proj1 (Forall_forall _ _) HHB (b, mm) Hin) as (Hm0 & Hblk & _). cbn [fst snd] in Hm0, Hblk.
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hblk) as (_ & B4096 & Bc & _).
    assert (Rq : mm + cf_head <= req_size (mm + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (mm + cf_head) 0); lia).
    lia.
  - destruct (frames_bounds_x _ _ _ LAWS _ _ _ _ _ _ _ _ HAR Hin) as (F0 & F1 & _). lia.
  - change (spZ (ea_regs a)) with (ea_sp0 a) in H1. rewrite EHI in H2. lia. }
destruct VB as (V4096 & V47 & Vhome).
destruct Hinb20 as (bs & msz & Hbs & Hbs1 & Hbs2 & _).
destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ bs msz HAR0 Hbs) as (_ & Bs4096 & Bsc & _).
rewrite <- HABL in Hbs.
assert (Rs : msz <= req_size msz) by (unfold req_size; destruct (Z.eqb_spec msz 0); lia).
assert (S40' : val_mem SEGS (mrestrict (w_H W) mem) (ea_S1 a + 40) 8 (ea_v a + 32)).
{ rewrite EV', Z.mod_small in S40 by lia. exact S40. }
assert (D2 : ea_v a + 32 + 8 <= ea_q a + 24 \/ ea_q a + 32 <= ea_v a + 32).
{ destruct (Z_le_gt_dec (ea_v a + 40) (ea_q a + 24)) as [D|D]; [left; lia|].
  destruct (Z_le_gt_dec (ea_q a + 32) (ea_v a + 32)) as [D'|D']; [right; lia|].
  exfalso. assert (Hz : PjStruct.pj_foot (ea_v a) (ea_D a) (Z.max (ea_v a + 32) (ea_q a + 24))) by (left; lia).
  destruct (FOOT _ Hz) as (_ & Hq & _). apply Hq. lia. }
assert (D5 : ea_v a + 32 + 8 <= kn \/ kn + 8 <= ea_v a + 32).
{ destruct (Z_le_gt_dec (ea_v a + 40) kn) as [D|D]; [left; lia|].
  destruct (Z_le_gt_dec (kn + 8) (ea_v a + 32)) as [D'|D']; [right; lia|].
  exfalso. apply (AP (keys, 8 * cap') (Z.max (ea_v a + 32) kn) HinKy);
    [unfold PRH_Reader.pj_holdsR; cbn [fst snd]; unfold kn in *; lia|lia]. }
(* the kid path's symbolic state *)
assert (Hvk : 4096 <= ea_v a + 32 <= 2 ^ 47 - 24) by lia.
assert (Hvk8 : (ea_v a + 32) mod 8 = 0) by (rewrite Z.add_mod, Hv8 by lia; reflexivity).
assert (Hknb : 4096 <= kn <= 2 ^ 47 - 64) by (unfold kn; lia).
assert (D1 : ea_v a + 32 + 8 <= ea_S1 a + 32 \/ ea_S1 a + 128 <= ea_v a + 32) by lia.
assert (D3 : kn + 8 <= ea_S1 a + 32) by (unfold kn; lia).
assert (D4 : kn + 8 <= ea_q a + 24) by (unfold kn; lia).
pose proof (p7a_stSk fxc regs mem W (ea_v a + 32) (Z.of_nat n) keys kn x (ea_scr a) (ea_q a) (ea_S1 a)
  R10 H23 R9 R19 R24 S32 S40' V120 Vkeys Vx Q4 ltac:(unfold kHighMemBeg; lia) ltac:(lia) ltac:(lia) S1al Qal
  Hvk Hvk8 Hknb Hkn8 eq_refl ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) D1 D2 D3 D4 D5) as HS.
set (xs := [ea_v a + 32; Z.of_nat n; keys; kn; x; ea_scr a]) in HS.
set (E := p7a_E regs xs) in *.
assert (HEI : img_env VAL A_LIM E) by apply p7a_env.
assert (SHOK : sh_ok SEGS p7a_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
assert (E24 : ew E 24 = Z_to_bv 64 SHADOW_OFF) by (exact (eq_trans (p7a_ewr regs xs 24%nat 24%bv ltac:(lia) eq_refl) R24)).
assert (E19 : ew E 19 = Z_to_bv 64 (ea_q a)) by (exact (eq_trans (p7a_ewr regs xs 19%nat 19%bv ltac:(lia) eq_refl) R19)).
assert (E32 : ew E 32 = Z_to_bv 64 (ea_v a + 32)) by (exact (p7a_ewx regs xs 0 ltac:(unfold A_TEXT; lia))).
assert (E35 : ew E 35 = Z_to_bv 64 kn) by (exact (p7a_ewx regs xs 3 ltac:(unfold A_TEXT; lia))).
assert (E36 : ew E 36 = Z_to_bv 64 x) by (exact (p7a_ewx regs xs 4 ltac:(unfold A_TEXT; lia))).
assert (E37 : ew E 37 = Z_to_bv 64 (ea_scr a)) by (exact (p7a_ewx regs xs 5 ltac:(unfold A_TEXT; lia))).
pose (RUN := paj_run_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
pose (RUNI := paj_run_x_inv (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (RUNTOI := paj_run_to_x_inv (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
(* 0x83924-0x8397c: `bnez a0`, `bnez s7` not taken, the loads, three shadow checks (obligations), up to the call *)
assert (OB1 : range_addressable (rd_of SEGS (mrestrict (w_H W) mem)) (U E p7a_Bx) (U E (SOff 32 0)) 8)
  by exact (p7a_ob_atom W mem E 32 (ea_v a + 32) 8 E24 E32 ltac:(lia)
      (range_addressable_sub _ _ (ea_v a) 56 (ea_v a + 32) 8 HRAv ltac:(lia) ltac:(lia))).
assert (OB2 : range_addressable (rd_of SEGS (mrestrict (w_H W) mem)) (U E p7a_Bx) (U E (SOff 35 0)) 8)
  by exact (p7a_ob_atom W mem E 35 kn 8 E24 E35 ltac:(lia) (proj1 (ev_lam_shadow B ARx LAWS HSH ly S Hp W mem md _ _ _ _ _ _ _
      keys (8 * cap') kn 8 HAR HLED Hlky ltac:(unfold kn; lia) ltac:(unfold kn; lia) ltac:(lia)))).
assert (OB3 : range_addressable (rd_of SEGS (mrestrict (w_H W) mem)) (U E p7a_Bx) (U E (SOff 19 24)) 8)
  by exact (p7a_ob_off W mem E 19 (ea_q a) 24 8 E24 E19 ltac:(lia) ltac:(lia)
      (range_addressable_sub _ _ (ea_q a) 40 (ea_q a + 24) 8
      (ev_q_addressable (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK LAWS a ly S Hp W mem md k _ _ _ HPRE HM)
      ltac:(lia) ltac:(lia))).
(* the run to the call is read-only: HMNr carries memnorm through the _inv runner, HMN stays at mem *)
pose proof HMN as HMNr.
paj_run_tok_x_inv RUNI HS HJ SHOK HMNr p7a_Bspan.
all: try lazymatch goal with
  | |- range_addressable _ _ (U _ (SOff 32 0)) _ => exact OB1
  | |- range_addressable _ _ (U _ (SOff 35 0)) _ => exact OB2
  | |- range_addressable _ _ (U _ (SOff 19 24)) _ => exact OB3 end.
all: try p7a_awr_ro.
p7a_ro_first mem Hm1.
pose proof (regs_kept_of_st_ok SEGS _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv HS
  ltac:(env_agree_chain (p7a_agree regs xs)) ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
prreg HS (10%bv : bv 5) Pa0. prreg HS (11%bv : bv 5) Pa1. prreg HS (1%bv : bv 5) Pra. prreg HS (23%bv : bv 5) N23.
rewrite E36 in Pa0. rewrite E37 in Pa1.
pmkst HS. rewrite Hm1 in HJ |- *.
lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst ?r _ _ _; cfg_model := ?d |} _ =>
  set (regsT := r) in *; set (mdT := d) in * end.
assert (GSP : spZ regsT = ea_S1 a).
{ unfold spZ. rewrite (HKR 2%bv ltac:(cbv; tauto)), R2. unfold w64. apply unsigned_lit_small. lia. }
set (kx := Z.of_nat (length nmt)). set (ky := Z.of_nat (length nm)).
assert (Hkxn : 0 <= kx) by (unfold kx; apply Nat2Z.is_nonneg).
assert (Hkyn : 0 <= ky) by (unfold ky; apply Nat2Z.is_nonneg).
assert (Hkxk : kx + 1 <= kk) by (unfold kx; exact Hkk).
assert (Hky1 : ky <= len) by (unfold ky, len; clear - Hlnm Hc2l; lia).
assert (Hx0 : 4096 <= x) by (clear - X4096 Hh0; lia).
assert (Hs0 : 4096 <= ea_scr a) by (clear - Bs4096 Hbs1; lia).
assert (Hxtop : x + kk <= ea_S1 a - 2 * ESTACK)
  by (unfold ESTACK; clear - Xc BC HS1lo HSTK Hh0; lia).
assert (Hstop : ea_scr a + len + 1 <= ea_S1 a - 2 * ESTACK)
  by (unfold ESTACK; clear - HDC BC HS1lo HSTK; lia).
assert (H63 : alloc_ceiling < 2 ^ 63) by (clear - C1 C2; lia).
(* the strcmp row in its xrom form (SCMP, contract item 3): arodata_okP for rom_view (p7a_aro), the memnorm keep last
   in its conclusion *)
eapply SRr_bind.
{ eapply (YGcallMxmn.aj_strcmp_at_xrom (fx := fxc) (SK := SK) SEGS B PST ARx (@pa_relro_lo _ A_prog_listing PA)
    (@pa_relro_hi _ A_prog_listing PA) LAWS (@pa_segs_low _ A_prog_listing PA)
    (SIGMA AS___wrap_strcmp) (SCMP fxc) W regsT mem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ x (ea_scr a) kx ky
    (ea_S1 a - (ea_sp0 a + ea_d a)) _ HJ).
  - exact Pa0.
  - exact Pa1.
  - clear - Hx0; lia.
  - clear - Hs0; lia.
  - exact Hkxn.
  - exact Hk32.
  - clear - Hkxk Xc Hh0 H63; lia.
  - exact Hkyn.
  - clear - Hky1 Hlen0; lia.
  - clear - Hky1 HDC H63; lia.
  - rewrite GSP. ring.
  - exact (p7a_mod16 _ _ _ S1al Hsp16 Hd16).
  - clear - BS2 BD0; lia.
  - unfold ESTACK. clear - HSTK HS1lo BD0; lia.
  - rewrite (HKR 3%bv ltac:(cbv; tauto)), R3. exact Hgp0.
  - rewrite (HKR 4%bv ltac:(cbv; tauto)), R4. exact Htp0.
  - exact Pra.
  - apply (ret_ok_codeptr_v (PI := PA)); [clear; lia | reflexivity].
  - exact (p7a_first_byte W mem x nmt Gx Hnzx').
  - exact (p7a_first_byte W mem (ea_scr a) nm Hbytes Hnzy).
  - replace (kx + 1) with (Z.of_nat (length (nmt ++ [0]))) by (rewrite length_app; cbn [length]; unfold kx; lia).
    apply (p7a_src_ok W regsT mem x _ Gx). intros a0 Ha0. rewrite GSP.
    rewrite length_app in Ha0. cbn [length] in Ha0. fold kx in Ha0. unfold ESTACK in *. clear - Ha0 Hxtop Hkxk. lia.
  - replace (ky + 1) with (Z.of_nat (length (nm ++ [0]))) by (rewrite length_app; cbn [length]; unfold ky; lia).
    apply (p7a_src_ok W regsT mem (ea_scr a) _ Hbytes). intros a0 Ha0. rewrite GSP.
    rewrite length_app in Ha0. cbn [length] in Ha0. fold ky in Ha0. unfold ESTACK in *. clear - Ha0 Hstop Hky1. lia.
  - intros a0 Ha0. clear - Ha0 Hxtop Hkxk. lia.
  - intros a0 Ha0. clear - Ha0 Hstop Hky1. lia.
  - (* walkkit b77223726823's strcmp row asks amem_range8: BLKAM8 for keys[n]'s block, a sub-range with the same end *)
    apply (p7a_am8_sub (x - cf_head) (req_size (kk + cf_head))); [exact (BLKAM8 ly S Hp W mem md _ _ HAR Hblkx)| |];
      rewrite ?Rx; clear - Hkxk Hkxn Hh0; lia.
  - apply (p7a_am8_sub bs (req_size msz)); [exact (BLKAM8 ly S Hp W mem md _ _ HAR Hbs)| |];
      clear - Hbs1 Hbs2 Rs Hky1 Hkyn; lia.
  - exact (proj1 (ev_lam_shadow B ARx LAWS HSH ly S Hp W mem md _ _ _ _ _ _ _ x kk x (kx + 1) HAR HLED HlinX
      ltac:(clear; lia) ltac:(clear - Hkxk; lia) ltac:(clear - Hkxn; lia))).
  - eapply p7a_inblk_hull; [exact HAR|exact HLED| |clear - Hkxn; lia].
    exists (x - cf_head), (kk + cf_head). split; [exact Hblkx|]. split; [clear - Hh0; lia|].
    split; [clear - Hkxk; lia|intros _; clear; lia].
  - exact (range_addressable_sub _ _ (ea_scr a) (len + 1) (ea_scr a) (ky + 1) HRAs ltac:(clear; lia)
      ltac:(clear - Hky1; lia)).
  - apply (p7a_hull_sub _ (ea_scr a) (len + 1));
      [exact (HHUs ltac:(unfold len; clear; lia))|clear; lia|clear - Hky1; lia|clear - Hkyn; lia].
  - (* the strcmp row's tail: the bytes after keys[n]'s NUL to the end of the NUL's granule; the NUL lies in the block *)
    intros a0 Ha0. apply (p7a_tail_present ly S Hp W mem md (x - cf_head) (kk + cf_head) (x + kx) a0 HAR Hblkx);
      [rewrite Rx; clear - Hkxk Hkxn Hh0; lia | exact Ha0].
  - intros a0 Ha0. apply (p7a_tail_present ly S Hp W mem md bs msz (ea_scr a + ky) a0 HAR Hbs);
      [clear - Hbs1 Hbs2 Rs Hky1 Hkyn; lia | exact Ha0].
  - exact (p7a_aro a ly S Hp W mem mdT k HPRE HJ). }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & rv & -> & HJ2 & HP2 & Hres & Hcmp & Hfr2 & Hpres2 & Hmn2).
(* memnorm at the strcmp's end memory: the row's keep (YGcallMxmn.aj_strcmp_at_xrom's last conjunct) *)
pose proof (Hmn2 HMN) as HMN2.
assert (ES1 : ea_sp0 a + ea_d a + (ea_S1 a - (ea_sp0 a + ea_d a)) = ea_S1 a) by lia. rewrite ES1 in Hfr2.
assert (HPG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv -> getr regs2 r = getr regs r).
{ intros r Hr. rewrite (p7a_pres_get _ _ HP2 r).
  - exact (HKR r Hr).
  - cbv [In] in Hr. repeat (destruct Hr as [<-|Hr]; [unfold acallee_saved; vm_compute (bv_unsigned _); lia|]). destruct Hr. }
assert (H23' : getr regs2 23 = getr regs 23).
{ rewrite (p7a_pres_get _ _ HP2 23%bv) by (unfold acallee_saved; vm_compute (bv_unsigned _); lia). rewrite N23, H23.
  reflexivity. }
assert (HB1 : 2 * ESTACK < ea_S1 a /\ alloc_ceiling <= ea_S1 a - 2 * ESTACK) by (unfold ESTACK; clear - BC BS1 C1 C2 HSTK HS1lo; lia).
unfold ESTACK in HB1.
assert (HB2 : ea_S1 a + 152 <= ea_q a /\ ea_q a + 40 <= 2 ^ 47) by (clear - BS2 BQ BQD B47; lia).
assert (HKS2 : forall z, ea_S1 a + 24 <= z < ea_S1 a + 152 -> aview SEGS (w_H W) mem2 z = aview SEGS (w_H W) mem z).
{ intros z Hz. apply Hfr2; [clear - Hz HB1 HB2; lia|clear - Hz; lia]. }
assert (HKQ2 : forall z, ea_q a <= z < ea_q a + 40 -> aview SEGS (w_H W) mem2 z = aview SEGS (w_H W) mem z).
{ intros z Hz. apply Hfr2; [clear - Hz HB1 HB2; lia|clear - Hz HB2; lia]. }
assert (HC2 : p7a_car a W regs2 mem2 n kid).
{ apply (p7a_car_keep23 a W regs mem n kid W regs2 mem2 HC HPG H23'). intros z Hz. apply HKS2. lia. }
assert (V88' : val_mem SEGS (mrestrict (w_H W) mem2) (ea_S1 a + 88) 8 (ea_q a + 32)).
{ apply (p7a_vm_av (w_H W) (w_H W) mem mem2); [intros z Hz; apply HKS2; cbn in Hz; clear - Hz; lia|exact S88]. }
pose proof HC2 as (HR2 & _).
pose proof HR2 as (R2' & R3' & R4' & R8' & R9' & R18' & R19' & R24' & R25' & R26').
assert (HB3 : kHighMemBeg <= ea_S1 a) by (unfold kHighMemBeg; clear - HB1 C1; lia).
pose proof (p7a_stC fxc regs2 mem2 W (ea_q a) (ea_S1 a) R9' R19' R24' V88'
  HB3 ltac:(clear - HB2; lia) ltac:(clear - HB2; lia) S1al Qal) as HS2.
lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 (_ + ?nn)) _ _ |} _ =>
  change (BASE + nn) with (BASE + p7a_k 0x6dc) end.
set (E2 := p7a_E regs2 []) in *.
assert (HEI2 : img_env VAL A_LIM E2) by apply p7a_env.
assert (SHOK2 : sh_ok SEGS p7a_Bx [] E2 (mrestrict (w_H W) mem2)) by apply Forall_nil.
assert (E2_10 : ew E2 10 = rv) by (exact (eq_trans (p7a_ewr regs2 [] 10%nat 10%bv ltac:(lia) eq_refl) Hres)).
assert (E2_9 : ew E2 9 = Z_to_bv 64 (ea_S1 a)) by (exact (eq_trans (p7a_ewr regs2 [] 9%nat 9%bv ltac:(lia) eq_refl) R9')).
assert (E2_19 : ew E2 19 = Z_to_bv 64 (ea_q a)) by (exact (eq_trans (p7a_ewr regs2 [] 19%nat 19%bv ltac:(lia) eq_refl) R19')).
assert (E2_24 : ew E2 24 = Z_to_bv 64 SHADOW_OFF) by (exact (eq_trans (p7a_ewr regs2 [] 24%nat 24%bv ltac:(lia) eq_refl) R24')).
assert (GROW2 : mem_grows (mrestrict (w_H W) mem) (mrestrict (w_H W) mem2)) by exact (p7a_grows_of_pres _ _ _ Hpres2).
assert (HQA : range_addressable (aview SEGS (w_H W) mem) SHADOW_OFF (ea_q a) 40)
  by exact (ev_q_addressable (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK LAWS a ly S Hp W mem md k _ _ _ HPRE HM).
assert (HLOW2 : forall s, 0 <= s < alloc_ceiling -> aview SEGS (w_H W) mem2 s = aview SEGS (w_H W) mem s)
  by (intros s0 Hsl; apply Hfr2; [clear - Hsl HB1 HB2; lia|unfold ESTACK; clear - Hsl HB1; lia]).
assert (HQA2 : range_addressable (aview SEGS (w_H W) mem2) SHADOW_OFF (ea_q a) 40)
  by exact (p7a_ra _ _ (ea_q a) 40 ltac:(clear - HB1 HB2; lia) ltac:(clear - HB2; lia) HLOW2 HQA).
psrr_branch_tok RUN BR HS2 SHOK2 p7a_Bspan.
all: rewrite branch_eq_U, U_SLit, U_SOff, E2_10, Z.add_0_r in Hc; change (zcanon 0) with 0 in Hc;
  rewrite zcanon_id in Hc by (pose proof (bv_unsigned_in_range 64 rv) as Hrr; unfold M64; unfold bv_modulus in Hrr;
    cbn [Z.of_N] in Hrr; lia).
- (* the key matched (0x83980 `beqz a0` taken): in->differs as it was *)
  apply Z.eqb_eq in Hc.
  assert (Hrv : rv = w64 0) by (apply bv_eq; rewrite Hc; reflexivity).
  assert (Heq : nmt = nm).
  { destruct (proj1 Hcmp Hrv) as (Hkxy & Hbe). exact (p7a_names_eq (w_H W) mem x (ea_scr a) nmt nm Gx Hbytes Hkxy Hbe). }
  pose proof HMN2 as HMN2r.
  paj_run_to_tok_x_inv RUNTOI HS2 HJ2 SHOK2 HMN2r p7a_Bspan (p7a_k EV_KEY); [p7a_awr_ro|].
  p7a_ro_first mem2 Hm2.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ P7A_KEPT HS2 ltac:(env_agree_chain (p7a_agree regs2 []))
    ltac:(vm_compute; reflexivity)) as HKR3; cbn [ms_regs restrict] in HKR3.
  pmkst HS2. p7a_cfg_to EV_KEY. rewrite Hm2 in HJ2 |- *.
  apply SRr_ret. right.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, ev_cfg _ ?r _ _ ?d = _ /\ _ =>
    exists fxc, r, mem2, d, ly, S, Hp, k, (i' + cc + 2)%nat, nm, dl1 end.
  split; [reflexivity|]. split; [exact HFX|].
  apply (p7a_key_of a W _ mem2 _ ly S Hp k n cap acc i (i' + cc + 2)%nat nm dln kid dl1).
  + replace (ea_x0 a + Z.of_nat (i' + cc + 2)) with (ea_x0 a + (Z.of_nat i' + Z.of_nat cc + 2)) by lia.
    apply (p7a_mid_frame a ly S Hp W mem md k _ _ _ mem2 _ _ _ _ (fun z => ea_S1 a - 2 * ESTACK <= z < ea_S1 a)
      HPRE HM HJ2 Hfr2 (p7a_grows_of_pres _ _ _ Hpres2)).
    * intros z Hz. left. clear - Hz. lia.
    * split; [|split; [|split; [|split]]]; (apply (p7a_vm_av (w_H W) (w_H W) mem mem2);
        [intros z Hz; apply HKQ2; cbn in Hz; clear - Hz; lia|]); assumption.
    * exact HMN2.
  + apply (p7a_car_keep a W regs2 mem2 n kid W _ mem2 HC2); [exact HKR3|intros z Hz; reflexivity].
  + exact HIT.
  + clear - Hi1 Hii'. lia.
  + exact HN.
  + exact (p7a_kid_frame a ly S Hp W mem md k _ _ _ mem2 (fun z => ea_S1 a - 2 * ESTACK <= z < ea_S1 a) true n kid HPRE HM
      Hfr2 ltac:(intros z Hz; left; cbv beta in Hz; clear - Hz; lia) HKO0).
  + apply (p7a_dl_key_eq a n nm dln dl1); [rewrite Et; exact Hnl'|rewrite Et; cbn [ev_kids]; exact Heq|exact HDK].
- (* no match: in->differs = 1 (0x83984-0x8399c: s1 + 88, the shadow check of q + 32 with its arm 0x83b44-0x83b50,
     `li a1,1`, `sw a1,0(a0)`) *)
  apply Z.eqb_neq in Hc.
  assert (Hrv : rv <> w64 0) by (intros E0; apply Hc; rewrite E0; reflexivity).
  assert (Hne : nmt <> nm).
  { intros Heq. apply Hrv. apply (proj2 Hcmp). split; [unfold kx, ky; rewrite Heq; reflexivity|].
    intros i0 Hi0. rewrite Heq in Gx. apply (p7a_names_same (w_H W) mem x (ea_scr a) nm Gx Hbytes).
    unfold kx in Hi0. rewrite Heq in Hi0. exact Hi0. }
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRES2 & _).
  pose proof (st_ok_pi_add_region _ _ _ p7a_rC2 HS2 eq_refl) as HS3.
  assert (HS4 := HS3 ltac:(unfold region_ok, p7a_rC2;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
      cbn [ms_mem restrict]; rewrite E2_19, unsigned_lit_small by (clear - HB1 HB2; lia);
      split; [clear - HB1 HB2; lia|]; split; [clear - HB2; lia|];
      split; [intros o Ho; apply (apresent_writable SEGS); apply HPRES2; clear - Ho HB1 HB2 BQD BQ HSTK BS1; lia|constructor])
    ltac:(apply all_disjoint_of_extents; unfold extent_of_region, p7a_rC2, p7a_ssC, p7a_rC1;
      cbn [ss_mem add_cond map YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite E2_9, E2_19, !unsigned_lit_small by (clear - HB1 HB2; lia); cbn [zall_disjoint]; unfold zdisj; cbn [fst snd];
      repeat split; clear - HB2; lia)).
  clear HS3 HS2.
  paj_run_to_tok_x_inv RUNTOI HS4 HJ2 SHOK2 HMN2 p7a_Bspan (p7a_k EV_KEY);
    [ exact (p7a_ob_off W mem2 E2 19 (ea_q a) 32 4 E2_24 E2_19 ltac:(clear - HB1 HB2; lia) ltac:(clear - HB1 HB2; lia)
        (range_addressable_sub _ _ (ea_q a) 40 (ea_q a + 32) 4 HQA2 ltac:(clear; lia) ltac:(clear; lia)))
    | p7a_awr19 E2_19
    | ].
  pose proof (p7a_frame_slot _ _ _ _ (ea_q a + 32) (ea_q a + 36) HFr ltac:(p7a_slot9 E2_19)) as HM3.
  pose proof (mem_grows_trans _ _ _ GROW2 HG) as GROW3.
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs2 _ P7A_KEPT HS4 ltac:(env_agree_chain (p7a_agree regs2 []))
    ltac:(vm_compute; reflexivity)) as HKR3; cbn [ms_regs restrict] in HKR3.
  pose proof (p7a_chunk_of_st fxc _ _ _ W 0%nat _ 0%nat 32 4%N (SLit 1) HS4 eq_refl eq_refl ltac:(clear; lia)) as V1.
  cbn [YP09.r_base base_val N.to_nat Pos.to_nat sv_denot ew ewset Nat.eqb] in V1.
  rewrite E2_19, !unsigned_lit_small in V1 by (clear - HB1 HB2; lia).
  lazymatch type of HS4 with st_ok_pi _ _ _ _ (restrict _ ?msn) => set (mem3 := ms_mem msn) in * end.
  pmkst HS4. p7a_cfg_to EV_KEY.
  apply SRr_ret. right.
  lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, ev_cfg _ ?r _ _ ?d = _ /\ _ =>
    exists fxc, r, mem3, d, ly, S, Hp, k, (i' + cc + 2)%nat, nm, 1 end.
  split; [reflexivity|]. split; [exact HFX|].
  set (Wr := fun z => (ea_S1 a - 2 * ESTACK <= z < ea_S1 a) \/ (ea_q a + 32 <= z < ea_q a + 36)).
  assert (AV3 : forall z, 0 <= z < 2 ^ 64 -> ~ Wr z -> aview SEGS (w_H W) mem3 z = aview SEGS (w_H W) mem z).
  { intros z Hz Hn. rewrite (p7a_av_of_raw W mem2 mem3 (fun z => ea_q a + 32 <= z < ea_q a + 36) HM3 z Hz
      ltac:(intros Hq; apply Hn; right; exact Hq)).
    apply Hfr2; [exact Hz|intros Hs; apply Hn; left; exact Hs]. }
  assert (HWR3 : forall z, Wr z -> ea_S1 a - 2 * ESTACK <= z < ea_S1 a + 152 \/ ea_q a <= z < ea_q a + 8 \/
     ea_q a + 16 <= z < ea_q a + 20 \/ ea_q a + 32 <= z < ea_q a + 36).
  { intros z [Hz|Hz]; [left; clear - Hz; lia|right; right; right; exact Hz]. }
  assert (HKQ3 : forall z, ea_q a <= z < ea_q a + 32 -> aview SEGS (w_H W) mem3 z = aview SEGS (w_H W) mem z).
  { intros z Hz. apply AV3; [clear - Hz HB1 HB2; lia|unfold Wr; clear - Hz HB2; lia]. }
  apply (p7a_key_of a W _ mem3 _ ly S Hp k n cap acc i (i' + cc + 2)%nat nm dln kid 1).
  + replace (ea_x0 a + Z.of_nat (i' + cc + 2)) with (ea_x0 a + (Z.of_nat i' + Z.of_nat cc + 2)) by (clear; lia).
    apply (p7a_mid_frame a ly S Hp W mem md k _ _ _ mem3 _ _ _ _ Wr HPRE HM HJ2 AV3 GROW3 HWR3); [|exact HMN2].
    split; [|split; [|split; [|split]]].
    * apply (p7a_vm_av (w_H W) (w_H W) mem mem3); [intros z Hz; apply HKQ3; cbn in Hz; clear - Hz; lia|exact Q1].
    * apply (p7a_vm_av (w_H W) (w_H W) mem mem3); [intros z Hz; apply HKQ3; cbn in Hz; clear - Hz; lia|exact Q2].
    * apply (p7a_vm_av (w_H W) (w_H W) mem mem3); [intros z Hz; apply HKQ3; cbn in Hz; clear - Hz; lia|exact Q3].
    * apply (p7a_vm_av (w_H W) (w_H W) mem mem3); [intros z Hz; apply HKQ3; cbn in Hz; clear - Hz; lia|exact Q4].
    * exact V1.
  + apply (p7a_car_keep a W regs2 mem2 n kid W _ mem3 HC2); [exact HKR3|].
    intros z Hz. apply (p7a_av_of_raw W mem2 mem3 (fun z => ea_q a + 32 <= z < ea_q a + 36) HM3 z);
      [clear - Hz HB1 HB2; lia|clear - Hz HB2; lia].
  + exact HIT.
  + clear - Hi1 Hii'. lia.
  + exact HN.
  + exact (p7a_kid_frame a ly S Hp W mem md k _ _ _ mem3 Wr true n kid HPRE HM AV3 HWR3 HKO0).
  + apply (p7a_dl_key_ne a n nm dln); [exact Hv'|rewrite Et; cbn [ev_kids]; exact Hne].
Qed.

Lemma p7a_s_of : p7a_s_spec.
Proof.
intros a fxc W regs mem md ly S Hp k n cap acc i i' dln kid dl1 p' HPRE HFX HSa.
destruct HSa as (HM & HC & Hii' & Hsk & H34 & HIT & HKO & HDK & HMT).
pose proof HC as (HR & H20 & H21 & H22 & H27 & H23 & HSP & V96 & V104 & V120).
pose proof HR as (R2 & R3 & R4 & R8 & R9 & R18 & R19 & R24 & R25 & R26).
pose proof HSP as (S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88).
pose proof HM as (HJ & HWIN & HHP & HABL & HLED & HCUR & HSRC & HWD & HTREE & HSAV & HFLAG & HROOM & HRPOS & HMN).
pose proof HIT as (Hd & Hni & Hil & Hna & HL & Hdl).
pose proof (p7a_bounds a HPRE) as (BC & BS1 & BS2 & S1al & BQ & BQD & B47 & Qal & BD0).
pose proof asan_consts as ((C1 & C2) & _).
rewrite p7a_cfg_eq.
pose (RUN := paj_run_x (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS).
(* both runs are read-only: the _inv runner carries memnorm (HMN); the cut's ev_mid is HM's, at mem *)
pose (RUNTOI := paj_run_to_x_inv (fx := fxc) (SK := SK) (PL := PL) (PI := PA) B PST ARx LAWS (YAkMemnorm.memnorm SEGS)
  (YSRrMemnorm.srr_inv_laws_memnorm_k SEGS)).
pose (BR := paj_branch (fx := fxc) (PI := PA)).
set (xs := @nil Z).
destruct (ev_run0 (PjGrammar.jr_string (skipn (Datatypes.S i') (ea_x a)))) as [[nm rest]|] eqn:EJS.
- destruct HMT as (R10 & (cc & Hsc & Hrest & ->) & Hbytes).
  pose proof (p7a_key_read (ea_x a) i i' nm rest cc Hsk ltac:(lia) H34 EJS Hsc Hrest) as (HN & Hi1).
  destruct (Z.eq_dec kid 0) as [Hk0 | Hk0].
  + (* no kid (s7 = 1): `bnez a0` and `bnez s7` (0x83924, 0x83928) straight to C_KEY with in->differs as it was *)
    rewrite Hk0 in H23. cbn in H23.
    pose proof (p7a_stSn fxc regs mem W R10 H23) as HS.
    fold xs in HS. set (E := p7a_E regs xs) in *.
    assert (HEI : img_env VAL A_LIM E) by apply p7a_env.
    assert (SHOK : sh_ok SEGS p7a_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
    paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7a_Bspan (p7a_k EV_KEY); [p7a_awr_ro|].
    p7a_ro_first mem Hm1.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 24; 25; 26; 27]%bv HS
      ltac:(env_agree_chain (p7a_agree regs xs)) ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR.
    prreg HS (23%bv : bv 5) N23.
    pmkst HS. p7a_cfg_to EV_KEY. rewrite Hm1 in HJ |- *.
    apply SRr_ret. right.
    lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _, ev_cfg _ ?r _ _ ?d = _ /\ _ =>
      exists fxc, r, mem, d, ly, S, Hp, k, (i' + cc + 2)%nat, nm, dl1 end.
    split; [reflexivity|]. split; [exact HFX|].
    apply (p7a_key_of a W _ mem _ ly S Hp k n cap acc i (i' + cc + 2)%nat nm dln kid dl1).
    * split; [exact HJ|]. replace (ea_x0 a + Z.of_nat (i' + cc + 2)) with (ea_x0 a + (Z.of_nat i' + Z.of_nat cc + 2)) by lia.
      exact (proj2 HM).
    * apply (p7a_car_keep23 a W regs mem n kid W _ mem HC HKR); [|intros z Hz; reflexivity].
      rewrite N23, H23. reflexivity.
    * exact HIT.
    * lia.
    * exact HN.
    * exact HKO.
    * apply p7a_dl_key0; [|exact HDK].
      destruct HKO as [(_ & Hv)|(_ & _ & Hk4 & _)]; [exact Hv|lia].
  + (* a kid (s7 = 0): the strcmp of keys[n] with the scratch *)
    exact (p7a_kid_path a fxc W regs mem md ly S Hp k n cap acc i i' dln kid dl1 nm rest cc HPRE HFX HM HC R10 Hk0
      Hii' Hsk H34 HIT HKO HDK EJS Hsc Hrest Hbytes).
- destruct HMT as (R10 & ->).
  (* ex_string refused: `bnez a0` to the refusal join *)
  pose proof (p7a_stSf fxc regs mem W (ea_S1 a) (ea_fr a) R10 R9 R18 S24 ltac:(unfold kHighMemBeg; lia) ltac:(lia) S1al)
    as HS.
  fold xs in HS. set (E := p7a_E regs xs) in *.
  assert (HEI : img_env VAL A_LIM E) by apply p7a_env.
  assert (SHOK : sh_ok SEGS p7a_Bx [] E (mrestrict (w_H W) mem)) by apply Forall_nil.
  assert (E18 : ew E 18 = Z_to_bv 64 (ea_fr a)) by (exact (eq_trans (p7a_ewr regs xs 18%nat 18%bv ltac:(lia) eq_refl) R18)).
  paj_run_to_tok_x_inv RUNTOI HS HJ SHOK HMN p7a_Bspan (p7a_k EV_EXIT); [p7a_awr_ro|].
  p7a_ro_first mem Hm1. p7a_exit_fin a fxc regs xs HS HJ HM HR HFX Hm1 E18.
  + rewrite HL. apply p7a_L_none.
    rewrite (p7a_name_at (ea_x a) i i' Hsk ltac:(lia)), H34, Z.eqb_refl. unfold ev_run0 in EJS |- *. rewrite EJS. reflexivity.
  + unfold ea_len. lia.
  + lia.
  + exact (proj1 HDK).
Qed.

(* ======== SEGMENT 2: C_KID 0x83878 -> C_KEY 0x839a0 (object path), or the refusal join 0x83b54 -> P_EXIT ======== *)
Lemma ev7_seg2_A : ev7_seg2_stmt (fx := fx) (L := A_prog_listing) (PA := PA) B ARx SK.
Proof. exact (p7a_seg2_of_x (p7a_x_of p7a_s_of)). Qed.

End w.
