(* reac_box_catalogue_match (0x84e40) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): its contract in
   cgif's world form (CONVENTIONS.md sections 2-5 (a working note, not in this delivery)), the image-B twin of a Theorem Labs lane's image-A draft
   (catalogue_match-spec-draft.md section 2 (a working note, not in this delivery)), under a Theorem Labs lane's B
   decisions (decisions.md (a working note, not in this delivery), 23:55Z / 00:05Z): segments
   YB1v.tfibsegs, a constant entry pc, arodata_okS, the window of the proved B run as the stack bound, A's P2 kept,
   the achain premise dropped (item 5's exception: the proof does not consume it).

   STATEMENT ONLY.  Image B's core twin Reusable/YB1v.v (a Theorem Labs lane) is Required below, and SEGS is a
   local Notation for the decided term YB1v.tfibsegs.  The proof (pb_reac_box_catalogue_match,
   plan at the end) re-uses the proved B run
   lib/B/Prog/reac_box_catalogue_matchF_on.v (reac_box_catalogue_match_holds_F_on, this lane: the route-(C) `_on` copy
   of reac_box_catalogue_matchF.v) cut at its allocator events;
   nothing of the function is walked again here.

   Form: afn_pre / apost_base (CONVENTIONS section 2): the function writes only its own frame, its class-2 fake frame
   and that frame's shadow; the callees' writes are theirs (the 32 bytes at F + 112 that reac_box_model_block writes,
   the 36 bytes at F + 32 that reac_ctrl_parse writes, are inside this function's own fake frame). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YG0v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YE01 APostBase.
(* image B's core twin (a Theorem Labs lane's B run ec8ce4c2cc5): the segments.  YE2k (the sink head) is NOT required: at
   9afb8c9070a it does not compile (YE2k.v:12 holds an unrelocated, refused value for address 0x41980), so SK stays a
   Section variable. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YB1v.
(* the result value: the shared model of the function (lib/Prog, not a frame-route file) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcMatch.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil}.
Context {SK : lib.Reusable.YI16.sink_head}. (* := lib.Reusable.YE2k.tfib_sink_head once YE2k.v compiles *)
#[local] Notation SEGS := YB1v.tfibsegs.
(* The read-only span of arodata_okS (decisions.md item 17, cgif lib/YC20.v:56): the composer instantiates it with
   the B PA instance's pa_relro = [0x9f168, 0xa15e8) and discharges RELRO_IMG. *)
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.

(* B: the function's entry in fuzz_ctrl.asan-ubsan (lib/B/Prog/reac_box_catalogue_match_c.v:11). *)
Definition A_reac_box_catalogue_matchP : Z := 0x84e40. (* image-B address *)
(* B: BOX_CATALOGUE, 11 rows of 296 bytes (lib/B/Prog/reac_box_catalogue_match_c.v:13), inside the read-only span
   [0x9f168, 0xa15e8) of arodata_okS (GNU_RELRO): the result names it, so it is a constant like the entry pc.  The
   theorem's Section takes RLO <= A_CM_TBL /\ A_CM_TBL + CM_ROWS <= RHI (the composer: arithmetic at the PA span). *)
Definition A_CM_TBL : Z := 0x9f620. (* image-B address; A_ = 'address of' (donor convention, cgif YCei.v:23), NOT image A *)
(* the table's DATA size; [0x9f620, 0xa02d8).  The 808 bytes [0xa02d8, 0xa0600) are the redzone and are POISONED
   (B's own __asan_global entry 55: size 0xcb8, size_with_redzone 0xfe0; a Theorem Labs lane's zero-shadow-B.md (a working note, not in this delivery)): never
   state addressability or zero shadow over them. *)
Definition CM_ROWS : Z := 3256.
(* B: the machine stack the call needs = the window K of ctrl's proved image-B run that the glue re-uses
   (lib/B/Prog/reac_box_catalogue_match_c.v:14-19: 336 + reac_ctrl_parse's 8800; decision 4).  It contains the
   class-2 request's ESTACK below CA = (S - 128) & -32 >= S - 144, the bcmp wrapper's window 4560 and the callees'
   windows (reac_ctrl_parse 8800, reac_box_model_block 4272) at sp = CA. *)
Definition CM_STK : Z := 9136.
(* No heap allocation in the function or its callees. *)
Definition EV_CM : Z := 0.
Definition LIVE_CM : Z := 0.

Section e.
Variable B : asyms.

Definition treac_box_catalogue_match_post (regs : bvmap 5 word) ly S (W : world SEGS) mem md
    (len : Z) (fb : list byte) : world SEGS -> config -> Prop :=
  apost_base SEGS B CM_STK [] regs ly S W mem md EV_CM
    (fun ly' S' W' regs' mem' md' =>
       getr regs' 10 = w64 (RcMatch.want A_CM_TBL len fb) /\
       Permutation (ablocks B ly' S') (ablocks B ly S)).

Definition treac_box_catalogue_match_spec : Prop :=
  forall ly S W (regs : bvmap 5 word) mem md (f len : Z) (fb : list byte),
    (* P1: afn_pre SEGS B CM_STK ly S W regs mem md ch without its achain conjunct (decisions.md item 5,
       EXCEPTION 00:05Z: this proof does not consume the frame chain, and the LLVMFuzzerTestOneInput walk cannot
       supply it at this call site) *)
    AR SEGS B ly S W mem md ->
    YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
    getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
    astk_ok CM_STK ly (spZ regs) ->
    (forall a, spZ regs - CM_STK <= a < spZ regs -> apresent (w_H W) mem a) ->
    qtight S ->
    arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) mem) ->                            (* P2 *)
    getr regs 10 = w64 f -> getr regs 11 = w64 len -> 0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 ->
    (* the record: a live block of at least 50 bytes, read only when len >= 50 *)
    length fb = 50%nat ->
    (50 <= len -> exists n, In (f, n) (ablocks B ly S) /\ 50 <= req_size n) ->
    (50 <= len -> garr8 SEGS (mrestrict (w_H W) mem) f (map (fun b : byte => bv_unsigned b) fb)) ->
    (* the catalogue is read-only image data that the runtime does not own (A draft section 6 (a)) *)
    (forall a, A_CM_TBL <= a < A_CM_TBL + CM_ROWS ->
       ~ Exists (in_zr a) (as_owned_static B) /\ ~ (as_errno B <= a < as_errno B + 4)) ->
    (* frame room: class 2 for this function, class 1 for reac_ctrl_parse, class 0 for reac_box_model_block *)
    count_cid 2 (frames S) < fs_frames 2 ->
    count_cid 1 (frames S) < fs_frames 1 ->
    count_cid 0 (frames S) < fs_frames 0 ->
    st_nev S + EV_CM <= EV_MAX -> blocks_bytes S + LIVE_CM <= LIVE_MAX ->
    SRr SEGS W (cfg_at SEGS A_reac_box_catalogue_matchP regs mem md)
      (treac_box_catalogue_match_post regs ly S W mem md len fb).
End e.
End b.

(* ---- The theorem and its proof plan (written when its dependencies land; no Admitted) ------------------------

   Section m (inside Section b):
     Variable B : asyms.
     Hypothesis TL   : TfibLib B.                      (* B image-lib record, YCeh twin (a Theorem Labs lane) *)
     Hypothesis LAWS : AR_laws SEGS B.
     Hypothesis ML   : model_laws (as_universe B).
     Hypothesis ASM2 : astack_malloc_realizes SEGS B 2. (* fake-stack owner a Theorem Labs lane with a Theorem Labs lane *)
     Hypothesis SMP  : stack_malloc_progressP B.
     Hypothesis ASF  : astack_free_law SEGS B.
     Hypothesis FFL  : frame_flag_lawP SEGS B.
     (route (C): no ProgWorld statement is a hypothesis; the base facts come from ProgWorldCtlRtC.ctl_rt_C_of_AR)
     Hypothesis ABCMP : bcmp_wrap_c_on.bcmp_wrap_contract_F_on.  (* inside the lifted stretch after model_block *)
     Variable G : list (Z * Z).
     Hypothesis HGM : CtrlRoB.globs_marked SEGS B G.  Hypothesis HG17 : In (A_CM_TBL, CM_ROWS) G.
     Hypothesis HIMGSH : CtrlRoB.img_shadow_vis SEGS B.
     Hypothesis TPARSE : C_reac_ctrl_parse.treac_ctrl_parse_spec B.          (* a Theorem Labs lane *)
     Hypothesis TMB : C_reac_box_model_block.treac_box_model_block_spec B.   (* a Theorem Labs lane *)
     until lib/B/ProgWorld.v lands, as Section hypotheses named as agreed: ajournal_of_fsteps, img_vis,
     ctl_fs_of_astack (class argument), ctl_post_reac_ctrl_parse, ctl_post_reac_box_model_block.
     Theorem pb_reac_box_catalogue_match : treac_box_catalogue_match_spec B.

   The walk: the lifted stretches are the cut lemmas of reac_box_catalogue_matchF_on.v (qualified), each by
   ProgBridge.fevt_of_evtF + YA0nR.SRr_fevt at RNG := ProgBridge.RNG_W (w_H W), the image by img_vis, the journal by
   ajournal_of_fsteps; the segment terms by ProgBridge.tfibsegs_rsegs.
   | # | stretch / event                                  | carried by                                            |
   |---|--------------------------------------------------|-------------------------------------------------------|
   | A | lifted: entry 0x84e40 .. __asan_stack_malloc_2   | cm_pre_sm2                                            |
   | E1| EVENT class 2 (ra 0x84eb4)                       | aj_stack_malloc_at 2 ASM2 (room from the spec), then  |
   |   |                                                  | ctl_fs_of_astack 2 -> cm_fs_post_2                    |
   | B | lifted: 0x84eb4 .. gate .. reac_ctrl_parse call  | cm_post_sm2_side .. cm_pre_parse (len < 50: .. release)|
   | E2| EVENT reac_ctrl_parse (ra 0x85058)               | TPARSE, then ctl_post_reac_ctrl_parse -> cm_parse_post |
   | C | lifted: 0x85058 .. model_block call of row 0     | cm_post_parse .. cm_pre_mb (result <> 9: .. release)  |
   | Ei| EVENT reac_box_model_block, row i (ra 0x8509c)   | TMB, then ctl_post_reac_box_model_block -> cm_mb_post |
   | Di| lifted: 0x8509c .. bcmp .. row i+1 call / release| cm_post_mb, cm_bc (ABCMP), cm_pre_mb / cm_pre_rel;     |
   |   |                                                  | an SRr induction over the 11 rows                     |
   | R | RELEASE 0x85190 `sb zero,0(a1)` (class-2 flag)   | aj_flag_store / astack_free_law, frame_flag_lawP      |
   | Z | lifted: after the release .. ret                 | cm_post_rel                                           |
   The a0 = 0 arm of the class-2 request is dead in cgif form (astack_malloc_realizes has no such arm; the room
   premise count_cid 2 < fs_frames 2 is in the spec), so the glue uses the side arm only.
   --------------------------------------------------------------------------------------------------------------- *)
