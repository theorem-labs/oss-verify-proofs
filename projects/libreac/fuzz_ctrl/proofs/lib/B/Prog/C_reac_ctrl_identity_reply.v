(* reac_ctrl_identity_reply (0x848fc) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): its contract in
   cgif's world form (CONVENTIONS.md sections 2-5 (a working note, not in this delivery)), the image-B twin of a Theorem Labs lane's image-A draft
   (reply-A-spec-draft.md section 2 (a working note, not in this delivery)), under a Theorem Labs lane's B decisions
   decisions.md (a working note, not in this delivery): segments Reusable.YB1v.tfibsegs (items 1, 16;
   B's core twin, planning core 9afb8c9070a), a constant entry pc (item 3), arodata_okS with RELRO_IMG (items 2, 17),
   the window of the proved B run as the stack bound (item 4), the achain premise dropped (by item 5's exception:
   the proof does not consume it).

   STATEMENT ONLY. The proof (pb_reac_ctrl_identity_reply, plan at the end) re-uses the proved B run
   lib/B/Prog/reac_ctrl_identity_replyF.v (reac_ctrl_identity_reply_holds_F, a working branch; not in this delivery) cut at its
   allocator events (the class-1 request __asan_stack_malloc_1, the call of reac_ctrl_parse) and at the inline
   release of its frame; nothing of the function is walked again here.

   Form: cgif's CALLER-JOURNAL form (donor lib/YC20.v:311-365 of c8557374ad2e; the same form as a Theorem Labs lane's
   treac_ctrl_parse_spec): the function writes the caller's three cells, pa (2 bytes), pp (8) and pn (8), objects
   of a caller frame, besides its own machine frame, its class-1 fake frame, that frame's shadow and its flag byte.
   Core names: acall_kept / awr_byte (YCbq.v) stand where the A draft names grant's tcj_kept / twr_ok (not in the
   ctrl core); A's tsrc_ok (not in the core either) is dropped, the message being given by garr8 as on A. *)
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require Import YM05 YE01.
(* image B's core twin (a Theorem Labs lane's B run, planning core 9afb8c9070a): the segments.  YI16 / YK11 / YM05 are three
   of the SIX modules that exist twice (core lib/Reusable and ctrl lib/A/Reusable): only the CORE copy is Required,
   from the lib.Reusable path (porter 04:24Z / 04:33Z amendment (b)); the closure reaches one copy (Locate). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YB1v YI16.
(* the results: the shared model of the function (lib/Prog, not a frame-route file) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcReply.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section b. Context {fx : Reusable.YK11.FPState} {rc : Reusable.YM05.RunCeil}.
(* := Reusable.YE2k.tfib_sink_head once B's core twin's YE2k.v builds: on 9afb8c9070a it does not
   (YE2k.v:12, `port_core_refused_41980` not found; log build-20261029T031344Z.log), so the sink stays a Context. *)
Context {SK : Reusable.YI16.sink_head}.
#[local] Notation SEGS := Reusable.YB1v.tfibsegs.
(* The read-only span of arodata_okS (decisions.md item 17, cgif lib/YC20.v:56): the composer instantiates it with
   the B PA instance's pa_relro = [0x9f168, 0xa15e8) and discharges RELRO_IMG. *)
Variables RLO RHI : Z.
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> in_img SEGS a.

(* B: the function's entry in fuzz_ctrl.asan-ubsan (lib/B/Prog/reac_ctrl_identity_reply_c.v:11). *)
Definition A_reac_ctrl_identity_replyP : Z := 0x848fc. (* image-B address *)
(* B: the machine stack the call needs = the window K of ctrl's proved image-B run that the glue re-uses
   (lib/B/Prog/reac_ctrl_identity_reply_c.v:12-17: 272 + reac_ctrl_parse's 8800; decision 4). It contains the
   own 128-byte frame realigned to 32 (rA = (S - 128) & -32 >= S - 144, 0x8493c), the class-1 request's ESTACK below
   rA, and reac_ctrl_parse's window 8800 at sp = rA. *)
Definition REAC_CTRL_IDENTITY_REPLY_STK : Z := 9072.
(* No heap allocation in the function or its callees: __asan_stack_malloc_1 and the flag release keep st_nev. *)
Definition EV_REPLY : Z := 0.

Section e.
Variable B : asyms.

(* The caller's three cells the function writes when it succeeds. *)
Definition treply_out (pa pp pn a : Z) : Prop :=
  pa <= a < pa + 2 \/ pp <= a < pp + 8 \/ pn <= a < pn + 8.

Definition treac_ctrl_identity_reply_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate)
    (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
    (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
    (regs : bvmap 5 word) (fr len pa pp pn : Z) (g : list byte) : world SEGS -> config -> Prop :=
  fun W2 c2 => wle W W2 /\ exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_REPLY) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\
    Permutation (ablocks B ly2 S2) (ablocks B lyc Sc) /\
    getr regs2 10 = w64 (RcReply.reply_ret fr len pa pp pn g) /\
    acall_kept SEGS B lyc Sc W memc W2 mem2 (spZ regs - REAC_CTRL_IDENTITY_REPLY_STK) (spZ regs)
      (fun a => RcReply.reply_ok fr len pa pp pn g = true /\ treply_out pa pp pn a) /\
    (RcReply.reply_ok fr len pa pp pn g = true ->
       garr8 SEGS (mrestrict (w_H W2) mem2) pa (map (fun b : byte => bv_unsigned b) (RcReply.reply_addr g)) /\
       val_mem SEGS (mrestrict (w_H W2) mem2) pp 8 (fr + 38) /\
       val_mem SEGS (mrestrict (w_H W2) mem2) pn 8 (RcReply.ir_s g - 13)).

Definition treac_ctrl_identity_reply_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word)
         (fr len pa pp pn : Z) (g : list byte),
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->                       (* P1 *)
    arodata_okS SEGS B RLO RHI (aview SEGS (w_H W) memc) ->                                        (* P2 *)
    YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->                                               (* P3 *)
    getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->                                (* P4 *)
    getr regs 10 = w64 fr -> getr regs 11 = w64 len -> getr regs 12 = w64 pa ->                    (* P5 *)
    getr regs 13 = w64 pp -> getr regs 14 = w64 pn ->
    0 <= fr < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> 0 <= pa < 2 ^ 64 -> 0 <= pp < 2 ^ 64 -> 0 <= pn < 2 ^ 64 ->
    (* P6 (achain) dropped: decisions.md item 5, EXCEPTION 00:05Z *)
    spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - REAC_CTRL_IDENTITY_REPLY_STK -> spZ regs <= sp0 -> (* P7 *)
    (* fake-stack class 1: its own frame and, while it holds it, reac_ctrl_parse's *)
    count_cid 1 (frames Sc) + 1 < fs_frames 1 ->                                                   (* P8 *)
    (* the message: read only when the four pointers are non-null and len >= 50; a heap block from its start
       (reac_ctrl_parse's P9 / P12 / P13 at the call) *)
    length g = 50%nat ->                                                                           (* P9 *)
    (RcReply.reply_args fr pa pp pn = true -> 50 <= len ->
       (exists nb, In (fr, nb) (ablocks B lyc Sc) /\ 50 <= req_size nb) /\
       garr8 SEGS (mrestrict (w_H W) memc) fr (map (fun b : byte => bv_unsigned b) g)) ->            (* P10 *)
    (* the caller's three cells: objects of a caller frame that the call may write, aligned, apart,
       addressable *)
    (RcReply.reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (forall a, treply_out pa pp pn a ->
          (* cid <> 1: a class-1 frame cell breaks rrB_SB_lifted's FP0 (fp_dj D (fp_w [1%nat] FS), RcAsanFP.v:56) *)
          (exists cid pos, In (cid, pos) (frames Sc) /\ cid <> 1 /\ in_zr a (frame_rng lyc (cid, pos))) /\
          awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a) /\
       range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pa 2 /\
       range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pp 8 /\
       range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF pn 8) ->                             (* P11 *)
    SRr SEGS W (cfg_at SEGS A_reac_ctrl_identity_replyP regs memc mdc)
      (treac_ctrl_identity_reply_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fr len pa pp pn g).
End e.
End b.

(* ---- The theorem and its proof plan (written when its dependencies land; no Admitted) ------------------------

   Section m (inside Section b):
     Variable B : asyms.
     Hypothesis TL   : TfibLib B.                       (* B image-lib record, YCeh twin (a Theorem Labs lane) *)
     Hypothesis LAWS : AR_laws SEGS B.
     Hypothesis ML   : model_laws (as_universe B).
     (* the class-1 fake-stack rules: a Theorem Labs lane's, taken from a working branch ff613211c11 (cgif lib/A/ACed.v:125-133,
        tfibX_ASM1 / tfibX_SMP / tfibX_ASF / tfibX_FFL), never restated (a Theorem Labs lane 01:18Z) *)
     Hypothesis ASM1 : astack_malloc_realizes SEGS B 1.
     Hypothesis SMP  : stack_malloc_progressP B.
     Hypothesis ASF  : astack_free_law SEGS B.
     Hypothesis FFL  : frame_flag_lawP SEGS B.
     Hypothesis RTB  : ProgWorld.ctlrt_of_AR_stmt B.    (* a Theorem Labs lane's lib/B/ProgWorld.v *)
     Hypothesis TPARSE : C_reac_ctrl_parse.treac_ctrl_parse_spec B.          (* a Theorem Labs lane *)
     until lib/B/ProgWorld.v lands, as Section hypotheses named as agreed: ajournal_of_fsteps,
     ctl_fs_of_astack (class argument), ctl_post_reac_ctrl_parse, ctl_release_of_free_law (class argument); and,
     until a Theorem Labs lane's B twin lands, img_vis_W named as A's (ProgBridge 7b850582d6a img_vis_of_Hoff / img_vis_W).
     Theorem pb_reac_ctrl_identity_reply : treac_ctrl_identity_reply_spec B.

   The walk: the lifted stretches are the cut lemmas of reac_ctrl_identity_replyF.v (not in this delivery) (qualified), each by
   ProgBridge.fevt_of_evtF + YA0nR.SRr_fevt at RNG := ProgBridge.RNG_W (w_H W); the run's image premise is paid AT
   EACH LIFT by ProgBridge.rng_of_visible (img_vis_W W) (decisions.md item 20b (a working note, not in this delivery): no image conjunct in this spec, none
   needed by the function's own run beyond what the lift discharges); the journal by ajournal_of_fsteps; the segment
   terms by ProgBridge.tfibsegs_rsegs. The post-call stretches are the re-based Section copy of a Theorem Labs lane's ruling
   (00:49Z) in a Theorem Labs lane's form.
   | # | stretch / event                                       | carried by                                        |
   |---|-------------------------------------------------------|---------------------------------------------------|
   | A | lifted: entry 0x848fc .. __asan_stack_malloc_1        | rp_stretchA_F                                     |
   | E1| EVENT class 1 (ra 0x8497c)                            | aj_stack_malloc_at 1 ASM1 (room from P8), then     |
   |   |                                                       | ctl_fs_of_astack 1                                |
   | B | lifted: 0x8497c .. reac_ctrl_parse call (null-pointer | rp_stretchB0_F .. rp_call_pre_F (null pointer: ..  |
   |   | exit: .. the flag release)                            | rp_epi .. rp_td_pre_F)                            |
   | E2| EVENT reac_ctrl_parse (ra 0x84a68)                    | TPARSE, then ctl_post_reac_ctrl_parse             |
   | C | lifted: 0x84a68 .. the flag release (the record-sum    | rKF = rp_tag (+ CKV inside) .. rp_stores / rp_fail |
   |   | call 0x84ba8 raises no event and stays inside)        | .. rp_f8 .. rp_epi .. rp_td_pre_F                 |
   | R | RELEASE 0x84c34 `sb zero,0(a1)` (class-1 flag)        | ctl_release_of_free_law 1 (fsteps twin of          |
   |   |                                                       | YCbq.v:2362 aj_flag_store), frame_flag_lawP       |
   | D | lifted: 0x84c38 .. ret                                | rp_td_post_F (.. rp_ret)                          |
   The a0 = 0 arm of the class-1 request is dead in cgif form (astack_malloc_realizes has no such arm; the room
   premise P8 is in the spec), so the glue uses the side arm only.
   --------------------------------------------------------------------------------------------------------------- *)
