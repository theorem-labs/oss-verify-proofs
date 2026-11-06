(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/jsoncons/fuzz_bigint/lib/L5TCopyS.v, with its module paths and module names changed; 2093 of its 2111 lines of code are new or changed and 230 lines of the source are left out. *)
(* reac_ctrl_parse (0x83e04, 2692 bytes) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): ctrl's PROVED
   footprint run lib/B/Prog/reac_ctrl_parseF.v (reac_ctrl_parse_x_F_holds), cut at its one allocator event, the
   class-1 request __asan_stack_malloc_1 (jal 0x83e74), and RE-BASED at the memory after that call, for the cgif-form
   glue of reac_ctrl_parse (porter ruling a Theorem Labs lane 2026-10-28T23:53Z: a declared re-basing, not a new _F file).
   rule 24: no function proved here; the run is ctrl's (released parse proofs are plain / ubsan guides only, run
   2026-10-28T22:31Z, CONFIRM a Theorem Labs lane 22:55Z).

   (a) rcpB_pre_F: 0x83e04 to the stack-malloc entry 0x3d868 (reac_ctrl_parseF.v's `entry` up to its jal), with the
       hypotheses this stretch reads only (the window and the four runtime cells `entry` destructs; no side-stack
       premise FP0).
   (b) Section SetupFB: 0x83e78 (the return of the call) to the ret 0x84314, at the memory m after the call, with the
       frame described in the cgif API's stack-malloc form (what astack_malloc_realizes gives, cgif c8557374ad2e
       lib/YG0d.v:284-298, plus the AR laws): Fr = frame_addr lyc 1 pos and FL = flag_addr lyc 1 pos (the glue
       instantiates them), no FS / fs_frame / flag-at-entry / runtime write set.  End condition Qb at the return.
       The instruction-level scripts are COPIED VERBATIM from reac_ctrl_parseF.v (fwords, the check tactics, b_done ..
       b_none, L_body_k, the side arm of L_epi, L_restore's stepping); a diff against reac_ctrl_parseF.v shows only
       the re-based helpers (named in the commit message, each with its reason) and these two lines of L_body_k:
       its FK case split (FK has one arm here) and its one FP0 use (.str.4 below the frame: now FkImg).  In the
       copied statements `Qp` is a local notation for Qb.
   (c) rcpB_keep / rcpB_wkeep: the composition across the call in the visible form.
   (d) Section RoFB, rcpB_post_F_ro: (b) on the REAL memory after the call (ro_agree, not mem_inv), by one normalize
       at the stretch base (lib/B/MemNormF.v, lib/B/MemNormTr.v); the post Qbr is Qb with ro_agree for mem_inv.

   THE PATTERN (a Theorem Labs lane 00:49Z: the template of the B / A glue of identity_reply, catalogue_match, model_block,
   lay_block, classify and parse).  Cut the _F run at its fake-stack call.  (a) One lemma for the stretch before the
   call, ending at pc_stack_malloc, its hypotheses cut to what that stretch reads.  (b) One Section re-based at the
   memory m AFTER the call: every Section hypothesis is a single-memory fact AT m (none is a munch / wmono relative
   to the entry memory), and the body invariants (BI, aJb, BJ) and the end condition Qb are relative to m.  Where
   the glue gets each Section hypothesis:
     - the frame (variables Fr FL, hypotheses FkAl .. FlO): the post of cgif's astack_malloc_realizes and the AR
       laws, clause by clause (the comment above them); the glue instantiates Fr := frame_addr lyc 1 pos and
       FL := flag_addr lyc 1 pos;
     - the runtime facts, which the run reads outside its own footprint (MI0 mem_inv over all bytes; SR0 the
       presence of the shadow region P, route (C)) and the runtime cells (AC0 asan_cells, HBCMP .. HCF255 the bcmp
       wrapper's cells): taken AT m from the world at the cut (lib.B.ProgWorldCtlRtC.ctl_rt_C_of_AR for AC0 and SR0,
       with P := cut_shadow lyc S2 \/ img_shadow by lib.B.ShadowRwOn.shadow_rw_on_union;
       lib.B.ProgBridgeData.ctl_bcmp_cells_of_AR for the bcmp wrapper's cells), never carried from the entry memory.
       The four covering hypotheses SRFr, SRf, SRo, SRbc name the shadow that P must hold: the aligned shadow-word
       span (sh_word_on) of any range inside the frame, f's 50 bytes, o's 36 bytes and .str.4's 6 bytes;
     - the window (ST0, AW0): the journal at the cut (present, writable) and AR_zshadow_law (zero shadow);
     - the data bytes and the caller's ranges (Hrd, HOK, AF0, AO0, ABC) and the saved registers (SVm, from
       rcpB_pre_F's post): carried over the call by its visible keep (YG0d.v:297: visible, not runtime-owned, outside
       the call's window), all of them inside the run's footprint;
     - RNG := the bytes not hidden in the world (RNG_W (w_H W)): each rng premise is "these bytes are visible".
   (c) composes the pre-call munch (entry -> pc_stack_malloc), the call's visible keep and Qb's munch (m -> ret) into
   one visible keep from the entry to the return.  An all-address entry-relative munch / wmono is NOT derivable
   across the call: the rule keeps only visible bytes that are not runtime-owned, and the runtime writes its own
   bytes (the class-1 hint word, the flag array). *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcKind RcKindLib RcLib RcParse RcParseLib
  RcAsan RcAsanLib RcBoxLib RcClassifyLib.
(* as reac_ctrl_parseF.v: asan_memset_cF / asan_memcpy_cF before reac_ctrl_parse_c; then reac_ctrl_parseF's general
   lemmas and tactics (rd_mono, stk_mono, the acl_ / frame_shadow_ lemmas, steps_to, chk_core, ...). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT RcAsanFP RcAsanFPLib
  asan_stack_malloc_c asan_memset_c asan_memcpy_c asan_memset_cF asan_memcpy_cF memcmp_c bcmp_wrap_c
  kind_of_link1_c kind_of_link1F reac_ctrl_parse_c reac_ctrl_parseF.
(* route (C): the callees' _on statements (premise `shadow_rw_on R m` for the shadow each callee reads, post
   `forall P, shadow_rw_on P m -> shadow_rw_on P m'`), and C_reac_ctrl_parseOn.v's shadow_rw_on twins of
   reac_ctrl_parseF's general lemmas.  None of them Exports a module, so the names above keep their sources. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_memset_cF_on asan_memcpy_cF_on
  bcmp_wrap_c_on C_reac_ctrl_parseOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOn B.Prog.sh_word_on B.Prog.asan_memset_c_on
  B.Prog.asan_memcpy_c_on.
(* Last: StepF's step / if_cases (evtF goals) shadow Step's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
Import ListNotations.
Open Scope Z_scope.

(* reac_ctrl_parseF.v's tactic hooks, which are local to that file: its acc_hint (a shadow access closes from the
   quantified covers), its store hook, and its footprint_after_store (which also carries rd_mono over a store). *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.acc_hint ::= acc_hintF.
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::= rcpF_store_opt.
Local Ltac footprint_after_store segs m a bs ::=
  repeat match goal with
  | MU : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_write Wq mq m a bs) in MU; [ | lia | simpl_sizes; slia | cbn [inside]; simpl_sizes; slia ]
            | fail 100 "store outside the declared footprint:" a ]
  | WMo : wmono segs ?mq m |- _ => apply (wmono_write segs mq m (wa a) bs) in WMo
  | RMo : rd_mono ?mq m |- _ => apply (rd_mono_write mq m (wa a) bs) in RMo
  | STq : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_write segs m loq hiq a bs) in STq; [ | lia | simpl_sizes; slia ]
            | fail 100 "cannot transport stk hypothesis" STq ]
  end.

(* ------------------------------------------------------------------------------------------------------------ *)
(* (a) Before the call: 0x83e04 .. the class-1 request, jal 0x83e74 to __asan_stack_malloc_1 = 0x3d868.  The script
   is reac_ctrl_parseF.v's `entry` up to its jal.  What it reads: the window (13 stores in [S - 128, S)), and of
   asan_cells only the four cells `entry` destructs (the shadow-offset cell CELL_K and its GOT word, the
   use-after-return word UAR = 1 and its GOT word); no side-stack premise (FP0 is first read after the call).  The
   post is the state at the stack-malloc entry: ra = 0x83e78, a0 = 128 (the class-1 frame size), sp = s1 = A =
   (S - 128) & -32, s0 = S, s4 / s5 / s6 = o / f / n, s9 = the shadow offset, the 12 caller registers saved at
   [S - 96, S), the memory changed only in [S - 128, S). *)
Lemma rcpB_pre_F : forall (RNG : ExecF.footprint)
    (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f n o S : Z),
  0 <= f < 2^64 -> 0 <= n < 2^64 -> 0 <= o < 2^64 -> 8800 <= S < 2^64 -> S mod 16 = 0 ->
  HIGHMEM_BEG <= S - 8800 -> S <= APPMEM_END ->
  stk rsegs m (S - 8800) S -> mem_inv rsegs m ->
  bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) -> bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) ->
  bytes_at rsegs m UAR (le4 (wa 1)) -> bytes_at rsegs m GOT_UAR (le8 (wa UAR)) ->
  rng RNG 0x10000 0x5ee000 -> rng RNG (S - 8800) 8800 ->
  evtF rsegs RNG
    (fun ms' => exists m1,
       ms' = MS (mkR (Z_to_bv 64 0x83e78) (Z_to_bv 64 ((S - 128) / 32 * 32)) gp tp t0 t1 t2 (Z_to_bv 64 S)
                     (Z_to_bv 64 ((S - 128) / 32 * 32)) (Z_to_bv 64 128) (wa CELL_K) (sx32 (wa 1)) a3 a4 a5 a6 a7
                     s2 s3 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n) s7 s8 (wa ASAN_K) s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x3d868) fc None m1 (seg_rom rsegs) /\
       munch [(S - 128, S)] m m1 /\ wmono rsegs m m1 /\ rd_mono m m1 /\ mem_inv rsegs m1 /\
       rw_cells rsegs m1 (S - 96) [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 n) (Z_to_bv 64 o)
             a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f n o S
    Rf Rn Ro RS S16 HHM HAE ST0 MI CK GCK UA GUA RIMG RWIN.
  set (A := (S - 128) / 32 * 32).
  assert (HA1 : A mod 32 = 0 /\ S - 160 < A <= S - 128) by (unfold A; Z.div_mod_to_equations; lia).
  unfold REAC_CTRL_PARSE.
  pose proof HA1 as (HA32 & HAlo & HAhi).
  pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
  assert (MU : munch [(S - 128, S)] m m) by apply munch_refl.
  assert (WM : wmono rsegs m m) by apply wmono_refl.
  assert (RM : rd_mono m m) by apply rd_mono_refl.
  unfold CELL_K, GOT_CELL_K, UAR, GOT_UAR in CK, GCK, UA, GUA.
  apply bytes_ro8 in CK. apply bytes_ro8 in GCK. apply bytes_ro4 in UA. apply bytes_ro8 in GUA.
  pose proof (stk_split rsegs m _ (S - 96) _ ST0 ltac:(lia)) as [STw STs].
  pose proof (stk_split rsegs m _ (S - 128) _ STw ltac:(lia)) as [STw2 STz].
  clear ST0 STw STw2.
  carve_frame 96%nat STs.
  carve_frame 32%nat STz.
  step.
  steps_to 0x83e40.
  step.
  assert (EA : Z.land (bv_unsigned (Z_to_bv 64 (S + -128))) 18446744073709551584 = A)
    by (rewrite unsigned_lit, land_align32 by lia; unfold A; f_equal; f_equal; lia).
  rewrite EA.
  steps_to 0x83e6c.
  step.
  replace (bv_eqb (sx32 (wa 1)) (Z_to_bv 64 0)) with false by (vm_compute; reflexivity). cbv iota.
  step. step.
  lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) => apply evtF_done; exists mm end.
  split; [solve [reflexivity | repeat f_equal; first [reflexivity | lia]] |].
  split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI | exact FR].
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* [a, a + la) and [b, b + lb) are apart.  The frame's separation hypotheses are stated with it so that lia, which
   splits on every disjunction and implication over linear facts in the context, does not split on them in each of
   the copied scripts' goals; the re-proved helpers unfold it where they use it. *)
Definition rcpB_dj (a la b lb : Z) : Prop := a + la <= b \/ b + lb <= a.

(* (b) After the call: Section SetupFB, re-based at the memory m at 0x83e78. *)
Section SetupFB.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n o S : Z) (fr junk : list byte) (RNG : ExecF.footprint) (Fr FL : Z).
  (* route (C): the shadow region the stretch holds at m (SR0 below); the four covering hypotheses SRFr .. SRbc
     after SR0 say which shadow bytes P holds. *)
  Variable P : Z -> Prop.
  (* The caller's state, as reac_ctrl_parseF.v's Section SetupF states it, now at the memory m after the call
     (the prologue wrote only [S - 128, S); the call kept every visible byte outside its frame, its window and the
     runtime's own bytes).  ra, s0 .. s11 are the caller's registers (the 12 saved ones are at [S - 96, S), SVm). *)
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rn : 0 <= n < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis RS : 8800 <= S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - 8800) S.
  Hypothesis MI0 : mem_inv rsegs m.   (* source pending: a Theorem Labs lane (mem_inv at post-call memory) *)
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 8800 \/ S <= f).
  Hypothesis Hrd : forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i.
  Hypothesis HOK : o <> 0 ->
    o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
    (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o).
  (* AC0, SR0, the bcmp wrapper's cells below: taken AT m from the world at the cut.  AC0 and SR0 from
     lib.B.ProgWorldCtlRtC.ctl_rt_C_of_AR (ctl_rt_C = asan_cells_at /\ shadow_rw_on (cut_shadow ly S) /\
     shadow_rw_on img_shadow /\ ro_agree_at, from AR with no visibility law), P := cut_shadow lyc S2 \/ img_shadow by
     lib.B.ShadowRwOn.shadow_rw_on_union; the bcmp wrapper's cells from lib.B.ProgBridgeData.ctl_bcmp_cells_of_AR.
     MI0 (above, mem_inv over all bytes of m): source pending, a Theorem Labs lane (mem_inv at post-call memory; ctl_rt dropped
     mem_inv_at 00:34Z).  ST0 / AW0: the window, from the journal at the cut (win_vis_stmt / win_sh_vis_stmt,
     AR_zshadow_law).  Hrd, HOK, AF0, AO0, ABC (and SVm below): carried over the call by its visible keep, munch_vis /
     wmono_vis of rt_post_frame_vis. *)
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : lib.B.ShadowRwOn.shadow_rw_on P m.
  (* The shadow that P holds: the aligned shadow-word span (lib.B.Prog.sh_word_on.sh_word_on p k) of every range
     [p, p + k) inside the class-1 frame [Fr, Fr + 128) (its 16 shadow bytes, which fwords writes and L_epi
     rewrites, and the record scratch at Fr + 32 that __asan_memset / __asan_memcpy check when o = 0), inside f's 50
     bytes (the sources of the two __asan_memcpy and the first operand of the bcmp wrapper), inside o's 36 bytes (the
     record that __asan_memset / __asan_memcpy check when o <> 0), and inside .str.4's 6 bytes (the bcmp wrapper's
     second operand).  The callees read no other shadow through their shadow_rw_on premise. *)
  Hypothesis SRFr : forall p k a, Fr <= p -> p + k <= Fr + 128 -> lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Hypothesis SRf : 50 <= n -> forall p k a, f <= p -> p + k <= f + 50 -> lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Hypothesis SRo : o <> 0 -> forall p k a, o <= p -> p + k <= o + 36 -> lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Hypothesis SRbc : forall p k a, REAC_CTRL_PARSE_BC <= p -> p + k <= REAC_CTRL_PARSE_BC + 6 ->
    lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Hypothesis HHM : HIGHMEM_BEG <= S - 8800.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - 8800) 8800.
  Hypothesis AF0 : 50 <= n -> addressable m f 50.
  Hypothesis AO0 : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o).
  Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
  Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
  Hypothesis HGCF : bytes_at rsegs m GOT_CF (le8 (wa CF)).
  Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].

  (* ---- The frame of the class-1 request, in the cgif API's stack-malloc form: each hypothesis is the lib/Lib
     image, at the memory m after the call, of one clause of astack_malloc_realizes' post (cgif c8557374ad2e
     lib/YG0d.v:284-298) or of the AR law that clause's frame (1, pos) :: frames S satisfies.  The glue takes
     Fr := frame_addr lyc 1 pos (the post's a0, YG0d.v:293) and FL := flag_addr lyc 1 pos.
       FkAl, FkApp   AR_frames_law (YG0d.v:447-455): frame_addr mod 32 = 0, in_app over fs_frame_bytes 1 = 128.
       FkSt          YG0d.v:296 (frame bytes apresent) + AR_frames_law (not aowned): present, so writable.
       Fk120         YG0d.v:295: rdword (frame_addr + fs_frame_bytes 1 - 8) = Some (flag_addr), the flag word.
       FkLo, FkHi    AR_sep_law (YG0d.v:476-480): 4096 <= frame_addr, frame_addr + 128 <= alloc_ceiling, and the
                     window lies above alloc_ceiling (ly_stk_lo, astk_ok).
       FkImg         AR_client_img_law (YG0d.v:490-495): no frame byte in the image (ly_img).
       FkF, FkO      AR_sep_law: the frame is apart from the caller's blocks and frames, which hold f's 50 bytes and
                     o's 36 bytes ((1, pos) is not in frames S, the call's apath).
       FlSt .. FlO   frame_flag_lawP (cgif YCbq.v): flag_addr present, an application byte, not an image byte, below
                     alloc_ceiling, runtime-owned (so apart from the caller's f and o).
     The side stack is a runtime-owned extent, which the call's keep (YG0d.v:297) does not carry: so these facts
     are taken AT m from the named world statements of ProgWorld (a working branch
     c03ce1627b6 lib/A/ProgWorld.v; B twin lib/B/ProgWorld.v): FkAl FkApp FkSt Fk120 FkImg (ASAN_GT <= fr) from
     ctl_fs_of_astack_stmt 1, with Fr = fs_frame FS 1 pos = frame_addr lyc 1 pos and FL = fs_flag FS 1 pos =
     flag_addr lyc 1 pos by ctl_fs_geom; FlSt (inside stk FS (FS + FS_SIZE)) from ctl_fs_of_AR_stmt; FkLo FkHi FkF FkO
     FlApp FlHi FlImg FlF FlO from the AR laws named above.  Never carried from the entry memory.  No other
     side-stack byte (hint word, other frames' flags) is read after m.  The release (FL := 0 at 0x84294, Qb's last
     conjunct) is the glue's ctl_release_of_free_law_stmt 1.
     YG0d.v:294 (the frame's shadow is zero) is not needed by the run: fwords writes all 16 shadow bytes before any
     read, and their writability is SR0 (shadow_rw_on P, P holding them by SRFr).  YG0d.v:297-298 (bytes kept
     outside the owned bytes and the call's window, the window present) are what the glue uses to carry the caller's
     facts above to m. ---- *)
  Hypothesis FkAl : Fr mod 32 = 0.
  Hypothesis FkApp : forall i, 0 <= i < 128 -> app_mem (Fr + i).
  Hypothesis FkSt : stk rsegs m Fr (Fr + 128).
  Hypothesis Fk120 : bytes_at rsegs m (Fr + 120) (le8 (Z_to_bv 64 FL)).
  Hypothesis FkLo : 4096 <= Fr.
  Hypothesis FkHi : Fr + 128 <= S - 8800.
  Hypothesis FkImg : rcpB_dj Fr 128 ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO).
  Hypothesis FkF : 50 <= n -> rcpB_dj f 50 Fr 128.
  Hypothesis FkO : o <> 0 -> rcpB_dj o 36 Fr 128.
  Hypothesis FlSt : stk rsegs m FL (FL + 1).
  Hypothesis FlApp : app_mem FL.
  Hypothesis FlHi : FL + 1 <= S - 8800.
  Hypothesis FlImg : rcpB_dj FL 1 ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO).
  Hypothesis FlF : 50 <= n -> rcpB_dj f 50 FL 1.
  Hypothesis FlO : o <> 0 -> rcpB_dj o 36 FL 1.

  (* ---- The footprint premises of the run, as reac_ctrl_parseF.v's (quantified shadow covers), with the frame's
     128 bytes, their shadow and the flag byte in place of the side stack's ranges. ---- *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 8800) 8800.
  Hypothesis SCW : shcov RNG (S - 8800) 8800.
  Hypothesis SKW : shkov RNG (S - 2560) 2432.
  Hypothesis RINF : 50 <= n -> rng RNG f 50.
  Hypothesis SCF : 50 <= n -> shcov RNG f 50.
  Hypothesis SKF : 50 <= n -> shkov RNG f 50.
  Hypothesis ROUT : o <> 0 -> rng RNG o 36.
  Hypothesis SCO : o <> 0 -> shcov RNG o 36.
  Hypothesis SKO : o <> 0 -> shkov RNG o 36.
  Hypothesis RBC : rng RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFk : rng RNG Fr 128.
  Hypothesis SCFk : shcov RNG Fr 128.
  Hypothesis SKFk : shkov RNG Fr 128.
  Hypothesis RFl : rng RNG FL 1.


  (* the aligned sp (s1 after andi) *)
  Definition A : Z := (S - 128) / 32 * 32.

  Lemma HA1 : A mod 32 = 0 /\ S - 160 < A <= S - 128.
  Proof. unfold A. Z.div_mod_to_equations. lia. Qed.

  Lemma STW0 : forall a, S - 8800 <= a < S -> wview rsegs m (wa a) <> None.
  Proof. intros a Ha. exact (stk_wv m _ _ _ ST0 Ha). Qed.

  (* The 12 saved registers, lowest address (S-96, s10) first. *)
  Definition SAVES : list cell :=
    [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* The 12 caller registers the prologue saved (rcpB_pre_F's post), kept by the call (outside its window). *)
  Hypothesis SVm : rw_cells rsegs m (S - 96) SAVES.

  (* RE-BASED.  The writes of the run outside o: the window, the flag byte FL, the frame and its shadow.  The second
     entry (the class-1 hint word in reac_ctrl_parseF.v, written by the runtime before m) is the empty range, so the
     positional proofs over Wf keep their shape. *)
  Definition Wf (fr j nn : Z) : list ivl :=
    [(S - 8800, S); (FL, FL); (FL, FL + nn); (fr, fr + 128); (shadow_addr fr, shadow_addr fr + 16)].

  (* RE-BASED.  The frame: the one the call returned (fv = fr = Fr, sp = A, the flag-word value w120 = FL at fr + 120);
     reac_ctrl_parseF.v's real-stack arm (fv = 0) is not reachable from the cgif rule, which returns a frame.
     j is kept (as 0) so that the copied statements keep their arity. *)
  Definition FK (fr fv spc j nn : Z) (w120 : word) : Prop :=
    j = 0 /\ fr = Fr /\ fv = fr /\ spc = A /\ w120 = Z_to_bv 64 FL /\ nn = 1.

  (* NEW (route (C)): the frame's 16 shadow bytes, at the addresses the run forms, are in P: they are in the aligned
     shadow-word span of the frame's 128 bytes (lib.B.Prog.C_reac_ctrl_parseOn.sh_word_on_frame16), which SRFr
     covers. *)
  Lemma fr_sh_P : forall a, Fr / 8 + ASAN_K <= a < Fr / 8 + ASAN_K + 16 -> P a.
  Proof. intros a Ha. apply (SRFr Fr 128 a); [lia | lia | exact (sh_word_on_frame16 Fr a Ha)]. Qed.

  Lemma fk_sh_P : forall fra fv spc j nn w120, FK fra fv spc j nn w120 ->
    forall a, fra / 8 + ASAN_K <= a < fra / 8 + ASAN_K + 16 -> P a.
  Proof. intros fra fv spc j nn w120 (_ & Efr & _) a Ha. subst fra. exact (fr_sh_P a Ha). Qed.


  Lemma app_range : forall Y nn, 0 < nn -> (forall i, 0 <= i < nn -> app_mem (Y + i)) ->
    Y + nn <= 2147450880 \/ 17594333495296 <= Y.
  Proof.
    intros Y nn Hn H. pose proof (H 0 ltac:(lia)) as H0. pose proof (H (nn - 1) ltac:(lia)) as H1.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H0, H1.
    destruct (Z.le_gt_cases (Y + nn) 2147450880) as [L|L]; [left; exact L|].
    destruct (Z.le_gt_cases 17594333495296 Y) as [G|G]; [right; exact G|].
    exfalso. pose proof (H (2147450880 - Y) ltac:(lia)) as H2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H2. lia.
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v read the side stack's placement out of FP0): what the frame gives, from FkAl,
     FkApp, FkSt, FkLo, FkHi.  The second conjunct is 4096 <= fr where reac_ctrl_parseF.v had FS + 36864 <= fr. *)
  Lemma fk_facts : forall fr fv spc j nn w120, FK fr fv spc j nn w120 ->
    fr mod 8 = 0 /\ 4096 <= fr /\ fr + 128 <= A /\ (spc = A \/ spc = fr) /\
    (forall i, 0 <= i < 128 -> wview rsegs m (wa (fr + i)) <> None) /\
    (forall i, 0 <= i < 128 -> app_mem (fr + i)) /\
    (fr + 128 <= 2147450880 \/ 17594333495296 <= fr) /\
    (forall i, 0 <= i < 16 -> wview rsegs m (wa (fr / 8 + ASAN_K + i)) <> None) /\
    2147450880 <= fr / 8 + ASAN_K /\ fr / 8 + ASAN_K + 16 <= 17594333495296.
  Proof.
    intros fr0 fv spc j nn w120 (Ej & Efr & Ef & Esp & Ew & En). subst fr0.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (B : Fr mod 8 = 0 /\ 4096 <= Fr /\ Fr + 128 <= A /\ (spc = A \/ spc = Fr) /\
                (forall i, 0 <= i < 128 -> wview rsegs m (wa (Fr + i)) <> None) /\
                (forall i, 0 <= i < 128 -> app_mem (Fr + i))).
    { split; [clear -FkAl; Z.div_mod_to_equations; lia|]. split; [exact FkLo|].
      split; [clear -FkHi HAlo; lia|]. split; [left; exact Esp|].
      split; [intros i Hi; apply (stk_wv m _ _ _ FkSt); lia | exact FkApp]. }
    destruct B as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (app_range Fr 128 ltac:(lia) B6) as B7.
    assert (B8 : forall i, 0 <= i < 16 -> Fr / 8 + ASAN_K + i = shadow_addr (Fr + 8 * i)).
    { intros i Hi. rewrite sh_add8 by exact B1. unfold shadow_addr. lia. }
    do 7 (split; [assumption|]).
    split.
    - intros i Hi. rewrite B8 by exact Hi.
      assert (HPi : P (shadow_addr (Fr + 8 * i))) by (rewrite <- (B8 i Hi); apply fr_sh_P; lia).
      apply (proj1 (SR0 _ HPi (rt_app_shadow _ (B6 (8 * i) ltac:(lia))))).
    - unfold ASAN_K. split; Z.div_mod_to_equations; lia.
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v took them from the side stack's frame area RFRM / SCFR / SKFR): the frame's 128
     bytes and their shadow are in RNG. *)
  Lemma rngF_frame : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> rng RNG fra 128.
  Proof. intros fra fv spc j nn w120 (_ & Efra & _). subst fra. exact RFk. Qed.

  Lemma rngF_frame_cov : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shcov RNG fra 128.
  Proof. intros fra fv spc j nn w120 (_ & Efra & _). subst fra. exact SCFk. Qed.

  Lemma rngF_frame_kov : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shkov RNG fra 128.
  Proof. intros fra fv spc j nn w120 (_ & Efra & _). subst fra. exact SKFk. Qed.


  (* The 16 shadow bytes of the frame, at the addresses the run forms: fra / 8 + ASAN_K + i. *)
  Lemma rngF_frame_blk : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> shblk RNG fra 15.
  Proof.
    intros fra fv spc j nn w120 HK.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & _).
    pose proof (rngF_frame_cov fra fv spc j nn w120 HK) as HC.
    intros i Hi. pose proof (sh_add8 fra i FR8) as Hs. unfold shadow_addr in Hs.
    replace (fra / 8 + ASAN_K + i) with ((fra + 8 * i) / 8 + ASAN_K) by lia.
    apply HC. lia.
  Qed.

  Definition BI (W : list ivl) (mc : word -> option byte) : Prop :=
    munch W m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 96) SAVES.

  (* The continuation at 0x83f28: the body. The last premise is the side frame's flag-pointer word at fr + 120
     (written by __asan_stack_malloc_1, read back by the release at the exit); the body never writes there. *)
  Definition KB (Q : machine_state -> Prop) : Prop :=
    forall (fr fv spc j nn : Z) (w120 : word) (mc : word -> option byte)
           (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31 : word),
      FK fr fv spc j nn w120 -> BI (Wf fr j nn) mc -> addressable mc (fr + 32) 36 ->
      (fv <> 0 -> bytes_at rsegs mc (fr + 120) (le8 w120)) ->
      evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                         x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                         (Z_to_bv 64 n) (Z_to_bv 64 (fr / 8 + ASAN_K)) (Z_to_bv 64 fr) (wa ASAN_K)
                         (Z_to_bv 64 (fr + 32)) s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x83f28) fc None mc (seg_rom rsegs)).

  Ltac wst a nn tac :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; tac | eassumption | lia | lia ])
    end.

  Ltac wstb a nn base fact :=
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
        let HS := fresh "HS" in
        assert (HS : store_ok rsegs mm (wa a) nn = true)
          by (eapply wv_store_ok;
                [ let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi;
                  match goal with |- wview _ _ (wa ?X) <> None => replace X with (base + (X - base)) by lia end;
                  apply fact; lia
                | eassumption | lia | lia ])
    end.

  (* A tracked poison store of one shadow byte at base + off (= base + Z.of_nat nn): the stored byte joins the
     frame-shadow cells so that the box's addressability can be read back. *)
  Ltac sstep base off nn fact :=
    wstb (base + off) 1%nat base fact; step;
    replace (base + off) with (base + Z.of_nat nn) by lia;
    rewrite rc_le1_lit; mem_after_store.

  (* 0x83ea8 .. 0x83f28: the stack slot, the 3 frame words and the 16 shadow bytes of the frame. *)
  Lemma fwords : forall fra fv spc j nn w120 mc
    (rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 : word) Q,
    FK fra fv spc j nn w120 -> BI (Wf fra j nn) mc ->
    (fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120)) -> KB Q ->
    evtF rsegs RNG Q (MS (mkR rr (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
                       x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 (Z_to_bv 64 o) (Z_to_bv 64 f)
                       (Z_to_bv 64 n) x23 (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
                    F (Z_to_bv 64 0x83ea8) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 mc rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x23 x26 x28 x29 x30 x31 Q
      HK HB H120 K.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    pose proof HB as HB'. destruct HB' as (MU & WM & RM & MI & SV).
    assert (HHMl : 17594333495296 <= S - 8800) by (pose proof HHM as HH0; unfold HIGHMEM_BEG in HH0; exact HH0).
    unfold Wf, shadow_addr in MU.
    (* the writes of this block: the stack slot, the 3 frame words and the 16 shadow bytes; fra + 120 is apart *)
    pose proof (munch_refl [(A + 24, A + 32); (fra, fra + 24);
                            (fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16)] mc) as MUw.
    wst (A + 24) 8%nat ltac:(apply STW0; lia). step. store_done.
    steps_to 0x83ed0.
    wstb fra 8%nat fra FW. step. store_done.
    wstb (fra + 8) 8%nat fra FW. step. store_done.
    wstb (fra + 16) 8%nat fra FW. step. store_done.
    step. step.
    rewrite (unsigned_lit fra) by lia. rewrite rc_shr3.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
      pose proof (shadow_rw_on_mono_mem P m mcur SR0 WM RM) as SRmc;
      pose proof (shadow16_stk_on P mcur fra SRmc (fk_sh_P fra fv spc j nn w120 HK) ltac:(lia) FRA ltac:(lia)
                    ltac:(lia)) as STsh
    end.
    pose proof (stk_carve rsegs m1 (fra / 8 + ASAN_K) (fra / 8 + ASAN_K + 16) 16%nat STsh ltac:(lia))
      as [STsh' [junkS SHC]].
    replace (fra / 8 + ASAN_K + 16 - Z.of_nat 16) with (fra / 8 + ASAN_K) in SHC by lia.
    sstep (fra / 8 + ASAN_K) 0 0%nat SW.
    sstep (fra / 8 + ASAN_K) 1 1%nat SW.
    sstep (fra / 8 + ASAN_K) 2 2%nat SW.
    sstep (fra / 8 + ASAN_K) 3 3%nat SW.
    step.
    sstep (fra / 8 + ASAN_K) 12 12%nat SW.
    sstep (fra / 8 + ASAN_K) 13 13%nat SW.
    sstep (fra / 8 + ASAN_K) 14 14%nat SW.
    sstep (fra / 8 + ASAN_K) 15 15%nat SW.
    sstep (fra / 8 + ASAN_K) 8 8%nat SW.
    sstep (fra / 8 + ASAN_K) 9 9%nat SW.
    sstep (fra / 8 + ASAN_K) 10 10%nat SW.
    sstep (fra / 8 + ASAN_K) 11 11%nat SW.
    sstep (fra / 8 + ASAN_K) 4 4%nat SW.
    sstep (fra / 8 + ASAN_K) 5 5%nat SW.
    sstep (fra / 8 + ASAN_K) 6 6%nat SW.
    sstep (fra / 8 + ASAN_K) 7 7%nat SW.
    destruct SHC as [[_ HB16] _]. cbn [cells_bytes cbytes app] in HB16.
    eapply K.
    - exact HK.
    - unfold BI, Wf, shadow_addr. refine (conj MU (conj WM (conj RM (conj MI SV)))).
    - apply frame_shadow_addr.
      + lia.
      + exact FR8.
      + unfold APPMEM_END in *; lia.
      + intros i Hi. replace (fra + 32 + i) with (fra + (32 + i)) by lia. apply FAP; lia.
      + intros g Hg. destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 0). split; [|reflexivity].
        assert (Hc : g = 4 \/ g = 5 \/ g = 6 \/ g = 7) by lia.
        destruct Hc as [H|[H|[H|H]]]; rewrite H;
          [ replace (fra / 8 + ASAN_K + 4) with (fra / 8 + ASAN_K + Z.of_nat 4) by lia;
            rewrite (Hr 4%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 5) with (fra / 8 + ASAN_K + Z.of_nat 5) by lia;
            rewrite (Hr 5%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 6) with (fra / 8 + ASAN_K + Z.of_nat 6) by lia;
            rewrite (Hr 6%nat ltac:(cbn [length]; lia))
          | replace (fra / 8 + ASAN_K + 7) with (fra / 8 + ASAN_K + Z.of_nat 7) by lia;
            rewrite (Hr 7%nat ltac:(cbn [length]; lia)) ]; reflexivity.
      + destruct HB16 as (_ & _ & Hr). exists (Z_to_bv 8 4). split; [|reflexivity].
        replace (fra / 8 + ASAN_K + 8) with (fra / 8 + ASAN_K + Z.of_nat 8) by lia.
        rewrite (Hr 8%nat ltac:(cbn [length]; lia)). reflexivity.
    - (* fra + 120 is apart from this block's writes, so the flag-pointer word is still there *)
      intros Hfv. eapply (bytes_at_transport rsegs _ mc _ (fra + 120) (le8 w120) (H120 Hfv) MUw).
      cbn [disjoint_from]. rewrite length_le8. lia.
  Qed.

  (* The cells the bcmp wrapper reads. *)
  Definition aCL (mc : word -> option byte) : Prop :=
    bytes_at rsegs mc REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs mc REAL_MEMCMP (le8 (wa MEMCMP)) /\
    bytes_at rsegs mc GOT_CF (le8 (wa CF)) /\ bytes_at rsegs mc (CF + 254) [Z_to_bv 8 1] /\
    bytes_at rsegs mc (CF + 255) [Z_to_bv 8 1].

  (* RE-BASED.  The writes from m to the return: the window (the callees' frames, the stack slot at A + 24, the saved
     registers' slots), the frame, its 16 shadow bytes, the flag byte, and the record at o (when o <> 0). *)
  Definition Wq : list ivl :=
    [(S - 8800, S); (Fr, Fr + 128); (shadow_addr Fr, shadow_addr Fr + 16); (FL, FL + 1)] ++
    (if o =? 0 then [] else [(o, o + 36)]).

  (* RE-BASED.  The end condition at the return (in place of reac_ctrl_parseF.v's Qp, whose runtime conjuncts at m'
     only FP0 at the entry memory gives): the caller's registers back (as Qp), a0 = the return code of ctrlparse,
     the writes inside Wq from m, the window still present and addressable (its shadow untouched), the record
     (o <> 0) = the 36 bytes of ctrlparse, and the frame's flag byte FL = 0 (the release at 0x84294). *)
  Definition Qb : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch Wq m m' /\ wmono rsegs m m' /\ rd_mono m m' /\ mem_inv rsegs m' /\ stk rsegs m' (S - 8800) S /\
      (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
      addressable m' (S - 8800) 8800 /\ mrd rsegs m' (wa FL) = Some (Z_to_bv 8 0).

  (* The copied statements (EPI, b_done .. b_none, L_body_k) name the end condition Qp: here it is Qb. *)
  Local Notation Qp := Qb (only parsing).

  (* RE-BASED (post Qb; premises: the conjuncts of Qb in place of reac_ctrl_parseF.v's aJ).  0x842dc .. 0x84314:
     sp = s0 - 128, the saved registers restored from [S - 96, S), ret.  The stepping is reac_ctrl_parseF.v's. *)
  Lemma L_restore : forall (m' : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (spc : Z),
    rw_cells rsegs m' (S - 96) SAVES ->
    munch Wq m m' -> wmono rsegs m m' -> rd_mono m m' -> mem_inv rsegs m' -> stk rsegs m' (S - 8800) S ->
    (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) ->
    addressable m' (S - 8800) 8800 -> mrd rsegs m' (wa FL) = Some (Z_to_bv 8 0) ->
    evtF rsegs RNG Qb
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x842dc) fc None m' (seg_rom rsegs)).
  Proof.
    intros m' x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 spc
      FR MU WM RM MI ST HBox AW HFL.
    unfold SAVES in FR.
    replace (S - 96) with (S + -96) in FR by lia.
    do 14 step. step.
    apply evtF_done. unfold Qb.
    do 14 eexists. exists m'. split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [exact RM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HBox|]. split; [exact AW | exact HFL].
  Qed.


  (* ================= the body (0x83f28 .. 0x842dc) ================= *)

  (* The record buffer the body fills: the caller's o when given, else the frame's 32-byte scratch at fra + 32. *)
  Definition REC (fra : Z) : Z := if o =? 0 then fra + 32 else o.

  (* The body's write footprint: the frame footprint Wf plus the record at o (when o <> 0). *)
  Definition Wb (fra j nn : Z) : list ivl :=
    Wf fra j nn ++ (if o =? 0 then [] else [(o, o + 36)]).

  (* The invariant carried through the body: the writes stay inside Wb, the window's saved registers are intact, and
     the record buffer is addressable (so the instrumented checks before each record access pass). *)
  Definition aJb (fra j nn : Z) (mc : word -> option byte) : Prop :=
    munch (Wb fra j nn) m mc /\ wmono rsegs m mc /\ rd_mono m mc /\ mem_inv rsegs mc /\
    rw_cells rsegs mc (S - 96) SAVES /\ addressable mc (REC fra) 36.

  (* The runtime's shadow region P survives the body's writes (route (C): shadow_rw_on P, from SR0). *)
  Lemma jb_sw : forall fra j nn mc, aJb fra j nn mc -> lib.B.ShadowRwOn.shadow_rw_on P mc.
  Proof. intros fra j nn mc (MU & WM & RM & _). exact (shadow_rw_on_mono_mem P m mc SR0 WM RM). Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: from fpx's data-range disjointness D_apart_frame, a side-stack fact): f is apart
     from the frame, FkF. *)
  Lemma f_apart_frame : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> 50 <= n ->
    f + 50 <= fra \/ fra + 128 <= f.
  Proof. intros fra fv spc j nn w120 (_ & Efr & _) HN. subst fra. exact (FkF HN). Qed.

  (* RE-PROVED (reac_ctrl_parseF.v used FP0 for the side stack's bytes being application memory): the shadow byte of
     an application byte apart from the frame is apart from every range the body writes; FL is an application byte
     (FlApp). *)
  Lemma jb_sh_out : forall fra fv spc j nn w120 y, FK fra fv spc j nn w120 ->
    app_mem y -> (y + 1 <= fra \/ fra + 128 <= y) -> outside (Wb fra j nn) (shadow_addr y).
  Proof.
    intros fra fv spc j nn w120 y HK Hap Hfr.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof (rt_app_shadow y Hap) as Hs. set (z := shadow_addr y) in *.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & FAP & _ & _ & _ & _).
    assert (Hzlt : z < 0x10007fff8000)
      by (clear -Hs; unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Hs; lia).
    assert (H4 : ~ (fra <= z < fra + 128)).
    { intros [c1 c2]. apply (acl_app_not_shadow z); [|exact Hs].
      replace z with (fra + (z - fra)) by lia. apply FAP. lia. }
    assert (H5 : ~ (shadow_addr fra <= z < shadow_addr fra + 16)).
    { pose proof (sh_add8 fra 16 FR8) as E. replace (fra + 8 * 16) with (fra + 128) in E by lia.
      pose proof (acl_win_sh y fra (fra + 128) FR8 ltac:(clear -Hfr; lia)) as HW. rewrite E in HW. exact HW. }
    assert (Hnn : nn = 1) by (destruct HK as (_ & _ & _ & _ & _ & En); exact En).
    unfold Wb. apply fl_out_app; [unfold Wf; cbn [outside] | ].
    - split; [clear -Hzlt HHM'; lia|].
      split; [lia|].
      split; [intros [c1 c2]; apply (acl_app_not_shadow z); [replace z with FL by lia; exact FlApp | exact Hs]|].
      split; [exact H4|].
      split; [exact H5 | exact I].
    - destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside].
      + exact I.
      + split; [|exact I]. destruct (AO0 Eo) as (AOa & _ & _). intros [c1 c2].
        apply (acl_app_not_shadow z); [replace z with (o + (z - o)) by lia; apply (acl_app_in m o 36); [exact AOa | clear -c1 c2; lia] | exact Hs].
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: the side frame's place below the window from FP0): the window stays addressable
     at the exit's memory, the frame being below the window (FkHi). *)
  Lemma epi_win_side : forall fra fv spc j nn w120 m',
    FK fra fv spc j nn w120 -> fv <> 0 -> munch (Wb fra j nn) m m' -> addressable m' (S - 8800) 8800.
  Proof.
    intros fra fv spc j nn w120 m' HK Hfv MU.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Efra128 : fra + 128 <= S - 8800) by (destruct HK as (_ & Efr & _); subst fra; exact FkHi).
    apply (acl_addr_munch (Wb fra j nn) m m' (S - 8800) 8800 AW0 MU). intros i Hi.
    assert (Hap : app_mem (S - 8800 + i)) by (unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END; lia).
    apply (jb_sh_out fra fv spc j nn w120 (S - 8800 + i) HK Hap). right. clear -Efra128 Hi. lia.
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: D_apart_frame, from FP0): o is apart from the frame, FkO. *)
  Lemma o_apart_frame : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> o <> 0 ->
    o + 36 <= fra \/ fra + 128 <= o.
  Proof. intros fra fv spc j nn w120 (_ & Efr & _) Ho. subst fra. exact (FkO Ho). Qed.

  (* RE-BASED.  The exit's own writes: the frame's cookie, its 16 shadow bytes, and the flag byte FL. *)
  Definition Wtight (fra j nn : Z) : list ivl :=
    [(fra, fra + 128); (fra / 8 + ASAN_K, fra / 8 + ASAN_K + 16); (FL, FL + nn)].

  (* RE-PROVED (reac_ctrl_parseF.v placed flag j inside the side stack with FP0): the exit's writes are apart from
     the saved registers and from o (the flag byte by FlHi and FlO). *)
  Lemma tight_out : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 ->
    (S - 96 <= x < S \/ (o <> 0 /\ o <= x < o + 36)) -> outside (Wtight fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Hx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & FRA & _ & SH2a & SH2b).
    assert (Efra128 : fra + 128 <= APPMEM_END) by (clear -FRhi HAhi HAE'; unfold APPMEM_END; lia).
    assert (Efra0 : 0 <= fra) by (clear -FRlo; lia).
    assert (Enn : nn = 1) by (destruct HK as (_ & _ & _ & _ & _ & En); exact En).
    unfold Wtight. cbn [outside].
    destruct Hx as [Hs | [Ho Hr]].
    - split; [clear -Hs FRhi HAhi RS; lia|].
      split; [clear -Hs SH2b HHM' RS; lia|].
      split; [|exact I]. clear -Hs FlHi Enn RS; lia.
    - pose proof (AO0 Ho) as (AOa & _ & _).
      pose proof (acl_app_in m o 36 (x - o) AOa ltac:(clear -Hr; lia)) as Hoapp.
      replace (o + (x - o)) with x in Hoapp by lia.
      pose proof (o_apart_frame fra fv spc j nn w120 HK Ho) as Hofr.
      split; [clear -Hr Hofr; lia|].
      split.
      + intro Hq. apply (acl_app_not_shadow x Hoapp).
        replace x with (fra / 8 + ASAN_K + (x - (fra / 8 + ASAN_K))) by lia.
        apply frame_shadow_in; [exact Efra0 | exact FRA | exact SH2a | exact SH2b | clear -Hq; lia].
      + split; [|exact I]. pose proof (FlO Ho) as HL. unfold rcpB_dj in HL. clear -HL Hr Enn. lia.
  Qed.

  (* RE-PROVED (target: Qb's write set Wq, in place of reac_ctrl_parseF.v's post footprint with fp_wx [1] FS X). *)
  Lemma wb_sub_fp : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> sub_fp (Wb fra j nn) Wq.
  Proof.
    intros fra fv spc j nn w120 (Ej & Efr & Ef & Esp & Ew & En) x Hout. subst fra nn.
    unfold Wq in Hout. apply acl_out_app_inv in Hout. destruct Hout as [Hq Ho].
    cbn [outside] in Hq. destruct Hq as (Hw & Hfr & Hsh & Hfl & _).
    unfold Wb. apply fl_out_app; [unfold Wf; cbn [outside] | exact Ho].
    split; [exact Hw|]. split; [lia|]. split; [exact Hfl|]. split; [exact Hfr|]. split; [exact Hsh | exact I].
  Qed.


  (* The exit's tight footprint is inside the body+exit footprint (so the composed munch stays over Wb). *)
  Lemma wtight_sub_wb : forall fra j nn, sub_fp (Wtight fra j nn) (Wb fra j nn).
  Proof.
    intros fra j nn x Hout. unfold Wb in Hout. apply acl_out_app_inv in Hout. destruct Hout as [HoutWf _].
    unfold Wf in HoutWf. cbn [outside] in HoutWf.
    destruct HoutWf as (_ & _ & Hflag & Hframe & Hshadow & _).
    unfold Wtight, shadow_addr in *. cbn [outside].
    split; [exact Hframe | split; [exact Hshadow | split; [exact Hflag | exact I]]].
  Qed.

  (* RE-BASED (the side arm of reac_ctrl_parseF.v's L_epi only, the real-stack arm being unreachable; the flag byte's
     writability from FlSt in place of the side stack's stk; the end through the re-based L_restore).  0x84224 ..
     0x842dc: the 5 unused poison bytes and the frame cookie, then the 16 shadow bytes set to 0xf5 (released) and the
     frame's flag byte cleared (sb zero at 0x84294: the release); the record and the saved registers survive. *)
  Lemma L_epi : forall fra fv spc j nn w120 (mc : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> aJb fra j nn mc ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    evtF rsegs RNG Qb
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84224) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31
      HK HJb Hrec Hw120.
    pose proof HJb as HJbc. destruct HJbc as (_ & WM & RM & MI & SV & AREC).
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHMx. pose proof HAE as HAEx. unfold HIGHMEM_BEG, APPMEM_END in HHMx, HAEx.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAPP & FRA & SWsh & SH2a & SH2b).
    pose proof (rngF_frame fra fv spc j nn w120 HK) as RGFRM.
    pose proof (rngF_frame_blk fra fv spc j nn w120 HK) as SBFRM.
    assert (Efra0 : 0 <= fra) by (clear -FRlo; lia).
    pose proof (jb_sw fra j nn mc HJb) as SRmc.
    pose proof (munch_refl (Wtight fra j nn) mc) as MUc.
    pose proof (wmono_refl rsegs mc) as WMc.
    pose proof (rd_mono_refl mc) as RMc.
    unfold Wtight, shadow_addr in MUc.
    pose proof HK as HK0.
    destruct HK0 as (Ej & Efra & Efvs & Espc & Ew120 & Enn).
    subst nn.
    assert (Hfrapos : 0 < fra) by (clear -FRlo; lia).
    assert (Hfvne : fv <> 0) by (rewrite Efvs; clear -Hfrapos; lia).
    pose proof (Hw120 Hfvne) as HW120. rewrite Ew120 in HW120. apply bytes_ro8 in HW120.
    pose proof FlSt as (FLb & _).
    rewrite Efvs.
    step.
    wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    step. step.
    wstb fra 8%nat fra FW. step. store_done.
    step. if_cases Eb; cbv iota.
    { exfalso. rewrite (rc_neq0_64 fra) in Eb by (clear -Hfrapos FRhi HAhi RS; lia). discriminate. }
    step.
    wstb (fra / 8 + ASAN_K + 4) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 5) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 6) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 7) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 0) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 1) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 2) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 3) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 12) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 13) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 14) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 15) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 8) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 9) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 10) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    wstb (fra / 8 + ASAN_K + 11) 1%nat (fra / 8 + ASAN_K) SWsh. step. store_done.
    step. (* ld a1, 120(s2): the frame's flag-byte address w120 = FL *)
    (* sb zero, 0(a1): the flag byte FL, carved from its stk (FlSt) as a 1-byte cell so its new value 0 is kept *)
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mcur _) =>
      pose proof (stk_mono m mcur FL (FL + 1) FlSt WM RM) as STF end.
    destruct (stk_carve rsegs _ FL (FL + 1) 1%nat STF ltac:(lia)) as [STF2 [junkF FLC]].
    clear STF STF2.
    replace (FL + 1 - Z.of_nat 1) with FL in FLC by lia.
    wst FL 1%nat ltac:(apply (stk_wv m FL (FL + 1)); [exact FlSt | clear -Hi; lia]).
    step.
    change (Z_to_bv 64 FL) with (wa FL).
    replace (wa FL) with (wa (FL + Z.of_nat 0)) by (f_equal; lia).
    rewrite rc_le1_lit. mem_after_store.
    step.
    lazymatch goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mfin _) =>
      assert (Hclr : mrd rsegs mfin (wa FL) = Some (Z_to_bv 8 0)) end.
    { destruct FLC as [[_ HBF] _]. cbn [cells_bytes cbytes app] in HBF.
      destruct HBF as (_ & _ & Hr). pose proof (Hr 0%nat ltac:(cbn [length]; lia)) as H0.
      cbn [Z.of_nat nth_error] in H0. rewrite Z.add_0_r in H0. exact H0. }
    destruct HJb as (MUbody & _).
    pose proof (munch_trans _ m mc _ MUbody (munch_weaken _ _ mc _ (wtight_sub_wb fra j 1) MUc)) as MUfin.
    eapply L_restore.
    + exact SV.
    + eapply munch_weaken; [exact (wb_sub_fp fra fv spc j 1 w120 HK) | exact MUfin].
    + exact WM.
    + exact RM.
    + exact MI.
    + exact (stk_mono m _ _ _ ST0 WM RM).
    + intros Ho. apply (acl_rw (Wtight fra j 1) mc _ o [CB 36 (snd (ctrlparse n fr))] (Hrec Ho) MUc WMc).
      intros y Hy. apply (tight_out fra fv spc j 1 w120 y HK). right. split; [exact Ho|].
      cbn [cells_size csize Nat.add] in Hy. lia.
    + exact (epi_win_side fra fv spc j 1 w120 _ HK Hfvne MUfin).
    + exact Hclr.
  Qed.


  (* ================= the body walk (0x83f28 .. 0x84224) ================= *)

  (* The callees of the body.  Route (C): __asan_memset, __asan_memcpy and the bcmp wrapper in their _on forms
     (premise: the shadow each one reads, shadow_rw_on R; post: every region the caller holds stays held). *)
  Hypothesis MSET : asan_memset_contract_F_on.
  Hypothesis MCPY : asan_memcpy_contract_F_on.
  Hypothesis BWRP : bcmp_wrap_contract_F_on.
  Hypothesis KOL : kind_of_link1_contract_F.

  (* The record buffer the body fills, named R (as o' in the plain proof): the caller's o when given, else the
     frame's 32-byte scratch at fra + 32. *)
  Definition RF (fra R : Z) : Prop := (o = 0 /\ R = fra + 32) \/ (o <> 0 /\ R = o).

  Lemma rf_rec : forall fra R, RF fra R -> REC fra = R.
  Proof.
    intros fra R [(Ho & ER)|(Ho & ER)]; unfold REC.
    - rewrite (proj2 (Z.eqb_eq o 0) Ho). lia.
    - rewrite (proj2 (Z.eqb_neq o 0) Ho). lia.
  Qed.

  (* NEW (route (C)): the aligned shadow-word span of a range inside the record R is in P: the frame's scratch
     (o = 0, SRFr) or the caller's o (o <> 0, SRo). *)
  Lemma rec_sh_P : forall fra fv spc j nn w120 R p k a, FK fra fv spc j nn w120 -> RF fra R ->
    R <= p -> p + k <= R + 36 -> lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Proof.
    intros fra fv spc j nn w120 R p k a HK HR H1 H2 Ha.
    destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - destruct HK as (_ & Efr & _). subst fra. apply (SRFr p k a); [lia | lia | exact Ha].
    - apply (SRo Ho p k a); [lia | lia | exact Ha].
  Qed.

  (* What the body itself writes: the record and the window (the callees' frames). *)
  Definition Wr (R : Z) : list ivl := [(R, R + 36); (S - 8800, S)].

  (* The memory state carried from 0x83f28 (mc0) to the current memory mc. *)
  Definition BJ (R : Z) (mc0 mc : word -> option byte) : Prop :=
    munch (Wr R) mc0 mc /\ wmono rsegs mc0 mc /\ rd_mono mc0 mc /\ mem_inv rsegs mc /\
    stk rsegs mc (S - 8800) S /\ rw_cells rsegs mc (S - 96) SAVES.

  Lemma bj_refl : forall R mc0, mem_inv rsegs mc0 -> stk rsegs mc0 (S - 8800) S ->
    rw_cells rsegs mc0 (S - 96) SAVES -> BJ R mc0 mc0.
  Proof.
    intros R mc0 MI ST SV. split; [apply munch_refl|]. split; [apply wmono_refl|].
    split; [apply rd_mono_refl|]. split; [exact MI|]. split; [exact ST | exact SV].
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: from the side stack's size in FP0): the frame is below the window, FkHi. *)
  Lemma side_frame_lo : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> fv <> 0 ->
    fra + 128 <= S - 8800.
  Proof. intros fra fv spc j nn w120 (_ & Efr & _) _. subst fra. exact FkHi. Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: the frame above the image from FS >= ASAN_GT in FP0; its real-stack case): the
     record's place, the frame's scratch case from FkImg / FkHi. *)
  Lemma rf_facts : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R ->
    0 < R /\ R mod 4 = 0 /\ R + 36 <= 2^64 /\ (forall i, 0 <= i <= 36 -> app_mem (R + i)) /\
    (R + 36 <= RT_LO \/ RT_HI <= R) /\ (R + 36 <= S - 96 \/ S <= R) /\
    (forall KK, 0 <= KK <= 4560 -> R + 36 <= spc - KK \/ spc <= R) /\
    (50 <= n -> R + 36 <= f \/ f + 50 <= R) /\
    (fv <> 0 -> R + 36 <= fra + 120 \/ fra + 128 <= R).
  Proof.
    intros fra fv spc j nn w120 R HK HR.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & Fsp & FW & FAP & FRA & SW & SH1 & SH2).
    assert (Hsp : spc = A /\ fra + 128 <= S - 8800).
    { pose proof HK as HK2. destruct HK2 as (_ & Efr & _ & Esp & _). split; [exact Esp|]. subst fra. exact FkHi. }
    assert (HI : fra + 128 <= 0x10000 \/ 0x5fe000 <= fra).
    { pose proof HK as HK2. destruct HK2 as (_ & Efr & _). subst fra. pose proof FkImg as HI.
      unfold rcpB_dj, ImgBounds.IMG_LO, ImgBounds.IMG_HI in HI. lia. }
    destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - (* the frame's scratch *)
      split; [clear -FRlo; lia|].
      split; [clear -FR8; Z.div_mod_to_equations; lia|].
      split; [clear -FRhi HAhi RS HAE'; lia|].
      split; [intros i Hi; replace (fra + 32 + i) with (fra + (32 + i)) by lia; apply FAP; lia|].
      split; [unfold RT_LO, RT_HI; clear -HI; lia|].
      split; [left; clear -FRhi HAhi RS; lia|].
      split; [intros KK HKK; destruct Hsp as [E1 E2]; clear -E1 E2 HAlo HAhi RS HKK; lia|].
      split.
      + intros HN. destruct (f_apart_frame fra fv spc j nn w120 HK HN) as [L|Rr];
          [right; clear -L; lia | left; clear -Rr; lia].
      + intros _. left. lia.
    - (* the caller's record *)
      destruct (HOK Ho) as (Ho4 & Ho36 & Horw & HoS & Hof).
      destruct (AO0 Ho) as (AOa & AOe & AOc). unfold GOT_CF, CF in AOc.
      split; [clear -Ho Ro; lia|]. split; [exact Ho4|]. split; [exact Ho36|].
      split.
      { intros i Hi. destruct (Z.eq_dec i 36) as [E36|E36]; [subst i; exact AOe|].
        exact (acl_app_in m o 36 i AOa ltac:(lia)). }
      split; [unfold RT_LO, RT_HI; clear -AOc; lia|].
      split; [clear -HoS RS; lia|].
      split; [intros KK HKK; destruct Hsp as [E1 E2]; clear -HoS E1 E2 HAlo HAhi RS HKK; lia|].
      split; [intros HN; destruct (Hof HN) as [L|Rr]; [left; exact L | right; exact Rr]|].
      intros _. destruct (o_apart_frame fra fv spc j nn w120 HK Ho) as [Hx|Hx];
        [left; clear -Hx; lia | right; clear -Hx; lia].
  Qed.


  (* Every byte the body writes is application memory, so no shadow byte is inside its footprint. *)

  (* ---- The footprint of the record R: the caller's buffer at o, or the frame's 32-byte scratch at fra + 32. ---- *)
  Lemma rngF_rec : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R -> rng RNG R 36.
  Proof.
    intros fra fv spc j nn w120 R HK HR. destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - eapply rng_sub; [exact (rngF_frame fra fv spc j nn w120 HK) | lia | lia].
    - exact (ROUT Ho).
  Qed.

  Lemma rngF_rec_cov : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R -> shcov RNG R 36.
  Proof.
    intros fra fv spc j nn w120 R HK HR. destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - eapply shcov_sub; [exact (rngF_frame_cov fra fv spc j nn w120 HK) | lia | lia].
    - exact (SCO Ho).
  Qed.

  Lemma rngF_rec_kov : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R -> shkov RNG R 36.
  Proof.
    intros fra fv spc j nn w120 R HK HR. destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - eapply shkov_sub; [exact (rngF_frame_kov fra fv spc j nn w120 HK) | lia | lia].
    - exact (SKO Ho).
  Qed.
  Lemma wr_app : forall fra fv spc j nn w120 R x, FK fra fv spc j nn w120 -> RF fra R ->
    ~ outside (Wr R) x -> app_mem x.
  Proof.
    intros fra fv spc j nn w120 R x HK HR Hin.
    pose proof HHM as HHM'. pose proof HAE as HAE'.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (_ & _ & _ & HRap & _).
    assert (D : (R <= x < R + 36) \/ (S - 8800 <= x < S)).
    { destruct (Z_le_dec R x) as [A1|A1]; destruct (Z_lt_dec x (R + 36)) as [A2|A2];
        destruct (Z_le_dec (S - 8800) x) as [A3|A3]; destruct (Z_lt_dec x S) as [A4|A4];
        first [ left; lia | right; lia
              | exfalso; apply Hin; unfold Wr; cbn [outside]; split; [lia | split; [lia | exact I]] ]. }
    destruct D as [D|D].
    - replace x with (R + (x - R)) by lia. apply HRap. lia.
    - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. right. lia.
  Qed.

  (* The body writes no shadow byte, so every addressable range stays addressable. *)
  Lemma bj_addr : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) p q,
    FK fra fv spc j nn w120 -> RF fra R -> addressable mc0 p q -> munch (Wr R) mc0 mc ->
    addressable mc p q.
  Proof.
    intros fra fv spc j nn w120 R mc0 mc p q HK HR AD MU.
    apply (acl_addr_munch (Wr R) mc0 mc p q AD MU). intros i Hi.
    destruct (rc_outside_dec (Wr R) (shadow_addr (p + i))) as [Hou|Hou]; [exact Hou|].
    exfalso. apply (acl_app_not_shadow (shadow_addr (p + i))).
    - exact (wr_app fra fv spc j nn w120 R _ HK HR Hou).
    - apply rt_app_shadow. exact (acl_app_in mc0 p q i AD Hi).
  Qed.

  Lemma Wr_sub : forall fra fv spc j nn w120 R, FK fra fv spc j nn w120 -> RF fra R ->
    sub_fp (Wr R) (Wb fra j nn).
  Proof.
    intros fra fv spc j nn w120 R HK HR x Hout.
    unfold Wb in Hout. apply acl_out_app_inv in Hout. destruct Hout as [HoutF HoutO].
    unfold Wf in HoutF. cbn [outside] in HoutF. destruct HoutF as (HW & _ & _ & HFr & _).
    unfold Wr. cbn [outside]. split; [|split; [exact HW | exact I]].
    destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - clear -HFr. lia.
    - rewrite (proj2 (Z.eqb_neq o 0) Ho) in HoutO. cbn [outside] in HoutO. exact (proj1 HoutO).
  Qed.

  (* The body's invariant, read back as the exit lemma's aJb. *)
  Lemma bj_aJb : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    BJ R mc0 mc -> aJb fra j nn mc.
  Proof.
    intros fra fv spc j nn w120 R mc0 mc HK HR (MU0 & WM0 & RM0 & _ & _) AD0 (MU & WM & RM & MI & ST & SV).
    unfold aJb. rewrite (rf_rec fra R HR).
    split.
    { apply (munch_trans _ m mc0 mc).
      - eapply munch_weaken; [|exact MU0]. unfold Wb. intros x Hx.
        exact (proj1 (acl_out_app_inv _ _ _ Hx)).
      - eapply munch_weaken; [|exact MU]. exact (Wr_sub fra fv spc j nn w120 R HK HR). }
    split; [exact (wmono_trans rsegs _ _ _ WM0 WM)|].
    split; [exact (rd_mono_trans _ _ _ RM0 RM)|].
    split; [exact MI|]. split; [exact SV|].
    exact (bj_addr fra fv spc j nn w120 R mc0 mc R 36 HK HR AD0 MU).
  Qed.

  (* The side frame's flag-pointer word survives the body. *)
  Lemma w120_bj : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> munch (Wr R) mc0 mc ->
    fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc HK HR H0 MU Hfv.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (_ & _ & _ & _ & _ & _ & _ & _ & Hfr).
    pose proof (side_frame_lo fra fv spc j nn w120 HK Hfv) as Hlo.
    eapply (bytes_at_transport rsegs (Wr R) mc0 mc _ _ (H0 Hfv) MU).
    unfold Wr. cbn [disjoint_from]. rewrite length_le8.
    destruct (Hfr Hfv) as [Hx|Hx]; repeat split; try exact I; clear -Hx Hlo; lia.
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: the hint word and flag array apart from f by fpx's D-disjointness, a side-stack
     fact): the input buffer is apart from every range the body's footprint names; FL by FlF. *)
  Lemma f_dj_Wb : forall fra fv spc j nn w120, FK fra fv spc j nn w120 -> 50 <= n ->
    forall a len, f <= a -> 0 <= len -> a + len <= f + 50 -> disjoint_from (Wb fra j nn) a len.
  Proof.
    intros fra fv spc j nn w120 HK HN a len Ha Hlen Hae.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    destruct (HF HN) as (Hf0 & Hf50 & HfW).
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & SH1 & SH2).
    assert (Hnn : nn = 1) by (destruct HK as (_ & _ & _ & _ & _ & En); exact En).
    pose proof (f_apart_frame fra fv spc j nn w120 HK HN) as Hfr.
    pose proof (FlF HN) as Hfl. unfold rcpB_dj in Hfl.
    assert (Hap : f + 50 <= 2147450880 \/ 17594333495296 <= f).
    { apply (app_range f 50 ltac:(lia)). intros i Hi. exact (acl_app_in m f 50 i (AF0 HN) Hi). }
    unfold Wb, Wf, shadow_addr. cbn [app disjoint_from].
    repeat split; try exact I.
    - clear -HfW Ha Hae Hlen; lia.
    - clear -Hfl Ha Hae Hlen; lia.
    - clear -Hfl Hnn Ha Hae Hlen; lia.
    - clear -Hfr Ha Hae Hlen; lia.
    - clear -Hap SH1 SH2 Ha Hae Hlen; lia.
    - destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [disjoint_from]; [exact I|].
      destruct (HOK Eo) as (_ & _ & _ & _ & Hof). destruct (Hof HN) as [Hx|Hx];
        split; try exact I; clear -Hx Ha Hae Hlen; lia.
  Qed.


  (* The munch the input-byte reads (rc_ro_now) need: from the entry memory m through the body. *)
  Lemma bj_mub : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> munch (Wr R) mc0 mc ->
    munch (Wb fra j nn) m mc.
  Proof.
    intros fra fv spc j nn w120 R mc0 mc HK HR (MU0 & _) MU.
    apply (munch_trans _ m mc0 mc).
    - eapply munch_weaken; [|exact MU0]. unfold Wb. intros x Hx. exact (proj1 (acl_out_app_inv _ _ _ Hx)).
    - eapply munch_weaken; [|exact MU]. exact (Wr_sub fra fv spc j nn w120 R HK HR).
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: the side stack above the image from FP0): the runtime's compare cells, between
     GOT_CF and CF + 256, are apart from the body's footprint (the frame and FL are not image bytes: FkImg, FlImg). *)
  Lemma low_out_Wb : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 ->
    GOT_CF <= x < CF + 256 -> outside (Wb fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Hx. unfold GOT_CF, CF in Hx.
    pose proof HHM as HHM'. unfold HIGHMEM_BEG in HHM'.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & SH1 & SH2).
    pose proof FkImg as HI. pose proof FlImg as HL. unfold rcpB_dj, ImgBounds.IMG_LO, ImgBounds.IMG_HI in HI, HL.
    destruct HK as (Ej & Efr & Ef & Esp & Ew & En).
    unfold Wb, Wf. apply fl_out_app; cbn [outside].
    - split; [clear -Hx HHM'; lia|].
      split; [lia|].
      split; [subst nn; clear -Hx HL; lia|].
      split; [subst fra; clear -Hx HI; lia|].
      split; [clear -Hx SH1; unfold shadow_addr; lia | exact I].
    - destruct (Z.eqb_spec o 0) as [Eo|Eo]; cbn [outside]; [exact I|].
      destruct (AO0 Eo) as (_ & _ & AOc). unfold GOT_CF, CF in AOc.
      split; [clear -Hx AOc; lia | exact I].
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: through aout_rt, which reads FP0 and fp_w [1] FS; moved after low_out_Wb, which
     it now uses): the runtime's cells survive the body's writes, [RT_LO, RT_HI) being inside [GOT_CF, CF + 256). *)
  Lemma jb_ac : forall fra fv spc j nn w120 mc, FK fra fv spc j nn w120 -> aJb fra j nn mc -> asan_cells mc.
  Proof.
    intros fra fv spc j nn w120 mc HK (MU & WM & RM & _).
    apply (fl_asan_cells (Wb fra j nn) m mc AC0 MU).
    intros y Hy. apply (low_out_Wb fra fv spc j nn w120 y HK).
    unfold RT_LO, RT_HI in Hy. unfold GOT_CF, CF. lia.
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v: o apart from the side stack's header and flag array by FP0): a byte of the
     caller's record is apart from everything the frame block writes; FL by FlO. *)
  Lemma o_out_Wf : forall fra fv spc j nn w120 x, FK fra fv spc j nn w120 -> o <> 0 ->
    o <= x < o + 36 -> outside (Wf fra j nn) x.
  Proof.
    intros fra fv spc j nn w120 x HK Ho Hx.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & SH1 & SH2).
    destruct (HOK Ho) as (Ho4 & Ho36 & Horw & HoS & Hof).
    destruct (AO0 Ho) as (AOa & AOe & AOc).
    assert (Hap : app_mem x)
      by (replace x with (o + (x - o)) by lia; exact (acl_app_in m o 36 (x - o) AOa ltac:(lia))).
    pose proof (FlO Ho) as HL. unfold rcpB_dj in HL.
    assert (Hnn : nn = 1) by (destruct HK as (_ & _ & _ & _ & _ & En); exact En).
    unfold Wf. cbn [outside].
    split; [clear -HoS Hx; lia|].
    split; [lia|].
    split; [clear -HL Hnn Hx; lia|].
    split; [pose proof (o_apart_frame fra fv spc j nn w120 HK Ho) as Hofr; clear -Hofr Hx; lia|].
    split; [|exact I].
    pose proof (sh_add8 fra 16 FR8) as Esh. replace (fra + 8 * 16) with (fra + 128) in Esh by lia.
    rewrite <- Esh.
    apply (acl_sh_out x fra (fra + 128) Hap);
      [clear -FRlo; lia | unfold APPMEM_END; clear -FRhi HAhi RS HAE'; lia].
  Qed.

  (* RE-PROVED (reac_ctrl_parseF.v carved the frame's scratch out of the side stack's stk in FP0): the record buffer
     is writable and readable at the body's entry memory; the scratch from the frame's stk FkSt. *)
  Lemma rec_rw : forall fra fv spc j nn w120 R (mc0 : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 ->
    exists junk', rw_cells rsegs mc0 R [CB 36 junk'].
  Proof.
    intros fra fv spc j nn w120 R mc0 HK HR HB.
    pose proof HB as (MU & WM & RM & MI & SV).
    destruct (fk_facts fra fv spc j nn w120 HK) as (FR8 & FRlo & FRhi & _ & _ & _ & _ & _ & SH1 & SH2).
    destruct HR as [(Ho & ER)|(Ho & ER)]; subst R.
    - assert (STf : stk rsegs m fra (fra + 128)) by (destruct HK as (_ & Efr & _); subst fra; exact FkSt).
      pose proof (stk_mono m mc0 fra (fra + 128) STf WM RM) as STf0.
      destruct (stk_split rsegs mc0 fra (fra + 68) (fra + 128) STf0 ltac:(lia)) as [STa _].
      destruct (stk_carve rsegs mc0 fra (fra + 68) 36 STa ltac:(lia)) as [_ [junk' HRW]].
      replace (fra + 68 - Z.of_nat 36) with (fra + 32) in HRW by lia.
      exists junk'. exact HRW.
    - destruct (HOK Ho) as (Ho4 & Ho36 & Horw & HoS & Hof).
      exists junk. apply (acl_rw (Wf fra j nn) m mc0 o [CB 36 junk] Horw MU WM).
      intros x Hx. cbn [cells_size csize Nat.add] in Hx.
      exact (o_out_Wf fra fv spc j nn w120 x HK Ho Hx).
  Qed.


  (* The cells the bcmp wrapper reads, at a body memory. *)
  Lemma jb_cl : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte),
    FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> munch (Wr R) mc0 mc -> aCL mc.
  Proof.
    intros fra fv spc j nn w120 R mc0 mc HK HR HB MU.
    pose proof (bj_mub fra fv spc j nn w120 R mc0 mc HK HR HB MU) as MUb.
    pose proof (fun x Hx => low_out_Wb fra fv spc j nn w120 x HK Hx) as LO.
    unfold aCL.
    split; [eapply fl_bytes; [exact HBCMP | exact MUb |]|].
    { intros x Hx. rewrite length_le8 in Hx. apply LO. unfold REAL_BCMP, GOT_CF, CF in *. lia. }
    split; [eapply fl_bytes; [exact HMEMCMP | exact MUb |]|].
    { intros x Hx. rewrite length_le8 in Hx. apply LO. unfold REAL_MEMCMP, GOT_CF, CF in *. lia. }
    split; [eapply fl_bytes; [exact HGCF | exact MUb |]|].
    { intros x Hx. rewrite length_le8 in Hx. apply LO. unfold GOT_CF, CF in *. lia. }
    split; [eapply fl_bytes; [exact HCF254 | exact MUb |]|].
    { intros x Hx. cbn [length] in Hx. apply LO. unfold GOT_CF, CF in *. lia. }
    eapply fl_bytes; [exact HCF255 | exact MUb |].
    intros x Hx. cbn [length] in Hx. apply LO. unfold GOT_CF, CF in *. lia.
  Qed.

  (* The shadow fact of a 1-byte access at p + jj. *)
  Lemma sh1 : forall (mq : word -> option byte) p q jj Y, addressable mq p q -> 0 <= jj -> jj + 1 <= q ->
    Y = p + jj ->
    exists kk : byte, ov_read_bytes rsegs mq (wa (Y / 8 + ASAN_K)) 1 = Some [kk]
      /\ (bv_signed kk = 0 \/ Y mod 8 + (1 - 1) < bv_signed kk) /\ -128 <= bv_signed kk < 128.
  Proof.
    intros mq p q jj Y AD H1 H2 HY.
    apply (acl_shadow mq p q jj 1 Y AD H1 ltac:(lia) ltac:(lia)); [|exact HY].
    pose proof (Z.mod_pos_bound Y 8 ltac:(lia)). lia.
  Qed.

  (* The shadow fact of a w-byte access at p + jj, p 4-aligned. *)
  Lemma shw : forall (mq : word -> option byte) p q jj w Y, addressable mq p q -> p mod 4 = 0 -> 0 <= jj ->
    jj mod 4 + w <= 4 -> 1 <= w -> jj + w <= q -> Y = p + jj ->
    exists kk : byte, ov_read_bytes rsegs mq (wa (Y / 8 + ASAN_K)) 1 = Some [kk]
      /\ (bv_signed kk = 0 \/ Y mod 8 + (w - 1) < bv_signed kk) /\ -128 <= bv_signed kk < 128.
  Proof.
    intros mq p q jj w Y AD Hp Hj Hjw Hw Hq HY.
    apply (acl_shadow mq p q jj w Y AD Hj Hw Hq); [|exact HY].
    rewrite HY. exact (acl_mod_al p jj w Hp Hj Hjw).
  Qed.

  (* The record's bytes 4..27, as in the plain proof. *)
  Definition P1 : list byte :=
    [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11;
     cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5;
     (if cp_bcast fr then Z_to_bv 8 1 else cp_z); cp_z; cp_z; cp_z;
     cp_b fr 14; cp_b fr 15; cp_b fr 18; cp_b fr 19; cp_b fr 21; cp_b fr 20; cp_b fr 22; cp_z].

  (* ----- the body's branch and record tactics (as in lib/U/Prog/reac_ctrl_parse.v) ----- *)

  Ltac cond_norm :=
    rewrite ?rc_lor0;
    rewrite ?rc_eqb_zxb by zlitr;
    repeat match goal with
    | |- context [bv_unsigned (cp_b fr ?i)] => change (bv_unsigned (cp_b fr i)) with (cp_v fr i)
    end.

  Ltac br :=
    cond_norm;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if negb (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    | |- evtF _ _ _ (MS _ _ (if (?x =? ?y) then _ else _) _ _ _ _) => zdec x y
    end.

  (* A pointer-overflow guard of the ubsan build that cannot fire. *)
  Ltac ub_false :=
    rc_wrap_lits;
    lazymatch goal with
    | |- evtF _ _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false;
        [ cbv iota
        | symmetry; unfold bv_eqb, bv_ltu; rewrite ?unsigned_lit by lia; cbn [negb];
          first [ reflexivity | apply Z.eqb_neq; lia | apply Z.ltb_ge; lia | apply negb_false_iff, Z.ltb_lt; lia ] ]
    end.

  Ltac kfact :=
    match goal with HE : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE end; cbn [fst];
    unfold cp_kind, cp_type, cp_amp; zeval; reflexivity.

  Ltac bfact :=
    match goal with HE : cp_hdr n fr = true |- _ => unfold ctrlparse; rewrite HE end; cbn [snd];
    unfold cp_struct, cp_rec, cp_kind, cp_type, cp_amp, P1; zeval; zeval; reflexivity.

  Ltac kbound := first [zlitr | match goal with KR : 2 <= KL1 ?x <= 13 /\ _ |- _ => clear - KR; lia end].

  (* The len input bytes at f + lo, readable at the current memory (MUq : munch (Wb ..) m _, DJ : f_dj_Wb ..). *)
  Ltac rdbb lo len MUq DJ tac :=
    let HIN := fresh "HIN" in
    assert (HIN : forall jj, (jj < len)%nat -> In (lo + jj)%nat (cp_rd n fr)) by tac;
    let RR := fresh "RO" in
    pose proof (rc_ro_now rsegs _ m _ f fr lo len (cp_rd n fr) Hrd HIN ltac:(lia) ltac:(lia) ltac:(lia)
                  MUq ltac:(apply DJ; lia)) as RR;
    cbn [map seq] in RR;
    let z := eval vm_compute in (Z.of_nat lo) in change (Z.of_nat lo) with z in RR;
    rewrite ?Z.add_0_r in RR;
    clear HIN.

  (* The exit lemma (0x84224 -> Qp), proved in the other lane; the body's lemmas take it as their continuation. *)
  Definition EPI : Prop :=
    forall fra fv spc j nn w120 (mc : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> aJb fra j nn mc ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84224) fc None mc (seg_rom rsegs)).

  (* 0x84224 with the record complete: hand it to the exit lemma. *)
  Lemma b_done : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    rw_cells rsegs mc R [CB 36 (snd (ctrlparse n fr))] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84224) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HRec.
    apply HEPI with (fra := fra) (fv := fv) (j := j) (nn := nn) (w120 := w120).
    - exact HK.
    - exact (bj_aJb fra fv spc j nn w120 R mc0 mc HK HR HB AD0 HJ).
    - intros Ho. destruct HR as [(Ho0 & _)|(_ & ER)]; [contradiction|]. rewrite <- ER. exact HRec.
    - exact (w120_bj fra fv spc j nn w120 R mc0 mc HK HR H120 (proj1 HJ)).
  Qed.

  (* 0x843d0: store the kind word and leave through 0x84224. *)
  Lemma b_kind : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) k tg
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    rw_cells rsegs mc R [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mc (R + 4) [CB 24 P1] ->
    rw_cells rsegs mc (R + 28) [CB 2 tg] -> rw_cells rsegs mc (R + 30) [CB 6 (repeat cp_z 6)] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ repeat cp_z 6 ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 k)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x843d0) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc k tg x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HKc HP HT HG Ek Hk EB.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (RP & R4 & R64 & _ & _ & RSV & _ & _ & _).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    step. step.
    match goal with H : rw_cells rsegs ?mm R [C4 _] |- _ => rename H into HK' end.
    pose proof (rc_rw_join rsegs _ R (R + 4) _ _ HK' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ R (R + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HT) as J2.
    pose proof (rc_rw_join rsegs _ R (R + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HG) as J3.
    apply (rc_rw_flat rsegs _ R _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (b_done fra fv spc j nn w120 R mc0 _); try eassumption.
      refine (conj MU (conj WM (conj RM (conj MI (conj ST SV))))).
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x845e8: the kind word is in the record; read it back (checked) and leave through 0x84224. *)
  Lemma b_fin4 : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) k tg amp
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    rw_cells rsegs mc R [C4 (Z_to_bv 64 k)] -> rw_cells rsegs mc (R + 4) [CB 24 P1] ->
    rw_cells rsegs mc (R + 28) [CB 2 tg] -> rw_cells rsegs mc (R + 30) [CB 6 amp] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ amp ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 x10
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x845e8) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc k tg amp x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HK' HP HT HG Ek Hk EB.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (RP & R4 & R64 & _ & _ & RSV & _ & _ & _).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    assert (RX : 0 <= R < 2^64) by lia.
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    assert (RD4 : ov_read_bytes rsegs mc (wa (R + 0)) 4 = Some (le4 (Z_to_bv 64 k))).
    { apply (cl_rd rsegs mc R (le4 (Z_to_bv 64 k)) _ 0 4);
        [ exact (proj2 (proj1 (cl_rw_c4 rsegs mc R (Z_to_bv 64 k) HK')))
        | rewrite length_le4; lia | reflexivity ]. }
    assert (SH : exists kk : byte, ov_read_bytes rsegs mc (wa (R / 8 + ASAN_K)) 1 = Some [kk]
                   /\ (bv_signed kk = 0 \/ R mod 8 + (4 - 1) < bv_signed kk) /\ -128 <= bv_signed kk < 128).
    { apply (acl_shadow mc R 36 0 4 R); [ | lia | lia | lia | exact (acl_mod_al0 R R4) | lia ].
      exact (bj_addr fra fv spc j nn w120 R mc0 mc R 36 HK HR AD0 MU). }
    chk_core R RX (Z_to_bv 5 11) SH pre_sr add3.
    step. rewrite (cl_sx32 k) by lia.
    step.
    apply cl_rw_c4 in HK'.
    pose proof (rc_rw_join rsegs _ R (R + 4) _ _ HK' ltac:(cbn [cells_size csize app]; lia) HP) as J1.
    pose proof (rc_rw_join rsegs _ R (R + 28) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HT) as J2.
    pose proof (rc_rw_join rsegs _ R (R + 30) _ _ J2 ltac:(cbn [cells_size csize app]; lia) HG) as J3.
    apply (rc_rw_flat rsegs _ R _ (snd (ctrlparse n fr))) in J3.
    - rewrite ctrlparse_length in J3. rewrite <- Ek.
      eapply (b_done fra fv spc j nn w120 R mc0 _); try eassumption.
      refine (conj MU (conj WM (conj RM (conj MI (conj ST SV))))).
    - rewrite EB. cbn [app cells_bytes cbytes]. rewrite rc_le4_small by lia.
      rewrite !app_nil_r. cbn [app]. reflexivity.
  Qed.

  (* 0x845e4: store the kind word, then 0x845e8. *)
  Lemma b_kind2 : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) k tg
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    rw_cells rsegs mc R [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mc (R + 4) [CB 24 P1] ->
    rw_cells rsegs mc (R + 28) [CB 2 tg] -> rw_cells rsegs mc (R + 30) [CB 6 (repeat cp_z 6)] ->
    fst (ctrlparse n fr) = k -> 0 <= k < 256 ->
    snd (ctrlparse n fr) = [Z_to_bv 8 k; cp_z; cp_z; cp_z] ++ P1 ++ tg ++ repeat cp_z 6 ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 k)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K) x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x845e4) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc k tg x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HKc HP HT HG Ek Hk EB.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (RP & R4 & R64 & _ & _ & RSV & _ & _ & _).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    step.
    match goal with H : rw_cells rsegs ?mm R [C4 _] |- _ => rename H into HK' end.
    eapply (b_fin4 fra fv spc j nn w120 R mc0 _ k tg (repeat cp_z 6)); try eassumption.
    refine (conj MU (conj WM (conj RM (conj MI (conj ST SV))))).
  Qed.

  (* The o-join `addi r, s10, 0; beqz s4, L; addi r, s4, 0`, stepped to its beqz (or `beqz s4, L; addi s10, s4, 0`
     with r = s10): at L the register r holds R whichever way the branch goes (HO: R = fra + 32 when o = 0, else o);
     only r is generalized, so s10 keeps fra + 32. *)
  Ltac ojoin HO R r :=
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        let G := fresh "G" in let Hz := fresh "Hz" in let Hq := fresh "Hq" in
        enough (G : forall w, w = Z_to_bv 64 R -> evtF sg rgq Qq (MS (bvmap_set r w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.

  (* The kind tree walks to one of these: the three 4-byte-store checks, the link-1 call, the record branch. *)
  Ltac drive2 :=
    repeat (lazymatch goal with
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84328) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84350) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843bc) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843d8) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84390) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843f0) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x845a0) _ _ _ _) => fail
            | |- evtF _ _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => br
            | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => step
            end).

  (* 0x84318 .. 0x84600: the kind tree, the record's tail fields (the link-1 and the head-amp records). *)
  Lemma b_tree : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte)
      (x1 x5 x6 x7 x16 x17 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    addressable mc0 f 50 -> (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    cp_hdr n fr = true -> ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0))%bool = false ->
    rw_cells rsegs mc R [CB 4 (repeat cp_z 4)] -> rw_cells rsegs mc (R + 4) [CB 24 P1] ->
    rw_cells rsegs mc (R + 28) [CB 2 (repeat cp_z 2)] -> rw_cells rsegs mc (R + 30) [CB 6 (repeat cp_z 6)] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 (f + 18)) (zxb (cp_b fr 22)) (zxb (cp_b fr 17)) (zxb (cp_b fr 18)) (zxb (cp_b fr 19))
               (zxb (cp_b fr 16)) x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) (Z_to_bv 64 o) (Z_to_bv 64 f)
               (Z_to_bv 64 (R + 16)) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) (wa ASAN_K)
               (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84318) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc x1 x5 x6 x7 x16 x17 x28 x29 x30 x31
      HEPI HK HR HB AD0 ADf0 H120 HJ HE T0 HKc HP HT HG.
    destruct (rf_facts fra fv spc j nn w120 R HK HR)
      as (RP & R4 & R64 & RAP & RRT & RSV & RSP & RFF & RW120).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    destruct (proj1 (cp_hdr_spec n fr) HE) as (HN & E12 & E13).
    destruct (HF HN) as (Hf0 & Hf50 & HfW).
    pose proof (RFF HN) as RFf.
    pose proof (RINF HN) as RGINF. pose proof (SCF HN) as SCINF. pose proof (SKF HN) as SKINF.
    assert (RXr : 0 < R /\ R + 36 <= 2^64) by lia.
    assert (RXf : 0 < f /\ f + 50 <= 2^64) by lia.
    pose proof HR as HO. unfold RF in HO.
    pose proof (cp_v_range fr 16). pose proof (cp_v_range fr 17). pose proof (cp_v_range fr 18).
    pose proof (cp_v_range fr 19). pose proof (cp_v_range fr 22).
    pose proof (cp_v_range fr 32). pose proof (cp_v_range fr 33). pose proof (cp_v_range fr 34).
    pose proof (cp_v_range fr 35).
    pose proof (KL1_range (cp_v fr 22)) as KR.
    assert (KL6 : KL1 (cp_v fr 22) <> 6) by (clear -KR; lia).
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq R 36 HK HR AD0 MUq) as ADR.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq f 50 HK HR ADf0 MUq) as ADF.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_mub fra fv spc j nn w120 R mc0 mq HK HR HB MUq) as MUB.
    pose proof (f_dj_Wb fra fv spc j nn w120 HK HN) as DJF.
    pose proof (shw mc R 36 0 4 R (ADR mc MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as SHR.
    drive2.
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84328) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
             eapply (b_kind fra fv spc j nn w120 R mc0 _ 4 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84350) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
             eapply (b_kind fra fv spc j nn w120 R mc0 _ 8 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843bc) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step;
             eapply (b_kind fra fv spc j nn w120 R mc0 _ 13 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843d8) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
             eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 12 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x845a0) _ _ _ _) =>
             chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
             eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 13 (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84390) _ _ _ _) => idtac
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843f0) _ _ _ _) => idtac
         end.
    (* the two blocks the tree leaves open *)
    all: lazymatch goal with
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x84390) _ _ _ _) =>
             (* 0x84390: kind_of_link1 (byte 22), then the checked store at 0x845e4 *)
             step; step;
             eapply evtF_cut; [eapply KOL | intros ? [? ->]];
             rewrite rc_signed_zxb;
             change (bv_unsigned (cp_b fr 22)) with (cp_v fr 22);
             replace (ret_pc (Z_to_bv 64 0x84398)) with (Z_to_bv 64 0x84398)
               by (symmetry; apply ret_pc_even; [lia | reflexivity]);
             destruct SHR as (kk & RK & OK & KR0);
             pre_sr R RXr; steps_until_if; clear RK;
             unfold sxb; rewrite (rc_eqb0_signed (bv_signed kk)) by (clear -KR0; lia);
             destruct (Z.eqb_spec (bv_signed kk) 0) as [K0|K0]; cbv iota;
             [ eapply (b_kind2 fra fv spc j nn w120 R mc0 _ (KL1 (cp_v fr 22)) (repeat cp_z 2));
               [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
               | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
               | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]
             | step; rewrite ?(unsigned_lit R) by (clear -RXr; lia); rewrite rc_land7;
               step;
               (let MB := fresh "MB" in pose proof (Z.mod_pos_bound R 8 eq_refl) as MB;
                rewrite ?(unsigned_lit (R mod 8)) by (clear -MB; lia); clear MB);
               step;
               (let MB := fresh "MB" in pose proof (Z.mod_pos_bound R 8 eq_refl) as MB;
                rewrite (rc_lts_signed (R mod 8 + 3) (bv_signed kk)) by (clear -MB KR0; lia);
                replace (R mod 8 + 3 <? bv_signed kk) with true
                  by (symmetry; apply Z.ltb_lt; destruct OK as [OK|OK];
                      [exfalso; exact (K0 OK) | clear -OK; lia]);
                clear MB);
               cbv iota;
               eapply (b_kind2 fra fv spc j nn w120 R mc0 _ (KL1 (cp_v fr 22)) (repeat cp_z 2));
                 [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
                 | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
                 | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ] ]
         | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 0x843f0) _ _ _ _) => idtac
         end.
    (* 0x843f0: byte 18 = 4; byte 19 decides kind 11 / the record *)
    step. step. br.
    2:{ chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3; step; step;
        eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 11 (repeat cp_z 2));
          [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
          | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
          | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]. }
    assert (HRC : cp_rec fr = true) by (unfold cp_rec, cp_type; zeval; reflexivity).
    rdbb 34%nat 2%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; apply cp_rd_rec; [exact HE | exact HRC | lia]).
    rdbb 32%nat 1%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; replace (32 + jj)%nat with 32%nat by lia; apply cp_rd_rec;
            [exact HE | exact HRC | lia]).
    step. step. ub_false. step. step. ub_false. step.
    pose proof (sh1 _ f 50 34 (f + 34) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH34.
    chk_core (f + 34) RXf (Z_to_bv 5 13) SH34 pre_sr no_extra.
    step.
    pose proof (sh1 _ f 50 35 (f + 35) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH35.
    chk_core (f + 35) RXf (Z_to_bv 5 12) SH35 pre_sr no_extra.
    step. step. ojoin HO R (Z_to_bv 5 12).
    step.
    pose proof (shw _ R 36 28 2 (R + 28) (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SH28.
    chk_core (R + 28) RXr (Z_to_bv 5 15) SH28 pre_sr add1.
    step. step. step. step. step. ub_false.
    match goal with H : rw_cells rsegs _ (R + 28) [C2 _] |- _ => rename H into HT' end.
    apply (rc_rw_flat rsegs _ (R + 28) _ [cp_b fr 35; cp_b fr 34]) in HT';
      [|cbn [cells_bytes cbytes]; rewrite rc_le2_pack; reflexivity].
    cbn [length] in HT'.
    step.
    pose proof (sh1 _ f 50 32 (f + 32) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH32.
    chk_core (f + 32) RXf (Z_to_bv 5 14) SH32 pre_sr no_extra.
    step. step. step. br.
    2:{ pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia)) as SHRa;
        chk_core R RXr (Z_to_bv 5 11) SHRa pre_sr add3; step;
        eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 5 [cp_b fr 35; cp_b fr 34]);
          [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
          | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
          | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]. }
    step. step. ub_false. step.
    rdbb 33%nat 1%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; replace (33 + jj)%nat with 33%nat by lia; apply cp_rd_33;
            [exact HE | exact HRC | lia]).
    pose proof (sh1 _ f 50 33 (f + 33) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH33.
    chk_core (f + 33) RXf (Z_to_bv 5 14) SH33 pre_sr no_extra.
    step. step. step. br.
    2:{ pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                      ltac:(lia)) as SHRa;
        chk_core R RXr (Z_to_bv 5 11) SHRa pre_sr add3; step;
        eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 5 [cp_b fr 35; cp_b fr 34]);
          [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
          | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
          | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]. }
    step. step.
    rewrite rc_pack_eqb by zlitr.
    change (bv_unsigned (cp_b fr 34)) with (cp_v fr 34). change (bv_unsigned (cp_b fr 35)) with (cp_v fr 35).
    zdec (cp_v fr 34 * 256 + cp_v fr 35) 257.
    2:{ destruct (Z.eqb_spec (cp_v fr 34) 1) as [E34n|E34n];
          [assert (E35n : cp_v fr 35 <> 1) by lia|].
        - pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(lia)) as SHRa.
          chk_core R RXr (Z_to_bv 5 11) SHRa pre_sr add3. step.
          eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 5 [cp_b fr 35; cp_b fr 34]);
            [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
            | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
            | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ].
        - pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                        ltac:(lia)) as SHRa.
          chk_core R RXr (Z_to_bv 5 11) SHRa pre_sr add3. step.
          eapply (b_kind2 fra fv spc j nn w120 R mc0 _ 5 [cp_b fr 35; cp_b fr 34]);
            [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
            | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
            | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ]. }
    assert (E34 : cp_v fr 34 = 1) by lia. assert (E35 : cp_v fr 35 = 1) by lia.
    assert (K6 : cp_kind fr = 6) by (unfold cp_kind, cp_type, cp_amp; zeval; reflexivity).
    rdbb 36%nat 3%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; apply cp_rd_amp; [exact HE | exact HRC | exact K6 | lia]).
    pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SHR6.
    chk_core R RXr (Z_to_bv 5 12) SHR6 pre_sr add3.
    step. step. step. step. ub_false. step.
    step. step. ojoin HO R (Z_to_bv 5 12).
    pose proof (sh1 _ f 50 36 (f + 36) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH36.
    chk_core (f + 36) RXf (Z_to_bv 5 14) SH36 pre_sr no_extra.
    step.
    pose proof (sh1 _ R 36 30 (R + 30) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH30.
    chk_core (R + 30) RXr (Z_to_bv 5 14) SH30 pre_sr no_extra.
    step. step. rewrite rc_le1_zxb. mem_after_store. step. ub_false. step.
    step. step. ojoin HO R (Z_to_bv 5 12).
    pose proof (sh1 _ f 50 37 (f + 37) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH37.
    chk_core (f + 37) RXf (Z_to_bv 5 14) SH37 pre_sr no_extra.
    step.
    pose proof (sh1 _ R 36 31 (R + 31) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH31.
    chk_core (R + 31) RXr (Z_to_bv 5 14) SH31 pre_sr no_extra.
    step. step. rewrite rc_le1_zxb. mem_after_store. step. ub_false. step.
    step. ojoin HO R (Z_to_bv 5 26).
    pose proof (sh1 _ f 50 38 (f + 38) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH38.
    chk_core (f + 38) RXf (Z_to_bv 5 12) SH38 pre_sr no_extra.
    step.
    pose proof (sh1 _ R 36 32 (R + 32) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH32r.
    chk_core (R + 32) RXr (Z_to_bv 5 13) SH32r pre_sr no_extra.
    step. rewrite rc_le1_zxb. mem_after_store. step.
    match goal with H : rw_cells rsegs _ R [C4 _] |- _ => rename H into HK6 end.
    match goal with H : rw_cells rsegs _ (R + 30) _ |- _ => rename H into HG6 end.
    eapply (rc_rw_flat rsegs _ (R + 30)) in HG6; [|reflexivity].
    cbn [cells_bytes cbytes app length] in HG6.
    eapply (b_fin4 fra fv spc j nn w120 R mc0 _ 6 [cp_b fr 35; cp_b fr 34] _);
      [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
      | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
      | eassumption | eassumption | eassumption | eassumption | kfact | kbound | bfact ].
  Qed.

  (* 0x84010 .. 0x84200: the broadcast word and the per-field stores, then the kind-1 leaf or the kind tree. *)
  Lemma b_fields : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte) v
      (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    addressable mc0 f 50 -> (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    cp_hdr n fr = true -> -256 < v < 256 -> (v =? 0) = cp_bcast fr ->
    ro_cells rsegs mc f (map C1 (map (cp_b fr) (seq 0 23))) ->
    rw_cells rsegs mc R [CB 4 (repeat cp_z 4)] ->
    rw_cells rsegs mc (R + 4) [CB 6 [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11]] ->
    rw_cells rsegs mc (R + 10) [CB 6 [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5]] ->
    rw_cells rsegs mc (R + 16) [CB 12 (repeat cp_z 12)] ->
    rw_cells rsegs mc (R + 28) [CB 2 (repeat cp_z 2)] -> rw_cells rsegs mc (R + 30) [CB 6 (repeat cp_z 6)] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A)
               (Z_to_bv 64 v) x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 R) (Z_to_bv 64 o)
               (Z_to_bv 64 f) (Z_to_bv 64 (R + 16)) (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra)
               (wa ASAN_K) (Z_to_bv 64 (fra + 32)) s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84010) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc v x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31
      HEPI HK HR HB AD0 ADf0 H120 HJ HE Hvr Hvb RO HKc HSRC HDST HMID HT HG.
    destruct (rf_facts fra fv spc j nn w120 R HK HR)
      as (RP & R4 & R64 & RAP & RRT & RSV & RSP & RFF & RW120).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    destruct (proj1 (cp_hdr_spec n fr) HE) as (HN & E12 & E13).
    destruct (HF HN) as (Hf0 & Hf50 & HfW).
    pose proof (RFF HN) as RFf.
    pose proof (RINF HN) as RGINF. pose proof (SCF HN) as SCINF. pose proof (SKF HN) as SKINF.
    assert (RXr : 0 < R /\ R + 36 <= 2^64) by lia.
    assert (RXf : 0 < f /\ f + 50 <= 2^64) by lia.
    pose proof HR as HO. unfold RF in HO.
    pose proof (cp_v_range fr 16). pose proof (cp_v_range fr 17).
    cbn [map seq] in RO.
    destruct HJ as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq R 36 HK HR AD0 MUq) as ADR.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq f 50 HK HR ADf0 MUq) as ADF.
    (* 0x84010 .. 0x84024: the broadcast word at R + 16, the overflow guards of f + 14 and f + 15 *)
    do 4 step. ub_false. do 2 step. ub_false.
    (* 0x84028: the check of byte 14 *)
    step.
    pose proof (sh1 _ f 50 14 (f + 14) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH14.
    chk_core (f + 14) RXf (Z_to_bv 5 12) SH14 pre_sr no_extra.
    (* 0x8403c .. 0x84048: a0 = f + 15; the o-join a3 = R (s10 keeps fra + 32) *)
    do 3 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 13) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x8404c: the check of byte 15 (and the load of byte 14) *)
    pose proof (sh1 _ f 50 15 (f + 15) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH15.
    chk_core (f + 15) RXf (Z_to_bv 5 11) SH15 pre_sr no_extra.
    (* 0x84060: the check of the 2-byte store at R + 20 (and the load of byte 15) *)
    step.
    pose proof (shw _ R 36 20 2 (R + 20) (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SH20.
    chk_core (R + 20) RXr (Z_to_bv 5 14) SH20 pre_sr add1.
    (* 0x84078 .. 0x84088: the store at R + 20, the overflow guard of f + 18 *)
    do 5 step. ub_false.
    (* 0x8408c: the check of byte 18 *)
    step.
    pose proof (sh1 _ f 50 18 (f + 18) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH18.
    chk_core (f + 18) RXf (Z_to_bv 5 12) SH18 pre_sr no_extra.
    (* 0x840a0 .. 0x840a8: the o-join a1 = R *)
    do 2 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 11) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x840ac: the check of the store at R + 22 (and the load of byte 18) *)
    step.
    pose proof (sh1 _ R 36 22 (R + 22) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH22.
    chk_core (R + 22) RXr (Z_to_bv 5 14) SH22 pre_sr no_extra.
    (* 0x840c4 .. 0x840cc: the store at R + 22 (le1 (zxb b) folded to [b] so it joins the record's cells), the
       overflow guard of f + 19 *)
    do 2 step. rewrite rc_le1_zxb. mem_after_store. step. ub_false.
    (* 0x840d0: the check of byte 19 *)
    step.
    pose proof (sh1 _ f 50 19 (f + 19) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH19.
    chk_core (f + 19) RXf (Z_to_bv 5 14) SH19 pre_sr no_extra.
    (* 0x840e4 .. 0x840ec: the o-join a2 = R *)
    do 2 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 12) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x840f0: the check of the store at R + 23 (and the load of byte 19) *)
    step.
    pose proof (sh1 _ R 36 23 (R + 23) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH23.
    chk_core (R + 23) RXr (Z_to_bv 5 11) SH23 pre_sr no_extra.
    (* 0x84108 .. 0x84114: the store at R + 23, the overflow guard of f + 21 *)
    do 3 step. rewrite rc_le1_zxb. mem_after_store. step. ub_false.
    (* 0x84118: the check of byte 20 *)
    step.
    pose proof (sh1 _ f 50 20 (f + 20) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH20f.
    chk_core (f + 20) RXf (Z_to_bv 5 15) SH20f pre_sr no_extra.
    (* 0x8412c .. 0x84138: a1 = f + 21; the o-join a6 = R *)
    do 3 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 16) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x8413c: the check of byte 21 (and the load of byte 20) *)
    pose proof (sh1 _ f 50 21 (f + 21) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH21.
    chk_core (f + 21) RXf (Z_to_bv 5 12) SH21 pre_sr no_extra.
    (* 0x84150: the check of the 2-byte store at R + 24 (and the load of byte 21) *)
    step.
    pose proof (shw _ R 36 24 2 (R + 24) (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SH24.
    chk_core (R + 24) RXr (Z_to_bv 5 17) SH24 pre_sr add1.
    (* 0x84168 .. 0x84178: the store at R + 24, the overflow guard of f + 22 *)
    do 5 step. ub_false.
    (* 0x8417c: the check of byte 22 *)
    step.
    pose proof (sh1 _ f 50 22 (f + 22) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH22f.
    chk_core (f + 22) RXf (Z_to_bv 5 15) SH22f pre_sr no_extra.
    (* 0x84190 .. 0x84198: the o-join a2 = R *)
    do 2 step.
    lazymatch goal with
    | |- evtF ?sg ?rgq ?Qq (MS ?Rg ?Fm (if _ then ?T else _) ?fcc ?rv ?mm ?ro) =>
        enough (G : forall w, w = Z_to_bv 64 R ->
                      evtF sg rgq Qq (MS (bvmap_set (Z_to_bv 5 12) w Rg) Fm T fcc rv mm ro));
        [ destruct HO as [[Hz Hq]|[Hz Hq]];
          [ rewrite (rc_beq0_true o Hz); cbv iota; exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq)))
          | rewrite (rc_beq0_false o Hz ltac:(lia)); cbv iota; step;
            exact (G _ (f_equal (Z_to_bv 64) (eq_sym Hq))) ]
        | intros ? ->; simp_regs ]
    end.
    (* 0x8419c: the check of the store at R + 26 (and the load of byte 22) *)
    step.
    pose proof (sh1 _ R 36 26 (R + 26) (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH26.
    chk_core (R + 26) RXr (Z_to_bv 5 16) SH26 pre_sr no_extra.
    (* 0x841b4 .. 0x841bc: the store at R + 26, the overflow guard of f + 16 *)
    do 2 step. rewrite rc_le1_zxb. mem_after_store. step. ub_false.
    (* 0x841c0: the check of byte 16 *)
    step.
    pose proof (sh1 _ f 50 16 (f + 16) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH16.
    chk_core (f + 16) RXf (Z_to_bv 5 16) SH16 pre_sr no_extra.
    (* 0x841d4 .. 0x841d8: the overflow guard of f + 17 *)
    do 2 step. ub_false.
    (* 0x841dc: the check of byte 17 (and the load of byte 16) *)
    step.
    pose proof (sh1 _ f 50 17 (f + 17) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH17.
    chk_core (f + 17) RXf (Z_to_bv 5 17) SH17 pre_sr no_extra.
    (* 0x841f4 .. 0x84200: the load of byte 17, the or of bytes 16 and 17, the branch *)
    step. step. rewrite ?rc_zextb. step. step.
    (* the record's bytes 4..27 are complete *)
    match goal with H : rw_cells rsegs _ (R + 4) [CB 6 _] |- _ => rename H into HSRC' end.
    match goal with H : rw_cells rsegs _ (R + 10) [CB 6 _] |- _ => rename H into HDST' end.
    pose proof (rc_rw_join rsegs _ (R + 4) (R + 10) _ _ HSRC' ltac:(cbn [cells_size csize app]; lia) HDST')
      as J1.
    pose proof (rc_rw_join rsegs _ (R + 4) (R + 16) _ _ J1 ltac:(cbn [cells_size csize app]; lia) HMID) as J2.
    clear HSRC' HDST' HMID J1.
    apply (rc_rw_flat rsegs _ (R + 4) _ P1) in J2.
    2:{ cbn [app cells_bytes cbytes]. rewrite rc_le4_seqz by lia. rewrite !rc_le2_pack. rewrite Hvb.
        cbn [skipn firstn repeat app]. reflexivity. }
    change (length P1) with 24%nat in J2. rename J2 into HP.
    cond_norm.
    destruct ((cp_v fr 16 =? 0) && (cp_v fr 17 =? 0))%bool eqn:T0; cbn [negb]; cbv iota.
    - (* 0x84204 .. 0x84218: kind 1: the check of the kind word at R, then 0x843d0 *)
      rewrite andb_true_iff, !Z.eqb_eq in T0. destruct T0 as [T0a T0b].
      pose proof (shw _ R 36 0 4 R (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                    ltac:(lia)) as SHR.
      chk_core R RXr (Z_to_bv 5 11) SHR pre_sr add3.
      step. step.
      eapply (b_kind fra fv spc j nn w120 R mc0 _ 1 (repeat cp_z 2));
        [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact H120
        | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))
        | exact HKc | exact HP | exact HT | exact HG | kfact | lia | bfact ].
    - (* 0x84318: the kind tree *)
      eapply (b_tree fra fv spc j nn w120 R mc0);
        [ exact HEPI | exact HK | exact HR | exact HB | exact AD0 | exact ADf0 | exact H120
        | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV))))) | exact HE | exact T0
        | exact HKc | exact HP | exact HT | exact HG ].
  Qed.

  Lemma rc_land3 : forall x, x mod 4 = 0 -> 0 <= x < 2^64 ->
    Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 x)) 3) = Z_to_bv 64 0.
  Proof.
    intros x H Rx. rewrite unsigned_lit by lia. change 3 with (Z.ones 2). rewrite Z.land_ones by lia.
    change (2^2) with 4. rewrite H. reflexivity.
  Qed.

  (* 0x8421c: a failed header guard; the record keeps the 36 zero bytes of ctrlparse. *)
  Lemma b_none : forall fra fv spc j nn w120 R (mc0 mc : word -> option byte)
      (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    EPI -> FK fra fv spc j nn w120 -> RF fra R -> BI (Wf fra j nn) mc0 -> addressable mc0 R 36 ->
    (fv <> 0 -> bytes_at rsegs mc0 (fra + 120) (le8 w120)) -> BJ R mc0 mc ->
    cp_hdr n fr = false -> rw_cells rsegs mc R [CB 36 (repeat cp_z 36)] ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 fv) (Z_to_bv 64 R) x20 x21 x22 (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra)
               x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x8421c) fc None mc (seg_rom rsegs)).
  Proof.
    intros fra fv spc j nn w120 R mc0 mc x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x25 x26
      x28 x29 x30 x31 HEPI HK HR HB AD0 H120 HJ HH HZ.
    destruct (rf_facts fra fv spc j nn w120 R HK HR) as (RP & R4 & R64 & _).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    assert (EK0 : fst (ctrlparse n fr) = 0) by (unfold ctrlparse; rewrite HH; reflexivity).
    step. rewrite rc_land3 by lia. step. ub_false.
    replace (Z_to_bv 64 0) with (Z_to_bv 64 (fst (ctrlparse n fr))) by (rewrite EK0; reflexivity).
    eapply (b_done fra fv spc j nn w120 R mc0 mc); try eassumption.
    rewrite (ctrlparse_bytes_none n fr HH). exact HZ.
  Qed.

  (* 0x83f28 .. 0x84010: the record's zeroing, the header guards, the two input copies and the compare. *)
  Lemma L_body_k :
    (forall fra fv spc j nn w120 (mc : word -> option byte)
      (x1 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x25 x26 x28 x29 x30 x31 : word),
    FK fra fv spc j nn w120 -> aJb fra j nn mc ->
    (o <> 0 -> rw_cells rsegs mc o [CB 36 (snd (ctrlparse n fr))]) ->
    (fv <> 0 -> bytes_at rsegs mc (fra + 120) (le8 w120)) ->
    evtF rsegs RNG Qp
      (MS (mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (fst (ctrlparse n fr)))
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) x19 x20 x21 x22
               (Z_to_bv 64 (fra / 8 + ASAN_K)) (Z_to_bv 64 fra) x25 x26 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x84224) fc None mc (seg_rom rsegs))) ->
    KB Qp.
  Proof.
    intros HEPI. unfold KB.
    intros fra fv spc j nn w120 mc0 rr x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31
      HK HB AD32 H120.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (Hspc : S - 288 <= spc <= S - 128).
    { pose proof HK as HK2. destruct HK2 as (_ & _ & _ & Esp & _); subst spc; lia. }
    remember (REC fra) as R eqn:ER.
    assert (HR : RF fra R).
    { unfold RF. subst R. unfold REC. destruct (Z.eqb_spec o 0) as [Eo|Eo];
        [left; split; [exact Eo | reflexivity] | right; split; [exact Eo | reflexivity]]. }
    clear ER.
    destruct (rf_facts fra fv spc j nn w120 R HK HR)
      as (RP & R4 & R64 & RAP & RRT & RSV & RSP & RFF & RW120).
    pose proof (rngF_rec fra fv spc j nn w120 R HK HR) as RGREC.
    pose proof (rngF_rec_cov fra fv spc j nn w120 R HK HR) as SCREC.
    pose proof (rngF_rec_kov fra fv spc j nn w120 R HK HR) as SKREC.
    (* the record is apart from each callee's frame, as plain disjunctions for the transport tactics *)
    pose proof (RSP 2208 ltac:(lia)) as RSPa.
    pose proof (RSP 2224 ltac:(lia)) as RSPb.
    pose proof (RSP 4560 ltac:(lia)) as RSPc.
    pose proof HB as HB'. destruct HB' as (MU0 & WM0 & RM0 & MIb & SV0).
    assert (AD0 : addressable mc0 R 36).
    { pose proof HR as HR2. destruct HR2 as [(Ho & ER2)|(Ho & ER2)]; subst R; [exact AD32|].
      destruct (AO0 Ho) as (AOa & _ & _).
      apply (acl_addr_munch (Wf fra j nn) m mc0 o 36 AOa MU0). intros i Hi.
      refine (proj1 (acl_out_app_inv _ _ _ (jb_sh_out fra fv spc j nn w120 (o + i) HK _ _)));
        [exact (acl_app_in m o 36 i AOa Hi)|].
      destruct (o_apart_frame fra fv spc j nn w120 HK Ho) as [Hx|Hx]; [left | right]; lia. }
    assert (ADf0 : 50 <= n -> addressable mc0 f 50).
    { intros HN. apply (acl_addr_munch (Wf fra j nn) m mc0 f 50 (AF0 HN) MU0). intros i Hi.
      refine (proj1 (acl_out_app_inv _ _ _ (jb_sh_out fra fv spc j nn w120 (f + i) HK _ _)));
        [exact (acl_app_in m f 50 i (AF0 HN) Hi)|].
      destruct (f_apart_frame fra fv spc j nn w120 HK HN) as [Hx|Hx]; [left | right]; lia. }
    assert (ADbc0 : addressable mc0 REAC_CTRL_PARSE_BC 6).
    { apply (acl_addr_munch (Wf fra j nn) m mc0 REAC_CTRL_PARSE_BC 6 ABC MU0). intros i Hi.
      refine (proj1 (acl_out_app_inv _ _ _
                (jb_sh_out fra fv spc j nn w120 (REAC_CTRL_PARSE_BC + i) HK _ _)));
        [exact (acl_app_in m REAC_CTRL_PARSE_BC 6 i ABC Hi)|].
      destruct HK as (_ & Efr & _). subst fra.
      pose proof FkImg as HI. unfold rcpB_dj, ImgBounds.IMG_LO, ImgBounds.IMG_HI in HI. unfold REAC_CTRL_PARSE_BC. lia. }
    assert (ST0' : stk rsegs mc0 (S - 8800) S) by exact (stk_mono m mc0 _ _ ST0 WM0 RM0).
    destruct (rec_rw fra fv spc j nn w120 R mc0 HK HR HB) as [junk0 HRW0].
    pose proof HR as HO. unfold RF in HO.
    pose proof (f_dj_Wb fra fv spc j nn w120 HK) as DJF0.
    pose proof (bj_refl R mc0 MIb ST0' SV0) as HJ0. clear MU0 WM0 SV0 ST0'.
    destruct HJ0 as (MU & WM & RM & MI & ST & SV). unfold Wr in MU. unfold SAVES in SV.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq R 36 HK HR AD0 MUq) as ADR.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_mub fra fv spc j nn w120 R mc0 mq HK HR HB MUq) as MUB.
    assert (UR : bv_unsigned (Z_to_bv 64 R) = R) by (apply unsigned_lit; lia).
    assert (U36 : bv_unsigned (Z_to_bv 64 36) = 36) by reflexivity.
    assert (U0 : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity.
    assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
    assert (Uspc : bv_unsigned (Z_to_bv 64 spc) = spc) by (apply unsigned_lit; lia).
    (* 0x83f28: s3 = the record *)
    step. step. ojoin HO R (Z_to_bv 5 19). step. step. step. step.
    (* 0x83f40: asan_memset(R, 0, 36) *)
    pose proof MSET as HM.
    unfold asan_memset_contract_F_on, ASAN_MEMSET_K, rng_asan.sh_word_rng, rng_asan.sh_al8_lo,
      rng_asan.sh_al8_hi in HM.
    cbv zeta in HM.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bj_aJb fra fv spc j nn w120 R mc0 mm HK HR HB AD0
                    (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))) as AJ;
      eapply evtF_cut; [ eapply (HM) with (junk := junk0) (lo := S - 8800)
        | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      m1 & Ems & MUc & WMc & MIc & STc & RWc & ACc & SRc);
          subst ms';
          (try lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nq)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 nq)) with (Z_to_bv 64 nq)
                 by (symmetry; apply ret_pc_even; [lia | reflexivity])
           end);
          rewrite ?UR, ?U36, ?U0, ?Uspc in MUc;
          rewrite ?Uspc in STc;
          rewrite ?UR, ?U36, ?U0 in RWc;
          cbv [ASAN_MEMSET_K ASAN_MEMCPY_K BCMP_WRAP_K] in MUc;
          assert (RMd : rd_mono mm m1) by
            (apply (rd_mono_list _ _ _ MUc); apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
             cbn [fst snd]; intros y Hy;
             first [ apply (rd_of_stk _ _ _ STc); lia
                   | destruct RWc as [[Hwf1 Hb1] Hw1];
                     apply (acl_bytes_rd m1 _ _ y Hb1);
                     cbn [cells_bytes cbytes]; rewrite ?app_nil_r, ?repeat_length; cbn [length];
                     rewrite ?Z2Nat.id by lia; lia ]);
          pose proof (rd_mono_trans mc0 mm m1 RM RMd) as RMn;
          transport_after_call rsegs mm m1 MUc WMc;
          assert (STn : stk rsegs m1 (S - 8800) S) by
            (apply (stk_mono m m1 (S - 8800) S ST0);
             [ destruct HB as (_ & WMb & _); apply (wmono_trans rsegs m mc0 m1 WMb WM)
             | apply (rd_mono_trans m mc0 m1 RM0 RMn) ]);
          try clear ST; try clear MI; clear RM RMd MUc WMc STc ACc SRc;
          rename STn into ST; rename RMn into RM; rename MIc into MI ]
    end.
    all: rewrite ?UR, ?U36, ?U0, ?Uspc.
    { change (Z.to_nat 36) with 36%nat. exact HRW0. }
    { lia. }
    { exact (ADR _ MU). }
    { right. apply RAP. lia. }
    { right. apply RAP. lia. }
    { exact RRT. }
    { apply RSP. lia. }
    { exact (proj1 (stk_split rsegs mc0 (S - 8800) spc S ST ltac:(lia))). }
    { lia. }
    { exact HHM. }
    { lia. }
    { exact (jb_ac fra fv spc j nn w120 _ HK AJ). }
    { (* route (C): the record's aligned shadow-word span is in P (rec_sh_P: SRFr or SRo) *)
      apply (lib.B.ShadowRwOn.shadow_rw_on_mono P); [|exact (jb_sw fra j nn _ AJ)].
      intros za Hza. unfold lib.B.Prog.asan_memset_c_on.asan_memset_shadow_R in Hza. rewrite ?UR, ?U36 in Hza.
      exact (rec_sh_P fra fv spc j nn w120 R R 36 za HK HR ltac:(lia) ltac:(lia) Hza). }
    { exact MI. }
    { (* the footprint is decided byte by byte *) exact RBY. }
    { (* the image *)
      eapply rng_sub; [exact RIMG | unfold ImgBounds.IMG_LO; lia | unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia]. }
    { (* __asan_memset's window *) eapply rng_sub; [exact RWIN | lia | lia]. }
    { (* the 36 bytes at R *) exact RGREC. }
    { (* their aligned shadow word cover *) right. unfold shadow_addr. apply SKREC; lia. }
    { (* the aligned shadow word span of __asan_memset's window *) right. unfold shadow_addr. apply SKW; lia. }
    rewrite ?UR, ?U36, ?U0 in *. change (Z.to_nat 36) with 36%nat in *.
    change (Z_to_bv 8 (0 mod 256)) with cp_z in *.
    match goal with H : rw_cells rsegs m1 R [CB 36 (repeat cp_z 36)] |- _ => rename H into HZ end.
    try clear HRW0.
    (* 0x83f44: n < 50 *)
    step. step. rewrite (rc_ltu64 n 50) by lia.
    destruct (Z.ltb_spec n 50) as [Hlt|Hge]; cbv iota.
    { assert (HH : cp_hdr n fr = false)
        by (unfold cp_hdr; rewrite (proj2 (Z.leb_gt 50 n) Hlt); reflexivity).
      eapply b_none; first [eassumption | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))]. }
    destruct (HF Hge) as (Hf0 & Hf50 & HfW).
    pose proof (RFF Hge) as RFf.
    pose proof (RINF Hge) as RGINF. pose proof (SCF Hge) as SCINF. pose proof (SKF Hge) as SKINF.
    pose proof (DJF0 Hge) as DJF.
    assert (RXr : 0 < R /\ R + 36 <= 2^64) by lia.
    assert (RXf : 0 < f /\ f + 50 <= 2^64) by lia.
    pose proof (fun (mq : word -> option byte) (MUq : munch (Wr R) mc0 mq) =>
                  bj_addr fra fv spc j nn w120 R mc0 mq f 50 HK HR (ADf0 Hge) MUq) as ADF.
    (* 0x83f4c .. 0x83f74: the first header byte *)
    step. ub_false. step. step. ub_false. step.
    rdbb 12%nat 1%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; replace (12 + jj)%nat with 12%nat by lia; apply cp_rd_12; lia).
    pose proof (sh1 _ f 50 12 (f + 12) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH12.
    chk_core (f + 12) RXf (Z_to_bv 5 12) SH12 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b fr 12) 136) by lia.
    change (bv_unsigned (cp_b fr 12)) with (cp_v fr 12).
    destruct (Z.eqb_spec (cp_v fr 12) 136) as [E12|E12]; cbn [negb]; cbv iota.
    2:{ assert (HH : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E12), andb_false_r; reflexivity).
        eapply b_none; first [eassumption | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))]. }
    (* 0x83f78 .. 0x83f9c: the second header byte *)
    step. step. ub_false. step.
    rdbb 13%nat 1%nat (MUB _ MU) DJF
      ltac:(intros jj Hjj; replace (13 + jj)%nat with 13%nat by lia; apply cp_rd_13; lia).
    pose proof (sh1 _ f 50 13 (f + 13) (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)) as SH13.
    chk_core (f + 13) RXf (Z_to_bv 5 12) SH13 pre_sr no_extra.
    step. step. step.
    rewrite (rc_eqb_zxb (cp_b fr 13) 25) by lia.
    change (bv_unsigned (cp_b fr 13)) with (cp_v fr 13).
    destruct (Z.eqb_spec (cp_v fr 13) 25) as [E13|E13]; cbn [negb]; cbv iota.
    2:{ assert (HH : cp_hdr n fr = false)
          by (unfold cp_hdr; rewrite (proj2 (Z.eqb_neq _ _) E13), andb_false_r; reflexivity).
        eapply b_none; first [eassumption | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))]. }
    assert (HE : cp_hdr n fr = true) by (apply cp_hdr_spec; lia).
    clear RO RO0.
    rdbb 0%nat 23%nat (MUB _ MU) DJF ltac:(intros jj Hjj; apply cp_rd_e; [exact HE | lia]).
    (* 0x83fa0: the record is 4-aligned *)
    step. rewrite rc_land3 by lia. step. ub_false.
    (* the record's pieces *)
    destruct (rc_rw_cut_at rsegs _ R cp_z 36 4 (R + 4) HZ ltac:(lia) ltac:(lia)) as [HKc HZ1];
      cbn [Nat.sub] in HZ1.
    destruct (rc_rw_cut_at rsegs _ (R + 4) cp_z 32 6 (R + 10) HZ1 ltac:(lia) ltac:(lia)) as [HSRC HZ2];
      cbn [Nat.sub] in HZ2.
    destruct (rc_rw_cut_at rsegs _ (R + 10) cp_z 26 6 (R + 16) HZ2 ltac:(lia) ltac:(lia)) as [HDST HZ3];
      cbn [Nat.sub] in HZ3.
    destruct (rc_rw_cut_at rsegs _ (R + 16) cp_z 20 12 (R + 28) HZ3 ltac:(lia) ltac:(lia)) as [HMID HZ4];
      cbn [Nat.sub] in HZ4.
    destruct (rc_rw_cut_at rsegs _ (R + 28) cp_z 8 2 (R + 30) HZ4 ltac:(lia) ltac:(lia)) as [HT HG];
      cbn [Nat.sub] in HG.
    clear HZ HZ1 HZ2 HZ3 HZ4.
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 0 6 RO ltac:(cbn; lia)) as BD0.
    cbn [map seq firstn skipn] in BD0. rewrite Z.add_0_r in BD0.
    assert (Uf : bv_unsigned (Z_to_bv 64 f) = f) by (apply unsigned_lit; lia).
    assert (U10 : bv_unsigned (Z_to_bv 64 (R + 10)) = R + 10) by (apply unsigned_lit; lia).
    (* 0x83fa8: asan_memcpy(R + 10, f, 6) *)
    step. step. ojoin HO R (Z_to_bv 5 10).
    step. step. step. step.
    pose proof MCPY as HMC.
    unfold asan_memcpy_contract_F_on, ASAN_MEMCPY_K, rng_asan.sh_word_rng, rng_asan.sh_al8_lo,
      rng_asan.sh_al8_hi in HMC.
    cbv zeta in HMC.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bj_aJb fra fv spc j nn w120 R mc0 mm HK HR HB AD0
                    (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))) as AJ1;
      eapply evtF_cut;
        [ eapply (HMC) with (src := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
            (junk := repeat cp_z 6) (lo := S - 8800)
        | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      m2 & Ems & MUc & WMc & MIc & STc & RWc & BAc & ACc & SRc);
          subst ms';
          (try lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nq)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 nq)) with (Z_to_bv 64 nq)
                 by (symmetry; apply ret_pc_even; [lia | reflexivity])
           end);
          rewrite ?U10, ?U6, ?Uf, ?Uspc in MUc;
          rewrite ?Uspc in STc;
          rewrite ?U10, ?U6 in RWc;
          cbv [ASAN_MEMSET_K ASAN_MEMCPY_K BCMP_WRAP_K] in MUc;
          assert (RMd : rd_mono mm m2) by
            (apply (rd_mono_list _ _ _ MUc); apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
             cbn [fst snd]; intros y Hy;
             first [ apply (rd_of_stk _ _ _ STc); lia
                   | destruct RWc as [[Hwf1 Hb1] Hw1];
                     apply (acl_bytes_rd m2 _ _ y Hb1);
                     cbn [cells_bytes cbytes]; rewrite ?app_nil_r, ?repeat_length; cbn [length];
                     rewrite ?Z2Nat.id by lia; lia ]);
          pose proof (rd_mono_trans mc0 mm m2 RM RMd) as RMn;
          transport_after_call rsegs mm m2 MUc WMc;
          assert (STn : stk rsegs m2 (S - 8800) S) by
            (apply (stk_mono m m2 (S - 8800) S ST0);
             [ destruct HB as (_ & WMb & _); apply (wmono_trans rsegs m mc0 m2 WMb WM)
             | apply (rd_mono_trans m mc0 m2 RM0 RMn) ]);
          try clear ST; try clear MI; clear RM RMd MUc WMc STc BAc ACc SRc; rename RWc into HDSTc;
          rename STn into ST; rename RMn into RM; rename MIc into MI ]
    end.
    all: rewrite ?U10, ?U6, ?Uf, ?Uspc.
    { exact BD0. }
    { reflexivity. }
    { change (Z.to_nat 6) with 6%nat. exact HDST. }
    { right. destruct RFf as [Hx|Hx]; [right | left]; lia. }
    { lia. }
    { exact (acl_addr_sub _ f 50 f 6 (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { exact (acl_addr_sub _ R 36 (R + 10) 6 (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { right. exact (acl_app_in mc0 f 50 6 (ADf0 Hge) ltac:(lia)). }
    { right. replace (R + 10 + 6) with (R + 16) by lia. apply RAP. lia. }
    { right. split; [exact (acl_app_in mc0 f 50 7 (ADf0 Hge) ltac:(lia))|].
      replace (R + 10 + 7) with (R + 17) by lia. apply RAP. lia. }
    { destruct RRT as [Hx|Hx]; [left | right]; unfold RT_LO, RT_HI in *; lia. }
    { destruct (RSP 2224 ltac:(lia)) as [Hx|Hx]; [left | right]; lia. }
    { destruct HfW as [Hx|Hx]; [left | right]; lia. }
    { exact (proj1 (stk_split rsegs _ (S - 8800) spc S ST ltac:(lia))). }
    { lia. }
    { exact HHM. }
    { lia. }
    { exact (jb_ac fra fv spc j nn w120 _ HK AJ1). }
    { (* route (C): the source's span is in f's 50 bytes (SRf), the destination's in the record (rec_sh_P) *)
      apply (lib.B.ShadowRwOn.shadow_rw_on_mono P); [|exact (jb_sw fra j nn _ AJ1)].
      intros za Hza. unfold lib.B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in Hza. rewrite ?U10, ?Uf, ?U6 in Hza.
      destruct Hza as [Hza|Hza];
        [ exact (SRf Hge f 6 za ltac:(lia) ltac:(lia) Hza)
        | exact (rec_sh_P fra fv spc j nn w120 R (R + 10) 6 za HK HR ltac:(lia) ltac:(lia) Hza) ]. }
    { exact MI. }
    { (* the footprint is decided byte by byte *) exact RBY. }
    { (* the image *)
      eapply rng_sub; [exact RIMG | unfold ImgBounds.IMG_LO; lia | unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia]. }
    { (* __asan_memcpy's window *) eapply rng_sub; [exact RWIN | lia | lia]. }
    { (* the destination bytes in the record *) eapply rng_sub; [exact RGREC | lia | lia]. }
    { (* the source bytes in the input *) eapply rng_sub; [exact RGINF | lia | lia]. }
    { (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKREC; lia. }
    { (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; lia. }
    { (* the aligned shadow word span of __asan_memcpy's window *) right. unfold shadow_addr. apply SKW; lia. }
    rewrite ?U10, ?U6, ?Uf in *. change (Z.to_nat 6) with 6%nat in *.
    (* 0x83fc4 .. 0x83fe4: asan_memcpy(R + 4, f + 6, 6) *)
    step. step. step. ub_false. step. step. ojoin HO R (Z_to_bv 5 22). step. step. step.
    pose proof (rc_ro_bytes rsegs _ f (map (cp_b fr) (seq 0 23)) 6 6 RO ltac:(cbn; lia)) as BD1.
    cbn [map seq firstn skipn] in BD1. change (Z.of_nat 6) with 6 in BD1.
    assert (U4 : bv_unsigned (Z_to_bv 64 (R + 4)) = R + 4) by (apply unsigned_lit; lia).
    assert (Uf6 : bv_unsigned (Z_to_bv 64 (f + 6)) = f + 6) by (apply unsigned_lit; lia).
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bj_aJb fra fv spc j nn w120 R mc0 mm HK HR HB AD0
                    (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))) as AJ2;
      eapply evtF_cut;
        [ eapply (HMC) with (src := [cp_b fr 6; cp_b fr 7; cp_b fr 8; cp_b fr 9; cp_b fr 10; cp_b fr 11])
            (junk := repeat cp_z 6) (lo := S - 8800)
        | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      m3 & Ems & MUc & WMc & MIc & STc & RWc & BAc & ACc & SRc);
          subst ms';
          (try lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nq)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 nq)) with (Z_to_bv 64 nq)
                 by (symmetry; apply ret_pc_even; [lia | reflexivity])
           end);
          rewrite ?U4, ?U6, ?Uf6, ?Uspc in MUc;
          rewrite ?Uspc in STc;
          rewrite ?U4, ?U6 in RWc;
          cbv [ASAN_MEMSET_K ASAN_MEMCPY_K BCMP_WRAP_K] in MUc;
          assert (RMd : rd_mono mm m3) by
            (apply (rd_mono_list _ _ _ MUc); apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]];
             cbn [fst snd]; intros y Hy;
             first [ apply (rd_of_stk _ _ _ STc); lia
                   | destruct RWc as [[Hwf1 Hb1] Hw1];
                     apply (acl_bytes_rd m3 _ _ y Hb1);
                     cbn [cells_bytes cbytes]; rewrite ?app_nil_r, ?repeat_length; cbn [length];
                     rewrite ?Z2Nat.id by lia; lia ]);
          pose proof (rd_mono_trans mc0 mm m3 RM RMd) as RMn;
          transport_after_call rsegs mm m3 MUc WMc;
          assert (STn : stk rsegs m3 (S - 8800) S) by
            (apply (stk_mono m m3 (S - 8800) S ST0);
             [ destruct HB as (_ & WMb & _); apply (wmono_trans rsegs m mc0 m3 WMb WM)
             | apply (rd_mono_trans m mc0 m3 RM0 RMn) ]);
          try clear ST; try clear MI; clear RM RMd MUc WMc STc BAc ACc SRc; rename RWc into HSRCc;
          rename STn into ST; rename RMn into RM; rename MIc into MI ]
    end.
    all: rewrite ?U4, ?U6, ?Uf6, ?Uspc.
    { exact BD1. }
    { reflexivity. }
    { change (Z.to_nat 6) with 6%nat. exact HSRC. }
    { right. destruct RFf as [Hx|Hx]; [right | left]; lia. }
    { lia. }
    { exact (acl_addr_sub _ f 50 (f + 6) 6 (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { exact (acl_addr_sub _ R 36 (R + 4) 6 (ADR _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { right. replace (f + 6 + 6) with (f + 12) by lia.
      exact (acl_app_in mc0 f 50 12 (ADf0 Hge) ltac:(lia)). }
    { right. replace (R + 4 + 6) with (R + 10) by lia. apply RAP. lia. }
    { right. split.
      - replace (f + 6 + 7) with (f + 13) by lia. exact (acl_app_in mc0 f 50 13 (ADf0 Hge) ltac:(lia)).
      - replace (R + 4 + 7) with (R + 11) by lia. apply RAP. lia. }
    { destruct RRT as [Hx|Hx]; [left | right]; unfold RT_LO, RT_HI in *; lia. }
    { destruct (RSP 2224 ltac:(lia)) as [Hx|Hx]; [left | right]; lia. }
    { destruct HfW as [Hx|Hx]; [left | right]; lia. }
    { exact (proj1 (stk_split rsegs _ (S - 8800) spc S ST ltac:(lia))). }
    { lia. }
    { exact HHM. }
    { lia. }
    { exact (jb_ac fra fv spc j nn w120 _ HK AJ2). }
    { (* route (C): the source's span is in f's 50 bytes (SRf), the destination's in the record (rec_sh_P) *)
      apply (lib.B.ShadowRwOn.shadow_rw_on_mono P); [|exact (jb_sw fra j nn _ AJ2)].
      intros za Hza. unfold lib.B.Prog.asan_memcpy_c_on.asan_memcpy_shadow_R in Hza. rewrite ?U4, ?Uf6, ?U6 in Hza.
      destruct Hza as [Hza|Hza];
        [ exact (SRf Hge (f + 6) 6 za ltac:(lia) ltac:(lia) Hza)
        | exact (rec_sh_P fra fv spc j nn w120 R (R + 4) 6 za HK HR ltac:(lia) ltac:(lia) Hza) ]. }
    { exact MI. }
    { (* the footprint is decided byte by byte *) exact RBY. }
    { (* the image *)
      eapply rng_sub; [exact RIMG | unfold ImgBounds.IMG_LO; lia | unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI; lia]. }
    { (* __asan_memcpy's window *) eapply rng_sub; [exact RWIN | lia | lia]. }
    { (* the destination bytes in the record *) eapply rng_sub; [exact RGREC | lia | lia]. }
    { (* the source bytes in the input *) eapply rng_sub; [exact RGINF | lia | lia]. }
    { (* the destination's aligned shadow word cover *) right. unfold shadow_addr. apply SKREC; lia. }
    { (* the source's aligned shadow word cover *) right. unfold shadow_addr. apply SKINF; lia. }
    { (* the aligned shadow word span of __asan_memcpy's window *) right. unfold shadow_addr. apply SKW; lia. }
    rewrite ?U4, ?U6, ?Uf6 in *. change (Z.to_nat 6) with 6%nat in *.
    (* 0x83fe8 .. 0x83ffc: the compare with .str.4 *)
    step. step. step. step. step. step.
    destruct (rc_memcmp_ff (cp_b fr 0) (cp_b fr 1) (cp_b fr 2) (cp_b fr 3) (cp_b fr 4) (cp_b fr 5))
      as (v & Hv & Hvr & Hvb).
    pose proof BWRP as HBC. unfold bcmp_wrap_contract_F_on, BCMP_WRAP_K in HBC. cbv zeta in HBC.
    match goal with |- evtF _ _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (bj_aJb fra fv spc j nn w120 R mc0 mm HK HR HB AD0
                    (conj MU (conj WM (conj RM (conj MI (conj ST SV)))))) as AJ3;
      pose proof (jb_cl fra fv spc j nn w120 R mc0 mm HK HR HB MU) as (CL1 & CL2 & CL3 & CL4 & CL5);
      eapply evtF_cut;
        [ eapply (HBC) with (ls := [cp_b fr 0; cp_b fr 1; cp_b fr 2; cp_b fr 3; cp_b fr 4; cp_b fr 5])
            (rs := repeat (Z_to_bv 8 255) 6) (v := v) (lo := S - 8800)
        | intros ms' (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? &
                      m4 & Ems & MUc & WMc & MIc & STc & ACc & SRc & BA1 & BA2);
          subst ms';
          (try lazymatch goal with
           | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?nq)) _ _ _ _) =>
               replace (ret_pc (Z_to_bv 64 nq)) with (Z_to_bv 64 nq)
                 by (symmetry; apply ret_pc_even; [lia | reflexivity])
           end);
          rewrite ?Uspc in MUc;
          rewrite ?Uspc in STc;
          cbv [ASAN_MEMSET_K ASAN_MEMCPY_K BCMP_WRAP_K] in MUc;
          assert (RMd : rd_mono mm m4) by
            (apply (rd_mono_list _ _ _ MUc); apply Forall_cons; [|apply Forall_nil];
             cbn [fst snd]; intros y Hy; apply (rd_of_stk _ _ _ STc); lia);
          pose proof (rd_mono_trans mc0 mm m4 RM RMd) as RMn;
          transport_after_call rsegs mm m4 MUc WMc;
          assert (STn : stk rsegs m4 (S - 8800) S) by
            (apply (stk_mono m m4 (S - 8800) S ST0);
             [ destruct HB as (_ & WMb & _); apply (wmono_trans rsegs m mc0 m4 WMb WM)
             | apply (rd_mono_trans m mc0 m4 RM0 RMn) ]);
          try clear ST; try clear MI; clear RM RMd MUc WMc STc ACc SRc BA1 BA2;
          rename STn into ST; rename RMn into RM; rename MIc into MI ]
    end.
    all: rewrite ?U6, ?Uf, ?Uspc.
    all: try change (bv_unsigned (Z_to_bv 64 135680)) with 135680.
    { exact BD0. }
    { apply (rc_ro_in_image rsegs _ _ (repeat (Z_to_bv 8 255) 6)); [exact MI | vm_compute; reflexivity]. }
    { change (Z.to_nat 6) with 6%nat. exact Hv. }
    { exact MI. }
    { lia. }
    { exact (acl_addr_sub _ f 50 f 6 (ADF _ MU) ltac:(lia) ltac:(lia) ltac:(lia)). }
    { exact (bj_addr fra fv spc j nn w120 R mc0 _ REAC_CTRL_PARSE_BC 6 HK HR ADbc0 MU). }
    { right. exact (acl_app_in mc0 f 50 6 (ADf0 Hge) ltac:(lia)). }
    { right. unfold app_mem, LOWMEM_END. left. lia. }
    { right. exact (acl_app_in mc0 f 50 7 (ADf0 Hge) ltac:(lia)). }
    { right. unfold app_mem, LOWMEM_END. left. lia. }
    { destruct HfW as [Hx|Hx]; [left | right]; lia. }
    { left. lia. }
    { exact (proj1 (stk_split rsegs _ (S - 8800) spc S ST ltac:(lia))). }
    { lia. }
    { exact HHM. }
    { lia. }
    { exact (jb_ac fra fv spc j nn w120 _ HK AJ3). }
    { (* route (C): the first operand's span is in f's 50 bytes (SRf), the second's in .str.4's 6 bytes (SRbc) *)
      apply (lib.B.ShadowRwOn.shadow_rw_on_mono P); [|exact (jb_sw fra j nn _ AJ3)].
      intros za Hza. unfold lib.B.Prog.bcmp_wrap_c_on.bcmp_wrap_shadow_R in Hza. rewrite ?Uf, ?U6 in Hza.
      try change (bv_unsigned (Z_to_bv 64 135680)) with 135680 in Hza.
      destruct Hza as [Hza|Hza];
        [ exact (SRf Hge f 6 za ltac:(lia) ltac:(lia) Hza)
        | exact (SRbc 135680 6 za ltac:(unfold REAC_CTRL_PARSE_BC; lia) ltac:(unfold REAC_CTRL_PARSE_BC; lia)
                   Hza) ]. }
    { exact CL1. }
    { exact CL2. }
    { exact CL3. }
    { exact CL4. }
    { exact CL5. }
    { (* the footprint is decided byte by byte *) exact RBY. }
    { (* the image *) exact RIMG. }
    { (* the bcmp wrapper's window *) eapply rng_sub; [exact RWIN | lia | lia]. }
    { (* the 6 input bytes *) eapply rng_sub; [exact RGINF | lia | lia]. }
    { (* their aligned shadow word cover (the _on text writes it 8 * (x / 8)) *)
      right. unfold shadow_addr. rewrite !(Z.mul_comm 8). apply SKINF; lia. }
    { (* the 6 bytes at .str.4 *)
      eapply rng_sub; [exact RBC | unfold REAC_CTRL_PARSE_BC; lia | unfold REAC_CTRL_PARSE_BC; lia]. }
    { (* their aligned shadow word cover *)
      right. unfold shadow_addr. rewrite !(Z.mul_comm 8). apply SKBC; unfold REAC_CTRL_PARSE_BC; lia. }
    (* 0x84000: the check of the 4-byte store at R + 16, then the field stores *)
    pose proof (shw _ R 36 16 4 (R + 16) (ADR _ MU) R4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                  ltac:(lia)) as SH16r.
    chk_core (R + 16) RXr (Z_to_bv 5 12) SH16r pre_sr add3.
    eapply b_fields;
      first [eassumption | exact (conj MU (conj WM (conj RM (conj MI (conj ST SV))))) | exact (ADf0 Hge) | exact Hvr | exact Hvb].
  Qed.

  (* NEW (the side arm of reac_ctrl_parseF.v's entry, :1568-1573 on 6939dc6611d, then fwords / L_body_k / L_epi):
     0x83e78 .. 0x84314 from the return of the class-1 request: a0 = Fr (the cgif rule's frame_addr lyc 1 pos),
     sp = s1 = A, s0 = S, s4 / s5 / s6 = o / f / n, s9 = the shadow offset, s11 the caller's; every other register
     anything (aregs_preserved of the rule keeps s2, s3, s7, s8, s10, which the run does not read before it writes
     them). *)
  Lemma rcpB_post_F : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x24 x26 x28 x29 x30 x31 : word),
    evtF rsegs RNG Qb
      (MS (mkR x1 (Z_to_bv 64 A) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 A) (Z_to_bv 64 Fr)
               x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
               x23 x24 (wa ASAN_K) x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83e78) fc None m (seg_rom rsegs)).
  Proof.
    intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x24 x26 x28 x29 x30 x31.
    pose proof HA1 as (HA32 & HAlo & HAhi).
    assert (HK : FK Fr Fr A 0 1 (Z_to_bv 64 FL)) by (unfold FK; repeat split).
    step. step. step. step.
    rewrite (rc_neq0_64 Fr) by lia. cbn [negb]. cbv iota.
    eapply (fwords Fr Fr A 0 1 (Z_to_bv 64 FL));
      [exact HK | | intros _; exact Fk120 | exact (L_body_k L_epi)].
    refine (conj (munch_refl _ _) (conj (wmono_refl rsegs m) (conj (rd_mono_refl m) (conj MI0 SVm)))).
  Qed.


End SetupFB.

(* ------------------------------------------------------------------------------------------------------------ *)
(* (c) The composition across the call, in the visible form (decisions 19 / 19a; the premises and the conclusion are
   ProgWorld's munch_vis / wmono_vis written out, with B's rsegs).  m0 = the entry memory, m1 = the
   memory at pc_stack_malloc (rcpB_pre_F: munch [(S - 128, S)] m0 m1, wmono), m2 = the memory after the call
   (SetupFB's m), m3 = the memory at the return (Qb: munch Wq m2 m3, wmono).  The call itself contributes its
   visible keep: H is the world's hidden-byte predicate (the glue takes w_H W) and K the bytes the call keeps
   (cgif YG0d.v:297: not aowned under S nor under S', outside the call's window [A - ESTACK, A)).  The result is one
   keep from the entry to the return, for the visible bytes of K outside [S - 128, S) and Wq. *)
Lemma rcpB_keep : forall (H : word -> bool) (K : Z -> Prop) (S : Z) (Wq : list ivl)
    (m0 m1 m2 m3 : word -> option byte),
  munch [(S - 128, S)] m0 m1 ->
  (forall x : word, H x = false -> K (bv_unsigned x) -> mrd rsegs m2 x = mrd rsegs m1 x) ->
  munch Wq m2 m3 ->
  forall x : word, H x = false -> K (bv_unsigned x) -> outside ((S - 128, S) :: Wq) (bv_unsigned x) ->
    mrd rsegs m3 x = mrd rsegs m0 x.
Proof.
  intros H K S Wq m0 m1 m2 m3 M1 KC M3 x Hx Kx Ox. cbn [outside] in Ox. destruct Ox as [O1 O3].
  transitivity (mrd rsegs m2 x).
  - unfold mrd. rewrite (M3 x O3). reflexivity.
  - rewrite (KC x Hx Kx). unfold mrd. rewrite (M1 x) by (cbn [outside]; split; [exact O1 | exact I]). reflexivity.
Qed.

(* The same for writability (wmono of rcpB_pre_F and of Qb, the call's visible wmono). *)
Lemma rcpB_wkeep : forall (H : word -> bool) (m0 m1 m2 m3 : word -> option byte),
  wmono rsegs m0 m1 -> (forall x : word, H x = false -> wview rsegs m1 x <> None -> wview rsegs m2 x <> None) ->
  wmono rsegs m2 m3 ->
  forall x : word, H x = false -> wview rsegs m0 x <> None -> wview rsegs m3 x <> None.
Proof. intros H m0 m1 m2 m3 W1 W2 W3 x Hx Hv. apply W3. apply W2; [exact Hx|]. apply W1. exact Hv. Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
(* (d) The re-based stretch on the REAL memory (decisions.md items 27 / 27a / 27b).  The real memory at the cut
   carries ro_agree, not mem_inv.  SetupFB runs on the normalized memory mn := normalize rsegs m (lib/B/MemNorm.v:34,
   read-only addresses dropped), where mem_inv holds (mem_inv_normalize, MemNorm.v:61) for the store tactics and for
   the in-stretch callees' _F contracts, which are used UNCHANGED; MemNormF.evtF_normalize_ro moves the run to m, and
   the post comes back across ms_rel (MemNorm.v:47-50) as Qbr: Qb with ro_agree in place of mem_inv, over the real
   memory.  One normalize at the stretch base; the shape is that of F13F (
   lib/A/Prog/Seg/F13F.v (at head lib/A/Prog/Seg/F13F.v:241-332; from a working branch 5dbd293c250), f13_evt_ro_F).  The transports are the one home's, lib/B/MemNormF.v and
   lib/B/MemNormTr.v (a working branch 52a6c9e6ecb, merged), stk_normalize_below_img and
   addressable_of_rel included. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import MemNorm MemNormF MemNormTr.
(* route (C): lib.B.ShadowRwOnT.shadow_rw_on_normalize (the shadow_rw_on twin of lib.B.MemNormTr.shadow_rw_normalize)
   for nSR0. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOnT.
(* MemNorm opens bv_scope; this part's numerals are Z's. *)
Open Scope Z_scope.

(* ---- The wrapper: SetupFB's hypotheses at the real memory m (RO0 in place of MI0, and HOro: o's record is at no
   read-only address, AR_client_img_law), SetupFB's run on normalize rsegs m, Qbr at the return.  No lift to the
   world here: the glue lifts the run (rrB_lift, with its hidden-bytes premise, a Theorem Labs lane). ---- *)
Section RoFB.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f n o S : Z) (fr junk : list byte) (RNG : ExecF.footprint) (Fr FL : Z).
  (* route (C): the shadow region the stretch holds at m (SR0), as in SetupFB. *)
  Variable P : Z -> Prop.
  Hypothesis Rf : 0 <= f < 2^64.
  Hypothesis Rn : 0 <= n < 2^64.
  Hypothesis Ro : 0 <= o < 2^64.
  Hypothesis RS : 8800 <= S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis ST0 : stk rsegs m (S - 8800) S.
  (* the real memory carries ro_agree, not mem_inv: source ProgWorldCtlRtC.ctl_rt_C_of_AR (ctl_rt_C's ro_agree_at,
     through ro_agree_of_view); SetupFB's MI0 holds on the normalized memory (mem_inv_normalize) *)
  Hypothesis RO0 : ro_agree rsegs m.
  Hypothesis Lfr : length fr = 50%nat.
  Hypothesis HF : 50 <= n -> 0 < f /\ f + 50 <= 2^64 /\ (f + 50 <= S - 8800 \/ S <= f).
  Hypothesis Hrd : forall i, In i (cp_rd n fr) -> mrd rsegs m (wa (f + Z.of_nat i)) = nth_error fr i.
  Hypothesis HOK : o <> 0 ->
    o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs m o [CB 36 junk] /\
    (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o).
  (* AC0, SR0, the bcmp wrapper's cells below: taken AT m from the world at the cut.  AC0 and SR0 from
     lib.B.ProgWorldCtlRtC.ctl_rt_C_of_AR (from AR with no visibility law), P := cut_shadow lyc S2 \/ img_shadow by
     lib.B.ShadowRwOn.shadow_rw_on_union; the bcmp wrapper's cells from lib.B.ProgBridgeData.ctl_bcmp_cells_of_AR.
     RO0 (above): ro_agree (decisions.md item 27).  ST0 / AW0: the window, from the journal at the cut (win_vis_stmt
     / win_sh_vis_stmt, AR_zshadow_law).  Hrd, HOK, AF0, AO0, ABC (and SVm below): carried over the call by its
     visible keep, munch_vis / wmono_vis of rt_post_frame_vis. *)
  Hypothesis AC0 : asan_cells m.
  Hypothesis SR0 : lib.B.ShadowRwOn.shadow_rw_on P m.
  (* The shadow that P holds (SetupFB's SRFr .. SRbc): the aligned shadow-word span of every range inside the frame,
     f's 50 bytes, o's 36 bytes and .str.4's 6 bytes.  Shadow addresses are not read-only, so SR0 moves to the
     normalized memory unchanged (lib.B.ShadowRwOnT.shadow_rw_on_normalize) and these four do not name memory. *)
  Hypothesis SRFr : forall p k a, Fr <= p -> p + k <= Fr + 128 -> lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Hypothesis SRf : 50 <= n -> forall p k a, f <= p -> p + k <= f + 50 -> lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Hypothesis SRo : o <> 0 -> forall p k a, o <= p -> p + k <= o + 36 -> lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Hypothesis SRbc : forall p k a, REAC_CTRL_PARSE_BC <= p -> p + k <= REAC_CTRL_PARSE_BC + 6 ->
    lib.B.Prog.sh_word_on.sh_word_on p k a -> P a.
  Hypothesis HHM : HIGHMEM_BEG <= S - 8800.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW0 : addressable m (S - 8800) 8800.
  Hypothesis AF0 : 50 <= n -> addressable m f 50.
  Hypothesis AO0 : o <> 0 -> addressable m o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o).
  Hypothesis ABC : addressable m REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)).
  Hypothesis HMEMCMP : bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)).
  Hypothesis HGCF : bytes_at rsegs m GOT_CF (le8 (wa CF)).
  Hypothesis HCF254 : bytes_at rsegs m (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].

  (* ---- The frame of the class-1 request, in the cgif API's stack-malloc form: each hypothesis is the lib/Lib
     image, at the memory m after the call, of one clause of astack_malloc_realizes' post (cgif c8557374ad2e
     lib/YG0d.v:284-298) or of the AR law that clause's frame (1, pos) :: frames S satisfies.  The glue takes
     Fr := frame_addr lyc 1 pos (the post's a0, YG0d.v:293) and FL := flag_addr lyc 1 pos.
       FkAl, FkApp   AR_frames_law (YG0d.v:447-455): frame_addr mod 32 = 0, in_app over fs_frame_bytes 1 = 128.
       FkSt          YG0d.v:296 (frame bytes apresent) + AR_frames_law (not aowned): present, so writable.
       Fk120         YG0d.v:295: rdword (frame_addr + fs_frame_bytes 1 - 8) = Some (flag_addr), the flag word.
       FkLo, FkHi    AR_sep_law (YG0d.v:476-480): 4096 <= frame_addr, frame_addr + 128 <= alloc_ceiling, and the
                     window lies above alloc_ceiling (ly_stk_lo, astk_ok).
       FkImg         AR_client_img_law (YG0d.v:490-495): no frame byte in the image (ly_img).
       FkF, FkO      AR_sep_law: the frame is apart from the caller's blocks and frames, which hold f's 50 bytes and
                     o's 36 bytes ((1, pos) is not in frames S, the call's apath).
       FlSt .. FlO   frame_flag_lawP (cgif YCbq.v): flag_addr present, an application byte, not an image byte, below
                     alloc_ceiling, runtime-owned (so apart from the caller's f and o).
     The side stack is a runtime-owned extent, which the call's keep (YG0d.v:297) does not carry: so these facts
     are taken AT m from the named world statements of ProgWorld (a working branch
     c03ce1627b6 lib/A/ProgWorld.v; B twin lib/B/ProgWorld.v): FkAl FkApp FkSt Fk120 FkImg (ASAN_GT <= fr) from
     ctl_fs_of_astack_stmt 1, with Fr = fs_frame FS 1 pos = frame_addr lyc 1 pos and FL = fs_flag FS 1 pos =
     flag_addr lyc 1 pos by ctl_fs_geom; FlSt (inside stk FS (FS + FS_SIZE)) from ctl_fs_of_AR_stmt; FkLo FkHi FkF FkO
     FlApp FlHi FlImg FlF FlO from the AR laws named above.  Never carried from the entry memory.  No other
     side-stack byte (hint word, other frames' flags) is read after m.  The release (FL := 0 at 0x84294, Qb's last
     conjunct) is the glue's ctl_release_of_free_law_stmt 1.
     YG0d.v:294 (the frame's shadow is zero) is not needed by the run: fwords writes all 16 shadow bytes before any
     read, and their writability is SR0 (shadow_rw_on P, P holding them by SRFr).  YG0d.v:297-298 (bytes kept
     outside the owned bytes and the call's window, the window present) are what the glue uses to carry the caller's
     facts above to m. ---- *)
  Hypothesis FkAl : Fr mod 32 = 0.
  Hypothesis FkApp : forall i, 0 <= i < 128 -> app_mem (Fr + i).
  Hypothesis FkSt : stk rsegs m Fr (Fr + 128).
  Hypothesis Fk120 : bytes_at rsegs m (Fr + 120) (le8 (Z_to_bv 64 FL)).
  Hypothesis FkLo : 4096 <= Fr.
  Hypothesis FkHi : Fr + 128 <= S - 8800.
  Hypothesis FkImg : rcpB_dj Fr 128 ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO).
  Hypothesis FkF : 50 <= n -> rcpB_dj f 50 Fr 128.
  Hypothesis FkO : o <> 0 -> rcpB_dj o 36 Fr 128.
  Hypothesis FlSt : stk rsegs m FL (FL + 1).
  Hypothesis FlApp : app_mem FL.
  Hypothesis FlHi : FL + 1 <= S - 8800.
  Hypothesis FlImg : rcpB_dj FL 1 ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO).
  Hypothesis FlF : 50 <= n -> rcpB_dj f 50 FL 1.
  Hypothesis FlO : o <> 0 -> rcpB_dj o 36 FL 1.

  (* ---- The footprint premises of the run, as reac_ctrl_parseF.v's (quantified shadow covers), with the frame's
     128 bytes, their shadow and the flag byte in place of the side stack's ranges. ---- *)
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 8800) 8800.
  Hypothesis SCW : shcov RNG (S - 8800) 8800.
  Hypothesis SKW : shkov RNG (S - 2560) 2432.
  Hypothesis RINF : 50 <= n -> rng RNG f 50.
  Hypothesis SCF : 50 <= n -> shcov RNG f 50.
  Hypothesis SKF : 50 <= n -> shkov RNG f 50.
  Hypothesis ROUT : o <> 0 -> rng RNG o 36.
  Hypothesis SCO : o <> 0 -> shcov RNG o 36.
  Hypothesis SKO : o <> 0 -> shkov RNG o 36.
  Hypothesis RBC : rng RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFk : rng RNG Fr 128.
  Hypothesis SCFk : shcov RNG Fr 128.
  Hypothesis SKFk : shkov RNG Fr 128.
  Hypothesis RFl : rng RNG FL 1.
  Hypothesis SVm : rw_cells rsegs m (S - 96)
    [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis HOro : o <> 0 -> forall i, 0 <= i < 36 -> ro_addr rsegs (wa (o + i)) = false.
  (* the in-stretch callees, used unchanged on the normalized memory; route (C): their _on forms, as in SetupFB *)
  Hypothesis MSET : asan_memset_contract_F_on.
  Hypothesis MCPY : asan_memcpy_contract_F_on.
  Hypothesis BWRP : bcmp_wrap_contract_F_on.
  Hypothesis KOL : kind_of_link1_contract_F.

  (* Qb over the real memory, with ro_agree in place of mem_inv (posts carry ro_agree, never mem_inv). *)
  Definition Qbr : machine_state -> Prop :=
    fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (Z_to_bv 64 S) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (fst (ctrlparse n fr)))
                    a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom rsegs) /\
      munch (Wq o S Fr FL) m m' /\ wmono rsegs m m' /\ rd_mono m m' /\ ro_agree rsegs m' /\
      stk rsegs m' (S - 8800) S /\ (o <> 0 -> rw_cells rsegs m' o [CB 36 (snd (ctrlparse n fr))]) /\
      addressable m' (S - 8800) 8800 /\ mrd rsegs m' (wa FL) = Some (Z_to_bv 8 0).

  Lemma rcpB_post_F_ro : forall (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x24 x26 x28 x29 x30 x31 : word),
    evtF rsegs RNG Qbr
      (MS (mkR x1 (Z_to_bv 64 (A S)) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 (A S)) (Z_to_bv 64 Fr)
               x11 x12 x13 x14 x15 x16 x17 x18 x19 (Z_to_bv 64 o) (Z_to_bv 64 f) (Z_to_bv 64 n)
               x23 x24 (wa ASAN_K) x26 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x83e78) fc None m (seg_rom rsegs)).
  Proof.
    intros x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x19 x23 x24 x26 x28 x29 x30 x31.
    pose proof (mem_rel_normalize rsegs m RO0) as REL.
    set (mn := normalize rsegs m) in *.
    pose proof HHM as HHM'. pose proof HAE as HAE'. unfold HIGHMEM_BEG, APPMEM_END in HHM', HAE'.
    assert (RQhi : forall x, ImgBounds.IMG_HI <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false)
      by exact ro_addr_above_img.
    assert (HIw : ImgBounds.IMG_HI <= S - 8800) by (unfold ImgBounds.IMG_HI; lia).
    (* the frame and its flag byte: above the image (stk_normalize_ro) or below it (stk_normalize_below_img) *)
    assert (nstk : forall lo hi, rcpB_dj lo (hi - lo) ImgBounds.IMG_LO (ImgBounds.IMG_HI - ImgBounds.IMG_LO) ->
                     0 <= lo <= hi -> stk rsegs m lo hi -> stk rsegs mn lo hi).
    { intros lo hi HI Hlo H. unfold rcpB_dj in HI. destruct HI as [HI|HI].
      - apply (stk_normalize_below_img m lo hi RO0); [lia | lia | exact H].
      - apply (stk_normalize_ro m lo hi RO0); [lia | exact H]. }
    (* SetupFB's hypotheses on the normalized memory *)
    assert (nST0 : stk rsegs mn (S - 8800) S) by exact (stk_normalize_ro m _ _ RO0 HIw ST0).
    assert (nMI0 : mem_inv rsegs mn) by exact (mem_inv_normalize rsegs m).
    assert (nHrd : forall i, In i (cp_rd n fr) -> mrd rsegs mn (wa (f + Z.of_nat i)) = nth_error fr i)
      by (intros i Hi; rewrite <- (mrd_rel rsegs m mn _ REL); exact (Hrd i Hi)).
    assert (nHOK : o <> 0 ->
      o mod 4 = 0 /\ o + 36 <= 2^64 /\ rw_cells rsegs mn o [CB 36 junk] /\
      (o + 36 <= S - 8800 \/ S <= o) /\ (50 <= n -> o + 36 <= f \/ f + 50 <= o)).
    { intros Ho. destruct (HOK Ho) as (H1 & H2 & H3 & H4 & H5).
      split; [exact H1|]. split; [exact H2|]. split; [|split; [exact H4 | exact H5]].
      apply (rw_cells_normalize m o _ RO0); [|exact H3].
      intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply (HOro Ho). lia. }
    assert (nAC0 : asan_cells mn) by exact (asan_cells_normalize m RO0 AC0).
    assert (nSR0 : lib.B.ShadowRwOn.shadow_rw_on P mn)
      by exact (lib.B.ShadowRwOnT.shadow_rw_on_normalize P m RO0 SR0).
    assert (nAW0 : addressable mn (S - 8800) 8800) by exact (addressable_normalize m _ _ RO0 AW0).
    assert (nAF0 : 50 <= n -> addressable mn f 50) by (intros H; exact (addressable_normalize m _ _ RO0 (AF0 H))).
    assert (nAO0 : o <> 0 -> addressable mn o 36 /\ app_mem (o + 36) /\ (o + 36 <= GOT_CF \/ CF + 256 <= o)).
    { intros H. destruct (AO0 H) as (H1 & H2 & H3). exact (conj (addressable_normalize m _ _ RO0 H1) (conj H2 H3)). }
    assert (nABC : addressable mn REAC_CTRL_PARSE_BC 6) by exact (addressable_normalize m _ _ RO0 ABC).
    assert (nHBCMP : bytes_at rsegs mn REAL_BCMP (le8 (wa BCMP))) by exact (bytes_at_normalize rsegs m _ _ RO0 HBCMP).
    assert (nHMEMCMP : bytes_at rsegs mn REAL_MEMCMP (le8 (wa MEMCMP)))
      by exact (bytes_at_normalize rsegs m _ _ RO0 HMEMCMP).
    assert (nHGCF : bytes_at rsegs mn GOT_CF (le8 (wa CF))) by exact (bytes_at_normalize rsegs m _ _ RO0 HGCF).
    assert (nHCF254 : bytes_at rsegs mn (CF + 254) [Z_to_bv 8 1]) by exact (bytes_at_normalize rsegs m _ _ RO0 HCF254).
    assert (nHCF255 : bytes_at rsegs mn (CF + 255) [Z_to_bv 8 1]) by exact (bytes_at_normalize rsegs m _ _ RO0 HCF255).
    assert (nFkSt : stk rsegs mn Fr (Fr + 128)).
    { apply nstk; [replace (Fr + 128 - Fr) with 128 by lia; exact FkImg | lia | exact FkSt]. }
    assert (nFk120 : bytes_at rsegs mn (Fr + 120) (le8 (Z_to_bv 64 FL))) by exact (bytes_at_normalize rsegs m _ _ RO0 Fk120).
    assert (nFlSt : stk rsegs mn FL (FL + 1)).
    { pose proof FlSt as (FLb & _).
      apply nstk; [replace (FL + 1 - FL) with 1 by lia; exact FlImg | lia | exact FlSt]. }
    assert (nSVm : rw_cells rsegs mn (S - 96)
                     [C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (rw_cells_normalize m _ _ RO0); [|exact SVm].
      intros i Hi. cbn [cells_size csize Nat.add] in Hi. apply RQhi. lia. }
    (* the run on the normalized memory, moved to m *)
    eapply evtF_mono.
    { eapply (evtF_normalize_ro RNG); [exact RO0|].
      eapply (rcpB_post_F ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mn f n o S fr junk RNG Fr FL P);
        assumption. }
    (* the post back to the real memory *)
    intros ms (s0' & HQ & Hrel & Hros).
    destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0'
                    & E & MU & WM & RM & MI' & ST' & HREC & AW' & HFL).
    subst s0'.
    destruct ms as [regsX frX pcX svcX rvX fcX memX romX].
    destruct Hrel as (HR & HF' & Hpc & Hsvc & Hres & Hfc & Hrom & Hmr).
    cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom MS]
      in HR, HF', Hpc, Hsvc, Hres, Hfc, Hrom, Hmr, Hros.
    subst regsX frX pcX svcX rvX fcX romX.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', memX.
    split; [reflexivity|].
    split; [exact (munch_rel rsegs _ m mn memX m0' REL Hmr Hros MU)|].
    split; [exact (wmono_rel rsegs m mn memX m0' REL Hmr Hros WM)|].
    split.
    { intros x (b & Hb). rewrite (mrd_rel rsegs memX m0' _ Hmr). apply RM. exists b.
      rewrite <- (mrd_rel rsegs m mn _ REL). exact Hb. }
    split; [exact (ro_agree_of_mem_rel rsegs memX m0' Hmr)|].
    split; [exact (stk_of_rel memX m0' _ _ Hmr ST')|].
    split; [intros Ho; exact (rw_cells_of_rel memX m0' _ _ Hmr (HREC Ho))|].
    split; [exact (addressable_of_rel memX m0' _ _ Hmr AW')|].
    rewrite (mrd_rel rsegs memX m0' _ Hmr). exact HFL.
  Qed.
End RoFB.
