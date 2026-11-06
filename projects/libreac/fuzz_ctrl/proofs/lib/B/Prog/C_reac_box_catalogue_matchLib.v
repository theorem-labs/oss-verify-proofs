(* reac_box_catalogue_match (0x84e40) of fuzz_ctrl's ASan+UBSan build (image B, libreac v1.9.0): the stretches of the
   proved footprint run lib/B/Prog/reac_box_catalogue_matchF_on.v (route (C): the `_on` copy of the accepted run
   reac_box_catalogue_matchF.v (not in this delivery), same lemma names, Section hypothesis SRo : shadow_rw_on R m for
   R := reac_box_catalogue_match_shadow_R f len Sp FS), each RE-BASED on its own base memory mb, at the glue
   level, so that the cgif-form walk (C_reac_box_catalogue_match.v) can lift each stretch and apply a world rule at
   each allocator event (brief REBASE-BRIEF.md (a working note, not in this delivery); rulings
   decisions.md items 24, 26, 27a, 27b, 28 (a working note, not in this delivery); measurement
   munch-consumers.md section 2.1, row group B1 (a working note, not in this delivery)).  rule 24: no function
   proved; this file re-states green lemmas of this lane's own proof at a different memory.

   THE SHAPE.  Each stretch lemma APPLIES the existing lemma of reac_box_catalogue_matchF_on.v (after End MatchF it is
   quantified over Section MatchF's memory m and its single-memory hypotheses) at m := MemNorm.normalize rsegs mb,
   where MemNorm.mem_inv_normalize gives Section MatchF's `mem_inv rsegs m` (decisions.md item 27a: mem_inv over all
   bytes does not hold at a real memory).  Every entry-relative premise becomes reflexive (munch_refl, wmono_refl).
   The run on normalize mb comes back to the real memory mb through image B's MemNormF.evtF_normalize_ro (stretch 6
   through MemNormF.evtF_rel_ro: its start memory is the release store's write over mb, not a normalized memory),
   and its post through MemNorm.munch_rel / wmono_rel / ro_agree_of_mem_rel and MemNormTr's *_of_rel (the shadow
   region facts through B.ShadowRwOnT.shadow_rw_on_rel / _of_rel / _normalize): the same
   composition as a Theorem Labs lane's rebase_ro_normalize_stmt (decisions.md item 28 (a working note, not in this delivery); provisional (stand-ins) on A at
   a working branch 7f07ac65e7b; its B twin is lib/B/ProgWorld.v:821, proved at :844; it is not used by name).  Each post is relative
   to mb and states ro_agree of the real final memory, never mem_inv.  No proof is copied.

   NO SECTION HYPOTHESES.  The normalize lemmas are image B's own, Required: lib/B/MemNormF.v and lib/B/MemNormTr.v
   (a working branch 0fa3ec38d61, twins of A's files of the same names).  The one
   callee contract a stretch uses, bcmp_wrap_c_on.bcmp_wrap_contract_F_on (stretch 4, inside the row's compare; owner
   a Theorem Labs lane, lib/B/Prog/bcmp_wrap_c_on.v), is a premise of that lemma.

   CTRL VOCABULARY ONLY (rsegs, evtF).  The world-to-ctrl step (AR, ly, S, W) belongs to the glue proof
   pb_reac_box_catalogue_match, and decisions.md item 15 keeps frame-route identifiers out of a glue file's Section
   hypotheses; so no ProgWorld statement is a hypothesis here.  Each base fact is a single-memory clause at mb, named
   below with the ProgWorld statement that supplies it.

   THE STRETCHES (cut lemmas of reac_box_catalogue_matchF_on.v):
     1  entry 0x84e40 -> the __asan_stack_malloc_2 call (pc 252408)          cmRB_pre_sm2        <- cm_pre_sm2
     2  class-2 return (pc 544436) -> gate -> reac_ctrl_parse call / exit    cmRB_post_sm2_side  <- cm_post_sm2_side,
                                                                                                     cm_pre_parse
     3  parse return (pc 0x85058) -> row 0's model_block call / exit         cmRB_post_parse     <- cm_post_parse_K
     4  model_block return (pc 0x8509c), row i -> row S i's call / exit      cmRB_post_mb        <- cm_post_mb_K
     5  exit (pc 0x850fc) -> the flag store (pc 0x85194)                     cmRB_pre_rel        <- cm_pre_rel
     6  after the store (pc 0x85198) -> ret                                  cmRB_post_rel       <- cm_post_rel
   (cm_post_parse_K and cm_post_mb_K: a working branch 077bb7bcf14.)  Stretches 3 to 6 are
   stated for any frame arm nn; the glue uses nn = 1 only (the a0 = 0 arm of the class-2 request is dead in cgif
   form, C_reac_box_catalogue_match.v), where clause (2) holds at every base.

   CLAUSE MAP of cmBase mb tp f len Sp FS fb, for the glue to close one for one at each stretch base.  Owner of
   every B twin: a Theorem Labs lane's lib/B/ProgWorld.v, twin of a Theorem Labs lane's lib/A/ProgWorld.v; state on image A at
   a working branch 7f07ac65e7b.  Image-A files are NOT Required here; each clause swaps for its B
   twin when that sha lands.
     (1)  asan_cells mb /\ shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) mb /\ MemNorm.ro_agree rsegs mb
            <- route (C): C_reac_box_catalogue_matchPfV.cmPf_shrwR_of_AR (the region from ctl_rt_C_of_AR, no
               AR_states_vis0_shadow) and ProgWorldCtlRtC.ctl_rt_C_of_AR's asan_cells and ro_agree conjuncts.
          The posts carry the run's region transport relative to the base, forall P, shadow_rw_on P mb ->
          shadow_rw_on P m' (the `_on` run's cmSRT at its normalized base, moved back by shadow_rw_on_rel / _of_rel).
     (2)  addressable mb (Sp - 9136) 9136
            <- ctl_stack_shadow_of_AR_stmt at lo := Sp - 9136, len := 9136 (its range premises are astk_ok's
               ly_stk_lo ly <= Sp - 9136 and Sp <= ly_stk_hi ly).  STATEMENT ONLY on A (in the file since 7f07ac65e7b).
     (3)  fp [0; 1; 2] mb (bv_unsigned tp) FS (Sp - 9136) Sp W D, with fs_place's stk [FS, FS + FS_SIZE) and fp_cls's
          hint words and flag bytes
            <- ctl_fp_of_AR_stmt; the stk, flag and hint parts are also ctl_fs_of_AR_stmt's conclusions.  Both
               provisional (stand-ins) on A (lib/A/ProgWorld_Fs.v, owner a Theorem Labs lane).
     (4)  cmRB_tls_dj mb tp FS Sp (= reac_box_catalogue_match_tls mb (bv_unsigned tp) FS (Sp - 9136) Sp)
            <- the thread cells: ctl_tls_of_AR_stmt (asan_tls_cells pins DT .. k), STATEMENT ONLY on A; their
               disjointness from fp_w and the window's shadow: a Theorem Labs lane's PROPOSED fp_tls_owned_stmt
               `fp_tls_owned_stmt B := CtrlTSyms B -> forall ly S W m md, AR segs B ly S W m md -> forall a, (a in
               some fp_tls range) -> aowned B ly S a` (fp_dj follows for any awr bytes, since awr_byte -> ~ aowned).
     (5)  aCL mb (REAL_BCMP, REAL_MEMCMP, GOT_CF, CF + 254, CF + 255)
            <- RT_used_of_AR_stmt (decisions.md item 29).  STATEMENT ONLY on A.
     (6)  50 <= len -> bytes_at rsegs mb f fb /\ addressable mb f 50
            <- the spec's live-block premises (C_reac_box_catalogue_match.v:87-88) and ctl_block_shadow_of_AR_stmt
               (provisional (stand-ins) on A: A.ProgWorldShadow.ctl_block_shadow_of_AR, a working branch
               1f8c45f4527).
     (7)  bytes_at rsegs mb CM_T CM_TBL
            <- the image: [CM_T, CM_T + 3256) is read-only data, where (1)'s ro_agree gives mrd = seg_rom.
     (8)  cmRB_tbl_addr mb (= addressable mb CM_T 3256)
            <- ONE named hypothesis citing ctl_zshadow_of_AR_stmt (provisional (stand-ins) on A:
               A.ProgWorldShadow.ctl_zshadow_of_AR), NOT wired to it: whether BOX_CATALOGUE is a corrected zero-shadow
               row is open for image A.  Only the data range [0x9f620, 0xa02d8); the redzone [0xa02d8, 0xa0600) is
               poisoned and is never claimed.
     (9)  cmRB_bc_addr mb (= addressable mb REAC_CTRL_PARSE_BC 6)
            <- a Theorem Labs lane's PROPOSED ctl_gshadow_of_AR_stmt `ctl_gshadow_of_AR_stmt B := CtrlTSyms B -> AR_laws segs B
               -> forall ly S W m md g k lo len, AR segs B ly S W m md -> In (z1 (ANum (shadow_addr g)) k)
               (Tfib_const ly) -> g mod 8 = 0 -> 0 < k < 8 -> g <= lo -> 0 <= len -> lo + len <= g + k ->
               AsanRT.addressable m lo len` at .str.4 (g = 0x21200, k = 7, len 6).  Its data needs a Theorem Labs lane's corrected
               shadow const rows; not derivable today.
   THE WINDOW `stk rsegs mb (Sp - 9136) Sp` is not in cmBase; each stretch states it in the form its base supplies:
     stretch 1 (the entry): the spec's P1 window premises (astk_ok CM_STK and apresent over [sp - CM_STK, sp),
       C_reac_box_catalogue_match.v:80-81).
     stretch 2 (after the class-2 request at sp = CA): below CA, ctl_fs_of_astack's `stk mem' lo (spZ regs)` at
       lo := Sp - 9136; above CA, cmRB_win_kept m1 mb Sp, the window [CA, Sp) kept byte for byte from the request
       memory m1, with stk over it at m1 (stretch 1's post).  Derivation: the stack lies above alloc_ceiling
       (layout_ok lo_stk_ceil: ASAN_CEIL <= ly_stk_lo) and is never owned (YG0d.v:469-470), so the request's frame
       condition (the amended ctl_fs_of_astack premise, YG0d.v:298-299) keeps its view outside [CA - ESTACK, CA);
       off the image at a visible address an aview equality is a raw byte equality (aview = mbyte (mrestrict H mem),
       seg_rom None there).  ProgWorld proves it as a Theorem Labs lane's helper (lib/B/ProgWorld.v:1187, without the `~ in_img` premise) in place of the PROPOSED `ctl_kept_of_view_eq : forall H m m'
       C, (forall x, H x = false -> C (bv_unsigned x) -> ~ in_img segs (bv_unsigned x) -> aview segs H m'
       (bv_unsigned x) = aview segs H m (bv_unsigned x)) -> ctl_kept_vis H m m' C /\ ctl_wmono_vis_off_img H m m'
       C` (ctl_kept_vis, ctl_wmono_vis_off_img: lib/B/ProgWorld.v:942 / :946, also in a Theorem Labs lane's lib/B/Prog/C_reac_ctrl_identity_replyPost.v (not in this delivery),
       a working branch 1df58ed9045).
     stretches 3, 4 (after a walked callee with window [lo, sp2): reac_ctrl_parse lo = sp2 - 8800, reac_box_model_block
       lo = sp2 - 4272): inside [lo, sp2), the callee's post (its stk over its own window); outside it, the window
       kept byte for byte from the call memory m1 (cmRB_kept m1 mb (cmRB_callee_kept ..)), with stk at m1 (the
       previous stretch's end).  Source of the kept bytes: the callee's post keeps every visible byte outside its
       writes (munch_vis), the window being visible (win_vis); off the image that is a raw byte equality, as above.
     stretches 5, 6: the same run (the exit's cmRB_J; cmRB_AtRel at the store memory).
   STRETCH PREMISES at the base (not ProgWorld clauses):
     cmRB_Fs2 (stretch 2), with fr = fs_frame FS 2 j: 0 <= j < fs_M 2, fr mod 64 = 0, the flag byte 1, the flag word at
      fr + 248, the 32 zero shadow bytes <- ctl_fs_of_astack_stmt 2, the amended statement (by a Theorem Labs lane, written on a working branch 878cb7afbc4, it
      gains, after its [sp - ESTACK, sp) presence premise, the request's frame condition YG0d.v:298-299; conclusions
      unchanged; provisional (stand-ins) on A: lib/A/ProgWorldAstack.v, a working branch d447ec8f286).
      Stretch 2's 13 saves at [Sp - 104, Sp) are stretch 1's (rw_cells at m1, cmRB_AtSM2), carried by cmRB_win_kept.
      The release store between stretches 5 and 6 is the glue's world rule, ctl_release_of_free_law_stmt
      (provisional (stand-ins) on A in the same lib/A/ProgWorldAstack.v).
     stretches 3, 4: at the call memory m1, the previous stretch's end (cmFK, the window's stk, the 13 saves, the flag
       word, the buffer's addressable range: cmRB_parse_at / cmRB_mb_call); at the return memory mb, the callee's
       post through the bridge the glue plan names (C_reac_box_catalogue_match.v: TPARSE + ctl_post_reac_ctrl_parse,
       TMB + ctl_post_reac_box_model_block): its window's stk and its output (reac_ctrl_parse: rw_cells (fr + 32)
       [CB 36 (snd (ctrlparse len fb))], a0 = fst (ctrlparse len fb); reac_box_model_block: bytes_at (fr + 112)
       (synth (cm_row i) 0 []) and a0 = rc (cm_row i) 0, which cm_rc turns into nth i DECLS [] and 1); and the kept
       bytes cmRB_callee_kept (the window outside the callee's window, the flag word [fr + 248, fr + 256), the
       buffer's shadow bytes; the frame and its shadow are visible by frame_vis).  cmRB_callee_base moves them to mb.
     cmRB_Fr (stretches 5, 6): cmFK; the saves and the flag word <- the same run: stretch 5 from the exit's cmRB_J,
       stretch 6 from stretch 5's premises, kept by stretch 5's munch (which avoids [Sp - 104, Sp) and
       [fr + 248, fr + 256)).
   The guards of the guarded stk transport (B's MemNormTr.stk_normalize_ro, a working branch
   0fa3ec38d61; the unguarded form is false, MemNormTr.stk_normalize_ro_unguarded_false): for the window, the named
   lemma cmRB_win_above_img at every site, through cmRB_stk_normalize; for fp's side stack, MemNormTr.fp_FS_above_img
   inside MemNormTr.fp_transport / fp_normalize.  The
   not-read-only facts this file needs (the saves, the flag byte, the parse buffer) come from wview at the normalized
   memory (MemNorm.ro_false_of_wview), never from app_mem. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Bytes
  ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_catalogue_match reac_box_catalogue_matchF_on.
(* route (C): the region form, its transports, and the bcmp wrapper's `_on` contract (stretch 4) *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The guard of the guarded stk transport for the window: it lies above the image, so no byte there is read-only. *)
Lemma cmRB_win_above_img : forall Sp, HIGHMEM_BEG <= Sp - 9136 -> ImgBounds.IMG_HI <= Sp - 9136.
Proof. intros Sp H. unfold HIGHMEM_BEG in H. unfold ImgBounds.IMG_HI. lia. Qed.

(* The guarded stk transport, under one name of this file: B's MemNormTr.stk_normalize_ro.  Every call site
   discharges the guard with cmRB_win_above_img. *)
Lemma cmRB_stk_normalize : forall m lo hi, MemNorm.ro_agree rsegs m -> ImgBounds.IMG_HI <= lo ->
  lib.Lib.Frame.stk rsegs m lo hi -> lib.Lib.Frame.stk rsegs (MemNorm.normalize rsegs m) lo hi.
Proof. exact MemNormTr.stk_normalize_ro. Qed.

(* A sub-window of a stk window. *)
Lemma cmRB_stk_sub : forall (m : word -> option byte) lo hi lo' hi', lib.Lib.Frame.stk rsegs m lo hi -> lo <= lo' -> hi' <= hi ->
  lib.Lib.Frame.stk rsegs m lo' hi'.
Proof. intros m lo hi lo' hi' (H1 & H2 & H) A B. split; [lia|]. split; [lia|]. intros a Ha. apply H. lia. Qed.

(* Two stk windows side by side are one. *)
Lemma cmRB_stk_join : forall (m : word -> option byte) lo mid hi, lib.Lib.Frame.stk rsegs m lo mid -> lib.Lib.Frame.stk rsegs m mid hi ->
  lib.Lib.Frame.stk rsegs m lo hi.
Proof.
  intros m lo mid hi (A0 & A1 & A) (B0 & B1 & B). split; [lia|]. split; [lia|].
  intros a Ha. destruct (Z.lt_ge_cases a mid); [apply A | apply B]; lia.
Qed.

(* ---- a range kept byte for byte keeps its readable and writable view ---- *)
Lemma cmRB_wview_keep : forall (m m' : word -> option byte) a, m' a = m a -> wview rsegs m' a = wview rsegs m a.
Proof. intros m m' a H. unfold wview. rewrite H. reflexivity. Qed.

Lemma cmRB_mrd_keep : forall (m m' : word -> option byte) a, m' a = m a -> lib.Lib.Mem.mrd rsegs m' a = lib.Lib.Mem.mrd rsegs m a.
Proof. intros m m' a H. unfold lib.Lib.Mem.mrd. rewrite H. reflexivity. Qed.

Lemma cmRB_stk_keep : forall (m m' : word -> option byte) lo hi,
  (forall a, lo <= a < hi -> m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a)) -> lib.Lib.Frame.stk rsegs m lo hi -> lib.Lib.Frame.stk rsegs m' lo hi.
Proof.
  intros m m' lo hi K (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  rewrite (cmRB_wview_keep m m' _ (K a Ha)), (cmRB_mrd_keep m m' _ (K a Ha)). exact (H a Ha).
Qed.

Lemma cmRB_rw_cells_keep : forall (m m' : word -> option byte) A cs,
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) -> m' (lib.Lib.Mem.wa (A + i)) = m (lib.Lib.Mem.wa (A + i))) ->
  lib.Lib.Step.rw_cells rsegs m A cs -> lib.Lib.Step.rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs K [[Hwf (B0 & B1 & B)] (W0 & W1 & W)].
  pose proof (lib.Lib.Cells.cells_bytes_length cs Hwf) as EL.
  split; [split; [exact Hwf|] |].
  - split; [exact B0|]. split; [exact B1|]. intros i Hi.
    rewrite (cmRB_mrd_keep m m' _ (K (Z.of_nat i) ltac:(rewrite <- EL; lia))). exact (B i Hi).
  - split; [exact W0|]. split; [exact W1|]. intros i Hi.
    rewrite (cmRB_wview_keep m m' _ (K i Hi)). exact (W i Hi).
Qed.

Lemma cmRB_bytes_keep : forall (m m' : word -> option byte) A bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> m' (lib.Lib.Mem.wa (A + i)) = m (lib.Lib.Mem.wa (A + i))) ->
  lib.Lib.Mem.bytes_at rsegs m A bs -> lib.Lib.Mem.bytes_at rsegs m' A bs.
Proof.
  intros m m' A bs K (B0 & B1 & B). split; [exact B0|]. split; [exact B1|]. intros i Hi.
  rewrite (cmRB_mrd_keep m m' _ (K (Z.of_nat i) ltac:(lia))). exact (B i Hi).
Qed.

Lemma cmRB_sh_mono : forall a b, a <= b -> shadow_addr a <= shadow_addr b.
Proof. intros a b H. unfold shadow_addr. pose proof (Z.div_le_mono a b 8 ltac:(lia) H). lia. Qed.

(* addressable reads only the shadow bytes of its range. *)
Lemma cmRB_addr_keep : forall (m m' : word -> option byte) p n,
  (forall a, shadow_addr p <= a <= shadow_addr (p + n - 1) -> m' (lib.Lib.Mem.wa a) = m (lib.Lib.Mem.wa a)) ->
  addressable m p n -> addressable m' p n.
Proof.
  intros m m' p n K (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  rewrite (cmRB_mrd_keep m m' _ (K _ (conj (cmRB_sh_mono p (p + i) ltac:(lia))
                                           (cmRB_sh_mono (p + i) (p + n - 1) ltac:(lia))))).
  exact Hb.
Qed.

Lemma cmRB_addressable_sub : forall (m : word -> option byte) p n p' n', addressable m p n -> p <= p' -> 0 <= n' ->
  p' + n' <= p + n -> addressable m p' n'.
Proof.
  intros m p n p' n' (H0 & H1 & H2 & H) A B C. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (p' + i) with (p + (p' - p + i)) by lia. apply H. lia.
Qed.

(* ---- arithmetic of the frame pointer and of the class-2 side-stack frame ---- *)
Lemma cmRB_CA : forall Sp, Sp mod 16 = 0 -> Sp - 144 <= CA Sp <= Sp - 128.
Proof. intros Sp H. unfold CA. Z.div_mod_to_equations. lia. Qed.

Lemma cmRB_fr_in_fs : forall FS j, 0 <= j < fs_M 2 ->
  FS <= fs_frame FS 2 j /\ fs_frame FS 2 j + 256 <= FS + FS_SIZE.
Proof.
  intros FS j Hj. change (fs_M 2) with 4096 in Hj. unfold fs_frame, FS_SIZE.
  change (fs_B 2) with 256. change (Z.of_nat 2 * 2 ^ 20) with 2097152. lia.
Qed.

Lemma cmRB_flag_in_fs : forall FS j, 0 <= j < fs_M 2 -> FS <= fs_flag FS 2 j < FS + FS_SIZE.
Proof.
  intros FS j Hj. change (fs_M 2) with 4096 in Hj. unfold fs_flag, FS_SIZE.
  change (2 ^ 15) with 32768. change (2 ^ (15 - Z.of_nat 2)) with 8192. lia.
Qed.

Lemma cmRB_fsBM : forall c, (c <= 10)%nat -> fs_B c * fs_M c = 1048576 /\ 64 <= fs_B c.
Proof.
  intros c Hc.
  do 11 (destruct c as [|c]; [split; [reflexivity | vm_compute; discriminate] |]).
  lia.
Qed.

(* The class-2 frame j is apart from every other frame of classes 0 .. 10 (the request's frame clause). *)
Lemma cmRB_fs2_disj : forall FS j, 0 <= j < fs_M 2 ->
  forall (c' : nat) (j' : Z), (c' <= 10)%nat -> 0 <= j' < fs_M c' -> (c' <> 2%nat \/ j' <> j) ->
    fs_frame FS c' j' + fs_B c' <= fs_frame FS 2 j \/ fs_frame FS 2 j + 256 <= fs_frame FS c' j'.
Proof.
  intros FS j Hj c' j' Hc Hj' Hne.
  change (fs_M 2) with 4096 in Hj. unfold fs_frame. change (fs_B 2) with 256. change (2 ^ 20) with 1048576.
  destruct (Nat.eq_dec c' 2) as [->|Hn].
  - change (fs_B 2) with 256. change (fs_M 2) with 4096 in Hj'.
    destruct Hne as [Hne|Hne]; [exfalso; exact (Hne eq_refl)|]. lia.
  - destruct (cmRB_fsBM c' Hc) as (EBM & HB).
    assert (Hlt : (c' < 2 \/ 2 < c')%nat) by lia.
    destruct Hlt as [Hlt|Hlt].
    + left. assert (Hc1 : Z.of_nat c' <= 1) by lia. nia.
    + right. assert (Hc3 : 3 <= Z.of_nat c') by lia. nia.
Qed.

(* ---- moving single-memory facts between two memories (compositions of B/MemNorm.v) ---- *)
(* addressable back from a related memory (A's lib/A/MemNormTr.v has no addressable_of_rel). *)
Lemma cmRB_addr_byte_of_rel : forall m m0 x, MemNorm.mem_rel rsegs m m0 -> addr_byte m0 x -> addr_byte m x.
Proof.
  intros m m0 x REL (Ha & b & Hb & Hok). split; [exact Ha|]. exists b. split; [|exact Hok].
  rewrite (MemNorm.mrd_rel rsegs m m0 _ REL). exact Hb.
Qed.

Lemma cmRB_addressable_of_rel : forall m m0 p n, MemNorm.mem_rel rsegs m m0 -> addressable m0 p n ->
  addressable m p n.
Proof.
  intros m m0 p n REL (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. exact (cmRB_addr_byte_of_rel m m0 _ REL (H i Hi)).
Qed.

Lemma cmRB_awx : forall Sp fr mc, addressable mc (Sp - 9136) 9136 -> AWX Sp fr mc.
Proof.
  intros Sp fr mc (_ & _ & _ & H) x Hx _. replace x with (Sp - 9136 + (x - (Sp - 9136))) by lia. apply H. lia.
Qed.

Lemma cmRB_ms_rel_MS : forall R F pc fc rv (m m0 : word -> option byte) ro, MemNorm.mem_rel rsegs m m0 ->
  MemNorm.ms_rel rsegs (lib.Lib.MState.MS R F pc fc rv m ro) (lib.Lib.MState.MS R F pc fc rv m0 ro).
Proof.
  intros R F pc fc rv m m0 ro H.
  exact (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl H))))))).
Qed.

(* Feed a lemma of reac_box_catalogue_matchF_on.v every leading Prop premise found in the context (it stops at the
   first binder over data, e.g. the registers). *)
Ltac cmRB_feed H :=
  repeat match type of H with
         | ?A -> _ => lazymatch type of A with Prop => specialize (H ltac:(assumption)) end
         end.

(* ------------------------------------------------------------------------------------------------------------ *)
(* The base facts.  (8) is the ONE named hypothesis of the catalogue's shadow; (4) and (9) are named after their
   proposed ProgWorld sources. *)
Definition cmRB_tbl_addr (mb : word -> option byte) : Prop := addressable mb CM_T 3256.
Definition cmRB_bc_addr (mb : word -> option byte) : Prop := addressable mb REAC_CTRL_PARSE_BC 6.
Definition cmRB_tls_dj (mb : word -> option byte) (tp : word) (FS Sp : Z) : Prop :=
  reac_box_catalogue_match_tls mb (bv_unsigned tp) FS (Sp - 9136) Sp.

Definition cmBase (mb : word -> option byte) (tp : word) (f len Sp FS : Z) (fb : list byte) : Prop :=
  (* (1) route (C): the run's region R at mb (C_reac_box_catalogue_matchPfV.cmPf_shrwR_of_AR) *)
  (asan_cells mb /\ shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) mb /\ MemNorm.ro_agree rsegs mb) /\
  (* (2) ctl_stack_shadow_of_AR *)
  addressable mb (Sp - 9136) 9136 /\
  (* (3) ctl_fp_of_AR (with ctl_fs_of_AR's stk, flags and hints inside) *)
  fp [0%nat; 1%nat; 2%nat] mb (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
    (reac_box_catalogue_match_D f len) /\
  (* (4) ctl_tls_of_AR and the proposed fp_tls_owned_stmt *)
  cmRB_tls_dj mb tp FS Sp /\
  (* (5) RT_used_of_AR_C *)
  aCL mb /\
  (* (6) the live block and ctl_block_shadow_of_AR *)
  (50 <= len -> lib.Lib.Mem.bytes_at rsegs mb f fb /\ addressable mb f 50) /\
  (* (7) the image *)
  lib.Lib.Mem.bytes_at rsegs mb CM_T CM_TBL /\
  (* (8) ONE named hypothesis citing ctl_zshadow_of_AR_stmt (not wired) *)
  cmRB_tbl_addr mb /\
  (* (9) the proposed ctl_gshadow_of_AR_stmt *)
  cmRB_bc_addr mb.

(* Stretch 2's base: the class-2 frame j, from ctl_fs_of_astack 2. *)
Definition cmRB_Fs2 (mb : word -> option byte) (FS j : Z) : Prop :=
  0 <= j < fs_M 2 /\ fs_frame FS 2 j mod 64 = 0 /\
  lib.Lib.Mem.bytes_at rsegs mb (fs_flag FS 2 j) [Z_to_bv 8 1] /\
  lib.Lib.Mem.bytes_at rsegs mb (fs_frame FS 2 j + 256 - 8) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 j))) /\
  lib.Lib.Mem.bytes_at rsegs mb (shadow_addr (fs_frame FS 2 j)) (repeat (Z_to_bv 8 0) (Z.to_nat 32)).

(* Stretch 2's window above CA: kept byte for byte from the request memory m1 (the request's frame condition off the
   image at visible addresses; a Theorem Labs lane's proved ctl_kept_of_view_eq (lib/B/ProgWorld.v:1187), see the header). *)
Definition cmRB_win_kept (m1 mb : word -> option byte) (Sp : Z) : Prop :=
  forall a, CA Sp <= a < Sp -> mb (lib.Lib.Mem.wa a) = m1 (lib.Lib.Mem.wa a).

(* Stretches 5 and 6: the frame geometry, the saves and the flag word, from the same run. *)
Definition cmRB_Fr (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (Sp FS fr sp2 jj nn : Z) : Prop :=
  cmFK Sp FS fr sp2 jj nn /\
  lib.Lib.Step.rw_cells rsegs mb (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  (nn = 1 -> lib.Lib.Mem.bytes_at rsegs mb (fr + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 jj)))).

(* ---- the posts, on the real memory, relative to the stretch base mb ---- *)
(* cmAtSM2 with ro_agree for mem_inv. *)
Definition cmRB_AtSM2 (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte) (Sp : Z)
    (m1 : word -> option byte) : Prop :=
  lib.Lib.Frame.munch [(Sp - 9136, Sp)] mb m1 /\ lib.Lib.Frame.wmono rsegs mb m1 /\ MemNorm.ro_agree rsegs m1 /\
  lib.Lib.Frame.stk rsegs m1 (Sp - 9136) Sp /\ lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).

(* cmJ with ro_agree for mem_inv. *)
Definition cmRB_J (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  cmFK Sp FS fr sp2 jj nn /\ lib.Lib.Frame.munch (aWc Sp FS) mb mc /\ lib.Lib.Frame.wmono rsegs mb mc /\ MemNorm.ro_agree rsegs mc /\
  RT tp mb f len Sp FS mc /\ AWX Sp fr mc /\ EXT f len fb mc /\
  lib.Lib.Frame.stk rsegs mc (Sp - 9136) Sp /\ lib.Lib.Frame.stk rsegs mc fr (fr + 192) /\
  lib.Lib.Step.rw_cells rsegs mc (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  (nn = 1 -> lib.Lib.Mem.bytes_at rsegs mc (fr + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 jj)))).

(* cm_exit_at with cmRB_J. *)
Definition cmRB_exit_at (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (ms : machine_state) : Prop :=
  exists (fr sp2 jj nn : Z) (mc : word -> option byte) (r : Z)
         (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
    r = want CM_T len fb /\ cmRB_J ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc /\
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp)) y0 y1 y2 y3 y4 y5 y6 y7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
                 (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
            F (Z_to_bv 64 0x850fc) fc None mc (lib.Lib.PropExec.seg_rom rsegs).

(* cmAtParse with cmRB_J. *)
Definition cmRB_AtParse (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  50 <= len /\
  bv_unsigned (nth 12 fb (Z_to_bv 8 0)) = 136 /\ bv_unsigned (nth 13 fb (Z_to_bv 8 0)) = 25 /\
  bv_unsigned (nth 16 fb (Z_to_bv 8 0)) = 205 /\ bv_unsigned (nth 17 fb (Z_to_bv 8 0)) = 234 /\
  cmRB_J ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc /\
  addressable mc (fr + 32) 36.

(* The reac_ctrl_parse call state (callee entry 0x83e04, return 0x85058). *)
Definition cmRB_parse_at (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (ms : machine_state) : Prop :=
  exists (fr sp2 jj nn : Z) (mc : word -> option byte)
         (rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x85058) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                 (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
                 rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x83e04) fc None mc (lib.Lib.PropExec.seg_rom rsegs) /\
    cmRB_AtParse ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc.

(* Stretch 2's end: the exit state or the reac_ctrl_parse call state. *)
Definition cmRB_gate (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (ms : machine_state) : Prop :=
  cmRB_exit_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb ms \/
  cmRB_parse_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb ms.

(* The same end in Section MatchF's terms (cm_pre_parse's post, its gate registers hidden): the Q of cmKB. *)
Definition cmQ_gate (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : word -> option byte) (f len Sp FS : Z) (fb : list byte) (ms : machine_state) : Prop :=
  cm_exit_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m f len Sp FS fb ms \/
  exists (fr sp2 jj nn : Z) (m0 : word -> option byte)
         (rt0 rt1 rt2 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 : word),
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x85058) (Z_to_bv 64 sp2) gp tp rt0 rt1 rt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                 (Z_to_bv 64 f) (Z_to_bv 64 len) (Z_to_bv 64 (fr + 32)) ra3 ra4 ra5 ra6 ra7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
                 rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 rt3 rt4 rt5 rt6)
            F (Z_to_bv 64 0x83e04) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
    cmAtParse ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m f len Sp FS fb fr sp2 jj nn m0.

(* cmAtRel's writes and facts at the store memory, without its base part; the region transport relative to mb. *)
Definition cmRB_AtRel (mb : word -> option byte) (Sp FS fr jj : Z) (m1 : word -> option byte) : Prop :=
  lib.Lib.Frame.munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)] mb m1 /\
  lib.Lib.Frame.wmono rsegs mb m1 /\ MemNorm.ro_agree rsegs m1 /\ (forall P, shadow_rw_on P mb -> shadow_rw_on P m1) /\
  lib.Lib.Frame.stk rsegs m1 (Sp - 9136) Sp /\ lib.Lib.Frame.stk rsegs m1 FS (FS + FS_SIZE).

(* cmPost with ro_agree for mem_inv. *)
Definition cmRB_Post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (lib.Lib.MState.ret_pc ra) fc None m' (lib.Lib.PropExec.seg_rom rsegs) /\
    lib.Lib.Frame.munch ([(Sp - 9136, Sp)] ++ fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (Sp - 9136), shadow_addr Sp)]) mb m' /\
    lib.Lib.Frame.wmono rsegs mb m' /\ MemNorm.ro_agree rsegs m' /\ lib.Lib.Frame.stk rsegs m' (Sp - 9136) Sp /\ asan_cells m' /\
    (forall P, shadow_rw_on P mb -> shadow_rw_on P m') /\ addressable m' (Sp - 9136) 9136 /\
    fp [0%nat; 1%nat; 2%nat] m' (bv_unsigned tp) FS (Sp - 9136) Sp (reac_box_catalogue_match_W Sp)
      (reac_box_catalogue_match_D f len) /\
    reac_box_catalogue_match_tls m' (bv_unsigned tp) FS (Sp - 9136) Sp.

(* ---- stretches 3 and 4: after a walked callee (reac_ctrl_parse, reac_box_model_block) ---- *)
(* Bytes kept byte for byte from the call memory m1 to the return memory mb, on the addresses P names. *)
Definition cmRB_kept (m1 mb : word -> option byte) (P : Z -> Prop) : Prop :=
  forall a, P a -> mb (lib.Lib.Mem.wa a) = m1 (lib.Lib.Mem.wa a).

(* The caller's bytes that a callee with window [lo, sp2) and output buffer [fr + b, fr + b + n) does not write and
   that the next stretch reads: the window outside the callee's window (the 13 saves among them), the frame's flag
   word, and the shadow bytes of the buffer.  Source: the callee's post keeps every visible byte outside its writes
   (munch_vis; the window by win_vis, the frame and its shadow by frame_vis), and off the image at a visible address
   that is a raw byte equality (a Theorem Labs lane's proved ctl_kept_of_view_eq (lib/B/ProgWorld.v:1187), see the header). *)
Definition cmRB_callee_kept (Sp fr sp2 lo b n : Z) (a : Z) : Prop :=
  (Sp - 9136 <= a < Sp /\ ~ (lo <= a < sp2)) \/ (fr + 248 <= a < fr + 256) \/
  (shadow_addr (fr + b) <= a <= shadow_addr (fr + b + n - 1)).

(* cmAtMB with cmRB_J. *)
Definition cmRB_AtMB (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (i : nat) (fr sp2 jj nn : Z) (mc : word -> option byte) : Prop :=
  (i < 11)%nat /\ cmRB_J ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc /\
  addressable mc (fr + 112) 32.

(* The reac_box_model_block call state for row i with s9 = k (callee entry 0x865d8, return 0x8509c). *)
Definition cmRB_mb_call (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (i k : nat) (fr sp2 jj nn : Z)
    (ms : machine_state) : Prop :=
  exists (m0 : word -> option byte) (zt0 zt1 zt2 za3 za4 za5 za6 za7 zt3 zt4 zt5 zt6 : word),
    ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp zt0 zt1 zt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                 (Z_to_bv 64 (CM_T + 296 * Z.of_nat i)) (Z_to_bv 64 0) (Z_to_bv 64 (fr + 112)) za3 za4 za5 za6 za7
                 (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
                 (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
                 (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) zt3 zt4 zt5 zt6)
            F (Z_to_bv 64 0x865d8) fc None m0 (lib.Lib.PropExec.seg_rom rsegs) /\
    cmRB_AtMB ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb i fr sp2 jj nn m0.

(* Stretch 3's end: the exit state, or the call of reac_box_model_block for row 0 (cm_post_parse_K's post). *)
Definition cmRB_parse_Q (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (ms : machine_state) : Prop :=
  cmRB_exit_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb ms \/
  (cm_gate len fb = true /\
   cmRB_mb_call ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb 0 11 fr sp2 jj nn ms).

(* Stretch 4's end: the exit state, or the call for row S i with the loop facts (cm_post_mb_K's post). *)
Definition cmRB_mb_Q (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (f len Sp FS : Z) (fb : list byte) (i : nat) (fr sp2 jj nn : Z)
    (ms : machine_state) : Prop :=
  cmRB_exit_at ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb ms \/
  exists k' : nat, (Corelib.Init.Datatypes.S i + k' = 11)%nat /\ (0 < k')%nat /\
    (forall j, (j < Corelib.Init.Datatypes.S i)%nat -> nth j DECLS [] <> cm_blk fb) /\
    cmRB_mb_call ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb (Corelib.Init.Datatypes.S i) k' fr sp2 jj nn ms.

(* ============================================================================================================ *)

(* cmBase moves to the normalized base: Section MatchF's single-memory hypotheses at m := normalize mb. *)
Lemma cmRB_norm : forall (mb : word -> option byte) (tp : word) (f len Sp FS : Z) (fb : list byte),
  HIGHMEM_BEG <= Sp - 9136 -> cmBase mb tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp ->
  MemNorm.mem_rel rsegs mb (MemNorm.normalize rsegs mb) /\
  lib.Lib.Frame.stk rsegs (MemNorm.normalize rsegs mb) (Sp - 9136) Sp /\
  lib.Lib.Mem.mem_inv rsegs (MemNorm.normalize rsegs mb) /\
  asan_cells (MemNorm.normalize rsegs mb) /\
  shadow_rw_on (reac_box_catalogue_match_shadow_R f len Sp FS) (MemNorm.normalize rsegs mb) /\
  addressable (MemNorm.normalize rsegs mb) (Sp - 9136) 9136 /\
  fp [0%nat; 1%nat; 2%nat] (MemNorm.normalize rsegs mb) (bv_unsigned tp) FS (Sp - 9136) Sp
    (reac_box_catalogue_match_W Sp) (reac_box_catalogue_match_D f len) /\
  reac_box_catalogue_match_tls (MemNorm.normalize rsegs mb) (bv_unsigned tp) FS (Sp - 9136) Sp /\
  aCL (MemNorm.normalize rsegs mb) /\
  (50 <= len -> lib.Lib.Mem.bytes_at rsegs (MemNorm.normalize rsegs mb) f fb /\ addressable (MemNorm.normalize rsegs mb) f 50) /\
  lib.Lib.Mem.bytes_at rsegs (MemNorm.normalize rsegs mb) CM_T CM_TBL /\
  addressable (MemNorm.normalize rsegs mb) CM_T 3256 /\
  addressable (MemNorm.normalize rsegs mb) REAC_CTRL_PARSE_BC 6.
Proof.
  intros mb tp f len Sp FS fb HHM ((AC & SR & RO) & AW & FP & TL & CL & HFB & BT & AT & ABC) STW.
  pose proof (MemNorm.mem_rel_normalize rsegs mb RO) as REL.
  pose proof (fun a bs H => MemNorm.bytes_at_normalize rsegs mb a bs RO H) as EB.
  split; [exact REL|].
  split; [exact (cmRB_stk_normalize mb _ _ RO (cmRB_win_above_img Sp HHM) STW)|].
  split; [exact (MemNorm.mem_inv_normalize rsegs mb)|].
  split; [exact (MemNormTr.asan_cells_normalize mb RO AC)|].
  split; [exact (B.ShadowRwOnT.shadow_rw_on_normalize _ mb RO SR)|].
  split; [exact (MemNormTr.addressable_normalize mb _ _ RO AW)|].
  split; [exact (MemNormTr.fp_normalize _ mb _ _ _ _ _ _ RO FP)|].
  split; [exact (MemNormTr.tls_dj_normalize mb (bv_unsigned tp)
                   (fp_w [0%nat; 1%nat; 2%nat] FS ++ [(shadow_addr (Sp - 9136), shadow_addr Sp)]) RO TL)|].
  split; [destruct CL as (C1 & C2 & C3 & C4 & C5);
          exact (conj (EB _ _ C1) (conj (EB _ _ C2) (conj (EB _ _ C3) (conj (EB _ _ C4) (EB _ _ C5)))))|].
  split; [intros L; destruct (HFB L) as (B1 & B2);
          exact (conj (EB _ _ B1) (MemNormTr.addressable_normalize mb _ _ RO B2))|].
  split; [exact (EB _ _ BT)|].
  split; [exact (MemNormTr.addressable_normalize mb CM_T 3256 RO AT)
         | exact (MemNormTr.addressable_normalize mb REAC_CTRL_PARSE_BC 6 RO ABC)].
Qed.

(* The 13 saves move to the normalized base (the window is not read-only: it is writable there). *)
Lemma cmRB_saves_n : forall (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte) (Sp : Z),
  MemNorm.mem_rel rsegs mb (MemNorm.normalize rsegs mb) ->
  lib.Lib.Frame.stk rsegs (MemNorm.normalize rsegs mb) (Sp - 9136) Sp ->
  lib.Lib.Step.rw_cells rsegs mb (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  lib.Lib.Step.rw_cells rsegs (MemNorm.normalize rsegs mb) (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  intros ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp REL STn SAV.
  apply MemNormTr.rw_cells_normalize; [exact (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) | | exact SAV].
  intros i Hi. change (lib.Lib.Cells.cells_size (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) with 104%nat in Hi.
  pose proof STn as (_ & _ & HS).
  apply (MemNorm.ro_false_of_wview rsegs mb (MemNorm.normalize rsegs mb) _ REL).
  exact (proj1 (HS (Sp + -104 + i) ltac:(lia))).
Qed.

(* Section MatchF's cmJ at the normalized base, from cmBase and cmRB_Fr (the frame's stk: in the window for the
   real-stack frame, in the side stack for a class-2 side frame). *)
Lemma cmRB_J_base : forall (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z),
  Sp mod 16 = 0 -> HIGHMEM_BEG <= Sp - 9136 ->
  cmBase mb tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp ->
  cmRB_Fr ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp FS fr sp2 jj nn ->
  cmJ ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb fr sp2 jj nn
    (MemNorm.normalize rsegs mb).
Proof.
  intros ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn S16 HHM HB STW (FK & SAV & FLG).
  destruct (cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  pose proof FPn as (DT & TS & C & T & DB & kk & _ & _ & (_ & _ & _ & _ & PSn) & _).
  pose proof (cmRB_CA Sp S16) as CAb.
  split; [exact FK|].
  split; [apply lib.Lib.Frame.munch_refl|].
  split; [apply lib.Lib.Frame.wmono_refl|].
  split; [exact MIn|].
  split; [exact (conj ACn (conj (fun P H => H) (conj FPn TLn)))|].
  split; [exact (cmRB_awx Sp fr _ AWn)|].
  split; [exact (conj HFBn (conj ATn (conj BTn (conj ABCn CLn))))|].
  split; [exact STn|].
  split.
  { destruct FK as [(Ef & _ & _ & _)|(Hj & Ef & _ & _)].
    - apply (cmRB_stk_sub _ _ _ _ _ STn); rewrite Ef; lia.
    - pose proof (cmRB_fr_in_fs FS jj Hj) as (B1 & B2).
      apply (cmRB_stk_sub _ _ _ _ _ PSn); rewrite Ef; lia. }
  split; [exact (cmRB_saves_n ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp REL STn SAV)|].
  intros Hn. exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO (FLG Hn)).
Qed.

(* A post's cmJ on the normalized run, carried back to the real memory that ms_rel relates to it (the writes and
   the writability by MemNorm.munch_rel / wmono_rel, which need the run's ro_same). *)
Lemma cmRB_J_of_rel : forall (ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb : word -> option byte)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj nn : Z) (mc mc' : word -> option byte),
  MemNorm.mem_rel rsegs mb (MemNorm.normalize rsegs mb) -> MemNorm.mem_rel rsegs mc' mc ->
  MemNorm.ro_same rsegs mb mc' ->
  cmJ ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb fr sp2 jj nn mc ->
  cmRB_J ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc'.
Proof.
  intros ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc mc' REL0 REL Hsm
    (FK & MU & WM & MI & (AC & SR & FP & TL) & AX & (E1 & E2 & E3 & E4 & E5) & STW & STF & SAV & FLG).
  pose proof (fun a bs H => proj2 (MemNorm.bytes_at_rel rsegs mc' mc a bs REL) H) as EB.
  split; [exact FK|].
  split; [exact (MemNorm.munch_rel rsegs _ mb _ mc' mc REL0 REL Hsm MU)|].
  split; [exact (MemNorm.wmono_rel rsegs mb _ mc' mc REL0 REL Hsm WM)|].
  split; [exact (MemNorm.ro_agree_of_mem_rel rsegs mc' mc REL)|].
  split.
  { split; [exact (MemNormTr.asan_cells_of_rel mc' mc REL AC)|].
    split; [intros P HP; exact (B.ShadowRwOnT.shadow_rw_on_of_rel P mc' mc REL
                                  (SR P (B.ShadowRwOnT.shadow_rw_on_rel P mb _ REL0 HP)))|].
    split; [exact (MemNormTr.fp_transport mc mc' _ _ _ _ _ _ _ EB
                     (fun lo hi _ H => MemNormTr.stk_of_rel mc' mc lo hi REL H) FP)|].
    intros DT TS C T DB kk H. apply TL.
    exact (MemNormTr.asan_tls_cells_transport mc' mc _ _ _ _ _ _ _
             (fun a bs H' => proj1 (MemNorm.bytes_at_rel rsegs mc' mc a bs REL) H') H). }
  split; [intros x Hx Hn; exact (cmRB_addr_byte_of_rel mc' mc x REL (AX x Hx Hn))|].
  split.
  { split; [intros L; destruct (E1 L) as (B1 & B2); exact (conj (EB _ _ B1) (cmRB_addressable_of_rel mc' mc _ _ REL B2))|].
    split; [exact (cmRB_addressable_of_rel mc' mc _ _ REL E2)|].
    split; [exact (EB _ _ E3)|].
    split; [exact (cmRB_addressable_of_rel mc' mc _ _ REL E4)|].
    destruct E5 as (C1 & C2 & C3 & C4 & C5).
    exact (conj (EB _ _ C1) (conj (EB _ _ C2) (conj (EB _ _ C3) (conj (EB _ _ C4) (EB _ _ C5))))). }
  split; [exact (MemNormTr.stk_of_rel mc' mc _ _ REL STW)|]. split; [exact (MemNormTr.stk_of_rel mc' mc _ _ REL STF)|].
  split; [exact (MemNormTr.rw_cells_of_rel mc' mc _ _ REL SAV)|].
  intros Hn. exact (EB _ _ (FLG Hn)).
Qed.

(* ---- stretch 1: entry 0x84e40 -> the __asan_stack_malloc_2 call (pc 252408); cm_pre_sm2 at m := normalize mb ---- *)
Lemma cmRB_pre_sm2 : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG 65536 6217728 -> lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 ->
  cmBase mb tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp ->
  forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evtF rsegs RNG
    (fun ms => exists m1, ms =
       lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 544436) (Z_to_bv 64 (CA Sp)) gp tp t0 t1 t2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
               (Z_to_bv 64 192) (lib.Lib.Mem.wa 693944) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 252408) fc None m1 (lib.Lib.PropExec.seg_rom rsegs) /\
       cmRB_AtSM2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp m1)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    Rf Rlen RS S16 HK Hfb HHM HAE RIMG RWIN HB STW t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  destruct (cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  pose proof (cm_pre_sm2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb) f len Sp fb
    RNG) as L.
  cmRB_feed L.
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mb _ RO (L t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6)) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & (m0 & -> & (MU & WM & _ & ST0 & SV0)) & Hrel & Hsm).
  destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
  exists (ms_mem st). split; [exact Es|].
  split; [exact (MemNorm.munch_rel rsegs _ mb _ (ms_mem st) m0 REL Hmr Hsm MU)|].
  split; [exact (MemNorm.wmono_rel rsegs mb _ (ms_mem st) m0 REL Hmr Hsm WM)|].
  split; [exact (MemNorm.ro_agree_of_mem_rel rsegs _ _ Hmr)|].
  split; [exact (MemNormTr.stk_of_rel _ _ _ _ Hmr ST0) | exact (MemNormTr.rw_cells_of_rel _ _ _ _ Hmr SV0)].
Qed.

(* ---- stretch 2: the class-2 return (pc 544436) -> the gate -> the reac_ctrl_parse call or the exit;
   cm_post_sm2_side at m := m0 := m2 := normalize mb, with cmKB's Q from cm_pre_parse ---- *)
Lemma cmRB_post_sm2_side : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  (50 <= len -> app_mem (f + 50)) ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  cmBase mb tp f len Sp FS fb ->
  lib.Lib.Frame.stk rsegs mb (Sp - 9136) (CA Sp) ->
  forall m1 : word -> option byte,
  lib.Lib.Frame.stk rsegs m1 (CA Sp) Sp -> lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  cmRB_win_kept m1 mb Sp ->
  forall j : Z, cmRB_Fs2 mb FS j ->
  forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
  evtF rsegs RNG (cmRB_gate ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 544436) (Z_to_bv 64 (CA Sp)) gp tp t0 t1 t2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 (fs_frame FS 2 j)) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
             s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (lib.Lib.MState.ret_pc (Z_to_bv 64 544436)) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RWIN RWSH RFD RFW RFPW HB HSTlo m1 HST1 HSV1 HKP j HS2
    t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6.
  (* the window at mb: below CA from the request's post, above CA kept from m1; the saves likewise kept *)
  pose proof (cmRB_CA Sp S16) as CAb0.
  assert (STW : lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp)
    by exact (cmRB_stk_join mb _ _ _ HSTlo (cmRB_stk_keep m1 mb _ _ HKP HST1)).
  assert (SAV : lib.Lib.Step.rw_cells rsegs mb (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (cmRB_rw_cells_keep m1 mb _ _); [|exact HSV1]. intros i Hi.
    change (lib.Lib.Cells.cells_size (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) with 104%nat in Hi.
    apply HKP. lia. }
  destruct (cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  destruct CLn as (C1n & C2n & C3n & C4n & C5n).
  assert (HFn : 50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs (MemNorm.normalize rsegs mb) f fb /\
                (f + 50 <= Sp - 9136 \/ Sp <= f)).
  { intros L. destruct (HFp L) as (Q1 & Q2 & Q3). destruct (HFBn L) as (B1 & _).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact B1 | exact Q3]. }
  assert (AFUn : 50 <= len -> addressable (MemNorm.normalize rsegs mb) f 50 /\ app_mem (f + 50)).
  { intros L. split; [exact (proj2 (HFBn L)) | exact (AFp L)]. }
  destruct HS2 as (Hj & Hm64 & HFL & HFW & HSH).
  pose proof (cmRB_saves_n ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp REL STn SAV) as SAVn.
  pose proof FPn as (DT & TS & C & T & DB & kk & _ & _ & (P1 & P2 & P3 & P4 & PSn) & _ & _ & HCn & HLO & _ & _ & _).
  pose proof (cmRB_CA Sp S16) as CAb.
  pose proof (cmRB_fr_in_fs FS j Hj) as (B1 & B2).
  (* the gate's continuation: cm_pre_parse at the normalized base, for every gate state *)
  assert (K : cmKB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb) f len Sp FS fb RNG
                (cmQ_gate ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
                   f len Sp FS fb)).
  { intros fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 INV.
    pose proof (cm_pre_parse ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
      f len Sp FS fb RNG) as L.
    cmRB_feed L.
    eapply evtF_mono;
      [exact (L fr sp2 jj nn mc rra rt0 rt1 rt2 ra0 ra1 ra3 ra4 ra5 ra6 ra7 rs6 rs9 rs10 rs11 rt3 rt4 rt5 rt6 INV)|].
    intros ms [EX|(m0 & E & HA)]; [left; exact EX|right].
    exists fr, sp2, jj, nn, m0, rt0, rt1, rt2, ra3, ra4, ra5, ra6, ra7, rs6, rs9, rs10, rs11, rt3, rt4, rt5, rt6.
    split; [exact E | exact HA]. }
  assert (HAt : cmAtSM2 ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) Sp
                  (MemNorm.normalize rsegs mb)).
  { split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|]. split; [exact MIn|]. split; [exact STn | exact SAVn]. }
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS ?R ?F' ?pc ?fc' ?rv _ ?ro) =>
    assert (HN : evtF rsegs RNG (cmQ_gate ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                                   (MemNorm.normalize rsegs mb) f len Sp FS fb)
                   (lib.Lib.MState.MS R F' pc fc' rv (MemNorm.normalize rsegs mb) ro)) end.
  { pose proof (cm_post_sm2_side ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
      f len Sp FS fb RNG) as L.
    cmRB_feed L.
    apply (L _ (MemNorm.normalize rsegs mb) _ K HAt).
    (* cm_fs_post_2 at the normalized base: the request's post with m0 = m2 = normalize mb *)
    exists t0, t1, t2, (Z_to_bv 64 (fs_frame FS 2 j)), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6,
      (MemNorm.normalize rsegs mb).
    split; [reflexivity|].
    split; [apply lib.Lib.Frame.wmono_refl|].
    split; [exact MIn|].
    split; [apply (cmRB_stk_sub _ _ _ _ _ STn); lia|].
    split; [exact PSn|].
    split; [destruct (proj1 (Forall_forall _ _) HCn 2%nat ltac:(right; right; left; reflexivity))
              as (_ & h & _ & Hh & _);
            exists h; exact Hh|].
    exists j.
    split; [exact Hj|]. split; [reflexivity|]. split; [exact Hm64|].
    split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HFL)|].
    split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HFW)|].
    split; [exact (MemNorm.bytes_at_normalize rsegs mb _ _ RO HSH)|].
    split; [apply (cmRB_stk_sub _ _ _ _ _ PSn); lia|].
    split; [intros a Ha; apply P4; lia|].
    split; [exact B1|]. split; [exact B2|]. split; [lia|].
    split; [unfold ASAN_STACK_MALLOC_K; lia|].
    split; [exact (cmRB_fs2_disj FS j Hj)|].
    apply lib.Lib.Frame.munch_refl. }
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mb _ RO HN) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & HQ & Hrel & Hsm).
  destruct HQ as [EX|PA].
  - left.
    destruct EX as (fr & sp2 & jj & nn & mc & r & x1 & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 &
                    z3 & z5 & z6 & z9 & z10 & z11 & u3 & u4 & u5 & u6 & Er & HJ & ->).
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists fr, sp2, jj, nn, (ms_mem st), r, x1, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9, z10, z11,
      u3, u4, u5, u6.
    split; [exact Er|]. split; [|exact Es].
    exact (cmRB_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc (ms_mem st)
             REL Hmr Hsm HJ).
  - right.
    destruct PA as (fr & sp2 & jj & nn & mc & rt0 & rt1 & rt2 & ra3 & ra4 & ra5 & ra6 & ra7 & rs6 & rs9 & rs10 & rs11 &
                    rt3 & rt4 & rt5 & rt6 & -> & (L50 & H12 & H13 & H16 & H17 & HJ & HAD)).
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists fr, sp2, jj, nn, (ms_mem st), rt0, rt1, rt2, ra3, ra4, ra5, ra6, ra7, rs6, rs9, rs10, rs11, rt3, rt4, rt5,
      rt6.
    split; [exact Es|].
    split; [exact L50|]. split; [exact H12|]. split; [exact H13|]. split; [exact H16|]. split; [exact H17|].
    split; [exact (cmRB_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn mc
                     (ms_mem st) REL Hmr Hsm HJ)|].
    exact (cmRB_addressable_of_rel _ _ _ _ Hmr HAD).
Qed.

(* A walked callee's return memory mb: the caller's window, saves, flag word and buffer shadow there, from the call
   memory m1 through the kept bytes and from the callee's own window [lo, sp2). *)
Lemma cmRB_callee_base : forall (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m1 mb : word -> option byte)
    (Sp FS fr sp2 jj nn lo b n : Z),
  Sp mod 16 = 0 -> cmFK Sp FS fr sp2 jj nn ->
  lib.Lib.Frame.stk rsegs m1 (Sp - 9136) Sp -> lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  (nn = 1 -> lib.Lib.Mem.bytes_at rsegs m1 (fr + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 jj)))) -> addressable m1 (fr + b) n ->
  lib.Lib.Frame.stk rsegs mb lo sp2 -> cmRB_kept m1 mb (cmRB_callee_kept Sp fr sp2 lo b n) ->
  lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp /\ cmRB_Fr ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp FS fr sp2 jj nn /\
  addressable mb (fr + b) n.
Proof.
  intros ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 mb Sp FS fr sp2 jj nn lo b n S16 FK ST1 SV1 FL1 AD1 STc KP.
  pose proof (cmRB_CA Sp S16) as CAb.
  assert (Hsp2 : sp2 <= Sp - 128) by (destruct FK as [(_ & E & _ & _)|(_ & _ & E & _)]; lia).
  split.
  { destruct ST1 as (A0 & A1 & A). destruct STc as (B0 & B1 & B). split; [exact A0|]. split; [exact A1|].
    intros a Ha. assert (D : (lo <= a < sp2) \/ ~ (lo <= a < sp2)) by lia.
    destruct D as [D|D]; [exact (B a D)|].
    pose proof (KP a (or_introl (conj Ha D))) as E.
    rewrite (cmRB_wview_keep m1 mb _ E), (cmRB_mrd_keep m1 mb _ E). exact (A a Ha). }
  split; [split; [exact FK|]; split|].
  - apply (cmRB_rw_cells_keep m1 mb _ _); [|exact SV1]. intros i Hi.
    change (lib.Lib.Cells.cells_size (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) with 104%nat in Hi.
    apply KP. left. lia.
  - intros Hn. apply (cmRB_bytes_keep m1 mb); [|exact (FL1 Hn)]. intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi.
    apply KP. right. left. lia.
  - apply (cmRB_addr_keep m1 mb _ _); [|exact AD1]. intros a Ha. apply KP. right. right. exact Ha.
Qed.

(* ---- stretch 3: the reac_ctrl_parse return (pc 0x85058) -> the exit, or the reac_box_model_block call of row 0
   (pc 0x865d8); cm_post_parse_K at m := mc := mp := normalize mb.  The base mb is the return memory; the call
   memory m1 is stretch 2's end (cmRB_parse_at). ---- *)
Lemma cmRB_post_parse : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  (50 <= len -> app_mem (f + 50)) ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  cmBase mb tp f len Sp FS fb ->
  forall (fr sp2 jj nn : Z) (m1 : word -> option byte),
  (* the call memory m1 (stretch 2's end) *)
  cmFK Sp FS fr sp2 jj nn -> lib.Lib.Frame.stk rsegs m1 (Sp - 9136) Sp ->
  lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  (nn = 1 -> lib.Lib.Mem.bytes_at rsegs m1 (fr + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 jj)))) -> addressable m1 (fr + 32) 36 ->
  (* the return memory mb: reac_ctrl_parse's window and output, the caller's bytes kept *)
  lib.Lib.Frame.stk rsegs mb (sp2 - 8800) sp2 -> lib.Lib.Step.rw_cells rsegs mb (fr + 32) [lib.Lib.Cells.CB 36 (snd (ctrlparse len fb))] ->
  cmRB_kept m1 mb (cmRB_callee_kept Sp fr sp2 (sp2 - 8800) 32 36) ->
  (* the gate's checks *)
  50 <= len ->
  bv_unsigned (nth 12 fb (Z_to_bv 8 0)) = 136 -> bv_unsigned (nth 13 fb (Z_to_bv 8 0)) = 25 ->
  bv_unsigned (nth 16 fb (Z_to_bv 8 0)) = 205 -> bv_unsigned (nth 17 fb (Z_to_bv 8 0)) = 234 ->
  forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rs6 rs9 rs10 rs11 : word),
  evtF rsegs RNG (cmRB_parse_Q ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb fr sp2 jj nn)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x85058) (Z_to_bv 64 sp2) gp tp t0 t1 t2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 (fst (ctrlparse len fb))) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K)
             rs6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) rs9 rs10 rs11 t3 t4 t5 t6)
        F (lib.Lib.MState.ret_pc (Z_to_bv 64 0x85058)) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RWIN RWSH RFD RFW RFPW HB fr sp2 jj nn m1
    FK ST1 SV1 FL1 AD1 STc RWo KP L E12 E13 E16 E17
    t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rs6 rs9 rs10 rs11.
  destruct (cmRB_callee_base ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 mb Sp FS fr sp2 jj nn (sp2 - 8800) 32 36
              S16 FK ST1 SV1 FL1 AD1 STc KP) as (STW & HFr & ADb).
  pose proof (cmRB_J_base ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn S16 HHM HB STW HFr)
    as HJ.
  destruct (cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  assert (HFn : 50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs (MemNorm.normalize rsegs mb) f fb /\
                (f + 50 <= Sp - 9136 \/ Sp <= f)).
  { intros L'. destruct (HFp L') as (Q1 & Q2 & Q3). destruct (HFBn L') as (B1 & _).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact B1 | exact Q3]. }
  assert (AFUn : 50 <= len -> addressable (MemNorm.normalize rsegs mb) f 50 /\ app_mem (f + 50)).
  { intros L'. split; [exact (proj2 (HFBn L')) | exact (AFp L')]. }
  pose proof (cmRB_CA Sp S16) as CAb.
  assert (Hsp2 : Sp - 336 <= sp2 <= Sp - 128) by (destruct FK as [(_ & E & _ & _)|(_ & _ & E & _)]; lia).
  destruct (acl_fs tp (MemNorm.normalize rsegs mb) f len Sp FS FPn) as (FSpos & _ & _ & FShi & _ & FSdj).
  assert (FRpos : 0 < fr).
  { destruct FK as [(Ef & _ & _ & _)|(Hj & Ef & _ & _)]; [lia|].
    pose proof (cmRB_fr_in_fs FS jj Hj) as (B1 & _). lia. }
  pose proof HJ as (_ & _ & _ & _ & (_ & _ & _ & TLJ) & _ & _ & _ & STFn & _ & _).
  (* cmAtParse at the normalized base *)
  assert (HAt : cmAtParse ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb
                  fr sp2 jj nn (MemNorm.normalize rsegs mb)).
  { exact (conj L (conj E12 (conj E13 (conj E16 (conj E17
             (conj HJ (MemNormTr.addressable_normalize mb _ _ RO ADb))))))). }
  (* the output buffer at the normalized base (in the frame, which is writable there: not read-only) *)
  assert (RWn : lib.Lib.Step.rw_cells rsegs (MemNorm.normalize rsegs mb) (fr + 32) [lib.Lib.Cells.CB 36 (snd (ctrlparse len fb))]).
  { apply MemNormTr.rw_cells_normalize; [exact RO | | exact RWo]. intros i Hi.
    change (lib.Lib.Cells.cells_size [lib.Lib.Cells.CB 36 (snd (ctrlparse len fb))]) with 36%nat in Hi.
    pose proof STFn as (_ & _ & HS).
    apply (MemNorm.ro_false_of_wview rsegs mb (MemNorm.normalize rsegs mb) _ REL).
    exact (proj1 (HS (fr + 32 + i) ltac:(lia))). }
  pose proof (cm_post_parse_K ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
    f len Sp FS fb RNG) as K.
  cmRB_feed K.
  (* reac_ctrl_parse's post at the normalized base, the return memory being the base itself *)
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS ?R ?F' ?pc ?fc' ?rv _ ?ro) =>
    assert (PP : cm_parse_post gp tp F fc f len Sp FS fb fr sp2 nn rs6 rs9 rs10 rs11 (MemNorm.normalize rsegs mb)
                   (lib.Lib.MState.MS R F' pc fc' rv (MemNorm.normalize rsegs mb) ro)) end.
  { exists t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, (MemNorm.normalize rsegs mb).
    split; [reflexivity|].
    split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|]. split; [exact MIn|].
    split; [unfold REAC_CTRL_PARSE_K; apply (cmRB_stk_sub _ _ _ _ _ STn); lia|].
    split; [exact RWn|]. split; [exact (fun P H => H)|].
    split; [unfold REAC_CTRL_PARSE_K; apply (cmRB_addressable_sub _ _ _ _ _ AWn); lia|].
    split.
    - unfold reac_ctrl_parse_W, reac_ctrl_parse_D, REAC_CTRL_PARSE_K.
      replace (fr + 32 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      replace (len <? 50) with false by (symmetry; apply Z.ltb_ge; lia).
      cbn [app]. replace (fr + 32 + 36) with (fr + 68) by lia.
      apply (cm_fp_callee ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb
               Rf Rlen S16 HK STn Hfb SRn AWn FPn fr sp2 jj nn (MemNorm.normalize rsegs mb) 1%nat (sp2 - 8800) 32 68
               _ HJ ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
      apply fl_dj_cons. split.
      + apply (fp_dj_incl _ (fp_w [0%nat; 1%nat; 2%nat] FS)); [apply fp_w_incl; cbn; tauto|].
        apply (fl_dj_sub f (f + 50)); [|lia|lia|lia].
        unfold aDf in FSdj. replace (len <? 50) with false in FSdj by (symmetry; apply Z.ltb_ge; lia).
        exact FSdj.
      + apply fl_dj_cons. split; [|constructor].
        exact (cm_dj_fr tp (MemNorm.normalize rsegs mb) f len Sp FS fb Rf Rlen S16 HK STn Hfb SRn AWn FPn
                 fr sp2 jj nn 32 68 1%nat FK ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)).
    - unfold REAC_CTRL_PARSE_K.
      exact (cm_tls_callee tp f len Sp FS fb Rf Rlen HK Hfb (MemNorm.normalize rsegs mb) 1%nat (sp2 - 8800) sp2
               ltac:(lia) TLJ ltac:(lia) ltac:(lia) ltac:(lia)). }
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mb _ RO (K fr sp2 jj nn _ rs6 rs9 rs10 rs11 _ HAt PP)) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & HQ & Hrel & Hsm).
  destruct HQ as [EX|(m0 & v4 & v9 & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & -> &
                      G & E4 & E9 & (Hi & HJ0 & AD0))].
  - left.
    destruct EX as (fr' & sp2' & jj' & nn' & mc & r & x1 & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 &
                    z3 & z5 & z6 & z9 & z10 & z11 & u3 & u4 & u5 & u6 & Er & HJE & ->).
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists fr', sp2', jj', nn', (ms_mem st), r, x1, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9,
      z10, z11, u3, u4, u5, u6.
    split; [exact Er|]. split; [|exact Es].
    exact (cmRB_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr' sp2' jj' nn' mc (ms_mem st)
             REL Hmr Hsm HJE).
  - right. subst v4 v9.
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    split; [exact G|].
    exists (ms_mem st), zt0, zt1, zt2, za3, za4, za5, za6, za7, zt3, zt4, zt5, zt6.
    split; [exact Es|].
    split; [exact Hi|].
    split; [exact (cmRB_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn m0
                     (ms_mem st) REL Hmr Hsm HJ0)|].
    exact (cmRB_addressable_of_rel _ _ _ _ Hmr AD0).
Qed.

(* ---- stretch 4: a reac_box_model_block return (pc 0x8509c), row i -> the exit, or the call of row S i
   (pc 0x865d8); cm_post_mb_K at m := mc := normalize mb.  The base mb is the return memory; the call memory m1 is
   the previous stretch's end (cmRB_mb_call).  reac_box_model_block's post gives the buffer as
   synth (cm_row i) 0 [] and a0 = rc (cm_row i) 0; cm_rc turns them into nth i DECLS [] and 1. ---- *)
Lemma cmRB_post_mb : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  bcmp_wrap_c_on.bcmp_wrap_contract_F_on ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  (50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ (f + 50 <= Sp - 9136 \/ Sp <= f)) ->
  (50 <= len -> app_mem (f + 50)) ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  rng_bytes RNG -> lib.Lib.ExecF.rng RNG 65536 6217728 ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  (50 <= len -> lib.Lib.ExecF.rng RNG f 50) ->
  (50 <= len -> forall p n, f <= p -> 0 < n -> p + n <= f + 50 -> sh_cover RNG p n) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  cmBase mb tp f len Sp FS fb ->
  forall (k : nat), cm_gate len fb = true ->
  forall (i : nat) (fr sp2 jj nn : Z) (m1 : word -> option byte),
  (i + k = 11)%nat -> (0 < k)%nat -> (forall j, (j < i)%nat -> nth j DECLS [] <> cm_blk fb) ->
  (* the call memory m1 (the previous stretch's end) *)
  cmFK Sp FS fr sp2 jj nn -> lib.Lib.Frame.stk rsegs m1 (Sp - 9136) Sp ->
  lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
  (nn = 1 -> lib.Lib.Mem.bytes_at rsegs m1 (fr + 248) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 2 jj)))) -> addressable m1 (fr + 112) 32 ->
  (* the return memory mb: reac_box_model_block's window and output, the caller's bytes kept *)
  lib.Lib.Frame.stk rsegs mb (sp2 - 4272) sp2 -> lib.Lib.Mem.bytes_at rsegs mb (fr + 112) (nth i DECLS []) ->
  cmRB_kept m1 mb (cmRB_callee_kept Sp fr sp2 (sp2 - 4272) 112 32) ->
  forall (yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6 : word),
  evtF rsegs RNG (cmRB_mb_Q ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb i fr sp2 jj nn)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8509c) (Z_to_bv 64 sp2) gp tp yt0 yt1 yt2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 1) ya1 ya2 ya3 ya4 ya5 ya6 ya7
             (Z_to_bv 64 (if nn =? 0 then 0 else fr)) (Z_to_bv 64 f) (Z_to_bv 64 (CM_T + 296 * Z.of_nat i))
             (Z_to_bv 64 (fr + 112)) (Z_to_bv 64 (f + 18)) (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
             (Z_to_bv 64 (Z.of_nat k)) (Z_to_bv 64 1) (Z_to_bv 64 (-8)) yt3 yt4 yt5 yt6)
        F (Z_to_bv 64 0x8509c) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    HBC Rf Rlen RS S16 HK Hfb HFp AFp HHM HAE RB RIMG RWIN RWSH RFD RFW RFPW HB k G i fr sp2 jj nn m1
    Hik Hk Hnd FK ST1 SV1 FL1 AD1 STc BBo KP yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6.
  destruct (cmRB_callee_base ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m1 mb Sp FS fr sp2 jj nn (sp2 - 4272) 112 32
              S16 FK ST1 SV1 FL1 AD1 STc KP) as (STW & HFr & ADb).
  pose proof (cmRB_J_base ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn S16 HHM HB STW HFr)
    as HJ.
  destruct (cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  assert (HFn : 50 <= len -> 0 < f /\ f + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs (MemNorm.normalize rsegs mb) f fb /\
                (f + 50 <= Sp - 9136 \/ Sp <= f)).
  { intros L'. destruct (HFp L') as (Q1 & Q2 & Q3). destruct (HFBn L') as (B1 & _).
    split; [exact Q1|]. split; [exact Q2|]. split; [exact B1 | exact Q3]. }
  assert (AFUn : 50 <= len -> addressable (MemNorm.normalize rsegs mb) f 50 /\ app_mem (f + 50)).
  { intros L'. split; [exact (proj2 (HFBn L')) | exact (AFp L')]. }
  pose proof (cm_post_mb_K ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
    f len Sp FS fb RNG) as K.
  cmRB_feed K.
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mb _ RO
    (K k G i fr sp2 jj nn (MemNorm.normalize rsegs mb) _ _ yt0 yt1 yt2 ya1 ya2 ya3 ya4 ya5 ya6 ya7 yt3 yt4 yt5 yt6
       eq_refl eq_refl Hik Hk Hnd HJ (MemNorm.bytes_at_normalize rsegs mb _ _ RO BBo)
       (MemNormTr.addressable_normalize mb _ _ RO ADb))) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & HQ & Hrel & Hsm).
  destruct HQ as [EX|(k' & m0 & v4 & v9 & zt0 & zt1 & zt2 & za3 & za4 & za5 & za6 & za7 & zt3 & zt4 & zt5 & zt6 & -> &
                      E4 & E9 & Hik' & Hk' & Hnd' & (Hi & HJ0 & AD0))].
  - left.
    destruct EX as (fr' & sp2' & jj' & nn' & mc & r & x1 & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 &
                    z3 & z5 & z6 & z9 & z10 & z11 & u3 & u4 & u5 & u6 & Er & HJE & ->).
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists fr', sp2', jj', nn', (ms_mem st), r, x1, u0, u1, u2, y0, y1, y2, y3, y4, y5, y6, y7, z3, z5, z6, z9,
      z10, z11, u3, u4, u5, u6.
    split; [exact Er|]. split; [|exact Es].
    exact (cmRB_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr' sp2' jj' nn' mc (ms_mem st)
             REL Hmr Hsm HJE).
  - right. subst v4 v9.
    destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
    exists k'. split; [exact Hik'|]. split; [exact Hk'|]. split; [exact Hnd'|].
    exists (ms_mem st), zt0, zt1, zt2, za3, za4, za5, za6, za7, zt3, zt4, zt5, zt6.
    split; [exact Es|].
    split; [exact Hi|].
    split; [exact (cmRB_J_of_rel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj nn m0
                     (ms_mem st) REL Hmr Hsm HJ0)|].
    exact (cmRB_addressable_of_rel _ _ _ _ Hmr AD0).
Qed.

(* ---- stretch 5: the exit (pc 0x850fc), side-stack arm -> the flag store (pc 0x85194);
   cm_pre_rel at m := mc := normalize mb ---- *)
Lemma cmRB_pre_rel : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  lib.Lib.ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  cmBase mb tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp ->
  forall (fr sp2 jj r : Z) (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmRB_Fr ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp FS fr sp2 jj 1 ->
  evtF rsegs RNG
    (fun ms => exists m1, ms =
       lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
               (Z_to_bv 64 (fs_flag FS 2 jj)) y1 y2 y3 y4 y5 y6 y7
               (Z_to_bv 64 fr) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
               z9 z10 z11 u3 u4 u5 u6)
          F (Z_to_bv 64 0x85194) fc None m1 (lib.Lib.PropExec.seg_rom rsegs) /\ cmRB_AtRel mb Sp FS fr jj m1)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp)) y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if 1 =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850fc) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    Rf Rlen RS S16 HK Hfb HHM HAE RWIN RWSH RHDR RFPW HB STW fr sp2 jj r
    x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HFr.
  pose proof (cmRB_J_base ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj 1 S16 HHM HB STW HFr)
    as HJ.
  destruct (cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  pose proof (cm_pre_rel ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
    f len Sp FS fb RNG) as L.
  cmRB_feed L.
  pose proof (MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mb _ RO
    (L fr sp2 jj (MemNorm.normalize rsegs mb) r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
       Er HJ)) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & (m1 & -> & (_ & MU & WM & _ & SR1 & STW1 & STF1)) & Hrel & Hsm).
  destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
  exists (ms_mem st). split; [exact Es|].
  split; [exact (MemNorm.munch_rel rsegs _ mb _ (ms_mem st) m1 REL Hmr Hsm MU)|].
  split; [exact (MemNorm.wmono_rel rsegs mb _ (ms_mem st) m1 REL Hmr Hsm WM)|].
  split; [exact (MemNorm.ro_agree_of_mem_rel rsegs _ _ Hmr)|].
  split; [intros P HP; exact (B.ShadowRwOnT.shadow_rw_on_of_rel P _ _ Hmr
                                (SR1 P (B.ShadowRwOnT.shadow_rw_on_rel P mb _ REL HP)))|].
  split; [exact (MemNormTr.stk_of_rel _ _ _ _ Hmr STW1) | exact (MemNormTr.stk_of_rel _ _ _ _ Hmr STF1)].
Qed.

(* ---- stretch 6: after the flag store (pc 0x85198) -> ret; cm_post_rel at m := mc := m1 := normalize mb.  The base
   mb is the memory at the store (stretch 5's end); the start memory is the store's write of the flag byte 0 over mb,
   so the run moves to it by MemNormF.evtF_rel_ro (MemNorm.write_rw: the flag byte is not read-only). ---- *)
Lemma cmRB_post_rel : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mb : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 -> lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  lib.Lib.ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  cmBase mb tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp ->
  forall (fr sp2 jj r : Z) (x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmRB_Fr ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb Sp FS fr sp2 jj 1 ->
  evtF rsegs RNG (cmRB_Post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb f len Sp FS fb)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             (Z_to_bv 64 (fs_flag FS 2 jj)) y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 fr) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr)
             z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x85198) fc None (write_to_mem mb (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0)))
        (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mb
    Rf Rlen RS S16 HK Hfb HHM HAE RWIN RWSH RHDR RFPW HB STW fr sp2 jj r
    x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HFr.
  pose proof (cmRB_J_base ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb f len Sp FS fb fr sp2 jj 1 S16 HHM HB STW HFr)
    as HJ.
  destruct (cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  pose proof FPn as (DT & TS & C & T & DB & kk & _ & _ & (_ & _ & _ & _ & PSn) & _).
  destruct HFr as ([(_ & _ & _ & En)|(Hj & _ & _ & _)] & _ & _); [discriminate En|].
  pose proof (cmRB_flag_in_fs FS jj Hj) as Gfl.
  assert (Hro : lib.Lib.Mem.ro_addr rsegs (lib.Lib.Mem.wa (fs_flag FS 2 jj)) = false).
  { pose proof PSn as (_ & _ & HS).
    apply (MemNorm.ro_false_of_wview rsegs mb (MemNorm.normalize rsegs mb) _ REL).
    exact (proj1 (HS (fs_flag FS 2 jj) Gfl)). }
  assert (HW : MemNorm.all_rw rsegs (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (length (lib.Lib.Mem.le1 (Z_to_bv 64 0)))).
  { rewrite lib.Lib.Mem.length_le1. split; [exact Hro | exact I]. }
  assert (HMR : MemNorm.mem_rel rsegs (write_to_mem mb (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0)))
                  (write_to_mem (MemNorm.normalize rsegs mb) (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0)))).
  { split.
    - exact (MemNorm.write_rw rsegs _ mb (MemNorm.normalize rsegs mb) _ (fun x => eq_refl) HW).
    - intros a b Ha Hb. rewrite (MemNorm.write_ro_same rsegs _ mb _ a HW Ha) in Hb. exact (proj2 REL a b Ha Hb). }
  assert (HAt : cmAtRel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (MemNorm.normalize rsegs mb) f len Sp FS fb
                  fr sp2 jj (MemNorm.normalize rsegs mb) (MemNorm.normalize rsegs mb)).
  { split; [exact HJ|]. split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|]. split; [exact MIn|].
    split; [exact (fun P H => H)|]. split; [exact STn | exact PSn]. }
  pose proof (cm_post_rel ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MemNorm.normalize rsegs mb)
    f len Sp FS fb RNG) as L.
  cmRB_feed L.
  match goal with |- evtF _ _ _ (lib.Lib.MState.MS ?R ?F' ?pc ?fc' ?rv _ ?ro) =>
    pose proof (cmRB_ms_rel_MS R F' pc fc' rv _ _ ro HMR) as HR end.
  pose proof (MemNormF.evtF_rel_ro _ _ _ _ HR
    (L fr sp2 jj (MemNorm.normalize rsegs mb) (MemNorm.normalize rsegs mb) r x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6
       z9 z10 z11 u3 u4 u5 u6 Er HAt)) as H.
  eapply evtF_mono; [exact H|].
  intros st (st0 & HP & Hrel & Hsame).
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> &
                  MU & WM & _ & STW' & AC' & SR' & AW' & FP' & TL').
  destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
  assert (Hsm : MemNorm.ro_same rsegs mb (ms_mem st)).
  { intros a Ha. rewrite (Hsame a Ha). exact (MemNorm.write_ro_same rsegs _ mb _ a HW Ha). }
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
  split; [exact Es|].
  split; [exact (MemNorm.munch_rel rsegs _ mb (MemNorm.normalize rsegs mb) (ms_mem st) m' REL Hmr Hsm MU)|].
  split; [exact (MemNorm.wmono_rel rsegs mb (MemNorm.normalize rsegs mb) (ms_mem st) m' REL Hmr Hsm WM)|].
  split; [exact (MemNorm.ro_agree_of_mem_rel rsegs _ _ Hmr)|].
  split; [exact (MemNormTr.stk_of_rel _ _ _ _ Hmr STW')|].
  split; [exact (MemNormTr.asan_cells_of_rel _ _ Hmr AC')|].
  split; [intros P HP; exact (B.ShadowRwOnT.shadow_rw_on_of_rel P _ _ Hmr
                                (SR' P (B.ShadowRwOnT.shadow_rw_on_rel P mb _ REL HP)))|].
  split; [exact (cmRB_addressable_of_rel _ _ _ _ Hmr AW')|].
  split; [exact (MemNormTr.fp_transport m' (ms_mem st) _ _ _ _ _ _ _
                   (fun a bs Hb => proj2 (MemNorm.bytes_at_rel rsegs _ _ a bs Hmr) Hb)
                   (fun lo hi _ Hs => MemNormTr.stk_of_rel _ _ lo hi Hmr Hs) FP')|].
  intros DT0 TS0 C0 T0 DB0 k0 Hc. apply TL'.
  exact (MemNormTr.asan_tls_cells_transport (ms_mem st) m' _ _ _ _ _ _ _
           (fun a bs Hb => proj1 (MemNorm.bytes_at_rel rsegs _ _ a bs Hmr) Hb) Hc).
Qed.

