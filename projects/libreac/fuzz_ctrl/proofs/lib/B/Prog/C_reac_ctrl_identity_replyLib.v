(* lib/B/Prog/C_reac_ctrl_identity_replyLib.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the RE-BASED
   stretches of reac_ctrl_identity_reply (0x848fc), for the cgif-form glue pb_reac_ctrl_identity_reply.

   Re-base ruling a Theorem Labs lane 00:49Z, shared form decisions.md items 26, 27a, 27b, 28 (a working note, not in this delivery).  Measured here and reported
   03:1xZ: the proved run's Section Rep (lib/B/Prog/reac_ctrl_identity_replyF.v (not in this delivery)) has ONE memory variable and
   every one of its memory hypotheses is single-memory at it, so a re-based stretch is the EXISTING lemma APPLIED
   at the stretch's base memory.  There is no proof copying and the _F file is unchanged; this file only names the
   instantiations and builds the two continuation packages (rBI, rJB) at the base, where the entry-relative
   conjuncts collapse by munch_refl / wmono_refl / rr_rd_mono_refl.

   CUTS (the two allocator calls only).  The inline class-1 release at 0x84c34 is NOT a cut: it is a plain store to
   a visible byte and ctl_release_of_free_law is usable mid-run (a Theorem Labs lane / a Theorem Labs lane, decisions.md (a working note, not in this delivery)), so it stays
   inside the last lifted stretch and the journal switches at the return.  rp_td_pre_F / rp_td_post_F of the _F
   file stay available and unused, which is what keeps rp_epiSC / rp_td_sideSC (RB's fine-list copies of the
   accepted rp_epi / rp_td_side) free of a continuation parameter.
     A  entry 0x848fc .. the first slot of __asan_stack_malloc_1   rp_stretchA_F (already at the entry memory)
     E1 the class-1 request                                        astack_malloc_realizes + ctl_fs_of_astack 1
     B  its return 0x8497c .. reac_ctrl_parse's first slot         rrB_B_start .. rrB_B_end (base mb)
     E2 reac_ctrl_parse                                            treac_ctrl_parse_spec + ctl_post_reac_ctrl_parse
     C  its return 0x84a68 .. ret                                  rrB_C (base mb, rrB_rJB_at) on RB's fine write list
                                                                   rWSC; the release inside it, its flag byte in rWSC

   THE SINGLE-MEMORY FACTS AT A STRETCH BASE are Section hypotheses here, each named after the image-B statement
   that supplies it at the composition.  Nothing of image A is Required into this image-B proof (a Theorem Labs lane 03:36Z).
     stk / asan_cells                    <- the stretch base's journal (presence + astk_ok) / ctl_rt_C's asan_cells_at
     shadow_rw_on (reac_ctrl_identity_reply_shadow_R ..) (SW)
                                         <- route (C): ctl_rt_C's cut_shadow / img_shadow at the base, by
                                            C_reac_ctrl_identity_replyCover.rrC_R_on (B.ProgWorldCtlRtC.ctl_rt_C_of_AR)
     fp [1] .. (FP0), fs_place           <- ctl_fp_of_AR         (* OWNER PENDING: B twin of lib/A/ProgWorld_Fs.v *)
     stk FS (FS + FS_SIZE), flags, hint  <- ctl_fs_of_AR         (* OWNER PENDING: B twin of lib/A/ProgWorld_Fs.v *)
     asan_tls_cells (TLS0)               <- ctl_tls_of_AR        (* OWNER PENDING: B twin of lib/A/ProgWorld.v *)
     addressable (window) (AW)           <- ctl_stack_shadow_of_AR (* OWNER PENDING: B twin of lib/A/ProgWorld.v *)
     the new frame after E1              <- ctl_fs_of_astack 1   (* OWNER PENDING: B twin of lib/A/ProgWorldAstack.v,
                                              a Theorem Labs lane's AMENDED text 878cb7afbc4: the frame condition premise after the
                                              [sp - ESTACK, sp) presence premise *)
     the flag byte at the release        <- ctl_release_of_free_law 1 (* OWNER PENDING: same file *)
   mem_inv is NOT taken from AR (decisions.md decision 27 (a working note, not in this delivery)): the stretch runs on MemNorm.normalize rsegs mb, where
   MemNorm.mem_inv_normalize gives it, and the result is carried back to the real memory by the wrapper
   rebase_ro_normalize / evtF_normalize_ro; the latter's image-B twin is lib/B/MemNormF.v (at head lib/B/MemNormF.v:148-152),
   with the text of lib/A/MemNormF.v (at head lib/A/MemNormF.v:148-152; written on a working branch 5dbd293c250).
   lib/B/MemNorm.v DOES exist (merged planning core), so normalize / mem_inv_normalize are Required, not assumed.

   STATEMENTS AND INSTANTIATIONS ONLY: no Axiom, no Parameter, no Admitted. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcRec RcKind RcParse RcParseLib RcReply RcReplyLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_ctrl_record_cksum_verify_c reac_ctrl_identity_reply_c
  asan_stack_malloc_cF_on reac_ctrl_identity_reply_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF RngBytes.
(* The generated copy (unit decision 125): the route-(C) run reac_ctrl_identity_replyF_on.v's Sections verbatim + the
   glue's cut lemmas (analyses/libreac/fuzz_ctrl/glue-B/identity_reply/gen_reac_ctrl_identity_replyRB.py); the run
   itself stays byte-identical. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_ctrl_identity_replyRB.
(* image B's normalization: lib/B/MemNorm.v is on the planning core; its MemNormF twin is not (hypothesis NORMF). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Section RB.
  (* The three callees in their route-(C) footprint form, as reac_ctrl_identity_reply_holds_F_on takes them (RB's
     Section Callees). *)
  Hypothesis MALLOC : asan_stack_malloc_1_contract_F_on.
  Hypothesis PARSE : reac_ctrl_parse_contract_x_F_on.
  Hypothesis CKV : reac_ctrl_record_cksum_verify_contract_F_on.

  (* The stretch's BASE memory is mb.  Every hypothesis below is single-memory at mb (Section Rep's own, with
     m := mb), which is what makes the re-base an instantiation. *)
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (fr len pa pp pn S FS : Z) (g ja jp jn : list byte).
  Hypothesis Rfr : 0 <= fr < 2^64.
  Hypothesis Rlen : 0 <= len < 2^64.
  Hypothesis Rpa : 0 <= pa < 2^64.
  Hypothesis Rpp : 0 <= pp < 2^64.
  Hypothesis Rpn : 0 <= pn < 2^64.
  Hypothesis HS : S < 2^64.
  Hypothesis S16 : S mod 16 = 0.
  Hypothesis HSK : 9072 <= S.
  Hypothesis ST : lib.Lib.Frame.stk rsegs mb (S - 9072) S.                      (* ctlrt_of_AR / ctl_stack_shadow_of_AR *)
  Hypothesis MI : lib.Lib.Mem.mem_inv rsegs mb.                               (* MemNorm.mem_inv_normalize at mb := normalize .. *)
  Hypothesis Hg : length g = 50%nat.
  Hypothesis HF : reply_args fr pa pp pn = true -> 50 <= len ->
    fr + 50 <= 2^64 /\ lib.Lib.Mem.bytes_at rsegs mb fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
    (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn).
  Hypothesis HO : reply_args fr pa pp pn = true ->
    pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
    lib.Lib.Step.rw_cells rsegs mb pa [lib.Lib.Cells.CB 2 ja] /\ lib.Lib.Step.rw_cells rsegs mb pp [lib.Lib.Cells.CB 8 jp] /\ lib.Lib.Step.rw_cells rsegs mb pn [lib.Lib.Cells.CB 8 jn] /\
    (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
    (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn).
  Hypothesis AC : asan_cells mb.                                  (* ctl_rt_C's asan_cells_at *)
  (* route (C): RB's (F_on's) narrowed premise; ctl_rt_C's cut_shadow / img_shadow by Cover.rrC_R_on *)
  Hypothesis SW : shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mb.
  Hypothesis HHM : HIGHMEM_BEG <= S - 9072.
  Hypothesis HAE : S <= APPMEM_END.
  Hypothesis AW : addressable mb (S - 9072) 9072.                 (* ctl_stack_shadow_of_AR (NO other source) *)
  Hypothesis AFfr : reply_args fr pa pp pn = true -> 50 <= len -> addressable mb fr 50.
  Hypothesis AOUT : reply_args fr pa pp pn = true ->
    addressable mb pa 2 /\ addressable mb pp 8 /\ addressable mb pn 8 /\
    (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn).
  Hypothesis ABC : addressable mb REAC_CTRL_PARSE_BC 6.
  Hypothesis HBCMP : lib.Lib.Mem.bytes_at rsegs mb REAL_BCMP (lib.Lib.Mem.le8 (lib.Lib.Mem.wa BCMP)).
  Hypothesis HMEMCMP : lib.Lib.Mem.bytes_at rsegs mb REAL_MEMCMP (lib.Lib.Mem.le8 (lib.Lib.Mem.wa MEMCMP)).
  Hypothesis HGCF : lib.Lib.Mem.bytes_at rsegs mb GOT_CF (lib.Lib.Mem.le8 (lib.Lib.Mem.wa CF)).
  Hypothesis HCF254 : lib.Lib.Mem.bytes_at rsegs mb (CF + 254) [Z_to_bv 8 1].
  Hypothesis HCF255 : lib.Lib.Mem.bytes_at rsegs mb (CF + 255) [Z_to_bv 8 1].
  Hypothesis FP0 : fp [1%nat] mb (bv_unsigned tp) FS (S - 9072) S
    (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn). (* ctl_fp_of_AR *)
  Hypothesis TLS0 : reac_ctrl_identity_reply_tls mb (bv_unsigned tp) FS (S - 9072) S.        (* ctl_tls_of_AR *)
  (* The footprint premises are memory-free, so they are the statement's own, unchanged by the re-base. *)
  Variable RNG : ExecF.footprint.
  Hypothesis RBY : rng_bytes RNG.
  Hypothesis RIMG : rng RNG 0x10000 0x5ee000.
  Hypothesis RWIN : rng RNG (S - 9072) 9072.
  Hypothesis SSW : shspan RNG (S - 9072) S.
  Hypothesis SCW : shcov RNG (S - 9072) 9072.
  Hypothesis SKW : shkov RNG (S - 288) 160.
  Hypothesis RFR : reply_args fr pa pp pn = true -> 50 <= len -> rng RNG fr 50.
  Hypothesis SCF : reply_args fr pa pp pn = true -> 50 <= len -> shcov RNG fr 50.
  Hypothesis SKF : reply_args fr pa pp pn = true -> 50 <= len -> shkov RNG fr 50.
  Hypothesis RPA : reply_args fr pa pp pn = true -> rng RNG pa 2.
  Hypothesis SCPA : reply_args fr pa pp pn = true -> shcov RNG pa 2.
  Hypothesis RPP : reply_args fr pa pp pn = true -> rng RNG pp 8.
  Hypothesis SCPP : reply_args fr pa pp pn = true -> shcov RNG pp 8.
  Hypothesis RPN : reply_args fr pa pp pn = true -> rng RNG pn 8.
  Hypothesis SCPN : reply_args fr pa pp pn = true -> shcov RNG pn 8.
  Hypothesis SKBC : shkov RNG REAC_CTRL_PARSE_BC 6.
  Hypothesis RFSS : rng RNG FS (fs_frame FS 0 0 - FS).
  Hypothesis RFLG : rng RNG (fs_flag FS 1 0) (fs_M 1).
  Hypothesis RFRM : rng RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SCFM : shcov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis SKFM : shkov RNG (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0).
  Hypothesis RW1 : Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_w [1%nat] FS).
  Hypothesis RTLS : forall DT TS C T DB k, asan_tls_cells mb (bv_unsigned tp) DT TS C T DB k ->
    Forall (fun iv => rng RNG (fst iv) (snd iv - fst iv)) (fp_tls (bv_unsigned tp) DT TS C T DB k).

  (* ---- The two continuation packages AT THE BASE: the entry-relative conjuncts collapse. ---- *)

  (* rBI at (mb, mb): what the stretch after the fake-stack call starts from.  munch / wmono / rr_rd_mono are
     reflexive at the base; the rest are the single-memory facts the astack post and AR give. *)
  Lemma rrB_rBI_at : forall G j nn,
    lib.Lib.Step.rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    (nn = 1 -> lib.Lib.Mem.bytes_at rsegs mb (G + 120) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 1 j))) /\
               lib.Lib.Mem.bytes_at rsegs mb (fs_flag FS 1 j) [Z_to_bv 8 1]) ->
    rBI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb S FS G j nn mb.
  Proof using MI.
    intros G j nn SV FL. unfold rBI.
    split; [apply lib.Lib.Frame.munch_refl|]. split; [apply lib.Lib.Frame.wmono_refl|]. split; [apply rr_rd_mono_refl|].
    split; [exact MI|]. split; [exact SV | exact FL].
  Qed.

  (* rJB at (mb, mb): what stretch C starts from at reac_ctrl_parse's return, in RB's fine form rJBSC, whose added
     conjunct munch (rWSC G j) mb mb is munch_refl (rJBSC_base).  munch / wmono / rr_rd_mono are reflexive at the
     base and the window apart from the frame is rr_awx_m (AW); the rest are the single-memory facts the parse post
     and AR give. *)
  Lemma rrB_rJB_at : forall G j nn,
    reply_args fr pa pp pn = true ->
    lib.Lib.Step.rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    lib.Lib.Step.rw_cells rsegs mb (G + 32) [lib.Lib.Cells.CB 36 (snd (ctrlparse len g))] ->
    (nn = 1 -> lib.Lib.Mem.bytes_at rsegs mb (G + 120) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 1 j))) /\
               lib.Lib.Mem.bytes_at rsegs mb (fs_flag FS 1 j) [Z_to_bv 8 1]) ->
    rJBSC ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb fr len pa pp pn S FS g ja jp jn G j nn mb.
  Proof using Rfr Rlen Rpa Rpp Rpn ST MI Hg HF HO AC SW AW AFfr AOUT FP0 TLS0.
    intros G j nn RAb SV REC FL.
    apply rJBSC_base. unfold rJB, rCore, rOUTC.
    destruct (HO RAb) as (_ & _ & _ & Ca & Cp & Cn & _).
    destruct (AOUT RAb) as (Aa & Ap & An & _).
    split; [apply lib.Lib.Frame.munch_refl|].
    split.
    { split; [apply lib.Lib.Frame.wmono_refl|]. split; [apply rr_rd_mono_refl|]. split; [exact MI|].
      split; [exact SV|]. split; [exact (rr_awx_m mb fr len pa pp pn S g Rfr Rlen Rpa Rpp Rpn Hg AW G)|].
      split; [exact FP0|]. split; [exact TLS0 | exact FL]. }
    split; [exact REC|].
    split; [intros HL; destruct (HF RAb HL) as (_ & HB & _); exact (conj HB (AFfr RAb HL))|].
    split; [exact (conj Ca (conj Cp (conj Cn (conj Aa (conj Ap An)))))|].
    split; [exact ST|]. split; [exact AC | exact SW].
  Qed.

  (* The stretch AFTER the class-1 request, from its return slot 0x8497c: the existing cut lemma at m := mb and
     m2 := mb.  Its premises are this Section's, so the re-base adds no proof. *)
  Lemma rrB_B_start : forall (Q : machine_state -> Prop),
    rKB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS RNG Q ->
    forall (jj : Z) (u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
      0 <= jj < fs_M 1 ->
      rBI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb S FS (fs_frame FS 1 jj) jj 1 mb ->
      ExecF.evtF rsegs RNG Q
        (lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x8497c) (Z_to_bv 64 (rA S)) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
                 (Z_to_bv 64 (fs_frame FS 1 jj)) x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp)
                 (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 s9 s10 (lib.Lib.Mem.wa ASAN_K) u3 u4 u5 u6)
            F (Z_to_bv 64 0x8497c) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
  Proof using Rfr Rlen Rpa Rpp Rpn HS S16 HSK ST Hg SW HHM HAE FP0 RWIN SCW RFRM SCFM.
    intros Q K jj u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj HB.
    exact (rp_stretchB0_F ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g
             Rfr Rlen Rpa Rpp Rpn HS S16 HSK ST Hg SW HHM HAE FP0 RNG RWIN SCW RFRM SCFM Q K jj mb
             u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj HB).
  Qed.

  (* The end of that stretch: the four register steps into reac_ctrl_parse's first slot.  rp_call_pre_F takes no
     memory premise at all, so it is already base-relative; it is named here for the glue. *)
  Lemma rrB_B_end : forall (G fv spc : Z) (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
    ExecF.evtF rsegs RNG
      (fun ms' => ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x84a68) (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S)
                               (Z_to_bv 64 (rA S)) (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32)) x13 x14
                               x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr)
                               (Z_to_bv 64 pa) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32))
                               (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (lib.Lib.Mem.wa ASAN_K) x28 x29 x30 x31)
                          F (Z_to_bv 64 REAC_CTRL_PARSE) fc None mb (lib.Lib.PropExec.seg_rom rsegs))
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 spc) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 (rA S)) (Z_to_bv 64 4)
               x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 fv) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr)
               (Z_to_bv 64 pa) (Z_to_bv 64 len) (Z_to_bv 64 (G + 32)) (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G)
               (lib.Lib.Mem.wa ASAN_K) x28 x29 x30 x31)
          F (Z_to_bv 64 0x84a58) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
  Proof using.
    intros G fv spc x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31.
    exact (rp_call_pre_F gp tp F fc fr len pa pp pn S RNG G fv spc mb
             x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31).
  Qed.

  (* The LAST stretch, from reac_ctrl_parse's return 0x84a68 to the function's own ret, at m := mb: RB's W-fine
     chain that rp_CSC runs (rp_tagSC over rp_failSC and rp_storesSC, each after rp_f8SC).  Its continuations carry
     the fine write list rWSC G j (the window, the frame, its 16 shadow bytes, the frame's flag byte, the OUT cells
     under reply_ok) and take a post indexed by the frame, QF G j.  The inline class-1 release at 0x84c34 is inside
     it; its flag byte is in rWSC. *)
  Lemma rrB_C : forall (QF : Z -> Z -> machine_state -> Prop),
    rKESC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g RNG QF ->
    rKFSC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g ja jp jn RNG QF.
  Proof using All.
    intros QF KE.
    pose (KT := rp_f8SC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g ja jp jn
                  Rfr Rlen Rpa Rpp Rpn S16 HSK ST Hg HF HO SW HHM HAE AFfr AOUT FP0 RNG SCW
                  RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN SCFM QF KE).
    exact (rp_tagSC CKV ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g ja jp jn
             Rfr Rlen Rpa Rpp Rpn HS S16 HSK ST Hg HF HO HHM HAE AFfr AOUT FP0 RNG RIMG RWIN
             RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN RFRM QF
             (rp_failSC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g RNG QF KT)
             (rp_storesSC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g ja jp jn
                Rfr Rlen Rpa Rpp Rpn HS Hg HF HO HHM HAE AFfr AOUT FP0 RNG
                RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN QF KT)).
  Qed.

  (* ---- S-B: the stretch AFTER the class-1 request, from its return slot 0x8497c, ending EITHER at reac_ctrl_parse's
     first slot (the four pointers non-null) OR at the epilogue entry 0x84bdc with a0 = -1 (a null pointer).  Both
     ends are allocator events or the start of the shared tail, so the stretch stops there.  The run is RB's
     FRAME-FIXED chain rp_stretchB0G -> rp_nullG -> (rKEG: stop) | rp_parse_CG -> (rKCG: rp_call_pre_F, stop), at
     m := mb, so the end state names the frame G = fs_frame FS 1 jj the fake-stack call returned. ---- *)
  Definition rrB_QSB (jj : Z) (ms : machine_state) : Prop :=
    (exists (mc m5 : word -> option byte) (x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
       ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR (Z_to_bv 64 0x84a68) (Z_to_bv 64 (rA S)) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
                    (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 ((fs_frame FS 1 jj) + 32)) x13 x14 x15 x16 x17
                    (Z_to_bv 64 (fs_frame FS 1 jj)) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
                    (Z_to_bv 64 len) (Z_to_bv 64 ((fs_frame FS 1 jj) + 32)) (Z_to_bv 64 ((fs_frame FS 1 jj) / 8 + ASAN_K))
                    (Z_to_bv 64 (fs_frame FS 1 jj)) (lib.Lib.Mem.wa ASAN_K) x28 x29 x30 x31)
               F (Z_to_bv 64 REAC_CTRL_PARSE) fc None m5 (lib.Lib.PropExec.seg_rom rsegs) /\
       rBI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb S FS (fs_frame FS 1 jj) jj 1 mc /\
       reply_args fr pa pp pn = true /\
       lib.Lib.Frame.munch [((fs_frame FS 1 jj) / 8 + ASAN_K + 4, (fs_frame FS 1 jj) / 8 + ASAN_K + 9)] mc m5 /\
       lib.Lib.Frame.wmono rsegs mc m5 /\ rr_rd_mono mc m5 /\ lib.Lib.Mem.mem_inv rsegs m5 /\
       lib.Lib.Mem.bytes_at rsegs m5 ((fs_frame FS 1 jj) / 8 + ASAN_K + 4)
         [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4]) \/
    (exists (mc : word -> option byte) (r : Z)
            (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word),
       ms = lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 r) x11 x12 x13 x14 x15 x16 x17
                    (Z_to_bv 64 (fs_frame FS 1 jj)) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 ((fs_frame FS 1 jj) / 8 + ASAN_K))
                    (Z_to_bv 64 (fs_frame FS 1 jj)) x27 x28 x29 x30 x31) F (Z_to_bv 64 0x84bdc) fc None mc
               (lib.Lib.PropExec.seg_rom rsegs) /\
       rBI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb S FS (fs_frame FS 1 jj) jj 1 mc /\
       rEI0 ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb fr len pa pp pn S FS g (fs_frame FS 1 jj) jj 1 mc /\
       r = reply_ret fr len pa pp pn g /\
       (* rKEG hands this to its continuation (RB); the -1 tail's base facts need it (rrB_tail_lifted's OUTb) *)
       (reply_ok fr len pa pp pn g = true -> rOUTF fr pa pp pn g mc)).

  Lemma rrB_SB_run : forall (jj : Z) (rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 : word),
    0 <= jj < fs_M 1 -> rBI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb S FS (fs_frame FS 1 jj) jj 1 mb ->
    ExecF.evtF rsegs RNG (rrB_QSB jj)
      (lib.Lib.MState.MS (lib.Lib.Frame.mkR rr0 (Z_to_bv 64 (rA S)) gp tp u0 u1 u2 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
               (Z_to_bv 64 (fs_frame FS 1 jj)) x1 x2 x3 x4 x5 x6 x7 s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp)
               (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 s9 s10 (lib.Lib.Mem.wa ASAN_K) u3 u4 u5 u6)
          F (Z_to_bv 64 0x8497c) fc None mb (lib.Lib.PropExec.seg_rom rsegs)).
  Proof using Rfr Rlen Rpa Rpp Rpn HS S16 HSK ST Hg HF HO SW HHM HAE AW AFfr AOUT FP0 TLS0
              RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN RWIN SCW RFRM SCFM.
    intros jj rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj HB.
    assert (HK : rFK S FS (fs_frame FS 1 jj) (fs_frame FS 1 jj) (rA S) jj 1) by (right; repeat split; lia).
    assert (KC : rKCG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS RNG
                   (fs_frame FS 1 jj) (fs_frame FS 1 jj) (rA S) jj 1 (rrB_QSB jj)).
    { intros mc m5 y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 HB' RAb MU5 WM5 RM5 MI5 BS5.
      eapply ExecF.evtF_cut;
        [exact (rp_call_pre_F gp tp F fc fr len pa pp pn S RNG (fs_frame FS 1 jj) (fs_frame FS 1 jj) (rA S) m5
                  y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31) |].
      intros ms' ->. apply ExecF.evtF_done. left.
      exists mc, m5, y5, y6, y7, y13, y14, y15, y16, y17, y28, y29, y30, y31.
      split; [reflexivity|]. split; [exact HB'|]. split; [exact RAb|].
      split; [exact MU5|]. split; [exact WM5|]. split; [exact RM5|]. split; [exact MI5 | exact BS5]. }
    assert (KE : rKEG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g RNG
                   (fs_frame FS 1 jj) (fs_frame FS 1 jj) (rA S) jj 1 (rrB_QSB jj)).
    { intros mc r y1 y2 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y27 y28 y29 y30 y31
        HB' HEI HOUT Er.
      apply ExecF.evtF_done. right.
      exists mc, r, y1, y2, y5, y6, y7, y9, y11, y12, y13, y14, y15, y16, y17, y19, y20, y21, y22, y23, y24, y27,
        y28, y29, y30, y31.
      split; [reflexivity|]. split; [exact HB'|]. split; [exact HEI|]. split; [exact Er | exact HOUT]. }
    pose (KN := rp_parse_CG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g
                  Rfr Rlen Rpa Rpp Rpn S16 HSK ST Hg SW HHM HAE FP0 RNG SCW SCFM (rrB_QSB jj)
                  (fs_frame FS 1 jj) (fs_frame FS 1 jj) (rA S) jj 1 HK KC).
    pose (KB := rp_nullG ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g ja jp jn
                  Rfr Rlen Rpa Rpp Rpn S16 HSK ST Hg HF HO SW HHM HAE AW AFfr AOUT FP0 TLS0 RNG
                  RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN (rrB_QSB jj) (fs_frame FS 1 jj) (fs_frame FS 1 jj) (rA S) jj 1 HK KE KN).
    exact (rp_stretchB0G ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g
             Rfr Rlen Rpa Rpp Rpn HS S16 HSK ST Hg SW HHM HAE FP0 RNG RWIN SCW RFRM SCFM (rrB_QSB jj) jj KB mb
             rr0 u0 u1 u2 x1 x2 x3 x4 x5 x6 x7 u3 u4 u5 u6 Hjj HB).
  Qed.
End RB.
