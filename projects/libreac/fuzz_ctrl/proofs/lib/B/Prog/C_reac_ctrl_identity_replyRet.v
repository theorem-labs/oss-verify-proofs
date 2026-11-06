(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10 (a Theorem Labs lane). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/C_reac_ctrl_build_asLib.v, with its module paths and module names changed; 1068 of its 1130 lines of code are new or changed and 635 lines of the source are left out. *)
(* lib/B/Prog/C_reac_ctrl_identity_replyRet.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the TAIL of the cgif-form
   glue pb_reac_ctrl_identity_reply (reac_ctrl_identity_reply, 0x848fc), on the plan of record
   analyses/libreac/fuzz_ctrl/glue-B/identity_reply/pb_reac_ctrl_identity_reply.plan.md, section 1, rows S-C and ret.

   rule 24: no function proved here.  Released-proof lookup of record
   (`proof-index reac_ctrl_identity_reply reac_ctrl_identity_reply_contract_F`,
   lookup-reac_ctrl_identity_reply.txt (a working note, not in this delivery), checker CONFIRM in
   lookup-check.md (a working note, not in this delivery)): At ossv/recipes c5e779efe8c (2026-10-31), no released proof outside this unit.  Written new.

   THE TWO ENTRIES OF THE SHARED TAIL.  Both lifts run RB's fine-write-list chain at a stretch BASE memory mb (the chain
   base is normalize mb) and end in the same post rrB_SCpost (RB's rQSC over the normalized run, the real end state, the
   read-only and hidden bytes kept):
     rrB_SC_lifted    from reac_ctrl_parse's return 0x84a68 (rKFSC's state), by RB's rp_CSC, the chain
                      rp_tagSC -> (rp_failSC | rp_storesSC) -> rp_f8SC -> rp_epiSC.  It is Lib's rrB_C at QF := rQSC,
                      KE := rp_epiSC: rp_CSC is that chain without rrB_C's `Proof using All`, which would add
                      reac_ctrl_parse's and __asan_stack_malloc_1's contracts and nine memory / footprint premises that
                      S-C never uses (ABC, HBCMP, HMEMCMP, HGCF, HCF254, HCF255, RBY, SSW, SKW, SKBC, RFSS, RW1, RTLS).
     rrB_tail_lifted  from the epilogue entry 0x84bdc (rKESC's state), by RB's rp_epiSC: the right end of S-B
                      (Lib.rrB_QSB, a0 = -1, a null pointer), where the same epilogue (with the class-1 release) runs.
   S-C is not cut at 0x84bdc: a cut there would need the chain's base facts at an intermediate memory the composition
   does not hold; the chain lemma itself composes S-C with the tail (rp_CSC uses rp_epiSC).

   WHICH LIFT.  GlueLift.rrB_lift (the run on normalize mb), not rrB_lift_st (the run on mb itself): RB's chain needs
   mem_inv at its base (rCore, rrB_rJB_at's MI), which holds at normalize mb (MemNorm.mem_inv_normalize) and not at the
   real memory.  The release step does not need the fsteps run that rrB_lift_st gives: GlueLift.rrB_journal_free (Qed)
   takes the run's memories (mem_rel, ro_same, the hidden bytes, the normalized end memory off the write set), which is
   what rrB_lift gives; so B.ProgWorldAstack.ctl_release_of_free_law (which needs the fsteps run) is not used.

   THE WRITE SET of the tail, Wr := ~ outside (rWSC G j) (RB, the fine list): the window [S - 9072, S) (awr_byte's
   window arm), the frame G = frame_addr lyb 1 pos and its 16 shadow bytes (the in_frames arm, (1, pos) owned at the
   base), the frame's flag byte (rrB_journal_free's flag arm; rQSC's last conjunct gives it 0 at the end, ReplySC
   dceac150ddc), the three OUT cells under reply_ok (the spec's P11 awr_byte, moved to the base state by rrR_awr_tr).
   One rrB_journal_free step: own drops (1, pos), S' = stack_free_state 1 pos Sb.

   acall_kept.  The post's acall_kept over [S - 9072, S) is built step by step from the function's entry (lyc, Sc, W,
   memc): rrB_K_SA (S-A's munch), rrB_K_E1 (the class-1 request's acall_kept), rrB_K_SB (S-B's munch and keeps),
   rrB_K_E2 (reac_ctrl_parse's acall_kept), then inside rrB_ret the tail's munch (rWSC).  Two generic steps carry it:
   rrB_K_raw (a lifted run, raw bytes kept off its write set) and rrB_K_ev (a call, its own acall_kept over a window
   inside [S - 9072, S)).  The bytes the function itself creates and writes (its frame, that frame's shadow and flag)
   are apart from every class acall_kept keeps (rrR_new_apart, from the AR laws: a Theorem Labs lane's C_reac_ctrl_parseW.v
   rcpW_apart_* (at head lib/B/Prog/C_reac_ctrl_parseW.v:246, :278, :310; from a working branch 2e352cba74d), copied with the frame-distinctness derived here).

   SECTION HYPOTHESES: LAWS (AR_laws; Sections RetW, Steps, Ret), ML (model_laws), ASF (astack_free_law), FFL
   (frame_flag_lawP) (Section Ret), the same names and texts as GlueLift.v's Section JournalFree and the spec's plan
   comment (OWNER PENDING: LAWS / ML core B bundle, the record core's TfibLib; ASF / FFL a Theorem Labs lane's class-1 fake-stack
   rules, a working branch ff613211c11).  segs_low is PROVED (B.ProgWorld.pws_segs_low); the callee contract
   reac_ctrl_record_cksum_verify_contract_F_on (RB's Section Callees, route (C)) is PROVED
   (reac_ctrl_record_cksum_verify_F.reac_ctrl_record_cksum_verify_holds_F_on).  The two lifts take RB's narrowed
   premise shadow_rw_on (reac_ctrl_identity_reply_shadow_R ..) at the real base memory and move it to normalize mb by
   B.ShadowRwOnT.shadow_rw_on_normalize.  Nothing of image A is Required; no Axiom, Parameter or Admitted. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c reac_ctrl_identity_reply_c
  reac_ctrl_identity_reply_c_on reac_ctrl_identity_replyRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YK04 YK04R YA0n YA0nR YM05 YI16 YK14.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0d YG0n YG0v YK0s YCbq YP09 YK1b.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG0s YI00 YI04 YB1v YN2e YO0f.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF ProgBridge ProgBridgeData ShadowRwOnT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld ProgWorld_Fs ProgWorldAstack ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP C_reac_ctrl_identity_replyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import GlueLift.
(* rrB_SBpost (S-B's post) and rrB_WSB (S-B's write set). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_reac_ctrl_identity_replyPf
  C_reac_ctrl_identity_replyComp.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_identity_replyE2 C_reac_ctrl_identity_reply
  C_reac_ctrl_parse reac_ctrl_record_cksum_verify_F.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
Import ListNotations.
Open Scope Z_scope.

(* ==== 1. The post of the shared tail and its two lifted entries. ==== *)
Section SC.
Context {fx : lib.Reusable.YK11.FPState}.

(* The tail's post at base mb: an end state s0' of the chain run over normalize mb (RB's rQSC at the frame G, j),
   related by ms_rel to the real end state ms', mb's read-only bytes kept, mb's hidden bytes kept, the model step, and
   (route (C)) the frame G's 16 shadow bytes readable at the run's base normalize mb: rQSC's post transports a
   shadow_rw_on fact of its base to its end, and rrB_ret needs those bytes readable at the end (the journal step). *)
Definition rrB_SCpost (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (fr len pa pp pn S FS : Z) (g : list byte) (G j : Z)
    (W : lib.Reusable.YA0n.world rsegs) (md : Model) (ms' : machine_state) (md' : Model) : Prop :=
  (exists s0', rQSC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs mb)
                 fr len pa pp pn S FS g G j s0' /\
     B.MemNorm.ms_rel rsegs ms' s0' /\ B.MemNorm.ro_same rsegs mb (ms_mem ms')) /\
  (forall x : word, lib.Reusable.YA0n.w_H W x = true -> ms_mem ms' x = mb x) /\
  lib.Reusable.YK04.same_but_materialized md md' /\
  shadow_rw_on (fun a => shadow_addr G <= a < shadow_addr G + 16) (B.MemNorm.normalize rsegs mb).

(* A class-1 frame's 16 shadow bytes lie in R's class-1 block disjunct (asan_stack_malloc_shadow_R FS 1). *)
Lemma rrR_frame_sh_inR : forall fr len pa pp pn S FS jj, 0 <= jj < fs_M 1 -> forall a,
  shadow_addr (fs_frame FS 1 jj) <= a < shadow_addr (fs_frame FS 1 jj) + 16 ->
  reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS a.
Proof.
  intros fr len pa pp pn S FS jj Hj a Ha. unfold reac_ctrl_identity_reply_shadow_R. cbv zeta. right; left.
  unfold asan_stack_malloc_c_on.asan_stack_malloc_shadow_R. rewrite !rrF_fs_frame1 in *.
  change (fs_M 1) with 8192 in Hj. unfold shadow_addr in *. Z.div_mod_to_equations. lia.
Qed.

(* S-C LIFTED from the REAL base memory mb (the memory after reac_ctrl_parse returns at 0x84a68; the composition
   takes mb := mp).  Premises: the chain's single-memory facts at mb (moved to normalize mb here, as rrB_SB_lifted does),
   rJB's pieces at mb (the 13 saved registers, parse's 36 bytes at G + 32, the flag-pointer word at G + 120 and the
   flag byte 1), and the run's footprint at RNG_W (w_H W) (the image range is img_vis_W's). *)
Lemma rrB_SC_lifted : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall (W : lib.Reusable.YA0n.world rsegs) (md : Model)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (fr len pa pp pn S FS : Z) (g ja jp jn : list byte) (jj : Z)
    (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 -> 9072 <= S ->
    B.MemNorm.ro_agree rsegs mb ->
    stk rsegs mb (S - 9072) S -> length g = 50%nat ->
    (reply_args fr pa pp pn = true -> 50 <= len ->
       fr + 50 <= 2^64 /\ bytes_at rsegs mb fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
       (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)) ->
    (reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs mb pa [CB 2 ja] /\ rw_cells rsegs mb pp [CB 8 jp] /\ rw_cells rsegs mb pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)) ->
    (reply_args fr pa pp pn = true -> ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn) ->
    asan_cells mb -> shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mb ->
    HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END ->
    addressable mb (S - 9072) 9072 ->
    (reply_args fr pa pp pn = true -> 50 <= len -> addressable mb fr 50) ->
    (reply_args fr pa pp pn = true ->
       addressable mb pa 2 /\ addressable mb pp 8 /\ addressable mb pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    fp [1%nat] mb (bv_unsigned tp) FS (S - 9072) S
      (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) ->
    reac_ctrl_identity_reply_tls mb (bv_unsigned tp) FS (S - 9072) S ->
    reply_args fr pa pp pn = true -> 0 <= jj < fs_M 1 ->
    rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    rw_cells rsegs mb (fs_frame FS 1 jj + 32) [CB 36 (snd (lib.Prog.RcParse.ctrlparse len g))] ->
    bytes_at rsegs mb (fs_frame FS 1 jj + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 jj))) ->
    bytes_at rsegs mb (fs_flag FS 1 jj) [Z_to_bv 8 1] ->
    ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (S - 9072) 9072 ->
    shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (S - 9072) 9072 ->
    (reply_args fr pa pp pn = true -> 50 <= len -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> 50 <= len -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> 50 <= len -> shkov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pa 2) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pa 2) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pp 8) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pp 8) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pn 8) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pn 8) ->
    ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_flag FS 1 0) (fs_M 1) ->
    ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_frame FS 1 0)
      (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0) ->
    shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0) ->
    (forall ms' md', rrB_SCpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g
                       (fs_frame FS 1 jj) jj W md ms' md' -> lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (MS (mkR x1 (Z_to_bv 64 (rA S)) gp tp x5 x6 x7 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
                      (Z_to_bv 64 (fst (lib.Prog.RcParse.ctrlparse len g))) x11 x12 x13 x14 x15 x16 x17
                      (Z_to_bv 64 (fs_frame FS 1 jj)) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa)
                      (Z_to_bv 64 len) (Z_to_bv 64 (fs_frame FS 1 jj + 32))
                      (Z_to_bv 64 (fs_frame FS 1 jj / 8 + ASAN_K)) (Z_to_bv 64 (fs_frame FS 1 jj))
                      (wa ASAN_K) x28 x29 x30 x31)
                 F (Z_to_bv 64 0x84a68) fc None mb (seg_rom rsegs)) md) Q.
Proof.
  intros Hwx W md ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g ja jp jn jj
    x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 Q
    Rfr Rlen Rpa Rpp Rpn HS S16 HSK RO ST Hg HF HO HOimg AC SW HHM HAE AW AFfr AOUT FP0 TLS0 RAb Hjj SV REC FL1 FL2
    RWIN SCW RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN RFLG RFRM SCFM K.
  pose proof FP0 as (DT & TS & C & T & DB & kk & _ & _ & (FS0 & FS4 & FSGT & FSapp & _) & _ & _ & _ & HFSlo & _).
  unfold ASAN_GT, FS_SIZE in *.
  set (RG := B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) in *.
  pose proof (rrF_fs_frame1 FS jj) as EG.
  set (G := fs_frame FS 1 jj) in *.
  assert (EM : fs_M 1 = 8192) by reflexivity.
  assert (RIMG : ExecF.rng RG 0x10000 0x5ee000).
  { pose proof (B.ProgBridge.rng_of_visible _ _ _ (B.ProgBridge.img_vis_W W)) as R.
    unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI in R. exact R. }
  (* the single-memory facts at normalize mb *)
  assert (STn : stk rsegs (B.MemNorm.normalize rsegs mb) (S - 9072) S)
    by (apply B.MemNormTr.stk_normalize_ro; [exact RO | unfold ImgBounds.IMG_HI; unfold HIGHMEM_BEG in HHM; lia | exact ST]).
  pose proof (B.MemNorm.mem_inv_normalize rsegs mb) as MIn.
  pose proof (B.MemNormTr.asan_cells_normalize mb RO AC) as ACn.
  assert (HFn : reply_args fr pa pp pn = true -> 50 <= len ->
     fr + 50 <= 2^64 /\ bytes_at rsegs (B.MemNorm.normalize rsegs mb) fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
     (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)).
  { intros RA HL. destruct (HF RA HL) as (A1 & A2 & A3). split; [exact A1|]. split; [|exact A3].
    exact (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO A2). }
  assert (NR : forall p n, ImgBounds.IMG_HI <= p -> p + n <= 2 ^ 64 -> forall i, 0 <= i < n ->
                 ro_addr rsegs (wa (p + i)) = false)
    by (intros p n Hp Hn i Hi; apply (B.MemNormTr.ro_addr_above_img_range p n Hp Hn i Hi)).
  assert (HOn : reply_args fr pa pp pn = true ->
     pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
     rw_cells rsegs (B.MemNorm.normalize rsegs mb) pa [CB 2 ja] /\
     rw_cells rsegs (B.MemNorm.normalize rsegs mb) pp [CB 8 jp] /\
     rw_cells rsegs (B.MemNorm.normalize rsegs mb) pn [CB 8 jn] /\
     (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
     (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)).
  { intros RA. destruct (HO RA) as (A1 & A2 & A3 & C1 & C2 & C3 & REST).
    destruct (HOimg RA) as (I1 & I2 & I3).
    destruct (AOUT RA) as ((B0 & _ & B2 & _) & (B3 & _ & B5 & _) & (B6 & _ & B8 & _) & _).
    unfold APPMEM_END in *.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pa _ RO);
            [intros i Hi; apply (NR pa 2); [exact I1 | lia | cbn in Hi; lia] | exact C1]|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pp _ RO);
            [intros i Hi; apply (NR pp 8); [exact I2 | lia | cbn in Hi; lia] | exact C2]|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pn _ RO);
            [intros i Hi; apply (NR pn 8); [exact I3 | lia | cbn in Hi; lia] | exact C3]|].
    exact REST. }
  pose proof (B.ShadowRwOnT.shadow_rw_on_normalize _ mb RO SW) as SWn.
  pose proof (B.MemNormTr.addressable_normalize mb _ _ RO AW) as AWn.
  assert (AFfrn : reply_args fr pa pp pn = true -> 50 <= len -> addressable (B.MemNorm.normalize rsegs mb) fr 50)
    by (intros RA HL; exact (B.MemNormTr.addressable_normalize mb _ _ RO (AFfr RA HL))).
  assert (AOUTn : reply_args fr pa pp pn = true ->
     addressable (B.MemNorm.normalize rsegs mb) pa 2 /\ addressable (B.MemNorm.normalize rsegs mb) pp 8 /\
     addressable (B.MemNorm.normalize rsegs mb) pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)).
  { intros RA. destruct (AOUT RA) as (B1 & B2 & B3 & REST).
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B1)|].
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B2)|].
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B3) | exact REST]. }
  pose proof (B.MemNormTr.fp_normalize _ mb _ _ _ _ _ _ RO FP0) as FP0n.
  assert (TLS0n : reac_ctrl_identity_reply_tls (B.MemNorm.normalize rsegs mb) (bv_unsigned tp) FS (S - 9072) S)
    by exact (B.MemNormTr.tls_dj_normalize mb (bv_unsigned tp)
                (fp_w [1%nat] FS ++ [(shadow_addr (S - 9072), shadow_addr S)]) RO TLS0).
  assert (SVn : rw_cells rsegs (B.MemNorm.normalize rsegs mb) (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (B.MemNormTr.rw_cells_normalize mb _ _ RO); [|exact SV].
    intros i Hi. apply (NR (S - 104) 104); [unfold ImgBounds.IMG_HI; unfold HIGHMEM_BEG in HHM; lia | lia | cbn in Hi; lia]. }
  assert (RECn : rw_cells rsegs (B.MemNorm.normalize rsegs mb) (G + 32) [CB 36 (snd (lib.Prog.RcParse.ctrlparse len g))]).
  { apply (B.MemNormTr.rw_cells_normalize mb _ _ RO); [|exact REC].
    intros i Hi. apply (NR (G + 32) 36); [unfold ImgBounds.IMG_HI; lia | lia | cbn in Hi; lia]. }
  pose proof (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO FL1) as FL1n.
  pose proof (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO FL2) as FL2n.
  (* rJBSC at the base, the frame, the chain *)
  pose proof (rrB_rJB_at ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs mb)
                fr len pa pp pn S FS g ja jp jn Rfr Rlen Rpa Rpp Rpn STn MIn Hg HFn HOn ACn SWn AWn AFfrn AOUTn
                FP0n TLS0n G jj 1 RAb SVn RECn (fun _ => conj FL1n FL2n)) as RJB.
  assert (HK : rFK S FS G G (rA S) jj 1) by (right; repeat split; first [exact (proj1 Hjj) | exact (proj2 Hjj) | reflexivity]).
  pose proof (rp_CSC reac_ctrl_record_cksum_verify_F.reac_ctrl_record_cksum_verify_holds_F_on
                ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs mb)
                fr len pa pp pn S FS g ja jp jn Rfr Rlen Rpa Rpp Rpn HS S16 HSK STn Hg HFn HOn ACn SWn HHM HAE
                AFfrn AOUTn FP0n RG RIMG RWIN SCW RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN RFLG RFRM SCFM
                G G (rA S) jj 1 (B.MemNorm.normalize rsegs mb)
                x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 HK RJB RAb) as RUN.
  apply (rrB_lift Hwx W md _ F _ fc None mb (seg_rom rsegs) _ Q RO RUN).
  intros ms' md' HP Hhid Hs. apply K. split; [exact HP|]. split; [exact Hhid|]. split; [exact Hs|].
  exact (shadow_rw_on_mono _ _ _ (rrR_frame_sh_inR fr len pa pp pn S FS jj Hjj) SWn).
Qed.

(* The SHARED TAIL LIFTED from the epilogue entry 0x84bdc (rKESC's state) at the REAL base memory mb: the right end of
   S-B (a0 = reply_ret = -1, a null pointer).  Premises: the chain's single-memory facts at mb as for rrB_SC_lifted,
   rEI0's pieces at mb (the saved registers, the flag-pointer word and the flag byte 1), the OUT cells' values when
   reply_ok holds, and the footprint at RNG_W (w_H W) that rp_epiSC takes. *)
Lemma rrB_tail_lifted : lib.Reusable.YK04.wx_segs_nowrap rsegs ->
  forall (W : lib.Reusable.YA0n.world rsegs) (md : Model)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mb : word -> option byte) (fr len pa pp pn S FS : Z) (g ja jp jn : list byte) (jj : Z)
    (x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 : word)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
    0 <= fr < 2^64 -> 0 <= len < 2^64 -> 0 <= pa < 2^64 -> 0 <= pp < 2^64 -> 0 <= pn < 2^64 ->
    S < 2^64 -> S mod 16 = 0 -> 9072 <= S ->
    B.MemNorm.ro_agree rsegs mb ->
    stk rsegs mb (S - 9072) S -> length g = 50%nat ->
    (reply_args fr pa pp pn = true -> 50 <= len ->
       fr + 50 <= 2^64 /\ bytes_at rsegs mb fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
       (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)) ->
    (reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       rw_cells rsegs mb pa [CB 2 ja] /\ rw_cells rsegs mb pp [CB 8 jp] /\ rw_cells rsegs mb pn [CB 8 jn] /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)) ->
    (reply_args fr pa pp pn = true -> ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn) ->
    asan_cells mb -> shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FS) mb ->
    HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END ->
    addressable mb (S - 9072) 9072 ->
    (reply_args fr pa pp pn = true -> 50 <= len -> addressable mb fr 50) ->
    (reply_args fr pa pp pn = true ->
       addressable mb pa 2 /\ addressable mb pp 8 /\ addressable mb pn 8 /\
       (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) ->
    fp [1%nat] mb (bv_unsigned tp) FS (S - 9072) S
      (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) ->
    reac_ctrl_identity_reply_tls mb (bv_unsigned tp) FS (S - 9072) S ->
    0 <= jj < fs_M 1 ->
    rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
    bytes_at rsegs mb (fs_frame FS 1 jj + 120) (le8 (Z_to_bv 64 (fs_flag FS 1 jj))) ->
    bytes_at rsegs mb (fs_flag FS 1 jj) [Z_to_bv 8 1] ->
    (reply_ok fr len pa pp pn g = true -> rOUTF fr pa pp pn g mb) ->
    ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (S - 9072) 9072 ->
    shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (S - 9072) 9072 ->
    (reply_args fr pa pp pn = true -> 50 <= len -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> 50 <= len -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> 50 <= len -> shkov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pa 2) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pa 2) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pp 8) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pp 8) ->
    (reply_args fr pa pp pn = true -> ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pn 8) ->
    (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pn 8) ->
    ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_flag FS 1 0) (fs_M 1) ->
    ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_frame FS 1 0)
      (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0) ->
    shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_frame FS 1 0) (fs_frame FS 1 (fs_M 1) - fs_frame FS 1 0) ->
    (forall ms' md', rrB_SCpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g
                       (fs_frame FS 1 jj) jj W md ms' md' -> lib.Reusable.YA0n.SRr rsegs W (mkCfg ms' md') Q) ->
    lib.Reusable.YA0n.SRr rsegs W
      (mkCfg (MS (mkR x1 x2 gp tp x5 x6 x7 (Z_to_bv 64 S) x9 (Z_to_bv 64 (reply_ret fr len pa pp pn g))
                      x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 (fs_frame FS 1 jj)) x19 x20 x21 x22 x23 x24
                      (Z_to_bv 64 (fs_frame FS 1 jj / 8 + ASAN_K)) (Z_to_bv 64 (fs_frame FS 1 jj)) x27 x28 x29 x30 x31)
                 F (Z_to_bv 64 0x84bdc) fc None mb (seg_rom rsegs)) md) Q.
Proof.
  intros Hwx W md ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g ja jp jn jj
    x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 Q
    Rfr Rlen Rpa Rpp Rpn HS S16 HSK RO ST Hg HF HO HOimg AC SW HHM HAE AW AFfr AOUT FP0 TLS0 Hjj SV FL1 FL2 OUTb
    RWIN SCW RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN RFLG RFRM SCFM K.
  set (RG := B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) in *.
  set (G := fs_frame FS 1 jj) in *.
  (* the single-memory facts at normalize mb *)
  assert (STn : stk rsegs (B.MemNorm.normalize rsegs mb) (S - 9072) S)
    by (apply B.MemNormTr.stk_normalize_ro; [exact RO | unfold ImgBounds.IMG_HI; unfold HIGHMEM_BEG in HHM; lia | exact ST]).
  pose proof (B.MemNorm.mem_inv_normalize rsegs mb) as MIn.
  pose proof (B.MemNormTr.asan_cells_normalize mb RO AC) as ACn.
  assert (HFn : reply_args fr pa pp pn = true -> 50 <= len ->
     fr + 50 <= 2^64 /\ bytes_at rsegs (B.MemNorm.normalize rsegs mb) fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
     (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)).
  { intros RA HL. destruct (HF RA HL) as (A1 & A2 & A3). split; [exact A1|]. split; [|exact A3].
    exact (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO A2). }
  assert (NR : forall p n, ImgBounds.IMG_HI <= p -> p + n <= 2 ^ 64 -> forall i, 0 <= i < n ->
                 ro_addr rsegs (wa (p + i)) = false)
    by (intros p n Hp Hn i Hi; apply (B.MemNormTr.ro_addr_above_img_range p n Hp Hn i Hi)).
  assert (HOn : reply_args fr pa pp pn = true ->
     pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
     rw_cells rsegs (B.MemNorm.normalize rsegs mb) pa [CB 2 ja] /\
     rw_cells rsegs (B.MemNorm.normalize rsegs mb) pp [CB 8 jp] /\
     rw_cells rsegs (B.MemNorm.normalize rsegs mb) pn [CB 8 jn] /\
     (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
     (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)).
  { intros RA. destruct (HO RA) as (A1 & A2 & A3 & C1 & C2 & C3 & REST).
    destruct (HOimg RA) as (I1 & I2 & I3).
    destruct (AOUT RA) as ((B0 & _ & B2 & _) & (B3 & _ & B5 & _) & (B6 & _ & B8 & _) & _).
    unfold APPMEM_END in *.
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pa _ RO);
            [intros i Hi; apply (NR pa 2); [exact I1 | lia | cbn in Hi; lia] | exact C1]|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pp _ RO);
            [intros i Hi; apply (NR pp 8); [exact I2 | lia | cbn in Hi; lia] | exact C2]|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pn _ RO);
            [intros i Hi; apply (NR pn 8); [exact I3 | lia | cbn in Hi; lia] | exact C3]|].
    exact REST. }
  pose proof (B.ShadowRwOnT.shadow_rw_on_normalize _ mb RO SW) as SWn.
  pose proof (B.MemNormTr.addressable_normalize mb _ _ RO AW) as AWn.
  assert (AFfrn : reply_args fr pa pp pn = true -> 50 <= len -> addressable (B.MemNorm.normalize rsegs mb) fr 50)
    by (intros RA HL; exact (B.MemNormTr.addressable_normalize mb _ _ RO (AFfr RA HL))).
  assert (AOUTn : reply_args fr pa pp pn = true ->
     addressable (B.MemNorm.normalize rsegs mb) pa 2 /\ addressable (B.MemNorm.normalize rsegs mb) pp 8 /\
     addressable (B.MemNorm.normalize rsegs mb) pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)).
  { intros RA. destruct (AOUT RA) as (B1 & B2 & B3 & REST).
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B1)|].
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B2)|].
    split; [exact (B.MemNormTr.addressable_normalize mb _ _ RO B3) | exact REST]. }
  pose proof (B.MemNormTr.fp_normalize _ mb _ _ _ _ _ _ RO FP0) as FP0n.
  assert (TLS0n : reac_ctrl_identity_reply_tls (B.MemNorm.normalize rsegs mb) (bv_unsigned tp) FS (S - 9072) S)
    by exact (B.MemNormTr.tls_dj_normalize mb (bv_unsigned tp)
                (fp_w [1%nat] FS ++ [(shadow_addr (S - 9072), shadow_addr S)]) RO TLS0).
  assert (SVn : rw_cells rsegs (B.MemNorm.normalize rsegs mb) (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (B.MemNormTr.rw_cells_normalize mb _ _ RO); [|exact SV].
    intros i Hi. apply (NR (S - 104) 104); [unfold ImgBounds.IMG_HI; unfold HIGHMEM_BEG in HHM; lia | lia | cbn in Hi; lia]. }
  pose proof (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO FL1) as FL1n.
  pose proof (B.MemNorm.bytes_at_normalize rsegs mb _ _ RO FL2) as FL2n.
  assert (HK : rFK S FS G G (rA S) jj 1) by (right; repeat split; first [exact (proj1 Hjj) | exact (proj2 Hjj) | reflexivity]).
  pose proof (rp_epiSC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs mb)
                fr len pa pp pn S FS g ja jp jn Rfr Rlen Rpa Rpp Rpn HS S16 HSK STn Hg HFn HOn ACn SWn HHM HAE
                AFfrn AOUTn FP0n RG RWIN SCW RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN RFLG RFRM SCFM
                G G (rA S) jj 1 (B.MemNorm.normalize rsegs mb) (reply_ret fr len pa pp pn g)
                x1 x2 x5 x6 x7 x9 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31 HK) as RUN0.
  (* rEI0SC at the base: munch / wmono / rr_rd_mono reflexive, the window addressable apart from the frame by
     rr_awx_m, the rest the single-memory facts *)
  match type of RUN0 with ?A -> _ => assert (EI : A) end.
  { unfold rEI0SC, rEI0, rCore.
    split; [|apply munch_refl].
    split; [apply munch_refl|].
    split; [apply wmono_refl|]. split; [apply rr_rd_mono_refl|]. split; [exact MIn|].
    split; [exact SVn|].
    split; [exact (rr_awx_m (B.MemNorm.normalize rsegs mb) fr len pa pp pn S g Rfr Rlen Rpa Rpp Rpn Hg AWn G)|].
    split; [exact FP0n|]. split; [exact TLS0n | intros _; exact (conj FL1n FL2n)]. }
  match type of RUN0 with _ -> ?A -> _ => assert (HOFn : A) end.
  { intros HOK. pose proof (OUTb HOK) as (C1 & C2 & C3).
    assert (RA : reply_args fr pa pp pn = true)
      by (unfold reply_ok in HOK; apply andb_prop in HOK; exact (proj1 HOK)).
    destruct (HOimg RA) as (I1 & I2 & I3).
    destruct (AOUT RA) as ((B0 & _ & B2 & _) & (B3 & _ & B5 & _) & (B6 & _ & B8 & _) & _).
    unfold APPMEM_END in *. unfold rOUTF.
    split; [apply (B.MemNormTr.rw_cells_normalize mb pa _ RO);
            [intros i Hi; apply (NR pa 2); [exact I1 | lia | cbn in Hi; lia] | exact C1]|].
    split; [apply (B.MemNormTr.rw_cells_normalize mb pp _ RO);
            [intros i Hi; apply (NR pp 8); [exact I2 | lia | cbn in Hi; lia] | exact C2]|].
    apply (B.MemNormTr.rw_cells_normalize mb pn _ RO);
      [intros i Hi; apply (NR pn 8); [exact I3 | lia | cbn in Hi; lia] | exact C3]. }
  pose proof (RUN0 EI HOFn eq_refl) as RUN.
  apply (rrB_lift Hwx W md _ F _ fc None mb (seg_rom rsegs) _ Q RO RUN).
  intros ms' md' HP Hhid Hs. apply K. split; [exact HP|]. split; [exact Hhid|]. split; [exact Hs|].
  exact (shadow_rw_on_mono _ _ _ (rrR_frame_sh_inR fr len pa pp pn S FS jj Hjj) SWn).
Qed.
End SC.

(* ==== 2. Generic tools: raw bytes, views, the register pc, the 64-bit address range. ==== *)
Lemma rrR_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
  intros a Ha. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact Ha.
Qed.

Lemma rrR_outside_dec : forall (WR : list ivl) (x : Z), outside WR x \/ ~ outside WR x.
Proof.
  induction WR as [|[lo hi] WR IH]; intros x; cbn [outside]; [left; exact I|].
  destruct (IH x) as [H|H]; destruct (Z_lt_le_dec x lo) as [L|L]; destruct (Z_lt_le_dec x hi) as [M|M];
    try (left; split; [lia | exact H]); right; intros [H1 H2]; try (apply H; exact H2); lia.
Qed.

(* The return pc of an even return address is that address (a Theorem Labs lane's cls_ret_pc_ok, C_reac_ctrl_classify_box_frame.v). *)
Lemma rrR_ret_pc : forall k : word, lib.Reusable.YK0s.ret_ok k -> ret_pc k = k.
Proof.
  intros k H. unfold lib.Reusable.YK0s.ret_ok in H. rewrite <- H at 2.
  unfold ret_pc. apply bv_eq.
  unfold lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ.
  rewrite bv_and_unsigned, bv_not_unsigned, !Z_to_bv_unsigned.
  change (bv_wrap 64 1) with 1%Z. change (Z.lnot 1) with (-2)%Z.
  rewrite Z.add_0_r.
  rewrite <- (bv_wrap_small 64 (bv_unsigned k)) at 1 by apply bv_unsigned_in_range.
  apply lib.Reusable.YK11.Z_land_m2_wrap.
Qed.

(* Every image byte lies below IMG_HI = 0x5fe000 (a Theorem Labs lane's rcpW_img_lt). *)
Lemma rrR_img_lt : forall a, lib.Reusable.YG0d.in_img rsegs a -> a < ImgBounds.IMG_HI.
Proof.
  intros a (sg & Hsg & Ha).
  assert (Hm : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg))
                 (map (fun s => (Z.of_N (seg_base s), Z.of_N (seg_size s))) rsegs))
    by (apply in_map_iff; exists sg; split; [reflexivity | exact Hsg]).
  rewrite B.ProgBridge.rsegs_spans in Hm. unfold ImgBounds.IMG_HI.
  cbn [In] in Hm. destruct Hm as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; lia.
Qed.

(* An 8-byte little-endian word's j-th byte (C_reac_ctrl_identity_replyPost.ctl_garr8_le8's step). *)
Lemma rrR_nth_le8 : forall v j, (j < 8)%nat ->
  nth_error (le8 (Z_to_bv 64 v)) j = Some (Z_to_bv 8 (lib.Reusable.YO0f.le_byte v 8 j)).
Proof.
  intros v j Hj.
  assert (Hw : 0 <= v mod 2 ^ 64 < 2 ^ 64) by (apply Z.mod_pos_bound; lia).
  unfold le8. rewrite <- (lib.Reusable.YN2e.Z64_mod v).
  rewrite (lib.Reusable.YN2e.word_to_le_bytes_nth 8 (v mod 2 ^ 64) j Hj Hw).
  unfold lib.Reusable.YO0f.le_byte. change (8 * Z.of_nat 8) with 64.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.

Section RetK.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

Lemma rrR_aview_eq : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  lib.Reusable.YG0n.aview rsegs H m' a = lib.Reusable.YG0n.aview rsegs H m a.
Proof.
  intros H m m' a E. unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
  rewrite E. reflexivity.
Qed.

Lemma rrR_apresent_eq : forall (H : word -> bool) (m m' : word -> option byte) (a : Z),
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) ->
  lib.Reusable.YG0n.apresent H m a -> lib.Reusable.YG0n.apresent H m' a.
Proof. intros H m m' a E [Hh (b & Hb)]. split; [exact Hh|]. exists b. rewrite E. exact Hb. Qed.

(* ---- The kept classes of acall_kept over the function's window [S - 9072, S), across ONE LIFTED RUN that changes
   only the bytes of Wr (raw equality off Wr, in the same world Wk): every byte Wr names outside the window is below
   alloc_ceiling, off the image, and in E' if it is a byte of a caller's block or frame (or that frame's shadow). ---- *)
Lemma rrB_K_raw : forall lyc Sc (W Wk : lib.Reusable.YA0n.world rsegs) (memc mk mk' : word -> option byte)
    (S : Z) (E E' Wr : Z -> Prop),
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc Wk mk (S - 9072) S E ->
  (forall x : word, ~ Wr (bv_unsigned x) -> mk' x = mk x) ->
  (forall a, E a -> E' a) ->
  lib.Reusable.YM05.alloc_ceiling <= S - 9072 -> S <= 2 ^ 64 ->
  (forall b m i, In (b, m) (lib.Reusable.YG0d.ablocks B lyc Sc) -> 0 <= i < lib.Reusable.YG00.req_size m ->
     0 <= b + i < S - 9072) ->
  (forall cid pos a, In (cid, pos) (lib.Reusable.YG01.frames Sc) ->
     (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) \/
      lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid pos),
                                 lib.Reusable.YG00.fs_frame_bytes cid / 8)) -> 0 <= a < S - 9072) ->
  (forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < S - 9072) ->
  (forall a, 0 <= a < 2 ^ 64 -> Wr a -> ~ (S - 9072 <= a < S) ->
     a < lib.Reusable.YM05.alloc_ceiling /\ ~ lib.Reusable.YG0d.in_img rsegs a /\
     (forall b m i, In (b, m) (lib.Reusable.YG0d.ablocks B lyc Sc) -> 0 <= i < lib.Reusable.YG00.req_size m ->
        a = b + i -> E' a) /\
     (forall cid pos, In (cid, pos) (lib.Reusable.YG01.frames Sc) ->
        (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) \/
         lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid pos),
                                    lib.Reusable.YG00.fs_frame_bytes cid / 8)) -> E' a)) ->
  (forall a, S - 9072 <= a < S -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H Wk) mk' a) ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc Wk mk' (S - 9072) S E'.
Proof.
  intros lyc Sc W Wk memc mk mk' S E E' Wr (K1 & K2 & K3 & K4 & K5 & K6) RAW HEE Hceil HS Hblk Hfrm Himg HWR HPR.
  pose proof (lib.Reusable.YCbq.asan_consts) as (C1 & _).
  assert (R : forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> mk' (Z_to_bv 64 a) = mk (Z_to_bv 64 a)).
  { intros a Ha Hw. apply RAW. rewrite rrR_u64 by exact Ha. exact Hw. }
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw.
    assert (Hn : ~ Wr a) by (intros Hx; destruct (HWR a ltac:(lia) Hx Hw) as (Hlt & _); lia).
    rewrite (rrR_aview_eq _ mk mk' a (R a ltac:(lia) Hn)). exact (K1 a Ha Hw).
  - intros b m i Hb Hi HE.
    pose proof (Hblk b m i Hb Hi) as Hlo.
    assert (Hn : ~ Wr (b + i)).
    { intros Hx. destruct (HWR (b + i) ltac:(lia) Hx ltac:(lia)) as (_ & _ & Hbk & _).
      exact (HE (Hbk b m i Hb Hi eq_refl)). }
    rewrite (rrR_aview_eq _ mk mk' (b + i) (R (b + i) ltac:(lia) Hn)).
    exact (K2 b m i Hb Hi (fun He => HE (HEE _ He))).
  - intros a Hi Hst Her. pose proof (Himg a Hi) as Hlo.
    assert (Hn : ~ Wr a).
    { intros Hx. destruct (HWR a ltac:(lia) Hx ltac:(lia)) as (_ & Hni & _). exact (Hni Hi). }
    rewrite (rrR_aview_eq _ mk mk' a (R a ltac:(lia) Hn)). exact (K3 a Hi Hst Her).
  - intros cid pos a Hin Hr HE. pose proof (Hfrm cid pos a Hin Hr) as Hlo.
    assert (Hn : ~ Wr a).
    { intros Hx. destruct (HWR a ltac:(lia) Hx ltac:(lia)) as (_ & _ & _ & Hfk). exact (HE (Hfk cid pos Hin Hr)). }
    rewrite (rrR_aview_eq _ mk mk' a (R a ltac:(lia) Hn)). exact (K4 cid pos a Hin Hr (fun He => HE (HEE _ He))).
  - intros a Ha Hw Hp.
    assert (Hn : ~ Wr a) by (intros Hx; destruct (HWR a ltac:(lia) Hx Hw) as (Hlt & _); lia).
    apply (rrR_apresent_eq _ mk mk' a (R a ltac:(lia) Hn)). exact (K5 a Ha Hw Hp).
  - exact HPR.
Qed.

(* ---- The kept classes across ONE CALL: its own acall_kept from its call state (lyq, Sq) over a window
   [slo, shi) inside [S - 9072, S); the caller's blocks and frames are blocks and frames of the call state (frames at
   the same addresses) and lie off the call's own output E2. ---- *)
Lemma rrB_K_ev : forall lyc Sc lyq Sq (W Wk Wk' : lib.Reusable.YA0n.world rsegs) (memc mk mk' : word -> option byte)
    (S slo shi : Z) (E E2 : Z -> Prop),
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc Wk mk (S - 9072) S E ->
  lib.Reusable.YCbq.acall_kept rsegs B lyq Sq Wk mk Wk' mk' slo shi E2 ->
  S - 9072 <= slo -> shi <= S ->
  (forall b m i, In (b, m) (lib.Reusable.YG0d.ablocks B lyc Sc) -> 0 <= i < lib.Reusable.YG00.req_size m ->
     ~ E (b + i) -> In (b, m) (lib.Reusable.YG0d.ablocks B lyq Sq) /\ ~ E2 (b + i)) ->
  (forall cid pos a, In (cid, pos) (lib.Reusable.YG01.frames Sc) ->
     (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) \/
      lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid pos),
                                 lib.Reusable.YG00.fs_frame_bytes cid / 8)) -> ~ E a ->
     In (cid, pos) (lib.Reusable.YG01.frames Sq) /\
     lib.Reusable.YG0f.frame_addr lyq cid pos = lib.Reusable.YG0f.frame_addr lyc cid pos /\ ~ E2 a) ->
  (forall a, S - 9072 <= a < S -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H Wk') mk' a) ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc Wk' mk' (S - 9072) S E.
Proof.
  intros lyc Sc lyq Sq W Wk Wk' memc mk mk' S slo shi E E2 (K1 & K2 & K3 & K4 & K5 & K6) (J1 & J2 & J3 & J4 & J5 & J6)
    Hslo Hshi Hblk Hfrm HPR.
  split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw. rewrite (J1 a Ha ltac:(lia)). exact (K1 a Ha Hw).
  - intros b m i Hb Hi HE. destruct (Hblk b m i Hb Hi HE) as [Hb' HE2].
    rewrite (J2 b m i Hb' Hi HE2). exact (K2 b m i Hb Hi HE).
  - intros a Hi Hst Her. rewrite (J3 a Hi Hst Her). exact (K3 a Hi Hst Her).
  - intros cid pos a Hin Hr HE. destruct (Hfrm cid pos a Hin Hr HE) as (Hin' & Efa & HE2).
    assert (Hr' : lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyq (cid, pos)) \/
                  lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyq cid pos),
                                             lib.Reusable.YG00.fs_frame_bytes cid / 8)).
    { unfold lib.Reusable.YCbq.frame_rng in *. cbn [fst snd] in *. rewrite Efa. exact Hr. }
    rewrite (J4 cid pos a Hin' Hr' HE2). exact (K4 cid pos a Hin Hr HE).
  - intros a Ha Hw Hp. apply (J5 a Ha ltac:(lia)). exact (K5 a Ha Hw Hp).
  - exact HPR.
Qed.

(* The first link: the kept classes from the entry to itself (the window present by the journal's presence clause). *)
Lemma rrB_K_entry : forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (W : lib.Reusable.YA0n.world rsegs) memc mdc k (S : Z) (E : Z -> Prop),
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= S - 9072 -> S <= sp0 ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W memc (S - 9072) S E.
Proof.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k S E HJ Hlo Hhi.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR & _).
  split; [intros; reflexivity|]. split; [intros; reflexivity|]. split; [intros; reflexivity|].
  split; [intros; reflexivity|]. split; [intros a _ _ Hp; exact Hp|].
  intros a Ha. apply HPR. lia.
Qed.
End RetK.

(* ==== 3. The function's own new bytes (its class-1 frame, that frame's shadow and flag) are apart from every class
   acall_kept keeps; the entry's classes lie below the window.  Copied from a Theorem Labs lane's C_reac_ctrl_parseW.v
   (a working branch 2e352cba74d: rcpW_ceil, rcpW_fgeo, rcpW_apart_block / frame), unchanged but for the
   names and the let-bound Fr / FL written out. ==== *)
Section RetW.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.

Lemma rrR_ceil : 0x7fff7f800000 <= lib.Reusable.YM05.alloc_ceiling <= 0x7fffff800000.
Proof. pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [H _]. unfold lib.Reusable.YG0f.ASAN_CEIL in H. exact H. Qed.

Lemma rrR_fgeo : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md c q,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (c, q) (lib.Reusable.YG01.frames S) ->
  0 <= c <= 10 /\
  ImgBounds.IMG_HI <= lib.Reusable.YG0f.ly_F ly /\
  lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff <= lib.Reusable.YG0f.frame_addr ly c q /\
  lib.Reusable.YG0f.frame_addr ly c q + lib.Reusable.YG00.fs_frame_bytes c <=
    lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize /\
  lib.Reusable.YG0f.frame_addr ly c q mod 64 = 0 /\ 64 <= lib.Reusable.YG00.fs_frame_bytes c /\
  lib.Reusable.YG00.fs_frame_bytes c mod 64 = 0 /\
  lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFlagsOff <= lib.Reusable.YG0f.flag_addr ly c q /\
  lib.Reusable.YG0f.flag_addr ly c q < lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeFramesOff /\
  (lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize <= lib.Reusable.YG0f.kLowShadowBeg \/
   (lib.Reusable.YG0f.kHighMemBeg <= lib.Reusable.YG0f.ly_F ly /\
    lib.Reusable.YG0f.ly_F ly + lib.Reusable.YG0f.kFakeStackSize <= lib.Reusable.YM05.alloc_ceiling)).
Proof.
  intros ly S W m md c q HAR Hin.
  pose proof HAR as (M & _).
  destruct (lib.Reusable.YG0s.frame_facts B ly S _ c q M Hin)
    as (Hc & _ & [_ HFa] & _ & Hpg & Ho1 & Ho2 & Ho64 & Hb64 & Hbm & Hfl).
  pose proof (B.ProgWorldAstack.pwfs_F_above B ly S W m md HAR) as Habove.
  unfold ASAN_GT in Habove.
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.flag_addr, lib.Reusable.YG0f.page_aligned,
    lib.Reusable.YG0f.ASAN_CEIL, ImgBounds.IMG_HI in *.
  split; [exact Hc|]. split; [lia|]. split; [lia|]. split; [lia|].
  split; [Z.div_mod_to_equations; lia|].
  split; [exact Hb64|]. split; [exact Hbm|]. split; [lia|]. split; [lia|].
  exact HFa.
Qed.

Lemma rrR_apart_block : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md pos p n a,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (1, pos) (lib.Reusable.YG01.frames S) ->
  In (p, n) (lib.Reusable.YG0d.ablocks B ly S) -> p <= a < p + lib.Reusable.YG00.req_size n ->
  ~ (lib.Reusable.YG0f.frame_addr ly 1 pos <= a < lib.Reusable.YG0f.frame_addr ly 1 pos + 128) /\
  a <> lib.Reusable.YG0f.flag_addr ly 1 pos /\
  ~ (shadow_addr (lib.Reusable.YG0f.frame_addr ly 1 pos) <= a < shadow_addr (lib.Reusable.YG0f.frame_addr ly 1 pos) + 16).
Proof.
  intros ly S W m md pos p n a HAR Hin Hb Ha.
  destruct (rrR_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & _ & _ & _ & _ & _ & Happ).
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS ly S W m md p n HAR Hb) as (_ & H4096 & Hbc & [_ Hbapp] & Hbo & _).
  destruct (lib.Reusable.YG0d.al_flag _ _ LAWS ly S W m md 1 pos HAR Hin) as (_ & Hfo & _).
  destruct (lib.Reusable.YG0d.al_sep _ _ LAWS ly S W m md HAR) as [Hpw _].
  pose proof (lib.Reusable.YG0s.pairwise_In lib.Reusable.YG0f.zdisjoint _ (p, lib.Reusable.YG00.req_size n)
    (lib.Reusable.YG0f.frame_addr ly 1 pos, lib.Reusable.YG00.fs_frame_bytes 1) _ _ eq_refl Hpw) as D.
  assert (D' : lib.Reusable.YG0f.zdisjoint (p, lib.Reusable.YG00.req_size n)
                 (lib.Reusable.YG0f.frame_addr ly 1 pos, lib.Reusable.YG00.fs_frame_bytes 1)).
  { apply D.
    - apply in_map_iff. exists (p, n). split; [reflexivity | exact Hb].
    - apply in_map_iff. exists (1, pos). split; [reflexivity | exact Hin]. }
  clear D. unfold lib.Reusable.YG0f.zdisjoint in D'. cbn [fst snd] in D'.
  pose proof rrR_ceil as Hce.
  assert (E1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E1 in Hf2, D'.
  set (Fr := lib.Reusable.YG0f.frame_addr ly 1 pos) in *.
  unfold ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize,
    lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg, lib.Reusable.YG0f.ASAN_CEIL in *.
  split; [lia|]. split.
  - intros E. apply (proj2 (Hbo a Ha)). rewrite E. exact Hfo.
  - unfold shadow_addr, ASAN_K. Z.div_mod_to_equations. lia.
Qed.

Lemma rrR_apart_frame : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md pos c q a,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> In (1, pos) (lib.Reusable.YG01.frames S) ->
  In (c, q) (lib.Reusable.YG01.frames S) -> (c, q) <> (1, pos) ->
  (lib.Reusable.YG0f.frame_addr ly c q <= a < lib.Reusable.YG0f.frame_addr ly c q + lib.Reusable.YG00.fs_frame_bytes c \/
   shadow_addr (lib.Reusable.YG0f.frame_addr ly c q) <= a <
     shadow_addr (lib.Reusable.YG0f.frame_addr ly c q) + lib.Reusable.YG00.fs_frame_bytes c / 8) ->
  ~ (lib.Reusable.YG0f.frame_addr ly 1 pos <= a < lib.Reusable.YG0f.frame_addr ly 1 pos + 128) /\
  a <> lib.Reusable.YG0f.flag_addr ly 1 pos /\
  ~ (shadow_addr (lib.Reusable.YG0f.frame_addr ly 1 pos) <= a < shadow_addr (lib.Reusable.YG0f.frame_addr ly 1 pos) + 16).
Proof.
  intros ly S W m md pos c q a HAR Hin Hcq Hne Ha.
  destruct (rrR_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & Hfm & _ & _ & Hl1 & Hl2 & Happ).
  destruct (rrR_fgeo ly S W m md c q HAR Hcq) as (_ & _ & Hg1 & Hg2 & Hgm & Hgb & Hgbm & _).
  pose proof HAR as (M & _).
  destruct (lib.Reusable.YG0s.frame_facts B ly S _ 1 pos M Hin) as (C1 & P1 & _).
  destruct (lib.Reusable.YG0s.frame_facts B ly S _ c q M Hcq) as (C2 & P2 & _).
  pose proof (lib.Reusable.YG0s.frames_apart c q 1 pos C2 P2 C1 P1 Hne) as D.
  unfold lib.Reusable.YG0f.zdisjoint in D. cbn [fst snd] in D.
  pose proof rrR_ceil as Hce.
  assert (E1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E1 in Hf2, D.
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.flag_addr in *.
  unfold ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeFlagsOff,
    lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg,
    shadow_addr, ASAN_K in *.
  destruct Ha as [Ha|Ha].
  - split; [lia|]. split; [lia|]. Z.div_mod_to_equations. lia.
  - split; [Z.div_mod_to_equations; lia|]. split; [Z.div_mod_to_equations; lia|].
    Z.div_mod_to_equations. lia.
Qed.

(* A frame listed after the function's own frame is a different frame (sep_frames_pos: two list positions are
   disjoint ranges, and a frame's range is not empty). *)
Lemma rrR_frame_ne : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md pos So c q,
  lib.Reusable.YG0n.AR rsegs B ly S W m md -> lib.Reusable.YG01.frames S = (1, pos) :: So -> In (c, q) So ->
  (c, q) <> (1, pos).
Proof.
  intros ly S W m md pos So c q HAR Hfr Hin E. rewrite E in Hin.
  apply in_split in Hin as (l1 & l2 & El).
  pose proof (lib.Reusable.YCbq.sep_frames_pos rsegs B LAWS ly S W m md (1, pos) (1, pos) [] l1 l2 HAR
                ltac:(rewrite Hfr, El; reflexivity)) as Hd.
  unfold lib.Reusable.YG0f.zdisjoint, lib.Reusable.YCbq.frame_rng in Hd. cbn [fst snd] in Hd.
  assert (E1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity. rewrite E1 in Hd. lia.
Qed.

(* The function's own new bytes at a state (ly, S) whose frames are (1, pos) followed by an older state's (lyo, So),
   with the same blocks and the same fake-stack base: below alloc_ceiling, off the image, off every block byte and
   every frame byte and frame-shadow byte of the older state. *)
Lemma rrR_new_apart : forall ly S (W : lib.Reusable.YA0n.world rsegs) m md pos lyo So,
  lib.Reusable.YG0n.AR rsegs B ly S W m md ->
  lib.Reusable.YG01.frames S = (1, pos) :: lib.Reusable.YG01.frames So ->
  lib.Reusable.YG0d.ablocks B ly S = lib.Reusable.YG0d.ablocks B lyo So ->
  lib.Reusable.YG0f.ly_F ly = lib.Reusable.YG0f.ly_F lyo ->
  forall a,
    (lib.Reusable.YG0f.frame_addr ly 1 pos <= a < lib.Reusable.YG0f.frame_addr ly 1 pos + 128 \/
     shadow_addr (lib.Reusable.YG0f.frame_addr ly 1 pos) <= a < shadow_addr (lib.Reusable.YG0f.frame_addr ly 1 pos) + 16 \/
     a = lib.Reusable.YG0f.flag_addr ly 1 pos) ->
    0 <= a < lib.Reusable.YM05.alloc_ceiling /\ ImgBounds.IMG_HI <= a /\ ~ lib.Reusable.YG0d.in_img rsegs a /\
    (forall b n i, In (b, n) (lib.Reusable.YG0d.ablocks B lyo So) -> 0 <= i < lib.Reusable.YG00.req_size n ->
       a <> b + i) /\
    (forall cid q, In (cid, q) (lib.Reusable.YG01.frames So) ->
       ~ (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyo (cid, q)) \/
          lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyo cid q),
                                     lib.Reusable.YG00.fs_frame_bytes cid / 8))).
Proof.
  intros ly S W m md pos lyo So HAR Hfr HAB EF a Ha.
  assert (Hin : In (1, pos) (lib.Reusable.YG01.frames S)) by (rewrite Hfr; left; reflexivity).
  assert (Efa : forall c q, lib.Reusable.YG0f.frame_addr lyo c q = lib.Reusable.YG0f.frame_addr ly c q)
    by (intros c q; unfold lib.Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  destruct (rrR_fgeo ly S W m md 1 pos HAR Hin) as (_ & HF & Hf1 & Hf2 & _ & _ & _ & Hl1 & Hl2 & Happ).
  pose proof rrR_ceil as Hce.
  assert (E1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity. rewrite E1 in Hf2.
  set (Fr := lib.Reusable.YG0f.frame_addr ly 1 pos) in *.
  set (FL := lib.Reusable.YG0f.flag_addr ly 1 pos) in *.
  assert (Hrange : 0 <= a < lib.Reusable.YM05.alloc_ceiling /\ ImgBounds.IMG_HI <= a).
  { unfold ImgBounds.IMG_HI, lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeFlagsOff,
      lib.Reusable.YG0f.kFakeStackSize, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *.
    destruct Ha as [Ha|[Ha|Ha]]; [lia | | subst a; lia].
    unfold shadow_addr, ASAN_K in Ha. Z.div_mod_to_equations. lia. }
  split; [exact (proj1 Hrange)|]. split; [exact (proj2 Hrange)|].
  split; [intros Hi; pose proof (rrR_img_lt a Hi); lia|].
  split.
  - intros b n i Hb Hi Eab. rewrite <- HAB in Hb.
    destruct (rrR_apart_block ly S W m md pos b n a HAR Hin Hb ltac:(lia)) as (N1 & N2 & N3).
    destruct Ha as [Ha|[Ha|Ha]]; [exact (N1 Ha) | exact (N3 Ha) | exact (N2 Ha)].
  - intros cid q Hcq Hr.
    assert (Hcq' : In (cid, q) (lib.Reusable.YG01.frames S)) by (rewrite Hfr; right; exact Hcq).
    pose proof (rrR_frame_ne ly S W m md pos (lib.Reusable.YG01.frames So) cid q HAR Hfr Hcq) as Hne.
    assert (Hr' : lib.Reusable.YG0f.frame_addr ly cid q <= a <
                    lib.Reusable.YG0f.frame_addr ly cid q + lib.Reusable.YG00.fs_frame_bytes cid \/
                  shadow_addr (lib.Reusable.YG0f.frame_addr ly cid q) <= a <
                    shadow_addr (lib.Reusable.YG0f.frame_addr ly cid q) + lib.Reusable.YG00.fs_frame_bytes cid / 8).
    { unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr. cbn [fst snd] in Hr.
      rewrite !Efa in Hr.
      unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Hr. unfold shadow_addr, ASAN_K.
      destruct Hr as [Hr|Hr]; [left; lia | right; lia]. }
    destruct (rrR_apart_frame ly S W m md pos cid q a HAR Hin Hcq' Hne Hr') as (N1 & N2 & N3).
    destruct Ha as [Ha|[Ha|Ha]]; [exact (N1 Ha) | exact (N3 Ha) | exact (N2 Ha)].
Qed.

(* The entry's classes lie below the window [S - 9072, S), which lies above alloc_ceiling (the journal's astk_ok). *)
Lemma rrR_entry_below : forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs)
    mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs) memc mdc k (S : Z),
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= S - 9072 -> S <= sp0 ->
  lib.Reusable.YM05.alloc_ceiling <= S - 9072 /\ S <= 2 ^ 47 /\
  (forall b m i, In (b, m) (lib.Reusable.YG0d.ablocks B lyc Sc) -> 0 <= i < lib.Reusable.YG00.req_size m ->
     0 <= b + i < S - 9072) /\
  (forall cid pos a, In (cid, pos) (lib.Reusable.YG01.frames Sc) ->
     (lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) \/
      lib.Reusable.YG0n.in_zr a (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.frame_addr lyc cid pos),
                                 lib.Reusable.YG00.fs_frame_bytes cid / 8)) -> 0 <= a < S - 9072) /\
  (forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < S - 9072).
Proof.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k S HJ Hlo Hhi.
  pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HSTK & _).
  destruct HSTK as (_ & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  pose proof rrR_ceil as Hce.
  split; [lia|]. split; [lia|].
  split; [|split].
  - intros b m i Hb Hi.
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & Hb4 & Hbc & _). lia.
  - intros cid pos a Hin Hr.
    destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F1 & F2 & _).
    pose proof (lib.Reusable.YCbq.fs_frame_bytes_nonneg cid).
    unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr. cbn [fst snd] in Hr.
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF in Hr.
    Z.div_mod_to_equations. lia.
  - intros a Hi. pose proof (rrR_img_lt a Hi). pose proof (B.ProgWorld.pws_segs_low a Hi) as Hl.
    unfold ImgBounds.IMG_HI in *. lia.
Qed.
End RetW.

(* An awr_byte of the entry state is one of a later state with the same blocks, the same frame addresses and more
   owned frames. *)
Lemma rrR_awr_tr : forall STK sp0 FP bl0 blc blc' lyo ly' own own' a,
  lib.Reusable.YCbq.awr_byte STK sp0 FP bl0 blc lyo own a -> blc' = blc ->
  (forall c q, lib.Reusable.YG0f.frame_addr ly' c q = lib.Reusable.YG0f.frame_addr lyo c q) ->
  (forall f, In f own -> In f own') ->
  lib.Reusable.YCbq.awr_byte STK sp0 FP bl0 blc' ly' own' a.
Proof.
  intros STK sp0 FP bl0 blc blc' lyo ly' own own' a Hw -> Efa Hown.
  destruct Hw as [H | [H | [H | (cid & q & Hin & Hr)]]];
    [left; exact H | right; left; exact H | right; right; left; exact H |].
  right; right; right. exists cid, q. split; [exact (Hown _ Hin)|]. rewrite !Efa. exact Hr.
Qed.

(* rWSC's bytes, one case each (the window, the frame, its 16 shadow bytes, the flag byte, the OUT cells under
   reply_ok). *)
Lemma rrR_WSC_cases : forall fr len pa pp pn S FS g G j a,
  ~ outside (rWSC fr len pa pp pn S FS g G j) a ->
  (S - 9072 <= a < S) \/ (G <= a < G + 128) \/ (shadow_addr G <= a < shadow_addr G + 16) \/ a = fs_flag FS 1 j \/
  (reply_ok fr len pa pp pn g = true /\ C_reac_ctrl_identity_reply.treply_out pa pp pn a).
Proof.
  intros fr len pa pp pn S FS g G j a H.
  destruct (Z_lt_le_dec a (S - 9072)) as [A1|A1];
    [|destruct (Z_lt_le_dec a S) as [A2|A2]; [left; lia|]];
  (destruct (Z_lt_le_dec a G) as [B1|B1];
     [|destruct (Z_lt_le_dec a (G + 128)) as [B2|B2]; [right; left; lia|]]);
  (destruct (Z_lt_le_dec a (shadow_addr G)) as [C1|C1];
     [|destruct (Z_lt_le_dec a (shadow_addr G + 16)) as [C2|C2]; [right; right; left; lia|]]);
  (destruct (Z.eq_dec a (fs_flag FS 1 j)) as [D|D]; [right; right; right; left; exact D|]);
  right; right; right; right;
  (destruct (reply_ok fr len pa pp pn g) eqn:OK;
     [split; [reflexivity|] | exfalso; apply H; unfold rWSC; rewrite OK; cbn [outside]; repeat split; first [exact I | lia]]);
  unfold C_reac_ctrl_identity_reply.treply_out;
  (destruct (Z_lt_le_dec a pa) as [E1|E1];
     [|destruct (Z_lt_le_dec a (pa + 2)) as [E2|E2]; [left; lia|]]);
  (destruct (Z_lt_le_dec a pp) as [F1|F1];
     [|destruct (Z_lt_le_dec a (pp + 8)) as [F2|F2]; [right; left; lia|]]);
  (destruct (Z_lt_le_dec a pn) as [G1|G1];
     [|destruct (Z_lt_le_dec a (pn + 8)) as [G2|G2]; [right; right; lia|]]);
  exfalso; apply H; unfold rWSC, rOUTW; rewrite OK; cbn [outside app]; repeat split; first [exact I | lia].
Qed.

(* A byte rw_cells names in the normalized end memory, above the image and visible, is the real memory's byte through
   the world's restriction. *)
Lemma rrR_mbyte_of_cells : forall (H : word -> bool) (mr mn : word -> option byte) (p : Z) (n : nat) (bs : list byte)
    (i : nat),
  B.MemNorm.mem_rel rsegs mr mn -> rw_cells rsegs mn p [CB n bs] -> (i < length bs)%nat ->
  ImgBounds.IMG_HI <= p + Z.of_nat i < 2 ^ 64 -> H (Z_to_bv 64 (p + Z.of_nat i)) = false ->
  lib.Reusable.YP09.mbyte rsegs (lib.Reusable.YK04.mrestrict H mr) (p + Z.of_nat i) = nth_error bs i.
Proof.
  intros H mr mn p n bs i [REL1 _] [[Hwf (H0 & H1 & Hb)] _] Hi Hrng Hv.
  assert (Hi' : (i < length (cells_bytes [CB n bs]))%nat) by (cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hi).
  pose proof (Hb i Hi') as Bi. cbn [cells_bytes cbytes] in Bi. rewrite app_nil_r in Bi.
  destruct (nth_error bs i) as [b|] eqn:Eb; [|apply nth_error_None in Eb; lia].
  assert (R : ro_addr rsegs (wa (p + Z.of_nat i)) = false) by (apply B.MemNormTr.ro_addr_above_img; lia).
  pose proof (REL1 (wa (p + Z.of_nat i))) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
  assert (Emn : mn (wa (p + Z.of_nat i)) = Some b).
  { unfold mrd in Bi. destruct (mn (wa (p + Z.of_nat i))) as [c|] eqn:Ec; [exact Bi|].
    rewrite (rrB_seg_rom_above (p + Z.of_nat i) ltac:(lia)) in Bi. discriminate Bi. }
  unfold lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. rewrite Hv.
  change (Z_to_bv 64 (p + Z.of_nat i)) with (wa (p + Z.of_nat i)). rewrite <- E1, Emn. reflexivity.
Qed.

(* ==== 4. The kept classes step by step from the entry, in the forms the stretches' and the events' lemmas give
   their facts.  Every step lemma is used by the composition; the tail's step is inside rrB_ret. ==== *)
Section Steps.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.

(* S-A: the entry 0x848fc to the first slot of __asan_stack_malloc_1 (rrB_to_E1's continuation: rMCALL over
   normalize memc, the real memory m1, and the journal at m1).  It writes only the window. *)
Lemma rrB_K_SA : forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc
    (W : lib.Reusable.YA0n.world rsegs) memc mdc k (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (S : Z)
    (m1 mc : word -> option byte) mdc1,
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= S - 9072 -> S <= sp0 ->
  rMCALL ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs memc) S mc ->
  B.MemNorm.mem_rel rsegs m1 mc -> B.MemNorm.ro_same rsegs memc m1 ->
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W m1 (S - 9072) S (fun _ => False).
Proof using LAWS.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S m1 mc mdc1
    HJ Hlo Hhi HR [REL1 _] ROS HJ1.
  destruct (rrR_entry_below B LAWS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k S HJ Hlo Hhi)
    as (Hceil & H47 & Hblk & Hfrm & Himg).
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR1 & _).
  pose proof HR as (MU & _).
  apply (rrB_K_raw B lyc Sc W W memc memc m1 S (fun _ => False) (fun _ => False) (fun a => S - 9072 <= a < S)
           (rrB_K_entry B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k S _ HJ Hlo Hhi)).
  - intros x Hx. destruct (ro_addr rsegs x) eqn:R; [exact (ROS x R)|].
    pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
    assert (Ho : outside [(S - 9072, S)] (bv_unsigned x)) by (cbn [outside]; split; [exact Hx | exact I]).
    pose proof (MU x Ho) as E2. unfold B.MemNorm.normalize in E2. rewrite R in E2.
    rewrite <- E1, E2. reflexivity.
  - intros a [].
  - exact Hceil.
  - lia.
  - exact Hblk.
  - exact Hfrm.
  - exact Himg.
  - intros a _ Hw Hn. exfalso. exact (Hn Hw).
  - intros a Ha. apply HPR1. lia.
Qed.

(* E1: the class-1 request (rrB_E1's continuation: its acall_kept over [rA S - ESTACK, rA S) from m1 to mem2, relative to
   the entry state, and the journal at mem2). *)
Lemma rrB_K_E1 : forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc S2
    (W : lib.Reusable.YA0n.world rsegs) memc m1 mem2 md2 k (S pos : Z),
  sp0 - STK <= S - 9072 -> S <= sp0 -> S mod 16 = 0 -> 9072 <= S ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W m1 (S - 9072) S (fun _ => False) ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2
    (sp0 + (rA S - sp0) - lib.Reusable.YG0d.ESTACK) (sp0 + (rA S - sp0)) (fun _ => False) ->
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W mem2 (S - 9072) S (fun _ => False).
Proof.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc S2 W memc m1 mem2 md2 k S pos Hlo Hhi S16 HSK HK HKE HJ2.
  assert (HA : S - 144 <= rA S <= S - 128) by (unfold rA; Z.div_mod_to_equations; lia).
  pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
  apply (rrB_K_ev B lyc Sc lyc Sc W W W memc m1 mem2 S _ _ (fun _ => False) (fun _ => False) HK HKE);
    [unfold lib.Reusable.YG0d.ESTACK; lia | lia | | | ].
  - intros b m i Hb _ _. split; [exact Hb | intros []].
  - intros cid q a Hin _ _. split; [exact Hin|]. split; [reflexivity | intros []].
  - intros a Ha. apply HPR2. lia.
Qed.

(* S-B: from the return of the class-1 request 0x8497c to either end of Lib.rrB_QSB (rrB_SB_lifted's continuation
   rrB_SBpost; the journal after it, rrB_J_SB's conclusion, at the call state (lyc, S2)).  Its write set is Comp's
   rrB_WSB: the window, the frame G and its 16 shadow bytes (the hint word and the flag byte are kept). *)
Lemma rrB_K_SB : forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc S2
    (W : lib.Reusable.YA0n.world rsegs) memc mdc k (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (mb : word -> option byte) (fr len pa pp pn S FS : Z) (g : list byte) (pos : Z)
    (md : Model) (ms' : machine_state) (md' : Model),
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= S - 9072 -> S <= sp0 ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W mb (S - 9072) S (fun _ => False) ->
  rrB_SBpost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mb fr len pa pp pn S FS g pos W md ms' md' ->
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W (ms_mem ms') md' k ->
  lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc ->
  FS = lib.Reusable.YG0f.ly_F lyc ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W (ms_mem ms') (S - 9072) S (fun _ => False).
Proof using LAWS.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc S2 W memc mdc k ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    mb fr len pa pp pn S FS g pos md ms' md' HJ Hlo Hhi HK ((s0' & HQ & HREL & HROS & HKH & HKFL) & _ & _) HJ' HAB HFS.
  destruct (rrR_entry_below B LAWS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k S HJ Hlo Hhi)
    as (Hceil & H47 & Hblk & Hfrm & Himg).
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrc & _).
  pose proof HJ' as (HAR2 & _ & _ & _ & _ & Hfr2 & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
  assert (HFR : lib.Reusable.YG01.frames S2 = (1, pos) :: lib.Reusable.YG01.frames Sc)
    by (rewrite Hfr2, Hfrc; reflexivity).
  pose proof (B.ProgWorld.ctl_fs_geom FS 1 pos ltac:(lia)) as (_ & _ & EGf & _ & _ & _ & _).
  change (Z.to_nat 1) with 1%nat in EGf.
  assert (EG : fs_frame FS 1 pos = lib.Reusable.YG0f.frame_addr lyc 1 pos) by (rewrite EGf, HFS; reflexivity).
  (* off rrB_WSB, the hint word and the flag byte, the normalized end memory is normalize mb (as rrB_J_SB reads it) *)
  unfold rrB_QSB, rBI, rWf in HQ.
  set (G := fs_frame FS 1 pos) in *.
  assert (KEY : forall x : word, ~ rrB_WSB S G (bv_unsigned x) -> ~ (FS + 8 <= bv_unsigned x < FS + 16) ->
                  ~ (fs_flag FS 1 pos <= bv_unsigned x < fs_flag FS 1 pos + 1) ->
                  ms_mem s0' x = B.MemNorm.normalize rsegs mb x).
  { assert (Ehint : fs_hint FS 1 = FS + 8) by (unfold fs_hint; change (Z.of_nat 1) with 1; lia).
    destruct HQ as [(mc & m5 & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 &
                     Es & (MUf & _) & _ & MU5 & _) |
                    (mc & r & y1 & y2 & y5 & y6 & y7 & y9 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 &
                     y21 & y22 & y23 & y24 & y27 & y28 & y29 & y30 & y31 & Es & (MUf & _) & _)];
      rewrite Es; cbn [MS ms_mem].
    - intros x N1 N2 N3. destruct (rrB_WSB_out _ _ _ N1) as (W1 & W2 & W3).
      rewrite (MU5 x).
      + apply MUf. cbn [outside]. rewrite Ehint. repeat split; lia.
      + cbn [outside]. unfold shadow_addr in W3. split; [lia | exact I].
    - intros x N1 N2 N3. destruct (rrB_WSB_out _ _ _ N1) as (W1 & W2 & W3).
      apply MUf. cbn [outside]. rewrite Ehint. repeat split; lia. }
  destruct HREL as (_ & _ & _ & _ & _ & _ & _ & [REL1 _]).
  apply (rrB_K_raw B lyc Sc W W memc mb (ms_mem ms') S (fun _ => False) (fun _ => False) (rrB_WSB S G) HK).
  - intros x Hx. destruct (ro_addr rsegs x) eqn:R; [exact (HROS x R)|].
    pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
    assert (E2 : ms_mem s0' x = B.MemNorm.normalize rsegs mb x).
    { destruct (rrB_in_dec (FS + 8) (FS + 16) (bv_unsigned x)) as [Hh|Hh].
      { apply HKH. unfold rrB_inH. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      destruct (rrB_in_dec (fs_flag FS 1 pos) (fs_flag FS 1 pos + 1) (bv_unsigned x)) as [Hf|Hf].
      { apply HKFL. unfold rrB_inH. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      exact (KEY x Hx Hh Hf). }
    unfold B.MemNorm.normalize in E2. rewrite R in E2. rewrite <- E1, E2. reflexivity.
  - intros a [].
  - exact Hceil.
  - lia.
  - exact Hblk.
  - exact Hfrm.
  - exact Himg.
  - intros a Ha HWa Hw. apply rrB_WSB_iff in HWa.
    destruct HWa as [HWa|HWa]; [exfalso; exact (Hw HWa)|].
    destruct (rrR_new_apart B LAWS lyc S2 W (ms_mem ms') md' pos lyc Sc HAR2 HFR HAB eq_refl a
                ltac:(rewrite <- EG; destruct HWa as [HWa|HWa]; [left; exact HWa | right; left; exact HWa]))
      as (Hr & _ & Hni & Hbk & Hfk).
    split; [lia|]. split; [exact Hni|].
    split; [intros b m i Hb Hi Ea; exfalso; exact (Hbk b m i Hb Hi Ea)|].
    intros cid q Hin Hr'. exfalso. exact (Hfk cid q Hin Hr').
  - intros a Ha. apply HPR2. lia.
Qed.

(* E2: the call of reac_ctrl_parse (C_reac_ctrl_identity_replyE2.rrB_E2_ret at the call state (lyc, S2), the state the
   journal after S-B names; its acall_kept over [rA S - 8800, rA S) with E = parse's 36 bytes at G + 32, inside the
   function's own frame G). *)
Lemma rrB_K_E2 : forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc S2
    (W : lib.Reusable.YA0n.world rsegs) memc mdc m5 md5 k (gp tp : word) (fr len pa pp pn S G : Z) (g : list byte)
    (pos : Z) (W2 : lib.Reusable.YA0n.world rsegs) ly2 S2' regs2 mp md2,
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
  sp0 - STK <= S - 9072 -> S <= sp0 -> S mod 16 = 0 -> 9072 <= S ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W m5 (S - 9072) S (fun _ => False) ->
  lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W m5 md5 k ->
  lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc ->
  G = lib.Reusable.YG0f.frame_addr lyc 1 pos ->
  C_reac_ctrl_identity_replyE2.rrB_E2_ret B STK sp0 FP ly S0 W0 mem0 md0 own pos lyc S2 W m5 k gp tp
    fr len pa pp pn S G g W2 ly2 S2' regs2 mp md2 ->
  lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc W2 mp (S - 9072) S (fun _ => False).
Proof using LAWS.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc S2 W memc mdc m5 md5 k gp tp fr len pa pp pn S G g pos W2 ly2 S2'
    regs2 mp md2 HJ Hlo Hhi S16 HSK HK HJq HAB EG (_ & HJp & _ & _ & _ & _ & _ & HKE & _).
  assert (HA : S - 144 <= rA S <= S - 128) by (unfold rA; Z.div_mod_to_equations; lia).
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrc & _).
  pose proof HJq as (HARq & _ & _ & _ & _ & Hfrq & _).
  pose proof HJp as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPRp & _).
  assert (HFR : lib.Reusable.YG01.frames S2 = (1, pos) :: lib.Reusable.YG01.frames Sc)
    by (rewrite Hfrq, Hfrc; reflexivity).
  apply (rrB_K_ev B lyc Sc lyc S2 W W W2 memc m5 mp S _ _ (fun _ => False) _ HK HKE);
    [unfold C_reac_ctrl_parse.REAC_CTRL_PARSE_STK; lia | lia | | | ].
  - intros b m i Hb Hi _. split; [rewrite HAB; exact Hb|].
    intros Hx. cbv beta in Hx.
    destruct (rrR_new_apart B LAWS lyc S2 W m5 md5 pos lyc Sc HARq HFR HAB eq_refl (b + i)
                ltac:(left; rewrite <- EG; lia)) as (_ & _ & _ & Hbk & _).
    exact (Hbk b m i Hb Hi eq_refl).
  - intros cid q a Hin Hr _.
    split; [rewrite HFR; right; exact Hin|]. split; [reflexivity|].
    intros Ha. cbv beta in Ha.
    destruct (rrR_new_apart B LAWS lyc S2 W m5 md5 pos lyc Sc HARq HFR HAB eq_refl a
                ltac:(left; rewrite <- EG; lia)) as (_ & _ & _ & _ & Hfk).
    exact (Hfk cid q Hin Hr).
  - intros a Ha. apply HPRp. lia.
Qed.
End Steps.

(* ==== 5. ret: from the journal at the tail's base (carried across E2, or rrB_J_SB's at the -1 end), the tail's post
   and the kept classes up to the base, the spec's post. ==== *)
Section Ret.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* OWNER PENDING: the core B bundle (the record core's TfibLib, lib/Reusable/YCeg.v; its line 25 names a refused name
   on every B base), as GlueLift.v's Section JournalFree takes them. *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
(* OWNER PENDING: a Theorem Labs lane's class-1 fake-stack rules, a working branch ff613211c11 (cgif lib/A/ACed.v:125-133,
   tfibX_ASF / tfibX_FFL), the spec's plan comment's ASF / FFL. *)
Hypothesis ASF : lib.Reusable.YG0d.astack_free_law rsegs B.
Hypothesis FFL : lib.Reusable.YCbq.frame_flag_lawP rsegs B.

Lemma rrB_ret :
  forall STK sp0 FP ly S0 (W0 : lib.Reusable.YA0n.world rsegs) mem0 md0 own lyc Sc (W : lib.Reusable.YA0n.world rsegs)
    memc mdc k (regs : bvmap 5 word) (fr len pa pp pn S FS : Z) (g : list byte) (pos : Z)
    lyb Sb (Wb : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) mdb (ms' : machine_state) (md' : Model),
    (* the entry: the spec's P1, P3, P7 and P11 *)
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ->
    lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) ->
    lib.Reusable.YG0d.spZ regs = S -> sp0 - STK <= S - 9072 -> S <= sp0 ->
    (reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (forall a, C_reac_ctrl_identity_reply.treply_out pa pp pn a ->
          (exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames Sc) /\ cid <> 1 /\
             lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos))) /\
          lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0)
            (lib.Reusable.YG0d.ablocks B lyc Sc) lyc own a) /\
       lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
         lib.Reusable.YG0f.SHADOW_OFF pa 2 /\
       lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
         lib.Reusable.YG0f.SHADOW_OFF pp 8 /\
       lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
         lib.Reusable.YG0f.SHADOW_OFF pn 8) ->
    (* the tail's base: the journal with the frame (1, pos) owned, the world, the blocks, the side stack, the kept
       classes from the entry *)
    lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyb Sb Wb mb mdb k ->
    lib.Reusable.YA0n.wle W Wb ->
    lib.Reusable.YG0d.ablocks B lyb Sb = lib.Reusable.YG0d.ablocks B lyc Sc ->
    FS = lib.Reusable.YG0f.ly_F lyc ->
    lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc Wb mb (S - 9072) S (fun _ => False) ->
    (* the tail's post (rrB_SC_lifted / rrB_tail_lifted), the run's registers those of the entry *)
    rrB_SCpost (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4)
      (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18)
      (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
      (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
      (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
      lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mb fr len pa pp pn S FS g (fs_frame FS 1 pos) pos
      Wb mdb ms' md' ->
    lib.B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_post B STK sp0 FP ly S0 W0 mem0 md0 own
      lyc Sc W memc k regs fr len pa pp pn g Wb (mkCfg ms' md').
Proof using LAWS ML ASF FFL.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs fr len pa pp pn S FS g pos lyb Sb Wb mb mdb ms' md'
    HJc Hret HSp Hlo Hhi P11 HJb Hle HAB HFSc HKb ((s0' & HQ & HREL & HROS) & Hhid & Hsame & SWb).
  destruct HQ as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Es0 & MU & _ & _ & ST' & OUTF & _ & SW' & _ & FP' & _ & FL0).
  subst s0'.
  destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL) as [Ems HMR].
  (* the two journals, the frames, the side stack *)
  destruct (rrR_entry_below B LAWS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k S HJc Hlo Hhi)
    as (Hceil & H47 & Hblk & Hfrm & Himg).
  pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrc & _).
  pose proof HJb as (HARb & Hlyb & _ & _ & _ & Hfrb & _).
  destruct Hlyc as (_ & _ & _ & _ & _ & EFc & _). destruct Hlyb as (_ & _ & _ & _ & _ & EFb & _).
  assert (EF : lib.Reusable.YG0f.ly_F lyb = lib.Reusable.YG0f.ly_F lyc) by (rewrite EFb, EFc; reflexivity).
  assert (HFS : FS = lib.Reusable.YG0f.ly_F lyb) by (rewrite HFSc, EF; reflexivity).
  assert (Efa : forall c q, lib.Reusable.YG0f.frame_addr lyb c q = lib.Reusable.YG0f.frame_addr lyc c q)
    by (intros c q; unfold lib.Reusable.YG0f.frame_addr; rewrite EF; reflexivity).
  assert (HFR : lib.Reusable.YG01.frames Sb = (1, pos) :: lib.Reusable.YG01.frames Sc)
    by (rewrite Hfrb, Hfrc; reflexivity).
  assert (HinG : In (1, pos) (lib.Reusable.YG01.frames Sb)) by (rewrite HFR; left; reflexivity).
  pose proof (B.ProgWorld.ctl_fs_geom FS 1 pos ltac:(lia)) as (_ & _ & EGf & EFl & _ & EFSZ & _).
  change (Z.to_nat 1) with 1%nat in EGf, EFl.
  assert (EG : fs_frame FS 1 pos = lib.Reusable.YG0f.frame_addr lyb 1 pos) by (rewrite EGf, HFS; reflexivity).
  set (G := fs_frame FS 1 pos) in *.
  assert (EL : fs_flag FS 1 pos = lib.Reusable.YG0f.flag_addr lyb 1 pos)
    by (rewrite EFl, HFS; reflexivity).
  destruct (rrR_fgeo B lyb Sb Wb mb mdb 1 pos HARb HinG) as (_ & HF & Hf1 & Hf2 & _ & _ & _ & Hl1 & Hl2 & Happ).
  assert (E128 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity. rewrite E128 in Hf2.
  pose proof rrR_ceil as Hce.
  pose proof (lib.Reusable.YCbq.asan_consts) as (C1 & _).
  assert (HGr : ImgBounds.IMG_HI <= G /\ G + 128 <= FS + FS_SIZE /\ FS <= G).
  { rewrite EG, HFS, EFSZ. unfold lib.Reusable.YG0f.kFakeFramesOff in Hf1. lia. }
  assert (HLr : ImgBounds.IMG_HI <= fs_flag FS 1 pos /\ fs_flag FS 1 pos + 1 <= FS + FS_SIZE /\ FS <= fs_flag FS 1 pos).
  { rewrite EL, HFS, EFSZ. unfold lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeFlagsOff,
      lib.Reusable.YG0f.kFakeStackSize in *. lia. }
  assert (HCEIL : FS + FS_SIZE <= lib.Reusable.YM05.alloc_ceiling).
  { rewrite HFS, EFSZ. unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in Happ. lia. }
  (* the OUT cells: in an entry frame, so off the image, below alloc_ceiling, above IMG_HI, visible at the base *)
  assert (HOUTf : reply_ok fr len pa pp pn g = true -> forall a, C_reac_ctrl_identity_reply.treply_out pa pp pn a ->
            ImgBounds.IMG_HI <= a < lib.Reusable.YM05.alloc_ceiling /\ ~ lib.Reusable.YG0d.in_img rsegs a /\
            lib.Reusable.YA0n.w_H Wb (Z_to_bv 64 a) = false /\
            lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0)
              (lib.Reusable.YG0d.ablocks B lyb Sb) lyb ((1, pos) :: own) a).
  { intros HOK a Ho.
    assert (RA : reply_args fr pa pp pn = true)
      by (unfold reply_ok in HOK; apply andb_prop in HOK; exact (proj1 HOK)).
    destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & HO & _).
    destruct (HO a Ho) as ((cid & q & Hin & _ & Hr) & Haw).
    assert (Hinb : In (cid, q) (lib.Reusable.YG01.frames Sb)) by (rewrite HFR; right; exact Hin).
    destruct (rrR_fgeo B lyb Sb Wb mb mdb cid q HARb Hinb) as (_ & HFq & Hq1 & Hq2 & _).
    destruct (lib.Reusable.YCbq.frames_bounds rsegs B LAWS lyc Sc W memc mdc cid q HARc Hin) as (_ & Fq2 & _).
    unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr. cbn [fst snd] in Hr.
    rewrite Efa in Hq1, Hq2.
    split; [unfold lib.Reusable.YG0f.kFakeFramesOff in Hq1; lia|].
    split; [exact (lib.Reusable.YCbq.frm_img rsegs B LAWS lyc Sc W memc mdc cid q a HARc Hin Hr)|].
    split.
    { destruct (B.ProgWorldVisFrame.frame_vis B LAWS lyb Sb Wb mb mdb cid q a 1 HARb Hinb
                  ltac:(rewrite Efa; lia) ltac:(rewrite Efa; lia)) as [(_ & _ & Hv) _].
      exact (Hv a ltac:(lia)). }
    exact (rrR_awr_tr STK sp0 FP _ _ _ lyc lyb own ((1, pos) :: own) a Haw HAB Efa
             (fun f Hf => or_intror Hf)). }
  (* the tail's write set *)
  set (Wr := fun a => ~ outside (rWSC fr len pa pp pn S FS g G pos) a).
  assert (Hdec : forall a, Wr a \/ ~ Wr a).
  { intros a. unfold Wr. destruct (rrR_outside_dec (rWSC fr len pa pp pn S FS g G pos) a) as [H|H];
      [right; intros N; exact (N H) | left; exact H]. }
  assert (Hout : forall x : word, ~ Wr (bv_unsigned x) -> outside (rWSC fr len pa pp pn S FS g G pos) (bv_unsigned x)).
  { intros x Hx. destruct (rrR_outside_dec (rWSC fr len pa pp pn S FS g G pos) (bv_unsigned x)) as [H|H];
      [exact H | exfalso; exact (Hx H)]. }
  (* off Wr the real end byte is mb's *)
  destruct HMR as [REL1 REL2].
  assert (RAW : forall x : word, ~ Wr (bv_unsigned x) -> ms_mem ms' x = mb x).
  { intros x Hx. destruct (ro_addr rsegs x) eqn:R; [exact (HROS x R)|].
    pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
    pose proof (MU x (Hout x Hx)) as E2. unfold B.MemNorm.normalize in E2. rewrite R in E2.
    rewrite <- E1, E2. reflexivity. }
  (* the journal across the tail: one rrB_journal_free step *)
  assert (J' : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyb
                 (lib.Reusable.YG01.stack_free_state 1 pos Sb) Wb (ms_mem ms') md' k).
  { apply (rrB_journal_free B LAWS B.ProgWorld.pws_segs_low ML ASF FFL STK sp0 FP ly S0 W0 mem0 md0 own lyb Sb Wb
             mb mdb k (ms_mem ms') m' md' Wr 1 pos HJb ltac:(lia)).
    - intros a Ha. destruct (rrR_WSC_cases fr len pa pp pn S FS g G pos a Ha) as [Hw|[Hf|[Hs|[Hfl|(HOK & Ho)]]]].
      + left. left. lia.
      + left. right; right; right. exists 1, pos. split; [left; reflexivity|]. left.
        unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- EG, E128. lia.
      + left. right; right; right. exists 1, pos. split; [left; reflexivity|]. right.
        unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- EG, E128.
        unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. unfold shadow_addr, ASAN_K in Hs.
        change (128 / 8) with 16. lia.
      + right. rewrite Hfl. exact EL.
      + left. exact (proj2 (proj2 (proj2 (HOUTf HOK a Ho)))).
    - intros a Ha. destruct (rrR_WSC_cases fr len pa pp pn S FS g G pos a Ha) as [Hw|[Hf|[Hs|[Hfl|(HOK & Ho)]]]].
      + unfold ImgBounds.IMG_HI. lia.
      + lia.
      + clear - Hs HGr HCEIL Hce. unfold shadow_addr, ASAN_K in Hs. unfold ImgBounds.IMG_HI in *.
        Z.div_mod_to_equations. lia.
      + lia.
      + pose proof (HOUTf HOK a Ho) as (Hr & _). lia.
    - exact Hdec.
    - intros x Hx. exact (MU x (Hout x Hx)).
    - intros a Ha. destruct (rrR_WSC_cases fr len pa pp pn S FS g G pos a Ha) as [Hw|[Hf|[Hs|[Hfl|(HOK & Ho)]]]].
      + destruct ST' as (_ & _ & Hs). exact (proj2 (Hs a Hw)).
      + pose proof FP' as (DT & TS & C & T & DB & kk & _ & _ & (_ & _ & _ & _ & STF) & _).
        destruct STF as (_ & _ & Hs). exact (proj2 (Hs a ltac:(lia))).
      + assert (Hsh : in_shadow a).
        { pose proof FP' as (DT & TS & C & T & DB & kk & _ & _ & (_ & _ & _ & FSapp & _) & _).
          pose proof (FSapp G ltac:(lia)) as A1. pose proof (FSapp (G + 127) ltac:(lia)) as A2.
          clear - A1 A2 Hs.
          unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
            APPMEM_END in *.
          Z.div_mod_to_equations. lia. }
        exact (proj2 (SW' _ SWb a Hs Hsh)).
      + pose proof FP' as (DT & TS & C & T & DB & kk & _ & _ & (_ & _ & _ & _ & STF) & _).
        destruct STF as (_ & _ & Hs). exact (proj2 (Hs a ltac:(lia))).
      + destruct (OUTF HOK) as (Ca & Cp & Cn).
        pose proof (stk_of_rw_cells rsegs _ _ _ Ca) as Sa. pose proof (stk_of_rw_cells rsegs _ _ _ Cp) as Sp.
        pose proof (stk_of_rw_cells rsegs _ _ _ Cn) as Sn. cbn [cells_size csize Nat.add] in Sa, Sp, Sn.
        unfold C_reac_ctrl_identity_reply.treply_out in Ho.
        destruct Ho as [Ho|[Ho|Ho]];
          [destruct Sa as (_ & _ & Hs) | destruct Sp as (_ & _ & Hs) | destruct Sn as (_ & _ & Hs)];
          exact (proj2 (Hs a ltac:(lia))).
    - rewrite <- EL. lia.
    - destruct (FL0 eq_refl) as (_ & _ & Hb). specialize (Hb 0%nat ltac:(cbn; lia)).
      change (Z.of_nat 0) with 0 in Hb. rewrite Z.add_0_r in Hb. rewrite <- EL. exact Hb.
    - split; [exact REL1 | exact REL2].
    - exact HROS.
    - exact Hhid.
    - exact Hsame. }
  pose proof J' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR' & _).
  (* the kept classes across the tail *)
  assert (HK' : lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc Wb (ms_mem ms') (S - 9072) S
                  (fun a => reply_ok fr len pa pp pn g = true /\ C_reac_ctrl_identity_reply.treply_out pa pp pn a)).
  { apply (rrB_K_raw B lyc Sc W Wb memc mb (ms_mem ms') S (fun _ => False) _ Wr HKb RAW);
      [intros a [] | exact Hceil | lia | exact Hblk | exact Hfrm | exact Himg | |].
    - intros a Ha HWa Hw.
      destruct (rrR_WSC_cases fr len pa pp pn S FS g G pos a HWa) as [Hw'|[Hf|[Hs|[Hfl|(HOK & Ho)]]]];
        [exfalso; exact (Hw Hw') | | | | ].
      1-3: destruct (rrR_new_apart B LAWS lyb Sb Wb mb mdb pos lyc Sc HARb HFR HAB EF a
                       ltac:(first [left; rewrite <- EG; exact Hf | right; left; rewrite <- EG; exact Hs |
                                    right; right; rewrite Hfl; exact EL]))
             as (Hr & _ & Hni & Hbk & Hfk);
           (split; [lia|]); (split; [exact Hni|]);
           (split; [intros b m i Hb Hi Ea; exfalso; exact (Hbk b m i Hb Hi Ea)|]);
           intros cid q Hin Hr'; exfalso; exact (Hfk cid q Hin Hr').
      pose proof (HOUTf HOK a Ho) as (Hr & Hni & _).
      split; [lia|]. split; [exact Hni|]. split; [intros; exact (conj HOK Ho) | intros; exact (conj HOK Ho)].
    - intros a Ha. apply HPR'. lia. }
  (* the post *)
  unfold lib.B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_post.
  split; [exact Hle|].
  exists lyb, (lib.Reusable.YG01.stack_free_state 1 pos Sb),
    (mkR (lib.Reusable.YK11.getr regs 1) (Z_to_bv 64 S) (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4)
         t0' t1' t2' (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
         (Z_to_bv 64 (reply_ret fr len pa pp pn g)) a1' a2' a3' a4' a5' a6' a7'
         (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
         (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
         (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
         (lib.Reusable.YK11.getr regs 27) t3' t4' t5' t6'),
    (ms_mem ms'), md'.
  split.
  { rewrite Ems at 1. rewrite (rrR_ret_pc _ Hret). reflexivity. }
  split.
  { unfold lib.B.Prog.C_reac_ctrl_identity_reply.EV_REPLY. rewrite Z.add_0_r. exact J'. }
  split.
  { intros r Hr. unfold lib.Reusable.YG0d.acallee_saved in Hr.
    assert (Hr' : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
                  r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by lia.
    destruct Hr' as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]]; try reflexivity.
    transitivity (Z_to_bv 64 S); [reflexivity|].
    rewrite <- HSp. unfold lib.Reusable.YG0d.spZ. rewrite Z_to_bv_bv_unsigned. reflexivity. }
  split.
  { change (lib.Reusable.YG01.frames (lib.Reusable.YG01.stack_free_state 1 pos Sb))
      with (lib.Reusable.YG00.del_pos (lib.Reusable.YG01.frames Sb) 1 pos).
    rewrite HFR. cbn [lib.Reusable.YG00.del_pos]. rewrite !Z.eqb_refl. reflexivity. }
  split.
  { change (lib.Reusable.YG0d.ablocks B lyb (lib.Reusable.YG01.stack_free_state 1 pos Sb))
      with (lib.Reusable.YG0d.ablocks B lyb Sb). rewrite HAB. apply Permutation_refl. }
  split; [reflexivity|].
  split.
  { rewrite HSp. unfold lib.B.Prog.C_reac_ctrl_identity_reply.REAC_CTRL_IDENTITY_REPLY_STK. exact HK'. }
  (* the three cells' values: rQSC's rOUTF read through the world's restriction at the real end memory *)
  intros HOK. destruct (OUTF HOK) as (Ca & Cp & Cn).
  assert (HV : forall p n bs (i : nat), rw_cells rsegs m' p [CB n bs] -> (i < length bs)%nat ->
                 C_reac_ctrl_identity_reply.treply_out pa pp pn (p + Z.of_nat i) ->
                 lib.Reusable.YP09.mbyte rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H Wb) (ms_mem ms'))
                   (p + Z.of_nat i) = nth_error bs i).
  { intros p n bs i Cs Hi Ho. pose proof (HOUTf HOK _ Ho) as (Hr & _ & Hv & _).
    apply (rrR_mbyte_of_cells _ (ms_mem ms') m' p n bs i (conj REL1 REL2) Cs Hi ltac:(lia) Hv). }
  split; [|split].
  - intros j Hj. rewrite length_map in Hj. unfold reply_addr in Hj |- *. cbn [length] in Hj.
    assert (Ej : j = 0%nat \/ j = 1%nat) by lia.
    assert (Hval : forall b : byte, nth_error (reply_addr g) j = Some b ->
              lib.Reusable.YI04.val_mem rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H Wb) (ms_mem ms'))
                (pa + Z.of_nat j) 1 (bv_unsigned b) /\ 0 <= bv_unsigned b < 256).
    { intros b Eb. split; [|pose proof (bv_unsigned_in_range 8 b) as Hb8; unfold bv_modulus in Hb8; exact Hb8].
      intros kk Hk. assert (kk = 0%nat) as -> by lia.
      change (Z.of_nat 0) with 0. rewrite Z.add_0_r.
      rewrite (HV pa 2%nat (reply_addr g) j Ca ltac:(unfold reply_addr; cbn [length]; lia)
                 ltac:(unfold C_reac_ctrl_identity_reply.treply_out; left; lia)), Eb.
      f_equal. unfold lib.Reusable.YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
      pose proof (bv_unsigned_in_range 8 b) as Hb8. unfold bv_modulus in Hb8. change (2 ^ Z.of_N 8) with 256 in Hb8.
      change (2 ^ 8) with 256. rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by lia.
      symmetry. apply stdpp.bitvector.definitions.Z_to_bv_bv_unsigned. }
    destruct Ej as [-> | ->]; cbn [nth map]; apply Hval; reflexivity.
  - intros kk Hk. transitivity (nth_error (le8 (Z_to_bv 64 (fr + 38))) kk); [|exact (rrR_nth_le8 _ kk Hk)].
    exact (HV pp 8%nat _ kk Cp ltac:(rewrite length_le8; exact Hk)
             ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; left; lia)).
  - intros kk Hk. transitivity (nth_error (le8 (Z_to_bv 64 (ir_s g - 13))) kk); [|exact (rrR_nth_le8 _ kk Hk)].
    exact (HV pn 8%nat _ kk Cn ltac:(rewrite length_le8; exact Hk)
             ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; right; lia)).
Qed.
End Ret.
