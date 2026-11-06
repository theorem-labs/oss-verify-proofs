(* lib/B/Prog/C_reac_box_catalogue_matchPf.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the pieces of
   pb_reac_box_catalogue_match, the cgif-form world walk of reac_box_catalogue_match (0x84e40) that proves
   C_reac_box_catalogue_match.treac_box_catalogue_match_spec B.  Brief:
   PB-H1-BRIEF.md (a working note, not in this delivery); map: a Theorem Labs lane's plan
   proofs/libreac/fuzz_ctrl/doc/pb_reac_ctrl_identity_reply.plan.md (a working note, not in this delivery) (one event fewer, same shape).
   rule 24: no function proved; this file composes this lane's own Qed stretch (C_reac_box_catalogue_matchLib.v) with
   shared Qed lemmas (a Theorem Labs lane's rrB_lift and rrB_journal_win, now in lib/B/Prog/GlueLift.v; YCbqMalloc's
   aj_stack_malloc_at_fc).

   THIS PIECE (H1): the entry stretch S-A and the class-2 event E1.
     c0  entry 0x84e40, journal J0 from the spec's P1 (afn_pre without its achain conjunct):
         GlueLift.rrB_ajournal_init_noch at sp0 := spZ regs (the unit's one copy).
     S-A the re-based stretch cmRB_pre_sm2 at mb := B.MemNorm.normalize rsegs memc, LIFTED by
         GlueLift.rrB_lift; journal J1 by GlueLift.rrB_journal_win with
         [lo, hi) := [Sp - 9136, Sp): cmPf_SA.
     E1  the class-2 request at pc 252408 (__asan_stack_malloc_2, ra 0x84eb4) by the core's
         YCbqMalloc.aj_stack_malloc_at_fc 2 (YCbq.aj_stack_malloc_at whose continuation also gets ecall_pre at the
         call configuration and the realizer's frame condition and presence clauses, YG0d.v:297-300: the premises of
         B.ProgWorldAstack.ctl_fs_of_astack) with ASM2; o := CA Sp - Sp: cmPf_E1.
     cmPf_to_sm2_ret composes them from the cgif cut at the entry to a continuation premise at the class-2 RETURN
     state, whose facts are the ONE named interface cmPf_sm2_ret (the contract with the next hand: S-B / E2 / S-C).

   SECTION HYPOTHESES (core / world vocabulary only, decisions.md item 15): LAWS, ML, ASM2, SMP; segs_low and
   errno_low (YCbq's Section a0 / d0 premises) and TL_CODE (the class-2 entry of B's code table), all three core,
   pending the record core (YCeg.v:25 refused name): their core statements are Reusable.YCeg.tfib_segs_low
   (YCeg.v:64), Reusable.YCeg.tl_env (YCeg.v:38) and the TfibLib field Reusable.YCeg.tl_code (YCeg.v:27), but
   lib/Reusable/YCeg.v compiles on no B base yet, so YCeg is not Required.  rsegs_wx_nowrap is a Require
   (lib/B/ProgBridgeData.v), not a hypothesis.
   FRAME-ROUTE FACTS are premises of the lemma that needs them, never Section hypotheses: the base facts at the
   caller's memory, `cmBase memc tp f len Sp FS fb` (cmPf_SA, cmPf_to_sm2_ret), each clause named at its premise
   with the ProgWorld statement that supplies it (owner a Theorem Labs lane, lib/B/ProgWorld.v, twin of a Theorem Labs lane's
   lib/A/ProgWorld.v).  The window's stk and visibility are NOT premises: the spec's P1 presence premise over
   [sp - CM_STK, sp) gives both (cmPf_stk_of_apresent, cmPf_vis_of_apresent); the image's footprint is
   ProgBridge.img_vis_W. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
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
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_reac_box_catalogue_matchLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16 YK04 YK0s YA0n YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0v YG0d YCbq YCbqMalloc YF0l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgBridge ProgBridgeData.
(* a Theorem Labs lane's lift / journal tools (moved from C_reac_ctrl_identity_replyPf.v to the shared GlueLift.v, which Requires
   no C_reac_* file). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require GlueLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_box_catalogue_match.
Import ListNotations.
Open Scope Z_scope.

(* ---- definitional helpers (no frame-route fact) ---- *)

(* A normalized memory agrees with the image on every read-only byte: it holds none there. *)
Lemma cmPf_ro_agree_normalize : forall m, B.MemNorm.ro_agree rsegs (B.MemNorm.normalize rsegs m).
Proof. intros m a H. unfold lib.Lib.Mem.mrd, B.MemNorm.normalize. rewrite H. reflexivity. Qed.

(* The spec's P1 presence over a range gives the stretch's stk window there (a present byte is a written byte). *)
Lemma cmPf_stk_of_apresent : forall (H : word -> bool) (m : word -> option byte) lo hi,
  0 <= lo -> hi <= 2 ^ 64 -> (forall a, lo <= a < hi -> lib.Reusable.YG0n.apresent H m a) -> lib.Lib.Frame.stk rsegs m lo hi.
Proof.
  intros H m lo hi H0 H1 HP. split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (HP a Ha) as [_ [b Hb]]. unfold lib.Lib.Mem.wa.
  split; [unfold wview; rewrite Hb; discriminate | exists b; unfold lib.Lib.Mem.mrd; rewrite Hb; reflexivity].
Qed.

(* ... and its visibility (a present byte is not hidden), the footprint premise ProgBridge.rng_of_visible takes. *)
Lemma cmPf_vis_of_apresent : forall (H : word -> bool) (m : word -> option byte) lo len,
  0 <= lo -> lo + len <= 2 ^ 64 -> (forall a, lo <= a < lo + len -> lib.Reusable.YG0n.apresent H m a) ->
  ProgBridge.range_visible H lo len.
Proof. intros H m lo len H0 H1 HP. split; [exact H0|]. split; [exact H1|]. intros a Ha. exact (proj1 (HP a Ha)). Qed.

(* cmBase moves to the normalized caller memory (cmRB_norm, plus the normalized memory's own ro_agree). *)
Lemma cmPf_base_normalize : forall (mb : word -> option byte) (tp : word) (f len Sp FS : Z) (fb : list byte),
  HIGHMEM_BEG <= Sp - 9136 -> cmBase mb tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mb (Sp - 9136) Sp ->
  cmBase (B.MemNorm.normalize rsegs mb) tp f len Sp FS fb /\ lib.Lib.Frame.stk rsegs (B.MemNorm.normalize rsegs mb) (Sp - 9136) Sp.
Proof.
  intros mb tp f len Sp FS fb HHM HB STW.
  destruct (cmRB_norm mb tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  split; [|exact STn].
  split; [exact (conj ACn (conj SRn (cmPf_ro_agree_normalize mb)))|].
  split; [exact AWn|]. split; [exact FPn|]. split; [exact TLn|]. split; [exact CLn|]. split; [exact HFBn|].
  split; [exact BTn|]. split; [exact ATn | exact ABCn].
Qed.

(* The class-2 request's return address 0x84eb4 is a ret_ok code pointer. *)
Lemma cmPf_ret_ok : lib.Reusable.YK0s.ret_ok (Z_to_bv 64 544436).
Proof. unfold lib.Reusable.YK0s.ret_ok. apply bv_eq. vm_compute. reflexivity. Qed.

(* The frame-pointer arithmetic of the class-2 request: o := CA Sp - Sp. *)
Lemma cmPf_CA : forall Sp, Sp mod 16 = 0 ->
  Sp - 144 <= CA Sp <= Sp - 128 /\ (CA Sp - Sp) mod 16 = 0.
Proof. intros Sp H. unfold CA. Z.div_mod_to_equations. lia. Qed.

(* c0, the journal at the entry from the spec's P1 without achain, is a Theorem Labs lane's shared
   GlueLift.rrB_ajournal_init_noch (YCbq.ajournal_init's proof, which never reads achain, ret_ok,
   raZ, gp or tp, stated over sp0); cmPf_to_sm2_ret uses it at sp0 := spZ regs. *)

Section SAE1.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* Core: the world's laws. *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
(* Core, PENDING THE RECORD CORE (YCeg.v:25 refused name): the statement of Reusable.YCeg.tfib_segs_low (YCeg.v:64)
   (tfibsegs = rsegs by ProgBridge.tfibsegs_rsegs); YCeg.v compiles on no B base yet, so it is not Required. *)
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.

(* ---- S-A: entry 0x84e40 -> the __asan_stack_malloc_2 call (pc 252408), LIFTED.  cmRB_pre_sm2 runs on
   normalize memc (its base facts moved there by cmPf_base_normalize); GlueLift.rrB_lift makes the
   run a silent prefix of the world walk from the REAL caller memory memc; GlueLift.rrB_journal_win
   carries the journal across it ([lo, hi) := [Sp - 9136, Sp), the only range the stretch writes: cmRB_AtSM2's munch).
   The continuation gets the real call memory m1 with the stretch's facts moved back to it (MemNormTr.stk_of_rel,
   rw_cells_of_rel, MemNorm.ro_agree_of_mem_rel / munch_rel / wmono_rel) and the journal J1 at m1.
   FRAME-ROUTE premise: `cmBase memc tp f len Sp FS fb`, the base facts at the caller's memory, clause by clause
   (C_reac_box_catalogue_matchLib.v CLAUSE MAP; owner of every B twin a Theorem Labs lane, lib/B/ProgWorld.v, twin of
   a Theorem Labs lane's lib/A/ProgWorld.v):
     (1) asan_cells /\ shadow_rw_on R /\ ro_agree  <- route (C): ctl_rt_C_of_AR and PfV.cmPf_shrwR_of_AR (no VIS0)
     (2) addressable (Sp - 9136) 9136          <- ctl_stack_shadow_of_AR_stmt (statement only on A)
     (3) fp [0; 1; 2] .. FS ..                 <- ctl_fp_of_AR_stmt / ctl_fs_of_AR_stmt (provisional (stand-ins) on A)
     (4) cmRB_tls_dj                           <- ctl_tls_of_AR_stmt + a Theorem Labs lane's PROPOSED fp_tls_owned_stmt
     (5) aCL                                   <- RT_used_of_AR_stmt (decisions.md item 29 (a working note, not in this delivery); statement only on A)
     (6) 50 <= len -> bytes_at f fb /\ addressable f 50
                                               <- the spec's live-block premises + ctl_block_shadow_of_AR_stmt
     (7) bytes_at CM_T CM_TBL                  <- the image (ro_agree's read-only data)
     (8) cmRB_tbl_addr                         <- ONE named hypothesis citing ctl_zshadow_of_AR_stmt (not wired)
     (9) cmRB_bc_addr                          <- a Theorem Labs lane's PROPOSED ctl_gshadow_of_AR_stmt.
   The window's stk and its visibility are premises here in ctrl form; cmPf_to_sm2_ret discharges both from the spec's
   P1 presence premise. ---- *)
Lemma cmPf_SA : forall (W : lib.Reusable.YA0n.world rsegs) (ly0 : lib.Reusable.YG0f.alayout)
    (S0 : lib.Reusable.YG00.astate) (W0 : lib.Reusable.YA0n.world rsegs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : lib.Reusable.YG0f.alayout) (S : lib.Reusable.YG00.astate)
    (memc : word -> option byte) (md : Model) (k : Z)
    (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (f len Sp FS : Z) (fb : list byte)
    (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (Sp - 9136) 9136 ->
  (* FRAME-ROUTE: the base facts at memc, clauses (1)-(9) above; source a Theorem Labs lane's lib/B/ProgWorld.v *)
  cmBase memc tp f len Sp FS fb ->
  lib.Lib.Frame.stk rsegs memc (Sp - 9136) Sp ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own ly S W memc md k ->
  (forall (m1 : word -> option byte) (md1 : Model),
     lib.Lib.Frame.stk rsegs m1 (Sp - 9136) Sp ->
     lib.Lib.Step.rw_cells rsegs m1 (Sp + -104) (cmSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) ->
     B.MemNorm.ro_agree rsegs m1 ->
     lib.Lib.Frame.munch [(Sp - 9136, Sp)] memc m1 -> lib.Lib.Frame.wmono rsegs memc m1 ->
     lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own ly S W m1 md1 k ->
     lib.Reusable.YA0n.SRr rsegs W
       (mkCfg (lib.Reusable.YK11.mkst
                 (lib.Lib.Frame.mkR (Z_to_bv 64 544436) (Z_to_bv 64 (CA Sp)) gp tp t0 t1 t2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                      (Z_to_bv 64 192) (lib.Lib.Mem.wa 693944) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) a3 a4 a5 a6 a7
                      s2 (Z_to_bv 64 f) (Z_to_bv 64 len) (lib.Lib.Mem.wa ASAN_K) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 (Z_to_bv 64 252408) m1 (lib.Lib.PropExec.seg_rom rsegs)) md1) Q) ->
  lib.Reusable.YA0n.SRr rsegs W
    (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 Sp) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 f) (Z_to_bv 64 len) a2 a3 a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               lib.Reusable.YK11.fp_regs (Z_to_bv 64 REAC_BOX_CATALOGUE_MATCH) lib.Reusable.YK11.fp_csr None memc
               (lib.Lib.PropExec.seg_rom rsegs)) md) Q.
Proof.
  intros W ly0 S0 W0 mem0 md0 own ly S memc md k ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 f len Sp FS fb
    t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 Q Rf Rlen RS S16 HK Hfb HHM HAE VW HB STW HJ K.
  pose proof HB as ((_ & _ & ROc) & _).
  destruct (cmPf_base_normalize memc tp f len Sp FS fb HHM HB STW) as [HBn STn].
  assert (RIMG : lib.Lib.ExecF.rng (ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) 65536 6217728).
  { pose proof (ProgBridge.rng_of_visible _ _ _ (ProgBridge.img_vis_W W)) as R.
    unfold ImgBounds.IMG_LO, ImgBounds.IMG_HI in R. exact R. }
  pose proof (ProgBridge.rng_of_visible _ _ _ VW) as RWIN.
  pose proof (cmRB_pre_sm2 ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lib.Reusable.YK11.fp_regs
    lib.Reusable.YK11.fp_csr f len Sp FS fb (ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
    (B.MemNorm.normalize rsegs memc) Rf Rlen RS S16 HK Hfb HHM HAE RIMG RWIN HBn STn
    t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) as RUN.
  apply (GlueLift.rrB_lift ProgBridgeData.rsegs_wx_nowrap W md _ _ _ _ _ memc _ _ Q ROc RUN).
  intros ms' md' (st & (m1n & -> & (MU & WM & RO1n & ST1n & SV1n)) & Hrel & Hsm) Hhid Hsame.
  destruct (MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Es Hmr].
  pose proof (B.MemNorm.mem_rel_normalize rsegs memc ROc) as REL0.
  assert (HJ1 : lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own
                  ly S W (ms_mem ms') md' k).
  { apply (GlueLift.rrB_journal_win B LAWS segs_low C_reac_box_catalogue_match.CM_STK Sp []
             ly0 S0 W0 mem0 md0 own ly S W memc md k (ms_mem ms') m1n md' (Sp - 9136) Sp HJ);
      [unfold C_reac_box_catalogue_match.CM_STK; lia | lia | exact (cmRB_win_above_img Sp HHM) | lia
      | exact MU | | exact Hmr | exact Hsm | exact Hhid | exact Hsame].
    intros a Ha. exact (proj2 (proj2 (proj2 ST1n) a Ha)). }
  rewrite Es.
  exact (K (ms_mem ms') md'
           (MemNormTr.stk_of_rel _ _ _ _ Hmr ST1n)
           (MemNormTr.rw_cells_of_rel _ _ _ _ Hmr SV1n)
           (B.MemNorm.ro_agree_of_mem_rel rsegs _ _ Hmr)
           (B.MemNorm.munch_rel rsegs _ memc _ (ms_mem ms') m1n REL0 Hmr Hsm MU)
           (B.MemNorm.wmono_rel rsegs memc _ (ms_mem ms') m1n REL0 Hmr Hsm WM)
           HJ1).
Qed.

(* Core, PENDING THE RECORD CORE (YCeg.v:25 refused name): the statement of Reusable.YCeg.tl_env (YCeg.v:38) for B. *)
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
(* Core: the model's laws. *)
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
(* Core: the fake stack's progress rule. *)
Hypothesis SMP : lib.Reusable.YCbq.stack_malloc_progressP B.
(* Core: the class-2 fake-stack rule (fake-stack owner a Theorem Labs lane with a Theorem Labs lane). *)
Hypothesis ASM2 : lib.Reusable.YG0d.astack_malloc_realizes rsegs B 2.
(* Core, PENDING THE RECORD CORE (YCeg.v:25 refused name): the statement of the TfibLib field Reusable.YCeg.tl_code
   (YCeg.v:27), B's code table; it gives the class-2 entry pc_stack_malloc (as_code B) 2 = 0x3d9f8 (cmPf_pc_sm2). *)
Hypothesis TL_CODE : lib.Reusable.YG0f.as_code B = lib.Reusable.YF0l.Tfib_code.

Lemma cmPf_pc_sm2 : lib.Reusable.YG0f.pc_stack_malloc (lib.Reusable.YG0f.as_code B) 2 = 252408.
Proof. rewrite TL_CODE. reflexivity. Qed.

(* ---- E1: the class-2 request at pc 252408 (ra 0x84eb4), by the core's YCbqMalloc.aj_stack_malloc_at_fc 2 with ASM2;
   the request runs at sp = CA Sp, so o := CA Sp - Sp (o mod 16 = 0, o <= 0, ESTACK - o <= 4240 <= CM_STK).  The
   continuation gets the rule's post verbatim, the kept window written [CA Sp - ESTACK, CA Sp), and (passed on from
   astack_malloc_realizes' post, YG0d.v:297-300) ecall_pre at the call configuration, the frame's presence, the frame
   condition and the presence of the request's window: the premises of B.ProgWorldAstack.ctl_fs_of_astack. ---- *)
Lemma cmPf_E1 : forall (W : lib.Reusable.YA0n.world rsegs) (ly0 : lib.Reusable.YG0f.alayout)
    (S0 : lib.Reusable.YG00.astate) (W0 : lib.Reusable.YA0n.world rsegs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (ly : lib.Reusable.YG0f.alayout) (S : lib.Reusable.YG00.astate)
    (m1 : word -> option byte) (md1 : Model) (k Sp : Z) (regsT : bvmap 5 word)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own ly S W m1 md1 k ->
  Sp mod 16 = 0 ->
  lib.Reusable.YG0d.spZ regsT = CA Sp ->
  lib.Reusable.YK11.getr regsT 1 = Z_to_bv 64 544436 ->
  lib.Reusable.YK11.getr regsT 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regsT 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
  lib.Reusable.YG01.count_cid 2 (lib.Reusable.YG01.frames S) < lib.Reusable.YG00.fs_frames 2 ->
  (forall (S2 : lib.Reusable.YG00.astate) (regs2 : bvmap 5 word) (m2 : word -> option byte) (md2 : Model) (pos : Z),
     lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 ((2, pos) :: own)
       ly S2 W m2 md2 k ->
     lib.Reusable.YG0d.aregs_preserved regsT regs2 ->
     lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.frame_addr ly 2 pos) ->
     lib.Reusable.YG0d.ablocks B ly S2 = lib.Reusable.YG0d.ablocks B ly S ->
     lib.Reusable.YG01.frames S2 = (2, pos) :: lib.Reusable.YG01.frames S ->
     ~ In (2, pos) (lib.Reusable.YG01.frames S) ->
     lib.Reusable.YG00.st_nev S2 = lib.Reusable.YG00.st_nev S ->
     lib.Reusable.YG01.blocks_bytes S2 = lib.Reusable.YG01.blocks_bytes S ->
     lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m2)
       lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr ly 2 pos) (lib.Reusable.YG00.fs_frame_bytes 2) ->
     lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m2)
       (lib.Reusable.YG0f.frame_addr ly 2 pos + lib.Reusable.YG00.fs_frame_bytes 2 - 8) =
       Some (lib.Reusable.YG0f.flag_addr ly 2 pos) ->
     lib.Reusable.YCbq.acall_kept rsegs B ly S W m1 W m2 (CA Sp - lib.Reusable.YG0d.ESTACK) (CA Sp) (fun _ => False) ->
     lib.Reusable.YG0d.ecall_pre rsegs B ly S W regsT m1 md1 ->
     (forall a, lib.Reusable.YG0f.frame_addr ly 2 pos <= a <
        lib.Reusable.YG0f.frame_addr ly 2 pos + lib.Reusable.YG00.fs_frame_bytes 2 ->
        lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m2 a) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Reusable.YG0n.aowned B ly S a -> ~ lib.Reusable.YG0n.aowned B ly S2 a ->
        ~ (lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regsT) ->
        lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m2 a = lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1 a) ->
     (forall a, lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regsT ->
        lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m2 a) ->
     lib.Reusable.YA0n.SRr rsegs W
       (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 544436) m2 (lib.Lib.PropExec.seg_rom rsegs)) md2) Q) ->
  lib.Reusable.YA0n.SRr rsegs W (mkCfg (lib.Reusable.YK11.mkst regsT (Z_to_bv 64 252408) m1 (lib.Lib.PropExec.seg_rom rsegs)) md1) Q.
Proof.
  intros W ly0 S0 W0 mem0 md0 own ly S m1 md1 k Sp regsT Q HJ S16 Hsp Hra Hgp Htp Hcnt K.
  destruct (cmPf_CA Sp S16) as (CAb & CAm).
  replace (Z_to_bv 64 252408) with (Z_to_bv 64 (lib.Reusable.YG0f.pc_stack_malloc (lib.Reusable.YG0f.as_code B) 2))
    by (rewrite cmPf_pc_sm2; reflexivity).
  eapply lib.Reusable.YA0n.SRr_bind.
  { exact (lib.Reusable.YCbqMalloc.aj_stack_malloc_at_fc rsegs B LAWS segs_low errno_low ML SMP 2 ASM2 ltac:(lia)
             W regsT m1 C_reac_box_catalogue_match.CM_STK Sp [] ly0 S0 W0 mem0 md0 own ly S md1 k (CA Sp - Sp)
             (Z_to_bv 64 544436) HJ ltac:(rewrite Hsp; lia) CAm ltac:(lia)
             ltac:(unfold lib.Reusable.YG0d.ESTACK, C_reac_box_catalogue_match.CM_STK; lia)
             Hgp Htp Hra cmPf_ret_ok Hcnt). }
  intros W' c' _ (-> & S2 & regs2 & m2 & md2 & pos & -> & HJ2 & HP & H10 & Hab & Hfr & Hnin & Hnev & Hbb & Hz & Hfl
    & Hkept & HPRE & Hfpres & Hfc & Hwpres).
  replace (Sp + (CA Sp - Sp) - lib.Reusable.YG0d.ESTACK) with (CA Sp - lib.Reusable.YG0d.ESTACK) in Hkept by lia.
  replace (Sp + (CA Sp - Sp)) with (CA Sp) in Hkept by lia.
  exact (K S2 regs2 m2 md2 pos HJ2 HP H10 Hab Hfr Hnin Hnev Hbb Hz Hfl Hkept HPRE Hfpres Hfc Hwpres).
Qed.

(* ==== THE INTERFACE for the next hand (S-B / E2 / S-C): the class-2 RETURN state of reac_box_catalogue_match.
   The world walk stands at mkCfg (mkst regs2 (Z_to_bv 64 544436) m2 (seg_rom rsegs)) md2 (pc 0x84eb4, world W
   unchanged), entered at cfg_at rsegs 0x84e40 regs memc md with the journal base (ly, S, W, memc, md), sp0 = spZ regs.
   (a) the call memory m1 (S-A's end, pc 252408): the window's stk, the 13 saves of the entry registers at
       [sp0 - 104, sp0), ro_agree, and S-A's writes relative to memc (only the window [sp0 - 9136, sp0));
   (b) J2, the journal from the entry to the return state, own = [(2, pos)];
   (c) the class-2 request's post (YCbqMalloc.aj_stack_malloc_at_fc): the new frame (2, pos), the frame's zero shadow
       and flag word through aview, the unchanged blocks / events / bytes, and acall_kept from m1 to m2 off the
       request's window [CA sp0 - ESTACK, CA sp0);
   (d) the registers at the return: a0 = the frame's address, and the callee-saved ones (aregs_preserved of the
       call registers, spelled out): sp = CA sp0, gp, tp, s0 = sp0, s1 = CA sp0, s2, s3 = f, s4 = len, s5 = ASAN_K,
       s6 .. s11.  The world rule leaves every other register, ra included, unconstrained;
   (e) the call configuration (regsT, m1, md1) of the class-2 request and the rest of its realizer's post, the
       premises of B.ProgWorldAstack.ctl_fs_of_astack 2: spZ regsT = CA sp0, ecall_pre there, the window's presence
       at m1 (J1's clause, [sp0 - CM_STK, sp0)), and astack_malloc_realizes' frame presence, frame condition and
       window presence (YG0d.v:297-300, passed on by aj_stack_malloc_at_fc). ==== *)
Definition cmPf_sm2_ret (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (m1 : word -> option byte) (md1 : Model) (regsT : bvmap 5 word) (S2 : lib.Reusable.YG00.astate) (regs2 : bvmap 5 word)
    (m2 : word -> option byte) (md2 : Model) (pos : Z) : Prop :=
  (* (a) *)
  lib.Lib.Frame.stk rsegs m1 (lib.Reusable.YG0d.spZ regs - 9136) (lib.Reusable.YG0d.spZ regs) /\
  lib.Lib.Step.rw_cells rsegs m1 (lib.Reusable.YG0d.spZ regs + -104)
    (cmSAVES (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
       (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
       (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
       (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
       (lib.Reusable.YK11.getr regs 27)) /\
  B.MemNorm.ro_agree rsegs m1 /\
  lib.Lib.Frame.munch [(lib.Reusable.YG0d.spZ regs - 9136, lib.Reusable.YG0d.spZ regs)] memc m1 /\ lib.Lib.Frame.wmono rsegs memc m1 /\
  (* (b) *)
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
    ly S W memc md [(2, pos)] ly S2 W m2 md2 0 /\
  (* (c) *)
  lib.Reusable.YG01.frames S2 = (2, pos) :: lib.Reusable.YG01.frames S /\
  ~ In (2, pos) (lib.Reusable.YG01.frames S) /\
  lib.Reusable.YG0d.ablocks B ly S2 = lib.Reusable.YG0d.ablocks B ly S /\
  lib.Reusable.YG00.st_nev S2 = lib.Reusable.YG00.st_nev S /\
  lib.Reusable.YG01.blocks_bytes S2 = lib.Reusable.YG01.blocks_bytes S /\
  lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m2)
    lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr ly 2 pos) (lib.Reusable.YG00.fs_frame_bytes 2) /\
  lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m2)
    (lib.Reusable.YG0f.frame_addr ly 2 pos + lib.Reusable.YG00.fs_frame_bytes 2 - 8) =
    Some (lib.Reusable.YG0f.flag_addr ly 2 pos) /\
  lib.Reusable.YCbq.acall_kept rsegs B ly S W m1 W m2
    (CA (lib.Reusable.YG0d.spZ regs) - lib.Reusable.YG0d.ESTACK) (CA (lib.Reusable.YG0d.spZ regs)) (fun _ => False) /\
  (* (d) *)
  lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.frame_addr ly 2 pos) /\
  lib.Reusable.YK11.getr regs2 2 = Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)) /\
  lib.Reusable.YK11.getr regs2 3 = lib.Reusable.YK11.getr regs 3 /\
  lib.Reusable.YK11.getr regs2 4 = lib.Reusable.YK11.getr regs 4 /\
  lib.Reusable.YK11.getr regs2 8 = Z_to_bv 64 (lib.Reusable.YG0d.spZ regs) /\
  lib.Reusable.YK11.getr regs2 9 = Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)) /\
  lib.Reusable.YK11.getr regs2 18 = lib.Reusable.YK11.getr regs 18 /\
  lib.Reusable.YK11.getr regs2 19 = Z_to_bv 64 f /\
  lib.Reusable.YK11.getr regs2 20 = Z_to_bv 64 len /\
  lib.Reusable.YK11.getr regs2 21 = lib.Lib.Mem.wa ASAN_K /\
  lib.Reusable.YK11.getr regs2 22 = lib.Reusable.YK11.getr regs 22 /\
  lib.Reusable.YK11.getr regs2 23 = lib.Reusable.YK11.getr regs 23 /\
  lib.Reusable.YK11.getr regs2 24 = lib.Reusable.YK11.getr regs 24 /\
  lib.Reusable.YK11.getr regs2 25 = lib.Reusable.YK11.getr regs 25 /\
  lib.Reusable.YK11.getr regs2 26 = lib.Reusable.YK11.getr regs 26 /\
  lib.Reusable.YK11.getr regs2 27 = lib.Reusable.YK11.getr regs 27 /\
  (* (e) *)
  lib.Reusable.YG0d.spZ regsT = CA (lib.Reusable.YG0d.spZ regs) /\
  lib.Reusable.YG0d.ecall_pre rsegs B ly S W regsT m1 md1 /\
  (forall a, lib.Reusable.YG0d.spZ regs - C_reac_box_catalogue_match.CM_STK <= a < lib.Reusable.YG0d.spZ regs ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m1 a) /\
  (forall a, lib.Reusable.YG0f.frame_addr ly 2 pos <= a <
     lib.Reusable.YG0f.frame_addr ly 2 pos + lib.Reusable.YG00.fs_frame_bytes 2 ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m2 a) /\
  (forall a, 0 <= a < 2 ^ 64 -> ~ lib.Reusable.YG0n.aowned B ly S a -> ~ lib.Reusable.YG0n.aowned B ly S2 a ->
     ~ (lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regsT) ->
     lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m2 a = lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1 a) /\
  (forall a, lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regsT ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m2 a).

(* ---- c0 + S-A + E1 from the cgif cut at the entry (C_reac_box_catalogue_match.treac_box_catalogue_match_spec's
   configuration, SEGS = YB1v.tfibsegs = rsegs by ProgBridge.tfibsegs_rsegs) to the interface.  The premises are the
   spec's own (P1 without achain, the arguments, the class-2 room), the frame-route base facts at memc, and the
   continuation at the class-2 return state.  The window's stk and visibility come from P1's presence premise; the
   cut's register map is moved to the canonical one by YA0nR.SRr_xregs_eqv (Regs6ss.mkR_of_eqv). ---- *)
Lemma cmPf_to_sm2_ret : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model)
    (f len FS : Z) (fb : list byte) (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  (* the spec's P1 without its achain conjunct (C_reac_box_catalogue_match.v:81-86), less ret_ok / raZ, which no
     step of S-A, E1 or the journal start reads *)
  lib.Reusable.YG0n.AR rsegs B ly S W memc md ->
  lib.Reusable.YK11.getr regs 3 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B) ->
  lib.Reusable.YK11.getr regs 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
  lib.Reusable.YCbq.astk_ok C_reac_box_catalogue_match.CM_STK ly (lib.Reusable.YG0d.spZ regs) ->
  (forall a, lib.Reusable.YG0d.spZ regs - C_reac_box_catalogue_match.CM_STK <= a < lib.Reusable.YG0d.spZ regs ->
     lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) memc a) ->
  lib.Reusable.YG01.qtight S ->
  (* the arguments (C_reac_box_catalogue_match.v:88-90) *)
  lib.Reusable.YK11.getr regs 10 = lib.Reusable.YG0d.w64 f -> lib.Reusable.YK11.getr regs 11 = lib.Reusable.YG0d.w64 len ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> length fb = 50%nat ->
  (* the class-2 room (C_reac_box_catalogue_match.v:97) *)
  lib.Reusable.YG01.count_cid 2 (lib.Reusable.YG01.frames S) < lib.Reusable.YG00.fs_frames 2 ->
  (* FRAME-ROUTE: the base facts at the caller's memory, clauses (1)-(9) at cmPf_SA; source a Theorem Labs lane's
     lib/B/ProgWorld.v (twin of a Theorem Labs lane's lib/A/ProgWorld.v), FS from ctl_fp_of_AR_stmt *)
  cmBase memc (lib.Reusable.YK11.getr regs 4) f len (lib.Reusable.YG0d.spZ regs) FS fb ->
  (* the continuation at the class-2 return state *)
  (forall (m1 : word -> option byte) (md1 : Model) (regsT : bvmap 5 word) (S2 : lib.Reusable.YG00.astate)
          (regs2 : bvmap 5 word) (m2 : word -> option byte) (md2 : Model) (pos : Z),
     cmPf_sm2_ret W ly S regs memc md f len m1 md1 regsT S2 regs2 m2 md2 pos ->
     lib.Reusable.YA0n.SRr rsegs W
       (mkCfg (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 544436) m2 (lib.Lib.PropExec.seg_rom rsegs)) md2) Q) ->
  lib.Reusable.YA0n.SRr rsegs W
    (lib.Reusable.YG0d.cfg_at rsegs C_reac_box_catalogue_match.A_reac_box_catalogue_matchP regs memc md) Q.
Proof.
  intros W ly S regs memc md f len FS fb Q HAR Hgp Htp Hstk Hpres HQT H10 H11 Rf Rlen Hfb Hcnt HB K.
  pose proof (GlueLift.rrB_ajournal_init_noch B C_reac_box_catalogue_match.CM_STK
                (lib.Reusable.YG0d.spZ regs) [] ly S W memc md HAR Hstk Hpres HQT) as HJ0.
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as RSp.
  unfold bv_modulus in RSp. cbn [Z.of_N] in RSp.
  change (bv_unsigned (lib.Reusable.YK11.getr regs 2)) with (lib.Reusable.YG0d.spZ regs) in RSp.
  set (Sp := lib.Reusable.YG0d.spZ regs) in *.
  pose proof Hstk as (S16 & _ & Hceil & Hslo & Hshi & H47 & _).
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo, Hpres.
  assert (HK : 9136 <= Sp) by lia.
  assert (HHM : HIGHMEM_BEG <= Sp - 9136) by (unfold HIGHMEM_BEG; lia).
  assert (HAE : Sp <= APPMEM_END) by (unfold APPMEM_END; lia).
  assert (STW : lib.Lib.Frame.stk rsegs memc (Sp - 9136) Sp)
    by (apply (cmPf_stk_of_apresent (lib.Reusable.YA0n.w_H W)); [lia | lia | exact Hpres]).
  assert (VW : ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (Sp - 9136) 9136)
    by (apply (cmPf_vis_of_apresent (lib.Reusable.YA0n.w_H W) memc); [lia | lia | intros a Ha; apply Hpres; lia]).
  destruct (cmPf_CA Sp S16) as (CAb & _).
  (* the cut's register map, canonical *)
  rewrite ProgBridge.cfg_at_MS.
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv rsegs W (Regs6ss.mkR_of regs) regs);
    [| exact (Regs6ss.xregs_eqv_sym _ _ (Regs6ss.mkR_of_eqv regs))].
  change (Regs6ss.mkR_of regs) with
    (lib.Lib.Frame.mkR (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 2) (lib.Reusable.YK11.getr regs 3)
         (lib.Reusable.YK11.getr regs 4) (lib.Reusable.YK11.getr regs 5) (lib.Reusable.YK11.getr regs 6)
         (lib.Reusable.YK11.getr regs 7) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
         (lib.Reusable.YK11.getr regs 10) (lib.Reusable.YK11.getr regs 11) (lib.Reusable.YK11.getr regs 12)
         (lib.Reusable.YK11.getr regs 13) (lib.Reusable.YK11.getr regs 14) (lib.Reusable.YK11.getr regs 15)
         (lib.Reusable.YK11.getr regs 16) (lib.Reusable.YK11.getr regs 17) (lib.Reusable.YK11.getr regs 18)
         (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
         (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
         (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
         (lib.Reusable.YK11.getr regs 28) (lib.Reusable.YK11.getr regs 29) (lib.Reusable.YK11.getr regs 30)
         (lib.Reusable.YK11.getr regs 31)).
  rewrite H10, H11.
  replace (lib.Reusable.YK11.getr regs 2) with (Z_to_bv 64 Sp)
    by (unfold Sp, lib.Reusable.YG0d.spZ; apply lib.Lib.MState.Z_to_bv_bv_unsigned).
  (* S-A *)
  apply (cmPf_SA W ly S W memc md [] ly S memc md 0
           (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4)
           (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18)
           (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
           (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
           (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
           f len Sp FS fb
           (lib.Reusable.YK11.getr regs 5) (lib.Reusable.YK11.getr regs 6) (lib.Reusable.YK11.getr regs 7)
           (lib.Reusable.YK11.getr regs 12) (lib.Reusable.YK11.getr regs 13) (lib.Reusable.YK11.getr regs 14)
           (lib.Reusable.YK11.getr regs 15) (lib.Reusable.YK11.getr regs 16) (lib.Reusable.YK11.getr regs 17)
           (lib.Reusable.YK11.getr regs 28) (lib.Reusable.YK11.getr regs 29) (lib.Reusable.YK11.getr regs 30)
           (lib.Reusable.YK11.getr regs 31) Q
           Rf Rlen ltac:(lia) S16 HK Hfb HHM HAE VW HB STW HJ0).
  intros m1 md1 ST1 SV1 RO1 MU1 WM1 HJ1.
  pose proof HJ1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
  (* E1 *)
  apply (cmPf_E1 W ly S W memc md [] ly S m1 md1 0 Sp _ Q HJ1 S16);
    [ unfold lib.Reusable.YG0d.spZ; exact (lib.Lib.Mem.wa_unsigned (CA Sp) ltac:(lia))
    | reflexivity | exact Hgp | exact Htp | exact Hcnt | ].
  intros S2 regs2 m2 md2 pos HJ2 HP R10 Hab Hfr Hnin Hnev Hbb Hz Hfl Hkept HPRE Hfpres Hfc Hwpres.
  match type of HPRE with lib.Reusable.YG0d.ecall_pre _ _ _ _ _ ?R _ _ =>
    apply (K m1 md1 R S2 regs2 m2 md2 pos) end.
  split; [exact ST1|]. split; [exact SV1|]. split; [exact RO1|]. split; [exact MU1|]. split; [exact WM1|].
  split; [exact HJ2|]. split; [exact Hfr|]. split; [exact Hnin|]. split; [exact Hab|]. split; [exact Hnev|].
  split; [exact Hbb|]. split; [exact Hz|]. split; [exact Hfl|]. split; [exact Hkept|]. split; [exact R10|].
  split; [exact (HP 2 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 3 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 4 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 8 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 9 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 18 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 19 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 20 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 21 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 22 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 23 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 24 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 25 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 26 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [exact (HP 27 ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia))|].
  split; [unfold lib.Reusable.YG0d.spZ; exact (lib.Lib.Mem.wa_unsigned (CA Sp) ltac:(lia))|].
  split; [exact HPRE|]. split; [exact Hpres1|]. split; [exact Hfpres|]. split; [exact Hfc | exact Hwpres].
Qed.
End SAE1.
