(* lib/B/Prog/C_reac_ctrl_identity_replyTop.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): THE TOP-LEVEL
   COMPOSITION pb_reac_ctrl_identity_reply : treac_ctrl_identity_reply_spec RLO RHI B
     (lib/B/Prog/C_reac_ctrl_identity_reply.v),
   on the plan of record analyses/libreac/fuzz_ctrl/glue-B/identity_reply/pb_reac_ctrl_identity_reply.plan.md
     (a working note, not in this delivery).
   Owner a Theorem Labs lane.

   ROUTE (C) (a Theorem Labs lane 09:20Z; L3 recipe, wave lead a Theorem Labs lane): the lifted run is RB's copy of the narrowed run
   reac_ctrl_identity_reply_holds_F_on, whose shadow premise is shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len
   pa pp pn S FS) m (lib/B/Prog/reac_ctrl_identity_reply_c_on.v).  At each stretch base (the entry memc, S-B's base
   mem2, S-C's base mp, the tail's base at S-B's -1 end) the composition SUPPLIES the cut's B.ACtlRtC.ctl_rt_C by
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR at that journal's AR with the image data there (the spec's P2 carried by the kept
   classes, rtop_aro); its parts give asan_cells, ro_agree and, by C_reac_ctrl_identity_replyCover.rrC_R_on, the
   run's narrowed premise.  No ProgWorld statement is a hypothesis.  The fr apartness of the three caller cells is no
   Section hypothesis: under the accepted contract_F guard (a working branch 20372bbcc3a) it is needed only
   under 50 <= len, where Base / SCBase prove it from AR_sep_law (P10's heap block vs P11's caller frames).

   rule 24: no function proved here.  Released-proof lookup of record
   (`proof-index reac_ctrl_identity_reply reac_ctrl_identity_reply_contract_F`,
   lookup-reac_ctrl_identity_reply.txt (a working note, not in this delivery), checker CONFIRM in
   lookup-check.md (a working note, not in this delivery)): At ossv/recipes c5e779efe8c (2026-10-31), no released proof outside this unit.  Written new.

   THE CHAIN (every piece Qed in its own file; this file only composes):
     entry 0x848fc --S-A + J1--> __asan_stack_malloc_1     C_reac_ctrl_identity_replyPf.rrB_to_E1
     E1, the class-1 request                                C_reac_ctrl_identity_replyPf.rrB_E1
     S-B lifted from mem2 (base facts rrB_SB_base)          C_reac_ctrl_identity_replyPf.rrB_SB_lifted,
       ..Base.rrB_SB_base
     the journal after S-B (both ends)                      C_reac_ctrl_identity_replyComp.rrB_J_SB
     LEFT end: E2, reac_ctrl_parse                          C_reac_ctrl_identity_replyE2.rrB_E2_parse (TPARSE)
               S-C lifted from mp (base facts rrB_SC_base)  ..Ret.rrB_SC_lifted, ..SCBase.rrB_SC_base
     -1 end:   the tail lifted from S-B's end memory        ..Ret.rrB_tail_lifted, ..SCBase.rrB_tail_base
     both:     the spec's post at ret                       ..Ret.rrB_ret, with the kept classes rrB_K_SA / _E1 / _SB
       / _E2
   The entry state (YG0d.cfg_at) is the footprint contracts' MS form by YA0nR.SRr_xregs_eqv (the register map against
   Regs6ss.mkR_of), and so is each event's return state (YK11.mkst).

   DISCHARGED at the composition: the PROVED ProgWorld statements fp_tls_apart_stmt (B.ProgWorldTlsApart.fp_tls_apart)
   and ctl_block_apart_fs_stmt (B.ProgWorldBlkApart.ctl_block_apart_fs) are cited inside BaseV / SCBase; the owned
   read-only bytes come with ctl_rt_C_of_AR (B.ProgWorldOwnedRo.AR_states_owned_ro_of_AR inside it); CELLS_NOT_C1
   from the spec's P11 conjunct cid <> 1 (with the frames' disjointness, Ret.rrR_apart_frame); segs_low by
   B.ProgWorld.pws_segs_low; wx_segs_nowrap by B.ProgBridgeData.rsegs_wx_nowrap; H_fr_stk / H_fr_shadow / H_fr_gt /
   HFRAMES_C1 of rrB_J_SB from B.ProgWorldAstack.ctl_fs_of_astack at cid 1; the callee contract
   reac_ctrl_record_cksum_verify_contract_F_on inside rrB_SC_lifted / rrB_tail_lifted (Ret, by
   reac_ctrl_record_cksum_verify_holds_F_on).

   KEPT NAMED (Section hypotheses below, each with its owner): RELRO_IMG (the spec's own Section hypothesis; the
     composer
   that instantiates RLO RHI with pa_relro discharges it); LAWS, ML, TS, errno_low, SMP, ASM1 (the core B bundle /
   a Theorem Labs lane's class-1 rules); PC1 (core: ctrlb_pc_stack_malloc_1 at B := YD2l.CtrlB, a working branch
   3cd6d1dbfb3; the theorem stays generic in B); ASF, FFL; TPARSE (a Theorem Labs lane,
   pb_reac_ctrl_parse).
   No Axiom, Parameter, Admitted, admit, Abort.  Nothing of image A is Required. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c reac_ctrl_identity_reply_c
  reac_ctrl_identity_replyRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF Regs6ss.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require
  YK04 YA0n YA0nR YG00 YG01 YG0f YG0n YG0d YG0v YCbq YI00 YI04 YF0m YE01 YP09 YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr ProgBridge ProgBridgeData ProgWorld.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorld_Fs ProgWorldAstack ACtlRtC ProgWorldCtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldCtlRt.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds C_reac_ctrl_identity_reply C_reac_ctrl_parse.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP C_reac_ctrl_identity_replyLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_identity_replyPf
  C_reac_ctrl_identity_replyComp
  C_reac_ctrl_identity_replyE2 C_reac_ctrl_identity_replyBase C_reac_ctrl_identity_replyRet
  C_reac_ctrl_identity_replySCBase.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
Import ListNotations.
Open Scope Z_scope.

(* A register map is xregs_eqv to the mkR of its 31 registers (Regs6ss.mkR_of), whatever names the registers carry. *)
Lemma rtop_mkR_eqv : forall (R : bvmap 5 word)
    (x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30
      x31 : word),
  lib.Reusable.YK11.getr R 1 = x1 -> lib.Reusable.YK11.getr R 2 = x2 -> lib.Reusable.YK11.getr R 3 = x3 ->
    lib.Reusable.YK11.getr R 4 = x4 ->
  lib.Reusable.YK11.getr R 5 = x5 -> lib.Reusable.YK11.getr R 6 = x6 -> lib.Reusable.YK11.getr R 7 = x7 ->
    lib.Reusable.YK11.getr R 8 = x8 ->
  lib.Reusable.YK11.getr R 9 = x9 -> lib.Reusable.YK11.getr R 10 = x10 -> lib.Reusable.YK11.getr R 11 = x11 ->
    lib.Reusable.YK11.getr R 12 = x12 ->
  lib.Reusable.YK11.getr R 13 = x13 -> lib.Reusable.YK11.getr R 14 = x14 -> lib.Reusable.YK11.getr R 15 = x15 ->
    lib.Reusable.YK11.getr R 16 = x16 ->
  lib.Reusable.YK11.getr R 17 = x17 -> lib.Reusable.YK11.getr R 18 = x18 -> lib.Reusable.YK11.getr R 19 = x19 ->
    lib.Reusable.YK11.getr R 20 = x20 ->
  lib.Reusable.YK11.getr R 21 = x21 -> lib.Reusable.YK11.getr R 22 = x22 -> lib.Reusable.YK11.getr R 23 = x23 ->
    lib.Reusable.YK11.getr R 24 = x24 ->
  lib.Reusable.YK11.getr R 25 = x25 -> lib.Reusable.YK11.getr R 26 = x26 -> lib.Reusable.YK11.getr R 27 = x27 ->
    lib.Reusable.YK11.getr R 28 = x28 ->
  lib.Reusable.YK11.getr R 29 = x29 -> lib.Reusable.YK11.getr R 30 = x30 -> lib.Reusable.YK11.getr R 31 = x31 ->
  lib.Lib.Regs6ss.xregs_eqv (mkR x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23
    x24 x25 x26 x27 x28 x29 x30 x31) R.
Proof.
  intros R x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29
    x30 x31
    E1 E2 E3 E4 E5 E6 E7 E8 E9 E10 E11 E12 E13 E14 E15 E16 E17 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 E28 E29 E30 E31.
  subst.
  exact (lib.Lib.Regs6ss.xregs_eqv_sym _ _ (lib.Lib.Regs6ss.mkR_of_eqv R)).
Qed.

Section Top.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variables RLO RHI : Z.
Variable B : lib.Reusable.YG0f.asyms.
(* the spec's own Section hypothesis (C_reac_ctrl_identity_reply.v:49): OWNER PENDING: the composer that instantiates
   RLO RHI with the B PA instance's pa_relro = [0x9f168, 0xa15e8) *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a.
(* OWNER PENDING: the core B bundle (the record core's TfibLib, lib/Reusable/YCeg.v; its line 25 names a refused name on
   every B base) *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
Hypothesis TS : lib.Reusable.YF0m.CtrlTSyms B.
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
(* OWNER PENDING: a Theorem Labs lane's class-1 fake-stack rules, a working branch ff613211c11 (cgif lib/A/ACed.v:125-133) *)
Hypothesis SMP : lib.Reusable.YCbq.stack_malloc_progressP B.
Hypothesis ASM1 : lib.Reusable.YG0d.astack_malloc_realizes rsegs B 1.
Hypothesis ASF : lib.Reusable.YG0d.astack_free_law rsegs B.
Hypothesis FFL : lib.Reusable.YCbq.frame_flag_lawP rsegs B.
(* OWNER PENDING: core; proved as ctrlb_pc_stack_malloc_1 at B := YD2l.CtrlB (a working branch
   3cd6d1dbfb3); the theorem is generic in B, so it is named *)
Hypothesis PC1 : lib.Reusable.YG0f.pc_stack_malloc (lib.Reusable.YG0f.as_code B) 1 = ASAN_STACK_MALLOC_1.
(* OWNER PENDING: a Theorem Labs lane, pb_reac_ctrl_parse (not Qed) *)
Hypothesis TPARSE : lib.B.Prog.C_reac_ctrl_parse.treac_ctrl_parse_spec lib.Reusable.YB1v.tfibsegs B RLO RHI.

(* The image data at a later memory of the walk: the spec's P2 at memc, carried by the kept classes' image clause
   (YCbq.acall_kept's third conjunct) to the memory and world the kept classes reach (as E2's premise HARO reads it). *)
Lemma rtop_aro : forall lyq Sq (Wq W2 : lib.Reusable.YA0n.world rsegs) (mq m2 : word -> option byte) slo shi E,
  lib.Reusable.YCbq.acall_kept rsegs B lyq Sq Wq mq W2 m2 slo shi E ->
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H Wq) mq) ->
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W2) m2).
Proof.
  intros lyq Sq Wq W2 mq m2 slo shi E (_ & _ & K3 & _) HP a Hin Ho Herr.
  assert (Himg : lib.Reusable.YG0d.in_img rsegs a).
  { destruct Hin as [(sg & Hsg & _ & Hb) | Hr]; [exists sg; split; [exact Hsg | exact Hb] | exact (RELRO_IMG a Hr)]. }
  etransitivity; [exact (K3 a Himg Ho Herr) | exact (HP a Hin Ho Herr)].
Qed.

Local Ltac rtop_hp HP r :=
  etransitivity; [exact (HP r ltac:(unfold lib.Reusable.YG0d.acallee_saved; lia)) | reflexivity].

(* pb_reac_ctrl_identity_reply. *)
Theorem pb_reac_ctrl_identity_reply : lib.B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec RLO RHI B.
Proof.
  unfold lib.B.Prog.C_reac_ctrl_identity_reply.treac_ctrl_identity_reply_spec.
  intros STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k regs fr len pa pp pn g
    P1 P2 P3r P3a P4g P4t P5f P5l P5a P5p P5n Rfr Rlen Rpa Rpp Rpn P7a P7b P7c P8 P9 P10 P11.
  match goal with |- lib.Reusable.YA0n.SRr _ _ _ ?Q0 => set (Q := Q0) end.
  unfold lib.B.Prog.C_reac_ctrl_identity_reply.REAC_CTRL_IDENTITY_REPLY_STK in P7b.
  set (S := lib.Reusable.YG0d.spZ regs) in *.
  assert (HSp : lib.Reusable.YG0d.spZ regs = S) by reflexivity.
  set (ra := lib.Reusable.YK11.getr regs 1). set (gp := lib.Reusable.YK11.getr regs 3). set (tp :=
    lib.Reusable.YK11.getr regs 4).
  set (t0 := lib.Reusable.YK11.getr regs 5). set (t1 := lib.Reusable.YK11.getr regs 6). set (t2 :=
    lib.Reusable.YK11.getr regs 7).
  set (s0 := lib.Reusable.YK11.getr regs 8). set (s1 := lib.Reusable.YK11.getr regs 9).
  set (a5 := lib.Reusable.YK11.getr regs 15). set (a6 := lib.Reusable.YK11.getr regs 16). set (a7 :=
    lib.Reusable.YK11.getr regs 17).
  set (s2 := lib.Reusable.YK11.getr regs 18). set (s3 := lib.Reusable.YK11.getr regs 19). set (s4 :=
    lib.Reusable.YK11.getr regs 20). set (s5 := lib.Reusable.YK11.getr regs 21).
  set (s6 := lib.Reusable.YK11.getr regs 22). set (s7 := lib.Reusable.YK11.getr regs 23). set (s8 :=
    lib.Reusable.YK11.getr regs 24). set (s9 := lib.Reusable.YK11.getr regs 25).
  set (s10 := lib.Reusable.YK11.getr regs 26). set (s11 := lib.Reusable.YK11.getr regs 27).
  set (t3 := lib.Reusable.YK11.getr regs 28). set (t4 := lib.Reusable.YK11.getr regs 29). set (t5 :=
    lib.Reusable.YK11.getr regs 30). set (t6 := lib.Reusable.YK11.getr regs 31).
  (* ---- the entry: the journal's AR, frames, presence and astk_ok; the numerics of the window ---- *)
  pose proof P1 as (HARc & _ & _ & _ & _ & HFRc & _ & _ & _ & _ & _ & _ & _ & HPRc & HASc & _).
  destruct HASc as (_ & _ & Hc1 & Hc2 & Hc3 & Hc4 & _).
  pose proof (@lib.Reusable.YM05.alloc_ceiling_val rc) as [Hceil Hceil2].
  change (2 ^ 47) with 140737488355328 in Hc4.
  assert (HSK : 9072 <= S) by lia.
  assert (HS : S < 2 ^ 64) by lia.
  assert (HHM : HIGHMEM_BEG <= S - 9072) by (unfold HIGHMEM_BEG; lia).
  assert (HAE : S <= APPMEM_END) by (unfold APPMEM_END; lia).
  (* the entry cut's ctl_rt_C (route (C)): its asan_cells and ro_agree parts at memc *)
  pose proof (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TS LAWS RLO RHI lyc Sc W memc mdc HARc
                (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ P2 (Z.le_refl _) (Z.le_refl _))) as HRTc.
  assert (ROc : B.MemNorm.ro_agree rsegs memc) by exact (proj2 (proj2 (proj2 HRTc))).
  assert (ACc : asan_cells memc) by exact (proj1 HRTc).
  assert (STc : stk rsegs memc (S - 9072) S)
    by (apply (B.ProgWorldAstack.pwfs_stk_of_present W memc); [lia | lia | intros a Ha; apply HPRc; lia]).
  assert (VWc : B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (S - 9072) 9072).
  { split; [lia|]. split; [lia|]. intros a Ha. exact (proj1 (HPRc a ltac:(lia))). }
  assert (Hcnt : lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames Sc) < lib.Reusable.YG00.fs_frames 1) by lia.
  (* CELLS_NOT_C1 (Base's form) from P11's cid <> 1: the frame holding a cell byte is unique (rrR_apart_frame) *)
  assert (CN1 : reply_args fr pa pp pn = true -> forall a cid q,
            C_reac_ctrl_identity_reply.treply_out pa pp pn a -> In (cid, q) (lib.Reusable.YG01.frames Sc) ->
            lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, q)) -> cid <> 1).
  { intros RA a cid q Ha Hin Hr Hc. subst cid.
    destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & Hcl & _).
    destruct (Hcl a Ha) as ((c0 & q0 & Hin0 & Hc0 & Hr0) & _).
    assert (Hne : (c0, q0) <> (1, q)) by (intros E; injection E as E1 _; exact (Hc0 E1)).
    unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr, Hr0. cbn [fst snd] in Hr, Hr0.
    destruct (C_reac_ctrl_identity_replyRet.rrR_apart_frame B lyc Sc W memc mdc q c0 q0 a HARc Hin Hin0 Hne
                (or_introl Hr0)) as (Hn & _).
    apply Hn. change (lib.Reusable.YG00.fs_frame_bytes 1) with 128 in Hr. exact Hr. }
  (* P11 in Base's form (without cid <> 1) *)
  assert (P11b : reply_args fr pa pp pn = true ->
    pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
    (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
    (forall a, C_reac_ctrl_identity_reply.treply_out pa pp pn a ->
       (exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames Sc) /\
          lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos))) /\
       lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0) (lib.Reusable.YG0d.ablocks B lyc Sc)
         lyc own a) /\
    lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
      lib.Reusable.YG0f.SHADOW_OFF pa 2 /\
    lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
      lib.Reusable.YG0f.SHADOW_OFF pp 8 /\
    lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
      lib.Reusable.YG0f.SHADOW_OFF pn 8).
  { intros RA. destruct (P11 RA) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
    split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
    split; [exact A6|].
    split; [|split; [exact A8|]; split; [exact A9 | exact A10]].
    intros a Ha. destruct (A7 a Ha) as ((c & q & Hin & _ & Hr) & Haw).
    split; [exists c, q; split; [exact Hin | exact Hr] | exact Haw]. }
  (* ---- the entry state in the footprint form, then S-A + J1 ---- *)
  rewrite B.ProgBridge.cfg_at_MS.
  change (Z_to_bv 64 C_reac_ctrl_identity_reply.A_reac_ctrl_identity_replyP) with (Z_to_bv 64 REAC_CTRL_IDENTITY_REPLY).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv _ W
           (mkR ra (Z_to_bv 64 S) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fr) (Z_to_bv 64 len) (Z_to_bv 64 pa)
              (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) regs).
  2: { apply rtop_mkR_eqv; try reflexivity.
       - unfold S, lib.Reusable.YG0d.spZ. rewrite Z_to_bv_bv_unsigned. reflexivity.
       - exact P5f.
       - exact P5l.
       - exact P5a.
       - exact P5p.
       - exact P5n. }
  apply (C_reac_ctrl_identity_replyPf.rrB_to_E1 B LAWS B.ProgWorld.pws_segs_low B.ProgBridgeData.rsegs_wx_nowrap
           STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
           lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr fr len pa pp pn S g t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 Q
           P1 P7b P7c Rfr Rlen Rpa Rpp Rpn HS P7a HSK ROc STc P9 ACc HHM HAE VWc).
  intros m1 mc mdc1 HR HREL HROS HJ1.
  (* ---- E1: the class-1 request ---- *)
  apply (C_reac_ctrl_identity_replyPf.rrB_E1 B LAWS B.ProgWorld.pws_segs_low errno_low ML SMP ASM1 PC1
           STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6
           fr len pa pp pn S Q HJ1 P7b P7c HS P7a HSK P4g P4t Hcnt).
  intros S2 regs2 mem2 md2 pos HJ2 HP H10 HAB HFR HNI HNEV HBB HZ HFL HKEPT HECP HFPRES HFRC HWPRES.
  set (regsT := C_reac_ctrl_identity_replyPf.rrB_regsT gp tp t0 t1 t2 a5 a6 a7 s2 s8 s9 s10 t3 t4 t5 t6
                  fr len pa pp pn S) in *.
  assert (HA : rA S mod 32 = 0 /\ S - 144 <= rA S <= S - 128) by (unfold rA; Z.div_mod_to_equations; lia).
  assert (Hsp : lib.Reusable.YG0d.spZ regsT = rA S).
  { unfold lib.Reusable.YG0d.spZ. change (lib.Reusable.YK11.getr regsT 2) with (Z_to_bv 64 (rA S)).
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia. }
  assert (HPRESW : forall a, lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regsT
    ->
            lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a)
    by (intros a Ha; apply HWPRES; rewrite Hsp in Ha; lia).
  assert (HFRCOND : forall a, 0 <= a < 2 ^ 64 -> ~ lib.Reusable.YG0n.aowned B lyc Sc a ->
            ~ lib.Reusable.YG0n.aowned B lyc S2 a ->
            ~ (lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regsT) ->
            lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2 a =
            lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1 a)
    by (intros a H1 H2 H3 H4; apply HFRC; [exact H1 | exact H2 | exact H3 | rewrite Hsp in H4; lia]).
  (* the new frame's facts at mem2 (B.ProgWorldAstack.ctl_fs_of_astack at cid 1, as Base applies it) *)
  pose proof HJ2 as (HAR2 & _).
  pose proof HECP as (HARecp & Hret & Hsp16 & HlyESP & Hsphi & Hpres_ecp & Hgp & Htp).
  assert (Hfb1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
  pose proof (B.ProgWorldAstack.ctl_fs_of_astack B 1 B.ProgWorld.ctl_fs_geom LAWS ltac:(lia)
                lyc Sc S2 W regsT regs2 m1 mem2 mdc1 md2 pos
                (lib.Reusable.YG0d.spZ regsT - lib.Reusable.YG0d.ESTACK) 128
                HECP ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; lia) HFR HNI HAR2 H10 HZ HFL HPRESW HFRCOND
                ltac:(rewrite Hfb1; lia)) as HFS.
  cbv zeta in HFS. change (Z.to_nat 1) with 1%nat in HFS.
  assert (HfB1 : fs_B 1 = 128) by (vm_compute; reflexivity).
  rewrite HfB1 in HFS.
  destruct HFS as (Hjj0 & _ & HflagB & HwordB & Hshz & _ & Hfrstk & Hfrapp & Hfr64 & HFSle & Hfrle & Hfrgt & _).
  set (FSc := lib.Reusable.YG0f.ly_F lyc) in *.
  set (G := fs_frame FSc 1 pos) in *.
  assert (EG : G = lib.Reusable.YG0f.frame_addr lyc 1 pos).
  { pose proof (B.ProgWorld.ctl_fs_geom FSc 1 pos ltac:(lia)) as (_ & _ & EGf & _).
    change (Z.to_nat 1) with 1%nat in EGf. unfold G. rewrite EGf. reflexivity. }
  assert (HGapp : (G + 128 <= LOWMEM_END \/ HIGHMEM_BEG <= G) /\ 0 <= G /\ G + 128 <= APPMEM_END).
  { pose proof (Hfrapp G ltac:(lia)) as A1. pose proof (Hfrapp (G + 127) ltac:(lia)) as A2.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in *. lia. }
  (* ---- the kept classes up to mem2; the S-B cut's ctl_rt_C (route (C)) at HJ2's AR, the image data at mem2 being
     P2's carried by them ---- *)
  pose proof (C_reac_ctrl_identity_replyRet.rrB_K_SA B LAWS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S m1 mc mdc1 P1 P7b P7c HR HREL HROS HJ1) as HK1.
  pose proof (C_reac_ctrl_identity_replyRet.rrB_K_E1 B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc S2 W memc m1 mem2 md2 k
                S pos P7b P7c P7a HSK HK1 HKEPT HJ2) as HK2.
  pose proof (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TS LAWS RLO RHI lyc S2 W mem2 md2 HAR2
                (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ (rtop_aro _ _ _ _ _ _ _ _ _ HK2 P2)
                   (Z.le_refl _) (Z.le_refl _))) as HRT2.
  (* ---- S-B: base facts at mem2 (Base), the lift (Pf) ---- *)
  destruct (C_reac_ctrl_identity_replyBase.rrB_SB_base B LAWS TS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc
    mdc k
              ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fr len pa pp pn S g P1 Rfr Rlen Rpa Rpp Rpn P7a P7b P7c P9
                P10 P11b
              m1 mc mdc1 HR HREL HROS HJ1 regsT regs2 S2 mem2 md2 pos HECP HJ2 H10 HFR HNI HZ HFL HPRESW HFRCOND HKEPT
              HRT2 P4t HAB CN1)
    as (ja & jp & jn & B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10 & B11 & B12 & B13 & B14 & B15 & B16 & B17 &
      B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & B28 & B29 & B30 & B31 & B32 & B33 & B34 & B35 & B36
      & B37 & B38 & B39).
  change (lib.Reusable.YK11.mkst regs2 (Z_to_bv 64 0x8497c) mem2 (lib.Reusable.YK11.seg_rom rsegs)) with
    (lib.Lib.MState.MS regs2 lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x8497c) lib.Reusable.YK11.fp_csr None mem2
       (lib.Reusable.YK11.seg_rom rsegs)).
  apply (lib.Reusable.YA0nR.SRr_xregs_eqv _ W
           (mkR (lib.Reusable.YK11.getr regs2 1) (Z_to_bv 64 (rA S)) gp tp (lib.Reusable.YK11.getr regs2 5)
             (lib.Reusable.YK11.getr regs2 6) (lib.Reusable.YK11.getr regs2 7) (Z_to_bv 64 S)
              (Z_to_bv 64 (rA S)) (Z_to_bv 64 G) (lib.Reusable.YK11.getr regs2 11) (lib.Reusable.YK11.getr regs2 12)
                (lib.Reusable.YK11.getr regs2 13) (lib.Reusable.YK11.getr regs2 14) (lib.Reusable.YK11.getr regs2 15)
                (lib.Reusable.YK11.getr regs2 16) (lib.Reusable.YK11.getr regs2 17)
              s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len) s8 s9 s10
              (wa ASAN_K) (lib.Reusable.YK11.getr regs2 28) (lib.Reusable.YK11.getr regs2 29) (lib.Reusable.YK11.getr
                regs2 30) (lib.Reusable.YK11.getr regs2 31)) regs2).
  2: { apply rtop_mkR_eqv;
         [ reflexivity
         | rtop_hp HP 2
         | rtop_hp HP 3
         | rtop_hp HP 4
         | reflexivity
         | reflexivity
         | reflexivity
         | rtop_hp HP 8
         | rtop_hp HP 9
         | (rewrite H10, EG; reflexivity)
         | reflexivity
         | reflexivity
         | reflexivity
         | reflexivity
         | reflexivity
         | reflexivity
         | reflexivity
         | rtop_hp HP 18
         | rtop_hp HP 19
         | rtop_hp HP 20
         | rtop_hp HP 21
         | rtop_hp HP 22
         | rtop_hp HP 23
         | rtop_hp HP 24
         | rtop_hp HP 25
         | rtop_hp HP 26
         | rtop_hp HP 27
         | reflexivity
         | reflexivity
         | reflexivity
         | reflexivity ]. }
  refine (C_reac_ctrl_identity_replyPf.rrB_SB_lifted B.ProgBridgeData.rsegs_wx_nowrap W md2 ra gp tp s0 s1 s2 s3 s4 s5
    s6 s7 s8 s9 s10 s11
            lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem2 fr len pa pp pn S FSc g ja jp jn pos
            (lib.Reusable.YK11.getr regs2 1) (lib.Reusable.YK11.getr regs2 5) (lib.Reusable.YK11.getr regs2 6)
              (lib.Reusable.YK11.getr regs2 7) (lib.Reusable.YK11.getr regs2 11) (lib.Reusable.YK11.getr regs2 12)
              (lib.Reusable.YK11.getr regs2 13) (lib.Reusable.YK11.getr regs2 14) (lib.Reusable.YK11.getr regs2 15)
              (lib.Reusable.YK11.getr regs2 16) (lib.Reusable.YK11.getr regs2 17) (lib.Reusable.YK11.getr regs2 28)
              (lib.Reusable.YK11.getr regs2 29) (lib.Reusable.YK11.getr regs2 30) (lib.Reusable.YK11.getr regs2 31) Q
            B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 B11 B12 B13 B14 B15 B16 B17 B18 B19 B20 B21 B22 B23 B24 B25 B26 B27 B28 B29
              B30 B31 B32 B33 B34 B35 B36 B37 B38 B39 _).
  intros ms5 md5 HSBp.
  pose proof HSBp as ((s0' & HQ & HREL5 & HROS5 & _ & _) & _ & _).
  (* ---- the journal after S-B, the kept classes up to S-B's end ---- *)
  assert (HFC1 : forall a, G <= a < G + 128 \/ shadow_addr G <= a < shadow_addr G + 16 ->
            lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0)
              (lib.Reusable.YG0d.ablocks B lyc S2) lyc ((1, pos) :: own) a).
  { intros a Ha. unfold lib.Reusable.YCbq.awr_byte. right; right; right.
    unfold lib.Reusable.YCbq.in_frames. exists 1, pos. split; [left; reflexivity|].
    unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- EG, Hfb1.
    destruct Ha as [Ha|Ha]; [left; lia | right].
    unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF. unfold shadow_addr, ASAN_K in Ha.
    change (128 / 8) with 16. lia. }
  pose proof (C_reac_ctrl_identity_replyComp.rrB_J_SB B LAWS B.ProgWorld.pws_segs_low STK sp0 FP ly S0 W0 mem0 md0
                ((1, pos) :: own) lyc S2 W mem2 md2 k ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr fr len pa pp pn S FSc g pos ms5 md5 HJ2 HSBp P7b P7c
                Hfrstk Hshz Hfrgt HFC1) as HJ5.
  pose proof (C_reac_ctrl_identity_replyRet.rrB_K_SB B LAWS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc S2 W memc mdc k
                ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mem2
                fr len pa pp pn S FSc g pos md2 ms5 md5 P1 P7b P7c HK2 HSBp HJ5 HAB eq_refl) as HK3.
  unfold C_reac_ctrl_identity_replyLib.rrB_QSB in HQ.
  destruct HQ as [(mc5 & m5n & x5 & x6 & x7 & x13 & x14 & x15 & x16 & x17 & x28 & x29 & x30 & x31 &
                   Es & HBI & HRA & MU5 & _ & _ & _ & BS5) |
                  (mc5 & r & y1 & y2 & y5 & y6 & y7 & y9 & y11 & y12 & y13 & y14 & y15 & y16 & y17 & y19 & y20 &
                   y21 & y22 & y23 & y24 & y27 & y28 & y29 & y30 & y31 & Es & HBI & HEI & Er & HOUT)].
  - (* ==== LEFT end: reac_ctrl_parse's first slot ==== *)
    rewrite Es in HREL5. destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL5) as [Ems HMR].
    set (m5 := ms_mem ms5) in *.
    destruct (C_reac_ctrl_identity_replySCBase.rrB_SBL_mem ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      (B.MemNorm.normalize rsegs mem2) mc5 m5n m5
                S FSc G pos HHM HAE (proj1 (proj2 HGapp)) (proj2 (proj2 HGapp)) (proj1 HGapp) HBI MU5 HMR)
      as (HSV5 & HFL15).
    pose proof HK3 as (_ & K2 & _ & _).
    (* E2's premises at the call *)
    assert (HARO : lib.Reusable.YE01.arodata_okS rsegs B RLO RHI
                     (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m5))
      by exact (rtop_aro _ _ _ _ _ _ _ _ _ HK3 P2).
    assert (HMSG : 50 <= len -> forall i, (i < 50)%nat ->
              lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m5 (fr + Z.of_nat i) =
              Some (lib.Prog.RcParse.cp_v g i)).
    { intros HL i Hi. destruct (P10 HRA HL) as ((nb & Hin & Hnb) & Hgarr).
      etransitivity; [exact (K2 fr nb (Z.of_nat i) Hin ltac:(lia) (fun HH => HH))|].
      assert (Hilt : (i < length (map (fun bb : byte => bv_unsigned bb) g))%nat) by (rewrite length_map, P9; exact Hi).
      destruct (Hgarr i Hilt) as [Hvm Hvr].
      unfold lib.Reusable.YI04.val_mem in Hvm.
      pose proof (Hvm 0%nat ltac:(lia)) as Hmb. rewrite Z.add_0_r in Hmb.
      destruct (nth_error g i) as [b0|] eqn:Eb; [|exfalso; apply nth_error_None in Eb; lia].
      assert (Hnthb : nth i (map (fun bb : byte => bv_unsigned bb) g) 0 = bv_unsigned b0)
        by (apply nth_error_nth; apply map_nth_error; exact Eb).
      rewrite Hnthb in Hmb, Hvr.
      assert (Hb0 : nth i g lib.Prog.RcParse.cp_z = b0) by (apply nth_error_nth; exact Eb).
      unfold lib.Prog.RcParse.cp_v, lib.Prog.RcParse.cp_b. rewrite Hb0.
      unfold lib.Reusable.YG0n.aview. change lib.Reusable.YB1v.tfibsegs with rsegs in Hmb. rewrite Hmb.
      cbn [option_map].
      rewrite (lib.Reusable.YI04.le_byte_small (bv_unsigned b0) 1 0
                ltac:(replace (2 ^ (8 * Z.of_nat 1)) with 256 by (vm_compute; reflexivity); lia) ltac:(lia)).
      change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
      rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
      rewrite Z.mod_small by lia. reflexivity. }
    assert (BS5r : lib.Lib.Mem.bytes_at rsegs m5 (G / 8 + ASAN_K + 4)
                     [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4])
      by exact (proj2 (B.MemNorm.bytes_at_rel rsegs m5 m5n _ _ HMR) BS5).
    pose proof HJ5 as (HAR5 & _ & _ & _ & _ & HFR5 & _).
    assert (Hin5 : In (1, pos) (lib.Reusable.YG01.frames S2))
      by (rewrite HFR5; apply in_or_app; left; left; reflexivity).
    destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc S2 W m5 md5 1 pos HAR5 Hin5) as (_ & _ & _ & Hsh5).
    rewrite <- EG, Hfb1 in Hsh5.
    assert (G8 : G mod 8 = 0) by exact (B.ProgWorldAstack.pwfs_mod8 _ Hfr64).
    assert (GHI : G + 128 <= 2 ^ 64) by (destruct HGapp as (_ & _ & X); unfold APPMEM_END in X; lia).
    assert (HADDR : lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m5)
                      lib.Reusable.YG0f.SHADOW_OFF (G + 32) 36).
    { intros x Hx.
      pose proof (Z.div_mod G 8 ltac:(lia)) as DG.
      pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
      assert (Hcase : exists i, 0 <= i < 5 /\ x / 8 = G / 8 + 4 + i /\ (i = 4 -> x mod 8 < 4)).
      { exists (x / 8 - G / 8 - 4). split; [lia|]. split; [lia|]. intros H4. lia. }
      destruct Hcase as (i & Hi & Exi & Hi4).
      destruct BS5r as (_ & _ & Hrd).
      pose proof (Hrd (Z.to_nat i) ltac:(cbn [length]; lia)) as Hm.
      rewrite Z2Nat.id in Hm by lia.
      destruct (Hsh5 (i + 4) ltac:(change (128 / 8) with 16; lia)) as [[Hh _] _].
      assert (Ea : lib.Reusable.YG0f.shadow_addr G + (i + 4) = G / 8 + ASAN_K + 4 + i)
        by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, ASAN_K; lia).
      rewrite Ea in Hh.
      assert (Esh : lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x = G / 8 + ASAN_K + 4 + i)
        by (unfold lib.Reusable.YG0v.shadow_of_addr, lib.Reusable.YG0f.SHADOW_OFF, ASAN_K; lia).
      assert (Hv : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m5
                     (lib.Reusable.YG0v.shadow_of_addr lib.Reusable.YG0f.SHADOW_OFF x) =
                   option_map (fun b : byte => bv_unsigned b)
                     (nth_error [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 4] (Z.to_nat i))).
      { rewrite Esh. etransitivity; [exact (B.ProgWorld.aview_vis_mrd W m5 _ Hh)|].
        unfold lib.Lib.Mem.wa in Hm. rewrite Hm. reflexivity. }
      assert (Hi' : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4) by lia.
      destruct Hi' as [-> | [-> | [-> | [-> | ->]]]].
      - exists 0. split; [exact Hv | left; reflexivity].
      - exists 0. split; [exact Hv | left; reflexivity].
      - exists 0. split; [exact Hv | left; reflexivity].
      - exists 0. split; [exact Hv | left; reflexivity].
      - exists 4. split; [exact Hv|]. right. split; [exact (Hi4 eq_refl) | lia]. }
    assert (HBLK : 50 <= len -> exists Lf : Z, In (fr, Lf) (lib.Reusable.YG0d.ablocks B lyc S2) /\
                                                50 <= lib.Reusable.YG00.req_size Lf).
    { intros HL. destruct (P10 HRA HL) as ((nb & Hin & Hnb) & _). exists nb. split; [rewrite HAB; exact Hin | exact
      Hnb]. }
    assert (Hcnt2 : lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames S2) < lib.Reusable.YG00.fs_frames 1).
    { rewrite HFR.
      assert (E : lib.Reusable.YG01.count_cid 1 ((1, pos) :: lib.Reusable.YG01.frames Sc) =
                  1 + lib.Reusable.YG01.count_cid 1 (lib.Reusable.YG01.frames Sc)) by reflexivity.
      lia. }
    (* ---- E2: reac_ctrl_parse ---- *)
    rewrite Ems.
    apply (C_reac_ctrl_identity_replyE2.rrB_E2_parse B RLO RHI TPARSE STK sp0 FP ly S0 W0 mem0 md0 own pos lyc S2 W m5
      md5 k
             gp tp x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 fr len pa pp pn S G g Q HJ5 HARO P4g P4t Rlen HSK HS
             P7b P7c EG G8 GHI Hcnt2 HBLK HADDR P9 HMSG).
    intros W2 ly2 S2' regs2' mp md2' HE2.
    pose proof HE2 as (Hle2 & HJp & HFRp & HABp & _ & E10 & _ & HKE2 & E2 & E3 & E4 & E8 & E9 & E18 & E19 & E20 & E21 &
                       E22 & E23 & E24 & E25 & E26 & E27 & _).
    change (lib.Reusable.YK11.mkst regs2' (Z_to_bv 64 0x84a68) mp (lib.Reusable.YK11.seg_rom rsegs)) with
      (lib.Lib.MState.MS regs2' lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x84a68) lib.Reusable.YK11.fp_csr None mp
         (lib.Reusable.YK11.seg_rom rsegs)).
    apply (lib.Reusable.YA0nR.SRr_xregs_eqv _ W2
             (mkR (lib.Reusable.YK11.getr regs2' 1) (Z_to_bv 64 (rA S)) gp tp (lib.Reusable.YK11.getr regs2' 5)
               (lib.Reusable.YK11.getr regs2' 6) (lib.Reusable.YK11.getr regs2' 7)
                (Z_to_bv 64 S) (Z_to_bv 64 (rA S)) (Z_to_bv 64 (fst (lib.Prog.RcParse.ctrlparse len g)))
                (lib.Reusable.YK11.getr regs2' 11) (lib.Reusable.YK11.getr regs2' 12) (lib.Reusable.YK11.getr regs2'
                  13) (lib.Reusable.YK11.getr regs2' 14) (lib.Reusable.YK11.getr regs2' 15) (lib.Reusable.YK11.getr
                  regs2' 16) (lib.Reusable.YK11.getr regs2' 17)
                (Z_to_bv 64 G) (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len)
                (Z_to_bv 64 (G + 32)) (Z_to_bv 64 (G / 8 + ASAN_K)) (Z_to_bv 64 G) (wa ASAN_K)
                (lib.Reusable.YK11.getr regs2' 28) (lib.Reusable.YK11.getr regs2' 29) (lib.Reusable.YK11.getr regs2'
                  30) (lib.Reusable.YK11.getr regs2' 31)) regs2').
    2: { apply rtop_mkR_eqv;
           [ reflexivity
           | exact E2
           | exact E3
           | exact E4
           | reflexivity
           | reflexivity
           | reflexivity
           | exact E8
           | exact E9
           | exact E10
           | reflexivity
           | reflexivity
           | reflexivity
           | reflexivity
           | reflexivity
           | reflexivity
           | reflexivity
           | exact E18
           | exact E19
           | exact E20
           | exact E21
           | exact E22
           | exact E23
           | exact E24
           | exact E25
           | exact E26
           | exact E27
           | reflexivity
           | reflexivity
           | reflexivity
           | reflexivity ]. }
    pose proof (C_reac_ctrl_identity_replyRet.rrB_K_E2 B LAWS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc S2 W memc mdc m5
      md5 k
                  gp tp fr len pa pp pn S G g pos W2 ly2 S2' regs2' mp md2' P1 P7b P7c P7a HSK HK3 HJ5 HAB EG HE2) as
                    HKp.
    assert (HABp' : lib.Reusable.YG0d.ablocks B ly2 S2' = lib.Reusable.YG0d.ablocks B lyc Sc) by (rewrite HABp; exact
      HAB).
    (* ---- S-C: the cut's ctl_rt_C at mp (route (C): ctl_rt_C_of_AR at the journal's AR after the call, the image data
       at mp being P2's carried by the kept classes), base facts at mp (SCBase), the lift (Ret), the post (Ret) ---- *)
    pose proof HJp as (HARp & _).
    pose proof (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TS LAWS RLO RHI ly2 S2' W2 mp md2' HARp
                  (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ (rtop_aro _ _ _ _ _ _ _ _ _ HKp P2)
                     (Z.le_refl _) (Z.le_refl _))) as HRTp.
    destruct (C_reac_ctrl_identity_replySCBase.rrB_SC_base B LAWS TS STK sp0 FP ly S0 W0 mem0 md0 own lyc
      Sc W
                memc mdc k tp fr len pa pp pn S g P1 P4t Rfr Rlen Rpa Rpp Rpn P7a P7b P7c P9 P10 P11
                pos ly2 S2' W2 mp md2' HJp HABp' HKp HRTp
                ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 S2 m5 md5 regs2' HJ5 HRA HSV5 HFL15 HE2)
      as (ja2 & jp2 & jn2 & C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12 & C13 & C14 & C15 & C16 & C17
        & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & C28 & C29 & C30 & C31 & C32 & C33 & C34 & C35 &
        C36 & C37 & C38 & C39 & C40 & C41 & C42 & C43).
    refine (C_reac_ctrl_identity_replyRet.rrB_SC_lifted B.ProgBridgeData.rsegs_wx_nowrap W2 md2' ra gp tp s0 s1 s2 s3
      s4 s5 s6 s7 s8 s9 s10 s11
              lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr mp fr len pa pp pn S FSc g ja2 jp2 jn2 pos
              (lib.Reusable.YK11.getr regs2' 1) (lib.Reusable.YK11.getr regs2' 5) (lib.Reusable.YK11.getr regs2' 6)
                (lib.Reusable.YK11.getr regs2' 7) (lib.Reusable.YK11.getr regs2' 11) (lib.Reusable.YK11.getr regs2'
                12) (lib.Reusable.YK11.getr regs2' 13) (lib.Reusable.YK11.getr regs2' 14) (lib.Reusable.YK11.getr
                regs2' 15) (lib.Reusable.YK11.getr regs2' 16) (lib.Reusable.YK11.getr regs2' 17)
                (lib.Reusable.YK11.getr regs2' 28) (lib.Reusable.YK11.getr regs2' 29) (lib.Reusable.YK11.getr regs2'
                30) (lib.Reusable.YK11.getr regs2' 31) Q
              C1 C2 C3 C4 C5 C6 C7 C8 C9 C10 C11 C12 C13 C14 C15 C16 C17 C18 C19 C20 C21 C22 C23 C24 C25 C26 C27 C28
                C29 C30 C31 C32 C33 C34 C35 C36 C37 C38 C39 C40 C41 C42 C43 _).
    intros ms' md' HSCp.
    apply lib.Reusable.YA0n.SRr_ret.
    exact (C_reac_ctrl_identity_replyRet.rrB_ret B LAWS ML ASF FFL STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k
             regs fr len pa pp pn S FSc g pos ly2 S2' W2 mp md2' ms' md' P1 P3r HSp P7b P7c P11 HJp Hle2 HABp' eq_refl
             HKp HSCp).
  - (* ==== -1 end: the epilogue entry 0x84bdc ==== *)
    rewrite Es in HREL5. destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ HREL5) as [Ems HMR].
    destruct (C_reac_ctrl_identity_replySCBase.rrB_SBR_mem ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
      (B.MemNorm.normalize rsegs mem2) mc5 (ms_mem ms5)
                fr len pa pp pn S FSc G pos g HBI HOUT HMR) as (HSVt & HFL1t & HOUTt).
    (* the tail's cut: ctl_rt_C at S-B's -1 end (ctl_rt_C_of_AR at HJ5's AR, the image data by the kept classes) *)
    pose proof HJ5 as (HAR5 & _).
    pose proof (B.ProgWorldCtlRtC.ctl_rt_C_of_AR B TS LAWS RLO RHI lyc S2 W (ms_mem ms5) md5 HAR5
                  (B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ (rtop_aro _ _ _ _ _ _ _ _ _ HK3 P2)
                     (Z.le_refl _) (Z.le_refl _))) as HRT5.
    destruct (C_reac_ctrl_identity_replySCBase.rrB_tail_base B LAWS TS STK sp0 FP ly S0 W0 mem0 md0 own lyc
      Sc W
                memc mdc k tp fr len pa pp pn S g P1 P4t Rfr Rlen Rpa Rpp Rpn P7a P7b P7c P9 P10 P11
                pos lyc S2 W (ms_mem ms5) md5 HJ5 HAB HK3 HRT5
                ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 HSVt HFL1t HOUTt)
      as (ja2 & jp2 & jn2 & T1 & T2 & T3 & T4 & T5 & T6 & T7 & T8 & T9 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17
        & T18 & T19 & T20 & T21 & T22 & T23 & T24 & T25 & T26 & T27 & T28 & T29 & T30 & T31 & T32 & T33 & T34 & T35 &
        T36 & T37 & T38 & T39 & T40 & T41 & T42).
    rewrite Ems. subst r.
    refine (C_reac_ctrl_identity_replyRet.rrB_tail_lifted B.ProgBridgeData.rsegs_wx_nowrap W md5 ra gp tp s0 s1 s2 s3
      s4 s5 s6 s7 s8 s9 s10 s11
              lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr (ms_mem ms5) fr len pa pp pn S FSc g ja2 jp2 jn2 pos
              y1 y2 y5 y6 y7 y9 y11 y12 y13 y14 y15 y16 y17 y19 y20 y21 y22 y23 y24 y27 y28 y29 y30 y31 Q
              T1 T2 T3 T4 T5 T6 T7 T8 T9 T10 T11 T12 T13 T14 T15 T16 T17 T18 T19 T20 T21 T22 T23 T24 T25 T26 T27 T28
                T29 T30 T31 T32 T33 T34 T35 T36 T37 T38 T39 T40 T41 T42 _).
    intros ms' md' HSCp.
    apply lib.Reusable.YA0n.SRr_ret.
    exact (C_reac_ctrl_identity_replyRet.rrB_ret B LAWS ML ASF FFL STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k
             regs fr len pa pp pn S FSc g pos lyc S2 W (ms_mem ms5) md5 ms' md' P1 P3r HSp P7b P7c P11 HJ5
             (lib.Reusable.YA0n.wle_refl _ W) HAB eq_refl HK3 HSCp).
Qed.
End Top.
