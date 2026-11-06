(* lib/B/Prog/C_reac_ctrl_identity_replySCBase.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the BASE FACTS of
   the shared tail of reac_ctrl_identity_reply (0x848fc), for the cgif-form glue pb_reac_ctrl_identity_reply, on the plan
   of record pb_reac_ctrl_identity_reply.plan.md section 1 (a working note, not in this delivery) (row S-C;
   STATUS row "S-C base facts at mp and the tail's base facts at S-B's -1 end memory").  Owner a Theorem Labs lane.

   rule 24: no function proved here.  Released-proof lookup of record
   (`proof-index reac_ctrl_identity_reply reac_ctrl_identity_reply_contract_F`,
   lookup-reac_ctrl_identity_reply.txt (a working note, not in this delivery), checker CONFIRM in
   lookup-check.md (a working note, not in this delivery)): At ossv/recipes c5e779efe8c (2026-10-31), no released proof outside this unit.  Written new.

   WHAT IS HERE.  The pattern of C_reac_ctrl_identity_replyBase.rrB_SB_base for rrB_SB_lifted, for the two lifted
   entries of the shared tail (C_reac_ctrl_identity_replyRet.v):
     rrB_SC_base    EVERY premise of rrB_SC_lifted except wx_segs_nowrap and the continuation, in its order, at
                    mb := mp (the memory at reac_ctrl_parse's return 0x84a68), W := the world after the call,
                    FS := ly_F lyc, jj := pos;
     rrB_tail_base  EVERY premise of rrB_tail_lifted except wx_segs_nowrap and the continuation, in its order, at
                    mb := the real memory at S-B's -1 end (the epilogue entry 0x84bdc).
   Both come from ONE base: a journal state (lyb, Sb, Wb, mb) that holds the function's class-1 frame (1, pos), whose
   blocks are the entry's, and the entry's kept classes up to it (acall_kept from (W, memc) to (Wb, mb) over the window,
   E = False; the composition builds it from Ret's rrB_K_SA / rrB_K_E1 / rrB_K_SB (/ rrB_K_E2)).  Section Common proves
   the facts of that base (the twin of BaseV's view half and Base's memory half, read off the AR of the base journal
   in place of the class-1 request's post, and off the kept classes in place of S-A's munch + E1's acall_kept); the
   end-specific facts are the 13 saved registers, the flag-pointer word at G + 120, (S-C) parse's 36 bytes and
   reply_args, (tail) the OUT cells: rrB_SBL_mem / rrB_SBR_mem read them off rrB_QSB's two ends, rrB_SC_SV / rrB_SC_FL1
   carry them across reac_ctrl_parse (E2's acall_kept: the window above the call's sp by its first clause, the frame
   (1, pos) by its frame clause, the flag-pointer word lying off parse's output [G + 32, G + 68)).

   SECTION HYPOTHESES (each NAMED with its owner):
     LAWS (AR_laws), TS (CtrlTSyms)  -- the core B bundle (OWNER PENDING: the record core's TfibLib)
     HRTb  the base cut's B.ACtlRtC.ctl_rt_C at (lyb, Sb, mb) (route (C)): the composition supplies it by
           B.ProgWorldCtlRtC.ctl_rt_C_of_AR at the base journal's AR, which takes no ProgWorld statement.  Its parts
           give asan_cells mb, the run's narrowed premise shadow_rw_on (reac_ctrl_identity_reply_shadow_R ..) mb (by
           C_reac_ctrl_identity_replyCover.rrC_R_on) and ro_agree mb (rsc_RT, rsc_RO).
   TLS_APART / BLOCK_APART_FS / CELLS_NOT_C1 are NOT hypotheses here: B.ProgWorldTlsApart.fp_tls_apart and
   B.ProgWorldBlkApart.ctl_block_apart_fs are applied, and the cells' frame class is the spec's P11 conjunct cid <> 1.
   No Axiom, Parameter, Admitted, admit, Abort.  Nothing of image A is Required. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c reac_ctrl_identity_reply_c
  reac_ctrl_identity_reply_c_on reac_ctrl_identity_replyRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require
  YK04 YA0n YG00 YG01 YG0f YG0n YG0d YG0v YG0s YCbq YI00 YI04 YF0m YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr ProgBridge ProgWorld ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldCtlRt ProgWorldAstack ProgWorldShadow ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldVisWin ProgWorldVisHeap ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldTlsApart ProgWorldBlkApart.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds rng_asan C_reac_ctrl_identity_reply
  C_reac_ctrl_identity_replyCover.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_identity_replyE2 C_reac_ctrl_parse.
(* rrB_rd, rrB_rw_present, rrB_rw_cong, rrB_pw_cross, rrB_u64 (Base); rb_* closed arithmetic (BaseV). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_identity_replyBase
  C_reac_ctrl_identity_replyBaseV.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcParse.
Import ListNotations.
Open Scope Z_scope.

(* ---- generic byte-level helpers ---- *)

(* bytes_at transfers between memories that agree, byte by byte, over the range. *)
Lemma rsc_bytes_cong : forall (m m' : word -> option byte) (a : Z) (bs : list byte),
  (forall i, (i < length bs)%nat -> m' (Z_to_bv 64 (a + Z.of_nat i)) = m (Z_to_bv 64 (a + Z.of_nat i))) ->
  lib.Lib.Mem.bytes_at rsegs m a bs -> lib.Lib.Mem.bytes_at rsegs m' a bs.
Proof.
  intros m m' a bs Hc (H0 & H1 & H2). split; [exact H0|]. split; [exact H1|].
  intros i Hi. rewrite <- (H2 i Hi). unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa. rewrite (Hc i Hi). reflexivity.
Qed.

(* Two memories whose views (in two worlds) agree at an address visible in both and present in both hold the same
   byte there. *)
Lemma rsc_mem_of_views : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z),
  lib.Reusable.YG0n.aview rsegs H' m' a = lib.Reusable.YG0n.aview rsegs H m a ->
  H' (Z_to_bv 64 a) = false -> H (Z_to_bv 64 a) = false ->
  (exists b, m' (Z_to_bv 64 a) = Some b) -> (exists b, m (Z_to_bv 64 a) = Some b) ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros H H' m m' a Hv Hh' Hh [b' Hb'] [b Hb].
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
  rewrite Hh, Hh' in Hv. rewrite Hb, Hb' in Hv. cbn [option_map] in Hv.
  injection Hv as Hbb. rewrite Hb, Hb'. f_equal. apply bv_eq. exact Hbb.
Qed.

(* ---- the end-specific facts read off rrB_QSB's two ends (C_reac_ctrl_identity_replyLib.v) ---- *)

(* At reac_ctrl_parse's first slot: rBI's saved registers and flag-pointer word at mc, kept by the 5-byte shadow munch
   into the normalized end memory m5n, and read at the real end memory m5 (mem_rel: above the image they are equal). *)
Lemma rrB_SBL_mem : forall (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb mc m5n m5 : word -> option byte)
    (S FS G j : Z),
  HIGHMEM_BEG <= S - 9072 -> S <= APPMEM_END -> 0 <= G -> G + 128 <= APPMEM_END ->
  (G + 128 <= LOWMEM_END \/ HIGHMEM_BEG <= G) ->
  rBI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb S FS G j 1 mc ->
  lib.Lib.Frame.munch [(G / 8 + ASAN_K + 4, G / 8 + ASAN_K + 9)] mc m5n ->
  B.MemNorm.mem_rel rsegs m5 m5n ->
  lib.Lib.Step.rw_cells rsegs m5 (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  lib.Lib.Mem.bytes_at rsegs m5 (G + 120) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 1 j))).
Proof.
  intros ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb mc m5n m5 S FS G j HHM HAE HG0 HG1 HGb HBI MU REL.
  destruct HBI as (_ & _ & _ & _ & SV & FL).
  destruct (FL eq_refl) as [FL1 _].
  unfold HIGHMEM_BEG, APPMEM_END, LOWMEM_END in *.
  assert (HD : 0 <= G / 8 /\ 8 * (G / 8) <= G) by (split; [apply Z.div_pos | apply Z.mul_div_le]; lia).
  pose proof (Z.div_mod G 8 ltac:(lia)) as HD1. pose proof (Z.mod_pos_bound G 8 ltac:(lia)) as HD2.
  assert (HDu : G / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
  change (2 ^ 47 / 8) with 17592186044416 in HDu.
  split.
  - apply (B.MemNormTr.rw_cells_of_rel m5 m5n); [exact REL|].
    apply (C_reac_ctrl_identity_replyBase.rrB_rw_cong mc m5n (S - 104)); [|exact SV].
    intros i Hi.
    assert (Hcs : Z.of_nat (lib.Lib.Cells.cells_size (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) = 104)
      by (vm_compute; reflexivity).
    rewrite Hcs in Hi. apply MU. cbn [lib.Lib.Frame.outside].
    rewrite (C_reac_ctrl_identity_replyBase.rrB_u64 (S - 104 + i)) by lia.
    unfold ASAN_K. split; [lia | exact I].
  - apply (B.MemNorm.bytes_at_rel rsegs m5 m5n _ _ REL).
    apply (rsc_bytes_cong mc m5n); [|exact FL1].
    intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi.
    apply MU. cbn [lib.Lib.Frame.outside].
    rewrite (C_reac_ctrl_identity_replyBase.rrB_u64 (G + 120 + Z.of_nat i)) by lia.
    unfold ASAN_K. split; [lia | exact I].
Qed.

(* At the -1 exit 0x84bdc: the end memory IS rBI's mc; the saved registers, the flag-pointer word and (rKEG's OUT fact,
   kept by rrB_QSB since 128f44eab50) the OUT cells, read at the real end memory. *)
Lemma rrB_SBR_mem : forall (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (mb mc m5 : word -> option byte)
    (fr len pa pp pn S FS G j : Z) (g : list byte),
  rBI ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb S FS G j 1 mc ->
  (reply_ok fr len pa pp pn g = true -> rOUTF fr pa pp pn g mc) ->
  B.MemNorm.mem_rel rsegs m5 mc ->
  lib.Lib.Step.rw_cells rsegs m5 (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  lib.Lib.Mem.bytes_at rsegs m5 (G + 120) (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FS 1 j))) /\
  (reply_ok fr len pa pp pn g = true -> rOUTF fr pa pp pn g m5).
Proof.
  intros ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mb mc m5 fr len pa pp pn S FS G j g HBI HOUT REL.
  destruct HBI as (_ & _ & _ & _ & SV & FL).
  destruct (FL eq_refl) as [FL1 _].
  split; [exact (B.MemNormTr.rw_cells_of_rel m5 mc _ _ REL SV)|].
  split; [exact (proj2 (B.MemNorm.bytes_at_rel rsegs m5 mc _ _ REL) FL1)|].
  intros HOK. destruct (HOUT HOK) as (Ca & Cp & Cn).
  split; [exact (B.MemNormTr.rw_cells_of_rel m5 mc _ _ REL Ca)|].
  split; [exact (B.MemNormTr.rw_cells_of_rel m5 mc _ _ REL Cp)|].
  exact (B.MemNormTr.rw_cells_of_rel m5 mc _ _ REL Cn).
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
Section Common.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
(* OWNER PENDING: the core B bundle (the record core's TfibLib, lib/Reusable/YCeg.v; its line 25 names a refused name on
   every B base) *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis TS : lib.Reusable.YF0m.CtrlTSyms B.

(* ---- the spec cut at the entry (lib/B/Prog/C_reac_ctrl_identity_reply.v: P1, P4, P5, P7, P9, P10, P11) ---- *)
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : lib.Reusable.YG0f.alayout) (S0 : lib.Reusable.YG00.astate)
  (W0 : lib.Reusable.YA0n.world rsegs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (W : lib.Reusable.YA0n.world rsegs)
  (memc : word -> option byte) (mdc : Model) (k : Z)
  (tp : word) (fr len pa pp pn S : Z) (g : list byte).
Hypothesis P1 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis P4tp : tp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B).
Hypothesis Rfr : 0 <= fr < 2 ^ 64.
Hypothesis Rlen : 0 <= len < 2 ^ 64.
Hypothesis Rpa : 0 <= pa < 2 ^ 64.
Hypothesis Rpp : 0 <= pp < 2 ^ 64.
Hypothesis Rpn : 0 <= pn < 2 ^ 64.
Hypothesis S16 : S mod 16 = 0.
Hypothesis HSlo : sp0 - STK <= S - 9072.
Hypothesis HShi : S <= sp0.
Hypothesis Hg : length g = 50%nat.
Hypothesis P10 : reply_args fr pa pp pn = true -> 50 <= len ->
  (exists nb, In (fr, nb) (lib.Reusable.YG0d.ablocks B lyc Sc) /\ 50 <= lib.Reusable.YG00.req_size nb) /\
  lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc) fr
    (map (fun b : byte => bv_unsigned b) g).
Hypothesis P11 : reply_args fr pa pp pn = true ->
  pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
  (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
  (forall a, C_reac_ctrl_identity_reply.treply_out pa pp pn a ->
     (exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames Sc) /\ cid <> 1 /\
        lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos))) /\
     lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0) (lib.Reusable.YG0d.ablocks B lyc Sc)
       lyc own a) /\
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
    lib.Reusable.YG0f.SHADOW_OFF pa 2 /\
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
    lib.Reusable.YG0f.SHADOW_OFF pp 8 /\
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
    lib.Reusable.YG0f.SHADOW_OFF pn 8.

(* ---- the base: a journal state holding the frame (1, pos), the entry's blocks, the entry's kept classes ---- *)
Variables (pos : Z) (lyb : lib.Reusable.YG0f.alayout) (Sb : lib.Reusable.YG00.astate)
  (Wb : lib.Reusable.YA0n.world rsegs) (mb : word -> option byte) (mdb : Model).
Hypothesis HJb : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyb Sb Wb mb mdb k.
Hypothesis HABb : lib.Reusable.YG0d.ablocks B lyb Sb = lib.Reusable.YG0d.ablocks B lyc Sc.
Hypothesis HKb : lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W memc Wb mb (S - 9072) S (fun _ => False).
(* route (C): the base cut HAS ctl_rt_C at (lyb, Sb, mb); the composition supplies it by
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR at HJb's AR. *)
Hypothesis HRTb : B.ACtlRtC.ctl_rt_C B lyb Sb mb.

Local Notation RGW := (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H Wb)).
Local Notation FSc := (lib.Reusable.YG0f.ly_F lyc).

(* ---- the base's layout, frames, window, side stack ---- *)
Lemma rsc_lay : lib.Reusable.YG0f.ly_F lyb = FSc /\
  lib.Reusable.YG0f.ly_stk_lo lyb = lib.Reusable.YG0f.ly_stk_lo lyc /\
  lib.Reusable.YG0f.ly_stk_hi lyb = lib.Reusable.YG0f.ly_stk_hi lyc.
Proof.
  pose proof P1 as (_ & Hlyc & _). pose proof HJb as (_ & Hlyb & _).
  destruct Hlyc as (_ & _ & _ & _ & _ & Fc & _ & _ & _ & Lc & Hc & _).
  destruct Hlyb as (_ & _ & _ & _ & _ & Fb & _ & _ & _ & Lb & Hb & _).
  rewrite Fb, Fc, Lb, Lc, Hb, Hc. split; [reflexivity|]. split; reflexivity.
Qed.

Lemma rsc_fa : forall c q, lib.Reusable.YG0f.frame_addr lyb c q = lib.Reusable.YG0f.frame_addr lyc c q.
Proof. intros c q. unfold lib.Reusable.YG0f.frame_addr. rewrite (proj1 rsc_lay). reflexivity. Qed.

Lemma rsc_fla : forall c q, lib.Reusable.YG0f.flag_addr lyb c q = lib.Reusable.YG0f.flag_addr lyc c q.
Proof. intros c q. unfold lib.Reusable.YG0f.flag_addr. rewrite (proj1 rsc_lay). reflexivity. Qed.

Lemma rsc_frb : lib.Reusable.YG01.frames Sb = (1, pos) :: lib.Reusable.YG01.frames Sc.
Proof.
  pose proof P1 as (_ & _ & _ & _ & _ & Fc & _). pose proof HJb as (_ & _ & _ & _ & _ & Fb & _).
  rewrite Fb, Fc. reflexivity.
Qed.

(* the window [S - 9072, S): inside the stack, above the allocation ceiling, present at mb in Wb (the base journal's
   presence and astk_ok conjuncts, YCbq.v:368-369, and layout_ok's lo_stk_ceil) *)
Lemma rsc_win :
  lib.Reusable.YG0f.ly_stk_lo lyb <= S - 9072 /\ S <= lib.Reusable.YG0f.ly_stk_hi lyb /\
  lib.Reusable.YG0f.ASAN_CEIL <= S - 9072 /\ S <= 140737488355328 /\
  (forall a, S - 9072 <= a < S -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H Wb) mb a).
Proof.
  pose proof HJb as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  pose proof HAR as (HM & _).
  pose proof (lib.Reusable.YG0f.lo_stk_ceil _ (lib.Reusable.YG0n.am_layout _ _ _ _ HM)) as Hc.
  change (2 ^ 47) with 140737488355328 in H47.
  rewrite Elo in Hc. rewrite Elo, Ehi.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros a Ha. apply Hpres. lia.
Qed.

(* the side stack: above the image, page-aligned and below the allocation ceiling *)
Lemma rsc_F : ASAN_GT <= FSc /\ FSc mod 4096 = 0 /\ FSc + lib.Reusable.YG0f.kFakeStackSize <= lib.Reusable.YG0f.ASAN_CEIL.
Proof.
  rewrite <- (proj1 rsc_lay).
  pose proof HJb as (HAR & _).
  pose proof (B.ProgWorld_Fs.pw_F_above B lyb Sb Wb mb mdb HAR) as HGT.
  pose proof HAR as (HM & _). pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ HM) as LO.
  pose proof (lib.Reusable.YG0f.lo_F_al _ LO) as Hal. unfold lib.Reusable.YG0f.page_aligned in Hal.
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO)
                (lib.Reusable.YG0f.ly_F lyb, lib.Reusable.YG0f.kFakeStackSize)
                ltac:(unfold lib.Reusable.YG0f.owned_extents; right; right; right; left; reflexivity)) as F1.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_in_app_ceil _ _ F1) as [_ F2]. cbn [fst snd] in F2.
  split; [exact HGT|]. split; [exact Hal | exact F2].
Qed.

Lemma rsc_tp : bv_unsigned tp = RT_TP.
Proof. rewrite P4tp, (B.ProgWorld.as_tp_RT_TP B TS). vm_compute. reflexivity. Qed.

(* ---- one byte of the three caller cells ---- *)
(* P11 puts it in a live frame (cid, q) of Sc with cid <> 1; that frame is a frame of the base (frames Sb =
   (1, pos) :: frames Sc), so AR_frames_law at the base gives its and its shadow byte's visibility in Wb; the kept
   classes' frame-shadow clause (YCbq.v:831-833, E = False) give that shadow byte's view at mb as at memc. *)
Lemma rsc_cell : reply_args fr pa pp pn = true -> forall a, C_reac_ctrl_identity_reply.treply_out pa pp pn a ->
  FSc + 36864 <= a < FSc + lib.Reusable.YG0f.kFakeStackSize /\
  (a < FSc + 1085440 \/ FSc + 2134016 <= a) /\
  4096 <= a /\
  (a < lib.Reusable.YG0f.kLowShadowBeg \/ (lib.Reusable.YG0f.kHighMemBeg <= a /\ a < lib.Reusable.YG0f.ASAN_CEIL)) /\
  lib.Reusable.YA0n.w_H Wb (Z_to_bv 64 a) = false /\
  lib.Reusable.YA0n.w_H Wb (Z_to_bv 64 (a / 8 + ASAN_K)) = false /\
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H Wb) mb (a / 8 + ASAN_K) =
    lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc (a / 8 + ASAN_K).
Proof.
  intros RA a Ha.
  destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & Hcells & _).
  destruct (Hcells a Ha) as ((cid & q & Hin & Hc1 & Hr) & _).
  pose proof P1 as (HARc & _). pose proof HJb as (HARb & _).
  assert (Hinb : In (cid, q) (lib.Reusable.YG01.frames Sb)) by (rewrite rsc_frb; right; exact Hin).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc Sc W memc mdc cid q HARc Hin) as (Hal & Happ & _ & _).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyb Sb Wb mb mdb cid q HARb Hinb) as (_ & _ & Hby & Hsh).
  rewrite rsc_fa in Hby, Hsh.
  pose proof HARc as (HM & _).
  pose proof (lib.Reusable.YG0n.am_wf _ _ _ _ HM) as HWf.
  pose proof (lib.Reusable.YG01.wfs_live _ (lib.Reusable.YG01.wf_fakestack _ _ _ _ _ HWf)) as Hlive.
  pose proof (proj1 (Forall_forall _ _) Hlive (cid, q) Hin) as Hpos. cbn [fst snd] in Hpos.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_frame_geom lyc cid q (proj1 Hpos) (proj2 Hpos)) as (G1 & G2 & G3 & G4).
  unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr. cbn [fst snd] in Hr.
  pose proof (lib.Reusable.YG0f.in_app_addr _ _ a Happ Hr) as Hap. unfold lib.Reusable.YG0f.app_addr in Hap.
  destruct rsc_win as (_ & _ & Hceil & H47 & _).
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  set (F := lib.Reusable.YG0f.frame_addr lyc cid q) in *.
  set (sz := lib.Reusable.YG00.fs_frame_bytes cid) in *.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF.
  pose proof (Z.div_mod F 32 ltac:(lia)) as DF32.
  pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds.
  assert (HF8 : F mod 8 = 0) by lia.
  assert (Hi : 0 <= a / 8 - F / 8 < sz / 8) by lia.
  split; [unfold lib.Reusable.YG0f.kFakeStackSize; lia|].
  split; [lia|].
  split; [lia|].
  split; [exact (proj2 Hap)|].
  split; [exact (proj1 (proj1 (Hby a Hr)))|].
  split.
  { destruct (Hsh (a / 8 - F / 8) Hi) as [[Hv _] _].
    replace (lib.Reusable.YG0f.shadow_addr F + (a / 8 - F / 8)) with (a / 8 + ASAN_K) in Hv
      by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, ASAN_K; lia).
    exact Hv. }
  pose proof HKb as (_ & _ & _ & K4 & _).
  assert (Hsa : lib.Reusable.YG0n.in_zr (a / 8 + ASAN_K) (lib.Reusable.YG0f.shadow_addr F, sz / 8)).
  { unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, ASAN_K.
    cbn [fst snd]. lia. }
  exact (K4 cid q (a / 8 + ASAN_K) Hin (or_intror Hsa) (fun H => H)).
Qed.

(* a cell [p, p + n) (n <= 8): its first and last byte give the cell's place *)
Lemma rsc_cell_ivl : reply_args fr pa pp pn = true -> forall p n, 1 <= n <= 8 ->
  (forall x, p <= x < p + n -> C_reac_ctrl_identity_reply.treply_out pa pp pn x) ->
  FSc + 36864 <= p /\ p + n <= FSc + lib.Reusable.YG0f.kFakeStackSize /\
  (p + n <= FSc + 1085440 \/ FSc + 2134016 <= p) /\ 4096 <= p /\
  (p + n <= lib.Reusable.YG0f.kLowShadowBeg \/
   (lib.Reusable.YG0f.kHighMemBeg <= p /\ p + n <= lib.Reusable.YG0f.ASAN_CEIL)).
Proof.
  intros RA p n Hn Hc.
  destruct (rsc_cell RA p (Hc p ltac:(lia))) as ((A0 & A1) & A2 & A3 & A4 & _).
  destruct (rsc_cell RA (p + n - 1) (Hc (p + n - 1) ltac:(lia))) as ((B0 & B1) & B2 & B3 & B4 & _).
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* a cell is addressable at mb: P11's shadow at memc, kept (rsc_cell) *)
Lemma rsc_addr_cell : reply_args fr pa pp pn = true -> forall p n, 1 <= n <= 8 ->
  (forall x, p <= x < p + n -> C_reac_ctrl_identity_reply.treply_out pa pp pn x) ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
    lib.Reusable.YG0f.SHADOW_OFF p n ->
  addressable mb p n.
Proof.
  intros RA p n Hn Hc HRA.
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  destruct (rsc_cell_ivl RA p n Hn Hc) as (_ & _ & _ & L3 & L4).
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in L4.
  unfold addressable. split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
  intros i Hi.
  destruct (rsc_cell RA (p + i) (Hc (p + i) ltac:(lia))) as (_ & _ & A0 & A1 & _ & _ & E).
  destruct (HRA (p + i) ltac:(lia)) as (s & Hs & Hok).
  unfold lib.Reusable.YG0v.shadow_of_addr in Hs.
  replace (lib.Reusable.YG0f.SHADOW_OFF + (p + i) / 8) with ((p + i) / 8 + ASAN_K) in Hs
    by (unfold lib.Reusable.YG0f.SHADOW_OFF, ASAN_K; lia).
  rewrite <- E in Hs.
  destruct (B.ProgWorld_Fs.pw_view_mrd Wb mb _ _ Hs) as [_ Hm].
  unfold lib.Reusable.YG0v.saddr_ok in Hok.
  pose proof (Z.mod_pos_bound (p + i) 8 ltac:(lia)) as Mi.
  assert (Hs8 : 0 <= s < 8) by lia.
  unfold addr_byte. split.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END.
    unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in A1. lia.
  - exists (Z_to_bv 8 s). split; [exact Hm|].
    rewrite (C_reac_ctrl_identity_replyBaseV.rb_bv_signed8 s Hs8). unfold shadow_ok. lia.
Qed.

Lemma rsc_cell_vis : reply_args fr pa pp pn = true -> forall p n, 1 <= n <= 8 ->
  (forall x, p <= x < p + n -> C_reac_ctrl_identity_reply.treply_out pa pp pn x) ->
  lib.Lib.ExecF.rng RGW p n /\ shcov RGW p n.
Proof.
  intros RA p n Hn Hc.
  destruct (rsc_cell_ivl RA p n Hn Hc) as (_ & _ & _ & L3 & L4).
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in L4.
  split.
  - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. destruct (rsc_cell RA a (Hc a Ha)) as (_ & _ & _ & _ & V & _). exact V.
  - intros x Hx. destruct (rsc_cell RA x (Hc x Hx)) as (_ & _ & X3 & X4 & _ & V & _).
    unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in X4.
    destruct (C_reac_ctrl_identity_replyBaseV.rb_sh_bound x ltac:(lia)) as [B0 B1].
    exact (C_reac_ctrl_identity_replyBaseV.rb_rng1 _ _ B0 B1 V).
Qed.

(* ---- the message (a heap block of Sc, P10; a block of the base by HABb) ---- *)
Lemma rsc_heap : reply_args fr pa pp pn = true -> 50 <= len ->
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H Wb) fr 50 /\
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H Wb) (B.Prog.rng_asan.sh_al8_lo fr)
    (B.Prog.rng_asan.sh_al8_hi fr 50 - B.Prog.rng_asan.sh_al8_lo fr).
Proof.
  intros RA HL. destruct (P10 RA HL) as ((nb & Hin & Hnb) & _).
  pose proof HJb as (HARb & _).
  assert (Hinb : In (fr, nb) (lib.Reusable.YG0d.ablocks B lyb Sb)) by (rewrite HABb; exact Hin).
  split.
  - exact (B.ProgWorldVisHeap.heap_vis B LAWS lyb Sb Wb mb mdb fr nb fr 50 HARb Hinb ltac:(lia) ltac:(lia)).
  - destruct (B.ProgWorldVisHeap.heap_sh_vis B LAWS lyb Sb Wb mb mdb fr nb fr 50 HARb Hinb ltac:(lia) ltac:(lia)
                ltac:(lia)) as [E | V]; [lia | exact V].
Qed.

Lemma rsc_SCF : reply_args fr pa pp pn = true -> 50 <= len -> shcov RGW fr 50.
Proof.
  intros RA HL x Hx. apply B.ProgBridge.rng_of_visible.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_sh_al8_in fr 50 x Hx) as [A1 A2].
  apply (B.ProgBridge.range_visible_sub _ _ _ _ _ (proj2 (rsc_heap RA HL)) A1); lia.
Qed.

Lemma rsc_SKF : reply_args fr pa pp pn = true -> 50 <= len -> shkov RGW fr 50.
Proof.
  intros RA HL a b H1 H2 H3. apply B.ProgBridge.rng_of_visible.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_sh_al8_kov fr 50 a b H1 H2 H3) as (A1 & A2 & A3).
  apply (B.ProgBridge.range_visible_sub _ _ _ _ _ (proj2 (rsc_heap RA HL)) A1 A2); lia.
Qed.

Lemma rsc_AFfr : reply_args fr pa pp pn = true -> 50 <= len -> addressable mb fr 50.
Proof.
  intros RA HL. destruct (P10 RA HL) as ((nb & Hin & Hnb) & _). pose proof HJb as (HAR & _).
  apply (B.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS lyb Sb Wb mb mdb fr nb fr 50 HAR);
    [rewrite HABb; exact Hin | lia | lia | lia].
Qed.

(* ---- the window ---- *)
Lemma rsc_RWIN : lib.Lib.ExecF.rng RGW (S - 9072) 9072.
Proof.
  destruct rsc_win as (_ & _ & Hc & H47 & Hp). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 _] _].
  apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
  intros a Ha. exact (proj1 (Hp a ltac:(lia))).
Qed.

Lemma rsc_SCW : shcov RGW (S - 9072) 9072.
Proof.
  pose proof HJb as (HAR & _). destruct rsc_win as (Hlo & Hhi & _).
  destruct (B.ProgWorldVisWin.win_sh_vis B LAWS lyb Sb Wb mb mdb (S - 9072) 9072 HAR Hlo ltac:(lia) ltac:(lia))
    as [E0 | HV]; [lia|].
  intros x Hx. apply B.ProgBridge.rng_of_visible.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_sh_al8_in (S - 9072) 9072 x Hx) as [A1 A2].
  apply (B.ProgBridge.range_visible_sub _ _ _ _ _ HV A1); lia.
Qed.

Lemma rsc_AW : addressable mb (S - 9072) 9072.
Proof.
  pose proof HJb as (HAR & _). destruct rsc_win as (Hlo & Hhi & _).
  exact (B.ProgWorldShadow.ctl_stack_shadow_of_AR B LAWS lyb Sb Wb mb mdb (S - 9072) 9072 HAR Hlo ltac:(lia)
           ltac:(lia)).
Qed.

Lemma rsc_ST : lib.Lib.Frame.stk rsegs mb (S - 9072) S.
Proof.
  destruct rsc_win as (_ & _ & Hc & H47 & Hp). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 _] _].
  apply (B.ProgWorldAstack.pwfs_stk_of_present Wb mb (S - 9072) S); [lia | lia | exact Hp].
Qed.

(* the runtime cells and the run's narrowed shadow premise at mb (route (C)): the base cut's ctl_rt_C HRTb, its
   asan_cells part and, by C_reac_ctrl_identity_replyCover.rrC_R_on, its cut_shadow / img_shadow parts (the own real
   frame and the parse frames and real-arm record by (Z), the class-1 block and side-arm record by the frames area, fr
   under reply_args by (L) with P10's block, a block of the base by HABb, BC by img_shadow). *)
Lemma rsc_RT : asan_cells mb /\ shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FSc) mb.
Proof.
  destruct HRTb as (AC & Hcut & Himg & _).
  split; [exact AC|].
  pose proof HJb as (HAR & _). pose proof HAR as (HM & _).
  destruct rsc_win as (Hlo & Hhi & _).
  rewrite <- (proj1 rsc_lay).
  apply (C_reac_ctrl_identity_replyCover.rrC_R_on B lyb Sb fr len pa pp pn S mb
           (lib.Reusable.YG0n.am_layout _ _ _ _ HM) Hlo Hhi); [|exact Hcut | exact Himg].
  intros RA HL. destruct (P10 RA HL) as ((nb & Hin & Hnb) & _). exists nb. rewrite HABb. exact (conj Hin Hnb).
Qed.

(* ---- the class-1 frames of the side stack, their flags and their shadow (am_areas, YG0n.v:137-139) ---- *)
Lemma rsc_fs_vis : forall a, FSc <= a < FSc + lib.Reusable.YG0f.kFakeStackSize ->
  lib.Reusable.YA0n.w_H Wb (Z_to_bv 64 a) = false.
Proof.
  intros a Ha. pose proof HJb as (HAR & _). rewrite <- (proj1 rsc_lay) in Ha.
  exact (proj1 (B.ProgWorld_Fs.pw_F_present B lyb Sb Wb mb mdb a HAR Ha)).
Qed.

Lemma rsc_fs_sh_vis : forall x, FSc + lib.Reusable.YG0f.kFakeFramesOff <= x < FSc + lib.Reusable.YG0f.kFakeStackSize ->
  lib.Reusable.YA0n.w_H Wb (Z_to_bv 64 (x / 8 + ASAN_K)) = false.
Proof.
  intros x Hx. pose proof HJb as (HAR & _). pose proof HAR as (HM & _).
  destruct rsc_F as (_ & HFal & _).
  pose proof (proj1 rsc_lay) as EF.
  assert (Hi : 0 <= x / 8 - (FSc + lib.Reusable.YG0f.kFakeFramesOff) / 8 <
               (lib.Reusable.YG0f.kFakeStackSize - lib.Reusable.YG0f.kFakeFramesOff) / 8).
  { change ((lib.Reusable.YG0f.kFakeStackSize - lib.Reusable.YG0f.kFakeFramesOff) / 8) with 1441792.
    unfold lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize in Hx |- *.
    pose proof (Z.div_mod x 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as R1.
    pose proof (Z.div_mod (FSc + (4096 + 32768)) 8 ltac:(lia)) as D2.
    pose proof (Z.mod_pos_bound (FSc + (4096 + 32768)) 8 ltac:(lia)) as R2.
    pose proof (Z.div_mod FSc 4096 ltac:(lia)) as D3.
    lia. }
  pose proof (lib.Reusable.YG0n.am_areas _ _ _ _ HM) as AA. unfold lib.Reusable.YG0n.aareas in AA.
  apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA]. apply Forall_app in AA as [_ AA].
  do 5 (apply Forall_cons_iff in AA as [_ AA]). apply Forall_cons_iff in AA as [AS _].
  rewrite <- EF in Hi.
  specialize (AS _ Hi). cbn [fst lib.Reusable.YG0f.aeval] in AS.
  pose proof (B.ProgWorldVisFrame.vis_of_aview _ Wb mb _ AS) as V.
  replace (lib.Reusable.YG0f.shadow_addr (lib.Reusable.YG0f.ly_F lyb + lib.Reusable.YG0f.kFakeFramesOff) +
           (x / 8 - (lib.Reusable.YG0f.ly_F lyb + lib.Reusable.YG0f.kFakeFramesOff) / 8)) with (x / 8 + ASAN_K) in V
    by (rewrite EF; unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, ASAN_K; lia).
  exact V.
Qed.

Lemma rsc_RFLG : lib.Lib.ExecF.rng RGW (fs_flag FSc 1 0) (fs_M 1).
Proof.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_fs1 FSc) as (_ & _ & _ & E4 & E5 & _). rewrite E4, E5.
  destruct rsc_F as (HGT & _ & HFc). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  unfold ASAN_GT, lib.Reusable.YG0f.kFakeStackSize in *.
  apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
  intros a Ha. apply rsc_fs_vis. unfold lib.Reusable.YG0f.kFakeStackSize. lia.
Qed.

Lemma rsc_RFRM : lib.Lib.ExecF.rng RGW (fs_frame FSc 1 0) (fs_frame FSc 1 (fs_M 1) - fs_frame FSc 1 0).
Proof.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_fs1 FSc) as (E1 & E2 & _). rewrite E1, E2.
  destruct rsc_F as (HGT & _ & HFc). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  unfold ASAN_GT, lib.Reusable.YG0f.kFakeStackSize in *.
  apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
  intros a Ha. apply rsc_fs_vis. unfold lib.Reusable.YG0f.kFakeStackSize. lia.
Qed.

Lemma rsc_SCFM : shcov RGW (fs_frame FSc 1 0) (fs_frame FSc 1 (fs_M 1) - fs_frame FSc 1 0).
Proof.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_fs1 FSc) as (E1 & E2 & _). rewrite E1, E2.
  destruct rsc_F as (HGT & _ & HFc). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  unfold ASAN_GT, lib.Reusable.YG0f.kFakeStackSize in *.
  intros x Hx.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_sh_bound x ltac:(lia)) as [B0 B1].
  apply (C_reac_ctrl_identity_replyBaseV.rb_rng1 _ _ B0 B1). apply rsc_fs_sh_vis.
  unfold lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize. lia.
Qed.

(* the frame (1, pos): its slot index, and its flag byte reads 1 (AR's fs_flags_ok at Sb, where (1, pos) is live) *)
Lemma rsc_jj : 0 <= pos < fs_M 1.
Proof.
  pose proof HJb as (HARb & _). pose proof HARb as (M & _).
  assert (Hin : In (1, pos) (lib.Reusable.YG01.frames Sb)) by (rewrite rsc_frb; left; reflexivity).
  destruct (lib.Reusable.YG0s.frame_facts B lyb Sb _ 1 pos M Hin) as (_ & Hpos & _).
  change (lib.Reusable.YG00.fs_frames 1) with 8192 in Hpos. change (fs_M 1) with 8192. exact Hpos.
Qed.

Lemma rsc_fl_eq : fs_flag FSc 1 pos = lib.Reusable.YG0f.flag_addr lyc 1 pos.
Proof.
  pose proof (B.ProgWorld.ctl_fs_geom FSc 1 pos ltac:(lia)) as (_ & _ & _ & EFl & _).
  change (Z.to_nat 1) with 1%nat in EFl. rewrite EFl. reflexivity.
Qed.

Lemma rsc_fr_eq : fs_frame FSc 1 pos = lib.Reusable.YG0f.frame_addr lyc 1 pos.
Proof.
  pose proof (B.ProgWorld.ctl_fs_geom FSc 1 pos ltac:(lia)) as (_ & _ & EGf & _).
  change (Z.to_nat 1) with 1%nat in EGf. rewrite EGf. reflexivity.
Qed.

Lemma rsc_FL2 : lib.Lib.Mem.bytes_at rsegs mb (fs_flag FSc 1 pos) [Z_to_bv 8 1].
Proof.
  pose proof HJb as (HARb & _). pose proof HARb as (M & _).
  pose proof rsc_jj as Hjj. change (fs_M 1) with 8192 in Hjj.
  assert (Hfl : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H Wb) mb (lib.Reusable.YG0f.flag_addr lyb 1 pos)
                = Some 1).
  { assert (Hpos : 0 <= pos < lib.Reusable.YG00.fs_frames 1)
      by (change (lib.Reusable.YG00.fs_frames 1) with 8192; lia).
    pose proof (lib.Reusable.YG0n.am_flags _ _ _ _ M 1 pos ltac:(lia) Hpos) as Hf.
    rewrite rsc_frb in Hf. cbn [lib.Reusable.YG00.mem_pos] in Hf. rewrite !Z.eqb_refl in Hf. exact Hf. }
  rewrite rsc_fla, <- rsc_fl_eq in Hfl.
  destruct rsc_F as (HGT & _ & HFc). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  destruct (C_reac_ctrl_identity_replyBaseV.rb_fs1 FSc) as (_ & _ & _ & E4 & _).
  assert (EFL : fs_flag FSc 1 pos = FSc + 20480 + pos)
    by (unfold fs_flag; change (Z.of_nat 1) with 1; change (2 ^ 15) with 32768;
        change (2 ^ (15 - 1)) with 16384; lia).
  unfold ASAN_GT, lib.Reusable.YG0f.kFakeStackSize in *.
  apply (B.ProgWorldAstack.pwfs_byte_of_view Wb mb _ 1 Hfl); lia.
Qed.

(* ---- the side-stack bundle fp [1%nat] mb .. (ctl_fp_of_AR at the base) and the thread cells' apartness ---- *)
Lemma rsc_fp : fp [1%nat] mb (bv_unsigned tp) FSc (S - 9072) S
    (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn).
Proof.
  rewrite rsc_tp.
  pose proof (proj1 rsc_lay) as EF.
  pose proof HJb as (HAR & _). pose proof HAR as (HM & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ HM) as LO.
  destruct rsc_win as (Hlo & Hhi & Hceil & H47 & _).
  destruct rsc_F as (HGT & HFal & HFc).
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  pose proof (lib.Reusable.YG0f.lo_app _ LO) as LA. rewrite Forall_forall in LA.
  destruct (C_reac_ctrl_identity_replyBaseV.rb_in_app_ceil _ _ (LA (lib.Reusable.YG0f.ly_T lyb,
      lib.Reusable.YG0f.kThreadObjSize)
      ltac:(unfold lib.Reusable.YG0f.owned_extents; right; right; left; reflexivity))) as (T0 & T1).
  destruct (C_reac_ctrl_identity_replyBaseV.rb_in_app_ceil _ _ (LA (lib.Reusable.YG0f.ly_C lyb, 256)
      ltac:(unfold lib.Reusable.YG0f.owned_extents; do 6 right; left; reflexivity))) as (Cc0 & Cc1).
  destruct (C_reac_ctrl_identity_replyBaseV.rb_in_app_ceil _ _ (LA (lib.Reusable.YG0f.ly_D lyb, 4096)
      ltac:(unfold lib.Reusable.YG0f.owned_extents; do 7 right; left; reflexivity))) as (D0 & D1).
  cbn [fst snd] in T0, T1, Cc0, Cc1, D0, D1.
  pose proof (lib.Reusable.YG0f.lo_disj _ LO) as LD.
  unfold lib.Reusable.YG0f.static_extents, lib.Reusable.YG0f.owned_extents in LD.
  cbn [app lib.Reusable.YG0f.pairwise] in LD.
  destruct LD as (_ & _ & LT & LF & _).
  apply Forall_cons_iff in LT as [DTF _].
  apply Forall_cons_iff in LF as [_ LF]. apply Forall_cons_iff in LF as [_ LF].
  apply Forall_cons_iff in LF as [DFC LF]. apply Forall_cons_iff in LF as [DFD _].
  unfold lib.Reusable.YG0f.zdisjoint in DTF, DFC, DFD. cbn [fst snd] in DTF, DFC, DFD.
  rewrite EF in DTF, DFC, DFD.
  assert (ETP32 : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32) by (vm_compute; reflexivity).
  assert (Etsd : bv_unsigned (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd lyb)) = 0x5fd9f8).
  { rewrite (lib.Reusable.YG0n.am_tsd _ _ _ _ HM), (B.ProgWorld.as_tsd_TSD B TS). vm_compute. reflexivity. }
  assert (EC : bv_unsigned (Z_to_bv 64 (lib.Reusable.YG0f.ly_C lyb)) = lib.Reusable.YG0f.ly_C lyb)
    by (apply B.ProgWorld_Fs.pw_u64; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 (lib.Reusable.YG0f.ly_T lyb)) = lib.Reusable.YG0f.ly_T lyb)
    by (apply B.ProgWorld_Fs.pw_u64; unfold lib.Reusable.YG0f.kThreadObjSize in T1; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (lib.Reusable.YG0f.ly_D lyb)) = lib.Reusable.YG0f.ly_D lyb)
    by (apply B.ProgWorld_Fs.pw_u64; lia).
  destruct (C_reac_ctrl_identity_replyBaseV.rb_fs1 FSc) as (E1 & E2 & E3 & E4 & E5 & E6).
  unfold ASAN_GT in HGT. unfold lib.Reusable.YG0f.kFakeStackSize in HFc, DFC, DFD, DTF.
  unfold lib.Reusable.YG0f.kThreadObjSize in T1, DTF.
  rewrite <- EF.
  apply (B.ProgWorld_Fs.ctl_fp_of_AR B TS LAWS lyb Sb Wb mb mdb [1%nat] (S - 9072) S
           (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) HAR).
  - repeat constructor.
  - rewrite EF. unfold FS_SIZE. lia.
  - intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - (* the writes W (window, cells) apart from the thread cells and the side stack's header *)
    unfold fp_dj, fp_tls, reac_ctrl_identity_reply_W, REAC_CTRL_IDENTITY_REPLY_K.
    rewrite ETP32, Etsd, EC, ET, ED, EF, E6.
    assert (CF : reply_args fr pa pp pn = true ->
      (FSc + 36864 <= pa /\ pa + 2 <= FSc + 11571200) /\ (FSc + 36864 <= pp /\ pp + 8 <= FSc + 11571200) /\
      (FSc + 36864 <= pn /\ pn + 8 <= FSc + 11571200)).
    { intros RA.
      destruct (rsc_cell_ivl RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)) as (Pa0 & Pa1 & _).
      destruct (rsc_cell_ivl RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))) as (Pp0 & Pp1 & _).
      destruct (rsc_cell_ivl RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))) as (Pn0 & Pn1 & _).
      unfold lib.Reusable.YG0f.kFakeStackSize in Pa1, Pp1, Pn1. lia. }
    destruct (reply_args fr pa pp pn).
    + destruct (CF eq_refl) as ((Pa0 & Pa1) & (Pp0 & Pp1) & (Pn0 & Pn1)).
      clear - Pa0 Pa1 Pp0 Pp1 Pn0 Pn1 HGT HFc Hceil C0 C1 T0 T1 Cc0 Cc1 D0 D1 DTF DFC DFD.
      rewrite Forall_forall. intros w Hw. cbv beta. rewrite Forall_forall. intros d Hd. cbv beta.
      cbn [In app] in Hw, Hd.
      destruct Hw as [<- | [<- | [<- | [<- | []]]]];
        repeat (destruct Hd as [<- | Hd];
                [unfold lib.Prog.RcLay.ly_dj, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF,
                   GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF, RT_TP; cbn [fst snd]; lia |]);
        destruct Hd.
    + clear - HGT HFc Hceil C0 C1 T0 T1 Cc0 Cc1 D0 D1. rewrite Forall_forall. intros w Hw. cbv beta.
      rewrite Forall_forall. intros d Hd. cbv beta.
      cbn [In app] in Hw, Hd.
      destruct Hw as [<- | []];
        repeat (destruct Hd as [<- | Hd];
                [unfold lib.Prog.RcLay.ly_dj, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF,
                   GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF, RT_TP; cbn [fst snd]; lia |]);
        destruct Hd.
  - (* the data ranges D (message, cells) apart from the class-1 side-stack bytes *)
    rewrite EF.
    unfold fp_dj, reac_ctrl_identity_reply_D, fp_w, fp_w1. cbn [flat_map app].
    rewrite E1, E2, E3, E4, E5.
    destruct (C_reac_ctrl_identity_replyBaseV.rb_shb FSc ltac:(lia) ltac:(lia)) as [SH0 SH1].
    assert (MSG : reply_args fr pa pp pn = true -> 50 <= len -> exists rs, 50 <= rs /\
      (fr + rs <= FSc \/ FSc + 11571200 <= fr) /\ 4096 <= fr /\
      (fr + rs <= 0x7fff7000 \/ (0x10007fff8000 <= fr /\ fr + rs <= lib.Reusable.YG0f.ASAN_CEIL))).
    { intros RA HL. destruct (P10 RA HL) as ((nb & Hin & Hnb) & _).
      pose proof P1 as (HARc & _).
      pose proof (B.ProgWorldBlkApart.ctl_block_apart_fs B LAWS lyc Sc W memc mdc fr nb HARc Hin) as BA.
      destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc W memc mdc fr nb HARc Hin) as (_ & _ & _ & Happ & _).
      unfold lib.Reusable.YG0f.in_app, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in Happ.
      unfold lib.Reusable.YG0f.kFakeStackSize in BA.
      exists (lib.Reusable.YG00.req_size nb). split; [exact Hnb|]. split; [exact BA | exact Happ]. }
    assert (CEL : reply_args fr pa pp pn = true ->
      (FSc + 36864 <= pa /\ (pa + 2 <= FSc + 1085440 \/ FSc + 2134016 <= pa) /\
       (pa + 2 <= 0x7fff7000 \/ (0x10007fff8000 <= pa /\ pa + 2 <= lib.Reusable.YG0f.ASAN_CEIL))) /\
      (FSc + 36864 <= pp /\ (pp + 8 <= FSc + 1085440 \/ FSc + 2134016 <= pp) /\
       (pp + 8 <= 0x7fff7000 \/ (0x10007fff8000 <= pp /\ pp + 8 <= lib.Reusable.YG0f.ASAN_CEIL))) /\
      (FSc + 36864 <= pn /\ (pn + 8 <= FSc + 1085440 \/ FSc + 2134016 <= pn) /\
       (pn + 8 <= 0x7fff7000 \/ (0x10007fff8000 <= pn /\ pn + 8 <= lib.Reusable.YG0f.ASAN_CEIL)))).
    { intros RA.
      destruct (rsc_cell_ivl RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)) as (A0 & _ & A2 & _ & A4).
      destruct (rsc_cell_ivl RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))) as (B0 & _ & B2 & _ & B4).
      destruct (rsc_cell_ivl RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))) as (N0 & _ & N2 & _ & N4).
      unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in A4, B4, N4.
      split; [split; [exact A0 | split; [exact A2 | exact A4]]|].
      split; [split; [exact B0 | split; [exact B2 | exact B4]] | split; [exact N0 | split; [exact N2 | exact N4]]]. }
    destruct (reply_args fr pa pp pn); [|constructor].
    specialize (CEL eq_refl). specialize (MSG eq_refl).
    rewrite Forall_forall. intros w Hw. cbv beta. rewrite Forall_forall. intros d Hd. cbv beta.
    cbn [In] in Hd.
    apply in_app_or in Hw. destruct Hw as [Hw | Hw].
    + clear CEL. destruct (len <? 50) eqn:HL; cbn [In] in Hw; [destruct Hw|].
      apply Z.ltb_ge in HL. destruct Hw as [<- | []].
      destruct (MSG HL) as (rs & R0 & R1 & R2 & R3). clear - R0 R1 R2 R3 SH0 SH1 HFc HGT C0 C1 Hd.
      repeat (destruct Hd as [<- | Hd]; [unfold lib.Prog.RcLay.ly_dj; cbn [fst snd]; lia |]); destruct Hd.
    + clear MSG. destruct CEL as ((A0 & A2 & A4) & (B0 & B2 & B4) & (N0 & N2 & N4)).
      cbn [In] in Hw. destruct Hw as [<- | [<- | [<- | []]]].
      * clear - A0 A2 A4 SH0 SH1 HFc HGT C0 C1 Hd.
        repeat (destruct Hd as [<- | Hd]; [unfold lib.Prog.RcLay.ly_dj; cbn [fst snd]; lia |]); destruct Hd.
      * clear - B0 B2 B4 SH0 SH1 HFc HGT C0 C1 Hd.
        repeat (destruct Hd as [<- | Hd]; [unfold lib.Prog.RcLay.ly_dj; cbn [fst snd]; lia |]); destruct Hd.
      * clear - N0 N2 N4 SH0 SH1 HFc HGT C0 C1 Hd.
        repeat (destruct Hd as [<- | Hd]; [unfold lib.Prog.RcLay.ly_dj; cbn [fst snd]; lia |]); destruct Hd.
Qed.

Lemma rsc_tls : reac_ctrl_identity_reply_tls mb (bv_unsigned tp) FSc (S - 9072) S.
Proof.
  rewrite rsc_tp, <- (proj1 rsc_lay). pose proof HJb as (HAR & _). destruct rsc_win as (Hlo & Hhi & _).
  intros DT TS0 C T DB kk Hc.
  exact (B.ProgWorldTlsApart.fp_tls_apart B TS LAWS lyb Sb Wb mb mdb [1%nat] (S - 9072) S HAR
           ltac:(repeat constructor) Hlo Hhi DT TS0 C T DB kk Hc).
Qed.

Lemma rsc_AOUT : reply_args fr pa pp pn = true ->
  addressable mb pa 2 /\ addressable mb pp 8 /\ addressable mb pn 8 /\
  (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn).
Proof.
  intros RA. destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & _ & RA1 & RA2 & RA3).
  destruct rsc_F as (HGT & _).
  destruct (rsc_cell_ivl RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)) as (La & _).
  destruct (rsc_cell_ivl RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))) as (Lp & _).
  destruct (rsc_cell_ivl RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))) as (Ln & _).
  unfold RT_LO, RT_HI, ASAN_GT in *.
  split; [exact (rsc_addr_cell RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx) RA1)|].
  split; [exact (rsc_addr_cell RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx)) RA2)|].
  split; [exact (rsc_addr_cell RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx)) RA3)|].
  split; [right; lia|]. split; right; lia.
Qed.

(* ---- the memory facts at mb ---- *)
(* ro_agree mb: the 4th part of the base cut's ctl_rt_C (route (C); ctl_rt_C_of_AR gives it from the base journal's
   AR and the image data at mb). *)
Lemma rsc_RO : B.MemNorm.ro_agree rsegs mb.
Proof. exact (proj2 (proj2 (proj2 HRTb))). Qed.

(* the message at fr: P10's bytes at memc, kept by the kept classes' block clause (YCbq.v:827-828, E = False); the
   three caller cells apart from it (P10's block vs P11's frames, al_sep) *)
Lemma rsc_HF : reply_args fr pa pp pn = true -> 50 <= len ->
  fr + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs mb fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
  (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn).
Proof.
  intros RA Hge. destruct (P10 RA Hge) as ((nb & Hin_frnb & Hreq) & Hgarr).
  pose proof P1 as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HastkC & _).
  destruct HastkC as (_ & _ & Hceil_lo & Hlo_sp & _).
  pose proof HKb as (_ & K2 & _).
  destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc W memc mdc fr nb HARc Hin_frnb)
    as (_ & Hfr4096 & Hfrceil & _ & _ & _ & _).
  assert (Hfr50 : fr + 50 <= S - 9072) by lia.
  destruct rsc_win as (_ & _ & _ & H47 & _).
  assert (Hfrapart : (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\
                     (pn + 8 <= fr \/ fr + 50 <= pn)).
  { destruct (lib.Reusable.YG0d.al_sep _ _ LAWS lyc Sc W memc mdc HARc) as [HsepPW _].
    destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & Hframe & _ & _ & _).
    assert (Hfr_byte : forall x, C_reac_ctrl_identity_reply.treply_out pa pp pn x -> x < fr \/ fr + 50 <= x).
    { intros x Hx. destruct (Hframe x Hx) as ((cid & pos0 & Hin_sc & _ & Hinzr) & _).
      unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr in Hinzr. cbn [fst snd] in Hinzr.
      assert (InBlk : In (fr, lib.Reusable.YG00.req_size nb)
                (map (fun b => (fst b, lib.Reusable.YG00.req_size (snd b))) (lib.Reusable.YG0d.ablocks B lyc Sc))).
      { change (fr, lib.Reusable.YG00.req_size nb)
          with ((fun b => (fst b, lib.Reusable.YG00.req_size (snd b))) (fr, nb)).
        apply in_map. exact Hin_frnb. }
      assert (InFrm : In (lib.Reusable.YG0f.frame_addr lyc cid pos0, lib.Reusable.YG00.fs_frame_bytes cid)
                (map (fun f => (lib.Reusable.YG0f.frame_addr lyc (fst f) (snd f),
                                lib.Reusable.YG00.fs_frame_bytes (fst f)))
                   (lib.Reusable.YG01.frames Sc))).
      { change (lib.Reusable.YG0f.frame_addr lyc cid pos0, lib.Reusable.YG00.fs_frame_bytes cid)
          with ((fun f => (lib.Reusable.YG0f.frame_addr lyc (fst f) (snd f),
                           lib.Reusable.YG00.fs_frame_bytes (fst f))) (cid, pos0)).
        apply in_map. exact Hin_sc. }
      pose proof (C_reac_ctrl_identity_replyBase.rrB_pw_cross lib.Reusable.YG0f.zdisjoint _ _ _ _ HsepPW InBlk
                    InFrm) as Hzd.
      unfold lib.Reusable.YG0f.zdisjoint in Hzd. cbn [fst snd] in Hzd. lia. }
    pose proof (Hfr_byte pa ltac:(unfold C_reac_ctrl_identity_reply.treply_out; left; lia)) as Hpa0.
    pose proof (Hfr_byte (pa + 1) ltac:(unfold C_reac_ctrl_identity_reply.treply_out; left; lia)) as Hpa1.
    pose proof (Hfr_byte pp ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; left; lia)) as Hpp0.
    pose proof (Hfr_byte (pp + 7) ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; left; lia)) as Hpp7.
    pose proof (Hfr_byte pn ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; right; lia)) as Hpn0.
    pose proof (Hfr_byte (pn + 7) ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; right; lia)) as Hpn7.
    split; [lia|]. split; lia. }
  split; [lia|]. split; [|split; [lia | exact Hfrapart]].
  apply (B.ProgWorldAstack.pwfs_bytes_of_view Wb mb fr g);
    [lia | rewrite Hg; change (Z.of_nat 50) with 50; lia |].
  intros i Hi.
  assert (HiZ50 : Z.of_nat i < 50).
  { assert (Hii : (i < 50)%nat) by (rewrite Hg in Hi; exact Hi). lia. }
  destruct (nth_error g i) as [b0|] eqn:Eb; [|exfalso; apply nth_error_None in Eb; lia].
  exists b0. split; [reflexivity|]. change lib.Reusable.YB1v.tfibsegs with rsegs.
  assert (Hilt : (i < length (map (fun bb : byte => bv_unsigned bb) g))%nat) by (rewrite length_map; exact Hi).
  destruct (Hgarr i Hilt) as [Hvm Hvr].
  unfold lib.Reusable.YI04.val_mem in Hvm.
  pose proof (Hvm 0%nat ltac:(lia)) as Hmb. rewrite Z.add_0_r in Hmb.
  assert (Hnthb : nth i (map (fun bb : byte => bv_unsigned bb) g) 0 = bv_unsigned b0)
    by (apply nth_error_nth; apply map_nth_error; exact Eb).
  rewrite Hnthb in Hmb, Hvr.
  assert (Havc : lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc (fr + Z.of_nat i)
                 = Some (bv_unsigned b0)).
  { unfold lib.Reusable.YG0n.aview. rewrite Hmb. cbn [option_map].
    rewrite (lib.Reusable.YI04.le_byte_small (bv_unsigned b0) 1 0
              ltac:(replace (2 ^ (8 * Z.of_nat 1)) with 256 by (vm_compute; reflexivity); lia) ltac:(lia)).
    change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
    rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
    rewrite Z.mod_small by lia. reflexivity. }
  rewrite (K2 fr nb (Z.of_nat i) Hin_frnb ltac:(lia) (fun HH => HH)), Havc. reflexivity.
Qed.

(* the three caller cells: present at mb (their frame is a frame of the base, AR_frames_law), apart from each other
   and from the window (their apartness from the message is rsc_HF's, under 50 <= len) *)
Lemma rsc_HO : exists ja jp jn : list byte,
  reply_args fr pa pp pn = true ->
    pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
    lib.Lib.Step.rw_cells rsegs mb pa (lib.Lib.Cells.CB 2 ja :: nil) /\
    lib.Lib.Step.rw_cells rsegs mb pp (lib.Lib.Cells.CB 8 jp :: nil) /\
    lib.Lib.Step.rw_cells rsegs mb pn (lib.Lib.Cells.CB 8 jn :: nil) /\
    (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
    (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn).
Proof.
  pose proof P1 as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HastkC & _).
  destruct HastkC as (_ & _ & Hceil_lo & Hlo_sp & _).
  pose proof HJb as (HARb & _).
  destruct (lib.Reusable.YG0d.al_sep _ _ LAWS lyc Sc W memc mdc HARc) as [_ HsepF].
  exists (C_reac_ctrl_identity_replyBase.rrB_rd mb pa 2), (C_reac_ctrl_identity_replyBase.rrB_rd mb pp 8),
    (C_reac_ctrl_identity_replyBase.rrB_rd mb pn 8). intros RA.
  destruct (P11 RA) as (Hm2 & Hm8p & Hm8n & Happp & Happn & Hpppn & Hframe & _ & _ & _).
  assert (Hcellpres : forall x, C_reac_ctrl_identity_reply.treply_out pa pp pn x -> mb (Z_to_bv 64 x) <> None).
  { intros x Hx. destruct (Hframe x Hx) as ((cid & pos0 & Hin_sc & _ & Hinzr) & _).
    unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr in Hinzr. cbn [fst snd] in Hinzr.
    assert (Hinb : In (cid, pos0) (lib.Reusable.YG01.frames Sb)) by (rewrite rsc_frb; right; exact Hin_sc).
    destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyb Sb Wb mb mdb cid pos0 HARb Hinb) as (_ & _ & Hfpres & _).
    rewrite rsc_fa in Hfpres.
    destruct (Hfpres x Hinzr) as [[_ [b Hb]] _]. rewrite Hb. discriminate. }
  assert (Hcell_lt_ceil : forall x, C_reac_ctrl_identity_reply.treply_out pa pp pn x ->
                            x < lib.Reusable.YM05.alloc_ceiling).
  { intros x Hx. destruct (Hframe x Hx) as ((cid & pos0 & Hin_sc & _ & Hinzr) & _).
    unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr in Hinzr. cbn [fst snd] in Hinzr.
    pose proof (proj1 (Forall_forall _ _) HsepF (cid, pos0) Hin_sc) as Hf. cbn [fst snd] in Hf. lia. }
  assert (Hpa1c : pa + 1 < lib.Reusable.YM05.alloc_ceiling)
    by (apply Hcell_lt_ceil; unfold C_reac_ctrl_identity_reply.treply_out; left; lia).
  assert (Hpp7c : pp + 7 < lib.Reusable.YM05.alloc_ceiling)
    by (apply Hcell_lt_ceil; unfold C_reac_ctrl_identity_reply.treply_out; right; left; lia).
  assert (Hpn7c : pn + 7 < lib.Reusable.YM05.alloc_ceiling)
    by (apply Hcell_lt_ceil; unfold C_reac_ctrl_identity_reply.treply_out; right; right; lia).
  split; [exact Hm2|]. split; [exact Hm8p|]. split; [exact Hm8n|].
  split.
  { apply C_reac_ctrl_identity_replyBase.rrB_rw_present; [lia | change (Z.of_nat 2) with 2; lia |].
    intros i Hi. change (Z.of_nat 2) with 2 in Hi. apply Hcellpres.
    unfold C_reac_ctrl_identity_reply.treply_out. left. lia. }
  split.
  { apply C_reac_ctrl_identity_replyBase.rrB_rw_present; [lia | change (Z.of_nat 8) with 8; lia |].
    intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply Hcellpres.
    unfold C_reac_ctrl_identity_reply.treply_out. right. left. lia. }
  split.
  { apply C_reac_ctrl_identity_replyBase.rrB_rw_present; [lia | change (Z.of_nat 8) with 8; lia |].
    intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply Hcellpres.
    unfold C_reac_ctrl_identity_reply.treply_out. right. right. lia. }
  split; [exact Happp|]. split; [exact Happn|]. split; [exact Hpppn|].
  split; [lia|]. split; lia.
Qed.

Lemma rsc_HOimg : reply_args fr pa pp pn = true ->
  ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn.
Proof.
  intros RA. destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & Hframe & _ & _ & _).
  pose proof P1 as (HARc & _).
  assert (Hge_img : forall x, C_reac_ctrl_identity_reply.treply_out pa pp pn x -> ImgBounds.IMG_HI <= x).
  { intros x Hx. destruct (Hframe x Hx) as ((cid & pos0 & Hin_sc & _ & Hinzr) & _).
    unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr in Hinzr. cbn [fst snd] in Hinzr.
    pose proof (B.ProgWorld_Fs.ctl_frame_above_img B lyc Sc W memc mdc cid pos0 HARc Hin_sc) as Hab.
    unfold ImgBounds.IMG_HI. lia. }
  split; [apply Hge_img; unfold C_reac_ctrl_identity_reply.treply_out; left; lia|].
  split; [apply Hge_img; unfold C_reac_ctrl_identity_reply.treply_out; right; left; lia
         |apply Hge_img; unfold C_reac_ctrl_identity_reply.treply_out; right; right; lia].
Qed.

Lemma rsc_nums : S < 2 ^ 64 /\ 9072 <= S /\ HIGHMEM_BEG <= S - 9072 /\ S <= APPMEM_END.
Proof.
  destruct rsc_win as (_ & _ & Hc & H47 & _). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 _] _].
  unfold HIGHMEM_BEG, APPMEM_END. lia.
Qed.

(* ==== S-C: the base is the memory at reac_ctrl_parse's return 0x84a68 ==== *)
Section SC.
(* the registers S-A saved at S - 104 (rSAVES), S-B's call-state data and the return of the call *)
Variables (ra gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (S2 : lib.Reusable.YG00.astate)
  (m5 : word -> option byte) (md5 : Model) (regs2 : bvmap 5 word).
(* the journal at the call (Comp.rrB_J_SB's conclusion at the call state) *)
Hypothesis HJ5 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W m5 md5 k.
(* rrB_QSB's left end: reply_args, and rBI's saved registers and flag-pointer word at the real call memory
   (rrB_SBL_mem) *)
Hypothesis HRA : reply_args fr pa pp pn = true.
Hypothesis HSV5 : lib.Lib.Step.rw_cells rsegs m5 (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Hypothesis HFL15 : lib.Lib.Mem.bytes_at rsegs m5 (fs_frame FSc 1 pos + 120)
  (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FSc 1 pos))).
(* E2's interface at the return (C_reac_ctrl_identity_replyE2.rrB_E2_ret, call state (lyc, S2)) *)
Hypothesis HE2 : C_reac_ctrl_identity_replyE2.rrB_E2_ret B STK sp0 FP ly S0 W0 mem0 md0 own pos lyc S2 W m5 k gp tp
  fr len pa pp pn S (fs_frame FSc 1 pos) g Wb lyb Sb regs2 mb mdb.

(* the 13 saved registers above the call's sp: kept across reac_ctrl_parse by its acall_kept's first clause (above
   alloc_ceiling, off parse's window [rA S - 8800, rA S)), present at both ends (the two journals' window presence) *)
Lemma rsc_SC_SV : lib.Lib.Step.rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Proof.
  pose proof HE2 as (_ & _ & _ & _ & _ & _ & _ & HK & _).
  pose proof HK as (K1 & _).
  pose proof HJ5 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp5 & _).
  destruct rsc_win as (_ & _ & Hceil & H47 & Hpb). unfold lib.Reusable.YG0f.ASAN_CEIL in Hceil.
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  assert (HA : S - 144 <= rA S <= S - 128) by (unfold rA; Z.div_mod_to_equations; lia).
  apply (C_reac_ctrl_identity_replyBase.rrB_rw_cong m5 mb (S - 104)); [|exact HSV5].
  intros i Hi.
  assert (Hcs : Z.of_nat (lib.Lib.Cells.cells_size (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) = 104)
    by (vm_compute; reflexivity).
  rewrite Hcs in Hi.
  destruct (Hpb (S - 104 + i) ltac:(lia)) as [Hhb Hmb].
  destruct (Hp5 (S - 104 + i) ltac:(lia)) as [Hh5 Hm5].
  apply (rsc_mem_of_views (lib.Reusable.YA0n.w_H W) (lib.Reusable.YA0n.w_H Wb) m5 mb (S - 104 + i));
    [| exact Hhb | exact Hh5 | exact Hmb | exact Hm5].
  apply K1; [lia | unfold C_reac_ctrl_parse.REAC_CTRL_PARSE_STK; lia].
Qed.

(* the flag-pointer word at G + 120: inside the frame (1, pos) of the call state, off parse's output [G + 32, G + 68),
   kept by the call's frame clause; present at both ends (AR_frames_law at the call and at the return) *)
Lemma rsc_SC_FL1 : lib.Lib.Mem.bytes_at rsegs mb (fs_frame FSc 1 pos + 120)
  (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FSc 1 pos))).
Proof.
  pose proof HE2 as (_ & _ & _ & _ & _ & _ & _ & HK & _).
  pose proof HK as (_ & _ & _ & K4 & _).
  pose proof HJ5 as (HAR5 & _ & _ & _ & _ & HFR5 & _).
  pose proof HJb as (HARb & _).
  assert (Hin5 : In (1, pos) (lib.Reusable.YG01.frames S2))
    by (rewrite HFR5; apply in_or_app; left; left; reflexivity).
  assert (Hinb : In (1, pos) (lib.Reusable.YG01.frames Sb)) by (rewrite rsc_frb; left; reflexivity).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc S2 W m5 md5 1 pos HAR5 Hin5) as (_ & _ & Hf5 & _).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyb Sb Wb mb mdb 1 pos HARb Hinb) as (_ & _ & Hfb & _).
  rewrite rsc_fa in Hfb.
  assert (E128 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by reflexivity.
  rewrite E128, <- rsc_fr_eq in Hf5, Hfb.
  apply (rsc_bytes_cong m5 mb); [|exact HFL15].
  intros i Hi. rewrite lib.Lib.Mem.length_le8 in Hi.
  destruct (Hfb (fs_frame FSc 1 pos + 120 + Z.of_nat i) ltac:(lia)) as [[Hhb Hmb] _].
  destruct (Hf5 (fs_frame FSc 1 pos + 120 + Z.of_nat i) ltac:(lia)) as [[Hh5 Hm5] _].
  apply (rsc_mem_of_views (lib.Reusable.YA0n.w_H W) (lib.Reusable.YA0n.w_H Wb) m5 mb _);
    [| exact Hhb | exact Hh5 | exact Hmb | exact Hm5].
  apply (K4 1 pos); [exact Hin5 | | cbv beta; lia].
  left. unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng. cbn [fst snd]. rewrite E128, <- rsc_fr_eq. lia.
Qed.

(* rrB_SC_base: every premise of C_reac_ctrl_identity_replyRet.rrB_SC_lifted except wx_segs_nowrap and its
   continuation, in rrB_SC_lifted's own order, at mb := the memory at parse's return, W := the world after the call,
   FS := ly_F lyc, jj := pos, with ja jp jn the bytes of the three cells at mb.
   The shadow premise is the run's narrowed one (route (C)), from the base cut's ctl_rt_C (rsc_RT). *)
Lemma rrB_SC_base :
  exists ja jp jn : list byte,
  0 <= fr < 2^64 /\ 0 <= len < 2^64 /\ 0 <= pa < 2^64 /\ 0 <= pp < 2^64 /\ 0 <= pn < 2^64 /\
  S < 2^64 /\ S mod 16 = 0 /\ 9072 <= S /\
  B.MemNorm.ro_agree rsegs mb /\
  stk rsegs mb (S - 9072) S /\ length g = 50%nat /\
  (reply_args fr pa pp pn = true -> 50 <= len ->
     fr + 50 <= 2^64 /\ bytes_at rsegs mb fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
     (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)) /\
  (reply_args fr pa pp pn = true ->
     pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
     rw_cells rsegs mb pa [CB 2 ja] /\ rw_cells rsegs mb pp [CB 8 jp] /\ rw_cells rsegs mb pn [CB 8 jn] /\
     (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
     (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)) /\
  (reply_args fr pa pp pn = true -> ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn) /\
  asan_cells mb /\ shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FSc) mb /\
  HIGHMEM_BEG <= S - 9072 /\ S <= APPMEM_END /\
  addressable mb (S - 9072) 9072 /\
  (reply_args fr pa pp pn = true -> 50 <= len -> addressable mb fr 50) /\
  (reply_args fr pa pp pn = true ->
     addressable mb pa 2 /\ addressable mb pp 8 /\ addressable mb pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) /\
  fp [1%nat] mb (bv_unsigned tp) FSc (S - 9072) S
    (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) /\
  reac_ctrl_identity_reply_tls mb (bv_unsigned tp) FSc (S - 9072) S /\
  reply_args fr pa pp pn = true /\ 0 <= pos < fs_M 1 /\
  rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  rw_cells rsegs mb (fs_frame FSc 1 pos + 32) [CB 36 (snd (lib.Prog.RcParse.ctrlparse len g))] /\
  bytes_at rsegs mb (fs_frame FSc 1 pos + 120) (le8 (Z_to_bv 64 (fs_flag FSc 1 pos))) /\
  bytes_at rsegs mb (fs_flag FSc 1 pos) [Z_to_bv 8 1] /\
  ExecF.rng RGW (S - 9072) 9072 /\
  shcov RGW (S - 9072) 9072 /\
  (reply_args fr pa pp pn = true -> 50 <= len -> ExecF.rng RGW fr 50) /\
  (reply_args fr pa pp pn = true -> 50 <= len -> shcov RGW fr 50) /\
  (reply_args fr pa pp pn = true -> 50 <= len -> shkov RGW fr 50) /\
  (reply_args fr pa pp pn = true -> ExecF.rng RGW pa 2) /\
  (reply_args fr pa pp pn = true -> shcov RGW pa 2) /\
  (reply_args fr pa pp pn = true -> ExecF.rng RGW pp 8) /\
  (reply_args fr pa pp pn = true -> shcov RGW pp 8) /\
  (reply_args fr pa pp pn = true -> ExecF.rng RGW pn 8) /\
  (reply_args fr pa pp pn = true -> shcov RGW pn 8) /\
  ExecF.rng RGW (fs_flag FSc 1 0) (fs_M 1) /\
  ExecF.rng RGW (fs_frame FSc 1 0) (fs_frame FSc 1 (fs_M 1) - fs_frame FSc 1 0) /\
  shcov RGW (fs_frame FSc 1 0) (fs_frame FSc 1 (fs_M 1) - fs_frame FSc 1 0).
Proof.
  destruct rsc_HO as (ja & jp & jn & HO).
  destruct rsc_nums as (N1 & N2 & N3 & N4).
  destruct rsc_RT as (AC & SW).
  pose proof HE2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                     REC & _).
  exists ja, jp, jn.
  split; [exact Rfr|]. split; [exact Rlen|]. split; [exact Rpa|]. split; [exact Rpp|]. split; [exact Rpn|].
  split; [exact N1|]. split; [exact S16|]. split; [exact N2|].
  split; [exact rsc_RO|]. split; [exact rsc_ST|]. split; [exact Hg|].
  split; [exact rsc_HF|]. split; [exact HO|]. split; [exact rsc_HOimg|].
  split; [exact AC|]. split; [exact SW|]. split; [exact N3|]. split; [exact N4|].
  split; [exact rsc_AW|]. split; [exact rsc_AFfr|]. split; [exact rsc_AOUT|].
  split; [exact rsc_fp|]. split; [exact rsc_tls|].
  split; [exact HRA|]. split; [exact rsc_jj|].
  split; [exact rsc_SC_SV|]. split; [exact REC|]. split; [exact rsc_SC_FL1|]. split; [exact rsc_FL2|].
  split; [exact rsc_RWIN|]. split; [exact rsc_SCW|].
  split; [intros RA HL; exact (B.ProgBridge.rng_of_visible _ _ _ (proj1 (rsc_heap RA HL)))|].
  split; [exact rsc_SCF|]. split; [exact rsc_SKF|].
  split; [intros RA; exact (proj1 (rsc_cell_vis RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)))|].
  split; [intros RA; exact (proj2 (rsc_cell_vis RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)))|].
  split; [intros RA; exact (proj1 (rsc_cell_vis RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))))|].
  split; [intros RA; exact (proj2 (rsc_cell_vis RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))))|].
  split; [intros RA; exact (proj1 (rsc_cell_vis RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))))|].
  split; [intros RA; exact (proj2 (rsc_cell_vis RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))))|].
  split; [exact rsc_RFLG|]. split; [exact rsc_RFRM | exact rsc_SCFM].
Qed.
End SC.

(* ==== the tail: the base is the real memory at S-B's -1 end (the epilogue entry 0x84bdc) ==== *)
Section Tail.
Variables (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word).
(* rrB_QSB's right end, read at the real end memory (rrB_SBR_mem) *)
Hypothesis HSVt : lib.Lib.Step.rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11).
Hypothesis HFL1t : lib.Lib.Mem.bytes_at rsegs mb (fs_frame FSc 1 pos + 120)
  (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag FSc 1 pos))).
Hypothesis HOUTt : reply_ok fr len pa pp pn g = true -> rOUTF fr pa pp pn g mb.

(* rrB_tail_base: every premise of C_reac_ctrl_identity_replyRet.rrB_tail_lifted except wx_segs_nowrap and its
   continuation, in rrB_tail_lifted's own order, at mb := the real memory at S-B's -1 end, FS := ly_F lyc, jj := pos.
   The shadow premise is the run's narrowed one (route (C)), from the base cut's ctl_rt_C (rsc_RT). *)
Lemma rrB_tail_base :
  exists ja jp jn : list byte,
  0 <= fr < 2^64 /\ 0 <= len < 2^64 /\ 0 <= pa < 2^64 /\ 0 <= pp < 2^64 /\ 0 <= pn < 2^64 /\
  S < 2^64 /\ S mod 16 = 0 /\ 9072 <= S /\
  B.MemNorm.ro_agree rsegs mb /\
  stk rsegs mb (S - 9072) S /\ length g = 50%nat /\
  (reply_args fr pa pp pn = true -> 50 <= len ->
     fr + 50 <= 2^64 /\ bytes_at rsegs mb fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
     (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)) /\
  (reply_args fr pa pp pn = true ->
     pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
     rw_cells rsegs mb pa [CB 2 ja] /\ rw_cells rsegs mb pp [CB 8 jp] /\ rw_cells rsegs mb pn [CB 8 jn] /\
     (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
     (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)) /\
  (reply_args fr pa pp pn = true -> ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn) /\
  asan_cells mb /\ shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FSc) mb /\
  HIGHMEM_BEG <= S - 9072 /\ S <= APPMEM_END /\
  addressable mb (S - 9072) 9072 /\
  (reply_args fr pa pp pn = true -> 50 <= len -> addressable mb fr 50) /\
  (reply_args fr pa pp pn = true ->
     addressable mb pa 2 /\ addressable mb pp 8 /\ addressable mb pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) /\
  fp [1%nat] mb (bv_unsigned tp) FSc (S - 9072) S
    (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) /\
  reac_ctrl_identity_reply_tls mb (bv_unsigned tp) FSc (S - 9072) S /\
  0 <= pos < fs_M 1 /\
  rw_cells rsegs mb (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  bytes_at rsegs mb (fs_frame FSc 1 pos + 120) (le8 (Z_to_bv 64 (fs_flag FSc 1 pos))) /\
  bytes_at rsegs mb (fs_flag FSc 1 pos) [Z_to_bv 8 1] /\
  (reply_ok fr len pa pp pn g = true -> rOUTF fr pa pp pn g mb) /\
  ExecF.rng RGW (S - 9072) 9072 /\
  shcov RGW (S - 9072) 9072 /\
  (reply_args fr pa pp pn = true -> 50 <= len -> ExecF.rng RGW fr 50) /\
  (reply_args fr pa pp pn = true -> 50 <= len -> shcov RGW fr 50) /\
  (reply_args fr pa pp pn = true -> 50 <= len -> shkov RGW fr 50) /\
  (reply_args fr pa pp pn = true -> ExecF.rng RGW pa 2) /\
  (reply_args fr pa pp pn = true -> shcov RGW pa 2) /\
  (reply_args fr pa pp pn = true -> ExecF.rng RGW pp 8) /\
  (reply_args fr pa pp pn = true -> shcov RGW pp 8) /\
  (reply_args fr pa pp pn = true -> ExecF.rng RGW pn 8) /\
  (reply_args fr pa pp pn = true -> shcov RGW pn 8) /\
  ExecF.rng RGW (fs_flag FSc 1 0) (fs_M 1) /\
  ExecF.rng RGW (fs_frame FSc 1 0) (fs_frame FSc 1 (fs_M 1) - fs_frame FSc 1 0) /\
  shcov RGW (fs_frame FSc 1 0) (fs_frame FSc 1 (fs_M 1) - fs_frame FSc 1 0).
Proof.
  destruct rsc_HO as (ja & jp & jn & HO).
  destruct rsc_nums as (N1 & N2 & N3 & N4).
  destruct rsc_RT as (AC & SW).
  exists ja, jp, jn.
  split; [exact Rfr|]. split; [exact Rlen|]. split; [exact Rpa|]. split; [exact Rpp|]. split; [exact Rpn|].
  split; [exact N1|]. split; [exact S16|]. split; [exact N2|].
  split; [exact rsc_RO|]. split; [exact rsc_ST|]. split; [exact Hg|].
  split; [exact rsc_HF|]. split; [exact HO|]. split; [exact rsc_HOimg|].
  split; [exact AC|]. split; [exact SW|]. split; [exact N3|]. split; [exact N4|].
  split; [exact rsc_AW|]. split; [exact rsc_AFfr|]. split; [exact rsc_AOUT|].
  split; [exact rsc_fp|]. split; [exact rsc_tls|].
  split; [exact rsc_jj|].
  split; [exact HSVt|]. split; [exact HFL1t|]. split; [exact rsc_FL2|]. split; [exact HOUTt|].
  split; [exact rsc_RWIN|]. split; [exact rsc_SCW|].
  split; [intros RA HL; exact (B.ProgBridge.rng_of_visible _ _ _ (proj1 (rsc_heap RA HL)))|].
  split; [exact rsc_SCF|]. split; [exact rsc_SKF|].
  split; [intros RA; exact (proj1 (rsc_cell_vis RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)))|].
  split; [intros RA; exact (proj2 (rsc_cell_vis RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)))|].
  split; [intros RA; exact (proj1 (rsc_cell_vis RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))))|].
  split; [intros RA; exact (proj2 (rsc_cell_vis RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))))|].
  split; [intros RA; exact (proj1 (rsc_cell_vis RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))))|].
  split; [intros RA; exact (proj2 (rsc_cell_vis RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))))|].
  split; [exact rsc_RFLG|]. split; [exact rsc_RFRM | exact rsc_SCFM].
Qed.
End Tail.
End Common.
