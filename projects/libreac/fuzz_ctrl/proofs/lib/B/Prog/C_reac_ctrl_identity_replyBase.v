(* lib/B/Prog/C_reac_ctrl_identity_replyBase.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the MEMORY half of
   the glue premise bundle for rrB_SB_lifted (lib/B/Prog/C_reac_ctrl_identity_replyPf.v, S-B lifted from the real base
   memory).  Owner a Theorem Labs lane (split with a Theorem Labs lane, who owns the FOOTPRINT/VIEW half in
   C_reac_ctrl_identity_replyBaseV.v; this file Requires it but not the lead's Pf/Lib files, and never edits them).

   rrB_SB_base_mem gives, from the data the glue holds at the class-1 fake-stack return (S-A's continuation of
   rrB_to_E1: rMCALL over normalize memc, mem_rel, ro_same, the journal at m1; E1's continuation of rrB_E1: the
   journal at ((1, pos) :: own) with mem2, acall_kept, and -- after the fd812f73bc3 re-proof of rrB_E1 through
   lib/Reusable/YCbqMalloc.aj_stack_malloc_at_fc -- the four pre/post facts the class-1 request now hands on:
   ecall_pre, the astack frame condition, and the two presence clauses), the MEMORY-side premises of rrB_SB_lifted at
   mb := mem2, FS := lib.Reusable.YG0f.ly_F lyc, jj := pos:
     the numerics; B.MemNorm.ro_agree mem2 (the 4th part of the cut's ctl_rt_C, HRT2); stk of the window; length g =
     50; the message bytes_at at fr (and, under 50 <= len, the three caller cells apart from it); the
     rw_cells of the three caller cells and of rSAVES at S - 104; the two flag facts of the frame and 0 <= pos < fs_M 1
     (by B.ProgWorldAstack.ctl_fs_of_astack 1); the premise that the three cells lie above IMG_HI.
   The FOOTPRINT/VIEW premises (shadow_rw_on R (route (C)), addressable, fp, tls, the rng/shcov/shkov at RNG_W (w_H W))
   are a Theorem Labs lane's half; rrB_SB_base composes the two.

   PROVED B lemmas used (file:line on e026bdcbd0d):
     B.ProgWorldAstack.ctl_fs_of_astack        (lib/B/ProgWorldAstack.v:248)   the frame facts after __asan_stack_malloc_1
     B.ProgWorld.ctl_fs_geom                    (lib/B/ProgWorld.v:437)         class geometry (fs_B 1 = 128 etc.)
     B.ProgWorld.aview_vis_mrd                  (lib/B/ProgWorld.v:579)         a visible byte's view is its mrd byte
     B.ProgWorld.rw_cells_CB_of_present         (lib/B/ProgWorld.v:712)         a present range is a CB rw_cells
     B.ProgWorld_Fs.ctl_frame_above_img         (lib/B/ProgWorld_Fs.v:531)      a live frame lies above IMG_HI
     B.ProgWorldAstack.pwfs_stk_of_present      (lib/B/ProgWorldAstack.v:155)   stk from presence
     B.ProgWorldAstack.pwfs_bytes_of_view       (lib/B/ProgWorldAstack.v:103)   bytes_at from the view
     B.ProgWorldCtlRt.find_segment_some_spec    (lib/B/ProgWorldCtlRt.v:318)    a found segment's bounds (in_img)
     B.MemNormTr.ro_addr_above_img              (lib/B/MemNormTr.v:53)          above IMG_HI no byte is read-only
     lib.Reusable.YG0d.{al_blocks,al_frames,al_sep}  (lib/Reusable/YG0d.v:497,501,509)  the AR laws
     lib.Reusable.YF0m.ts_errno                 (lib/Reusable/YF0m.v:2991)      as_errno B = TFIB_ERRNO
     lib.Reusable.YI04.le_byte_small            (lib/Reusable/YI04.v:147)       the one-byte little-endian value
   Named Section hypotheses of the memory half: HRT2, the cut's B.ACtlRtC.ctl_rt_C at (lyc, S2, mem2) (route (C):
     the composition supplies it by B.ProgWorldCtlRtC.ctl_rt_C_of_AR at HJ2's AR); its 4th part is ro_agree mem2.
     The fr apartness of the three caller cells is in HF, under reply_args and 50 <= len (the accepted contract_F
     guard, a working branch 20372bbcc3a), where P10's heap block and P11's caller frames give it by al_sep
     (blocks vs frames).
   No Axiom, Parameter, Admitted, admit, Abort. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import
  asan_stack_malloc_c reac_ctrl_identity_reply_c reac_ctrl_identity_reply_c_on reac_ctrl_identity_replyRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require
  YK11 YM05 YI16 YK04 YA0n YG0f YG0d YG00 YG01 YG0n YG0v YI00 YI04 YCbq YF0m YB1v.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require
  B.MemNorm B.MemNormTr B.ProgBridge B.ProgWorld B.ProgWorldAstack B.ProgWorld_Fs B.ProgWorldCtlRt B.ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds C_reac_ctrl_identity_reply.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
(* a Theorem Labs lane's view half (rrB_SB_base_vis), composed below into rrB_SB_base. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require RcAsanFP C_reac_ctrl_identity_replyBaseV.
Import ListNotations.
Open Scope Z_scope.

(* ------------------------------------------------------------------------------------------------------------ *)
(* Generic byte-level helpers (over the fixed image segments rsegs = B.Img0.rsegs). *)

(* A default-zero reader of n bytes from m at a. *)
Fixpoint rrB_rd (m : word -> option byte) (a : Z) (n : nat) : list byte :=
  match n with
  | O => nil
  | S k => match m (Z_to_bv 64 a) with Some b => b | None => Z_to_bv 8 0 end :: rrB_rd m (a + 1) k
  end.

Lemma rrB_rd_length : forall n m a, length (rrB_rd m a n) = n.
Proof. induction n as [|n IH]; intros m a; [reflexivity|]. cbn [rrB_rd length]. rewrite IH. reflexivity. Qed.

Lemma rrB_rd_mrd : forall n (m : word -> option byte) d i, (i < n)%nat ->
  m (Z_to_bv 64 (d + Z.of_nat i)) <> None ->
  lib.Lib.Mem.mrd rsegs m (Z_to_bv 64 (d + Z.of_nat i)) = nth_error (rrB_rd m d n) i.
Proof.
  induction n as [|n IH]; intros m d i Hi Hp; [lia|].
  destruct i as [|i].
  - cbn [rrB_rd nth_error]. rewrite Z.add_0_r in Hp |- *.
    unfold lib.Lib.Mem.mrd. destruct (m (Z_to_bv 64 d)) as [b|] eqn:Em; [reflexivity|].
    exfalso. apply Hp. reflexivity.
  - cbn [rrB_rd nth_error].
    replace (d + Z.of_nat (S i)) with ((d + 1) + Z.of_nat i) by lia.
    apply IH; [lia|]. replace ((d + 1) + Z.of_nat i) with (d + Z.of_nat (S i)) by lia. exact Hp.
Qed.

Lemma rrB_rw_present : forall (m : word -> option byte) (d : Z) (k : nat),
  0 <= d -> d + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> m (Z_to_bv 64 (d + i)) <> None) ->
  lib.Lib.Step.rw_cells rsegs m d (lib.Lib.Cells.CB k (rrB_rd m d k) :: nil).
Proof.
  intros m d k Hd Hk Hp.
  apply B.ProgWorld.rw_cells_CB_of_present; [apply rrB_rd_length | exact Hd | exact Hk | |].
  - intros i Hi. apply rrB_rd_mrd; [exact Hi|].
    apply Hp. split; [lia|]. apply Nat2Z.inj_lt in Hi. lia.
  - intros i Hi. apply Hp. exact Hi.
Qed.

(* aview reads memory only at the one address. *)
Lemma rrB_aview_point : forall (W : lib.Reusable.YA0n.world rsegs) (m m' : word -> option byte) (a : Z),
  m (Z_to_bv 64 a) = m' (Z_to_bv 64 a) ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m a =
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m' a.
Proof.
  intros W m m' a H. unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict.
  destruct (lib.Reusable.YA0n.w_H W (Z_to_bv 64 a)) eqn:E; [reflexivity|]. rewrite H. reflexivity.
Qed.

(* Two present memories with equal views at a visible address hold equal bytes there. *)
Lemma rrB_mem_of_aview_eq : forall (W : lib.Reusable.YA0n.world rsegs) (m m' : word -> option byte) (a : Z),
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m' a =
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m a ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false ->
  (exists b, m' (Z_to_bv 64 a) = Some b) -> (exists b, m (Z_to_bv 64 a) = Some b) ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a).
Proof.
  intros W m m' a Hv Hh [b' Hb'] [b Hb].
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict in Hv.
  rewrite Hh in Hv. rewrite Hb, Hb' in Hv. cbn [option_map] in Hv.
  injection Hv as Hbb. rewrite Hb, Hb'. f_equal. apply bv_eq. exact Hbb.
Qed.

(* rw_cells transfers between memories that agree, byte by byte, over the cell range. *)
Lemma rrB_rw_cong : forall (m m' : word -> option byte) (A : Z) (cs : list lib.Lib.Cells.cell),
  (forall i, 0 <= i < Z.of_nat (lib.Lib.Cells.cells_size cs) -> m' (Z_to_bv 64 (A + i)) = m (Z_to_bv 64 (A + i))) ->
  lib.Lib.Step.rw_cells rsegs m A cs -> lib.Lib.Step.rw_cells rsegs m' A cs.
Proof.
  intros m m' A cs Hcong [[Hwf Hba] Hwr].
  assert (Hlen : length (lib.Lib.Cells.cells_bytes cs) = lib.Lib.Cells.cells_size cs)
    by (apply lib.Lib.Cells.cells_bytes_length; exact Hwf).
  split; [split; [exact Hwf|] |].
  - destruct Hba as (HA & HAL & Hb). split; [exact HA|]. split; [exact HAL|].
    intros i Hi.
    assert (Hic : (i < lib.Lib.Cells.cells_size cs)%nat) by (rewrite <- Hlen; exact Hi).
    replace (lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa (A + Z.of_nat i)))
       with (lib.Lib.Mem.mrd rsegs m (lib.Lib.Mem.wa (A + Z.of_nat i)))
       by (unfold lib.Lib.Mem.mrd, lib.Lib.Mem.wa;
           rewrite (Hcong (Z.of_nat i) ltac:(split; [lia|]; apply Nat2Z.inj_lt; exact Hic)); reflexivity).
    exact (Hb i Hi).
  - destruct Hwr as (HA & HAL & Hw). split; [exact HA|]. split; [exact HAL|].
    intros i Hi.
    replace (wview rsegs m' (lib.Lib.Mem.wa (A + i))) with (wview rsegs m (lib.Lib.Mem.wa (A + i)))
      by (unfold wview, lib.Lib.Mem.wa; rewrite (Hcong i Hi); reflexivity).
    exact (Hw i Hi).
Qed.

(* pairwise over a concatenation relates any left element to any right element. *)
Lemma rrB_pw_cross : forall {X : Type} (R : X -> X -> Prop) (L1 L2 : list X) (u v : X),
  lib.Reusable.YG0f.pairwise R (L1 ++ L2) -> In u L1 -> In v L2 -> R u v.
Proof.
  induction L1 as [|a L1 IH]; intros L2 u v HP Hu Hv; [destruct Hu|].
  cbn [app] in HP. cbn [lib.Reusable.YG0f.pairwise] in HP. destruct HP as [HF HP'].
  destruct Hu as [->|Hu].
  - rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hv.
  - exact (IH L2 u v HP' Hu Hv).
Qed.

Lemma rrB_u64 : forall a, 0 <= a < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 a) = a.
Proof.
  intros a H. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. exact H.
Qed.

(* ------------------------------------------------------------------------------------------------------------ *)
Section Base.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis TS : lib.Reusable.YF0m.CtrlTSyms B.

(* ---- the spec cut at the entry (lib/B/Prog/C_reac_ctrl_identity_reply.v, FROZEN: P1, P4, P5, P7, P9, P10, P11) ---- *)
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : lib.Reusable.YG0f.alayout) (S0 : lib.Reusable.YG00.astate)
  (W0 : lib.Reusable.YA0n.world rsegs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (W : lib.Reusable.YA0n.world rsegs)
  (memc : word -> option byte) (mdc : Model) (k : Z)
  (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fr len pa pp pn S : Z) (g : list byte).
Hypothesis P1 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k.
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
     (exists cid pos, In (cid, pos) (lib.Reusable.YG01.frames Sc) /\
        lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos))) /\
     lib.Reusable.YCbq.awr_byte STK sp0 FP (lib.Reusable.YG0d.ablocks B ly S0) (lib.Reusable.YG0d.ablocks B lyc Sc)
       lyc own a) /\
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
    lib.Reusable.YG0f.SHADOW_OFF pa 2 /\
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
    lib.Reusable.YG0f.SHADOW_OFF pp 8 /\
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
    lib.Reusable.YG0f.SHADOW_OFF pn 8.

(* ---- S-A: the continuation data of rrB_to_E1 (lib/B/Prog/C_reac_ctrl_identity_replyPf.v) ---- *)
Variables (m1 mc : word -> option byte) (mdc1 : Model).
Hypothesis HR : rMCALL ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs memc) S mc.
Hypothesis HREL : B.MemNorm.mem_rel rsegs m1 mc.
Hypothesis HROS : B.MemNorm.ro_same rsegs memc m1.
Hypothesis HJ1 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k.

(* ---- E1: the continuation data of rrB_E1, re-proved through lib.Reusable.YCbqMalloc.aj_stack_malloc_at_fc
   (fd812f73bc3): regs is the pre-call register bundle (rrB_regsT ..) with spZ regs = rA S supplied at composition. ---- *)
Variables (regs regs2 : bvmap 5 word) (S2 : lib.Reusable.YG00.astate)
  (mem2 : word -> option byte) (md2 : Model) (pos : Z).
Hypothesis HECP : lib.Reusable.YG0d.ecall_pre rsegs B lyc Sc W regs m1 mdc1.
Hypothesis HJ2 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k.
Hypothesis H10 : lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.frame_addr lyc 1 pos).
Hypothesis HFR : lib.Reusable.YG01.frames S2 = (1, pos) :: lib.Reusable.YG01.frames Sc.
Hypothesis HNI : ~ In (1, pos) (lib.Reusable.YG01.frames Sc).
Hypothesis HZ : lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
  lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr lyc 1 pos) (lib.Reusable.YG00.fs_frame_bytes 1).
Hypothesis HFL : lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
  (lib.Reusable.YG0f.frame_addr lyc 1 pos + lib.Reusable.YG00.fs_frame_bytes 1 - 8) =
  Some (lib.Reusable.YG0f.flag_addr lyc 1 pos).
Hypothesis HPRESW : forall a, lib.Reusable.YG0d.spZ regs - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regs ->
  lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a.
Hypothesis HFRCOND : forall a, 0 <= a < 2 ^ 64 ->
  ~ lib.Reusable.YG0n.aowned B lyc Sc a -> ~ lib.Reusable.YG0n.aowned B lyc S2 a ->
  ~ (lib.Reusable.YG0d.spZ regs - lib.Reusable.YG0d.ESTACK <= a < lib.Reusable.YG0d.spZ regs) ->
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2 a =
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) m1 a.
Hypothesis HKEPT : lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2
  (sp0 + (rA S - sp0) - lib.Reusable.YG0d.ESTACK) (sp0 + (rA S - sp0)) (fun _ => False).
(* route (C): the cut after the class-1 request HAS ctl_rt_C at (lyc, S2, mem2) (the composition supplies it by
   B.ProgWorldCtlRtC.ctl_rt_C_of_AR at HJ2's AR); its 4th part is ro_agree mem2. *)
Hypothesis HRT2 : B.ACtlRtC.ctl_rt_C B lyc S2 mem2.

Lemma rrB_SB_base_mem :
  (0 <= fr < 2 ^ 64) /\ (0 <= len < 2 ^ 64) /\ (0 <= pa < 2 ^ 64) /\ (0 <= pp < 2 ^ 64) /\ (0 <= pn < 2 ^ 64) /\
  S < 2 ^ 64 /\ S mod 16 = 0 /\ 9072 <= S /\
  B.MemNorm.ro_agree rsegs mem2 /\
  lib.Lib.Frame.stk rsegs mem2 (S - 9072) S /\
  length g = 50%nat /\
  (reply_args fr pa pp pn = true -> 50 <= len ->
     fr + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs mem2 fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
     (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)) /\
  (exists ja jp jn : list byte,
     reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       lib.Lib.Step.rw_cells rsegs mem2 pa (lib.Lib.Cells.CB 2 ja :: nil) /\
       lib.Lib.Step.rw_cells rsegs mem2 pp (lib.Lib.Cells.CB 8 jp :: nil) /\
       lib.Lib.Step.rw_cells rsegs mem2 pn (lib.Lib.Cells.CB 8 jn :: nil) /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)) /\
  (reply_args fr pa pp pn = true ->
     ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn) /\
  HIGHMEM_BEG <= S - 9072 /\ S <= APPMEM_END /\
  lib.Lib.Step.rw_cells rsegs mem2 (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  lib.Lib.Mem.bytes_at rsegs mem2 (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + 120)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag (lib.Reusable.YG0f.ly_F lyc) 1 pos))) /\
  lib.Lib.Mem.bytes_at rsegs mem2 (fs_flag (lib.Reusable.YG0f.ly_F lyc) 1 pos) (Z_to_bv 8 1 :: nil) /\
  0 <= pos < fs_M 1.
Proof.
  (* --- facts from the journals and the stack frame --- *)
  pose proof P1 as P1c.
  destruct P1c as (HARc & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HastkC & _ & _).
  pose proof HJ1 as HJ1c.
  destruct HJ1c as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresM1 & _ & _ & _).
  pose proof HJ2 as HJ2c.
  destruct HJ2c as (HAR2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HpresM2 & _ & _ & _).
  destruct HastkC as (_ & _ & Hceil_lo & Hlo_sp & Hsp_hi & Hhi_47 & _ & _ & _).
  pose proof lib.Reusable.YM05.alloc_ceiling_val as [Hcv1 Hcv2].
  pose proof HKEPT as HKEPTc.
  destruct HKEPTc as (KA1 & KA2 & KA3 & _ & _ & _).
  (* --- numerics --- *)
  assert (Hceil_S : lib.Reusable.YM05.alloc_ceiling <= S - 9072) by lia.
  assert (Hc64 : (2:Z) ^ 64 = 18446744073709551616) by (vm_compute; reflexivity).
  assert (Happ47 : APPMEM_END = 2 ^ 47) by (vm_compute; reflexivity).
  assert (H4764 : (2:Z) ^ 47 < 2 ^ 64) by (vm_compute; reflexivity).
  assert (HAE' : S <= APPMEM_END) by (rewrite Happ47; lia).
  assert (HS' : S < 2 ^ 64) by lia.
  assert (HSK' : 9072 <= S) by lia.
  assert (HHM' : HIGHMEM_BEG <= S - 9072) by (unfold HIGHMEM_BEG; lia).
  assert (HrAbnd : S - 144 <= rA S <= S - 128) by (unfold rA; pose proof S16; Z.div_mod_to_equations; lia).
  (* --- ro_agree mem2: the 4th part of the cut's ctl_rt_C --- *)
  assert (ROmem2 : B.MemNorm.ro_agree rsegs mem2) by exact (proj2 (proj2 (proj2 HRT2))).
  (* --- stk of the window --- *)
  assert (Hstk : lib.Lib.Frame.stk rsegs mem2 (S - 9072) S).
  { apply (B.ProgWorldAstack.pwfs_stk_of_present W mem2 (S - 9072) S); [lia | lia |].
    intros a Ha. apply HpresM2. lia. }
  (* --- the frame facts after __asan_stack_malloc_1, by ctl_fs_of_astack at cid 1 --- *)
  pose proof HECP as HECPc.
  destruct HECPc as (HARecp & Hret & Hsp16 & HlyESP & Hsphi & Hpres_ecp & Hgp & Htp).
  assert (Hfb1 : lib.Reusable.YG00.fs_frame_bytes 1 = 128) by (vm_compute; reflexivity).
  assert (HFS := B.ProgWorldAstack.ctl_fs_of_astack B 1 B.ProgWorld.ctl_fs_geom LAWS ltac:(lia)
                   lyc Sc S2 W regs regs2 m1 mem2 mdc1 md2 pos (lib.Reusable.YG0d.spZ regs - lib.Reusable.YG0d.ESTACK) 128
                   HECP ltac:(lia) ltac:(lia)
                   ltac:(intros a Ha; exfalso; lia) HFR HNI HAR2 H10 HZ HFL HPRESW HFRCOND ltac:(rewrite Hfb1; lia)).
  cbv zeta in HFS. change (Z.to_nat 1) with 1%nat in HFS.
  assert (HfB1 : fs_B 1 = 128) by (vm_compute; reflexivity).
  destruct HFS as (Hjj0 & _ & HflagB & HwordB & _ & _ & _ & _ & _ & _ & _ & _ & _).
  assert (FL1' : lib.Lib.Mem.bytes_at rsegs mem2 (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + 120)
                   (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag (lib.Reusable.YG0f.ly_F lyc) 1 pos)))).
  { replace (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + 120)
       with (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + fs_B 1 - 8) by (rewrite HfB1; lia).
    exact HwordB. }
  (* --- rSAVES at S - 104, transported mc -> mem2 over [S - 104, S) --- *)
  pose proof HR as HRc.
  destruct HRc as (MU & _ & _ & _ & _ & _ & _ & _ & _ & SVmc & _).
  pose proof HREL as HRELc. destruct HRELc as [REL1 REL2].
  assert (SVmem2 : lib.Lib.Step.rw_cells rsegs mem2 (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)).
  { apply (rrB_rw_cong mc mem2 (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)); [|exact SVmc].
    intros i Hi.
    assert (Hcs : Z.of_nat (lib.Lib.Cells.cells_size (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11)) = 104)
      by (vm_compute; reflexivity).
    rewrite Hcs in Hi.
    set (aa := S - 104 + i).
    assert (Haabnd : lib.Reusable.YM05.alloc_ceiling <= aa < 2 ^ 64) by (unfold aa; lia).
    assert (Haawin : ~ (sp0 + (rA S - sp0) - lib.Reusable.YG0d.ESTACK <= aa < sp0 + (rA S - sp0)))
      by (unfold aa, lib.Reusable.YG0d.ESTACK; lia).
    assert (Hp2 : lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 aa) by (apply HpresM2; unfold aa; lia).
    assert (Hp1 : lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) m1 aa) by (apply HpresM1; unfold aa; lia).
    destruct Hp2 as [Hh2 [b2 Hb2]]. destruct Hp1 as [Hh1 [b1 Hb1]].
    pose proof (KA1 aa Haabnd Haawin) as Hav.
    assert (Hmem21 : mem2 (Z_to_bv 64 aa) = m1 (Z_to_bv 64 aa))
      by (apply (rrB_mem_of_aview_eq W m1 mem2 aa);
          [exact Hav | exact Hh2 | exists b2; exact Hb2 | exists b1; exact Hb1]).
    assert (Hro0 : lib.Lib.Mem.ro_addr rsegs (Z_to_bv 64 aa) = false).
    { replace (Z_to_bv 64 aa) with (lib.Lib.Mem.wa aa) by reflexivity.
      apply B.MemNormTr.ro_addr_above_img. unfold ImgBounds.IMG_HI, aa.
      unfold HIGHMEM_BEG in HHM'. lia. }
    pose proof (REL1 (Z_to_bv 64 aa)) as Hmc. unfold B.MemNorm.normalize in Hmc. rewrite Hro0 in Hmc.
    rewrite Hmem21, <- Hmc. reflexivity. }
  (* --- m1 = memc off the window --- *)
  assert (rrB_OFF : forall x : word, ~ (S - 9072 <= bv_unsigned x < S) -> m1 x = memc x).
  { intros x Hx. destruct (lib.Lib.Mem.ro_addr rsegs x) eqn:R.
    - exact (HROS x R).
    - pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
      assert (Hout : lib.Lib.Frame.outside ((S - 9072, S) :: nil) (bv_unsigned x))
        by (cbn [lib.Lib.Frame.outside]; split; [exact Hx | exact I]).
      pose proof (MU x Hout) as E2. unfold B.MemNorm.normalize in E2. rewrite R in E2.
      rewrite <- E1, E2. reflexivity. }
  (* --- cell separation facts (blocks vs frames, frames below the ceiling) --- *)
  destruct (lib.Reusable.YG0d.al_sep _ _ LAWS lyc Sc W memc mdc HARc) as [HsepPW HsepF].
  (* --- HF: the message at fr, and the three caller cells apart from it (P10's block vs P11's frames) --- *)
  assert (HFproof : reply_args fr pa pp pn = true -> 50 <= len ->
     fr + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs mem2 fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
     (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)).
  { intros RA Hge. destruct (P10 RA Hge) as ((nb & Hin_frnb & Hreq) & Hgarr).
    destruct (lib.Reusable.YG0d.al_blocks _ _ LAWS lyc Sc W memc mdc fr nb HARc Hin_frnb)
      as (_ & Hfr4096 & Hfrceil & _ & _ & _ & _).
    assert (Hfr50 : fr + 50 <= S - 9072) by lia.
    assert (Hfrapart : (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\
                       (pn + 8 <= fr \/ fr + 50 <= pn)).
    { destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & Hframe & _ & _ & _).
      assert (Hfr_byte : forall x, C_reac_ctrl_identity_reply.treply_out pa pp pn x -> x < fr \/ fr + 50 <= x).
      { intros x Hx. destruct (Hframe x Hx) as ((cid & pos0 & Hin_sc & Hinzr) & _).
        unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr in Hinzr. cbn [fst snd] in Hinzr.
        assert (InBlk : In (fr, lib.Reusable.YG00.req_size nb)
                  (map (fun b => (fst b, lib.Reusable.YG00.req_size (snd b))) (lib.Reusable.YG0d.ablocks B lyc Sc))).
        { change (fr, lib.Reusable.YG00.req_size nb)
            with ((fun b => (fst b, lib.Reusable.YG00.req_size (snd b))) (fr, nb)).
          apply in_map. exact Hin_frnb. }
        assert (InFrm : In (lib.Reusable.YG0f.frame_addr lyc cid pos0, lib.Reusable.YG00.fs_frame_bytes cid)
                  (map (fun f => (lib.Reusable.YG0f.frame_addr lyc (fst f) (snd f), lib.Reusable.YG00.fs_frame_bytes (fst f)))
                     (lib.Reusable.YG01.frames Sc))).
        { change (lib.Reusable.YG0f.frame_addr lyc cid pos0, lib.Reusable.YG00.fs_frame_bytes cid)
            with ((fun f => (lib.Reusable.YG0f.frame_addr lyc (fst f) (snd f), lib.Reusable.YG00.fs_frame_bytes (fst f)))
                    (cid, pos0)).
          apply in_map. exact Hin_sc. }
        pose proof (rrB_pw_cross lib.Reusable.YG0f.zdisjoint _ _ _ _ HsepPW InBlk InFrm) as Hzd.
        unfold lib.Reusable.YG0f.zdisjoint in Hzd. cbn [fst snd] in Hzd. lia. }
      pose proof (Hfr_byte pa ltac:(unfold C_reac_ctrl_identity_reply.treply_out; left; lia)) as Hpa0.
      pose proof (Hfr_byte (pa + 1) ltac:(unfold C_reac_ctrl_identity_reply.treply_out; left; lia)) as Hpa1.
      pose proof (Hfr_byte pp ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; left; lia)) as Hpp0.
      pose proof (Hfr_byte (pp + 7) ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; left; lia)) as Hpp7.
      pose proof (Hfr_byte pn ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; right; lia)) as Hpn0.
      pose proof (Hfr_byte (pn + 7) ltac:(unfold C_reac_ctrl_identity_reply.treply_out; right; right; lia)) as Hpn7.
      split; [lia|]. split; lia. }
    split; [lia|]. split; [|split; [lia | exact Hfrapart]].
    apply (B.ProgWorldAstack.pwfs_bytes_of_view W mem2 fr g);
      [lia | rewrite Hg; change (Z.of_nat 50) with 50; lia |].
    intros i Hi.
    assert (HiZ50 : Z.of_nat i < 50).
    { assert (Hii : (i < 50)%nat) by (rewrite Hg in Hi; exact Hi). lia. }
    destruct (nth_error g i) as [b0|] eqn:Eb; [|exfalso; apply nth_error_None in Eb; lia].
    exists b0. split; [reflexivity|]. change lib.Reusable.YB1v.tfibsegs with rsegs.
    assert (Hilt : (i < length (map (fun bb : byte => bv_unsigned bb) g))%nat) by (rewrite map_length; exact Hi).
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
    assert (HiZreq : Z.of_nat i < lib.Reusable.YG00.req_size nb) by lia.
    pose proof (KA2 fr nb (Z.of_nat i) Hin_frnb ltac:(lia) ltac:(intros HH; exact HH)) as Hk2.
    assert (Hoffpt : m1 (Z_to_bv 64 (fr + Z.of_nat i)) = memc (Z_to_bv 64 (fr + Z.of_nat i)))
      by (apply rrB_OFF; rewrite rrB_u64 by lia; lia).
    pose proof (rrB_aview_point W m1 memc (fr + Z.of_nat i) Hoffpt) as Hpt.
    rewrite Hk2, Hpt, Havc. reflexivity. }
  (* --- HO --- *)
  assert (HOproof : exists ja jp jn : list byte,
     reply_args fr pa pp pn = true ->
       pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
       lib.Lib.Step.rw_cells rsegs mem2 pa (lib.Lib.Cells.CB 2 ja :: nil) /\
       lib.Lib.Step.rw_cells rsegs mem2 pp (lib.Lib.Cells.CB 8 jp :: nil) /\
       lib.Lib.Step.rw_cells rsegs mem2 pn (lib.Lib.Cells.CB 8 jn :: nil) /\
       (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
       (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)).
  { exists (rrB_rd mem2 pa 2), (rrB_rd mem2 pp 8), (rrB_rd mem2 pn 8). intros RA.
    destruct (P11 RA) as (Hm2 & Hm8p & Hm8n & Happp & Happn & Hpppn & Hframe & _ & _ & _).
    assert (Hcellpres : forall x, C_reac_ctrl_identity_reply.treply_out pa pp pn x -> mem2 (Z_to_bv 64 x) <> None).
    { intros x Hx. destruct (Hframe x Hx) as ((cid & pos0 & Hin_sc & Hinzr) & _).
      unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr in Hinzr. cbn [fst snd] in Hinzr.
      assert (Hin2 : In (cid, pos0) (lib.Reusable.YG01.frames S2)) by (rewrite HFR; right; exact Hin_sc).
      destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc S2 W mem2 md2 cid pos0 HAR2 Hin2) as (_ & _ & Hfpres & _).
      destruct (Hfpres x Hinzr) as [[_ [b Hb]] _]. rewrite Hb. discriminate. }
    assert (Hcell_lt_ceil : forall x, C_reac_ctrl_identity_reply.treply_out pa pp pn x ->
                              x < lib.Reusable.YM05.alloc_ceiling).
    { intros x Hx. destruct (Hframe x Hx) as ((cid & pos0 & Hin_sc & Hinzr) & _).
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
    { apply rrB_rw_present; [lia | change (Z.of_nat 2) with 2; lia |].
      intros i Hi. change (Z.of_nat 2) with 2 in Hi. apply Hcellpres.
      unfold C_reac_ctrl_identity_reply.treply_out. left. lia. }
    split.
    { apply rrB_rw_present; [lia | change (Z.of_nat 8) with 8; lia |].
      intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply Hcellpres.
      unfold C_reac_ctrl_identity_reply.treply_out. right. left. lia. }
    split.
    { apply rrB_rw_present; [lia | change (Z.of_nat 8) with 8; lia |].
      intros i Hi. change (Z.of_nat 8) with 8 in Hi. apply Hcellpres.
      unfold C_reac_ctrl_identity_reply.treply_out. right. right. lia. }
    split; [exact Happp|]. split; [exact Happn|]. split; [exact Hpppn|].
    split; [lia|]. split; lia. }
  (* --- HOimg --- *)
  assert (HOimgproof : reply_args fr pa pp pn = true ->
     ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn).
  { intros RA. destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & Hframe & _ & _ & _).
    assert (Hge_img : forall x, C_reac_ctrl_identity_reply.treply_out pa pp pn x -> ImgBounds.IMG_HI <= x).
    { intros x Hx. destruct (Hframe x Hx) as ((cid & pos0 & Hin_sc & Hinzr) & _).
      unfold lib.Reusable.YCbq.frame_rng, lib.Reusable.YG0n.in_zr in Hinzr. cbn [fst snd] in Hinzr.
      pose proof (B.ProgWorld_Fs.ctl_frame_above_img B lyc Sc W memc mdc cid pos0 HARc Hin_sc) as Hab.
      unfold ImgBounds.IMG_HI. lia. }
    split; [apply Hge_img; unfold C_reac_ctrl_identity_reply.treply_out; left; lia|].
    split; [apply Hge_img; unfold C_reac_ctrl_identity_reply.treply_out; right; left; lia
           |apply Hge_img; unfold C_reac_ctrl_identity_reply.treply_out; right; right; lia]. }
  (* --- assemble --- *)
  refine (conj Rfr (conj Rlen (conj Rpa (conj Rpp (conj Rpn (conj HS' (conj S16 (conj HSK'
          (conj ROmem2 (conj Hstk (conj Hg (conj HFproof (conj HOproof (conj HOimgproof
          (conj HHM' (conj HAE' (conj SVmem2 (conj FL1' (conj HflagB Hjj0))))))))))))))))))).
Qed.

(* ---- The composition.  a Theorem Labs lane's view half (C_reac_ctrl_identity_replyBaseV.rrB_SB_base_vis) needs these Section
   facts besides the shared header and HRT2; each is copied verbatim from that file, so the closed lemma's arguments
   line up.  The ProgWorld statements fp_tls_apart_stmt / ctl_block_apart_fs_stmt are PROVED and cited there
   (B.ProgWorldTlsApart.fp_tls_apart, B.ProgWorldBlkApart.ctl_block_apart_fs), not carried. ---- *)
Hypothesis P4tp : tp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B).
Hypothesis HAB : lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc.
(* SPEC GAP, a Theorem Labs lane; approved text (C_reac_ctrl_identity_replyBaseV.v); the composition gives it from the
   spec's P11 conjunct cid <> 1 *)
Hypothesis CELLS_NOT_C1 : reply_args fr pa pp pn = true -> forall a cid pos,
  C_reac_ctrl_identity_reply.treply_out pa pp pn a -> In (cid, pos) (lib.Reusable.YG01.frames Sc) ->
  lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) -> cid <> 1.

(* rrB_SB_base: every premise of rrB_SB_lifted except wx_segs_nowrap and its continuation K, in rrB_SB_lifted's own
   order, at mb := mem2, FS := ly_F lyc, jj := pos, with ja jp jn the bytes of the three cells at mem2.  The memory half
   is rrB_SB_base_mem (this file); the view / footprint half is a Theorem Labs lane's rrB_SB_base_vis. *)
Lemma rrB_SB_base :
  exists ja jp jn : list byte,
  (0 <= fr < 2 ^ 64) /\ (0 <= len < 2 ^ 64) /\ (0 <= pa < 2 ^ 64) /\ (0 <= pp < 2 ^ 64) /\ (0 <= pn < 2 ^ 64) /\
  S < 2 ^ 64 /\ S mod 16 = 0 /\ 9072 <= S /\
  B.MemNorm.ro_agree rsegs mem2 /\
  lib.Lib.Frame.stk rsegs mem2 (S - 9072) S /\
  length g = 50%nat /\
  (reply_args fr pa pp pn = true -> 50 <= len ->
     fr + 50 <= 2 ^ 64 /\ lib.Lib.Mem.bytes_at rsegs mem2 fr g /\ (fr + 50 <= S - 9072 \/ S <= fr) /\
     (pa + 2 <= fr \/ fr + 50 <= pa) /\ (pp + 8 <= fr \/ fr + 50 <= pp) /\ (pn + 8 <= fr \/ fr + 50 <= pn)) /\
  (reply_args fr pa pp pn = true ->
     pa mod 2 = 0 /\ pp mod 8 = 0 /\ pn mod 8 = 0 /\
     lib.Lib.Step.rw_cells rsegs mem2 pa (lib.Lib.Cells.CB 2 ja :: nil) /\
     lib.Lib.Step.rw_cells rsegs mem2 pp (lib.Lib.Cells.CB 8 jp :: nil) /\
     lib.Lib.Step.rw_cells rsegs mem2 pn (lib.Lib.Cells.CB 8 jn :: nil) /\
     (pa + 2 <= pp \/ pp + 8 <= pa) /\ (pa + 2 <= pn \/ pn + 8 <= pa) /\ (pp + 8 <= pn \/ pn + 8 <= pp) /\
     (pa + 2 <= S - 9072 \/ S <= pa) /\ (pp + 8 <= S - 9072 \/ S <= pp) /\ (pn + 8 <= S - 9072 \/ S <= pn)) /\
  (reply_args fr pa pp pn = true ->
     ImgBounds.IMG_HI <= pa /\ ImgBounds.IMG_HI <= pp /\ ImgBounds.IMG_HI <= pn) /\
  shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S (lib.Reusable.YG0f.ly_F lyc)) mem2 /\
  HIGHMEM_BEG <= S - 9072 /\ S <= APPMEM_END /\
  addressable mem2 (S - 9072) 9072 /\
  (reply_args fr pa pp pn = true -> 50 <= len -> addressable mem2 fr 50) /\
  (reply_args fr pa pp pn = true ->
     addressable mem2 pa 2 /\ addressable mem2 pp 8 /\ addressable mem2 pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) /\
  RcAsanFP.fp [1%nat] mem2 (bv_unsigned tp) (lib.Reusable.YG0f.ly_F lyc) (S - 9072) S
    (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) /\
  reac_ctrl_identity_reply_tls mem2 (bv_unsigned tp) (lib.Reusable.YG0f.ly_F lyc) (S - 9072) S /\
  lib.Lib.Step.rw_cells rsegs mem2 (S - 104) (rSAVES ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11) /\
  lib.Lib.Mem.bytes_at rsegs mem2 (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + 120)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag (lib.Reusable.YG0f.ly_F lyc) 1 pos))) /\
  lib.Lib.Mem.bytes_at rsegs mem2 (fs_flag (lib.Reusable.YG0f.ly_F lyc) 1 pos) (Z_to_bv 8 1 :: nil) /\
  0 <= pos < fs_M 1 /\
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (S - 9072) 9072 /\
  shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (S - 9072) 9072 /\
  (reply_args fr pa pp pn = true -> 50 <= len ->
     lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) /\
  (reply_args fr pa pp pn = true -> 50 <= len -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) /\
  (reply_args fr pa pp pn = true -> 50 <= len -> shkov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) fr 50) /\
  (reply_args fr pa pp pn = true -> lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pa 2) /\
  (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pa 2) /\
  (reply_args fr pa pp pn = true -> lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pp 8) /\
  (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pp 8) /\
  (reply_args fr pa pp pn = true -> lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pn 8) /\
  (reply_args fr pa pp pn = true -> shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) pn 8) /\
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
    (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 0)
    (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 (fs_M 1) - fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 0) /\
  shcov (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 0)
    (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 (fs_M 1) - fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 0).
Proof.
  destruct rrB_SB_base_mem as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & (ja & jp & jn & M13)
    & M14 & M15 & M16 & M17 & M18 & M19 & M20).
  destruct (C_reac_ctrl_identity_replyBaseV.rrB_SB_base_vis B LAWS TS STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W
              memc mdc k ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 fr len pa pp pn S g P1 P4tp HSlo HShi P10 P11
              m1 mc HR HREL HROS S2 mem2 md2 pos HJ2 HAB HKEPT HRT2 CELLS_NOT_C1)
    as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13 & V14 & V15 & V16 & V17 & V18 & V19).
  exists ja, jp, jn.
  split; [exact M1|]. split; [exact M2|]. split; [exact M3|]. split; [exact M4|]. split; [exact M5|].
  split; [exact M6|]. split; [exact M7|]. split; [exact M8|]. split; [exact M9|]. split; [exact M10|].
  split; [exact M11|]. split; [exact M12|]. split; [exact M13|]. split; [exact M14|].
  split; [exact V1|]. split; [exact M15|]. split; [exact M16|].
  split; [exact V2|]. split; [exact V3|]. split; [exact V4|]. split; [exact V5|]. split; [exact V6|].
  split; [exact M17|]. split; [exact M18|]. split; [exact M19|]. split; [exact M20|].
  split; [exact V7|]. split; [exact V8|]. split; [exact V9|]. split; [exact V10|]. split; [exact V11|].
  split; [exact V12|]. split; [exact V13|]. split; [exact V14|]. split; [exact V15|]. split; [exact V16|].
  split; [exact V17|]. split; [exact V18|]. exact V19.
Qed.

End Base.
