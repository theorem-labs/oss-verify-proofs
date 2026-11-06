(* lib/B/Prog/C_reac_ctrl_identity_replyBaseV.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the VIEW half
   of rrB_SB_base, the base facts of the stretch S-B of reac_ctrl_identity_reply (0x848fc) after the class-1 fake-stack
   request E1.  Split by a Theorem Labs lane (2026-10-29): this file (a Theorem Labs lane) gives rrB_SB_base_vis, the footprint / view /
   runtime premises of rrB_SB_lifted (lib/B/Prog/C_reac_ctrl_identity_replyPf.v) at mb := mem2, FS := ly_F lyc;
   C_reac_ctrl_identity_replyBase.v (a Theorem Labs lane) gives the memory half and composes rrB_SB_base by Requiring this file.
   The Section header below is the SHARED one (replybase-shared-header.v (not in this delivery)),
   pasted verbatim for the entry cut, S-A and E1 (route (C) removed VIS0 / OWNRO and added HRT2); C_reac_ctrl_identity_replyBase.v leaves P4gp / P4tp out of its header and has its own E1 block, so both closed lemmas take the other entry-cut and S-A arguments in the same order.

   rrB_SB_base_vis's conclusion is the conjunction, in rrB_SB_lifted's order, of: shadow_rw_on
   (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S (ly_F lyc)) mem2 (route (C)); addressable of the window, of the
   message (fr, 50) and of the three cells with their RT_LO / RT_HI apartness; fp [1%nat] mem2 .. and
   reac_ctrl_identity_reply_tls mem2 ..; the 13 footprint premises at RNG_W (w_H W) (window, message, cells, class-1
   frames and their shadow covers).

   PROVED image-B lemmas used:
     the cut's ctl_rt_C (HRT2, supplied at the composition by B.ProgWorldCtlRtC.ctl_rt_C_of_AR at the journal's AR)
       and C_reac_ctrl_identity_replyCover.rrC_R_on                     shadow_rw_on (R ..) mem2 (route (C))
     B.ProgWorldShadow.ctl_stack_shadow_of_AR (lib/B/ProgWorldShadow.v:135) addressable mem2 (S - 9072) 9072
     B.ProgWorldShadow.ctl_block_shadow_of_AR (lib/B/ProgWorldShadow.v:85)  addressable mem2 fr 50
     B.ProgWorld_Fs.ctl_fp_of_AR (lib/B/ProgWorld_Fs.v:407)               fp [1%nat] mem2 ..
     B.ProgWorld_Fs.pw_F_above (:267), pw_F_present (:292), pw_view_mrd (:72), pw_u64 (:49)
     B.ProgWorld.as_tp_RT_TP (lib/B/ProgWorld.v:893), as_tsd_TSD (:1206)
     B.ProgWorldVisWin.win_sh_vis (lib/B/ProgWorldVisWin.v:69)            the window's shadow cover
     B.ProgWorldVisHeap.heap_vis (:43), heap_sh_vis (:53)                  the message and its shadow covers
     B.ProgWorldVisFrame.vis_of_aview (lib/B/ProgWorldVisFrame.v:39)       the class-1 frames' shadow (am_areas)
     B.ProgWorldTlsApart.fp_tls_apart, B.ProgWorldBlkApart.ctl_block_apart_fs (the ProgWorld statements
       fp_tls_apart_stmt / ctl_block_apart_fs_stmt, cited, not assumed)
     B.ProgBridge.rng_of_visible (:57), range_visible_sub (:126)
     core: YG0d.al_frames / al_blocks (AR_frames_law / AR_blocks_law, YG0d.v:423-455, the law frame_vis uses),
           YCbq.acall_kept's frame-shadow clause (YCbq.v:831-833), YG01.wfs_live (YG01.v:313).
   win_vis (ProgWorldVisWin.v:52) is NOT applied: win_vis_stmt fixes the journal's sink_head to
   lib.Reusable.YE2k.tfib_sink_head (lib/B/ProgWorld.v:62), while the glue's journal HJ2 carries the Section's SK;
   rb_RWIN uses the same two journal conjuncts win_vis's proof uses (YCbq.v:368-369: presence and astk_ok).
   The cell bytes' shadow at mem2 is P11's shadow at memc, carried memc -> m1 off the S-A window (rMCALL's munch,
   mem_rel, ro_same) and m1 -> mem2 by E1's acall_kept on the shadow of the caller frame that holds the cell.

   NAMED Section hypotheses of this file (besides the shared header's): CELLS_NOT_C1 (SPEC GAP; the composition
   gives it from the spec's P11 conjunct cid <> 1) and HRT2 (the cut's ctl_rt_C).  rule 24:
   lookup-reac_ctrl_identity_reply.txt (a working note, not in this delivery), checker CONFIRM; At ossv/recipes c5e779efe8c (2026-10-31), no released proof outside this unit; written new. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT ShadowRwOn.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import asan_stack_malloc_c reac_ctrl_identity_reply_c
  reac_ctrl_identity_reply_c_on reac_ctrl_identity_replyRB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require ExecF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YA0n YG00 YG01 YG0f YG0n YG0d YG0v YCbq YI00 YF0m.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YP09.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm ProgBridge ProgWorld ProgWorld_Fs.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldShadow ProgWorldVisWin ProgWorldVisHeap ProgWorldVisFrame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgWorldTlsApart ProgWorldBlkApart ACtlRtC.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require rng_asan C_reac_ctrl_identity_reply
  C_reac_ctrl_identity_replyCover.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanFP.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcReply.
Import ListNotations.
Open Scope Z_scope.

(* ---- closed arithmetic ---- *)
Lemma rb_bv_signed8 : forall s, 0 <= s < 8 -> bv_signed (Z_to_bv 8 s) = s.
Proof.
  intros s Hs. assert (H : s = 0 \/ s = 1 \/ s = 2 \/ s = 3 \/ s = 4 \/ s = 5 \/ s = 6 \/ s = 7) by lia.
  destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; vm_compute; reflexivity.
Qed.

Lemma rb_sh_bound : forall x, 0 <= x < 0x7fffff800000 -> 0 <= x / 8 + ASAN_K /\ x / 8 + ASAN_K + 1 <= 2 ^ 64.
Proof.
  intros x Hx. unfold ASAN_K.
  assert (H0 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (H1 : x / 8 <= x) by (apply Z.div_le_upper_bound; lia).
  lia.
Qed.

(* the shadow byte of x lies in the 8-aligned shadow word cover of [p, p + n) (rng_asan.v:82-83) *)
Lemma rb_sh_al8_in : forall p n x, p <= x < p + n ->
  B.Prog.rng_asan.sh_al8_lo p <= x / 8 + ASAN_K /\ x / 8 + ASAN_K + 1 <= B.Prog.rng_asan.sh_al8_hi p n.
Proof.
  intros p n x Hx. unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, shadow_addr.
  assert (M1 : p / 8 <= x / 8) by (apply Z.div_le_mono; lia).
  assert (M2 : x / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  pose proof (Z.div_mod (p / 8 + ASAN_K) 8 ltac:(lia)) as D1.
  pose proof (Z.mod_pos_bound (p / 8 + ASAN_K) 8 ltac:(lia)) as R1.
  pose proof (Z.div_mod ((p + n - 1) / 8 + ASAN_K) 8 ltac:(lia)) as D2.
  pose proof (Z.mod_pos_bound ((p + n - 1) / 8 + ASAN_K) 8 ltac:(lia)) as R2.
  lia.
Qed.

(* shkov's aligned range for a <= b inside [p, p + n) lies in the same cover *)
Lemma rb_sh_al8_kov : forall p n a b, p <= a -> a <= b -> b < p + n ->
  B.Prog.rng_asan.sh_al8_lo p <= (a / 8 + ASAN_K) / 8 * 8 /\
  0 <= (b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8 /\
  (a / 8 + ASAN_K) / 8 * 8 + ((b / 8 + ASAN_K) / 8 * 8 + 8 - (a / 8 + ASAN_K) / 8 * 8) <=
    B.Prog.rng_asan.sh_al8_hi p n.
Proof.
  intros p n a b H1 H2 H3. unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, shadow_addr.
  assert (M1 : p / 8 <= a / 8) by (apply Z.div_le_mono; lia).
  assert (M2 : a / 8 <= b / 8) by (apply Z.div_le_mono; lia).
  assert (M3 : b / 8 <= (p + n - 1) / 8) by (apply Z.div_le_mono; lia).
  assert (N1 : (p / 8 + ASAN_K) / 8 <= (a / 8 + ASAN_K) / 8) by (apply Z.div_le_mono; lia).
  assert (N2 : (a / 8 + ASAN_K) / 8 <= (b / 8 + ASAN_K) / 8) by (apply Z.div_le_mono; lia).
  assert (N3 : (b / 8 + ASAN_K) / 8 <= ((p + n - 1) / 8 + ASAN_K) / 8) by (apply Z.div_le_mono; lia).
  lia.
Qed.

Lemma rb_shb : forall F, 0 <= F -> F + 11571200 <= 0x7fffff800000 ->
  0x7fff8000 <= shadow_addr (F + 1085440) /\ shadow_addr (F + 2134016) <= 0x10007ff78000.
Proof.
  intros F H0 H1. unfold shadow_addr, ASAN_K.
  assert (A0 : 0 <= (F + 1085440) / 8) by (apply Z.div_pos; lia).
  assert (A1 : (F + 2134016) / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia).
  assert (E : 0x7fffff800000 / 8 = 0xffffff00000) by reflexivity. rewrite E in A1. lia.
Qed.

(* ctrl's class-1 side-stack numerals (asan_stack_malloc_c.v:26-31; rrF_fs_frame1, reac_ctrl_identity_replyRB.v:179) *)
Lemma rb_fs1 : forall FS, fs_frame FS 1 0 = FS + 1085440 /\ fs_frame FS 1 (fs_M 1) = FS + 2134016 /\
  fs_hint FS 1 = FS + 8 /\ fs_flag FS 1 0 = FS + 20480 /\ fs_M 1 = 8192 /\ fs_frame FS 0 0 = FS + 36864.
Proof.
  intros FS. rewrite !rrF_fs_frame1. assert (EM : fs_M 1 = 8192) by reflexivity. rewrite EM.
  split; [lia|]. split; [lia|].
  split; [unfold fs_hint; change (Z.of_nat 1) with 1; lia|].
  split; [unfold fs_flag; change (Z.of_nat 1) with 1; change (2 ^ 15) with 32768; change (2 ^ (15 - 1)) with 16384;
          lia|].
  split; [reflexivity|]. unfold fs_frame. change (Z.of_nat 0) with 0. lia.
Qed.

(* A live fake frame of class cid (0 <= cid <= 10, AR's Wf) lies in its class's 1 MiB band of the side stack. *)
Lemma rb_frame_geom : forall (ly : lib.Reusable.YG0f.alayout) cid q,
  0 <= cid <= 10 -> 0 <= q < lib.Reusable.YG00.fs_frames cid ->
  lib.Reusable.YG0f.ly_F ly + 36864 + cid * 1048576 <= lib.Reusable.YG0f.frame_addr ly cid q /\
  lib.Reusable.YG0f.frame_addr ly cid q + lib.Reusable.YG00.fs_frame_bytes cid <=
    lib.Reusable.YG0f.ly_F ly + 36864 + (cid + 1) * 1048576 /\
  lib.Reusable.YG00.fs_frame_bytes cid mod 8 = 0 /\ 8 <= lib.Reusable.YG00.fs_frame_bytes cid.
Proof.
  intros ly cid q Hc Hq.
  assert (E : Z.shiftl 64 cid * Z.shiftl 1 (lib.Reusable.YG00.kStackSizeLog - 6 - cid) = 1048576 /\
              Z.shiftl 64 cid mod 8 = 0 /\ 8 <= Z.shiftl 64 cid).
  { assert (H : cid = 0 \/ cid = 1 \/ cid = 2 \/ cid = 3 \/ cid = 4 \/ cid = 5 \/ cid = 6 \/ cid = 7 \/ cid = 8 \/
                cid = 9 \/ cid = 10) by lia.
    destruct H as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]];
      (split; [reflexivity | split; [reflexivity | apply Z.leb_le; reflexivity]]). }
  unfold lib.Reusable.YG0f.frame_addr, lib.Reusable.YG0f.fs_frame_off, lib.Reusable.YG0f.kFakeFramesOff.
  unfold lib.Reusable.YG00.fs_frames in Hq. unfold lib.Reusable.YG00.fs_frame_bytes.
  change (Z.shiftl 1 lib.Reusable.YG00.kStackSizeLog) with 1048576.
  destruct E as (E1 & E2 & E3).
  set (k := Z.shiftl 64 cid) in *. set (nf := Z.shiftl 1 (lib.Reusable.YG00.kStackSizeLog - 6 - cid)) in *.
  assert (Hk : (q + 1) * k <= nf * k) by (apply Z.mul_le_mono_nonneg_r; lia).
  split; [nia | split; [nia | split; [exact E2 | exact E3]]].
Qed.

Lemma rb_in_app_ceil {rc : lib.Reusable.YM05.RunCeil} : forall lo len, lib.Reusable.YG0f.in_app lo len ->
  4096 <= lo /\ lo + len <= lib.Reusable.YG0f.ASAN_CEIL.
Proof.
  intros lo len [H0 H]. pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 _] _].
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in H. lia.
Qed.

Lemma rb_rng1 : forall (H : word -> bool) x, 0 <= x -> x + 1 <= 2 ^ 64 -> H (Z_to_bv 64 x) = false ->
  lib.Lib.ExecF.rng (B.ProgBridge.RNG_W H) x 1.
Proof.
  intros H x H0 H1 Hv. apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
  intros a Ha. replace a with x by lia. exact Hv.
Qed.

Section Base.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
Hypothesis TS : lib.Reusable.YF0m.CtrlTSyms B.

(* ---- the spec's cut at the entry (lib/B/Prog/C_reac_ctrl_identity_reply.v, P1 P4 P5 P7 P9 P10 P11) ---- *)
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : lib.Reusable.YG0f.alayout) (S0 : lib.Reusable.YG00.astate)
  (W0 : lib.Reusable.YA0n.world rsegs) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (W : lib.Reusable.YA0n.world rsegs)
  (memc : word -> option byte) (mdc : Model) (k : Z)
  (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (fr len pa pp pn S : Z) (g : list byte).
Hypothesis P1 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis P4gp : gp = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_gp B).
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

(* ---- S-A: the continuation of rrB_to_E1 (C_reac_ctrl_identity_replyPf.v) ---- *)
Variables (m1 mc : word -> option byte) (mdc1 : Model).
Hypothesis HR : rMCALL ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs memc) S mc.
Hypothesis HREL : B.MemNorm.mem_rel rsegs m1 mc.
Hypothesis HROS : B.MemNorm.ro_same rsegs memc m1.
Hypothesis HJ1 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 own lyc Sc W m1 mdc1 k.

(* ---- E1: the continuation of rrB_E1 (C_reac_ctrl_identity_replyPf.v) ---- *)
Variables (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word)
  (S2 : lib.Reusable.YG00.astate) (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) (pos : Z).
Hypothesis HJ2 : lib.Reusable.YCbq.ajournal rsegs B STK sp0 FP ly S0 W0 mem0 md0 ((1, pos) :: own) lyc S2 W mem2 md2 k.
Hypothesis HP : lib.Reusable.YG0d.aregs_preserved
  (lib.Lib.Frame.mkR (Z_to_bv 64 0x8497c) (Z_to_bv 64 (rA S)) gp tp t0 t1 t2 (Z_to_bv 64 S) (Z_to_bv 64 (rA S))
       (Z_to_bv 64 128) (lib.Lib.Mem.wa CELL_K) (lib.Lib.Mem.sx32 (lib.Lib.Mem.wa 1)) (Z_to_bv 64 pp) (Z_to_bv 64 pn) a5 a6 a7
       s2 (Z_to_bv 64 pn) (Z_to_bv 64 pp) (Z_to_bv 64 fr) (Z_to_bv 64 pa) (Z_to_bv 64 len)
       s8 s9 s10 (lib.Lib.Mem.wa ASAN_K) t3 t4 t5 t6) regs2.
Hypothesis H10 : lib.Reusable.YK11.getr regs2 10 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.frame_addr lyc 1 pos).
Hypothesis HAB : lib.Reusable.YG0d.ablocks B lyc S2 = lib.Reusable.YG0d.ablocks B lyc Sc.
Hypothesis HFR : lib.Reusable.YG01.frames S2 = (1, pos) :: lib.Reusable.YG01.frames Sc.
Hypothesis HNI : ~ In (1, pos) (lib.Reusable.YG01.frames Sc).
Hypothesis HNEV : lib.Reusable.YG00.st_nev S2 = lib.Reusable.YG00.st_nev Sc.
Hypothesis HBB : lib.Reusable.YG01.blocks_bytes S2 = lib.Reusable.YG01.blocks_bytes Sc.
Hypothesis HZ : lib.Reusable.YG0v.zero_shadow (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
  lib.Reusable.YG0f.SHADOW_OFF (lib.Reusable.YG0f.frame_addr lyc 1 pos) (lib.Reusable.YG00.fs_frame_bytes 1).
Hypothesis HFL : lib.Reusable.YG0d.rdword (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2)
  (lib.Reusable.YG0f.frame_addr lyc 1 pos + lib.Reusable.YG00.fs_frame_bytes 1 - 8) =
  Some (lib.Reusable.YG0f.flag_addr lyc 1 pos).
Hypothesis HKEPT : lib.Reusable.YCbq.acall_kept rsegs B lyc Sc W m1 W mem2
  (sp0 + (rA S - sp0) - lib.Reusable.YG0d.ESTACK) (sp0 + (rA S - sp0)) (fun _ => False).
(* ---- route (C): at the cut after the class-1 request the glue HAS ctl_rt_C at (lyc, S2, mem2); the composition
   supplies it by B.ProgWorldCtlRtC.ctl_rt_C_of_AR at HJ2's AR, which takes no ProgWorld statement ---- *)
Hypothesis HRT2 : B.ACtlRtC.ctl_rt_C B lyc S2 mem2.

(* ---- the interim hypothesis (a Theorem Labs lane 2026-10-29): ctl_fs_of_astack's conclusion at cid 1 (ProgWorld.v:497-508),
   regs' := regs2, mem' := mem2, ly := lyc, spZ regs := rA S (the call's sp), lo := S - 9072, L := 128 ---- *)
(* OWNER PENDING: lib.Reusable.YCbqMalloc.aj_stack_malloc_at_fc (core, a Theorem Labs lane 2026-10-29); the continuation of
   YCbq.aj_stack_malloc_at does not carry ecall_pre, astack_malloc_realizes' frame condition or the presence clauses,
   which B.ProgWorldAstack.ctl_fs_of_astack requires *)
Hypothesis H_aj_stack_malloc_at_fc :
  0 <= pos < fs_M 1 /\
  lib.Reusable.YK11.getr regs2 10 = Z_to_bv 64 (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos) /\
  lib.Lib.Mem.bytes_at rsegs mem2 (fs_flag (lib.Reusable.YG0f.ly_F lyc) 1 pos) (Z_to_bv 8 1 :: nil) /\
  lib.Lib.Mem.bytes_at rsegs mem2 (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + fs_B 1 - 8)
    (lib.Lib.Mem.le8 (Z_to_bv 64 (fs_flag (lib.Reusable.YG0f.ly_F lyc) 1 pos))) /\
  lib.Lib.Mem.bytes_at rsegs mem2 (shadow_addr (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos))
    (repeat (Z_to_bv 8 0) (Z.to_nat (fs_B 1 / 8))) /\
  addressable mem2 (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos) 128 /\
  lib.Lib.Frame.stk rsegs mem2 (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos)
    (fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + fs_B 1) /\
  (forall a, fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos <= a < fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + fs_B 1 ->
     app_mem a) /\
  fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos mod 64 = 0 /\
  lib.Reusable.YG0f.ly_F lyc <= fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos /\
  fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos + fs_B 1 <= lib.Reusable.YG0f.ly_F lyc + FS_SIZE /\
  ASAN_GT <= fs_frame (lib.Reusable.YG0f.ly_F lyc) 1 pos /\
  lib.Lib.Frame.stk rsegs mem2 (S - 9072) (rA S).
(* (fs_M fs_B fs_frame fs_flag FS_SIZE ASAN_GT = B.Prog.asan_stack_malloc_c.X; shadow_addr app_mem addressable =
   B.AsanRT.X -- spell them qualified in the file.) *)

(* ---- a Theorem Labs lane's own named hypotheses (approved by a Theorem Labs lane, 2026-10-29) ---- *)
(* SPEC GAP, 2026-10-29: FP0's fp_dj D (fp_w [1%nat] FS) (RcAsanFP.v:56, :29-32) needs the cell frames to be of class
   <> 1; the frozen spec's P11 (C_reac_ctrl_identity_reply.v:110-112) says only "some live frame of Sc". OWNER PENDING:
   spec owner, through the stream lead and a Theorem Labs lane. TRUE at the real call site: the caller's cells live in LLVMF's
   CLASS-6 fake frame -- a Theorem Labs lane ctl-post-callees.md:546-548 (a working note, not in this delivery) and lib/A/ACtlCutP.v:54-55 (own6, "the shell passes
   sel = fr"), read by my ReplyE2 hand *)
Hypothesis CELLS_NOT_C1 : reply_args fr pa pp pn = true -> forall a cid pos,
  C_reac_ctrl_identity_reply.treply_out pa pp pn a -> In (cid, pos) (lib.Reusable.YG01.frames Sc) ->
  lib.Reusable.YG0n.in_zr a (lib.Reusable.YCbq.frame_rng lyc (cid, pos)) -> cid <> 1.

Local Notation RGW := (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)).
Local Notation FSc := (lib.Reusable.YG0f.ly_F lyc).
(* Every lemma below states its Section dependencies with `Proof using rbBase` and starts by clearing the Section
   hypotheses outside rbBase (rb_clr): lia reverts every arithmetic hypothesis of its context into its proof term, so
   otherwise the closed lemmas would also take premises they never need (the numeric premises Rfr .. Rpn, S16, Hg and
   the interim H_aj_stack_malloc_at_fc, measured by About on fa3e3dde5f7). *)
Local Ltac rb_clr := clear P4gp Rfr Rlen Rpa Rpp Rpn S16 Hg HJ1 HP H10 HFR HNI HNEV HBB HZ HFL
  H_aj_stack_malloc_at_fc.
Collection rbBase := LAWS TS P1 P4tp HSlo HShi P10 P11 HR HREL HROS HJ2 HAB HKEPT HRT2 CELLS_NOT_C1.

(* ---- the cut facts ---- *)
(* the S-B window [S - 9072, S): inside the stack, above the allocation ceiling, present at mem2 (the journal's
   presence and astk_ok conjuncts, YCbq.v:368-369, and layout_ok's lo_stk_ceil, YG0f.v:334) *)
Lemma rb_win :
  lib.Reusable.YG0f.ly_stk_lo lyc <= S - 9072 /\ S <= lib.Reusable.YG0f.ly_stk_hi lyc /\
  lib.Reusable.YG0f.ASAN_CEIL <= S - 9072 /\ S <= 140737488355328 /\
  (forall a, S - 9072 <= a < S -> lib.Reusable.YG0n.apresent (lib.Reusable.YA0n.w_H W) mem2 a).
Proof using rbBase.
  rb_clr.
  pose proof HJ2 as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  destruct Hstk as (_ & HSTK & Hceil & Hsp0 & Hsphi & H47 & _).
  pose proof HAR as (HM & _).
  pose proof (lib.Reusable.YG0f.lo_stk_ceil _ (lib.Reusable.YG0n.am_layout _ _ _ _ HM)) as Hc.
  change (2 ^ 47) with 140737488355328 in H47.
  rewrite Elo in Hc. rewrite Elo, Ehi.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  intros a Ha. apply Hpres. lia.
Qed.

(* the side stack: above the image (pw_F_above), page-aligned and below the allocation ceiling (layout_ok) *)
Lemma rb_F : ASAN_GT <= FSc /\ FSc mod 4096 = 0 /\ FSc + lib.Reusable.YG0f.kFakeStackSize <= lib.Reusable.YG0f.ASAN_CEIL.
Proof using rbBase.
  rb_clr.
  pose proof HJ2 as (HAR & _).
  pose proof (B.ProgWorld_Fs.pw_F_above B lyc S2 W mem2 md2 HAR) as HGT.
  pose proof HAR as (HM & _). pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ HM) as LO.
  pose proof (lib.Reusable.YG0f.lo_F_al _ LO) as Hal. unfold lib.Reusable.YG0f.page_aligned in Hal.
  pose proof (proj1 (Forall_forall _ _) (lib.Reusable.YG0f.lo_app _ LO)
                (lib.Reusable.YG0f.ly_F lyc, lib.Reusable.YG0f.kFakeStackSize)
                ltac:(unfold lib.Reusable.YG0f.owned_extents; right; right; right; left; reflexivity)) as F1.
  destruct (rb_in_app_ceil _ _ F1) as [_ F2]. cbn [fst snd] in F2.
  split; [exact HGT|]. split; [exact Hal | exact F2].
Qed.

(* off the S-A window the real memory at the call is the caller's (the OFF step of rrB_journal_gen) *)
Lemma rb_off_win : forall x : word, ~ (S - 9072 <= bv_unsigned x < S) -> m1 x = memc x.
Proof using rbBase.
  rb_clr.
  intros x Hx. destruct (lib.Lib.Mem.ro_addr rsegs x) eqn:R; [exact (HROS x R)|].
  destruct HREL as [REL1 _]. pose proof (REL1 x) as E1. unfold B.MemNorm.normalize in E1. rewrite R in E1.
  pose proof HR as (MU & _).
  pose proof (MU x ltac:(cbn [lib.Lib.Frame.outside]; split; [exact Hx | exact I])) as E2. unfold B.MemNorm.normalize in E2. rewrite R in E2.
  rewrite <- E1. exact E2.
Qed.

Lemma rb_tp : bv_unsigned tp = RT_TP.
Proof using rbBase. rb_clr. rewrite P4tp, (B.ProgWorld.as_tp_RT_TP B TS). vm_compute. reflexivity. Qed.

(* ---- one byte of the three caller cells ---- *)
(* P11 puts it in a live frame (cid, q) of Sc; CELLS_NOT_C1 makes cid <> 1; AR_frames_law (YG0d.v:447-455) at memc
   gives its visibility, its shadow byte's visibility and its application address; E1's acall_kept keeps that shadow
   byte's view (the frame-shadow clause, YCbq.v:831-833, E = False) from m1 to mem2, and S-A keeps it from memc to m1
   (it is off the window). *)
Lemma rb_cell : reply_args fr pa pp pn = true -> forall a, C_reac_ctrl_identity_reply.treply_out pa pp pn a ->
  FSc + 36864 <= a < FSc + lib.Reusable.YG0f.kFakeStackSize /\
  (a < FSc + 1085440 \/ FSc + 2134016 <= a) /\
  4096 <= a /\
  (a < lib.Reusable.YG0f.kLowShadowBeg \/ (lib.Reusable.YG0f.kHighMemBeg <= a /\ a < lib.Reusable.YG0f.ASAN_CEIL)) /\
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false /\
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 (a / 8 + ASAN_K)) = false /\
  lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) mem2 (a / 8 + ASAN_K) =
    lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc (a / 8 + ASAN_K).
Proof using rbBase.
  rb_clr.
  intros RA a Ha.
  destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & Hcells & _).
  destruct (Hcells a Ha) as ((cid & q & Hin & Hr) & _).
  pose proof (CELLS_NOT_C1 RA a cid q Ha Hin Hr) as Hc1.
  pose proof P1 as (HARc & _).
  destruct (lib.Reusable.YG0d.al_frames _ _ LAWS lyc Sc W memc mdc cid q HARc Hin) as (Hal & Happ & Hby & Hsh).
  pose proof HARc as (HM & _).
  pose proof (lib.Reusable.YG0n.am_wf _ _ _ _ HM) as HWf.
  pose proof (lib.Reusable.YG01.wfs_live _ (lib.Reusable.YG01.wf_fakestack _ _ _ _ _ HWf)) as Hlive.
  pose proof (proj1 (Forall_forall _ _) Hlive (cid, q) Hin) as Hpos. cbn [fst snd] in Hpos.
  destruct (rb_frame_geom lyc cid q (proj1 Hpos) (proj2 Hpos)) as (G1 & G2 & G3 & G4).
  unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YCbq.frame_rng in Hr. cbn [fst snd] in Hr.
  pose proof (lib.Reusable.YG0f.in_app_addr _ _ a Happ Hr) as Hap. unfold lib.Reusable.YG0f.app_addr in Hap.
  destruct rb_win as (_ & _ & Hceil & H47 & _).
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  set (F := lib.Reusable.YG0f.frame_addr lyc cid q) in *.
  set (sz := lib.Reusable.YG00.fs_frame_bytes cid) in *.
  pose proof (Z.div_mod a 8 ltac:(lia)) as Da. pose proof (Z.mod_pos_bound a 8 ltac:(lia)) as Ma.
  pose proof (Z.div_mod F 8 ltac:(lia)) as DF. pose proof (Z.mod_pos_bound F 8 ltac:(lia)) as MF.
  pose proof (Z.div_mod F 32 ltac:(lia)) as DF32.
  pose proof (Z.div_mod sz 8 ltac:(lia)) as Ds.
  assert (HF8 : F mod 8 = 0) by lia.
  assert (Hi : 0 <= a / 8 - F / 8 < sz / 8) by lia.
  assert (Hlow : 0 <= a / 8 + ASAN_K < S - 9072).
  { unfold ASAN_K, lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *. lia. }
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
  pose proof HKEPT as (_ & _ & _ & K4 & _).
  assert (Hsa : lib.Reusable.YG0n.in_zr (a / 8 + ASAN_K) (lib.Reusable.YG0f.shadow_addr F, sz / 8)).
  { unfold lib.Reusable.YG0n.in_zr, lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, ASAN_K.
    cbn [fst snd]. lia. }
  rewrite (K4 cid q (a / 8 + ASAN_K) Hin (or_intror Hsa) (fun H => H)).
  assert (Eoff : m1 (Z_to_bv 64 (a / 8 + ASAN_K)) = memc (Z_to_bv 64 (a / 8 + ASAN_K))).
  { apply rb_off_win. rewrite (B.ProgWorld_Fs.pw_u64 (a / 8 + ASAN_K) ltac:(lia)). lia. }
  unfold lib.Reusable.YG0n.aview, lib.Reusable.YP09.mbyte, lib.Reusable.YK04.mrestrict. cbv beta.
  rewrite Eoff. reflexivity.
Qed.

(* a cell [p, p + n) (n <= 8): its first and last byte give the cell's place *)
Lemma rb_cell_ivl : reply_args fr pa pp pn = true -> forall p n, 1 <= n <= 8 ->
  (forall x, p <= x < p + n -> C_reac_ctrl_identity_reply.treply_out pa pp pn x) ->
  FSc + 36864 <= p /\ p + n <= FSc + lib.Reusable.YG0f.kFakeStackSize /\
  (p + n <= FSc + 1085440 \/ FSc + 2134016 <= p) /\ 4096 <= p /\
  (p + n <= lib.Reusable.YG0f.kLowShadowBeg \/
   (lib.Reusable.YG0f.kHighMemBeg <= p /\ p + n <= lib.Reusable.YG0f.ASAN_CEIL)).
Proof using rbBase.
  rb_clr.
  intros RA p n Hn Hc.
  destruct (rb_cell RA p (Hc p ltac:(lia))) as ((A0 & A1) & A2 & A3 & A4 & _).
  destruct (rb_cell RA (p + n - 1) (Hc (p + n - 1) ltac:(lia))) as ((B0 & B1) & B2 & B3 & B4 & _).
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. lia.
Qed.

(* a cell is addressable at mem2: P11's shadow at memc, kept (rb_cell) *)
Lemma rb_addr_cell : reply_args fr pa pp pn = true -> forall p n, 1 <= n <= 8 ->
  (forall x, p <= x < p + n -> C_reac_ctrl_identity_reply.treply_out pa pp pn x) ->
  lib.Reusable.YG0v.range_addressable (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc)
    lib.Reusable.YG0f.SHADOW_OFF p n ->
  addressable mem2 p n.
Proof using rbBase.
  rb_clr.
  intros RA p n Hn Hc HRA.
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  destruct (rb_cell_ivl RA p n Hn Hc) as (_ & _ & _ & L3 & L4).
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in L4.
  unfold addressable. split; [lia|]. split; [lia|]. split; [unfold APPMEM_END; lia|].
  intros i Hi.
  destruct (rb_cell RA (p + i) (Hc (p + i) ltac:(lia))) as (_ & _ & A0 & A1 & _ & _ & E).
  destruct (HRA (p + i) ltac:(lia)) as (s & Hs & Hok).
  unfold lib.Reusable.YG0v.shadow_of_addr in Hs.
  replace (lib.Reusable.YG0f.SHADOW_OFF + (p + i) / 8) with ((p + i) / 8 + ASAN_K) in Hs
    by (unfold lib.Reusable.YG0f.SHADOW_OFF, ASAN_K; lia).
  rewrite <- E in Hs.
  destruct (B.ProgWorld_Fs.pw_view_mrd W mem2 _ _ Hs) as [_ Hm].
  unfold lib.Reusable.YG0v.saddr_ok in Hok.
  pose proof (Z.mod_pos_bound (p + i) 8 ltac:(lia)) as Mi.
  assert (Hs8 : 0 <= s < 8) by lia.
  unfold addr_byte. split.
  - unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END.
    unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in A1. lia.
  - exists (Z_to_bv 8 s). split; [exact Hm|].
    rewrite (rb_bv_signed8 s Hs8). unfold shadow_ok. lia.
Qed.

Lemma rb_cell_vis : reply_args fr pa pp pn = true -> forall p n, 1 <= n <= 8 ->
  (forall x, p <= x < p + n -> C_reac_ctrl_identity_reply.treply_out pa pp pn x) ->
  lib.Lib.ExecF.rng RGW p n /\ shcov RGW p n.
Proof using rbBase.
  rb_clr.
  intros RA p n Hn Hc.
  destruct (rb_cell_ivl RA p n Hn Hc) as (_ & _ & _ & L3 & L4).
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in L4.
  split.
  - apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
    intros a Ha. destruct (rb_cell RA a (Hc a Ha)) as (_ & _ & _ & _ & V & _). exact V.
  - intros x Hx. destruct (rb_cell RA x (Hc x Hx)) as (_ & _ & X3 & X4 & _ & V & _).
    unfold lib.Reusable.YG0f.kLowShadowBeg, lib.Reusable.YG0f.kHighMemBeg in X4.
    destruct (rb_sh_bound x ltac:(lia)) as [B0 B1].
    exact (rb_rng1 _ _ B0 B1 V).
Qed.

(* ---- the message (a heap block of Sc, P10) ---- *)
Lemma rb_heap : reply_args fr pa pp pn = true -> 50 <= len ->
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) fr 50 /\
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (B.Prog.rng_asan.sh_al8_lo fr)
    (B.Prog.rng_asan.sh_al8_hi fr 50 - B.Prog.rng_asan.sh_al8_lo fr).
Proof using rbBase.
  rb_clr.
  intros RA HL. destruct (P10 RA HL) as ((nb & Hin & Hnb) & _).
  pose proof P1 as (HARc & _).
  split.
  - exact (B.ProgWorldVisHeap.heap_vis B LAWS lyc Sc W memc mdc fr nb fr 50 HARc Hin ltac:(lia) ltac:(lia)).
  - destruct (B.ProgWorldVisHeap.heap_sh_vis B LAWS lyc Sc W memc mdc fr nb fr 50 HARc Hin ltac:(lia) ltac:(lia)
                ltac:(lia)) as [E | V]; [lia | exact V].
Qed.

Lemma rb_SCF : reply_args fr pa pp pn = true -> 50 <= len -> shcov RGW fr 50.
Proof using rbBase.
  rb_clr.
  intros RA HL x Hx. apply B.ProgBridge.rng_of_visible.
  destruct (rb_sh_al8_in fr 50 x Hx) as [A1 A2].
  apply (B.ProgBridge.range_visible_sub _ _ _ _ _ (proj2 (rb_heap RA HL)) A1); lia.
Qed.

Lemma rb_SKF : reply_args fr pa pp pn = true -> 50 <= len -> shkov RGW fr 50.
Proof using rbBase.
  rb_clr.
  intros RA HL a b H1 H2 H3. apply B.ProgBridge.rng_of_visible.
  destruct (rb_sh_al8_kov fr 50 a b H1 H2 H3) as (A1 & A2 & A3).
  apply (B.ProgBridge.range_visible_sub _ _ _ _ _ (proj2 (rb_heap RA HL)) A1 A2); lia.
Qed.

Lemma rb_AFfr : reply_args fr pa pp pn = true -> 50 <= len -> addressable mem2 fr 50.
Proof using rbBase.
  rb_clr.
  intros RA HL. destruct (P10 RA HL) as ((nb & Hin & Hnb) & _). pose proof HJ2 as (HAR & _).
  apply (B.ProgWorldShadow.ctl_block_shadow_of_AR B LAWS lyc S2 W mem2 md2 fr nb fr 50 HAR);
    [rewrite HAB; exact Hin | lia | lia | lia].
Qed.

(* ---- the window ---- *)
Lemma rb_RWIN : lib.Lib.ExecF.rng RGW (S - 9072) 9072.
Proof using rbBase.
  rb_clr.
  destruct rb_win as (_ & _ & Hc & H47 & Hp). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 _] _].
  apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
  intros a Ha. exact (proj1 (Hp a ltac:(lia))).
Qed.

Lemma rb_SCW : shcov RGW (S - 9072) 9072.
Proof using rbBase.
  rb_clr.
  pose proof HJ2 as (HAR & _). destruct rb_win as (Hlo & Hhi & _).
  destruct (B.ProgWorldVisWin.win_sh_vis B LAWS lyc S2 W mem2 md2 (S - 9072) 9072 HAR Hlo ltac:(lia) ltac:(lia))
    as [E0 | HV]; [lia|].
  intros x Hx. apply B.ProgBridge.rng_of_visible.
  destruct (rb_sh_al8_in (S - 9072) 9072 x Hx) as [A1 A2].
  apply (B.ProgBridge.range_visible_sub _ _ _ _ _ HV A1); lia.
Qed.

Lemma rb_AW : addressable mem2 (S - 9072) 9072.
Proof using rbBase.
  rb_clr.
  pose proof HJ2 as (HAR & _). destruct rb_win as (Hlo & Hhi & _).
  exact (B.ProgWorldShadow.ctl_stack_shadow_of_AR B LAWS lyc S2 W mem2 md2 (S - 9072) 9072 HAR Hlo ltac:(lia)
           ltac:(lia)).
Qed.

(* route (C): the run's narrowed premise from the cut's ctl_rt_C (its cut_shadow and img_shadow parts), region by
   region (C_reac_ctrl_identity_replyCover.rrC_R_cover): the own real frame and the parse frames and the real-arm
   record by (Z), the class-1 block and the side-arm record by the frames area, fr (under reply_args, P10's block, a
   block of S2 by HAB) by (L), BC by img_shadow. *)
Lemma rb_SW : shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FSc) mem2.
Proof using rbBase.
  rb_clr.
  pose proof HJ2 as (HAR & _). pose proof HAR as (HM & _).
  destruct rb_win as (Hlo & Hhi & _).
  destruct HRT2 as (_ & Hcut & Himg & _).
  apply (C_reac_ctrl_identity_replyCover.rrC_R_on B lyc S2 fr len pa pp pn S mem2
           (lib.Reusable.YG0n.am_layout _ _ _ _ HM) Hlo Hhi); [|exact Hcut | exact Himg].
  intros RA HL. destruct (P10 RA HL) as ((nb & Hin & Hnb) & _). exists nb. rewrite HAB. exact (conj Hin Hnb).
Qed.

(* ---- the class-1 frames of the side stack and their shadow (am_areas, YG0n.v:137-139) ---- *)
Lemma rb_fs_vis : forall a, FSc <= a < FSc + lib.Reusable.YG0f.kFakeStackSize ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 a) = false.
Proof using rbBase.
  rb_clr.
  intros a Ha. pose proof HJ2 as (HAR & _).
  exact (proj1 (B.ProgWorld_Fs.pw_F_present B lyc S2 W mem2 md2 a HAR Ha)).
Qed.

Lemma rb_fs_sh_vis : forall x, FSc + lib.Reusable.YG0f.kFakeFramesOff <= x < FSc + lib.Reusable.YG0f.kFakeStackSize ->
  lib.Reusable.YA0n.w_H W (Z_to_bv 64 (x / 8 + ASAN_K)) = false.
Proof using rbBase.
  rb_clr.
  intros x Hx. pose proof HJ2 as (HAR & _). pose proof HAR as (HM & _).
  destruct rb_F as (_ & HFal & _).
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
  specialize (AS _ Hi). cbn [fst lib.Reusable.YG0f.aeval] in AS.
  pose proof (B.ProgWorldVisFrame.vis_of_aview _ W mem2 _ AS) as V.
  replace (lib.Reusable.YG0f.shadow_addr (FSc + lib.Reusable.YG0f.kFakeFramesOff) +
           (x / 8 - (FSc + lib.Reusable.YG0f.kFakeFramesOff) / 8)) with (x / 8 + ASAN_K) in V
    by (unfold lib.Reusable.YG0f.shadow_addr, lib.Reusable.YG0f.SHADOW_OFF, ASAN_K; lia).
  exact V.
Qed.

Lemma rb_RFRM : lib.Lib.ExecF.rng RGW (fs_frame FSc 1 0) (fs_frame FSc 1 (fs_M 1) - fs_frame FSc 1 0).
Proof using rbBase.
  rb_clr.
  destruct (rb_fs1 FSc) as (E1 & E2 & _). rewrite E1, E2.
  destruct rb_F as (HGT & _ & HFc). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  unfold ASAN_GT, lib.Reusable.YG0f.kFakeStackSize in *.
  apply B.ProgBridge.rng_of_visible. split; [lia|]. split; [lia|].
  intros a Ha. apply rb_fs_vis. unfold lib.Reusable.YG0f.kFakeStackSize. lia.
Qed.

Lemma rb_SCFM : shcov RGW (fs_frame FSc 1 0) (fs_frame FSc 1 (fs_M 1) - fs_frame FSc 1 0).
Proof using rbBase.
  rb_clr.
  destruct (rb_fs1 FSc) as (E1 & E2 & _). rewrite E1, E2.
  destruct rb_F as (HGT & _ & HFc). pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  unfold ASAN_GT, lib.Reusable.YG0f.kFakeStackSize in *.
  intros x Hx.
  destruct (rb_sh_bound x ltac:(lia)) as [B0 B1].
  apply (rb_rng1 _ _ B0 B1). apply rb_fs_sh_vis.
  unfold lib.Reusable.YG0f.kFakeFramesOff, lib.Reusable.YG0f.kFakeStackSize. lia.
Qed.

(* ---- the side-stack bundle fp [1%nat] mem2 .. (ctl_fp_of_AR) and the thread cells' apartness ---- *)
Lemma rb_fp : fp [1%nat] mem2 (bv_unsigned tp) FSc (S - 9072) S
    (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn).
Proof using rbBase.
  rb_clr.
  rewrite rb_tp.
  pose proof HJ2 as (HAR & _). pose proof HAR as (HM & _).
  pose proof (lib.Reusable.YG0n.am_layout _ _ _ _ HM) as LO.
  destruct rb_win as (Hlo & Hhi & Hceil & H47 & _).
  destruct rb_F as (HGT & HFal & HFc).
  pose proof (@lib.Reusable.YG0f.ASAN_CEIL_range rc) as [[C0 C1] _].
  pose proof (lib.Reusable.YG0f.lo_app _ LO) as LA. rewrite Forall_forall in LA.
  destruct (rb_in_app_ceil _ _ (LA (lib.Reusable.YG0f.ly_T lyc, lib.Reusable.YG0f.kThreadObjSize)
      ltac:(unfold lib.Reusable.YG0f.owned_extents; right; right; left; reflexivity))) as (T0 & T1).
  destruct (rb_in_app_ceil _ _ (LA (lib.Reusable.YG0f.ly_C lyc, 256)
      ltac:(unfold lib.Reusable.YG0f.owned_extents; do 6 right; left; reflexivity))) as (Cc0 & Cc1).
  destruct (rb_in_app_ceil _ _ (LA (lib.Reusable.YG0f.ly_D lyc, 4096)
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
  assert (ETP32 : bv_unsigned (Z_to_bv 64 (RT_TP + 32)) = RT_TP + 32) by (vm_compute; reflexivity).
  assert (Etsd : bv_unsigned (Z_to_bv 64 (lib.Reusable.YG0f.ly_tsd lyc)) = 0x5fd9f8).
  { rewrite (lib.Reusable.YG0n.am_tsd _ _ _ _ HM), (B.ProgWorld.as_tsd_TSD B TS). vm_compute. reflexivity. }
  assert (EC : bv_unsigned (Z_to_bv 64 (lib.Reusable.YG0f.ly_C lyc)) = lib.Reusable.YG0f.ly_C lyc)
    by (apply B.ProgWorld_Fs.pw_u64; lia).
  assert (ET : bv_unsigned (Z_to_bv 64 (lib.Reusable.YG0f.ly_T lyc)) = lib.Reusable.YG0f.ly_T lyc)
    by (apply B.ProgWorld_Fs.pw_u64; unfold lib.Reusable.YG0f.kThreadObjSize in T1; lia).
  assert (ED : bv_unsigned (Z_to_bv 64 (lib.Reusable.YG0f.ly_D lyc)) = lib.Reusable.YG0f.ly_D lyc)
    by (apply B.ProgWorld_Fs.pw_u64; lia).
  destruct (rb_fs1 FSc) as (E1 & E2 & E3 & E4 & E5 & E6).
  unfold ASAN_GT in HGT. unfold lib.Reusable.YG0f.kFakeStackSize in HFc, DFC, DFD, DTF.
  unfold lib.Reusable.YG0f.kThreadObjSize in T1, DTF.
  apply (B.ProgWorld_Fs.ctl_fp_of_AR B TS LAWS lyc S2 W mem2 md2 [1%nat] (S - 9072) S
           (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) HAR).
  - repeat constructor.
  - unfold FS_SIZE. lia.
  - intros a Ha. unfold app_mem, HIGHMEM_BEG, APPMEM_END. right. lia.
  - (* the writes W (window, cells) apart from the thread cells and the side stack's header *)
    unfold fp_dj, fp_tls, reac_ctrl_identity_reply_W, REAC_CTRL_IDENTITY_REPLY_K.
    rewrite ETP32, Etsd, EC, ET, ED, E6.
    (* the cells' place, taken BEFORE the case split on reply_args (the split rewrites the Section's P10 / P11) *)
    assert (CF : reply_args fr pa pp pn = true ->
      (FSc + 36864 <= pa /\ pa + 2 <= FSc + 11571200) /\ (FSc + 36864 <= pp /\ pp + 8 <= FSc + 11571200) /\
      (FSc + 36864 <= pn /\ pn + 8 <= FSc + 11571200)).
    { intros RA.
      destruct (rb_cell_ivl RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)) as (Pa0 & Pa1 & _).
      destruct (rb_cell_ivl RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))) as (Pp0 & Pp1 & _).
      destruct (rb_cell_ivl RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))) as (Pn0 & Pn1 & _).
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
    + clear - HGT HFc Hceil C0 C1 T0 T1 Cc0 Cc1 D0 D1. rewrite Forall_forall. intros w Hw. cbv beta. rewrite Forall_forall. intros d Hd. cbv beta.
      cbn [In app] in Hw, Hd.
      destruct Hw as [<- | []];
        repeat (destruct Hd as [<- | Hd];
                [unfold lib.Prog.RcLay.ly_dj, TLS_INDEX, REAL_TLS_GET_ADDR, TSD_KEY_INITED, TSD_KEY, GOT_CF, CF,
                   GOT_VERBOSITY, VERBOSITY, DTLS_TPOFF, RT_TP; cbn [fst snd]; lia |]);
        destruct Hd.
  - (* the data ranges D (message, cells) apart from the class-1 side-stack bytes *)
    unfold fp_dj, reac_ctrl_identity_reply_D, fp_w, fp_w1. cbn [flat_map app].
    rewrite E1, E2, E3, E4, E5.
    destruct (rb_shb FSc ltac:(lia) ltac:(lia)) as [SH0 SH1].
    (* the message's and the cells' place, taken BEFORE the case split on reply_args *)
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
      destruct (rb_cell_ivl RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)) as (A0 & _ & A2 & _ & A4).
      destruct (rb_cell_ivl RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))) as (B0 & _ & B2 & _ & B4).
      destruct (rb_cell_ivl RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))) as (N0 & _ & N2 & _ & N4).
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

Lemma rb_tls : reac_ctrl_identity_reply_tls mem2 (bv_unsigned tp) FSc (S - 9072) S.
Proof using rbBase.
  rb_clr.
  rewrite rb_tp. pose proof HJ2 as (HAR & _). destruct rb_win as (Hlo & Hhi & _).
  intros DT TS0 C T DB kk Hc.
  exact (B.ProgWorldTlsApart.fp_tls_apart B TS LAWS lyc S2 W mem2 md2 [1%nat] (S - 9072) S HAR ltac:(repeat constructor)
           Hlo Hhi
           DT TS0 C T DB kk Hc).
Qed.

Lemma rb_AOUT : reply_args fr pa pp pn = true ->
  addressable mem2 pa 2 /\ addressable mem2 pp 8 /\ addressable mem2 pn 8 /\
  (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn).
Proof using rbBase.
  rb_clr.
  intros RA. destruct (P11 RA) as (_ & _ & _ & _ & _ & _ & _ & RA1 & RA2 & RA3).
  destruct rb_F as (HGT & _).
  destruct (rb_cell_ivl RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)) as (La & _).
  destruct (rb_cell_ivl RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))) as (Lp & _).
  destruct (rb_cell_ivl RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))) as (Ln & _).
  unfold RT_LO, RT_HI, ASAN_GT in *.
  split; [exact (rb_addr_cell RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx) RA1)|].
  split; [exact (rb_addr_cell RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx)) RA2)|].
  split; [exact (rb_addr_cell RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx)) RA3)|].
  split; [right; lia|]. split; right; lia.
Qed.

(* ==== rrB_SB_base_vis: the view / footprint / runtime premises of rrB_SB_lifted (C_reac_ctrl_identity_replyPf.v),
   in its order (SW AW AFfr AOUT FP0 TLS0, then RWIN SCW RFR SCF SKF RPA SCPA RPP SCPP RPN SCPN RFRM SCFM), at
   mb := mem2, FS := ly_F lyc, tp := the Section's tp. ==== *)
Lemma rrB_SB_base_vis :
  shadow_rw_on (reac_ctrl_identity_reply_shadow_R fr len pa pp pn S FSc) mem2 /\
  addressable mem2 (S - 9072) 9072 /\
  (reply_args fr pa pp pn = true -> 50 <= len -> addressable mem2 fr 50) /\
  (reply_args fr pa pp pn = true ->
     addressable mem2 pa 2 /\ addressable mem2 pp 8 /\ addressable mem2 pn 8 /\
     (pa + 2 <= RT_LO \/ RT_HI <= pa) /\ (pp + 8 <= RT_LO \/ RT_HI <= pp) /\ (pn + 8 <= RT_LO \/ RT_HI <= pn)) /\
  fp [1%nat] mem2 (bv_unsigned tp) (lib.Reusable.YG0f.ly_F lyc) (S - 9072) S
    (reac_ctrl_identity_reply_W fr pa pp pn S) (reac_ctrl_identity_reply_D fr len pa pp pn) /\
  reac_ctrl_identity_reply_tls mem2 (bv_unsigned tp) (lib.Reusable.YG0f.ly_F lyc) (S - 9072) S /\
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
Proof using rbBase.
  rb_clr.
  split; [exact rb_SW|]. split; [exact rb_AW|]. split; [exact rb_AFfr|]. split; [exact rb_AOUT|].
  split; [exact rb_fp|]. split; [exact rb_tls|]. split; [exact rb_RWIN|]. split; [exact rb_SCW|].
  split; [intros RA HL; exact (B.ProgBridge.rng_of_visible _ _ _ (proj1 (rb_heap RA HL)))|].
  split; [exact rb_SCF|]. split; [exact rb_SKF|].
  split; [intros RA; exact (proj1 (rb_cell_vis RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)))|].
  split; [intros RA; exact (proj2 (rb_cell_vis RA pa 2 ltac:(lia) (fun x Hx => or_introl Hx)))|].
  split; [intros RA; exact (proj1 (rb_cell_vis RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))))|].
  split; [intros RA; exact (proj2 (rb_cell_vis RA pp 8 ltac:(lia) (fun x Hx => or_intror (or_introl Hx))))|].
  split; [intros RA; exact (proj1 (rb_cell_vis RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))))|].
  split; [intros RA; exact (proj2 (rb_cell_vis RA pn 8 ltac:(lia) (fun x Hx => or_intror (or_intror Hx))))|].
  split; [exact rb_RFRM | exact rb_SCFM].
Qed.
End Base.
