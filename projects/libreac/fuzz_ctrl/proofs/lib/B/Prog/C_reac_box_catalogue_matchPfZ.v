(* lib/B/Prog/C_reac_box_catalogue_matchPfZ.v -- fuzz_ctrl image B (asan-ubsan, libreac v1.9.0): the LAST piece (H3) of
   pb_reac_box_catalogue_match, the cgif-form world walk of reac_box_catalogue_match (0x84e40) that proves
   C_reac_box_catalogue_match.treac_box_catalogue_match_spec B.  Brief:
   PB-H3-BRIEF.md (a working note, not in this delivery); map: a Theorem Labs lane's plan
   pb_reac_ctrl_identity_reply.plan.md section 1 (a working note, not in this delivery) (its `ret` step and its NOTE).
   rule 24: no function proved; this file composes this lane's own Qed stretches (reac_box_catalogue_matchF_on.v's
   cm_pre_rel, C_reac_box_catalogue_matchLibW.v's cmW_post_rel) with shared Qed lemmas (B MemNormF / MemNormTr,
   B ProgBridge, YA0nR.SRr_fsteps, ProgWorldAstack.ctl_release_of_free_law, ProgWorld.ctl_fs_geom,
   ProgWorldVisWin.win_vis, YCbq).

   THIS PIECE: from the exit state (pc 0x850fc, the class-2 side-stack frame (2, pos) still owned) to the return.
     S-5 + R + S-6, ONE run (cmZ_rel_run): F's cm_pre_rel (exit -> the release store at 0x85194), the store
         `sb zero, 0(a0)` itself (one step, as F's cm_exit side-stack arm), and LibW's cmW_post_rel (0x85198 ->
         ret), all three at the normalized EXIT memory (m := mc := normalize mx), back to the real memory by
         B.MemNormF.evtF_normalize_ro.  Why not Lib.cmRB_pre_rel then LibW.cmRBw_post_rel: cmRBw_post_rel
         (LibW.v:2139) takes cmBase at the STORE memory, and the flag byte fs_flag FS 2 jj there (fp_cls class 2) has
         no source: cmRB_pre_rel's post (Lib.v:415, cmRB_AtRel) declares that byte in its munch.  At the exit memory
         every cmBase clause has its source (cmPfB_mid's HBASE at the exit's journal state, PfB.cmPfB_me_exit:
         PfV.cmPf_base_of_AR at the exit's AR, route (C) through ctl_rt_C_of_AR).  The run's post
         (cmZ_RelPost): the registers of the return, the writes [(fr, fr + 8); (shadow fr, + 32); (flag byte, + 1)]
         relative to the exit memory, and the flag byte 0.
     the RELEASE and the journal (cmZ_rel_ret): the run as fsteps (B.ProgBridge.fevt_of_evtF), the world walk by
         YA0nR.SRr_fsteps, and the journal ONE step by ProgWorldAstack.ctl_release_of_free_law 2 (Qed, used by name):
         own [(2, pos)] -> [], S' = stack_free_state 2 pos Sc, written set = in_frames bytes (the frame's first word,
         its 32 shadow bytes) plus the one flag byte; ctl_fs_geom turns fs_frame / fs_flag into frame_addr / flag_addr.
     the POST (cmPf_exit_post): apost_base's witnesses at the return (the journal from the entry, aregs_preserved
         from the restored saves, a0 = want, the blocks' Permutation).

   SECTION HYPOTHESES (core vocabulary only, decisions.md item 15 (a working note, not in this delivery)): LAWS (AR_laws), ASF (astack_free_law), both
   from a Theorem Labs lane on a working branch, as in C_reac_box_catalogue_matchPf.v's header.
   FRAME-ROUTE FACTS are premises of the lemma that needs them, each named at its premise with its source: the base
   facts at the exit memory (cmBase, the window's stk, cmRB_Fr: cmBase from cmPfB_mid's HBASE at the exit's journal
   state, the window's stk and cmRB_Fr from the last re-based stretch's cmRBw_J, PfB.cmPfB_me_exit), and the
   footprint's visibility (window: ProgWorldVisWin.win_vis, Qed, used by name; window shadow:
   ProgWorldVisWin.win_sh_vis, Qed; side stack and its frames' shadow: AR through ProgWorld_Fs.pw_F_present and
   am_areas, C_reac_box_catalogue_matchPfV.cmPf_fs_vis, Qed).
   ajournal's sink head: ProgWorld's statements resolve it to lib.Reusable.YE2k.tfib_sink_head; with FP = [] the
   journal does not depend on it (cmZ_ajournal_sk), so this file stays generic in SK as the spec is. *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import Specs.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes
  ZBridge Image.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcLib RcBox RcBoxLib RcSynth RcParse
  RcMatch RcMatchLib RcAsan RcAsanLib RcLay.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import RcAsanRT asan_stack_malloc_c RcAsanFP RcAsanFPLib
  memcmp_c bcmp_wrap_c reac_ctrl_parse_c reac_box_model_block_c reac_box_catalogue_match_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
(* StepF after Step, as in reac_box_catalogue_matchF_on.v and C_reac_box_catalogue_matchLibW.v (the one store step). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import reac_box_catalogue_match reac_box_catalogue_matchF_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require MemNorm MemNormTr MemNormF.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require ImgBounds.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import C_reac_box_catalogue_matchLib
  C_reac_box_catalogue_matchLibW.
(* The six collided modules by the unambiguous lib.Reusable path (porter's gate). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK11 YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YK04 YK04R YK0s YK14 YA0n YA0nR.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YG00 YG01 YG0f YG0n YG0d YCbq YP09 APostBase YE2k.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YE01 YI00 YF0l.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require ProgBridge ProgBridgeData.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib Require B.ProgWorld B.ProgWorldAstack B.ProgWorldVisWin B.Prog.rng_asan.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_box_catalogue_match C_reac_box_catalogue_matchPf
  C_reac_box_catalogue_matchPfI C_reac_box_catalogue_matchPfV C_reac_box_catalogue_matchPfB.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require C_reac_ctrl_parse C_reac_box_model_block.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Reusable Require YI04.
Import ListNotations.
Open Scope Z_scope.

(* The store hook of reac_box_catalogue_matchF_on.v / C_reac_box_catalogue_matchLibW.v (local there): the release store
   writes le1 (Z_to_bv 64 0), the form cmW_post_rel's start memory names. *)
Local Ltac OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.StepF.mem_after_store_opt ::=
  C_reac_box_catalogue_matchLibW.cmF_store_opt.

(* ---- definitional helpers (no frame-route fact) ---- *)

(* A ret_ok return address is its own jalr target (the twin of lib/B/KindBGlue.v's kb_ret_pc over the CORE
   lib.Reusable.YK0s, which KindBGlue does not Require). *)
Lemma cmZ_mod2_land : forall x, (x mod 2 ^ 64) mod 2 = x mod 2.
Proof.
  intros x. change ((x mod 2 ^ 64) mod 2) with ((x mod 2 ^ 64) mod 2 ^ 1). change (x mod 2) with (x mod 2 ^ 1).
  rewrite <- !Z.land_ones by lia. rewrite <- Z.land_assoc. reflexivity.
Qed.

Lemma cmZ_land_m2 : forall x, Z.land x (-2) mod 2 = 0.
Proof.
  intros x. change (Z.land x (-2) mod 2) with (Z.land x (-2) mod 2 ^ 1).
  rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. apply Z.land_0_r.
Qed.

(* A byte the view reads unchanged is the same byte (the view is bv_unsigned of mbyte at the restricted memory). *)
Lemma cmZ_mbyte_of_view : forall (H H' : word -> bool) (m m' : word -> option byte) (a : Z) (b : byte),
  lib.Reusable.YG0n.aview rsegs H' m' a = lib.Reusable.YG0n.aview rsegs H m a ->
  lib.Reusable.YP09.mbyte rsegs (lib.Reusable.YK04.mrestrict H m) a = Some b ->
  lib.Reusable.YP09.mbyte rsegs (lib.Reusable.YK04.mrestrict H' m') a = Some b.
Proof.
  intros H H' m m' a b E Hb. unfold lib.Reusable.YG0n.aview in E. cbv beta in E. rewrite Hb in E.
  destruct (lib.Reusable.YP09.mbyte rsegs (lib.Reusable.YK04.mrestrict H' m') a) as [b'|];
    cbn [option_map] in E; [|discriminate E].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.

(* garr8 moves along a view kept byte for byte (the journal's block clause). *)
Lemma cmZ_garr8_view : forall (H H' : word -> bool) (m m' : word -> option byte) (base : Z) (l : list Z),
  (forall j, (j < length l)%nat ->
     lib.Reusable.YG0n.aview rsegs H' m' (base + Z.of_nat j) = lib.Reusable.YG0n.aview rsegs H m (base + Z.of_nat j)) ->
  lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict H m) base l ->
  lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict H' m') base l.
Proof.
  intros H H' m m' base l Hv Hg j Hj.
  destruct (Hg j Hj) as [Hm Hr]. split; [|exact Hr].
  intros k Hk. assert (Ek : k = 0%nat) by lia. subst k.
  specialize (Hm 0%nat Hk). cbn [Z.of_nat] in Hm |- *. rewrite Z.add_0_r in Hm. rewrite Z.add_0_r.
  exact (cmZ_mbyte_of_view H H' m m' _ _ (Hv j Hj) Hm).
Qed.

Lemma cmZ_ret_pc : forall k, lib.Reusable.YK0s.ret_ok k -> lib.Lib.MState.ret_pc k = k.
Proof.
  intros k Hk. unfold lib.Reusable.YK0s.ret_ok, lib.Reusable.YK14.v_jalr, lib.Reusable.YK11.jalr_tgtZ in Hk.
  pose proof (bv_unsigned_in_range 64 k) as Hr.
  assert (Hz : bv_unsigned k = Z.land (bv_unsigned k) (-2) mod 2 ^ 64).
  { rewrite <- Hk at 1. rewrite Z_to_bv_unsigned, Z.add_0_r. reflexivity. }
  assert (Hm : bv_unsigned k mod 2 = 0) by (rewrite Hz, cmZ_mod2_land; apply cmZ_land_m2).
  rewrite <- (lib.Lib.MState.Z_to_bv_bv_unsigned k). apply lib.Lib.MState.ret_pc_even; [exact Hr | exact Hm].
Qed.

(* ---- S-5 + the release store + S-6: ONE run from the exit (pc 0x850fc, side-stack arm) to the return, at the
   normalized EXIT memory, back to the real memory mx.  The base facts are at mx only (the premises of
   Lib.cmRB_pre_rel, the same set). ---- *)
Definition cmZ_RelPost (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (mx : word -> option byte) (f len Sp FS : Z) (fb : list byte) (fr jj : Z) (ms' : machine_state) : Prop :=
  exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
    ms' = lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (want CM_T len fb))
                  a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
             F (lib.Lib.MState.ret_pc ra) fc None m' (lib.Lib.PropExec.seg_rom rsegs) /\
    lib.Lib.Frame.munch [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
      mx m' /\
    lib.Lib.Mem.mrd rsegs m' (lib.Lib.Mem.wa (fs_flag FS 2 jj)) = Some (Z_to_bv 8 0).

Lemma cmZ_rel_run : forall (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f len Sp FS : Z) (fb : list byte) (RNG : lib.Lib.ExecF.footprint) (mx : word -> option byte),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  lib.Lib.ExecF.rng RNG (Sp - 9136) 9136 ->
  lib.Lib.ExecF.rng RNG (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  lib.Lib.ExecF.rng RNG FS (fs_frame FS 0 0 - FS) ->
  Forall (fun iv : Z * Z => lib.Lib.ExecF.rng RNG (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  cmBase mx tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mx (Sp - 9136) Sp ->
  forall (fr sp2 jj r : Z) (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  r = want CM_T len fb -> cmRB_Fr ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mx Sp FS fr sp2 jj 1 ->
  lib.Lib.ExecF.evtF rsegs RNG (cmZ_RelPost ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc mx f len Sp FS fb fr jj)
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if 1 =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850fc) fc None mx (lib.Lib.PropExec.seg_rom rsegs)).
Proof.
  intros ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb RNG mx
    Rf Rlen RS S16 HK Hfb HHM HAE RWIN RWSH RHDR RFPW HB STW fr sp2 jj r
    x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HFr.
  pose proof (cmRB_J_base ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mx f len Sp FS fb fr sp2 jj 1 S16 HHM HB STW HFr)
    as HJ.
  destruct (cmRB_norm mx tp f len Sp FS fb HHM HB STW)
    as (REL & STn & MIn & ACn & SRn & AWn & FPn & TLn & CLn & HFBn & BTn & ATn & ABCn).
  pose proof (B.MemNorm.ro_agree_of_mem_rel rsegs _ _ REL) as RO.
  pose proof (acl_fs tp (B.MemNorm.normalize rsegs mx) f len Sp FS FPn) as (AF1 & AF2 & AF3 & AF4 & AF5 & AF6).
  pose proof HFr as ([(_ & _ & _ & En) | (Hj & Ef & Es & _)] & _ & _); [discriminate En|].
  assert (FLo : FS <= fs_flag FS 2 jj /\ fs_flag FS 2 jj + 1 <= FS + 36864).
  { unfold fs_flag, fs_M in Hj |- *. cbn [Z.of_nat Pos.of_succ_nat] in Hj |- *.
    change (2 ^ 15) with 32768. change (2 ^ 13) with 8192. change (2 ^ 12) with 4096 in Hj. lia. }
  (* the run on the normalized exit memory: cm_pre_rel, the store, cmW_post_rel *)
  assert (RUN : lib.Lib.ExecF.evtF rsegs RNG
    (fun ms' => exists m1 : word -> option byte,
       cmAtRel ra tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (B.MemNorm.normalize rsegs mx) f len Sp FS fb fr sp2 jj
         (B.MemNorm.normalize rsegs mx) m1 /\
       cmPostW ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs mx) f len Sp FS fb
         (write_to_mem m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) (lib.Lib.Mem.le1 (Z_to_bv 64 0))) ms')
    (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
             y0 y1 y2 y3 y4 y5 y6 y7
             (Z_to_bv 64 (if 1 =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6 (Z_to_bv 64 (shadow_addr fr))
             (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
        F (Z_to_bv 64 0x850fc) fc None (B.MemNorm.normalize rsegs mx) (lib.Lib.PropExec.seg_rom rsegs))).
  { pose proof (cm_pre_rel ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs mx)
      f len Sp FS fb RNG) as L.
    C_reac_box_catalogue_matchLib.cmRB_feed L.
    eapply lib.Lib.ExecF.evtF_cut;
      [exact (L fr sp2 jj (B.MemNorm.normalize rsegs mx) r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11
                u3 u4 u5 u6 Er HJ)|].
    intros ms (m1 & -> & HAt).
    (* the release store sb zero, 0(a0) at 0x85194 (F's cm_exit, side-stack arm) *)
    pose proof (rf_flag2 f len Sp FS fb RNG Rf Rlen Hfb RHDR jj Hj) as RFL.
    pose proof HAt as (_ & _ & _ & _ & _ & _ & STfs1).
    assert (SOKfl : store_ok rsegs m1 (lib.Lib.Mem.wa (fs_flag FS 2 jj)) 1 = true)
      by (apply (wv_store_ok f len Sp fb Rf Rlen Hfb m1 m1 (fs_flag FS 2 jj) 1);
          [ intros i Hi; replace (fs_flag FS 2 jj + i) with (fs_flag FS 2 jj) by lia;
            apply (cm_stk_wv m1 FS (FS + FS_SIZE) (fs_flag FS 2 jj) STfs1); unfold FS_SIZE in *; lia
          | apply lib.Lib.Frame.wmono_refl | lia | unfold FS_SIZE in *; lia ]).
    clear STfs1.
    change (Z_to_bv 64 (fs_flag FS 2 jj)) with (lib.Lib.Mem.wa (fs_flag FS 2 jj)).
    step.
    eapply lib.Lib.ExecF.evtF_mono;
      [exact (cmW_post_rel ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (B.MemNorm.normalize rsegs mx)
                f len Sp FS fb RNG Rf Rlen RS S16 HK STn Hfb SRn HHM HAE AWn FPn RWIN RWSH RHDR RFPW
                fr sp2 jj (B.MemNorm.normalize rsegs mx) m1 r x1 u0 u1 u2 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11
                u3 u4 u5 u6 Er HAt)|].
    intros ms' HP. exists m1. exact (conj HAt HP). }
  (* back to the real exit memory *)
  pose proof (B.MemNormF.evtF_normalize_ro _ _ _ _ _ _ _ mx _ RO RUN) as H.
  eapply lib.Lib.ExecF.evtF_mono; [exact H|].
  intros st (st0 & (m1 & HAt & HP) & Hrel & Hsm).
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mn & -> &
                  MU0 & _).
  destruct (B.MemNormTr.ms_rel_MS _ _ _ _ _ _ _ _ Hrel) as [Est Hmr].
  pose proof HAt as (_ & MUw & _).
  apply (lib.Lib.Frame.munch_write _ (B.MemNorm.normalize rsegs mx) m1 (fs_flag FS 2 jj)
           (lib.Lib.Mem.le1 (Z_to_bv 64 0))) in MUw;
    [| unfold FS_SIZE in *; lia | rewrite lib.Lib.Mem.length_le1; unfold FS_SIZE in *; lia
     | rewrite lib.Lib.Mem.length_le1; cbn [lib.Lib.Frame.inside]; right; right; left; split; lia].
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', (ms_mem st).
  split; [exact Est|].
  split.
  - intros x Hx. destruct (lib.Lib.Mem.ro_addr rsegs x) eqn:E; [exact (Hsm x E)|].
    rewrite <- (B.MemNorm.mem_rel_rw rsegs _ _ x Hmr E), (MU0 x I), (MUw x Hx).
    unfold B.MemNorm.normalize. rewrite E. reflexivity.
  - rewrite (B.MemNorm.mrd_rel rsegs _ _ _ Hmr), (cmRB_mrd_keep _ _ _ (MU0 _ I)).
    pose proof (lib.Lib.Mem.bytes_at_write_same rsegs m1 (fs_flag FS 2 jj) (lib.Lib.Mem.le1 (Z_to_bv 64 0))
                  ltac:(lia) ltac:(rewrite lib.Lib.Mem.length_le1; unfold FS_SIZE in *; lia)) as BW.
    destruct BW as (_ & _ & BW). specialize (BW 0%nat ltac:(rewrite lib.Lib.Mem.length_le1; lia)).
    replace (fs_flag FS 2 jj + Z.of_nat 0) with (fs_flag FS 2 jj) in BW by lia.
    rewrite BW. reflexivity.
Qed.

Section Z.
Context {fx : lib.Reusable.YK11.FPState} {rc : lib.Reusable.YM05.RunCeil} {SK : lib.Reusable.YI16.sink_head}.
Variable B : lib.Reusable.YG0f.asyms.

(* The journal with FP = [] does not depend on the sink head: its one SK-dependent clause (fp_spares FP, YCbq.v:362)
   holds for every a when the footprint holds no sink (YCbq.fp_spares_closed / sink_closed_nil). *)
Lemma cmZ_ajournal_sk : forall (SK1 SK2 : lib.Reusable.YI16.sink_head) STK sp0 ly S
    (W : lib.Reusable.YA0n.world rsegs) mem md own ly' S' (W' : lib.Reusable.YA0n.world rsegs) mem' md' k,
  lib.Reusable.YCbq.ajournal (SK := SK1) rsegs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
  lib.Reusable.YCbq.ajournal (SK := SK2) rsegs B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k.
Proof.
  intros SK1 SK2 STK sp0 ly S W mem md own ly' S' W' mem' md' k
    (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17).
  split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact A5|].
  split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|].
  split; [intros a Hi Hns He _;
          exact (A11 a Hi Hns He (lib.Reusable.YCbq.fp_spares_closed (SK := SK1) [] a lib.Reusable.YCbq.sink_closed_nil))|].
  split; [exact A12|]. split; [exact A13|]. split; [exact A14|]. split; [exact A15|].
  split; [exact A16 | exact A17].
Qed.

(* Core: the world's laws. *)
Hypothesis LAWS : lib.Reusable.YG0d.AR_laws rsegs B.
(* Core: the fake stack's release rule. *)
Hypothesis ASF : lib.Reusable.YG0d.astack_free_law rsegs B.

(* ---- the RELEASE as the journal's ONE step across the whole run (a Theorem Labs lane's plan (a working note, not in this delivery), `ret`): cmZ_rel_run at
   RNG := RNG_W (w_H W), as fsteps (ProgBridge.fevt_of_evtF), lifted by YA0nR.SRr_fsteps, and the journal by
   ProgWorldAstack.ctl_release_of_free_law 2 (Qed; written set: the frame's first word and its 32 shadow bytes,
   in_frames of (2, pos), plus the flag byte flag_addr lyc 2 pos, which ends 0).  The continuation gets the return
   state with the journal released: own [] and stack_free_state 2 pos Sc.
   FRAME-ROUTE premises: the footprint's visibility (sources at cmPf_exit_post) and the base facts at the exit
   memory mx (PfB.cmPfB_me_exit); FS = ly_F lyc and jj = pos name the frame of the class-2 request (ctl_fs_of_astack 2,
   the glue's S-B). ---- *)
Lemma cmZ_rel_ret : forall (W : lib.Reusable.YA0n.world rsegs) (ly0 : lib.Reusable.YG0f.alayout)
    (S0 : lib.Reusable.YG00.astate) (W0 : lib.Reusable.YA0n.world rsegs) (mem0 : word -> option byte) (md0 : Model)
    (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate) (mx : word -> option byte) (mdx : Model)
    (k sp0 pos : Z) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (f len Sp FS : Z) (fb : list byte) (fr sp2 jj r : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word)
    (Q : lib.Reusable.YA0n.world rsegs -> config -> Prop),
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> Sp < 2 ^ 64 -> Sp mod 16 = 0 -> 9136 <= Sp -> length fb = 50%nat ->
  HIGHMEM_BEG <= Sp - 9136 -> Sp <= APPMEM_END ->
  (* FRAME-ROUTE: the footprint's visibility in the current world (sources: cmPf_exit_post) *)
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (Sp - 9136) 9136 ->
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (shadow_addr (Sp - 9136)) (shadow_addr Sp - shadow_addr (Sp - 9136)) ->
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) FS (fs_frame FS 0 0 - FS) ->
  Forall (fun iv : Z * Z => B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W) (fst iv) (snd iv - fst iv))
    (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  (* FRAME-ROUTE: the base facts at the exit memory (PfB.cmPfB_me_exit) *)
  cmBase mx tp f len Sp FS fb -> lib.Lib.Frame.stk rsegs mx (Sp - 9136) Sp ->
  r = want CM_T len fb -> cmRB_Fr ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 mx Sp FS fr sp2 jj 1 ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK sp0 [] ly0 S0 W0 mem0 md0 [(2, pos)]
    lyc Sc W mx mdx k ->
  FS = lib.Reusable.YG0f.ly_F lyc -> jj = pos ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte) (md' : Model),
     lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK sp0 [] ly0 S0 W0 mem0 md0 []
       lyc (lib.Reusable.YG01.stack_free_state 2 pos Sc) W m' md' k ->
     lib.Reusable.YA0n.SRr rsegs W
       (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR ra (Z_to_bv 64 Sp) gp tp t0' t1' t2' s0 s1
                                    (Z_to_bv 64 (want CM_T len fb)) a1' a2' a3' a4' a5' a6' a7'
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (lib.Lib.MState.ret_pc ra) fc None m' (lib.Lib.PropExec.seg_rom rsegs)) md') Q) ->
  lib.Reusable.YA0n.SRr rsegs W
    (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) gp tp u0 u1 u2 (Z_to_bv 64 Sp) (Z_to_bv 64 (CA Sp))
                                 y0 y1 y2 y3 y4 y5 y6 y7
                                 (Z_to_bv 64 (if 1 =? 0 then 0 else fr)) z3 (Z_to_bv 64 r) z5 z6
                                 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
              F (Z_to_bv 64 0x850fc) fc None mx (lib.Lib.PropExec.seg_rom rsegs)) mdx) Q.
Proof.
  intros W ly0 S0 W0 mem0 md0 lyc Sc mx mdx k sp0 pos ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    f len Sp FS fb fr sp2 jj r x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Q
    Rf Rlen RS S16 HK Hfb HHM HAE VWIN VWSH VHDR VFPW HB STW Er HFr HJ HFS Hjj K.
  pose proof HFr as ([(_ & _ & _ & En) | (Hj & Ef & _ & _)] & _ & _); [discriminate En|].
  assert (RFPW : Forall (fun iv : Z * Z => lib.Lib.ExecF.rng (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
                                             (fst iv) (snd iv - fst iv)) (fp_w [0%nat; 1%nat; 2%nat] FS)).
  { eapply Forall_impl; [| exact VFPW]. intros iv Hv. exact (B.ProgBridge.rng_of_visible _ _ _ Hv). }
  pose proof (cmZ_rel_run ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f len Sp FS fb
                (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W)) mx Rf Rlen RS S16 HK Hfb HHM HAE
                (B.ProgBridge.rng_of_visible _ _ _ VWIN) (B.ProgBridge.rng_of_visible _ _ _ VWSH)
                (B.ProgBridge.rng_of_visible _ _ _ VHDR) RFPW HB STW fr sp2 jj r
                x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 Er HFr) as RUN.
  destruct (B.ProgBridge.fevt_of_evtF _ _ _ RUN) as (ms' & Hrun & HP).
  apply (lib.Reusable.YA0nR.SRr_fsteps rsegs B.ProgBridgeData.rsegs_wx_nowrap W _ ms' mdx _ Q Hrun
           (B.ProgBridge.fp_avoids_RNG_W _)).
  intros md' Hsame.
  destruct HP as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & Ems &
                  MU & FL).
  (* the geometry of the class-2 frame (2, pos): ctrl's fs_frame / fs_flag / shadow_addr as the core's *)
  pose proof (lib.B.ProgWorld.ctl_fs_geom FS 2 pos ltac:(lia)) as (_ & _ & GF & GFl & _ & _ & GSH).
  change (Z.to_nat 2) with 2%nat in GF, GFl.
  assert (Efr : fr = lib.Reusable.YG0f.frame_addr lyc 2 pos).
  { unfold lib.Reusable.YG0f.frame_addr. rewrite Ef, Hjj, GF, HFS. reflexivity. }
  assert (Efl : fs_flag FS 2 jj = lib.Reusable.YG0f.flag_addr lyc 2 pos).
  { unfold lib.Reusable.YG0f.flag_addr. rewrite Hjj, GFl, HFS. reflexivity. }
  assert (FB2 : lib.Reusable.YG00.fs_frame_bytes 2 = 256) by reflexivity.
  (* the journal, ONE step: ctl_release_of_free_law 2 *)
  assert (HJ' : lib.Reusable.YCbq.ajournal (SK := lib.Reusable.YE2k.tfib_sink_head) rsegs B
                  C_reac_box_catalogue_match.CM_STK sp0 [] ly0 S0 W0 mem0 md0 []
                  lyc (lib.Reusable.YG01.stack_free_state 2 pos Sc) W (ms_mem ms') md' k).
  { refine (lib.B.ProgWorldAstack.ctl_release_of_free_law B 2 LAWS ASF B.ProgBridgeData.rsegs_wx_nowrap ltac:(lia)
              C_reac_box_catalogue_match.CM_STK sp0 [] ly0 S0 W0 mem0 md0 [] lyc Sc W _ ms' mdx md' k pos
              (B.ProgBridge.RNG_W (lib.Reusable.YA0n.w_H W))
              [(fr, fr + 8); (shadow_addr fr, shadow_addr fr + 32); (fs_flag FS 2 jj, fs_flag FS 2 jj + 1)]
              _ Hrun (B.ProgBridge.fp_avoids_RNG_W _) _ Hsame _ _).
    - exact (cmZ_ajournal_sk SK lib.Reusable.YE2k.tfib_sink_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ).
    - rewrite Ems. exact MU.
    - intros a Ha Hout.
      assert (Hc : (fr <= a < fr + 8) \/ (shadow_addr fr <= a < shadow_addr fr + 32) \/
                   (fs_flag FS 2 jj <= a < fs_flag FS 2 jj + 1)).
      { cbn [lib.Lib.Frame.outside] in Hout. lia. }
      unfold lib.Reusable.YCbq.awr_byte, lib.Reusable.YCbq.in_frames.
      destruct Hc as [Hc | [Hc | Hc]].
      + left. right; right; right. exists 2, pos. split; [left; reflexivity|]. left.
        unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr, FB2. lia.
      + left. right; right; right. exists 2, pos. split; [left; reflexivity|]. right.
        unfold lib.Reusable.YG0n.in_zr. cbn [fst snd]. rewrite <- Efr, FB2, <- GSH.
        change (256 / 8) with 32. lia.
      + right. rewrite <- Efl. lia.
    - unfold lib.Reusable.YP09.mbyte. rewrite Ems, <- Efl. exact FL. }
  rewrite Ems in HJ' |- *.
  apply (K t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' md').
  exact (cmZ_ajournal_sk lib.Reusable.YE2k.tfib_sink_head SK _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ').
Qed.

(* ---- the POST: from the exit state to treac_box_catalogue_match_post (apost_base, APostBase.v:59).  The run and the
   release by cmZ_rel_ret; at the return: the configuration at the caller's ra (ret_ok, cmZ_ret_pc), the journal from
   the entry with own [] and k = EV_CM = 0, aregs_preserved (the 13 saves restored, sp = the entry sp, gp / tp kept),
   a0 = want A_CM_TBL len fb (CM_T = A_CM_TBL = 0x9f620), and the blocks' Permutation (stack_free_state keeps the
   blocks, YG01.blocks_stack_free_state).
   FRAME-ROUTE premises, each with its source:
     the window [sp - 9136, sp) visible  <- ProgWorldVisWin.win_vis (Qed) on the exit journal, used here by name;
     the window's shadow visible         <- ProgWorldVisWin.win_sh_vis (Qed), sh_al8 cover of it (the composer);
     the side stack's header and every fp_w [0; 1; 2] range visible
                                         <- AR: ProgWorld_Fs.pw_F_present (Qed) and am_areas' frames-shadow entry
                                            (YG0n.v:139), C_reac_box_catalogue_matchPfV.cmPf_fs_vis (Qed);
     cmBase / stk / cmRB_Fr at the exit memory
                                         <- cmPfB_mid's HBASE at the exit's journal state (cmPf_base_of_AR) and the
                                            last re-based stretch's cmRBw_J, PfB.cmPfB_me_exit;
     FS = ly_F lyc, jj = pos             <- ctl_fs_of_astack 2 (the glue's S-B), the layout kept by the journal;
     the blocks' Permutation at the exit <- the class-2 request (ablocks kept) and the callees' posts.  ---- *)
Lemma cmPf_exit_post : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model)
    (f len FS : Z) (fb : list byte) (lyc : lib.Reusable.YG0f.alayout) (Sc : lib.Reusable.YG00.astate)
    (Wx : lib.Reusable.YA0n.world rsegs) (mx : word -> option byte) (mdx : Model) (pos fr sp2 jj : Z)
    (x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6 : word),
  lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> length fb = 50%nat ->
  lib.Reusable.YCbq.ajournal rsegs B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
    ly S W memc md [(2, pos)] lyc Sc Wx mx mdx 0 ->
  Permutation (lib.Reusable.YG0d.ablocks B lyc Sc) (lib.Reusable.YG0d.ablocks B ly S) ->
  FS = lib.Reusable.YG0f.ly_F lyc -> jj = pos ->
  (* FRAME-ROUTE: visibility (win_sh_vis; cmPf_fs_vis) *)
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H Wx) (shadow_addr (lib.Reusable.YG0d.spZ regs - 9136))
    (shadow_addr (lib.Reusable.YG0d.spZ regs) - shadow_addr (lib.Reusable.YG0d.spZ regs - 9136)) ->
  B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H Wx) FS (fs_frame FS 0 0 - FS) ->
  Forall (fun iv : Z * Z => B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H Wx) (fst iv) (snd iv - fst iv))
    (fp_w [0%nat; 1%nat; 2%nat] FS) ->
  (* FRAME-ROUTE: the base facts at the exit memory (PfB.cmPfB_me_exit) *)
  cmBase mx (lib.Reusable.YK11.getr regs 4) f len (lib.Reusable.YG0d.spZ regs) FS fb ->
  lib.Lib.Frame.stk rsegs mx (lib.Reusable.YG0d.spZ regs - 9136) (lib.Reusable.YG0d.spZ regs) ->
  cmRB_Fr (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9)
    (lib.Reusable.YK11.getr regs 18) (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20)
    (lib.Reusable.YK11.getr regs 21) (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23)
    (lib.Reusable.YK11.getr regs 24) (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26)
    (lib.Reusable.YK11.getr regs 27) mx (lib.Reusable.YG0d.spZ regs) FS fr sp2 jj 1 ->
  lib.Reusable.YA0n.SRr rsegs Wx
    (mkCfg (lib.Lib.MState.MS (lib.Lib.Frame.mkR x1 (Z_to_bv 64 sp2) (lib.Reusable.YK11.getr regs 3)
                                 (lib.Reusable.YK11.getr regs 4) u0 u1 u2
                                 (Z_to_bv 64 (lib.Reusable.YG0d.spZ regs)) (Z_to_bv 64 (CA (lib.Reusable.YG0d.spZ regs)))
                                 y0 y1 y2 y3 y4 y5 y6 y7
                                 (Z_to_bv 64 (if 1 =? 0 then 0 else fr)) z3 (Z_to_bv 64 (want CM_T len fb)) z5 z6
                                 (Z_to_bv 64 (shadow_addr fr)) (Z_to_bv 64 fr) z9 z10 z11 u3 u4 u5 u6)
              lib.Reusable.YK11.fp_regs (Z_to_bv 64 0x850fc) lib.Reusable.YK11.fp_csr None mx
              (lib.Lib.PropExec.seg_rom rsegs)) mdx)
    (C_reac_box_catalogue_match.treac_box_catalogue_match_post B regs ly S W memc md len fb).
Proof.
  intros W ly S regs memc md f len FS fb lyc Sc Wx mx mdx pos fr sp2 jj
    x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
    Hra Rf Rlen Hfb HJ HPerm HFS Hjj VWSH VHDR VFPW HB STW HFr.
  pose proof (bv_unsigned_in_range 64 (lib.Reusable.YK11.getr regs 2)) as RSp.
  unfold bv_modulus in RSp. cbn [Z.of_N] in RSp.
  change (bv_unsigned (lib.Reusable.YK11.getr regs 2)) with (lib.Reusable.YG0d.spZ regs) in RSp.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S16 & _ & Hceil & Hslo & Hshi & H47 & _)
                    & _ & _).
  pose proof lib.Reusable.YCbq.asan_consts as (C1 & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo.
  assert (HK : 9136 <= lib.Reusable.YG0d.spZ regs) by lia.
  assert (HHM : HIGHMEM_BEG <= lib.Reusable.YG0d.spZ regs - 9136) by (unfold HIGHMEM_BEG; lia).
  assert (HAE : lib.Reusable.YG0d.spZ regs <= APPMEM_END) by (unfold APPMEM_END; lia).
  (* the window's visibility: ProgWorldVisWin.win_vis on the exit journal *)
  pose proof (lib.B.ProgWorldVisWin.win_vis B C_reac_box_catalogue_match.CM_STK (lib.Reusable.YG0d.spZ regs) []
                ly S W memc md [(2, pos)] lyc Sc Wx mx mdx 0 (lib.Reusable.YG0d.spZ regs - 9136) 9136
                (cmZ_ajournal_sk SK lib.Reusable.YE2k.tfib_sink_head _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ)
                ltac:(unfold C_reac_box_catalogue_match.CM_STK; lia) ltac:(lia)) as VWIN.
  apply (cmZ_rel_ret Wx ly S W memc md lyc Sc mx mdx 0 (lib.Reusable.YG0d.spZ regs) pos
           (lib.Reusable.YK11.getr regs 1) (lib.Reusable.YK11.getr regs 3) (lib.Reusable.YK11.getr regs 4)
           (lib.Reusable.YK11.getr regs 8) (lib.Reusable.YK11.getr regs 9) (lib.Reusable.YK11.getr regs 18)
           (lib.Reusable.YK11.getr regs 19) (lib.Reusable.YK11.getr regs 20) (lib.Reusable.YK11.getr regs 21)
           (lib.Reusable.YK11.getr regs 22) (lib.Reusable.YK11.getr regs 23) (lib.Reusable.YK11.getr regs 24)
           (lib.Reusable.YK11.getr regs 25) (lib.Reusable.YK11.getr regs 26) (lib.Reusable.YK11.getr regs 27)
           lib.Reusable.YK11.fp_regs lib.Reusable.YK11.fp_csr f len (lib.Reusable.YG0d.spZ regs) FS fb fr sp2 jj
           (want CM_T len fb) x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
           (C_reac_box_catalogue_match.treac_box_catalogue_match_post B regs ly S W memc md len fb)
           Rf Rlen ltac:(lia) S16 HK Hfb HHM HAE VWIN VWSH VHDR VFPW HB STW eq_refl HFr HJ HFS Hjj).
  intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' md' HJ'.
  apply lib.Reusable.YA0n.SRr_ret.
  unfold C_reac_box_catalogue_match.treac_box_catalogue_match_post, lib.Reusable.APostBase.apost_base.
  do 5 eexists.
  split; [rewrite (cmZ_ret_pc _ Hra); reflexivity|].
  split; [unfold C_reac_box_catalogue_match.EV_CM; exact HJ'|].
  split.
  { intros rr Hr. unfold lib.Reusable.YG0d.acallee_saved in Hr.
    destruct Hr as [-> | [-> | [-> | [-> | [-> | Hr]]]]].
    - transitivity (Z_to_bv 64 (lib.Reusable.YG0d.spZ regs)); [reflexivity|].
      unfold lib.Reusable.YG0d.spZ. apply lib.Lib.MState.Z_to_bv_bv_unsigned.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - assert (Hr' : rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/
                    rr = 26 \/ rr = 27) by lia.
      destruct Hr' as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]]]; reflexivity. }
  split.
  - reflexivity.
  - unfold lib.Reusable.YG0d.ablocks. rewrite lib.Reusable.YG01.blocks_stack_free_state. exact HPerm.
Qed.

(* ---- H3 from H2's interface C_reac_box_catalogue_matchPfI.cmPf_exit_at (the exit 0x850fc) to the post.  The
   footprint's visibility, all from the exit's AR (the journal's first conjunct), each by a Qed lemma used by name:
   the window's shadow by ProgWorldVisWin.win_sh_vis (the stack bounds from the entry's astk_ok through the journal's
   layout_le; its sh_al8 cover contains [shadow (sp - 9136), shadow sp)); the side stack's header and every
   fp_w [0; 1; 2] range by C_reac_box_catalogue_matchPfV.cmPf_fs_vis at ly_F ly' = ly_F ly (cmPf_exit_at (g)).
   FS = ly_F ly, jj = pos.  No frame-route premise is left. ---- *)
Lemma cmPf_exit_at_post : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (W' : lib.Reusable.YA0n.world rsegs) (c : config),
  lib.Reusable.YK0s.ret_ok (lib.Reusable.YK11.getr regs 1) ->
  0 <= f < 2 ^ 64 -> 0 <= len < 2 ^ 64 -> length fb = 50%nat ->
  C_reac_box_catalogue_matchPfI.cmPf_exit_at B W ly S regs memc md f len fb W' c ->
  lib.Reusable.YA0n.SRr rsegs W' c
    (C_reac_box_catalogue_match.treac_box_catalogue_match_post B regs ly S W memc md len fb).
Proof.
  intros W ly S regs memc md f len fb W' c Hra Rf Rlen Hfb
    (ly' & S' & mX & mdX & pos & x1 & u0 & u1 & u2 & y0 & y1 & y2 & y3 & y4 & y5 & y6 & y7 & z3 & z5 & z6 & z9 & z10 &
     z11 & u3 & u4 & u5 & u6 & -> & HJ & Hfrs & Hnin & HPerm & HlyF & Hpos & Hfa & Hfla & HB & STW & HFr).
  (* the side stack's visibility: C_reac_box_catalogue_matchPfV.cmPf_fs_vis at the exit's AR *)
  pose proof HJ as (HARx & _).
  destruct (C_reac_box_catalogue_matchPfV.cmPf_fs_vis B ly' S' W' mX mdX HARx) as [VHDR VFPW].
  rewrite HlyF in VHDR, VFPW.
  (* the window's shadow: ProgWorldVisWin.win_sh_vis at the exit's AR *)
  pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S16 & _ & Hceil & Hslo & Hshi & _) & _).
  destruct Hly as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Elo & Ehi & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo.
  destruct (lib.B.ProgWorldVisWin.win_sh_vis B LAWS ly' S' W' mX mdX (lib.Reusable.YG0d.spZ regs - 9136) 9136 HAR
              ltac:(rewrite Elo; lia) ltac:(rewrite Ehi; lia) ltac:(lia)) as [E0 | VSH]; [lia|].
  assert (VWSH : B.ProgBridge.range_visible (lib.Reusable.YA0n.w_H W') (shadow_addr (lib.Reusable.YG0d.spZ regs - 9136))
                   (shadow_addr (lib.Reusable.YG0d.spZ regs) - shadow_addr (lib.Reusable.YG0d.spZ regs - 9136))).
  { apply (B.ProgBridge.range_visible_sub _ _ _ _ _ VSH);
      unfold B.Prog.rng_asan.sh_al8_lo, B.Prog.rng_asan.sh_al8_hi, shadow_addr, ASAN_K; Z.div_mod_to_equations; lia. }
  exact (cmPf_exit_post W ly S regs memc md f len (lib.Reusable.YG0f.ly_F ly) fb ly' S' W' mX mdX pos
           (fs_frame (lib.Reusable.YG0f.ly_F ly) 2 pos) (CA (lib.Reusable.YG0d.spZ regs)) pos
           x1 u0 u1 u2 y0 y1 y2 y3 y4 y5 y6 y7 z3 z5 z6 z9 z10 z11 u3 u4 u5 u6
           Hra Rf Rlen Hfb HJ HPerm (eq_sym HlyF) eq_refl VWSH VHDR VFPW HB STW HFr).
Qed.

(* ==== THE TOP COMPOSITION: the spec from H1 (C_reac_box_catalogue_matchPf.cmPf_to_sm2_ret: entry -> S-A -> E1 ->
   cmPf_sm2_ret), H2 (C_reac_box_catalogue_matchPfB.cmPfB_mid: cmPf_sm2_ret -> S-B -> E2 -> S-C -> the row loop ->
   cmPf_exit_at) and H3 (cmPf_exit_at_post: exit -> S-5 + release + S-6 -> post).
   SECTION HYPOTHESES added here (core vocabulary only, as in C_reac_box_catalogue_matchPf.v's and
   C_reac_box_catalogue_matchPfB.v's headers):
     segs_low, errno_low, TL_CODE  core statements pending the record core (YCeg.tfib_segs_low, YCeg.tl_env,
                                   YCeg.tl_code; lib/Reusable/YCeg.v compiles on no B base yet);
     ML, SMP, ASM2                 core laws;
     RELRO_IMG                     the spec file's own Section hypothesis (C_reac_box_catalogue_match.v:46), the
                                   composer's (CtrlImg.ctrl_relro_img at pa_relro);
     GLOBS, TPARSE, TMB            the two walked callees' contracts by name (a Theorem Labs lane ea59dbb03aa; a Theorem Labs lane
                                   5487787da37 / 572f4b58796), as cmPfB_mid takes them;
     ABCMP                         the bcmp wrapper's route-(C) contract bcmp_wrap_c_on.bcmp_wrap_contract_F_on
                                   (lib/B/Prog/bcmp_wrap_c_on.v), as cmPfB_mid takes it.
   PREMISES of cmPf_top:
     HTS   the core bundle law YF0m.CtrlTSyms B;
           no ProgWorld statement is a premise (route (C)): C_reac_box_catalogue_matchPfV.cmPf_base_of_AR gives the
           base facts at the entry (cmPf_to_sm2_ret's cmBase) and, by cmZ_base_all, at every journal state
           (cmPfB_mid's HBASE) from ProgWorldCtlRtC.ctl_rt_C_of_AR and PfV.cmPf_shrwR_of_AR: cmBase's clause (1)
           is the run's region R = reac_box_catalogue_match_shadow_R f len Sp FS (the `_on` run
           reac_box_catalogue_matchF_on.v takes SRo : shadow_rw_on R m), never the universal B.AsanRT.shadow_rw, so
           AR_states_vis0_shadow and AR_states_owned_ro are no premises;
     HG17  FRAME-ROUTE, cmPfB_mid's: the image's registered globals GLOBS hold the table's data range
           [CM_T, CM_T + 3256) (C_reac_box_catalogue_match.v:120 plan, HG17 : In (A_CM_TBL, CM_ROWS) G);
     HRLO, HRHI
           the table inside the spec's read-only span (C_reac_box_catalogue_match.v:49-51: the composer's
           arithmetic at the B PA instance's pa_relro). ==== *)
(* Core, PENDING THE RECORD CORE (YCeg.v:25 refused name): the statement of Reusable.YCeg.tfib_segs_low (YCeg.v:64). *)
Hypothesis segs_low : forall a, lib.Reusable.YG0d.in_img rsegs a -> 0 <= a < lib.Reusable.YG0f.kLowMemEnd.
(* Core, PENDING THE RECORD CORE (YCeg.v:25 refused name): the statement of Reusable.YCeg.tl_env (YCeg.v:38) for B. *)
Hypothesis errno_low : lib.Reusable.YCbq.api_env rsegs B.
(* Core: the model's laws. *)
Hypothesis ML : lib.Reusable.YG0d.model_laws (lib.Reusable.YG0f.as_universe B).
(* Core: the fake stack's progress rule. *)
Hypothesis SMP : lib.Reusable.YCbq.stack_malloc_progressP B.
(* Core: the class-2 fake-stack rule (fake-stack owner a Theorem Labs lane with a Theorem Labs lane). *)
Hypothesis ASM2 : lib.Reusable.YG0d.astack_malloc_realizes rsegs B 2.
(* Core, PENDING THE RECORD CORE (YCeg.v:25 refused name): the statement of the TfibLib field Reusable.YCeg.tl_code
   (YCeg.v:27), B's code table. *)
Hypothesis TL_CODE : lib.Reusable.YG0f.as_code B = lib.Reusable.YF0l.Tfib_code.
(* The read-only span of the spec's arodata_okS (C_reac_box_catalogue_match.v:44). *)
Variables RLO RHI : Z.
(* The spec file's Section hypothesis (C_reac_box_catalogue_match.v:45). *)
Hypothesis RELRO_IMG : forall a, RLO <= a < RHI -> lib.Reusable.YG0d.in_img rsegs a.
(* The registered globals (TMB) and the two walked callees, by name, as C_reac_box_catalogue_matchPfB.v takes them. *)
Variable GLOBS : list (Z * Z).
Hypothesis TPARSE : C_reac_ctrl_parse.treac_ctrl_parse_spec (SK := SK) rsegs B RLO RHI.
Hypothesis TMB : C_reac_box_model_block.treac_box_model_block_spec RLO RHI B GLOBS.
(* The bcmp wrapper inside stretch 4, route (C) (lib/B/Prog/bcmp_wrap_c_on.v). *)
Hypothesis ABCMP : bcmp_wrap_c_on.bcmp_wrap_contract_F_on.

(* cmPfB_mid's HBASE from cmPf_base_of_AR at each journal state (the journal's head is AR): with FP = [] the journal
   keeps the live record block (its dropped-block clause gives inFP [] otherwise, YI04.inFP_nil) and its bytes (its
   block clause), the read-only view (C_reac_box_catalogue_matchPfB.cmPfB_mb_aro, RELRO_IMG), the stack bounds
   (astk_ok at the entry layout, layout_le) and ly_F. *)
Lemma cmZ_base_all : forall (W : lib.Reusable.YA0n.world rsegs) (ly : lib.Reusable.YG0f.alayout)
    (S : lib.Reusable.YG00.astate) (regs : bvmap 5 word) (memc : word -> option byte) (md : Model) (f len : Z)
    (fb : list byte) (pos : Z),
  lib.Reusable.YF0m.CtrlTSyms B ->
  (* no ProgWorld statement (route (C)) *)
  lib.Reusable.YE01.arodata_okS rsegs B RLO RHI (lib.Reusable.YG0n.aview rsegs (lib.Reusable.YA0n.w_H W) memc) ->
  RLO <= C_reac_box_catalogue_match.A_CM_TBL ->
  C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS <= RHI ->
  (forall a, C_reac_box_catalogue_match.A_CM_TBL <= a < C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS ->
     ~ Exists (lib.Reusable.YG0n.in_zr a) (lib.Reusable.YG0f.as_owned_static B) /\
     ~ (lib.Reusable.YG0f.as_errno B <= a < lib.Reusable.YG0f.as_errno B + 4)) ->
  lib.Reusable.YK11.getr regs 4 = lib.Reusable.YG0d.w64 (lib.Reusable.YG0f.as_tp B) ->
  0 <= f < 2 ^ 64 -> length fb = 50%nat ->
  (50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S) /\ 50 <= lib.Reusable.YG00.req_size n) ->
  (50 <= len -> lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H W) memc) f
                  (map (fun b : byte => bv_unsigned b) fb)) ->
  C_reac_box_catalogue_matchPfB.cmPfB_base_all B ly S W regs memc md f len fb pos.
Proof.
  intros W ly S regs memc md f len fb pos HTS Hro HRLO HRHI Htbl Htp Rf Hfb Hlive Hbytes.
  unfold C_reac_box_catalogue_matchPfB.cmPfB_base_all.
  intros lyc Sc Wc m mdc k HJ.
  pose proof HJ as (HARc & Hly & _ & _ & _ & _ & _ & _ & _ & JBL & _ & _ & JDROP & _ & Hstk & _).
  pose proof Hly as (_ & _ & _ & _ & _ & EF & _ & _ & _ & Elo & Ehi & _).
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo.
  (* the live record block is kept *)
  assert (Hd : forall x y : Z * Z, {x = y} + {x <> y}) by (decide equality; apply Z.eq_dec).
  assert (Hkeep : forall n, In (f, n) (lib.Reusable.YG0d.ablocks B ly S) -> 50 <= lib.Reusable.YG00.req_size n ->
                    In (f, n) (lib.Reusable.YG0d.ablocks B lyc Sc)).
  { intros n Hin Hn. destruct (in_dec Hd (f, n) (lib.Reusable.YG0d.ablocks B lyc Sc)) as [Hc | Hc]; [exact Hc|].
    exfalso. exact (lib.Reusable.YI04.inFP_nil _ (JDROP f n 0 Hin Hc ltac:(lia))). }
  assert (Hlivec : 50 <= len -> exists n, In (f, n) (lib.Reusable.YG0d.ablocks B lyc Sc) /\
                                          50 <= lib.Reusable.YG00.req_size n).
  { intros L. destruct (Hlive L) as (n & Hin & Hn). exists n. exact (conj (Hkeep n Hin Hn) Hn). }
  (* its bytes are kept *)
  assert (Hbytesc : 50 <= len -> lib.Reusable.YI00.garr8 rsegs (lib.Reusable.YK04.mrestrict (lib.Reusable.YA0n.w_H Wc) m)
                                   f (map (fun b : byte => bv_unsigned b) fb)).
  { intros L. destruct (Hlive L) as (n & Hin & Hn).
    apply (cmZ_garr8_view (lib.Reusable.YA0n.w_H W) (lib.Reusable.YA0n.w_H Wc) memc m f _); [|exact (Hbytes L)].
    intros j Hj. rewrite length_map, Hfb in Hj.
    exact (JBL f n (Z.of_nat j) Hin (Hkeep n Hin Hn) ltac:(lia) (lib.Reusable.YI04.inFP_nil _)). }
  (* the read-only view is kept *)
  pose proof (C_reac_box_catalogue_matchPfB.cmPfB_mb_aro B RLO RHI _ _ _ _ _ _ _ _ _ _ _ _ _ _ RELRO_IMG HJ Hro)
    as Hroc.
  pose proof (C_reac_box_catalogue_matchPfV.cmPf_base_of_AR B LAWS RLO RHI lyc Sc Wc m mdc f len
                (lib.Reusable.YG0d.spZ regs) fb HTS HARc
                (lib.B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Hroc ltac:(lia) ltac:(lia))
                HRLO HRHI Htbl ltac:(lia) ltac:(lia) ltac:(lia) Rf Hfb Hlivec Hbytesc) as HB.
  rewrite EF, <- Htp in HB. exact HB.
Qed.

Theorem cmPf_top :
  (* the core bundle law *)
  lib.Reusable.YF0m.CtrlTSyms B ->
  (* no ProgWorld statement is a premise (route (C): cmBase's clause (1) is the run's region, from ctl_rt_C_of_AR) *)
  (* FRAME-ROUTE HG17 (cmPfB_mid's): the registered globals hold the table's data range *)
  (exists q sz, In (q, sz) GLOBS /\ q <= CM_T /\ CM_T + 3256 <= q + sz) ->
  (* the table inside the read-only span (C_reac_box_catalogue_match.v:49-51) *)
  RLO <= C_reac_box_catalogue_match.A_CM_TBL ->
  C_reac_box_catalogue_match.A_CM_TBL + C_reac_box_catalogue_match.CM_ROWS <= RHI ->
  C_reac_box_catalogue_match.treac_box_catalogue_match_spec RLO RHI B.
Proof.
  intros HTS HG17 HRLO HRHI.
  unfold C_reac_box_catalogue_match.treac_box_catalogue_match_spec.
  intros ly S W regs memc md f len fb HAR Hra Hra4 Hgp Htp Hstk Hpres HQT Hro H10 H11 Rf Rlen Hfb Hlive Hbytes Htbl
    Hc2 Hc1 Hc0 Hnev Hbb.
  pose proof Hstk as (_ & _ & Hceil & Hslo & Hshi & _).
  unfold C_reac_box_catalogue_match.CM_STK in Hslo.
  pose proof (C_reac_box_catalogue_matchPfV.cmPf_base_of_AR B LAWS RLO RHI ly S W memc md f len
                (lib.Reusable.YG0d.spZ regs) fb HTS HAR
                (lib.B.ProgWorld.arodata_okP_of_S B RLO RHI RLO RHI _ Hro ltac:(lia) ltac:(lia))
                HRLO HRHI Htbl Hceil ltac:(lia) Hshi Rf Hfb Hlive Hbytes) as HB.
  rewrite <- Htp in HB.
  apply (C_reac_box_catalogue_matchPf.cmPf_to_sm2_ret B LAWS segs_low errno_low ML SMP ASM2 TL_CODE W ly S regs memc md
           f len (lib.Reusable.YG0f.ly_F ly) fb _ HAR Hgp Htp Hstk Hpres HQT H10 H11 Rf Rlen Hfb Hc2 HB).
  intros m1 md1 regsT S2 regs2 m2 md2 pos HSM.
  apply (C_reac_box_catalogue_matchPfB.cmPfB_mid B RLO RHI GLOBS LAWS segs_low TPARSE TMB ABCMP
           W ly S regs memc md f len fb m1 md1 regsT S2 regs2 m2 md2 pos _ Hgp Htp Rf Rlen Hfb Hlive Hbytes Hro Htbl
           Hc1 Hc0 RELRO_IMG
           (cmZ_base_all W ly S regs memc md f len fb pos HTS Hro HRLO HRHI Htbl Htp Rf Hfb Hlive Hbytes)
           HG17 HRLO HRHI HSM).
  intros W' c HEX.
  exact (cmPf_exit_at_post W ly S regs memc md f len fb W' c Hra Rf Rlen Hfb HEX).
Qed.
End Z.

(* The closed statement and its assumptions, printed in the build log. *)
Check cmPf_top.
Print Assumptions cmPf_top.
